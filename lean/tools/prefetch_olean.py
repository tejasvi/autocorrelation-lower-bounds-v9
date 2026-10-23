"""Page-cache prefetch of exactly the pages that Lean's import (readModuleData + finalizeImport) touches in each .olean:
the header page, the root ModuleData object, the arrays it points to (imports, constNames, constants, extraConstNames,
entries) with their element objects, and for `constants` every ConstantInfo object (finalizeImport stores each one in
the constant map, and the runtime reads its header), plus the inner arrays of the entries.  Measured on c39t shard
oleans with mincore: the import of one 153-module closure touched 22% of the pages in ~1 run per job; these objects
are where the runs are.  Pages are read with pread in parallel threads (adjacent pages merged).
usage: prefetch_olean.py LIST [THREADS]"""
import os, sys, struct, time
from concurrent.futures import ThreadPoolExecutor

PS = 4096


def pages_of(fd, size):
    head = os.pread(fd, PS, 0)
    base, rootp = struct.unpack_from("<QQ", head, 80)
    pages = {0}
    cache = {}

    def page(pg):
        b = cache.get(pg)
        if b is None:
            b = os.pread(fd, PS, pg * PS); cache[pg] = b
        return b

    def read(off, n):
        out = b""
        while n > 0:
            pg, o = divmod(off, PS)
            b = page(pg); pages.add(pg)
            k = min(n, PS - o)
            out += b[o:o + k]; off += k; n -= k
        return out

    def hdr(off):
        return struct.unpack("<iHBB", read(off, 8))

    def obj(p):                         # pointer -> file offset (scalars: None)
        if p & 1:
            return None
        o = p - base
        return o if 0 <= o < size else None

    ro = obj(rootp)
    _, _, nf, _ = hdr(ro)
    fields = struct.unpack("<%dQ" % nf, read(ro + 8, 8 * nf))
    for fi, fp in enumerate(fields):
        fo = obj(fp)
        if fo is None:
            continue
        rc, cs, other, tag = hdr(fo)
        if tag != 246:                  # not an array
            continue
        n = struct.unpack("<Q", read(fo + 8, 8))[0]
        elems = struct.unpack("<%dQ" % n, read(fo + 24, 8 * n)) if n else ()
        for ep in elems:
            eo = obj(ep)
            if eo is None:
                continue
            _, _, enf, _ = hdr(eo)          # touches the element object's page (ConstantInfo, Name, pair, Import)
            if fi == 4 and enf >= 2:        # entries: (Name × Array EnvExtensionEntry): the inner array's header
                sub = struct.unpack("<%dQ" % enf, read(eo + 8, 8 * enf))
                for sp in sub:
                    so = obj(sp)
                    if so is not None:
                        hdr(so)
    return len(pages)


def one(path):
    try:
        fd = os.open(path, os.O_RDONLY)
    except OSError:
        return 0
    try:
        return pages_of(fd, os.fstat(fd).st_size)
    except Exception as e:
        sys.stderr.write(f"{path}: {e!r}\n")
        return 0
    finally:
        os.close(fd)


if __name__ == "__main__":
    lst = [l.strip() for l in open(sys.argv[1]) if l.strip()]
    th = int(sys.argv[2]) if len(sys.argv) > 2 else 64
    t0 = time.time(); tot = 0
    with ThreadPoolExecutor(th) as ex:
        for i, n in enumerate(ex.map(one, lst, chunksize=16)):
            tot += n
            if i and i % 20000 == 0:
                print(f"{i} files {tot} pages ({tot * PS / 1e9:.1f} GB) {time.time() - t0:.0f}s", flush=True)
    print(f"done {len(lst)} files {tot} pages ({tot * PS / 1e9:.1f} GB) {time.time() - t0:.0f}s", flush=True)
