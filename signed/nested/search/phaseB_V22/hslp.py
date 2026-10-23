# Direct highspy solves for the generator LPs (same LPs as scipy.optimize.linprog(method='highs') with A_ub x <= b_ub):
# presolve off, no scipy wrapper overhead, optional warm start from the previous basis of the same shape.
import os, numpy as np, highspy
_INF = highspy.kHighsInf
_BASIS = {}
HREUSE = os.environ.get("HREUSE", "0") == "1"     # one Highs object per process (Highs() + enableCallbacks cost ~1.3 ms per LP)
_H = None
def _highs():
    global _H
    if not HREUSE:
        h = highspy.Highs(); h.setOptionValue("output_flag", False); h.setOptionValue("presolve", "off"); return h
    if _H is None:
        _H = highspy.Highs(); _H.setOptionValue("output_flag", False); _H.setOptionValue("presolve", "off")
    else:
        _H.clearModel()
    return _H
def solve_ub(c, A, b, lo, hi, key=None):
    """min c.x s.t. A x <= b, lo <= x <= hi (None -> infinite). Returns (status_ok, x, fun)."""
    A = np.asarray(A, float); nr, nc = A.shape
    h = _highs()
    lp = highspy.HighsLp(); lp.num_col_ = nc; lp.num_row_ = nr
    lp.col_cost_ = np.asarray(c, float)
    lp.col_lower_ = np.array([-_INF if v is None else v for v in lo], float)
    lp.col_upper_ = np.array([_INF if v is None else v for v in hi], float)
    lp.row_lower_ = np.full(nr, -_INF); lp.row_upper_ = np.asarray(b, float)
    nzr, nzc = np.nonzero(A.T)            # column-major order of nonzeros
    lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise
    lp.a_matrix_.start_ = np.concatenate([[0], np.cumsum(np.bincount(nzr, minlength=nc))]).astype(np.int32)
    lp.a_matrix_.index_ = nzc.astype(np.int32); lp.a_matrix_.value_ = A.T[nzr, nzc]
    h.passModel(lp)
    if key is not None and key in _BASIS and _BASIS[key][0] == (nr, nc):
        h.setBasis(_BASIS[key][1])
    h.run()
    if h.getModelStatus() != highspy.HighsModelStatus.kOptimal: return False, None, None
    if key is not None: _BASIS[key] = ((nr, nc), h.getBasis())
    x = np.array(h.getSolution().col_value)
    return True, x, float(np.dot(lp.col_cost_, x))
