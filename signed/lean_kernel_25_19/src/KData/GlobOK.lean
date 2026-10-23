import KData.Glob
import C64K.KChk
import C64Shard.ShardK
import C64Shard.LeafK

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

open C64Chk

namespace KData

theorem globOK : C64KChk.checkGlob glob = true := by
  decide +kernel

end KData
