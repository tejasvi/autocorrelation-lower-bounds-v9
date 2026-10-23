import C64K.KChk

/-!
# Decidable equality of the kernel-layer data (core Lean only)

For hoisted facts such as `arcCtx g .. = some A0` with a literal `A0` (`decide +kernel`): derived `DecidableEq` for
the sign-magnitude balls, the tables, the ellipses, the arc context, and `C64Chk.Q`.
-/

deriving instance DecidableEq for KIval.KBall
deriving instance DecidableEq for KNum.KCBall
deriving instance DecidableEq for C64Chk.Q
deriving instance DecidableEq for C64KChk.EllB
deriving instance DecidableEq for C64KChk.PtT
deriving instance DecidableEq for C64KChk.ACtx
