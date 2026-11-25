# 实际更新底的规范域保持
不读记号；编译定理：两条实际链的全部累计前缀自相关，实际更新 Base 也自相关。
来源：YiVRRel 的 NoΩ/Ωt≼ 与 YiOGFold.fl；不把自相关当作两条链之间的底比较。
没有填 ActualMissing；入口为 source-base-can、target-base-can。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOGCanon where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiVRRel as V
import OCF.Lean.YiVRFold as VF
import OCF.Lean.YiOGState as St
import OCF.Lean.YiOGFold as Fold
import OCF.Lean.YiOFLocal as C
import OCF.Lean.YiTNRow as R
module G = St.G
module T = St.T
source-no : (n : ℕ) → V.NoΩ (C.g n)
source-no n = V.NoΩ↑ (C.f n)
shift-no : (d : B.Tr B.zero) → V.NoΩ (R.shift d)
shift-no B.zero = tt
shift-no (B.suc d) = shift-no d
shift-no (B.lim f a) = λ n → shift-no (f n)
shift-no (B.Ω () g)
shift-no (B.up x () y e)
target-no : (n : ℕ) → V.NoΩ (C.h n)
target-no n = shift-no (C.f n)
source-base-standard = VF.B₀⊴-noΩ G.ℓ source-no
target-base-standard = VF.B₀⊴-noΩ T.ℓ target-no

opaque
  unfolding G.prefix G.part G.previous G.base-at
  source-prefix-can : (n : ℕ) → V.Can G.ℓ (G.prefix n)
  source-prefix-can zero = V.upz≼ 0 (V.Ωt≼ (C.g 0) (source-no 0))
  source-prefix-can (suc n) = V.+≼ (source-prefix-can n) (V.upz≼ (suc n) (V.Ωt≼ (C.g (suc n)) (source-no (suc n))))
  source-previous-can : (n : ℕ) → V.Can G.ℓ (G.previous n)
  source-previous-can zero = V.z≼
  source-previous-can (suc n) = source-prefix-can n
  source-base-can : (n : ℕ) → VF._⊴_ (G.base-at n) (G.base-at n)
  source-base-can n i u pr = Fold.fl G.ℓ source-no C.og (F.B₀ G.ℓ) (F.B₀ G.ℓ) source-base-standard
    i (P.inc n u) (O.Ωt i) (O.Ωt i) (V.Ωt≼ i (V.NoΩ≤ u (source-no n))) (source-previous-can n)

opaque
  unfolding T.prefix T.part T.previous T.base-at
  target-prefix-can : (n : ℕ) → V.Can T.ℓ (T.prefix n)
  target-prefix-can zero = V.upz≼ 0 (V.Ωt≼ (C.h 0) (target-no 0))
  target-prefix-can (suc n) = V.+≼ (target-prefix-can n) (V.upz≼ (suc n) (V.Ωt≼ (C.h (suc n)) (target-no (suc n))))
  target-previous-can : (n : ℕ) → V.Can T.ℓ (T.previous n)
  target-previous-can zero = V.z≼
  target-previous-can (suc n) = target-prefix-can n
  target-base-can : (n : ℕ) → VF._⊴_ (T.base-at n) (T.base-at n)
  target-base-can n i u pr = Fold.fl T.ℓ target-no St.oh (F.B₀ T.ℓ) (F.B₀ T.ℓ) target-base-standard
    i (P.inc n u) (O.Ωt i) (O.Ωt i) (V.Ωt≼ i (V.NoΩ≤ u (target-no n))) (target-previous-can n)
```
