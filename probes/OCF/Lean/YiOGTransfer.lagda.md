# 第 1 前缀的逐分量底义务
不读记号；编译条件定理：BaseTransferOne 与已证 β 界推出 SameLevelMissing。
BaseTransferOne 保留源实际底及目标实际底的两次拉回，居民在 YiOGBaseAll。
零层的值序与 Le 互推；不外推全体 ActualMissing。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOGTransfer where
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiVRRel as R
import OCF.Lean.YiVRFold as RF
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiOFLocal as C
import OCF.Lean.YiOGState as S
import OCF.Lean.YiOGActual as A
import OCF.Lean.YiOGCanon as Can
import OCF.Lean.YiOGFold as Fold

v→r : (x y : B.Tr B.zero) → V.val B.zero x V.≼ V.val B.zero y → R.Le B.zero x y
v→r B.zero y d = R.z≼
v→r (B.suc x) B.zero ()
v→r (B.suc x) (B.suc y) (V.s≼s d) = R.s≼s (v→r x y d)
v→r (B.suc x) (B.lim f a) (V.≼l n d) = R.≼l n (v→r (B.suc x) (f n) d)
v→r (B.lim f a) B.zero (V.l≼ h) = R.l≼ (λ n → v→r (f n) B.zero (h n))
v→r (B.lim f a) (B.suc y) (V.l≼ h) = R.l≼ (λ n → v→r (f n) (B.suc y) (h n))
v→r (B.lim f a) (B.lim g b) (V.l≼ h) = R.l≼ (λ n → v→r (f n) (B.lim g b) (h n))
v→r (B.lim f a) (B.lim g b) (V.≼l n d) = R.≼l n (v→r (B.lim f a) (g n) d)
v→r (B.Ω () g) y d
v→r (B.up x () y e) z d
v→r (B.suc x) (B.Ω () g) d
v→r (B.suc x) (B.up y () z e) d
v→r (B.lim f a) (B.Ω () g) d
v→r (B.lim f a) (B.up y () z e) d

r→v : {x y : B.Tr B.zero} → R.Le B.zero x y → V.val B.zero x V.≼ V.val B.zero y
r→v R.z≼ = V.z≼
r→v (R.s≼s d) = V.s≼s (r→v d)
r→v (R.≼s d) = V.≼-suc (r→v d)
r→v (R.≼l n d) = V.≼l n (r→v d)
r→v (R.l≼ h) = V.l≼ (λ n → r→v (h n))
r→v (R.≼w {p = ()} d)
r→v (R.w≼w {p = ()} h)
r→v (R.≼u {c = ()} d)
r→v (R.u≼u {c = ()} dx dy)

source-base : F.Base (C.g 1)
source-base = S.G.base-at 1
target-base : F.Base (C.g 1)
target-base i u = S.T.base-at 1 i (P.inc tt (P.inc tt u))
BaseTransferOne : Set
BaseTransferOne = RF._⊴_ source-base target-base
transfer-one : BaseTransferOne → A.SameLevelMissing
transfer-one b = subst (λ x → V.val B.zero (proj₁ x) V.≼ V.val B.zero (proj₁ A.D₂.low))
  (sym (S.G.state-row 1)) (r→v
    (Fold.fl (C.g 1) (Can.source-no 1) (proj₂ C.og 1) source-base target-base b
      B.zero (C.wg 1) (S.G.start-at 1) (S.T.start-at 1)
      (v→r _ _ A.beta-one) (R.Ωt≼ (C.g 1) (Can.source-no 1))))
```
