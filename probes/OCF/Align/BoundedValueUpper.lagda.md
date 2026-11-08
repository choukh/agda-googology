# 实际有界混合不超过公共目标地板

把每个搬运分量识别为公共目标地板 θ 累加中的真实被加项。
全部自然数部分和同时比较，不选择有限最大分量。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedValueUpper where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (LH; lz; lΩ; Lv)
open import OCF.Lean.LHRecLay using (ΩL; upL; _⊕L_)
open import OCF.Lean.LHRecFl using (flL; cxI; gcF)
import OCF.Lean.LHRecLeg as Leg
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; l≤; ≤l; ≤Ω)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo; same-value; same-sym)
open import OCF.Align.FrozenInnerOuter using (same-add; same-refl)
open import OCF.Align.FrozenOutputModel using (same-trans)
import OCF.Lean.BoundedContextClosed as C

family : Cd → LH
family c = ΩL C.k ⊕L upL C.k (up c)

-- 上界地板的真实坐标累加器。
θ : Cd → HB C.M.T
θ = Leg.New.θ (cxI lz family)
  (gcF (λ d → ι (inj₂ d) (flL (family d))))

zero-add : ∀ {S} (a : HB S) → Same (hz ⊞ a) a
zero-add hz = zz
zero-add (hs a) = ss (zero-add a)
zero-add (hl f) = ll (λ n → zero-add (f n))
zero-add (hΩ κ g) = oo (λ c → zero-add (g c))

component : ∀ n (a : HB (C.M.F (C.member n))) →
  Same (C.M.embed (C.M.inject (C.member n) a)) (ι (inj₂ (C.num n)) a)
component n hz = zz
component n (hs a) = ss (component n a)
component n (hl f) = ll (λ j → component n (f j))
component n (hΩ κ g) = oo (λ c → component n (g c))

embed-add : ∀ (a b : HB C.M.S) →
  Same (C.M.embed (a ⊞ b)) (C.M.embed a ⊞ C.M.embed b)
embed-add a hz = same-refl _
embed-add a (hs b) = ss (embed-add a b)
embed-add a (hl f) = ll (λ n → embed-add a (f n))
embed-add a (hΩ (i , κ) g) = oo (λ c → embed-add a (g (Leg.frC (C.M.ctx i) κ c)))

sums-θ : ∀ n → Same (C.M.embed (C.M.sums C.member n)) (θ (C.num (suc n)))
sums-θ zero = same-trans (component 0 (flL (family (C.num 0))))
  (same-sym (zero-add (ι (inj₂ (C.num 0)) (flL (family (C.num 0))))))
sums-θ (suc n) = same-trans
  (embed-add (C.M.sums C.member n) (C.M.floor (C.member (suc n))))
  (same-add (sums-θ n) (component (suc n) (flL (family (C.num (suc n))))))

output≤θω : C.output ≤ᵛ θ (hl C.num)
output≤θω = l≤ (λ n → ≤l (suc n) (same-value (sums-θ n)))

θω≤output : θ (hl C.num) ≤ᵛ C.output
θω≤output = l≤ each
  where
  each : ∀ n → θ (C.num n) ≤ᵛ C.output
  each zero = z≤
  each (suc n) = ≤l n (same-value (same-sym (sums-θ n)))

output≤common-floor : C.output ≤ᵛ flL (C.M.g C.B)
output≤common-floor = ≤Ω (hl C.num)
  (l≤ (λ n → ≤l (suc n) (same-value (sums-θ n))))
```

这是无条件的高层树值上界：实际混合输出不超过其已有公共目标地板。
还证明 output 与公共目标地板的实际 θ(ω) 分支互相 ≤ᵛ。
它没有证明某个有限编号分量最大，也没有把可数折叠后的 ψ 强度判低。
目前仍缺保留这些下界的可数折叠，以及该折叠值与终点参照的连接。
