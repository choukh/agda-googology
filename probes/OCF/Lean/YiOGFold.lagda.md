# 更新底在树侧模拟关系中的保持
不读记号；编译定理：NoΩ 层号上，最小表折叠保持 YiVRRel.Le 的底、起点与输入关系。
来源：YiKAMono.cbK/inflK/flK；改为 YiRWPath 与 YiTBRow，复用 YiVRFold 的结点引理。
前提先在实际首前缀检查；不声称任意树的值单调，实际更新实例见 YiOGCanon。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOGFold where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂; _,_)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; kp)
open import OCF.Lean.YiVRRel
open import OCF.Lean.YiVRFold using (_⊴_; posW-pr; kpR; node≼ʳ; node≼)
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
ψ : (ℓ : L) → Ok ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j
ψ ℓ o = TB.ψ ℓ o (MT.rbᶻ ℓ)
cb : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (B : Base (nd s h)) (c : Ch s) (x : Tr (nd s h)) → Base (h c)
cb s h o B c x i u = ψ (nd s h) o B i (inc c u) (B i (inc c u)) x

infl : (ℓ : L) → NoΩ ℓ → (o : Ok ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) (x : Tr ℓ) {a : Tr j}
      → Le j a (proj₁ β) → Le j a (proj₁ (ψ ℓ o B j w β x))
infl ℓ ν o B j w β zero      d = d
infl ℓ ν o B j w β (suc x)   d = ≼l 0 (infl ℓ ν o B j w β x d)
infl ℓ ν o B j w β (lim f a) d = ≼l 0 (infl ℓ ν o B j w β (f 0) d)
infl ℓ ν o B j w β (Ω p g)   d = node≼ʳ (kp ℓ o p w) _ _ (infl ℓ ν o B j w β (g (fromBr ℓ p zero)) d)
infl (nd s h) ν o B _ self β (up x c y e) d =
  ≼Up (h c) (down stop c) (ψ (nd s h) o B _ self β x) y (infl (nd s h) ν o B _ self β x d)
infl (nd sS h) ν o B j (inu ws) β (up x c y e) d =
  infl (h c) ν (proj₂ o c) (cb sS h o B c x) j (ws c) (ψ (nd sS h) o B j (inu ws) β x) y (infl (nd sS h) ν o B j (inu ws) β x d)
infl (nd sL g) ν o B j (inu ws) β (up x c y e) d =
  infl (g c) (ν c) (proj₂ o c) (cb sL g o B c x) j (ws c) (ψ (nd sL g) o B j (inu ws) β x) y (infl (nd sL g) ν o B j (inu ws) β x d)
infl (nd sS h) ν o B j (inc c′ v) β (up x c y e) d =
  infl (h c) ν (proj₂ o c) (cb sS h o B c x) j v (ψ (nd sS h) o B j (inc c′ v) β x) y (infl (nd sS h) ν o B j (inc c′ v) β x d)
infl (nd sL g) ν o B j (inc n v) β (up x m y e) {a} d =
  cW-ind (λ Z → Le j a (proj₁ Z)) (way g (proj₁ o) m n)
    (λ u → infl (g n) (ν n) (proj₂ o n) (cb sL g o B n x) j v (ψ (nd sL g) o B j (inc n v) β x)
             (proj₁ (emb (g n) (proj₂ o n) u (y , e))) (infl (nd sL g) ν o B j (inc n v) β x d))
    (λ u → infl (g m) (ν m) (proj₂ o m) (cb sL g o B m x) j (v ∙ u) (ψ (nd sL g) o B j (inc n v) β x) y
             (infl (nd sL g) ν o B j (inc n v) β x d))
infl (nd (sΩ k) h) () o B j w β (up x c y e) d

fl : (ℓ : L) → NoΩ ℓ → (o : Ok ℓ) (B B′ : Base ℓ) → B ⊴ B′ → (j : L) (w : j ≤ ℓ) (β β′ : Tr⁺ j)
    → Le j (proj₁ β) (proj₁ β′) → {x x′ : Tr ℓ} → Le ℓ x x′
    → Le j (proj₁ (ψ ℓ o B j w β x)) (proj₁ (ψ ℓ o B′ j w β′ x′))
fl ℓ ν o B B′ hB j w β β′ hβ {x′ = x′} z≼ = infl ℓ ν o B′ j w β′ x′ hβ
fl ℓ ν o B B′ hB j w β β′ hβ (s≼s d)  = next≼ _ _ (fl ℓ ν o B B′ hB j w β β′ hβ d)
fl ℓ ν o B B′ hB j w β β′ hβ (≼s d)   = ≼l 0 (fl ℓ ν o B B′ hB j w β β′ hβ d)
fl ℓ ν o B B′ hB j w β β′ hβ (≼l n d) = ≼l n (fl ℓ ν o B B′ hB j w β β′ hβ d)
fl ℓ ν o B B′ hB j w β β′ hβ (l≼ h)   = l≼ (λ n → fl ℓ ν o B B′ hB j w β β′ hβ (h n))
fl ℓ ν o B B′ hB j w β β′ hβ (≼w {p = p} d) = node≼ʳ (kp ℓ o p w) _ _ (fl ℓ ν o B B′ hB j w β β′ hβ d)
fl ℓ ν o B B′ hB j w β β′ hβ (w≼w {p = p} {g = g} {g′ = g′} h) =
  node≼ (LB ℓ p) (kp ℓ o p w) (kpR ℓ o p w)
    (λ z → ψ ℓ o B j w β (g z)) (λ z → ψ ℓ o B′ j w β′ (g′ z))
    (λ z → fromBr ℓ p (proj₁ (ψ ℓ o B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z))))
    (λ z → fromBr ℓ p (proj₁ (ψ ℓ o B′ (at ℓ p) (posW ℓ p) (B′ (at ℓ p) (posW ℓ p)) (g′ z))))
    (fromBr≼ ℓ p z≼)
    (λ z z′ r → fl ℓ ν o B B′ hB j w β β′ hβ (h z z′ r))
    (λ z z′ r → fromBr≼ ℓ p (fl ℓ ν o B B′ hB (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (B′ (at ℓ p) (posW ℓ p))
                               (hB (at ℓ p) (posW ℓ p) (posW-pr ℓ p)) (h z z′ r)))
-- 右边多一层嵌入
fl (nd s h) ν o B B′ hB _ self β β′ hβ (≼u {x = x} {c = c} {y = y} d) =
  ≼Up (h c) (down stop c) (ψ (nd s h) o B′ _ self β′ x) y (fl (nd s h) ν o B B′ hB _ self β β′ hβ d)
fl (nd sS h) ν o B B′ hB j (inu ws) β β′ hβ (≼u {x = x} {c = c} {y = y} d) =
  infl (h c) ν (proj₂ o c) (cb sS h o B′ c x) j (ws c) (ψ (nd sS h) o B′ j (inu ws) β′ x) y
       (fl (nd sS h) ν o B B′ hB j (inu ws) β β′ hβ d)
fl (nd sL g) ν o B B′ hB j (inu ws) β β′ hβ (≼u {x = x} {c = c} {y = y} d) =
  infl (g c) (ν c) (proj₂ o c) (cb sL g o B′ c x) j (ws c) (ψ (nd sL g) o B′ j (inu ws) β′ x) y
       (fl (nd sL g) ν o B B′ hB j (inu ws) β β′ hβ d)
fl (nd sS h) ν o B B′ hB j (inc c′ v) β β′ hβ (≼u {x = x} {c = c} {y = y} d) =
  infl (h c) ν (proj₂ o c) (cb sS h o B′ c x) j v (ψ (nd sS h) o B′ j (inc c′ v) β′ x) y
       (fl (nd sS h) ν o B B′ hB j (inc c′ v) β β′ hβ d)
fl (nd sL g) ν o B B′ hB j (inc n v) β β′ hβ {x = a} (≼u {x = x} {c = m} {y = y} {e = e} d) =
  cW-ind (λ Z → Le j (proj₁ (ψ (nd sL g) o B j (inc n v) β a)) (proj₁ Z)) (way g (proj₁ o) m n)
    (λ u → infl (g n) (ν n) (proj₂ o n) (cb sL g o B′ n x) j v (ψ (nd sL g) o B′ j (inc n v) β′ x)
             (proj₁ (emb (g n) (proj₂ o n) u (y , e))) (fl (nd sL g) ν o B B′ hB j (inc n v) β β′ hβ d))
    (λ u → infl (g m) (ν m) (proj₂ o m) (cb sL g o B′ m x) j (v ∙ u) (ψ (nd sL g) o B′ j (inc n v) β′ x) y
             (fl (nd sL g) ν o B B′ hB j (inc n v) β β′ hβ d))
-- 两边都是同一个孩子的嵌入
fl (nd s h) ν o B B′ hB _ self β β′ hβ (u≼u {x = x} {x′ = x′} {c = c} dx dy) =
  Up≼ (h c) (down stop c) (ψ (nd s h) o B _ self β x) (ψ (nd s h) o B′ _ self β′ x′) (fl (nd s h) ν o B B′ hB _ self β β′ hβ dx) dy
fl (nd sS h) ν o B B′ hB j (inu ws) β β′ hβ (u≼u {x = x} {x′ = x′} {c = c} dx dy) =
  fl (h c) ν (proj₂ o c) (cb sS h o B c x) (cb sS h o B′ c x′)
     (λ i u _ → fl (nd sS h) ν o B B′ hB i (inc c u) (B i (inc c u)) (B′ i (inc c u)) (hB i (inc c u) tt) dx)
     j (ws c) (ψ (nd sS h) o B j (inu ws) β x) (ψ (nd sS h) o B′ j (inu ws) β′ x′)
     (fl (nd sS h) ν o B B′ hB j (inu ws) β β′ hβ dx) dy
fl (nd sL g) ν o B B′ hB j (inu ws) β β′ hβ (u≼u {x = x} {x′ = x′} {c = c} dx dy) =
  fl (g c) (ν c) (proj₂ o c) (cb sL g o B c x) (cb sL g o B′ c x′)
     (λ i u _ → fl (nd sL g) ν o B B′ hB i (inc c u) (B i (inc c u)) (B′ i (inc c u)) (hB i (inc c u) tt) dx)
     j (ws c) (ψ (nd sL g) o B j (inu ws) β x) (ψ (nd sL g) o B′ j (inu ws) β′ x′)
     (fl (nd sL g) ν o B B′ hB j (inu ws) β β′ hβ dx) dy
fl (nd sS h) ν o B B′ hB j (inc c′ v) β β′ hβ (u≼u {x = x} {x′ = x′} {c = c} dx dy) =
  fl (h c) ν (proj₂ o c) (cb sS h o B c x) (cb sS h o B′ c x′)
     (λ i u _ → fl (nd sS h) ν o B B′ hB i (inc c u) (B i (inc c u)) (B′ i (inc c u)) (hB i (inc c u) tt) dx)
     j v (ψ (nd sS h) o B j (inc c′ v) β x) (ψ (nd sS h) o B′ j (inc c′ v) β′ x′)
     (fl (nd sS h) ν o B B′ hB j (inc c′ v) β β′ hβ dx) dy
fl (nd sL g) ν o B B′ hB j (inc n v) β β′ hβ (u≼u {x = x} {x′ = x′} {c = m} {y = y} {y′ = y′} {e = e} {e′ = e′} dx dy) =
  cW-ind₂ (λ Z Z′ → Le j (proj₁ Z) (proj₁ Z′)) (way g (proj₁ o) m n)
    (λ u → fl (g n) (ν n) (proj₂ o n) (cb sL g o B n x) (cb sL g o B′ n x′)
             (λ i u′ _ → fl (nd sL g) ν o B B′ hB i (inc n u′) (B i (inc n u′)) (B′ i (inc n u′)) (hB i (inc n u′) tt) dx)
             j v (ψ (nd sL g) o B j (inc n v) β x) (ψ (nd sL g) o B′ j (inc n v) β′ x′)
             (fl (nd sL g) ν o B B′ hB j (inc n v) β β′ hβ dx)
             (emb≼ (g n) (proj₂ o n) u {y = y , e} {y′ = y′ , e′} dy))
    (λ u → fl (g m) (ν m) (proj₂ o m) (cb sL g o B m x) (cb sL g o B′ m x′)
             (λ i u′ _ → fl (nd sL g) ν o B B′ hB i (inc m u′) (B i (inc m u′)) (B′ i (inc m u′)) (hB i (inc m u′) tt) dx)
             j (v ∙ u) (ψ (nd sL g) o B j (inc n v) β x) (ψ (nd sL g) o B′ j (inc n v) β′ x′)
             (fl (nd sL g) ν o B B′ hB j (inc n v) β β′ hβ dx) dy)
fl (nd (sΩ k) h) () o B B′ hB j w β β′ hβ (≼u d)
fl (nd (sΩ k) h) () o B B′ hB j w β β′ hβ (u≼u dx dy)
```
