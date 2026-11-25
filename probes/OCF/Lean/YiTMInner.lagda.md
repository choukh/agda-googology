# 树侧的内层封装
不读记号；变量行分解与每个内链点到整行的值界。
来源：YiE4Inner 的 g/feed/out 封装、YiE4Cut20.row0 的零层 Keep 消去；去掉验收导入。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTMInner where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (inj₁)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiVWVal as V

row0 : {X : Set} {z : X} (m : F.Keep B.zero X z) (G : X → O.Tr⁺ B.zero) (s : X → X)
  → F.node⁺ m G s ≡ O.limc⁺ (λ n → G (O.iter s z n))
row0 (just (() , _)) G s
row0 nothing G s = refl

right-⊹ : (a b : V.V B.zero) → b V.≼ a V.⊹ b
right-⊹ a V.zero = V.z≼
right-⊹ a (V.suc b) = V.s≼s (right-⊹ a b)
right-⊹ a (V.lim f) = V.l≼ (λ n → V.≼l n (right-⊹ a (f n)))
right-⊹ a (V.Ω () g)

-- perf: S-1/C-9，在变量层号上出生并封装，再由闭项实例化。
opaque
  collapse : (h : B.L) → P.Ok h → TB.Rb h → F.Base h → O.Tr⁺ B.zero → O.Tr⁺ B.zero
  collapse h o r bs β = TB.ψ h o r bs B.zero (P.z≤ h) β (proj₁ (O.Ωt h))
  collapse-eq : ∀ h o r bs β → collapse h o r bs β
    ≡ TB.ψ h o r bs B.zero (P.z≤ h) β (proj₁ (O.Ωt h))
  collapse-eq h o r bs β = refl

module Inner (k : B.L) (a : B.Tr k → B.L) (o : P.Ok (B.nd (B.sΩ k) a))
  (r : TB.Rb (B.nd (B.sΩ k) a)) (bs : F.Base (B.nd (B.sΩ k) a)) (β : O.Tr⁺ B.zero) where
  ℓ = B.nd (B.sΩ k) a
  opaque
    g : B.Tr k → B.Tr ℓ
    g d = proj₁ (O.upz {s = B.sΩ k} {h = a} d (O.Ωt (a d)))
    g-eq : g ≡ (λ d → proj₁ (O.upz {s = B.sΩ k} {h = a} d (O.Ωt (a d))))
    g-eq = refl
    feed : B.Tr k → B.Tr k
    feed d = proj₁ (TB.ψ ℓ o r bs k (P.ink P.self) (bs k (P.ink P.self)) (g d))
    feed-eq : feed ≡ (λ d → proj₁ (TB.ψ ℓ o r bs k (P.ink P.self) (bs k (P.ink P.self)) (g d)))
    feed-eq = refl
    out : B.Tr k → O.Tr⁺ B.zero
    out d = TB.ψ ℓ o r bs B.zero (P.z≤ ℓ) β (g d)
    out-eq : out ≡ (λ d → TB.ψ ℓ o r bs B.zero (P.z≤ ℓ) β (g d))
    out-eq = refl
  chain : ℕ → B.Tr k
  chain = O.iter feed B.zero
  opaque
    unfolding g feed out collapse
    row : collapse ℓ o r bs β ≡ O.limc⁺ (λ n → out (chain n))
    row = row0 (F.kp ℓ o (inj₁ (inj₁ tt)) (P.z≤ ℓ)) out feed
  point-cum : (n : ℕ) → V.val B.zero (proj₁ (out (chain n)))
    V.≼ V.val B.zero (O.cum (λ m → proj₁ (out (chain m))) n)
  point-cum zero = V.≼-refl _
  point-cum (suc n) = V.≼-trans
    (right-⊹ (V.val B.zero (O.cum (λ m → proj₁ (out (chain m))) n)) (V.val B.zero (proj₁ (out (chain (suc n))))))
    (Data.Product.proj₂ (V.val-+ (O.cum (λ m → proj₁ (out (chain m))) n) (proj₁ (out (chain (suc n))))))
  point-row : (n : ℕ) → V.val B.zero (proj₁ (out (chain n)))
    V.≼ V.val B.zero (proj₁ (collapse ℓ o r bs β))
  point-row n = subst (λ t → V.val B.zero (proj₁ (out (chain n))) V.≼ V.val B.zero (proj₁ t))
    (Relation.Binary.PropositionalEquality.sym row) (V.≼l n (point-cum n))
```
