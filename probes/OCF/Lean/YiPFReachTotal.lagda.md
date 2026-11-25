# 可达分支闭包在 Ok 层的总化
不读记号；编译定理：当前 W 在每个 Ok 层包含所有树；不否定所有阶段无关域。
任意满足所列种子、前驱、孩子及回灌输出闭包的域族均如此；不需要 visit 字段。
来源：独立复核提出的带任意孩子的 Ω 下界底，原六文件保持冻结；本文件不增加第三种域方案。
入口：`output-total-ok`、`w-total-ok`、`w-total-tw`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPFReachTotal where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.YiRWBlock hiding (D; B)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow using (Rb; ψ; rb-no)
open import OCF.Lean.YiPFReach using (W; OKᵀ)
import OCF.Lean.YiPFReach as W

S : L → L
S ℓ = nd sS (λ _ → ℓ)

record OutputClosed (Q : (ℓ : L) → Tr ℓ → Set) : Set where
  field
    rootᵒ : ∀ ℓ → Q ℓ (proj₁ (Ωt ℓ))
    belowᵒ : ∀ {ℓ x y} → Q ℓ y → ℓ ⊢ x ◃ y → Q ℓ x
    childᵒ : ∀ {s h x c y e} → Q (nd s h) (up x c y e) → Q (h c) y
    outputᵒ : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OKᵀ B
      → (p : Pos ℓ) (g : Br ℓ p → Tr ℓ) → Q ℓ (Ω p g)
      → ∀ n → Q (at ℓ p) (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p)
          (B (at ℓ p) (posW ℓ p)) (g (W.chain ℓ o r B p g n))))

closedᵂ : OutputClosed W
closedᵂ = record { rootᵒ = W.root ; belowᵒ = W.below ; childᵒ = W.child ; outputᵒ = W.output }

module Proof (Q : (ℓ : L) → Tr ℓ → Set) (cl : OutputClosed Q) (ℓ : L) (o : Ok ℓ) (x : Tr ℓ) where
  open OutputClosed cl
  a : L
  a = S ℓ

  H : L
  H = S a

  oa : Ok a
  oa = tt , λ _ → o

  oh : Ok H
  oh = tt , λ _ → oa

  e : ℓ ⊢ zero ◃ suc x
  e = z◃ x ◃s

  b : Tr⁺ a
  b = up (proj₁ (Ωt a)) tt (suc x) e , ◃t (proj₂ (Ωt a)) (◃u (proj₁ (Ωt a)) tt (suc x) e)

  Ba : Base a
  Ba .a self = b
  Ba j (inc c u) = Ωt j
  Ba j (inu us) = Ωt j

  Ba-ok : OKᵀ Ba
  Ba-ok .a self = inj₂ (◃u (proj₁ (Ωt a)) tt (suc x) e)
  Ba-ok j (inc c u) = inj₁ refl
  Ba-ok j (inu us) = inj₁ refl

  B : Base H
  B .H self = Ωt H
  B j (inc c u) = Ba j u
  B j (inu us) = Ωt j

  B-ok : OKᵀ B
  B-ok .H self = inj₁ refl
  B-ok j (inc c u) = Ba-ok j u
  B-ok j (inu us) = inj₁ refl

  p : Pos H
  p = inj₂ (tt , inj₁ tt)

  g : Br H p → Tr H
  g c = up zero tt (suc c) (z◃ c ◃s)

  first-output : (r : Rb H) → Q a (proj₁ (next⁺ b))
  first-output r = outputᵒ H oh r B B-ok p g (rootᵒ H) 0

  b-in : Q a (proj₁ b)
  b-in = belowᵒ (first-output (rb-no H)) (◃l 0)

  result : Q ℓ x
  result = belowᵒ (childᵒ b-in) ◃s

output-total-ok : ∀ {Q} → OutputClosed Q → ∀ ℓ → Ok ℓ → ∀ (x : Tr ℓ) → Q ℓ x
output-total-ok {Q} cl ℓ o x = Proof.result Q cl ℓ o x

w-total-ok : ∀ ℓ → Ok ℓ → ∀ (x : Tr ℓ) → W ℓ x
w-total-ok = output-total-ok closedᵂ

w-total-tw : ∀ n (x : Tr (tw n)) → W (tw n) x
w-total-tw n = w-total-ok (tw n) (Ok-tw n)

no-exclusion-ok : ∀ {Q} → OutputClosed Q → ∀ ℓ → Ok ℓ → ∀ x → (Q ℓ x → ⊥) → ⊥
no-exclusion-ok cl ℓ o x outside = outside (output-total-ok cl ℓ o x)
```
