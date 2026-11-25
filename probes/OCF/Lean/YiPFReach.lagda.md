# 实际回灌可达分支的闭包域
不读记号；编译域族 `W`，Ω 分支沿有 Ω 下界的底生成的实际回灌链访问。
保留第一位置前驱、嵌入孩子及实际链输出；未证明 W 是真子域，也未填全层保持律。
来源：链与下界形状据 `YiLKIface`；第 0 步实际链覆盖在 `YiPFReachCover`。
入口：`W`、`chain`、`w-to-d`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPFReach where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock hiding (D)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiPFDom using (feedᴰ)
import OCF.Lean.YiPFDom as Wide

OKᵀ : ∀ {ℓ} → Base ℓ → Set
OKᵀ B = ∀ i u → (proj₁ (Ωt i) ≡ proj₁ (B i u)) ⊎ (i ⊢ proj₁ (Ωt i) ◃ proj₁ (B i u))

base-ok : ∀ ℓ → OKᵀ (B₀ ℓ)
base-ok ℓ i u = inj₁ refl

chain : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (p : Pos ℓ) (g : Br ℓ p → Tr ℓ) → ℕ → Br ℓ p
chain ℓ o r B p g = iter (feedᴰ ℓ o r B p g) (fromBr ℓ p zero)

data W : (ℓ : L) → Tr ℓ → Set where
  root : ∀ ℓ → W ℓ (proj₁ (Ωt ℓ))
  below : ∀ {ℓ x y} → W ℓ y → ℓ ⊢ x ◃ y → W ℓ x
  child : ∀ {s h x c y e} → W (nd s h) (up x c y e) → W (h c) y
  visit : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OKᵀ B
    → (p : Pos ℓ) (g : Br ℓ p → Tr ℓ) → W ℓ (Ω p g)
    → ∀ n → W ℓ (g (chain ℓ o r B p g n))
  output : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OKᵀ B
    → (p : Pos ℓ) (g : Br ℓ p → Tr ℓ) → W ℓ (Ω p g)
    → ∀ n → W (at ℓ p) (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p)
        (B (at ℓ p) (posW ℓ p)) (g (chain ℓ o r B p g n))))

zero-in : ∀ ℓ → W ℓ zero
zero-in ℓ = below (root ℓ) (proj₂ (Ωt ℓ))

suc-inv : ∀ {ℓ x} → W ℓ (suc x) → W ℓ x
suc-inv d = below d ◃s

lim-inv : ∀ {ℓ f a} → W ℓ (lim f a) → ∀ n → W ℓ (f n)
lim-inv d n = below d (◃l n)

w-to-d : ∀ {ℓ x} → W ℓ x → Wide.D ℓ x
w-to-d (root ℓ) = Wide.root ℓ
w-to-d (below d e) = Wide.below (w-to-d d) e
w-to-d (child d) = Wide.child (w-to-d d)
w-to-d (visit ℓ o r B gb p g d n) = Wide.branch (w-to-d d) (chain ℓ o r B p g n)
w-to-d (output ℓ o r B gb p g d n) = Wide.feed-out ℓ o r B p g (w-to-d d) (chain ℓ o r B p g n)
```
