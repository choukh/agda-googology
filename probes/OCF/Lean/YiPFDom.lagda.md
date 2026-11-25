# 全层 Ω 种子的前驱闭包域
不读记号；编译定义与定理：阶段无关的最小闭包 `D` 包含所有树，故不能收窄量化域。
域取 Ω 种子、第一位置前驱、Ω 分支、嵌入孩子及回灌输出；不改树、折叠或合法性。
来源：回灌逐字据 `YiLKIface.feed`，总域证明只用后继形状的 Ω 树，不用回灌。
入口：`D`、`seed-children-total`、`all-in`、`least`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPFDom where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.YiRWBlock hiding (D)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow using (Rb; ψ)

feedᴰ : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (p : Pos ℓ)
  → (Br ℓ p → Tr ℓ) → Br ℓ p → Br ℓ p
feedᴰ ℓ o r B p g c = fromBr ℓ p
  (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g c)))

data D : (ℓ : L) → Tr ℓ → Set where
  root : ∀ ℓ → D ℓ (proj₁ (Ωt ℓ))
  below : ∀ {ℓ x y} → D ℓ y → ℓ ⊢ x ◃ y → D ℓ x
  branch : ∀ {ℓ p g} → D ℓ (Ω p g) → ∀ c → D ℓ (g c)
  child : ∀ {s h x c y e} → D (nd s h) (up x c y e) → D (h c) y
  feed-out : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (p : Pos ℓ) (g : Br ℓ p → Tr ℓ)
    → D ℓ (Ω p g) → ∀ c → D (at ℓ p)
        (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g c)))

zero-in : ∀ ℓ → D ℓ zero
zero-in ℓ = below (root ℓ) (proj₂ (Ωt ℓ))

suc-inv : ∀ {ℓ x} → D ℓ (suc x) → D ℓ x
suc-inv d = below d ◃s

lim-inv : ∀ {ℓ f a} → D ℓ (lim f a) → ∀ n → D ℓ (f n)
lim-inv d n = below d (◃l n)

seed-children-total : (Q : (ℓ : L) → Tr ℓ → Set)
  → (∀ ℓ → Q ℓ (proj₁ (Ωt ℓ)))
  → (∀ {ℓ p g} → Q ℓ (Ω p g) → ∀ c → Q ℓ (g c))
  → (∀ {s h x c y e} → Q (nd s h) (up x c y e) → Q (h c) y)
  → (∀ {ℓ x} → Q ℓ (suc x) → Q ℓ x)
  → ∀ ℓ x → Q ℓ x
seed-children-total Q rt br ch si ℓ x = si
  (ch {s = sS} {h = λ _ → ℓ} {x = zero} {c = tt} {y = suc x}
    {e = z◃ x ◃s} (br (rt (nd sS (λ _ → ℓ))) x))

all-in : ∀ ℓ (x : Tr ℓ) → D ℓ x
all-in = seed-children-total D root branch child suc-inv

record Closed (Q : (ℓ : L) → Tr ℓ → Set) : Set where
  field
    rootᶜ : ∀ ℓ → Q ℓ (proj₁ (Ωt ℓ))
    belowᶜ : ∀ {ℓ x y} → Q ℓ y → ℓ ⊢ x ◃ y → Q ℓ x
    branchᶜ : ∀ {ℓ p g} → Q ℓ (Ω p g) → ∀ c → Q ℓ (g c)
    childᶜ : ∀ {s h x c y e} → Q (nd s h) (up x c y e) → Q (h c) y
    feedᶜ : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (p : Pos ℓ) (g : Br ℓ p → Tr ℓ)
      → Q ℓ (Ω p g) → ∀ c → Q (at ℓ p)
          (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g c)))

closed : Closed D
closed = record { rootᶜ = root ; belowᶜ = below ; branchᶜ = branch ; childᶜ = child ; feedᶜ = feed-out }

least : ∀ {Q} → Closed Q → ∀ {ℓ x} → D ℓ x → Q ℓ x
least q (root ℓ) = Closed.rootᶜ q ℓ
least q (below d e) = Closed.belowᶜ q (least q d) e
least q (branch d c) = Closed.branchᶜ q (least q d) c
least q (child d) = Closed.childᶜ q (least q d)
least q (feed-out ℓ o r B p g d c) = Closed.feedᶜ q ℓ o r B p g (least q d) c

closed-total : ∀ {Q} → Closed Q → ∀ ℓ x → Q ℓ x
closed-total q ℓ x = least q (all-in ℓ x)

no-exclusion : ∀ {Q} → Closed Q → ∀ {ℓ x} → (Q ℓ x → ⊥) → ⊥
no-exclusion q {ℓ} {x} outside = outside (closed-total q ℓ x)
```
