# YiLvFold 第 1 站：只读裸层号的派发，有限层号上的闭项

**判决 (编译定理)：派发 `wayᵇ` 按层号的形状算出，不读证书；它在有限层号上完全 (`complete-fin`：有槽位就保留)。
对一切 `n`，`ψ₀ (Ω̂ (sucⁿ 0))` 合法 (`foldᶠ-legal`)；`ψ₀ (Ω̂ ω)` 合法 (`fold-Ωω-legal`)。** 读法 ψ₀(Ω_n), ψ₀(Ω_ω)，没有值的定理。
`wayᵇ` 在极限目标层上只认 `f (j+1) = suc (sucʲ 0)` 这一种形状，见 [YiLvFoldLim](YiLvFoldLim.lagda.md)。折叠在 [YiLvFold](YiLvFold.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLvFoldFin where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Maybe.Base using (Maybe; just; nothing; map)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; trans)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (Ω̂; cO; cO-Lgl; cO-Nested; up)
open import OCF.Align.YiIrrIf using (R; CP; self; suc; Legal; iterate)
open import OCF.Align.YiIrrFoldSeed using (Seedᶠ; seed-Ω̂)
open import OCF.Align.YiIrrNegLegal using (Legal-Ω̂)
open import OCF.Align.YiIrrFbIf using (Pt; pt; at)
open import OCF.Align.YiLvIf using (Plain; lev; upT-onlyP)
open import OCF.Align.YiLvFoldAdd
open import OCF.Align.YiLvFoldBase
open import OCF.Align.YiLvFold
```

## 1 派发

`eqᶠ` 只在两边都是字面的 `sucⁿ 0` 时回答相等。目标层 `suc m`：结点层号等于 `m` 则槽位 `inj₁`，否则到 `m` 里找。
目标层 `lim f`：只看第 `j+1` 支 (`j` 是结点层号头上的后继个数)，那一支字面是 `suc k` 才保留。`keep` 自带 `lev m s ≡ k`，
所以保留总是对的；会错的只有该保留而折叠。

```agda
fin : ℕ → LF
fin zero = zero
fin (suc n) = suc (fin n)

ω : LF
ω = lim fin

eqᶠ : (a b : LF) → Maybe (a ≡ b)
eqᶠ zero zero = just refl
eqᶠ (suc a) (suc b) = map (cong suc) (eqᶠ a b)
eqᶠ _ _ = nothing

sizeᶠ : LF → ℕ
sizeᶠ (suc k) = suc (sizeᶠ k)
sizeᶠ _ = zero

slotOf : ∀ {a k} → a ≡ suc k → Σ (Pre a) λ r → lev a r ≡ k
slotOf refl = inj₁ tt , refl

stepˢ : ∀ {m k} → Maybe (m ≡ k) → Way m k → Way (suc m) k
stepˢ (just e) y = keep (inj₁ tt) e
stepˢ nothing (keep s e) = keep (inj₂ s) e
stepˢ nothing fold = fold

hitˡ : ∀ f k n → Maybe (f n ≡ suc k) → Way (lim f) k
hitˡ f k n (just e) = keep (n , proj₁ (slotOf e)) (proj₂ (slotOf e))
hitˡ f k n nothing = fold

wayᵇ : ∀ m k → Way m k
wayᵇ zero k = fold
wayᵇ (suc m) k = stepˢ (eqᶠ m k) (wayᵇ m k)
wayᵇ (lim f) k =
  hitˡ f k (suc (sizeᶠ k)) (eqᶠ (f (suc (sizeᶠ k))) (suc k))
wayᵇ (lc k₀ c w b t g) k = fold

open Fold wayᵇ public
```

## 2 有限层号上派发完全

```agda
IsKeep : ∀ {m k} → Way m k → Set
IsKeep (keep s e) = ⊤
IsKeep fold = ⊥

eqᶠ-fin : ∀ n → eqᶠ (fin n) (fin n) ≡ just refl
eqᶠ-fin zero = refl
eqᶠ-fin (suc n) = cong (map (cong suc)) (eqᶠ-fin n)

step-just : ∀ {m k} (z : Maybe (m ≡ k)) (y : Way m k) e → z ≡ just e →
  IsKeep (stepˢ z y)
step-just .(just e) y e refl = tt

step-keep : ∀ {m k} (z : Maybe (m ≡ k)) (y : Way m k) → IsKeep y →
  IsKeep (stepˢ z y)
step-keep (just e) y h = tt
step-keep nothing (keep s e) h = tt

complete-fin : ∀ i (s : Pre (fin i)) → IsKeep (wayᵇ (fin i) (lev (fin i) s))
complete-fin (suc i) (inj₁ _) = step-just _ _ refl (eqᶠ-fin i)
complete-fin (suc i) (inj₂ s) = step-keep _ _ (complete-fin i s)

-- 反过来: 保留时结点层号严格在目标层之下. 合起来, 有限层号上保留当且仅当 i = suc (e + j).
size-fin : ∀ j → sizeᶠ (fin j) ≡ j
size-fin zero = refl
size-fin (suc j) = cong suc (size-fin j)

fin-inj : ∀ {a b} → fin a ≡ fin b → a ≡ b
fin-inj {a} {b} e = trans (sym (size-fin a)) (trans (cong sizeᶠ e) (size-fin b))

slot-of : ∀ {m k} (y : Way m k) → IsKeep y → Σ (Pre m) λ s → lev m s ≡ k
slot-of (keep s e) h = s , e

lev-bound : ∀ i (s : Pre (fin i)) →
  Σ ℕ λ j → Σ ℕ λ e → (lev (fin i) s ≡ fin j) × (i ≡ suc (e + j))
lev-bound (suc n) (inj₁ _) = n , zero , refl , refl
lev-bound (suc n) (inj₂ r) =
  proj₁ (lev-bound n r) , suc (proj₁ (proj₂ (lev-bound n r))) ,
  proj₁ (proj₂ (proj₂ (lev-bound n r))) ,
  cong suc (proj₂ (proj₂ (proj₂ (lev-bound n r))))

bound-at : ∀ i j (s : Pre (fin i)) → lev (fin i) s ≡ fin j →
  Σ ℕ λ e → i ≡ suc (e + j)
bound-at i j s q =
  proj₁ (proj₂ (lev-bound i s)) ,
  subst (λ z → i ≡ suc (proj₁ (proj₂ (lev-bound i s)) + z))
    (fin-inj (trans (sym (proj₁ (proj₂ (proj₂ (lev-bound i s))))) q))
    (proj₂ (proj₂ (proj₂ (lev-bound i s))))

sound-fin : ∀ i j → IsKeep (wayᵇ (fin i) (fin j)) → Σ ℕ λ e → i ≡ suc (e + j)
sound-fin i j h =
  bound-at i j (proj₁ (slot-of (wayᵇ (fin i) (fin j)) h))
    (proj₂ (slot-of (wayᵇ (fin i) (fin j)) h))

slotᶠ : ∀ e j → Pre (fin (suc (e + j)))
slotᶠ zero j = inj₁ tt
slotᶠ (suc e) j = inj₂ (slotᶠ e j)

lev-slotᶠ : ∀ e j → lev (fin (suc (e + j))) (slotᶠ e j) ≡ fin j
lev-slotᶠ zero j = refl
lev-slotᶠ (suc e) j = lev-slotᶠ e j

keep-fin : ∀ e j → IsKeep (wayᵇ (fin (suc (e + j))) (fin j))
keep-fin e j =
  subst (λ k → IsKeep (wayᵇ (fin (suc (e + j))) k)) (lev-slotᶠ e j)
    (complete-fin (suc (e + j)) (slotᶠ e j))

-- 两个小测试 (有限测试): 等层与在上都折叠, 在下的槽位是算出来的.
test-same : wayᵇ (fin 2) (fin 2) ≡ fold
test-same = refl

test-above : wayᵇ (fin 1) (fin 3) ≡ fold
test-above = refl

test-below : wayᵇ (fin 3) (fin 1) ≡ keep (inj₂ (inj₁ tt)) refl
test-below = refl
```

## 3 闭项：一切有限层号与 ω

```agda
fin-plain : ∀ n → Plain (fin n)
fin-plain zero = tt
fin-plain (suc n) = fin-plain n

fin-legal : ∀ n → Legal (fin n)
fin-legal zero = tt
fin-legal (suc n) = fin-legal n

fin-seed : ∀ n → Seedᶠ (fin n)
fin-seed zero = tt
fin-seed (suc n) = fin-seed n

dom-Ω̂ : ∀ L → Plain L → Legal L → Seedᶠ L → Dom (Ω̂ L)
dom-Ω̂ L pl lg sd = upT-onlyP L pl , Legal-Ω̂ L lg , seed-Ω̂ L sd

dom-Ωᶠ : ∀ n → Dom (Ω̂ (fin n))
dom-Ωᶠ n = dom-Ω̂ (fin n) (fin-plain n) (fin-legal n) (fin-seed n)

foldᶠ : ℕ → R
foldᶠ n = ψ zero (Ω̂ (fin n)) (dom-Ωᶠ n)

foldᶠ-legal : ∀ n → Lgl zero (foldᶠ n)
foldᶠ-legal n = ψ-legal zero tt (Ω̂ (fin n)) (dom-Ωᶠ n)

-- Ω̂ (sucⁿ⁺¹ 0) 是层号 sucⁿ 0 的结点; 目标层 0 上它走链行, 链在 Raw (sucⁿ 0) 里, 对 n 一致.
Ωᶠ-branch : ∀ n (η : Raw (fin n)) → .(Gd (fin n) (cO (fin n)) η) → LF
Ωᶠ-branch n η e = up (fin n) η (proj₂ (proj₂ e))

Ωᶠ-form : ∀ n → Ω̂ (fin (suc n)) ≡
  lc (fin n) (cO (fin n)) (cO-Lgl (fin n)) (cO-Nested (fin n)) (Ω̂ (fin n))
    (Ωᶠ-branch n)
Ωᶠ-form n = refl

foldᶠ-row : ∀ n → foldᶠ (suc n) ≡
  G.lim (λ i → out zero (fin n) (cO (fin n)) _ _ (Ω̂ (fin n)) (Ωᶠ-branch n)
    (dom-Ωᶠ (suc n))
    (iterate (next (fin n) (cO (fin n)) _ _ (Ω̂ (fin n)) (Ωᶠ-branch n)
      (dom-Ωᶠ (suc n))) (startᴸ (fin n) (cO (fin n)) _ _) i))
foldᶠ-row n = refl

ω-plain : Plain ω
ω-plain = fin-plain

ω-legal : Legal ω
ω-legal = (λ n → suc self) , fin-legal

ω-seed : Seedᶠ ω
ω-seed = fin-seed

dom-Ωω : Dom (Ω̂ ω)
dom-Ωω = dom-Ω̂ ω ω-plain ω-legal ω-seed

fold-Ωω : R
fold-Ωω = ψ zero (Ω̂ ω) dom-Ωω

fold-Ωω-legal : Lgl zero fold-Ωω
fold-Ωω-legal = ψ-legal zero tt (Ω̂ ω) dom-Ωω

-- Ω̂ ω 里没有层号 ω 的结点: 它是各 Ω̂ (sucⁿ 0) 的极限, 折叠逐项.
fold-Ωω-row : fold-Ωω ≡ G.lim foldᶠ
fold-Ωω-row = refl

-- 一般目标层的输出也合法并带嵌套证据, 例如目标层 sucⁱ 0 上的 Ω̂ (sucⁿ 0).
foldᶠ-at : ∀ i n → Raw (fin i)
foldᶠ-at i n = ψ (fin i) (Ω̂ (fin n)) (dom-Ωᶠ n)

foldᶠ-at-legal : ∀ i n → Lgl (fin i) (foldᶠ-at i n)
foldᶠ-at-legal i n = ψ-legal (fin i) (fin-plain i) (Ω̂ (fin n)) (dom-Ωᶠ n)

foldᶠ-at-nested : ∀ i n → Nested (fin i) (foldᶠ-at i n)
foldᶠ-at-nested i n = ψ-nested (fin i) (Ω̂ (fin n)) (dom-Ωᶠ n)
```

## 4 层号 0 与 1 上的行

与 [YiIrrFbIf](YiIrrFbIf.lagda.md) 的 `FbRows` 同形的四行，都是 `refl`：保留行、层号 0 的链行、回灌行、层号 1 的链行；
`x + top` 在第 1 层展开成同一个结点。不同的两处：加法是 `plus` (与 `_+ʳ_`, `_+¹_` 逐点同方程，字面相等没有证)；
第 0 层 ω 倍的第 0 项是一份而不是零份。

```agda
keep-row₁ : ∀ c (w : Lgl zero c) (b : Nested zero c) t
  (g : (η : R) → .(Gd zero c η) → LF) (d : Dom (lc zero c w b t g)) →
  ψ (fin 1) (lc zero c w b t g) d ≡
  G.lc (inj₁ tt) c (ψ (fin 1) t (Node.first zero c w b t g d))
    (λ η e → ψ (fin 1) (g η e) (Node.branch zero c w b t g d η e))
keep-row₁ c w b t g d = refl

gt-row₀ : ∀ c (w : Lgl zero c) (b : Nested zero c) t
  (g : (η : R) → .(Gd zero c η) → LF) (d : Dom (lc zero c w b t g)) →
  ψ zero (lc zero c w b t g) d ≡
  G.lim (λ n → out zero zero c w b t g d
    (iterate (next zero c w b t g d) (startᴸ zero c w b) n))
gt-row₀ c w b t g d = refl

feedback-row₁ : ∀ c (w : Lgl (fin 1) c) (b : Nested (fin 1) c) t
  (g : (η : Raw (fin 1)) → .(Gd (fin 1) c η) → LF)
  (d : Dom (lc (fin 1) c w b t g)) →
  ψ zero (lc (fin 1) c w b t g) d ≡
  G.lim (λ n → out zero (fin 1) c w b t g d
    (iterate (next (fin 1) c w b t g d) (startᴸ (fin 1) c w b) n))
feedback-row₁ c w b t g d = refl

gt-row₁ : ∀ c (w : Lgl (fin 1) c) (b : Nested (fin 1) c) t
  (g : (η : Raw (fin 1)) → .(Gd (fin 1) c η) → LF)
  (d : Dom (lc (fin 1) c w b t g)) →
  ψ (fin 1) (lc (fin 1) c w b t g) d ≡
  G.lim (λ n → out (fin 1) (fin 1) c w b t g d
    (iterate (next (fin 1) c w b t g d) (startᴸ (fin 1) c w b) n))
gt-row₁ c w b t g d = refl

plus-top₁ : ∀ x → plus (fin 1) x G.top ≡
  G.lc (inj₁ tt) (cO zero) (G.suc x)
    (λ η e → add zero (shS (rawAlg (fin 1))) x η)
plus-top₁ x = refl
```
