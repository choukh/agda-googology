# 字面上界: 带来源的折叠 (无语法, 无总判决)

> 不含记号. 结论写在 [InaccFloor](InaccFloor.lagda.md). 检验在 [InaccFloorAccept](InaccFloorAccept.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccFloorTree where

open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.InaccTreeBase
```

## §1 有限目标: 对全部原始层号正确

目标是自然数时, 比较是结构的, 不需要界: $j\cong n$ 只看 $j$ 的头. `limᴼ` 与 `lim` 都不 $\cong$ 任何自然数, 所以答 `rise`. 这对一切原始的 $j$ 成立 (`finD-rise`, `finD-pen`), 不受 `noBT` 影响, 因为 `noBT` 用的是极限目标.

```agda
natL : ℕ → Lv
natL zero    = zero
natL (suc n) = suc (natL n)

isN : ∀ j n → Maybe (j ≡ natL n)
isN zero    zero    = just refl
isN (suc j) (suc n) with isN j n
... | just refl = just refl
... | nothing   = nothing
isN _ _ = nothing

finD : ∀ j n → Verdict j (natL n)
finD j zero    = rise
finD j (suc n) with isN j n
... | just refl = pen (inj₁ tt) (λ y → y)
... | nothing with finD j n
...   | pen r b = pen (inj₂ r) b
...   | rise    = rise
```

## §2 字面路径

`Sib`: 树侧说不清的情形. **只有**两条路径在同一个 `lim` 或 `limᴼ` 的不同分支上时才问它. 这是一个参数, 不是判决的实现; 下面 §5 用 `∀ S` 的 `refl` 证明路径上它没有被问到.

```agda
Sib : Set
Sib = (j i : Lv) → Verdict j i

-- 节点是 0: 不问 `S`. 目标里字面的 0 路径就是穿透 (对 `Lv` 结构递归)
zp : (i : Lv) → Maybe (Σ (Pre i) λ r → at i r ≡ zero)
zp zero       = nothing
zp (suc zero) = just (inj₁ tt , refl)
zp (suc (suc i)) with zp (suc i)
... | just (r , e) = just (inj₂ r , e)
... | nothing      = nothing
zp (suc (lim h)) with zp (lim h)
... | just (r , e) = just (inj₂ r , e)
... | nothing      = nothing
zp (suc (limᴼ k g)) with zp (limᴼ k g)
... | just (r , e) = just (inj₂ r , e)
... | nothing      = nothing
zp (lim h) with zp (h 0)
... | just (r , e) = just ((0 , r) , e)
... | nothing with zp (h 1)
...   | just (r , e) = just ((1 , r) , e)
...   | nothing      = nothing
zp (limᴼ zero g) = just (inj₁ (inj₁ tt) , refl)
zp (limᴼ (suc k) g) with zp (suc k)
... | just (r , e) = just (inj₁ (inj₂ r) , e)
... | nothing      = nothing
zp (limᴼ (lim h) g) with zp (lim h)
... | just (r , e) = just (inj₁ (inj₂ r) , e)
... | nothing      = nothing
zp (limᴼ (limᴼ k h) g) with zp (limᴼ k h)
... | just (r , e) = just (inj₁ (inj₂ r) , e)
... | nothing      = nothing

zv : (i : Lv) → Verdict zero i
zv i with zp i
... | just (r , e) = pen r (subst Ordᴸ e)
... | nothing      = rise

Sz : Sib → Sib
Sz S zero i = zv i
Sz S (suc j) i = S _ i
Sz S (lim f) i = S _ i
Sz S (limᴼ k g) i = S _ i

lit : Sib → (k : Lv) (r q : Pre k) → Verdict (at k r) (at k q)
lit S (suc k) (inj₁ _) _        = rise
lit S (suc k) (inj₂ r) (inj₁ _) = pen r (λ y → y)
lit S (suc k) (inj₂ r) (inj₂ q) = lit S k r q
lit S (lim f) (n , r) (m , q) with n ≟ m
... | yes refl = lit S (f n) r q
... | no _     = Sz S _ _
lit S (limᴼ k g) (inj₁ (inj₁ _)) (inj₁ _) = rise
lit S (limᴼ k g) (inj₁ (inj₂ r)) (inj₁ (inj₁ _)) = pen r (λ y → y)
lit S (limᴼ k g) (inj₁ (inj₂ r)) (inj₁ (inj₂ q)) = lit S k r q
lit S (limᴼ k g) (inj₁ _) (inj₂ _) = Sz S _ _
lit S (limᴼ k g) (inj₂ _) _        = Sz S _ _
```

## §3 折叠

`Mode k i` 记录目标 `i` 与树层 `k` 的**来源**. `fin`: 有限目标. `bel`: 树层在目标之下 (`Sim`, 永远穿透). `lt q`: 目标是树层的字面前驱. `sib`: 走过 `up` 之后目标落到了别的分支. 判决不从 `(j, i)` 反读任何东西: 路径是折叠一路带下来的.

```agda
data Mode (k i : Lv) : Set where
  fin : ∀ n → i ≡ natL n → Mode k i
  bel : Sim k i → Mode k i
  lt  : (q : Pre k) → i ≡ at k q → Mode k i
  sib : Mode k i

upM : ∀ {i} k d → Mode k i → Mode (down k d) i
upM k d (fin n e) = fin n e
upM k d (bel σ)   = bel (σ ∘σ ι k d)
upM (suc k) _ (lt (inj₁ _) refl) = bel (σ-id k)
upM (suc k) _ (lt (inj₂ q) e)    = lt q e
upM (lim f) m (lt (n , q) e) with n ≟ m
... | yes refl = lt q e
... | no _     = sib
upM (limᴼ k g) x (lt q e) = sib
upM k d sib = sib

verdict : Sib → ∀ {k i} → Mode k i → (r : Pre k) → Verdict (at k r) i
verdict S (fin n refl) r = finD _ n
verdict S {k} {i} (bel σ) r = pen (proj₁ (σ r)) (subst Ordᴸ (proj₂ (σ r)))
verdict S {k} (lt q refl) r = lit S k r q
verdict S sib r = Sz S _ _

-- 链的目标: 字面的自然数走 `fin`, 否则走路径
asN : (j : Lv) → Maybe (Σ ℕ λ n → j ≡ natL n)
asN zero    = just (zero , refl)
asN (suc j) with asN j
... | just (n , refl) = just (suc n , refl)
... | nothing         = nothing
asN (lim _)    = nothing
asN (limᴼ _ _) = nothing

chM : ∀ k (r : Pre k) → Mode k (at k r)
chM k r with asN (at k r)
... | just (n , e) = fin n e
... | nothing      = lt r refl

module PF (S : Sib) where
  ψᵖ : ∀ {k i} → Mode k i → Ordᴸ k → Ordᴸ i
  ψᵖ {i = i} m zero    = Ω i
  ψᵖ {i = i} m (suc a) = lim (iter (ψᵖ m a +_) zero)
  ψᵖ m (lim f) = lim (λ n → ψᵖ m (f n))
  ψᵖ {k} {i} m (limᵢ r f) with verdict S m r
  ... | pen r′ b = limᵢ r′ (λ y → ψᵖ m (f (intoL k r (b (outL i r′ y)))))
  ... | rise     = lim (λ n → ψᵖ m (f (intoL k r
                     (iter (λ x → ψᵖ (chM k r) (f (intoL k r x))) (Ω (at k r)) n))))
  ψᵖ {suc k}    m (up d x) = ψᵖ (upM (suc k) d m) x
  ψᵖ {lim f}    m (up d x) = ψᵖ (upM (lim f) d m) x
  ψᵖ {limᴼ k g} m (up d x) = ψᵖ (upM (limᴼ k g) d m) x

  -- ψ_n(x), 层号是 x 的层
  ψⁿ : ∀ n {k} → Ordᴸ k → Ordᴸ (natL n)
  ψⁿ n = ψᵖ (fin n refl)

  -- 第 5 站的一致族: θ ↦ ψ₁(Ω_θ), 对一切原始层号 θ
  F : Lv → Ordᴸ (natL 1)
  F θ = ψⁿ 1 (Ω θ)

  -- ψ₀(Ω_L)
  T : Lv → Ordᴸ zero
  T L = ψⁿ 0 (Ω L)

  -- 第 5 站: ψ₀(Ω_{ψ₁(Ω_Ω)})
  T₅ : Ordᴸ zero
  T₅ = T (toLv (F (toLv (Ω (natL 1)))))

  -- 起点: ψ₀(Ω_{Ω_Ω})
  TΩΩ : Ordᴸ zero
  TΩΩ = T (toLv (Ω (toLv (Ω (natL 1)))))
```
