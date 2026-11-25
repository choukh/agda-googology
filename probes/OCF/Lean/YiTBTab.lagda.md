# 比较表: 塔第 1 项上带 ℕ 极限孩子的表

> 定义候选（摆脱侧，证据一类），未经作者采纳. 不改块, 不改折叠: 只给 `YiTBRow.Rb (tw 1)` 另一个闭项 `rbᶜ`. 一个孩子是字面自然数 `nat m` 时, 在另一个孩子里沿 "后继取前驱, ℕ 极限取第 m 项" 找 `fn m` 的字面路径 (`sub`), 找到就给比较.
> 覆盖: 自然数对自然数 (同 `rb1`); 自然数对含 ℕ 极限的孩子, 只要搜索到达字面自然数 (`ωᶜ`, `ωᵉ` 在内, `ent-ω`, `ent-ωᵉ`). 两个孩子都不是字面自然数时没有条目.
> 不否定什么. 值的验收在 [YiTBLim](YiTBLim.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTBTab where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiTBRow
```

## 在一个孩子里找 `fn m`

```agda
leN : (m n : ℕ) → Maybe (fn m ≤ fn n)
leN m n with way fn (λ i → inc tt self) n m
... | inj₁ _ = nothing
... | inj₂ u = just u

leI : ∀ {c} (m : ℕ) → IsNat c → Maybe (fn m ≤ h₁ c)
leI m (isn n) = leN m n

subS : (m : ℕ) (x : Tr zero) → Maybe (IsNat (suc x)) → Maybe (fn m ≤ h₁ x) → Maybe (fn m ≤ h₁ (suc x))
subS m x (just w) rec = leI m w
subS m x nothing  rec = map (inc tt) rec

sub : (m : ℕ) (c : Tr zero) → Maybe (fn m ≤ h₁ c)
sub m zero      = leN m 0
sub m (suc x)   = subS m x (isNat (suc x)) (sub m x)
sub m (lim f a) = map (inc m) (sub m (f m))
```

## 表

```agda
tbᶜ′ : (c c′ : Tr zero) → Maybe (IsNat c) → Maybe (IsNat c′) → Maybe ((h₁ c′ ≤ h₁ c) ⊎ (h₁ c ≤ h₁ c′))
tbᶜ′ _ _  (just (isn n)) (just (isn m)) = just (way fn (λ i → inc tt self) m n)
tbᶜ′ c _  nothing        (just (isn m)) = map inj₁ (sub m c)
tbᶜ′ _ c′ (just (isn n)) nothing        = map inj₂ (sub n c′)
tbᶜ′ _ _  nothing        nothing        = nothing

tbᶜ : (c c′ : Tr zero) → Maybe ((h₁ c′ ≤ h₁ c) ⊎ (h₁ c ≤ h₁ c′))
tbᶜ c c′ = tbᶜ′ c c′ (isNat c) (isNat c′)

rbᶜ : Rb (tw 1)
rbᶜ = tbᶜ , λ c → rb-no (h₁ c)
```

## 条目 (闭项上的计算)

```agda
ωᶜ : Tr zero
ωᶜ = lim nat (λ n → ◃s)

ent-ω : tbᶜ ωᶜ (nat 2) ≡ just (inj₁ (inc 2 self))
ent-ω = refl

ent-ω′ : tbᶜ (nat 2) ωᶜ ≡ just (inj₂ (inc 2 self))
ent-ω′ = refl

dbl : ℕ → Tr zero
dbl zero    = zero
dbl (suc n) = suc (suc (dbl n))

ωᵉ : Tr zero
ωᵉ = lim dbl (λ n → ◃t ◃s ◃s)

ent-ωᵉ : tbᶜ ωᵉ (nat 2) ≡ just (inj₁ (inc 2 (inc tt (inc tt self))))
ent-ωᵉ = refl

ent-ωω : tbᶜ ωᶜ ωᵉ ≡ nothing
ent-ωω = refl
```
