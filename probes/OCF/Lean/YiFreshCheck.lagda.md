# 空白页样本: J2 与 J3

> 判决: J2 是编译定理 (后继层与 ℕ 极限层: 一切目标与一切底; 一切层号含 `Ωₗ`: 到第 0 层的折叠); `Ωₗ` 层分支侧目标不在 J2 内 (见 `YiFreshFold` 文首退让).
> J3 是有限测试 (`refl`): 源层号是 ℕ 极限层号、目标层有其槽位的结点保留, 含塔的第 3 项与 Λ 的形状.
> `J2-Ωₗ-gap` 是有限反例: 分支侧目标上 J2 不成立 (本设计的默认分支所致). 不否定任何路线. 入口: `YiFreshFold`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFreshCheck where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; subst)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold
```

## J2: 嵌入分支里的折叠等于孩子层里的折叠

带任意底与任意偏移的形式 (底是偏移 x 的折叠), 与默认底、零偏移的形式.

```agda
J2-suc : (a : L) (B : Base (suc a)) (j : L) (w : j ≤ a) (x : Tr (suc a)) (y : Tr a)
  → ψs (suc a) B j (ins w) (up x tt y)
  ≡ ψs a (base (ψ⊥ (suc a) B x) (λ j′ w′ → ψs (suc a) B j′ (ins w′) x)) j w y
J2-suc a B j w x y = refl

J2-lim : (g : ℕ → L) (B : Base (lim g)) (n : ℕ) (j : L) (w : j ≤ g n)
         (x : Tr (lim g)) (y : Tr (g n))
  → ψs (lim g) B j (inl n w) (up x n y)
  ≡ ψs (g n) (base (ψ⊥ (lim g) B x) (λ j′ w′ → ψs (lim g) B j′ (inl n w′) x)) j w y
J2-lim g B n j w x y rewrite eqℕ-refl n = refl

J2₀-suc : (a : L) (j : L) (w : j ≤ a) (y : Tr a)
  → ψs (suc a) (B₀ (suc a)) j (ins w) (up zero tt y) ≡ ψs a (B₀ a) j w y
J2₀-suc a j w y = refl

J2₀-lim : (g : ℕ → L) (n : ℕ) (j : L) (w : j ≤ g n) (y : Tr (g n))
  → ψs (lim g) (B₀ (lim g)) j (inl n w) (up zero n y) ≡ ψs (g n) (B₀ (g n)) j w y
J2₀-lim g n j w y rewrite eqℕ-refl n = refl
```

到第 0 层的折叠对一切层号 (含 `Ωₗ`).

```agda
J2⊥ : (ℓ : L) (B : Base ℓ) (x : Tr ℓ) (c : Ch ℓ) (y : ChT ℓ c)
  → Σ (Base (chL ℓ c)) λ B′ → (b⊥ B′ ≡ ψ⊥ ℓ B x) × (ψ⊥ ℓ B (up x c y) ≡ ψ⊥ (chL ℓ c) B′ (chT ℓ c y))
J2⊥ (suc a)  B x c y = _ , refl , refl
J2⊥ (lim g)  B x n y = _ , refl , refl
J2⊥ (Ωₗ k h) B x c y = _ , refl , refl

J2₀⊥ : (ℓ : L) (c : Ch ℓ) (y : ChT ℓ c)
  → ψ₀ ℓ (up zero c y) ≡ ψ₀ (chL ℓ c) (chT ℓ c y)
J2₀⊥ (suc a)  c y = refl
J2₀⊥ (lim g)  n y = refl
J2₀⊥ (Ωₗ k h) c y = refl
```

## J3: 源层号为 ℕ 极限的结点保留 (有限测试)

ωₗ 是层号 ω; 结点在 ℓ 里的槽位落在 ℕ 极限层号上, 目标层有这个槽位.

```agda
fin : ℕ → L
fin zero    = zero
fin (suc n) = suc (fin n)

ωₗ : L
ωₗ = lim fin

J3-ω : ψs (suc (suc ωₗ)) (B₀ _) (suc ωₗ) (ins self) (Ω (inj₂ (inj₁ tt)) (λ _ → zero))
     ≡ Ω (inj₁ tt) (λ _ → Ωt (suc ωₗ))
J3-ω = refl
```

塔的第 3 项: c 是第 tw 2 层的树 ω+1, 分支层号 tw 2 ⊕ ↑c = (ℕ 极限) + 1; 结点在 tw 3 的分支 c 里、这个 ℕ 极限层号的槽位上 (`J3-src`).

```agda
finT : ℕ → Tr (tw 2)
finT zero    = zero
finT (suc n) = suc (finT n)

c₃ : Tr (tw 2)
c₃ = suc (lim finT)

p₃ : Pos (tw 3)
p₃ = inj₂ (c₃ , inj₂ (inj₁ tt))

J3-src : at (tw 3) p₃ ≡ lim (λ n → tw 2 ⊕ ↑ (tw 2) (finT n))
J3-src = refl

J3-tw3 : ψs (suc (tw 3)) (B₀ _) (tw 3) (ins self) (Ω (inj₂ p₃) (λ _ → zero))
       ≡ Ω p₃ (λ _ → Ωt (tw 3))
J3-tw3 = refl

J3-Λ : ψs (suc Λ) (B₀ _) Λ (ins self) (Ω (inj₂ (3 , inj₂ p₃)) (λ _ → zero))
     ≡ Ω (3 , inj₂ p₃) (λ _ → Ωt Λ)
J3-Λ = refl

J3-Λ-inl : ψs (suc Λ) (B₀ _) (tw 3) (ins (inl 3 self)) (Ω (inj₂ (3 , inj₂ p₃)) (λ _ → zero))
         ≡ Ω p₃ (λ _ → Ωt (tw 3))
J3-Λ-inl = refl
```

嵌入孩子里的同形结点, 目标是孩子层自身: 结点在保留的嵌入里原样留下.

```agda
J3-up : ψs (suc (suc (tw 3))) (B₀ _) (tw 3) (ins (ins self))
          (up zero tt (Ω (inj₂ p₃) (λ _ → zero)))
      ≡ Ω p₃ (λ _ → Ωt (tw 3))
J3-up = refl
```

## J2 在 `Ωₗ` 分支侧目标上不成立 (有限反例)

tw 1 的分支 c₁ = 1 的孩子层是 1; 目标经分支 c₁ 落到第 0 层. 折叠走 "无从比较" 的默认, 与孩子层折叠的第 0 项不同.

```agda
c₁ : Tr zero
c₁ = suc zero

hd : ∀ {P B C D} → T P B C D → T P B C D
hd (lim f) = f zero
hd x       = x

pr : ∀ {P B C D} → T P B C D → T P B C D
pr (suc x) = x
pr x       = x

isZ : ∀ {P B C D} → T P B C D → Set
isZ zero = ⊤
isZ _    = ⊥

J2-Ωₗ-gap : ψs (tw 1) (B₀ _) zero (inb c₁ (ins self)) (up zero c₁ (suc zero))
          ≢ ψs (suc zero) (B₀ _) zero (ins self) (suc zero)
J2-Ωₗ-gap e = subst isZ (cong (λ t → pr (hd t)) (sym e)) tt
```
