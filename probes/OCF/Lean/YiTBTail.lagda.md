# 兄弟孩子那一行: 去掉回退尾巴就不单调 (否定)

> 判决: 编译的否定定理, 无前提, 不读记号. `YiRBSib` 那一行在证据在时是 `headˢ ⊞ 回退项` (`row-split`, `refl`), 其中 `headˢ` (在孩子 c′ + c 的层上折该层的 Ω 树) 的写法里没有嵌入的孩子树 y. `notail`: 塔第 1 项上, 朝第 0 层经孩子 0, 任何在嵌入 `up x c y e` 上等于 `headˢ` 的函数都不单调. 一般形式 `nomono`: 在嵌入上不读 y 的函数不单调.
> 机制: `◃c` 给出同一 x, c 下 y′ ◃ y 的两个嵌入, 输出相同, 单调要求 t ◃ t; 第 0 层的 `◃` 良基 (`acc⁰`).
> 否定的是 "只去掉 ⊞ 回退项, 其余不动"; 不否定换成别的读 y 的项 (比较表那一行直接折 y, 没有尾巴, `YiTBRow`). 临时试验 (去尾后原样编译) 的首个错误在单调的 `◃c` 情形, 见回报.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTBTail where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiRBSib
```

## 第 0 层的 `◃` 良基

```agda
data Acc⁰ (x : Tr zero) : Set where
  acc : ((y : Tr zero) → zero ⊢ y ◃ x → Acc⁰ y) → Acc⁰ x

inv : ∀ {x} → Acc⁰ x → (y : Tr zero) → zero ⊢ y ◃ x → Acc⁰ y
inv (acc h) = h

below : (x y : Tr zero) → zero ⊢ y ◃ x → Acc⁰ y
below (suc x)   .x     ◃s        = acc (below x)
below (lim f a) .(f n) (◃l n)    = acc (below (f n))
below x         y      (◃t {y = z} d e) = inv (below x z e) y d

acc⁰ : (x : Tr zero) → Acc⁰ x
acc⁰ x = acc (below x)

irr : ∀ {x} → Acc⁰ x → zero ⊢ x ◃ x → ⊥
irr {x} (acc h) d = irr (h x d) d
```

## 在嵌入上不读 y 的函数不单调

```agda
c0 : Tr zero
c0 = zero

y₁ y₂ : Tr (zero ⊕ ↑ zero c0)
y₁ = suc zero
y₂ = suc (suc zero)

nomono : (G : Tr (tw 1) → Tr zero)
  → (∀ x c y e y′ e′ → G (up x c y e) ≡ G (up x c y′ e′))
  → (∀ {x y} → tw 1 ⊢ x ◃ y → zero ⊢ G x ◃ G y) → ⊥
nomono G cst mn =
  irr (acc⁰ _) (subst (λ t → zero ⊢ t ◃ G (up zero c0 y₂ (◃t ◃s ◃s))) (cst zero c0 y₁ ◃s y₂ (◃t ◃s ◃s))
                 (mn (◃c zero c0 {y′ = y₁} {y = y₂} {e′ = ◃s} {e = ◃t ◃s ◃s} ◃s)))
```

## 那一行拆成不读 y 的部分与回退项

```agda
headˢ : ∀ n (B : Base (tw (suc n))) j c′ (v : j ≤ (tw n ⊕ ↑ (tw n) c′)) (β : Tr⁺ j) (x : Tr (tw (suc n))) (c : Tr (tw n)) → Tr⁺ j
headˢ n B j c′ v β x c =
  ψ (tw n ⊕ ↑ (tw n) (c′ + c)) (proj₂ (Ok-tw (suc n)) (c′ + c)) (rb-no _)
    (λ i u → ψ (tw (suc n)) (Ok-tw (suc n)) (rb-tw (suc n)) B i (inc (c′ + c) u) (B i (inc (c′ + c) u)) x) j
    (v ∙ wk (⊕⊑ (tw n) (pre (tw n) c′ c)))
    (ψ (tw (suc n)) (Ok-tw (suc n)) (rb-tw (suc n)) B j (inc c′ v) β x) (proj₁ (Ωt (tw n ⊕ ↑ (tw n) (c′ + c))))

row-split : ∀ n (B : Base (tw (suc n))) j c′ (v : j ≤ (tw n ⊕ ↑ (tw n) c′)) β x c y e
  → ψ (tw (suc n)) (Ok-tw (suc n)) (rb-tw (suc n)) B j (inc c′ v) β (up x c y e)
  ≡ headˢ n B j c′ v β x c ⊞ ψ₀ʳ (tw n ⊕ ↑ (tw n) c) (proj₂ (Ok-tw (suc n)) c) (rb-no _) y
row-split n B j c′ v β x c y e = refl

notail : (G : Tr (tw 1) → Tr zero)
  → (∀ x c y e → G (up x c y e) ≡ proj₁ (headˢ 0 (B₀ (tw 1)) zero c0 self (Ωt zero) x c))
  → (∀ {x y} → tw 1 ⊢ x ◃ y → zero ⊢ G x ◃ G y) → ⊥
notail G eq mn = nomono G (λ x c y e y′ e′ → trans′ (eq x c y e) (eq x c y′ e′)) mn
  where
  trans′ : ∀ {A : Set} {a b c : A} → a ≡ b → c ≡ b → a ≡ c
  trans′ refl refl = refl
```

前提各自可满足: `G₀` 在嵌入上逐字等于 `headˢ` (`G₀-eq`); 带尾巴的折叠本身单调 (`YiRBSib.mono`).

```agda
G₀ : Tr (tw 1) → Tr zero
G₀ (up x c y e) = proj₁ (headˢ 0 (B₀ (tw 1)) zero c0 self (Ωt zero) x c)
G₀ _            = zero

G₀-eq : ∀ x c y e → G₀ (up x c y e) ≡ proj₁ (headˢ 0 (B₀ (tw 1)) zero c0 self (Ωt zero) x c)
G₀-eq x c y e = refl
```
