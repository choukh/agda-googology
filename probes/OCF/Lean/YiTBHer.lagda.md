# 比较表: 塔各项上由孩子树的字面前缀读出的表

> 定义候选（摆脱侧，证据一类），未经作者采纳. 不改块, 不改折叠: 给 `YiTBRow.Rb (tw n)` 对一切 n 的闭项 `rbᴴ`. 比较从孩子树自身读出: `srch k c c′` 沿 c 的 "后继取前驱, 嵌入取左项" 下行, 遇到与 c′ 字面相等 (只判零与后继, `eqF`) 就给路径 ↑ c′ ⊑ ↑ c.
> 覆盖: c′ 是有限后继链且是 c 的字面前缀 (c 可以带嵌入) 的那些对, 以及对称的情形; ℕ 极限与 Ω 结点处不下行, 没有条目. 实例在塔第 1, 2 项 (`ent1`, `ent2`, `refl`).
> 不否定什么. 值没有测; 嵌套的孩子层号上的表取空表 (`rb-no`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTBHer where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiTBRow using (Rb; RbS; rb-no)
```

## 字面相等 (零与后继) 与前缀搜索

```agda
eqF : (k : L) (c c′ : Tr k) → Maybe (c′ ≡ c)
eqF k zero    zero     = just refl
eqF k (suc c) (suc c′) = map (cong suc) (eqF k c c′)
eqF k _       _        = nothing

orElse : {A : Set} → Maybe A → Maybe A → Maybe A
orElse (just a) _ = just a
orElse nothing  m = m

hit : (k : L) (c c′ : Tr k) → Maybe (c′ ≡ c) → Maybe (↑ k c′ ⊑ ↑ k c)
hit k c .c (just refl) = just self
hit k c c′ nothing     = nothing

srch : (k : L) (c c′ : Tr k) → Maybe (↑ k c′ ⊑ ↑ k c)
dsc  : (k : L) (c c′ : Tr k) → Maybe (↑ k c′ ⊑ ↑ k c)

srch k c c′ = orElse (hit k c c′ (eqF k c c′)) (dsc k c c′)

dsc k        zero           c′ = nothing
dsc k        (suc x)        c′ = map (inc tt) (srch k x c′)
dsc k        (lim f a)      c′ = nothing
dsc k        (Ω p g)        c′ = nothing
dsc (nd s h) (up x cc y e)  c′ = map (λ p → p ∙ lift (↑ (nd s h) x) (↑ (h cc) y)) (srch (nd s h) x c′)
```

## 表, 对塔的一切项

```agda
tbᴴ : (n : ℕ) (c c′ : Tr (tw n))
    → Maybe (((tw n ⊕ ↑ (tw n) c′) ≤ (tw n ⊕ ↑ (tw n) c)) ⊎ ((tw n ⊕ ↑ (tw n) c) ≤ (tw n ⊕ ↑ (tw n) c′)))
tbᴴ n c c′ = orElse (map (λ p → inj₁ (wk (⊕⊑ (tw n) p))) (srch (tw n) c c′))
                    (map (λ p → inj₂ (wk (⊕⊑ (tw n) p))) (srch (tw n) c′ c))

rbᴴ : (n : ℕ) → Rb (tw n)
rbᴴ zero    = tt
rbᴴ (suc n) = tbᴴ n , λ c → rb-no (tw n ⊕ ↑ (tw n) c)
```

## 实例

```agda
ent1 : tbᴴ 0 (suc (suc (suc zero))) (suc (suc zero)) ≡ just (inj₁ (inc tt self))
ent1 = refl

ent1′ : tbᴴ 0 (suc zero) (suc (suc zero)) ≡ just (inj₂ (inc tt self))
ent1′ = refl

one₁ : Tr (tw 1)
one₁ = suc zero

emb₁ : Tr (tw 1)
emb₁ = up one₁ zero (suc zero) ◃s

ent2 : tbᴴ 1 emb₁ one₁ ≡ just (inj₁ (inu (λ _ → self)))
ent2 = refl

ent-lim : ∀ f a → tbᴴ 0 (lim f a) (suc (suc zero)) ≡ nothing
ent-lim f a = refl
```

`eqF` 的类型是 `YiAbsObs.viaE→dec` 里证据函数的类型 (`Maybe (c′ ≡ c)`), 但对角线在 ℕ 极限处为空, 所以不是自反的证据函数; 表也不声称 "指定孩子的交接" (`Same`).

```agda
eqF-lim : ∀ f a → eqF zero (lim f a) (lim f a) ≡ nothing
eqF-lim f a = refl
```
