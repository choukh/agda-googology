# 留在孩子里, 底依赖左边: 塔第 2 项链第一步的值

> 验收文件. 编译定理, 无前提, 对任意底 B: 链第一步第 0 支折到第 0 层, (C′) 的输出 `up β₁ 0 (next 1)` 的值不高于 `β₁ + β₁` 的值 (`below2`), 从而不高于 (A) 的输出 `next β₁` 的值 (`br0-≼`); 用 (C′) 的折叠取值 (`ValC`) 与用 (A) 的折叠取值 (`ValA`) 各一条.
> 有限测试: 两边在第 0 层的形状 (`f-A`, `f-C′`, `f-C′₀`, `f-C′₁`); tw 1 这一站的链步在 c = 0 上 (A) 与 (C′) 逐字相同 (`tw1-same0`).
> 只有 "不高于", 没有证严格; 没有与参照比较 (本仓库已编译的参照下界只到 tw 1: `YiUpValTw1.bho-tw1`, 那是对 (A) 证的, 本篇没有对 (C′) 重证). 不否定任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOmCVal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Lean.YiFreshBlock renaming (L to LF)
open import OCF.Lean.YiFreshFold using (_+_; iter; next; cum; Ωt)
open import OCF.Lean.YiFreshLegal using (seq)
open import OCF.Lean.YiFreshValRead using (T₀; read; read-+; plus≽)
open import OCF.Lean.YiPhiBlock
import OCF.Lean.YiUpFold as A
import OCF.Lean.YiOmCFold as C′
open import OCF.Lean.YiOmCCheck using (ε₁; h₁; β₁; br; stepA; stepC′)

import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼l; l≼; ≼-refl; ≼-trans; ≅→≼; +-mono)
```

## 第 0 层的工具

`nx m b` 是 b 上做 m+1 次 `next`; `num m` 是第 0 层的数 m+1 (写成 `next 1` 的第 m 项). `next` 对值序单调.

```agda
nx : ℕ → Tr zero → Tr zero
nx zero    b = next b
nx (suc m) b = next (nx m b)

num : ℕ → Tr zero
num m = iter (suc zero +_) (suc zero) m

one+ : (m : ℕ) → suc zero + num m ≡ suc (num m)
one+ zero    = refl
one+ (suc m) = cong (suc zero +_) (one+ m)

rd+ : (a a′ b b′ : Tr zero) → read a ≼ read a′ → read b ≼ read b′ → read (a + b) ≼ read (a′ + b′)
rd+ a a′ b b′ p q = ≼-trans (≅→≼ (read-+ a b)) (≼-trans (+-mono p q) (≅→≼ (L.≅-sym (read-+ a′ b′))))

next-mono : (a b : Tr zero) → read a ≼ read b → read (next a) ≼ read (next b)
next-mono a b p = l≼ (λ n → ≼l n (go n))
  where
  go : ∀ n → read (iter (a +_) a n) ≼ read (iter (b +_) b n)
  go zero    = p
  go (suc n) = rd+ a b _ _ p (go n)
```

## 第 0 支折到第 0 层

对一个折叠 (只用两个折叠共有的各行): 任意层号的 Ω 树的折叠值不低于底的 `next` (`Ω≽next`); ℕ 极限层号的 Ω 树的第 m 项不低于底的 m+1 次 `next` (`Ωlim≽`).
`β₁ + β₁` 的链第 1 项是 ℕ 极限层号 `lim (g₁ B)` 的 Ω 树的折叠 (`term1`), 底的第 0 层分量是 β₁ 的折叠; (C′) 的输出的第 m 项正是这个底的 m+1 次 `next` (`form-C`, `num-nx`).

```agda
module ValC where
  open import OCF.Lean.YiOmCFold using (ψ⊥; ψs)

  Ω≽next : (ℓ : LF) (ε : Ev ℓ) (B : Base ℓ) → read (next (b⊥ B)) ≼ read (ψ⊥ ℓ ε B (Ωt ℓ))
  Ω≽next zero     ε B = ≼-refl (read (next (b⊥ B)))
  Ω≽next (suc a)  ε B = ≼l 0 (≼-refl (read (next (b⊥ B))))
  Ω≽next (lim g)  ε B = ≼l 0 (Ω≽next (g 0) (ε 0) _)
  Ω≽next (Ωₗ k h) ε B = ≼l 0 (Ω≽next (h zero) (proj₂ (proj₂ ε zero)) _)

  Ωlim≽ : (g : ℕ → LF) (ε : Ev (lim g)) (D : Base (lim g)) (m : ℕ)
    → read (nx m (b⊥ D)) ≼ read (ψ⊥ (lim g) ε D (seq (Ωt (lim g)) m))
  Ωlim≽ g ε D zero    = Ω≽next (g 0) (ε 0) _
  Ωlim≽ g ε D (suc m) =
    ≼-trans (next-mono (nx m (b⊥ D)) (ψ⊥ (lim g) ε D (seq (Ωt (lim g)) m)) (Ωlim≽ g ε D m))
            (Ω≽next (g (suc m)) (ε (suc m)) _)

  num-nx : (D : Base zero) (m : ℕ) → ψ⊥ zero tt D (num m) ≡ nx m (b⊥ D)
  num-nx D zero    = refl
  num-nx D (suc m) = trans (cong (ψ⊥ zero tt D) (one+ m)) (cong next (num-nx D m))

  D₀ : Base (tw 1) → Base zero
  D₀ B = base (ψ⊥ (tw 1) ε₁ B β₁) (λ j w → ψs (tw 1) ε₁ B j (inb zero w) (bs B j (inb zero w)) β₁)

  v′ : Base (tw 1) → Tr zero
  v′ B = ψs (tw 1) ε₁ B zero (ink self) (bs B zero (ink self)) β₁

  z₁ : Base (tw 1) → Tr zero
  z₁ B = next (v′ B)

  g₁ : Base (tw 1) → ℕ → LF
  g₁ B n = h₁ (iter (v′ B +_) (v′ B) n)

  εz : (B : Base (tw 1)) → Ev (lim (g₁ B))
  εz B = proj₂ (proj₂ ε₁ (z₁ B))

  D₁ : (B : Base (tw 1)) → Base (lim (g₁ B))
  D₁ B = base (ψ⊥ (tw 1) ε₁ B β₁) (λ j w → ψs (tw 1) ε₁ B j (inb (z₁ B) w) (bs B j (inb (z₁ B) w)) β₁)

  form-C : (B : Base (tw 1))
    → ψ⊥ (tw 1) ε₁ B (up β₁ zero (next (suc zero))) ≡ lim (λ m → ψ⊥ zero tt (D₀ B) (num m))
  form-C B = refl

  mid : (B : Base (tw 1))
    → read (ψ⊥ (tw 1) ε₁ B (up β₁ zero (next (suc zero))))
    ≼ read (ψ⊥ (lim (g₁ B)) (εz B) (D₁ B) (Ωt (lim (g₁ B))))
  mid B = l≼ (λ m → ≼l m
    (subst (λ t → read t ≼ read (ψ⊥ (lim (g₁ B)) (εz B) (D₁ B) (seq (Ωt (lim (g₁ B))) m)))
           (sym (num-nx (D₀ B) m)) (Ωlim≽ (g₁ B) (εz B) (D₁ B) m)))

  term1 : (B : Base (tw 1))
    → ψ⊥ (tw 1) ε₁ B (up β₁ (z₁ B) (Ωt (lim (g₁ B)))) ≡ ψ⊥ (lim (g₁ B)) (εz B) (D₁ B) (Ωt (lim (g₁ B)))
  term1 B = refl

  top : (B : Base (tw 1))
    → read (ψ⊥ (lim (g₁ B)) (εz B) (D₁ B) (Ωt (lim (g₁ B)))) ≼ read (ψ⊥ (tw 1) ε₁ B (β₁ + β₁))
  top B = ≼l 1 (plus≽ (ψ⊥ (tw 1) ε₁ B (up β₁ zero (suc zero)))
                      (ψ⊥ (tw 1) ε₁ B (up β₁ (z₁ B) (Ωt (lim (g₁ B)))))
                      (≼-refl (read (ψ⊥ (lim (g₁ B)) (εz B) (D₁ B) (Ωt (lim (g₁ B)))))))

  below2 : (B : Base (tw 1))
    → read (ψ⊥ (tw 1) ε₁ B (up β₁ zero (next (suc zero)))) ≼ read (ψ⊥ (tw 1) ε₁ B (β₁ + β₁))
  below2 B = ≼-trans (mid B) (top B)

  br0-≼ : (B : Base (tw 1))
    → read (ψ⊥ (tw 1) ε₁ B (br (stepC′ zero) zero)) ≼ read (ψ⊥ (tw 1) ε₁ B (br (stepA zero) zero))
  br0-≼ B = ≼-trans (below2 B) (≼l 1 (≼-refl (read (ψ⊥ (tw 1) ε₁ B (β₁ + β₁)))))

module ValA where
  open import OCF.Lean.YiUpFold using (ψ⊥; ψs)

  Ω≽next : (ℓ : LF) (ε : Ev ℓ) (B : Base ℓ) → read (next (b⊥ B)) ≼ read (ψ⊥ ℓ ε B (Ωt ℓ))
  Ω≽next zero     ε B = ≼-refl (read (next (b⊥ B)))
  Ω≽next (suc a)  ε B = ≼l 0 (≼-refl (read (next (b⊥ B))))
  Ω≽next (lim g)  ε B = ≼l 0 (Ω≽next (g 0) (ε 0) _)
  Ω≽next (Ωₗ k h) ε B = ≼l 0 (Ω≽next (h zero) (proj₂ (proj₂ ε zero)) _)

  Ωlim≽ : (g : ℕ → LF) (ε : Ev (lim g)) (D : Base (lim g)) (m : ℕ)
    → read (nx m (b⊥ D)) ≼ read (ψ⊥ (lim g) ε D (seq (Ωt (lim g)) m))
  Ωlim≽ g ε D zero    = Ω≽next (g 0) (ε 0) _
  Ωlim≽ g ε D (suc m) =
    ≼-trans (next-mono (nx m (b⊥ D)) (ψ⊥ (lim g) ε D (seq (Ωt (lim g)) m)) (Ωlim≽ g ε D m))
            (Ω≽next (g (suc m)) (ε (suc m)) _)

  num-nx : (D : Base zero) (m : ℕ) → ψ⊥ zero tt D (num m) ≡ nx m (b⊥ D)
  num-nx D zero    = refl
  num-nx D (suc m) = trans (cong (ψ⊥ zero tt D) (one+ m)) (cong next (num-nx D m))

  D₀ : Base (tw 1) → Base zero
  D₀ B = base (ψ⊥ (tw 1) ε₁ B β₁) (λ j w → ψs (tw 1) ε₁ B j (inb zero w) (bs B j (inb zero w)) β₁)

  v′ : Base (tw 1) → Tr zero
  v′ B = ψs (tw 1) ε₁ B zero (ink self) (bs B zero (ink self)) β₁

  z₁ : Base (tw 1) → Tr zero
  z₁ B = next (v′ B)

  g₁ : Base (tw 1) → ℕ → LF
  g₁ B n = h₁ (iter (v′ B +_) (v′ B) n)

  εz : (B : Base (tw 1)) → Ev (lim (g₁ B))
  εz B = proj₂ (proj₂ ε₁ (z₁ B))

  D₁ : (B : Base (tw 1)) → Base (lim (g₁ B))
  D₁ B = base (ψ⊥ (tw 1) ε₁ B β₁) (λ j w → ψs (tw 1) ε₁ B j (inb (z₁ B) w) (bs B j (inb (z₁ B) w)) β₁)

  form-C : (B : Base (tw 1))
    → ψ⊥ (tw 1) ε₁ B (up β₁ zero (next (suc zero))) ≡ lim (λ m → ψ⊥ zero tt (D₀ B) (num m))
  form-C B = refl

  mid : (B : Base (tw 1))
    → read (ψ⊥ (tw 1) ε₁ B (up β₁ zero (next (suc zero))))
    ≼ read (ψ⊥ (lim (g₁ B)) (εz B) (D₁ B) (Ωt (lim (g₁ B))))
  mid B = l≼ (λ m → ≼l m
    (subst (λ t → read t ≼ read (ψ⊥ (lim (g₁ B)) (εz B) (D₁ B) (seq (Ωt (lim (g₁ B))) m)))
           (sym (num-nx (D₀ B) m)) (Ωlim≽ (g₁ B) (εz B) (D₁ B) m)))

  term1 : (B : Base (tw 1))
    → ψ⊥ (tw 1) ε₁ B (up β₁ (z₁ B) (Ωt (lim (g₁ B)))) ≡ ψ⊥ (lim (g₁ B)) (εz B) (D₁ B) (Ωt (lim (g₁ B)))
  term1 B = refl

  top : (B : Base (tw 1))
    → read (ψ⊥ (lim (g₁ B)) (εz B) (D₁ B) (Ωt (lim (g₁ B)))) ≼ read (ψ⊥ (tw 1) ε₁ B (β₁ + β₁))
  top B = ≼l 1 (plus≽ (ψ⊥ (tw 1) ε₁ B (up β₁ zero (suc zero)))
                      (ψ⊥ (tw 1) ε₁ B (up β₁ (z₁ B) (Ωt (lim (g₁ B)))))
                      (≼-refl (read (ψ⊥ (lim (g₁ B)) (εz B) (D₁ B) (Ωt (lim (g₁ B)))))))

  below2 : (B : Base (tw 1))
    → read (ψ⊥ (tw 1) ε₁ B (up β₁ zero (next (suc zero)))) ≼ read (ψ⊥ (tw 1) ε₁ B (β₁ + β₁))
  below2 B = ≼-trans (mid B) (top B)

  br0-≼ : (B : Base (tw 1))
    → read (ψ⊥ (tw 1) ε₁ B (br (stepC′ zero) zero)) ≼ read (ψ⊥ (tw 1) ε₁ B (br (stepA zero) zero))
  br0-≼ B = ≼-trans (below2 B) (≼l 1 (≼-refl (read (ψ⊥ (tw 1) ε₁ B (β₁ + β₁)))))
```

## 形状 (有限测试)

```agda
f-A : (B : Base (tw 1)) →
  A.ψ⊥ (tw 1) ε₁ B (br (stepA zero) zero) ≡ lim (λ n → A.ψ⊥ (tw 1) ε₁ B (iter (β₁ +_) β₁ n))
f-A B = refl

f-C′ : (B : Base (tw 1)) →
  C′.ψ⊥ (tw 1) ε₁ B (br (stepC′ zero) zero) ≡ lim (λ n → C′.ψ⊥ zero tt (ValC.D₀ B) (num n))
f-C′ B = refl

f-C′₀ : (B : Base (tw 1)) → C′.ψ⊥ zero tt (ValC.D₀ B) (num 0) ≡ next (C′.ψ⊥ (tw 1) ε₁ B β₁)
f-C′₀ B = refl

f-C′₁ : (B : Base (tw 1)) → C′.ψ⊥ zero tt (ValC.D₀ B) (num 1) ≡ next (next (C′.ψ⊥ (tw 1) ε₁ B β₁))
f-C′₁ B = refl
```

tw 1 这一站 (目标第 0 层) 的链步: c = 0 上两个折叠逐字相同. c 非零时两边的底记录里各带自己的折叠, `refl` 不比较; 不是值不同的证据.

```agda
tw1-same0 :
  A.ψs (tw 1) ε₁ (B₀ (tw 1)) zero (ink self) (Ωt zero) (up zero zero (Ωt (h₁ zero)))
  ≡ C′.ψs (tw 1) ε₁ (B₀ (tw 1)) zero (ink self) (Ωt zero) (up zero zero (Ωt (h₁ zero)))
tw1-same0 = refl
```
