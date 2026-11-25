# 辅助系统 `Out.nodeE` 原形状的链一支: 最小实例上第 1 个链点不成立

> 判决: 编译定理, 不读记号. 塔第 1 项, 目标 `h₁ 1`, 孩子 1 的换基状态 (底值 1; 就是 `YiBLFold.Main.Srᴮ` 在 x = 0 处, `reach₁`): 换基层号的 Ω 树的顶结点不保留 (`noEv₁`), 按折叠自己的链 (`iter S x₀`), 第 1 个链点的像不 `⊴` 结点的像 (`no-chain₁`). 所以 `Out` 链一支的 `∀ k → Φ (g (z k)) ⊴ Φ (nd p g)` 在 k = 1 处挡住, 是形状的问题: 结点的像是部分和极限, 第 1 个链点的像只作为右加数进入部分和, 在本实例里不在任何部分和的第一位置序下面.
> 不否定什么: 只对这条链; 改成按关系支配后链一支对一切 k 成立 (`YiQDFold.AddR.chain-dom`). 做法: 不变量 "有限数, 或以第 0 个链点的像为左前缀" 沿第一位置序向下封闭 (`P-dw`), 结点的像满足, 第 1 个链点的像不满足.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiQDNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
import OCF.Lean.YiRBSib as R
open import OCF.Lean.YiBSBase
open import OCF.Lean.YiBLFold using (module Aux; module Main; _⊴ᵗ_; Sₙ; rcₙ; route-tw1)
open import OCF.Lean.YiVALeaf using (nzs)
open import OCF.Lean.YiTBRow using (h₁; nat)
open import OCF.Lean.YiTBTab using (ωᶜ)
```

## 不变量

`SW A x`: x 由 A 经右侧的后继, 极限, 结点, 嵌入左项得到 (`A + y` 都是, `sw-add`). A 是各项为有限数的极限时, "有限数或 `SW A`" 沿第一位置序向下封闭.

```agda
module Inv (J : L) where
  data Fin′ : Tr J → Set where
    fz : Fin′ zero
    fs : ∀ {x} → Fin′ x → Fin′ (suc x)

  data SW (A : Tr J) : Tr J → Set where
    here : ∀ {x} → x ≡ A → SW A x
    s    : ∀ {x} → SW A x → SW A (suc x)
    l    : ∀ {f a} → (∀ n → SW A (f n)) → SW A (lim f a)
    w    : ∀ {p g} → (∀ z → SW A (g z)) → SW A (Ω p g)
    u    : ∀ {x c y e} → SW A x → SW A (up x c y e)

  sw-add : ∀ {A x} (y : Tr J) → SW A x → SW A (x + y)
  sw-add zero         h = h
  sw-add (suc y)      h = s (sw-add y h)
  sw-add (lim f a)    h = l (λ n → sw-add (f n) h)
  sw-add (Ω p g)      h = w (λ z → sw-add (g z) h)
  sw-add (up y c v e) h = u (sw-add y h)

  sw-cum : ∀ (F : ℕ → Tr J) m → SW (F 0) (cum F m)
  sw-cum F zero    = here refl
  sw-cum F (suc m) = sw-add (F (suc m)) (sw-cum F m)

  comp : ℕ → Tr J → Tr J
  comp n (lim f _) = f n
  comp n t         = t

  tg : Tr J → ℕ
  tg zero         = 0
  tg (suc _)      = 1
  tg (lim _ _)    = 2
  tg (Ω _ _)      = 3
  tg (up _ _ _ _) = 4

  module _ (f₀ : ℕ → Tr J) (a₀ : (n : ℕ) → J ⊢ f₀ n ◃ f₀ (suc n)) (fin₀ : ∀ n → Fin′ (f₀ n)) where
    Pv : Tr J → Set
    Pv x = Fin′ x ⊎ SW (lim f₀ a₀) x

    P-dw : ∀ {x y} → J ⊢ x ◃ y → Pv y → Pv x
    P-dw ◃s           (inj₁ (fs h))     = inj₁ h
    P-dw ◃s           (inj₂ (here ()))
    P-dw ◃s           (inj₂ (s h))      = inj₂ h
    P-dw (◃l n)       (inj₁ ())
    P-dw (◃l n)       (inj₂ (here refl)) = inj₁ (fin₀ n)
    P-dw (◃l n)       (inj₂ (l h))      = inj₂ (h n)
    P-dw ◃w           (inj₁ ())
    P-dw ◃w           (inj₂ (here ()))
    P-dw ◃w           (inj₂ (w h))      = inj₂ (h _)
    P-dw (◃u x c y e) (inj₁ ())
    P-dw (◃u x c y e) (inj₂ (here ()))
    P-dw (◃u x c y e) (inj₂ (u h))      = inj₂ h
    P-dw (◃c x c r)   (inj₁ ())
    P-dw (◃c x c r)   (inj₂ (here ()))
    P-dw (◃c x c r)   (inj₂ (u h))      = inj₂ (u h)
    P-dw (◃t d₁ d₂)   q                 = P-dw d₁ (P-dw d₂ q)

    P-⊴ : ∀ {x y} → x ⊴ᵗ y → Pv y → Pv x
    P-⊴ (inj₁ refl) q = q
    P-⊴ (inj₂ d)    q = P-dw d q
```

## 最小实例

目标 j₁ = `h₁ 1`, 换基层号 a₁ = j₁ ⊕ ↑1 (后继形状, 孩子是 j₁), 底值 1. Ω 树的顶结点在孩子层号自身的槽位上; 链与 `YiRBSib.ψ` 的结点一行逐字相同.

```agda
j₁ b₁ a₁ : L
j₁ = h₁ (nat 1)
b₁ = ↑ zero (nat 1)
a₁ = j₁ ⊕ b₁

β₁ : Tr⁺ j₁
β₁ = suc zero , ◃s

p₁ : Pos a₁
p₁ = inj₂ (tt , inj₁ tt)

gᵃ : Br a₁ p₁ → Tr a₁
gᵃ c = proj₁ (upz {s = sS} {h = λ _ → j₁} tt (suc c , z◃ c ◃s))

Ωt-a₁ : proj₁ (Ωt a₁) ≡ Ω p₁ gᵃ
Ωt-a₁ = refl

fin-add1 : ∀ {x} → Inv.Fin′ j₁ x → Inv.Fin′ j₁ (suc zero + x)
fin-add1 Inv.fz     = Inv.fs Inv.fz
fin-add1 (Inv.fs h) = Inv.fs (fin-add1 h)

fin-iter : ∀ n → Inv.Fin′ j₁ (iter (suc zero +_) (suc zero) n)
fin-iter zero    = Inv.fs Inv.fz
fin-iter (suc n) = fin-add1 (fin-iter n)

module Min (o : Ok a₁) where
  open Inv j₁
  s₁ : Aux.Stᴬ j₁ a₁
  s₁ = Aux.rbs {j₁} b₁ o (B₀ a₁) β₁

  Φ : Tr a₁ → Tr j₁
  Φ x = proj₁ (Aux.Φᴬ j₁ s₁ x)

  Sᵃ : Br a₁ p₁ → Br a₁ p₁
  Sᵃ c = fromBr a₁ p₁ (proj₁ (R.ψ a₁ o (R.rb-no a₁) (B₀ a₁) (at a₁ p₁) (posW a₁ p₁) (B₀ a₁ (at a₁ p₁) (posW a₁ p₁)) (gᵃ c)))

  zᵃ : ℕ → Br a₁ p₁
  zᵃ k = iter Sᵃ (fromBr a₁ p₁ zero) k

  noEv₁ : Aux.Evᴬ j₁ s₁ p₁ → ⊥
  noEv₁ (q , cv , e , ())

  P₁ : Tr j₁ → Set
  P₁ = Pv (iter (suc zero +_) (suc zero)) (nextA (suc zero) ◃s) fin-iter

  node-P : P₁ (Φ (Ω p₁ gᵃ))
  node-P = inj₂ (l (λ m → sw-cum (λ n → Φ (gᵃ (zᵃ n))) m))
```

第 1 个链点的像不满足不变量: 逐层剥开 (链点 ω·Ω₁ 处的自身折叠, Ω₁ 的分支取 ω), 每一层的极限第 0 项与左前缀的第 0 项 (或第 1 项) 形状不同, 最后落到底值 1.

```agda
  not-P : P₁ (Φ (gᵃ (zᵃ 1))) → ⊥
  not-P (inj₁ ())
  not-P (inj₂ (here e)) with cong tg (cong (comp 0) e)
  ... | ()
  not-P (inj₂ (l h)) with h 0
  ... | here e with cong tg (cong (comp 0) e)
  ...   | ()
  not-P (inj₂ (l h)) | l h₁′ with h₁′ 0
  ... | here ()
  ... | w h₂ with h₂ ωᶜ
  ...   | here e with cong tg (cong (comp 0) e)
  ...     | ()
  not-P (inj₂ (l h)) | l h₁′ | w h₂ | l h₃ with h₃ 0
  ... | here e with cong tg (cong (comp 1) e)
  ...   | ()
  not-P (inj₂ (l h)) | l h₁′ | w h₂ | l h₃ | l h₄ with h₄ 0
  ... | here ()
  ... | s (here ())

  no-chain₁ : Φ (gᵃ (zᵃ 1)) ⊴ᵗ Φ (proj₁ (Ωt a₁)) → ⊥
  no-chain₁ le = not-P (P-⊴ (iter (suc zero +_) (suc zero)) (nextA (suc zero) ◃s) fin-iter le node-P)
```

这个状态就是塔第 1 项 (目标 `h₁ 1`, 底值 1) 根状态在孩子 1, x = 0 处的换基状态.

```agda
reach₁ : (B : _) → Main.Srᴮ zero h₁ (Ok-tw 1) (Sₙ 0) (rcₙ 0) B j₁ (nat 1) self (lift zero (↑ zero (nat 1))) (route-tw1 (nzs zero))
    β₁ (nat 1) zero
  ≡ Aux.rbs {j₁} b₁ (Main.oᴮ zero h₁ (Ok-tw 1) (Sₙ 0) (rcₙ 0) B j₁ (nat 1) self (lift zero (↑ zero (nat 1))) (route-tw1 (nzs zero)) (nat 1))
      (B₀ a₁) β₁
reach₁ B = refl
```
