# 抽象理论 (四): 值的下界的通用出口与单调折叠的传递

> 判决: 编译定理, 无前提, 不导入仓库模块. 对任意值前序 `Val` 与任意带基本列的参照系统 (余尾 0, 1, ω; `pred`, `fsn`): 一族对基本列封闭的 (参照项, 值) 给出下界 (`exit`; `YiMonoExit.exit` 是它的实例, 见 `YiAbsSimInst`).
> 充分条件: 源层上的一个步进关系 (严格的 `⇝ˢ` 与不严格的 `⇝`) 在折叠后的值上各自成立, 参照项与源树的对应 R 沿基本列走这两种步, 就有下界 (`lower`). 第一位置序在单调且保持合法的折叠下是这样的步 (`mono-strict`, `mono-weak`).
> 不给出什么: 结点行的链与后继行的迭代不是第一位置序的步, 它们要各自的行律作为 `⇝` 的成员; 多层的对应 R 没有在这里构造. 前提的实例: `Fin.lower-fin` (有限序数).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAbsSim where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
```

## 值前序

```agda
record Val : Set₁ where
  infix 4 _≼_
  field
    V       : Set
    _≼_     : V → V → Set
    ≼-refl  : ∀ {a} → a ≼ a
    ≼-trans : ∀ {a b c} → a ≼ b → b ≼ c → a ≼ c
    vz      : V
    vs      : V → V
    vl      : (ℕ → V) → V
    z≼      : ∀ {a} → vz ≼ a
    s≼s     : ∀ {a b} → a ≼ b → vs a ≼ vs b
    l≼      : ∀ {f a} → (∀ n → f n ≼ a) → vl f ≼ a
    ≼s      : ∀ {a} → a ≼ vs a
```

## 出口

参照系统: 项 `T`, 余尾的三种情形 (任意谓词), 前驱与基本列. `HC t` 是 t 沿基本列遗传可达, `tree` 是它的值.

```agda
module Exit (𝕍 : Val) {T : Set} (C0 C1 Cω : T → Set) (pred : T → T) (fsn : T → ℕ → T) where
  open Val 𝕍

  data HC (t : T) : Set where
    h0 : C0 t → HC t
    h1 : C1 t → HC (pred t) → HC t
    hω : Cω t → (∀ n → HC (fsn t n)) → HC t

  tree : ∀ {t} → HC t → V
  tree (h0 _)   = vz
  tree (h1 _ h) = vs (tree h)
  tree (hω _ h) = vl (λ n → tree (h n))

  record Closed (P : T → V → Set) : Set where
    field
      step1 : ∀ {t X} → P t X → C1 t → Σ V λ X′ → P (pred t) X′ × (vs X′ ≼ X)
      stepω : ∀ {t X} → P t X → Cω t → ∀ n → Σ V λ X′ → P (fsn t n) X′ × (X′ ≼ X)
  open Closed

  exit : ∀ {P} → Closed P → ∀ {t X} → P t X → (h : HC t) → tree h ≼ X
  exit C p (h0 _)   = z≼
  exit C p (h1 e h) =
    ≼-trans (s≼s (exit C (proj₁ (proj₂ (step1 C p e))) h)) (proj₂ (proj₂ (step1 C p e)))
  exit C p (hω e h) = l≼ (λ n →
    ≼-trans (exit C (proj₁ (proj₂ (stepω C p e n))) (h n)) (proj₂ (proj₂ (stepω C p e n))))
```

## 源层的步进传到值上

`S₁` 是被折叠的树, `S₀` 是折叠的输出, `v` 读成值, `G` 是量化域 (合法, 或规范的读回域).
`x′ ⇝ˢ x`: 折叠后值严格更小; `x′ ⇝ x`: 折叠后值不更大. 对应 R 在余尾 1 处走一步 `⇝ˢ` 到 `pred`, 在余尾 ω 处逐项走 `⇝` 到 `fsn`.

```agda
  module Sim {S₁ S₀ : Set} (v : S₀ → V) (ψ : S₁ → S₀) (G : S₁ → Set)
      (_⇝ˢ_ _⇝_ : S₁ → S₁ → Set)
      (strict : ∀ {x y} → G y → x ⇝ˢ y → vs (v (ψ x)) ≼ v (ψ y))
      (weak   : ∀ {x y} → G y → x ⇝ y → v (ψ x) ≼ v (ψ y))
      (R : T → S₁ → Set)
      (r1 : ∀ {t x} → R t x → G x → C1 t → Σ S₁ λ x′ → R (pred t) x′ × G x′ × (x′ ⇝ˢ x))
      (rω : ∀ {t x} → R t x → G x → Cω t → ∀ n → Σ S₁ λ x′ → R (fsn t n) x′ × G x′ × (x′ ⇝ x)) where

    P : T → V → Set
    P t X = Σ S₁ λ x → R t x × G x × (v (ψ x) ≼ X)

    closed : Closed P
    closed .step1 (x , r , g , le) e with r1 r g e
    ... | x′ , r′ , g′ , st = v (ψ x′) , (x′ , r′ , g′ , ≼-refl) , ≼-trans (strict g st) le
    closed .stepω (x , r , g , le) e n with rω r g e n
    ... | x′ , r′ , g′ , st = v (ψ x′) , (x′ , r′ , g′ , ≼-refl) , ≼-trans (weak g st) le

    lower : ∀ {t x} → R t x → G x → (h : HC t) → tree h ≼ v (ψ x)
    lower {x = x} r g h = exit closed (x , r , g , ≼-refl) h
```

第一位置序是这样的步: 折叠单调, 保持合法, 输出层的第一位置序在合法树上值严格.

```agda
module FromMono (𝕍 : Val) {S₁ S₀ : Set} (v : S₀ → Val.V 𝕍) (ψ : S₁ → S₀)
    (_◃₁_ : S₁ → S₁ → Set) (_◃₀_ : S₀ → S₀ → Set) (G₁ : S₁ → Set) (G₀ : S₀ → Set)
    (mono : ∀ {x y} → x ◃₁ y → ψ x ◃₀ ψ y)
    (pres : ∀ {y} → G₁ y → G₀ (ψ y))
    (str₀ : ∀ {a b} → G₀ b → a ◃₀ b → Val._≼_ 𝕍 (Val.vs 𝕍 (v a)) (v b)) where
  open Val 𝕍

  mono-strict : ∀ {x y} → G₁ y → x ◃₁ y → vs (v (ψ x)) ≼ v (ψ y)
  mono-strict g d = str₀ (pres g) (mono d)

  mono-weak : ∀ {x y} → G₁ y → x ◃₁ y → v (ψ x) ≼ v (ψ y)
  mono-weak g d = ≼-trans ≼s (mono-strict g d)
```

## 前提的实例: 有限序数

参照项与源树都是 ℕ, 折叠是恒等, 步是 "后继". 只为说明前提同时可满足.

```agda
module Fin (𝕍 : Val) where
  open Val 𝕍

  predℕ : ℕ → ℕ
  predℕ zero    = zero
  predℕ (suc n) = n

  val : ℕ → V
  val zero    = vz
  val (suc n) = vs (val n)

  open Exit 𝕍 {T = ℕ} (λ n → n ≡ zero) (λ n → Σ ℕ λ m → n ≡ suc m) (λ _ → ⊥) predℕ (λ n _ → n)

  open Sim {S₁ = ℕ} {S₀ = ℕ} val (λ n → n) (λ _ → ⊤) (λ x y → y ≡ suc x) (λ _ _ → ⊥)
    (λ { _ refl → ≼-refl }) (λ _ ())
    _≡_
    (λ { refl _ (m , refl) → m , refl , tt , refl })
    (λ _ _ ())

  lower-fin : (n : ℕ) (h : HC n) → tree h ≼ val n
  lower-fin n h = lower refl tt h
```
