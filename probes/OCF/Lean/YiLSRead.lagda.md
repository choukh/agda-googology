# 合法块上的值: 第 0 层的读回

> 验收文件 (定义与引理). 合法块第 0 层的树读成参照框架的第 0 层树 `read`; 加法, `next`, 部分和的读回与值序; 第一位置序的自反闭包 `⊴`.
> 编译定理: 第一位置序读成前驱包含 (`◃⊑`) 与字面前驱 (`◃→≺`, 对一切树, 因为每棵树都合法); 读回带证书 `HSr`.
> 不否定什么, 不涉及上界. 模拟的关系族在 `YiLSRel`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLSRead where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≅→≼; ⊑→≼; ≼-+ʳ) renaming (+-mono to +ᵛ-mono)
import OCF.Align.RR4MonoFragment as MF
open import OCF.Align.BTBOFullV3 using (≺→⊑₀)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
```

## 读回

```agda
T₀ : Set
T₀ = L.Ordᶜ L.zero

read : Tr zero → T₀
read zero          = L.zero
read (suc x)       = L.suc (read x)
read (lim f _)     = L.lim (λ n → read (f n))
read (Ω () _)
read (up _ () _ _)

read-+ : (x y : Tr zero) → read (x + y) L.≅ (read x L.+ read y)
read-+ x zero          = L.≅-refl⁰ (read x)
read-+ x (suc y)       = L.s≅ (read-+ x y)
read-+ x (lim f _)     = L.l≅ (λ n → read-+ x (f n))
read-+ x (Ω () _)
read-+ x (up _ () _ _)
```

## 值序

```agda
plus≽ : (a : Tr zero) {y : T₀} (b : Tr zero) → y ≼ read b → y ≼ read (a + b)
plus≽ a b q = ≼-trans q (≼-trans (MF.≼-+ˡ (read a) (read b)) (≅→≼ (L.≅-sym (read-+ a b))))

cum≽ : (F : ℕ → Tr zero) (n : ℕ) {y : T₀} → y ≼ read (F n) → y ≼ read (cum F n)
cum≽ F zero    q = q
cum≽ F (suc n) q = plus≽ (cum F n) (F (suc n)) q

limcum≽ : (F : ℕ → Tr zero) (nz : (n : ℕ) → zero ⊢ zero ◃ F n) (n : ℕ) {y : T₀}
  → y ≼ read (F n) → y ≼ read (limc F nz)
limcum≽ F nz n q = ≼l n (cum≽ F n q)

next≽ : (b : Tr zero) (nz : zero ⊢ zero ◃ b) {Y : T₀} → Y ≼ read b
  → L.lim (iterᴸ (Y L.+_) L.zero) ≼ read (next b nz)
next≽ b nz {Y} q = l≼ λ where
    zero    → z≼
    (suc n) → ≼l n (go n)
  where
  go : ∀ n → iterᴸ (Y L.+_) L.zero (suc n) ≼ read (iter (b +_) b n)
  go zero    = q
  go (suc n) = ≼-trans (+ᵛ-mono q (go n)) (≅→≼ (L.≅-sym (read-+ b (iter (b +_) b n))))
```

## 第一位置序的读回

```agda
◃⊑ : {x y : Tr zero} → zero ⊢ x ◃ y → read x L.⊑ read y
◃⊑ ◃s            h = L.≺s h
◃⊑ (◃l n)        h = L.≺l n h
◃⊑ (◃w {p = ()})
◃⊑ (◃u _ () _ _)
◃⊑ (◃c _ () _)
◃⊑ (◃t d e)      h = ◃⊑ e (◃⊑ d h)

HSr : (x : Tr zero) → L.HS (read x)
HSr zero          = L.hz
HSr (suc x)       = L.hs (HSr x)
HSr (lim f a)     = L.hl (λ n → HSr (f n)) (λ n → ◃⊑ (a n))
HSr (Ω () _)
HSr (up _ () _ _)
```

字面前驱: 先定义 "相邻项逐个是字面前驱" 的遗传谓词, 它沿第一位置序向下封闭, 并且对一切树成立.

```agda
St≺ : Tr zero → Set
St≺ zero          = ⊤
St≺ (suc x)       = St≺ x
St≺ (lim f _)     = ((n : ℕ) → St≺ (f n)) × ((n : ℕ) → read (f n) L.≺ read (f (suc n)))
St≺ (Ω () _)
St≺ (up _ () _ _)

st-dn : {x y : Tr zero} → St≺ y → zero ⊢ x ◃ y → St≺ x
st-dn w ◃s            = w
st-dn w (◃l n)        = proj₁ w n
st-dn w (◃w {p = ()})
st-dn w (◃u _ () _ _)
st-dn w (◃c _ () _)
st-dn w (◃t d e)      = st-dn (st-dn w e) d

lt≺ : {x y : Tr zero} → St≺ y → zero ⊢ x ◃ y → read x L.≺ read y
lt≺ {x} w ◃s        = L.≺z (L.≅-refl⁰ (read x))
lt≺ w (◃l n)        = L.≺l (suc n) (proj₂ w n)
lt≺ w (◃w {p = ()})
lt≺ w (◃u _ () _ _)
lt≺ w (◃c _ () _)
lt≺ w (◃t d e)      = ≺→⊑₀ (lt≺ w e) (lt≺ (st-dn w e) d)

all-st : (x : Tr zero) → St≺ x
all-st zero          = tt
all-st (suc x)       = all-st x
all-st (lim f a)     = (λ n → all-st (f n)) , (λ n → lt≺ (all-st (f (suc n))) (a n))
all-st (Ω () _)
all-st (up _ () _ _)

◃→≺ : {x y : Tr zero} → zero ⊢ x ◃ y → read x L.≺ read y
◃→≺ {y = y} d = lt≺ (all-st y) d
```

## 自反闭包

```agda
infix 4 _⊢_⊴_
data _⊢_⊴_ (ℓ : L) (t : Tr ℓ) : Tr ℓ → Set where
  ⊴r : ℓ ⊢ t ⊴ t
  ⊴◃ : ∀ {t′} → ℓ ⊢ t ◃ t′ → ℓ ⊢ t ⊴ t′

⊴-◃ : ∀ {ℓ} {a b c : Tr ℓ} → ℓ ⊢ a ⊴ b → ℓ ⊢ b ◃ c → ℓ ⊢ a ◃ c
⊴-◃ ⊴r     e = e
⊴-◃ (⊴◃ d) e = ◃t d e

◃-⊴ : ∀ {ℓ} {a b c : Tr ℓ} → ℓ ⊢ a ◃ b → ℓ ⊢ b ⊴ c → ℓ ⊢ a ◃ c
◃-⊴ d ⊴r     = d
◃-⊴ d (⊴◃ e) = ◃t d e

⊴-trans : ∀ {ℓ} {a b c : Tr ℓ} → ℓ ⊢ a ⊴ b → ℓ ⊢ b ⊴ c → ℓ ⊢ a ⊴ c
⊴-trans d ⊴r     = d
⊴-trans d (⊴◃ e) = ⊴◃ (⊴-◃ d e)

⊴→≼ : {a b : Tr zero} → zero ⊢ a ⊴ b → read a ≼ read b
⊴→≼ {a} ⊴r     = ≼-refl (read a)
⊴→≼ {a} (⊴◃ d) = ⊑→≼ (read a) (◃⊑ d)
```
