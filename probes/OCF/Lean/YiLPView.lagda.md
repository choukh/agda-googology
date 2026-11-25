# 合法块的 View: 实例

> 判决: 成品候选 (View). 编译定理 `brwView`, 无前提: 与 `YiViewInst.brwView` 同一个通用记录 (`BrwViewDef.BrwView`), 一个记录对一切层号 ℓ 成立; `Tr ℓ` 的每个对象读作零, 后继, ℕ 极限 (相邻项按值的第一位置序 `_◁_` 步进) 或 Ω 极限之一, 部分是同层的对象, 值与构造子作用在部分的值上互相 `≼`.
> Ω 极限的坐标是 `Br ℓ p`, 即低层的树 (合法块里每棵树都合法, 坐标与对象的合法性都是 `⊤`). `up x c y e` 按 y 的 View 分解 (`mapUp`), 部分是 `upz x c ·`: 孩子是零时取 x, 否则用 `zl` 给出的非零证明嵌入.
> 不否定什么. 部分的良基在 [YiLPWf](YiLPWf.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLPView where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym; cong)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps using (zl; chP; chBr)
open import OCF.Lean.YiLPVal
open import OCF.Align.BrwViewDef using (View; vz; vs; vl; vΩ; BrwView) renaming (Sig to BSig)
```

## 签名

```agda
SigY : BSig
SigY = record
  { Ix = L ; B = V ; _≼_ = λ a b → a ≼ b ; Stp = λ a b → a ◁ b
  ; Kd = Pos ; Cd = λ {i} p → Br i p ; LgC = λ _ → ⊤ ; tg = λ {i} _ → i
  ; bz = zero ; bs = suc ; bl = lim ; bΩ = Ω }

VW : (ℓ : L) → V ℓ → Set
VW ℓ v = View SigY Tr (λ {i} x → val i x) (λ _ → ⊤) ℓ v
```

## 去掉零孩子的嵌入

```agda
chT⁻ : (ℓ : L) (c : Ch ℓ) → Tr (chL ℓ c) → ChT ℓ c
chT⁻ zero     () y
chT⁻ (suc a)  c y = y
chT⁻ (lim g)  n y = y
chT⁻ (Ωₗ k h) c y = y

conv : (ℓ : L) (c : Ch ℓ) {a b : Tr (chL ℓ c)} → chL ℓ c ⊢ a ◃ b → RCh ℓ c (chT⁻ ℓ c a) (chT⁻ ℓ c b)
conv zero     () d
conv (suc a)  c d = d
conv (lim g)  n d = d
conv (Ωₗ k h) c d = d

conv₀ : (ℓ : L) (c : Ch ℓ) {b : Tr (chL ℓ c)} → chL ℓ c ⊢ zero ◃ b → RCh ℓ c (chZ ℓ c) (chT⁻ ℓ c b)
conv₀ zero     () d
conv₀ (suc a)  c d = d
conv₀ (lim g)  n d = d
conv₀ (Ωₗ k h) c d = d

chT-β : (ℓ : L) (c : Ch ℓ) (y : Tr (chL ℓ c)) → chT ℓ c (chT⁻ ℓ c y) ≡ y
chT-β zero     () y
chT-β (suc a)  c y = refl
chT-β (lim g)  n y = refl
chT-β (Ωₗ k h) c y = refl

upz′ : (ℓ : L) (c : Ch ℓ) → Tr ℓ → (y : Tr (chL ℓ c)) → (zero ≡ y) ⊎ (chL ℓ c ⊢ zero ◃ y) → Tr ℓ
upz′ ℓ c x y (inj₁ _) = x
upz′ ℓ c x y (inj₂ d) = up x c (chT⁻ ℓ c y) (conv₀ ℓ c d)

upz : (ℓ : L) (c : Ch ℓ) → Tr ℓ → Tr (chL ℓ c) → Tr ℓ
upz ℓ c x y = upz′ ℓ c x y (zl y)

valCh-β : (ℓ : L) (c : Ch ℓ) (y : Tr (chL ℓ c)) → valCh ℓ c (chT⁻ ℓ c y) ≡ emb ℓ c (val (chL ℓ c) y)
valCh-β zero     () y
valCh-β (suc a)  c y = refl
valCh-β (lim g)  n y = refl
valCh-β (Ωₗ k h) c y = refl

val-upz′ : (ℓ : L) (c : Ch ℓ) (x : Tr ℓ) (y : Tr (chL ℓ c)) (s : (zero ≡ y) ⊎ (chL ℓ c ⊢ zero ◃ y))
         → val ℓ (upz′ ℓ c x y s) ≡ val ℓ x ⊹ emb ℓ c (val (chL ℓ c) y)
val-upz′ ℓ c x .zero (inj₁ refl) = refl
val-upz′ ℓ c x y     (inj₂ d)    = cong (val ℓ x ⊹_) (valCh-β ℓ c y)

val-upz : (ℓ : L) (c : Ch ℓ) (x : Tr ℓ) (y : Tr (chL ℓ c))
        → val ℓ (upz ℓ c x y) ≡ val ℓ x ⊹ emb ℓ c (val (chL ℓ c) y)
val-upz ℓ c x y = val-upz′ ℓ c x y (zl y)
```

## View 的搬运与 `up` 的分解

```agda
reidx : ∀ {ℓ} {w w′ : V ℓ} → w′ ≈ w → VW ℓ w → VW ℓ w′
reidx e (vz e′)         = vz (≈-trans e e′)
reidx e (vs y h e′)     = vs y h (≈-trans e e′)
reidx e (vl f h st e′)  = vl f h st (≈-trans e e′)
reidx e (vΩ p g h e′)   = vΩ p g h (≈-trans e e′)

lim≡ : ∀ {ℓ} (a b : ℕ → V ℓ) → ((n : ℕ) → a n ≡ b n) → lim a ≈ lim b
lim≡ a b e = l≼ (λ n → ≼l n (subst (λ t → a n ≼ t) (e n) (≼-refl (a n))))
           , l≼ (λ n → ≼l n (subst (λ t → b n ≼ t) (sym (e n)) (≼-refl (b n))))

Ω≡ : ∀ {ℓ} (p : Pos ℓ) (a b : Br ℓ p → V ℓ) → ((z : Br ℓ p) → a z ≡ b z) → Ω p a ≈ Ω p b
Ω≡ p a b e = Ω≼ (λ z → ≼Ω z (subst (λ t → a z ≼ t) (e z) (≼-refl (a z))))
           , Ω≼ (λ z → ≼Ω z (subst (λ t → b z ≼ t) (sym (e z)) (≼-refl (b z))))

mapUp : (ℓ : L) (c : Ch ℓ) (x : Tr ℓ) → VW ℓ (val ℓ x)
      → {v : V (chL ℓ c)} → VW (chL ℓ c) v → VW ℓ (val ℓ x ⊹ emb ℓ c v)
mapUp ℓ c x vx (vz e) = reidx (F≈ ℓ c (val ℓ x) e) vx
mapUp ℓ c x vx (vs y _ e) =
  vs (upz ℓ c x y) tt
     (subst (λ t → (val ℓ x ⊹ emb ℓ c _) ≈ suc t) (sym (val-upz ℓ c x y)) (F≈ ℓ c (val ℓ x) e))
mapUp ℓ c x vx (vl f _ st e) =
  vl (λ n → upz ℓ c x (f n)) (λ n → tt)
     (λ n → subst₂ _◁_ (sym (val-upz ℓ c x (f n))) (sym (val-upz ℓ c x (f (suc n))))
                       (⊹-mono◁ (val ℓ x) (emb-mono◁ ℓ c (st n))))
     (≈-trans (F≈ ℓ c (val ℓ x) e)
              (lim≡ _ _ (λ n → sym (val-upz ℓ c x (f n)))))
mapUp ℓ c x vx (vΩ p g _ e) =
  vΩ (chP ℓ c p) (λ z → upz ℓ c x (g (chBr ℓ c p z))) (λ z _ → tt)
     (≈-trans (F≈ ℓ c (val ℓ x) e)
              (Ω≡ (chP ℓ c p) _ _ (λ z → sym (val-upz ℓ c x (g (chBr ℓ c p z))))))
```

## View

```agda
view : (ℓ : L) (x : Tr ℓ) → VW ℓ (val ℓ x)
view ℓ zero      = vz (≈-refl zero)
view ℓ (suc x)   = vs x tt (≈-refl _)
view ℓ (lim f a) = vl f (λ n → tt) (λ n → val-mono ℓ (a n)) (≈-refl _)
view ℓ (Ω p g)   = vΩ p g (λ z _ → tt) (≈-refl _)
view zero     (up x () y e)
view (suc a)  (up x c y e) = mapUp (suc a) c x (view (suc a) x) (view a y)
view (lim g)  (up x n y e) = mapUp (lim g) n x (view (lim g) x) (view (g n) y)
view (Ωₗ k h) (up x c y e) = mapUp (Ωₗ k h) c x (view (Ωₗ k h) x) (view (h c) y)

brwView : BrwView SigY Tr (λ {i} x → val i x) (λ _ → ⊤)
brwView = record { view = λ {i} x _ → view i x }
```
