# 内部 View: 实例

> 判决: 成品候选 (View). 编译定理 `brwView`: 一个记录对一切层号 ℓ 成立, `Tr ℓ` 的每个合法对象有 `BrwViewDef` 意义下的 View (零, 后继, ℕ 极限, Ω 极限之一), 部分是同层的合法对象, 值与构造子作用在部分的值上互相 `≼`; ℕ 极限的相邻项按值的第一位置序 `_◁_` 步进. 无前提.
> `up x c y` 按 y 的 View 分解 (`mapUp`): y 读作零时用 x 的 View; 后继, ℕ 极限逐项, Ω 极限 (父层槽位 `chP`) 的部分都是 `upz x c ·`; 嵌套的 `up` 由对 y 的递归处理.
> 不否定什么. 部分的良基与对象层的步进在 [YiViewWf](YiViewWf.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiViewInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym; cong)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshLegal using (_⊢_◃_; Leg; LegBr; LegCh; zl)
open import OCF.Lean.YiUpBlock using (chP; chBr)
open import OCF.Lean.YiUpLegal using (chLeg)
open import OCF.Lean.YiViewVal
open import OCF.Align.BrwViewDef using (Sig; View; vz; vs; vl; vΩ; BrwView)
```

## 签名

一个签名管一切层: 下标是层号, 种类是槽位, 坐标是槽位上的低层树, 坐标的合法性是 `LegBr`, 分支在同一层.

```agda
SigY : Sig
SigY = record
  { Ix = L ; B = V ; _≼_ = λ a b → a ≼ b ; Stp = λ a b → a ◁ b
  ; Kd = Pos ; Cd = λ {i} p → Br i p ; LgC = λ {i} {p} z → LegBr i p z ; tg = λ {i} _ → i
  ; bz = zero ; bs = suc ; bl = lim ; bΩ = Ω }

VW : (ℓ : L) → V ℓ → Set
VW ℓ v = View SigY Tr (λ {i} x → val i x) (λ {i} x → Leg i x) ℓ v
```

## 去掉零孩子的嵌入

`upz x c y` 在 y 是零时取 x (合法性不允许零孩子), 否则取 `up x c y`; 两种情形的值都是 x 的值加 y 的值的抬升.

```agda
chT⁻ : (ℓ : L) (c : Ch ℓ) → Tr (chL ℓ c) → ChT ℓ c
chT⁻ zero     () y
chT⁻ (suc a)  c y = y
chT⁻ (lim g)  n y = y
chT⁻ (Ωₗ k h) c y = y

upz : (ℓ : L) (c : Ch ℓ) → Tr ℓ → Tr (chL ℓ c) → Tr ℓ
upz ℓ c x zero = x
upz ℓ c x y    = up x c (chT⁻ ℓ c y)

valCh-β : (ℓ : L) (c : Ch ℓ) (y : Tr (chL ℓ c)) → valCh ℓ c (chT⁻ ℓ c y) ≡ emb ℓ c (val (chL ℓ c) y)
valCh-β zero     () y
valCh-β (suc a)  c y = refl
valCh-β (lim g)  n y = refl
valCh-β (Ωₗ k h) c y = refl

val-upz : (ℓ : L) (c : Ch ℓ) (x : Tr ℓ) (y : Tr (chL ℓ c))
        → val ℓ (upz ℓ c x y) ≡ val ℓ x ⊹ emb ℓ c (val (chL ℓ c) y)
val-upz ℓ c x zero         = refl
val-upz ℓ c x y@(suc _)    = cong (val ℓ x ⊹_) (valCh-β ℓ c y)
val-upz ℓ c x y@(lim _)    = cong (val ℓ x ⊹_) (valCh-β ℓ c y)
val-upz ℓ c x y@(Ω _ _)    = cong (val ℓ x ⊹_) (valCh-β ℓ c y)
val-upz ℓ c x y@(up _ _ _) = cong (val ℓ x ⊹_) (valCh-β ℓ c y)

legCh⁻ : (ℓ : L) (c : Ch ℓ) (y : Tr (chL ℓ c)) → Leg (chL ℓ c) y
       → LegCh ℓ c (chT⁻ ℓ c y) × (chL ℓ c ⊢ zero ◃ chT ℓ c (chT⁻ ℓ c y) → chL ℓ c ⊢ zero ◃ y)
legCh⁻ zero     () y h
legCh⁻ (suc a)  c y h = h , λ d → d
legCh⁻ (lim g)  n y h = h , λ d → d
legCh⁻ (Ωₗ k h′) c y h = h , λ d → d

nz◃ : (ℓ : L) (c : Ch ℓ) (y : Tr (chL ℓ c)) → chL ℓ c ⊢ zero ◃ y → chL ℓ c ⊢ zero ◃ chT ℓ c (chT⁻ ℓ c y)
nz◃ zero     () y d
nz◃ (suc a)  c y d = d
nz◃ (lim g)  n y d = d
nz◃ (Ωₗ k h) c y d = d

upz-up : (ℓ : L) (c : Ch ℓ) (x : Tr ℓ) (y : Tr (chL ℓ c)) → Leg ℓ x → Leg (chL ℓ c) y
       → chL ℓ c ⊢ zero ◃ y → Leg ℓ (up x c (chT⁻ ℓ c y))
upz-up ℓ c x y hx hy d = hx , proj₁ (legCh⁻ ℓ c y hy) , nz◃ ℓ c y d

upz-leg : (ℓ : L) (c : Ch ℓ) (x : Tr ℓ) (y : Tr (chL ℓ c)) → Leg ℓ x → Leg (chL ℓ c) y
        → Leg ℓ (upz ℓ c x y)
upz-leg ℓ c x zero hx hy = hx
upz-leg ℓ c x y@(suc _) hx hy with zl y hy
... | inj₁ ()
... | inj₂ d = upz-up ℓ c x y hx hy d
upz-leg ℓ c x y@(lim _) hx hy with zl y hy
... | inj₁ ()
... | inj₂ d = upz-up ℓ c x y hx hy d
upz-leg ℓ c x y@(Ω _ _) hx hy with zl y hy
... | inj₁ ()
... | inj₂ d = upz-up ℓ c x y hx hy d
upz-leg ℓ c x y@(up _ _ _) hx hy with zl y hy
... | inj₁ ()
... | inj₂ d = upz-up ℓ c x y hx hy d
```

## View 的搬运与 `up` 的分解

`reidx`: 值互相 `≼` 的两个值共用 View. `mapUp`: 孩子 y 的 View 给出 `up x c y` 的 View.

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
Ω≡ p a b e = Ω≼ (λ z l → ≼Ω z l (subst (λ t → a z ≼ t) (e z) (≼-refl (a z))))
           , Ω≼ (λ z l → ≼Ω z l (subst (λ t → b z ≼ t) (sym (e z)) (≼-refl (b z))))

mapUp : (ℓ : L) (c : Ch ℓ) (x : Tr ℓ) → Leg ℓ x → VW ℓ (val ℓ x)
      → {v : V (chL ℓ c)} → VW (chL ℓ c) v → VW ℓ (val ℓ x ⊹ emb ℓ c v)
mapUp ℓ c x hx vx (vz e) = reidx (F≈ ℓ c (val ℓ x) e) vx
mapUp ℓ c x hx vx (vs y hy e) =
  vs (upz ℓ c x y) (upz-leg ℓ c x y hx hy)
     (subst (λ t → (val ℓ x ⊹ emb ℓ c _) ≈ suc t) (sym (val-upz ℓ c x y)) (F≈ ℓ c (val ℓ x) e))
mapUp ℓ c x hx vx (vl f hf st e) =
  vl (λ n → upz ℓ c x (f n)) (λ n → upz-leg ℓ c x (f n) hx (hf n))
     (λ n → subst₂ _◁_ (sym (val-upz ℓ c x (f n))) (sym (val-upz ℓ c x (f (suc n))))
                       (⊹-mono◁ (val ℓ x) (emb-mono◁ ℓ c (st n))))
     (≈-trans (F≈ ℓ c (val ℓ x) e)
              (lim≡ _ _ (λ n → sym (val-upz ℓ c x (f n)))))
mapUp ℓ c x hx vx (vΩ p g hg e) =
  vΩ (chP ℓ c p) (λ z → upz ℓ c x (g (chBr ℓ c p z)))
     (λ z l → upz-leg ℓ c x (g (chBr ℓ c p z)) hx (hg (chBr ℓ c p z) (chLeg ℓ c p z l)))
     (≈-trans (F≈ ℓ c (val ℓ x) e)
              (Ω≡ (chP ℓ c p) _ _ (λ z → sym (val-upz ℓ c x (g (chBr ℓ c p z))))))
```

## View

零, 后继, ℕ 极限, Ω 结点各读作自己; `up` 一行按层号的形状读出孩子 (与 `YiUpBlock.Up` 同), 对孩子递归.

```agda
view : (ℓ : L) (x : Tr ℓ) → Leg ℓ x → VW ℓ (val ℓ x)
view ℓ zero    h          = vz (≈-refl zero)
view ℓ (suc x) h          = vs x h (≈-refl _)
view ℓ (lim f) (hf , adj) = vl f hf (λ n → val-mono ℓ (adj n)) (≈-refl _)
view ℓ (Ω p g) h          = vΩ p g h (≈-refl _)
view zero     (up x () y) h
view (suc a)  (up x c y) (hx , hy , _) = mapUp (suc a) c x hx (view (suc a) x hx) (view a y hy)
view (lim g)  (up x n y) (hx , hy , _) = mapUp (lim g) n x hx (view (lim g) x hx) (view (g n) y hy)
view (Ωₗ k h) (up x c y) (hx , hy , _) = mapUp (Ωₗ k h) c x hx (view (Ωₗ k h) x hx) (view (h c) y hy)

brwView : BrwView SigY Tr (λ {i} x → val i x) (λ {i} x → Leg i x)
brwView = record { view = λ {i} x h → view i x h }
```
