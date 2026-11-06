# 布劳威尔树的 View (四): 高度树 `H`, 检验记录本身

> 不含记号. 入口 [BrwView](BrwView.lagda.md). 高度树 `H` ([HtFeedTree](HtFeedTree.lagda.md)) 本身就是布劳威尔树, View 是恒等, 值一致是自反. 这一篇只检验记录 `BrwView` 能装下它.
>
> - 值前序 `_≤ᴴ_`: 同 `EndLowH` 的那一个 (四条加 $\Omega$-极限两条, 取遍**一切**坐标 $c:A$). 这里重写一遍, 不导入 `EndLowH` (导入闭包的约定).
> - 步进: `LgH` 里 $\mathbb N$-极限的那一条, `_⊲[ azero ]_`.
> - $\Omega$-极限一种, 坐标 `A`, 坐标的合法性 `Lg`. **部分的合法性只在合法坐标上有** (`LgH (hΩ g)` 只给 `Lg c → LgH (g c)`), 而值取遍一切坐标. 记录用 `LgC` 把这一点写在类型里. 这就是第二次审查说的 "`hΩ g` 的分支取遍 `A` 含不合法坐标": View 能写, 但与 "按低层合法树分支" 只在合法坐标上同形.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwViewHt where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import OCF.Align.CumReadCF using (A; azero; Lg)
open import OCF.Align.HtFeedTree using (H; hz; hs; hl; hΩ; _⊲[_]_; LgH)
open import OCF.Align.BrwViewDef
```

## §1 值前序

```agda
infix 4 _≤ᴴ_
data _≤ᴴ_ : H → H → Set where
  z≤ᴴ : ∀ {b} → hz ≤ᴴ b
  s≤ᴴ : ∀ {a b} → a ≤ᴴ b → hs a ≤ᴴ hs b
  ≤hl : ∀ {a f} n → a ≤ᴴ f n → a ≤ᴴ hl f
  hl≤ : ∀ {f b} → (∀ n → f n ≤ᴴ b) → hl f ≤ᴴ b
  ≤hΩ : ∀ {a g} c → a ≤ᴴ g c → a ≤ᴴ hΩ g
  hΩ≤ : ∀ {g b} → (∀ c → g c ≤ᴴ b) → hΩ g ≤ᴴ b

≤ᴴ-refl : ∀ a → a ≤ᴴ a
≤ᴴ-refl hz = z≤ᴴ
≤ᴴ-refl (hs a) = s≤ᴴ (≤ᴴ-refl a)
≤ᴴ-refl (hl f) = hl≤ (λ n → ≤hl n (≤ᴴ-refl (f n)))
≤ᴴ-refl (hΩ g) = hΩ≤ (λ c → ≤hΩ c (≤ᴴ-refl (g c)))
```

## §2 签名与 View

```agda
Sigᴴ : Sig
Sigᴴ = record
  { Ix = ⊤ ; B = λ _ → H ; _≼_ = _≤ᴴ_ ; Stp = λ a b → a ⊲[ azero ] b
  ; Kd = λ _ → ⊤ ; Cd = λ _ → A ; LgC = Lg ; tg = λ _ → tt
  ; bz = hz ; bs = hs ; bl = hl ; bΩ = λ _ → hΩ }

viewᴴ : BrwView Sigᴴ (λ _ → H) (λ h → h) LgH
viewᴴ = record { view = v }
  where
  v : ∀ {i} (x : H) → LgH x → View Sigᴴ (λ _ → H) (λ h → h) LgH i x
  v hz _ = vz (z≤ᴴ , z≤ᴴ)
  v (hs h) l = vs h l (≤ᴴ-refl _ , ≤ᴴ-refl _)
  v (hl f) (st , l) = vl f l st (≤ᴴ-refl _ , ≤ᴴ-refl _)
  v (hΩ g) (mo , l) = vΩ tt g l (≤ᴴ-refl _ , ≤ᴴ-refl _)
```
