# 裸折叠: 派发一律折叠, 根见证全为 `none`

非验收文件 (实验甲). [YiDlFold](YiDlFold.lagda.md) 的 `Fold` 取派发 `Dᵇ` (一律折叠); 公共上界按 [YiLamFold](YiLamFold.lagda.md) 的 `Lw-Ω̂`, `lgl→Lw` 另写一份, 见证全取 `none`, 不用 `selfU`, `sxU`, `witU`, `witT` 与 `dfin` 一族.
编译定理, 无前提: `TΛᵇ-legal` (读法 ψ₀(Λ)), `Twᵇ-legal`, `T⁺ʷᵇ-legal`, 都是 `Ψ-lgl` 的一次应用; `top-none` (`refl`): 见证为 `none` 时结点分支族 `Kfk`, `nrmk` 不进值. 不陈述值; 值的回归在 `YiBare*` 验收文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBareFold where
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (Way; fold; Ext; R; psum)
open import OCF.Lean.YiLamFold using (Lw; w0; ws; wl; wΩ; none; cps; lwN; Pk)
open Pk
import OCF.Lean.YiNextTower as T
open import OCF.Lean.YiDlFold using (module Fold)
```

## 1 派发与折叠

```agda
Dᵇ : ∀ k K → Ext k K
Dᵇ k K r = fold

open Fold Dᵇ public

-- 见证为 none 时, Ω 结点层号的 top 是部分和的极限; ΩT 的结点分支族 (Kfk, nrmk) 不进值.
top-none : ∀ m {k} {g : Raw k → LF} (V : ∀ η → Lgl k η → Lw (g η)) (x : Ext m (lc k g)) →
  Ψ m (wΩ V none) x G.top ≡ G.lim (psum m (λ n →
    Ψ m (V (co (ptsΩ k g V n)) (lw (ptsΩ k g V n))) (λ r → x (co (ptsΩ k g V n) , lw (ptsΩ k g V n) , r)) G.top))
top-none m V x = refl
```

## 2 见证全为 `none` 的公共上界

```agda
Lw-Ω̂ᵇ : ∀ x → T.Legal x → Lw x → Lw (upT x)
lgl→Lwᵇ : ∀ y → T.Legal y → Lw y → ∀ a → Lgl y a → Lw (up y a)

Lw-Ω̂ᵇ zero L W = ws w0
Lw-Ω̂ᵇ (suc k) L (ws W) = wΩ (λ η l → lgl→Lwᵇ k L W η l) none
Lw-Ω̂ᵇ (lim f) (st , L) (wl W s) = wl (λ n → Lw-Ω̂ᵇ (f n) (L n) (W n)) (λ n → cps (T.Ω̂-CP (st n)))
Lw-Ω̂ᵇ (lc k g) (Lk , lg , mo) (wΩ W w) = wΩ (λ η l → Lw-Ω̂ᵇ (g η) (lg η l) (W η l)) none

lgl→Lwᵇ y L W G.zero l = w0
lgl→Lwᵇ y L W (G.suc a) l = ws (lgl→Lwᵇ y L W a l)
lgl→Lwᵇ y L W (G.lim f) (st , lf) = wl (λ n → lgl→Lwᵇ y L W (f n) (lf n)) (λ n → cps (T.cp→CP y (st n)))
lgl→Lwᵇ y L W (G.lc r h) (lg , mo) = lwN y r (λ η → up y (h η)) (λ η l → lgl→Lwᵇ y L W (h η) (lg η l))
lgl→Lwᵇ (suc k) L (ws W) (G.em _ a) l = lgl→Lwᵇ k L W a l
lgl→Lwᵇ (lim f) (st , L) (wl W s) (G.em n a) l = lgl→Lwᵇ (f n) (L n) (W n) a l
lgl→Lwᵇ (lc k g) (Lk , lg , mo) (wΩ W w) (G.em (η , lη) a) l = lgl→Lwᵇ (g η) (lg η lη) (W η lη) a l
lgl→Lwᵇ y L W G.top l = Lw-Ω̂ᵇ y L W

Lw-twᵇ : ∀ n → Lw (tw n)
Lw-twᵇ zero = w0
Lw-twᵇ (suc n) = Lw-Ω̂ᵇ (tw n) (T.Legal-tw n) (Lw-twᵇ n)

VΛᵇ : Lw Λ
VΛᵇ = wl Lw-twᵇ (λ n → cps (T.tw-step n))
```

## 3 闭项

```agda
TΛᵇ : R
TΛᵇ = Ψ zero VΛᵇ (λ _ → fold) G.top

TΛᵇ-legal : Lgl zero TΛᵇ
TΛᵇ-legal = Ψ-lgl zero VΛᵇ (λ _ → fold) G.top tt

Twᵇ : ℕ → R
Twᵇ n = Ψ zero (Lw-twᵇ n) (λ _ → fold) G.top

Twᵇ-legal : ∀ n → Lgl zero (Twᵇ n)
Twᵇ-legal n = Ψ-lgl zero (Lw-twᵇ n) (λ _ → fold) G.top tt

-- 读法 ψ₀(Ω_{Ω+1})
T⁺ʷᵇ : R
T⁺ʷᵇ = Ψ zero (ws (Lw-twᵇ 2)) (λ _ → fold) G.top

T⁺ʷᵇ-legal : Lgl zero T⁺ʷᵇ
T⁺ʷᵇ-legal = Ψ-lgl zero (ws (Lw-twᵇ 2)) (λ _ → fold) G.top tt

TΛᵇ-form : TΛᵇ ≡ G.lim (psum zero Twᵇ)
TΛᵇ-form = refl
```
