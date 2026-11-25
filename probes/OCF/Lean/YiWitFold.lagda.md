# 收缩的根见证: 只留有限层号的根

非验收文件. 折叠就是 [YiDlFold](YiDlFold.lagda.md) 的 `Fold dl` (燃料搜索派发); 公共上界按 [YiLamFold](YiLamFold.lagda.md) 的 `Lw-Ω̂`, `lgl→Lw` 另写一份, 只改 Ω̂ 的 `lc` 情形的见证: `witT` 的搬运换成 `none`; `suc` 情形仍取 `witU` (根层号是字面有限数时给见证). 不用 `sxU`, `witT`.
编译定理, 无前提: `TΛ-legal` (读法 ψ₀(Λ)), `Tw-legal`, `T⁺ʷ-legal`; `TΛ-form` 是 `refl`. 不陈述值; 回归在 `YiWit*` 验收文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWitFold where
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (fold; R; psum)
open import OCF.Lean.YiLamFold using (Lw; w0; ws; wl; wΩ; none; cps; lwN; witU)
import OCF.Lean.YiNextTower as T
open import OCF.Lean.YiDlFold using (Ψ; Ψ-lgl)
```

## 1 公共上界: `lc` 层号的 Ω̂ 不带见证

```agda
Lw-Ω̂ : ∀ x → T.Legal x → Lw x → Lw (upT x)
lgl→Lw : ∀ y → T.Legal y → Lw y → ∀ a → Lgl y a → Lw (up y a)

Lw-Ω̂ zero L W = ws w0
Lw-Ω̂ (suc k) L (ws W) = wΩ (λ η l → lgl→Lw k L W η l) (witU k)
Lw-Ω̂ (lim f) (st , L) (wl W s) = wl (λ n → Lw-Ω̂ (f n) (L n) (W n)) (λ n → cps (T.Ω̂-CP (st n)))
Lw-Ω̂ (lc k g) (Lk , lg , mo) (wΩ W w) = wΩ (λ η l → Lw-Ω̂ (g η) (lg η l) (W η l)) none

lgl→Lw y L W G.zero l = w0
lgl→Lw y L W (G.suc a) l = ws (lgl→Lw y L W a l)
lgl→Lw y L W (G.lim f) (st , lf) = wl (λ n → lgl→Lw y L W (f n) (lf n)) (λ n → cps (T.cp→CP y (st n)))
lgl→Lw y L W (G.lc r h) (lg , mo) = lwN y r (λ η → up y (h η)) (λ η l → lgl→Lw y L W (h η) (lg η l))
lgl→Lw (suc k) L (ws W) (G.em _ a) l = lgl→Lw k L W a l
lgl→Lw (lim f) (st , L) (wl W s) (G.em n a) l = lgl→Lw (f n) (L n) (W n) a l
lgl→Lw (lc k g) (Lk , lg , mo) (wΩ W w) (G.em (η , lη) a) l = lgl→Lw (g η) (lg η lη) (W η lη) a l
lgl→Lw y L W G.top l = Lw-Ω̂ y L W

Lw-tw : ∀ n → Lw (tw n)
Lw-tw zero = w0
Lw-tw (suc n) = Lw-Ω̂ (tw n) (T.Legal-tw n) (Lw-tw n)

VΛ : Lw Λ
VΛ = wl Lw-tw (λ n → cps (T.tw-step n))
```

## 2 闭项

```agda
TΛ : R
TΛ = Ψ zero VΛ (λ _ → fold) G.top

TΛ-legal : Lgl zero TΛ
TΛ-legal = Ψ-lgl zero VΛ (λ _ → fold) G.top tt

Tw : ℕ → R
Tw n = Ψ zero (Lw-tw n) (λ _ → fold) G.top

Tw-legal : ∀ n → Lgl zero (Tw n)
Tw-legal n = Ψ-lgl zero (Lw-tw n) (λ _ → fold) G.top tt

-- 读法 ψ₀(Ω_{Ω+1})
T⁺ʷ : R
T⁺ʷ = Ψ zero (ws (Lw-tw 2)) (λ _ → fold) G.top

T⁺ʷ-legal : Lgl zero T⁺ʷ
T⁺ʷ-legal = Ψ-lgl zero (ws (Lw-tw 2)) (λ _ → fold) G.top tt

TΛ-form : TΛ ≡ G.lim (psum zero Tw)
TΛ-form = refl
```
