# 两种种类的单调 (十四): 闭项之间的无条件值定理

> 入口 [TpPort](TpPort.lagda.md). 不含记号. 手写. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`, 不改树、折叠、合法性.
>
> 由 [TpPortStep](TpPortStep.lagda.md) 的 `fst<F` (律 (b) 在不含 Ω-极限的右边上) 与 `LimF.grow` (ℕ-极限一步只要前 $n+1$ 项不含 Ω-极限):
>
> 1. **一切可数高度** (`embᵀ : A → Ht`, 不含 Ω-极限): 沿 $A$ 的严格序 $\ll$, $T^+$ 严格增长 (`grow≪`); 特例: 有限高度 (`growN`), $\omega$ (`growω`), $\omega+1$ (`growω1`), $\omega\cdot2$ (`growω2`).
> 2. **[TpMonoTab](TpMonoTab.lagda.md) 的条件定理里能去条件的**: ℕ-极限一步或第一位置, 涉及的项不含 Ω-极限的: `T⁺ 0 < T-Ω₂ω` (`mul<ω 0`), `T-fb₂ 0 < T-fb₂ω` (`fb₂<ω 0`), `T⁺ (cells 0) < Tᵀ`, `T⁺ (cells 1) < Tᵀ` (`cells<Tᵀ 0`, `1`), `T⁺ (cells 0) ≤ T⁺ (cells 1)` (`cells≤ 0`), `T⁺ (x 0) < Tᵁ` (`x<Tᵁ 0`).
> 3. **其余条件定理的较小一边含 Ω-极限 (编译过的事实)**: `Ω₂ᴴ`, `mul 1`, `H 0` (即 `cum 0`), `Λs₂ 1`, `cells 2`, `C₁.x 1` 都不是 `Free` (`¬F-*`). 所以本组的定理对它们不适用. 这只说明本组覆盖不到, 不否定这些比较.
>
> 值定理是值的定理 (`TLRuleSpec._≤_`), 不是对参照树的序数值验收.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TpPortTab where

open import Data.Nat using (ℕ; zero; suc) renaming (_≤_ to _≤ℕ_)
open import Data.Nat using (z≤n; s≤s)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg; _⊲_; _≪_)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.HtTowerTy using (HB; hz; hs; hl; hΩ; hself; hsuc; hlim; hLim; _⊲[_]_; LgB)
open import OCF.Align.HtTowerFTree using (Ht)
open import OCF.Align.HtTowerFClosed using (T⁺; Ω₂ᴴ; mul; Lg-mul; Ω₂ω; Lg-Ω₂ω; T-Ω₂ω)
open import OCF.Align.HtTowerNFb using (Λs₂; Λω₂; lΛω₂; T-fb₂; T-fb₂ω; isΩH; Λ₁-ΩH)
open import OCF.Align.FamFoldOne using (idx; Lg-idx; cells; cells-st; Ω₃; Tᵀ)
open import OCF.Align.UipFbClosed using (module C₁; Tᵁ)
open import OCF.Align.FamFoldAll using (H; cum)
open import OCF.Align.TpMonoIf using (_⊲⁺[_]_; psuc; plim; pLim; _⊏_)
open import OCF.Align.TpPortSim using (Free)
open import OCF.Align.TpPortStep using (fstF; fst<F; module LimF; Upto)
```

## §1 可数的高度

```agda
embᵀ : A → Ht
embᵀ azero = hz
embᵀ (asuc a) = hs (embᵀ a)
embᵀ (alim f) = hl (λ n → embᵀ (f n))

free-emb : ∀ a → Free (embᵀ a)
free-emb azero = tt
free-emb (asuc a) = free-emb a
free-emb (alim f) = λ n → free-emb (f n)

emb⊲ : ∀ {a b w} → a ⊲ b → embᵀ a ⊲[ w ] embᵀ b
emb⊲ C.self = hself
emb⊲ (C.suc p) = hsuc (emb⊲ p)
emb⊲ (C.lim n p) = hlim n (emb⊲ p)

Lg-emb : ∀ a → Lg a → LgB (embᵀ a)
Lg-emb azero _ = tt
Lg-emb (asuc a) l = Lg-emb a l
Lg-emb (alim f) (st , l) = (λ n → emb⊲ (st n)) , (λ n → Lg-emb (f n) (l n))

⁺→⊲ : ∀ {a b w} → a ⊲⁺[ w ] b → a ⊲[ w ] b
⁺→⊲ (psuc p) = hsuc p
⁺→⊲ (plim n p) = hlim n p
⁺→⊲ (pLim e p) = hLim e p

-- A 的严格序 ⇒ 一切世界里的严格第一位置
≪→⊏ : ∀ {a b} → a ≪ b → embᵀ a ⊏ embᵀ b
≪→⊏ C.zero = psuc hself
≪→⊏ (C.suc r) = psuc (⁺→⊲ (≪→⊏ r))
≪→⊏ (C.lim n r) = plim n (⁺→⊲ (≪→⊏ r))

TE : ∀ a → Lg a → A
TE a la = T⁺ (embᵀ a) (Lg-emb a la)

-- 一切可数高度: 沿 ≪ 严格增长 (无前提)
grow≪ : ∀ {a b} → a ≪ b → (la : Lg a) (lb : Lg b) → asuc (TE a la) ≤ TE b lb
grow≪ {a} {b} r la lb = fst<F (embᵀ a) (Lg-emb a la) (embᵀ b) (Lg-emb b lb) (free-emb b) (≪→⊏ r)
```

**特例.** 有限高度 $N\,n$, $\omega$, $\omega+n$, $\omega\cdot2$.

```agda
N : ℕ → Ht
N zero = hz
N (suc n) = hs (N n)

lgN : ∀ n → LgB (N n)
lgN zero = tt
lgN (suc n) = lgN n

freeN : ∀ n → Free (N n)
freeN zero = tt
freeN (suc n) = freeN n

growN : ∀ n → asuc (T⁺ (N n) (lgN n)) ≤ T⁺ (N (suc n)) (lgN n)
growN n = fst<F (N n) (lgN n) (N (suc n)) (lgN n) (freeN n) (psuc hself)

ω : Ht
ω = hl N

lgω : LgB ω
lgω = (λ n → hsuc hself) , lgN

growω : ∀ n → asuc (T⁺ (N n) (lgN n)) ≤ T⁺ ω lgω
growω n = fst<F (N n) (lgN n) ω lgω freeN (plim n hself)

growω1 : asuc (T⁺ ω lgω) ≤ T⁺ (hs ω) lgω
growω1 = fst<F ω lgω (hs ω) lgω freeN (psuc hself)

ωp : ℕ → Ht
ωp zero = ω
ωp (suc n) = hs (ωp n)

lgωp : ∀ n → LgB (ωp n)
lgωp zero = lgω
lgωp (suc n) = lgωp n

freeωp : ∀ n → Free (ωp n)
freeωp zero = freeN
freeωp (suc n) = freeωp n

lgω2 : LgB (hl ωp)
lgω2 = (λ n → hsuc hself) , lgωp

growω2 : ∀ n → asuc (T⁺ (ωp n) (lgωp n)) ≤ T⁺ (hl ωp) lgω2
growω2 n = fst<F (ωp n) (lgωp n) (hl ωp) lgω2 freeωp (plim n hself)
```

## §2 `TpMonoTab` 里能去条件的

都是 ℕ-极限一步的前几项, 这几项不含 Ω-极限: `mul 0`, `Λs₂ 0`, `cells 0` 定义地是 `hz`; `cells 1` 与 `C₁.x 0` 化简后不含 Ω-极限 (`Free` 化成 $\top$, 由 `tt` 给出, 检查器计算); `C₁.x 1` 含 (`¬F-x1`).

```agda
up0 : ∀ (f : ℕ → Ht) → Free (f 0) → Upto f 0
up0 f f0 zero z≤n = f0

-- T⁺ 0 < T⁺ (Ω₂·ω)
mul<ω₀ : asuc (T⁺ (mul 0) (Lg-mul 0)) ≤ T-Ω₂ω
mul<ω₀ = LimF.grow mul Lg-Ω₂ω 0 (up0 mul tt)

-- T⁺ 0 < T-fb₂ω
fb₂<ω₀ : asuc (T-fb₂ 0) ≤ T-fb₂ω
fb₂<ω₀ = LimF.grow (λ n → proj₁ (Λs₂ n)) lΛω₂ 0 (up0 (λ n → proj₁ (Λs₂ n)) tt)

-- T⁺ (cells 0) < Tᵀ
cells<Tᵀ₀ : asuc (T⁺ (cells 0) (proj₂ (Lg-idx Ω₃) 0)) ≤ Tᵀ
cells<Tᵀ₀ = LimF.grow cells (Lg-idx Ω₃) 0 (up0 cells tt)

up1 : Upto cells 1
up1 zero _ = tt
up1 (suc zero) _ = tt
up1 (suc (suc m)) (s≤s ())

-- T⁺ (cells 1) < Tᵀ
cells<Tᵀ₁ : asuc (T⁺ (cells 1) (proj₂ (Lg-idx Ω₃) 1)) ≤ Tᵀ
cells<Tᵀ₁ = LimF.grow cells (Lg-idx Ω₃) 1 up1

-- T⁺ (cells 0) ≤ T⁺ (cells 1)
cells≤₀ : T⁺ (cells 0) (proj₂ (Lg-idx Ω₃) 0) ≤ T⁺ (cells 1) (proj₂ (Lg-idx Ω₃) 1)
cells≤₀ = fstF (cells 0) (proj₂ (Lg-idx Ω₃) 0) (cells 1) (proj₂ (Lg-idx Ω₃) 1) tt (cells-st 0)

-- T⁺ (x 0) < Tᵁ
x<Tᵁ₀ : asuc (T⁺ (C₁.x 0) (C₁.lx 0)) ≤ Tᵁ
x<Tᵁ₀ = LimF.grow C₁.x C₁.lΛᶜ 0 (up0 C₁.x tt)
```

## §3 其余条件定理的较小一边含 Ω-极限

```agda
¬F-Ω₂ : Free Ω₂ᴴ → ⊥
¬F-Ω₂ ()

¬F-mul1 : Free (mul 1) → ⊥
¬F-mul1 ()

¬F-H0 : Free (H 0) → ⊥
¬F-H0 ()

¬F-cum0 : Free (cum 0) → ⊥
¬F-cum0 ()

ΩH→¬F : ∀ h → isΩH h ≡ true → Free h → ⊥
ΩH→¬F hz () f
ΩH→¬F (hs h) () f
ΩH→¬F (hl g) () f
ΩH→¬F (hΩ κ g) e ()

¬F-Λs₂1 : Free (proj₁ (Λs₂ 1)) → ⊥
¬F-Λs₂1 = ΩH→¬F (proj₁ (Λs₂ 1)) Λ₁-ΩH

¬F-cell₂ : Free (cells 2) → ⊥
¬F-cell₂ ()

¬F-x1 : Free (C₁.x 1) → ⊥
¬F-x1 ()
```
