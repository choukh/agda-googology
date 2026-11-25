# `Tw 3` 的计算问到目标层是极限的派发

非验收文件. 编译定理: 层号 `lc J (up J)` 的 Ω 结点 (`J` 是 ℕ 极限层号, `finOf J ≡ nothing`) 的折叠 `NJ` 是 `Tw 3` 的第一位置或右加数 (`asked◁`, 关系 `_◁_`); 它的链第 1 点用 `stp = dfin J (up J top)`, 一律折叠 (`step-fold`, `pt1`).
这一步的第 0 个分量的根由位置 `r♯` (层号 1) 派发 (`comp0`), 派发是折叠 (`lost`), 而 `J` 有层号 1 的槽位 (`could`). `Tw 2` 的各支没有 Ω 结点 (`noΩ₂`). 值的形式 (`≼`) 在 [YiLamNAskV](YiLamNAskV.lagda.md).
不陈述丢掉的值有多少.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLamNAsk where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (R; lev; Way; keep; fold; Ext; psum; succ; ΩT)
open import OCF.Lean.YiLamFold
open import OCF.Lean.YiLamNInst using (bS; bL; bC; ωw; stp; cpt; cpt-lgl)
open import OCF.Lean.YiUniIf using (At)
```

## 1 第一位置或右加数

`a ◁ b`: 沿 ℕ 极限的分量与第 0 层加法的右加数从 `b` 走到 `a`. 值上 `a ≼ b` (验收文件).

```agda
data _◁_ : R → R → Set where
  here   : ∀ {a} → a ◁ a
  inLim  : ∀ {a f} n → a ◁ f n → a ◁ G.lim f
  inPlus : ∀ {a} p b → a ◁ b → a ◁ plus zero p b

inΣ : ∀ h n {a} → a ◁ h n → a ◁ G.lim (psum zero h)
inΣ h zero q = inLim zero q
inΣ h (suc n) q = inLim (suc n) (inPlus (psum zero h n) (h (suc n)) q)

ΩT0 : ∀ k (w : Way zero k) K o {a} → a ◁ G.lim o → a ◁ ΩT zero k w K o
ΩT0 k (keep () e) K o q
ΩT0 k fold K o q = q

obsL : ∀ {f} → Lw (lim f) → ℕ → R
obsL V n = Ψ zero (bL V n) (λ _ → fold) G.top

obsΩ : ∀ {k g} → Lw (lc k g) → ℕ → R
obsΩ V n = Ψ zero (bC V (cpt V n) (cpt-lgl V n)) (λ _ → fold) G.top

stepL : ∀ {f} (V : Lw (lim f)) n {a} → a ◁ obsL V n → a ◁ Ψ zero V (λ _ → fold) G.top
stepL (wl V st) n q = inΣ _ n q

stepΩ : ∀ {k g} (V : Lw (lc k g)) n {a} → a ◁ obsΩ V n → a ◁ Ψ zero V (λ _ → fold) G.top
stepΩ {k} {g} (wΩ V w) n q = ΩT0 k (rootW zero k g w (λ _ → fold)) _ _ (inΣ _ n q)
```

## 2 那个结点

`Y = succ zero top`; `J = ⌜top + Y⌝`. 路径: `tw 3` 的链点 1, 再沿 ℕ 极限层号的分量 0, 1, 0, 1, 0.

```agda
Y : R
Y = succ zero G.top

J : LF
J = up zero (plus zero G.top Y)

A B C D E : Σ LF Lw
A = _ , bC (Lw-tw 3) (cpt (Lw-tw 3) 1) (cpt-lgl (Lw-tw 3) 1)
B = _ , bL (proj₂ A) 0
C = _ , bL (proj₂ B) 1
D = _ , bL (proj₂ C) 0
E = _ , bL (proj₂ D) 1

VJ : Lw (lc J (up J))
VJ = bL (proj₂ E) 0

NJ : R
NJ = Ψ zero VJ (λ _ → fold) G.top

asked◁ : NJ ◁ Tw 3
asked◁ = stepΩ (Lw-tw 3) 1 (stepL (proj₂ A) 0 (stepL (proj₂ B) 1 (stepL (proj₂ C) 0
  (stepL (proj₂ D) 1 (stepL (proj₂ E) 0 here)))))
```

## 3 它的链用极限目标上的 `dfin`

```agda
J-nonfin : finOf J ≡ nothing
J-nonfin = refl

step-is-dfin : stp VJ G.top tt ≡ dfin J (up J G.top)
step-is-dfin = refl

step-fold : ∀ r → stp VJ G.top tt r ≡ fold
step-fold r = refl

NJ-form : NJ ≡ G.lim (psum zero (obsΩ VJ))
NJ-form = refl

pt1 : cpt VJ 1 ≡ plus J G.top (Ψ J (bC VJ G.top tt) (λ _ → fold) G.top)
pt1 = refl
```

链第 1 点要算的 `top` 像是 ℕ 极限层号 `J` 上的部分和; 第 0 个分量是层号 `upT 2` 的 Ω 结点, 它的根由位置 `r♯` 派发.

```agda
ρ♯ : Pre (upT (suc zero))
ρ♯ = G.suc (G.suc G.zero) , tt , inj₁ tt

r♯ : Pre (upT J)
r♯ = 0 , G.top , tt , ρ♯

r♯-lev : lev (upT J) r♯ ≡ suc zero
r♯-lev = refl

comp0 : ωw J (bL (bC VJ G.top tt) 0) (λ r → stp VJ G.top tt (0 , r)) ≡ stp VJ G.top tt r♯
comp0 = refl

lost : stp VJ G.top tt r♯ ≡ fold
lost = refl

could : At J (lev (upT J) r♯)
could = (0 , inj₁ tt) , refl
```

## 4 `Tw 2` 的各支没有 Ω 结点

`dfin` 只出现在 `cmpw` 的 `wΩ` 子句与 `ptsΩ` 里; `tw 2` 的根层号是 `lc zero ⌜_⌝`, 它的链只用 `dfin zero` (判断: 所以塔里第一个极限目标在 `Tw 3`).

```agda
NoΩ : ∀ {k} → Lw k → Set
NoΩ w0 = ⊤
NoΩ (ws V) = NoΩ V
NoΩ (wl V st) = ∀ n → NoΩ (V n)
NoΩ (wΩ V w) = ⊥

noΩ₂ : ∀ η l → NoΩ (bC (Lw-tw 2) η l)
noΩ₂ G.zero l = tt
noΩ₂ (G.suc a) l = noΩ₂ a l
noΩ₂ (G.lim f) (st , lf) = λ n → noΩ₂ (f n) (lf n)
noΩ₂ (G.lc () g) l
noΩ₂ (G.em () a) l
noΩ₂ G.top l = tt
```
