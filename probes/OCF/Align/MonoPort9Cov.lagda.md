# Ω-极限高度 (九): 走过的坐标覆盖 $V_\omega$ 之下

> 入口 [MonoPort9](MonoPort9.lagda.md) (接手清单第 2 项的续). 不含记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`. 不改已有文件.
>
> - `cov`: 一次 `Walk` 沿路径 $p : a_0 \lhd b$ 走. 对一切 $x \ll b$: 要么 $x$ 落在某个走过的坐标 $c$ 之下 ($x \ll c$ 或 $x \equiv c$), 要么 $x \ll a_0$. 对 $b$ 的结构归纳, 照 `Walk` 的三句; `lim n p` 一句里, $x \ll f(k)$ 先抬到第 $k$ 段的终点 $f(k+n+1)$ (`≪⊳`, `tailP`), 再从第 $k$ 段往回找到第一段覆盖它的 (`down`).
> - `covCell`: 回灌的格首尾相接 (第 $n+1$ 格从 $V_n$ 起, 第 $0$ 格从 $0$ 起), 所以对一切 $x \ll V_n$, 有某个 $k\le n$ 的格走过的坐标 $c$, $x \ll c$ 或 $x\equiv c$. 由此 `covω`: 对一切 $x \ll V_\omega$.
> - **`allBelow`**: 对一切合法的 $a \ll V_\omega$ ($\Omega$ 处的 $V_\omega$), $T_a < T_\Omega$. 前提 $a \ll V_\omega$ 可满足: 例如 $V_0 = 1+\omega$ 之下的一切 $1+m$ (`ex-fin`, `allFin`), 以及每一格走过的坐标 (`walked≪`, `ex-cell`: 对每个 $n$, 第 $n$ 格走过的某个 $c$ 有 $c \ll V_\omega$).
>
> 与 [MonoPort9Neg](MonoPort9Neg.lagda.md) 合看: $V_\omega$ 与 $T_\Omega$ 在值上互相 $\le$ (`MonoPort9Cell.Cell.Vω≤T`, `T≤Vω`), 而 `no-all` 在 $a=T_\Omega$ 处失败. 本文的范围是**字面的** $a \ll V_\omega$ ($\ll$ 是路径, 不是值的序); 不说值上低于 $T_\Omega$ 的一切 $a$ (判断: 那要 "值 < 推出某个字面 ≪" 一类的引理, 没写).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPort9Cov where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; ≤-refl)
open import OCF.Align.HtFeedTree using (H; LgH; hΩ; tailP; pt; n1; n0; _⨾_)
open import OCF.Align.HtFeedClosed using (TΛ; one)
open import OCF.Align.HtFeedHt using (emb; Lg-emb; Ωᴴ; Lg-Ωᴴ)
open import OCF.Align.HtCrossVInst using (free-emb)
open import OCF.Align.HtCrossVSim using (Free)
open import OCF.Align.MonoPort7Lim using (TE)
open import OCF.Align.MonoPort8Om using (module Om)
open import OCF.Align.MonoPort9One using (Walked; wHere; wThere; wPre; wSub)
open import OCF.Align.MonoPort9Walk using (module WE)
open import OCF.Align.MonoPort9Cell using (growΩᴴC; below≪)
open import OCF.Align.MonoPort9Inh using (module Inh)
```

## 1 小件

```agda
-- ≪ 之后接一段第一位置, 仍是 ≪
≪⊳ : ∀ {x y z} → x ≪ y → y ⊲ z → x ≪ z
≪⊳ h C.self = h
≪⊳ h (C.suc q) = C.suc (≪⊳ h q)
≪⊳ h (C.lim n q) = C.lim n (≪⊳ h q)

-- 走过的坐标是合法的
walkedLg : ∀ {b a} {p : a ⊲ b} {lb : Lg b} {c} → Walked b p lb c → Lg c
walkedLg {lb = lb} wHere = lb
walkedLg (wThere h) = walkedLg h
walkedLg (wPre h) = walkedLg h
walkedLg (wSub m h) = walkedLg h

-- 走过的坐标字面地在 Walk 的终点之下
walked≪ : ∀ {b a} {p : a ⊲ b} {lb : Lg b} {c} → Walked b p lb c → c ≪ b
walked≪ wHere = C.zero
walked≪ (wThere h) = C.suc (walked≪ h)
walked≪ (wPre {n = n} h) = C.lim n (walked≪ h)
walked≪ (wSub {n = n} m h) = C.lim (suc (m + n)) (walked≪ h)

Under : ∀ b {a} → a ⊲ b → Lg b → A → Set
Under b p lb x = Σ A (λ c → Walked b p lb c × ((x ≪ c) ⊎ (x ≡ c)))

```

## 2 一次 `Walk` 的覆盖

```agda
cov : ∀ b {a₀} (p : a₀ ⊲ b) (lb : Lg b) {x} → x ≪ b → Under b p lb x ⊎ (x ≪ a₀)
cov b C.self lb h = inj₂ h
cov (asuc c) (C.suc p) lb C.zero = inj₁ (c , (wHere , inj₂ refl))
cov (asuc c) (C.suc p) lb (C.suc h) with cov c p lb h
... | inj₁ (c′ , (w , e)) = inj₁ (c′ , (wThere w , e))
... | inj₂ h′ = inj₂ h′
cov (alim f) {a₀} (C.lim n p) (stp , wl) {x} (C.lim k h) = goPre (down k (subst (λ j → x ≪ f (suc j)) (+-comm n k) (≪⊳ h (tailP f stp C.self (suc n)))))
  where
  U = Under (alim f) (C.lim n p) (stp , wl) x
  -- 第 m 段往回: x ≪ 第 m 段的终点 ⇒ 被第 ≤ m 段覆盖, 或 x ≪ f n
  down : ∀ m → x ≪ f (suc (m + n)) → U ⊎ (x ≪ f n)
  down m h₁ with cov (f (suc (m + n))) (stp (m + n)) (wl (suc (m + n))) h₁
  ... | inj₁ (c′ , (w , e)) = inj₁ (c′ , (wSub m w , e))
  down zero h₁ | inj₂ h₂ = inj₂ h₂
  down (suc m) h₁ | inj₂ h₂ = down m h₂
  goPre : U ⊎ (x ≪ f n) → U ⊎ (x ≪ a₀)
  goPre (inj₁ u) = inj₁ u
  goPre (inj₂ h₃) with cov (f n) p (wl n) h₃
  ... | inj₁ (c′ , (w , e)) = inj₁ (c′ , (wPre w , e))
  ... | inj₂ h₄ = inj₂ h₄
```

## 3 回灌的格首尾相接

```agda
module Cv (g : A → H) (l : LgH (hΩ g)) (fg : ∀ c → Free (g c)) where
  open WE g l fg using (Vn; Vω)
  open Om g l using (module P; κ)

  CellUnder : A → Set
  CellUnder x = Σ ℕ (λ k → Under (Vn k) (P.av (κ k)) (P.lv (κ k)) x)

  covCell : ∀ n {x} → x ≪ Vn n → CellUnder x
  covCell n {x} h with cov (Vn n) (P.av (κ n)) (P.lv (κ n)) h
  ... | inj₁ u = n , u
  covCell zero h | inj₂ ()
  covCell (suc n) h | inj₂ h′ = covCell n h′

  covω : ∀ {x} → x ≪ Vω → CellUnder x
  covω (C.lim n h) = covCell n h
```

## 4 结论: $\Omega$ 处, 一切 $a \ll V_\omega$

```agda
module CvΩ = Cv emb Lg-Ωᴴ free-emb

VωΩ : A
VωΩ = WE.Vω emb Lg-Ωᴴ free-emb

allBelow : ∀ a (la : Lg a) → a ≪ VωΩ → asuc (TE a la) ≤ TΛ Ωᴴ Lg-Ωᴴ
allBelow a la h with CvΩ.covω h
... | n , (c , (w , inj₁ ac)) = below≪ n ac la (walkedLg w) w
... | n , (c , (w , inj₂ refl)) = growΩᴴC n w (Lg-emb a la)

-- 前提可满足: 第 0 格的世界 V₀ = 1 + ω 之下的一切有限 a
module OΩ = Om emb Lg-Ωᴴ

f₀ : ℕ → A
f₀ = pt {one} one (λ _ → n1 ⨾ n0)

ex-fin : ∀ m → f₀ m ≪ VωΩ
ex-fin m = C.lim 0 (C.lim (suc m) C.zero)

allFin : ∀ m (la : Lg (f₀ m)) → asuc (TE (f₀ m) la) ≤ TΛ Ωᴴ Lg-Ωᴴ
allFin m la = allBelow (f₀ m) la (ex-fin m)

-- 前提在每一格都可满足: 第 n 格走过的坐标 (Inh.walked n) 都 ≪ V_ω
ex-cell : ∀ n → Σ A (λ c → c ≪ VωΩ)
ex-cell n = proj₁ (Inh.walked emb Lg-Ωᴴ n) , C.lim n (walked≪ (proj₂ (Inh.walked emb Lg-Ωᴴ n)))
```
