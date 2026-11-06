# Ω-极限高度 (七): 回灌每一格的每个走过的坐标

> 入口 [MonoPort9](MonoPort9.lagda.md). 不含记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.
>
> 合起来: 重做的格 ([MonoPort9Walk](MonoPort9Walk.lagda.md)) 全在世界 $V_\omega$ 里, 状态自洽 (`gZ`, 每格由 [MonoPort9One](MonoPort9One.lagda.md) 的 `WG`), 以字面的起始段为最左一段 (`pZ`); 对重做的第 $n$ 格用路径归纳 `WL`, 再用 `cell≈` 把和换回实际的第 $n$ 格, 最后 $T_\Lambda=\lim_n(\mathrm{pt}\,b\,D)$ (`MonoPort8Om.Om.TΛ≡`, 定义性的).
>
> 结论 `growC`: $g$ 的分支都不含 Ω-极限 ⇒ 对一切 $n$ 与第 $n$ 格走过的一切坐标 $c$, $T_{g(c)} < T_{\mathrm{h\Omega}\,g}$. 特例 `growΩᴴC` ($\Omega$ 本身, 无前提) 与 `below≪`: 对一切 $a \ll c$, $c$ 是某一格走过的坐标, $T_a < T_\Omega$. `growC∃`: 每一格都有走过的坐标 ([MonoPort9Inh](MonoPort9Inh.lagda.md) 的 `walked`), 所以 `growC n` 对每个 $n$ 都不空; `ex0`, `exS` 是第 0 格的具体居留 ($0$ 与一切 $1+m$). `Vω≤T`, `T≤Vω`: 重做用的世界 $V_\omega=\lim_n V_n$ 与 $T_\Lambda$ 在值上互相 $\le$ (走过的坐标都在 $V_\omega$ 之下; 与 [MonoPort9Neg](MonoPort9Neg.lagda.md) 合看, 见入口 §3).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPort9Cell where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; s≤; ≤l; l≤; ≤-refl; ≤-trans; ≤-suc)
open import OCF.Align.HtFeedTree
open import OCF.Align.HtFeedClosed using (module At; TΛ; one)
open import OCF.Align.HtFeedGrow using (sum≥)
open import OCF.Align.HtFeedHt using (emb; Lg-emb; Ωᴴ; Lg-Ωᴴ)
open import OCF.Align.HtCrossVSim using (Free)
open import OCF.Align.HtCrossVInst using (free-emb)
open import OCF.Align.MonoPort8Om using (module Om; drp≤)
open import OCF.Align.MonoPort8Fin using (here; left)
open import OCF.Align.MonoPort7Lim using (TE; grow≪)
open import OCF.Align.MonoPort9One using (Walked; wHere; wPre; wSub; module One)
open import OCF.Align.MonoPort9Walk using (module WE)
open import OCF.Align.MonoPort9Inh using (module Inh)
```

## 1 重做的格: 自洽, 前缀

```agda
module Cell (g : A → H) (l : LgH (hΩ g)) (fg : ∀ c → Free (g c)) where
  open WE g l fg using (Vn; Vω; lω; X; X₁; co′; Z; Δ′; Δ; cell≈)
  open Om g l using (Λ; module P; κ; b; Dn; one≤b)
  open One g l fg Vω lω X₁ using (module R7; Pfx; gZ₀; g⊕; WG; WL)

  gZ : ∀ n → R7.Good (Z n)
  gZ zero = gZ₀
  gZ (suc n) = g⊕ {Z n} {Δ′ n} (gZ n) (WG (Vn n) (P.av (κ n)) (P.ap (κ n)) (P.lv (κ n)) (X n) (co′ n) (Z n) (gZ n))

  pZ : ∀ n → Pfx (Z n)
  pZ zero T = here
  pZ (suc n) T = left (pZ n T)

  ptb : ∀ n → b ≤ pt b Dn n
  ptb zero = ≤-refl b
  ptb (suc n) = ≤-trans (ptb n) (sum≥ (pt b Dn n) (Dn n))
```

## 2 结论

```agda
  growC : ∀ n {c} → Walked (Vn n) (P.av (κ n)) (P.lv (κ n)) c → ∀ (lk : LgH (g c)) → asuc (TΛ (g c) lk) ≤ TΛ Λ l
  growC n h lk =
    ≤-trans (WL (Vn n) (P.av (κ n)) (P.ap (κ n)) (P.lv (κ n)) (X n) (co′ n) (Z n) (gZ n) (pZ n) (pt b Dn n) (≤-trans one≤b (ptb n)) h lk)
    (≤-trans (cell≈ n (pt b Dn n))
    (≤-trans (drp≤ (≤-refl (pt b Dn n)) (P.yc (Δ n) (P.τ₀ (P.lv (κ n)))))
             (≤l (suc n) (≤-refl _))))

  -- 回灌的世界在值上就是闭项: V_n 与部分和 pt b D n 互相 ≤, 所以 V_ω 与 T_Λ 互相 ≤
  drp≥ : ∀ {W W′} {c c′} → c ≤ c′ → (x : D₀ W) → sum c (drp {W} {W′} x) ≤ sum c′ x
  pdrp≥ : ∀ {W W′} {c c′} → c ≤ c′ → (d : ℕ → D₀ W) → ∀ n → pt c (λ m → drp {W} {W′} (d m)) n ≤ pt c′ d n
  drp≥ h n0 = h
  drp≥ h n1 = s≤ h
  drp≥ h (x ⨾ y) = drp≥ (drp≥ h x) y
  drp≥ h (nl d) = l≤ (λ n → ≤l n (pdrp≥ h d n))
  drp≥ h (ni () u)
  drp≥ h (nκ () u)
  drp≥ h (nw p x) = drp≥ h x
  pdrp≥ h d zero = h
  pdrp≥ h d (suc n) = drp≥ (pdrp≥ h d n) (d n)

  cellT : ∀ n → D₀ (Vn n)
  cellT n = P.yc (Δ n) (P.τ₀ (P.lv (κ n)))

  V≤pt : ∀ n → Vn n ≤ pt b Dn n
  pt≤V : ∀ n → pt b Dn n ≤ Vn n
  V≤pt zero = ≤-refl b
  V≤pt (suc n) = drp≤ (V≤pt n) (cellT n)
  pt≤V zero = ≤-refl b
  pt≤V (suc n) = drp≥ (pt≤V n) (cellT n)

  Vω≤T : Vω ≤ TΛ Λ l
  Vω≤T = l≤ (λ n → ≤l n (V≤pt n))

  T≤Vω : TΛ Λ l ≤ Vω
  T≤Vω = l≤ (λ n → ≤l n (pt≤V n))

  -- 每一格都有走过的坐标, 所以 growC 对每一格都不空 (MonoPort9Inh.walked)
  growC∃ : ∀ n → Σ A (λ c → Walked (Vn n) (P.av (κ n)) (P.lv (κ n)) c × (∀ (lk : LgH (g c)) → asuc (TΛ (g c) lk) ≤ TΛ Λ l))
  growC∃ n = proj₁ w , (proj₂ w , growC n (proj₂ w))
    where w = Inh.walked g l n

  -- Walked 有居留: 第 0 格走过 0 与一切 1 + m
  f₀ : ℕ → A
  f₀ = pt {one} one (λ _ → n1 ⨾ n0)

  ex0 : Walked (Vn 0) (P.av (κ 0)) (P.lv (κ 0)) azero
  ex0 = wPre wHere

  exS : ∀ m → Walked (Vn 0) (P.av (κ 0)) (P.lv (κ 0)) (f₀ (m + 0))
  exS m = wSub m wHere

-- Ω 本身: 一切格的一切走过的坐标, 无前提
module CΩ = Cell emb Lg-Ωᴴ free-emb
module OΩ = Om emb Lg-Ωᴴ

growΩᴴC : ∀ n {c} → Walked (WE.Vn emb Lg-Ωᴴ free-emb n) (OΩ.P.av (OΩ.κ n)) (OΩ.P.lv (OΩ.κ n)) c →
          ∀ (lk : LgH (emb c)) → asuc (TΛ (emb c) lk) ≤ TΛ Ωᴴ Lg-Ωᴴ
growΩᴴC = CΩ.growC

-- 一切 a ≪ c (c 是某一格走过的坐标): T_a < T_Ω
below≪ : ∀ n {a c} → a ≪ c → (la : Lg a) (lc : Lg c) →
         Walked (WE.Vn emb Lg-Ωᴴ free-emb n) (OΩ.P.av (OΩ.κ n)) (OΩ.P.lv (OΩ.κ n)) c →
         asuc (TE a la) ≤ TΛ Ωᴴ Lg-Ωᴴ
below≪ n {a} {c} ac la lc h = ≤-trans (grow≪ ac lc la) (≤-trans (≤-suc (≤-refl (TE c lc))) (growΩᴴC n h (Lg-emb c lc)))
```
