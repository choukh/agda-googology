# LamIso (五): 值 — 回灌格的世界 (定理); 严格值定理未走通

> 不含记号. 入口 [LamIso](LamIso.lagda.md). 第 4 层 (只新增定理, 不改定义). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> **交付 (b) 的档.** 本篇只有**世界这一档**的定理 (同 [LeanLvVal](LeanLvVal.lagda.md)): 对一切 $n$, 头 $n$ 的回灌第 0 格的世界里, 头的顶 = 原顶 $\boxplus$ (状态在 `L n` 上的数据沿 `prtL n` 读进 `Lv (st n)` 的读回) (`Cell.top0`). 头 3: $\Omega_{L_3}$ (`Stp` 发出的数据) 读成第 3 站里坐标 $\beta+1$ 处、第 $1$ 支的新种类的 $\Omega$-结点 (`rdΩd3`), $\beta$ = 世界里 `L 3` 顶种类的顶; 基世界里就是 `kTop3` (坐标 `HB (Lv (st 2))`; `rdΩd3-base`), 主候选 `TVs` 的头 3 读不出这个种类 (否定一路 `NegLeanLvS.no-top3-RLs`). 状态取 $\Omega_t$ 时升上来的顶含它 (`CellΩ3.top0-Ωd`). 头 4 同样不再有损 (`rdΩd4`, 一个 $\Omega$-结点).
>
> **世界变大不是值变大.** 严格的值定理 (`TI` 严格高于 `TVs` 或 `TL`) 未走通, 也没有否定; 卡点同 `LeanLvVal` §3 (两边在不同世界里跑, `rkT` 的保留/上升可能不同, 闭包分支对世界的单调没有定理), 而否定一路 `NegLeanLvVal.absorb-D` 说明 "每格严格" 推不出 "闭项严格".

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LamIsoVal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanTTree
open import OCF.Lean.LeanFbIf
open import OCF.Lean.LeanFbSt using (SLs; νS; headUp) renaming (st to stL)
open import OCF.Lean.LeanLvIf using (HasK; here; inS; inL; inΩ)
open import OCF.Lean.LeanLvEmb using (idE)
open import OCF.Lean.LamIsoPsi SLs using (X)
open import OCF.Lean.LamIsoL using (L; L⊲; prtL; Λ′; lΛ′; one′)
open import OCF.Lean.LamIsoTm
open import OCF.Lean.LamIsoShape using (kTop3)
import OCF.Lean.LeanLvRdS as RdM
import OCF.Lean.LeanTFold as Fold
open RdM SLs using (readS)
open Tree SLs hiding (inS)
open FoldTy SLs Λ′
open Fold SLs bkS Λ′ lΛ′ one′ fbI
```

## §1 $\Omega_{L_n}$ 的读回不再有损

```agda
κT3 : K X
κT3 = inj₁ (3 , inj₁ (inj₁ tt , inj₂ tt))

kO : Wd L₀ → K (Lv (stL 3))
kO W = inj₂ (hs (top X κT3 W)) , (inj₂ (hs hz) , inj₂ tt)

rdΩd3 : ∀ {W} (lW : LgW L₀ W) → HasK (kO W) (LvRd.δ (Rown 3) lW (Ωd (L 3)))
rdΩd3 lW = here

rdΩd3-base : HasK kTop3 (LvRd.δ (Rown 3) (lw₀ L₀) (Ωd (L 3)))
rdΩd3-base = here

rdΩd4 : ∀ {W} (lW : LgW L₀ W) → Σ (K (Lv (stL 4))) (λ κ → Σ (E (Lv (stL 4)) κ → HB (Lv (stL 4))) (λ g →
          LvRd.δ (Rown 4) lW (Ωd (L 4)) ≡ hΩ κ g))
rdΩd4 lW = _ , _ , refl
```

## §2 回灌格的世界

```agda
hasK-⊞ : ∀ {S : KS} {κ : K S} (a : HB S) {b} → HasK κ b → HasK κ (a ⊞ b)
hasK-⊞ a here = here
hasK-⊞ a (inS h) = inS (hasK-⊞ a h)
hasK-⊞ a (inL n h) = inL n (hasK-⊞ a h)
hasK-⊞ a (inΩ c h) = inΩ c (hasK-⊞ a h)

module Cell {ly W₀ W} (n : ℕ) (ac : AccY ly) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W)
            (lL : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) where
  c : ℕ → ClA W ly
  c = κcF ac (toFbI (feedOwn n)) u q₀ lW lL A₀ w Y

  δ₀ : HB (Lv (stL n))
  δ₀ = readS (toS (prtL n)) idE lW hz (yc (d Y) (tg ≤rf (L⊲ n) lW))

  top0 : top SLs (νS n) (wA (c zero)) ≡ top SLs (νS n) (proj₁ W) ⊞ δ₀
  top0 = rz-top (headUp n) tt δ₀ (proj₁ W)

-- 前提实例: 状态的累计输出在每个目标层 t 上取 Ωd t
Y-Ωd : ∀ {W} → St W
Y-Ωd = st (df (λ {t} _ → Ωd t)) n0 n0

module CellΩ3 {ly W₀ W} (ac : AccY ly) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W)
              (lL : LW ly W) (A₀ : Ig ly W) (w : D ly W) where
  open Cell 3 ac u q₀ lW lL A₀ w Y-Ωd

  top0-Ωd : HasK (kO W) (top SLs (νS 3) (wA (c zero)))
  top0-Ωd = subst (HasK (kO W)) (sym top0) (hasK-⊞ (top SLs (νS 3) (proj₁ W)) (rdΩd3 lW))
```
