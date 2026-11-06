# ValW (一): 结点的 "保留/上升" 在两个世界里

> 不含记号. 入口 [ValW](ValW.lagda.md), 接口 [ValWIf](ValWIf.lagda.md). 第 4 层: 只新增定理. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延.
>
> 此前 [LeanLvVal](LeanLvVal.lagda.md) §3 卡点 (a) 的判断: "世界变大后右边可能出现左边没有的结点证据 (`keep` 对 `rise`)". 本篇把它分成两件:
>
> - **同层** (`rk-agree`, 定理, 接口律 R1): 同一个结点层 $k$, 同一个目标层 $t$, 目标世界 $m_1\le m_2$, 两个实例 (级回灌参数任意) 的决定一致. 世界变大**不会**让同层的决定分歧. 依据: "上升" 带证据 $t\lhd k$ (在自己的世界里), 世界变大保持 $\lhd$, 与对面的 "保留" ($k$ 是 $t$ 的直接前驱的第一位置) 拼成 $k$ 的自环, 与可达矛盾.
> - **两个层** (`rk-cross`, 定理, 接口律 R2): 结点层 $k_1\lhd k_2$ 时, "左上升右保留" 不出现; 其余三种都可能. "左保留右上升" 确实出现 (`kr-occurs`, 定理, 在 `TL`/`TF` 的参数上, $k_1=0$, $k_2=1$, $t=1$, 基世界).
>
> 所以卡点 (a) 只在两边结点层不同时存在. 两边结点层不同的来源: $\Omega_L$ 的 $\Omega$-行在世界 $W'$ 里过第 $g(\mathrm{top}\,\kappa\,W')$ 层, 回灌把右边的世界升高, 右边走到的层更高 (见 [ValWRel](ValWRel.lagda.md)).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTTree
module OCF.Lean.ValWRk (T : KS) (bk : Tree.BotK T) (Λ : HB (step T)) (lΛ : LgB Λ)
  (one⊲ : ∀ {w} → hs hz ⊲[ w ] Λ) (fb₁ fb₂ : K T → FoldTy.Fb T Λ ⊎ ⊤) where

open import Data.Empty using (⊥; ⊥-elim)
import OCF.Lean.LeanTFold as Fold
open import OCF.Lean.ValWIf T bk Λ lΛ one⊲ fb₁ fb₂
open Tree T
open FoldTy T Λ
```

## §1 "上升" 的证据

`Valid x`: 保留无条件; 上升带 $t\lhd k$ (在目标世界里). 对一切级回灌参数, `rkT` 的结果都满足它 (照 `rkT` 的 `with` 逐行).

```agda
irrS : ∀ {W k} → AccY {L₀} k → StH W k k → ⊥
irrS (acc g) R = irrS (g R) R

module Val (fb : K T → Fb ⊎ ⊤) where
  open Fold T bk Λ lΛ one⊲ fb

  Valid : ∀ {k t m} → Rk k t m → Set
  Valid (keep R) = ⊤
  Valid {k} {t} {m} rise = t ⊲[ m ] k

  rkS-valid : ∀ {k t m} (p : k ⊲[ m ] t) → Valid (rkS p)
  rkS-valid hself = hself
  rkS-valid (hsuc p) = tt
  rkS-valid (hlim n p) = tt
  rkS-valid (hLim e p) = tt

  rk-valid : ∀ {k t m} (km : k ⊲[ m ] Λ) (tm : t ⊲[ m ] Λ) (lm : LgW L₀ m) → Valid (rkT km tm lm)
  rk-valid km tm lm with cmpB km tm lm lΛ
  ... | inj₁ t⊲k = t⊲k
  ... | inj₂ k⊲t = rkS-valid k⊲t

module V₁ = Val fb₁
module V₂ = Val fb₂
```

## §2 同层: 两边一致 (律 R1)

```agda
agree : ∀ {k t m₁ m₂} → m₁ ≤ m₂ → (x₁ : F₁.Rk k t m₁) (x₂ : F₂.Rk k t m₂) → V₁.Valid x₁ → V₂.Valid x₂ → RkSame x₁ x₂
agree q (F₁.keep R₁) (F₂.keep R₂) _ _ = kp
agree q (F₁.keep R₁) F₂.rise _ t⊲k = ⊥-elim (irrS accᴸ (Sk (Kup q R₁) t⊲k))
agree q F₁.rise (F₂.keep R₂) t⊲k _ = ⊥-elim (irrS accᴸ (Sk R₂ (⊲ᴮ↑ q t⊲k)))
agree q F₁.rise F₂.rise _ _ = rs

rk-agree : RkAgree
rk-agree q km₁ tm₁ lm₁ km₂ tm₂ lm₂ =
  agree q (F₁.rkT km₁ tm₁ lm₁) (F₂.rkT km₂ tm₂ lm₂) (V₁.rk-valid km₁ tm₁ lm₁) (V₂.rk-valid km₂ tm₂ lm₂)
```

## §3 两个层: "左上升右保留" 不出现 (律 R2)

```agda
cross : ∀ {k₁ k₂ t m₁ m₂} → m₁ ≤ m₂ → k₁ ⊲[ m₂ ] k₂ →
        (x₁ : F₁.Rk k₁ t m₁) (x₂ : F₂.Rk k₂ t m₂) → V₁.Valid x₁ → V₂.Valid x₂ → RkR x₁ x₂
cross q e (F₁.keep R₁) (F₂.keep R₂) _ _ = kp
cross q e (F₁.keep R₁) F₂.rise _ _ = kr
cross q e F₁.rise (F₂.keep R₂) t⊲k₁ _ = ⊥-elim (irrS accᴸ (Sk R₂ (⊲ᴮ-tr (⊲ᴮ↑ q t⊲k₁) e)))
cross q e F₁.rise F₂.rise _ _ = rs

rk-cross : RkCross
rk-cross q e km₁ tm₁ lm₁ km₂ tm₂ lm₂ =
  cross q e (F₁.rkT km₁ tm₁ lm₁) (F₂.rkT km₂ tm₂ lm₂) (V₁.rk-valid km₁ tm₁ lm₁) (V₂.rk-valid km₂ tm₂ lm₂)
```
