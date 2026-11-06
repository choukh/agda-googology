# 结构关系, 第十五轮的否定 (四): 跨目标层后四种种类都实际出现; 左留右升也一出现就假

> 不读记号. 入口 [StrRel15N](StrRel15N.lagda.md). 对着接口 [StrRel15If](StrRel15If.lagda.md) (定稿 2026-11-05 10:48) 的 `NodeObl²` 写. 实例 $\Lambda_2=2$, 节点同 `StrRel13Val`: `xL` (层 $2$, 坐标层 $0$), `xR` (层 $2$, 坐标层 $1$); 运行世界 $0$, 路径 `self`. 目标 $T_0,T_1,T_2$ (层 $0,1,2$, 世界 $0$, 路径 `self`), 对齐都是 `cp00`.
>
> **(定理) 四种都出现, 种类等式都是 `NodeObl²` 的 `rkL`/`rkR` 字面上的 `refl`:**
>
> | 节点对 (坐标层) | 目标对 (目标层) | `TX` 的 $t\sqsubseteq_\infty t'$ | 种类 | 名字 |
> |---|---|---|---|---|
> | `xL`, `xL` ($0,0$) | $T_0,T_0$ ($0,0$) | `s∞` | 升, 升 | `kRR` |
> | `xL`, `xL` ($0,0$) | $T_1,T_2$ ($1,2$) | `u∞ s∞` | 留, 留 | `kKK` |
> | `xL`, `xL` ($0,0$) | $T_0,T_1$ ($0,1$) | `u∞ s∞` | **升, 留** | `kRK` |
> | `xL`, `xR` ($0,1$) | $T_1,T_1$ ($1,1$) | `s∞` | 留, 升 | `kKR` |
>
> 左升右留 (`StrRel13Rk.rk-mono` 在同一目标层时排除的那一种) 在坐标层相同 ($k=k'$, 同一个节点) 时就出现; 左留右升要 $k\ne k'$ (若 $k=k'$, 由 $k\sqsubset t\sqsubseteq_\infty t'\sqsubseteq_\infty k$ 成环, 判断, 依据 `StrRel11Rk.irr`; 没有编译). 推论 (定理): **`¬oblRK²₂`** (`xL` 对 `xL`) 与 **`¬oblKR²₂`** (`xL` 对 `xR`) 在任意状态、动作、上下文上都不成立 (由 `StrRel15NDead.rk-dead⇒`, `kr-dead⇒`).
>
> **只否定什么.** 只否定这两对节点上的 `OblRK²`, `OblKR²` (以 `RelX` 为输出关系). 不否定 `OblRR²`, `OblKK²`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel15NKind where

open import Data.Unit using (tt)
open import Data.Product using (_,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (azero)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (hz; hs; hself; hsuc; ss; D; n1; accL)
open import OCF.Align.StrRel13Val using (Λ₂; r₀; r₁; cp00)
open import OCF.Align.StrRel11Rk Λ₂ tt using (s∞; u∞)
open import OCF.Align.StrRel15If Λ₂ tt
open import OCF.Align.StrRel15NDead Λ₂ tt using (module Dead)
open P using (Tg; tg; τ₀; St; Ig; rise; keep)

T₀ : Tg azero hz azero
T₀ = τ₀ tt
T₁ : Tg azero (hs hz) azero
T₁ = tg C.self (hsuc hself) tt
T₂ : Tg azero Λ₂ azero
T₂ = tg C.self hself tt

module _ (A₀ A₀′ : Ig Λ₂ azero) (w w′ : D Λ₂ azero) (Y Y′ : St azero) where
  -- 同一个节点 xL 对 xL
  module S = NodeObl² {lV = tt} {lV′ = tt} r₀ r₀ (λ _ _ _ → n1) (λ _ _ _ → n1) tt tt
                      (accL Λ₂) (accL hz) (accL Λ₂) (accL hz) C.self C.self hself hself A₀ A₀′ w w′ Y Y′
  module SD = Dead {lV = tt} {lV′ = tt} r₀ r₀ (λ _ _ _ → n1) (λ _ _ _ → n1) tt tt
                   (accL Λ₂) (accL hz) (accL Λ₂) (accL hz) C.self C.self hself hself A₀ A₀′ w w′ Y Y′
  -- 坐标层 0 对 1: xL 对 xR
  module X = NodeObl² {lV = tt} {lV′ = tt} r₀ r₁ (λ _ _ _ → n1) (λ _ _ _ → n1) tt tt
                      (accL Λ₂) (accL hz) (accL Λ₂) (accL (hs hz)) C.self C.self hself hself A₀ A₀′ w w′ Y Y′
  module XD = Dead {lV = tt} {lV′ = tt} r₀ r₁ (λ _ _ _ → n1) (λ _ _ _ → n1) tt tt
                   (accL Λ₂) (accL hz) (accL Λ₂) (accL (hs hz)) C.self C.self hself hself A₀ A₀′ w w′ Y Y′

  kRR : (S.rkL T₀ ≡ rise) × (S.rkR T₀ ≡ rise)
  kRR = refl , refl

  kKK : (S.rkL T₁ ≡ keep (ss hself)) × (S.rkR T₂ ≡ keep (ss (hsuc hself)))
  kKK = refl , refl

  kRK : (S.rkL T₀ ≡ rise) × (S.rkR T₁ ≡ keep (ss hself))
  kRK = refl , refl

  kKR : (X.rkL T₁ ≡ keep (ss hself)) × (X.rkR T₁ ≡ rise)
  kKR = refl , refl

  -- 四个目标对都是 TX
  txRR : TX tt tt T₀ T₀
  txRR = cp00 , s∞
  txKK : TX tt tt T₁ T₂
  txKK = cp00 , u∞ s∞
  txRK : TX tt tt T₀ T₁
  txRK = cp00 , u∞ s∞
  txKR : TX tt tt T₁ T₁
  txKR = cp00 , s∞

  ¬oblRK²₂ : ¬ S.OblRK²
  ¬oblRK²₂ = SD.rk-dead⇒ T₀ T₁ txRK (ss hself) refl refl

  ¬oblKR²₂ : ¬ X.OblKR²
  ¬oblKR²₂ = XD.kr-dead⇒ T₁ T₁ txKR (ss hself) refl refl
```
