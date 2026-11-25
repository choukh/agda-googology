# K3 封顶 (三之三): `OutputDriven.closed` 与 `closedGrid`

> **第 4 层 (验收侧) 的判定文件.** 不改任何候选的定义, 不进成品与证书. 本篇不导入记号模块 (用不到). 一般陈述在 [K3CapSan](K3CapSan.lagda.md); 这里把它们接到 `OutputDrivenDown.With` 的每一站. 两个闭项 (`OutputDrivenClosed.closed`, `OutputDrivenGrid.closedGrid`) 的每一项都是某个世界族上的 `With.TN`, 所以对任一世界族陈述就同时盖住两个.
>
> **判决: (乙) 内容封顶的编译事实; 层号类型不封顶.** 与 [K3CapThird](K3CapThird.lagda.md) 相同的两条在这里原样成立, 因为下降用的是同一个洗法与同一个跨底折叠:
>
> 1. `driven-rep` (`refl`): 第 n 站的跨底折叠在指标分量旧种类的结点 (回灌下标是 Ω-结点时的源) 上, 等于它在代表坐标一支上的值. 代表坐标这里是 `OutputDrivenTop.topS n (worlds n) κ`, 即当前世界里该种类的实际界.
> 2. `driven-Er` (`refl`) 加 `driven-san-Ωfree`: 留下的结点的坐标经同一个洗法 `ThirdSan.Er`; 层是 Ω-结点时洗成没有 Ω-结点的树.
>
> **与 Third 不同的一条 (如实).** Third 的世界固定, 分量种类的界恒为 0 (`K3CapThird.comp-bound-zero`). 这里世界由输出更新, 这一条**不成立**: `rep-is-bound` (`refl`) 说第 c 个分量的顶新种类的代表坐标就是世界里存的那个界; 候选自己的 `OutputDrivenWorld.Driven.feedback-admitted` 说回灌的值在更新后的界之下 (已有定理, 这里重述类型). 所以这个候选比 Third 少一处损失; 上面两条仍在.
>
> **第一个 Ω-共尾派发的站在哪.** 与 Third 相同: 第 1 个底的值才有 Ω-结点, 所以是从第 2 个底向第 1 个底下降的那一步 (`With.stp 1`, 深度 1 的格 `TN 1` 的第一步). `first-feed-Ω`, `first-src-old` 说从第 1 站起每一站的第一次回灌读到的源就是旧种类的结点, 第 1 条当场生效 (编译事实: `TN-first`, `first-step-chain` 把 `With.TN (suc n)` 的第一步接到 `K3CapSan.Rep.ΦX-chain` 的链上). 深度 0 的格不经过这两条 (已有的 `GridCheckCountableSan`: 第 0 个底上洗法前后互相 `≤ᵛ`; 本篇没有重编它).
>
> **它说了什么, 没说什么.**
>
> - 编译事实: 上面各条, 对一切世界族与一切 `n`.
> - **不是值上界.** 没有证明 `closed` 或 `closedGrid` 的序数值不超过任何具名序数. 已有的值定理只有下界 `epsilon ≤ᵛ first ≤ᵛ closedGrid` (`GridBaseTowerAccept`; 本篇没有重编). 代表坐标是实际的界, 它随回灌增长, 取一支之后的值可以仍然很大.
> - 条件覆盖定理 (甲) 没有实填.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.K3CapOutputDriven where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw)
open import OCF.Lean.ThirdTw using (Sb; fl; XSof; gtX)
open import OCF.Lean.ThirdPS using (PH)
import OCF.Lean.ThirdFold as TF
import OCF.Lean.ThirdSan as TS
open import OCF.Lean.OutputDrivenTop using (topS; topS-bd)
import OCF.Lean.ThirdRichLegBuild as Rich
import OCF.Lean.OutputDrivenDown as Down
import OCF.Lean.OutputDrivenWorld as World
import OCF.Lean.OutputDrivenClosed as Closed
import OCF.Lean.OutputDrivenGrid as Grid
open import OCF.Align.K3CapSan
```

## §1 每一站用的就是一般陈述里的那几件

```agda
module _ (worlds : ∀ n → Wd (Sb n)) (legal : ∀ n → LgW (Sb n) (worlds n)) (n : ℕ) where
  module S = Down.With.St worlds legal n

  driven-Er : S.Er ≡ TS.Er (Sb n) (worlds n) (legal n) (fl n)
  driven-Er = refl

  module Wn = Wash (Sb n) (worlds n) (legal n) (fl n)

  driven-san-Ωfree : ∀ κ₀ g c → ΩFree (TF.San.san S.Er (hΩ κ₀ g) c)
  driven-san-Ωfree = Wn.san-Ωfree

  driven-rep : ∀ t B (lB : LgB B) (pt : t S.⊲ᵘ B) (b : S.GT t) κ (g : E (Sb n) κ → HB (XSof (Sb n)))
    (nd : PH S.PSX B (hΩ (inj₁ tt , inj₁ κ) g)) →
    S.ΦX t B lB pt b (hΩ (inj₁ tt , inj₁ κ) g) nd
      ≡ S.ΦX t B lB pt b (g (topS n (worlds n) κ)) (proj₂ nd (topS n (worlds n) κ) (topS-bd n (worlds n) κ))
  driven-rep t B lB pt b κ g nd = refl
```

## §1′ 从第 1 站起, 第一次回灌读到的就是旧种类的结点

与 `K3CapThird` 同一段: 第 `suc n` 站的种子是地板 `fl (suc n)`, 链的第 0 项在坐标 `sh₀ 1 (fl (suc n))` 处读源 (`K3CapSan.Rep.ΦX-chain`, `chain-first`); 这个坐标是 Ω-结点, 读到的源是旧种类的结点, `driven-rep` 生效. 这里的合法化是 `ThirdRichLegBuild.legS`, 结论相同.

```agda
module _ (worlds : ∀ n → Wd (Sb n)) (legal : ∀ n → LgW (Sb n) (worlds n)) (n : ℕ) where
  module S₁ = Down.With.St worlds legal (suc n)

  seed-is-floor : proj₁ (Down.With.seed worlds legal (suc n)) ≡ fl (suc n)
  seed-is-floor = refl

  first-feed-Ω : IsΩ (S₁.X.sh₀ (hs hz) (fl (suc n)))
  first-feed-Ω = tt

  first-src-old : IsOld (gtX (Sb (suc n)) (fl (suc n)) (S₁.X.sh₀ (hs hz) (fl (suc n))))
  first-src-old = gtX-Ω (Sb (suc n)) (fl (suc n)) (S₁.X.sh₀ (hs hz) (fl (suc n))) first-feed-Ω
```

**接到闭项的实际运行上.** 任一世界族上, `With.TN (suc n)` 的第一步是 `first-step` (`TN-first`, `refl`), 它的输出是 `K3CapSan.Rep` 里的那条链 (`first-step-chain`), 链的第 0 项等于代表坐标一支上的折叠 (`first-item-rep`).

```agda
module _ (worlds : ∀ n → Wd (Sb n)) (legal : ∀ n → LgW (Sb n) (worlds n)) (n : ℕ) where
  open Down.With worlds legal using (stp; desc; TN; Gdn; seed; own-path)
  module S₂ = Down.With.St worlds legal (suc n)
  module R = Rep (Sb (suc n)) (worlds (suc n)) (legal (suc n)) S₂.Er
    (Rich.legS (suc n)) (Rich.Lg-legS (suc n)) (topS (suc n) (worlds (suc n))) (topS-bd (suc n) (worlds (suc n)))

  first-step : HB (Sb (suc n))
  first-step = stp (suc n) (fl (suc (suc n))) (own-path (suc n) (hs hz) hself)

  TN-first : Σ (Gdn n first-step) (λ gd → TN (suc n) ≡ desc n first-step gd)
  TN-first = _ , refl

  first-step-chain : first-step ≡ hl (λ k → proj₁ (TF.chainG (Sb (suc n)) (worlds (suc n)) (legal (suc n))
    (seed (suc n))
    (R.link (seed (suc n)) (gtX (Sb (suc n)) (fl (suc n))) (proj₂ (own-path (suc n) (hs hz) hself))) k))
  first-step-chain = R.ΦX-chain (seed (suc n)) (gtX (Sb (suc n)) (fl (suc n)))
    (proj₂ (own-path (suc n) (hs hz) hself))

  -- 链的第 0 项: 回灌种子, 读到旧种类的结点, 等于代表坐标一支上的折叠
  g₁ = gtX (Sb (suc n)) (fl (suc n))
  pg₁ = proj₂ (own-path (suc n) (hs hz) hself)

  c₁ : HB (Sb (suc n))
  c₁ = S₂.X.sh₀ (hs hz) (fl (suc n))

  old₁ : IsOld (g₁ c₁)
  old₁ = gtX-Ω (Sb (suc n)) (fl (suc n)) c₁ tt

  first-item-rep : R.link (seed (suc n)) g₁ pg₁ (seed (suc n))
    ≡ S₂.ΦX hz (hs c₁) (proj₂ (S₂.X.aS {hs hz} (fl (suc n)) tt))
        (S₂.X.⊲tr (hsuc hself) (S₂.X.↑S {hs hz} (fl (suc n)))) (seed (suc n))
        (R.rep-branch (g₁ c₁) old₁)
        (R.rep-path (g₁ c₁) old₁ (pg₁ c₁ (S₂.X.aS {hs hz} (fl (suc n)) tt)))
  first-item-rep = R.ΦX-old hz (hs c₁) (proj₂ (S₂.X.aS {hs hz} (fl (suc n)) tt))
    (S₂.X.⊲tr (hsuc hself) (S₂.X.↑S {hs hz} (fl (suc n)))) (seed (suc n)) (g₁ c₁) old₁
    (pg₁ c₁ (S₂.X.aS {hs hz} (fl (suc n)) tt))
```

## §2 代表坐标是世界里的实际界 (与 Third 的差别)

```agda
-- 第 c 个分量的顶新种类: 代表坐标就是世界在那个分量里存的界
rep-is-bound : ∀ n (w : Wd (Sb (suc n))) (c : HB (Sb n)) →
  topS (suc n) w (inj₂ c , inj₂ tt) ≡ proj₂ (w (inj₂ c))
rep-is-bound n w c = refl

-- 候选自己的定理 (重述类型): 回灌的值在更新后的世界的界之下
module _ (n : ℕ) (u : Wd (Sb n)) (lu : LgW (Sb n) u) where
  open World.Driven n u lu

  feedback-in-bound : ∀ (s : State) m →
    Bd (Sb (suc n)) (inj₂ m , inj₂ tt) (F.feedback (bounds s) (output s) m) (world (next s))
  feedback-in-bound = feedback-admitted
```

## §3 与闭项的接线 (只取类型)

```agda
closed-term closed-grid : Cd
closed-term = Closed.closed
closed-grid = Grid.closedGrid

-- 两个闭项的每一项都是某个世界族上的 TN
cell : (worlds : ∀ n → Wd (Sb n)) → (∀ n → LgW (Sb n) (worlds n)) → ℕ → Cd
cell = Down.With.TN
```

## §4 结论 (按档)

- **[定理]** `driven-Er`, `driven-rep` (`refl`); `driven-san-Ωfree`; `seed-is-floor` (`refl`), `first-feed-Ω`, `first-src-old`; `TN-first` (`refl`), `first-step-chain`, `first-item-rep`; `rep-is-bound` (`refl`); `feedback-in-bound` (候选已有定理的重述).
- **[判断]** 第一个 Ω-共尾派发的站是从第 2 个底向第 1 个底的下降; 层号类型不封顶.
- **没有的.** 值上界; 损失使值下降的见证; 条件覆盖定理的实填.
