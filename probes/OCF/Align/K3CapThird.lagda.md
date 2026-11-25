# K3 封顶 (三之二): `Third.TΛ`

> **第 4 层 (验收侧) 的判定文件.** 不改任何候选的定义, 不进成品与证书. 本篇不导入记号模块 (用不到). 一般陈述在 [K3CapSan](K3CapSan.lagda.md); 这里把它们接到 `ThirdTm` 的每一站, 并补上这个候选独有的一条 (世界固定).
>
> **判决: (乙) 内容封顶的编译事实; 层号类型不封顶.** `ThirdTm.Cn.TN c₀ n` 的第 n 站用底 `Sb n`, 固定的世界 `W.wS c₀ n`, 洗法 `Er`, 代表坐标 `W.pkS c₀ n`. 层号的类型一路到 `SΛ = sup ℕ Sb`, 类型上没有装不下的站. 封在运行上:
>
> 1. `third-rep` (`refl`): 第 n 站的跨底折叠在指标分量旧种类的结点 (回灌下标是 Ω-结点时的源) 上, 等于它在代表坐标 `pkS n κ` 一支上的值.
> 2. `third-Er` (`refl`) 加 [K3CapSan](K3CapSan.lagda.md) 的 `san-Ωfree`, `san-kept`, `keep-washed`: 第 n 站留下的结点的坐标经同一个洗法; 层是 Ω-结点时洗成没有 Ω-结点的树.
> 3. `comp-bound-zero`, `comp-pos`: **这个候选独有.** 第 n+1 个底的世界里, 第 c 个分量的顶新种类的界是 0: 界之下的坐标只有 `hz` (与已有的 `ThirdVal.slot-zero` 同一事实, 这里写成种类结构自己的 `Bd`); 于是塔高度穿过这种 Ω-结点时, 位置证据只能走第 0 支. 折叠的结点分类 `cg` 要的 `Pos` 证据因此只在第 0 个分量上有.
>
> **第一个 Ω-共尾派发的站在哪.** `K (Sb 0) = ⊥`, 第 0 个底的值是可数树; 第 1 个底的值 `HB (Sb 1)` 才有 Ω-结点. 所以回灌下标第一次可能是 Ω-结点, 是在从第 2 个底向第 1 个底下降的那一步 (`stp 1`, 即 `TN c₀ 1` 的第一步). 这不只是可能: `first-feed-Ω`, `first-src-old` 说从第 1 站起每一站的**第一次**回灌 (回灌的是种子, 即地板 `fl (suc n)`) 读到的源就是旧种类的结点, 第 1 条当场生效 (编译事实: `TN-first`, `first-step-chain` 把闭项 `TN c₀ (suc n)` 的第一步接到 `K3CapSan.Rep.ΦX-chain` 的链上). 这一步在原入口的读法里是层号越过 Ω 的第一站; 读法本身没有定理 (判断).
>
> **它说了什么, 没说什么.**
>
> - 编译事实: 上面各条, 对一切 `c₀`, `n`. `comp-bound-zero` 的前提 (一个界之下的坐标) 有实例 `hz` (`comp-bound-inhabited`).
> - **不是值上界.** 没有证明 `TΛ` 的序数值不超过任何具名序数; 入口写的 ψ₀(Ω_{Ω·ω}) 附近仍是判断. 也没有证明这三处使值下降.
> - 条件覆盖定理 (甲) 没有实填: `Cover.terminal` 取 `X = TΛ` 时三个前提都空着.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.K3CapThird where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw; Pos)
open import OCF.Lean.ThirdTw using (Sb; fl; XSof; gtX)
open import OCF.Lean.ThirdPS using (PH)
open import OCF.Lean.ThirdLeg using (module W; legS; Lg-legS)
import OCF.Lean.ThirdFold as TF
import OCF.Lean.ThirdSan as TS
open import OCF.Lean.ThirdTm using (module Cn; TΛ)
open import OCF.Align.K3CapSan
```

## §1 每一站用的就是一般陈述里的那几件

```agda
module _ (c₀ : Cd) (lc₀ : LgB c₀) (n : ℕ) where
  open W c₀ lc₀ using (wS; lwS; pkS; pk-bd)
  module S = Cn.St c₀ lc₀ n

  third-Er : S.Er ≡ TS.Er (Sb n) (wS n) (lwS n) (fl n)
  third-Er = refl

  -- 洗法的定理在这一站上
  module Wn = Wash (Sb n) (wS n) (lwS n) (fl n)

  third-san-Ωfree : ∀ κ₀ g c → ΩFree (TF.San.san S.Er (hΩ κ₀ g) c)
  third-san-Ωfree = Wn.san-Ωfree

  -- 跨底折叠: 指标分量旧种类的结点只走代表坐标一支
  third-rep : ∀ t B (lB : LgB B) (pt : t S.⊲ᵘ B) (b : S.GT t) κ (g : E (Sb n) κ → HB (XSof (Sb n)))
    (nd : PH S.PSX B (hΩ (inj₁ tt , inj₁ κ) g)) →
    S.ΦX t B lB pt b (hΩ (inj₁ tt , inj₁ κ) g) nd
      ≡ S.ΦX t B lB pt b (g (pkS n κ)) (proj₂ nd (pkS n κ) (pk-bd n κ))
  third-rep t B lB pt b κ g nd = refl
```

## §1′ 从第 1 站起, 第一次回灌读到的就是旧种类的结点

第 `suc n` 站的下降是 `ΦX hz (hs hz) tt (hsuc hself) (b₀ (suc n)) (fl (suc (suc n))) …`. 种子是地板 `fl (suc n)` (`seed-is-floor`), 源的根是指标种类的结点, 分支族是 `gtX (Sb (suc n)) (fl (suc n))` (`source-shape`). 按 `K3CapSan.Rep.ΦX-chain`, `chain-first`, 链的第 0 项在坐标 `sh₀ 1 (fl (suc n))` 处读源. 这个坐标是 Ω-结点 (`first-feed-Ω`), 读到的源是旧种类的结点 (`first-src-old`), 于是 `third-rep` 生效: 只走代表坐标一支.

```agda
module _ (c₀ : Cd) (lc₀ : LgB c₀) (n : ℕ) where
  module S₁ = Cn.St c₀ lc₀ (suc n)

  seed-is-floor : proj₁ (Cn.b₀ c₀ lc₀ (suc n)) ≡ fl (suc n)
  seed-is-floor = refl

  source-shape : fl (suc (suc n)) ≡ hΩ (inj₁ tt , inj₂ tt) (gtX (Sb (suc n)) (fl (suc n)))
  source-shape = refl

  first-feed-Ω : IsΩ (S₁.X.sh₀ (hs hz) (fl (suc n)))
  first-feed-Ω = tt

  first-src-old : IsOld (gtX (Sb (suc n)) (fl (suc n)) (S₁.X.sh₀ (hs hz) (fl (suc n))))
  first-src-old = gtX-Ω (Sb (suc n)) (fl (suc n)) (S₁.X.sh₀ (hs hz) (fl (suc n))) first-feed-Ω
```

**把上面几条接到闭项的实际运行上.** `TN c₀ (suc n)` 的第一步是 `first-step` (`TN-first`, `refl`): 第 `suc n` 站的下降, 源是地板 `fl (suc (suc n))`, 路径的根证据是 `hself`. 这一步的输出是 `K3CapSan.Rep` 里的那条链 (`first-step-chain`), 链的第 0 项回灌种子 `fl (suc n)`, 读到的源是旧种类的结点 (`first-src-old`), 于是第 0 项等于代表坐标一支上的折叠 (`first-item-rep`).

```agda
module _ (c₀ : Cd) (lc₀ : LgB c₀) (n : ℕ) where
  open Cn c₀ lc₀ using (stp; desc; TN; Gdn; b₀; module Fl)
  open W c₀ lc₀ using (wS; lwS; pkS; pk-bd)
  module S₂ = Cn.St c₀ lc₀ (suc n)
  module R = Rep (Sb (suc n)) (wS (suc n)) (lwS (suc n)) S₂.Er
    (legS (suc n)) (Lg-legS (suc n)) (pkS (suc n)) (pk-bd (suc n))

  first-step : HB (Sb (suc n))
  first-step = stp (suc n) (fl (suc (suc n))) (Fl.PH-fl (suc n) (hs hz) hself)

  TN-first : Σ (Gdn n first-step) (λ gd → TN (suc n) ≡ desc n first-step gd)
  TN-first = _ , refl

  first-step-chain : first-step ≡ hl (λ k → proj₁ (TF.chainG (Sb (suc n)) (wS (suc n)) (lwS (suc n))
    (b₀ (suc n))
    (R.link (b₀ (suc n)) (gtX (Sb (suc n)) (fl (suc n))) (proj₂ (Fl.PH-fl (suc n) (hs hz) hself))) k))
  first-step-chain = R.ΦX-chain (b₀ (suc n)) (gtX (Sb (suc n)) (fl (suc n)))
    (proj₂ (Fl.PH-fl (suc n) (hs hz) hself))

  -- 链的第 0 项: 回灌种子, 读到旧种类的结点, 等于代表坐标一支上的折叠
  g₁ = gtX (Sb (suc n)) (fl (suc n))
  pg₁ = proj₂ (Fl.PH-fl (suc n) (hs hz) hself)

  c₁ : HB (Sb (suc n))
  c₁ = S₂.X.sh₀ (hs hz) (fl (suc n))

  old₁ : IsOld (g₁ c₁)
  old₁ = gtX-Ω (Sb (suc n)) (fl (suc n)) c₁ tt

  first-item-rep : R.link (b₀ (suc n)) g₁ pg₁ (b₀ (suc n))
    ≡ S₂.ΦX hz (hs c₁) (proj₂ (S₂.X.aS {hs hz} (fl (suc n)) tt))
        (S₂.X.⊲tr (hsuc hself) (S₂.X.↑S {hs hz} (fl (suc n)))) (b₀ (suc n))
        (R.rep-branch (g₁ c₁) old₁)
        (R.rep-path (g₁ c₁) old₁ (pg₁ c₁ (S₂.X.aS {hs hz} (fl (suc n)) tt)))
  first-item-rep = R.ΦX-old hz (hs c₁) (proj₂ (S₂.X.aS {hs hz} (fl (suc n)) tt))
    (S₂.X.⊲tr (hsuc hself) (S₂.X.↑S {hs hz} (fl (suc n)))) (b₀ (suc n)) (g₁ c₁) old₁
    (pg₁ c₁ (S₂.X.aS {hs hz} (fl (suc n)) tt))
```

## §2 世界固定: 分量种类的界是 0

```agda
module _ (c₀ : Cd) (lc₀ : LgB c₀) (n : ℕ) (c : HB (Sb n)) where
  open W c₀ lc₀ using (wS)

  -- 第 c 个分量的顶新种类 (坐标是第 c 层的值)
  κc : K (Sb (suc n))
  κc = inj₂ c , inj₂ tt

  comp-bound-zero : ∀ e → Bd (Sb (suc n)) κc e (wS (suc n)) → e ≡ hz
  comp-bound-zero .hz hself = refl

  comp-bound-inhabited : Bd (Sb (suc n)) κc hz (wS (suc n))
  comp-bound-inhabited = hself

  -- 高度穿过这种 Ω-结点: 位置只能走第 0 支
  comp-pos : ∀ (g : E (Sb (suc n)) κc → HB (Sb (suc n))) {a} →
    a ⊲[ wS (suc n) ] hΩ κc g → (a ≡ hΩ κc g) ⊎ (a ⊲[ wS (suc n) ] g hz)
  comp-pos g hself = inj₁ refl
  comp-pos g (hLim {c = e} b p) with comp-bound-zero e b
  ... | refl = inj₂ p

  -- 塔里的种类要的位置证据: 只在第 0 个分量上有
  comp-Pos : ∀ (g : E (Sb (suc n)) κc → HB (Sb (suc n))) e (κ : K (Tw (Sb (suc n)) (g e))) →
    Pos (Sb (suc n)) (wS (suc n)) (hΩ κc g) (e , κ) → e ≡ hz
  comp-Pos g e κ (b , _) = comp-bound-zero e b
```

## §3 与闭项的接线 (只取类型)

```agda
closed-term : Cd
closed-term = TΛ
```

## §4 结论 (按档)

- **[定理]** `third-Er`, `third-rep` (`refl`); `third-san-Ωfree`; `seed-is-floor`, `source-shape` (`refl`), `first-feed-Ω`, `first-src-old`; `TN-first` (`refl`), `first-step-chain`, `first-item-rep`; `comp-bound-zero`, `comp-pos`, `comp-Pos`; `comp-bound-inhabited`.
- **[判断]** 第一个 Ω-共尾派发的站是从第 2 个底向第 1 个底的下降; 层号类型不封顶.
- **没有的.** 值上界; 损失使值下降的见证; 条件覆盖定理的实填.
