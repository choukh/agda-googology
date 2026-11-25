# K3 封顶 (三之一): Third 一族的折叠在 Ω-共尾的高度上做了什么

> **第 4 层 (验收侧) 的判定文件.** 不改任何候选的定义, 不进成品与证书. 本篇不导入记号模块 (用不到). 对象是 `Third.TΛ` 与 `OutputDriven.closed`, `closedGrid` 共用的三件: 洗法 `ThirdSan.Er`, 同底折叠的结点决定 `ThirdFold.F.pickG`, 跨底折叠 `ThirdX.ΦX`. 这里对任一底 `U`, 任一合法世界 `w`, 任一地板 `fb` 陈述; 两个候选各自的实例在 [K3CapThird](K3CapThird.lagda.md), [K3CapOutputDriven](K3CapOutputDriven.lagda.md).
>
> **判决: (乙) 内容封顶的编译事实, 形状是 "运行在这一步与一个更小的对象定义性相等".** 这一族的层号类型不封顶 (第 n+1 个底的分量下标取遍第 n 个底的值, `ThirdTw.Sb`, `SΛ`). 封在运行上, 一共三处, 都发生在层号或回灌下标是 Ω-结点的地方:
>
> 1. **跨底折叠在 Ω-共尾的回灌下标处只走一支.** 回灌的下标 `y` 是 Ω-结点 `hΩ κ h` 时, 源 `gtX U fb y` 是指标分量旧种类的结点 (`src-Ω`, `refl`); `ΦX` 在这种结点上的值, 定义性地等于它在代表坐标 `pk κ` 那一支上的值 (`ΦX-rep`, `refl`); 把分支族换成那一支的常值族, 值不变 (`ΦX-const`, `refl`). 目标层与结点层在这里没有被比较.
> 2. **Ω-共尾的层上, 留下的结点的坐标被洗成没有 Ω-结点的树.** 层 `i` 的新种类 (读法 Ω_{i+1}) 被留下时, 分支先经 `san i` (`keep-washed`, `keep-washed-below`, `refl`). `i` 是 Ω-结点 `hΩ κ₀ g` 时, `san i c` 对一切坐标 `c` 都没有 Ω-结点 (`san-Ωfree`); 一般地, 洗过的坐标里只剩 "不穿过高度的 Ω-结点" 的种类 (`san-kept`; `kept-Ω`, `kept-new`, `kept-old` 说明哪些种类算).
> 3. **Ω-共尾的层的地板取底分量** (`tp-bot`, `refl`): "在上" 的链从这个地板出发.
>
> **它说了什么, 没说什么.**
>
> - 编译事实: 上面各条, 对一切 `U`, `w`, `fb` (第 1 条对一切洗法, 合法化, 代表坐标). 没有额外前提.
> - 读法 (判断): 第 1, 2 条所在的地方就是 Buchholz 式折叠要按 "目标层对结点层" 分情况的地方 (结点的共尾度是不可数的, 层号本身含 Ω-结点). 候选在那里不分情况: 回灌下标取一支, 留下的坐标洗掉.
> - 到达: 第 1 条在两个候选的实际运行里从第 1 站的第一次回灌起就到达 (`K3CapThird.first-src-old`, `K3CapOutputDriven.first-src-old`, 编译事实). 第 2, 3 条在闭项的实际运行里是否到达, 本组没有验证.
> - **不是值上界.** 取一支或洗坐标之后的值可以仍然很大 (代表坐标是世界的界, 它本身随回灌增长). 本篇没有证明任何闭项的序数值不超过某个具名序数, 也没有证明这些损失使值下降.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.K3CapSan where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw; Pos)
open import OCF.Lean.ThirdTw using (XSof; Ix; FX; gtX; along; frA; posA)
open import OCF.Lean.ThirdPS using (PH)
import OCF.Lean.ThirdFold as TF
import OCF.Lean.ThirdSan as TS
import OCF.Lean.ThirdX as TX
```

## §1 两个谓词

`ΩFree x`: 树 `x` 里没有 Ω-结点. `AllK P x`: `x` 里每个 Ω-结点的种类都满足 `P` (遗传地, 对一切分支).

```agda
ΩFree : ∀ {S : KS} → HB S → Set
ΩFree hz = ⊤
ΩFree (hs x) = ΩFree x
ΩFree (hl f) = ∀ n → ΩFree (f n)
ΩFree (hΩ κ g) = ⊥

AllK : ∀ {S : KS} → (K S → Set) → HB S → Set
AllK P hz = ⊤
AllK P (hs x) = AllK P x
AllK P (hl f) = ∀ n → AllK P (f n)
AllK P (hΩ κ g) = P κ × (∀ e → AllK P (g e))

IsL : ∀ {X Y : Set} → X ⊎ Y → Set
IsL (inj₁ _) = ⊤
IsL (inj₂ _) = ⊥

-- 根是 Ω-结点
IsΩ : ∀ {S : KS} → HB S → Set
IsΩ hz = ⊥
IsΩ (hs x) = ⊥
IsΩ (hl f) = ⊥
IsΩ (hΩ κ g) = ⊤

-- 加法的右项是 Ω-结点时, 和也是
⊞-Ω : ∀ {S : KS} (a : HB S) κ (g : E S κ → HB S) → IsΩ (a ⊞ hΩ κ g)
⊞-Ω a κ g = tt

-- 没有 Ω-结点的树读成可数树 (只是定义, 说明洗过的坐标落在哪一类里)
skel : ∀ {S : KS} (x : HB S) → ΩFree x → Cd
skel hz p = hz
skel (hs x) p = hs (skel x p)
skel (hl f) p = hl (λ n → skel (f n) (p n))
```

## §2 洗法

```agda
module Wash (U : KS) (w : Wd U) (lw : LgW U w) (fb : HB U) where
  open TF U w lw using (T; Gd; AdT; _⊲ᵘ_)
  open TS U w lw fb using (sf; san; sN; gd-san; tpS; Er)
  module FE = TF.F U w lw Er

  -- 种类 κ 在层 m 的塔里被洗法留下: 它不穿过 m 的 Ω-结点
  Kept : ∀ m → K (T m) → Set
  Kept m κ = IsL (sf m κ)

  kept-Ω : ∀ κ₀ g κ → Kept (hΩ κ₀ g) κ ≡ ⊥
  kept-Ω κ₀ g κ = refl

  kept-new : ∀ x → Kept (hs x) (inj₂ tt) ≡ ⊤
  kept-new x = refl

  kept-old : ∀ x κ → Kept (hs x) (inj₁ κ) ≡ Kept x κ
  kept-old x κ = refl

  -- 洗过的坐标里只剩被留下的种类
  san-kept : ∀ m c → AllK (Kept m) (san m c)
  sN-kept  : ∀ m κ g r → (IsL r → Kept m κ) → AllK (Kept m) (sN m κ g r)
  san-kept m hz = tt
  san-kept m (hs x) = san-kept m x
  san-kept m (hl f) = λ n → san-kept m (f n)
  san-kept m (hΩ κ g) = sN-kept m κ g (sf m κ) (λ z → z)
  sN-kept m κ g (inj₁ p) k = k tt , λ e → san-kept m (g e)
  sN-kept m κ g (inj₂ _) k = tt

  -- Ω-共尾的层上: 洗过的坐标没有 Ω-结点
  san-Ωfree : ∀ κ₀ g c → ΩFree (san (hΩ κ₀ g) c)
  san-Ωfree κ₀ g hz = tt
  san-Ωfree κ₀ g (hs x) = san-Ωfree κ₀ g x
  san-Ωfree κ₀ g (hl f) = λ n → san-Ωfree κ₀ g (f n)
  san-Ωfree κ₀ g (hΩ κ h) = tt

  -- Ω-共尾的层的地板: 底分量
  tp-bot : ∀ κ g → tpS (hΩ κ g) ≡ ι {E U κ} {λ e → T (g e)} (bot U κ) (tpS (g (bot U κ)))
  tp-bot κ g = refl
```

**留下的结点的分支先洗.** `pickG` 的两条 "留" 子句: 目标恰是 `hs i` 时, 与结点层 `hs i` 严格在目标之下时. 两处的分支都是 `to (san i …)`.

```agda
  keep-washed : ∀ {X i : HB U} {A : Set} {R : A → Set} (to : HB (T i) → A)
    (ad : ∀ c → Gd i c → R (to c)) (u : hs i ⊲ᵘ X) →
    FE.pickG {X} {hs i} {i} {A} {R} to ad u (inj₁ hself)
      ≡ FE.keep (inj₂ tt) tt (λ c → to (san i c)) (λ c → ad _ (gd-san i c))
  keep-washed to ad u = refl

  keep-washed-below : ∀ {X t i : HB U} {A : Set} {R : A → Set} (to : HB (T i) → A)
    (ad : ∀ c → Gd i c → R (to c)) (u : hs i ⊲ᵘ X) (q : hs i ⊲ᵘ t) →
    FE.pickG {X} {t} {i} {A} {R} to ad u (inj₂ q)
      ≡ FE.keep (along q) (posA q) (λ c → to (san i (frA q c))) (λ c → ad _ (gd-san i (frA q c)))
  keep-washed-below to ad u q = refl
```

## §3 跨底折叠: Ω-共尾的回灌下标处只走代表坐标的一支

`gtX U fb y` 是指标种类在坐标 `y` 处的分支 (读法 $\sum_{c<y}$). `y` 是 Ω-结点时它是指标分量旧种类的结点; `ΦX` 在这种结点上不留, 不比较, 取 `pk κ` 那一支.

```agda
src-Ω : ∀ U (fb : HB U) κ (h : E U κ → HB U) →
  gtX U fb (hΩ κ h) ≡ hΩ (inj₁ tt , inj₁ κ) (λ e → gtX U fb (h e))
src-Ω U fb κ h = refl

-- 根是指标分量旧种类的结点
IsOld : ∀ {U : KS} → HB (XSof U) → Set
IsOld hz = ⊥
IsOld (hs x) = ⊥
IsOld (hl f) = ⊥
IsOld (hΩ (inj₁ _ , inj₁ _) g) = ⊤
IsOld (hΩ (inj₁ _ , inj₂ _) g) = ⊥
IsOld (hΩ (inj₂ _ , _) g) = ⊥

gtX-Ω : ∀ U (fb : HB U) y → IsΩ y → IsOld (gtX U fb y)
gtX-Ω U fb (hΩ κ h) _ = tt

module Rep (U : KS) (w : Wd U) (lw : LgW U w) (Sn : TF.San U w lw)
  (leg : HB U → HB U) (Lg-leg : ∀ a → LgB (leg a))
  (pk : (κ : K U) → E U κ) (pk-bd : ∀ κ → Bd U κ (pk κ) w) where
  open TF U w lw using (GT; _⊲ᵘ_; chainG)
  open TX U w lw Sn leg Lg-leg pk pk-bd using (ΦX; PSX; sh₀; Adm₀; aS; ↑S; ⊲tr)

  ΦX-rep : ∀ t B (lB : LgB B) (pt : t ⊲ᵘ B) (b : GT t) κ (g : E U κ → HB (XSof U))
    (nd : PH PSX B (hΩ (inj₁ tt , inj₁ κ) g)) →
    ΦX t B lB pt b (hΩ (inj₁ tt , inj₁ κ) g) nd
      ≡ ΦX t B lB pt b (g (pk κ)) (proj₂ nd (pk κ) (pk-bd κ))
  ΦX-rep t B lB pt b κ g nd = refl

  -- 同一件事的另一种说法: 把整个分支族换成代表坐标那一支的常值族, 折叠的值不变
  ΦX-const : ∀ t B (lB : LgB B) (pt : t ⊲ᵘ B) (b : GT t) κ (g : E U κ → HB (XSof U))
    (nd : PH PSX B (hΩ (inj₁ tt , inj₁ κ) g)) →
    ΦX t B lB pt b (hΩ (inj₁ tt , inj₁ κ) g) nd
      ≡ ΦX t B lB pt b (hΩ (inj₁ tt , inj₁ κ) (λ _ → g (pk κ)))
          (tt , λ _ _ → proj₂ nd (pk κ) (pk-bd κ))
  ΦX-const t B lB pt b κ g nd = refl
```

**这种结点在运行里从哪来.** 各候选每一站的下降都是 `ΦX hz (hs hz) tt (hsuc hself) 种子 源 路径`: 目标第 0 层, 界 1, 源的根是指标种类的结点 `hΩ ιK g`, 路径的根证据是 `hself`. 这时结点走 "同层" 一支, 输出是一条链 (`ΦX-chain`, `refl`): 链的每一项把上一项 `b′` 回灌成坐标 `sh₀ 1 (proj₁ b′)`, 在那个坐标处读源 `g`. 所以只要回灌出的坐标是 Ω-结点, 读到的源就是旧种类的结点 (`gtX-Ω`), `ΦX-rep` 生效. 第 0 项回灌的是种子自己 (`chain-first`, `refl`).

```agda
  link : (b : GT hz) (g : HB U → HB (XSof U))
    (pg : ∀ e (a : Adm₀ (hs hz) e) → PH PSX (hs e) (g e)) → GT hz → GT hz
  link b g pg b′ =
    ΦX hz (hs (sh₀ (hs hz) (proj₁ b′))) (proj₂ (aS {hs hz} (proj₁ b′) tt))
      (⊲tr (hsuc hself) (↑S {hs hz} (proj₁ b′))) b′
      (g (sh₀ (hs hz) (proj₁ b′))) (pg _ (aS {hs hz} (proj₁ b′) tt))

  ΦX-chain : ∀ (b : GT hz) (g : HB U → HB (XSof U))
    (pg : ∀ e (a : Adm₀ (hs hz) e) → PH PSX (hs e) (g e)) →
    proj₁ (ΦX hz (hs hz) tt (hsuc hself) b (hΩ (inj₁ tt , inj₂ tt) g) (hself , pg))
      ≡ hl (λ k → proj₁ (chainG b (link b g pg) k))
  ΦX-chain b g pg = refl

  chain-first : ∀ (b : GT hz) (g : HB U → HB (XSof U))
    (pg : ∀ e (a : Adm₀ (hs hz) e) → PH PSX (hs e) (g e)) →
    chainG b (link b g pg) 0 ≡ link b g pg b
  chain-first b g pg = refl

  -- ΦX-rep 对 "根是旧种类的结点" 这个谓词的形式: 不必写出结点的分支族
  rep-branch : (x : HB (XSof U)) → IsOld x → HB (XSof U)
  rep-branch (hΩ (inj₁ _ , inj₁ κ) g) _ = g (pk κ)

  rep-path : ∀ {B} (x : HB (XSof U)) (o : IsOld x) → PH PSX B x → PH PSX B (rep-branch x o)
  rep-path (hΩ (inj₁ _ , inj₁ κ) g) _ nd = proj₂ nd (pk κ) (pk-bd κ)

  ΦX-old : ∀ t B (lB : LgB B) (pt : t ⊲ᵘ B) (b : GT t) (x : HB (XSof U)) (o : IsOld x)
    (nd : PH PSX B x) →
    ΦX t B lB pt b x nd ≡ ΦX t B lB pt b (rep-branch x o) (rep-path x o nd)
  ΦX-old t B lB pt b (hΩ (inj₁ _ , inj₁ κ) g) _ nd = refl
```

## §4 结论 (按档)

- **[定理]** `san-Ωfree`: 层是 Ω-结点时, 洗过的坐标没有 Ω-结点. `san-kept`: 洗过的坐标里每个 Ω-结点的种类都被 `sf` 判为留下. `kept-Ω`, `kept-new`, `kept-old` (`refl`): 层是 Ω-结点时没有种类留下; 后继层的新种类留下; 后继层的旧种类看下一层. `tp-bot` (`refl`). `keep-washed`, `keep-washed-below` (`refl`): 留下的结点的分支是 `to (san i …)`. `src-Ω` (`refl`), `ΦX-rep` (`refl`): 跨底折叠在指标分量旧种类的结点上等于代表坐标一支上的折叠. `ΦX-const` (`refl`): 把该结点的分支族换成代表坐标那一支的常值族, 折叠的值不变. `ΦX-chain`, `chain-first` (`refl`): 每一站的下降是一条链, 链的每一项在回灌出的坐标处读源, 第 0 项回灌种子; `gtX-Ω`: 回灌出的坐标是 Ω-结点时读到的源是旧种类的结点. `ΦX-old`: `ΦX-rep` 对谓词 `IsOld` 的形式.
- **[判断]** 这三处就是 "目标层对结点层" 的派发本该发生的地方; 候选在那里不派发.
- **没有的.** 值上界; 损失使值下降的见证; 条件覆盖定理的实填.
