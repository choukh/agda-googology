# 只对可入层号给分量的并: 接口

> **接口定稿 2026-11-05 11:12 (编译通过).** 定稿之后只增不改; 若必须改, 在这里写变更记录. 变更记录: (无).
>
> 不含记号. 作者选定原话: "ColimW: 只对可入层号给分量". 构造一路 `ColimA*`, 否定一路 `NegColimA*` 共用本篇. 配合 [ColimW](ColimW.lagda.md) 的第一个障碍, [ColimWNeg](ColimWNeg.lagda.md) 的 `raiseA-sep` 与 "不否定: 只对可入层号给分量的世界", [Survey/StallDiagnosis.md](../../Survey/StallDiagnosis.md) §2.2, §2.4. 本篇只放类型与类型层的定义 (种类结构族, 世界, 限制映射, 层号映射, 律的陈述, 最小实例), 不放证明. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> **世界.** 固定外层世界 $w$ (`Wd S`) 与外层界 $X$ (`HB S`, 当前节点的层号高度). 层号 $y$ **可入** 指 `AdmL X w y = hs y ⊲[ w ] X` (`ColimWIf.AdmL`, 字面第一位置, Ω-结点处带界的证据). 世界
>
> $$\mathrm{GWA}\,X\,w = A \times \prod_{y:\mathrm{HB}\,S}\ \bigl(\mathrm{AdmL}\,X\,w\,y \to \mathrm{HB}(\mathrm{LevA}\,w\,y)\bigr),$$
>
> 第一个分量是底种类的界, $\beta\,y\,p$ 是层号 $y$ 在证据 $p$ 下的界. **不可入的层号没有分量.** 这是诊断 §2.2 的 W⁺ 的原文, 也是 `ColimWNeg` 判决里 "不否定" 的那一项.
>
> **为什么种类族也要换 (`LevA w`, §1; 理由, 判断档的部分标出).** `ColimWIf` 的 `restr x : GW S → Wd (Lev x)` 在 Ω-结点 `hΩ κ g` 处要对**一切**坐标 $c$ 给出 `Wd (Lev (g c))`, 其中的层号只在 $c$ 有界 (`Bd S κ c w`) 时可入; 有没有界不可判定, 所以由只含可入分量的世界算不出 `Wd (Lev x)`. 两种出路:
>
> 1. 种类不带证据, 世界的 Ω-分量只对有界坐标给出: 这就是 `AdmWIf.SupB`. 它不是 `KS` (缺 `botBd`), 同一种类的两个证据给两个分量, `cmpK` 要跨证据相干 (`AdmWCoh.¬cmpK`, `coh≡→cmpK`).
> 2. **Ω-并只取有界坐标** (本篇): `LevA w (hΩ κ g) = sup (Σ c (Bd S κ c w)) (LevA w ∘ g ∘ proj₁)`. 种类里带着坐标的界的证据 (固定的外层世界 $w$ 下), 所以 `LevA w x` 是 `KS` (由 `S₀`, `step`, `sup` 拼成), `restrA x π` 沿种类里的证据把路径 $\pi : x \lhd_{[w]} X$ 接下去, 算得出来. 同一种类只有一个路径, `cmpK` 不跨证据. 跨证据的问题移到**拷贝**上: 同一层号经两条路径出现, 是两个种类, 读 $\beta\,y\,p$ 与 $\beta\,y\,p'$.
>
> 选 2 的理由: 它让 `LevC′` 是 `KS` (拉回), 把跨证据的问题从 `cmpK` (每次比较都要) 挪到认同 (只在拷贝之间要). 代价: 种类依赖固定的外层世界 $w$; 外层世界变大时种类要沿 `Bd↑` 搬 (本篇不处理, 判断: 只是搬运, 不判定任何东西). 底 `S₀` 与 `step`, `sup ℕ` 原样, 只改 Ω-并的下标.
>
> **律的定义域 (AGENTS "律带公共上界, 构造与否定配对"). 逐条:**
>
> 1. `GlobA` (§4, 认同): **每条只含一个种类** $\kappa$ (带它的路径 $\pi$), 说它的界等于它的 (层号, 证据) `lvlA x π κ` 处的界. 没有一对下标.
> 2. `CrossA` (§4, 拷贝): 同一层号 $y$ 的两个证据 $p, p'$ (都是 `AdmL X w y`, 公共上界 $X$, 同一外层世界 $w$); **前提是世界相干 `CohA W`** ($\beta\,y\,p \equiv \beta\,y\,p'$). 认同需要跨证据相干, 写在类型里. 它不判定任何相等.
> 3. `CmpKC`, `BotBdC` (§3): 一对坐标在**同一个种类**的同一个界之下 (`KS` 的字段). 同一种类只有一个路径, 所以不涉及证据.
> 4. 更新 `RaiseA′` (§5): 被升高的 $(y_0, p_0)$ 与律里的每个 $(y, p)$ **都带** `AdmL X w` 的证据 (公共上界 $X$, 同一外层世界 $w$). `atA`: 与 $y_0$ 相等的一切 $(y, p)$ 接长 (一切拷贝); `offA`: 可入且 $\ne y_0$ 的 $(y,p)$ 不动; 没有对裸层号的律. 增量是**可入层号上的族** `IncA` (LocUip 的族增量写法, `LocUipIf.Inc` 的可入版), 不是单个高度; `cohA` 的前提是族相干 `CohI`. 单个增量的版本 `RaiseA1` 也给出类型 (§5), 它的相干要沿判定给的相等证明搬运.
> 5. 判定: 构造一路用 `StallDxBdec.bdec` (同一合法界 $X$ 之下, 同一合法世界 $w$) 判 $y_0 \equiv y$; 律里不出现判定.
>
> **最小实例** (§6): `S₁ = step S₀`, $X = x_0 =$ `Ωtop S₀`, 外层世界 `wω = (0, hs (hs ω₀))` (`ColimWNeg.wω`, 合法), 使第一个无限层号 `up ω₀` 可入 (证据 `pω`, 即 `ColimWNeg.adm-ω`). 种类: `κ₂` (坐标 2, 新种类, 层号 `finH 1`), 拷贝 `κ₂′` (坐标 3); `κω` (坐标 `hs ω₀`, 新种类, 层号 `up ω₀`), 拷贝 `κω′` (坐标 `hs (hs ω₀)`); 底种类 `κA`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ColimAIf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.ColimWIf using (AdmL; S₁; finH; x₀; ω₀)
open import OCF.Align.ColimWNeg using (wω; Lg-wω)
```

## §1 Ω-并只取有界坐标的种类结构族

```agda
LevA : ∀ {S} → Wd S → HB S → KS
LevA w hz = S₀
LevA w (hs x) = step (LevA w x)
LevA w (hl f) = sup ℕ (λ n → LevA w (f n))
LevA {S} w (hΩ κ g) = sup (Σ (E S κ) (λ c → Bd S κ c w)) (λ ce → LevA w (g (proj₁ ce)))
```

## §2 只对可入层号给分量的世界, 与限制映射

```agda
GWA : ∀ {S} → HB S → Wd S → Set
GWA {S} X w = A × ((y : HB S) → AdmL X w y → HB (LevA w y))

module Adm {S : KS} (X : HB S) (w : Wd S) where
  -- 路径往下走一步
  dnS : ∀ {x} → hs x ⊲[ w ] X → x ⊲[ w ] X
  dnS π = ⊲ᴮ-tr (hsuc hself) π

  dnL : ∀ {f} n → hl f ⊲[ w ] X → f n ⊲[ w ] X
  dnL n π = ⊲ᴮ-tr (hlim n hself) π

  dnΩ : ∀ {κ g c} → Bd S κ c w → hΩ κ g ⊲[ w ] X → g c ⊲[ w ] X
  dnΩ e π = ⊲ᴮ-tr (hLim e hself) π

  -- LevA w x 的世界由 GWA 沿路径算出: 每个 hs y 处放 (restrA y _ W , β y π)
  restrA : (x : HB S) → x ⊲[ w ] X → GWA X w → Wd (LevA w x)
  restrA hz π W = proj₁ W
  restrA (hs x) π W = restrA x (dnS π) W , proj₂ W x π
  restrA (hl f) π W = λ n → restrA (f n) (dnL n π) W
  restrA (hΩ κ g) π W = λ ce → restrA (g (proj₁ ce)) (dnΩ (proj₂ ce) π) W

  -- 整体的合法, 世界序, 跨证据相干
  LgGA : GWA X w → Set
  LgGA W = Lg (proj₁ W) × (∀ y (p : AdmL X w y) → LgB (proj₂ W y p))

  infix 4 _≤GA_
  _≤GA_ : GWA X w → GWA X w → Set
  W ≤GA W′ = (proj₁ W ⊲ proj₁ W′) ×
             (∀ y (p : AdmL X w y) → proj₂ W y p ⊲[ restrA y (dnS p) W′ ] proj₂ W′ y p)

  CohA : GWA X w → Set
  CohA W = ∀ y (p p′ : AdmL X w y) → proj₂ W y p ≡ proj₂ W y p′
```

## §3 `LevC′ X w` 的各部分 (沿 `restrA X hself` 拉回)

种类与坐标就是 `LevA w X` 的; 世界是 `GWA X w`. 构造一路证明它们组成 `KS` (`ColimAKS.LevC′`).

```agda
  KC : Set
  KC = K (LevA w X)

  EC : KC → Set
  EC = E (LevA w X)

  LgWC : GWA X w → Set
  LgWC W = LgW (LevA w X) (restrA X hself W)

  BdC : (κ : KC) → EC κ → GWA X w → Set
  BdC κ c W = Bd (LevA w X) κ c (restrA X hself W)

  PrC : (κ : KC) → GWA X w → EC κ → EC κ → Set
  PrC κ W = Pr (LevA w X) κ (restrA X hself W)

  CmpKC : Set
  CmpKC = ∀ {κ c c′ W} → BdC κ c W → BdC κ c′ W → LgWC W → PrC κ W c′ c ⊎ PrC κ W c c′

  BotBdC : Set
  BotBdC = ∀ κ W → BdC κ (bot (LevA w X) κ) W
```

## §4 认同: 带证据的层号映射, `GlobA` 与 `CrossA`

`LvA`: `nothing` 是底种类, `just (y , p)` 是层号 $y$ 在证据 $p$ 下. `lvlA x π κ`: 种类 $\kappa$ 的 (层号, 证据), 对 $x$ 与 $\kappa$ 结构递归, 证据沿种类里的路径算出. `cEA`: 坐标的字面换型 (每步恒等).

```agda
  LvA : Set
  LvA = Maybe (Σ (HB S) (AdmL X w))

  LEA : LvA → Set
  LEA nothing = A
  LEA (just (y , _)) = HB (LevA w y)

  lvlA : (x : HB S) → x ⊲[ w ] X → K (LevA w x) → LvA
  lvlA hz π _ = nothing
  lvlA (hs x) π (inj₁ κ) = lvlA x (dnS π) κ
  lvlA (hs x) π (inj₂ _) = just (x , π)
  lvlA (hl f) π (n , κ) = lvlA (f n) (dnL n π) κ
  lvlA (hΩ κ g) π (ce , κ′) = lvlA (g (proj₁ ce)) (dnΩ (proj₂ ce) π) κ′

  cEA : (x : HB S) (π : x ⊲[ w ] X) (κ : K (LevA w x)) → E (LevA w x) κ → LEA (lvlA x π κ)
  cEA hz π _ c = c
  cEA (hs x) π (inj₁ κ) c = cEA x (dnS π) κ c
  cEA (hs x) π (inj₂ _) c = c
  cEA (hl f) π (n , κ) c = cEA (f n) (dnL n π) κ c
  cEA (hΩ κ g) π (ce , κ′) c = cEA (g (proj₁ ce)) (dnΩ (proj₂ ce) π) κ′ c

  BdLA : (ℓ : LvA) → LEA ℓ → GWA X w → Set
  BdLA nothing a W = a ⊲ proj₁ W
  BdLA (just (y , p)) c W = c ⊲[ restrA y (dnS p) W ] proj₂ W y p

  PrLA : (ℓ : LvA) → GWA X w → LEA ℓ → LEA ℓ → Set
  PrLA nothing W a a′ = a ⊲ a′
  PrLA (just (y , p)) W c c′ = c ⊲[ restrA y (dnS p) W ] c′

  -- 认同律: 每条只含一个种类 (带它的路径)
  GlobA : Set₁
  GlobA = ∀ (x : HB S) (π : x ⊲[ w ] X) κ c W →
    Bd (LevA w x) κ c (restrA x π W) ≡ BdLA (lvlA x π κ) (cEA x π κ c) W

  GlobPrA : Set₁
  GlobPrA = ∀ (x : HB S) (π : x ⊲[ w ] X) κ W c c′ →
    Pr (LevA w x) κ (restrA x π W) c c′ ≡ PrLA (lvlA x π κ) W (cEA x π κ c) (cEA x π κ c′)

  -- 拷贝: 同一层号的两个证据; 前提是相干
  CrossA : Set
  CrossA = ∀ {W} → CohA W → ∀ y (p p′ : AdmL X w y) (c : HB (LevA w y)) →
    BdLA (just (y , p)) c W → BdLA (just (y , p′)) c W

  CrossPrA : Set
  CrossPrA = ∀ {W} → CohA W → ∀ y (p p′ : AdmL X w y) (c c′ : HB (LevA w y)) →
    PrLA (just (y , p)) W c c′ → PrLA (just (y , p′)) W c c′
```

## §5 更新

`IncA`: 可入层号上的增量族 (以证据为参数); `CohI δ`: 族与证据无关. `RaiseA′`: 族增量的更新, 七条律. `RaiseA1`: 单个增量 $\delta :$ `HB (LevA w y₀)` 的更新 (对照用), 律只在 $(y_0, p_0)$ 处陈述 `at1`, 相干 `coh1`.

```agda
  IncA : Set
  IncA = (y : HB S) → AdmL X w y → HB (LevA w y)

  CohI : IncA → Set
  CohI δ = ∀ y (p p′ : AdmL X w y) → δ y p ≡ δ y p′

  record RaiseA′ : Set where
    field
      raiseA : GWA X w → (y₀ : HB S) → AdmL X w y₀ → IncA → GWA X w
      baseA  : ∀ W y₀ p₀ δ → proj₁ (raiseA W y₀ p₀ δ) ≡ proj₁ W
      -- 与 y₀ 相等的一切 (y, p) (一切拷贝) 接长
      atA    : ∀ W y₀ p₀ δ y (p : AdmL X w y) → y₀ ≡ y →
               proj₂ (raiseA W y₀ p₀ δ) y p ≡ proj₂ W y p ⊞ δ y p
      -- 可入且不等于 y₀ 的 (y, p) 不动
      offA   : ∀ W y₀ p₀ δ y (p : AdmL X w y) → ¬ (y₀ ≡ y) →
               proj₂ (raiseA W y₀ p₀ δ) y p ≡ proj₂ W y p
      monoA  : ∀ W y₀ p₀ δ → W ≤GA raiseA W y₀ p₀ δ
      legalA : ∀ W y₀ p₀ δ → (∀ p → LgB (δ y₀ p)) → LgGA W → LgGA (raiseA W y₀ p₀ δ)
      cohA   : ∀ W y₀ p₀ δ → CohI δ → CohA W → CohA (raiseA W y₀ p₀ δ)

  record RaiseA1 : Set where
    field
      raise1 : GWA X w → (y₀ : HB S) → AdmL X w y₀ → HB (LevA w y₀) → GWA X w
      at1    : ∀ W y₀ p₀ δ → proj₂ (raise1 W y₀ p₀ δ) y₀ p₀ ≡ proj₂ W y₀ p₀ ⊞ δ
      off1   : ∀ W y₀ p₀ δ y (p : AdmL X w y) → ¬ (y₀ ≡ y) →
               proj₂ (raise1 W y₀ p₀ δ) y p ≡ proj₂ W y p
      coh1   : ∀ W y₀ p₀ δ → CohA W → CohA (raise1 W y₀ p₀ δ)
```

## §6 最小实例

外层世界 `wω = (0, hs (hs ω₀))` (`ColimWNeg.wω`). 坐标 $c$ 在它之下的证据: `e₂`, `e₃` (有限), `eω`, `eω′` (经 $\omega$).

```agda
e₂ : _⊲[_]_ {S₀} (finH 2) azero (hs (hs ω₀))
e₂ = hsuc (hsuc (hlim 2 hself))

e₃ : _⊲[_]_ {S₀} (finH 3) azero (hs (hs ω₀))
e₃ = hsuc (hsuc (hlim 3 hself))

eω : _⊲[_]_ {S₀} (hs ω₀) azero (hs (hs ω₀))
eω = hsuc hself

eω′ : _⊲[_]_ {S₀} (hs (hs ω₀)) azero (hs (hs ω₀))
eω′ = hself

eA : _⊲[_]_ {S₀} hz azero (hs (hs ω₀))
eA = z⊲ᴮ (hs (hs ω₀))

L₀ : KS
L₀ = LevA wω x₀

-- 层号 finH 1: 坐标 2 的新种类, 坐标 3 里的拷贝
κ₂ κ₂′ : K L₀
κ₂ = (finH 2 , e₂) , inj₂ tt
κ₂′ = (finH 3 , e₃) , inj₁ (inj₂ tt)

-- 第一个无限层号 up ω₀: 坐标 hs ω₀ 的新种类, 坐标 hs (hs ω₀) 里的拷贝
κω κω′ : K L₀
κω = (hs ω₀ , eω) , inj₂ tt
κω′ = (hs (hs ω₀) , eω′) , inj₁ (inj₂ tt)

-- 底种类
κA : K L₀
κA = (hz , eA) , tt

-- 层号 up ω₀ 的可入证据 (= ColimWNeg.adm-ω)
pω : AdmL x₀ wω (up ω₀)
pω = hLim {c = hs ω₀} eω hself
```
