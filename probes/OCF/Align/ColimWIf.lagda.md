# `Lev` 取并 (colim): 接口

> **接口定稿 2026-11-05 10:46.** 定稿之后只增不改; 若必须改, 在这里写变更记录. 变更记录: (无).
>
> 不含记号. 作者选定原话: "Lev 改成并 (colim)". 配合 [Survey/StallDiagnosis.md](../../Survey/StallDiagnosis.md) §2.4 (拷贝), §3.3, §4 第 4 条 (iii) ("`Lev` 在 ℕ-极限与 Ω-极限处取和而不取并"). 本篇只放类型与类型层的定义 (世界, 限制映射, 层号映射, 律的陈述), 不放证明; 构造在 `ColimW*`, 否定在 `ColimWNeg*`. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> **做法.** `HtTowerTy.Lev` 在极限处取 `sup`, 世界是逐分量的积: 同一个低级种类 (同一棵字面层号 $y$ 处的新种类) 在不同的分支里各有一份界 (`CohWNeg.no-cross`, `HtTowerNStage.no-wmatch`). 取并的意思是这些拷贝沿塔的映射 (字面子项的包含) 被认同. 这里的写法: **种类与坐标不动** (仍是 `Lev x` 的; 种类是高度结点里的标签, 不能依赖世界), **世界换成每个层号一个界**:
>
> $$\mathrm{GW}\,S = A \times \prod_{y:\mathrm{HB}\,S} \mathrm{HB}(\mathrm{Lev}\,y),$$
>
> 第一个分量是底种类 (坐标 `A`) 的界, $\beta\,y$ 是层号 $y$ (结点 `hs y` 处的新种类, 坐标 `HB (Lev y)`) 的界. `Lev x` 的世界由限制映射 `restr x : GW S → Wd (Lev x)` **算出来** (对 $x$ 结构递归: 每遇到 `hs y` 就放 $(\mathrm{restr}\,y\,W, \beta\,y)$), 所以同一层号的一切拷贝, 在一切深度, 读同一个分量. `LevC x` 是把 `Lev x` 的界、第一位置、合法、世界序都沿 `restr x` 拉回到 `GW S` 上的种类结构 (构造在 [ColimW](ColimW.lagda.md)). 这与 `CohWTy.colim` 的 `pj` 同一思想 (世界算出来而不是存下来), 也与 `CohWGl.GW` 同形, 不同处是直接用 `HtTowerTy` 的 `Lev` 与 `HB`, 对一切 `S`, 一切 $x$.
>
> **认同是按字面层号, 不是按塔的映射逐条认同 (判断, 写明差别).** 沿塔的映射的余极限只认同由映射连起来的拷贝; 这里认同一切字面层号相同的拷贝 (包括不由映射相连的两个分支里的同一个 $y$), 比余极限更粗. 因为种类标签只记字面层号, 这一粗化不需要任何路径数据, 与世界无关.
>
> **律的定义域 (AGENTS "律带公共上界, 构造与否定配对"). 逐条:**
>
> 1. 认同律 `Glob` (§3): **每条只含一个种类** $\kappa$, 说它的界等于它的层号 `lvl x κ` 的界. 没有一对下标, 不判定任何相等. 两个拷贝的界相同, 是两条 `Glob` 的右边字面相同 (`refl`), 不是由 "两个层号相等" 推出.
> 2. `cmpK`, `botBd` (§2 的类型 `CmpKC`, `BotBdC`): 一对坐标在**同一个种类**的同一个界之下 (就是 `KS` 的字段). 公共上界是那个界.
> 3. 更新 (§4) 有两个版本:
>    - `RaiseG y₀` (裸层号): `off` 律对一切 $y$ 陈述, 前提 `¬ (y₀ ≡ y)`. **这是裸下标上的律**; 按 AGENTS, 它的否定已有同族的编译定理 (`CohWUpd.upd→wdec`: 对一切层号都有这样的更新就推出层号相等的弱判定). 这里不对一切 $y_0$ 要它, 只对带判定证书 `DecAt y₀` 的 $y_0$ (例如有限层号) 构造; 证书就是让这一对下标可判定的证据, 写在类型里.
>    - `RaiseA x w` (可入层号): 更新的层号 $y_0$ 与律里的 $y$ **都带证据** `hs y ⊲[ w ] x` (公共上界是 $x$ 本身, 在外层世界 $w$ 里); `bdec` 使它们的相等可判定. 但世界 `GW` 本身是裸层号上的函数, 更新必须对一切 $y$ 给出值. 这个版本只给出类型, 构造开放.
> 4. 认同是否要判定相等: **不要** (第 1 条). 要判定的是更新 (第 3 条).
>
> **最小实例** (§5): `S₁ = step S₀`; Ω-极限级 `x₀ = Ωtop S₀` (`Lev x₀ = sup (HB S₀) (Lev ∘ up)`); ℕ-极限级 `xω = hl finH` (`Lev xω = sup ℕ (Lev ∘ finH)`). 种类: `κ₂` (`Lev x₀` 在坐标 2 处的新种类, 层号 `finH 1`, 坐标 `HB S₁`; 即 `ChainZNeg` 的 `κ₂` 在 `Lev` 部分的形状) 与它的两个拷贝 `κ₂′` (坐标 3 处), `κ₂ω` (坐标 $\omega$ 处的第 2 项); 底种类 `κA` 与拷贝 `κA′`, `κAω`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ColimWIf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
```

## §1 每个层号一个界的世界, 与限制映射

```agda
GW : KS → Set
GW S = A × ((y : HB S) → HB (Lev y))

-- Lev x 的世界由 GW 算出: 每个 hs y 处放 (restr y W , β y)
restr : ∀ {S} (x : HB S) → GW S → Wd (Lev x)
restr hz W = proj₁ W
restr (hs x) W = restr x W , proj₂ W x
restr (hl f) W = λ n → restr (f n) W
restr (hΩ κ g) W = λ c → restr (g c) W

-- 整体的合法与世界序 (对一切层号)
LgG : ∀ {S} → GW S → Set
LgG W = Lg (proj₁ W) × (∀ y → LgB (proj₂ W y))

infix 4 _≤G_
_≤G_ : ∀ {S} → GW S → GW S → Set
W ≤G W′ = (proj₁ W ⊲ proj₁ W′) × (∀ y → proj₂ W y ⊲[ restr y W′ ] proj₂ W′ y)
```

## §2 `LevC x` 的各部分 (沿 `restr x` 拉回)

种类与坐标就是 `Lev x` 的; 世界是 `GW S`. 构造一路证明这些部分组成一个 `KS` (`ColimW.LevC`), 其中 `cmpK` 与 `botBd` 的类型如下.

```agda
module LevCParts {S : KS} (x : HB S) where
  KC : Set
  KC = K (Lev x)

  EC : KC → Set
  EC = E (Lev x)

  LgWC : GW S → Set
  LgWC W = LgW (Lev x) (restr x W)

  _≤C_ : GW S → GW S → Set
  W ≤C W′ = _≤w_ (Lev x) (restr x W) (restr x W′)

  BdC : (κ : KC) → EC κ → GW S → Set
  BdC κ c W = Bd (Lev x) κ c (restr x W)

  PrC : (κ : KC) → GW S → EC κ → EC κ → Set
  PrC κ W = Pr (Lev x) κ (restr x W)

  CmpKC : Set
  CmpKC = ∀ {κ c c′ W} → BdC κ c W → BdC κ c′ W → LgWC W → PrC κ W c′ c ⊎ PrC κ W c c′

  BotBdC : Set
  BotBdC = ∀ κ W → BdC κ (bot (Lev x) κ) W
```

## §3 认同: 层号映射与 `Glob`

层号 `Lvl S = Maybe (HB S)`: `nothing` 是底种类 (坐标 `A`), `just y` 是 `hs y` 处的新种类. `lvl x κ`: 种类 $\kappa$ 的层号, 对 $x$ 与 $\kappa$ 结构递归. `cE`: 坐标的字面换型 (每一步都是恒等; 递归只为让检查器看见类型相同). `BdL ℓ`: 层号 $\ell$ 的界, 只读世界在 $\ell$ 处的分量.

```agda
Lvl : KS → Set
Lvl S = Maybe (HB S)

LE : ∀ {S} → Lvl S → Set
LE nothing = A
LE (just y) = HB (Lev y)

lvl : ∀ {S} (x : HB S) → K (Lev x) → Lvl S
lvl hz _ = nothing
lvl (hs x) (inj₁ κ) = lvl x κ
lvl (hs x) (inj₂ _) = just x
lvl (hl f) (n , κ) = lvl (f n) κ
lvl (hΩ κ g) (c , κ′) = lvl (g c) κ′

cE : ∀ {S} (x : HB S) (κ : K (Lev x)) → E (Lev x) κ → LE (lvl x κ)
cE hz _ c = c
cE (hs x) (inj₁ κ) c = cE x κ c
cE (hs x) (inj₂ _) c = c
cE (hl f) (n , κ) c = cE (f n) κ c
cE (hΩ κ g) (c₀ , κ′) c = cE (g c₀) κ′ c

BdL : ∀ {S} (ℓ : Lvl S) → LE ℓ → GW S → Set
BdL nothing a W = a ⊲ proj₁ W
BdL (just y) c W = c ⊲[ restr y W ] proj₂ W y

PrL : ∀ {S} (ℓ : Lvl S) → GW S → LE ℓ → LE ℓ → Set
PrL nothing W a a′ = a ⊲ a′
PrL (just y) W c c′ = c ⊲[ restr y W ] c′

-- 认同律: 每条只含一个种类; 没有一对下标
Glob : KS → Set₁
Glob S = ∀ (x : HB S) κ c W → Bd (Lev x) κ c (restr x W) ≡ BdL (lvl x κ) (cE x κ c) W

GlobPr : KS → Set₁
GlobPr S = ∀ (x : HB S) κ W c c′ → Pr (Lev x) κ (restr x W) c c′ ≡ PrL (lvl x κ) W (cE x κ c) (cE x κ c′)
```

## §4 更新

`DecAt y₀`: 与 $y_0$ 相等可判定, 且对角上给 `refl` (判定证书). `RaiseG y₀`: 在层号 $y_0$ 上接长 $\delta$; `off` 是裸层号上的律, 只对带证书的 $y_0$ 构造. `RaiseA x w`: 可入版, 律里每个层号都带 `hs y ⊲[ w ] x`.

```agda
DecAt : ∀ {S} → HB S → Set
DecAt {S} y₀ = Σ ((y : HB S) → (y₀ ≡ y) ⊎ ¬ (y₀ ≡ y)) (λ d → d y₀ ≡ inj₁ refl)

record RaiseG {S : KS} (y₀ : HB S) : Set where
  field
    raise : GW S → HB (Lev y₀) → GW S
    base  : ∀ W δ → proj₁ (raise W δ) ≡ proj₁ W
    at    : ∀ W δ → proj₂ (raise W δ) y₀ ≡ proj₂ W y₀ ⊞ δ
    off   : ∀ W δ y → ¬ (y₀ ≡ y) → proj₂ (raise W δ) y ≡ proj₂ W y
    mono  : ∀ W δ → W ≤G raise W δ
    legal : ∀ W δ → LgB δ → LgG W → LgG (raise W δ)

-- 可入版: x 是公共上界, w 是外层世界
AdmL : ∀ {S} → HB S → Wd S → HB S → Set
AdmL x w y = hs y ⊲[ w ] x

record RaiseA {S : KS} (x : HB S) (w : Wd S) : Set where
  field
    raiseA : GW S → (y₀ : HB S) → AdmL x w y₀ → HB (Lev y₀) → GW S
    atA    : ∀ W y₀ p₀ δ → proj₂ (raiseA W y₀ p₀ δ) y₀ ≡ proj₂ W y₀ ⊞ δ
    offA   : ∀ W y₀ p₀ δ y → AdmL x w y → ¬ (y₀ ≡ y) → proj₂ (raiseA W y₀ p₀ δ) y ≡ proj₂ W y
    monoA  : ∀ W y₀ p₀ δ → W ≤G raiseA W y₀ p₀ δ
    legalA : ∀ W y₀ p₀ δ → LgB δ → LgG W → LgG (raiseA W y₀ p₀ δ)
```

## §5 最小实例

```agda
S₁ : KS
S₁ = step S₀

finH : ∀ {S} → ℕ → HB S
finH zero = hz
finH (suc n) = hs (finH n)

-- Ω-极限级与 ℕ-极限级
x₀ : HB S₁
x₀ = Ωtop S₀

xω : HB S₁
xω = hl finH

ω₀ : HB S₀
ω₀ = hl finH

-- x₀ 里坐标 2 处的新种类 (层号 finH 1, 坐标 HB S₁), 与它的两个拷贝
κ₂ κ₂′ κ₂ω : K (Lev x₀)
κ₂ = finH 2 , inj₂ tt
κ₂′ = finH 3 , inj₁ (inj₂ tt)
κ₂ω = ω₀ , (2 , inj₂ tt)

-- 底种类与它的两个拷贝
κA κA′ κAω : K (Lev x₀)
κA = hz , tt
κA′ = finH 1 , inj₁ tt
κAω = ω₀ , (0 , tt)

-- ℕ-极限级 xω 里层号 finH 1 的两个拷贝
λ₂ λ₃ : K (Lev xω)
λ₂ = 2 , inj₂ tt
λ₃ = 3 , inj₁ (inj₂ tt)

-- κ₂ 处的格: y ⊞ δ 在世界 W 里有界
Cell₂ : HB S₁ → HB S₁ → GW S₁ → Set
Cell₂ y δ W = Bd (Lev x₀) κ₂ (y ⊞ δ) (restr x₀ W)
```
