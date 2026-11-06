# 族增量世界上的真折叠: 接口

> **接口定稿 2026-11-05 11:20 (编译通过).** 定稿之后只增不改; 若必须改, 在这里写变更记录. 变更记录: (无).
>
> 不含记号. 作者选定原话: "族增量世界上写真折叠". 构造一路 `FamFold*`, 否定一路 `NegFam*`, 共用本篇. 本篇只放类型与记录, 不放证明. 依赖 [AdmWIf](AdmWIf.lagda.md) (`Slot` 的世界 `Wᴮ = Σ (w : Out) (Cmp w)`, 分量以 (坐标, 可入证据) 为下标), [LocUipIf](LocUipIf.lagda.md) (族增量 `Inc`, 更新记录 `RaiseF`, 拷贝相干 `CopyCoh`), 两种种类的折叠 ([HtTowerFTree](HtTowerFTree.lagda.md), [HtTowerNRead](HtTowerNRead.lagda.md) 的第 2 层数据树 `D₂`, [HtTowerFClosed](HtTowerFClosed.lagda.md) 的 `Ω₂ᴴ`). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> **对象.** 一级 (κ₂ 那一级) 的新种类是 `Slot` 在坐标 $1$ (`fin 1`) 处的槽种类, 坐标类型 `HB (G₀ (fin 1)) = HB S₁` (定义相等). 一级折叠的层是 `HB S₂` (`S₂ = step S₁`, 三种种类: `A`, `H₀`, `HB S₁`), 输出是两种种类折叠第 2 层的数据树 `D₂` (第 2 层是 κ₂ 的读回层: `rd₂` 把它读成 `HB S₁`).
>
> - **§1 世界.** 族增量世界 `Wᴮ`; 两种相干合起来 `CohC = Coh≡ × CopyCoh`; 槽 `slotAt`.
> - **§2 读回对坐标一致.** `SecAt c₀ δ`: 读回值 $\delta$ 是某个族 `F : Inc` 在 $c_0$ 处的值 (`LocUipNegSec` 的前提). `Uniform O c₀ rd`: 读回由输出 $o$ 对**一切**坐标给出一个族, 在 $c_0$ 处就是读回层上的读法 $\mathrm{rd}\,o$.
> - **§3 一级折叠, 以世界为参数.** `FoldW₁`: 外层世界 $w$, 坐标 $1$ 的可入证据 $p_0$, 分量函数 $v$, 层 $\Lambda$ ↦ 第 2 层输出. 记录 `Feed₁ R`: 折叠在 κ₂ 节点 $\mathrm{h\Omega}\,\kappa_2\,g$ 处是一条世界链上的 ℕ-极限 (`fold-Ω`); 链的每一步是族更新 `raiseF R` (`ch-s`), 增量是**折叠自己**在分支 $g(\text{当前槽})$ 上的输出经读回 `rdO` 得到的族 (`famO`); 链上世界合法, 两种相干都保, 只增 (`ch-lg`, `ch-coh`, `ch-≤`). 读回是折叠的输出, 不是参数: `rdO` 的参数是 `fold` 的值.
> - **§4 一级闭项.** `Fold₁ = (Λ : HB S₂) → LgB Λ → A`; 两种种类折叠的输入 `Input₁ = HB S₂ → Ht`; **不被压回** `NotPressed inp`: 级顶 `Ωtop S₁` 的输入不与 `Ω₂ᴴ` 互模拟, 也不与任何 `H₀` 嵌入 `up h` 互模拟 (对照 `TdPlusVal.pr-top`, `UipFbTop.pr₂-top`).
> - **§5 一切级.** 塔 `Sk`; `FoldAll`; 层的下降 `Down S` (把 `step S` 的高度折成 `S` 的高度, 合法由形状给出); 一步 `DownStep` (对塔的一步: 由第 $k$ 级的下降给出第 $k+1$ 级的下降) 与对一切级 `TowerDown`. 只有类型.
>
> **律的定义域 (逐条).** 每一条律里出现的每一对坐标都带同一个外层世界 $w=(a,b)$ 的可入证据:
>
> - `CohC` 的 `Coh≡`: 同一坐标 $c$ 的两个证据 $p, p' : c \lhd_{[a]} b$, 公共上界 $b$.
> - `CohC` 的 `CopyCoh`: $c_0$ 与 `hs c₀` 各带证据 $p_0, p_1$, 公共上界 $b$.
> - `Feed₁` 的 `ch-s`: 更新 `raiseF R w lo v c₁ p₀ δ`, 律 (`RaiseF` 的 `atF`, `belowF`, `monoF`, `legalF`, `cohF`) 只比较带 $w$ 的证据的坐标 (LocUipIf 原文); 本记录不加对裸坐标的律.
> - `Feed₁` 的 `fold-Ω`, `ch-z`: 只有一个坐标 $1$ 与它的证据 $p_0$.
> - `SecAt`, `Uniform`: 只有一个坐标 $c_0$; 族在别的坐标上的值不进任何律 (更新只在判定 "是 $c_0$" 的分量上用它, 判定在同一个界之下, `dD`).
> - `NotPressed`: 不含坐标.
> - §5: 不含坐标.
>
> 没有 "别处不变" 一类对一切坐标的律.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FamFoldIf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.CumReadCF using (A; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.HtTowerFTree using (S₁; H₀; Ht; Wd₂; nl)
open import OCF.Align.HtTowerNRead using (D₂)
open import OCF.Align.HtTowerFClosed using (Ω₂ᴴ)
open import OCF.Align.DiagK3Zero using (_≈_)
open import OCF.Align.AdmWIf
open import OCF.Align.AdmWCoh using (fin)
open import OCF.Align.LocUipIf using (Inc; RaiseF; raiseF; CopyCoh)
open Slot
```

## §1 世界

```agda
S₂ : KS
S₂ = step S₁

-- 一级的新种类: 坐标是 HB S₁
κ₂ : K S₂
κ₂ = inj₂ tt

c₁ : HB S₀
c₁ = fin 1

-- 两种相干: 跨证据 (同一坐标) 与拷贝 (c₀ 与 hs c₀), 都在同一外层界之下
CohC : Wᴮ → Set
CohC W = Coh≡ W × CopyCoh W

-- (c₀, p₀) 处的槽
slotAt : ∀ {w} → Cmp w → (c₀ : HB S₀) → AdmE w c₀ → HB (G₀ c₀)
slotAt v c₀ p₀ = proj₂ (v c₀ p₀)
```

## §2 读回对坐标一致

```agda
-- 读回值是某个族在 c₀ 处的值
SecAt : (c₀ : HB S₀) → HB (G₀ c₀) → Set
SecAt c₀ δ = Σ Inc (λ F → F c₀ ≡ δ)

-- 读回由输出对一切坐标给出族, 在 c₀ 处就是读回层上的读法
Uniform : (O : Set) (c₀ : HB S₀) → (O → HB (G₀ c₀)) → Set
Uniform O c₀ rd = Σ (O → Inc) (λ F → ∀ o → F o c₀ ≡ rd o)
```

## §3 一级折叠, 以世界为参数

```agda
-- 两种种类折叠第 2 层的输出 (对一切世界; 世界写成显式参数, 免得隐式实例化)
Out₂ : Set
Out₂ = (W : Wd₂) → D₂ W

-- 一级折叠: 外层世界, 坐标 1 的可入证据, 分量函数 (族增量世界), 层 ↦ 第 2 层输出
FoldW₁ : Set
FoldW₁ = ∀ (w : Out) → LgO w → AdmE w c₁ → Cmp w → HB S₂ → Out₂

record Feed₁ (R : RaiseF) : Set where
  field
    fold   : FoldW₁
    -- 读回: 第 2 层输出 ↦ κ₂ 的坐标 (HB S₁), 合法由形状给出
    rdO    : Out₂ → Ht
    lg-rdO : ∀ o → LgB (rdO o)
    -- 读回对坐标一致
    famO   : Uniform Out₂ c₁ rdO
    -- κ₂ 节点处的世界链
    chain  : ∀ w → LgO w → AdmE w c₁ → Cmp w → (Ht → HB S₂) → ℕ → Cmp w
    ch-z   : ∀ w lo p₀ v g → chain w lo p₀ v g zero ≡ v
    -- 每一步是族更新, 增量是折叠自己在分支 g (当前槽) 上的输出的读回
    ch-s   : ∀ w lo p₀ v g n →
             chain w lo p₀ v g (suc n) ≡
             raiseF R w lo (chain w lo p₀ v g n) c₁ p₀
               (proj₁ famO (fold w lo p₀ (chain w lo p₀ v g n) (g (slotAt (chain w lo p₀ v g n) c₁ p₀))))
    -- 折叠在 κ₂ 节点处: 链上分支的 ℕ-极限
    fold-Ω : ∀ w lo p₀ v g W →
             fold w lo p₀ v (hΩ κ₂ g) W ≡
             nl (λ n → fold w lo p₀ (chain w lo p₀ v g n) (g (slotAt (chain w lo p₀ v g n) c₁ p₀)) W)
    -- 链上的世界: 合法, 两种相干, 只增
    ch-lg  : ∀ w lo p₀ v g → LgWᴮ (w , v) → ∀ n → LgWᴮ (w , chain w lo p₀ v g n)
    ch-coh : ∀ w lo p₀ v g → CohC (w , v) → ∀ n → CohC (w , chain w lo p₀ v g n)
    ch-≤   : ∀ w lo p₀ v g n → (w , chain w lo p₀ v g n) ≤ᴮ (w , chain w lo p₀ v g (suc n))
```

## §4 一级闭项与 "不被压回"

```agda
Fold₁ : Set
Fold₁ = (Λ : HB S₂) → LgB Λ → A

-- 两种种类折叠 (T⁺) 的输入
Input₁ : Set
Input₁ = HB S₂ → Ht

-- 级顶的输入不与 Ω₂ᴴ 互模拟, 也不与任何 H₀ 嵌入互模拟
NotPressed : Input₁ → Set
NotPressed inp = ¬ (inp (Ωtop S₁) ≈ Ω₂ᴴ) × (∀ (h : H₀) → ¬ (inp (Ωtop S₁) ≈ up h))
```

## §5 一切级 (只有类型)

```agda
Sk : ℕ → KS
Sk zero = S₀
Sk (suc k) = step (Sk k)

FoldAll : Set
FoldAll = ∀ k → (Λ : HB (Sk (suc k))) → LgB Λ → A

-- 层的下降: step S 的高度折成 S 的高度, 合法由形状给出
record Down (S : KS) : Set where
  field
    down    : HB (step S) → HB S
    lg-down : ∀ x → LgB (down x)

-- 对塔的一步与对一切级
DownStep : Set
DownStep = ∀ k → Down (Sk (suc k)) → Down (Sk (suc (suc k)))

TowerDown : Set
TowerDown = ∀ k → Down (Sk (suc k))
```
