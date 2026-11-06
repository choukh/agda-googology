# LeanLv: 接口 (种类的嵌入, 层与层号的同形, 沿同形的级读回)

> **接口定稿 2026-11-05 22:11 (首次编译通过).** 定稿之后只增不改; 若必须改, 在这里写变更记录. 变更记录: 2026-11-05 只增 §6 (`Sim⁺`, `RdS⁺Ty`): 极限位置带一个可选的 "后继种类" 嵌入, 不改 §1–§5.

> 不含记号. 构造一路前缀 `LeanLv`, 否定一路前缀 `NegLeanLv` 导入本文件, 不另造接口. 只放类型与记录, 不放证明. 只导入 [LeanTBase](LeanTBase.lagda.md), [LeanTLv](LeanTLv.lagda.md), [LeanTTree](LeanTTree.lagda.md), [LeanFbIf](LeanFbIf.lagda.md), 都不改. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> **问题** (作者 2026-11-05 选定, 原话 "LeanFb: 头按自己的级读回"). [LeanFb](LeanFb.lagda.md) 的第 $n\ge2$ 站的头 `νS n` (坐标 `HB (Lv (st n))`) 的读回在级层 $1$ 上, 输出只含一个级 0 种类的 $\Omega$-结点 (否定一路 `NegLeanFbInst.rdX-one-kind`). 按自己的级读回要: 级层 $\ell$ 的子层与 `Lv x` 的种类对应, 过子层的结点读成对应种类的 $\Omega$-结点 ([KindLvRd](../Align/KindLvRd.lagda.md), [StratTwRd](../Align/StratTwRd.lagda.md) 的形状). 本接口把这件事拆成三样:
>
> - **`Emb S′ S` (§1, 种类的嵌入).** `S′` 的种类搬进 `S` (`j`), 坐标来回 (`cv`, `vc`, `cv-vc`), 世界向下投影 (`π`, `lgπ`), 界与第一位置沿投影搬 (`bd→`, `bd←`, `pr→`). 同 `KindLvIf.Emb`, 去掉 `lgE→` (`KS` 没有 `LgE`, 见 [LeanTBase](LeanTBase.lagda.md) 头第 2 条).
> - **`Sim T a x` (§2, 层与层号的同形).** 层 $a$ : `HB (step T)` 与层号 $x$ : `LH` 逐构造子对上: $0\sim$`lz`, 后继, $\mathbb N$-极限逐项, $\Omega$-极限 `hΩ κ h` $\sim$ `lΩ k g` 带一个坐标映射 `cv : E (step T) κ → HB (Lv k)` 与逐支同形. 没有律, 是数据.
> - **`RdSTy T` (§3, 沿同形的级读回的类型)** 与 **`LvSim T Λ Q` (§4)**: 接口 `LvRd` 的一个实例, 带它的级层到某个 $x$ 的同形与 `Lv x` 到 `Q` 的嵌入. "**按自己的级**" 指 $x$ 就是这个种类的坐标的层号, 嵌入是恒等 (构造一路写成形状定理, 不是律).
> - **`HasK κ h` (§5).** 高度 $h$ 里有种类 $\kappa$ 的 $\Omega$-结点 (共用的词汇, 形状定理用).
>
> ## 律的定义域 (逐条)
>
> - `Emb.bd→`, `bd←`: 一个种类, 一个世界, 一个坐标. `pr→`: 一个种类, 一个世界里的一对坐标, 前提是这一对的第一位置 (`Pr`, 公共上界是后一个). `cv-vc`: 一个坐标. `lgπ`: 一个世界. 不比较两个种类.
> - `Sim`: 数据, 没有律. 不判定层号相等, 不比较两个层.
> - `LvSim`: 继承 `LvRd.ℓ⊲` (一对 $(\ell,\Lambda)$, 公共上界是字面的 $\Lambda$); `σ` 与 `em` 是证据 (构造给出), 不是对裸下标的判定.
>
> 没有对两个下标的比较律, 没有 "留别份" 律.
>
> **接口不管什么 (盲).** (1) `LvSim` 不逼 `R` 的读回是沿 `σ` 读的: `R` 可以是任一 `LvRd` (例如 `NegLeanFbBlind.rdConst`), `σ`, `em` 只是随附的证据. 读回是否沿同形, 由构造一路对实例写形状定理. (2) `Sim` 的 `cv` 任意: 常值映射也满足, 这时一切分支读进同一个分量. (3) `Emb` 不要求 `j` 单射; 嵌入可以把不同的种类放到一处 (只要坐标类型一致). (4) "自己的级" (`x` 等于坐标的层号, `em` 是恒等) 不是律.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LeanLvIf where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanTTree
open import OCF.Lean.LeanFbIf
```

## §1 种类的嵌入

```agda
record Emb (S′ S : KS) : Set where
  field
    j     : K S′ → K S
    cv    : ∀ {κ} → E S (j κ) → E S′ κ
    vc    : ∀ {κ} → E S′ κ → E S (j κ)
    cv-vc : ∀ {κ} (c : E S′ κ) → cv {κ} (vc c) ≡ c
    π     : Wd S → Wd S′
    lgπ   : ∀ {w} → LgW S w → LgW S′ (π w)
    bd→   : ∀ {κ e w} → Bd S (j κ) e w → Bd S′ κ (cv e) (π w)
    bd←   : ∀ {κ c w} → Bd S′ κ c (π w) → Bd S (j κ) (vc c) w
    pr→   : ∀ {κ e e′ w} → Pr S (j κ) w e e′ → Pr S′ κ (π w) (cv e) (cv e′)
open Emb public
```

## §2 层与层号的同形

```agda
module _ (T : KS) where
  data Sim : HB (step T) → LH → Set where
    sz : Sim hz lz
    ss : ∀ {a x} → Sim a x → Sim (hs a) (ls x)
    sl : ∀ {f g} → (∀ n → Sim (f n) (g n)) → Sim (hl f) (ll g)
    sΩ : ∀ {κ h k g} (cv : E (step T) κ → HB (Lv k)) → (∀ e → Sim (h e) (g (cv e))) → Sim (hΩ κ h) (lΩ k g)
```

## §3 沿同形的级读回 (类型)

层 $a$ 上的数据, 沿 `Sim T a x` 读进 `Lv x` 的高度, 再经嵌入放进任一 $X$ (带一个起点).

```agda
RdSTy : KS → Set₁
RdSTy T = ∀ {a x} → Sim T a x → ∀ {X : KS} → Emb (Lv x) X → ∀ {W} → LgW (step T) W → HB X → Tree.D T a W → HB X
```

## §4 带同形的级读回实例

```agda
module _ (T : KS) (Λ : HB (step T)) where
  record LvSim (Q : KS) : Set₁ where
    field
      R  : LvRd T Λ Q
      x  : LH
      σ  : Sim T (LvRd.ℓ R) x
      em : Emb (Lv x) Q
  open LvSim public
```

## §5 高度里有某个种类的 $\Omega$-结点

```agda
data HasK {S : KS} (κ : K S) : HB S → Set where
  here : ∀ {g} → HasK κ (hΩ κ g)
  inS  : ∀ {a} → HasK κ a → HasK κ (hs a)
  inL  : ∀ {f} n → HasK κ (f n) → HasK κ (hl f)
  inΩ  : ∀ {κ′ g} c → HasK κ (g c) → HasK κ (hΩ κ′ g)
```

## §6 只增: 极限位置带后继种类的同形

`Sim` 在极限位置 (ℕ-极限的第 $n$ 支本身, $\Omega$-极限坐标 $e$ 的一支本身) 没有种类: 过这一支本身的结点, 它的分支以这一支 (同形于 $g\,n$ 或 $g\,(\mathrm{cv}\,e)$) 上的数据为输入, 对应的种类是 `step (Lv (g n))` 的新种类, 不在 `Lv (ll g)` 或 `Lv (lΩ k g)` 的字面分量里. `Sim⁺` 在这两处多带一个可选的嵌入 `Emb (Lv (ls (g _))) (Lv _)` (`inj₂ tt` 表示没有). 构造一路的实例: `st 2 = lΩ lz g₂` 在坐标 $c$ 处取分量 `inj₂ (hs c)` (那里 `g₂ (hs c)` 定义相等于 `ls (g₂ c)`; 否定一路 `NegLeanLvPre.succK-co` 的种类). 定义域: 数据, 没有律; 嵌入是证据.

```agda
module _ (T : KS) where
  data Sim⁺ : HB (step T) → LH → Set where
    sz⁺ : Sim⁺ hz lz
    ss⁺ : ∀ {a x} → Sim⁺ a x → Sim⁺ (hs a) (ls x)
    sl⁺ : ∀ {f g} → (∀ n → Sim⁺ (f n) (g n)) → (∀ n → Emb (Lv (ls (g n))) (Lv (ll g)) ⊎ ⊤) → Sim⁺ (hl f) (ll g)
    sΩ⁺ : ∀ {κ h k g} (cv : E (step T) κ → HB (Lv k)) → (∀ e → Sim⁺ (h e) (g (cv e))) →
          (∀ e → Emb (Lv (ls (g (cv e)))) (Lv (lΩ k g)) ⊎ ⊤) → Sim⁺ (hΩ κ h) (lΩ k g)

RdS⁺Ty : KS → Set₁
RdS⁺Ty T = ∀ {a x} → Sim⁺ T a x → ∀ {X : KS} → Emb (Lv x) X → ∀ {W} → LgW (step T) W → HB X → Tree.D T a W → HB X
```

