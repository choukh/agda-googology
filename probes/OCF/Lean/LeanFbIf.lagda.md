# LeanFb: 接口 (一起升, 按级读回, 回灌计划)

> **接口定稿 2026-11-05 21:23 (首次编译通过).** 定稿之后只增不改; 若必须改, 在这里写变更记录. 变更记录: 2026-11-05 22:00 只改文字, 代码未动: 依否定一路 `NegLeanFbBlind.rdConst` (常数读回 $\delta\equiv1$ 满足 `δ-n1`), 把 "看数据 (`δ-n1` …)" 与盲区第 (1) 条 "`δ-n1` 只排除完全不看数据的读回" 更正为下文的写法.

> 不含记号. 构造一路前缀 `LeanFb`, 否定一路前缀 `NegLeanFb` 导入本文件, 不另造接口. 只放类型与记录, 不放证明. 只导入 [LeanTBase](LeanTBase.lagda.md), [LeanTTree](LeanTTree.lagda.md), 都不改. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> **问题.** [LeanTFold](LeanTFold.lagda.md) 的级回灌参数 `fb : K T → Fb ⊎ ⊤` 只要 "级层, 起点, 升界, 两条律". 否定一路的 `NegLeanFbPre.stayFb`, `relevelFb` 说明 `Fb` 记录不逼回灌读数据, 也不逼升界. 本接口把一个非有损的种类要的东西拆成两件, 并要求触发回灌的种类自己是被升的成员:
>
> - **`Up T Q` (§1, 一起升).** 一族成员 `κJ j` ($j$ : `J`, `J` 可以含函数), 每个成员的坐标读进公共的高度类型 `HB Q` (`co j`). 一次调用 `rz δ w` 把**一切**成员的界加上同一个增量 $\delta$ (`rz-top`: 成员 $j$ 升后的顶读出来是原顶 $\boxplus\,\delta$), 世界变大 (`rz≤`), 合法 (`rzLg`). 不判定下标. 站以 $\mathbb N$ 为下标时一个站的头就是只有一个成员的 `Up`.
> - **`LvRd T Λ Q` (§2, 按级读回).** 级层 `ℓ` ($\Lambda$ 的字面第一位置, 对一切世界), 读回 `δ`: 级层上的数据读成 `HB Q` 的一个增量, 合法 (`δLg`), `δ-n1`: 数据 $1$ 读成 $1$ (这一条**不**排除不看数据的读回: 常数 $1$ 满足它, `NegLeanFbBlind.rdConst`).
> - **`Feed`, `Plan` (§3).** 一个种类 $\kappa$ 的回灌是一个公共类型 $Q$, 一个 `LvRd`, 一个 `Up`, 与 "$\kappa$ 是这个 `Up` 的成员" 的证据 (`mem`, 一个字面的成员下标与相等). `Plan`: 每个种类或者有 `Feed`, 或者有损.
>
> ## 律的定义域 (逐条)
>
> - `rz≤`, `rzLg`: 一个世界, 一个增量. 公共上界是 `rz δ w` 本身.
> - `rz-top`: **一个**成员 $j$, 一个世界. 不比较两个成员.
> - `co`: 一个成员, 一个坐标.
> - `ℓ⊲`: 一个层; 公共上界是字面的 $\Lambda$.
> - `δLg`, `δ-n1`: 一个世界上的一份数据.
> - `mem`: 一个成员下标与一个种类的相等, 是**证据** (构造给出), 不是对裸下标的判定律.
>
> 没有对两个下标的比较律, 没有 "留别份" 律 (见下面的盲区第 2 条).
>
> **接口不管什么 (盲).** (1) `δ-n1` 不排除不看数据的读回 (常数 $1$ 满足它); 读回是否看数据, 是否在自己的级上 (级层与成员坐标的级一致), 是否产出高层种类的 $\Omega$-结点, 都不是律, 只能对构造一路的实例写形状定理 (同 `NegKindLvBlind.relevel`). (2) `Up` 不说非成员的界怎样变: 一次调用可以升一切种类 (否定一路的 `allFb` 形状满足它). (3) 加性的 `rz-top` 说的是 "加同一个增量", 不是 "置成同一个值"; 成员原来的界相同时升后仍相同, 但接口不带 "同界" 的世界证据 (对照 `SlotIf.ShW`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LeanFbIf where

open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTTree
```

## §1 一起升

```agda
record Up (T : KS) (Q : KS) : Set₁ where
  field
    J      : Set
    κJ     : J → K T
    co     : ∀ j → E T (κJ j) → HB Q
    rz     : HB Q → Wd T → Wd T
    rz≤    : ∀ δ w → _≤w_ T w (rz δ w)
    rzLg   : ∀ {δ w} → LgB δ → LgW T w → LgW T (rz δ w)
    rz-top : ∀ j δ w → co j (top T (κJ j) (rz δ w)) ≡ co j (top T (κJ j) w) ⊞ δ
open Up public
```

## §2 按级读回

```agda
module _ (T : KS) (Λ : HB (step T)) where
  open Tree T

  record LvRd (Q : KS) : Set₁ where
    field
      ℓ    : HB L₀
      ℓ⊲   : ∀ {w} → ℓ ⊲[ w ] Λ
      δ    : ∀ {W} → LgW L₀ W → D ℓ W → HB Q
      δLg  : ∀ {W} (lW : LgW L₀ W) x → LgB (δ lW x)
      δ-n1 : ∀ {W} (lW : LgW L₀ W) → δ lW n1 ≡ hs hz
  open LvRd public
```

## §3 回灌计划

```agda
  record Feed (κ : K T) : Set₂ where
    field
      Q   : KS
      R   : LvRd Q
      U   : Up T Q
      mem : Σ (J U) (λ j → κJ U j ≡ κ)
  open Feed public

  Plan : Set₂
  Plan = (κ : K T) → Feed κ ⊎ ⊤
```
