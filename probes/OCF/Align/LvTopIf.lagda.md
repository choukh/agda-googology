# 整座塔加对角: 接口 `FoldAt`

> **接口定稿 2026-11-05 (编译通过).** 定稿之后只增不改; 若必须改, 在这里写变更记录. 变更记录: (无).
>
> 不含记号. 作者此前选定的方向原话: "A3: 读回包 + 第 ω+1 级折叠"; 本路 (前缀 `LvTop`) 是它的续作, 目标 (作者原话) "写出 ψ₀Λ 的候选闭项". 入口 [LvTop](LvTop.lagda.md). 本篇只放类型与记录, 不放证明. 依赖 [LvFbCode](LvFbCode.lagda.md) 的路径码 `Code`, `tgt`, [HtTowerTy](HtTowerTy.lagda.md) 的 `Lev` (种类结构以高度为下标). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> **对象.**
>
> - **码与世界.** 外层 `A`-世界固定为 $0$ (与 `LvRd` 同). 界 $b$ (`HB S₀` 的合法高度) 之下的码 `Cod b = Code 0 b` (从界往下的字面路径, 数据, 相等可判定, `LvFbCode.code-≟`). 码 $k$ 的目标是坐标 `tgt k`, 它的槽是第 `tgt k` 级的高度 `HB (Lev (tgt k))`. 世界 `Wb b`: 界 $b$ 之下每个码一个槽 (`LvRdIf.Wld` 的推广: 界不再固定为 $\omega+1$, 槽类型由 `Lev` 给出, 不由码的形状逐个写).
> - **`FoldAt Cov`: 在码目标 $c$ 上的一级折叠.** 输入: 界 $b$ (合法), $b$ 之下的码 $c$, 覆盖证据 `Cov (tgt c)`, $c$ 所在的世界 $w$ (合法). 输出: 第 $\mathrm{tgt}\,c+1$ 级的级顶 (`Ωtop (Lev (tgt c))`) 经这一级折叠的读回 `rt` (落在 $c$ 的槽类型里, 供极限站回灌), 以及它降到 `Ht` 的回灌输出 `H`. 两个输出都合法 (`lrt`, `lgH`): 这是接口的律, 塔的合法性由它们与形状给出. `Cov` 是 "这个实例覆盖哪些坐标"; 一切码上的折叠是 `FoldAll = FoldAt (λ _ → ⊤)`.
>
> **律的定义域 (逐条).** 律里出现的每一对下标都带字面公共上界:
>
> - `rt`, `lrt`, `H`, `lgH`: 每条只出现**一个**码 $c$, 它带着字面的界 $b$ (路径 `pth c : tgt c ⊲ b` 就是证据); 世界 $w$ 是界 $b$ 之下的码到槽的函数, 律不比较两个码, 不比较两个坐标. 没有 "两个下标相等时 ..." 形状的律 (比较 `StallDiagnosis`: 裸下标上的更新律会重证判等).
> - 接口不含更新律: 世界在塔里怎样构造 (各站的世界, 极限站的世界) 在 [LvTopTower](LvTopTower.lagda.md), 那里用到的判定只有码的数据判定 (对码的构造子分情形) 与 `NegLvRdWk.Canon` 的码的前缀判定 (`prefix?`, 数据).
>
> **接口不管什么 (盲, 定理在 [LvTopVal](LvTopVal.lagda.md) `foldTriv`).** 记录只要求输出合法; 恒取 $0$ 的折叠也是实例. 所以接口不决定值: 全塔版本的读法依赖实际给的 `FoldAt`, 不依赖接口.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvTopIf where

open import Data.Unit using (⊤; tt)
open import OCF.Align.CumReadCF using (azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (Ht)
open import OCF.Align.LvFbCode using (Code; tgt)
```

## §1 码与世界

```agda
-- 界 b 之下的码 (外层 A-世界取 0)
Cod : HB S₀ → Set
Cod b = Code azero b

-- 界 b 之下的世界: 每个码一个槽, 槽是码目标那一级的高度
Wb : HB S₀ → Set
Wb b = (k : Cod b) → HB (Lev (tgt k))

LgWb : ∀ {b} → Wb b → Set
LgWb w = ∀ k → LgB (w k)
```

## §2 在码目标上的一级折叠

```agda
record FoldAt (Cov : HB S₀ → Set) : Set where
  field
    -- 第 tgt c + 1 级的级顶经这一级折叠的读回, 落在 c 的槽类型里
    rt  : ∀ {b} → LgB b → (c : Cod b) → Cov (tgt c) → (w : Wb b) → LgWb w → HB (Lev (tgt c))
    lrt : ∀ {b} (lb : LgB b) c (cv : Cov (tgt c)) w (lw : LgWb w) → LgB (rt lb c cv w lw)
    -- 级顶的回灌输出, 降到 Ht
    H   : ∀ {b} → LgB b → (c : Cod b) → Cov (tgt c) → (w : Wb b) → LgWb w → Ht
    lgH : ∀ {b} (lb : LgB b) c (cv : Cov (tgt c)) w (lw : LgWb w) → LgB (H lb c cv w lw)

-- 一切码上的折叠
FoldAll : Set
FoldAll = FoldAt (λ _ → ⊤)
```
