# 新塔: 接口 (每一处都不落回固定类型)

> **接口定稿 2026-11-05 17:39 (首次编译通过).** 定稿之后只增不改; 若必须改, 在这里写变更记录. 变更记录 (只有文字说明, 不改任何定义): (i) 2026-11-05 文字更正: "塔的形状" 一段的 "闭项 cl(1⊞up(hl Bᴧ))" 应读作 "cl(up(hl Bᴧ))", 前面接 $1$ 由坍缩的实现 `NewTwrColl.collG` 自己做. (ii) 2026-11-05 文字更正 (依否定一路 `NegNewTwrShape.codC`, `retC`, `stage0-Ht`, `viaHt`): "类型论证" 里标 [定理, 构造文件] 的两条 (值域与最终层不是 `Ht` 的收缩; 值域依赖上一站的值) **不是本接口的后果**, 是构造文件对具体实例 `NewTwrK.N₀` 的定理; 常数下降或 $b_0=1$ 时值域就是 `Ht`, 任何保合法的 `HB (step T) → Ht` 接 `T⁺` 也是 `CollK`. 接口只给类型的位置, 不保证不落回 `Ht`.
>
> 不含记号. 目标 (作者原话): "写出 ψ₀Λ 的候选闭项". 本路 (前缀 `NewTwr`) 是 [GenFold](GenFold.lagda.md) 接手清单第 1、2 条的**构造**一路; 否定一路 (前缀 `NegNewTwr`) 导入本文件, 不另造接口. 本篇只放类型与记录, 不放证明与折叠. 导入 [HtTowerTy](HtTowerTy.lagda.md) (`KS`, `HB`, `Lev`, `step`, `sup`), [LvKtIf](LvKtIf.lagda.md) (`Kc`, `KΛc`, `nxt`, `emb`, `injL`, `ιΛ`), [GenFoldIf](GenFoldIf.lagda.md) (`GenK`, `LgDn`, `FbLg`), 都不改. **不导入 `Ht`** (`HtTowerFTree`), 也不导入 `HtTowerFClosed.T⁺`: 接口里没有一处的值落在固定的 `Ht` 里. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> ## 类型论证 (从层号到闭项, 每一步的值所在的类型)
>
> 记 $B_s$ 为第 $s$ 站的层号. 下表每一行是一个类型事实 (由定义给出; 构造文件里写成 `refl` 定理的标 [定理]), 最后一列说它的上界是不是固定的.
>
> | 步 | 值 | 类型 | 上界 |
> |---|---|---|---|
> | 0 | 起点 $b_0$ | `HB S₀` | 起点 |
> | 1 | 第 $s$ 站层号 $B_s$ | `HB (Kc s)`; `Kc (s+1) = nxt (Kc s) = sup (⊤ ⊎ HB (Kc s)) (FN (Kc s))` | 随 $s$ 变: 第 $s+1$ 站的种类以第 $s$ 站的**一切**高度为下标 |
> | 2 | 第 $s$ 站的下降 (求值后的读回) | `HB (Lev B_s)` (`RdK`, §1); 构造文件取 $B_s=\mathrm{hs}\,X$, `Lev B_s = step (Lev X)` [定理] | 随 $B_s$ 变 (类型依赖于上一站算出的值); 不是 `Ht` |
> | 2′ | 求值内部: 层, 世界, 数据树 | `HB (step (Lev X))`, `Wd (step (Lev X))`, `GenFoldIf.DK (Lev X)` | 同上 |
> | 3 | 增量 | `injL B_s (…) : HB (Kc (s+1))` | 随 $s$ 变 |
> | 4 | 层号对角 | `Bᴧ s : HB KΛc`, `ΛB = hl Bᴧ : HB KΛc` | `KΛc = sup ℕ Kc`, 一切站的并 |
> | 5 | 最终坍缩的层 | `HB (step KΛc)` (`CollK KΛc`, §2) | 对角之上一步 |
> | 6 | 最终坍缩 | GenFold 的一般折叠 `GenFoldRun KΛc …` 在 `step KΛc` 上折到第 0 层, `sum` 成 `A` | — |
> | 7 | 闭项, FGH | `A`, `ℕ → ℕ` | — |
>
> 与 [GenFold](GenFold.lagda.md) 的对照 (类型事实): 那里每站的下降 `EvSys.evH : … → Ht`, 闭项 `T⁺ : (h : Ht) → LgB h → A`; 步 2 与步 5 都落回 `Ht`. 本接口的步 2 值域是 `HB (Lev b)` ($b$ 是本站层号), 步 5 是 `HB (step KΛc)`.
>
> **"不再有固定上界" 的哪部分是定理, 哪部分是判断.**
>
> - [定理, 构造文件] 每站的下降值域与最终层的类型都**不是 `Ht` 的收缩**: 它们的种类结构里有坐标类型为 `Ht` 的种类, 由 `NegDnFoldRet.no-faithful` (对一切 `S`, `HasHt S` ⇒ 任何 `HB S → Ht` 无左逆), 任何到 `Ht` 的映射都丢东西.
> - [定理, 构造文件] 第 $s+1$ 站的值域 `HB (Lev B_{s+1})` 定义相等于 `HB (step (Lev X_s))`, 其中 $X_s$ 是含第 $s$ 站下降值的 `HB (Kc (s+1))` 的元素: 值域的类型依赖于上一站算出的值.
> - [判断] "值域随站变大" 指的是类型族 `s ↦ HB (Lev B_s)` 没有一个共同的、与 $s$ 无关的类型作上界 (除了最后的 `HB (step KΛc)`, 它是一切站的并之上一步). 这是类型的读法, 不是关于序数值的定理.
>
> ## 对象
>
> - **`RdK K`** (§1): 对种类结构 `K` 的每个合法层号 $b$, 给出第 $b$ 级的一个合法高度 (类型 `HB (Lev b)`). **这就是新塔的 "下降"**: 值域是本站读回所在的类型, 不是 `Ht`. `RdTower = ∀ s → RdK (Kc s)`.
> - **`CollK T`** (§2): 在 `step T` 的层上的坐标塌缩, 输出布劳威尔树 `A` 与它的合法 (`Lg`). `CollGenTy`: GenFold 的一般折叠给出的形状 (对一切带 `GenK T`, `LgDn T`, `FbLg` 的 $T$).
> - **`NewTw`** (§3): 新塔的参数: 每站的下降 `rd`, 起点 $b_0$ (合法), 在 `KΛc` 上的最终坍缩 `cl`.
>
> **塔的形状 (构造文件写成定义, 这里只说形状).** $B_0=b_0$; $B_{s+1}=\mathrm{emb}\,B_s\boxplus\mathrm{injL}\,B_s\,(\mathrm{rd}\,s\,B_s)$; 层号对角 $\mathrm{B}^\Lambda_0=\iota_0 b_0$, $\mathrm{B}^\Lambda_{s+1}=\mathrm{B}^\Lambda_s\boxplus\iota_{s+1}(\mathrm{injL}\,B_s\,(\mathrm{rd}\,s\,B_s))$ (`LvKtTower.Tower.Bᴧ` 的形状, 部分和, 否则撞 `NegLvKtTrap.diag-trap`); 闭项 $\mathrm{cl}(1\boxplus\mathrm{up}(\mathrm{hl}\,\mathrm{B}^\Lambda))$.
>
> ## 律的定义域 (逐条)
>
> 律里出现的每一对下标都带字面公共上界, 或者根本不比较两个下标:
>
> - `RdK`: 一个层号 $b$, 输出一个高度与它的合法. 不比较两个层号, 不比较两站, 不判定.
> - `CollK.lgCol`: 一个层 $h$ 与它的合法. 不比较.
> - `NewTw`: 记录, 不含律.
> - 塔里用到的律 (构造文件): `emb`, `injL`, `ιΛ` 是并的分量注入 (`ι-⊲`, `Lg-ι`, 只对同一分量里的一对高度, 公共上界是这个分量的世界); `⊞-fst` (一对高度 $a$, $a\boxplus b$, 公共上界是后者). 对角相邻项同在 `HB KΛc`, 第一位置由 `⊞-fst` 给出.
> - 最终坍缩内部 (GenFold 的一般折叠): 唯一的比较是 `cmpB`, 公共上界是最高层; 回灌只在可判定下标上点更新 (`GenFoldInst.upd`, `updL`), 其余有损 (GenFold 接口的律, 不在本接口里重述). 本接口**不含 "升一份留别份"** (`NegGenFoldUpd.upd₁-sep`).
>
> **`no-retract` 与壁垒 (检查).** `Kc (s+1)` 的种类以 `HB (Kc s)` 为下标, `KΛc` 的种类是各 `Kc s` 的种类, 最终层在 `HB (step KΛc)`: `step KΛc` 的新种类以 `HB KΛc` 为坐标, 没有种类以 `HB (step KΛc)` 自身为坐标. 本接口不要求任何下标类型上的三歧或判定. [判断] 不触壁垒; 否定一路若找到反例, 以它为准.
>
> **接口不管什么 (盲).** `RdK` 被常数下降满足 (例如 `λ b _ → hz , tt`); `CollK` 被常数坍缩满足 (`col = λ _ _ → azero`). 所以接口不决定值; "读回进了闭项" 是构造文件里对具体塔的形状定理, 不是接口的律 (手册 §3.3, §3.7).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NewTwrIf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Align.CumReadCF using (A; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.LvKtIf using (Kc; KΛc)
open import OCF.Align.GenFoldIf using (GenK; LgDn; FbLg)
```

## §1 下降: 值域是本站读回所在的类型

```agda
-- 第 b 级的合法高度
LvV : ∀ {K : KS} → HB K → Set
LvV b = Σ (HB (Lev b)) (λ r → LgB r)

-- 对种类结构 K 的一切合法层号的下降
RdK : KS → Set
RdK K = ∀ (b : HB K) → LgB b → LvV b

-- 每站一条
RdTower : Set
RdTower = ∀ s → RdK (Kc s)
```

## §2 最终坍缩: 在 `step T` 的层上, 输出 `A`

```agda
record CollK (T : KS) : Set where
  field
    col   : (h : HB (step T)) → LgB h → A
    lgCol : ∀ h (lh : LgB h) → Lg (col h lh)
open CollK public

-- GenFold 的一般折叠给出的形状 (构造文件实现)
CollGenTy : Set₁
CollGenTy = ∀ {T : KS} (G : GenK T) → LgDn T → FbLg G → CollK T
```

## §3 新塔的参数

```agda
record NewTw : Set where
  field
    rd  : RdTower
    b₀  : HB S₀
    lb₀ : LgB b₀
    cl  : CollK KΛc
open NewTw public
```

**定稿时刻.** 2026-11-05 17:39 (首次编译通过).
