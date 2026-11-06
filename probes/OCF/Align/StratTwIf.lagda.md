# 分层互递归塔: 接口

> **接口定稿 2026-11-05 19:13 (首次编译通过).** 定稿之后只增不改; 若必须改, 在这里写变更记录. 变更记录: (无).

> 不含记号. 目标 (作者原话): "写出 ψ₀Λ 的候选闭项"; 作者本轮选定 "分层互递归塔". 本路 (前缀 `StratTw`) 是 [KindLv](KindLv.lagda.md) 接手清单第 1 条 (互递归的塔) 的**构造**一路; 否定一路 (前缀 `NegStratTw`) 导入本文件, 不另造接口. 本篇只放类型, 记录与只由构造子组成的定义, 不放证明与折叠. 导入 [HtTowerTy](HtTowerTy.lagda.md) (`KS`, `HB`, `Lev`, `step`, `up`), [GenFoldIf](GenFoldIf.lagda.md) (`DK`, `TopG`), [KindLvIf](KindLvIf.lagda.md) (`lyL`, `KLv`, `LvFb`), 都不改. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> ## 问题与分层
>
> KindLv 的草稿 `Cs (suc s) = step (Lev (Ys s))`, `Ys s : HB (sup ℕ Cs)` 停机检查失败. [判断] 这是类型层的真循环: 类型 `HB (sup ℕ Cs)` 的种类 $\Sigma_i K(C_i)$ 含 $K(C_{s+1})$, 而 $C_{s+1}$ 要 $Y_s$ 的值. **分层**: 按 $s$ 做普通的 ℕ 递归, 同时造**前缀结构** $P_s$ 与级 $X_s:\mathrm{HB}\,P_s$ (第 $s$ 站的级只用分量 $\le s$), 令 $C_{s+1}=\mathrm{step}(\mathrm{Lev}\,X_s)$, 总结构 $T=\mathrm{sup}\ \mathbb N\ C$. 总结构里的级 $Y_s:\mathrm{HB}\,T$ 另由 ℕ 递归写出 (层号对角的部分和); $Y_s$ 与 $X_s$ 的**同形**是一个归纳关系 `Sim` 的证据, 不是定义相等. 级读回沿 `Sim` 递归: 读级层 `lyL (Y s)` (在 $T$ 里, 是最终层的字面第一位置) 的数据, 输出 `HB (Lev X_s)` (就是第 $s+1$ 个分量的头种类的坐标类型).
>
> ## 对象
>
> - **种类映射 `KMap S′ T` (§1).** 只有数据: 种类的映射 $j$ 与坐标的反向转换 `cv κ : E T (j κ) → E S′ κ`. 没有律 (构造文件的实例里 `cv` 在每个分支上定义地是恒等).
> - **同形 `Sim M c X` (§1).** 数据类型, 四个构造子各对一个高度构造子: $0\sim0$, 后继, ℕ-极限逐项, $\Omega$-极限 (总结构里种类是 $j\,\kappa$, 分支在坐标 $e$ 处同形于前缀里在 `cv κ e` 处的分支). 不判定任何东西.
> - **沿同形的级读回与写入 `RdSTy`, `WrSTy` (§2).** `KindLvIf.RdLTy`/`WrLTy` 的推广: 级层用总结构里的 $c$, 级的高度用前缀里的 $X$ (`HB (Lev X)`), 两者由 `Sim` 连起来. $M=$ 恒等且 $c=X$ 时就是 `RdLTy`.
> - **分层塔 `StratTw T` (§3).** 字段: 前缀 `P s`, 前缀里的级 `X s`, 种类映射 `M s`, 总结构里的级 `Y s`, 同形 `sim s`, 合法 `lY s`, 对角相邻项 `Yfst s`, 头种类 `hd s` 与它的坐标类型 `hdE s : E T (hd s) ≡ HB (Lev (X s))`. 由字段定义 (只由构造子组成): 层号对角 `Bᴧ s = hs (Y s)`, 最终层 `ΛS = up (hl Bᴧ)`.
> - **每站头种类按自己的级回灌 `OwnHd` (§4).** 对一个 `LvFb`: 每个 $s$, 头种类 `hd s` 的回灌是 `inj₁ L`, 且 $L$ 的级层就是 `lyL (Y s)`. 这是构造一路要交的性质 (对照 `NegKindLvInst.only-κ₁`, `head-lossy`).
> - **坍缩的类型**: 用 `KindLvIf.CollLvFbTy` (不另写).
>
> ## 律的定义域 (逐条)
>
> 律里出现的每一对下标都带字面公共上界, 或者根本不比较两个下标:
>
> - `Yfst s : hs (Y s) ⊲[ w ] Y (suc s)` (对一切世界): 一对 $(\mathrm{hs}\,Y_s, Y_{s+1})$, 公共上界是 $Y_{s+1}$ 本身 (字面第一位置). 不比较两个站的前缀级 ($X_s$ 与 $X_{s+1}$ 在不同类型里, 没有律).
> - `sim s`: 一对 $(Y_s, X_s)$, 在两个类型里, 是形状的证据, 不是比较; 不判定.
> - `lY s`: 一个高度. `hdE s`: 一个种类的坐标类型 (`≡` 在 `Set` 里, 只用于陈述; 构造文件给 `refl`).
> - `OwnHd`: 每条只有一个站 $s$ 与一个种类 `hd s`; `ℓ L ≡ lyL (Y s)` 是同一个类型里两个项的定义相等, 不是下标比较.
> - `KMap`: 没有律.
> - 升界 (构造文件): 只在 ℕ 下标上点更新 (`GenFoldInst.upd`) 与换 `step` 的第二分量; 不用升界算子, 不写 "升一份留别份" 的律 (`NegKindLvInst.updHΛ-sep`).
>
> **`no-retract` 与壁垒 (检查).** 头种类 `hd s` 的坐标是 `HB (Lev X_s)`, $X_s$ 在前缀 $P_s$ 里; 没有种类以 `HB T` 或 `HB (step T)` 为坐标. 接口不要求任何下标类型上的三歧或判定. [判断] 不触壁垒; 否定一路若找到反例, 以它为准.
>
> **接口不管什么 (盲).** `OwnHd` 只说级层是自己的, 不说读回读了数据 (`NegKindLvBlind.relevel` 同型: 读回恒取起点满足 `KLv`). `Sim` 只说形状, 不说 `Lev (Y s)` 与 `Lev (X s)` 定义相等 (它们一般不相等). 所以接口不决定值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StratTwIf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_; inj₁)
open import Data.Product using (Σ; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (DK; TopG)
open import OCF.Align.KindLvIf using (lyL; KLv; ℓ; LvFb)
```

## §1 种类映射与同形

```agda
record KMap (S′ T : KS) : Set where
  field
    j  : K S′ → K T
    cv : (κ : K S′) → E T (j κ) → E S′ κ
open KMap public

data Sim {S′ T : KS} (M : KMap S′ T) : HB T → HB S′ → Set where
  sz : Sim M hz hz
  ss : ∀ {c X} → Sim M c X → Sim M (hs c) (hs X)
  sl : ∀ {f g} → (∀ n → Sim M (f n) (g n)) → Sim M (hl f) (hl g)
  sΩ : ∀ {κ h g} → (∀ e → Sim M (h e) (g (cv M κ e))) → Sim M (hΩ (j M κ) h) (hΩ κ g)
```

## §2 沿同形的级读回与写入

```agda
-- 读回: 起点 + 级层 lyL c 的数据 → 前缀里第 X 级的高度
RdSTy : KS → Set₁
RdSTy T = ∀ {S′} (M : KMap S′ T) (c : HB T) (X : HB S′) → Sim M c X →
          ∀ {W} → LgW (step T) W → HB (Lev X) → DK T (lyL c) W → HB (Lev X)

-- 写入: 前缀里第 X 级的高度 → 级层 lyL c 的数据 (对一切世界)
WrSTy : KS → Set₁
WrSTy T = ∀ {S′} (M : KMap S′ T) (c : HB T) (X : HB S′) → Sim M c X →
          ∀ {W} → HB (Lev X) → DK T (lyL c) W
```

## §3 分层塔

```agda
record StratTw (T : KS) : Set₁ where
  field
    P    : ℕ → KS
    X    : (s : ℕ) → HB (P s)
    M    : (s : ℕ) → KMap (P s) T
    Y    : ℕ → HB T
    sim  : ∀ s → Sim (M s) (Y s) (X s)
    lY   : ∀ s → LgB (Y s)
    Yfst : ∀ s {w} → hs (Y s) ⊲[ w ] Y (suc s)
    hd   : ℕ → K T
    hdE  : ∀ s → E T (hd s) ≡ HB (Lev (X s))
open StratTw public

-- 层号对角与最终层
Bᴧ : ∀ {T} → StratTw T → ℕ → HB T
Bᴧ St s = hs (Y St s)

ΛS : ∀ {T} → StratTw T → HB (step T)
ΛS St = up (hl (Bᴧ St))
```

## §4 每站头种类按自己的级回灌

```agda
OwnHd : ∀ {T} (St : StratTw T) (tp : TopG T) → LvFb T tp (ΛS St) → Set
OwnHd {T} St tp lv =
  ∀ s → Σ (KLv T tp (ΛS St) (hd St s)) (λ L → (lv (hd St s) ≡ inj₁ L) × (ℓ L ≡ lyL (Y St s)))
```
