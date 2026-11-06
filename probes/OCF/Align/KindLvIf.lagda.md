# 按级回灌: 接口 (每个种类按自己的级回灌)

> **接口定稿 2026-11-05 18:33 (首次编译通过).** 定稿之后只增不改; 若必须改, 在这里写变更记录. 变更记录: 2026-11-05 只增 §5 `CollLvFbTy` (坍缩的类型多带 `FbLg G`: 构造文件的折叠在 `lv κ = inj₂ tt` 时退回 `GenFoldRun` 原样的 A-回灌一行, 不是一律有损), 不改已有定义; 文件头 "`inj₂ tt` 时有损" 一句对构造文件的折叠应读作 "`inj₂ tt` 时按 `fbA G κ` (A-回灌或有损)".

> 不含记号. 目标 (作者原话): "写出 ψ₀Λ 的候选闭项". 本路 (前缀 `KindLv`) 是 [NewTwr](NewTwr.lagda.md) 接手清单第 1 条 (作者选定 "R 与按级回灌一起派") 的**构造**一路; 否定一路 (前缀 `NegKindLv`) 导入本文件, 不另造接口. 本篇只放类型与记录, 不放证明与折叠. 导入 [HtTowerTy](HtTowerTy.lagda.md) (`KS`, `HB`, `Lev`, `step`, `up`), [GenFoldIf](GenFoldIf.lagda.md) (`DK`, `TopG`, `GenK`, `LgDn`), 都不改. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> ## 对象
>
> - **级层与级读回 (§2).** 种类结构 $T$ 的高度 $c$ 叫一个**级**; 它的**级层**是 `hs (up c) : HB (step T)` (同 `KcFoldIf.lyK`). `RdLTy T`: 级层的数据读进**第 $c$ 级的高度** `HB (Lev c)` (带一个起点); `WrLTy T`: 反方向, 第 $c$ 级的高度写成级层的数据. 构造文件对 $c$ 的构造子递归: 过第 $k\lhd\mathrm{up}\,c$ 层的结点读成 `Lev c` 里沿路径 $k\lhd\mathrm{up}\,c$ 的种类的 $\Omega$-结点 (路径停在 $\mathrm{hs}\,c_1$ 处是 `step (Lev c₁)` 的新种类, 坐标 `HB (Lev c₁)`, 输入就是第 $c_1$ 级的级层数据; 停在 $0$ 处是底种类, 坐标 `A`). 在 `S₀` ($c=0$, 级层 $1$) 上它与 `GenFoldRd.rd₁` 同型, 在 `step S₀` ($c=1$, 级层 $2$) 上与 `rd₂` 同型 (构造文件写对照).
> - **嵌入 `Emb S′ S` (§1).** 把 `S′` 的种类搬进 `S` (坐标来回不丢, 世界向下投影, 界与第一位置沿投影搬). 级读回要它: 坐标 $y$ 的 $\Omega$-结点 (种类在 `Lev c₁` 里) 要读成 `Lev c` 的 $\Omega$-结点. 实例只有三个构造: 恒等, `step` 的旧种类, 并的一个分量 (构造文件).
> - **每个种类的级回灌 `KLv T tp Λ κ` (§3).** 种类 $\kappa$ 的级层 $\ell$ (是最终层 $\Lambda$ 的字面第一位置), 级层数据到 $\kappa$ 的坐标的读回 `rd` (带起点), 把世界里 $\kappa$ 的界升到一个坐标 $v$ 的 `rs`. **这是 `GenFoldIf.FBA` 的推广**: `FBA` 只处理坐标是 `A` 的种类 (级层 $0$, 读回 `sum`); `KLv` 对坐标类型任意的种类, 级层任意.
> - **`LvFb T tp Λ = (κ : K T) → KLv T tp Λ κ ⊎ ⊤`.** 每个种类给一个级回灌或 "有损". 折叠 (构造文件 `KindLvRun`, 由 `GenFoldRun` 改写) 在第 0 层目标下对旧种类 `inj₁ κ` 的闭包结点: `inj₁ L` 时按 $\kappa$ 的级回灌 ($v_0=\mathrm{rd}(\mathrm{top}_\kappa w,\ \text{级层的累计输出})$, $w_{n+1}=\mathrm{rs}\,w_n\,v_n$, $v_{n+1}=\mathrm{rd}(\mathrm{top}_\kappa w_{n+1},\ \Delta_n)$, $\Delta_n$ 是分支在世界 $w_{n+1}$ 里折到级层 $\ell$ 的输出); `inj₂ tt` 时有损 (当前世界的分支, 重复 $\omega$ 次).
> - **坍缩的类型 `CollLvTy` (§4)**: 对一切带 `GenK`, `LgDn`, 层 $\Lambda$ (第 1 层是它的字面第一位置) 与 `LvFb` 的 $T$, 给出 `A` 的元素与它的合法.
>
> ## 塔的形状 (构造文件写成定义, 这里只说形状)
>
> 种类结构族 $C:\mathbb N\to$ `KS` 与级 $Y_s$ **互递归** (同一个 `mutual` 块, 对 $s$ 递归): $C_0=S_0$, $C_{s+1}=\mathrm{step}(\mathrm{Lev}\,Y_s)$; $U=\mathrm{sup}\ \mathbb N\ C$; $Y_0=\iota_0\,1$, $Y_{s+1}=\mathrm{hs}\,Y_s\boxplus\iota_{s+1}(\mathrm{ev}\,Y_s)$, 其中 $\mathrm{ev}\,Y_s$ 是第 $Y_s$ 级之上的求值 (`NewTwrEv.evN`, 值在 `HB (step (Lev Y_s)) = HB (C_{s+1})`). 层号对角 $\mathrm{B}^\Lambda_s=\mathrm{hs}\,Y_s$ 就是**第 $s+1$ 站的级本身** (不是另一个类型里的拷贝): $\mathrm{B}^\Lambda_{s+1}=\mathrm{B}^\Lambda_s\boxplus\iota_{s+1}(\mathrm{hs}(\mathrm{ev}\,Y_s))$ (定义相等). 最终层 $\Lambda=\mathrm{up}(\mathrm{hl}\,\mathrm{B}^\Lambda)$. 第 $s+1$ 个分量的头种类 `(suc s , inj₂ tt)` 的坐标是 `HB (Lev Y_s)`, 级层是 $\mathrm{hs}(\mathrm{up}\,Y_s)=\mathrm{up}(\mathrm{B}^\Lambda_s)$, 是 $\Lambda$ 的字面第一位置 (`hlim s hself`, 对一切世界).
>
> 与 [NewTwr](NewTwr.lagda.md) 的差 (类型事实): 那里种类以**另一站的类型** `HB (Kc s)` 的高度为下标, 最终层在 `HB (step KΛc)`; 读回分量的级层 `up (ιΛ s c)` 不是对角的第一位置 (`NegNewTwrShape.tw-not-below`), `Lev (up (ιΛ s c))` 与 `Lev c` 不定义相等. 这里种类的下标就是 $U$ 自己的高度 (对角的部分和), 级层与级读回的类型逐字对上.
>
> ## 律的定义域 (逐条)
>
> 律里出现的每一对下标都带字面公共上界, 或者根本不比较两个下标:
>
> - `Emb`: 每条律只出现一个种类, 一个世界 (`bd→`, `bd←`, `lgE→`), 或同一个种类在同一个世界里的一对坐标 (`pr→`, 前提就是这一对的第一位置, 公共上界是后一个). 不比较两个种类.
> - `KLv.ℓ⊲`: 一对 $(\ell, \Lambda)$, 公共上界 $\Lambda$ 本身 (对一切世界).
> - `KLv.rd-fst`: 一对 $(b, \mathrm{rd}\,b\,x)$, 公共上界是后者 (`Pr` 在给定世界里).
> - `KLv.rs≤`: 前提 `Pr T κ w (top κ w) v` 是一对 $(\mathrm{top}_\kappa w, v)$ 的字面第一位置 (公共上界 $v$); 结论是两个世界 $w \le \mathrm{rs}\,w\,v$. `rsLg`, `rd-lg`: 一个值. `rs-top`: 一个世界里一个种类的顶坐标 (`≡` 只在一个种类的坐标类型里).
> - 没有 "升一份留别份" (`NegGenFoldUpd.upd₁-sep`, `NegNewTwrFeed.updΛ⁺-sep`): `rs` 只说升后的世界更大且 $\kappa$ 的顶是 $v$, 不说别的种类不动. 构造文件在可判定下标 ($\mathbb N$ 分量, `step` 的第二分量) 上逐字写出 `rs`, 不用升界算子 (`RaiseIf`).
> - 折叠里的比较: 只有 `cmpB` (公共上界是最终层 $\Lambda$, 同 `GenFoldRun.rkT`).
>
> **`no-retract` 与壁垒 (检查).** $U$ 的种类的坐标是 `HB (Lev y)` ($y$ 是 $U$ 的高度的第一位置), 不是 `HB U` 本身; 最终层在 `HB (step U)`, 没有种类以 `HB (step U)` 为坐标. 接口不要求任何下标类型上的三歧或判定. [判断] 不触壁垒; 否定一路若找到反例, 以它为准.
>
> **接口不管什么 (盲).** `KLv` 被 "读回恒取起点" 满足 (`rd lW b x = b`, `rd-fst` 用自反); `rs` 若不改世界, 则 `rs-top` 一般不成立: `rs-top` 是唯一说 "升界被看见" 的律 (同 `FBA.tp-rs`), 但折叠的定义不用它 (折叠每格从当前世界的顶读起). `LvFb` 被 "一切种类有损" 满足 (`λ _ → inj₂ tt`). 所以接口不决定值; "按级回灌进了闭项" 是构造文件对具体实例的形状定理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KindLvIf where

open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.CumReadCF using (A; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (DK; TopG; top; GenK; tpK; LgDn; FbLg)
```

## §1 嵌入: 一个种类结构的种类搬进另一个

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
    lgE→  : ∀ {κ e} → LgE S (j κ) e → LgE S′ κ (cv e)
open Emb public
```

## §2 级层的数据与第 $c$ 级的高度

```agda
-- 级 c 的级层
lyL : ∀ {T : KS} → HB T → HB (step T)
lyL c = hs (up c)

-- 读回: 起点 + 级层数据 → 第 c 级的高度
RdLTy : KS → Set
RdLTy T = (c : HB T) → ∀ {W} → LgW (step T) W → HB (Lev c) → DK T (lyL c) W → HB (Lev c)

-- 写入: 第 c 级的高度 → 级层数据 (对一切世界)
WrLTy : KS → Set
WrLTy T = (c : HB T) → ∀ {W} → HB (Lev c) → DK T (lyL c) W
```

## §3 每个种类的级回灌

```agda
record KLv (T : KS) (tp : TopG T) (Λ : HB (step T)) (κ : K T) : Set where
  field
    ℓ      : HB (step T)
    ℓ⊲     : ∀ {w} → ℓ ⊲[ w ] Λ
    rd     : ∀ {W} → LgW (step T) W → E T κ → DK T ℓ W → E T κ
    rd-fst : ∀ {W} (lW : LgW (step T) W) b x → Pr T κ (proj₁ W) b (rd lW b x)
    rd-lg  : ∀ {W} (lW : LgW (step T) W) b x → LgE T κ b → LgE T κ (rd lW b x)
    rs     : Wd T → E T κ → Wd T
    rs≤    : ∀ {w v} → Pr T κ w (top tp κ w) v → _≤w_ T w (rs w v)
    rsLg   : ∀ {w v} → LgW T w → LgE T κ v → LgW T (rs w v)
    rs-top : ∀ {w v} → top tp κ (rs w v) ≡ v
open KLv public

LvFb : (T : KS) → TopG T → HB (step T) → Set
LvFb T tp Λ = (κ : K T) → KLv T tp Λ κ ⊎ ⊤
```

## §4 坍缩的类型

```agda
CollLvTy : Set₁
CollLvTy = ∀ {T : KS} (G : GenK T) → LgDn T → (Λ : HB (step T)) → LgB Λ →
           (∀ {w} → hs hz ⊲[ w ] Λ) → LvFb T (tpK G) Λ → Σ A Lg
```

## §5 只增: 坍缩的类型带 `FbLg`

```agda
CollLvFbTy : Set₁
CollLvFbTy = ∀ {T : KS} (G : GenK T) → LgDn T → FbLg G → (Λ : HB (step T)) → LgB Λ →
             (∀ {w} → hs hz ⊲[ w ] Λ) → LvFb T (tpK G) Λ → Σ A Lg
```

定义域: 同 §4, 不含律.
