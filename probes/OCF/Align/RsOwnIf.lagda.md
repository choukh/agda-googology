# 积世界上的升界: 接口 (几种形状)

> **接口定稿 2026-11-05 19:21 (首次编译通过).** 定稿之后只增不改; 若必须改, 在这里写变更记录. 变更记录: (无).

> 不含记号. 目标 (作者原话): "写出 ψ₀Λ 的候选闭项"; 本轮作者选定 (原话): "挑战 '只剩一种升界'". 本路 (前缀 `RsOwn`) 是构造一路; 否定一路 (前缀 `NegRsOwn`) 导入本文件, 不另造接口. 本篇只放类型, 记录与只由构造子组成的定义, 不放证明. 导入 [HtTowerTy](HtTowerTy.lagda.md) (`KS`, `sup`), [GenFoldIf](GenFoldIf.lagda.md) (`TopG`), 都不改. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> **问题.** `NegKindLv` 的判断 (b): 以含函数的高度为下标的并里, 升界只剩 "精确置自己的分量, 别处只增不减且按分量不同" 一种未被否定的形状. 本接口把 "升界" 拆成几种形状, 每种写成记录, 让构造与否定对着同一组记录.
>
> ## 对象
>
> - **升界的核 `RsK T tp κ` (§1).** 就是 `KindLvIf.KLv` 的升界三律 (`rs≤`, `rsLg`, `rs-top`) 单独成记录. `rs≤` 的前提是 "旧顶是 $v$ 的第一位置" (公共上界 $v$); 世界变大是对**一切**分量说的, 但只在这个前提下.
> - **积世界 `sup I F` 上的形状 (§2, 模块 `PW`).** 自己的种类是 $(i_0,\kappa_0)$.
>   - `ViaΦ`: 升界逐分量写成 $\Phi\,i\,(w\,i)\,v$ (分量 $i$ 的新世界只看分量 $i$ 的旧世界与 $v$; $\Phi$ 可以依赖 $i$, 也可以依赖自己 $i_0$).
>   - `Keep` ("留"): 下标不同的分量不动.
>   - `AllFam` ("同一个 $R$ 一起升" 的推广): 一族自己的种类 $(ix\,j,\kappa_j)$ 共用**一个**不依赖 $j$ 的 $\Psi$ (可以依赖分量 $i$), 回灌值经 `inV j` 进同一个值类型 $V$.
>   - `OwnFam` ("精确置自己, 别处只增, 依赖分量"): 一族 `RsK`, 每个带 `ViaΦ`, $\Phi$ 可依赖 $j$. 按否定一路的建议 (`NegRsOwnPre.no-ownJoin`, `ownB₁-sep`), "别处只增" 只在 `rs≤` 的前提下要, 别处**不要求**含 $v$.
> - **带字面公共上界的升界 `RsBd` (§3).** 世界带一个上界数据 `Up w` (如 "一切底拷贝都在 $\Lambda$ 之下"), $v$ 带它在上界之下的证据 `U w u v`. 世界变大**无前提**; `rs-top` 只在旧顶 $\lhd v$ 时要; 升后仍有上界.
> - **世界带不变式 `subW T P`, `RsInv` (§4).** `subW T P`: 种类, 坐标, 界, 第一位置, 比较都沿用 $T$, 世界是 $\Sigma\,(w : \mathrm{Wd}\,T)\,(P\,w)$ (世界带一份证据). `RsInv`: 升界读证据, 保证据, `rs≤` 的前提多一份 $P\,w$. 例 (构造文件): $P\,w$ = "一切底拷贝的界都等于同一个 $a$", 证据里的 $a$ 就是一切底拷贝的字面公共上界. `topSub`: 顶坐标沿用.
>
> ## 律的定义域 (逐条)
>
> - `RsK.rs≤`: 前提是一对 $(\mathrm{top}_\kappa w, v)$ 的第一位置, 公共上界 $v$; 结论是两个世界 $w\le \mathrm{rs}\,w\,v$. `rsLg`: 一个值. `rs-top`: 一个种类的坐标类型里的 `≡`.
> - `ViaΦ.rs≡`: 同一个分量 $i$ 的两个世界 (类型相同) 的 `≡`; 不比较两个下标.
> - `Keep.keep`: 前提 `¬ (i ≡ i₀)` 是两个下标的不等. **这是裸下标上的律** (手册 §3.1): 已知它与 "升" 合起来推出分离子 (`NegKindLvUpd.updH₁-sep`); 记录在此只为让否定一路有名字可引, 构造一路不用它.
> - `AllFam.rs≡`: 同 `ViaΦ`; 不比较两个 $j$.
> - `RsBd`: `rsᵇ≤` 无前提 (公共上界由 `Up`, `U` 的证据给出); `rsᵇ-top` 的前提同 `rs≤`.
> - `RsInv`: 前提多一份 $P\,w$, 它是**一个**世界上的证据, 不比较下标. 在构造文件里 $P$ 的证据是 "每份底拷贝 $\equiv a$", 即一切底拷贝的字面公共上界 $a$.
>
> **`no-retract` 与壁垒 (检查).** 接口不要求任何下标类型上的三歧或判定 (`Keep` 的不等是前提, 不是判定). `subW` 不加种类, 不改坐标. [判断] 不触壁垒; 否定一路若找到反例, 以它为准.
>
> **接口不管什么 (盲).** 不说升后世界的大小 (只给下界与 `rs-top`); `RsInv` 被 "$P$ 恒假" 空真地满足, 所以用 `RsInv` 时要给 $P$ 的实例 (构造文件给基世界的证据); `AllFam` 不说 $V$ 是什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RsOwnIf where

open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (TopG; top; topBd)
```

## §1 升界的核

```agda
record RsK (T : KS) (tp : TopG T) (κ : K T) : Set where
  field
    rs     : Wd T → E T κ → Wd T
    rs≤    : ∀ {w v} → Pr T κ w (top tp κ w) v → _≤w_ T w (rs w v)
    rsLg   : ∀ {w v} → LgW T w → LgE T κ v → LgW T (rs w v)
    rs-top : ∀ {w v} → top tp κ (rs w v) ≡ v
open RsK public
```

## §2 积世界上的形状

```agda
module PW (I : Set) (F : I → KS) where
  private
    T = sup I F

  record ViaΦ (tp : TopG T) (i₀ : I) (κ₀ : K (F i₀)) (R : RsK T tp (i₀ , κ₀)) : Set where
    field
      Φ   : (i : I) → Wd (F i) → E (F i₀) κ₀ → Wd (F i)
      rs≡ : ∀ w v i → rs R w v i ≡ Φ i (w i) v

  record Keep (tp : TopG T) (i₀ : I) (κ₀ : K (F i₀)) (R : RsK T tp (i₀ , κ₀)) : Set where
    field
      keep : ∀ w v i → ¬ (i ≡ i₀) → rs R w v i ≡ w i

  -- 一族自己的种类共用一个不依赖 j 的 Ψ ("同一个 R 一起升" 的推广, Ψ 可依赖分量)
  record AllFam (tp : TopG T) (J : Set) (ix : J → I) (κJ : (j : J) → K (F (ix j))) : Set₁ where
    field
      V   : Set
      inV : ∀ j → E (F (ix j)) (κJ j) → V
      Ψ   : (i : I) → Wd (F i) → V → Wd (F i)
      R   : ∀ j → RsK T tp (ix j , κJ j)
      rs≡ : ∀ j w v i → rs (R j) w v i ≡ Ψ i (w i) (inV j v)

  -- 精确置自己, 别处只增 (在 rs≤ 的前提下), Φ 依赖分量与自己
  record OwnFam (tp : TopG T) (J : Set) (ix : J → I) (κJ : (j : J) → K (F (ix j))) : Set where
    field
      R  : ∀ j → RsK T tp (ix j , κJ j)
      vi : ∀ j → ViaΦ tp (ix j) (κJ j) (R j)
```

## §3 带字面公共上界的升界

```agda
record RsBd (T : KS) (tp : TopG T) (κ : K T)
            (Up : Wd T → Set) (U : (w : Wd T) → Up w → E T κ → Set) : Set where
  field
    rsᵇ     : (w : Wd T) (u : Up w) (v : E T κ) → U w u v → Wd T
    rsᵇ≤    : ∀ {w u v} (q : U w u v) → _≤w_ T w (rsᵇ w u v q)
    rsᵇLg   : ∀ {w u v} (q : U w u v) → LgW T w → LgE T κ v → LgW T (rsᵇ w u v q)
    rsᵇ-top : ∀ {w u v} (q : U w u v) → Pr T κ w (top tp κ w) v → top tp κ (rsᵇ w u v q) ≡ v
    rsᵇ-up  : ∀ {w u v} (q : U w u v) → Up (rsᵇ w u v q)
open RsBd public
```

## §4 世界带不变式

```agda
subW : (T : KS) → (Wd T → Set) → KS
subW T P = record
  { K = K T ; E = E T ; Wd = Σ (Wd T) P
  ; LgW = λ w → LgW T (proj₁ w)
  ; _≤w_ = λ u v → _≤w_ T (proj₁ u) (proj₁ v)
  ; ≤w-rf = ≤w-rf T ; ≤w-tr = ≤w-tr T
  ; Bd = λ κ c w → Bd T κ c (proj₁ w)
  ; Pr = λ κ w c c′ → Pr T κ (proj₁ w) c c′
  ; Bd↑ = Bd↑ T ; cmpK = cmpK T ; LgE = LgE T ; lgBd = lgBd T
  ; bot = bot T ; botBd = λ κ w → botBd T κ (proj₁ w) }

topSub : ∀ {T : KS} {P : Wd T → Set} → TopG T → TopG (subW T P)
topSub tp = record { top = λ κ w → top tp κ (proj₁ w) ; topBd = λ κ w → topBd tp κ (proj₁ w) }

record RsInv (T : KS) (P : Wd T → Set) (tp : TopG T) (κ : K T) : Set where
  field
    rsᴵ     : (w : Wd T) → P w → E T κ → Wd T
    rsᴵ-P   : ∀ {w} (p : P w) v → P (rsᴵ w p v)
    rsᴵ≤    : ∀ {w v} (p : P w) → Pr T κ w (top tp κ w) v → _≤w_ T w (rsᴵ w p v)
    rsᴵLg   : ∀ {w v} (p : P w) → LgW T w → LgE T κ v → LgW T (rsᴵ w p v)
    rsᴵ-top : ∀ {w v} (p : P w) → top tp κ (rsᴵ w p v) ≡ v
open RsInv public
```
