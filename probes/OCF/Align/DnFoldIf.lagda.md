# 有内容的下降: 接口 (经求值的下降, 有损的下降, 层号在 `Ht` 的层, 忠实)

> **接口定稿 2026-11-05 16:13 (首次编译通过).** 定稿之后只增不改; 若必须改, 在这里写变更记录. 变更记录: (无).
>
> 不含记号. 本路 (前缀 `DnFold`) 是 [KcFold](KcFold.lagda.md) 的续作的**构造**一路: 给出有内容的下降 `DnK (Lev (B s))`, 代入 `KcFoldTower.KD`, 让读回进入闭项. 否定一路 (前缀 `NegDnFold`) 导入本文件, 不另造接口. 本篇只放类型, 记录与只由构造子组成的定义, 不放证明. 导入 [KcFoldIf](KcFoldIf.lagda.md) (不改它), [KcFoldTower](KcFoldTower.lagda.md) (只用 `KD`, `Shape.X` 写忠实的类型), [LvKtInst](LvKtInst.lagda.md) (只用截断版 `TrK.Hs` 写 "与截断版不同" 的类型). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> **对象.**
>
> - **层号在 `Ht` 的层 `LvH a c`** (§1): 就是 `KcFoldIf.LvW` 取 `K = S₁` (外层世界 $a$ 在 `Wd₂ = A × H₀`): `LvOmLev.LvM.Lv` 的推广, 多一行 κH: $\Omega$-结点 `hΩ κH g` 只取 $y\lhd_{[a_A]}a_H$ 的分支. 读回层 `LyH c` (`LvOmLev.Ly` 的推广, 逐构造子, κH 原样).
> - **(D1) 经求值的下降, 层在 `Ht`** (§2, 第 1 站的形状): 记录 `DnEv S`: 数据树的层 $L$ (合法, 第 1 层是它在一切世界里的第一位置), 求值的世界 $W$ (合法, 第 2 层在 $W$ 里是 $L$ 的第一位置), 翻译 `tr : HB S → D L W`. 由它得下降: 翻译, 用两种种类折叠的 `Run` (层 $L$) 求到第 2 层, 经第 1 级读回 (`LvRdPkg.RdF 1`) 落到 `Ht` (照 `LvRd.dω`, `LvOmClosed.Dc`; 这一步是定义, 放在构造文件). **数据树没有合法性**, 所以翻译可以是任何函数; 下降的合法由读回的形状给出.
> - **(D1′) 经求值的下降, 一般的求值系统** (§3, 第 2 站起的形状): 记录 `EvSys` (层的类型, 世界, 数据树, 可求值的条件, 求值到 `Ht` 与它的合法) 与 `DnEvS E S`. 数据树的层推广到 `HB (step K)` 的情形写成 `EvSysK K` (层的类型是 `KcFoldIf.LayK K`). 本篇只有类型.
> - **(D2) 有损的下降** (§4): 记录 `DnSq T`: `HB (step T) → Ht` 保合法, 新种类的 $\Omega$-结点只沿一列坐标 `cs n` 读 (`sq-new`: 输出只经 `n ↦ sq (g (cs n))` 依赖分支). **丢了什么**: 新种类坐标里不在这一列上的一切高度 (坐标取遍 `HB T`, 读成一个 ℕ-极限或其它只看 `cs` 的组合).
> - **忠实** (§5): `FaithRd T d`: 下降 $d$ 区分读回 `rdTop T = hs (Ωtop T)` (新种类结点, 分支原样嵌入) 与把分支全换成 $0$ 的截断 `rdCut T`. 塔上 `FaithTower dn dnL`: 第 $s+1$ 站的下降在该站的读回上忠实 (读回所在的级是 `step (Lev (X s))`, 定义相等); `Faith0`: 第 0 站. `DiffTkc`: 某站的回灌输出不等于截断版 (`LvKtInst.TrK.Hs`) 那一站的输出.
> - **桥与可入的类型** (§6): `RestrK`: 无世界的层到带世界的层的函数 (`ForgetK` 的反方向, 不要求保合法); `ExactAdm K a`: 对裸坐标判定在外层世界 $a$ 里可入.
>
> **律的定义域 (逐条).** 律里出现的每一对下标都带字面公共上界:
>
> - `DnEv`: `o1` 只有一个层 $L$ (一切世界, 第一位置, 不比较两个下标); `ev2` 只在一个世界 $W$ 里. `tr` 是函数, 不是律. 没有更新律.
> - `EvSys.lgEv`: 单个数据树的输出合法; 不比较两个下标.
> - `DnSq.sq-new`: 一个结点, 一列坐标 `cs n`; 不比较两个坐标, 不判定.
> - `FaithRd`, `FaithTower`, `DiffTkc`: 比较的是两个**输出** (`Ht` 的元素) 的相等, 不是下标的可入或序; 不出现世界.
> - `RestrK` 是函数类型, 不是律. `ExactAdm` 是**裸判定** (没有公共上界), 写出来只为让否定一路对准: 带公共上界的版本是 `KcFoldIf.BDecK` (已有实例 `KcFoldBdec.bdecLv`).
>
> **`no-retract` 与壁垒 (检查).** `LvH a c` 的种类以 `Σ x. Bd S₁ κ x a` 为下标, 坐标是 `A`, `H₀` 或更低的 `HB (LvH a c′)`, 没有种类以 `HB (LvH a c)` 自身为坐标. `DnEv` 不要求任何判定. [判断] 不触壁垒; 否定一路若找到反例, 以它为准.
>
> **接口不管什么 (盲).** `DnEv` 的翻译取常数 `n0` 也是实例, 下降合法; `DnSq` 的 `sq` 取常数也满足 `sq-new` (取 `comb` 为常数). 所以接口不决定值; 忠实 (`FaithRd`) 是另加的形状要求, 它也不说大小 (手册 §3.3).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DnFoldIf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.HtTowerFTree using (S₁; H₀; Ht; Wd₂; LgW₂; D)
open import OCF.Align.LvKtIf
open import OCF.Align.LvKtInst using (module TrK)
open import OCF.Align.KcFoldIf
open import OCF.Align.KcFoldTower using (module KD; module Shape)
```

## §1 层号在 `Ht` 的层与读回层

```agda
LvH : Wd₂ → Ht → KS
LvH a c = LvW {S₁} a c

LyH : Ht → Ht
LyH hz = hs hz
LyH (hs c) = hs (LyH c)
LyH (hl f) = hl (λ n → LyH (f n))
LyH (hΩ κ g) = hΩ κ (λ x → LyH (g x))
```

## §2 (D1) 经求值的下降, 层在 `Ht`

```agda
record DnEv (S : KS) : Set where
  field
    Lw  : Ht
    lLw : LgB Lw
    o1  : ∀ {w} → hs hz ⊲[ w ] Lw
    Wv  : Wd₂
    lWv : LgW₂ Wv
    ev2 : hs (hs hz) ⊲[ Wv ] Lw
    tr  : HB S → D Lw Wv

DnEvTower : Set
DnEvTower = ∀ s (b : HB (Kc s)) → LgB b → DnEv (Lev b)
```

## §3 (D1′) 一般的求值系统

```agda
record EvSys : Set₁ where
  field
    Lay  : Set
    Wor  : Set
    LgWo : Wor → Set
    Dat  : Lay → Wor → Set
    Ok   : Lay → Wor → Set
    evH  : ∀ {L W} → Ok L W → LgWo W → Dat L W → Ht
    lgEv : ∀ {L W} (o : Ok L W) (lW : LgWo W) (X : Dat L W) → LgB (evH o lW X)

record DnEvS (E : EvSys) (S : KS) : Set where
  open EvSys E
  field
    Lw  : Lay
    Wv  : Wor
    ok  : Ok Lw Wv
    lWv : LgWo Wv
    tr  : HB S → Dat Lw Wv

-- 数据树的层推广到 HB (step K)
EvSysK : KS → Set₁
EvSysK K = Σ EvSys (λ E → EvSys.Lay E ≡ LayK K)
```

## §4 (D2) 有损的下降

```agda
record DnSq (T : KS) : Set where
  field
    sq     : HB (step T) → Ht
    lsq    : ∀ x → LgB x → LgB (sq x)
    cs     : ℕ → HB T
    comb   : (ℕ → Ht) → Ht
    sq-new : ∀ g → sq (hΩ (inj₂ tt) g) ≡ comb (λ n → sq (g (cs n)))
```

## §5 忠实

```agda
rdTop : (T : KS) → HB (step T)
rdTop T = hs (Ωtop T)

rdCut : (T : KS) → HB (step T)
rdCut T = hs (hΩ (inj₂ tt) (λ _ → hz))

FaithRd : (T : KS) → (HB (step T) → Ht) → Set
FaithRd T d = ¬ (d (rdTop T) ≡ d (rdCut T))

Faith0 : DnTower → Set
Faith0 dn = FaithRd S₀ (proj₁ (dn 0 (hs hz) tt))

FaithTower : DnTower → DnLim → Set
FaithTower dn dnL = ∀ s →
  FaithRd (Lev (Shape.X dn dnL s)) (proj₁ (dn (suc s) (KD.B dn dnL (suc s)) (KD.lB dn dnL (suc s))))

DiffTkc : DnTower → DnLim → Set
DiffTkc dn dnL = Σ ℕ (λ s → ¬ (KD.Hs dn dnL s ≡ TrK.Hs s))
```

## §6 桥与可入的类型

```agda
RestrK : KS → Set
RestrK K = ∀ (a : Wd K) → LgW K a → (c : HB K) → HB (Lev c) → HB (LvW a c)

ExactAdm : (K : KS) → Wd K → Set
ExactAdm K a = ∀ κ (x : E K κ) → Dec (Bd K κ x a)
```
