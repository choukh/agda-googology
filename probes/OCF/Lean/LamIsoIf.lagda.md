# LamIso: 接口 (忠实的同形 `Prt`, 含各站同形层的最高层, 按自己的级读回)

> **接口定稿 2026-11-05 22:58 (首次编译通过).** 定稿之后只增不改; 若必须改, 在这里写变更记录. 变更记录: 无.

> 不含记号. 构造一路前缀 `LamIso`, 否定一路前缀 `NegLamIso` 导入本文件, 不另造接口. 只放类型与记录, 不放证明. 只导入 [LeanTBase](LeanTBase.lagda.md), [LeanTLv](LeanTLv.lagda.md), [LeanTTree](LeanTTree.lagda.md), [LeanFbIf](LeanFbIf.lagda.md), [LeanFbSt](LeanFbSt.lagda.md), [LeanLvIf](LeanLvIf.lagda.md), 都不改. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> **问题** (作者 2026-11-05 选定, 原话 "②: 最高层 Λ 含与站层号同形的层"; 选项说明 "新最高层 Λ′ 含与各站层号同形的层 (先 n=3, 再一般 n)"). 在 `ΛF` 上第 $n\ge3$ 站的头没有自己的级层 (`NegLeanLvBlind.no-sim`). 本接口把 "改最高层" 拆成三样:
>
> - **`Prt T a x` (§1, 忠实的同形).** 层 $a$ : `HB (step T)` 与层号 $x$ 逐构造子对上, 同 `LeanLvIf.Sim⁺`; 差在 $\Omega$-极限: `lΩ k g` 对应的结点的种类**字面是**一个嵌入 `Em : Emb (FL k) (step T)` 的新种类的像 `j Em (inj₂ tt)`, 坐标映射**就是** `cv Em` (坐标类型 `HB (Lv k)` 是这个种类坐标的收缩, `cv-vc`). 所以常值坐标映射 (否定一路 `NegLamIsoPre.Col` 的一种类塌缩) 不满足 `Prt` (判断: `cv-vc` 要 `cv Em` 满射; 由否定一路写成定理). 极限位置的后继种类同 `Sim⁺`, 可选.
> - **`LamIso Λ` (§2, 含各站同形层的最高层).** 对每个 $n$ 一个层 `L n`, 对一切世界是 $\Lambda$ 的字面第一位置 (`L⊲`), 与第 $n$ 站的层号 `st n` 忠实同形 (`prt`); $\Lambda$ 合法.
> - **`OwnRd Λ n` (§3, 按自己的级读回).** 第 $n$ 站的头的读回 `LvRd SLs Λ (Lv (st n))` 与它的级层到 `st n` 的忠实同形. 目标就是 `Lv (st n)` (头 $n$ 的坐标的种类结构), 没有嵌入: "自己的级" 写进类型, 不是律.
>
> ## 律的定义域 (逐条)
>
> - `Prt`: 数据, 没有律. 不判定层号相等, 不比较两个层. 嵌入 `Em` 的律 (`bd→`, `bd←`, `pr→`, `cv-vc`) 的定义域见 `LeanLvIf` §1 (一个种类, 一个世界, 一对带第一位置证据的坐标).
> - `LamIso.L⊲`: 一个层 `L n` 与字面的 $\Lambda$ (公共上界就是 $\Lambda$), 对一切世界. `lΛ`: 一个层.
> - `OwnRd`: 继承 `LvRd.ℓ⊲` (一对 $(\ell,\Lambda)$, 公共上界字面的 $\Lambda$); `π` 是证据.
>
> 没有对两个下标的比较律, 没有 "留别份" 律, 不要求 `L n` 与 `L (n+1)` 之间的关系 (构造一路若有, 写成定理).
>
> **接口不管什么 (盲).** (1) `OwnRd` 不逼 `R` 的读回沿 `π` 读 (常数读回也满足, 同 `NegLeanLvBlind.simConst`); 是否沿同形读, 由构造一路对实例写形状定理. (2) `Prt` 不要求不同结点用不同的嵌入, 也不要求嵌入单射: 一切同级结点可以共用一个嵌入. (3) `LamIso` 不说 $\Lambda$ 与 `ΛF` 的关系, 也不说 `L n` 里出现哪些种类; 折叠里哪些种类回灌由计划决定. (4) 忠实只管 $\Omega$-结点的种类与坐标映射; 不管层的值 (两个忠实同形于 `st n` 的层值可以不同).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LamIsoIf where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₂)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanTTree
open import OCF.Lean.LeanFbIf
open import OCF.Lean.LeanFbSt using (SLs) renaming (st to stL)
open import OCF.Lean.LeanLvIf using (Emb; j; cv)
```

## §1 忠实的同形

```agda
module _ (T : KS) where
  data Prt : HB (step T) → LH → Set where
    pz : Prt hz lz
    ps : ∀ {a x} → Prt a x → Prt (hs a) (ls x)
    pl : ∀ {f g} → (∀ n → Prt (f n) (g n)) → (∀ n → Emb (Lv (ls (g n))) (Lv (ll g)) ⊎ ⊤) → Prt (hl f) (ll g)
    pΩ : ∀ {k g} (Em : Emb (FL k) (step T)) {h : E (step T) (j Em (inj₂ tt)) → HB (step T)} → (∀ e → Prt (h e) (g (cv Em {inj₂ tt} e))) →
         (∀ e → Emb (Lv (ls (g (cv Em {inj₂ tt} e)))) (Lv (lΩ k g)) ⊎ ⊤) → Prt (hΩ (j Em (inj₂ tt)) h) (lΩ k g)
```

## §2 含各站同形层的最高层

```agda
record LamIso (Λ : HB (step SLs)) : Set₁ where
  field
    lΛ  : LgB Λ
    L   : ℕ → HB (step SLs)
    L⊲  : ∀ n {w} → L n ⊲[ w ] Λ
    prt : ∀ n → Prt SLs (L n) (stL n)
open LamIso public
```

## §3 按自己的级读回

```agda
record OwnRd (Λ : HB (step SLs)) (n : ℕ) : Set₁ where
  field
    R : LvRd SLs Λ (Lv (stL n))
    π : Prt SLs (LvRd.ℓ R) (stL n)
open OwnRd public
```
