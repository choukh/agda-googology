# LHRec: 接口 (第 $k$ 层世界的移动)

> 不含记号. 入口 [LHRec](LHRec.lagda.md). 构造一路 LHRec, 否定一路 NegLHRec 共用. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 只导入 [CRwBase](CRwBase.lagda.md), [LHRecTy](LHRecTy.lagda.md).
>
> **接口定稿 2026-11-06 08:06 (首次编译通过).** 定稿后只增不改. 接口文件与它导入的 [LHRecTy](LHRecTy.lagda.md) 一起定稿.
>
> **设计 (构造一路的计划, 不是接口的律).** 底对层号 `LH` 递归: 层号 `lΩ k g` 的种类结构是 $\sup$ (指标分量 `step (Lv k)`, 第 $c$ 个分量 `Lv (g c)`), $c$ 过第 $k$ 层的值 `HB (Lv k)` (RecB 卡点 1). 第 $c$ 个分量的序号由**世界的一层**界住, 这一层是 `Wd (step (Lv k))` $=$ (第 $k$ 层的世界 $w$, 第 $k$ 层的界 $B$), 证据是 $c\lhd_w B$ (RecB 卡点 2; 低层世界 $w$ 随层带着, 由 `NegRecBPre.wdep-low`). 指标分量的种类 ($\Omega_{k+1}$, 坐标是第 $k$ 层的值) 移动这一层世界: 进入坐标 $e$ 前先回灌 `sh k W e` (RecB 卡点 3), 再要可入 `Adm k W e`, 进入后世界换成 `nxt k W e a`. 每个底的指标分量是 `IxL.ixL` (RecB 卡点 4, 由 `NegRecBInst.ΦX↓M-fails`).
>
> **律.** 与 `CRwIf` 同形, 把可数树 `Cd` 换成第 $k$ 层的世界 `Wd (step (Lv k))`, 把 $B\lhd B'$ 换成那一层的世界序 `_≤w_ (step (Lv k))` (即 $w\le w'$ 且 $B\lhd_{w'}B'$: 字面公共上界 $B'$, 低层世界不缩小):
>
> - `adm-sh`: 回灌的坐标可入 (世界合法时; 对一切坐标, 不要坐标合法);
> - `nx-up`: 进入不缩小世界, 带字面证据 $W\le$ `nxt k W e a`;
> - `lg-nx`: 进入保世界合法;
> - `adm↓`: 可入随世界变小, 进入后的世界有序; 成对的两个世界都带字面证据 $W\le W'$.
> - 初始世界 `W₀ k`, 带字面证据 $1\lhd$ (`W₀ k` 的界) 与合法.
>
> **没有对裸下标的比较律.** 律里出现的世界对只有 $(W, W')$ 与 $(W, \mathrm{nxt}\,k\,W\,e\,a)$, 都带字面 `≤w` 证据; 坐标对不出现.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LHRecIf where

open import Data.Unit using (tt)
open import Data.Sum using (inj₂)
open import Data.Product using (Σ)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy public

-- 第 k 层的一层世界: (第 k 层的世界, 第 k 层的界)
WL : LH → Set
WL k = Wd (step (Lv k))

-- 世界序 (字面公共上界: 后一个世界的界), 合法
LeW : ∀ k → WL k → WL k → Set
LeW k = _≤w_ (step (Lv k))

LgWL : ∀ k → WL k → Set
LgWL k = LgW (step (Lv k))

record LHRecIf : Set₁ where
  field
    Adm    : ∀ k → WL k → HB (Lv k) → Set
    nxt    : ∀ k (W : WL k) e → Adm k W e → WL k
    sh     : ∀ k → WL k → HB (Lv k) → HB (Lv k)
    adm-sh : ∀ k {W} c → LgWL k W → Adm k W (sh k W c)
    nx-up  : ∀ k {W e} (a : Adm k W e) → LeW k W (nxt k W e a)
    lg-nx  : ∀ k {W e} (a : Adm k W e) → LgWL k W → LgWL k (nxt k W e a)
    adm↓   : ∀ k {W W′} → LeW k W W′ → ∀ {e} (a′ : Adm k W′ e) →
             Σ (Adm k W e) (λ a → LeW k (nxt k W e a) (nxt k W′ e a′))
    W₀     : ∀ k → WL k
    o₀     : ∀ k → Bd (step (Lv k)) (inj₂ tt) (hs hz) (W₀ k)   -- 字面证据: 1 ⊲ (W₀ k 的界)
    lW₀    : ∀ k → LgWL k (W₀ k)
```
