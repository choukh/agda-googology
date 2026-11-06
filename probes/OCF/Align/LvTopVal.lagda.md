# 整座塔加对角 (三): 值的结论, 接口的盲

> 不含记号. 入口 [LvTop](LvTop.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 交付的 (b) 部分. 只有输入一侧的定理与条件定理; **没有无条件的值定理, 没有序数值验收.**
>
> - **[定理] 输入一侧 (对任一 `FoldAt` 与读法)**: 界逐站是第一位置 (`Tower.B-fst`, 在 [LvTopTower](LvTopTower.lagda.md)); 对角严格高于每个部分和 `cum-strict : cum k ⊏ Λ∞`; 加极限站不降 `lim-fst : Λ∞ ⊑ Λ∞ω`.
> - **[条件定理] 值一侧**: 前提 `FstMono T⁺` / `FstMono< T⁺` ([TpMonoIf](TpMonoIf.lagda.md); `T⁺` 对一切世界的字面第一位置单调 / 严格单调, 未证也未否定, 同 `LvRdVal`). 则每个部分和的闭项在对角之下 (`val-cum`, 严格 `val-cum<`), 对角在加极限站的闭项之下 (`val-lim`).
> - **[定理] 截断版的站**: 第 $0$ 站的输出就是 `LvRdFold.Hn 0` (`tr-H0`, 计算); 各站的界是 `fin s` (`LvTopInst.B-fin`).
> - **[定义 + 判断] 层号的类型** (§4): 塔的层号 `Tower.B s` 是 `HB S₀` 的树; `Lev t` 的级数由 $t$ 的树形给出 (`hs` ↦ `step`, `hl` ↦ `sup ℕ`, `hΩ` ↦ `sup A`), 所以塔的各级都是 `Kt 1 = Lev (Ωtop S₀) = sup (HB S₀) (Lev ∘ up)` (`Kt1`, 即 `AdmWIf.lev-Ωtop`) 的分量的形状. 层号逐站换类型的塔 `Kt (s+1) = Lev (Ωtop (Kt s))`, 极限 `KΛ = sup ℕ Kt` 是对 "x ↦ Ω_x 的第一个不动点" 的树侧写法 (读法是判断, 见入口).
> - **[定理, 盲] 接口不决定值**: `foldTriv : FoldAll` (读回与输出恒为 $0$) 是接口的实例; 用它的全塔各站输出都是 $0$ (`triv-Hs`). 所以 "全塔版本的读法" 是对实际给出的 `FoldAt` 的判断, 不是接口的推论.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvTopVal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; asuc)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (Ht)
open import OCF.Align.TpMonoIf using (_⊑_; _⊏_; FstMono; FstMono<; plim; T⁺)
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.LvRdFold using (Hn)
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.LvRdWk using (σ₀; lσ₀)
open import OCF.Align.LvTopIf
open import OCF.Align.LvTopTower
open import OCF.Align.LvTopInst using (module Tr; module FullΛ)
```

## §1 输入一侧与条件的值 (对任一 `FoldAt`)

```agda
module ValT (CovS : HB S₀ → Set) (F : FoldAt CovS)
            (σ-of : Ht → HB S₀) (lσ : ∀ h → LgB (σ-of h)) (b₀ : HB S₀) (lb₀ : LgB b₀)
            (cov0 : CovS b₀) (covS : ∀ t h → CovS t → CovS (t ⊞ σ-of h)) where
  open Tower CovS F σ-of lσ b₀ lb₀ cov0 covS

  cum-strict : ∀ k → cum k ⊏ Λ∞
  cum-strict k = plim (suc k) (⊞-fst (cum k) (Hs (suc k)))

  val-cum : FstMono T⁺ → ∀ k → T⁺ (cum k) (lcum k) ≤ TΛ∞
  val-cum fm k = fm (cum k) (lcum k) Λ∞ lΛ∞ (hlim (suc k) (⊞-fst (cum k) (Hs (suc k))))

  val-cum< : FstMono< T⁺ → ∀ k → asuc (T⁺ (cum k) (lcum k)) ≤ TΛ∞
  val-cum< fm k = fm (cum k) (lcum k) Λ∞ lΛ∞ (cum-strict k)

  module ValL (CovL : HB S₀ → Set) (FL : FoldAt CovL) (covL : CovL Bω) where
    open Lim CovL FL covL

    lim-fst : Λ∞ ⊑ Λ∞ω
    lim-fst = ⊞-fst Λ∞ Hω

    val-lim : FstMono T⁺ → TΛ∞ ≤ TΛ∞ω
    val-lim fm = fm Λ∞ lΛ∞ Λ∞ω lΛ∞ω lim-fst
```

## §2 截断版的第 0 站

```agda
tr-H0 : Tr.Hs zero ≡ Hn zero
tr-H0 = refl
```

## §3 盲: 接口不决定值

```agda
foldTriv : FoldAll
foldTriv = record
  { rt = λ lb c cv w lw → hz ; lrt = λ lb c cv w lw → tt
  ; H = λ lb c cv w lw → hz ; lgH = λ lb c cv w lw → tt }

triv-Hs : ∀ b₀ (lb₀ : LgB b₀) s → FullΛ.Hs foldTriv b₀ lb₀ s ≡ hz
triv-Hs b₀ lb₀ s = refl
```

## §4 层号的类型

塔 (`LvTopTower.Tower`) 的层号都在 `HB S₀` 里, 码也是 `HB S₀` 的界之下的路径. 下面的 `Kt` 是层号逐站换类型的写法: 第 $s+1$ 站的层号取第 $s$ 站的一切高度 (`Lev (Ωtop K)` 是以 `K` 的高度为下标的各级之并). 只是定义, 不进闭项; 读法 (判断) 见入口.

```agda
Kt : ℕ → KS
Kt zero = S₀
Kt (suc s) = Lev (Ωtop (Kt s))

KΛ : KS
KΛ = sup ℕ Kt

-- 第 1 站: 以 HB S₀ 的一切高度为层号的各级之并 (AdmWIf.lev-Ωtop 的形状)
Kt1 : Kt 1 ≡ sup (HB S₀) (λ c → Lev (up c))
Kt1 = refl
```
