# 读回包 (七): 值的结论

> 不含记号. 入口 [LvRd](LvRd.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 交付的 (b) 部分. 闭项 `T∞ω1 = T⁺ (ΛF ⊞ Hω1)`, 对照 `T∞F = T⁺ ΛF` (只有有限级的对角).
>
> - **[定理] 输入一侧**: `lay-fst : ΛF ⊑ Λω1` (一切世界里的字面第一位置); `lay-strict : ΛF ⊏ Λω1` (严格: `Hω1` 最外是 ℕ-极限, 计算得出 `Hω1-hl`).
> - **[条件定理] 值一侧**: 前提是 [TpMonoIf](TpMonoIf.lagda.md) 的 `FstMono T⁺` / `FstMono< T⁺` (`T⁺` 对一切世界的字面第一位置单调 / 严格单调). 则 `T∞F ≤ T∞ω1` (`val-mono`), `asuc T∞F ≤ T∞ω1` (`val-strict`).
> - **前提的状态**: `FstMono T⁺` 与 `FstMono< T⁺` 未证也未被否定 (`TpMono` 判决 PARTIAL; `NegTpMono` 没有找到反例, 并给出满足同一组律的别的 `F`, 说明律的形状可满足). 对 `T⁺` 本身前提是否成立未知, 所以第二条只是条件定理. 没有与 `LvFbFold.T∞c`, `FamFoldAll.T∞` 的值比较 (输入之间没有字面第一位置的证据, 不在 `FstMono` 的定义域里), 没有对参照树的序数值验收.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvRdVal where

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; asuc)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (Ht)
open import OCF.Align.TpMonoIf using (_⊑_; _⊏_; FstMono; FstMono<; plim; T⁺)
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.LvRdFold using (ΛF; lΛF; Hω1; Λω1; lΛω1; T∞F; T∞ω1)

lay-fst : ΛF ⊑ Λω1
lay-fst = ⊞-fst ΛF Hω1

Hω1-hl : Σ (ℕ → Ht) (λ f → Hω1 ≡ hl f)
Hω1-hl = _ , refl

lay-strict : ΛF ⊏ Λω1
lay-strict = plim 0 (⊞-fst ΛF _)

val-mono : FstMono T⁺ → T∞F ≤ T∞ω1
val-mono fm = fm ΛF lΛF Λω1 lΛω1 lay-fst

val-strict : FstMono< T⁺ → asuc T∞F ≤ T∞ω1
val-strict fm = fm ΛF lΛF Λω1 lΛω1 lay-strict
```
