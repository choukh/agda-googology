# 精确标签下路径证据域在 tw 1 上为空

> 验收文件 (读记号)。编译否定: 对任意槽位标签, Ω 形状层号经指定孩子 (`inc`) 折到目标时, 只要某个孩子里有一个带标签的槽位, 其标签低于目标标签, 就没有框架 (`no-frame-Ωinc`); 取 `Lbl` 时 `tw 1` 没有 `IndexTree` (`no-index-tree-tw1ˣ`), 失败处只用到不含 Ω 形状的层号 `one`, `zero` 的标签, 与 Ω 形状层号的标签无关。
> 原因是折叠的保留判定 `kp` 在 "Ω 形状, 槽位在孩子里, 路径经 `inc`" 一行恒取走链 (`nothing`)。只否定 `IndexTree`/`SlotIndex` 这一证据域在 `tw 1` 上有居民; 不否定 `LowKeepAtˣ (tw 1)`, 不否定 LowKeep 或路线。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXPNeg where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiTBRow using (rb-no)
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLean3Base using (sucT≤)
open import OCF.Lean.YiGTIndexNeg using (pen-gt)
open import OCF.Lean.YiGLFrame using (Lbl; lbl-fin; ≤→pen)
import OCF.Lean.YiXPRows as XW
import OCF.Lean.YiXPFold as XF
```

```agda
module Any (Lab : L → E.T → Set) where
  open XW Lab using (NodeFrame)

  no-frame-Ωinc : ∀ k h (o : Ok (nd (sΩ k) h)) (c : Tr k) {j} (v : j ≤ h c) {ν}
    (c′ : Tr k) (t : Pos⁼ (h c′)) {κ} → Lab (proj₁ (sl⁼ (h c′) t)) κ → E._<ᵀ_ κ ν
    → NodeFrame (nd (sΩ k) h) o j (inc c v) ν → ⊥
  no-frame-Ωinc k h o c v c′ t l lt fr = pen-gt (≤→pen (sucT≤ lt)) (fr (inj₂ (c′ , t)) _ l)

open XF Lbl using (IndexTree)

no-index-tree-tw1ˣ : IndexTree (tw 1) → ⊥
no-index-tree-tw1ˣ it = Any.no-frame-Ωinc Lbl zero (λ c → zero ⊕ ↑ zero c) (Ok-tw 1)
  (suc zero) self (suc zero) (inj₂ (inj₂ (tt , inj₁ tt))) refl E.[]<
  (proj₁ (proj₁ it (Ok-tw 1) (rb-no (tw 1)) (inj₂ (suc zero , inj₁ tt)) (E.natT 1) (lbl-fin 1)))
```
