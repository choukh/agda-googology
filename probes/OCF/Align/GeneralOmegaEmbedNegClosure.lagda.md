# 后继层原输出合法性的精确剩余前提

配对审计给正面边界：只要同一后继层中的原嵌入前缀输出合法，完整
后继地板的实际输出就合法。证明直接对原纯尾回调递归，不从Same
搬运第一位置，也不从leg的值下界推出合法性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaEmbedNegClosure where
open import Data.Nat using (zero)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.LHRecTy using (LH; Lv; ls; lz)
open import OCF.Lean.LHRecFl using (flL)
open import OCF.Lean.HigherIndexConsumeCode using (pure)
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.TowerCollapseClosed using (module LegalSum)
import OCF.Lean.GeneralOmegaConsumeRun as R
import OCF.Lean.GeneralOmegaConsumeLayerIf as Layer

module Tail (x : LH) (a : HB (Lv x)) where
  F : Cd → Cd
  F d = R.run (ls x) (up (a ⊞ pure (Lv x) d))
  position : ∀ {d e} → d ⊲ e → F d ⊲ F e
  position hself = hself
  position (hsuc p) = ⊲ᴮ-tr (position p) (hlim zero hself)
  position (hlim n p) = hlim n (position p)
  position (hLim {κ = ()} bd p)

  legal : LgB (R.run (ls x) (up a)) → ∀ d → LgB d → LgB (F d)
  legal la hz ld = la
  legal la (hs d) ld = LegalSum.sum-legal S⊥ _ (λ _ → legal la d ld)
  legal la (hl f) (st , ld) = (λ n → position (st n)) , (λ n → legal la (f n) (ld n))
  legal la (hΩ () f) ld

successor-legal : ∀ x → LgB (Layer.A x) → LgB (R.run (ls x) (flL (ls x)))
successor-legal x la = LegalSum.sum-legal S⊥ _
  (λ n → Tail.legal x (flL x) la (leg (chain _ n)) (Lg-leg (chain _ n)))

lowest-instance : LgB (R.run (ls lz) (flL (ls lz)))
lowest-instance = successor-legal lz tt
```

条件在最低后继层有真实实例。一般x的前提仍是原A x输出合法，未将
它换成低层run x(flL x)，也未证明完整ΛL raw合法或完成值保持。
每次回调的leg保证纯尾合法，输出部分和自动第一位置步进；无需假设
回调值单调或先证明整条chain合法。
