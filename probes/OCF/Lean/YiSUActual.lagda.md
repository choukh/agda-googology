# 显式供给归约在最小层的实际折叠
验收文件；两个 `Support` 与整段实际折叠实例，均不使用全域 `Leaf`。
根底分别为规范底与逐点 next 的底，前缀分别为空与 1；更新到底层后的 `Support` 为真。
这里只实填 `fn 1`，不声称全层前缀供给或原 `LowKeep` 已证。
入口：`support-next`、`fold-one`、`empty-fold`、`prefix-fold`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSUActual where
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiTBRow using (ψ; rb-no)
open import OCF.Lean.YiSUSupport
open import OCF.Lean.YiSUFold
open import OCF.Lean.YiSUBridge using (Bnext; ok-next; prefix-next)
open import OCF.Lean.YiSUNeg using (ℓ; o; t; okB; small-step)
open import OCF.Lean.YiGICheck using (leaf-fin)
open import OCF.Lean.YiKVRel using (⊴r)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E

support-next : ∀ o r → Support ℓ o r Bnext t
support-next o r = prefix-next , λ m c → tt

fold-one : SupportedPres ℓ
fold-one = fold ℓ rows-one

empty-fold : GR.R zero (E.ψ [] (E.Ωt (E.natT 1)) ∷ [])
  (proj₁ (ψ ℓ o (rb-no ℓ) (B₀ ℓ) zero (z≤ ℓ) (Ωt zero) (proj₁ (Ωt ℓ))))
empty-fold = fold-one o (rb-no ℓ) (B₀ ℓ) okB [] (support-one o (rb-no ℓ))
  (Ωt zero) (H.m1 refl H.mz) (leaf-fin 1)

prefix-fold : GR.R zero (E.ψ [] (t ++ E.Ωt (E.natT 1)) ∷ [])
  (proj₁ (ψ ℓ o (rb-no ℓ) Bnext zero (z≤ ℓ) (next⁺ (Ωt zero)) (proj₁ (Ωt ℓ))))
prefix-fold = fold-one o (rb-no ℓ) Bnext ok-next t (support-next o (rb-no ℓ))
  (next⁺ (Ωt zero)) small-step (leaf-fin 1)
```
