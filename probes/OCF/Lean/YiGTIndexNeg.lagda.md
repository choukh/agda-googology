# 第二有限层不满足当前同步槽位框架
验收文件（读记号）；编译否定只针对 `NodeFrame`、`SlotIndex`、`IndexTree` 这些新增证据。
同一个余尾下标 0 可在两种槽位出现，实际 kp 一个保留、一个走链，当前框架要求互斥的比较。
不否定 SelfKeep、StepU′、PresAt、规范塔域或一般目标路线；说明本证据域不能覆盖实际 tw 1。
入口：`no-frame₂`、`no-index-tree₂`、`no-index-tree-tw1`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGTIndexNeg where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiTBRow using (Rb; rb-no)
open import OCF.Lean.YiCLFam using (fn; okf)
open import OCF.Lean.YiANFam using (Pen)
open import OCF.Lean.YiGTNode using (NodeFrame)
open import OCF.Lean.YiGTDirect using (SlotIndex; IndexTree; LayerIndex)
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E

p-top : Pos (fn 2)
p-top = inj₂ (tt , inj₁ tt)

p-deep : Pos (fn 2)
p-deep = inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))

pen-gt : ∀ {m} → Pen m → m ≡ E.gt → ⊥
pen-gt (inj₁ ()) refl
pen-gt (inj₂ ()) refl

no-frame₂ : ∀ (o : Ok (fn 2)) ν → NodeFrame (fn 2) o (fn 1) (inc tt self) ν → ⊥
no-frame₂ o ν fr = pen-gt
  (proj₁ (fr p-deep [] (GR.c0 refl))) (fr p-top [] (GR.c0 refl))

no-slot-index₂ : ∀ (o : Ok (fn 2)) (r : Rb (fn 2)) → SlotIndex (fn 2) o r → ⊥
no-slot-index₂ o r si = no-frame₂ o [] (proj₁ (si p-top [] (GR.c0 refl)))

no-index-tree₂ : IndexTree (fn 2) → ⊥
no-index-tree₂ it = no-slot-index₂ (okf 2) (rb-no (fn 2)) (proj₁ it (okf 2) (rb-no (fn 2)))

no-index-tree-tw1 : IndexTree (tw 1) → ⊥
no-index-tree-tw1 it = no-index-tree₂ (proj₂ it (suc (suc zero)))

no-layer-tw1 : ∀ (o : Ok (tw 1)) (r : Rb (tw 1)) → LayerIndex (tw 1) o r → ⊥
no-layer-tw1 o r li = no-index-tree₂ (proj₂ li (suc (suc zero)))

no-self-frame₁-zero : (o : Ok (fn 1)) → NodeFrame (fn 1) o (fn 1) self [] → ⊥
no-self-frame₁-zero o fr with proj₁ (fr (inj₂ (tt , inj₁ tt)) [] (GR.c0 refl))
... | inj₁ ()
... | inj₂ ()

no-read→frame₁ : ((ν : E.T) → GR.Rd (fn 1) ν → NodeFrame (fn 1) (okf 1) (fn 1) self ν) → ⊥
no-read→frame₁ f = no-self-frame₁-zero (okf 1) (f [] (GR.c0 refl))
```
