# 树侧判据 (二): 弱证据的树上的有限测试

> **检验旧树的文件, 不干净:** 读法 `Tc-of rΩ₁ gΩ₁` 的证据 `rΩ₁`, `gΩ₁` 取自 [GuardReadAccept](GuardReadAccept.lagda.md), 那个文件读记号 (这里只用它给的 `Rs` 项). **全部是有限测试.** 结论写在 [TreeJudge2](TreeJudge2.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeJudge2TestW where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.TreeJudge2Test using (tabk; pC)
open import OCF.Align.TreeJudgeObs
open import OCF.Align.TreeJudgeRead using (rd)
open import OCF.Align.GuardWeakTree using (T₀ʷ)
open import OCF.Align.GuardWeakRd using (Tc-of)
open import OCF.Align.GuardReadAccept using (rΩ₁; gΩ₁)
open import OCF.Align.GuardTightLv
open Lv Dom₀ using (suc; s≈)
open import OCF.Align.GuardTightCert using (c₁; wf₁; sf₁)

o-w : Obs
o-w = rd (T₀ʷ (suc c₁) (wf₁ , s≈ sf₁) (Tc-of rΩ₁ gΩ₁))

b-w : tabk (lm 1 ∷ []) (lm 0 ∷ []) 5 8 2 o-w ≡ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []
b-w = refl

v-w : shape (go pC o-w) ≡ shc 1
v-w = refl

hf-w : run 8 7 2 o-w ≡ nothing
hf-w = refl

b-w2 : tabk (lm 2 ∷ []) (lm 1 ∷ []) 6 9 2 o-w ≡ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []
b-w2 = refl
```
