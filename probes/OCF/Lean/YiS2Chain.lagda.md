# 第 2 站的实际槽位链
验收文件；编译定理：每个正编号实际链点在 tw 1 上对着所需 γ 项，实际孩子的 Ω 树对着对应 Ω 项。
来源：底下界复用 YiTBFam.ψ-⊵，槽位关系复用 YiLLCheck.leafΩ，孩子关系复用 YiNLRaise.raiseR。
本件不提供零层保持；YiS2Low 的证书经语义反射构造，与本件的方法分开。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiS2Chain where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Data.Sum using (inj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWPath
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBFam as TF
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiLLCheck as LL
open import OCF.Lean.YiKCStep using (⊴-trans)
open import OCF.Lean.YiGIInst using (baseᴱ; betaᴱ; pre)
import OCF.Lean.YiFRStep as FR
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Lean.YiCNTw1 using (leaf-tw1)
open import OCF.Lean.YiNLRaise using (raiseR)
open import OCF.Lean.YiNLCtx using (prefix)

ΩΩ : E.T
ΩΩ = E.Ωt (E.Ωt (E.natT 1))
βslot : O.Tr⁺ (tw 1)
βslot = baseᴱ 2 (tw 1) (ink self)
slot-above : proj₁ (O.Ωt (tw 1)) K.⊴ proj₁ βslot
slot-above = TF.ψ-⊵ Λ Ok-Λ (MT.rbᶻ Λ) (F.B₀ Λ) (tw 1) (inc 2 (ink self)) (O.Ωt (tw 1)) (pre 2)
feed-above : ∀ c → proj₁ βslot K.⊴ FR.Step.feed 1 c
feed-above c = TF.ψ-⊵ (tw 2) (Ok-tw 2) (MT.rbᶻ (tw 2)) (baseᴱ 2) (tw 1) (ink self) βslot (FR.Step.g 1 c)
actual-above : ∀ n → proj₁ (O.Ωt (tw 1)) K.⊴ FR.Step.chain 1 (suc n)
actual-above n = ⊴-trans slot-above (feed-above (FR.Step.chain 1 n))

chain-top : ∀ n → GR.R (tw 1) ΩΩ (FR.Step.chain 1 (suc n))
chain-top n = H.Gen.m⊴ LL.leafΩ (actual-above n)

gamma-bound : ∀ n → E.γT ΩΩ [] n ≤ᵀ ΩΩ
gamma-bound zero = inj₁ (E.hd< (E.lv< E.[]<))
gamma-bound (suc n) = inj₁ (E.hd< (E.lv< E.[]<))
actual-chain : ∀ n → GR.R (tw 1) (E.γT ΩΩ [] n) (FR.Step.chain 1 (suc n))
actual-chain n = H.mc (gamma-bound n) (chain-top n)

child-leaf : ∀ n → GR.R (FR.Step.child 1 (FR.Step.chain 1 (suc n))) (E.Ωt (E.γT ΩΩ [] n))
  (proj₁ (O.Ωt (FR.Step.child 1 (FR.Step.chain 1 (suc n)))))
child-leaf n = raiseR (tw 1) (prefix (tw 1)) [] (GR.c0 refl) (leaf-tw1 (GR.c0 refl)) (actual-chain n)

actual-g : ∀ n → GR.R (tw 2) (E.Ωt (E.γT ΩΩ [] n)) (FR.Step.g 1 (FR.Step.chain 1 (suc n)))
actual-g n = H.mU H.mz (child-leaf n)
```
