# 带底与前缀联系的槽位步进
验收文件；`StepU′` 在 `StepU` 的参数中增加槽位底承载 ψν(t) 的证据。
这是待实填的修改接口；`YiSUMin.step′-one` 给最小层号的全称实例。
`YiLKFold` 的当前 `OK B`、`Bdᵍ` 不提供这个新增前提；没有重编原 `LowKeep` 的归约。
入口：`PrefixU`、`StepU′`、`WholeU`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSUIface where
open import Data.Nat using (ℕ; suc)
open import Data.Product using (proj₁)
open import Data.List using (_∷_; []; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow using (Rb)
open import OCF.Lean.YiLKIface using (feed; OK)
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E

PrefixU : ∀ {ℓ} → Base ℓ → E.T → Set
PrefixU {ℓ} B t = (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν
  → GR.R (at ℓ p) (E.ψ ν t ∷ []) (proj₁ (B (at ℓ p) (posW ℓ p)))

StepU′ : L → Set
StepU′ ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t : E.T) → PrefixU B t
  → (a : E.T) (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν
  → E.cof a ≡ E.cΩ ν → (g : Br ℓ p → Tr ℓ) (n : ℕ) (c : Br ℓ p)
  → GR.Low ℓ p (E.γT (t ++ a) ν n) c
  → GR.R ℓ (E.fsT a (E.γT (t ++ a) ν n)) (g c)
  → GR.Low ℓ p (E.γT (t ++ a) ν (suc n)) (feed ℓ o r B p g c)

WholeU : L → Set
WholeU ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t a : E.T) (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν
  → E.cof a ≡ E.cΩ ν → (g : Br ℓ p → Tr ℓ)
  → (∀ η c → GR.Low ℓ p η c → GR.R ℓ (E.fsT a η) (g c))
  → (n : ℕ) (c : Br ℓ p) → GR.Low ℓ p (E.γT (t ++ a) ν n) c
  → GR.Low ℓ p (E.γT (t ++ a) ν (suc n)) (feed ℓ o r B p g c)
```
