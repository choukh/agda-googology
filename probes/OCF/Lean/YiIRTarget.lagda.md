# 独立审查的目标基本列
验收文件；ψ₀(Ω_{Ω₂}) 的基本列公式及参照证书有构造，第0项在实际内分支下方。
第1项与完整目标的零层界未证，不增加已知强度；阶段0计划在本路私有封存包。
来源：规范对象复用 YiAZ/YiE4，初项复用 YiFRStations.k2；HC复用 YiRefTw2.hω-inv。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiIRTarget where
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
import OCF.Align.EboLeanDef as E
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiAZLocal as Z
import OCF.Lean.YiAZStart as A
import OCF.Lean.YiRefTw2 as R
import OCF.Lean.YiExInst as XI
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiFRStations as FS
open import OCF.Align.Value using (_≼_; ≼-trans)

target : E.T
target = E.ψ [] (E.Ωt (E.Ωt (E.natT 2))) ∷ []
Γ : ℕ → E.T
Γ zero = E.Ωt (E.natT 1)
Γ (suc n) = E.ψ (E.natT 1) (E.Ωt (Γ n)) ∷ []
γ-form : ∀ n → E.γT (E.Ωt (E.Ωt (E.natT 2))) (E.natT 1) n ≡ Γ n
γ-form zero = refl
γ-form (suc n) = cong (λ t → E.ψ (E.natT 1) (E.Ωt t) ∷ []) (γ-form n)
term : ℕ → E.T
term n = E.fsn target n
term-form : ∀ n → term n ≡ E.ψ [] (E.Ωt (Γ n)) ∷ []
term-form n = cong (λ t → E.ψ [] (E.Ωt t) ∷ []) (γ-form n)
term0 : term 0 ≡ Z.S 1
term0 = refl
term1 : term 1 ≡ E.ψ [] (E.Ωt (E.ψ (E.natT 1) (E.Ωt (E.Ωt (E.natT 1))) ∷ [])) ∷ []
term1 = refl
opaque
  target-hc : SI.E.HC target
  target-hc = subst SI.E.HC Z.S2 (Z.hc-S 2)
  term-hc : ∀ n → SI.E.HC (term n)
  term-hc n = SI.conv (R.hω-inv (XI.back target-hc) refl n)

initial-low : ∀ d → (h : SI.E.HC (term 0))
  → SI.E.tree h ≼ K.readRW (proj₁ (A.N.Inner.out d))
initial-low d h = ≼-trans
  (subst (λ x → SI.E.tree h ≼ K.readRW x) (sym Z.β-prior) (FS.k2 h)) (Z.out-base d)
initial-partial : (h : SI.E.HC (term 0)) → SI.E.tree h ≼ K.readRW (A.P 0)
initial-partial = Z.S1-low
```
