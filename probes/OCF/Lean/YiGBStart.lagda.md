# 里程碑第1项的文献条件
验收文件；实际 fs1 的 NF、精确 G₀ 成员、全 γ 参数规范实例为编译定理；不增加值下界。
沿用 YiIRTarget/YiAZ 的实际目标；不改树、折叠、底与表，不判定 FirstRow。
来源：Buchholz 3.3/3.6；复用 EboLeanClosure.cl-fsn-NF/tow，后者源自 ExBuchholz@6da2de5 Closure.lean:1554–1633。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGBStart where
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase
import OCF.Align.EboLeanClosure as EC
import OCF.Align.EboLeanTree as ET
import OCF.Align.EboLeanView as V
import OCF.Lean.YiAZStart as AZ
import OCF.Lean.YiAZLocal as AL
import OCF.Lean.YiIRTarget as IR
import OCF.Lean.YiAbsSimInst as SI

param : ℕ → E.T
param n = E.Ωt (IR.Γ n)
ref : ℕ → E.T
ref n = E.ψ [] (param n) ∷ []
ref-eq : ∀ n → E.fsn (AL.S 2) n ≡ ref n
ref-eq = IR.term-form
nf-S2 : NF (AL.S 2)
nf-S2 = EC.cl-fsn-NF (EC.cl-fsn-NF (AZ.nf-T 0) refl 0) refl 2
ref-NF : ∀ n → NF (ref n)
ref-NF n = subst NF (ref-eq n) (EC.cl-fsn-NF nf-S2 refl n)
param-NF : ∀ n → NF (param n)
param-NF n = nfp-a (nf-hd (ref-NF n))
param-G : ∀ n → GB [] (param n) (param n)
param-G n = nfp-g (nf-hd (ref-NF n))
opaque
  ref-HC : ∀ n → SI.E.HC (ref n)
  ref-HC n = subst SI.E.HC (ref-eq n) (IR.term-hc n)

fs1 : E.T
fs1 = E.fsn (AL.S 2) 1
fs1-NF : NF fs1
fs1-NF = EC.cl-fsn-NF nf-S2 refl 1
fs1-form : fs1 ≡ E.ψ [] (E.Ωt (E.ψ (E.natT 1) (E.ΩTower 2) ∷ [])) ∷ []
fs1-form = refl
Γ1-G : ∀ {z} → InG [] z (IR.Γ 1) → (z ≡ E.ΩTower 2) ⊎ (z ≡ [])
Γ1-G (gp (gh _)) = inj₁ refl
Γ1-G (gp (gw _ i)) = inj₂ (ET.G0-tower 0 i)
Γ1-G (gp (gc _ i)) = inj₂ (ET.G0-tower 2 i)
Γ1-G (gtl ())
param1-G : ∀ {z} → InG [] z (param 1) → (z ≡ E.ΩTower 2) ⊎ (z ≡ [])
param1-G (gp (gh _)) = inj₂ refl
param1-G (gp (gw _ i)) = Γ1-G i
param1-G (gp (gc _ ()))
param1-G (gtl ())
fs1-G : ∀ {z} → InG [] z fs1 → (z ≡ param 1) ⊎ (z ≡ E.ΩTower 2) ⊎ (z ≡ [])
fs1-G (gp (gh _)) = inj₁ refl
fs1-G (gp (gw _ ()))
fs1-G (gp (gc _ i)) = inj₂ (param1-G i)
fs1-G (gtl ())
arg∈G : InG [] (param 1) fs1
arg∈G = gp (gh (inj₂ refl))
tower∈G : InG [] (E.ΩTower 2) fs1
tower∈G = gp (gc (inj₂ refl) (gp (gw (inj₁ E.[]<) (gp (gh (inj₁ E.[]<))))))
zero∈G : InG [] [] fs1
zero∈G = gp (gc (inj₂ refl) (gp (gh (inj₁ E.[]<))))

w : V.VΩ (E.Ωt (E.Ωt (E.natT 2))) (E.natT 1)
w = V.ωl refl (V.ωr refl)
γ-form : ∀ q → V.γ w q ≡ IR.Γ q
γ-form zero = refl
γ-form (suc q) = cong (λ x → E.ψ (E.natT 1) (E.Ωt x) ∷ []) (γ-form q)
γ-data : ∀ q → NF (IR.Γ q) × GB [] (IR.Γ q) (param q)
γ-data q = subst (λ x → NF x × GB [] x (E.Ωt x)) (γ-form q)
  (EC.tow nf-S2 w (inj₁ E.[]<) q)
param-grow : ∀ q → param q E.<ᵀ param (suc q)
param-grow zero = E.hd< (E.lv< (E.hd< (E.ar< E.[]<)))
param-grow (suc q) = E.hd< (E.lv< (E.hd< (E.ar< (param-grow q))))
sample : ∀ q → NF (param q) × GB [] (param q) (param q) × (param q ≤ᵀ param q) × SI.E.HC (ref q)
sample q = param-NF q , param-G q , inj₂ refl , ref-HC q
new-sample : ∀ q → NF (param (suc q)) × GB [] (param (suc q)) (param (suc q))
  × (param q E.<ᵀ param (suc q)) × (param (suc q) ≤ᵀ param (suc q)) × SI.E.HC (ref (suc q))
new-sample q = param-NF (suc q) , param-G (suc q) , param-grow q , inj₂ refl , ref-HC (suc q)
```
