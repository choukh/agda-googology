# 文献式验收的最小检查
验收文件；NF、G 分量、γ 链及实际链首两点为编译定理；不增加值下界。
目标与证书、原 feed/out 均保持原定义；本文件不判定 FirstMissing。
来源：EboLeanClosure.cl-fsn-NF/tow；后者已移植 ExBuchholz@6da2de5 Closure.lean:1554–1633。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLBStart where
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; trans)
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase
open import OCF.Align.EboLeanClosure using (cl-fsn-NF; tow)
import OCF.Align.EboLeanView as V
import OCF.Align.EboLeanTree as ET
import OCF.Lean.YiFRStep as FR
import OCF.Lean.YiGIEnd as GE
import OCF.Lean.YiGIInst as GI
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
open FR using (module Step)
open import OCF.Lean.YiExSuff
open ExSuff GI.gradedᵍ GI.domsᵍ using (Keel⁻)
row3 : E.T
row3 = Keel⁻.row GI.keelᴱ 3
target : E.T
target = E.fsn row3 1
nf-row3 : NF row3
nf-row3 = subst NF (sym (GE.row-eq 3)) (ET.nf-tower 3)
nf-target : NF target
nf-target = cl-fsn-NF nf-row3 (FR.rowω 2) 1
r2 : E.T
r2 = E.EBOψ 2
arg : E.T
arg = E.Ωt (E.Ωt r2)
target-form : target ≡ E.ψ [] arg ∷ []
target-form = refl
w : V.VΩ (E.ΩTower 3) []
w = V.ωl refl (V.ωl refl (V.ωr refl))
gamma0 : V.γ w 0 ≡ E.ΩTower 0
gamma0 = refl
gamma1 : V.γ w 1 ≡ r2
gamma1 = refl
gamma-NF-G : ∀ q → NF (V.γ w q) × GB [] (V.γ w q) (V.fΩ w (V.γ w q))
gamma-NF-G = tow (ET.nf-tower 3) w (inj₂ refl)
gamma-G : ∀ {z} → InG [] z r2 → (z ≡ E.ΩTower 2) ⊎ (z ≡ [])
gamma-G (gp (gh _)) = inj₁ refl
gamma-G (gp (gw _ ()))
gamma-G (gp (gc _ i)) = inj₂ (ET.G0-tower 2 i)
gamma-G (gtl ())
arg-G : ∀ {z} → InG [] z arg → (z ≡ E.ΩTower 2) ⊎ (z ≡ [])
arg-G (gp (gh _)) = inj₂ refl
arg-G (gp (gw _ (gp (gh _)))) = inj₂ refl
arg-G (gp (gw _ (gp (gw _ i)))) = gamma-G i
arg-G (gp (gw _ (gp (gc _ ()))))
arg-G (gp (gw _ (gtl ())))
arg-G (gp (gc _ ()))
arg-G (gtl ())
target-G : ∀ {z} → InG [] z target → (z ≡ arg) ⊎ (z ≡ E.ΩTower 2) ⊎ (z ≡ [])
target-G (gp (gh _)) = inj₁ refl
target-G (gp (gw _ ()))
target-G (gp (gc _ i)) = inj₂ (arg-G i)
target-G (gtl ())
hc-target : SI.E.HC target
hc-target = SI.conv (ET.hc nf-target (c∷ c[]))
chain0 : Step.chain 2 0 ≡ B.zero
chain0 = refl
g0 : Step.g 2 B.zero ≡ proj₁ (O.upz {s = B.sΩ (B.tw 2)} {h = Step.child 2} B.zero (O.Ωt (B.tw 2)))
g0 = refl
chain1 : Step.chain 2 1 ≡ proj₁ (TB.ψ (B.tw 3) (P.Ok-tw 3) (MT.rbᶻ (B.tw 3)) (GI.baseᴱ 3)
  (B.tw 2) (P.ink P.self) (GI.baseᴱ 3 (B.tw 2) (P.ink P.self))
  (proj₁ (O.upz {s = B.sΩ (B.tw 2)} {h = Step.child 2} B.zero (O.Ωt (B.tw 2)))))
chain1 = refl
chain1-nz : B.tw 2 B.⊢ B.zero ◃ Step.chain 2 1
chain1-nz = proj₂ (TB.ψ (B.tw 3) (P.Ok-tw 3) (MT.rbᶻ (B.tw 3)) (GI.baseᴱ 3)
  (B.tw 2) (P.ink P.self) (GI.baseᴱ 3 (B.tw 2) (P.ink P.self)) (Step.g 2 B.zero))
out-nz : ∀ q → B.zero B.⊢ B.zero ◃ proj₁ (Step.out 2 (Step.chain 2 q))
out-nz q = proj₂ (Step.out 2 (Step.chain 2 q))

arg∈G : InG [] arg target
arg∈G = gp (gh (inj₂ refl))
tower∈G : InG [] (E.ΩTower 2) target
tower∈G = gp (gc (inj₂ refl) (gp (gw (inj₁ E.[]<) (gp (gw (inj₁ E.[]<) (gp (gh (inj₂ refl))))))))
zero∈G : InG [] [] target
zero∈G = gp (gc (inj₂ refl) (gp (gh (inj₁ E.[]<))))

chain1-self : Step.chain 2 1 ≡ proj₁ (TB.ψ (B.tw 2) (P.Ok-tw 2) (MT.rbᶻ (B.tw 2))
  (λ i u → GI.baseᴱ 3 i (P.inc B.zero u)) (B.tw 2) P.self
  (GI.baseᴱ 3 (B.tw 2) (P.ink P.self)) (proj₁ (O.Ωt (B.tw 2))))
chain1-self = refl
```
