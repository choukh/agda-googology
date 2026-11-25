# 可数孩子上的第 1 层归纳归约
验收文件，读记号；编译条件定理：后继步骤 Step 推出最小目标，Step 尚未实填。
零情形复用 YiBVZero；mL、mw 已填，对第 0 层树用 YiTBTail.acc⁰ 良基归纳。
量化域固定为 YiBVSmall.child d 的带证据读回，不对一切合法层号断言保持。
不声称 MinimalGoal 的无条件居民或实际 BranchNeed；有限实例见 YiQLCheck，链义务见 YiQLSuccessor。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiQLRead where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiBVReadBound as R
import OCF.Lean.YiBVSmall as S
import OCF.Lean.YiBVDomain as D
import OCF.Lean.YiBVZero as Z
import OCF.Lean.YiKVInst as I
import OCF.Lean.YiMENote as MN
import OCF.Lean.YiTBTail as W
import OCF.Lean.YiKCFin as Fin
import OCF.Align.EboLeanDef as E
Target : E.T → E.T
Target η = E.fsT D.slot η
formula : ∀ η → Target η ≡ (E.ψ (E.natT 1) (E.Ωt η) ∷ [])
formula η = refl
Need : E.T → B.Tr B.zero → Set
Need η d = R.At (Target η) (S.child d) (S.lower d)
zero : ∀ d → Need [] d
zero = Z.zero-at
limit : ∀ η d → E.cof η ≡ E.cω → (∀ n → Need (E.fsn η n) d) → Need η d
limit η d e ih o r base beta ok hb = K.mL
  (MN.cofψω (E.natT 1) (E.Ωt η) (I.Ωω η e))
  (λ n → subst (λ t → H.M 1 t (proj₁ (TB.ψ (S.child d) o r base K.one (S.lower d) beta (proj₁ (O.Ωt (S.child d))))))
    (sym (trans (MN.fsnψω (E.natT 1) (E.Ωt η) n (I.Ωω η e))
      (cong (λ t → E.ψ (E.natT 1) t ∷ []) (I.fsnΩω η n e))))
    (ih n o r base beta ok hb))
weak : ∀ η {d d′} → B._⊢_◃_ B.zero d d′ → Need η d → Need η d′
weak η e = R.canonical-mono (Target η) K.two (P.inc tt P.self)
  (K.⊴-◃ (Fin.suc-⊴ e) B.◃s)
Step : Set
Step = ∀ {η d} → E.cof η ≡ E.c1 → K.M⁰ (E.pred η) d
  → Need (E.pred η) d → Need η (B.suc d)
close : Step → (d : B.Tr B.zero)
  → ((x : B.Tr B.zero) → B._⊢_◃_ B.zero x d → (η : E.T) → K.M⁰ η x → Need η x)
  → (η : E.T) → K.M⁰ η d → Need η d
close st d ih .[] K.mz = zero d
close st .(B.suc x) ih η (K.m1 {x = x} e m) = st e m (ih x B.◃s (E.pred η) m)
close st d ih η (K.mL e h) = limit η d e (λ n → close st d ih (E.fsn η n) (h n))
close st d ih η (K.mΩ {p = ()} _ _ _)
close st d ih η (K.mU {c = ()} _ _)
close st d ih η (K.mw {x = x} m e) = weak η e (ih x e η m)
induct : Step → (d : B.Tr B.zero) → W.Acc⁰ d → (η : E.T) → K.M⁰ η d → Need η d
induct st d (W.acc sub) = close st d (λ x e → induct st x (sub x e))
leaf : Step → ∀ η d → K.M⁰ η d → Need η d
leaf st η d = induct st d (W.acc⁰ d) η
minimal-from : Step → S.MinimalGoal
minimal-from st = subst (H.M 1 D.slot) (sym (S.Small.kept-row S.small-keep))
  (K.mΩ refl refl (λ η d m → leaf st η d m
    (proj₂ S.okay d) (proj₂ (D.Input.table S.minimal) d)
    (S.Small.child-base d) (O.Ωt K.one) (λ i u → K.⊴r) (H.Mβ 0)))
```
