# 有限 η 的读回与后继步
验收文件，读记号；编译定理：所有有限 η 的 Need，以及 Step 在 η = natT (suc n) 上的实例。
来源：YiTBFam.sΩ-LF/liftU、YiCLPhi.nat⊴、YiQLRead.weak；有限锚点多走三层。
不更改定义，不声称一般 Step 或 MinimalGoal；基本列逐项有限的极限见 YiSQOmega。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSQNat where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiTBFam as T
import OCF.Lean.YiRBFam as R
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiCLLow as L
import OCF.Lean.YiBVReadBound as RB
import OCF.Lean.YiBVSmall as S
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiKCFin as Fin
import OCF.Lean.YiQLRead as Q
import OCF.Lean.YiQLCheck as C
import OCF.Lean.YiANFam as A
import OCF.Lean.YiCLPhi as Phi
import OCF.Align.EboLeanDef as E
v : ∀ n → P._≤_ K.one (H.fn (suc (suc n)))
v zero = P.inc tt P.self
v (suc n) = P.inu (λ _ → v n)
pt : ∀ n → R.Pt (suc (suc n)) 1
pt zero = R.can (L.ss L.s0)
pt (suc n) = R.pu (pt n)
pt-eq : ∀ n → R.pt (pt n) ≡ v n
pt-eq zero = refl
pt-eq (suc n) = cong (λ w → P.inu (λ _ → w)) (pt-eq n)
tp : ∀ n → R.Tp (suc n) 1
tp zero = R.tc L.s0
tp (suc n) = R.tu (pt n)
tp-eq : ∀ n → R.tp (tp n) ≡ v n
tp-eq zero = refl
tp-eq (suc n) = cong (λ w → P.inu (λ _ → w)) (pt-eq n)
Pair : Set
Pair = Σ B.L (P._≤_ K.one)
raise : Pair → Pair
raise (a , w) = B.nd B.sS (λ _ → a) , P.inu (λ _ → w)
shape : ∀ n → (S.child (H.nat n) , S.lower (H.nat n))
  ≡ (H.fn (suc (suc (suc n))) , P.inu (λ _ → v n))
shape zero = refl
shape (suc n) = cong raise (shape n)
exact : ∀ n → RB.At (Q.Target (E.natT (suc (suc n)))) (H.fn (suc (suc n))) (v n)
exact n o r = subst (RB.Bound (Q.Target (E.natT (suc (suc n)))) (H.fn (suc (suc n))) o r)
  (tp-eq n) (T.sΩ-LF o r (tp n))
padded : ∀ n → RB.At (Q.Target (E.natT (suc (suc n)))) (H.fn (suc (suc (suc (suc (suc n))))))
  (P.inu (λ _ → P.inu (λ _ → P.inu (λ _ → v n))))
padded n o r = T.liftU o r (P.inu (λ _ → P.inu (λ _ → v n)))
  (T.liftU (proj₂ o tt) (proj₂ r tt) (P.inu (λ _ → v n))
    (T.liftU (proj₂ (proj₂ o tt) tt) (proj₂ (proj₂ r tt) tt) (v n)
      (exact n (proj₂ (proj₂ (proj₂ o tt) tt) tt) (proj₂ (proj₂ (proj₂ r tt) tt) tt))))
anchor : ∀ n → Q.Need (E.natT n) (H.nat n)
anchor zero = Q.zero B.zero
anchor (suc zero) = C.at-one
anchor (suc (suc n)) = subst (λ p → RB.At (Q.Target (E.natT (suc (suc n)))) (proj₁ p) (proj₂ p))
  (sym (shape (suc (suc n)))) (padded n)
nat-all : ∀ n {d} → K.M⁰ (E.natT n) d → Q.Need (E.natT n) d
nat-all n m = lift (Phi.nat⊴ n m refl)
  where
  lift : ∀ {d} → K._⊴_ (H.nat n) d → Q.Need (E.natT n) d
  lift K.⊴r = anchor n
  lift (K.⊴◃ e) = Q.weak (E.natT n) e (anchor n)
step-nat : ∀ n {d} → K.M⁰ (E.pred (E.natT (suc n))) d
  → Q.Need (E.pred (E.natT (suc n))) d → Q.Need (E.natT (suc n)) (B.suc d)
step-nat n m ih = nat-all (suc n) (K.m1 (A.cof-nat n) m)
```
