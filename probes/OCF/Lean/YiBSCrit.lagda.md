# tw 1 换基行在目标第 2 层的校准
验收文件（读记号）；编译定理 finite-crit 对自然数孩子 n ≥ 3 给 ψ₂(Ω_n) 关系，finite-shift 给移位关系。
证明复用 YiRBCrit 的 eqᵗ、critU、shiftU，换基部分仍用其无证据内核；非任意 η 的结论。
前提实例由 pre-ok 给出；该结果不提高已知终点强度。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBSCrit where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiBSBase
import OCF.Lean.YiBSFold as F
import OCF.Lean.YiRBSib as R
import OCF.Lean.YiRBCrit as C
open import OCF.Lean.YiKVRel using (_⊴_; ⊴r; +⊴; M⁰)
open import OCF.Lean.YiCLFam using (nat; fn; M; m⊴N; Mβ)
import OCF.Lean.YiRBFam
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ)
import OCF.Align.EboLeanDef as E

two : L
two = fn 2
o2 : Ok two
o2 = proj₂ (Ok-tw 1) (nat 2)
S₁ : Schema zero (λ c → zero ⊕ ↑ zero c)
S₁ = schema zero (↑ zero) tt self (OkO↑ zero zero tt self) (λ c → refl)
u2 : zero ≤ two
u2 = lift zero (↑ zero (nat 2))
g : Tr zero → Tr⁺ two
g c = F.ψ (tw 1) (Ok-tw 1) (rb-tw 1) (B₀ (tw 1)) two (inc (nat 2) self) (Ωt two) (C.blk c)
branch : Tr zero → Tr⁺ two
branch c = seen S₁ two o2 u2 (Ωt two) c
row : ∀ c → g c ≡ branch c ⊞ F.ψ₀ (C.h₁ c) (proj₂ (Ok-tw 1) c) (proj₂ (rb-tw 1) c) (proj₁ (Ωt (C.h₁ c)))
row c = refl
seen-at : ∀ {t} n → C.SP t (fn (C.sh n) , OCF.Lean.YiRBFam.pt (C.ptk n)) → M 2 t (proj₁ (branch (nat n)))
seen-at {t} n s = subst (C.SP t) (sym (C.eqᵗ n)) s
  (Ok⊕ two (↑ zero (nat n)) o2 (raiseO zero two (↑ zero (nat n)) u2 (OkO↑ zero zero tt self (nat n))))
  (R.rb-no _) (B₀ _) (Ωt two) (C.okB₀ _) (Mβ 1)
branch-at : ∀ {t} n → C.SP t (fn (C.sh n) , OCF.Lean.YiRBFam.pt (C.ptk n)) → M 2 t (proj₁ (g (nat n)))
branch-at {t} n s = subst (λ z → M 2 t (proj₁ z)) (sym (row (nat n)))
  (m⊴N 2 (seen-at n s) (+⊴ _ _))
finite-crit : ∀ k → C.CritAt g (suc (suc (suc k)))
finite-crit k = branch-at (suc (suc (suc k))) (C.critU k)
finite-shift : ∀ k → M 2 (ψᴺ 2 (Ωᴺ (suc (C.sh k)))) (proj₁ (g (nat (suc k))))
finite-shift k = branch-at (suc k) (C.shiftU k)
pre-ok : ∀ n → M⁰ (E.natT n) (nat n)
pre-ok = C.pre-ok
```
