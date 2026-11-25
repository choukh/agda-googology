# 混合族：所有标准形层号的 Ω 种子

按有限层码的共尾度写四行：零给 1，后继给 raw 正规结点，
ω-共尾逐 n 递归，Ω-共尾用携码奇异分支。递归只下降本层 Acc。
这比仅有第 1 层合同强，但仍是甲的记号引导定义，不是乙的 Ω。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaMixedOmega where

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ)
open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
open import OCF.Align.EboLeanDef
  using (T; Cof; c0; c1; cω; cΩ; cof; cofψ0; pred; Ωt; Ωs; fsn; fsn0; fsT; fsT0; _<ᵀ_)
open import OCF.Align.EboLeanBase using (NF; n[]; nf-Ω; nf-pred; <ᵀ-trans)
open import OCF.Align.EBO using (<-sucT)
open import OCF.Align.EboLean3Omega using (Acc′; acc)
open import OCF.Align.EboLeanView using (ne; cof0; vΩ; nf-ν; dom<; fΩ-eq)
open import OCF.Align.EboLeanTrian using (t<; T-pred; TΩ)
open import OCF.Align.EboLeanOmega using (NFΩ)
open import OCF.Align.EboLeanClosure using (cl-fsn-NF; trian-fsn)
open import OCF.Align.JiaMixedBase
open import OCF.Align.JiaMixedRep
open RelLayer using (rz; rs; rl; rr; rq)

empty : ∀ c → cof c ≡ c0 → c ≡ []
empty [] e = refl
empty c@(_ ∷ _) e = ⊥-elim (cof0 c ne e)

cof-Ω-1 : ∀ c → cof c ≡ c1 → cof (Ωt c) ≡ cΩ (pred c)
cof-Ω-1 [] ()
cof-Ω-1 c@(_ ∷ _) e = cong (cofψ0 c) e

fsT-Ω-1 : ∀ c → cof c ≡ c1 → ∀ d → fsT (Ωt c) d ≡ d
fsT-Ω-1 [] () d
fsT-Ω-1 c@(_ ∷ _) e d = cong (λ k → fsT0 c k d) e

cof-Ω-ω : ∀ c → cof c ≡ cω → cof (Ωt c) ≡ cω
cof-Ω-ω [] ()
cof-Ω-ω c@(_ ∷ _) e = cong (cofψ0 c) e

fsn-Ω-ω : ∀ c → cof c ≡ cω → ∀ n → fsn (Ωt c) n ≡ Ωt (fsn c n)
fsn-Ω-ω [] () n
fsn-Ω-ω c@(_ ∷ _) e n = cong (λ k → fsn0 c k n) e

cof-Ω-Ω : ∀ c j → cof c ≡ cΩ j → cof (Ωt c) ≡ cΩ j
cof-Ω-Ω [] j ()
cof-Ω-Ω c@(_ ∷ _) j e = cong (cofψ0 c) e

fsT-Ω-Ω : ∀ c j → cof c ≡ cΩ j → ∀ d → fsT (Ωt c) d ≡ Ωt (fsT c d)
fsT-Ω-Ω [] j () d
fsT-Ω-Ω c@(_ ∷ _) j e d = cong (λ k → fsT0 c k d) e

pred-below : ∀ {c} → NF c → cof c ≡ c1 → Below (pred c) c
pred-below {c} nc e = below (nf-pred nc) (t< (T-pred c e))

nat-below : ∀ {c} → NF c → cof c ≡ cω → (n : ℕ) → Below (fsn c n) c
nat-below nc e n = below (cl-fsn-NF nc e n) (t< (trian-fsn nc e n))

node-below : ∀ {c j} → NF c → cof c ≡ cΩ j → Below j c
node-below {c} {j} nc e = below (nf-ν nc v)
  (<ᵀ-trans (<-sucT j) (dom< nc v))
  where v = vΩ c e

code-below : ∀ {c j} → NF c → cof c ≡ cΩ j → (d : CodeArg j) → Below (fsT c (code d)) c
code-below {c} nc e d = below
  (subst NF (sym (fΩ-eq v (code d))) (NFΩ nc v (code-normal d) (code-bound d)))
  (subst (_<ᵀ c) (sym (fΩ-eq v (code d))) (t< (TΩ v (code-bound d))))
  where v = vΩ c e

at : ∀ {ℓ j} (a : Acc′ ℓ) → Below j ℓ → Acc′ j
at (acc h) p = h (normal p) (smaller p)

build : ∀ {c} → NF c → (a : Acc′ c) →
  (∀ {j} (p : Below j c) → Tree j (at a p)) →
  (k : Cof) → cof c ≡ k → Tree c a
build nc (acc h) sub c0 e = Layer.s Layer.z
build nc (acc h) sub c1 e = Layer.r p (lift (at (acc h) p) (acc h) p)
  where p = pred-below nc e
build nc (acc h) sub cω e = Layer.l (λ n →
  lift (at (acc h) (nat-below nc e n)) (acc h) (nat-below nc e n) (sub (nat-below nc e n)))
build nc (acc h) sub (cΩ j) e = Layer.q (node-below nc e) (λ d →
  lift (at (acc h) (code-below nc e d)) (acc h) (code-below nc e d) (sub (code-below nc e d)))

omega : ∀ {c} → NF c → (a : Acc′ c) → Tree c a
omega {c} nc (acc h) = build nc (acc h)
  (λ p → omega (normal p) (h (normal p) (smaller p))) (cof c) refl

build-rep : ∀ {c} (nc : NF c) (a : Acc′ c)
  (sub : ∀ {j} (p : Below j c) → Tree j (at a p)) →
  (∀ {j} (p : Below j c) → Rep (at a p) (sub p) (Ωt j)) →
  (k : Cof) (e : cof c ≡ k) → Rep a (build nc a sub k e) (Ωt c)
build-rep {c} nc (acc h) sub sub-rep c0 e =
  subst (λ d → Rep (acc h) (Layer.s Layer.z) (Ωt d)) (sym (empty c e)) (rs rz)
build-rep {c} nc (acc h) sub sub-rep c1 e = rr (cof-Ω-1 c e)
  (λ {y} {d} r → subst (Rep (acc h) _) (sym (fsT-Ω-1 c e d))
    (rep-lift (at (acc h) p) (acc h) p r))
  where p = pred-below nc e
build-rep {c} nc (acc h) sub sub-rep cω e = rl (cof-Ω-ω c e)
  (λ n → subst (Rep (acc h) _) (sym (fsn-Ω-ω c e n))
    (rep-lift (at (acc h) (nat-below nc e n)) (acc h) (nat-below nc e n)
      (sub-rep (nat-below nc e n))))
build-rep {c} nc (acc h) sub sub-rep (cΩ j) e = rq (cof-Ω-Ω c j e)
  (λ d → subst (Rep (acc h) _) (sym (fsT-Ω-Ω c j e (code d)))
    (rep-lift (at (acc h) (code-below nc e d)) (acc h) (code-below nc e d)
      (sub-rep (code-below nc e d))))

omega-rep : ∀ {c} (nc : NF c) (a : Acc′ c) → Rep a (omega nc a) (Ωt c)
omega-rep {c} nc (acc h) = build-rep nc (acc h)
  (λ p → omega (normal p) (h (normal p) (smaller p)))
  (λ p → omega-rep (normal p) (h (normal p) (smaller p))) (cof c) refl

record Seeds : Set₁ where
  field
    seed : ∀ {c} → NF c → (a : Acc′ c) → Tree c a
open Seeds public

record SeedSpec (seeds : Seeds) (ℓ : T) : Set where
  field
    sound : ∀ {i} (p : Below i ℓ) (ai : Acc′ i) → Rep ai (seed seeds (normal p) ai) (Ωt i)
open SeedSpec public

omega-seeds : Seeds
seed omega-seeds = omega

all-seeds : ∀ ℓ → SeedSpec omega-seeds ℓ
sound (all-seeds ℓ) p ai = omega-rep (normal p) ai
```

all-seeds 没有全局闭包假设，对每个标准形低层均实填，因而覆盖 Λ 以下
全部有限标准形层码。它不等于 ψ 保持、反馈闭包或终点下界已完成。
翻译账：种子按码的 cof、fsn、fsT 递归；奇异分支的 CodeArg 明读记号码。
