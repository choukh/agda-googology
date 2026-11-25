# YiXVSourceFinitePath
> 验收文件。档位：编译定理。有限源路径的规范化；Sbᶠ 复用 YiASIface，复合复用 YiLMLow.comp。
> 接 YiXVSourceSem、SourceAffine*、Finite*，有限搬运比较参照 YiXVCan2Embed；未交完整外层链或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceFinitePath where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (1+n≰n)
open import Data.Empty using (⊥-elim)
open import OCF.Lean.YiASProofLow using (sb≤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegPath as P
open import OCF.Lean.YiASIface using (Sbᶠ; s0; ss)
open import OCF.Lean.YiLMLow using (comp)
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceSlots as Slots
import OCF.Lean.YiXVSourceCast as C

suc-inj : ∀ {a b : S.L} → S.suc a ≡ S.suc b → a ≡ b
suc-inj refl = refl
suc-eta : ∀ {a b : S.L} (e : S.suc a ≡ S.suc b) → cong S.suc (suc-inj e) ≡ e
suc-eta refl = refl
nat-inj : ∀ n m → J.nat n ≡ J.nat m → n ≡ m
nat-inj zero zero e = refl
nat-inj zero (suc m) ()
nat-inj (suc n) zero ()
nat-inj (suc n) (suc m) e = cong suc (nat-inj n m (suc-inj e))
nat-eq : ∀ n (e : J.nat n ≡ J.nat n) → e ≡ refl
nat-eq zero = C.zero-unique
nat-eq (suc n) e = trans (sym (suc-eta e)) (cong (cong S.suc) (nat-eq n (suc-inj e)))

pc : ∀ {a b n} → a ≡ b → a P.≤ J.nat n → b P.≤ J.nat n
pc {n = n} e w = subst (λ a → a P.≤ J.nat n) e w

pc-ins : ∀ {a b n} (e : a ≡ b) (w : a P.≤ J.nat n) → pc e (P.ins w) ≡ P.ins (pc e w)
pc-ins refl w = refl
record Cut (n : ℕ) {k} (w : k P.≤ J.nat n) : Set where
  constructor cut-path
  field
    j : ℕ
    e : k ≡ J.nat j
    s : Sbᶠ n j
    same : pc e w ≡ Slots.pth s
cut : ∀ n {k} (w : k P.≤ J.nat n) → Cut n w
cut zero P.self = cut-path 0 refl s0 refl
cut (suc n) P.self = cut-path (suc n) refl s0 refl
cut (suc n) (P.ins w) = cut-path (Cut.j old) (Cut.e old) (ss (Cut.s old))
  (trans (pc-ins (Cut.e old) w) (cong P.ins (Cut.same old)))
  where old = cut n w
sb-inj : ∀ {n j k} (s : Sbᶠ n j) (t : Sbᶠ n k) → j ≡ k → (j , s) ≡ (k , t)
sb-inj s0 s0 e = refl
sb-inj {n = suc n} s0 (ss t) e = ⊥-elim (1+n≰n (subst (λ k → k Data.Nat.≤ n) (sym e) (sb≤ t)))
sb-inj {n = suc n} (ss s) s0 e = ⊥-elim (1+n≰n (subst (λ k → k Data.Nat.≤ n) e (sb≤ s)))
sb-inj (ss s) (ss t) e = cong (λ { (j , s) → j , ss s }) (sb-inj s t e)
snd-path : ∀ {n} {x y : Σ ℕ (Sbᶠ n)} (e : x ≡ y) → subst (Sbᶠ n) (cong proj₁ e) (proj₂ x) ≡ proj₂ y
snd-path refl = refl
sb-unique : ∀ {n j} (s t : Sbᶠ n j) → s ≡ t
sb-unique {n} s t = trans (sym (cong (λ e → subst (Sbᶠ n) e s)
  (Data.Nat.Properties.≡-irrelevant (cong proj₁ bundle) refl))) (snd-path bundle)
  where bundle = sb-inj s t refl
thin : ∀ {n j} (s : Sbᶠ n j) (w : J.nat j P.≤ J.nat n) → w ≡ Slots.pth s
thin {n} {j} s w = finish (Cut.j c) (Cut.e c) (Cut.s c) (Cut.same c) (nat-inj j (Cut.j c) (Cut.e c))
  where
  c = cut n w
  finish : ∀ k (e : J.nat j ≡ J.nat k) (s′ : Sbᶠ n k) → pc e w ≡ Slots.pth s′ → j ≡ k → w ≡ Slots.pth s
  finish .j e s′ same refl rewrite nat-eq j e = trans same (cong Slots.pth (sb-unique s′ s))

compose : ∀ {n j m} (s : Sbᶠ n j) (t : Sbᶠ m n) → Slots.pth s P.∙ Slots.pth t ≡ Slots.pth (comp s t)
compose s s0 = refl
compose s (ss t) = cong P.ins (compose s t)
actual : P.ins (P.ins P.self) ≡ Slots.pth (ss (ss {n = 1} s0))
actual = thin (ss (ss s0)) (P.ins (P.ins P.self))

view : ∀ {n j} (w : J.nat j P.≤ J.nat n) → Σ (Sbᶠ n j) (λ s → w ≡ Slots.pth s)
view {n} {j} w = finish (Cut.j c) (Cut.e c) (Cut.s c) (Cut.same c) (nat-inj j (Cut.j c) (Cut.e c))
  where
  c = cut n w
  finish : ∀ k (e : J.nat j ≡ J.nat k) (s′ : Sbᶠ n k) → pc e w ≡ Slots.pth s′ → j ≡ k → Σ (Sbᶠ n j) (λ s → w ≡ Slots.pth s)
  finish .j e s′ same refl rewrite nat-eq j e = s′ , same
```
