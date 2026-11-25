# 零层下标可从所选独立重置的层号取回

第四层。对任意零层树 z，读回其层号的标准 Ω，再折到零层，所得值至少为 z 的序数值。左端可预接任意有限串层号。后继情形使用实际首个正下标的覆盖，极限情形保留每个累加项的前缀。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4NextLiftIndex where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Maybe.Base using (nothing; just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
import W4Block as W
import W4Ops as O
import W4Fold as F
import W4Path as P
open import WVOne using (T₀; read; h₁; cum-≥)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; s≼s; z≼; l≼)
import B12Terminal as T
import B12ActualSlots as C
import B12Strict as Strict
import B15ReadPaths as R
import B15Spine as Sp
import B20Room as Room
open T.Run

plug : List W.L → W.L → W.L
plug [] x = x
plug (a ∷ p) x = plug p (a W.⊕ x)
node : ∀ p s (h : W.Ch s → W.L) → plug p (W.nd s h) ≡ W.nd s (λ c → plug p (h c))
node [] s h = refl
node (a ∷ p) s h = node p s (λ c → a W.⊕ h c)
inside : ∀ p {a b} → R.Reach a b → R.Reach (plug p a) (plug p b)
inside [] e = e
inside (a ∷ p) e = inside p (R.left a e)

Worth : T₀ → W.L → Set
Worth x l = (r : T.Run l) → C.Covered r → x ≼ read (T.value r)
via : ∀ {a b x} → R.Reach a b → Worth x a → Worth x b
via e u r c = ≼-trans (u (Room.sub e r) (Room.cover e r c)) (Room.below e r c)

diag = λ z → W.↑ (h₁ z) (proj₁ (O.Ωt (h₁ z)))
covered-path : ∀ k {b} → C._⊴_ (proj₁ (O.Ωt k)) b → R.Reach (W.↑ k (proj₁ (O.Ωt k))) (W.↑ k b)
covered-path k (inj₁ refl) = R.here
covered-path k (inj₂ d) = R.read-step k d

node-strict : ∀ {X : Set} {z : X} (v : F.Keep W.zero X z) (G : X → O.Tr⁺ W.zero) (s : X → X) n →
  L.suc (read (proj₁ (G (W.iter s z n)))) ≼ read (proj₁ (F.node⁺ v G s))
node-strict nothing G s n = ≼-trans (s≼s (cum-≥ _ n)) (Strict.strict (W.◃l n))
node-strict (just (() , _)) G s n

module Positive (k : W.L) (g : W.Tr k → W.L) (r : T.Run (W.nd (W.sΩ k) g)) (cv : C.Covered r) where
  module A = Sp.Cardinal k g r
  c = A.ix 1
  reach : R.Reach (W.↑ k (proj₁ (O.Ωt k))) (W.↑ k c)
  reach = covered-path k step
    where
    step : C._⊴_ (proj₁ (O.Ωt k)) c
    step with C.preserve _ (ok r) (bs r) k (W.ink W.self) (bs r k (W.ink W.self)) (A.b W.zero)
    ... | inj₁ e = subst (C._⊴_ (proj₁ (O.Ωt k))) e (cv k (W.ink W.self))
    ... | inj₂ e = C.extend (cv k (W.ink W.self)) e
  strict : L.suc (read (T.value (A.child 1))) ≼ read (T.value r)
  strict = node-strict (F.kp _ (ok r) A.p (P.z≤ _)) (λ z → F.ψ _ (ok r) (bs r) W.zero (P.z≤ _) (β r) (A.b z)) A.step 1

growth : ∀ z p → Worth (read z) (plug p (diag z))
growth W.zero p r cv = z≼
growth (W.suc z) p = subst (Worth (L.suc (read z))) (sym (node p (W.sΩ k) h)) proof
  where
  k = h₁ z
  h = λ c → W.zero W.⊕ W.nd W.sS (λ _ → W.↑ k c)
  g = λ c → plug p (h c)
  proof : Worth (L.suc (read z)) (W.nd (W.sΩ k) g)
  proof r cv = ≼-trans (s≼s (via site (growth z (W.zero ∷ p)) (Q.A.child 1) (Q.A.cover cv 1))) Q.strict
    where
    module Q = Positive k g r cv
    site = inside (W.zero ∷ p) (R.via Q.reach R.succ)
growth (W.lim f d) p = subst (Worth (read (W.lim f d))) (sym (node p W.sL h)) proof
  where
  k = h₁ (W.lim f d)
  seg = λ n → proj₁ (O.upz {h = λ n → h₁ (f n)} n (O.Ωt (h₁ (f n))))
  h = λ n → W.↑ k (O.cum seg n)
  g = λ n → plug p (h n)
  before : ℕ → W.L
  before zero = W.zero
  before (suc n) = W.↑ k (O.cum seg n)
  cost : ∀ n → Worth (read (f n)) (g n)
  cost zero = growth (f 0) (before 0 ∷ p)
  cost (suc n) = growth (f (suc n)) (before (suc n) ∷ p)
  proof : Worth (read (W.lim f d)) (W.nd W.sL g)
  proof r cv = l≼ λ n → via (R.limit n) (cost n) r cv
```
