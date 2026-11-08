# 相对有限证书的结构闭包

闭包不要求中间Legal成为raw LgB。所有目标层共用这些定理。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedFiniteRegClosure where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Align.BoundedFiniteRegIf
open import OCF.Align.BoundedFiniteRegSub

seed-map : ∀ n {D R} ext ext′ κ (g : E (F n) κ → HB D) (h : E (F n) κ → HB R) →
  (∀ W → RegWorld n W → ∀ c d → RegCoord n κ c → RegCoord n κ d →
    g c ⊲[ ext W ] g d → h c ⊲[ ext′ W ] h d) → Seed n ext κ g → Seed n ext′ κ h
seed-map zero ext ext′ κ g h map p = tt
seed-map (suc n) ext ext′ (inj₁ κ) g h map p =
  seed-map n (λ W → ext (W , one n)) (λ W → ext′ (W , one n)) κ g h
    (λ W rW c d rc rd q → map (W , one n) (rW , reg-one n) c d rc rd q) p
seed-map (suc n) ext ext′ (inj₂ _) g h map p {W} {c} {d} rW bc bd q =
  map (W , one n) (rW , reg-one n) c d (reg-sub n rW (reg-one n) bc)
    (reg-sub n rW (reg-one n) bd) (p rW bc bd q)

reg-add : ∀ n a b → Reg n a → Reg n b → Reg n (a ⊞ b)
reg-add zero a b ra rb = tt
reg-add (suc n) a hz ra rb = ra
reg-add (suc n) a (hs b) ra rb = reg-add (suc n) a b ra rb
reg-add (suc n) a (hl f) ra rb = λ j → reg-add (suc n) a (f j) ra (rb j)
reg-add (suc n) a (hΩ κ g) ra (mo , r) =
  seed-map (suc n) (λ W → W) (λ W → W) κ g (λ c → a ⊞ g c)
    (λ W rW c d rc rd p → ⊞-⊲ a p) mo ,
  (λ c rc → reg-add (suc n) a (g c) ra (r c rc))

legal-add : ∀ n a b → Legal n a → Legal n b → Legal n (a ⊞ b)
legal-add zero a b la lb = Lg-⊞ a b la lb
legal-add (suc n) a hz la lb = la
legal-add (suc n) a (hs b) la lb = legal-add (suc n) a b la lb
legal-add (suc n) a (hl f) la (st , l) =
  (λ rw j → ⊞-⊲ a (st rw j)) , (λ j → legal-add (suc n) a (f j) la (l j))
legal-add (suc n) a (hΩ κ g) la (mo , l) =
  (λ lw b b′ p → ⊞-⊲ a (mo lw b b′ p)) ,
  (λ c lc → legal-add (suc n) a (g c) la (l c lc))

good-add : ∀ n a b → Good n a → Good n b → Good n (a ⊞ b)
good-add n a b (ra , la) (rb , lb) = reg-add n a b ra rb , legal-add n a b la lb
legal-one : ∀ n → Legal n (one n)
legal-one zero = tt
legal-one (suc n) = tt
good-one : ∀ n → Good n (one n)
good-one n = reg-one n , legal-one n

reg-lim : ∀ n f → (∀ j → Reg n (f j)) → Reg n (hl f)
reg-lim zero f r = tt
reg-lim (suc n) f r = r
legal-lim : ∀ n f → (∀ {W} → RegWorld n W → ∀ j → f j ⊲[ W ] f (suc j)) →
  (∀ j → Legal n (f j)) → Legal n (hl f)
legal-lim zero f st l = (λ j → st tt j) , l
legal-lim (suc n) f st l = st , l

reg-sum : ∀ n f → (∀ j → Reg n (f j)) → Reg n (Ops.sum (F n) f)
reg-sum n f r = reg-lim n _ partial
  where
  partial : ∀ j → Reg n (Ops.partial (F n) f j)
  partial zero = r zero
  partial (suc j) = reg-add n _ _ (partial j) (r (suc j))
legal-sum : ∀ n f → (∀ j → Legal n (f j)) → Legal n (Ops.sum (F n) f)
legal-sum n f l = legal-lim n _ (λ rw j → ⊞-fst _ _) partial
  where
  partial : ∀ j → Legal n (Ops.partial (F n) f j)
  partial zero = l zero
  partial (suc j) = legal-add n _ _ (partial j) (l (suc j))

legal-node : ∀ n κ g →
  (∀ {W c d} → LegalWorld n W → Bd (F n) κ c W → Bd (F n) κ d W → Pr (F n) κ W c d → g c ⊲[ W ] g d) →
  (∀ c → LegalCoord n κ c → Legal n (g c)) → Legal n (hΩ κ g)
legal-node zero κ g mo l = mo , (λ {w = W} {c} lw b → l c (W , lw , b))
legal-node (suc n) κ g mo l = mo , l
```
