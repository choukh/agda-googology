# 同形高度的路径与规范合法证对应

路径关系保留后继与同一个ℕ分量编号；它没有宣称不同路径相等。
LegalShape明确记录两边合法步进的对应，因此Same高度本身不足以
替代该前提。原leg与Lg-leg的规范实例由部分和形状直接构造。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableShapeBase where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg; Σ₀; Lg-Σ₀)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo)
open import OCF.Lean.GeneralOmegaConsumeLayerRun using (leg-same; leg-sums)
open import OCF.Lean.BoundedDiagonalSame using (same-add)
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableShapeIf using (map-K)

data Paths : ∀ {a b A B : Cd} → Same a b → Same A B → a ⊲ A → b ⊲ B → Set where
  phere : ∀ {a b} (p : Same a b) → Paths p p hself hself
  pnext : ∀ {a b A B} {p : Same a b} {q : Same A B} {u v} →
    Paths p q u v → Paths p (ss q) (hsuc u) (hsuc v)
  plimit : ∀ {a b : Cd} {f g : ℕ → Cd} {p : Same a b} {q : ∀ n → Same (f n) (g n)}
    n {u : a ⊲ f n} {v : b ⊲ g n} →
    Paths p (q n) u v → Paths p (ll q) (hlim n u) (hlim n v)

record Moved {A B : Cd} (q : Same A B) {a : Cd} (u : a ⊲ A) : Set where
  constructor moved
  field
    target : Cd
    object-shape : Same a target
    target-path : target ⊲ B
    aligned : Paths object-shape q u target-path
transfer : ∀ {A B a} (q : Same A B) (u : a ⊲ A) → Moved q u
transfer {B = B} q hself = moved B q hself (phere q)
transfer (ss q) (hsuc u) with transfer q u
... | moved b r v h = moved b r (hsuc v) (pnext h)
transfer (ll q) (hlim n u) with transfer (q n) u
... | moved b r v h = moved b r (hlim n v) (plimit n h)
transfer q (hLim {κ = ()} e u)

-- 这里只同步rank和位置；没有声称任意to函数保持坐标关系。
data ClShape {A B : Cd} (q : Same A B) (κ : K (F A)) :
  C.Cl {S⊥} A κ → C.Cl {S⊥} B (map-K q κ) → Set where
  cnew : ∀ {i j pi pj to to′} (p : Same i j) → Paths (ss p) q pi pj →
    ClShape q κ (C.nw i pi to) (C.nw j pj to′)
cl-shape : ∀ {A B} (q : Same A B) κ → ClShape q κ (C.cl A κ) (C.cl B (map-K q κ))
cl-shape zz ()
cl-shape {A = hs A} {B = hs B} (ss q) (inj₁ κ)
  with C.cl A κ | C.cl B (map-K q κ) | cl-shape q κ
... | C.bas () to | v | h
... | C.nw i pi to | C.nw j pj to′ | cnew p h = cnew p (pnext h)
cl-shape (ss q) (inj₂ u) = cnew q (phere (ss q))
cl-shape {A = hl f} {B = hl g} (ll q) (n , κ)
  with C.cl (f n) κ | C.cl (g n) (map-K (q n) κ) | cl-shape (q n) κ
... | C.bas () to | v | h
... | C.nw i pi to | C.nw j pj to′ | cnew p h = cnew p (plimit n h)
cl-shape (oo {κ = ()} q) κ

LegalShape : ∀ {A B : Cd} → Same A B → LgB A → LgB B → Set
LegalShape zz la lb = ⊤
LegalShape (ss q) la lb = LegalShape q la lb
LegalShape (ll q) (sta , la) (stb , lb) =
  (∀ n → Paths (q n) (q (suc n)) (sta n) (stb n)) × (∀ n → LegalShape (q n) (la n) (lb n))
LegalShape (oo {κ = ()} q) la lb

add-paths : ∀ {a b x y A B} (p : Same a b) {q : Same x y} {r : Same A B} {u v} →
  Paths q r u v → Paths (same-add p q) (same-add p r) (⊞-⊲ a u) (⊞-⊲ b v)
add-paths p (phere q) = phere (same-add p q)
add-paths p (pnext h) = pnext (add-paths p h)
add-paths p (plimit n h) = plimit n (add-paths p h)
prefix-paths : ∀ {a b c d} (p : Same a b) (q : Same c d) →
  Paths p (same-add p q) (⊞-fst a c) (⊞-fst b d)
prefix-paths p zz = phere p
prefix-paths p (ss q) = pnext (prefix-paths p q)
prefix-paths p (ll q) = plimit zero (prefix-paths p (q zero))
prefix-paths p (oo {κ = ()} q)

legal-add : ∀ {a b c d} (p : Same a b) (q : Same c d) la lb lc ld →
  LegalShape p la lb → LegalShape q lc ld →
  LegalShape (same-add p q) (Lg-⊞ a c la lc) (Lg-⊞ b d lb ld)
legal-add p zz la lb lc ld hp hq = hp
legal-add p (ss q) la lb lc ld hp hq = legal-add p q la lb lc ld hp hq
legal-add p (ll q) la lb (stc , lc) (std , ld) hp (stq , hq) =
  (λ n → add-paths p (stq n)) , (λ n → legal-add p (q n) la lb (lc n) (ld n) hp (hq n))
legal-add p (oo {κ = ()} q) la lb lc ld hp hq

mutual
  canonical-leg-legal : ∀ {a b} (p : Same a b) →
    LegalShape (leg-same p) (Lg-leg a) (Lg-leg b)
  canonical-leg-legal zz = tt
  canonical-leg-legal (ss p) = canonical-leg-legal p
  canonical-leg-legal (ll p) =
    (λ n → prefix-paths (leg-sums p n) (leg-same (p (suc n)))) , canonical-sums-legal p
  canonical-leg-legal (oo {κ = ()} p)

  canonical-sums-legal : ∀ {f g : ℕ → Cd} (p : ∀ n → Same (f n) (g n)) n →
    LegalShape (leg-sums p n) (Lg-Σ₀ f n) (Lg-Σ₀ g n)
  canonical-sums-legal p zero = canonical-leg-legal (p zero)
  canonical-sums-legal {f} {g} p (suc n) = legal-add
    (leg-sums p n) (leg-same (p (suc n)))
    (Lg-Σ₀ f n) (Lg-Σ₀ g n) (Lg-leg (f (suc n))) (Lg-leg (g (suc n)))
    (canonical-sums-legal p n) (canonical-leg-legal (p (suc n)))
```

canonical-leg-legal实填的是原规范合法性证明的逐点对应，不需要函数
外延或两份LgB证据相等。classify与完整观察是否保持这些关系，仍须
消费此字段逐步证明，不能由路径映射存在就宣称Γ同形相容。
