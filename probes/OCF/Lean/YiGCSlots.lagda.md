# 精确对应下的保留判定规格
验收文件；NoΩ 域的 kp/kp⁼：保留时槽位与关系相配，默认时参照层号不低于目标。
来源：YiLSFold 的 Keep/kpF/relFrom；保持现有 kp 的每一行，函数性来自 YiGCCorr。
起点 START 采用 Level 的 Ω，在 ℕ 极限处按孩子的累计极限构造。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGCSlots where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst)
open import OCF.Lean.YiRWBlock renaming (L to LF)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath hiding (wk; emb) renaming (psh to pshP)
import OCF.Lean.YiRWFold as F
open import OCF.Lean.YiNRHit using (NoΩ; chN)
open import OCF.Lean.YiFPFrames using (Dc; Ctx; []; _∷_; fr; kid; asChild)
open import OCF.Lean.YiGCCorr
open import OCF.Lean.YiGCRel
open import OCF.Lean.YiKVRel using (_⊴_; ⊴r; ⊴◃)
import OCF.Align.Level as L

psh-at : ∀ {k a} (v : k ≤ a) t → proj₁ (sl⁼ a (pshP v t)) ≡ proj₁ (sl⁼ k t)
psh-at self t = refl
psh-at (inc c v) t = psh-at v t
psh-at {a = nd s h} (inu vs) t = psh-at (vs (c₀ s)) t
psh-at (ink v) t = psh-at v t
psh-rel : ∀ {k a} (v : k ≤ a) t {i} {y : L.Ordᶜ i} {z : Br⁼ a (pshP v t)}
  → RelP⁼ a (pshP v t) y z → RelP⁼ k t y (pshBr v t z)
psh-rel self t r = r
psh-rel (inc c v) t r = psh-rel v t r
psh-rel {a = nd s h} (inu vs) t r = psh-rel (vs (c₀ s)) t r
psh-rel (ink v) t r = psh-rel v t r
record Kept (lv : LF) (X : Set) (RP : ∀ {i} → L.Ordᶜ i → X → Set) (j : LF) (q : Pos j) (cv : Br j q → X) : Set where
  field
    lev : at j q ≡ lv
    conv : ∀ {i} {y : L.Ordᶜ i} {c} → RelP j q y c → RP y (cv c)
    below : ∀ {i′ i} → Corr i′ lv → Corr i j → i′ L.≺ᴵ i
Dflt : LF → LF → Set
Dflt lv j = ∀ {i′ i} → Corr i′ lv → Corr i j → ¬ (i′ L.≺ᴵ i)
Spec : (lv : LF) (X : Set) (RP : ∀ {i} → L.Ordᶜ i → X → Set) (j : LF) {x₀ : X} → F.Keep j X x₀ → Set
Spec lv X RP j (just (q , cv , e)) = Kept lv X RP j q cv
Spec lv X RP j nothing = Dflt lv j
keep-psh : ∀ {k a} (v : k ≤ a) t {j q} {cv : Br j q → Br⁼ a (pshP v t)}
  → Kept (proj₁ (sl⁼ a (pshP v t))) (Br⁼ a (pshP v t)) (RelP⁼ a (pshP v t)) j q cv
  → Kept (proj₁ (sl⁼ k t)) (Br⁼ k t) (RelP⁼ k t) j q (λ z → pshBr v t (cv z))
keep-psh v t kf = record
  { lev = trans (Kept.lev kf) (psh-at v t)
  ; conv = λ r → psh-rel v t (Kept.conv kf r)
  ; below = λ ci′ ci → Kept.below kf (subst (Corr _) (sym (psh-at v t)) ci′) ci }
map-spec : ∀ {k a} (v : k ≤ a) t {j} (m : F.Keep j (Br⁼ a (pshP v t)) (bz⁼ a (pshP v t)))
  → Spec (proj₁ (sl⁼ a (pshP v t))) _ (RelP⁼ a (pshP v t)) j m
  → Spec (proj₁ (sl⁼ k t)) _ (RelP⁼ k t) j (F.mapK (pshBr v t) (pshFirst v t) m)
map-spec v t (just (q , cv , e)) kf = keep-psh v t kf
map-spec v t nothing df ci′ ci = df (subst (Corr _) (sym (psh-at v t)) ci′) ci
mutual
  kpSpec : ∀ {a} (ns : NoΩ a) (o : Ok a) p {j} (w : j ≤ a) → Spec (at a p) _ (RelP a p) j (F.kp a o p w)
  kpSpec ns o p self = record { lev = refl ; conv = λ r → r ; below = λ cj ci → POS ns p cj ci }
  kpSpec {nd s h} ns (os , oc) (inj₂ (c , t)) (inu ws) = kpSpec⁼ (chN s h ns c) (oc c) t (ws c)
  kpSpec {nd sS h} ns (os , oc) (inj₂ (tt , t)) (inc tt w) = kpSpec⁼ (ns tt) (oc tt) t w
  kpSpec {nd sL g} ns (os , oc) (inj₂ (m , t)) (inc n w) = cW-ind (Spec _ _ (RelP⁼ (g m) t) _) (way g os m n)
    (λ v → map-spec v t (F.kp⁼ (g n) (oc n) (pshP v t) w) (kpSpec⁼ (ns n) (oc n) (pshP v t) w))
    (λ v → kpSpec⁼ (ns m) (oc m) t (w ∙ v))
  kpSpec {nd (sΩ k) h} () o p w
  kpSpec⁼ : ∀ {a} (ns : NoΩ a) (o : Ok a) t {j} (w : j ≤ a) → Spec (proj₁ (sl⁼ a t)) _ (RelP⁼ a t) j (F.kp⁼ a o t w)
  kpSpec⁼ ns o (inj₁ tt) w ci′ ci = notBelow w ns ci ci′
  kpSpec⁼ ns o (inj₂ p) w = kpSpec ns o p w

nodeCase : ∀ {a} (ns : NoΩ a) (o : Ok a) p {j} (w : j ≤ a)
  (G : Br a p → Tr⁺ j) (s : Br a p → Br a p) (R : Tr j → Set)
  → (∀ q cv → Kept (at a p) _ (RelP a p) j q cv → R (Ω q (λ z → proj₁ (G (cv z)))))
  → (Dflt (at a p) j → R (proj₁ (limc⁺ (λ n → G (iter s (fromBr a p zero) n)))) )
  → R (proj₁ (F.node⁺ (F.kp a o p w) G s))
nodeCase {a} ns o p {j} w G s R hk hd = choose (F.kp a o p w) (kpSpec ns o p w)
  where
  choose : (m : F.Keep j (Br a p) (fromBr a p zero)) → Spec (at a p) _ (RelP a p) j m → R (proj₁ (F.node⁺ m G s))
  choose (just (q , cv , e)) sp = hk q cv sp
  choose nothing sp = hd sp

at-mv : ∀ {j a} (d : Dn j a) p → at j (mv d p) ≡ at a p
at-mv stop p = refl
at-mv (down d c) p = at-mv d (inj₂ (c , inj₂ p))
mvRel : ∀ {j a} (d : Dn j a) p {i} {y : L.Ordᶜ i} {z : Br j (mv d p)} → RelP j (mv d p) y z → RelP a p y (mvBr d p z)
mvRel stop p r = r
mvRel (down d c) p r = mvRel d (inj₂ (c , inj₂ p)) r
toSl : ∀ (a : LF) {b} (d : Dc a b) p {i} {y : L.Ordᶜ i} {c} → RelP b p y c → SlOf a d p y c
toSl a [] p r = r
toSl zero (() ∷ d) p r
toSl (nd s h) (c ∷ d) p r = toSl (h c) d p r
mutual
  relFrom : ∀ (a : LF) (p : Pos a) {i} {y : L.Ordᶜ i} {c} → Rel (at a p) y c → RelP a p y (fromBr a p c)
  relFrom (nd s h) (inj₂ (c , t)) r = relFrom⁼ (h c) t r
  relFrom (nd (sΩ k) h) (inj₁ t) r = relFrom⁼ k t r
  relFrom⁼ : ∀ (a : LF) t {i} {y : L.Ordᶜ i} {c} → Rel (proj₁ (sl⁼ a t)) y c → RelP⁼ a t y (proj₂ (sl⁼ a t) c)
  relFrom⁼ a (inj₁ tt) r = r
  relFrom⁼ a (inj₂ p) r = relFrom a p r
Rel-⊴ : ∀ {j k} {X : L.Ordᶜ k} {t t′ : Tr j} → Rel j X t → t ⊴ t′ → Rel j X t′
Rel-⊴ r ⊴r = r
Rel-⊴ r (⊴◃ d) = wk r d
START : ∀ {a i} → NoΩ a → Corr i a → Rel a (L.Ω i) (proj₁ (Ωt a))
START ns cz = ss zr
START ns (cs c) = nodeR c (λ y z sl → ur (psh {Γ = []} (wk (emb zero tt sl) ◃s)))
START {a = nd sL g} ns (cl c st) = ll (λ n → ul n (wk (go n (c n)) (◃l n)))
  where
  go : ∀ n {i} → Corr i (g n) → Rel (nd sL g) (L.Ω i) (cum (λ m → proj₁ (upz m (Ωt (g m)))) n)
  go zero ci = psh {Γ = []} (emb zero zero (START (ns zero) ci))
  go (suc n) ci = psh {Γ = []} (emb (cum (λ m → proj₁ (upz m (Ωt (g m)))) n) (suc n) (START (ns (suc n)) ci))
```
