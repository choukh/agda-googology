# 实际继承槽反复回读所能达到的上界

第四层，无条件。每轮从正塔的一次真实询问选一个先前标准层的槽，按该层标准环境折回零层，以完整返回作下一轮起点。从 1 出发，这些返回的上确界达到标准塔极限 K，当且仅当所访问的外塔编号无界。槽与询问可随轮次变化。[实际槽](Reports-2026-11-19/attachments/B27UActualPorts.agda.txt)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4ReturnBound where

open import Data.Nat.Base as N using (ℕ; zero; suc; _≤_; _<_; _⊔_; z≤n; s≤s)
import Data.Nat.Properties as NP
open import Data.Unit.Base using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality using (sym; subst)
import W4Block as W
import W4Fold as F
import W4Path as P
import W4Ops as O
open import WVOne using (T₀; 𝟏; read)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≈ᵛ_; _≼_; l≼; ≼l; ≼lim⁻; s≼s; ≼-trans; ≼-suc; ≼-refl)
open import OCF.Align.TightValBase using (s≼-irrefl)
import B12Strict as Strict
import B18Product as M
import B18TowerEmb as Emb
import B19IdealArithmetic as Ar
import B19PathValue as Scale
import B14PathHeight as PH
import B25Return as Ord
import B27UActualPorts as Real
import B27UEpsilon as Hull
import B20StandardInside as Std
import B21StandardShape as Rise
import B22MovingIndex as E
import B22TowerCut as K

positive : ∀ n → 𝟏 ≼ Std.std n
positive n = Strict.strict (proj₂ (Emb.standard n))

record Port : Set where
  constructor port
  field
    n j m : ℕ
    w : W.tw m W.≤ Real.At.ℓ n j
    old : m ≤ n
open Port

module Call (d : Port) where
  module Q = Real.At.Port (n d) (j d) (m d) (w d)
  level = W.tw (m d)
  slot = Real.At.bs (n d) (j d) level (w d)
  run : O.Tr⁺ W.zero → O.Tr⁺ W.zero
  run β = F.ψ level (P.Ok-tw (m d)) (F.B₀ level) W.zero (P.z≤ level) β (proj₁ slot)

  scale : ∀ β → read (proj₁ (run β)) ≈ᵛ (read (proj₁ β) M.· Q.val)
  scale β = Scale.At.scale level (P.Ok-tw (m d)) (F.B₀ level) (proj₁ slot) (PH.standard level) β

  floor : Std.std (n d) ≼ Q.val
  floor = subst (Std.std (n d) ≼_) (sym Q.same)
    (≼-trans {b = Ar.norm (Std.std (n d))} (Ar.up (Std.std (n d)))
      (≼-trans {b = Q.Slots.val (n d) M.· Ar.norm (Std.std (n d))}
        (M.pad (≼-trans {b = Std.std (m d)} (positive (m d)) (Q.Slots.lower (n d))) (Ar.norm (Std.std (n d))))
        (proj₂ (Q.Slots.append (n d)))))

  slot-in : ∀ b → n d ≤ b → Hull.At.In (Std.std b) Q.val
  slot-in b nb = subst (Hull.At.In (Std.std b)) (sym Q.same)
    (Q.Slots.Limit.within b (NP.≤-trans (old d) nb) (suc (n d)) (s≤s nb))

module Chain (pick : ℕ → Port) where
  module C (i : ℕ) = Call (pick i)
  tower = λ i → n (pick i)
  returned : ℕ → O.Tr⁺ W.zero
  returned zero = O.Ωt W.zero
  returned (suc i) = C.run i (returned i)
  val = λ i → read (proj₁ (returned i))
  limit : T₀
  limit = L.lim val

  paid : ∀ i → Std.std (tower i) ≼ val (suc i)
  paid i = ≼-trans {b = C.Q.val i} (C.floor i) (≼-trans {b = val i M.· C.Q.val i}
    (M.pad (Strict.strict (proj₂ (returned i))) (C.Q.val i)) (proj₂ (C.scale i (returned i))))

  History : ℕ → ℕ → Set
  History b zero = ⊤
  History b (suc i) = History b i × tower i ≤ b

  raise : ∀ {a b} i → a ≤ b → History a i → History b i
  raise zero ab h = tt
  raise (suc i) ab (h , v) = raise i ab h , NP.≤-trans v ab

  budget : ∀ b i → History b i → Hull.At.In (Std.std b) (val i)
  budget b zero h = Hull.At.down (Std.std b) {𝟏} {Std.std b} (positive b) (Hull.At.seed (Std.std b))
  budget b (suc i) (h , v) = Hull.At.down (Std.std b) {val (suc i)} {val i M.· C.Q.val i}
    (proj₁ (C.scale i (returned i))) (Hull.At.mulC (Std.std b) {val i} {C.Q.val i} (budget b i h) (C.slot-in i b v))

  finite : ∀ i → Σ ℕ λ b → History b i
  finite zero = 0 , tt
  finite (suc i) with finite i
  ... | b , h = b ⊔ tower i , raise i (NP.m≤m⊔n b (tower i)) h , NP.m≤n⊔m b (tower i)

  escape : ∀ b i → History b i ⊎ Σ ℕ (λ j → b < tower j)
  escape b zero = inj₁ tt
  escape b (suc i) with tower i NP.≤? b | escape b i
  ... | no gt | _ = inj₂ (i , NP.≰⇒> gt)
  ... | yes h | inj₁ prior = inj₁ (prior , h)
  ... | yes _ | inj₂ w = inj₂ w

  step-cap : ∀ b i → History b i → L.suc (val i) ≼ E.above (Std.std b)
  step-cap b i h = Hull.At.finite (Std.std b) {val i} (budget b i h)

  bounded : ∀ b → (∀ i → tower i ≤ b) → limit ≼ E.above (Std.std b)
  bounded b h = l≼ λ i → ≼-trans {b = L.suc (val i)} (≼-suc (≼-refl _)) (step-cap b i (hist i))
    where
    hist : ∀ i → History b i
    hist zero = tt
    hist (suc i) = hist i , h i

  proper : ∀ b → (∀ i → tower i ≤ b) → L.suc limit ≼ K.cut
  proper b h = ≼-trans {b = L.suc (E.above (Std.std b))} (s≼s (bounded b h))
    (K.inside {x = Std.std b} (≼l {f = Std.std} (suc b) (Rise.rise b)))

  upper : limit ≼ K.cut
  upper = l≼ each
    where
    each : ∀ i → val i ≼ K.cut
    each i with finite i
    ... | b , h = ≼l {f = Std.std} (suc (suc (suc b))) (≼-trans {b = L.suc (val i)}
      (≼-suc (≼-refl _)) (≼-trans {b = E.above (Std.std b)} (step-cap b i h) (K.up b)))

  Unbounded = ∀ b → Σ ℕ λ j → b < tower j
  sufficient : Unbounded → K.cut ≼ limit
  sufficient co = l≼ λ b → let j , d = co b in ≼l {f = val} (suc j)
    (≼-trans {b = Std.std (tower j)} (Ord.up (NP.<⇒≤ d)) (paid j))

  necessary : K.cut ≼ limit → Unbounded
  necessary h b with ≼lim⁻ {a = Std.std cap} {f = val} (≼-trans {b = K.cut} (≼l {f = Std.std} (suc cap) (Rise.rise cap)) h)
    where cap = suc (suc (suc b))
  ... | i , hi with escape b i
  ...   | inj₂ w = w
  ...   | inj₁ past = ⊥-elim (s≼-irrefl (Std.std (suc (suc (suc b)))) (≼-trans {b = val i} hi
    (≼-trans {b = L.suc (val i)} (≼-suc (≼-refl _)) (≼-trans {b = E.above (Std.std b)} (step-cap b i past) (K.up b)))))

bottom : (n j : ℕ) → Port
bottom n j = port n j 0 (P.z≤ (Real.At.ℓ n j)) z≤n

module Bottom (query : ℕ → ℕ) where
  module A = Chain (λ n → bottom n (query n))
  exact : A.limit ≈ᵛ K.cut
  exact = A.upper , A.sufficient (λ b → suc b , NP.≤-refl)
```
