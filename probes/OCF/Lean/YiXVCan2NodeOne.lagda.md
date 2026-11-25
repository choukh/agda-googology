# YiXV: 层 1 下标上的节点回灌
> 验收文件。档位：编译定理。由 YiXVNum/YiXVNode 推广；完整 SC₁ 与后继余量给出回灌链、两种部分和上界，实际调用在 YiXVCan2Sem。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCan2NodeOne where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import OCF.Lean.YiLegBlock hiding (P)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegFold using (Base)
open import OCF.Lean.YiLSRead using (read)
open import OCF.Lean.YiCeilRead using (plus≼)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l; l≼) renaming (+-mono to +ᵛ)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVRef2 as F
import OCF.Lean.YiXVSim as S
import OCF.Lean.YiXVPlus as P
import OCF.Lean.YiXVAnchor as H
import OCF.Lean.YiXVCan2Core as C
import OCF.Lean.YiXVCan2One as I
import OCF.Lean.YiXVCan2Zero as Z
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)

module Ref (f : R.T₁ → F.T₂) (sc : C.SC₁ f)
  (gb : ∀ Y → O.Gd Y → O.Ω₁ R.≤ₚ Y → C.Gd (f Y)) where
  P : R.T₁ → R.T₁
  P Y = F.ψ₁ (f Y)
  ν : R.T₁ → R.T₀
  ν Y = L.ψ⁰ (f Y)
  module It = I.It f (λ Y g o → I.good₁ (gb Y g o))
  open It public renaming (c to d)
  mo : ∀ {X Y} → O.Gd X → O.Gd Y → O.Ω₁ R.≤ₚ X → X R.≤ₚ Y → P X R.≤ₚ P Y
  mo gx gy o q = I.mono₁ (C.SC₁.mo₁ sc _ _ gx gy o q)
  mo₀ : ∀ {X Y} → O.Gd X → O.Gd Y → O.Ω₁ R.≤ₚ X → X R.≤ₚ Y → ν X ≼ ν Y
  mo₀ gx gy o q = Z.mono₀ (C.SC₁.mo₁ sc _ _ gx gy o q)
  dbl : ∀ n → L.suc (d n) R.≤ₚ d (suc n) → (d (suc n) L.+ d (suc n)) R.≤ₚ d (suc (suc n))
  dbl n q = R.trans (R.≤l 2 (O.reflₚ (O.Gd-+ (good (suc n)) (good (suc n)))))
    (R.trans (I.mono₁ (C.SC₁.db₁ sc (d n) (good n) (floor n)))
      (mo (O.gs (good n)) (good (suc n)) (R.ws (floor n)) q))
  incr : ∀ n → L.suc (d n) R.≤ₚ d (suc n)
  incr zero = R.trans (I.succ-step O.Gd-Ω O.pos-Ω) (I.mono₁ (C.SC₁.po₁ sc))
  incr (suc n) = R.trans (O.+ₚ (O.reflₚ (good (suc n))) (R.trans O.pos-Ω (floor (suc n)))) (dbl n (incr n))
  le : ∀ n → d n R.≤ₚ d (suc n)
  le n = R.trans (R.ws (O.reflₚ (good n))) (incr n)
  dbl₀ : ∀ n → (ν (d n) L.+ ν (d n)) ≼ ν (d (suc n))
  dbl₀ n = ≼-trans (≼l 2 (≼-refl _))
    (≼-trans (Z.mono₀ (C.SC₁.db₁ sc (d n) (good n) (floor n)))
      (mo₀ (O.gs (good n)) (good (suc n)) (R.ws (floor n)) (incr n)))
  idx : ℕ → ℕ
  idx zero = 1
  idx (suc n) = suc (suc (idx n))

module Chain (B : Base (suc zero)) (f : R.T₁ → F.T₂) (sc : C.SC₁ f)
  (gb : ∀ Y → O.Gd Y → O.Ω₁ R.≤ₚ Y → C.Gd (f Y))
  (gk : Tr (suc zero) → Tr (suc zero))
  (zeroU : S.Sim.U B zero O.Ω₁) (zeroC : H.Anchor.Closed B zeroU)
  (Hk : ∀ a X Y → O.Gd X → O.Gd Y → O.Ω₁ R.≤ₚ Y →
    (h : S.Sim.U B a X) → H.Anchor.Closed B h → L.suc X R.≤ₚ Y →
    Σ (S.Sim.U B (gk a) (F.ψ₁ (f Y))) (H.Anchor.Closed B)) where
  module U = S.Sim B
  module HC = H.Anchor B
  open Ref f sc gb
  c : ℕ → Tr (suc zero)
  c = iter gk zero
  Bounds : ℕ → Set
  Bounds n = Σ R.T₁ λ X → O.Gd X × (Σ (U.U (c n) X) HC.Closed) × (L.suc X R.≤ₚ d (idx n))
  bounds : ∀ n → Bounds n
  bounds zero = O.Ω₁ , O.Gd-Ω , (zeroU , zeroC) , incr 0
  bounds (suc n) with bounds n
  ... | X , gx , (h , hc) , q = d (suc (idx n)) , good (suc (idx n)) , Hk (c n) X (d (idx n)) gx (good (idx n)) (floor (idx n)) h hc q , incr (suc (idx n))

  module Ground (gm : Tr (suc zero) → Tr zero)
    (Hm : ∀ a X Y → O.Gd X → O.Gd Y → O.Ω₁ R.≤ₚ Y → (h : U.U a X) → HC.Closed h →
      L.suc X R.≤ₚ Y → read (gm a) ≼ ν Y) where
    F : ℕ → Tr zero
    F n = gm (c n)
    rows : ∀ n → read (F n) ≼ ν (d (idx n))
    rows n with bounds n
    ... | X , gx , (h , hc) , q = Hm (c n) X (d (idx n)) gx (good (idx n)) (floor (idx n)) h hc q
    sums : ∀ n → read (cum F n) ≼ ν (d (suc (idx n)))
    sums zero = ≼-trans (rows 0) (mo₀ (good 1) (good 2) (floor 1) (le 1))
    sums (suc n) = ≼-trans (plus≼ (cum F n) (F (suc n))
      (≼-trans (sums n) (mo₀ (good (suc (idx n))) (good (suc (suc (idx n)))) (floor (suc (idx n))) (le (suc (idx n))))) (rows (suc n)))
      (dbl₀ (idx (suc n)))
    result : ∀ nz → read (limc F nz) ≼ L.lim (λ n → ν (d n))
    result nz = l≼ (λ n → ≼l (suc (idx n)) (sums n))

  module Slot (gm : Tr (suc zero) → Tr (suc zero))
    (Hm : ∀ a X Y → O.Gd X → O.Gd Y → O.Ω₁ R.≤ₚ Y → (h : U.U a X) → HC.Closed h →
      L.suc X R.≤ₚ Y → Σ (U.U (gm a) (P Y)) HC.Closed) where
    module Cl = P.Closure B
    F : ℕ → Tr (suc zero)
    F n = gm (c n)
    Rows : ℕ → Set
    Rows n = Σ (U.U (F n) (d (suc (idx n)))) HC.Closed
    rows : ∀ n → Rows n
    rows n with bounds n
    ... | X , gx , (h , hc) , q = Hm (c n) X (d (idx n)) gx (good (idx n)) (floor (idx n)) h hc q
    Sums : ℕ → Set
    Sums n = Σ (U.U (cum F n) (d (suc (suc (idx n))))) HC.Closed
    sums : ∀ n → Sums n
    sums zero = U.uw (good 2) (proj₁ (rows 0)) (le 2) , proj₂ (rows 0)
    sums (suc n) = U.uw (O.Gd-+ (good t) (good t))
      (Cl.plus-comp (good t) old (good t) new) (dbl k (incr k)) ,
      HC.plus-closed (good t) old (proj₂ (sums n)) (good t) new (proj₂ (rows (suc n)))
      where
      k = suc (suc (idx n))
      t = suc k
      old = U.uw (good k) (proj₁ (sums n)) (le k)
      new = proj₁ (rows (suc n))
    result : ∀ nz → Σ (U.U (limc F nz) (L.lim (λ n → P (d n)))) HC.Closed
    result nz = U.ul (λ n → U.uw (good (suc (suc (idx n)))) (proj₁ (sums n))
      (R.≤l (suc (idx n)) (O.reflₚ (good (suc (suc (idx n))))))) , λ n → proj₂ (sums n)
```
