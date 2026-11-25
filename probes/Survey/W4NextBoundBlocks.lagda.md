# 首座完整塔中定值的共尾地址块

第四层，取节点使用排中律。对每个严格低于树根的值 q，可选一个非空地址到达恰值 q 的实际节点。改变第一步的副本号给出共尾多块，每一块包括该地址的所有合法后续。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4NextBoundBlocks where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Maybe.Base using (just; nothing)
open import Data.Bool.Base using (true)
open import Data.Empty using (⊥)
open import Induction.WellFounded using (Acc; acc; acc-inverse)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRVLevel using (LEM)
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans; ≼-refl; ≼l; s≼s)
import OCF.Align.Level as L
open import WVOne using (T₀)
import Survey.W4PTOAddresses as A
import B17ValueDich as C
import Survey.W4PTODescent as Descent
import B26Names as N
import B19IdealPowers as Powers
import B22MovingIndex as E
import B27UEpsilon as Hull
import B29SFirst as FirstUnits
import B29SCases as FirstTower
open import OCF.Align.TightValBase using (s≼-irrefl)
import B12BtboCut as Cut
import Survey.W4FixedDepth as Depth
import Survey.W4FiniteOmegaCut as Finite

_≺_ : T₀ → T₀ → Set
y ≺ x = A.Hop x y

accessible : ∀ x → Acc _≺_ x
accessible L.zero = acc λ ()
accessible (L.suc x) = acc λ { A.pred → accessible x }
accessible (L.lim f) = acc λ { (A.via i e) → acc-inverse (accessible (f i)) e }

replay : ∀ x ps {z} → A.follow x ps ≡ just z → ∀ tail →
  A.follow x (ps ++ tail) ≡ A.follow z tail
replay x [] refl tail = refl
replay x ((ns , i) ∷ ps) done tail with A.land x ns
... | just y = replay y ps done tail
... | nothing with done
...   | ()

record AtRank (x q : T₀) : Set where
  constructor arrived
  field
    path : A.Trail
    node : T₀
    reached : A.follow x path ≡ just node
    exact : node ≈ᵛ q

record Blocks (x q : T₀) : Set where
  constructor blocks
  field
    ticket : Data.List.Base.List ℕ
    rest : A.Trail
    node : T₀
    reached : ∀ i → A.follow x ((ticket , i) ∷ rest) ≡ just node
    exact : node ≈ᵛ q

  prefix : ℕ → A.Trail
  prefix i = (ticket , i) ∷ rest
  valid : ∀ i → A.member x (just (prefix i)) ≡ true
  valid i rewrite reached i = refl
  tail : ∀ i ps → A.member x (just (prefix i ++ ps)) ≡ A.inhabited (A.follow node ps)
  tail i ps rewrite replay x (prefix i) (reached i) ps = refl

module Select (lem : LEM) where
  find : ∀ {x} q → q ≼ x → Acc _≺_ x → AtRank x q
  find {x} q lo (acc rec) with C.Classical.compare lem x q
  ... | inj₁ hi = arrived [] x refl (hi , lo)
  ... | inj₂ strict with A.pick {x = q} {y = x} strict
  ...   | y , e , fits with find q fits (rec e)
  ...     | arrived ps z done same = arrived ((A.route e , 0) ∷ ps) z through same
    where
    through : A.follow x ((A.route e , 0) ∷ ps) ≡ just z
    through rewrite A.exact e = done

  select : ∀ x q → L.suc q ≼ x → Blocks x q
  select x q strict with A.pick {x = q} {y = x} strict
  ... | y , e , fits with find q fits (accessible y)
  ...   | arrived ps z done same = blocks (A.route e) ps z through same
    where
    through : ∀ i → A.follow x ((A.route e , i) ∷ ps) ≡ just z
    through i rewrite A.exact e = done

  module First = Descent.DepthTwo
  actual : ∀ q → q ≼ N.value First.beta → Blocks First.root q
  actual q lo = select First.root q (≼-trans {b = L.suc (N.value First.beta)} (s≼s lo) First.strict)

beta = N.value Descent.DepthTwo.beta

ceiling : ∀ q → q ≼ beta → L.suc (E.step (L.suc q)) ≼ Cut.finite 3
ceiling q low = ≼-trans {b = L.suc (E.above beta)}
  (s≼s (≼l {f = E.steps beta} 1 (Powers.expo Powers.omega-pos (s≼s low))))
  (≼-trans {b = L.suc (Finite.epsilon-orbit beta)} (s≼s (≼l 1 (≼-refl (E.above beta))))
    (Finite.orbit-inside 1 beta (Depth.upper 1)))

local-room : E.above beta ≼ FirstTower.Y₁
local-room = ≼-trans {b = FirstUnits.S}
  (E.least beta FirstUnits.S
    (≼-trans {b = FirstTower.Y₁} Descent.DepthTwo.strict FirstTower.upper) (proj₁ FirstUnits.fixed))
  FirstTower.lower

proper : ∀ q → q ≼ beta → L.suc (E.step (L.suc q)) ≼ FirstTower.Y₁
proper q lo = ≼-trans {b = E.above beta}
  (B.finite {E.step (L.suc q)} (B.expC {L.suc q} (B.sucC {q} (B.down {q} {beta} lo B.seed)))) local-room
  where module B = Hull.At beta

misses : ∀ q → q ≼ beta → FirstTower.Y₁ ≼ E.step (L.suc q) → ⊥
misses q lo covers = s≼-irrefl _ (≼-trans {b = FirstTower.Y₁} (proper q lo) covers)
```

固定 q 和 `actual` 选出的有限路径。首键为 2 的固定幂乘 2i+1，随 i 严格递增且无界。所得块两两不交，且在首座塔的地址序中共尾。`tail` 允许块内的每条后续路径。由地址序型计算，q>0 时每块的序型为 ω^q+1，q=0 时为 1。因此按 i 合并这些块所得子序的序型在两种情形下均为 **ω^(q+1)**。当 q≤β=D₀D₂²0 时，`ceiling` 给出统一严格上界 ψ₀(Ω₃)。选定一个 q 后只须检查有限前缀及原塔地址判定，所得子序有递归呈现。对 q 的选点用到了排中律。[地址序型](W4PTOAddresses.lagda.md)

**经典纸面推论。** 对上述每个固定子序，序型界保证它可严格保序嵌入原记号 ψ₀(Ω₃) 的初段。这一嵌入的存在性是一条由两边序型独立证真的 Σ¹₁ 句。在 ACA₀ 中，有了嵌入和包含该初段的原塔公理，任何假想降链都会送到原塔降链。因此 Tᴿ 配合该真辅助句能导出此子序的良序性。[原塔公理](EboPTOSegments.lagda.md)
