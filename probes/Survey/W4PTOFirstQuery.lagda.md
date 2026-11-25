# 固定塔的对角迭代在首个询问中的位置

第四层，无条件。$G(1)$ 是 $ID_2$ 深度 3 第零枝的首个询问。将任一正份数作前缀，一个更大的固定份数容下以该前缀为界的全部对角迭代，时钟可取到上方首个 ε 点。起点取旧见证的起点 $D$ 时，这一整段在 $G(1)$ 中有严格余量。[固定塔定理](W4PTOClock.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module Survey.W4PTOFirstQuery where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([]; _∷_)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l; l≼; s≼s; ≅→≼)
import OCF.Align.BTBOValUp as U
import OCF.Align.BTBOValDn as Dn
open import WVOne using (T₀)
open import YiLAB7Replay using (Ω₂ᴸ)
import YiLAB10Src as Y
import B12LimitSrc as A
import B12Omega3Ref as R
import B12Omega3Cuts as Cut
import B13Target as P
import B14RefFixed as K
import B14RefGain as Path
import B15RefSource as One
import B17RefAllSource as Src
import B19OldSource as Old
import B19RowSecond as Coeff
import B21TowerGrowth as Tower
import B22RowSource as Tail
import B22MovingIndex as E
import B22TowerCut as Towers
import B23RShare as First
import B23NFirst as Ask
import B24ROrbit as Seed
import B24RExit as Exit
import B24AQueries as Q
import B25ACap as Start
import B25ARank as X
import B25AOrbit as Orbit
import B20StandardInside as Std
import Survey.W4PTOClock as C

copies : ∀ n → U.Mh Y.a (Y.ll n)
copies zero = Y.up-rel 0
copies (suc n) = U.M-add-r {σ = R.idσ} Ω₂ᴸ (copies n)

module Part (n : ℕ) where
  q = P.pass (Y.ll n)
  rq = P.pass-pres (Y.regular n)
  prefix = Exit.passed (A.aligned (Y.up-rel n) (Y.dn-rel n) (Y.regular n))
  right = λ a → q L.+ L.up L.zero (K.collapse a)
  reg : ∀ {a : A.Lev₂} → a L.≅ a → right a L.≅ right a
  reg d = L.add-≅ {σ = L.suc} {σ′ = L.suc} rq (K.pres d)

  compare : L.ψ⁰ (Tower.add q) ≼ L.ψ⁰ (right q)
  compare = Cut.sandwich {s = Src.pass (Y.ss n) Src.S.+ Src.S.↑ Src.B.zero
      (Src.S.ψ< {i = One.one} Src.B.zero Old.src-prefix)}
    (Dn.Dn-add {σ = L.suc} (A.Aligned.dn prefix) (Dn.Dn-↑ Src.B.zero
      (Dn.Dn-ψ {i = One.one} (L.≅ᴵ-refl _) L.zero R.idσ Src.B.zero (A.Aligned.dn Old.prefix))))
    (U.M-add {σ = L.suc} (A.Aligned.up prefix) (U.M-↑ Src.B.zero
      (U.M-ψ {i = One.one} (L.≅ᴵ-refl _) L.zero R.idσ Src.B.zero (Src.pass-up 1 (copies n)))))
    (reg {a = Coeff.p} (A.Aligned.regular Old.prefix)) (reg {a = q} rq)

  next : L.ψ⁰ (Tower.add q) ≼ Q.recorded (suc n)
  next = ≼-trans {b = L.ψ⁰ (right q)} compare
    (≼-trans {b = L.ψ⁰ (q L.+ Ω₂ᴸ)} (≼l 1 (≼l 0 (≼l 1 (≼-refl _))))
      (≼-trans {b = Tail.Tail.row q rq} (≼l 1 (≼-refl _))
        (≼-trans {b = L.ψ⁰ (q L.+ Coeff.p)} (Tail.Tail.lower q rq)
          (≼-trans {b = L.ψ⁰ (q L.+ q)} (Q.lead n q)
            (≼l 0 (≼l 0 (≼l 2 (≼-refl _))))))))

  module Clock = C.Clocks q rq
  batch : ∀ x → x ≼ Q.recorded n → ∀ t → Clock.H.In t →
    C.run x t ≼ Q.recorded (suc n)
  batch x h t e = ≼-trans {b = L.ψ⁰ (Tower.add q)}
    (Clock.P.collect x h t (Clock.room t e)) next

  endpoint : ∀ x → x ≼ Q.recorded n → C.run x (E.above (Q.recorded n)) ≼ Q.recorded (suc n)
  endpoint x h = l≼ λ j → batch x h (E.steps (Q.recorded n) j) (Clock.H.point j)

  margin : L.suc (Q.recorded n) ≼ First.oneStep
  margin = ≼l (suc (suc n)) (≼-trans {b = Q.recorded (suc n)} (Q.rise n)
    (≅→≼ (L.ψ⁰-≅ (P.pass-pres (L.≅-sym (R.matches (suc n)))))))

module Two = Part 1

local : ∀ t → C.Actual.H.In t → C.run Seed.D t ≼ Q.recorded 2
local t h = Two.batch Seed.D Start.start t (Two.Clock.small t
  (≼-trans {b = E.above (L.ψ⁰ X.p)} (C.Actual.H.finite {t} h)
    (Towers.advance {L.ψ⁰ X.p} {Q.recorded 1}
      (≼-trans {b = Seed.D} (≅→≼ (L.≅-sym Exit.input)) Start.start))))

strict : ∀ t → C.Actual.H.In t → L.suc (C.run Seed.D t) ≼ First.oneStep
strict t h = ≼-trans {b = L.suc (Q.recorded 2)} (s≼s (local t h)) (Part.margin 2)

old-strict : L.suc Orbit.whole ≼ First.oneStep
old-strict = ≼-trans {b = L.suc (C.run Seed.D L.ωᶜ)}
  (s≼s C.whole-clock) (strict L.ωᶜ C.Actual.omega)
```

严格余量对整个族成立。即使自由选择可数多次允许的时钟再取上确界，也跨不过这个询问。特别可在候选的第 4 座标准塔里用到 ε 端点本身。

```agda
module Family (f : ℕ → T₀) (small : ∀ j → C.Actual.H.In (f j)) where
  value : T₀
  value = L.lim (λ j → C.run Seed.D (f j))
  paid : value ≼ Std.std 4
  paid = l≼ λ j → C.in-four (f j) (small j)
  below : L.suc value ≼ First.oneStep
  below = ≼-trans {b = L.suc (Q.recorded 2)}
    (s≼s (l≼ λ j → local (f j) (small j))) (Part.margin 2)

module End = Family (E.steps (L.ψ⁰ X.p)) C.Actual.H.point
paid-end : C.run Seed.D (E.above (L.ψ⁰ X.p)) ≼ Std.std 4
paid-end = End.paid
below-end : L.suc (C.run Seed.D (E.above (L.ψ⁰ X.p))) ≼ First.oneStep
below-end = End.below
```

在原 ψ₀(Ω₃) 的基本列中按从零起算的地址写出已越过的位置。前三步抵达首个询问，后两步抵达实际迭代的起点。

```agda
query-address : Path.along (2 ∷ 0 ∷ 0 ∷ []) (L.ψ⁰ R.Ω₃) L.≅ First.oneStep
query-address = Ask.asked

start-address : Path.along (2 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ []) (L.ψ⁰ R.Ω₃) L.≅ Seed.D
start-address = Src.part (Src.part query-address 2) 0

past-address : L.suc (Path.along (2 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ []) (L.ψ⁰ R.Ω₃)) ≼ Std.std 4
past-address = ≼-trans {b = L.suc Seed.D} (s≼s (≅→≼ start-address))
  (≼-trans {b = Orbit.whole} (Orbit.proper 0)
    (≼-trans {b = L.suc Orbit.whole} (OCF.Align.Value.≼-suc (≼-refl _)) C.strict-in-four))
```

沿同一地址计算本地标准项，起点为 $\psi_0(\psi_2(\Omega_2+\Omega_1))$，询问为 $\psi_0(\psi_2(\psi_2(1)))$。下界可对该起点的任何遗传基本列证书使用。

```agda
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.EboLeanDef using (T; ψ; natT; cof; cω; fsn; HC)
open import OCF.Lean.YiRefTw2 using (Rt; tree-≼)
import Survey.EboPTOFinite as B
import Survey.W4PTOGamma as Gamma
import B28FFinite as Finite

module Names where
  d : ℕ → T → T
  d n a = ψ (natT n) a ∷ []
  start = d 0 (d 2 (ψ (natT 2) [] ∷ ψ (natT 1) [] ∷ []))
  query = d 0 (d 2 (d 2 (natT 1)))
  At : T → T₀ → Set
  At a y = Σ (HC a) (λ h → Rt h L.≅ y)
  child : ∀ {a y} → cof a ≡ cω → At a y → ∀ n → At (fsn a n) (R.at y n)
  child {y = y} w (h , v) n = Gamma.child-iso h w y v n refl
  opaque
    root : At (B.row 2) (L.ψ⁰ R.Ω₃)
    root = B.row-h 2 , Finite.Fin.same 3 (B.row-h 2)
    asked : At query (Path.along (2 ∷ 0 ∷ 0 ∷ []) (L.ψ⁰ R.Ω₃))
    asked = child refl (child refl (child refl root 2) 0) 0
    reached : At start (Path.along (2 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ []) (L.ψ⁰ R.Ω₃))
    reached = child refl (child refl asked 2) 0
  in-four : ∀ h → L.suc (Rt {start} h) ≼ Std.std 4
  in-four h = ≼-trans {b = L.suc (Rt (proj₁ reached))} (s≼s (tree-≼ refl h (proj₁ reached)))
    (≼-trans {b = L.suc (Path.along (2 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ []) (L.ψ⁰ R.Ω₃))}
      (s≼s (≅→≼ (proj₂ reached))) past-address)
```
