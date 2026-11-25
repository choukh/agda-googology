# 在真实零槽中重启两份 Ω₂ 的反馈

第四层，无条件。两份 Ω₂ 的第零枝从 1 迭代函数 $H$，首个不动点为 $D$。实际高塔允许从已经得到的值的后继再次开始，一次三级子运行支付随后的整条轨道。[首个询问](W4PTOFirstQuery.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module Survey.W4PTOSeededQuery where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import W4Block
open import W4Path using (Ok-tw)
open import W4Ops
open import W4Fold
open import WVOne using (T₀; read)
open import WVTwo using (p₂; g₂; ◃→≼)
open import WKGen using (Ω₁t; node-ge)
open import WKShape using (lvl3)
open import YiLAB7Orbit using (lvl1; lvl2; ok₂; p₁)
open import YiLAB7Replay using (Ω₂ᴸ)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-refl; ≼-trans; ≼-suc; ≼l; l≼; s≼s; z≼)
import B11OuterCore as Core
import B12ActualSlots as Cover
import B12Terminal as Term
import B13Orbit as Block
import B13OrbitFeed as Frame
import B13SeedOuter as Outer
import B20Room as Room
import B20StandardInside as Std
import B20UnitSecond as Unit
import B21TowerGrowth as Tower
import B21StandardShape as Shape
import B22RowRule as Rule
import B22RowPrefix as Prefix
import B22RowLive as Live
import B22TowerCut as Cut
import B23ABlocks as Op
import B23AFinite as Pieces
import B24AFeedback as Feedback
import B24AFirst as First
import B24RKernel as Ref

inflation : ∀ x → x ≼ Ref.H x
inflation L.zero = z≼
inflation (L.suc x) = ≼-trans {b = L.suc (Ref.H x)} (s≼s (inflation x)) (Ref.grow x)
inflation (L.lim f) = l≼ λ n → ≼l n (inflation (f n))

orbit : T₀ → ℕ → T₀
orbit = λ x → iter Ref.H (L.suc x)
next : T₀ → T₀
next x = L.lim (λ n → orbit x (suc n))
above : ∀ x → L.suc x ≼ next x
above x = ≼l 0 (inflation (L.suc x))
fixed : ∀ x → Ref.H (next x) ≈ᵛ next x
fixed x = (l≼ λ n → ≼l (suc n) (≼-refl _)) , inflation (next x)
least : ∀ x b → L.suc x ≼ b → Ref.H b ≼ b → next x ≼ b
least x b seed closed = l≼ λ n → point (suc n) where
  point : ∀ n → orbit x n ≼ b
  point zero = seed
  point (suc n) = ≼-trans {b = Ref.H b} (Ref.monotone {orbit x n} {b} (point n)) closed

module Chain (Q : Op {lvl2} nil) (law : Rule.Rule Q Ω₂ᴸ)
             (st : Base lvl2) (input : Live.Present Prefix.empty st)
             (w : zero ≤ lvl2) (value : Tr⁺ zero) (hv : L.ψ⁰ (Prefix.q Prefix.empty) ≼ read (proj₁ value)) where
  module One = Feedback.Site Q Ω₂ᴸ law
  module Site = One.Run {L.zero} Prefix.empty st input
  open Site using (S₁; step₁; step₂; dz)
  clock : ℕ → Tr zero
  clock = iter step₁ zero
  own = σ Frame.m₁ w
  inner = E ok₂ Frame.D₁ Ω₁t One.K₁ S₁ zero own value

  module Start (x : T₀) (seed : x ≼ read (proj₁ (S₁ zero dz))) where
    track : ∀ n → orbit x n ≼ read (suc (clock (suc n)))
    track zero = s≼s (≼-trans seed (◃→≼ (Einf ok₂ Frame.D₁ (Frame.g₁ zero)
      One.K₁ S₁ zero dz (S₁ zero dz))))
    track (suc n) = ≼-suc (≼-trans (First.lower (orbit x n))
      (Site.Branch.value (orbit x n) (clock (suc n)) (track n) dz (S₁ zero dz)
        (Live.lower input (proj₂ dz))))
    inside : next x ≼ read (proj₁ inner)
    inside = l≼ λ n → ≼-trans (First.lower (orbit x n))
      (≼-trans (Site.Branch.value (orbit x n) (clock (suc n)) (track n) own value hv)
        (node-ge (kpT (fr Frame.D₁) ok₂ p₁ (tv Frame.D₁ own))
          (λ z → E ok₂ Frame.D₁ (Frame.g₁ z) One.K₁ S₁ zero own value) step₁ (suc n)))

  standard = run (Block.block (Ωt lvl2) Q) st zero w value
  parent : read (proj₁ inner) ≼ read (proj₁ standard)
  parent = ≼-trans (◃→≼ (Emono ok₂ tdNil Q st zero w value
    {x = up zero tt Ω₁t (proj₂ (Ωt lvl1))} {y = g₂ (step₂ zero)}
    (◃c zero tt (◃t (Core.st (Live.struct input))
      (◃t (Einf ok₂ tdNil (g₂ zero) Q st lvl1 Core.slot (st lvl1 Core.slot)) ◃s)))))
    (node-ge (kp lvl2 ok₂ p₂ w)
      (λ z → E ok₂ tdNil (g₂ z) Q st zero w value) step₂ 1)
  picked : ∀ c → Cover._⊴_ (proj₁ (Ωt lvl2)) (proj₁ c) →
    read (proj₁ standard) ≼ read (proj₁ (run (Block.block c Q) st zero w value))
  picked c (inj₁ eq) = subst (λ t → read (proj₁ standard) ≼
    read (proj₁ (E ok₂ tdNil t Q st zero w value))) eq (≼-refl _)
  picked c (inj₂ ge) = ◃→≼ (Emono ok₂ tdNil Q st zero w value ge)
  opaque
    in-block : ∀ x → x ≼ read (proj₁ (S₁ zero dz)) → ∀ c → Cover._⊴_ (proj₁ (Ωt lvl2)) (proj₁ c) →
      next x ≼ read (proj₁ (run (Block.block c Q) st zero w value))
    in-block x h c ge = ≼-trans {b = read (proj₁ inner)} (Start.inside x h)
      (≼-trans {b = read (proj₁ standard)} parent (picked c ge))

module Run (r : Term.Run lvl3) (cv : Cover.Covered r) where
  module A = Outer.At r
  module F = First.At r cv
  module C = Chain F.Q₁ F.law A.st1 F.input A.w2 A.v₁ F.seed
  open C.Site using (S₁; dz)
  paid : ∀ x → Room.Room r x → next x ≼ read (Term.value r)
  paid x slots = ≼-trans {b = read (proj₁ (run F.Q₂ A.st1 zero A.w2 A.v₁))}
    (C.in-block x seed A.c⁺ (Op.Site.cp r cv))
    (≼-trans {b = read (proj₁ (run A.G A.st1 zero A.w2 A.v₁))}
      (◃→≼ (Pieces.At.inside r cv 2 A.st1 zero A.w2 A.v₁)) (A.outer 0))
    where
    seed : x ≼ read (proj₁ (S₁ zero dz))
    seed = ≼-trans (slots (inc tt (proj₂ dz))) (◃→≼ (inf A.K A.S₀ zero (proj₂ dz) (A.S₀ zero (proj₂ dz))))

module Middle (r : Term.Run (tw 2)) (eq : Term.Run.ok r ≡ Ok-tw 2) (cv : Cover.Covered r)
              (q : T₀) (slots : Room.Room r q) where
  module Site = Unit.At.Three r eq cv q slots
  opaque
    paid : ∀ x → x ≼ L.suc q → next x ≼ read (Term.value r)
    paid x h = ≼-trans {b = read (Term.value Site.run)}
      (Run.paid Site.run Site.covered x (λ w → ≼-trans {b = L.suc q} h (Site.all w))) Site.value

module Higher (m : ℕ) where
  module R = Tower.At.Standard m
  k = Tower.At.k m
  top = Tower.At.top m
  opaque
    room : ∀ x → x ≼ L.suc (Std.std k) → next x ≼ Std.std top
    room x h = ≼-trans {b = read (Term.value R.s)}
      (Middle.paid R.s R.cert R.cv (Std.std k) R.high x h) R.below
```
