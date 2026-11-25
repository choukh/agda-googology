# 三份前缀的首次询问在实际折叠中的位置

第四层验值。给第三级运行选择第三次块操作，每一行取零输入的一次向外返回。整族若分别支配三份参照的首次询问，同一运行即支配整份参照。[参照压缩](W4ThreeCopies.lagda.md) · [带初值的实际归纳](W4PTOSeededQuery.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4ThreeReturn where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂)
open import W4Block
open import W4Ops
open import W4Fold
open import WVOne using (T₀; 𝟏; read)
open import WVTwo using (g₂; p₂; ◃→≼)
open import WKGen using (Ω₁t; node-ge)
open import WKShape using (lvl3)
open import YiLAB7Orbit using (lvl1; lvl2; ok₂; p₁)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼-suc; ≼l; l≼; s≼s; ≅→≼; ≼lim⁻)
import B11OuterCore as Core
import B12ActualSlots as Cov
import B12Terminal as T
import B12Strict as Strict
import YiLAB11Orbit as State
import B13Orbit as Orb
import B13OrbitFeed as O
import B13SeedOuter as Outer
import B14OrbitReal as Carry
import B15OrbitModel as Context
import B18OrbitWorld as World
import B18OrbitLevels as Worlds
import B20Room as Room
import B22RowPrefix as Pref
import B22RowLive as Live
import B23ABlocks as Bl
import B23AFinite as Pieces
import B24AFirst as Two
import B24AWhole as Whole
import Survey.W4PTOSeededQuery as Restart
import Survey.W4ThreeCopies as Ref

series : T₀ → T₀
series x = L.lim (λ n → iter Restart.next x (suc n))

module Project (Q : Op {lvl2} nil) (S : Base lvl2) (w : zero ≤ lvl2) (b : Tr⁺ zero) where
  deep = enterO O.m₂ (enterO O.m₁ Q)
  S₀ : St Context.X₀
  S₀ i t = State.push S i (proj₂ t)
  pull : St Context.X₀ → Base lvl2
  pull s i t = s i (σ O.m₂ (σ O.m₁ t))
  project-state : ∀ n → pull (itS deep n S₀) ≡ itS Q n S
  project-state zero = refl
  project-state (suc n) = cong (stepS Q) (project-state n)
  project-value : ∀ n → itV deep n S₀ zero (σ O.m₂ (σ O.m₁ w)) b ≡ itV Q n S zero w b
  project-value zero = refl
  project-value (suc n) = cong₂ (λ s v → run Q s zero w v) (project-state n) (project-value n)
  result = E ok₂ O.D₁ (O.g₁ zero) (enterO O.m₁ Q) (State.push S) zero (σ O.m₁ w) b
  opaque
    shape : read (proj₁ result) L.≅ L.lim (λ n → read (proj₁ (itV Q (suc n) S zero w b)))
    shape = L.l≅ λ n → subst (λ v → read (proj₁ (itV deep (suc n) S₀ zero (σ O.m₂ (σ O.m₁ w)) b)) L.≅
      read (proj₁ v)) (project-value (suc n)) (L.≅-refl⁰ _)

module Actual (r : T.Run lvl3) (cv : Cov.Covered r) where
  module A = Outer.At r
  module F = Two.At r cv
  module G = Whole.Geometry F.Q₂ A.st1 (Core.st (Live.struct F.input)) A.w2 A.v₁
  cp = Bl.Site.cp r cv
  Q₃ = Orb.block A.c⁺ F.Q₂

  curve : ℕ → Tr zero → Tr lvl1
  curve zero = O.g₁
  curve (suc n) = G.curve n
  stored : ∀ n → lvl1 ⊢ Ω p₁ (curve n) ◃ G.seq (suc n)
  stored zero = ◃t (Core.st (Live.struct F.input))
    (Einf ok₂ tdNil (g₂ zero) F.Q₂ A.st1 lvl1 Core.slot G.c₀)
  stored (suc n) = G.stored n

  eval = λ n z → E ok₂ O.D₁ (curve n z) G.K G.S zero
  sample = λ n → read (proj₁ (eval n zero G.own A.v₁))
  curve-rise : ∀ n → lvl1 ⊢ curve n zero ◃ curve (suc n) zero
  curve-rise zero = ◃t ◃w (◃t (Core.st (Live.struct F.input))
    (Einf ok₂ O.D₁ (O.g₁ zero) G.K G.S lvl1 G.high G.c₀))
  curve-rise (suc zero) = Emono ok₂ O.D₁ G.K G.S lvl1 G.high G.c₀ (curve-rise zero)
  curve-rise (suc (suc n)) = Emono ok₂ O.D₁ G.K G.S lvl1 G.high G.c₀ (curve-rise (suc n))
  rise : ∀ n → L.suc (sample n) ≼ sample (suc n)
  rise n = Strict.strict (Emono ok₂ O.D₁ G.K G.S zero G.own A.v₁ (curve-rise n))
  upper : ∀ n → sample n ≼ read (T.value r)
  upper n = ≼-trans {b = read (proj₁ (run Q₃ A.st1 zero A.w2 A.v₁))} picked
    (≼-trans {b = read (proj₁ (run A.G A.st1 zero A.w2 A.v₁))}
      (◃→≼ (Pieces.At.inside r cv 3 A.st1 zero A.w2 A.v₁)) (A.outer 0))
    where
    node = Ω p₁ (curve n)
    child = E ok₂ O.D₁ node G.K G.S zero G.own A.v₁
    inner : sample n ≼ read (proj₁ child)
    inner = node-ge (kpT (fr O.D₁) ok₂ p₁ (tv O.D₁ G.own))
      (λ z → eval n z G.own A.v₁) (λ z → proj₁ (eval n z G.at₀ (G.S zero G.at₀))) 0
    standard : sample n ≼ read (proj₁ (run (Orb.block (Ωt lvl2) F.Q₂) A.st1 zero A.w2 A.v₁))
    standard = ≼-trans {b = read (proj₁ child)} inner
      (≼-trans {b = read (proj₁ (G.out₂ (G.seq (suc n))))}
        (◃→≼ (Emono ok₂ O.D₁ G.K G.S zero G.own A.v₁
          {x = node} {y = suc (G.seq (suc n))} (◃t (stored n) ◃s)))
        (node-ge (kp lvl2 ok₂ p₂ A.w2) G.out₂ G.step₂ (suc n)))
    move : ∀ c → Cov._⊴_ (proj₁ (Ωt lvl2)) (proj₁ c) →
      sample n ≼ read (proj₁ (run (Orb.block c F.Q₂) A.st1 zero A.w2 A.v₁))
    move c (inj₁ eq) = subst (λ z → sample n ≼ read (proj₁ (E ok₂ tdNil z F.Q₂ A.st1 zero A.w2 A.v₁)))
      eq standard
    move c (inj₂ d) = ≼-trans standard (◃→≼ (Emono ok₂ tdNil F.Q₂ A.st1 zero A.w2 A.v₁ d))
    picked = move A.c⁺ cp

  covers : (∀ n → Ref.test n ≼ sample n) → Ref.target ≼ read (T.value r)
  covers h = ≼-trans {b = L.lim Ref.test} (proj₁ Ref.Three.complete)
    (l≼ λ n → ≼-trans {b = sample n} (h n) (upper n))

  module Iter (S : Base lvl2) (ready : Live.Present Pref.empty S)
              (x : T₀) (initial : ∀ w → x ≼ read (proj₁ (S zero w))) where
    st = λ n → itS F.Q₂ n S
    step = iter Restart.next x
    live : ∀ n → Live.Present Pref.empty (st n)
    live zero = ready
    live (suc n) = Live.present (λ w → ≼-trans (Live.lower h w) (◃→≼ (inf F.Q₂ (st n) zero w (st n zero w))))
      (Carry.carry {e = Pref.e Pref.empty} {R = st n} {S = st (suc n)} grow (Live.struct h))
      (λ d → World.rise (Worlds.world d) (st n lvl1 Core.slot) (st (suc n) lvl1 Core.slot)
        grow _ (Live.index h d))
      where
      h = live n
      grow = inf F.Q₂ (st n) lvl1 Core.slot (st n lvl1 Core.slot)

    next-in : ∀ n → (∀ w → step n ≼ read (proj₁ (st n zero w))) →
      ∀ w b → 𝟏 ≼ read (proj₁ b) → step (suc n) ≼ read (proj₁ (run F.Q₂ (st n) zero w b))
    next-in n hab w b hb = C.in-block (step n) (hab (proj₂ C.Site.dz)) A.c⁺ cp
      where module C = Restart.Chain F.Q₁ F.law (st n) (live n) w b hb

    slots : ∀ n w → step n ≼ read (proj₁ (st n zero w))
    slots zero = initial
    slots (suc n) w = next-in n (slots n) w (st n zero w) (Live.lower (live n) w)

    output : ∀ n w b → 𝟏 ≼ read (proj₁ b) →
      step (suc n) ≼ read (proj₁ (itV F.Q₂ (suc n) S zero w b))
    output n w b hb = next-in n (slots n) w (itV F.Q₂ n S zero w b) (one n)
      where
      one : ∀ j → 𝟏 ≼ read (proj₁ (itV F.Q₂ j S zero w b))
      one zero = hb
      one (suc j) = ≼-trans (one j) (◃→≼ (inf F.Q₂ (st j) zero w (itV F.Q₂ j S zero w b)))
```

第零次询问打开两个低层框架。拉回到原环境以后，它的分支恰好是第二次块操作在同一输入上的每个正次迭代。

```agda
  first-value = Project.shape F.Q₂ A.st1 A.w2 A.v₁

  outcomes = λ n → read (proj₁ (itV F.Q₂ (suc n) A.st1 zero A.w2 A.v₁))
  Finite : Set
  Finite = ∀ n → Σ ℕ (λ j → L.suc (Ref.parts n) ≼ outcomes j)
  necessary : Ref.test 0 ≼ sample 0 → Finite
  necessary h n = ≼lim⁻ {a = Ref.parts n} {f = outcomes}
    (≼-trans {b = Ref.test 0} (≼l (suc n) (Ref.parts-rise n))
      (≼-trans {b = sample 0} h (≅→≼ first-value)))
  sufficient : Finite → Ref.test 0 ≼ sample 0
  sufficient h = ≼-trans {b = L.lim outcomes} (l≼ each) (≅→≼ (L.≅-sym first-value))
    where
    each : ∀ n → Ref.parts n ≼ L.lim outcomes
    each n with h n
    ... | j , d = ≼l j (≼-trans {b = L.suc (Ref.parts n)} (≼-suc (≼-refl _)) d)
  first-finite : L.suc (Ref.parts 0) ≼ outcomes 0
  first-finite = ≼-trans {b = Restart.next 𝟏} (Restart.above 𝟏) (I.output 0 A.w2 A.v₁ F.seed)
    where module I = Iter A.st1 F.input 𝟏 (Live.lower F.input)
  need-two : Ref.test 0 ≼ sample 0 → Σ ℕ (λ j → L.suc Ref.two ≼ outcomes j)
  need-two h = necessary h 1

  finite-funded : ∀ x → Room.Room r x → ∀ n → iter Restart.next x (suc n) ≼ outcomes n
  finite-funded x slots n = I.output n A.w2 A.v₁ F.seed
    where
    high : ∀ w → x ≼ read (proj₁ (A.st1 zero w))
    high w = ≼-trans (slots (inc tt w)) (◃→≼ (inf A.K A.S₀ zero w (A.S₀ zero w)))
    module I = Iter A.st1 F.input x high

  funded : ∀ x → Room.Room r x → series x ≼ sample 0
  funded x slots = ≼-trans {b = L.lim outcomes}
    (l≼ (λ n → ≼l n (finite-funded x slots n))) (≅→≼ (L.≅-sym first-value))

```
