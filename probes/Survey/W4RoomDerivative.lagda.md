# 以塔的共同零槽为起点求 h 的下一个不动点

第四层，无条件。以 g 连续枚举 h 的不动点，已证 g(ω·n) ≤ 第 1+4n 座标准塔，g(ω²) ≤ W4。首塔的所有零槽若都达到 x，每条零路径的输出都达到严格大于 x 的首个 h 不动点。选定孩子的路径换底后仍可使用实际反馈产生的层号。[首个不动点](W4RoomDiagonal.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4RoomDerivative where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-refl; ≼-trans; ≼-suc; s≼s; ≼l; l≼; z≼)
import W4Block as W
import W4Ops as O
import W4Path as P
import W4Fold as F
open import WVOne using (T₀; read; 𝟏; p₀; h₁; gt)
import B12Terminal as T
import B12ActualSlots as C
import B12Strict as Strict
import B14Tower as V
import B15TowerSeed as Seed
import B19RowSecondParent as Add
import B20Room as Room
import WKGen as Node
import Survey.W4RoomHeight as Height
import Survey.W4RoomDiagonal as D
open D using (three; module H; buffer)
open import Survey.W4FourthLiftValue using (h)

chain : T₀ → ℕ → T₀
chain x = W.iter h (L.suc x)
next : T₀ → T₀
next x = L.lim (chain x)

inflation : ∀ a → a ≼ h a
inflation L.zero = z≼
inflation (L.suc a) = ≼-trans (s≼s (inflation a)) (Survey.W4PTOSeededQuery.above (h a))
  where import Survey.W4PTOSeededQuery
inflation (L.lim a) = l≼ λ n → ≼l n (inflation (a n))

above : ∀ x → L.suc x ≼ next x
above x = ≼l 0 (≼-refl _)

fixed : ∀ x → h (next x) ≈ᵛ next x
fixed x = l≼ (λ n → ≼l (suc n) (≼-refl _)) , inflation (next x)

least : ∀ x y → L.suc x ≼ y → h y ≼ y → next x ≼ y
least x y p q = l≼ each
  where
  each : ∀ n → chain x n ≼ y
  each zero = p
  each (suc n) = ≼-trans (D.monotone (each n)) q

module At (r : T.Run (W.tw 1)) (cv : C.Covered r) (x : T₀) (high : Room.Room r x) where
  module X = V.At r
  module I = Seed.First r cv
  enough : ∀ n → W.iter L.suc x n ≼ read (I.parts n)
  enough zero = high (W.ink W.self)
  enough (suc n) = ≼-trans (s≼s (enough n)) (Strict.strict (O.nextA I.c (proj₂ X.slot) n))

  budget : ∀ n → H.cut (chain x n) ≼ read (X.idx (suc n))
  budget zero = ≼l 4 (≼-trans (s≼s (D.pad 3 x)) (enough 4))
  budget (suc n) = ≼-trans (buffer (chain x n) 𝟏)
    (H.apply (chain x n) z (budget n) s (V.chain-covered r cv z) 𝟏 (T.Run.oneB s) (X.path z))
    where
    z = X.idx (suc n)
    s = X.chain z

  module Emit (n : ℕ) where
    t = chain x n
    z = X.idx (suc n)
    original = T.tower-child r (suc n)
    reset = T.initial (h₁ z) (proj₂ (T.Run.ok r) z)
    point : ∀ (a : T.Run (h₁ z)) → C.Covered a → ∀ w → h t ≼ V.valueAt a w
    point a ca w = ≼-trans (WVOne.≼-+ˡ three (h t)) (≼-trans (buffer t 𝟏)
      (H.apply t z (budget n) a ca 𝟏 (T.Run.oneB a) w))
    call = λ w b → F.ψ (W.tw 1) (T.Run.ok r) (T.Run.bs r) W.zero w (T.Run.β r) (gt b)
    branch : ∀ w → h t ≼ read (proj₁ (call w z))
    branch (W.inu ws) = point original (C.enter (W.sΩ W.zero) h₁ r z W.zero cv) (ws z)
    branch (W.ink W.self) = point original (C.enter (W.sΩ W.zero) h₁ r z W.zero cv) (X.path z)
    branch (W.inc c w) = ≼-trans (point reset (C.initial (h₁ z) (T.Run.ok reset)) (P.z≤ (h₁ z)))
      (Add.append (T.Run.β r) (F.ψ (h₁ z) (T.Run.ok reset) (F.B₀ (h₁ z)) W.zero (P.z≤ _) (O.Ωt W.zero) (proj₁ (O.Ωt (h₁ z)))))
    join : ∀ w → h t ≼ read (proj₁ (F.node⁺ (F.kp (W.tw 1) (T.Run.ok r) p₀ w) (call w) X.next))
    join w = ≼-trans (branch w) (Node.node-ge (F.kp (W.tw 1) (T.Run.ok r) p₀ w) (call w) X.next (suc n))
    inside : ∀ w → h t ≼ V.valueAt r w
    inside (W.inc c v) = join (W.inc c v)
    inside (W.inu ws) = join (W.inu ws)
    inside (W.ink W.self) = join (W.ink W.self)

  output : ∀ w → next x ≼ V.valueAt r w
  output w = l≼ λ { zero → ≼-trans (inflation (L.suc x)) (Emit.inside 0 w) ; (suc n) → Emit.inside n w }

law : Height.Law (W.tw 1) next
law = At.output
```

第二塔在同一次返回内访问首塔的一个后继层，故容纳任意有限次取下一个不动点。改变标准塔号，可以从之前已经容纳的值重新开始。

```agda
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
import B20UnitSecond as U
import B20StandardInside as Std
import B21TowerGrowth as Site
import B21StandardShape as Rise
import B22TowerCut as K
import B18Product as Mul

block = Height.repeat next

module Second (r : T.Run (W.tw 2)) (eq : T.Run.ok r ≡ P.Ok-tw 2) (cv : C.Covered r)
              (x : T₀) (high : Room.Room r x) where
  module S = U.At r eq cv x high
  block-in : block x ≼ read (T.value r)
  block-in = ≼-trans (Height.Successor.all (W.sΩ W.zero) h₁ next law S.root S.cr x S.hr (P.z≤ _))
    (≼-trans (Room.below S.take S.c S.cc) (S.Top.D.C.lift-value 1))

module Standard (m : ℕ) where
  module Place = Site.At.Standard m
  pay : ∀ x → x ≼ Std.std m → block x ≼ Std.std (Site.At.top m)
  pay x d = ≼-trans (Second.block-in Place.s Place.cert Place.cv x (λ w → ≼-trans room (Place.high w))) Place.below
    where
    next-tower : ∀ k → Std.std k ≼ Std.std (suc k)
    next-tower k = ≼-trans (≼-suc (≼-refl _)) (Rise.rise k)
    room = ≼-trans d (≼-trans (next-tower m) (next-tower (suc m)))

g : T₀ → T₀
g L.zero = next L.zero
g (L.suc a) = next (g a)
g (L.lim s) = L.lim (λ i → g (s i))

enumerated : ∀ a → h (g a) ≈ᵛ g a
enumerated L.zero = fixed L.zero
enumerated (L.suc a) = fixed (g a)
enumerated (L.lim s) = l≼ (λ n → ≼l n (proj₁ (enumerated (s n)))) ,
                       l≼ (λ n → ≼l n (proj₂ (enumerated (s n))))

base : g L.zero ≈ᵛ D.fixedPoint
base = least L.zero D.fixedPoint (≼l 1 (Survey.W4PTOSeededQuery.above L.zero)) (proj₁ D.fixed) ,
       D.least (next L.zero) (proj₁ (fixed L.zero))
  where import Survey.W4PTOSeededQuery

finite : ∀ a n → g (a L.+ L.natᶜ n) ≡ W.iter next (g a) n
finite a zero = refl
finite a (suc n) = cong next (finite a n)

limit-block : ∀ a → g (a L.+ L.ωᶜ) ≼ block (g a)
limit-block a = l≼ λ n → ≼l n (subst (_≼ W.iter next (g a) (suc n)) (Relation.Binary.PropositionalEquality.sym (finite a n))
  (≼-trans (≼-suc (≼-refl _)) (above (W.iter next (g a) n))))

first : g L.zero ≼ Std.std 1
first = ≼-trans (proj₁ base) (D.Tower.whole B12TerminalSrc.standard (C.initial _ (P.Ok-tw 1)))
  where import B12TerminalSrc

index = λ n → L.ωᶜ Mul.· L.natᶜ n
towers : ℕ → ℕ
towers zero = 1
towers (suc n) = Site.At.top (towers n)

paid : ∀ n → g (index n) ≼ Std.std (towers n)
paid zero = first
paid (suc n) = ≼-trans (limit-block (index n)) (Standard.pay (towers n) (g (index n)) (paid n))

omega-square : g (L.ωᶜ Mul.· L.ωᶜ) ≼ K.cut
omega-square = l≼ λ n → ≼l (towers n) (paid n)

closed : ∀ {x} → L.suc x ≼ K.cut → L.suc (block x) ≼ K.cut
closed {x} (≼l m d) = ≼l (suc (Site.At.top m))
  (≼-trans (s≼s (Standard.pay m x (≼-trans (≼-suc (≼-refl _)) d))) (Rise.rise (Site.At.top m)))

cut-fixed : h K.cut ≈ᵛ K.cut
cut-fixed = l≼ (λ m → ≼l (Site.At.top m) (≼-trans (point (Std.std m)) (Standard.pay m _ (≼-refl _)))) ,
            inflation K.cut
  where
  point : ∀ x → h x ≼ block x
  point x = ≼-trans {b = next x} (≼l 1 (D.monotone (≼-suc (≼-refl x)))) (≼l 0 (≼-refl _))

import Survey.W4RouteTests as A
terminal : g (L.ωᶜ Mul.· L.ωᶜ) ≼ A.Y
terminal = ≼-trans omega-square K.terminal

past-first : L.suc D.fixedPoint ≼ g (L.ωᶜ Mul.· L.ωᶜ)
past-first = ≼l {f = λ n → g (index n)} 1 (≼l 1 (≼-trans (s≼s (proj₂ base)) (above (g L.zero))))

import B27UEpsilon as Env
import B22MovingIndex as Eps
import Survey.W4ThreeTower as Earlier
import Survey.W4PTOSeededQuery as N
import B24RKernel as Kernel
import Survey.W4ClockClosure as Clock

module Small = Env.At L.zero

past-local : L.suc (h (L.ωᶜ Mul.· L.ωᶜ)) ≼ D.fixedPoint
past-local = ≼l {f = D.stages} 2 (≼-trans (N.above (h square)) (D.monotone {L.suc square} {h L.zero} start))
  where
  square = L.ωᶜ Mul.· L.ωᶜ
  omega-small = Earlier.Gap.omega-in L.zero
  start : L.suc square ≼ h L.zero
  start = ≼-trans {b = Eps.above L.zero} (Small.finite {square} (Small.mulC {L.ωᶜ} {L.ωᶜ} omega-small omega-small))
    (≼-trans {b = Clock.jump L.zero} (A.clock-below L.zero (Eps.above L.zero))
    (≼-trans {b = Kernel.H 𝟏} (Earlier.jump-step L.zero L.zero z≼) (≼l 0 (≼-refl _))))
```
