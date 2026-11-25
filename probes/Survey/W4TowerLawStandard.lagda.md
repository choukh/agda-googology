# 每升一座标准塔就能再次迭代 h 的下一个不动点

第四层，无条件。标准外塔的第一个正分支沿零前缀到达独立标准环境。第一次集齐正反馈重置时，较低塔的全部零槽已经达到整座前塔的标准值。自第三座起，每上移一塔即容纳从前塔值重新开始的全部有限次迭代。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4TowerLawStandard where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans; cong)
import W4Block as W
import W4Ops as O
import W4Fold as F
import W4Path as P
open import WVOne using (T₀; read; 𝟏; ≼-+ˡ)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼-suc; ≼l; l≼; +-mono)
import B8FreezeMain as Freeze
import B12Terminal as T
import B12ActualSlots as C
import B15Spine as Sp
import B15ReadPaths as R
import B15FixedWitness as Cert
import B15TowerFeedback as Trail
import B20Room as Room
import B20OldBlocks as Short
import B20StandardInside as Std
import B21StandardShape as Rise
import B21TowerRead as Read
import Survey.W4RoomDerivative as D
import Survey.W4ReturnCarry as Carry
open T.Run

-- 只有自然极限的正号孩子会把非零前缀写进环境。
data Empty : ∀ {a b} → R.Reach a b → Set where
  here : ∀ {a} → Empty (R.here {a})
  child : ∀ {h} → Empty (R.succ {h})
  limit : ∀ {h} → Empty (R.limit {h} 0)
  omega : ∀ {k h} → Empty (R.omega {k} {h})
  via : ∀ {a b c} {p : R.Reach a b} {q : R.Reach b c} → Empty p → Empty q → Empty (R.via p q)

left : ∀ a {j k} {p : R.Reach j k} → Empty p → Empty (R.left a p)
left a here = here
left a child = child
left a limit = limit
left a omega = omega
left a (via d e) = via (left a d) (left a e)

base : ∀ a b → Empty (R.base a b)
base a W.zero = here
base a (W.nd W.sS h) = via (base a (h tt)) child
base a (W.nd W.sL h) = via (base a (h 0)) limit
base a (W.nd (W.sΩ k) h) = via (base a (h W.zero)) omega

floor : ∀ k → Empty (Trail.floor k)
floor W.zero = here
floor (W.nd W.sS h) = omega
floor (W.nd W.sL h) = via (left W.zero (floor (h 0))) limit
floor (W.nd (W.sΩ k) h) = via (left W.zero (floor (h W.zero))) omega

first : ∀ k f u → Empty (Trail.through k f u 0)
first W.zero f u = limit
first (W.nd W.sS h) f u = via limit omega
first (W.nd W.sL h) f u = via (first (h 0) f u) limit
first (W.nd (W.sΩ k) h) f u = via (first (h W.zero) f u) omega

stay : ∀ {a b} {p : R.Reach a b} → Empty p → (r : T.Run b) → bs r ≡ F.B₀ b → bs (Room.sub p r) ≡ F.B₀ a
stay here r e = e
stay child (T.makeRun _ _ _ _ _ _) refl = refl
stay limit (T.makeRun _ _ _ _ _ _) refl = refl
stay omega (T.makeRun _ _ _ _ _ _) refl = refl
stay (via {q = q} d e) r fresh = stay d (Room.sub q r) (stay e r fresh)

module Whole (m : ℕ) where
  module K = Read.Standard m
  module A = Carry.At.Orbit m (F.B₀ (W.tw (suc m))) 𝟏
  part = λ j → proj₁ (K.M.reference (K.M.M.index j))
  bound : ∀ n → read (O.cum part n) ≼ A.total n
  bound zero = ≼-+ˡ 𝟏 (A.unit 0)
  bound (suc n) = ≼-trans (Freeze.read-+′ (O.cum part n) (part (suc n)))
    (+-mono (bound n) (≼-+ˡ 𝟏 (A.unit (suc n))))
  captured : Std.std (suc m) ≼ A.budget
  captured = ≼-trans {b = read (proj₁ K.M.projected)} (proj₁ K.whole) (l≼ λ n → ≼l {f = A.total} n (bound n))

  parent = W.tw (suc (suc m))
  r = T.initial parent (P.Ok-tw (suc (suc m)))
  module ARun = Carry.At.Actual m r refl (C.initial parent (ok r)) 𝟏 (oneB r)
  module Location = ARun.A
  module U = ARun.Use
  clean : Empty Location.path
  clean = left (W.tw (suc m)) (via (floor (W.tw (suc m)))
    (via (base Location.D.w Location.D.w) (first (W.tw (suc m)) (W.opR Location.D.w) Location.D.w)))
  core : bs Location.found ≡ F.B₀ _
  core = stay clean Location.one refl
  fresh : U.initialB ≡ F.B₀ (W.tw (suc m))
  fresh = stay child Location.found core
  stored : Std.std (suc m) ≼ U.reserve 0
  stored = subst (λ b → Std.std (suc m) ≼ Carry.At.Orbit.budget m b 𝟏) (Relation.Binary.PropositionalEquality.sym fresh) captured
  module Target = U.Selected 0 0
  room : Room.Room Target.target (Std.std (suc m))
  room w = ≼-trans stored (Target.common w)
  into : read (T.value Target.target) ≼ Std.std (suc (suc m))
  into = ARun.into 0 0

module Step (m : ℕ) where
  module Q = Whole (suc (suc m))
  path = Short.toward m
  r = Room.sub path Q.Target.target
  okay = trans (Room.cert path Q.Target.target) (trans (cong (Cert.pull path) Q.Target.standard) (Short.good m))
  cv = Room.cover path Q.Target.target Q.Target.covered
  from : ∀ x → x ≼ Std.std (suc (suc (suc m))) → D.block x ≼ Std.std (suc (suc (suc (suc m))))
  from x d = ≼-trans (D.Second.block-in r okay cv x (λ w → ≼-trans d (Room.room path Q.Target.target Q.room w)))
    (≼-trans (Room.below path Q.Target.target Q.Target.covered) Q.into)

-- g 连续枚举 h 的不动点，以 ω·n 为下标逐塔归纳。
paid : ∀ n → D.g (D.index n) ≼ Std.std (suc (suc (suc n)))
paid zero = ≼-trans D.first (≼-trans (≼-trans (≼-suc (≼-refl _)) (Rise.rise 1))
  (≼-trans (≼-suc (≼-refl _)) (Rise.rise 2)))
paid (suc n) = ≼-trans (D.limit-block (D.index n)) (Step.from n _ (paid n))

next-mono : ∀ {x y} → x ≼ y → D.next x ≼ D.next y
next-mono {x} {y} p = D.least x (D.next y)
  (≼-trans (OCF.Align.Value.s≼s p) (D.above y)) (proj₁ (D.fixed y))

first-block : D.g (D.index 1) ≼ Std.std 2
first-block = ≼-trans {b = D.block 𝟏} (l≼ λ n → ≼l n (term n))
  (D.Second.block-in r refl (C.initial (W.tw 2) (P.Ok-tw 2)) 𝟏 (oneB r))
  where
  r = T.initial (W.tw 2) (P.Ok-tw 2)
  term : ∀ n → D.g (D.index 0 L.+ L.natᶜ n) ≼ W.iter D.next 𝟏 (suc n)
  term zero = next-mono OCF.Align.Value.z≼
  term (suc n) = next-mono (term n)

fast : ∀ n → D.g (D.index (suc n)) ≼ Std.std (suc (suc (suc n)))
fast zero = ≼-trans first-block (≼-trans (≼-suc (≼-refl _)) (Rise.rise 2))
fast (suc n) = ≼-trans (D.limit-block (D.index (suc n))) (Step.from n _ (fast n))
```
