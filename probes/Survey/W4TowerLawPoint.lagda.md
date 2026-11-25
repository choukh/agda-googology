# 一条实际零槽路径就能启动不动点迭代

第四层，无条件。首塔只读正槽的零层预算即可覆盖下一 h 不动点。每加一个后继层，一条预先确定的输入路径仍能使全部输出路径迭代前层律任意有限次。第二塔的规范输出也只需要一条可计算的输入路径。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4TowerLawPoint where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
import W4Block as W
import W4Ops as O
import W4Path as P
import W4Fold as F
open import WVOne using (T₀; read; h₁; 𝟏; gt; p₀)
open import WVTwo using (◃→≼)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼l; l≼; s≼s)
import WKGen as Node
import B12Terminal as T
import B12ActualSlots as C
import B12Strict as Strict
import B13FiniteLift as U
import B14Tower as V
import B15TowerSeed as Seed
import B15ReadPaths as R
import B19RowSecondParent as Add
import B20OldStage as St
import B20Room as Room
import B20OldSecond as OS
import Survey.W4RoomHeight as H
import Survey.W4RoomDerivative as D
open D using (chain; next; inflation)
import Survey.W4RoomDiagonal as G
open G using (buffer; three) renaming (module H to Heights)
open import Survey.W4FourthLiftValue using (h)

slot : ∀ {l} → T.Run l → W.zero W.≤ l → T₀
slot r p = read (proj₁ (T.Run.bs r W.zero p))
Law : ∀ {l} → W.zero W.≤ l → (T₀ → T₀) → Set
Law {l} p f = (r : T.Run l) → C.Covered r → ∀ x → x ≼ slot r p → ∀ w → f x ≼ V.valueAt r w

-- 第一个正下标来自正槽内的零槽，后来各步都从实际下标及其覆盖证书得到。
module First (r : T.Run (W.tw 1)) (cv : C.Covered r) (x : T₀) (fund : x ≼ slot r (W.ink W.self)) where
  module X = V.At r
  module I = Seed.First r cv
  enough : ∀ n → W.iter L.suc x n ≼ read (I.parts n)
  enough zero = fund
  enough (suc n) = ≼-trans (s≼s (enough n)) (Strict.strict (O.nextA I.c (proj₂ X.slot) n))

  budget : ∀ n → Heights.cut (chain x n) ≼ read (X.idx (suc n))
  budget zero = ≼l 4 (≼-trans (s≼s (G.pad 3 x)) (enough 4))
  budget (suc n) = ≼-trans (buffer (chain x n) 𝟏)
    (Heights.apply (chain x n) z (budget n) s (V.chain-covered r cv z) 𝟏 (T.Run.oneB s) (X.path z))
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
      (Heights.apply t z (budget n) a ca 𝟏 (T.Run.oneB a) w))
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

first : Law {W.tw 1} (W.ink W.self) next
first = First.output

module Lift (s : W.Sh) (h : W.Ch s → W.L) (p : W.zero W.≤ W.nd s h) (f : T₀ → T₀) (pay : Law p f)
  (r : T.Run (U.sc (W.nd s h))) (cv : C.Covered r) (x : T₀) (fund : x ≼ slot r (W.inc tt p)) where
  open T.Run
  module A = St.At s h r cv
  raised : ∀ n → W.iter f x n ≼ read (proj₁ (A.S n W.zero p))
  raised zero = ≼-trans fund (◃→≼ (F.inf A.K (bs A.r₀) W.zero p (bs A.r₀ W.zero p)))
  raised (suc n) = ≼-trans (pay (V.reset a (bs a W.zero p) (oneB a p)) (A.cover n) _ (raised n) p) (A.weaken _ p _)
    where a = A.setup p (β r) (oneβ r) n
  emit : ∀ w n → W.iter f x (suc n) ≼ read (proj₁ (A.v w (β r) (suc n)))
  emit w n = ≼-trans (pay (A.setup w (β r) (oneβ r) n) (A.cover n) _ (raised n) w) (A.weaken _ w _)
  all : ∀ w → H.repeat f x ≼ V.valueAt r w
  all (W.inc tt w) = l≼ λ n → ≼-trans (emit w n) (A.send A.select (β r) n)
  all (W.inu ws) = l≼ λ n → ≼-trans (emit (ws tt) n) (A.send (A.every refl) (β r) n)

level : ℕ → W.L
level zero = W.tw 1
level (suc n) = U.sc (level n)
path : ∀ n → W.zero W.≤ level n
path zero = W.ink W.self
path (suc n) = W.inc tt (path n)
operation = W.iter H.repeat next
all : ∀ n → Law (path n) (operation n)
all zero = first
all (suc zero) = Lift.all (W.sΩ W.zero) h₁ (path zero) next first
all (suc (suc n)) = Lift.all W.sS (λ _ → level n) (path (suc n)) (operation (suc n)) (all (suc n))

outer : ∀ {a b} → R.Reach a b → W.zero W.≤ a → W.zero W.≤ b
outer R.here w = w
outer R.succ w = W.inc tt w
outer (R.limit n) w = W.inc n w
outer R.omega w = W.inc W.zero w
outer (R.via p q) w = outer q (outer p w)
keep : ∀ {a b} (d : R.Reach a b) (r : T.Run b) w → slot r (outer d w) ≼ slot (Room.sub d r) w
keep R.here r w = OCF.Align.Value.≼-refl _
keep R.succ r w = OCF.Align.Value.≼-refl _
keep (R.limit {h} j) r w = T.inflate0 _ (T.Run.ok r) (T.Run.bs r) (W.inc j w) (T.Run.bs r W.zero (W.inc j w)) (T.prefix h j)
keep R.omega r w = OCF.Align.Value.≼-refl _
keep (R.via p q) r w = ≼-trans (keep q r (outer p w)) (keep p (Room.sub q r) w)

module Second (r : T.Run (W.tw 2)) (eq : T.Run.ok r ≡ P.Ok-tw 2) (cv : C.Covered r) where
  module S = OS.At r eq cv
  route = R.left (W.tw 1) S.trail
  child = S.D.C.child 1
  cc = S.D.C.cover cv 1
  address : W.zero W.≤ W.tw 2
  address = W.inc (S.D.C.ix 1) (outer route (path 1))
  pay : ∀ x → x ≼ slot r address → D.block x ≼ read (T.value r)
  pay x funded = ≼-trans (all 1 (Room.sub route child) (Room.cover route child cc) x
      (≼-trans funded (keep route child (path 1))) (P.z≤ _))
    (≼-trans (Room.below route child cc) (S.D.C.lift-value 1))
```
