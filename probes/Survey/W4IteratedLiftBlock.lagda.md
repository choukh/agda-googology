# 标准正块携带任意右加的可数树

第四层。给出正块、有限连接和可数极限的统一值律。右加可数树后全部零路径仍能支出原变换。含多个标准正块时可顺次把上一变换的有限次迭代取上确界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4IteratedLiftBlock where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
import W4Block as W
import W4Ops as O
import W4Fold as F
import W4Path as P
import WKGen as Node
open import WVOne using (T₀; read; 𝟏)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; ≼l)
import B12Terminal as T
import B12ActualSlots as C
import B13FiniteLift as U
import B14Tower as V
import B15Spine as S
import B19RowSecondParent as Add
import B20Room as Room
import Survey.W4NextLiftIndex as I
import Survey.W4RoomHeight as H
open T.Run

k = W.tw 1
Tr = W.Tr k
base = proj₁ (O.Ωt k)
readL = W.↑ k
wrap : List Tr → Tr → Tr
wrap [] t = t
wrap (a ∷ e) t = wrap e (a O.+ t)

post : ∀ e v → readL (wrap e (W.suc v)) ≡ U.sc (readL (wrap e v))
post [] v = refl
post (a ∷ e) v = post e (a O.+ v)
limit : ∀ e g d → readL (wrap e (W.lim g d)) ≡ W.nd W.sL (λ n → readL (wrap e (g n)))
limit [] g d = refl
limit (a ∷ e) g d = limit e (λ n → a O.+ g n) (λ n → O.+-mono a (d n))
origin : ∀ e a → readL (wrap e (a O.+ base)) ≡ W.nd (W.sΩ W.zero) (λ z → readL (wrap e a) W.⊕ I.diag z)
origin [] a = refl
origin (b ∷ e) a = origin e (b O.+ a)

data Nonzero : W.L → Set where
  node : ∀ s h → Nonzero (W.nd s h)
live : ∀ p → Nonzero (I.plug p W.zero) → ∀ l → Nonzero (I.plug p l)
live p nz W.zero = nz
live p nz (W.nd s h) = subst Nonzero (sym (I.node p s h)) (node s _)

up : ∀ {l} → Nonzero l → ∀ {f} → H.Law l f → H.Law (U.sc l) (H.repeat f)
up (node s h) {f} = H.Successor.all s h f
one : ∀ {l f} → H.Law l (H.repeat f) → H.Law l f
one pay r cv x hi w = ≼-trans (≼l 0 (≼-refl _)) (pay r cv x hi w)
all-children : ∀ g {f} → (∀ n → H.Law (g n) f) → H.Law (W.nd W.sL g) f
all-children g {f} q = H.Limit.all g 0 f (λ n _ → q n)

module Zero (h : W.Tr W.zero → W.L) (decode : ∀ z → I.Worth (read z) (h z)) (f : T₀ → T₀) (pay : H.Law (h W.zero) f) where
  root = W.nd (W.sΩ W.zero) h
  module At (r : T.Run root) (cv : C.Covered r) (x : T₀) (high : Room.Room r x) where
    module A = S.Cardinal W.zero h r
    start = A.child 0
    high₀ = λ u → high (W.inc W.zero u)
    cr = A.cover cv 0
    s = V.reset start (bs r W.zero (W.ink W.self)) (oneB r (W.ink W.self))
    z = A.ix 1
    paid : f x ≼ read z
    paid = pay s cr x high₀ (W.self W.∙ proj₂ (proj₁ (ok r)) W.zero)
    call = λ w z → F.ψ root (ok r) (bs r) W.zero w (β r) (A.b z)
    upper = λ w → read (proj₁ (F.node⁺ (F.kp root (ok r) A.p w) (call w) A.step))
    inside : ∀ w n → read (proj₁ (call w (A.ix n))) ≼ upper w
    inside w n = Node.node-ge (F.kp root (ok r) A.p w) (call w) A.step n
    fresh = T.initial (h z) (proj₂ (ok r) z)
    all : ∀ w → f x ≼ V.valueAt r w
    all (W.inu ws) = ≼-trans (pay start cr x high₀ (ws W.zero)) (inside (W.inu ws) 0)
    all (W.ink W.self) = ≼-trans (pay start cr x high₀ (W.self W.∙ proj₂ (proj₁ (ok r)) W.zero)) (inside (W.ink W.self) 0)
    all (W.inc c w) = ≼-trans paid (≼-trans (decode z fresh (C.initial _ (ok fresh)))
      (≼-trans (Add.append (β r) (F.ψ₀ (h z) (ok fresh) (proj₁ (O.Ωt (h z))))) (inside (W.inc c w) 1)))

from : ∀ e p → Nonzero (I.plug p W.zero) → ∀ {f} → H.Law (I.plug p (readL (wrap e W.zero))) f →
  H.Law (I.plug p (readL (wrap e base))) (H.repeat f)
from e p nz {f} q = subst (λ l → H.Law l (H.repeat f)) (sym shape) (Zero.At.all h (λ z → I.growth z (v ∷ p)) (H.repeat f) first)
  where
  v = readL (wrap e W.zero)
  h = λ z → I.plug (v ∷ p) (I.diag z)
  shape = trans (cong (I.plug p) (origin e W.zero)) (I.node p (W.sΩ W.zero) (λ z → v W.⊕ I.diag z))
  first : H.Law (h W.zero) (H.repeat f)
  first = subst (λ l → H.Law l (H.repeat f)) (sym (I.node (v ∷ p) W.sS (λ _ → W.zero))) (up (live p nz v) q)

extend : ∀ b z e p → Nonzero (I.plug p W.zero) → ∀ {f} → H.Law (I.plug p (readL (wrap e b))) f →
  H.Law (I.plug p (readL (wrap e (b O.+ O.ι k z)))) f
extend b W.zero e p nz q = q
extend b (W.suc z) e p nz {f} q = subst (λ l → H.Law l f) (sym shape) (one (up (live p nz (readL (wrap e t))) (extend b z e p nz q)))
  where
  t = b O.+ O.ι k z
  shape = trans (cong (I.plug p) (post e t)) (I.node p W.sS (λ _ → readL (wrap e t)))
extend b (W.lim a d) e p nz {f} q = subst (λ l → H.Law l f) (sym shape) (all-children _ (λ n → extend b (a n) e p nz q))
  where
  ts = λ n → b O.+ O.ι k (a n)
  diff = λ n → O.+-mono b (O.ι-mono k (d n))
  shape = trans (cong (I.plug p) (limit e ts diff)) (I.node p W.sL (λ n → readL (wrap e (ts n))))

data Positive : Tr → Set where
  seed : Positive base
  join : ∀ {a b} → Positive a → Positive b → Positive (a O.+ b)
  append : ∀ {a} → Positive a → ∀ z → Positive (a O.+ O.ι k z)
  collect : ∀ {g d} → (∀ n → Positive (g n)) → Positive (W.lim g d)

raise : ∀ {t} → Positive t → ∀ e p → Nonzero (I.plug p W.zero) → ∀ {f} → H.Law (I.plug p (readL (wrap e W.zero))) f →
  H.Law (I.plug p (readL (wrap e t))) (H.repeat f)
raise seed e p = from e p
raise (join {a} q s) e p nz low = raise s (a ∷ e) p nz (one (raise q e p nz low))
raise (append {a} q z) e p nz low = extend a z e p nz (raise q e p nz low)
raise (collect {g} {d} q) e p nz {f} low = subst (λ l → H.Law l (H.repeat f)) (sym shape) (all-children _ (λ n → raise (q n) e p nz low))
  where shape = trans (cong (I.plug p) (limit e g d)) (I.node p W.sL (λ n → readL (wrap e (g n))))
```
