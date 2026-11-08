# 累计地板与完整直接观察保持关系

原并层地板用同分量ι及加法闭包建立证书。反馈使用原floor作为
初值，每一步的异坐标关系只由source ro证书和实际分类运输得到。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableRelRun where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaCountableRelIf
open import OCF.Lean.GeneralOmegaCountableRelClass

add-rel : ∀ {B a b c d} → Rel B a b → Rel B c d → Rel B (a ⊞ c) (b ⊞ d)
add-rel p rz = p
add-rel p (rs q) = rs (add-rel p q)
add-rel p (rl q) = rl (λ n → add-rel p (q n))
add-rel p (ro q) = ro (λ r → add-rel p (q r))
up-rel : ∀ {B a b} → Rel B a b → Rel (hs B) (up a) (up b)
up-rel rz = rz
up-rel (rs p) = rs (up-rel p)
up-rel (rl p) = rl (λ n → up-rel (p n))
up-rel (ro p) = ro (λ r → up-rel (p r))
ι-rel : ∀ {f : ℕ → Cd} {n} {a b : HB (F (f n))} → Rel (f n) a b → Rel (hl f) (ι n a) (ι n b)
ι-rel rz = rz
ι-rel (rs p) = rs (ι-rel p)
ι-rel (rl p) = rl (λ n → ι-rel (p n))
ι-rel (ro p) = ro (λ r → ι-rel (p r))

floor-related : ∀ B → Rel B (floor B) (floor B)
sum-related : ∀ f n → Rel (hl f) (C.ΣT S⊥ (hs hz) f n) (C.ΣT S⊥ (hs hz) f n)
floor-related hz = rs rz
floor-related (hs B) = ro (λ r → up-rel r)
floor-related (hl f) = rl (sum-related f)
floor-related (hΩ () f)
sum-related f zero = ι-rel (floor-related (f zero))
sum-related f (suc n) = add-rel (sum-related f n) (ι-rel (floor-related (f (suc n))))
left-rel : ∀ {B a b} → Rel B a b → ∀ n → Rel B (leftMul a n) (leftMul b n)
left-rel p zero = rz
left-rel p (suc n) = add-rel p (left-rel p n)
iterate-rel : ∀ {B} {f g : HB (F B) → HB (F B)} →
  (∀ {a b} → Rel B a b → Rel B (f a) (g b)) → ∀ {a b} → Rel B a b →
  ∀ n → Rel B (iterate f a n) (iterate g b n)
iterate-rel fg p zero = p
iterate-rel fg p (suc n) = fg (iterate-rel fg p n)

node-rel : ∀ {B t A} (Q : A → A → Set) (pt : t ⊲ B) (v : C.Dc F B t A) → Good Q v →
  (rec rec′ : ∀ r → r ⊲ B → A → HB (F r)) →
  (∀ r pr {a b} → Q a b → Rel r (rec r pr a) (rec′ r pr b)) →
  Rel t (node pt v rec) (node pt v rec′)
node-rel Q pt (C.keep κ fr) good rec rec′ rel = ro (λ r → rel _ pt (good r))
node-rel {t = t} Q pt (C.same to) good rec rec′ rel = rl (λ n → rel t pt
  (good (iterate-rel (λ r → rel t pt (good r)) (floor-related t) n)))
node-rel {t = t} Q pt (C.above i pi ti to) good rec rec′ rel = rl (λ n → rel t pt
  (good (iterate-rel (λ r → rel i (⊲ᴮ-tr (hsuc hself) pi) (good r)) (floor-related i) n)))

observe-related : ∀ B lB t pt {a b} → Rel B a b →
  Rel t (observe B lB t pt a) (observe B lB t pt b)
observe-related B lB t pt rz = floor-related t
observe-related B lB t pt (rs r) = rl (left-rel (observe-related B lB t pt r))
observe-related B lB t pt (rl r) = rl (λ n → observe-related B lB t pt (r n))
observe-related B lB t pt (ro {κ} {f} {g} r) = node-rel (Coord B κ) pt
  (classify B lB t pt κ) (class-good B lB t pt κ)
  (λ i pi e → observe B lB i pi (f e)) (λ i pi e → observe B lB i pi (g e))
  (λ i pi cd → observe-related B lB i pi (r cd))
instance-rel : RelObserver
instance-rel = record { floor-related = floor-related ; observe-related = observe-related }
```

全部定义递归原关系证书或原Cd结构，无停机/正性指示。输出关系
保持原目标路径，未对不同lB或pt作证明无关假设。
