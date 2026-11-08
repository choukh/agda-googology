# 原flL与原θ的分层关系闭包

每个分量的关系仍索引于选中它的确切Tree证据。这里只递归原树与
Layer构造子，没有把两个同端点的证明视作相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaEmbedOmegaFloorRun where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit.Polymorphic using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecFl using (flL; ΣF; gcF; cxI)
open import OCF.Lean.LHRecLeg using (module New)
open import OCF.Lean.GeneralOmegaEmbedOmegaIf
open import OCF.Lean.GeneralOmegaEmbedOmegaLayer using (tower-layer; lambda-layer)
open import OCF.Lean.GeneralOmegaEmbedOmegaFloorIf using (FloorLaws)
open import OCF.Lean.LHRecLay using (twL; ΛL)

tree-add : ∀ {x y a b c d} (p : Layer x y) → Tree p a b → Tree p c d →
  Tree p (a ⊞ c) (b ⊞ d)
tree-add p r tz = r
tree-add p r (ts s) = ts (tree-add p r s)
tree-add p r (tl s) = tl (λ n → tree-add p r (s n))
tree-add p r (to k s) = to k (λ e → tree-add p r (s e))

tree-up : ∀ {x y a b} (p : Layer x y) → Tree p a b → Tree (ls′ p) (up a) (up b)
tree-up p tz = tz
tree-up p (ts r) = ts (tree-up p r)
tree-up p (tl r) = tl (λ n → tree-up p (r n))
tree-up p (to k r) = to k (λ e → tree-up p (r e))

tree-sum : ∀ {f g : ℕ → LH} {n} {a : HB (Lv (f n))} {b : HB (Lv (g n))} (p : ∀ n → Layer (f n) (g n)) → Tree (p n) a b →
  Tree (ll′ p) (ι n a) (ι n b)
tree-sum p tz = tz
tree-sum p (ts r) = ts (tree-sum p r)
tree-sum p (tl r) = tl (λ n → tree-sum p (r n))
tree-sum p (to k r) = to (refl , k) (λ e → tree-sum p (r e))

tree-component : ∀ {k j f g a b c d} (p : Layer k j)
  (q : ∀ {a b} → Tree p a b → Layer (f a) (g b)) (r : Tree p a b) →
  Tree (q r) c d →
  Tree (lo′ p q) (ι {IxL k} {FXL k f} (inj₂ a) c) (ι {IxL j} {FXL j g} (inj₂ b) d)
tree-component p q r tz = tz
tree-component p q r (ts s) = ts (tree-component p q r s)
tree-component p q r (tl s) = tl (λ n → tree-component p q r (s n))
tree-component p q r (to k s) = to (r , k) (λ e → tree-component p q r (s e))

module Theta {k j f g} (p : Layer k j)
  (q : ∀ {a b} → Tree p a b → Layer (f a) (g b))
  (components : ∀ {a b} (r : Tree p a b) → Tree (q r) (flL (f a)) (flL (g b))) where
  left : HB (Lv k) → HB (Lv (lΩ k f))
  left = New.θ (cxI k f) (gcF (λ a → ι {IxL k} {FXL k f} (inj₂ a) (flL (f a))))
  right : HB (Lv j) → HB (Lv (lΩ j g))
  right = New.θ (cxI j g) (gcF (λ b → ι {IxL j} {FXL j g} (inj₂ b) (flL (g b))))
  related : ∀ {a b} → Tree p a b → Tree (lo′ p q) (left a) (right b)
  related tz = tz
  related (ts r) = tree-add (lo′ p q) (related r) (tree-component p q r (components r))
  related (tl r) = tl (λ n → related (r n))
  related (to k r) = to k (λ e → related (r e))

floor : ∀ {x y} (p : Layer x y) → Tree p (flL x) (flL y)
sums : ∀ {f g} (p : ∀ n → Layer (f n) (g n)) → ∀ n → Tree (ll′ p) (ΣF f n) (ΣF g n)
floor lz′ = tz
floor (ls′ p) = to tt (λ r → tree-up p r)
floor (ll′ p) = tl (sums p)
floor (lo′ p q) = to tt (Theta.related p q (λ r → floor (q r)))
sums p zero = tree-sum p (floor (p zero))
sums p (suc n) = tree-add (ll′ p) (sums p n) (tree-sum p (floor (p (suc n))))

instance-floor : FloorLaws
instance-floor = record { add = tree-add ; floor = floor }

tower-floor : ∀ n → Tree (tower-layer n) (flL (twL n)) (flL (twL n))
tower-floor n = floor (tower-layer n)
lambda-floor : Tree lambda-layer (flL ΛL) (flL ΛL)
lambda-floor = floor lambda-layer
```

这给所有原twL与完整ΛL地板的实际关系证书。Tree不是序数值关系；
后续仍要实际code保持Coord，再由结构模拟接到原run，不能据此宣称
ψ₀Λ的大小已验收。
