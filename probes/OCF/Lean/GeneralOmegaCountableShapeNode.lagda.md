# 对应合法公共界内的完整节点反馈

两次cmp各在各自source公共界内运行；Compared只同步原结果，不在
裸高度间引入判等。保留节点用逐点坐标运输，同层和高层分别同步
原floor种子及全部无累加反馈。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableShapeNode where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableShapeIf
open import OCF.Lean.GeneralOmegaCountableShapeBase
open import OCF.Lean.GeneralOmegaCountableShapeCompare
open import OCF.Lean.GeneralOmegaCountableShapeCoord
open import OCF.Lean.GeneralOmegaCountableShapeFloor
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo)

iterate-tree : ∀ {a b : Cd} (p : Same a b) {f : HB (F a) → HB (F a)} {g : HB (F b) → HB (F b)} →
  (∀ {x y} → Tree p x y → Tree p (f x) (g y)) →
  ∀ {x y} → Tree p x y → ∀ n → Tree p (iterate f x n) (iterate g y n)
iterate-tree p fg r zero = r
iterate-tree p fg r (suc n) = fg (iterate-tree p fg r n)

pick-node : ∀ {A B t u i j : Cd} {X Y : Set}
  (source : Same A B) (target : Same t u) (rank : Same i j)
  {pt : t ⊲ A} {qt : u ⊲ B} {pi : hs i ⊲ A} {pj : hs j ⊲ B}
  (target-paths : Paths target source pt qt) (rank-paths : Paths (ss rank) source pi pj)
  (Q : X → Y → Set) (encode : HB (F i) → X) (encode′ : HB (F j) → Y)
  (codes : ∀ {x y} → Tree rank x y → Q (encode x) (encode′ y))
  (rec : ∀ r → r ⊲ A → X → HB (F r)) (rec′ : ∀ r → r ⊲ B → Y → HB (F r))
  (ih : ∀ {r s} (p : Same r s) {pr qr} → Paths p source pr qr → ∀ {x y} → Q x y → Tree p (rec r pr x) (rec′ s qr y))
  {left : (t ⊲ hs i) ⊎ (hs i ⊲ t)} {right : (u ⊲ hs j) ⊎ (hs j ⊲ u)} →
  Compared (ss rank) target left right →
  Tree target (node pt (C.pick S⊥ encode pi left) rec) (node qt (C.pick S⊥ encode′ pj right) rec′)
pick-node source target rank ht hi Q encode encode′ codes rec rec′ ih (cright h) =
  node-eq (along-key h) (λ r → ih target ht (codes (along-coord h r)))
pick-node source .(ss rank) rank ht hi Q encode encode′ codes rec rec′ ih (cleft (phere .(ss rank))) =
  to (λ r → ih (ss rank) ht (codes r))
pick-node source target .target ht hi Q encode encode′ codes rec rec′ ih (cleft (pnext (phere .target))) =
  tl (λ n → ih target ht (codes (iterate-tree target (λ r → ih target ht (codes r)) (floor-tree target) n)))
pick-node source target rank ht hi Q encode encode′ codes rec rec′ ih (cleft (pnext (pnext h))) =
  tl (λ n → ih target ht (codes (iterate-tree rank
    (λ r → ih rank (compose-paths (pnext (phere rank)) hi) (codes r)) (floor-tree rank) n)))
pick-node source target rank ht hi Q encode encode′ codes rec rec′ ih (cleft (pnext (plimit n h))) =
  tl (λ n → ih target ht (codes (iterate-tree rank
    (λ r → ih rank (compose-paths (pnext (phere rank)) hi) (codes r)) (floor-tree rank) n)))

node-shape : ∀ {A B t u : Cd} (source : Same A B) la lb → LegalShape source la lb →
  ∀ (target : Same t u) {pt qt} → Paths target source pt qt → ∀ κ
  (rec : ∀ r → r ⊲ A → E (F A) κ → HB (F r))
  (rec′ : ∀ r → r ⊲ B → E (F B) (map-K source κ) → HB (F r)) →
  (∀ {r s} (p : Same r s) {pr qr} → Paths p source pr qr → ∀ {x y} → Coord source κ x y →
    Tree p (rec r pr x) (rec′ s qr y)) →
  Tree target (node pt (classify A la t pt κ) rec) (node qt (classify B lb u qt (map-K source κ)) rec′)
node-shape {A} {B} source la lb legal target {pt} {qt} ht κ rec rec′ ih
  with C.cl A κ | C.cl B (map-K source κ) | cl-shape source κ | cl-coord source κ
... | C.nw i pi encode | C.nw j pj encode′ | cnew rank hi | codes =
  pick-node source target rank ht hi (Coord source κ) encode encode′ codes rec rec′ ih
    (cmp-shape source la lb (ss rank) target legal hi ht)
```
