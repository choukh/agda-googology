# 结点内完备不推出层号全序（验收反例）
编译定理：四点分叉块的每个允许结点均有可靠全派发，证据对给定 ψ 封闭，原层序仍无全序。
每个层号都出现在结点中；不可比的 left、right 同有字面上界 cap。缺的是两者共现，不是单点覆盖。
这是有限玩具接口的反例，不满足主线折叠方程，也不否定写法 A 或树自足。前提先在临时文件编译。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTDDiamond where

open import Data.Bool.Base using (Bool; false; true)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (tt)
open import Relation.Binary.Structures using (IsDecTotalOrder)
import Relation.Binary.Construct.StrictToNonStrict as SN
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _×_; _,_)
open import Relation.Binary.Definitions using (Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst₂)
open import OCF.Lean.YiTDIface
import OCF.Lean.YiTDOrder as Order

data Level : Set where
  root left right cap : Level

tip : Bool → Level
tip false = left
tip true = right

data _≺_ : Level → Level → Set where
  rl : root ≺ left
  rr : root ≺ right
  lc : left ≺ cap
  rc : right ≺ cap
  zc : root ≺ cap

trans≺ : Transitive _≺_
trans≺ rl lc = zc
trans≺ rr rc = zc
trans≺ lc ()
trans≺ rc ()
trans≺ zc ()

irrefl≺ : ∀ {x} → x ≺ x → ⊥
irrefl≺ {x = root} ()
irrefl≺ {x = left} ()
irrefl≺ {x = right} ()
irrefl≺ {x = cap} ()

frame : Frame
frame = record { A = Level; _<_ = _≺_; trans = trans≺; irrefl = irrefl≺ }

open On frame

data Slot : Set where
  lo mid hi : Slot

label : Bool → Slot → Level
label s lo = root
label s mid = tip s
label s hi = cap

nodes : Nodes
nodes = record { Node = Bool; Child = λ _ → Slot; label = label }

below : ∀ s → root ≺ tip s
below false = rl
below true = rr

above : ∀ s → tip s ≺ cap
above false = lc
above true = rc

node-answer : ∀ s c d → Answer (label s c) (label s d)
node-answer s lo lo = inj₂ (inj₁ refl)
node-answer s lo mid = inj₁ (below s)
node-answer s lo hi = inj₁ zc
node-answer s mid lo = inj₂ (inj₂ (below s))
node-answer s mid mid = inj₂ (inj₁ refl)
node-answer s mid hi = inj₁ (above s)
node-answer s hi lo = inj₂ (inj₂ zc)
node-answer s hi mid = inj₂ (inj₂ (above s))
node-answer s hi hi = inj₂ (inj₁ refl)

local : Evidence (Scope nodes)
local = record
  { E = Scope nodes
  ; answer = λ x y → λ { (s , c , d , ex , ey) → subst₂ Answer ex ey (node-answer s c d) }
  ; provide = λ _ _ e → e }

ψ : Level → Level
ψ root = root
ψ left = root
ψ right = root
ψ cap = left

slotψ : Level → Slot
slotψ root = lo
slotψ left = lo
slotψ right = lo
slotψ cap = mid

labelψ : ∀ x → label false (slotψ x) ≡ ψ x
labelψ root = refl
labelψ left = refl
labelψ right = refl
labelψ cap = refl

closed : ∀ x y → Scope nodes (ψ x) (ψ y)
closed x y = false , slotψ x , slotψ y , labelψ x , labelψ y

bounded : (left ≺ cap) × (right ≺ cap)
bounded = lc , rc

left-not-right : Answer left right → ⊥
left-not-right (inj₁ ())
left-not-right (inj₂ (inj₁ ()))
left-not-right (inj₂ (inj₂ ()))

member : ∀ x → Σ Bool λ s → Σ Slot λ c → label s c ≡ x
member root = false , lo , refl
member left = false , mid , refl
member right = true , mid , refl
member cap = false , hi , refl

ψ-closed : Closed ψ (Scope nodes)
ψ-closed {x} {y} _ = closed x y

no-global : Evidence Global → ⊥
no-global D = left-not-right (Evidence.answer D left right (Evidence.provide D left right tt))

no-cover : Covers nodes → ⊥
no-cover cover = no-global (Order.Theorems.scoped→global frame local cover)

no-notation : Notation → ⊥
no-notation N = no-global (Order.Theorems.notation→global frame N)

no-order : IsDecTotalOrder _≡_ (SN._≤_ _≡_ _≺_) → ⊥
no-order O with IsDecTotalOrder.total O left right
... | inj₁ (inj₁ ())
... | inj₁ (inj₂ ())
... | inj₂ (inj₁ ())
... | inj₂ (inj₂ ())

```
