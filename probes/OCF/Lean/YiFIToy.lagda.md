# 整体接口的模型: 充分性的前提可满足

> 判决: 编译定理, 无前提; 只导入标准库与 `YiAbs*`, `YiFIIface`. 两层的玩具模型 (层号是 `Bool`, 高层有一个孩子指向低层, 树与参照项是 ℕ, 嵌入是加法, 折叠是 β + x) 上, `WfL`, `KeepLaw`, `FallLaw`, `Monoˢ`, `Out`, `Gen⁺` 都有居民, 充分性给出 `toy-low`.
> 模型里没有槽位, 余尾 ω 与 Ω 为空, 所以保留律与出口的结点一条是空真; 嵌入一行与上下文的交接非空. 非空的保留律在具体块上 ([YiFIFold](YiFIFold.lagda.md) 的 `keepᴷ`), 它的出口没有实填.
> `YiAbsGToy` 的模型孩子层等于本层, 不满足 `WfL`, 所以另写这一个.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFIToy where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; +-mono-≤; <⇒≤; +-assoc; +-suc; +-monoʳ-<)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst₂)

open import OCF.Lean.YiAbsFrame
open import OCF.Lean.YiAbsSim
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiAbsGRow
open import OCF.Lean.YiFIIface

module Toy (𝕍 : Val) where
  Chᵗ : Bool → Set
  Chᵗ true  = ⊤
  Chᵗ false = ⊥

  predℕ : ℕ → ℕ
  predℕ zero    = zero
  predℕ (suc n) = n

  blk : Block
  blk = record
    { Lv = Bool ; Tr = λ _ → ℕ ; Ch = Chᵗ ; chL = λ _ _ → false ; ChT = λ _ _ → ℕ ; chT = λ _ _ y → y
    ; _⊑_ = λ _ _ → ⊤ ; self = tt ; inc = λ _ _ _ → tt ; incU = λ _ _ _ → tt
    ; up = λ x _ y → x + y ; hd = λ _ → false ; _◃_ = _<_ ; Leg = λ _ → ⊤ }

  fold : Fold blk
  fold = record
    { Bs = λ _ → ⊤ ; LegB = λ _ _ → ⊤ ; Bt = λ _ → ℕ ; LegT = λ _ _ → ⊤
    ; ψ = λ _ _ _ _ β x → β + x ; ψβ = λ _ _ _ _ β x → β + x ; dn = λ _ _ _ _ → tt }

  rows : Rows blk fold
  rows = record
    { sc = suc ; Sl = λ _ → ⊥ ; slL = λ _ () ; SlT = λ _ () ; slT = λ _ () ; nd = λ ()
    ; Ωt = λ _ → 1 ; Dn = λ _ _ → ⊤ ; upf = λ _ β y → β + y
    ; sucL = λ ℓ → ℓ ; ΩL = λ k _ → k ; lift = λ k _ → k }

  ref : Ref
  ref = record
    { T = ℕ ; C0 = λ t → t ≡ 0 ; C1 = λ t → Σ ℕ λ m → t ≡ suc m ; Cω = λ _ → ⊥ ; CΩ = λ _ _ → ⊥
    ; pred = predℕ ; fsn = λ t _ → t ; fsT = λ t _ → t ; _⊕_ = _+_ ; Ωr = suc }

  graded : Graded blk fold rows ref 𝕍
  graded = record
    { ℓ₀ = false ; v = λ _ → Val.vz 𝕍 ; R = λ _ t x → t ≤ x ; Rd = λ _ _ → ⊤ ; Nu = λ _ () ; bt = λ β → β
    ; cl = λ _ t → t ; Cx = λ _ _ → ℕ ; app = λ K a → K + a ; Bd = λ _ _ β K → K ≤ β }

  doms : Doms blk fold
  doms = record { Gx = λ _ _ → ⊤ ; Gb = λ _ _ → ⊤ ; Wl = λ _ → ⊤ ; Gl = λ _ _ → ⊤ }

  open FI graded doms
  open Laws graded doms using (Weak; Lim; Node)
  open Row graded doms using (Rules)

  No : ℕ → ℕ → Set
  No _ _ = ⊥

  sys : Sys false
  sys = record
    { St = λ _ → ℕ ; Φ = λ β x → β + x ; Ev = λ _ _ → ⊥
    ; Cxt = ℕ ; ap = λ K t → K + t ; Bdˢ = λ β K → K ≤ β }
  open Sys sys

  keepᵗ : KeepLaw
  keepᵗ = record { slot = λ _ () ; mvc = λ _ () ; keep = λ _ () }

  fallᵗ : FallLaw
  fallᵗ = record { step = λ β _ x → β + x ; fall = λ β c x y → inj₁ (+-assoc β x y) }

  monoᵗ : Monoˢ
  monoᵗ β d = +-monoʳ-< β d

  outᵗ : Out No keepᵗ fallᵗ
  outᵗ = record
    { zeroE = λ { β K bd refl → +-mono-≤ bd z≤n }
    ; succE = λ { β K bd {x = x} (m , refl) _ q → subst₂ _≤_ (sym (+-suc K m)) (sym (+-suc β x)) (s≤s q) }
    ; limE  = λ _ _ _ ()
    ; upE   = λ β K bd c {t} r q → K + t , q , λ u → +-assoc K t u
    ; leE   = λ _ _ _ ()
    ; nodeE = λ _ _ _ () }

  weakᵗ : Weak
  weakᵗ l d = ≤-trans l (<⇒≤ d)

  limᵗ : Lim
  limᵗ ()

  nodeᵗ : Node
  nodeᵗ ()

  genᵗ : ∀ a → Gen⁺ No a
  genᵗ a Q rs le z≤n     = Rules.qz rs refl
  genᵗ a Q rs le (s≤s l) = Rules.q1 rs (_ , refl) l (genᵗ a Q rs le l)

  wfᵗ : WfL true
  wfᵗ = wf (λ _ → wf (λ ()))

  toy-low : (β K : ℕ) → K ≤ β → ∀ {a x} → a ≤ x → K + a ≤ β + x
  toy-low β K bd = Suff.sys→low No weakᵗ limᵗ nodeᵗ monoᵗ keepᵗ fallᵗ outᵗ genᵗ wfᵗ β K bd tt tt β K (λ _ → refl) (λ _ → refl)
```
