# 换基律的模型: `SuffRA` 的前提可同时满足, 换基行非空

> 判决: 编译定理, 无前提; 只导入标准库与 `YiAbs*`, `YiFIIface`, `YiBLIface`, 不读记号. 两层玩具 (改自 `YiFIToy`: 孩子树换型成 `suc y`, 低层关系加上界 1); 高层的嵌入行是换基行 (换基层号是高层自身, 替身是 1), 辅助系统用 `YiFIIface` 的回退律; 换基律, `OutR` (含替身支配原材料), 辅助的 `Out`, `Gen⁺` 都有居民, `SuffRA` 给出 `toy-lowᴿ`.
> 模型里没有槽位, 所以副本与结点一条是空真; 换基行与它的两条出口非空. 只说明前提可满足, 不是具体块的实例 (那在 [YiBLFold](YiBLFold.lagda.md)).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBLToy where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; +-mono-≤; +-monoʳ-≤; <⇒≤; +-assoc; +-suc; +-monoʳ-<)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)

open import OCF.Lean.YiAbsFrame
open import OCF.Lean.YiAbsSim
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiAbsGRow
open import OCF.Lean.YiFIIface
open import OCF.Lean.YiBLIface

module Toy (𝕍 : Val) where
  Chᵗ : Bool → Set
  Chᵗ true  = ⊤
  Chᵗ false = ⊥

  predℕ : ℕ → ℕ
  predℕ zero    = zero
  predℕ (suc n) = n

  blk : Block
  blk = record
    { Lv = Bool ; Tr = λ _ → ℕ ; Ch = Chᵗ ; chL = λ _ _ → false ; ChT = λ _ _ → ℕ ; chT = λ _ _ y → suc y
    ; _⊑_ = λ _ _ → ⊤ ; self = tt ; inc = λ _ _ _ → tt ; incU = λ _ _ _ → tt
    ; up = λ x _ y → x + suc y ; hd = λ _ → false ; _◃_ = _<_ ; Leg = λ _ → ⊤ }

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

  Rᵗ : Bool → ℕ → ℕ → Set
  Rᵗ true  t x = t ≤ x
  Rᵗ false t x = (t ≤ 1) × (t ≤ x)

  graded : Graded blk fold rows ref 𝕍
  graded = record
    { ℓ₀ = false ; v = λ _ → Val.vz 𝕍 ; R = Rᵗ ; Rd = λ _ _ → ⊤ ; Nu = λ _ () ; bt = λ β → β
    ; cl = λ _ t → t ; Cx = λ _ _ → ℕ ; app = λ K a → K + a ; Bd = λ _ _ β K → K ≤ β }

  doms : Doms blk fold
  doms = record { Gx = λ _ _ → ⊤ ; Gb = λ _ _ → ⊤ ; Wl = λ _ → ⊤ ; Gl = λ _ _ → ⊤ }

  open FI graded doms
  open BL graded doms
  open Laws graded doms using (Weak; Lim; Node)
  open Row graded doms using (Rules)
```

系统 (目标是高层, 同 `YiFIToy.sys`) 与它的回退律, 出口; Le 取 ≤.

```agda
  sys : Sys true
  sys = record
    { St = λ _ → ℕ ; Φ = λ β x → β + x ; Ev = λ _ _ → ⊥
    ; Cxt = ℕ ; ap = λ K t → K + t ; Bdˢ = λ β K → K ≤ β }
  open Sys sys using (KeepLaw; FallLaw; Monoˢ; Out)

  keepᵗ : KeepLaw
  keepᵗ = record { slot = λ _ () ; mvc = λ _ () ; keep = λ _ () }

  fallᵗ : FallLaw
  fallᵗ = record { step = λ β _ x → β + x ; fall = λ β c x y → inj₁ (+-assoc β x (suc y)) }

  monoᵗ : Monoˢ
  monoᵗ β d = +-monoʳ-< β d

  leᵗ : ∀ (K : ℕ) {u t o : ℕ} → u ≤ t → K + t ≤ o → K + u ≤ o
  leᵗ K le r = ≤-trans (+-monoʳ-≤ K le) r

  outᵗ : Out _≤_ keepᵗ fallᵗ
  outᵗ = record
    { zeroE = λ { β K bd refl → +-mono-≤ bd z≤n }
    ; succE = λ { β K bd {x = x} (m , refl) _ q → subst₂ _≤_ (sym (+-suc K m)) (sym (+-suc β x)) (s≤s q) }
    ; limE  = λ _ _ _ ()
    ; upE   = λ β K bd c {t} r q → K + t , q , λ u → +-assoc K t u
    ; leE   = λ β K bd le r → leᵗ K le r
    ; nodeE = λ _ _ _ () }

  weakᵗ : Weak
  weakᵗ {ℓ = true}  l d       = ≤-trans l (<⇒≤ d)
  weakᵗ {ℓ = false} (b , l) d = b , ≤-trans l (<⇒≤ d)

  limᵗ : Lim
  limᵗ ()

  nodeᵗ : Node
  nodeᵗ ()

  genᵗ : ∀ a → Gen⁺ _≤_ a
  genᵗ true  Q rs le z≤n               = Rules.qz rs refl
  genᵗ true  Q rs le (s≤s l)           = Rules.q1 rs (_ , refl) l (genᵗ true Q rs le l)
  genᵗ false Q rs le (z≤n , _)         = Rules.qz rs refl
  genᵗ false Q rs le (s≤s z≤n , s≤s _) = Rules.q1 rs (zero , refl) (z≤n , z≤n) (Rules.qz rs refl)

  wfᵗ : ∀ b → WfL b
  wfᵗ true  = wf (λ _ → wf (λ ()))
  wfᵗ false = wf (λ ())
```

高层的嵌入行取换基行: 换基层号是高层, 辅助状态是 β + x, 替身是 1. 替身像不低于行的输出要用 y 分两种情形; 替身支配原材料: 低层的参照项不超过 1.

```agda
  reb₁ : ∀ β x (y : ℕ) → ((β + x) + 1 ≡ β + (x + suc y)) ⊎ ((β + x) + 1 < β + (x + suc y))
  reb₁ β x zero     = inj₁ (+-assoc β x 1)
  reb₁ β x (suc y′) = inj₂ (subst (λ z → z < β + (x + suc (suc y′))) (sym (+-assoc β x 1))
                             (+-monoʳ-< β (+-monoʳ-< x (s≤s (s≤s z≤n)))))

  rebᵗ : (β : ℕ) → RebAt sys sys keepᵗ {true} β
  rebᵗ β = record
    { Lr = λ _ _ → true ; Sr = λ _ x → β + x ; sub = λ _ _ → 1 ; reb = λ _ x y → reb₁ β x y
    ; lw = λ _ _ → tt ; cp = λ _ _ () ; cpE = λ _ _ () ; cpS = λ _ _ () }

  rowᵗ : ∀ {a} (β : ℕ) → FallAt sys sys keepᵗ {a} β ⊎ RebAt sys sys keepᵗ {a} β
  rowᵗ {a = true}  β = inj₂ (rebᵗ β)
  rowᵗ {a = false} β = inj₁ (record { step = λ () ; fall = λ () })

  embᵗ : EmbLaw sys sys keepᵗ
  embᵗ = record { row = rowᵗ }

  embEᵗ : ∀ {a} (β : ℕ) (K : ℕ) → K ≤ β → EmbOut sys sys keepᵗ embᵗ _≤_ {a} β K (rowᵗ β)
  embEᵗ {a = true}  β K bd = (λ c {t} r q → K + t , q , λ u → +-assoc K t u)
                       , (λ c {t} y r ry → 1 , s≤s z≤n , +-monoʳ-≤ t (proj₁ ry))
  embEᵗ {a = false} β K bd = λ ()

  outRᵗ : OutR sys sys keepᵗ embᵗ _≤_ keepᵗ
  outRᵗ = record
    { zeroE = Out.zeroE outᵗ ; succE = Out.succE outᵗ ; limE = λ _ _ _ () ; leE = λ β K bd le r → leᵗ K le r
    ; nodeE = Out.nodeE outᵗ ; embE = embEᵗ }

  toy-lowᴿ : (β K : ℕ) → K ≤ β → ∀ {a x} → a ≤ x → K + a ≤ β + x
  toy-lowᴿ β K bd = SuffRA.sys→low sys sys keepᵗ embᵗ _≤_ weakᵗ limᵗ nodeᵗ monoᵗ keepᵗ outRᵗ monoᵗ fallᵗ outᵗ wfᵗ genᵗ
    (wfᵗ true) β K bd tt tt β K (λ _ → refl) (λ _ → refl)
```
