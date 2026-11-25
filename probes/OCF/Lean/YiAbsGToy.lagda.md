# 抽象理论 (十二): 分级模拟的模型与否定前提的实例

> 判决: 编译定理, 无前提; 只导入标准库与 `YiAbs*`. 玩具模型 (层号, 树, 参照项都是 ℕ; 孩子下标是 `ℕ → Bool`, 没有可判定的相等; 折叠是 β + x) 满足 `GSim` 的全部十五条律, `Base`, `Keel` 与每层的 `Gen` (`gsim`, `base`, `keel`, `gen`), 充分性定理给出它的终点 (`toy-end`).
> 模型里余尾 ω 与 Ω 为空, 所以 `Lim`, `Node`, `RdL`, `RdΩ` 是空真; 它们的非空实例在具体块上 (见 [YiAbsGFin](YiAbsGFin.lagda.md)).
> 否定前提的实例: 参照折叠取 a ↦ a + a 时 `cap→¬low` 的前提全成立 (`bad-¬low`); 折叠丢掉结点的两点模型里 `unkept→¬low` 的前提全成立 (`drop-¬low`). `𝕍ᴮ` 是带严格性 `irr` 的值前序 (布劳威尔树).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAbsGToy where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-mono-≤; <⇒≤)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiAbsFrame
open import OCF.Lean.YiAbsSim
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiAbsGSuff
open import OCF.Lean.YiAbsGRow
open import OCF.Lean.YiAbsGNeg
```

## 带严格性的值前序

```agda
data O : Set where
  oz : O
  os : O → O
  ol : (ℕ → O) → O

infix 4 _≤ᴼ_
data _≤ᴼ_ : O → O → Set where
  z≤ : ∀ {b} → oz ≤ᴼ b
  s≤ : ∀ {a b} → a ≤ᴼ b → os a ≤ᴼ os b
  ≤l : ∀ {a f} n → a ≤ᴼ f n → a ≤ᴼ ol f
  l≤ : ∀ {f b} → (∀ n → f n ≤ᴼ b) → ol f ≤ᴼ b

reflᴼ : ∀ a → a ≤ᴼ a
reflᴼ oz     = z≤
reflᴼ (os a) = s≤ (reflᴼ a)
reflᴼ (ol f) = l≤ (λ n → ≤l n (reflᴼ (f n)))

transᴼ : ∀ {a b c} → a ≤ᴼ b → b ≤ᴼ c → a ≤ᴼ c
transᴼ z≤       q        = z≤
transᴼ (l≤ p)   q        = l≤ (λ n → transᴼ (p n) q)
transᴼ (s≤ p)   (s≤ q)   = s≤ (transᴼ p q)
transᴼ (s≤ p)   (≤l n q) = ≤l n (transᴼ (s≤ p) q)
transᴼ (≤l n p) (≤l m q) = ≤l m (transᴼ (≤l n p) q)
transᴼ (≤l n p) (l≤ q)   = transᴼ p (q n)

≤sᴼ : ∀ a → a ≤ᴼ os a
≤sᴼ oz     = z≤
≤sᴼ (os a) = s≤ (≤sᴼ a)
≤sᴼ (ol f) = l≤ (λ n → transᴼ (≤sᴼ (f n)) (s≤ (≤l n (reflᴼ (f n)))))

irrᴼ : ∀ a → os a ≤ᴼ a → ⊥
irrᴼ (os a) (s≤ p)   = irrᴼ a p
irrᴼ (ol f) (≤l n p) = irrᴼ (f n) (transᴼ (s≤ (≤l n (reflᴼ (f n)))) p)

𝕍ᴮ : Val
𝕍ᴮ = record
  { V = O ; _≼_ = _≤ᴼ_ ; ≼-refl = λ {a} → reflᴼ a ; ≼-trans = transᴼ
  ; vz = oz ; vs = os ; vl = ol ; z≼ = z≤ ; s≼s = s≤ ; l≼ = l≤ ; ≼s = λ {a} → ≤sᴼ a }
```

## 玩具模型

f 是参照一侧折到低层的作用 (`app K a = K + f a`). 层号 n 读作不高于 n 的下标; 第 n 层的 Ω 树是 n + 1; 把树 x 读成层号就是 x.

```agda
module Toy (f : ℕ → ℕ) (𝕍 : Val) where
  open Val 𝕍 using (V; z≼; s≼s)
  open Fin 𝕍 using (val)

  predℕ : ℕ → ℕ
  predℕ zero    = zero
  predℕ (suc n) = n

  blk : Block
  blk = record
    { Lv = ℕ ; Tr = λ _ → ℕ ; Ch = λ _ → ℕ → Bool ; chL = λ ℓ _ → ℓ ; ChT = λ _ _ → ℕ ; chT = λ _ _ y → y
    ; _⊑_ = λ _ _ → ⊤ ; self = tt ; inc = λ _ _ _ → tt ; incU = λ _ _ _ → tt
    ; up = λ x _ y → x + y ; hd = λ _ → false ; _◃_ = _<_ ; Leg = λ _ → ⊤ }

  fold : Fold blk
  fold = record
    { Bs = λ _ → ⊤ ; LegB = λ _ _ → ⊤ ; Bt = λ _ → ℕ ; LegT = λ _ _ → ⊤
    ; ψ = λ _ _ _ _ β x → β + x ; ψβ = λ _ _ _ _ β x → β + x ; dn = λ _ _ _ _ → tt }

  rows : Rows blk fold
  rows = record
    { sc = suc ; Sl = λ _ → ⊥ ; slL = λ _ () ; SlT = λ _ () ; slT = λ _ () ; nd = λ ()
    ; Ωt = suc ; Dn = λ _ _ → ⊤ ; upf = λ _ β y → β + y
    ; sucL = suc ; ΩL = λ k _ → k ; lift = λ _ x → x }

  ref : Ref
  ref = record
    { T = ℕ ; C0 = λ t → t ≡ 0 ; C1 = λ t → Σ ℕ λ m → t ≡ suc m ; Cω = λ _ → ⊥ ; CΩ = λ _ _ → ⊥
    ; pred = predℕ ; fsn = λ t _ → t ; fsT = λ t _ → t ; _⊕_ = _+_ ; Ωr = suc }

  graded : Graded blk fold rows ref 𝕍
  graded = record
    { ℓ₀ = 0 ; v = val ; R = λ _ t x → t ≤ x ; Rd = λ ℓ ν → ν ≤ ℓ ; Nu = λ _ () ; bt = λ β → β
    ; cl = λ _ t → t ; Cx = λ _ _ → ℕ ; app = λ K a → K + f a ; Bd = λ _ _ β K → K ≤ β }

  doms : Doms blk fold
  doms = record { Gx = λ _ _ → ⊤ ; Gb = λ _ _ → ⊤ ; Wl = λ _ → ⊤ ; Gl = λ _ _ → ⊤ }

  open Laws graded doms using (Base; HC; h0; h1; tree; Zero; Succ; Lim; Weak; Node; Emb; SelfKeep; UpKeep; Rd0; RdS; RdL; RdΩ; Leaf; Lift)
  open Row graded doms using (Gen; Rules)

  val-mono : ∀ {m n} → m ≤ n → Val._≼_ 𝕍 (val m) (val n)
  val-mono z≤n     = z≼
  val-mono (s≤s l) = s≼s (val-mono l)

  base : Base
  base = record
    { G₀ = λ _ → ⊤ ; _⇝ˢ_ = λ x y → suc x ≤ y ; _⇝_ = λ _ _ → ⊥
    ; strict = λ _ l → val-mono l ; weak = λ _ ()
    ; inv1 = λ { l _ (m , refl) → m , ≤-refl , tt , l } ; invω = λ _ _ () }

  hc : ∀ t → HC t
  hc zero    = h0 refl
  hc (suc m) = h1 (m , refl) (hc m)

  gen : ∀ ℓ → Gen ℓ
  gen ℓ Q rs z≤n     = Rules.qz rs refl
  gen ℓ Q rs (s≤s l) = Rules.q1 rs (_ , refl) l (gen ℓ Q rs l)
```

与 f 无关的十四条律.

```agda
  zeroᵀ : Zero
  zeroᵀ refl = z≤n

  succᵀ : Succ
  succᵀ (m , refl) l = s≤s l

  limᵀ : Lim
  limᵀ ()

  weakᵀ : Weak
  weakᵀ l d = ≤-trans l (<⇒≤ d)

  nodeᵀ : Node
  nodeᵀ ()

  embᵀ : Emb
  embᵀ c y l l′ = +-mono-≤ l l′

  selfᵀ : SelfKeep
  selfᵀ b β gb l l′ = +-mono-≤ l l′

  upᵀ : UpKeep
  upᵀ d β l l′ = +-mono-≤ l l′

  rd0ᵀ : Rd0
  rd0ᵀ refl = z≤n

  rdSᵀ : RdS
  rdSᵀ (m , refl) l = s≤s l

  rdLᵀ : RdL
  rdLᵀ ()

  rdΩᵀ : RdΩ
  rdΩᵀ h ()

  leafᵀ : Leaf
  leafᵀ l = s≤s l

  liftᵀ : Lift
  liftᵀ _ l = l
```

## f 取恒等: 全部律, 塔, 终点

```agda
module Good (𝕍 : Val) where
  open Val 𝕍 using (V; _≼_; vl)
  open Fin 𝕍 using (val)
  open Toy (λ a → a) 𝕍
  open Laws graded doms using (GSim; Keel; LowKeep; tree)
  open Suff graded doms

  lowᵀ : LowKeep
  lowᵀ b w β K gb wl bd gx l = +-mono-≤ bd l

  gsim : GSim
  gsim = record
    { zeroᴿ = zeroᵀ ; succᴿ = succᵀ ; limᴿ = limᵀ ; weakᴿ = weakᵀ ; nodeᴿ = nodeᵀ ; embᴿ = embᵀ
    ; selfᴷ = selfᵀ ; upᴷ = upᵀ ; lowᴷ = lowᵀ
    ; rd0 = rd0ᵀ ; rdS = rdSᵀ ; rdL = rdLᵀ ; rdΩ = rdΩᵀ ; leaf = leafᵀ ; liftᴿ = liftᵀ }

  keel : Keel base
  keel = record
    { tw = λ n → n ; κ₀ = 0 ; rd-tw0 = z≤n ; tw-step = λ n l → l ; gl = λ _ → tt
    ; b₀ = λ _ → tt ; w₀ = λ _ → tt ; β₀ = λ _ → 0 ; K₀ = λ _ → 0
    ; gb = λ _ → tt ; wl = λ _ → tt ; bd = λ _ → z≤n ; gx = λ _ → tt ; g₀ = λ _ → tt }

  open Keel keel using (row; twc)

  toy-K : ∀ n → tree (hc (row n)) ≼ val (suc n)
  toy-K n = FromGSim.Kᴳ gsim keel n (hc (row n))

  toy-end : (Y : V) → (∀ n → val (suc n) ≼ Y) → vl (λ n → tree (hc (row n))) ≼ Y
  toy-end Y up = FromGSim.endpointᴳ gsim keel Y up (λ n → hc (row n))
```

## 值封顶的前提可满足

参照折叠取 a ↦ a + a, 树一侧仍是加法: 其余律不变, `LowKeep` 不成立.

```agda
module Bad where
  open Toy (λ a → a + a) 𝕍ᴮ
  open Laws graded doms using (LowKeep)
  open Neg graded doms

  bad-¬low : LowKeep → ⊥
  bad-¬low = Cap.cap→¬low (λ {a} → irrᴼ a) base {ℓ = 0} tt tt 0 0 tt tt z≤n {a = 1} {x = 1} tt (s≤s z≤n) tt
    (hc 2) (os oz) (reflᴼ (os oz)) (reflᴼ (os (os oz)))
```

## 槽位不保留的前提可满足

一层, 树与参照项都是两点 (`false` 是零, `true` 是结点与 Ω), 关系是 "t 为 Ω 时 x 为结点", 折叠恒为零 (不保留结点).

```agda
module Drop where
  blk² : Block
  blk² = record
    { Lv = ⊤ ; Tr = λ _ → Bool ; Ch = λ _ → ⊥ ; chL = λ _ _ → tt ; ChT = λ _ _ → ⊤ ; chT = λ _ ()
    ; _⊑_ = λ _ _ → ⊤ ; self = tt ; inc = λ _ _ _ → tt ; incU = λ _ _ _ → tt
    ; up = λ x _ _ → x ; hd = λ x → x ; _◃_ = λ x y → (x ≡ false) × (y ≡ true) ; Leg = λ _ → ⊤ }

  fold² : Fold blk²
  fold² = record
    { Bs = λ _ → ⊤ ; LegB = λ _ _ → ⊤ ; Bt = λ _ → ⊤ ; LegT = λ _ _ → ⊤
    ; ψ = λ _ _ _ _ _ _ → false ; ψβ = λ _ _ _ _ _ _ → tt ; dn = λ _ _ _ _ → tt }

  rows² : Rows blk² fold²
  rows² = record
    { sc = λ x → x ; Sl = λ _ → ⊤ ; slL = λ _ _ → tt ; SlT = λ _ _ → Bool ; slT = λ _ _ c → c ; nd = λ _ _ → true
    ; Ωt = λ _ → true ; Dn = λ _ _ → ⊤ ; upf = λ _ _ y → y ; sucL = λ ℓ → ℓ ; ΩL = λ k _ → k ; lift = λ k _ → k }

  ref² : Ref
  ref² = record
    { T = Bool ; C0 = λ t → t ≡ false ; C1 = λ _ → ⊥ ; Cω = λ _ → ⊥ ; CΩ = λ t _ → t ≡ true
    ; pred = λ t → t ; fsn = λ t _ → t ; fsT = λ _ _ → false ; _⊕_ = _∨_ ; Ωr = λ _ → true }

  graded² : Graded blk² fold² rows² ref² 𝕍ᴮ
  graded² = record
    { ℓ₀ = tt ; v = λ _ → oz ; R = λ _ t x → t ≡ true → x ≡ true ; Rd = λ _ _ → ⊤ ; Nu = λ _ _ _ → ⊤
    ; bt = λ _ → false ; cl = λ _ t → t ; Cx = λ _ _ → ⊤ ; app = λ _ a → a ; Bd = λ _ _ _ _ → ⊤ }

  doms² : Doms blk² fold²
  doms² = record { Gx = λ _ _ → ⊤ ; Gb = λ _ _ → ⊤ ; Wl = λ _ → ⊤ ; Gl = λ _ _ → ⊤ }

  open Laws graded² doms² using (LowKeep)
  open Row graded² doms² using (Gen; Rules)
  open Neg graded² doms²

  gen² : Gen tt
  gen² Q rs {t = false}              r = Rules.qz rs refl
  gen² Q rs {t = true} {x = true}   r = Rules.qΩ rs tt {κ = true} (λ _ → false) refl tt (λ _ _ _ ()) (λ _ _ _ → Rules.qz rs refl)
  gen² Q rs {t = true} {x = false}  r with r refl
  ... | ()

  drop-¬low : LowKeep → ⊥
  drop-¬low = Inv.unkept→¬low gen² true (λ o → o ≡ true)
    (λ { refl () }) (λ ()) (λ ()) (λ _ _ → refl) (λ _ d → proj₂ d) (λ ())
    tt tt tt tt tt tt tt {a = true} {x = true} tt (λ _ → refl) refl (λ ())
```
