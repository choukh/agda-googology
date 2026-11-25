# YiSuc 并行：第 1 层右结合和式上，主线折叠对参照两向

**验收文件，档位：编译定理。** 主线第 1 层的右结合和式 `X′ + (Y₁ + (… + Z))` 与参照 `X + (A₁ + (… + Z))` (语境 `CtxM`, `CtxR`) 逐项并行：`par`：语境两向 (`S`) 时，尾部再接 `M a = Ψ₁ a` 与 `F₁ (read a)` 仍两向，对一切合法的第 0 层树 a。
结点 (尾部是 Ω₁ 与 `top`) 由 [YiSucNode](YiSucNode.lagda.md) 处理，主线的累加链经吸收对上参照的链，对数取 `flat`；后继与 ℕ 极限是 ω 倍错开一位。不比较不并行的和式 (`top + M a` 对 `F₁ (read a)` 的吸收在 [YiSucAbs](YiSucAbs.lagda.md))。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSucPar where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import OCF.Lean.YiLeanCore
open import OCF.Lean.YiLeanFold
open import OCF.Lean.YiLeanLegal using (plus-lgl; chain-lgl; Ψ-lgl)
open import OCF.Lean.YiLeanTw3 using (R)
open import OCF.Lean.YiLeanAccFin using (read; read-plus)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl)
open import OCF.Align.YiVmConExact using (_≼ˣ_; ≼lˣ; lˣ; reflˣ; ≅→≼ˣ; ˣ→≼; ⊑→≼ˣ)
open import OCF.Lean.YiZeroAccP using (ψ⁰ˣ; +ˣ)
open import OCF.Lean.YiChainBase using (T₀; transˣ)
open import OCF.Lean.YiChainOne using (cc; Gc; module Phi)
open import OCF.Lean.YiChainBack using (GcR; module PhiR)
open import OCF.Lean.YiChainFlat using (flat; ψ⁰-flat)
open import OCF.Lean.YiFlatObs using (Good; Good-add; Good-Ω; Good-ψ; Good-tr⁻; gu; HS-flat)
open import OCF.Lean.YiUBRed using (Two)
open import OCF.Lean.YiSucLx using (T₁; F₁)
open import OCF.Lean.YiSucGood using (good-read)
open import OCF.Lean.YiSucNode using (module Chains; module NodeTwo)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
```

## 1 语境

`D ▸ A` 在最里层接一项：`plugR X (D ▸ A) Z = plugR X D (A + Z)`，于是加长语境不需要结合律。

```agda
L1 : LF
L1 = suc zero

R₁ : Set
R₁ = Raw L1

Ω₁ : T₁
Ω₁ = L.Ω (L.suc L.zero)

infixl 5 _▸_
data CtxR : Set where
  ε : CtxR
  _▸_ : CtxR → T₁ → CtxR

data CtxM : Set where
  ε : CtxM
  _▸_ : CtxM → R₁ → CtxM

plugR : T₁ → CtxR → T₁ → T₁
plugR X ε Z = X L.+ Z
plugR X (D ▸ A) Z = plugR X D (A L.+ Z)

plugM : R₁ → CtxM → R₁ → R₁
plugM X ε Z = plus L1 X Z
plugM X (C ▸ Y) Z = plugM X C (plus L1 Y Z)

pR-suc : ∀ X D Z → plugR X D (L.suc Z) ≡ L.suc (plugR X D Z)
pR-suc X ε Z = refl
pR-suc X (D ▸ A) Z = pR-suc X D (A L.+ Z)

pR-lim : ∀ X D (F : ℕ → T₁) → plugR X D (L.lim F) ≡ L.lim (λ n → plugR X D (F n))
pR-lim X ε F = refl
pR-lim X (D ▸ A) F = pR-lim X D (λ n → A L.+ F n)

pR-node : ∀ X D (g : T₀ → T₁) → plugR X D (L.limᵢ {i = L.zero} L.zero g) ≡ L.limᵢ L.zero (λ y → plugR X D (g y))
pR-node X ε g = refl
pR-node X (D ▸ A) g = pR-node X D (λ y → A L.+ g y)

pR-up0 : ∀ X D → plugR X D (L.up L.zero L.zero) ≡ plugR X D L.zero
pR-up0 X ε = refl
pR-up0 X (D ▸ A) = refl

pR-upS : ∀ X D (y : T₀) → plugR X D (L.up L.zero (L.suc y)) ≡ L.suc (plugR X D (L.up L.zero y))
pR-upS X ε y = refl
pR-upS X (D ▸ A) y = pR-suc X D (A L.+ L.up L.zero y)

pR-upL : ∀ X D (f : ℕ → T₀) → plugR X D (L.up L.zero (L.lim f)) ≡ L.lim (λ n → plugR X D (L.up L.zero (f n)))
pR-upL X ε f = refl
pR-upL X (D ▸ A) f = pR-lim X D (λ n → A L.+ L.up L.zero (f n))

pM-suc : ∀ X C Z → plugM X C (G.suc Z) ≡ G.suc (plugM X C Z)
pM-suc X ε Z = refl
pM-suc X (C ▸ Y) Z = pM-suc X C (plus L1 Y Z)

pM-lim : ∀ X C (F : ℕ → R₁) → plugM X C (G.lim F) ≡ G.lim (λ n → plugM X C (F n))
pM-lim X ε F = refl
pM-lim X (C ▸ Y) F = pM-lim X C (λ n → plus L1 Y (F n))

pM-node : ∀ X C (g : R → R₁) → plugM X C (G.lc (inj₁ tt) g) ≡ G.lc (inj₁ tt) (λ η → plugM X C (g η))
pM-node X ε g = refl
pM-node X (C ▸ Y) g = pM-node X C (λ η → plus L1 Y (g η))

pM-top : ∀ X C → plugM X C G.top ≡ G.lc (inj₁ tt) (λ η → plugM X C (G.em tt η))
pM-top X ε = refl
pM-top X (C ▸ Y) = pM-node X C (λ η → plus L1 Y (G.em tt η))

pM-em0 : ∀ X C → plugM X C (G.em tt G.zero) ≡ plugM X C G.zero
pM-em0 X ε = refl
pM-em0 X (C ▸ Y) = refl

pM-emS : ∀ X C a → plugM X C (G.em tt (G.suc a)) ≡ G.suc (plugM X C (G.em tt a))
pM-emS X ε a = refl
pM-emS X (C ▸ Y) a = pM-suc X C (plus L1 Y (G.em tt a))

pM-emL : ∀ X C (f : ℕ → R) → plugM X C (G.em tt (G.lim f)) ≡ G.lim (λ n → plugM X C (G.em tt (f n)))
pM-emL X ε f = refl
pM-emL X (C ▸ Y) f = pM-lim X C (λ n → plus L1 Y (G.em tt (f n)))

pM-emT : ∀ X C → plugM X C (G.em tt G.top) ≡ G.suc (plugM X C G.zero)
pM-emT X ε = refl
pM-emT X (C ▸ Y) = pM-suc X C Y
```

## 2 第 0 层的小引理

`Ψ⁰ x` 是主线第 1 层的树折到第 0 层 (派发 `x` 只能折叠)。`succ²`：ω 倍错开一位的两向版 (`Phi.succPHI` 与 `PhiR.succR`)。

```agda
Ψ⁰ : Ext zero L1 → R₁ → R
Ψ⁰ x = Ψ zero (vs v0) x

x₀ : Ext zero zero
x₀ = λ _ → fold

succ² : ∀ {A : T₀} (y : R) → Two A (read y) → Two (L.lim (iterᴸ (A L.+_) L.zero)) (read (succ zero y))
succ² y (p , q) = proj₁ (Phi.succPHI x₀ y p (ˣ→≼ q)) , proj₁ (PhiR.succR x₀ y q (ˣ→≼ p))

Z0 : ∀ (x : Ext zero zero) a → L.𝟎 {L.zero} L.≺ read (Ψ zero v0 x a)
Z0 x G.zero = L.≺z L.z≅
Z0 x (G.suc a) = L.≺l 0 (Z0 x a)
Z0 x (G.lim f) = L.≺l 0 (Z0 x (f 0))
Z0 x (G.lc () g)
Z0 x (G.em () a)
Z0 x G.top = L.≺l 0 (L.≺z L.z≅)

Zn : ∀ (w : Way zero zero) gm gk → L.𝟎 {L.zero} L.≺ read (gm G.top) → L.𝟎 {L.zero} L.≺ read (Ψn zero zero w gm gk)
Zn (keep () q) gm gk h
Zn fold gm gk h = L.≺l 0 h

Z1 : ∀ (x : Ext zero L1) ξ → L.𝟎 {L.zero} L.≺ read (Ψ⁰ x ξ)
Z1 x G.zero = L.≺z L.z≅
Z1 x (G.suc a) = L.≺l 0 (Z1 x a)
Z1 x (G.lim f) = L.≺l 0 (Z1 x (f 0))
Z1 x (G.lc (inj₁ tt) g) = Zn (x (inj₁ tt)) _ _ (Z1 x (g G.top))
Z1 x (G.lc (inj₂ ()) g)
Z1 x (G.em tt a) = Z0 _ a
Z1 x G.top = Zn (x (inj₁ tt)) _ _ (L.≺l 0 (L.≺z L.z≅))

+≺ : ∀ (B : T₀) {x y : T₀} → x L.≺ y → (B L.+ x) L.≺ (B L.+ y)
+≺ B (L.≺z e) = L.≺z (L.add-≅ (L.≅-refl⁰ B) e)
+≺ B (L.≺s d) = L.≺s (+≺ B d)
+≺ B (L.≺l n d) = L.≺l n (+≺ B d)
+≺ B (L.≺i {p = ()} z ez d)
+≺ B (L.≺u {r = ()} d)

lead : ∀ (X : T₀) {Y : T₀} → L.𝟎 {L.zero} L.≺ Y → X L.≺ (X L.+ Y)
lead X (L.≺z L.z≅) = L.≺z (L.≅-refl⁰ X)
lead X (L.≺z (L.upʳ {r = ()} e))
lead X (L.≺s d) = L.≺s (lead X d)
lead X (L.≺l n d) = L.≺l n (lead X d)
lead X (L.≺i {p = ()} x ex d)
lead X (L.≺u {r = ()} d)
```

`fl⊑`：压平后，左加数在和之下 (沿第一支下降)。

```agda
fl⊑ : ∀ {k ℓ} (X : L.Ordᶜ ℓ) (σ : L.Simᴵ k ℓ) (Z : L.Ordᶜ k) → flat X L.⊑ flat (L.add X σ Z)
fl⊑ X σ L.zero h = h
fl⊑ X σ (L.suc Z) h = L.≺s (fl⊑ X σ Z h)
fl⊑ X σ (L.lim F) h = L.≺l 0 (fl⊑ X σ (F 0) h)
fl⊑ X σ (L.limᵢ {i = j} q f) h =
  L.≺l 0 (fl⊑ X σ (f (L.coe (L.<→◃ (σ q)) (L.<→◃ q) (L.into (L.<→◃ (σ q)) (L.Ω j)))) h)
fl⊑ X σ (L.up L.zero x) h = fl⊑ X (λ q → σ (L.suc q)) x h
fl⊑ X σ (L.up (L.self n) x) h = fl⊑ X (λ q → σ (L.lim n q)) x h
```

## 3 第 1 层的起点：Ω₁ 对 `top`，派发任意

```agda
baseΩ : ∀ (x : Ext zero L1) → Two (L.ψ⁰ Ω₁) (read (Ψ⁰ x G.top))
baseΩ x = go (x (inj₁ tt))
  where
  go : ∀ (w : Way zero zero) →
    Two (L.ψ⁰ Ω₁) (read (Ψn zero zero w (λ η → Ψ zero v0 (λ r → x (inj₂ r)) η) (λ η → Ψ zero v0 (self zero) η)))
  go (keep () q)
  go fold =
    lˣ (λ k → ≼lˣ k (transˣ (ψ⁰ˣ (Gc k)) (proj₁ (Phi.PHI (λ r → x (inj₂ r)) (cc k))))) ,
    lˣ (λ k → ≼lˣ k (transˣ (proj₁ (PhiR.PHIR (λ r → x (inj₂ r)) (cc k))) (ψ⁰ˣ (GcR k))))
```

## 4 尾部是第 0 层的树

```agda
Two-sub : ∀ {A A′ B B′ : T₀} → A ≡ A′ → B ≡ B′ → Two A B → Two A′ B′
Two-sub refl refl t = t

module Tail (X : T₁) (D : CtxR) (X′ : R₁) (C : CtxM)
  (base : ∀ x → Two (L.ψ⁰ (plugR X D L.zero)) (read (Ψ⁰ x (plugM X′ C G.zero)))) where

  tail : ∀ x a → Two (L.ψ⁰ (plugR X D (L.up L.zero (read a)))) (read (Ψ⁰ x (plugM X′ C (G.em tt a))))
  tail x G.zero = Two-sub (cong L.ψ⁰ (sym (pR-up0 X D))) (cong (λ t → read (Ψ⁰ x t)) (sym (pM-em0 X′ C))) (base x)
  tail x (G.suc a) = Two-sub (cong L.ψ⁰ (sym (pR-upS X D (read a)))) (cong (λ t → read (Ψ⁰ x t)) (sym (pM-emS X′ C a)))
    (succ² (Ψ⁰ x (plugM X′ C (G.em tt a))) (tail x a))
  tail x (G.lim f) = Two-sub (cong L.ψ⁰ (sym (pR-upL X D (λ n → read (f n))))) (cong (λ t → read (Ψ⁰ x t)) (sym (pM-emL X′ C f)))
    (lˣ (λ n → ≼lˣ n (proj₁ (tail x (f n)))) , lˣ (λ n → ≼lˣ n (proj₂ (tail x (f n)))))
  tail x (G.lc () g)
  tail x (G.em () a)
  tail x G.top = Two-sub (cong L.ψ⁰ (sym (trans′ (pR-upS X D L.zero) (cong L.suc (pR-up0 X D)))))
    (cong (λ t → read (Ψ⁰ x t)) (sym (pM-emT X′ C)))
    (succ² (Ψ⁰ x (plugM X′ C G.zero)) (base x))
    where
    trans′ : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
    trans′ refl q = q
```

## 5 语境的良好性与结点

```agda
AllR : CtxR → Set
AllR ε = ⊤
AllR (D ▸ A) = AllR D × (Good A × A L.≅ A)

AllM : CtxM → Set
AllM ε = ⊤
AllM (C ▸ Y) = AllM C × Lgl L1 Y

record OK (X : T₁) (D : CtxR) (X′ : R₁) (C : CtxM) : Set where
  constructor ok
  field
    gX : Good X
    sX : X L.≅ X
    aD : AllR D
    lX : Lgl L1 X′
    aC : AllM C
    pX : L.𝟎 {L.zero} L.≺ flat X

good-plug : ∀ {X} D {Z} → Good X → X L.≅ X → AllR D → Good Z → Z L.≅ Z → Good (plugR X D Z)
good-plug ε gX sX a gZ sZ = Good-add gX sX gZ
good-plug (D ▸ A) gX sX (a , gA , sA) gZ sZ = good-plug D gX sX a (Good-add gA sA gZ) (L.add-≅ sA sZ)

self-plug : ∀ {X} D {Z Z′} → X L.≅ X → AllR D → Z L.≅ Z′ → plugR X D Z L.≅ plugR X D Z′
self-plug ε sX a e = L.add-≅ sX e
self-plug (D ▸ A) sX (a , gA , sA) e = self-plug D sX a (L.add-≅ sA e)

lgl-plug : ∀ {X′} C {Z} → Lgl L1 X′ → AllM C → Lgl L1 Z → Lgl L1 (plugM X′ C Z)
lgl-plug {X′} ε {Z} lX a lZ = plus-lgl L1 X′ Z lX lZ
lgl-plug (C ▸ Y) {Z} lX (a , lY) lZ = lgl-plug C lX a (plus-lgl L1 Y Z lY lZ)

pos-plug : ∀ X D Z → L.𝟎 {L.zero} L.≺ flat X → L.𝟎 {L.zero} L.≺ flat (plugR X D Z)
pos-plug X ε Z h = fl⊑ X (λ q → q) Z h
pos-plug X (D ▸ A) Z h = pos-plug X D (A L.+ Z) h

≅-≡ : ∀ {a b c : T₀} → a ≡ b → b L.≅ c → a L.≅ c
≅-≡ refl e = e

FU : ∀ X D (y : T₀) → flat (plugR X D (L.up L.zero y)) L.≅ (flat (plugR X D L.zero) L.+ y)
FU X D L.zero = ≅-≡ (cong flat (pR-up0 X D)) (L.≅-refl⁰ _)
FU X D (L.suc y) = ≅-≡ (cong flat (pR-upS X D y)) (L.s≅ (FU X D y))
FU X D (L.lim f) = ≅-≡ (cong flat (pR-upL X D f)) (L.l≅ (λ n → FU X D (f n)))
FU X D (L.limᵢ () g)
FU X D (L.up () y)

S : T₁ → CtxR → R₁ → CtxM → Set
S X D X′ C = (∀ x → Two (L.ψ⁰ (plugR X D L.zero)) (read (Ψ⁰ x (plugM X′ C G.zero)))) × OK X D X′ C

xc : Ext zero L1
xc = cmp (vs v0) (inj₁ tt)

module Node (X : T₁) (D : CtxR) (X′ : R₁) (C : CtxM) (s : S X D X′ C) where
  open OK (proj₂ s)
  open Tail X D X′ C (proj₁ s)

  f : T₀ → T₁
  f y = plugR X D (L.up L.zero y)

  gm : Ext zero L1 → R → R
  gm x η = Ψ⁰ x (plugM X′ C (G.em tt η))

  B : T₀
  B = flat (plugR X D L.zero)

  open Chains f (gm xc) renaming (X to Xr)

  lgl : ∀ n → Lgl zero (d n)
  lgl = chain-lgl zero (gm xc) (λ η l → Ψ-lgl zero (vs v0) xc _ (lgl-plug C lX aC l))

  same : ∀ y → f y L.≅ f y
  same y = self-plug D sX aD (L.upˡ (L.upʳ (L.≅-refl⁰ y)))

  fl≅ : ∀ y → L.ψ⁰ (f y) L.≅ L.ψ⁰ (B L.+ y)
  fl≅ y = L.≅-trans (ψ⁰-flat (f y)) (L.ψ⁰-≅ (FU X D y))

  cg : ∀ {y y′} → y ≼ˣ y′ → L.ψ⁰ (f y) ≼ˣ L.ψ⁰ (f y′)
  cg {y} {y′} q = transˣ (≅→≼ˣ (fl≅ y)) (transˣ (ψ⁰ˣ (+ˣ (reflˣ B) (≼-refl B) q)) (≅→≼ˣ (L.≅-sym (fl≅ y′))))

  st : ∀ n → flat (f (Xr n)) L.≺ flat (f (Xr (suc n)))
  st n = L.≺-respˡ (L.≅-sym (FU X D (Xr n))) (L.≺-respʳ (+≺ B lt) (L.≅-sym (FU X D (Xr (suc n)))))
    where
    lt : Xr n L.≺ Xr (suc n)
    lt = L.≺-respʳ (lead (Xr n) (Z1 xc (plugM X′ C (G.em tt (d n))))) (L.≅-sym (read-plus (d n) (gm xc (d n))))

  z0 : L.𝟎 {L.zero} L.≺ flat (f (L.suc L.zero))
  z0 = L.≺-respʳ (L.≺s (pos-plug X D L.zero pX)) (L.≅-sym (FU X D (L.suc L.zero)))

  module N (x : Ext zero L1) = NodeTwo f same (gm x) (gm xc) (λ y → flat (f y))
    (λ n → tail x (d n)) (λ n → tail xc (d n)) cg
    (λ y → ≅→≼ˣ (ψ⁰-flat (f y)) , ≅→≼ˣ (L.≅-sym (ψ⁰-flat (f y))))
    (λ n → HS-flat (good-plug D gX sX aD (gu (good-read (d n) (lgl n))) (L.upˡ (L.upʳ (L.≅-refl⁰ (Xr n)))))
      (same (Xr n)))
    st z0

  node : ∀ x → Two (L.ψ⁰ (plugR X D Ω₁)) (read (Ψ⁰ x (plugM X′ C G.top)))
  node x = Two-sub (cong L.ψ⁰ (sym (pR-node X D (L.up L.zero)))) (cong (λ t → read (Ψ⁰ x t)) (sym (pM-top X′ C)))
    (N.result x (x (inj₁ tt)))
```

## 6 并行

`M a = Ψ₁ a` (第 0 层的树折到目标层 1)；`F₁ (read a)` 是参照的同一件事。后继与 `top` 处两边是 ω 倍：参照从 0 起，主线从 `Y` 起，错开一位；第 k 项由语境逐次加长 (`iterS`) 得到。

```agda
xk : Ext L1 zero
xk r = keep (inj₂ r) refl

M : R → R₁
M a = Ψ L1 v0 xk a

repR : CtxR → T₁ → ℕ → CtxR
repR D A zero = D
repR D A (suc k) = repR D A k ▸ A

repM : CtxM → R₁ → ℕ → CtxM
repM C Y zero = C
repM C Y (suc k) = repM C Y k ▸ Y

trans≡ : ∀ {T : Set} {a b c : T} → a ≡ b → b ≡ c → a ≡ c
trans≡ refl q = q

iter-shift : ∀ {T : Set} (h : T → T) x k → iterᴸ h (h x) k ≡ h (iterᴸ h x k)
iter-shift h x zero = refl
iter-shift h x (suc k) = cong h (iter-shift h x k)

acc-iter : ∀ {T : Set} (h : T → T) x k → acc (λ _ z → h z) x k ≡ iterᴸ h x k
acc-iter h x zero = refl
acc-iter h x (suc k) = cong h (acc-iter h x k)

pR-rep : ∀ X D A k Z → plugR X (repR D A k) Z ≡ plugR X D (iterᴸ (A L.+_) Z k)
pR-rep X D A zero Z = refl
pR-rep X D A (suc k) Z = trans≡ (pR-rep X D A k (A L.+ Z)) (cong (plugR X D) (iter-shift (A L.+_) Z k))

pM-rep : ∀ X C Y k Z → plugM X (repM C Y k) Z ≡ plugM X C (iterᴸ (plus L1 Y) Z k)
pM-rep X C Y zero Z = refl
pM-rep X C Y (suc k) Z = trans≡ (pM-rep X C Y k (plus L1 Y Z)) (cong (plugM X C) (iter-shift (plus L1 Y) Z k))

iterS : ∀ {X X′ A Y} → (∀ {D C} → S X D X′ C → S X (D ▸ A) X′ (C ▸ Y)) →
  ∀ {D C} → S X D X′ C → ∀ k → S X (repR D A k) X′ (repM C Y k)
iterS step s zero = s
iterS step s (suc k) = step (iterS step s k)

sucTwo : ∀ {X D X′ C A Y} → (∀ k → S X (repR D A k) X′ (repM C Y k)) →
  L.HS (flat (plugR X D (L.lim (iterᴸ (A L.+_) L.zero)))) →
  ∀ x → Two (L.ψ⁰ (plugR X D (L.lim (iterᴸ (A L.+_) L.zero)))) (read (Ψ⁰ x (plugM X′ C (succ L1 Y))))
sucTwo {X} {D} {X′} {C} {A} {Y} ss hf x =
  Two-sub (cong L.ψ⁰ (sym (pR-lim X D G))) (cong (λ t → read (Ψ⁰ x t)) (sym (pM-lim X′ C H)))
    (lˣ (λ { zero → ≼lˣ 0 (transˣ mono (proj₁ (two 0))) ; (suc k) → ≼lˣ k (proj₁ (two k)) }) ,
     lˣ (λ k → ≼lˣ (suc k) (proj₂ (two k))))
  where
  G : ℕ → T₁
  G = iterᴸ (A L.+_) L.zero
  H : ℕ → R₁
  H = acc (λ _ z → plus L1 Y z) Y
  two : ∀ k → Two (L.ψ⁰ (plugR X D (G (suc k)))) (read (Ψ⁰ x (plugM X′ C (H k))))
  two k = Two-sub (cong L.ψ⁰ (trans≡ (pR-rep X D A k A) (cong (plugR X D) (iter-shift (A L.+_) L.zero k))))
    (cong (λ t → read (Ψ⁰ x t)) (trans≡ (pM-rep X′ C Y k Y) (cong (plugM X′ C) (sym (acc-iter (plus L1 Y) Y k)))))
    (proj₁ (ss (suc k)) x)
  hs′ : L.HS (L.lim (λ k → flat (plugR X D (G k))))
  hs′ = subst (λ t → L.HS (flat t)) (pR-lim X D G) hf
  mono : L.ψ⁰ (plugR X D (G 0)) ≼ˣ L.ψ⁰ (plugR X D (G 1))
  mono = transˣ (≅→≼ˣ (ψ⁰-flat (plugR X D (G 0))))
    (transˣ (ψ⁰ˣ (⊑→≼ˣ _ (L.hl₂ hs′ 0))) (≅→≼ˣ (L.≅-sym (ψ⁰-flat (plugR X D (G 1))))))

trself : ∀ (y : T₀) → L.tr⁻ L.z≅ y L.≅ L.tr⁻ L.z≅ y
trself y = L.tr⁻-≅ L.z≅ (L.≅-tr⁻ L.z≅ (L.≅-refl⁰ y))

selfF : ∀ (y : T₀) → F₁ y L.≅ F₁ y
selfF y = L.ψ-≅ (L.≅ᴵ-refl _) (trself y)

goodF : ∀ a → Lgl zero a → Good (F₁ (read a))
goodF a l = Good-ψ (Good-tr⁻ L.z≅ (good-read a l)) (trself (read a))

parZ : ∀ {X D X′ C} → S X D X′ C → S X (D ▸ Ω₁) X′ (C ▸ G.top)
parZ {X} {D} {X′} {C} s = Node.node X D X′ C s , ok gX sX (aD , goodF G.zero tt , selfF L.zero) lX (aC , tt) pX
  where open OK (proj₂ s)

par : ∀ {X D X′ C} a → Lgl zero a → S X D X′ C → S X (D ▸ F₁ (read a)) X′ (C ▸ M a)
two : ∀ {X D X′ C} a → Lgl zero a → S X D X′ C →
  ∀ x → Two (L.ψ⁰ (plugR X D (F₁ (read a)))) (read (Ψ⁰ x (plugM X′ C (M a))))

par {X} {D} {X′} {C} a l s = two a l s , ok gX sX (aD , goodF a l , selfF (read a)) lX (aC , Ψ-lgl L1 v0 xk a l) pX
  where open OK (proj₂ s)

two {X} {D} {X′} {C} G.zero l s = Node.node X D X′ C s
two {X} {D} {X′} {C} (G.suc a) l s = sucTwo (iterS (par a l) s)
  (HS-flat (good-plug D gX sX aD (goodF (G.suc a) l) (selfF (read (G.suc a)))) (self-plug D sX aD (selfF (read (G.suc a)))))
  where open OK (proj₂ s)
two {X} {D} {X′} {C} (G.lim f) (st , lf) s x =
  Two-sub (cong L.ψ⁰ (sym (pR-lim X D (λ n → F₁ (read (f n))))))
    (cong (λ t → read (Ψ⁰ x t)) (sym (pM-lim X′ C (λ n → M (f n)))))
    (lˣ (λ n → ≼lˣ n (proj₁ (two (f n) (lf n) s x))) , lˣ (λ n → ≼lˣ n (proj₂ (two (f n) (lf n) s x))))
two (G.lc () g) l s
two (G.em () a) l s
two {X} {D} {X′} {C} G.top l s = sucTwo (iterS parZ s)
  (HS-flat (good-plug D gX sX aD (goodF G.top tt) (selfF (read G.top))) (self-plug D sX aD (selfF (read G.top))))
  where open OK (proj₂ s)
```
