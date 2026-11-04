# 第 0 层是值: 上下文

> 不含记号. 与 [Om1HnCx](Om1HnCx.lagda.md) 同形, 输出从第 $(0,0)$ 层的项换成 `Tm`: 一个待计值的项, 连同世界的证据. `idC` 现在收一切层的项, 因为 `E` 对一切层都有定义, `Hb idC` 是 $\top$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoCumNodeCx where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (module Trich)
open Trich renaming (_<_ to _<ᴺ_) using (zero; suc)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit using (_⊴₀_; Ord₀)
open import OCF.Align.NoCumW
open import OCF.Align.NoCumEq
open import OCF.Align.NoCumLe
open import OCF.Align.NoCumMain using (ψL′; Ωfst)
open import OCF.Align.NoCumForce using (Fp; fq; fs; fl; Fp-mono; ⊴→Fp)
open import OCF.Align.NoCumNodeE
```

## §1 待计值的项

```agda
record Tm : Set where
  constructor tmk
  field
    {tp} : ℕ
    {ta tu} : A
    tx : 𝓞 tp ta tu
    tg : Gw tu
    tv : A
    tgv : Gw tv
    tuv : tu ⊲ tv
    tav : ta ⊲ tv
open Tm public

GT : Tm → Set
GT (tmk x g v gv uv av) = Ev x g v gv uv av

vT : (T : Tm) → GT T → Ord₀
vT (tmk x g v gv uv av) d = val x d

-- 第一位置给值的单调
fT : (T T′ : Tm) → tx T ⊴ tx T′ → (a : GT T) (b : GT T′) → vT T a ⊴₀ vT T′ b
fT (tmk x g v gv uv av) (tmk x′ g′ v′ gv′ uv′ av′) d a b = val⊴ᵉ d a b



```

`Hd`: 往下搬的两种情形: 同层, 或者异层但 $x$ 的层在 $x'$ 的世界之下, 而且上下文收这个高度 (`Hb`).

```agda
data Hd (Hb : ℕ → Set) (p : ℕ) (a : A) : ℕ → A → A → Set where
  hom : ∀ {u′} → Hd Hb p a p a u′
  het : ∀ {p′ a′ u′} → Hb p → a ⊲ u′ → Hd Hb p a p′ a′ u′

record Cx : Set₁ where
  field
    Hb : ℕ → Set
    Rn : ∀ {p a u} → 𝓞 p a u → Tm → Set
    mn : ∀ {p a u p′ a′ u′} {x : 𝓞 p a u} {x′ : 𝓞 p′ a′ u′} {y y′ : Tm} → x ⊴ x′ → Rn x y → Rn x′ y′ → tx y ⊴ tx y′
    dn : ∀ {p a u p′ a′ u′} {x : 𝓞 p a u} {x′ : 𝓞 p′ a′ u′} {y′ : Tm} → Hd Hb p a p′ a′ u′ → Gw u → x ⊴ x′ → u ⊲ u′ → Rn x′ y′ → (d′ : GT y′) →
         Σ Tm λ y → Rn x y × Σ (GT y) λ d → vT y d ⊴₀ vT y′ d′
open Cx public

data IdR : ∀ {p a u} → 𝓞 p a u → Tm → Set where
  idr : ∀ {p a u} {x : 𝓞 p a u} (g : Gw u) v (gv : Gw v) (uv : u ⊲ v) (av : a ⊲ v) → IdR x (tmk x g v gv uv av)

idC : Cx
Hb idC _ = ⊤
Rn idC = IdR
mn idC d (idr g v gv uv av) (idr g′ v′ gv′ uv′ av′) = d
dn idC {x = x} hom gu d uu (idr g v gv uv av) b with E-dn x d gu _ _ _ _ (Mi gu gv (⊲-tr uu uv) av) b (Mi g gv uv av)
... | A₁ , f = tmk x gu v gv (⊲-tr uu uv) av , idr gu v gv (⊲-tr uu uv) av , A₁ , f
dn idC {x = x} (het _ ae) gu d uu (idr g v gv uv av) b with E-dn x d gu _ _ _ _ (Mi gu gv (⊲-tr uu uv) (⊲-tr ae uv)) b (Mi g gv uv av)
... | A₁ , f = tmk x gu v gv (⊲-tr uu uv) (⊲-tr ae uv) , idr gu v gv (⊲-tr uu uv) (⊲-tr ae uv) , A₁ , f

data Rψ (C : Cx) (q : ℕ) (t : A) {p a u} (x : 𝓞 p a u) (y : Tm) : Set where
  rψ : (gx : Gw u) (v : A) (gv : Gw v) (uv : u ⊲ v) (tv : t ⊲ v) (av : a ⊲ v) → Rn C (ψ q t x gx v gv uv tv av) y → Rψ C q t x y

Fψ : Cx → ℕ → A → Cx
Hb (Fψ C q t) _ = ⊤
Rn (Fψ C q t) = Rψ C q t
mn (Fψ C q t) d (rψ gx v gv uv tv av r) (rψ gx′ v′ gv′ uv′ tv′ av′ r′) =
  mn C (ψL′ q t d gx gx′ v gv uv tv av v′ gv′ uv′ tv′ av′) r r′
dn (Fψ C q t) {x = x} hom gu d uu (rψ gx′ v gv uv tv av r) b with
  dn C hom gv (ψL′ q t d gu gx′ v gv (⊲-tr uu uv) tv av v gv uv tv av) C.self r b
... | y , r₀ , d₀ , f = y , rψ gu v gv (⊲-tr uu uv) tv av r₀ , d₀ , f
dn (Fψ C q t) {x = x} (het _ ae) gu d uu (rψ gx′ v gv uv tv av r) b with
  dn C hom gv (ψL′ q t d gu gx′ v gv (⊲-tr uu uv) tv (⊲-tr ae uv) v gv uv tv av) C.self r b
... | y , r₀ , d₀ , f = y , rψ gu v gv (⊲-tr uu uv) tv (⊲-tr ae uv) r₀ , d₀ , f

data Ra (C : Cx) {pw aw u₀} (W : 𝓞 pw aw u₀) (gu₀ : Gw u₀) {p a u} (x : 𝓞 p a u) (y : Tm) : Set where
  ra : (L : Rel p a pw aw) (gx : Gw u) (v : A) (gv : Gw v) (uv : u₀ ⊲ v) (xv : u ⊲ v) (bv : bw L ⊲ v) → Rn C (add W gu₀ L x gx v gv uv xv bv) y → Ra C W gu₀ x y

HbA : ∀ {pw aw u₀} → 𝓞 pw aw u₀ → ℕ → Set
HbA {pw} W p = p <ᴺ pw

Fa : ∀ {pw aw u₀} → Cx → (W : 𝓞 pw aw u₀) (gu₀ : Gw u₀) → W ≈ W → Cx
Hb (Fa C W gu₀ E) = HbA W
Rn (Fa C W gu₀ E) = Ra C W gu₀
mn (Fa C W gu₀ E) d (ra L gx v gv uv xv bv r) (ra L′ gx′ v′ gv′ uv′ xv′ bv′ r′) =
  mn C (AddM.mm2 W gu₀ E d L L′ gx gx′ v gv uv xv bv v′ gv′ uv′ xv′ bv′) r r′
dn (Fa C W gu₀ E) hom gu d uu (ra L gx′ v gv uv xv bv r) b with
  dn C hom gv (AddM.mm2 W gu₀ E d L L gu gx′ v gv uv (⊲-tr uu xv) bv v gv uv xv bv) C.self r b
... | y , r₀ , d₀ , f = y , ra L gu v gv uv (⊲-tr uu xv) bv r₀ , d₀ , f
dn (Fa C W gu₀ E) (het i ae) gu d uu (ra L gx′ v gv uv xv bv r) b with
  dn C hom gv (AddM.mm2 W gu₀ E d (lw i) L gu gx′ v gv uv (⊲-tr uu xv) (⊲-tr ae xv) v gv uv xv bv) C.self r b
... | y , r₀ , d₀ , f = y , ra (lw i) gu v gv uv (⊲-tr uu xv) (⊲-tr ae xv) r₀ , d₀ , f
```

## §3 看见

`Sees C q c`: 输入压过 $\Omega_{q,c}$, 则 $c$ 在输出的第一位置上. 这是 `OCF.Free` 的 `CvP`, 这里加了 $1$. `Seen C c`: 不管输入, $c$ 都在输出的第一位置上.

```agda
Sees : Cx → ℕ → A → Set
Sees C q c = ∀ {p a u} (z : 𝓞 p a u) (gz : Gw u) {y : Tm} → c ⊲ u → Ω̇at q c gz ⊴ z → Rn C z y → (d : GT y) → Fp c (vT y d) × Fp one (vT y d)

Seen : Cx → A → Set
Seen C c = ∀ {p a u} (z : 𝓞 p a u) {y : Tm} → Rn C z y → (d : GT y) → Fp c (vT y d)

Fo : ℕ → Cx → Set
Fo q C = ∀ {p′} → p′ <ᴺ q → Seen C one × Hb C p′

record 𝓥 (q : ℕ) (t : A) (C : Cx) : Set₁ where
  constructor vv
  field
    vfo : Fo q C
    vse : ∀ {c} → c ≪ t → Sees C q c
open 𝓥 public

record 𝓥′ (q : ℕ) (t : A) (C : Cx) : Set₁ where
  constructor vt
  field
    vb : 𝓥 q t C
    vs : Sees C q t
open 𝓥′ public
```

`Over h₀ k C′ D`: $C'$ 的每次运行都是 $D$ 在一个压过 $\Omega_{h_0,k}$ 的 $z$ 上的运行. `q₁`: 输入的高度, 决定要 `Hb` 的范围.

```agda
record Ov (h₀ : ℕ) (k : A) (D : Cx) (y : Tm) : Set where
  constructor ov
  field
    {uz} : A
    z : 𝓞 h₀ k uz
    gz : Gw uz
    kz : k ⊲ uz
    rz : Rn D z y
    ωz : Ω̇at h₀ k gz ⊴ z

record Over (q₁ h₀ : ℕ) (k : A) (C′ D : Cx) : Set where
  constructor over
  field
    ovr : ∀ {p a u} (t : 𝓞 p a u) {y : Tm} → Rn C′ t y → Ov h₀ k D y
    ovb : ∀ {p′} → p′ <ᴺ q₁ → Hb C′ p′
open Over public

record FlOver {p a u} (x : 𝓞 p a u) (O C″ : Cx) : Set where
  constructor flo
  field
    flr : ∀ {p₂ a₂ u₂} (t : 𝓞 p₂ a₂ u₂) {y : Tm} → Rn C″ t y → (d : GT y) → Σ Tm λ y₀ → Rn O x y₀ × Σ (GT y₀) λ d₀ → vT y₀ d₀ ⊴₀ vT y d
    flb : ∀ {p′} → p′ <ᴺ p → Hb C″ p′
open FlOver public

Cl : Set₂
Cl = Cx → Set₁

data Im (F : Cx → Cx) (𝓔 : Cl) (D : Cx) : Set₁ where
  im : (C : Cx) → 𝓔 C → D ≡ F C → Im F 𝓔 D

_∧_ : Cl → Cl → Cl
(𝓖 ∧ 𝓑) C = 𝓖 C × 𝓑 C
```
