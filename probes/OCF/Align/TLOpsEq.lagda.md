# 树的算子语言 (二): 结构等价

> 不含记号. 入口 [TLOps](TLOps.lagda.md). 由 [NoCumEq](NoCumEq.lagda.md) 改写, 高度是 $A$. 高度比较 (`p ≡ p′`) 仍是字面的, 因为高度都是同一棵合法树里的字面子项 (`⊲◁`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLOpsEq where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂; cong)
open import OCF.Free.Level using (_≅_; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Strict; ss; sl; Lg; ⊲-tr; lg⊲; z⊲; ≪∘; ≪S; ≪⊲; S→⊲; Rk; keep; rise; cmpN; cmpF)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit using (_≈ᴬ_; z≈; s≈; l≈; ≈ᴬ-refl; ≈ᴬ-sym; ≈ᴬ-trans)
open import OCF.Align.TLOpsW
```

## §1 下标的结构等价

```agda
infix 4 _⊏_
-- 真的第一位置
data _⊏_ : A → A → Set where
  sf : ∀ {a b} → a ⊲ b → a ⊏ asuc b
  lf : ∀ {a f} n → a ⊲ f n → a ⊏ alim f

⊏→⊲ : ∀ {a b} → a ⊏ b → a ⊲ b
⊏→⊲ (sf p) = C.suc p
⊏→⊲ (lf n p) = C.lim n p

≪→⊏ : ∀ {a b} → a ≪ b → a ⊏ b
≪→⊏ C.zero = sf C.self
≪→⊏ (C.suc r) = sf (⊏→⊲ (≪→⊏ r))
≪→⊏ (C.lim n r) = lf n (⊏→⊲ (≪→⊏ r))

⊏⊲ : ∀ {a b c} → a ⊏ b → b ⊲ c → a ⊏ c
⊏⊲ r C.self = r
⊏⊲ r (C.suc q) = sf (⊏→⊲ (⊏⊲ r q))
⊏⊲ r (C.lim n q) = lf n (⊏→⊲ (⊏⊲ r q))

⊲or : ∀ {a b} → a ⊲ b → (a ≡ b) ⊎ (a ⊏ b)
⊲or C.self = inj₁ refl
⊲or (C.suc p) = inj₂ (sf p)
⊲or (C.lim n p) = inj₂ (lf n p)

⊲-mv : ∀ {a b b′} → a ⊲ b → b ≈ᴬ b′ → Σ A (λ a′ → (a′ ⊲ b′) × (a ≈ᴬ a′))
⊲-mv {b′ = b′} C.self e = b′ , C.self , e
⊲-mv (C.suc p) (s≈ e) with ⊲-mv p e
... | a′ , q , d = a′ , C.suc q , d
⊲-mv (C.lim n p) (l≈ h) with ⊲-mv p (h n)
... | a′ , q , d = a′ , C.lim n q , d

⊏-mv : ∀ {a b b′} → a ⊏ b → b ≈ᴬ b′ → Σ A (λ a′ → (a′ ⊏ b′) × (a ≈ᴬ a′))
⊏-mv (sf p) (s≈ e) with ⊲-mv p e
... | a′ , q , d = a′ , sf q , d
⊏-mv (lf n p) (l≈ h) with ⊲-mv p (h n)
... | a′ , q , d = a′ , lf n q , d

data Acc⊏ (a : A) : Set where
  acc : (∀ {b} → b ⊏ a → Acc⊏ b) → Acc⊏ a

acc⊲ : ∀ a {b} → b ⊲ a → Acc⊏ b
acc⊏ : ∀ a {b} → b ⊏ a → Acc⊏ b
acc⊲ a C.self = acc (acc⊏ a)
acc⊲ (asuc a) (C.suc p) = acc⊲ a p
acc⊲ (alim f) (C.lim n p) = acc⊲ (f n) p
acc⊏ (asuc a) (sf p) = acc⊲ a p
acc⊏ (alim f) (lf n p) = acc⊲ (f n) p

irr′ : ∀ {a b} → Acc⊏ a → b ⊏ a → b ≈ᴬ a → ⊥
irr′ (acc h) r e with ⊏-mv r (≈ᴬ-sym e)
... | b₂ , r₂ , d = irr′ (h r) r₂ (≈ᴬ-sym d)

irr : ∀ {a b} → b ⊏ a → b ≈ᴬ a → ⊥
irr {a} = irr′ (acc (acc⊏ a))

-- k ⊏ t, t ≈ t′, t′ ⊲ k′, k′ ≈ k 相撞
clash⊏ : ∀ {k t k′ t′} → k ⊏ t → t′ ⊲ k′ → k ≈ᴬ k′ → t ≈ᴬ t′ → ⊥
clash⊏ s q ek et with ⊲-mv q (≈ᴬ-sym ek)
... | t″ , q″ , d with ⊏-mv s (≈ᴬ-trans et d)
...   | k₂ , r₂ , d₂ = irr (⊏⊲ r₂ q″) (≈ᴬ-sym d₂)

clash : ∀ {k t k′ t′} → k ≪ t → t′ ⊲ k′ → k ≈ᴬ k′ → t ≈ᴬ t′ → ⊥
clash s = clash⊏ (≪→⊏ s)

-- 反对称, 模 ≈ᴬ
anti : ∀ {a b a′ b′} → a ⊲ b → b′ ⊲ a′ → a ≈ᴬ a′ → b ≈ᴬ b′ → a ≈ᴬ b
anti {a} p q ea eb with ⊲or p
... | inj₁ refl = ≈ᴬ-refl a
... | inj₂ r = ⊥-elim (clash⊏ r q ea eb)

⊲≪ : ∀ {k a b} → k ≪ a → a ⊲ b → k ⊲ b
⊲≪ r q = ⊲-tr (≪⊲ r) q
```

## §2 $\max$ 的值

```agda
data Mis (m u t a : A) : Set where
  iu : m ≡ u → Mis m u t a
  it : m ≡ t → Mis m u t a
  ia : m ≡ a → Mis m u t a

mx-is : ∀ {u t a v} (gu : Gw u) (gv : Gw v) (uv : u ⊲ v) (tv : t ⊲ v) (av : a ⊲ v) → Mis (Mx.m (mx gu gv uv tv av)) u t a
mx-is {u} {t} {a} gu gv uv tv av with cmpF uv tv (lgw gv)
... | inj₁ t⊲u with cmpF uv av (lgw gv)
...   | inj₁ a⊲u = iu refl
...   | inj₂ u⊲a = ia refl
mx-is {u} {t} {a} gu gv uv tv av | inj₂ u⊲t with cmpF tv av (lgw gv)
...   | inj₁ a⊲t = it refl
...   | inj₂ t⊲a = ia refl

-- m 被对面的上界控制
ctrl : ∀ {m u t a m′ u′ t′ a′} → Mis m u t a → u′ ⊲ m′ → t′ ⊲ m′ → a′ ⊲ m′ → u ≈ᴬ u′ → t ≈ᴬ t′ → a ≈ᴬ a′ →
       Σ A (λ x′ → (x′ ⊲ m′) × (m ≈ᴬ x′))
ctrl {u′ = u′} (iu refl) p₁ p₂ p₃ e₁ e₂ e₃ = u′ , p₁ , e₁
ctrl {t′ = t′} (it refl) p₁ p₂ p₃ e₁ e₂ e₃ = t′ , p₂ , e₂
ctrl {a′ = a′} (ia refl) p₁ p₂ p₃ e₁ e₂ e₃ = a′ , p₃ , e₃

m≈ : ∀ {m u t a m′ u′ t′ a′} → Mis m u t a → Mis m′ u′ t′ a′ → u ⊲ m → t ⊲ m → a ⊲ m → u′ ⊲ m′ → t′ ⊲ m′ → a′ ⊲ m′ →
     u ≈ᴬ u′ → t ≈ᴬ t′ → a ≈ᴬ a′ → m ≈ᴬ m′
m≈ is is′ p₁ p₂ p₃ p₁′ p₂′ p₃′ e₁ e₂ e₃ with ctrl is p₁′ p₂′ p₃′ e₁ e₂ e₃ | ctrl is′ p₁ p₂ p₃ (≈ᴬ-sym e₁) (≈ᴬ-sym e₂) (≈ᴬ-sym e₃)
... | x′ , xp , xe | y , yp , ye = ≈ᴬ-sym (≈ᴬ-trans ye (anti yp xp (≈ᴬ-sym ye) xe))
```

## §3 `≈`

```agda
infix 4 _≈_
_≈_ : ∀ {p a u p′ a′ u′} → 𝓞 p a u → 𝓞 p′ a′ u′ → Set
ELl : ∀ {p h k u p′ a′ u′} (j : h ◁ p) → Low p j k u → 𝓞 p′ a′ u′ → Set
ELr : ∀ {p a u p′ h k u′} → 𝓞 p a u → (j : h ◁ p′) → Low p′ j k u′ → Set
EqW : ∀ {p h k u p′ h′ k′ u′} (j : h ◁ p) (j′ : h′ ◁ p′) → Low p j k u → Low p′ j′ k′ u′ → Set
EqV : ∀ {p a b u p′ a′ b′ u′} (R : Strict b a) (R′ : Strict b′ a′) → Vs p a R u → Vs p′ a′ R′ u′ → Set
EVC : ∀ {p a b u p′ a′ b′ u′} (P : b ⊲ a) (R′ : Strict b′ a′) → Vc p a P u → Vs p′ a′ R′ u′ → Set
ELO : ∀ {p b u p′ a′ b′ u′} → 𝓞 p b u → (R′ : Strict b′ a′) → Vs p′ a′ R′ u′ → Set
EOC : ∀ {p b u p′ a′ b′ u′} → 𝓞 p b u → (P : b′ ⊲ a′) → Vc p′ a′ P u′ → Set

oe es x ≈ y = x ≈ y
oe (el n) x ≈ y = x ≈ y
oL j k e x ≈ y = ELl j x y
ow p g x ≈ y = x ≈ y
_≈_ X@o0 (oe es y) = X ≈ y
_≈_ X@o0 (oe (el n) y) = X ≈ y
_≈_ X@o0 (oL j k₂ e y) = ELr X j y
_≈_ X@o0 (ow p g y) = X ≈ y
_≈_ X@(os x) (oe es y) = X ≈ y
_≈_ X@(os x) (oe (el n) y) = X ≈ y
_≈_ X@(os x) (oL j k₂ e y) = ELr X j y
_≈_ X@(os x) (ow p g y) = X ≈ y
_≈_ X@(ol F) (oe es y) = X ≈ y
_≈_ X@(ol F) (oe (el n) y) = X ≈ y
_≈_ X@(ol F) (oL j k₂ e y) = ELr X j y
_≈_ X@(ol F) (ow p g y) = X ≈ y
_≈_ X@(oi r h) (oe es y) = X ≈ y
_≈_ X@(oi r h) (oe (el n) y) = X ≈ y
_≈_ X@(oi r h) (oL j k₂ e y) = ELr X j y
_≈_ X@(oi r h) (ow p g y) = X ≈ y
_≈_ X@(od i k r h) (oe es y) = X ≈ y
_≈_ X@(od i k r h) (oe (el n) y) = X ≈ y
_≈_ X@(od i k r h) (oL j k₂ e y) = ELr X j y
_≈_ X@(od i k r h) (ow p g y) = X ≈ y
_≈_ X@(oc x h) (oe es y) = X ≈ y
_≈_ X@(oc x h) (oe (el n) y) = X ≈ y
_≈_ X@(oc x h) (oL j k₂ e y) = ELr X j y
_≈_ X@(oc x h) (ow p g y) = X ≈ y
o0 ≈ o0 = ⊤
_≈_ {p} {a} {u} {p′} {a′} {u′} (os x) (os y) = (p ≡ p′) × (a ≈ᴬ a′) × (u ≈ᴬ u′) × (x ≈ y)
ol F ≈ ol G = ∀ n → F n ≈ G n
_≈_ {p} {a} {u} {p′} {a′} {u′} (oi {k = k} r h) (oi {k = k′} r′ h′) =
  (p ≡ p′) × (a ≈ᴬ a′) × (u ≈ᴬ u′) × (k ≈ᴬ k′) ×
  (∀ {v v′} (q : u ⊲ v) (q′ : u′ ⊲ v′) (g : Gw v) (g′ : Gw v′) → v ≈ᴬ v′ → ∀ y y′ → EqV (≪S r) (≪S r′) y y′ → h q g y ≈ h′ q′ g′ y′)
_≈_ {p} {a} {u} {p′} {a′} {u′} (od {h = h₀} j k r h) (od {h = h₁} j′ k′ r′ h′) =
  (p ≡ p′) × (h₀ ≡ h₁) × (a ≈ᴬ a′) × (u ≈ᴬ u′) × (k ≈ᴬ k′) ×
  (∀ {v v′} (q : u ⊲ v) (q′ : u′ ⊲ v′) (g : Gw v) (g′ : Gw v′) → v ≈ᴬ v′ → ∀ y y′ → EqW j j′ y y′ → h q g y ≈ h′ q′ g′ y′)
_≈_ {p} {a} {u} {p′} {a′} {u′} (oc x h) (oc x′ h′) =
  (p ≡ p′) × (a ≈ᴬ a′) × (u ≈ᴬ u′) × (x ≈ x′) ×
  (∀ {v v′} (q : u ⊲ v) (q′ : u′ ⊲ v′) (g : Gw v) (g′ : Gw v′) → v ≈ᴬ v′ → h q g ≈ h′ q′ g′)
_ ≈ _ = ⊥

ELl zero x y = x ≈ y
ELl (self n₉) x y = x ≈ y
ELl (suc j) x y = ELl j x y
ELl (lim n₉ j) x y = ELl j x y
ELr X zero y = X ≈ y
ELr X (self n₉) y = X ≈ y
ELr X (suc j) y = ELr X j y
ELr X (lim n₉ j) y = ELr X j y
EqW zero j′ x y = ELr x j′ y
EqW (self n₉) j′ x y = ELr x j′ y
EqW (suc j) j′ x y = EqW j j′ x y
EqW (lim n₉ j) j′ x y = EqW j j′ x y
EqV (ss P) R′ y y′ = EVC P R′ y y′
EqV (sl n P) R′ y y′ = EVC P R′ y y′
EVC C.self R′ y y′ = ELO y R′ y′
EVC (C.suc P) R′ y y′ = EVC P R′ y y′
EVC (C.lim n P) R′ y y′ = EVC P R′ y y′
ELO x (ss P) y′ = EOC x P y′
ELO x (sl n P) y′ = EOC x P y′
EOC x C.self y′ = x ≈ y′
EOC x (C.suc P) y′ = EOC x P y′
EOC x (C.lim n P) y′ = EOC x P y′
```

## §4 换视角

```agda
Ll→ : ∀ {p h k u p′ a′ u′} (j : h ◁ p) (x : Low p j k u) {y : 𝓞 p′ a′ u′} → ELl j x y → outL j x ≈ y
Ll→ zero x e = e
Ll→ (self n₉) x e = e
Ll→ (suc j) x e = Ll→ j x e
Ll→ (lim n₉ j) x e = Ll→ j x e

→Ll : ∀ {p h k u p′ a′ u′} (j : h ◁ p) (x : Low p j k u) {y : 𝓞 p′ a′ u′} → outL j x ≈ y → ELl j x y
→Ll zero x e = e
→Ll (self n₉) x e = e
→Ll (suc j) x e = →Ll j x e
→Ll (lim n₉ j) x e = →Ll j x e

Lr→ : ∀ {p a u p′ h k u′} (X : 𝓞 p a u) (j : h ◁ p′) (y : Low p′ j k u′) → ELr X j y → X ≈ outL j y
Lr→ X zero y e = e
Lr→ X (self n₉) y e = e
Lr→ X (suc j) y e = Lr→ X j y e
Lr→ X (lim n₉ j) y e = Lr→ X j y e

→Lr : ∀ {p a u p′ h k u′} (X : 𝓞 p a u) (j : h ◁ p′) (y : Low p′ j k u′) → X ≈ outL j y → ELr X j y
→Lr X zero y e = e
→Lr X (self n₉) y e = e
→Lr X (suc j) y e = →Lr X j y e
→Lr X (lim n₉ j) y e = →Lr X j y e

W→ : ∀ {p h k u p′ h′ k′ u′} (j : h ◁ p) (j′ : h′ ◁ p′) (x : Low p j k u) (y : Low p′ j′ k′ u′) → EqW j j′ x y → outL j x ≈ outL j′ y
W→ zero j′ x y e = Lr→ x j′ y e
W→ (self n₉) j′ x y e = Lr→ x j′ y e
W→ (suc j) j′ x y e = W→ j j′ x y e
W→ (lim n₉ j) j′ x y e = W→ j j′ x y e

→W : ∀ {p h k u p′ h′ k′ u′} (j : h ◁ p) (j′ : h′ ◁ p′) (x : Low p j k u) (y : Low p′ j′ k′ u′) → outL j x ≈ outL j′ y → EqW j j′ x y
→W zero j′ x y e = →Lr x j′ y e
→W (self n₉) j′ x y e = →Lr x j′ y e
→W (suc j) j′ x y e = →W j j′ x y e
→W (lim n₉ j) j′ x y e = →W j j′ x y e

V→ : ∀ {p a b u p′ a′ b′ u′} (R : Strict b a) (R′ : Strict b′ a′) (y : Vs p a R u) (y′ : Vs p′ a′ R′ u′) → EqV R R′ y y′ → outS R y ≈ outS R′ y′
VC→ : ∀ {p a b u p′ a′ b′ u′} (P : b ⊲ a) (R′ : Strict b′ a′) (y : Vc p a P u) (y′ : Vs p′ a′ R′ u′) → EVC P R′ y y′ → outC P y ≈ outS R′ y′
LO→ : ∀ {p b u p′ a′ b′ u′} (x : 𝓞 p b u) (R′ : Strict b′ a′) (y′ : Vs p′ a′ R′ u′) → ELO x R′ y′ → x ≈ outS R′ y′
OC→ : ∀ {p b u p′ a′ b′ u′} (x : 𝓞 p b u) (P : b′ ⊲ a′) (y′ : Vc p′ a′ P u′) → EOC x P y′ → x ≈ outC P y′
V→ (ss P) R′ y y′ e = VC→ P R′ y y′ e
V→ (sl n P) R′ y y′ e = VC→ P R′ y y′ e
VC→ C.self R′ y y′ e = LO→ y R′ y′ e
VC→ (C.suc P) R′ y y′ e = VC→ P R′ y y′ e
VC→ (C.lim n P) R′ y y′ e = VC→ P R′ y y′ e
LO→ x (ss P) y′ e = OC→ x P y′ e
LO→ x (sl n P) y′ e = OC→ x P y′ e
OC→ x C.self y′ e = e
OC→ x (C.suc P) y′ e = OC→ x P y′ e
OC→ x (C.lim n P) y′ e = OC→ x P y′ e

→V : ∀ {p a b u p′ a′ b′ u′} (R : Strict b a) (R′ : Strict b′ a′) (y : Vs p a R u) (y′ : Vs p′ a′ R′ u′) → outS R y ≈ outS R′ y′ → EqV R R′ y y′
→VC : ∀ {p a b u p′ a′ b′ u′} (P : b ⊲ a) (R′ : Strict b′ a′) (y : Vc p a P u) (y′ : Vs p′ a′ R′ u′) → outC P y ≈ outS R′ y′ → EVC P R′ y y′
→LO : ∀ {p b u p′ a′ b′ u′} (x : 𝓞 p b u) (R′ : Strict b′ a′) (y′ : Vs p′ a′ R′ u′) → x ≈ outS R′ y′ → ELO x R′ y′
→OC : ∀ {p b u p′ a′ b′ u′} (x : 𝓞 p b u) (P : b′ ⊲ a′) (y′ : Vc p′ a′ P u′) → x ≈ outC P y′ → EOC x P y′
→V (ss P) R′ y y′ e = →VC P R′ y y′ e
→V (sl n P) R′ y y′ e = →VC P R′ y y′ e
→VC C.self R′ y y′ e = →LO y R′ y′ e
→VC (C.suc P) R′ y y′ e = →VC P R′ y y′ e
→VC (C.lim n P) R′ y y′ e = →VC P R′ y y′ e
→LO x (ss P) y′ e = →OC x P y′ e
→LO x (sl n P) y′ e = →OC x P y′ e
→OC x C.self y′ e = e
→OC x (C.suc P) y′ e = →OC x P y′ e
→OC x (C.lim n P) y′ e = →OC x P y′ e
```

## §5 右边的包装透明

```agda
≈ow : ∀ {p a u p′} (x : 𝓞 p a u) {a′ u₀ v₀} (p₀ : u₀ ⊲ v₀) (g₀′ : Gw u₀) (y : 𝓞 p′ a′ u₀) → x ≈ y → x ≈ (ow p₀ g₀′ y)
≈owS : ∀ {p h k u p′} (j : h ◁ p) (x : Low p j k u) {a′ u₀ v₀} (p₀ : u₀ ⊲ v₀) (g₀′ : Gw u₀) (y : 𝓞 p′ a′ u₀) → ELl j x y → ELl j x (ow p₀ g₀′ y)
≈ow o0 p₀ g₀′ y d = d
≈ow (os x₁) p₀ g₀′ y d = d
≈ow (ol F) p₀ g₀′ y d = d
≈ow (oi r h) p₀ g₀′ y d = d
≈ow (od i k r h) p₀ g₀′ y d = d
≈ow (oc x₁ h) p₀ g₀′ y d = d
≈ow (oe es x) p₀ g₀′ y d = ≈ow x p₀ g₀′ y d
≈ow (oe (el m) x) p₀ g₀′ y d = ≈ow x p₀ g₀′ y d
≈ow (oL j₁ k₁ e₁ x) p₀ g₀′ y d = ≈owS j₁ x p₀ g₀′ y d
≈ow (ow q₁ g₁ x) p₀ g₀′ y d = ≈ow x p₀ g₀′ y d
≈owS zero x p₀ g₀′ y d = ≈ow x p₀ g₀′ y d
≈owS (self n₉) x p₀ g₀′ y d = ≈ow x p₀ g₀′ y d
≈owS (suc j) x p₀ g₀′ y d = ≈owS j x p₀ g₀′ y d
≈owS (lim n₉ j) x p₀ g₀′ y d = ≈owS j x p₀ g₀′ y d

≈ow⁻ : ∀ {p a u p′} (x : 𝓞 p a u) {a′ u₀ v₀} (p₀ : u₀ ⊲ v₀) (g₀′ : Gw u₀) (y : 𝓞 p′ a′ u₀) → x ≈ (ow p₀ g₀′ y) → x ≈ y
≈ow⁻S : ∀ {p h k u p′} (j : h ◁ p) (x : Low p j k u) {a′ u₀ v₀} (p₀ : u₀ ⊲ v₀) (g₀′ : Gw u₀) (y : 𝓞 p′ a′ u₀) → ELl j x (ow p₀ g₀′ y) → ELl j x y
≈ow⁻ o0 p₀ g₀′ y d = d
≈ow⁻ (os x₁) p₀ g₀′ y d = d
≈ow⁻ (ol F) p₀ g₀′ y d = d
≈ow⁻ (oi r h) p₀ g₀′ y d = d
≈ow⁻ (od i k r h) p₀ g₀′ y d = d
≈ow⁻ (oc x₁ h) p₀ g₀′ y d = d
≈ow⁻ (oe es x) p₀ g₀′ y d = ≈ow⁻ x p₀ g₀′ y d
≈ow⁻ (oe (el m) x) p₀ g₀′ y d = ≈ow⁻ x p₀ g₀′ y d
≈ow⁻ (oL j₁ k₁ e₁ x) p₀ g₀′ y d = ≈ow⁻S j₁ x p₀ g₀′ y d
≈ow⁻ (ow q₁ g₁ x) p₀ g₀′ y d = ≈ow⁻ x p₀ g₀′ y d
≈ow⁻S zero x p₀ g₀′ y d = ≈ow⁻ x p₀ g₀′ y d
≈ow⁻S (self n₉) x p₀ g₀′ y d = ≈ow⁻ x p₀ g₀′ y d
≈ow⁻S (suc j) x p₀ g₀′ y d = ≈ow⁻S j x p₀ g₀′ y d
≈ow⁻S (lim n₉ j) x p₀ g₀′ y d = ≈ow⁻S j x p₀ g₀′ y d


≈oe : ∀ {p a u p′ c b u₀} {R : Strict b c} (x : 𝓞 p a u) (stp : Stp R) (y : Vs p′ c R u₀) → x ≈ outS R y → x ≈ oe stp y
≈oeS : ∀ {p h k u p′ c b u₀} {R : Strict b c} (j : h ◁ p) (x : Low p j k u) (stp : Stp R) (y : Vs p′ c R u₀) → ELl j x (outS R y) → ELl j x (oe stp y)
≈oe⁻ : ∀ {p a u p′ c b u₀} {R : Strict b c} (x : 𝓞 p a u) (stp : Stp R) (y : Vs p′ c R u₀) → x ≈ oe stp y → x ≈ outS R y
≈oe⁻S : ∀ {p h k u p′ c b u₀} {R : Strict b c} (j : h ◁ p) (x : Low p j k u) (stp : Stp R) (y : Vs p′ c R u₀) → ELl j x (oe stp y) → ELl j x (outS R y)
≈oe o0 es y d = d
≈oe (os x) es y d = d
≈oe (ol F) es y d = d
≈oe (oi r h) es y d = d
≈oe (od i k r h) es y d = d
≈oe (oc x h) es y d = d
≈oe o0 (el n) y d = d
≈oe (os x) (el n) y d = d
≈oe (ol F) (el n) y d = d
≈oe (oi r h) (el n) y d = d
≈oe (od i k r h) (el n) y d = d
≈oe (oc x h) (el n) y d = d
≈oe (oe es x) stp y d = ≈oe x stp y d
≈oe (oe (el m) x) stp y d = ≈oe x stp y d
≈oe (oL j₁ k₁ e₁ x) stp y d = ≈oeS j₁ x stp y d
≈oe (ow q₁ g₁ x) stp y d = ≈oe x stp y d
≈oeS zero x stp y d = ≈oe x stp y d
≈oeS (self n₉) x stp y d = ≈oe x stp y d
≈oeS (suc j) x stp y d = ≈oeS j x stp y d
≈oeS (lim n₉ j) x stp y d = ≈oeS j x stp y d
≈oe⁻ o0 es y d = d
≈oe⁻ (os x) es y d = d
≈oe⁻ (ol F) es y d = d
≈oe⁻ (oi r h) es y d = d
≈oe⁻ (od i k r h) es y d = d
≈oe⁻ (oc x h) es y d = d
≈oe⁻ o0 (el n) y d = d
≈oe⁻ (os x) (el n) y d = d
≈oe⁻ (ol F) (el n) y d = d
≈oe⁻ (oi r h) (el n) y d = d
≈oe⁻ (od i k r h) (el n) y d = d
≈oe⁻ (oc x h) (el n) y d = d
≈oe⁻ (oe es x) stp y d = ≈oe⁻ x stp y d
≈oe⁻ (oe (el m) x) stp y d = ≈oe⁻ x stp y d
≈oe⁻ (oL j₁ k₁ e₁ x) stp y d = ≈oe⁻S j₁ x stp y d
≈oe⁻ (ow q₁ g₁ x) stp y d = ≈oe⁻ x stp y d
≈oe⁻S zero x stp y d = ≈oe⁻ x stp y d
≈oe⁻S (self n₉) x stp y d = ≈oe⁻ x stp y d
≈oe⁻S (suc j) x stp y d = ≈oe⁻S j x stp y d
≈oe⁻S (lim n₉ j) x stp y d = ≈oe⁻S j x stp y d

≈oL : ∀ {p a u p′ a′ h k u₀} (x : 𝓞 p a u) (j : h ◁ p′) (e : k ⊲ u₀) (y : Low p′ j k u₀) → x ≈ outL j y → _≈_ {a′ = a′} x (oL j k e y)
≈oLS : ∀ {p h₁ k₁ u p′ a′ h k u₀} (j₁ : h₁ ◁ p) (x : Low p j₁ k₁ u) (j : h ◁ p′) (e : k ⊲ u₀) (y : Low p′ j k u₀) → ELl j₁ x (outL j y) → ELl {a′ = a′} j₁ x (oL j k e y)
≈oL o0 j e y d = →Lr o0 j y d
≈oL X@(os x) j e y d = →Lr X j y d
≈oL X@(ol F) j e y d = →Lr X j y d
≈oL X@(oi r h) j e y d = →Lr X j y d
≈oL X@(od i k r h) j e y d = →Lr X j y d
≈oL X@(oc x h) j e y d = →Lr X j y d
≈oL (oe es x) j e y d = ≈oL x j e y d
≈oL (oe (el m) x) j e y d = ≈oL x j e y d
≈oL (oL j₁ k₁ e₁ x) j e y d = ≈oLS j₁ x j e y d
≈oL (ow q₁ g₁ x) j e y d = ≈oL x j e y d
≈oLS zero x j e y d = ≈oL x j e y d
≈oLS (self n₉) x j e y d = ≈oL x j e y d
≈oLS (suc j₁) x j e y d = ≈oLS j₁ x j e y d
≈oLS (lim n₉ j₁) x j e y d = ≈oLS j₁ x j e y d

≈oL⁻ : ∀ {p a u p′ a′ h k u₀} (x : 𝓞 p a u) (j : h ◁ p′) (e : k ⊲ u₀) (y : Low p′ j k u₀) → _≈_ {a′ = a′} x (oL j k e y) → x ≈ outL j y
≈oL⁻S : ∀ {p h₁ k₁ u p′ a′ h k u₀} (j₁ : h₁ ◁ p) (x : Low p j₁ k₁ u) (j : h ◁ p′) (e : k ⊲ u₀) (y : Low p′ j k u₀) → ELl {a′ = a′} j₁ x (oL j k e y) → ELl j₁ x (outL j y)
≈oL⁻ o0 j e y d = Lr→ o0 j y d
≈oL⁻ X@(os x) j e y d = Lr→ X j y d
≈oL⁻ X@(ol F) j e y d = Lr→ X j y d
≈oL⁻ X@(oi r h) j e y d = Lr→ X j y d
≈oL⁻ X@(od i k r h) j e y d = Lr→ X j y d
≈oL⁻ X@(oc x h) j e y d = Lr→ X j y d
≈oL⁻ (oe es x) j e y d = ≈oL⁻ x j e y d
≈oL⁻ (oe (el m) x) j e y d = ≈oL⁻ x j e y d
≈oL⁻ (oL j₁ k₁ e₁ x) j e y d = ≈oL⁻S j₁ x j e y d
≈oL⁻ (ow q₁ g₁ x) j e y d = ≈oL⁻ x j e y d
≈oL⁻S zero x j e y d = ≈oL⁻ x j e y d
≈oL⁻S (self n₉) x j e y d = ≈oL⁻ x j e y d
≈oL⁻S (suc j₁) x j e y d = ≈oL⁻S j₁ x j e y d
≈oL⁻S (lim n₉ j₁) x j e y d = ≈oL⁻S j₁ x j e y d

-- 用 O k 的值陈述分支
nI : ∀ {p a u p′ a′ u′ k k′} {r : k ≪ a} {r′ : k′ ≪ a′} {f : ∀ {v} → u ⊲ v → Gw v → Vs p a (≪S r) v → 𝓞 p a v} {f′ : ∀ {v} → u′ ⊲ v → Gw v → Vs p′ a′ (≪S r′) v → 𝓞 p′ a′ v} →
     (∀ {v v′} (q : u ⊲ v) (q′ : u′ ⊲ v′) (g : Gw v) (g′ : Gw v′) → v ≈ᴬ v′ → ∀ y y′ → EqV (≪S r) (≪S r′) y y′ → f q g y ≈ f′ q′ g′ y′) →
     ∀ {v v′} (q : u ⊲ v) (q′ : u′ ⊲ v′) (g : Gw v) (g′ : Gw v′) → v ≈ᴬ v′ → (z : 𝓞 p k v) (z′ : 𝓞 p′ k′ v′) → z ≈ z′ → f q g (inS (≪S r) z) ≈ f′ q′ g′ (inS (≪S r′) z′)
nI {r = r} {r′} N q q′ g g′ vv z z′ d = N q q′ g g′ vv _ _ (→V (≪S r) (≪S r′) _ _ (subst₂ _≈_ (sym (out-inS (≪S r) z)) (sym (out-inS (≪S r′) z′)) d))

nD : ∀ {p a u p′ a′ u′ h₀ h₁ k k′} {j : h₀ ◁ p} {j′ : h₁ ◁ p′} {f : ∀ {v} → u ⊲ v → Gw v → Low p j k v → 𝓞 p a v} {f′ : ∀ {v} → u′ ⊲ v → Gw v → Low p′ j′ k′ v → 𝓞 p′ a′ v} →
     (∀ {v v′} (q : u ⊲ v) (q′ : u′ ⊲ v′) (g : Gw v) (g′ : Gw v′) → v ≈ᴬ v′ → ∀ y y′ → EqW j j′ y y′ → f q g y ≈ f′ q′ g′ y′) →
     ∀ {v v′} (q : u ⊲ v) (q′ : u′ ⊲ v′) (g : Gw v) (g′ : Gw v′) → v ≈ᴬ v′ → (z : 𝓞 h₀ k v) (z′ : 𝓞 h₁ k′ v′) → z ≈ z′ → f q g (inL j z) ≈ f′ q′ g′ (inL j′ z′)
nD {j = j} {j′} N q q′ g g′ vv z z′ d = N q q′ g g′ vv _ _ (→W j j′ _ _ (subst₂ _≈_ (sym (out-inL j z)) (sym (out-inL j′ z′)) d))
```

## §6 $\Omega$, 加法, $y\cdot n$

```agda
Ω≈ : ∀ p {a b} → a ≈ᴬ b → Ω̇ p a ≈ Ω̇ p b
Ω≈ azero z≈ = refl , z≈ , s≈ z≈ , tt
Ω≈ (alim f) z≈ = λ n → ≈oL {a′ = azero} {k = azero} {u₀ = one} (Ω̇ (f n) azero) (self n) (z⊲ one) (Ω̇ (f n) azero) (Ω≈ (f n) z≈)
Ω≈ (asuc p) z≈ = refl , z≈ , (s≈ z≈) , (≈oL {a′ = azero} {k = one} {u₀ = one} (Ω̇ p one) zero C.self (Ω̇ p one) (Ω≈ p (≈ᴬ-refl one))) ,
  (λ {v} {v′} q q′ g g′ vv → ≈oL {a′ = azero} {k = v′} {u₀ = v′} (ow (pos g) g₀ (Ω̇ p v)) zero C.self (ow (pos g′) g₀ (Ω̇ p v′))
     (≈ow (Ω̇ p v) (pos g′) g₀ (Ω̇ p v′) (Ω≈ p vv)))
Ω≈ p (s≈ {a} {b} e) = refl , s≈ e , s≈ z≈ , e , (λ q q′ g g′ vv y y′ d → ≈oe {R = ss C.self} y es y′ (V→ (ss C.self) (ss C.self) y y′ d))
Ω≈ p (l≈ {f} {g} h) = λ n → ≈oe {p} {f n} {one} {p} {alim g} {g n} {one} {sl n C.self} (Ω̇ p (f n)) (el n) (Ω̇ p (g n)) (Ω≈ p (h n))

◁→⊏ : ∀ {a b} → a ◁ b → a ⊏ b
◁→⊏ zero = sf C.self
◁→⊏ (suc i) = sf (◁⊲ i)
◁→⊏ (self n) = lf n C.self
◁→⊏ (lim n i) = lf n (◁⊲ i)

<irr : ∀ {n} → n ◁ n → ⊥
<irr {n} i = irr (◁→⊏ i) (≈ᴬ-refl n)

no◁◁ : ∀ {a b} → a ◁ b → b ◁ a → ⊥
no◁◁ i j = <irr (◁-tr i j)

≈-Ωat : ∀ p {a b v v′} (g : Gw v) (g′ : Gw v′) → a ≈ᴬ b → Ω̇at p a g ≈ Ω̇at p b g′
≈-Ωat p {a} {b} g g′ e = ≈ow (Ω̇ p a) (pos g′) g₀ (Ω̇ p b) (Ω≈ p e)

bw≈ : ∀ {p p₁ b a p₂ b′ a′} (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p a′) → p₁ ≡ p₂ → b ≈ᴬ b′ → bw R ≈ᴬ bw R′
bw≈ (sa P) (sa P′) eh e = z≈
bw≈ (lw i) (lw i′) eh e = e
bw≈ (sa P) (lw i′) refl e = ⊥-elim (<irr i′)
bw≈ (lw i) (sa P′) refl e = ⊥-elim (<irr i)

-- 左边 W 对齐, 输出世界规范
module AddE {p a a′ u₀ u₀′} {W : 𝓞 p a u₀} {W′ : 𝓞 p a′ u₀′} (ea : a ≈ᴬ a′) (eu : u₀ ≈ᴬ u₀′) (E : W ≈ W′) (gu : Gw u₀) (gu′ : Gw u₀′) where
  add⁰≈ : ∀ {p₁ b w p₂ b′ w′} (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p a′) (x : 𝓞 p₁ b w) (y : 𝓞 p₂ b′ w′) (gx : Gw w) (gy : Gw w′)
          m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : bw R ⊲ m) → Mis m u₀ w (bw R) →
          ∀ m′ (gm′ : Gw m′) (um′ : u₀′ ⊲ m′) (tm′ : w′ ⊲ m′) (am′ : bw R′ ⊲ m′) → Mis m′ u₀′ w′ (bw R′) →
          x ≈ y → add⁰ W gu R x gx m gm um tm am ≈ add⁰ W′ gu′ R′ y gy m′ gm′ um′ tm′ am′

  add≈ : ∀ {p₁ b w p₂ b′ w′} (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p a′) (x : 𝓞 p₁ b w) (y : 𝓞 p₂ b′ w′) (gx : Gw w) (gy : Gw w′)
         v (gv : Gw v) (uv : u₀ ⊲ v) (xv : w ⊲ v) (bv : bw R ⊲ v)
         v′ (gv′ : Gw v′) (uv′ : u₀′ ⊲ v′) (xv′ : w′ ⊲ v′) (bv′ : bw R′ ⊲ v′) →
         x ≈ y → add W gu R x gx v gv uv xv bv ≈ add W′ gu′ R′ y gy v′ gv′ uv′ xv′ bv′
  add≈ R R′ x y gx gy v gv uv xv bv v′ gv′ uv′ xv′ bv′ d
    with mx gu gv uv xv bv | mx-is gu gv uv xv bv | mx gu′ gv′ uv′ xv′ bv′ | mx-is gu′ gv′ uv′ xv′ bv′
  ... | mx′ m gm um tm am mv | is | mx′ m′ gm′ um′ tm′ am′ mv′ | is′ =
    ≈ow (add⁰ W gu R x gx m gm um tm am) mv′ gm′ (add⁰ W′ gu′ R′ y gy m′ gm′ um′ tm′ am′) (add⁰≈ R R′ x y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d)

  addl : ∀ {p₁ b w p₂ b′ w′} (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p a′) (x : 𝓞 p₁ b w) (y : 𝓞 p₂ b′ w′) (gx : Gw w) (gy : Gw w′)
         m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : bw R ⊲ m)
         m′ (gm′ : Gw m′) (um′ : u₀′ ⊲ m′) (tm′ : w′ ⊲ m′) (am′ : bw R′ ⊲ m′) → Mis m′ u₀′ w′ (bw R′) →
         x ≈ y → add W gu R x gx m gm um tm am ≈ add⁰ W′ gu′ R′ y gy m′ gm′ um′ tm′ am′
  addl R R′ x y gx gy m gm um tm am m′ gm′ um′ tm′ am′ is′ d with mx gu gm um tm am | mx-is gu gm um tm am
  ... | mx′ m₁ g₁ u₁ t₁ a₁ _ | is₁ = add⁰≈ R R′ x y gx gy m₁ g₁ u₁ t₁ a₁ is₁ m′ gm′ um′ tm′ am′ is′ d

  addr : ∀ {p₁ b w p₂ b′ w′} (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p a′) (x : 𝓞 p₁ b w) (y : 𝓞 p₂ b′ w′) (gx : Gw w) (gy : Gw w′)
         m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : bw R ⊲ m) → Mis m u₀ w (bw R) →
         ∀ m′ (gm′ : Gw m′) (um′ : u₀′ ⊲ m′) (tm′ : w′ ⊲ m′) (am′ : bw R′ ⊲ m′) →
         x ≈ y → add⁰ W gu R x gx m gm um tm am ≈ add W′ gu′ R′ y gy m′ gm′ um′ tm′ am′
  addr R R′ x y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d with mx gu′ gm′ um′ tm′ am′ | mx-is gu′ gm′ um′ tm′ am′
  ... | mx′ m₁ g₁ u₁ t₁ a₁ mv | is₁ = ≈ow (add⁰ W gu R x gx m gm um tm am) mv g₁ (add⁰ W′ gu′ R′ y gy m₁ g₁ u₁ t₁ a₁) (add⁰≈ R R′ x y gx gy m gm um tm am is m₁ g₁ u₁ t₁ a₁ is₁ d)

  addLl : ∀ {p₁ h k w p₂ b′ w′} (t : h ◁ p) (j : h ◁ p₁) (x : Low p₁ j k w) (R′ : Rel p₂ b′ p a′) (y : 𝓞 p₂ b′ w′) (gx : Gw w) (gy : Gw w′)
          m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (km : k ⊲ m)
          m′ (gm′ : Gw m′) (um′ : u₀′ ⊲ m′) (tm′ : w′ ⊲ m′) (am′ : bw R′ ⊲ m′) → Mis m′ u₀′ w′ (bw R′) →
          ELl j x y → addL W gu t j x gx m gm um tm km ≈ add⁰ W′ gu′ R′ y gy m′ gm′ um′ tm′ am′
  addLl t zero x R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d = addl (lw t) R′ x y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d
  addLl t (self n₉) x R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d = addl (lw t) R′ x y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d
  addLl t (suc j) x R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d = addLl t j x R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d
  addLl t (lim n₉ j) x R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d = addLl t j x R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d

  addLr : ∀ {p₁ b w p₂ h k w′} (R : Rel p₁ b p a) (x : 𝓞 p₁ b w) (t : h ◁ p) (j : h ◁ p₂) (y : Low p₂ j k w′) (gx : Gw w) (gy : Gw w′)
          m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : bw R ⊲ m) → Mis m u₀ w (bw R) →
          ∀ m′ (gm′ : Gw m′) (um′ : u₀′ ⊲ m′) (tm′ : w′ ⊲ m′) (km′ : k ⊲ m′) →
          ELr x j y → add⁰ W gu R x gx m gm um tm am ≈ addL W′ gu′ t j y gy m′ gm′ um′ tm′ km′
  addLr R x t zero y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d = addr R (lw t) x y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d
  addLr R x t (self n₉) y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d = addr R (lw t) x y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d
  addLr R x t (suc j) y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d = addLr R x t j y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d
  addLr R x t (lim n₉ j) y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d = addLr R x t j y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d

  add⁰≈ (sa P) R′ (oe es x) y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addl (sa (⊲-tr (C.suc C.self) P)) R′ x y gx gy m gm um tm am m′ gm′ um′ tm′ am′ is′ d
  add⁰≈ (lw i) R′ (oe es x) y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addl (lw i) R′ x y gx gy m gm um tm (⊲-tr (C.suc C.self) am) m′ gm′ um′ tm′ am′ is′ d
  add⁰≈ (sa P) R′ (oe (el n) x) y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addl (sa (⊲-tr (C.lim n C.self) P)) R′ x y gx gy m gm um tm am m′ gm′ um′ tm′ am′ is′ d
  add⁰≈ (lw i) R′ (oe (el n) x) y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addl (lw i) R′ x y gx gy m gm um tm (⊲-tr (C.lim n C.self) am) m′ gm′ um′ tm′ am′ is′ d
  add⁰≈ (sa P) R′ (oL j k e x) y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLl j j x R′ y gx gy m gm um tm (⊲-tr e tm) m′ gm′ um′ tm′ am′ is′ d
  add⁰≈ (lw i) R′ (oL j k e x) y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLl (◁-tr j i) j x R′ y gx gy m gm um tm (⊲-tr e tm) m′ gm′ um′ tm′ am′ is′ d
  add⁰≈ R R′ (ow p′ g′ x) y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addl R R′ x y g′ gy m gm um (⊲-tr p′ tm) am m′ gm′ um′ tm′ am′ is′ d
  add⁰≈ R (sa P) X@o0 (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.suc C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@o0 (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) d
  add⁰≈ R (sa P) X@o0 (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.lim n C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@o0 (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) d
  add⁰≈ R (sa P) X@o0 (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X j j y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e tm′) d
  add⁰≈ R (lw i) X@o0 (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X (◁-tr j i) j y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e tm′) d
  add⁰≈ R R′ X@o0 (ow p′ g′ y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R R′ X y gx g′ m gm um tm am is m′ gm′ um′ (⊲-tr p′ tm′) am′ d
  add⁰≈ R (sa P) X@(os x) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.suc C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(os x) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) d
  add⁰≈ R (sa P) X@(os x) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.lim n C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(os x) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) d
  add⁰≈ R (sa P) X@(os x) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X j j y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e tm′) d
  add⁰≈ R (lw i) X@(os x) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X (◁-tr j i) j y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e tm′) d
  add⁰≈ R R′ X@(os x) (ow p′ g′ y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R R′ X y gx g′ m gm um tm am is m′ gm′ um′ (⊲-tr p′ tm′) am′ d
  add⁰≈ R (sa P) X@(ol F) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.suc C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(ol F) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) d
  add⁰≈ R (sa P) X@(ol F) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.lim n C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(ol F) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) d
  add⁰≈ R (sa P) X@(ol F) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X j j y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e tm′) d
  add⁰≈ R (lw i) X@(ol F) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X (◁-tr j i) j y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e tm′) d
  add⁰≈ R R′ X@(ol F) (ow p′ g′ y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R R′ X y gx g′ m gm um tm am is m′ gm′ um′ (⊲-tr p′ tm′) am′ d
  add⁰≈ R (sa P) X@(oi r f) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.suc C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(oi r f) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) d
  add⁰≈ R (sa P) X@(oi r f) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.lim n C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(oi r f) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) d
  add⁰≈ R (sa P) X@(oi r f) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X j j y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e tm′) d
  add⁰≈ R (lw i) X@(oi r f) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X (◁-tr j i) j y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e tm′) d
  add⁰≈ R R′ X@(oi r f) (ow p′ g′ y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R R′ X y gx g′ m gm um tm am is m′ gm′ um′ (⊲-tr p′ tm′) am′ d
  add⁰≈ R (sa P) X@(od j₃ k₃ r f) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.suc C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(od j₃ k₃ r f) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) d
  add⁰≈ R (sa P) X@(od j₃ k₃ r f) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.lim n C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(od j₃ k₃ r f) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) d
  add⁰≈ R (sa P) X@(od j₃ k₃ r f) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X j j y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e tm′) d
  add⁰≈ R (lw i) X@(od j₃ k₃ r f) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X (◁-tr j i) j y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e tm′) d
  add⁰≈ R R′ X@(od j₃ k₃ r f) (ow p′ g′ y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R R′ X y gx g′ m gm um tm am is m′ gm′ um′ (⊲-tr p′ tm′) am′ d
  add⁰≈ R (sa P) X@(oc x f) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.suc C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(oc x f) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) d
  add⁰≈ R (sa P) X@(oc x f) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.lim n C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(oc x f) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) d
  add⁰≈ R (sa P) X@(oc x f) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X j j y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e tm′) d
  add⁰≈ R (lw i) X@(oc x f) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X (◁-tr j i) j y gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e tm′) d
  add⁰≈ R R′ X@(oc x f) (ow p′ g′ y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R R′ X y gx g′ m gm um tm am is m′ gm′ um′ (⊲-tr p′ tm′) am′ d
  add⁰≈ R R′ o0 o0 gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = ≈ow W um′ gu′ W′ E
  add⁰≈ R R′ (os x) (os y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh , ez , ex , d) =
    refl , ea , m≈ is is′ um tm am um′ tm′ am′ eu ex (bw≈ R R′ eh ez) , add≈ R R′ x y gx gy m gm um tm am m′ gm′ um′ tm′ am′ d
  add⁰≈ R R′ (ol F) (ol G) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = λ n → add≈ R R′ (F n) (G n) gx gy m gm um tm am m′ gm′ um′ tm′ am′ (d n)
  add⁰≈ (sa P) (sa P′) (oi r f) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh , ez , ex , ek , N) =
    refl , ea , m≈ is is′ um tm am um′ tm′ am′ eu ex z≈ , ek , (λ {v} {v′} q q′ g g′ vv y y′ d′ →
      add≈ (sa P) (sa P′) _ _ g g′ v g (⊲-tr um q) C.self (z⊲ v) v′ g′ (⊲-tr um′ q′) C.self (z⊲ v′)
        (nI {r = r} {r′} {f} {f′} N (⊲-tr tm q) (⊲-tr tm′ q′) g g′ vv _ _ (V→ (≪S (≪∘ r P)) (≪S (≪∘ r′ P′)) y y′ d′)))
  add⁰≈ (lw i) (lw i′) (oi r f) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (refl , ez , ex , ek , N) =
    refl , refl , ea , m≈ is is′ um tm am um′ tm′ am′ eu ex ez , ek , (λ {v} {v′} q q′ g g′ vv y y′ d′ →
      add≈ (lw i) (lw i′) _ _ g g′ v g (⊲-tr um q) C.self (⊲-tr am q) v′ g′ (⊲-tr um′ q′) C.self (⊲-tr am′ q′)
        (nI {r = r} {r′} {f} {f′} N (⊲-tr tm q) (⊲-tr tm′ q′) g g′ vv _ _ (W→ i i′ y y′ d′)))
  add⁰≈ (sa P) (lw i′) (oi r f) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (refl , _) = ⊥-elim (<irr i′)
  add⁰≈ (lw i) (sa P′) (oi r f) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (refl , _) = ⊥-elim (<irr i)
  add⁰≈ (sa P) (sa P′) (od j k r f) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh₀ , eh , ez , ex , ek , N) =
    refl , eh , ea , m≈ is is′ um tm am um′ tm′ am′ eu ex z≈ , ek , (λ {v} {v′} q q′ g g′ vv y y′ d′ →
      add≈ (sa P) (sa P′) _ _ g g′ v g (⊲-tr um q) C.self (z⊲ v) v′ g′ (⊲-tr um′ q′) C.self (z⊲ v′)
        (nD {j = j} {j′} {f} {f′} N (⊲-tr tm q) (⊲-tr tm′ q′) g g′ vv _ _ (W→ j j′ y y′ d′)))
  add⁰≈ (lw i) (lw i′) (od j k r f) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh₀ , eh , ez , ex , ek , N) =
    refl , eh , ea , m≈ is is′ um tm am um′ tm′ am′ eu ex ez , ek , (λ {v} {v′} q q′ g g′ vv y y′ d′ →
      add≈ (lw i) (lw i′) _ _ g g′ v g (⊲-tr um q) C.self (⊲-tr am q) v′ g′ (⊲-tr um′ q′) C.self (⊲-tr am′ q′)
        (nD {j = j} {j′} {f} {f′} N (⊲-tr tm q) (⊲-tr tm′ q′) g g′ vv _ _ (W→ (◁-tr j i) (◁-tr j′ i′) y y′ d′)))
  add⁰≈ (sa P) (lw i′) (od j k r f) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (refl , _) = ⊥-elim (<irr i′)
  add⁰≈ (lw i) (sa P′) (od j k r f) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (refl , _) = ⊥-elim (<irr i)
  add⁰≈ R R′ (oc x f) (oc y f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh , ez , ex , d , N) =
    refl , ea , m≈ is is′ um tm am um′ tm′ am′ eu ex (bw≈ R R′ eh ez) , add≈ R R′ x y gx gy m gm um tm am m′ gm′ um′ tm′ am′ d ,
    (λ {v} {v′} q q′ g g′ vv →
      add≈ R R′ (f (⊲-tr tm q) g) (f′ (⊲-tr tm′ q′) g′) g g′ v g (⊲-tr um q) C.self (⊲-tr am q) v′ g′ (⊲-tr um′ q′) C.self (⊲-tr am′ q′) (N (⊲-tr tm q) (⊲-tr tm′ q′) g g′ vv))
  add⁰≈ R R′ o0 (os y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ o0 (ol G) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ o0 (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ o0 (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ o0 (oc y f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (os x) o0 gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (os x) (ol G) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (os x) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (os x) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (os x) (oc y f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (ol F) o0 gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (ol F) (os y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (ol F) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (ol F) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (ol F) (oc y f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oi r f) o0 gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oi r f) (os y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oi r f) (ol G) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oi r f) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oi r f) (oc y f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (od j k r f) o0 gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (od j k r f) (os y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (od j k r f) (ol G) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (od j k r f) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (od j k r f) (oc y f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oc x f) o0 gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oc x f) (os y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oc x f) (ol G) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oc x f) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oc x f) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()

rep≈ : ∀ {q t t′ u u′} {y : 𝓞 q t u} {y′ : 𝓞 q t′ u′} → t ≈ᴬ t′ → u ≈ᴬ u′ → y ≈ y′ → (g : Gw u) (g′ : Gw u′) → ∀ n → rep y g n ≈ rep y′ g′ n
rep≈ et eu e g g′ zero = tt
rep≈ et eu e g g′ (suc zero) = e
rep≈ {u = u} {u′} {y = y} {y′} et eu e g g′ (suc (suc m)) =
  AddE.add≈ et eu (rep≈ et eu e g g′ (suc m)) g g′ (sa C.self) (sa C.self) y y′ g g′ u g C.self C.self (z⊲ u) u′ g′ C.self C.self (z⊲ u′) e
```
