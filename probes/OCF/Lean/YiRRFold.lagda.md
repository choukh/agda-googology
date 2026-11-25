# N 的同层折叠保持
不读记号；编译定理：`NoΩ` 层号上，表任取（两侧可不同），两侧的底按 `N` 相关且右侧的底不低于标准 Ω 树（`YiLXClimb.Dom`），则折叠保持起点与输入树的 `N` 关系（`fl`）；一切层号上折叠不低于起点（`inflA`）。
`≼W` 一行（`nodeW`）：保留时目标槽位上有对应的入口（`kpE`，换型的逆都是恒等）；走链时入口之上取链的第 1 项，`Dom` 与 `geβ` 给出链的第 1 项高于入口，不用传递性。其余各行照 `YiLXFold.fl/inflA`、`YiVRFold.node≼/kpR` 搬来。
不否定什么；跨层在 [YiRRClimb](YiRRClimb.lagda.md)。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRRFold where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; Keep; mapK; kp; kp⁼; node⁺)
open import OCF.Lean.YiVRRel using (NoΩ)
open import OCF.Lean.YiVRFold using (Pr; posW-pr)
open import OCF.Lean.YiTBRow using (Rb; ψ; mono; dW-ind)
open import OCF.Lean.YiLXClimb using (_⊴◃_; Dom)
open import OCF.Lean.YiRRRel

infix 4 _⊴ⁿ_
_⊴ⁿ_ : ∀ {ℓ} → Base ℓ → Base ℓ → Set
_⊴ⁿ_ {ℓ} B B′ = (j : L) (w : j ≤ ℓ) → Pr w → N j (proj₁ (B j w)) (proj₁ (B′ j w))

⊴◃-tr : ∀ {i} {x y z : Tr i} → x ⊴◃ y → y ⊴◃ z → x ⊴◃ z
⊴◃-tr (inj₁ refl) e = e
⊴◃-tr (inj₂ d) (inj₁ refl) = inj₂ d
⊴◃-tr (inj₂ d) (inj₂ e) = inj₂ (◃t d e)

geβ : (ℓ : L) (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) (x : Tr ℓ)
    → proj₁ β ⊴◃ proj₁ (ψ ℓ o r B j w β x)
geβ ℓ o r B j w β x with zl x
... | inj₁ refl = inj₁ refl
... | inj₂ d    = inj₂ (mono ℓ o r B j w β d)
```

## 保留判定: 换型保持分支关系, 入口有对应

```agda
KR : ∀ {j X x₀} → (X → X → Set) → Keep j X x₀ → Set
KR {j} RX (just (q , cv , _)) = (z z′ : Br j q) → NB j q z z′ → RX (cv z) (cv z′)
KR     RX nothing             = ⊤

mapKR : ∀ {j X Y x₀ y₀} {RX : X → X → Set} {RY : Y → Y → Set} (f : X → Y) (e : f x₀ ≡ y₀)
      → (∀ {x x′} → RX x x′ → RY (f x) (f x′)) → (m : Keep j X x₀) → KR RX m → KR RY (mapK f e m)
mapKR f e fr (just (q , cv , g)) kr = λ z z′ r → fr (kr z z′ r)
mapKR f e fr nothing             kr = tt

KE : ∀ {j X x₀} → (X → X → Set) → (X → Set) → Keep j X x₀ → Set
KE {j} RX EX (just (q , cv , _)) =
  (z : _) → EX z → Σ (Br j q) λ u → NE j q u × ((u′ : Br j q) → NB j q u u′ → RX z (cv u′))
KE     RX EX nothing             = ⊤

mapKE : ∀ {j X Y x₀ y₀} {RX : X → X → Set} {EX : X → Set} {RY : Y → Y → Set} {EY : Y → Set}
      (f : X → Y) (e : f x₀ ≡ y₀) (g : Y → X) → (∀ y → EY y → EX (g y)) → (∀ y x′ → RX (g y) x′ → RY y (f x′))
      → (m : Keep j X x₀) → KE RX EX m → KE RY EY (mapK f e m)
mapKE f e g hE hR (just (q , cv , _)) ke = λ y ey →
  proj₁ (ke (g y) (hE y ey)) , proj₁ (proj₂ (ke (g y) (hE y ey))) ,
  λ u′ r → hR y (cv u′) (proj₂ (proj₂ (ke (g y) (hE y ey))) u′ r)
mapKE f e g hE hR nothing ke = tt

mutual
  kpR : (ℓ : L) (o : Ok ℓ) (p : Pos ℓ) → ∀ {j} (w : j ≤ ℓ) → KR (NB ℓ p) (kp ℓ o p w)
  kpR ℓ             o               p              self      = λ z z′ r → r
  kpR (nd s h)      (_ , oc)        (inj₂ (c , t)) (inu vs)  = kpR⁼ (h c) (oc c) t (vs c)
  kpR (nd (sΩ k) h) ((_ , kh) , oc) (inj₂ (c , t)) (ink v)   = kpR⁼ (h c) (oc c) t (v ∙ kh c)
  kpR (nd sS h)     (_ , oc)        (inj₂ (c , t)) (inc _ v) = kpR⁼ (h c) (oc c) t v
  kpR (nd sL g)     (r , oc)        (inj₂ (m , t)) (inc n v) =
    cW-ind (KR (NB⁼ (g m) t)) (way g r m n)
      (λ u → mapKR (pshBr u t) (pshFirst u t) (pshN u t) (kp⁼ (g n) (oc n) (psh u t) v) (kpR⁼ (g n) (oc n) (psh u t) v))
      (λ u → kpR⁼ (g m) (oc m) t (v ∙ u))
  kpR (nd (sΩ k) h) _               (inj₂ _)       (inc _ _) = tt
  kpR (nd (sΩ k) h) ((ok , _) , _)  (inj₁ t)       (ink v)   = kpR⁼ k ok t v
  kpR (nd (sΩ k) h) ((_ , kh) , oc) (inj₁ t)       (inc c v) =
    mapKR (pshBr (kh c) t) (pshFirst (kh c) t) (pshN (kh c) t) (kp⁼ (h c) (oc c) (psh (kh c) t) v)
          (kpR⁼ (h c) (oc c) (psh (kh c) t) v)
  kpR (nd (sΩ k) h) ((_ , kh) , oc) (inj₁ t)       (inu vs)  =
    mapKR (pshBr (kh zero) t) (pshFirst (kh zero) t) (pshN (kh zero) t) (kp⁼ (h zero) (oc zero) (psh (kh zero) t) (vs zero))
          (kpR⁼ (h zero) (oc zero) (psh (kh zero) t) (vs zero))

  kpR⁼ : (a : L) (o : Ok a) (t : Pos⁼ a) → ∀ {j} (w : j ≤ a) → KR (NB⁼ a t) (kp⁼ a o t w)
  kpR⁼ a o (inj₁ _) w = tt
  kpR⁼ a o (inj₂ p) w = kpR a o p w

mutual
  kpE : (ℓ : L) (o : Ok ℓ) (p : Pos ℓ) → ∀ {j} (w : j ≤ ℓ) → KE (NB ℓ p) (NE ℓ p) (kp ℓ o p w)
  kpE ℓ             o               p              self      = λ z ez → z , ez , λ u′ r → r
  kpE (nd s h)      (_ , oc)        (inj₂ (c , t)) (inu vs)  = kpE⁼ (h c) (oc c) t (vs c)
  kpE (nd (sΩ k) h) ((_ , kh) , oc) (inj₂ (c , t)) (ink v)   = kpE⁼ (h c) (oc c) t (v ∙ kh c)
  kpE (nd sS h)     (_ , oc)        (inj₂ (c , t)) (inc _ v) = kpE⁼ (h c) (oc c) t v
  kpE (nd sL g)     (r , oc)        (inj₂ (m , t)) (inc n v) =
    cW-ind (KE (NB⁼ (g m) t) (NE⁼ (g m) t)) (way g r m n)
      (λ u → mapKE (pshBr u t) (pshFirst u t) (pshBr⁻ u t) (λ y ey → pshE u t ey) (λ y x′ r → pshN⁻ u t r)
               (kp⁼ (g n) (oc n) (psh u t) v) (kpE⁼ (g n) (oc n) (psh u t) v))
      (λ u → kpE⁼ (g m) (oc m) t (v ∙ u))
  kpE (nd (sΩ k) h) _               (inj₂ _)       (inc _ _) = tt
  kpE (nd (sΩ k) h) ((ok , _) , _)  (inj₁ t)       (ink v)   = kpE⁼ k ok t v
  kpE (nd (sΩ k) h) ((_ , kh) , oc) (inj₁ t)       (inc c v) =
    mapKE (pshBr (kh c) t) (pshFirst (kh c) t) (pshBr⁻ (kh c) t) (λ y ey → pshE (kh c) t ey) (λ y x′ r → pshN⁻ (kh c) t r)
          (kp⁼ (h c) (oc c) (psh (kh c) t) v) (kpE⁼ (h c) (oc c) (psh (kh c) t) v)
  kpE (nd (sΩ k) h) ((_ , kh) , oc) (inj₁ t)       (inu vs)  =
    mapKE (pshBr (kh zero) t) (pshFirst (kh zero) t) (pshBr⁻ (kh zero) t) (λ y ey → pshE (kh zero) t ey)
          (λ y x′ r → pshN⁻ (kh zero) t r)
          (kp⁼ (h zero) (oc zero) (psh (kh zero) t) (vs zero)) (kpE⁼ (h zero) (oc zero) (psh (kh zero) t) (vs zero))

  kpE⁼ : (a : L) (o : Ok a) (t : Pos⁼ a) → ∀ {j} (w : j ≤ a) → KE (NB⁼ a t) (NE⁼ a t) (kp⁼ a o t w)
  kpE⁼ a o (inj₁ _) w = tt
  kpE⁼ a o (inj₂ p) w = kpE a o p w
```

## 结点

`nodeW`: 右边是结点, 左边由 `≼W` 进入它的源槽位. 走链时用链的第 1 项 (部分和的第 1 项右加第 0 项).

```agda
node≼ʳ : ∀ {j X x₀} (m : Keep j X x₀) (G : X → Tr⁺ j) (s : X → X) {a : Tr j}
       → N j a (proj₁ (G x₀)) → N j a (proj₁ (node⁺ m G s))
node≼ʳ {j} (just (q , cv , e)) G s {a} d = ≼w (subst (λ t → N j a (proj₁ (G t))) (sym e) d)
node≼ʳ nothing                 G s d     = ≼l 0 d

node≼ : ∀ {j X x₀} (RX : X → X → Set) (m : Keep j X x₀) → KR RX m → (G G′ : X → Tr⁺ j) (s s′ : X → X)
      → RX x₀ x₀ → ((z z′ : X) → RX z z′ → N j (proj₁ (G z)) (proj₁ (G′ z′))) → ((z z′ : X) → RX z z′ → RX (s z) (s′ z′))
      → N j (proj₁ (node⁺ m G s)) (proj₁ (node⁺ m G′ s′))
node≼ RX (just (q , cv , _)) kr G G′ s s′ r₀ hG hs = w≼w (λ z z′ r → hG (cv z) (cv z′) (kr z z′ r))
node≼ {x₀ = x₀} RX nothing   kr G G′ s s′ r₀ hG hs =
  limc≼ (λ n → G (iter s x₀ n)) (λ n → G′ (iter s′ x₀ n)) (λ n → hG _ _ (ch n))
  where
  ch : (n : ℕ) → RX (iter s x₀ n) (iter s′ x₀ n)
  ch zero    = r₀
  ch (suc n) = hs _ _ (ch n)

nodeW : ∀ {j X x₀} (RX : X → X → Set) (EX : X → Set) (m : Keep j X x₀) → KE RX EX m → (G′ : X → Tr⁺ j) (s′ : X → X)
      {a : Tr j} (z : X) → EX z → RX z (s′ x₀) → ((z′ : X) → RX z z′ → N j a (proj₁ (G′ z′)))
      → N j a (proj₁ (node⁺ m G′ s′))
nodeW RX EX (just (q , cv , _)) ke G′ s′ z ez rz k =
  ≼W (proj₁ (ke z ez)) (proj₁ (proj₂ (ke z ez))) (λ u′ r → k (cv u′) (proj₂ (proj₂ (ke z ez)) u′ r))
nodeW {x₀ = x₀} RX EX nothing ke G′ s′ z ez rz k = ≼l 1 (right-add (k (s′ x₀) rz) (proj₁ (G′ x₀)))
```

## 折叠不低于起点

```agda
cb : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) (c : Ch s) (x : Tr (nd s h)) → Base (h c)
cb s h o r B c x i u = ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x

inflA : (ℓ : L) (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) (x : Tr ℓ) {a : Tr j}
      → N j a (proj₁ β) → N j a (proj₁ (ψ ℓ o r B j w β x))
inflA ℓ o r B j w β zero      d = d
inflA ℓ o r B j w β (suc x)   d = ≼l 0 (inflA ℓ o r B j w β x d)
inflA ℓ o r B j w β (lim f a) d = ≼l 0 (inflA ℓ o r B j w β (f 0) d)
inflA ℓ o r B j w β (Ω p g)   d = node≼ʳ (kp ℓ o p w) _ _ (inflA ℓ o r B j w β (g (fromBr ℓ p zero)) d)
inflA (nd s h) o r B _ self β (up x c y e) d =
  ≼Up (h c) (down stop c) (ψ (nd s h) o r B _ self β x) y (inflA (nd s h) o r B _ self β x d)
inflA (nd s h) o r B j (inu ws) β (up x c y e) d =
  inflA (h c) (proj₂ o c) (proj₂ r c) (cb s h o r B c x) j (ws c) (ψ (nd s h) o r B j (inu ws) β x) y
    (inflA (nd s h) o r B j (inu ws) β x d)
inflA (nd (sΩ k) h) o r B j (ink v) β (up x c y e) d =
  inflA (h c) (proj₂ o c) (proj₂ r c) (cb (sΩ k) h o r B c x) j (v ∙ proj₂ (proj₁ o) c) (ψ (nd (sΩ k) h) o r B j (ink v) β x) y
    (inflA (nd (sΩ k) h) o r B j (ink v) β x d)
inflA (nd sS h) o r B j (inc c′ v) β (up x c y e) d =
  inflA (h c) (proj₂ o c) (proj₂ r c) (cb sS h o r B c x) j v (ψ (nd sS h) o r B j (inc c′ v) β x) y
    (inflA (nd sS h) o r B j (inc c′ v) β x d)
inflA (nd sL g) o r B j (inc n v) β (up x m y e) {a} d =
  cW-ind (λ Z → N j a (proj₁ Z)) (way g (proj₁ o) m n)
    (λ u → inflA (g n) (proj₂ o n) (proj₂ r n) (cb sL g o r B n x) j v (ψ (nd sL g) o r B j (inc n v) β x)
             (proj₁ (emb (g n) (proj₂ o n) u (y , e))) (inflA (nd sL g) o r B j (inc n v) β x d))
    (λ u → inflA (g m) (proj₂ o m) (proj₂ r m) (cb sL g o r B m x) j (v ∙ u) (ψ (nd sL g) o r B j (inc n v) β x) y
             (inflA (nd sL g) o r B j (inc n v) β x d))
inflA (nd (sΩ k) h) o r B j (inc c′ v) β (up x c y e) {a} d =
  dW-ind (λ Z → N j a (proj₁ Z)) (proj₁ r c c′)
    (λ u → inflA (h c) (proj₂ o c) (proj₂ r c) (cb (sΩ k) h o r B c x) j (v ∙ u) (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) y
             (inflA (nd (sΩ k) h) o r B j (inc c′ v) β x d))
    (λ u → inflA (h c′) (proj₂ o c′) (proj₂ r c′) (cb (sΩ k) h o r B c′ x) j v (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x)
             (proj₁ (emb (h c′) (proj₂ o c′) u (y , e))) (inflA (nd (sΩ k) h) o r B j (inc c′ v) β x d))
    (≼+ (inflA (nd (sΩ k) h) o r B j (inc c′ v) β x d) _)

domcb : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) → Dom B
      → (c : Ch s) (x : Tr (nd s h)) → Dom (cb s h o r B c x)
domcb s h o r B dB c x i u _ = ⊴◃-tr (dB i (inc c u) tt) (geβ (nd s h) o r B i (inc c u) (B i (inc c u)) x)
```

## 折叠保持关系

```agda
fl : (ℓ : L) → NoΩ ℓ → (o : Ok ℓ) (r r′ : Rb ℓ) (B B′ : Base ℓ) → B ⊴ⁿ B′ → Dom B′ → (j : L) (w : j ≤ ℓ) (β β′ : Tr⁺ j)
    → N j (proj₁ β) (proj₁ β′) → {x x′ : Tr ℓ} → N ℓ x x′
    → N j (proj₁ (ψ ℓ o r B j w β x)) (proj₁ (ψ ℓ o r′ B′ j w β′ x′))
fl ℓ ν o r r′ B B′ hB dB j w β β′ hβ {x′ = x′} z≼ = inflA ℓ o r′ B′ j w β′ x′ hβ
fl ℓ ν o r r′ B B′ hB dB j w β β′ hβ (s≼s d)  = next≼ _ _ (fl ℓ ν o r r′ B B′ hB dB j w β β′ hβ d)
fl ℓ ν o r r′ B B′ hB dB j w β β′ hβ (≼s d)   = ≼l 0 (fl ℓ ν o r r′ B B′ hB dB j w β β′ hβ d)
fl ℓ ν o r r′ B B′ hB dB j w β β′ hβ (≼l n d) = ≼l n (fl ℓ ν o r r′ B B′ hB dB j w β β′ hβ d)
fl ℓ ν o r r′ B B′ hB dB j w β β′ hβ (l≼ h)   = l≼ (λ n → fl ℓ ν o r r′ B B′ hB dB j w β β′ hβ (h n))
fl ℓ ν o r r′ B B′ hB dB j w β β′ hβ (≼w {p = p} d) = node≼ʳ (kp ℓ o p w) _ _ (fl ℓ ν o r r′ B B′ hB dB j w β β′ hβ d)
fl ℓ ν o r r′ B B′ hB dB j w β β′ hβ (w≼w {p = p} {g = g} {g′ = g′} h) =
  node≼ (NB ℓ p) (kp ℓ o p w) (kpR ℓ o p w)
    (λ z → ψ ℓ o r B j w β (g z)) (λ z → ψ ℓ o r′ B′ j w β′ (g′ z))
    (λ z → fromBr ℓ p (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z))))
    (λ z → fromBr ℓ p (proj₁ (ψ ℓ o r′ B′ (at ℓ p) (posW ℓ p) (B′ (at ℓ p) (posW ℓ p)) (g′ z))))
    (fromN ℓ p z≼)
    (λ z z′ q → fl ℓ ν o r r′ B B′ hB dB j w β β′ hβ (h z z′ q))
    (λ z z′ q → fromN ℓ p (fl ℓ ν o r r′ B B′ hB dB (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (B′ (at ℓ p) (posW ℓ p))
                             (hB (at ℓ p) (posW ℓ p) (posW-pr ℓ p)) (h z z′ q)))
fl ℓ ν o r r′ B B′ hB dB j w β β′ hβ (≼W {p = p} {g = g} z ez k) =
  nodeW (NB ℓ p) (NE ℓ p) (kp ℓ o p w) (kpE ℓ o p w)
    (λ z → ψ ℓ o r′ B′ j w β′ (g z))
    (λ z → fromBr ℓ p (proj₁ (ψ ℓ o r′ B′ (at ℓ p) (posW ℓ p) (B′ (at ℓ p) (posW ℓ p)) (g z))))
    z ez
    (ez _ (⊴◃-tr (dB (at ℓ p) (posW ℓ p) (posW-pr ℓ p))
                 (geβ ℓ o r′ B′ (at ℓ p) (posW ℓ p) (B′ (at ℓ p) (posW ℓ p)) (g (fromBr ℓ p zero)))))
    (λ z′ q → fl ℓ ν o r r′ B B′ hB dB j w β β′ hβ (k z′ q))
fl (nd s h) ν o r r′ B B′ hB dB _ self β β′ hβ (≼u {x = x} {c = c} {y = y} d) =
  ≼Up (h c) (down stop c) (ψ (nd s h) o r′ B′ _ self β′ x) y (fl (nd s h) ν o r r′ B B′ hB dB _ self β β′ hβ d)
fl (nd sS h) ν o r r′ B B′ hB dB j (inu ws) β β′ hβ (≼u {x = x} {c = c} {y = y} d) =
  inflA (h c) (proj₂ o c) (proj₂ r′ c) (cb sS h o r′ B′ c x) j (ws c) (ψ (nd sS h) o r′ B′ j (inu ws) β′ x) y
       (fl (nd sS h) ν o r r′ B B′ hB dB j (inu ws) β β′ hβ d)
fl (nd sL g) ν o r r′ B B′ hB dB j (inu ws) β β′ hβ (≼u {x = x} {c = c} {y = y} d) =
  inflA (g c) (proj₂ o c) (proj₂ r′ c) (cb sL g o r′ B′ c x) j (ws c) (ψ (nd sL g) o r′ B′ j (inu ws) β′ x) y
       (fl (nd sL g) ν o r r′ B B′ hB dB j (inu ws) β β′ hβ d)
fl (nd sS h) ν o r r′ B B′ hB dB j (inc c′ v) β β′ hβ (≼u {x = x} {c = c} {y = y} d) =
  inflA (h c) (proj₂ o c) (proj₂ r′ c) (cb sS h o r′ B′ c x) j v (ψ (nd sS h) o r′ B′ j (inc c′ v) β′ x) y
       (fl (nd sS h) ν o r r′ B B′ hB dB j (inc c′ v) β β′ hβ d)
fl (nd sL g) ν o r r′ B B′ hB dB j (inc n v) β β′ hβ {x = a} (≼u {x = x} {c = m} {y = y} {e = e} d) =
  cW-ind (λ Z → N j (proj₁ (ψ (nd sL g) o r B j (inc n v) β a)) (proj₁ Z)) (way g (proj₁ o) m n)
    (λ u → inflA (g n) (proj₂ o n) (proj₂ r′ n) (cb sL g o r′ B′ n x) j v (ψ (nd sL g) o r′ B′ j (inc n v) β′ x)
             (proj₁ (emb (g n) (proj₂ o n) u (y , e))) (fl (nd sL g) ν o r r′ B B′ hB dB j (inc n v) β β′ hβ d))
    (λ u → inflA (g m) (proj₂ o m) (proj₂ r′ m) (cb sL g o r′ B′ m x) j (v ∙ u) (ψ (nd sL g) o r′ B′ j (inc n v) β′ x) y
             (fl (nd sL g) ν o r r′ B B′ hB dB j (inc n v) β β′ hβ d))
fl (nd s h) ν o r r′ B B′ hB dB _ self β β′ hβ (u≼u {x = x} {x′ = x′} {c = c} dx dy) =
  Up≼ (h c) (down stop c) (ψ (nd s h) o r B _ self β x) (ψ (nd s h) o r′ B′ _ self β′ x′)
      (fl (nd s h) ν o r r′ B B′ hB dB _ self β β′ hβ dx) dy
fl (nd sS h) ν o r r′ B B′ hB dB j (inu ws) β β′ hβ (u≼u {x = x} {x′ = x′} {c = c} dx dy) =
  fl (h c) ν (proj₂ o c) (proj₂ r c) (proj₂ r′ c) (cb sS h o r B c x) (cb sS h o r′ B′ c x′)
     (λ i u _ → fl (nd sS h) ν o r r′ B B′ hB dB i (inc c u) (B i (inc c u)) (B′ i (inc c u)) (hB i (inc c u) tt) dx)
     (domcb sS h o r′ B′ dB c x′)
     j (ws c) (ψ (nd sS h) o r B j (inu ws) β x) (ψ (nd sS h) o r′ B′ j (inu ws) β′ x′)
     (fl (nd sS h) ν o r r′ B B′ hB dB j (inu ws) β β′ hβ dx) dy
fl (nd sL g) ν o r r′ B B′ hB dB j (inu ws) β β′ hβ (u≼u {x = x} {x′ = x′} {c = c} dx dy) =
  fl (g c) (ν c) (proj₂ o c) (proj₂ r c) (proj₂ r′ c) (cb sL g o r B c x) (cb sL g o r′ B′ c x′)
     (λ i u _ → fl (nd sL g) ν o r r′ B B′ hB dB i (inc c u) (B i (inc c u)) (B′ i (inc c u)) (hB i (inc c u) tt) dx)
     (domcb sL g o r′ B′ dB c x′)
     j (ws c) (ψ (nd sL g) o r B j (inu ws) β x) (ψ (nd sL g) o r′ B′ j (inu ws) β′ x′)
     (fl (nd sL g) ν o r r′ B B′ hB dB j (inu ws) β β′ hβ dx) dy
fl (nd sS h) ν o r r′ B B′ hB dB j (inc c′ v) β β′ hβ (u≼u {x = x} {x′ = x′} {c = c} dx dy) =
  fl (h c) ν (proj₂ o c) (proj₂ r c) (proj₂ r′ c) (cb sS h o r B c x) (cb sS h o r′ B′ c x′)
     (λ i u _ → fl (nd sS h) ν o r r′ B B′ hB dB i (inc c u) (B i (inc c u)) (B′ i (inc c u)) (hB i (inc c u) tt) dx)
     (domcb sS h o r′ B′ dB c x′)
     j v (ψ (nd sS h) o r B j (inc c′ v) β x) (ψ (nd sS h) o r′ B′ j (inc c′ v) β′ x′)
     (fl (nd sS h) ν o r r′ B B′ hB dB j (inc c′ v) β β′ hβ dx) dy
fl (nd sL g) ν o r r′ B B′ hB dB j (inc n v) β β′ hβ (u≼u {x = x} {x′ = x′} {c = m} {y = y} {y′ = y′} {e = e} {e′ = e′} dx dy) =
  cW-ind₂ (λ Z Z′ → N j (proj₁ Z) (proj₁ Z′)) (way g (proj₁ o) m n)
    (λ u → fl (g n) (ν n) (proj₂ o n) (proj₂ r n) (proj₂ r′ n) (cb sL g o r B n x) (cb sL g o r′ B′ n x′)
             (λ i u′ _ → fl (nd sL g) ν o r r′ B B′ hB dB i (inc n u′) (B i (inc n u′)) (B′ i (inc n u′)) (hB i (inc n u′) tt) dx)
             (domcb sL g o r′ B′ dB n x′)
             j v (ψ (nd sL g) o r B j (inc n v) β x) (ψ (nd sL g) o r′ B′ j (inc n v) β′ x′)
             (fl (nd sL g) ν o r r′ B B′ hB dB j (inc n v) β β′ hβ dx)
             (emb≼ (g n) (proj₂ o n) u {y = y , e} {y′ = y′ , e′} dy))
    (λ u → fl (g m) (ν m) (proj₂ o m) (proj₂ r m) (proj₂ r′ m) (cb sL g o r B m x) (cb sL g o r′ B′ m x′)
             (λ i u′ _ → fl (nd sL g) ν o r r′ B B′ hB dB i (inc m u′) (B i (inc m u′)) (B′ i (inc m u′)) (hB i (inc m u′) tt) dx)
             (domcb sL g o r′ B′ dB m x′)
             j (v ∙ u) (ψ (nd sL g) o r B j (inc n v) β x) (ψ (nd sL g) o r′ B′ j (inc n v) β′ x′)
             (fl (nd sL g) ν o r r′ B B′ hB dB j (inc n v) β β′ hβ dx) dy)
fl (nd (sΩ k) h) () o r r′ B B′ hB dB j w β β′ hβ (≼u d)
fl (nd (sΩ k) h) () o r r′ B B′ hB dB j w β β′ hβ (u≼u dx dy)
```
