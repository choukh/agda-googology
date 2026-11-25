# 候选 A: 不含 Ω 形状的层号上折叠对底单调

> 验收文件 (工具), 树、折叠、合法性一行不改. 编译定理, 无前提: 在不含 Ω 形状的层号上 (`NoΩ`), 候选 A 的折叠对底、起点、树保持 `YiVRRel` 的值关系 (`flK`), 证法照 `YiVRFold.fl` 的对应各行; 折叠不低于起点 (`inflK`, 以及第一位置序的 `geβ`).
> 关系的右延 (`le◃`): 关系后接第一位置序仍在关系里. 不涉及 Ω 形状的层号, 不否定什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKAMono where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKVPath
open import OCF.Lean.YiKVFold
open import OCF.Lean.YiCertFold using (Base; Keep; mapK; node⁺; nodeLe)
open import OCF.Lean.YiVRRel hiding (emb≼)
open import OCF.Lean.YiVRFold using (Pr; _⊴_; posW-pr; KR)
```

## 关系的右延, 折叠不低于起点

```agda
le◃ : ∀ {ℓ} {a b c : Tr ℓ} → Le ℓ a b → ℓ ⊢ b ◃ c → Le ℓ a c
le◃ d ◃s           = ≼s d
le◃ d (◃l n)       = ≼l n d
le◃ d ◃w           = ≼w d
le◃ d (◃u x c y e) = ≼u d
le◃ {nd s h} z≼          (◃c x c r) = z≼
le◃ {nd s h} (l≼ k)      (◃c x c r) = l≼ (λ n → le◃ (k n) (◃c x c r))
le◃ {nd s h} (≼u d)      (◃c x c r) = ≼u d
le◃ {nd s h} (u≼u dx dy) (◃c x c r) = u≼u dx (le◃ {h c} dy r)
le◃ d (◃t e f) = le◃ (le◃ d e) f

le⊴ : ∀ {ℓ} {a b c : Tr ℓ} → Le ℓ a b → (b ≡ c) ⊎ (ℓ ⊢ b ◃ c) → Le ℓ a c
le⊴ d (inj₁ refl) = d
le⊴ d (inj₂ e)    = le◃ d e

geβ : (ℓ : L) (o : Ok ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) (x : Tr ℓ)
    → (proj₁ β ≡ proj₁ (ψ ℓ o B j w β x)) ⊎ (j ⊢ proj₁ β ◃ proj₁ (ψ ℓ o B j w β x))
geβ ℓ o B j w β x with zl x
... | inj₁ refl = inj₁ refl
... | inj₂ d    = inj₂ (mono ℓ o B j w β d)

νc : ∀ {s h} → NoΩ (nd s h) → (c : Ch s) → NoΩ (h c)
νc {s = sS}   ν tt = ν
νc {s = sL}   ν n  = ν n
νc {s = sΩ k} () c
```

## 结点与保留判定

```agda
node≼ʳK : ∀ {j X x₀} (m : Keep j X x₀) (G : X → Tr⁺ j) (s : X → X) {a : Tr j}
        → Le j a (proj₁ (G x₀)) → Le j a (proj₁ (node⁺ m G s))
node≼ʳK {j} (just (q , cv , e)) G s {a} d = ≼w (subst (λ t → Le j a (proj₁ (G t))) (sym e) d)
node≼ʳK nothing                 G s d     = ≼l 0 d

node≼K : ∀ {j X x₀} (RX : X → X → Set) (m : Keep j X x₀) → KR RX m → (G G′ : X → Tr⁺ j) (s s′ : X → X)
       → RX x₀ x₀ → ((z z′ : X) → RX z z′ → Le j (proj₁ (G z)) (proj₁ (G′ z′))) → ((z z′ : X) → RX z z′ → RX (s z) (s′ z′))
       → Le j (proj₁ (node⁺ m G s)) (proj₁ (node⁺ m G′ s′))
node≼K RX (just (q , cv , _)) kr G G′ s s′ r₀ hG hs = w≼w (λ z z′ r → hG (cv z) (cv z′) (kr z z′ r))
node≼K {x₀ = x₀} RX nothing   kr G G′ s s′ r₀ hG hs =
  limc≼ (λ n → G (iter s x₀ n)) (λ n → G′ (iter s′ x₀ n)) (λ n → hG _ _ (ch n))
  where
  ch : (n : ℕ) → RX (iter s x₀ n) (iter s′ x₀ n)
  ch zero    = r₀
  ch (suc n) = hs _ _ (ch n)

mapKRK : ∀ {j X Y x₀ y₀} {RX : X → X → Set} {RY : Y → Y → Set} (f : X → Y) (e : f x₀ ≡ y₀)
       → (∀ {x x′} → RX x x′ → RY (f x) (f x′)) → (m : Keep j X x₀) → KR RX m → KR RY (mapK f e m)
mapKRK f e fr (just (q , cv , g)) kr = λ z z′ r → fr (kr z z′ r)
mapKRK f e fr nothing             kr = tt

mutual
  kpRK : (ℓ : L) → NoΩ ℓ → (o : Ok ℓ) (p : Pos ℓ) → ∀ {j} (w : j ≤ ℓ) → KR (LB ℓ p) (kp ℓ o p w)
  kpRK ℓ             ν o        p              self      = λ z z′ r → r
  kpRK (nd sS h)     ν (_ , oc) (inj₂ (c , t)) (inu vs)  = kpRK⁼ (h c) ν (oc c) t (vs c)
  kpRK (nd sL g)     ν (_ , oc) (inj₂ (c , t)) (inu vs)  = kpRK⁼ (g c) (ν c) (oc c) t (vs c)
  kpRK (nd sS h)     ν (_ , oc) (inj₂ (c , t)) (inc _ v) = kpRK⁼ (h c) ν (oc c) t v
  kpRK (nd sL g)     ν (r , oc) (inj₂ (m , t)) (inc n v) =
    cW-ind (KR (LB⁼ (g m) t)) (way g r m n)
      (λ u → mapKRK (pshBr u t) (pshFirst u t) (pshLB u t) (kp⁼ (g n) (oc n) (psh u t) v) (kpRK⁼ (g n) (ν n) (oc n) (psh u t) v))
      (λ u → kpRK⁼ (g m) (ν m) (oc m) t (v ∙ u))
  kpRK (nd (sΩ k) h) ()

  kpRK⁼ : (a : L) → NoΩ a → (o : Ok a) (t : Pos⁼ a) → ∀ {j} (w : j ≤ a) → KR (LB⁼ a t) (kp⁼ a o t w)
  kpRK⁼ a ν o (inj₁ _) w = tt
  kpRK⁼ a ν o (inj₂ p) w = kpRK a ν o p w
```

## 嵌入

```agda
embK≼ : (ℓ : L) → NoΩ ℓ → (o : Ok ℓ) {k : L} (v : k ≤ ℓ) {y y′ : Tr⁺ k} → Le k (proj₁ y) (proj₁ y′)
      → Le ℓ (proj₁ (emb ℓ o v y)) (proj₁ (emb ℓ o v y′))
embK≼ ℓ             ν o self      d = d
embK≼ (nd sS h)     ν o (inc c v) d = u≼u z≼ (embK≼ (h c) ν (proj₂ o c) v d)
embK≼ (nd sL g)     ν o (inc c v) d = u≼u z≼ (embK≼ (g c) (ν c) (proj₂ o c) v d)
embK≼ (nd sS h)     ν o (inu vs)  d = u≼u z≼ (embK≼ (h tt) ν (proj₂ o tt) (vs tt) d)
embK≼ (nd sL g)     ν o (inu vs)  d = u≼u z≼ (embK≼ (g zero) (ν zero) (proj₂ o zero) (vs zero) d)
embK≼ (nd (sΩ k) h) () o v d
```

## 折叠不低于起点 (关系版), 折叠保持关系

```agda
cbK : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (B : Base (nd s h)) (c : Ch s) (x : Tr (nd s h)) → Base (h c)
cbK s h o B c x i u = ψ (nd s h) o B i (inc c u) (B i (inc c u)) x

inflK : (ℓ : L) → NoΩ ℓ → (o : Ok ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) (x : Tr ℓ) {a : Tr j}
      → Le j a (proj₁ β) → Le j a (proj₁ (ψ ℓ o B j w β x))
inflK ℓ ν o B j w β zero      d = d
inflK ℓ ν o B j w β (suc x)   d = ≼l 0 (inflK ℓ ν o B j w β x d)
inflK ℓ ν o B j w β (lim f a) d = ≼l 0 (inflK ℓ ν o B j w β (f 0) d)
inflK ℓ ν o B j w β (Ω p g)   d = node≼ʳK (kp ℓ o p w) _ _ (inflK ℓ ν o B j w β (g (fromBr ℓ p zero)) d)
inflK (nd s h) ν o B _ self β (up x c y e) d =
  ≼Up (h c) (down stop c) (ψ (nd s h) o B _ self β x) y (inflK (nd s h) ν o B _ self β x d)
inflK (nd sS h) ν o B j (inu ws) β (up x c y e) d =
  inflK (h c) ν (proj₂ o c) (cbK sS h o B c x) j (ws c) (ψ (nd sS h) o B j (inu ws) β x) y (inflK (nd sS h) ν o B j (inu ws) β x d)
inflK (nd sL g) ν o B j (inu ws) β (up x c y e) d =
  inflK (g c) (ν c) (proj₂ o c) (cbK sL g o B c x) j (ws c) (ψ (nd sL g) o B j (inu ws) β x) y (inflK (nd sL g) ν o B j (inu ws) β x d)
inflK (nd sS h) ν o B j (inc c′ v) β (up x c y e) d =
  inflK (h c) ν (proj₂ o c) (cbK sS h o B c x) j v (ψ (nd sS h) o B j (inc c′ v) β x) y (inflK (nd sS h) ν o B j (inc c′ v) β x d)
inflK (nd sL g) ν o B j (inc n v) β (up x m y e) {a} d =
  cW-ind (λ Z → Le j a (proj₁ Z)) (way g (proj₁ o) m n)
    (λ u → inflK (g n) (ν n) (proj₂ o n) (cbK sL g o B n x) j v (ψ (nd sL g) o B j (inc n v) β x)
             (proj₁ (emb (g n) (proj₂ o n) u (y , e))) (inflK (nd sL g) ν o B j (inc n v) β x d))
    (λ u → inflK (g m) (ν m) (proj₂ o m) (cbK sL g o B m x) j (v ∙ u) (ψ (nd sL g) o B j (inc n v) β x) y
             (inflK (nd sL g) ν o B j (inc n v) β x d))
inflK (nd (sΩ k) h) () o B j w β (up x c y e) d

flK : (ℓ : L) → NoΩ ℓ → (o : Ok ℓ) (B B′ : Base ℓ) → B ⊴ B′ → (j : L) (w : j ≤ ℓ) (β β′ : Tr⁺ j)
    → Le j (proj₁ β) (proj₁ β′) → {x x′ : Tr ℓ} → Le ℓ x x′
    → Le j (proj₁ (ψ ℓ o B j w β x)) (proj₁ (ψ ℓ o B′ j w β′ x′))
flK ℓ ν o B B′ hB j w β β′ hβ {x′ = x′} z≼ = inflK ℓ ν o B′ j w β′ x′ hβ
flK ℓ ν o B B′ hB j w β β′ hβ (s≼s d)  = next≼ _ _ (flK ℓ ν o B B′ hB j w β β′ hβ d)
flK ℓ ν o B B′ hB j w β β′ hβ (≼s d)   = ≼l 0 (flK ℓ ν o B B′ hB j w β β′ hβ d)
flK ℓ ν o B B′ hB j w β β′ hβ (≼l n d) = ≼l n (flK ℓ ν o B B′ hB j w β β′ hβ d)
flK ℓ ν o B B′ hB j w β β′ hβ (l≼ h)   = l≼ (λ n → flK ℓ ν o B B′ hB j w β β′ hβ (h n))
flK ℓ ν o B B′ hB j w β β′ hβ (≼w {p = p} d) = node≼ʳK (kp ℓ o p w) _ _ (flK ℓ ν o B B′ hB j w β β′ hβ d)
flK ℓ ν o B B′ hB j w β β′ hβ (w≼w {p = p} {g = g} {g′ = g′} h) =
  node≼K (LB ℓ p) (kp ℓ o p w) (kpRK ℓ ν o p w)
    (λ z → ψ ℓ o B j w β (g z)) (λ z → ψ ℓ o B′ j w β′ (g′ z))
    (λ z → fromBr ℓ p (proj₁ (ψ ℓ o B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z))))
    (λ z → fromBr ℓ p (proj₁ (ψ ℓ o B′ (at ℓ p) (posW ℓ p) (B′ (at ℓ p) (posW ℓ p)) (g′ z))))
    (fromBr≼ ℓ p z≼)
    (λ z z′ r → flK ℓ ν o B B′ hB j w β β′ hβ (h z z′ r))
    (λ z z′ r → fromBr≼ ℓ p (flK ℓ ν o B B′ hB (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (B′ (at ℓ p) (posW ℓ p))
                               (hB (at ℓ p) (posW ℓ p) (posW-pr ℓ p)) (h z z′ r)))
-- 右边多一层嵌入
flK (nd s h) ν o B B′ hB _ self β β′ hβ (≼u {x = x} {c = c} {y = y} d) =
  ≼Up (h c) (down stop c) (ψ (nd s h) o B′ _ self β′ x) y (flK (nd s h) ν o B B′ hB _ self β β′ hβ d)
flK (nd sS h) ν o B B′ hB j (inu ws) β β′ hβ (≼u {x = x} {c = c} {y = y} d) =
  inflK (h c) ν (proj₂ o c) (cbK sS h o B′ c x) j (ws c) (ψ (nd sS h) o B′ j (inu ws) β′ x) y
       (flK (nd sS h) ν o B B′ hB j (inu ws) β β′ hβ d)
flK (nd sL g) ν o B B′ hB j (inu ws) β β′ hβ (≼u {x = x} {c = c} {y = y} d) =
  inflK (g c) (ν c) (proj₂ o c) (cbK sL g o B′ c x) j (ws c) (ψ (nd sL g) o B′ j (inu ws) β′ x) y
       (flK (nd sL g) ν o B B′ hB j (inu ws) β β′ hβ d)
flK (nd sS h) ν o B B′ hB j (inc c′ v) β β′ hβ (≼u {x = x} {c = c} {y = y} d) =
  inflK (h c) ν (proj₂ o c) (cbK sS h o B′ c x) j v (ψ (nd sS h) o B′ j (inc c′ v) β′ x) y
       (flK (nd sS h) ν o B B′ hB j (inc c′ v) β β′ hβ d)
flK (nd sL g) ν o B B′ hB j (inc n v) β β′ hβ {x = a} (≼u {x = x} {c = m} {y = y} {e = e} d) =
  cW-ind (λ Z → Le j (proj₁ (ψ (nd sL g) o B j (inc n v) β a)) (proj₁ Z)) (way g (proj₁ o) m n)
    (λ u → inflK (g n) (ν n) (proj₂ o n) (cbK sL g o B′ n x) j v (ψ (nd sL g) o B′ j (inc n v) β′ x)
             (proj₁ (emb (g n) (proj₂ o n) u (y , e))) (flK (nd sL g) ν o B B′ hB j (inc n v) β β′ hβ d))
    (λ u → inflK (g m) (ν m) (proj₂ o m) (cbK sL g o B′ m x) j (v ∙ u) (ψ (nd sL g) o B′ j (inc n v) β′ x) y
             (flK (nd sL g) ν o B B′ hB j (inc n v) β β′ hβ d))
-- 两边都是同一个孩子的嵌入
flK (nd s h) ν o B B′ hB _ self β β′ hβ (u≼u {x = x} {x′ = x′} {c = c} dx dy) =
  Up≼ (h c) (down stop c) (ψ (nd s h) o B _ self β x) (ψ (nd s h) o B′ _ self β′ x′) (flK (nd s h) ν o B B′ hB _ self β β′ hβ dx) dy
flK (nd sS h) ν o B B′ hB j (inu ws) β β′ hβ (u≼u {x = x} {x′ = x′} {c = c} dx dy) =
  flK (h c) ν (proj₂ o c) (cbK sS h o B c x) (cbK sS h o B′ c x′)
     (λ i u _ → flK (nd sS h) ν o B B′ hB i (inc c u) (B i (inc c u)) (B′ i (inc c u)) (hB i (inc c u) tt) dx)
     j (ws c) (ψ (nd sS h) o B j (inu ws) β x) (ψ (nd sS h) o B′ j (inu ws) β′ x′)
     (flK (nd sS h) ν o B B′ hB j (inu ws) β β′ hβ dx) dy
flK (nd sL g) ν o B B′ hB j (inu ws) β β′ hβ (u≼u {x = x} {x′ = x′} {c = c} dx dy) =
  flK (g c) (ν c) (proj₂ o c) (cbK sL g o B c x) (cbK sL g o B′ c x′)
     (λ i u _ → flK (nd sL g) ν o B B′ hB i (inc c u) (B i (inc c u)) (B′ i (inc c u)) (hB i (inc c u) tt) dx)
     j (ws c) (ψ (nd sL g) o B j (inu ws) β x) (ψ (nd sL g) o B′ j (inu ws) β′ x′)
     (flK (nd sL g) ν o B B′ hB j (inu ws) β β′ hβ dx) dy
flK (nd sS h) ν o B B′ hB j (inc c′ v) β β′ hβ (u≼u {x = x} {x′ = x′} {c = c} dx dy) =
  flK (h c) ν (proj₂ o c) (cbK sS h o B c x) (cbK sS h o B′ c x′)
     (λ i u _ → flK (nd sS h) ν o B B′ hB i (inc c u) (B i (inc c u)) (B′ i (inc c u)) (hB i (inc c u) tt) dx)
     j v (ψ (nd sS h) o B j (inc c′ v) β x) (ψ (nd sS h) o B′ j (inc c′ v) β′ x′)
     (flK (nd sS h) ν o B B′ hB j (inc c′ v) β β′ hβ dx) dy
flK (nd sL g) ν o B B′ hB j (inc n v) β β′ hβ (u≼u {x = x} {x′ = x′} {c = m} {y = y} {y′ = y′} {e = e} {e′ = e′} dx dy) =
  cW-ind₂ (λ Z Z′ → Le j (proj₁ Z) (proj₁ Z′)) (way g (proj₁ o) m n)
    (λ u → flK (g n) (ν n) (proj₂ o n) (cbK sL g o B n x) (cbK sL g o B′ n x′)
             (λ i u′ _ → flK (nd sL g) ν o B B′ hB i (inc n u′) (B i (inc n u′)) (B′ i (inc n u′)) (hB i (inc n u′) tt) dx)
             j v (ψ (nd sL g) o B j (inc n v) β x) (ψ (nd sL g) o B′ j (inc n v) β′ x′)
             (flK (nd sL g) ν o B B′ hB j (inc n v) β β′ hβ dx)
             (embK≼ (g n) (ν n) (proj₂ o n) u {y = y , e} {y′ = y′ , e′} dy))
    (λ u → flK (g m) (ν m) (proj₂ o m) (cbK sL g o B m x) (cbK sL g o B′ m x′)
             (λ i u′ _ → flK (nd sL g) ν o B B′ hB i (inc m u′) (B i (inc m u′)) (B′ i (inc m u′)) (hB i (inc m u′) tt) dx)
             j (v ∙ u) (ψ (nd sL g) o B j (inc n v) β x) (ψ (nd sL g) o B′ j (inc n v) β′ x′)
             (flK (nd sL g) ν o B B′ hB j (inc n v) β β′ hβ dx) dy)
flK (nd (sΩ k) h) () o B B′ hB j w β β′ hβ (≼u d)
flK (nd (sΩ k) h) () o B B′ hB j w β β′ hβ (u≼u dx dy)
```
