# 层号等式的搬运：有限后继塔与一级比较
不读记号；编译定理：有限后继塔（`Tow`）上层号等式的证明唯一（`uipR`，局部 Hedberg，无公设）；`step`：源层与目标层只经等式连到 `YiPTLadder` 的标准形时，嵌入 Ω 树的折叠按 `N` 有序（对两条等式做 J 后用 `E`）；`stepTop`：顶层同理用 `climbₒ`。
ℕ 极限层号上 `way` 与 `emb` 的标准形（`way-eq`、`tree`）：相邻路径按等式是 `inc tt self` 时，嵌入沿等式等于 `ups`。函数外延不用。
不否定什么；用在 [YiPTChain](YiPTChain.lagda.md)。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPTTow where
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ₙ_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; trans)
open import Relation.Binary.PropositionalEquality.Properties using (trans-symˡ; subst-subst)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiVRRel using (NoΩ; NoΩ≤)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiLXClimb using (_⊴◃_)
open import OCF.Lean.YiTYPath using (pull-ok)
open import OCF.Lean.YiRRRel
open import OCF.Lean.YiRRFold using (geβ)
open import OCF.Lean.YiRRClimb using (climbₒ)
open import OCF.Lean.YiPTLadder using (S1; S2; v2; Tw; ups; ups′; fitW; E)
```

## 有限后继塔上等式证明唯一

```agda
data Tow : L → Set where
  tz : Tow zero
  ts : ∀ {X} → Tow X → Tow (S1 X)

child : L → L
child (nd sS h) = h tt
child _ = zero

decTow : ∀ {x} → Tow x → (y : L) → Dec (x ≡ y)
decTow tz zero = yes refl
decTow tz (nd s h) = no (λ ())
decTow (ts t) zero = no (λ ())
decTow (ts t) (nd sS h) with decTow t (h tt)
... | yes e = yes (cong (λ Z → nd sS (λ _ → Z)) e)
... | no ne = no (λ e → ne (cong child e))
decTow (ts t) (nd sL g) = no (λ ())
decTow (ts t) (nd (sΩ k) h) = no (λ ())

module Hed {x : L} (d : (y : L) → Dec (x ≡ y)) where
  nf : ∀ {y} → x ≡ y → x ≡ y
  nf {y} p with d y
  ... | yes q = q
  ... | no ¬q = ⊥-elim (¬q p)
  nfc : ∀ {y} (p q : x ≡ y) → nf p ≡ nf q
  nfc {y} p q with d y
  ... | yes _ = refl
  ... | no ¬r = ⊥-elim (¬r p)
  can : ∀ {y} (p : x ≡ y) → trans (sym (nf refl)) (nf p) ≡ p
  can refl = trans-symˡ (nf refl)
  uip : ∀ {y} (p q : x ≡ y) → p ≡ q
  uip p q = trans (sym (can p)) (trans (cong (trans (sym (nf refl))) (nfc p q)) (can q))

ss : ∀ {A : Set} {x y : A} (p : x ≡ y) → sym (sym p) ≡ p
ss refl = refl

uipR : ∀ {x y} → Tow y → (p q : x ≡ y) → p ≡ q
uipR t p q = trans (sym (ss p)) (trans (cong sym (Hed.uip (decTow t) (sym p) (sym q))) (ss q))

towNoΩ : ∀ {X} → Tow X → NoΩ X
towNoΩ tz = tt
towNoΩ (ts t) = towNoΩ t

towTw : ∀ {X} → Tow X → (D : ℕ) → Tow (Tw X D)
towTw t zero = t
towTw t (suc D) = ts (towTw t D)

OkT : ∀ {X} → Tow X → (o o′ : Ok X) → o ≡ o′
OkT tz o o′ = refl
OkT (ts t) (a , f) (a′ , f′) = cong (λ z → tt , λ _ → z) (OkT t (f tt) (f′ tt))
```

## 一级比较

层号只经等式 `es`、`e1` 连到标准形；对两条等式做 J, 余下是 `E`; 源的 `Ok` 由塔上 `Ok` 唯一 (`OkT`) 换成拉回.

```agda
step : (A : L) (tA : Tow A) (D : ℕ) {ℓs ℓt : L} (es : ℓs ≡ Tw A D) (e1 : ℓt ≡ S2 ℓs)
  (os : Ok ℓs) (ot : Ok ℓt) (rs : Rb ℓs) (rt : Rb ℓt) (Bs : Base ℓs) (Bt : Base ℓt) (Xs : Tr⁺ ℓs) (Xt : Tr⁺ ℓt)
  → subst Tr⁺ es Xs ≡ ups A D → subst Tr⁺ (trans e1 (cong S2 es)) Xt ≡ ups′ A D
  → ((i : L) (u : i ≤ ℓs) → N i (proj₁ (Bs i u)) (proj₁ (Bt i (subst (i ≤_) (sym e1) (inc tt (inc tt u))))))
  → ((i : L) (w : i ≤ ℓt) → proj₁ (Ωt i) ⊴◃ proj₁ (Bt i w))
  → (i : L) (u : i ≤ ℓs) (βs βt : Tr⁺ i) → N i (proj₁ βs) (proj₁ βt)
  → N i (proj₁ (ψ ℓs os rs Bs i u βs (proj₁ Xs))) (proj₁ (ψ ℓt ot rt Bt i (subst (i ≤_) (sym e1) (inc tt (inc tt u))) βt (proj₁ Xt)))
step A tA D refl refl os ot rs rt Bs Bt Xs Xt refl refl hb db i u βs βt hβ =
  subst (λ o → N i (proj₁ (ψ (Tw A D) o rs Bs i u βs (proj₁ (ups A D)))) (proj₁ (ψ (S2 (Tw A D)) ot rt Bt i (inc tt (inc tt u)) βt (proj₁ (ups′ A D)))))
    (OkT (towTw tA D) (pull-ok v2 ot) os)
    (E A (towNoΩ tA) D ot rs rt Bs Bt (λ j w _ → hb j w) (λ j w _ → db j w) i u false false βs βt hβ)

stepTop : {ℓs ℓt : L} (tS : Tow ℓs) (e1 : ℓt ≡ S2 ℓs)
  (os : Ok ℓs) (ot : Ok ℓt) (rs : Rb ℓs) (rt : Rb ℓt) (Bs : Base ℓs) (Bt : Base ℓt)
  → ((i : L) (u : i ≤ ℓs) → N i (proj₁ (Bs i u)) (proj₁ (Bt i (subst (i ≤_) (sym e1) (inc tt (inc tt u))))))
  → ((i : L) (w : i ≤ ℓt) → proj₁ (Ωt i) ⊴◃ proj₁ (Bt i w))
  → (ws : zero ≤ ℓs) (wt : zero ≤ ℓt) → subst (zero ≤_) e1 wt ≡ inu (λ _ → inu (λ _ → ws))
  → (βs βt : Tr⁺ zero) → N zero (proj₁ βs) (proj₁ βt)
  → N zero (proj₁ (ψ ℓs os rs Bs zero ws βs (proj₁ (Ωt ℓs)))) (proj₁ (ψ ℓt ot rt Bt zero wt βt (proj₁ (Ωt ℓt))))
stepTop {ℓs} tS refl os ot rs rt Bs Bt hb db ws .(inu (λ _ → inu (λ _ → ws))) refl βs βt hβ =
  climbₒ v2 (fitW true true ws) (towNoΩ tS) ot os (OkT tS os (pull-ok v2 ot)) rs rt Bs Bt (λ j w _ → hb j w) (λ j w _ → db j w) βs βt hβ
```

## way 与 emb 的标准形

```agda
cWl : ∀ {A B X : Set} {W : A ⊎ B} {a : A} {F : A → X} {G : B → X} → W ≡ inj₁ a → cW W F G ≡ F a
cWl refl = refl

Pw : (g : ℕ → L) (r : (n : ℕ) → g n ≤ g (suc n)) (m d : ℕ) → g m ≤ g (suc (m +ₙ d))
Pw g r zero d = from0 g r (suc d)
Pw g r (suc m) d = Pw (λ i → g (suc i)) (λ i → r (suc i)) m d

way-eq : (g : ℕ → L) (r : (n : ℕ) → g n ≤ g (suc n)) (m d : ℕ) → way g r m (suc (m +ₙ d)) ≡ inj₁ (Pw g r m d)
way-eq g r zero d = refl
way-eq g r (suc m) d = way-eq (λ i → g (suc i)) (λ i → r (suc i)) m d

Adj : (g : ℕ → L) (r : (n : ℕ) → g n ≤ g (suc n)) → Set
Adj g r = (i : ℕ) → _≡_ {A = Σ L (g i ≤_)} (g (suc i) , r i) (S1 (g i) , inc tt self)

upzTr : ∀ {X Y} (e : X ≡ Y) (y : Tr⁺ X) → subst Tr⁺ (cong S1 e) (upz {sS} {λ _ → X} tt y) ≡ upz {sS} {λ _ → Y} tt (subst Tr⁺ e y)
upzTr refl y = refl

embStep : ∀ {Y X b : L} (v : X ≤ b) (q : _≡_ {A = Σ L (X ≤_)} (b , v) (S1 X , inc tt self)) (o : Ok b) (w : Y ≤ X) (y : Tr⁺ Y)
  → subst Tr⁺ (cong proj₁ q) (emb b o (w ∙ v) y) ≡ upz {sS} {λ _ → X} tt (emb X (proj₂ (subst Ok (cong proj₁ q) o) tt) w y)
embStep v refl o w y = refl

twr0 : (g : ℕ → L) (r : (n : ℕ) → g n ≤ g (suc n)) → Adj g r → (d : ℕ) → g (suc d) ≡ Tw (g 0) (suc d)
twr0 g r H zero = cong proj₁ (H 0)
twr0 g r H (suc d) = trans (cong proj₁ (H (suc d))) (cong S1 (twr0 g r H d))

tree0 : (g : ℕ → L) (r : (n : ℕ) → g n ≤ g (suc n)) (H : Adj g r) (d : ℕ) (o : Ok (g (suc d)))
  → subst Tr⁺ (twr0 g r H d) (emb (g (suc d)) o (from0 g r (suc d)) (Ωt (g 0))) ≡ ups (g 0) (suc d)
tree0 g r H zero o = embStep (r 0) (H 0) o self (Ωt (g 0))
tree0 g r H (suc d) o =
  trans (sym (subst-subst {P = Tr⁺} (cong proj₁ (H (suc d)))))
    (trans (cong (subst Tr⁺ (cong S1 (twr0 g r H d))) (embStep (r (suc d)) (H (suc d)) o (from0 g r (suc d)) (Ωt (g 0))))
      (trans (upzTr (twr0 g r H d) _) (cong (upz tt) (tree0 g r H d _))))

twr : (g : ℕ → L) (r : (n : ℕ) → g n ≤ g (suc n)) → Adj g r → (m d : ℕ) → g (suc (m +ₙ d)) ≡ Tw (g m) (suc d)
twr g r H zero d = twr0 g r H d
twr g r H (suc m) d = twr (λ i → g (suc i)) (λ i → r (suc i)) (λ i → H (suc i)) m d

tree : (g : ℕ → L) (r : (n : ℕ) → g n ≤ g (suc n)) (H : Adj g r) (m d : ℕ) (o : Ok (g (suc (m +ₙ d))))
  → subst Tr⁺ (twr g r H m d) (emb (g (suc (m +ₙ d))) o (Pw g r m d) (Ωt (g m))) ≡ ups (g m) (suc d)
tree g r H zero d o = tree0 g r H d o
tree g r H (suc m) d o = tree (λ i → g (suc i)) (λ i → r (suc i)) (λ i → H (suc i)) m d o

swap : (A : L) (D : ℕ) → Tw (S2 A) D ≡ S2 (Tw A D)
swap A zero = refl
swap A (suc D) = cong S1 (swap A D)

ups-swap : (A : L) (D : ℕ) → subst Tr⁺ (swap A D) (ups (S2 A) D) ≡ ups′ A D
ups-swap A zero = refl
ups-swap A (suc D) = trans (upzTr (swap A D) (ups (S2 A) D)) (cong (upz tt) (ups-swap A D))

ups-cong : ∀ {X Y} (e : X ≡ Y) (D : ℕ) → subst Tr⁺ (cong (λ Z → Tw Z D) e) (ups X D) ≡ ups Y D
ups-cong refl D = refl
```
