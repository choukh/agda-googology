# YiPE 阶梯：累加的目标上，各块嵌入不必一致

**验收文件，档位：编译定理。** `glue`：`a` 嵌进 `T`、`a′` 嵌进 `Y`，且 `a ≅ᴵ a′` 或 `a ≺ᴵ a′` (带证据) 时，`a′` 嵌进 `T ⊕ Y`，并在 `a` 的前驱上延拓原嵌入 (`glue-ext`)；分界只用 `a′` 前驱上的有界三歧。
`Stair.stair`：源是 `lim f`，每一步 `f n ≅ᴵ f (n+1)` 或 `f n ≺ᴵ f (n+1)`，目标逐块累加 `t n ⊕ Y (n+1) ≅ᴵ t (n+1)`，各块任给嵌入 `f n → Y n`，则 `lim f` 嵌进目标。不要求各块嵌入在公共前驱上一致 (对照 `PEmb-limˡ` 的前提)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPEStair where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import OCF.Align.Level as L
open L using (Ordᴵ; _≅ᴵ_; _⊑ᴵ_; _≺ᴵ_; via)
open import OCF.Align.BTBOFullLe using (⊑≅)
open import OCF.Align.BTBOFullEmb using (PEmb)
open PEmb
open import OCF.Align.YiMonoEmb using (PEmb-⊑; PEmb-∘; PEmb-limˡ)
open import OCF.Lean.YiPEStep using (_⊕_; ⊕-≺; ⊕-≅; ⊑⊕; PEmb-≅ʳ; PEmb-≅ˡ)
```

## 1 小引理

```agda
≺⊑ : ∀ {c b a} → c ≺ᴵ b → b ⊑ᴵ a → c ≺ᴵ a
≺⊑ (via e p) k = L.≺ᴵ-respˡ e (L.sim k p)

tri : ∀ {a c b} → c ≺ᴵ b → a ≺ᴵ b → (c ≺ᴵ a) ⊎ ((a ≺ᴵ c) ⊎ (c ≅ᴵ a))
tri (via e p) (via e′ q) with L.<ᴵ-dec p q
... | inj₁ r = inj₁ (L.≺ᴵ-respʳ (L.≺ᴵ-respˡ e r) (L.≅ᴵ-sym e′))
... | inj₂ (inj₁ r) = inj₂ (inj₁ (L.≺ᴵ-respʳ (L.≺ᴵ-respˡ e′ r) (L.≅ᴵ-sym e)))
... | inj₂ (inj₂ r) = inj₂ (inj₂ (L.≅ᴵ-trans e (L.≅ᴵ-trans r (L.≅ᴵ-sym e′))))

irr : ∀ {a} → a ≺ᴵ a → ∀ {X : Set} → X
irr r = ⊥-elim (L.≺ᴵ-irrefl r)

-- a ≼ c (≻ 或 ≅) 与 c ≺ a 矛盾
ge-lt : ∀ {a c} → (a ≺ᴵ c) ⊎ (c ≅ᴵ a) → c ≺ᴵ a → ∀ {X : Set} → X
ge-lt (inj₁ ac) ca = irr (L.≺ᴵ-trans ac ca)
ge-lt (inj₂ e) ca = irr (L.≺ᴵ-respˡ (L.≅ᴵ-sym e) ca)
```

## 2 一块的粘接

分界：`a′` 的前驱 `c` 若在 `a` 之下，用旧嵌入 `Q` (像在 `T` 之下)；否则 (`a ≼ c`) 映到 `T ⊕ P c`。

```agda
module Gl {a a′ T Y : Ordᴵ} (Q : PEmb a T) (P : PEmb a′ Y) (w : a ≺ᴵ a′) where
  Side : Ordᴵ → Set
  Side c = (c ≺ᴵ a) ⊎ ((a ≺ᴵ c) ⊎ (c ≅ᴵ a))

  mp : ∀ {c} → c ≺ᴵ a′ → Side c → Ordᴵ
  mp r (inj₁ q) = map Q q
  mp r (inj₂ _) = T ⊕ map P r

  bndH : ∀ {c} (r : c ≺ᴵ a′) x → mp r x ≺ᴵ (T ⊕ Y)
  bndH r (inj₁ q) = ≺⊑ (bnd Q q) (⊑⊕ T Y)
  bndH r (inj₂ _) = ⊕-≺ T (bnd P r)

  monoH : ∀ {c d} (r : c ≺ᴵ a′) (s : d ≺ᴵ a′) → c ≺ᴵ d → ∀ x y → mp r x ≺ᴵ mp s y
  monoH r s lt (inj₁ q) (inj₁ q′) = mono Q q q′ lt
  monoH r s lt (inj₁ q) (inj₂ _) = ≺⊑ (bnd Q q) (⊑⊕ T (map P s))
  monoH r s lt (inj₂ u) (inj₁ q′) = ge-lt u (L.≺ᴵ-trans lt q′)
  monoH r s lt (inj₂ _) (inj₂ _) = ⊕-≺ T (mono P r s lt)

  cohH : ∀ {c d} (r : c ≺ᴵ a′) (s : d ≺ᴵ a′) → c ≅ᴵ d → ∀ x y → mp r x ≅ᴵ mp s y
  cohH r s e (inj₁ q) (inj₁ q′) = coh Q q q′ e
  cohH r s e (inj₁ q) (inj₂ u) = ge-lt u (L.≺ᴵ-respˡ (L.≅ᴵ-sym e) q)
  cohH r s e (inj₂ u) (inj₁ q′) = ge-lt u (L.≺ᴵ-respˡ e q′)
  cohH r s e (inj₂ _) (inj₂ _) = ⊕-≅ T (coh P r s e)

  emb : PEmb a′ (T ⊕ Y)
  map emb r = mp r (tri r w)
  bnd emb r = bndH r (tri r w)
  mono emb r s lt = monoH r s lt (tri r w) (tri s w)
  coh emb r s e = cohH r s e (tri r w) (tri s w)

  extH : ∀ {c} (r′ : c ≺ᴵ a′) x (r : c ≺ᴵ a) → mp r′ x ≅ᴵ map Q r
  extH r′ (inj₁ q) r = coh Q q r (L.≅ᴵ-refl _)
  extH r′ (inj₂ u) r = ge-lt u r

glue : ∀ {a a′ T Y T′} → PEmb a T → PEmb a′ Y → (a ≅ᴵ a′) ⊎ (a ≺ᴵ a′) → (T ⊕ Y) ≅ᴵ T′ → PEmb a′ T′
glue {T = T} {Y} Q P (inj₁ e) eT = PEmb-∘ (PEmb-≅ˡ (L.≅ᴵ-sym e) Q) (PEmb-⊑ (⊑≅ (⊑⊕ T Y) eT))
glue Q P (inj₂ w) eT = PEmb-≅ʳ (Gl.emb Q P w) eT

glue-ext : ∀ {a a′ T Y T′} (Q : PEmb a T) (P : PEmb a′ Y) (d : (a ≅ᴵ a′) ⊎ (a ≺ᴵ a′)) (eT : (T ⊕ Y) ≅ᴵ T′)
  {c} (r : c ≺ᴵ a) (r′ : c ≺ᴵ a′) → map (glue Q P d eT) r′ ≅ᴵ map Q r
glue-ext Q P (inj₁ e) eT r r′ = coh Q (L.≺ᴵ-respʳ r′ (L.≅ᴵ-sym e)) r (L.≅ᴵ-refl _)
glue-ext Q P (inj₂ w) eT r r′ = Gl.extH Q P w r′ (tri r′ w) r
```

## 3 阶梯

`Q n : f n → t n` 逐块粘出，后一块延拓前一块 (`ext`)；于是任意两块在公共前驱上一致 (`cohQ`)，`PEmb-limˡ` 的前提由构造给出。

```agda
_⊞_ : ℕ → ℕ → ℕ
n ⊞ zero = n
n ⊞ suc k = suc (n ⊞ k)

z⊞ : ∀ n → zero ⊞ n ≡ n
z⊞ zero = refl
z⊞ (suc n) = cong suc (z⊞ n)

s⊞ : ∀ m k → suc m ⊞ k ≡ suc (m ⊞ k)
s⊞ m zero = refl
s⊞ m (suc k) = cong suc (s⊞ m k)

cmpℕ : ∀ n m → (Σ ℕ λ k → m ≡ n ⊞ k) ⊎ (Σ ℕ λ k → n ≡ m ⊞ k)
cmpℕ n zero = inj₂ (n , sym (z⊞ n))
cmpℕ n (suc m) with cmpℕ n m
... | inj₁ (k , e) = inj₁ (suc k , cong suc e)
... | inj₂ (zero , e) = inj₁ (1 , cong suc (sym e))
... | inj₂ (suc k , e) = inj₂ (k , trans e (sym (s⊞ m k)))

module Stair (f : ℕ → Ordᴵ) (s : ∀ n → f n ⊑ᴵ f (suc n))
  (dec : ∀ n → (f n ≅ᴵ f (suc n)) ⊎ (f n ≺ᴵ f (suc n)))
  (t Y : ℕ → Ordᴵ) (P : ∀ n → PEmb (f n) (Y n))
  (t0 : Y 0 ≅ᴵ t 0) (tY : ∀ n → (t n ⊕ Y (suc n)) ≅ᴵ t (suc n))
  {B : Ordᴵ} (tB : ∀ n → t n ⊑ᴵ B) where

  Q : ∀ n → PEmb (f n) (t n)
  Q zero = PEmb-≅ʳ (P 0) t0
  Q (suc n) = glue (Q n) (P (suc n)) (dec n) (tY n)

  ext : ∀ {c} n (r : c ≺ᴵ f n) (r′ : c ≺ᴵ f (suc n)) → map (Q (suc n)) r′ ≅ᴵ map (Q n) r
  ext n r r′ = glue-ext (Q n) (P (suc n)) (dec n) (tY n) r r′

  ups : ∀ {c} n k → c ≺ᴵ f n → c ≺ᴵ f (n ⊞ k)
  ups n zero r = r
  ups n (suc k) r = ≺⊑ (ups n k r) (s (n ⊞ k))

  far : ∀ {c} n k (r : c ≺ᴵ f n) (u : c ≺ᴵ f (n ⊞ k)) → map (Q (n ⊞ k)) u ≅ᴵ map (Q n) r
  far n zero r u = coh (Q n) u r (L.≅ᴵ-refl _)
  far n (suc k) r u = L.≅ᴵ-trans (ext (n ⊞ k) (ups n k r) u) (far n k r (ups n k r))

  tr≡ : ∀ {c n m} (e : n ≡ m) (u : c ≺ᴵ f n) → map (Q n) u ≅ᴵ map (Q m) (subst (λ i → c ≺ᴵ f i) e u)
  tr≡ {n = n} refl u = coh (Q n) u u (L.≅ᴵ-refl _)

  cohQ : ∀ n m {c} (r : c ≺ᴵ f n) (u : c ≺ᴵ f m) → map (Q n) r ≅ᴵ map (Q m) u
  cohQ n m {c} r u with cmpℕ n m
  ... | inj₁ (k , e) = L.≅ᴵ-sym (L.≅ᴵ-trans (tr≡ e u) (far n k r (subst (λ i → c ≺ᴵ f i) e u)))
  ... | inj₂ (k , e) = L.≅ᴵ-trans (tr≡ e r) (far m k u (subst (λ i → c ≺ᴵ f i) e r))

  stair : PEmb (L.lim f s) B
  stair = PEmb-limˡ (λ n → PEmb-∘ (Q n) (PEmb-⊑ (tB n))) cohQ
```
