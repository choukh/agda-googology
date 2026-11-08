# Ω层闭包所需的低层坐标关系

Coded只观察实际回灌，不能反推upL所读取的种类结构。本接口尝试把
层、种类、低层坐标与树的关系共同定义；Ω分量只在显式相关坐标上
提供对应层，不假定任意函数保持Same。所有比较由该字面结构配对
见证限定，未引入裸层号判等或次序。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaEmbedOmegaIf where
open import Data.Nat using (ℕ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy

-- 树关系不要求所有raw树自相关；每个Ω保留明确种类见证。
data Trees {S T : KS} (KR : K S → K T → Set₁)
  (ER : ∀ {κ κ′} → KR κ κ′ → E S κ → E T κ′ → Set₁) : HB S → HB T → Set₁ where
  tz : Trees KR ER hz hz
  ts : ∀ {a b} → Trees KR ER a b → Trees KR ER (hs a) (hs b)
  tl : ∀ {f g} → (∀ n → Trees KR ER (f n) (g n)) → Trees KR ER (hl f) (hl g)
  to : ∀ {κ κ′ f g} (p : KR κ κ′) →
    (∀ {a b} → ER p a b → Trees KR ER (f a) (g b)) →
    Trees KR ER (hΩ κ f) (hΩ κ′ g)

mutual
  data Layer : LH → LH → Set₁ where
    lz′ : Layer lz lz
    ls′ : ∀ {x y} → Layer x y → Layer (ls x) (ls y)
    ll′ : ∀ {f g} → (∀ n → Layer (f n) (g n)) → Layer (ll f) (ll g)
    lo′ : ∀ {k j f g} (p : Layer k j) →
      (∀ {a b} → Tree p a b → Layer (f a) (g b)) → Layer (lΩ k f) (lΩ j g)

  Tree : ∀ {x y} → Layer x y → HB (Lv x) → HB (Lv y) → Set₁
  Tree p = Trees (Kind p) (Coord p)

  Kind : ∀ {x y} → Layer x y → K (Lv x) → K (Lv y) → Set₁
  Kind lz′ () κ′
  Kind (ls′ p) (inj₁ κ) (inj₁ κ′) = Kind p κ κ′
  Kind (ls′ p) (inj₁ κ) (inj₂ _) = ⊥
  Kind (ls′ p) (inj₂ _) (inj₁ κ′) = ⊥
  Kind (ls′ p) (inj₂ _) (inj₂ _) = ⊤
  Kind (ll′ p) (n , κ) (m , κ′) = Σ (n ≡ m) (λ { refl → Kind (p n) κ κ′ })
  Kind (lo′ p q) (inj₁ _ , κ) (inj₂ b , κ′) = ⊥
  Kind (lo′ p q) (inj₂ a , κ) (inj₁ _ , κ′) = ⊥
  Kind (lo′ p q) (inj₁ _ , inj₁ κ) (inj₁ _ , inj₁ κ′) = Kind p κ κ′
  Kind (lo′ p q) (inj₁ _ , inj₁ κ) (inj₁ _ , inj₂ _) = ⊥
  Kind (lo′ p q) (inj₁ _ , inj₂ _) (inj₁ _ , inj₁ κ′) = ⊥
  Kind (lo′ p q) (inj₁ _ , inj₂ _) (inj₁ _ , inj₂ _) = ⊤
  Kind (lo′ p q) (inj₂ a , κ) (inj₂ b , κ′) = Σ (Tree p a b) (λ r → Kind (q r) κ κ′)

  Coord : ∀ {x y} (p : Layer x y) {κ κ′} → Kind p κ κ′ → E (Lv x) κ → E (Lv y) κ′ → Set₁
  Coord lz′ {()} r a b
  Coord (ls′ p) {inj₁ κ} {inj₁ κ′} r a b = Coord p r a b
  Coord (ls′ p) {inj₁ κ} {inj₂ _} () a b
  Coord (ls′ p) {inj₂ _} {inj₁ κ′} () a b
  Coord (ls′ p) {inj₂ _} {inj₂ _} r a b = Tree p a b
  Coord (ll′ p) {(n , κ)} {(.n , κ′)} (refl , r) a b = Coord (p n) r a b
  Coord (lo′ p q) {(inj₁ _ , inj₁ κ)} {(inj₁ _ , inj₁ κ′)} r a b = Coord p r a b
  Coord (lo′ p q) {(inj₁ _ , inj₁ κ)} {(inj₁ _ , inj₂ _)} () a b
  Coord (lo′ p q) {(inj₁ _ , inj₂ _)} {(inj₁ _ , inj₁ κ′)} () a b
  Coord (lo′ p q) {(inj₁ _ , inj₂ _)} {(inj₁ _ , inj₂ _)} r a b = Tree p a b
  Coord (lo′ p q) {(inj₁ _ , κ)} {(inj₂ b′ , κ′)} () a b
  Coord (lo′ p q) {(inj₂ a′ , κ)} {(inj₁ _ , κ′)} () a b
  Coord (lo′ p q) {(inj₂ a′ , κ)} {(inj₂ b′ , κ′)} (r , s) a b = Coord (q r) s a b
```
