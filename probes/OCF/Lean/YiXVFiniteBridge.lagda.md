# YiXVFiniteBridge
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteBridge where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import Data.Fin as F
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteCoerce as C

Ω : ∀ k → I.T k
Ω k = L.Ω (L.natᴵ k)
ord-suc-inj : ∀ {a b : L.Ordᴵ} → L.suc a ≡ L.suc b → a ≡ b
ord-suc-inj refl = refl
nat-inj : ∀ a b → L.natᴵ a ≡ L.natᴵ b → a ≡ b
nat-inj zero zero p = refl
nat-inj zero (suc b) ()
nat-inj (suc a) zero ()
nat-inj (suc a) (suc b) p = cong suc (nat-inj a b (ord-suc-inj p))

idx : ∀ n {i} → i L.<ᴵ L.natᴵ (suc n) → F.Fin (suc n)
idx n q = I.FinSlot.index (I.cutF n q)
num : ∀ n {i} → i L.<ᴵ L.natᴵ (suc n) → ℕ
num n q = I.rank n (idx n q)
eq : ∀ n {i} (q : i L.<ᴵ L.natᴵ (suc n)) → i ≡ L.natᴵ (num n q)
eq n q = I.FinSlot.same (I.cutF n q)
rank-eq : ∀ n m {i} (p : i L.<ᴵ L.natᴵ (suc n)) (q : i L.<ᴵ L.natᴵ (suc m)) → num n p ≡ num m q
rank-eq n m p q = nat-inj _ _ (trans (sym (eq n p)) (eq m q))

cast-compose : ∀ {i a b} (p : i ≡ L.natᴵ a) (e : a ≡ b) (x : L.Ordᶜ i) →
  subst I.T e (subst L.Ordᶜ p x) ≡ subst L.Ordᶜ (trans p (cong L.natᴵ e)) x
cast-compose refl refl x = refl
cast-Ω : ∀ {a b} (e : a ≡ b) → subst I.T e (Ω a) ≡ Ω b
cast-Ω refl = refl

ref-coe : ∀ n m {i} (p : i L.<ᴵ L.natᴵ (suc n)) (q : i L.<ᴵ L.natᴵ (suc m)) (u : L.U i (L.<→◃ q)) →
  subst I.T (rank-eq n m p q) (I.Uref n p (L.coe (L.<→◃ q) (L.<→◃ p) u)) ≡ I.Uref m q u
ref-coe n m p q u = trans
  (cong (subst I.T e) (cong (subst L.Ordᶜ (eq n p)) (L.out-into (L.<→◃ p) (L.out (L.<→◃ q) u))))
  (trans (cast-compose (eq n p) e (L.out (L.<→◃ q) u))
    (cong (λ d → subst L.Ordᶜ d (L.out (L.<→◃ q) u))
      (I.AtFinite.unique (I.below (I.finite (suc n)) p) (trans (eq n p) (cong L.natᴵ e)) (eq m q))))
  where e = rank-eq n m p q

G-eq : ∀ {a b} (e : a ≡ b) (x : I.T a) (y : I.T b) → subst I.T e x ≡ y → A.Gd a x ≡ A.Gd b y
G-eq refl x .x refl = refl
R-eq : ∀ {a b} (e : a ≡ b) (x x′ : I.T a) (y y′ : I.T b) → subst I.T e x ≡ y → subst I.T e x′ ≡ y′ →
  A.Le a x x′ ≡ A.Le b y y′
R-eq refl x x′ .x .x′ refl refl = refl

GU-eq : ∀ n m {i} (p : i L.<ᴵ L.natᴵ (suc n)) (q : i L.<ᴵ L.natᴵ (suc m)) (u : L.U i (L.<→◃ q)) →
  A.GoFam n (idx n p) (I.Uref n p (L.coe (L.<→◃ q) (L.<→◃ p) u)) ≡ A.GoFam m (idx m q) (I.Uref m q u)
GU-eq n m p q u = trans (B.good-stable n (idx n p) _)
  (trans (G-eq (rank-eq n m p q) _ _ (ref-coe n m p q u)) (sym (B.good-stable m (idx m q) _)))
RU-eq : ∀ n m {i} (p : i L.<ᴵ L.natᴵ (suc n)) (q : i L.<ᴵ L.natᴵ (suc m)) (u v : L.U i (L.<→◃ q)) →
  A.LeFam n (idx n p) (I.Uref n p (L.coe (L.<→◃ q) (L.<→◃ p) u)) (I.Uref n p (L.coe (L.<→◃ q) (L.<→◃ p) v)) ≡
  A.LeFam m (idx m q) (I.Uref m q u) (I.Uref m q v)
RU-eq n m p q u v = trans (B.le-stable n (idx n p) _ _)
  (trans (R-eq (rank-eq n m p q) _ _ _ _ (ref-coe n m p q u) (ref-coe n m p q v)) (sym (B.le-stable m (idx m q) _ _)))
floor-eq : ∀ n m {i} (p : i L.<ᴵ L.natᴵ (suc n)) (q : i L.<ᴵ L.natᴵ (suc m)) (u : L.U i (L.<→◃ q)) →
  A.LeFam n (idx n p) (Ω (num n p)) (I.Uref n p (L.coe (L.<→◃ q) (L.<→◃ p) u)) ≡
  A.LeFam m (idx m q) (Ω (num m q)) (I.Uref m q u)
floor-eq n m p q u = trans (B.le-stable n (idx n p) _ _)
  (trans (R-eq (rank-eq n m p q) _ _ _ _ (cast-Ω (rank-eq n m p q)) (ref-coe n m p q u)) (sym (B.le-stable m (idx m q) _ _)))
```
