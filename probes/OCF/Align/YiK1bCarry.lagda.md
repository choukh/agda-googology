# K1′：有限次 Ω 读回的 Carry 保持

Regs 的全原分支证明已在 Base 独立给出。本篇仅把 Carry 的 LglB
递归补上；Raw 的 Nested 在 lc 行保存全部原分支的证书，因此读回的
lc 第一支与实际带证书分支均可递归，不需要收窄 Reg。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiK1bCarry where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Unit.Base using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
import OCF.Align.LevelFixCore as F
open F using (module G)
import OCF.Align.LevelFixVal as V
open import OCF.Align.YiRegBase using (Reg)
open import OCF.Align.YiDispBase using (Below)
import OCF.Align.YiK1 as K
import OCF.Align.YiCarry as Y
open Y using (Carry; LglB)
open import OCF.Align.YiK1bBase

Carrys : ℕ → F.LF → Set
Carrys zero y = Carry y
Carrys (suc n) y = Carrys n y × Carry (pow (suc n) y)

carrys-base : ∀ n y → Carrys n y → Carry y
carrys-base zero y r = r
carrys-base (suc n) y r = carrys-base n y (proj₁ r)

carrys-last : ∀ n y → Carrys n y → Carry (pow n y)
carrys-last zero y r = r
carrys-last (suc n) y r = proj₂ r

carrys-omega : ∀ n y → Carrys (suc n) y → Carry (V.Ω̂ y)
carrys-omega zero y r = proj₂ r
carrys-omega (suc n) y r = carrys-omega n y (proj₁ r)

carrys-regs : ∀ n y → Carrys n y → Regs n y
carrys-regs zero y r = Y.forget r
carrys-regs (suc n) y r = carrys-regs n y (proj₁ r) , Y.forget (proj₂ r)

mutual
  read-carrys : ∀ n y → Below (F.suc y) (V.Ω̂ y) → Carrys (suc n) y →
    ∀ η → F.Gd y (V.cO y) η → LglB y η → Carrys n (V.up y η)
  read-carrys zero y p r = Y.guard-read-carry y
    (Y.forget (carrys-base 1 y r)) (root p) (carrys-omega zero y r)
  read-carrys (suc n) F.zero p r η e b = ⊥-elim (no-one-one p)
  read-carrys (suc n) (F.suc y) p r η e b =
    carry-step n (F.suc y) refl p r η e b
  read-carrys (suc n) (F.lim f) p r η e b =
    carry-step n (F.lim f) refl p r η e b
  read-carrys (suc n) (F.lc k c t g) p r η e b =
    carry-step n (F.lc k c t g) refl p r η e b

  carry-step : ∀ n y → V.cO y ≡ G.top →
    Below (F.suc y) (V.Ω̂ y) → Carrys (suc (suc n)) y →
    ∀ η → F.Gd y (V.cO y) η → LglB y η → Carrys (suc n) (V.up y η)
  carry-step n y eq p r η e b =
    read-carrys n y p (proj₁ r) η e b ,
    go η b (subst (λ z → F.Cp y z η) eq (proj₁ e))
    where
    as-guard : ∀ η → F.Cp y G.top η → F.Lgl y η → F.Gd y (V.cO y) η
    as-guard η q l = subst (λ z → F.Cp y z η) (sym eq) q , l

    reg : ∀ η → F.Gd y (V.cO y) η → Reg (pow (suc n) (V.up y η))
    reg η e = regs-last (suc n) (V.up y η)
      (read-regs (suc n) y p (carrys-regs (suc (suc n)) y r) η e)

    go : ∀ η → LglB y η → F.Cp y G.top η → Carry (pow (suc n) (V.up y η))
    go G.zero b (inj₁ ())
    go G.zero b (inj₂ ())
    go (G.suc a) b (inj₁ ())
    go (G.suc a) b (inj₂ q) =
      pow-node-carry n (V.up y a) (V.cO (V.up y a)) (V.Ω̂ (V.up y a))
        (λ ζ d → V.up (V.up y a) ζ)
        (reg (G.suc a) (as-guard (G.suc a) (inj₂ q) (proj₁ b)))
        (V.Lgl-cO (V.up y a)) (go a b q)
        (λ ζ d bz → carrys-last n (V.up (V.up y a) ζ)
          (read-carrys n (V.up y a) pa ra ζ d bz))
      where
      ea : F.Gd y (V.cO y) a
      ea = as-guard a q (proj₁ b)
      pa : Below (F.suc (V.up y a)) (V.Ω̂ (V.up y a))
      pa = read-root y p a ea
      ra : Carrys (suc n) (V.up y a)
      ra = read-carrys n y p (proj₁ r) a ea b , go a b q
    go (G.lim f) ((st , lf) , bf) (inj₁ ())
    go (G.lim f) ((st , lf) , bf) (inj₂ (m , q)) =
      pow-lim-carry (suc n) (λ j → V.up y (f j)) term
      where
      term : ∀ j → Carry (pow (suc n) (V.up y (f j)))
      term j with F.cmpC y (f (j + m))
        (subst (λ z → F.Cp y (f j) (f z)) (+-comm m j) (K.up-to y f st m j))
        (F.Cp-tr y q (K.up-to y f st j m)) (lf (j + m))
      ... | inj₁ below-top = Y.cp-carry (pow-cp (suc n) (V.cp→CP y below-top)) (proj₂ r)
      ... | inj₂ above-top = go (f j) (lf j , bf j) above-top
    go (G.lc r₀ c t g) b (inj₁ ())
    go (G.lc r₀ c t g) b@((tg , mono , irr , lt , lg) , lc , bc , bt , bg) (inj₂ q) =
      pow-upN-carry (suc n) y r₀ c (V.up y t) (λ η e → V.up y (g η e))
        lc (reg (G.lc r₀ c t g) (as-guard (G.lc r₀ c t g) (inj₂ q) (proj₁ b)))
        (go t (lt , bt) q)
        (λ η e → go (g η e) (lg η e , bg η e) (F.Cp-tr y q (tg η e)))
    go (G.em i a) b (inj₁ ())
    go (G.em i a) b (inj₂ ())
    go G.top b q = proj₂ r
```
