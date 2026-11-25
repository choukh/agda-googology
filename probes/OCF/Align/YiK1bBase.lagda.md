# K1′：有限次 Ω 的结构引理

本篇只加外部证明，不改共用接口。`pow n x` 是原 Ω̂ 的有限次复合，
没有新增构造子或改变原 Ω̂。关键的树侧路径是 `Below (suc y) (Ω̂ y)`：
它沿原守卫读回传递。下游只对第 0 层正坐标实填此路径，
不从 Reg 或 Carry 凭空推出它。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiK1bBase where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst; cong; trans; sym)
open import OCF.Align.LevelFixCore using (LF; Raw; Gd; Cp; Lgl; Pre; Low; GdL)
import OCF.Align.LevelFixCore as F
open F using (module G)
import OCF.Align.LevelFixVal as V
open import OCF.Align.YiDispBase
  using (Below; one; more; e-suc; e-lim; e-first; e-branch; below-trans)
open import OCF.Align.YiRegBase using (Reg)
import OCF.Align.YiK1 as K
import OCF.Align.YiCarry as Y
open Y using (Carry; LglB; LglLow)
import OCF.Align.RR4RegOmega2 as R

pow : ℕ → LF → LF
pow zero x = x
pow (suc n) x = pow n (V.Ω̂ x)

pow-Ω : ∀ n x → pow n (V.Ω̂ x) ≡ V.Ω̂ (pow n x)
pow-Ω zero x = refl
pow-Ω (suc n) x = pow-Ω n (V.Ω̂ x)

pow-tw : ∀ n → pow n F.zero ≡ V.tw n
pow-tw zero = refl
pow-tw (suc n) = trans (pow-Ω n F.zero) (cong V.Ω̂ (pow-tw n))

Ω-below : ∀ {a b} → Below a b → Below (V.Ω̂ a) (V.Ω̂ b)
Ω-below (one e-suc) = one e-first
Ω-below (one (e-lim n)) = one (e-lim n)
Ω-below (one e-first) = one e-first
Ω-below (one (e-branch η e)) = one (e-branch η e)
Ω-below (more p e-suc) = more (Ω-below p) e-first
Ω-below (more p (e-lim n)) = more (Ω-below p) (e-lim n)
Ω-below (more p e-first) = more (Ω-below p) e-first
Ω-below (more p (e-branch η e)) = more (Ω-below p) (e-branch η e)

pow-below : ∀ n {a b} → Below a b → Below (pow n a) (pow n b)
pow-below zero p = p
pow-below (suc n) p = pow-below n (Ω-below p)

pow-cp : ∀ n {a b} → V.CP a b → V.CP (pow n a) (pow n b)
pow-cp zero p = p
pow-cp (suc n) p = pow-cp n (V.Ω̂-CP p)

root : ∀ {y} → Below (F.suc y) (V.Ω̂ y) → Below y (V.Ω̂ y)
root p = below-trans (one e-suc) p

root-pow : ∀ n y → Below (F.suc y) (V.Ω̂ y) →
  Below (F.suc y) (pow (suc n) y)
root-pow zero y p = p
root-pow (suc n) y p =
  below-trans (root-pow n y p) (pow-below (suc n) (root p))

read-root : ∀ y → Below (F.suc y) (V.Ω̂ y) →
  ∀ η → Gd y (V.cO y) η →
  Below (F.suc (V.up y η)) (V.Ω̂ (V.up y η))
read-root y p η e = R.below-cp
  (below-trans (one (e-branch (G.suc η) (inj₂ (proj₁ e) , proj₂ e)))
    (Ω-below p))
  (V.Ω̂-CP (V.cO-CP y (proj₁ e)))

_⊴_ : LF → LF → Set
a ⊴ b = (a ≡ b) ⊎ Below a b

cp-weak : ∀ {a b} → V.CP a b → a ⊴ b
cp-weak V.self = inj₁ refl
cp-weak (V.suc p) with cp-weak p
... | inj₁ refl = inj₂ (one e-suc)
... | inj₂ q = inj₂ (more q e-suc)
cp-weak (V.lim n p) with cp-weak p
... | inj₁ refl = inj₂ (one (e-lim n))
... | inj₂ q = inj₂ (more q (e-lim n))
cp-weak (V.fst p) with cp-weak p
... | inj₁ refl = inj₂ (one e-first)
... | inj₂ q = inj₂ (more q e-first)

node-reg : ∀ k c t g → F.suc k ⊴ t → Reg k → Reg t →
  (∀ η e → Reg (g η e)) → Reg (F.lc k c t g)
node-reg k c t g (inj₁ refl) rk rt rg = one e-first , rk , rt , rg
node-reg k c t g (inj₂ p) rk rt rg = more p e-first , rk , rt , rg

pow-node-reg : ∀ n k c t g → F.suc k ⊴ pow n t → Reg k →
  Reg (pow n t) → (∀ η e → Reg (pow n (g η e))) →
  Reg (pow n (F.lc k c t g))
pow-node-reg zero k c t g p rk rt rg = node-reg k c t g p rk rt rg
pow-node-reg (suc n) k c t g p rk rt rg =
  pow-node-reg n k c (V.Ω̂ t) (λ η e → V.Ω̂ (g η e)) p rk rt rg

pow-node-carry : ∀ n k c t g → Reg (pow n (F.lc k c t g)) →
  Lgl k c → Carry (pow n t) →
  (∀ η e → LglB k η → Carry (pow n (g η e))) →
  Carry (pow n (F.lc k c t g))
pow-node-carry zero k c t g reg lc ct cg = reg , lc , ct , cg
pow-node-carry (suc n) k c t g reg lc ct cg =
  pow-node-carry n k c (V.Ω̂ t) (λ η e → V.Ω̂ (g η e)) reg lc ct cg

pow-lim-reg : ∀ n (f : ℕ → LF) →
  (∀ j → Reg (pow n (f j))) → Reg (pow n (F.lim f))
pow-lim-reg zero f r = r
pow-lim-reg (suc n) f r = pow-lim-reg n (λ j → V.Ω̂ (f j)) r

pow-lim-carry : ∀ n (f : ℕ → LF) →
  (∀ j → Carry (pow n (f j))) → Carry (pow n (F.lim f))
pow-lim-carry zero f r = r
pow-lim-carry (suc n) f r = pow-lim-carry n (λ j → V.Ω̂ (f j)) r

pow-upN-reg : ∀ n y → Reg y → (r : Pre y) (c : Low y r)
  (t : LF) (g : (η : Low y r) → GdL y r c η → LF) →
  Below y (pow n t) → Reg (pow n t) →
  (∀ η e → Reg (pow n (g η e))) → Reg (pow n (V.upN y r c t g))
pow-upN-reg n F.zero ry ()
pow-upN-reg n (F.suc y) ry (inj₁ _) c t g p rt rg =
  pow-node-reg n y c t g (inj₂ p) ry rt rg
pow-upN-reg n (F.suc y) ry (inj₂ r) c t g p rt rg =
  pow-upN-reg n y ry r c t g (below-trans (one e-suc) p) rt rg
pow-upN-reg n (F.lim f) ry (m , r) c t g p rt rg =
  pow-upN-reg n (f m) (ry m) r c t g
    (below-trans (one (e-lim m)) p) rt rg
pow-upN-reg n (F.lc k c₀ t₀ g₀) (bound , rk , rt₀ , rg₀)
  (inj₁ (inj₁ _)) c t g p rt rg =
  pow-node-reg n k c t g (inj₂ (below-trans bound p)) rk rt rg
pow-upN-reg n (F.lc k c₀ t₀ g₀) (bound , rk , rt₀ , rg₀)
  (inj₁ (inj₂ r)) c t g p rt rg =
  pow-upN-reg n k rk r c t g
    (below-trans (below-trans (one e-suc) bound) p) rt rg
pow-upN-reg n (F.lc k c₀ t₀ g₀) (bound , rk , rt₀ , rg₀)
  (inj₂ (inj₁ r)) c t g p rt rg =
  pow-upN-reg n t₀ rt₀ r c t g (below-trans (one e-first) p) rt rg
pow-upN-reg n (F.lc k c₀ t₀ g₀) (bound , rk , rt₀ , rg₀)
  (inj₂ (inj₂ (η , e , r))) c t g p rt rg =
  pow-upN-reg n (g₀ η e) (rg₀ η e) r c t g
    (below-trans (one (e-branch η e)) p) rt rg

pow-upN-carry : ∀ n y (r : Pre y) (c : Low y r)
  (t : LF) (g : (η : Low y r) → GdL y r c η → LF) →
  LglLow y r c → Reg (pow n (V.upN y r c t g)) →
  Carry (pow n t) → (∀ η e → Carry (pow n (g η e))) →
  Carry (pow n (V.upN y r c t g))
pow-upN-carry n F.zero ()
pow-upN-carry n (F.suc y) (inj₁ _) c t g lc reg ct cg =
  pow-node-carry n y c t g reg lc ct (λ η e b → cg η e)
pow-upN-carry n (F.suc y) (inj₂ r) c t g lc reg ct cg =
  pow-upN-carry n y r c t g lc reg ct cg
pow-upN-carry n (F.lim f) (m , r) c t g lc reg ct cg =
  pow-upN-carry n (f m) r c t g lc reg ct cg
pow-upN-carry n (F.lc k c₀ t₀ g₀) (inj₁ (inj₁ _)) c t g lc reg ct cg =
  pow-node-carry n k c t g reg lc ct (λ η e b → cg η e)
pow-upN-carry n (F.lc k c₀ t₀ g₀) (inj₁ (inj₂ r)) c t g lc reg ct cg =
  pow-upN-carry n k r c t g lc reg ct cg
pow-upN-carry n (F.lc k c₀ t₀ g₀) (inj₂ (inj₁ r)) c t g lc reg ct cg =
  pow-upN-carry n t₀ r c t g lc reg ct cg
pow-upN-carry n (F.lc k c₀ t₀ g₀) (inj₂ (inj₂ (η , e , r))) c t g lc reg ct cg =
  pow-upN-carry n (g₀ η e) r c t g lc reg ct cg
```

以下对次数归纳，每个非零次数的内部再按 Raw 结构递归。
Reg 版本量化全部原守卫坐标；Carry 版本另用 LglB，不混淆两域。
`Regs n y` 保存从 0 到 n 次的原 Reg，并不假设全塔。

```agda
Regs : ℕ → LF → Set
Regs zero y = Reg y
Regs (suc n) y = Regs n y × Reg (pow (suc n) y)

regs-base : ∀ n y → Regs n y → Reg y
regs-base zero y r = r
regs-base (suc n) y r = regs-base n y (proj₁ r)

regs-last : ∀ n y → Regs n y → Reg (pow n y)
regs-last zero y r = r
regs-last (suc n) y r = proj₂ r

regs-omega : ∀ n y → Regs (suc n) y → Reg (V.Ω̂ y)
regs-omega zero y r = proj₂ r
regs-omega (suc n) y r = regs-omega n y (proj₁ r)

open import Data.Empty using (⊥; ⊥-elim)

no-below-zero : ∀ {a} → Below a F.zero → ⊥
no-below-zero (one ())
no-below-zero (more p ())

no-one-one : Below (F.suc F.zero) (F.suc F.zero) → ⊥
no-one-one (one ())
no-one-one (more p e-suc) = no-below-zero p

mutual
  read-regs : ∀ n y → Below (F.suc y) (V.Ω̂ y) → Regs (suc n) y →
    ∀ η → Gd y (V.cO y) η → Regs n (V.up y η)
  read-regs zero y p r =
    K.guard-read-reg y (regs-base 1 y r) (root p) (regs-omega zero y r)
  read-regs (suc n) F.zero p r η e = ⊥-elim (no-one-one p)
  read-regs (suc n) (F.suc y) p r η e = read-step n (F.suc y) refl p r η e
  read-regs (suc n) (F.lim f) p r η e = read-step n (F.lim f) refl p r η e
  read-regs (suc n) (F.lc k c t g) p r η e =
    read-step n (F.lc k c t g) refl p r η e

  read-step : ∀ n y → V.cO y ≡ G.top →
    Below (F.suc y) (V.Ω̂ y) → Regs (suc (suc n)) y →
    ∀ η → Gd y (V.cO y) η → Regs (suc n) (V.up y η)
  read-step n y eq p r η e =
    read-regs n y p (proj₁ r) η e , go η (proj₂ e) (subst (λ z → Cp y z η) eq (proj₁ e))
    where
    ry : Reg y
    ry = regs-base (suc (suc n)) y r
    ro : Reg (V.Ω̂ y)
    ro = regs-omega (suc n) y r

    go : ∀ η → Lgl y η → Cp y G.top η → Reg (pow (suc n) (V.up y η))
    go G.zero l (inj₁ ())
    go G.zero l (inj₂ ())
    go (G.suc a) l (inj₁ ())
    go (G.suc a) l (inj₂ q) =
      pow-node-reg n (V.up y a) (V.cO (V.up y a)) (V.Ω̂ (V.up y a))
        (λ ζ d → V.up (V.up y a) ζ)
        (inj₂ (root-pow n (V.up y a) pa))
        (regs-base (suc n) (V.up y a) ra) (go a l q)
        (λ ζ d → regs-last n (V.up (V.up y a) ζ)
          (read-regs n (V.up y a) pa ra ζ d))
      where
      ea : Gd y (V.cO y) a
      ea = subst (λ z → Cp y z a) (sym eq) q , l
      pa : Below (F.suc (V.up y a)) (V.Ω̂ (V.up y a))
      pa = read-root y p a ea
      ra : Regs (suc n) (V.up y a)
      ra = read-regs n y p (proj₁ r) a ea , go a l q
    go (G.lim f) (st , lf) (inj₁ ())
    go (G.lim f) (st , lf) (inj₂ (m , q)) =
      pow-lim-reg (suc n) (λ j → V.up y (f j)) term
      where
      term : ∀ j → Reg (pow (suc n) (V.up y (f j)))
      term j with F.cmpC y (f (j + m))
        (subst (λ z → Cp y (f j) (f z)) (+-comm m j) (K.up-to y f st m j))
        (F.Cp-tr y q (K.up-to y f st j m)) (lf (j + m))
      ... | inj₁ below-top = K.cp-reg (pow-cp (suc n) (V.cp→CP y below-top)) (proj₂ r)
      ... | inj₂ above-top = go (f j) (lf j) above-top
    go (G.lc r₀ c t g) (tg , mono , irr , lt , lg) (inj₁ ())
    go (G.lc r₀ c t g) (tg , mono , irr , lt , lg) (inj₂ q) =
      pow-upN-reg (suc n) y ry r₀ c (V.up y t) (λ η e → V.up y (g η e))
        (R.below-cp
          (below-trans (one e-suc) (root-pow (suc n) y p))
          (pow-cp (suc n) (V.cp→CP y q)))
        (go t lt q) (λ η e → go (g η e) (lg η e) (F.Cp-tr y q (tg η e)))
    go (G.em i a) l (inj₁ ())
    go (G.em i a) l (inj₂ ())
    go G.top l q = proj₂ r
```
