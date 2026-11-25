# YiNextVal 路径：第一位置证明在两个块之间的对应

**验收文件，档位：编译定理，无前提。** 第一位置的证明 (`Cp`, `Dn`) 记成走过的路径 (后继、ℕ 极限的编号、结点的 `top` 支)；
两个块的加法、结点两行、折叠把路径相同的证明送到路径相同的证明 (`addCpP`, `addWkP`, `ΨCpP`)。链点的合法性证明决定公共上界的位置搬运，所以要这一层。
树的关系在 [YiNextValRel](YiNextValRel.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNextValPath where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import OCF.Lean.YiLeanCore as M
import OCF.Lean.YiLeanFold as MF
import OCF.Lean.YiLeanLegal as ML
import OCF.Lean.YiNextCore as N
import OCF.Lean.YiNextBase as NB
import OCF.Lean.YiNextFold as NF
open import OCF.Lean.YiNextValRel
```

## 1 路径

```agda
data St : Set where
  D S C : St
  L : ℕ → St

tl : List St → List St
tl [] = []
tl (_ ∷ xs) = xs

ix : List St → ℕ
ix (L n ∷ _) = n
ix _ = 0

pCᴹ : ∀ y {a d : M.Raw y} → M.Cp y a d → List St
pDᴹ : ∀ y {a} (d : M.Raw y) → M.Dn y a d → List St
pCᴹ y (inj₁ _) = []
pCᴹ y (inj₂ p) = D ∷ pDᴹ y _ p
pDᴹ y (M.G.suc d) p = S ∷ pCᴹ y p
pDᴹ y (M.G.lim f) (n , p) = L n ∷ pCᴹ y p
pDᴹ y (M.G.lc r g) p = C ∷ pCᴹ y p
pDᴹ y _ _ = []

pCᴺ : ∀ y {a d : N.Raw y} → N.Cp y a d → List St
pDᴺ : ∀ y {a} (d : N.Raw y) → N.Dn y a d → List St
pCᴺ y (inj₁ _) = []
pCᴺ y (inj₂ p) = D ∷ pDᴺ y _ p
pDᴺ y (N.G.suc d) p = S ∷ pCᴺ y p
pDᴺ y (N.G.lim f) (n , p) = L n ∷ pCᴺ y p
pDᴺ y (N.G.lc r g) p = C ∷ pCᴺ y p
pDᴺ y _ _ = []

pLeᴹ : (k : M.LF) (r : M.Pre k) {η η′ : M.Lay.A (M.Lo k r)} → M.Le (M.Lo k r) η η′ → List St
pLeᴹ (M.suc k) (inj₁ _) e = pCᴹ k e
pLeᴹ (M.suc k) (inj₂ r) e = pLeᴹ k r e
pLeᴹ (M.lim f) (n , r) e = pLeᴹ (f n) r e
pLeᴹ _ _ _ = []

pLeᴺ : (k : N.LF) (r : N.Pre k) {η η′ : N.Lay.A (N.Lo k r)} → N.Le (N.Lo k r) η η′ → List St
pLeᴺ (N.suc k) (inj₁ _) e = pCᴺ k e
pLeᴺ (N.suc k) (inj₂ r) e = pLeᴺ k r e
pLeᴺ (N.lim f) (n , r) e = pLeᴺ (f n) r e
pLeᴺ _ _ _ = []
```

## 2 加法

`DBR`：造结点的办法下行时把路径相同的证明送到路径相同的证明 (对 `G.lc` 是在前面添 `C`)。

```agda
DBR : ∀ {T T′ k k′} (B : M.Bld T k) (B′ : N.Bld T′ k′) → ML.DnB B → NB.DnB B′ → Set
DBR {T} {T′} {k} {k′} B B′ h h′ = ∀ r r′ → PR k k′ r r′ → ∀ g g′ {z z′}
  (q : M.Cp T z (g (M.Lay.tp (M.Lo k r)))) (q′ : N.Cp T′ z′ (g′ (N.Lay.tp (N.Lo k′ r′)))) →
  pCᴹ T q ≡ pCᴺ T′ q′ → pDᴹ T (B r g) (h r g q) ≡ pDᴺ T′ (B′ r′ g′) (h′ r′ g′ q′)

dbLc : ∀ {T T′} → DBR {T} {T′} M.G.lc N.G.lc ML.dnLc NB.dnLc
dbLc r r′ e g g′ q q′ eq = cong (C ∷_) eq

addCpP : ∀ {T T′ k k′} → LR k k′ → ∀ {B B′ h h′} → DBR {T} {T′} {k} {k′} B B′ h h′ → ∀ x x′ {a a′ b b′} →
  RR k k′ b b′ → (p : M.Cp k a b) (p′ : N.Cp k′ a′ b′) → pCᴹ k p ≡ pCᴺ k′ p′ →
  pCᴹ T (ML.add-cp k B h x p) ≡ pCᴺ T′ (NB.add-cp k′ B′ h′ x′ p′)
addDnP : ∀ {T T′ k k′} → LR k k′ → ∀ {B B′ h h′} → DBR {T} {T′} {k} {k′} B B′ h h′ → ∀ x x′ {a a′ b b′} →
  RR k k′ b b′ → (p : M.Dn k a b) (p′ : N.Dn k′ a′ b′) → pDᴹ k b p ≡ pDᴺ k′ b′ p′ →
  pDᴹ T (M.add k B x b) (ML.add-dn k B h x b p) ≡ pDᴺ T′ (N.add k′ B′ x′ b′) (NB.add-dn k′ B′ h′ x′ b′ p′)

addCpP e hb x x′ d (inj₁ refl) (inj₁ refl) eq = refl
addCpP e hb x x′ d (inj₂ p) (inj₂ p′) eq = cong (D ∷_) (addDnP e hb x x′ d p p′ (cong tl eq))
addCpP e hb x x′ d (inj₁ refl) (inj₂ p′) ()
addCpP e hb x x′ d (inj₂ p) (inj₁ refl) ()

addDnP e hb x x′ (rs d) p p′ eq = cong (S ∷_) (addCpP e hb x x′ d p p′ (cong tl eq))
addDnP e hb x x′ (rl d) (n , p) (n′ , p′) eq with cong ix eq
... | refl = cong (L n ∷_) (addCpP e hb x x′ (d n) p p′ (cong tl eq))
addDnP e hb x x′ (rc {r = r} {r′ = r′} q h) p p′ eq =
  hb r r′ q _ _ (ML.add-cp _ _ _ x p) (NB.add-cp _ _ _ x′ p′)
    (addCpP e hb x x′ (h _ _ (tpR e r r′ q)) p p′ (cong tl eq))

addWkP : ∀ {T T′ k k′} → LR k k′ → ∀ {B B′ h h′} → DBR {T} {T′} {k} {k′} B B′ h h′ → ∀ x x′ {a a′} →
  RR k k′ a a′ → pCᴹ T (ML.add-weak k B h x a) ≡ pCᴺ T′ (NB.add-weak k′ B′ h′ x′ a′)
addWkP e hb x x′ rz = refl
addWkP e hb x x′ (rs d) = cong (λ z → D ∷ S ∷ z) (addWkP e hb x x′ d)
addWkP e hb x x′ (rl d) = cong (λ z → D ∷ L 0 ∷ z) (addWkP e hb x x′ (d 0))
addWkP e hb x x′ (rc {r = r} {r′ = r′} q h) =
  cong (D ∷_) (hb r r′ q _ _ _ _ (addWkP e hb x x′ (h _ _ (tpR e r r′ q))))
addWkP lz hb x x′ rt = refl
addWkP (ls e) hb x x′ rt = cong (D ∷_) (hb (inj₁ tt) (inj₁ tt) tt _ _ _ _
  (addWkP e (λ r r′ q → hb (inj₂ r) (inj₂ r′) q) x x′ rt))
addWkP (ll e) hb x x′ rt = cong (λ z → D ∷ L 0 ∷ z)
  (addWkP (e 0) (λ r r′ q → hb (0 , r) (0 , r′) (refl , q)) x x′ rt)

succStepP : ∀ {m m′} → LR m m′ → ∀ {y y′} → RR m m′ y y′ → ∀ n →
  pCᴹ m (ML.succ-step m y n) ≡ pCᴺ m′ (NB.succ-step m′ y′ n)
succStepP e yr zero = addWkP e dbLc _ _ yr
succStepP e yr (suc n) = addCpP e dbLc _ _ (accR (RR _ _) (λ _ d → plusR e yr d) yr (suc n)) _ _ (succStepP e yr n)
```

## 3 结点的两行与折叠

```agda
nodeAtDnP : ∀ {T T′ m m′} → LR m m′ → ∀ p p′ → PR m m′ p p′ → ∀ {B B′ h h′} → DBR {T} {T′} {m} {m′} B B′ h h′ →
  ∀ g g′ {z z′} (q : M.Cp T z (g M.G.top)) (q′ : N.Cp T′ z′ (g′ N.G.top)) → pCᴹ T q ≡ pCᴺ T′ q′ →
  pDᴹ T (MF.nodeAt m p B g) (ML.nodeAt-dn m p B h g q) ≡ pDᴺ T′ (NB.nodeAt m′ p′ B′ g′) (NB.nodeAt-dn m′ p′ B′ h′ g′ q′)
nodeAtDnP lz () p′ e hb
nodeAtDnP (ls em) (inj₁ _) (inj₁ _) e hb = hb (inj₁ tt) (inj₁ tt) tt
nodeAtDnP (ls em) (inj₂ p) (inj₂ p′) e hb = nodeAtDnP em p p′ e (λ r r′ q → hb (inj₂ r) (inj₂ r′) q)
nodeAtDnP (ls em) (inj₁ _) (inj₂ _) () hb
nodeAtDnP (ls em) (inj₂ _) (inj₁ _) () hb
nodeAtDnP (ll em) (n , p) (_ , p′) (refl , e) hb = nodeAtDnP (em n) p p′ e (λ r r′ q → hb (n , r) (n , r′) (refl , q))

ΨnDnP : ∀ {m m′} → LR m m′ → ∀ {j j′} (w : MF.Way m j) (w′ : NB.Way m′ j′) → WR m m′ w w′ →
  ∀ gm gm′ gk gk′ {z z′} (q : M.Cp m z (gm M.G.top)) (q′ : N.Cp m′ z′ (gm′ N.G.top)) → pCᴹ m q ≡ pCᴺ m′ q′ →
  pDᴹ m (MF.Ψn m j w gm gk) (ML.Ψn-dn m j w gm gk q) ≡ pDᴺ m′ (NB.Ψn m′ j′ w′ gm′ gk′) (NB.Ψn-dn m′ j′ w′ gm′ gk′ q′)
ΨnDnP em (MF.keep p refl) (NB.keep p′ refl) e gm gm′ gk gk′ = nodeAtDnP em p p′ e dbLc gm gm′
ΨnDnP em MF.fold NB.fold e gm gm′ gk gk′ q q′ eq = cong (L 0 ∷_) eq
ΨnDnP em (MF.keep p _) NB.fold ()
ΨnDnP em MF.fold (NB.keep p′ _) ()

ΨNDnP : ∀ {m m′} → LR m m′ → ∀ {k k′} → LR k k′ → ∀ r r′ → PR k k′ r r′ →
  (w : MF.Way m (MF.lev k r)) (w′ : NB.Way m′ (NB.lev k′ r′)) → WR m m′ w w′ → ∀ gm gm′ gk gk′ {z z′}
  (q : M.Cp m z (gm (M.Lay.tp (M.Lo k r)))) (q′ : N.Cp m′ z′ (gm′ (N.Lay.tp (N.Lo k′ r′)))) → pCᴹ m q ≡ pCᴺ m′ q′ →
  pDᴹ m (MF.ΨN m k r w gm gk) (ML.ΨN-dn m k r w gm gk q) ≡ pDᴺ m′ (NB.ΨN m′ k′ r′ w′ gm′ gk′) (NB.ΨN-dn m′ k′ r′ w′ gm′ gk′ q′)
ΨNDnP em lz () r′ q
ΨNDnP em (ls ek) (inj₁ _) (inj₁ _) q = ΨnDnP em
ΨNDnP em (ls ek) (inj₂ r) (inj₂ r′) q = ΨNDnP em ek r r′ q
ΨNDnP em (ls ek) (inj₁ _) (inj₂ _) ()
ΨNDnP em (ls ek) (inj₂ _) (inj₁ _) ()
ΨNDnP em (ll ek) (n , r) (_ , r′) (refl , q) = ΨNDnP em (ek n) r r′ q

ΨCpP : ∀ {m m′} → LR m m′ → ∀ {k k′} {V : MF.Lv k} {V′ : NB.Lv k′} → VR V V′ → ∀ {x x′} → XR m m′ k k′ x x′ →
  ∀ {ξ ξ′ ζ ζ′} → RR k k′ ζ ζ′ → (p : M.Cp k ξ ζ) (p′ : N.Cp k′ ξ′ ζ′) → pCᴹ k p ≡ pCᴺ k′ p′ →
  pCᴹ m (ML.Ψ-cp m V x p) ≡ pCᴺ m′ (NF.Ψ-cp m′ V′ x′ p′)
ΨDnP : ∀ {m m′} → LR m m′ → ∀ {k k′} {V : MF.Lv k} {V′ : NB.Lv k′} → VR V V′ → ∀ {x x′} → XR m m′ k k′ x x′ →
  ∀ {ξ ξ′ ζ ζ′} → RR k k′ ζ ζ′ → (p : M.Dn k ξ ζ) (p′ : N.Dn k′ ξ′ ζ′) → pDᴹ k ζ p ≡ pDᴺ k′ ζ′ p′ →
  pDᴹ m (MF.Ψ m V x ζ) (ML.Ψ-dn m V x ζ p) ≡ pDᴺ m′ (NF.Ψ m′ V′ x′ ζ′) (NF.Ψ-dn m′ V′ x′ ζ′ p′)

ΨCpP em v xr d (inj₁ refl) (inj₁ refl) eq = refl
ΨCpP em v xr d (inj₂ p) (inj₂ p′) eq = cong (D ∷_) (ΨDnP em v xr d p p′ (cong tl eq))
ΨCpP em v xr d (inj₁ refl) (inj₂ p′) ()
ΨCpP em v xr d (inj₂ p) (inj₁ refl) ()

ΨDnP em v xr (rs d) p p′ eq = cong (L 0 ∷_) (ΨCpP em v xr d p p′ (cong tl eq))
ΨDnP em v xr (rl d) (n , p) (n′ , p′) eq with cong ix eq
... | refl = cong (L n ∷_) (ΨCpP em v xr (d n) p p′ (cong tl eq))
ΨDnP em {V = V} {V′} v {x} {x′} xr (rc {r = r} {r′ = r′} {g = g} {g′ = g′} q h) p p′ eq =
  ΨNDnP em (vLR v) r r′ q (x r) (x′ r′) (xr r r′ q)
    (λ η → MF.Ψ _ V x (g η)) (λ η → NF.Ψ _ V′ x′ (g′ η))
    (λ η → MF.Ψ (MF.lev _ r) V (MF.cmp V r) (g η)) (λ η → NF.Ψ (NB.lev _ r′) V′ (NB.cmp V′ r′) (g′ η))
    (ML.Ψ-cp _ V x p) (NF.Ψ-cp _ V′ x′ p′) (ΨCpP em v xr (h _ _ (tpR (vLR v) r r′ q)) p p′ (cong tl eq))
```
