# YiNextVal 关系：主线块与下一站块的结构互模拟 (可数层号)

**验收文件，档位：编译定理，无前提。** 两个块的代码逐字相同但是两个模块；本文给层号、位置、树、派发、公共上界的跨模块关系 (树只取不含 `em` 的)，
证明两边的折叠 `Ψ` 把相关的输入折成相关的输出 (`ΨR`)，第 0 层相关的树读回结构互模拟 (`read≅`)。公共上界只取零、后继、ℕ 极限 (`VR` 不含 `vΩ`)。
合法性证明的对应在 [YiNextValLgl](YiNextValLgl.lagda.md)，链点与 `T₃` 在 [YiNextValFin](YiNextValFin.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNextValRel where

open import Data.Nat.Base using (ℕ; zero; suc; _⊔_; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤⇒≤′)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst₂)
import OCF.Lean.YiLeanCore as M
import OCF.Lean.YiLeanFold as MF
import OCF.Lean.YiNextCore as N
import OCF.Lean.YiNextBase as NB
import OCF.Lean.YiNextFold as NF
import OCF.Lean.YiLeanAccFin as MA
import OCF.Lean.YiNextAcc as NA
import OCF.Align.Level as L
```

## 1 层号、位置、树

`LR`：两边的层号由零、后继、ℕ 极限同样地搭成。`PR`：位置同样 (ℕ 极限处编号相等)。树的关系 `RR` 对两边的层号递归：
结点的位置相关，分支把相关的下标送到相关的树 (下标所在那一层的 `RR`，由 `LayRel` 沿位置走到)。

```agda
data LR : M.LF → N.LF → Set where
  lz : LR M.zero N.zero
  ls : ∀ {k k′} → LR k k′ → LR (M.suc k) (N.suc k′)
  ll : ∀ {f : ℕ → M.LF} {f′ : ℕ → N.LF} → (∀ n → LR (f n) (f′ n)) → LR (M.lim f) (N.lim f′)

PR : (k : M.LF) (k′ : N.LF) → M.Pre k → N.Pre k′ → Set
PR (M.suc k) (N.suc k′) (inj₁ _) (inj₁ _) = ⊤
PR (M.suc k) (N.suc k′) (inj₂ r) (inj₂ r′) = PR k k′ r r′
PR (M.lim f) (N.lim f′) (n , r) (n′ , r′) = (n ≡ n′) × PR (f n) (f′ n′) r r′
PR _ _ _ _ = ⊥

module GR {P : Set} {Lf : P → Set} {K : Set} {B : K → Set}
          {P′ : Set} {Lf′ : P′ → Set} {K′ : Set} {B′ : K′ → Set}
          (Q : P → P′ → Set) (H : ∀ r r′ → Lf r → Lf′ r′ → Set) where
  data Rel : M.G.R P Lf K B → N.G.R P′ Lf′ K′ B′ → Set where
    rz : Rel M.G.zero N.G.zero
    rs : ∀ {a a′} → Rel a a′ → Rel (M.G.suc a) (N.G.suc a′)
    rl : ∀ {f f′} → (∀ n → Rel (f n) (f′ n)) → Rel (M.G.lim f) (N.G.lim f′)
    rc : ∀ {r r′ g g′} → Q r r′ → (∀ η η′ → H r r′ η η′ → Rel (g η) (g′ η′)) → Rel (M.G.lc r g) (N.G.lc r′ g′)
    rt : Rel M.G.top N.G.top
open GR public using (rz; rs; rl; rc; rt)

RR : (k : M.LF) (k′ : N.LF) → M.Raw k → N.Raw k′ → Set
LayRel : (k : M.LF) (k′ : N.LF) (r : M.Pre k) (r′ : N.Pre k′) →
  M.Lay.A (M.Lo k r) → N.Lay.A (N.Lo k′ r′) → Set

RR k k′ = GR.Rel (PR k k′) (LayRel k k′)
LayRel (M.suc k) (N.suc k′) (inj₁ _) (inj₁ _) = RR k k′
LayRel (M.suc k) (N.suc k′) (inj₂ r) (inj₂ r′) = LayRel k k′ r r′
LayRel (M.lim f) (N.lim f′) (n , r) (n′ , r′) = LayRel (f n) (f′ n′) r r′
LayRel _ _ _ _ _ _ = ⊥

tpR : ∀ {k k′} → LR k k′ → ∀ r r′ → PR k k′ r r′ → LayRel k k′ r r′ (M.Lay.tp (M.Lo k r)) (N.Lay.tp (N.Lo k′ r′))
tpR lz () r′ q
tpR (ls e) (inj₁ _) (inj₁ _) q = rt
tpR (ls e) (inj₂ r) (inj₂ r′) q = tpR e r r′ q
tpR (ls e) (inj₁ _) (inj₂ _) ()
tpR (ls e) (inj₂ _) (inj₁ _) ()
tpR (ll e) (n , r) (_ , r′) (refl , q) = tpR (e n) r r′ q

levR : ∀ {k k′} → LR k k′ → ∀ r r′ → PR k k′ r r′ → LR (MF.lev k r) (NB.lev k′ r′)
levR lz () r′ q
levR (ls e) (inj₁ _) (inj₁ _) q = e
levR (ls e) (inj₂ r) (inj₂ r′) q = levR e r r′ q
levR (ls e) (inj₁ _) (inj₂ _) ()
levR (ls e) (inj₂ _) (inj₁ _) ()
levR (ll e) (n , r) (_ , r′) (refl , q) = levR (e n) r r′ q
```

## 2 派发与公共上界

```agda
WR : (m : M.LF) (m′ : N.LF) {j : M.LF} {j′ : N.LF} → MF.Way m j → NB.Way m′ j′ → Set
WR m m′ (MF.keep s _) (NB.keep s′ _) = PR m m′ s s′
WR m m′ MF.fold NB.fold = ⊤
WR m m′ _ _ = ⊥

XR : (m : M.LF) (m′ : N.LF) (k : M.LF) (k′ : N.LF) → MF.Ext m k → NB.Ext m′ k′ → Set
XR m m′ k k′ x x′ = ∀ r r′ → PR k k′ r r′ → WR m m′ (x r) (x′ r′)

data VR : ∀ {k k′} → MF.Lv k → NB.Lv k′ → Set where
  v0R : VR MF.v0 NB.v0
  vsR : ∀ {k k′} {V : MF.Lv k} {V′ : NB.Lv k′} → VR V V′ → VR (MF.vs V) (NB.vs V′)
  vlR : ∀ {f : ℕ → M.LF} {f′ : ℕ → N.LF} {V : ∀ n → MF.Lv (f n)} {V′ : ∀ n → NB.Lv (f′ n)}
    {st : ∀ n → MF.Shift (f n) (f (suc n))} {st′ : ∀ n → NB.Shift (f′ n) (f′ (suc n))} → (∀ n → VR (V n) (V′ n)) →
    (∀ n q q′ → PR (f n) (f′ n) q q′ → PR (f (suc n)) (f′ (suc n)) (proj₁ (st n q)) (proj₁ (st′ n q′))) →
    VR (MF.vl V st) (NB.vl V′ st′)

vLR : ∀ {k k′} {V : MF.Lv k} {V′ : NB.Lv k′} → VR V V′ → LR k k′
vLR v0R = lz
vLR (vsR v) = ls (vLR v)
vLR (vlR v h) = ll (λ n → vLR (v n))

shiftR : ∀ {f : ℕ → M.LF} {f′ : ℕ → N.LF} {st : ∀ n → MF.Shift (f n) (f (suc n))} {st′ : ∀ n → NB.Shift (f′ n) (f′ (suc n))} →
  (∀ n q q′ → PR (f n) (f′ n) q q′ → PR (f (suc n)) (f′ (suc n)) (proj₁ (st n q)) (proj₁ (st′ n q′))) →
  ∀ {n m} (p : n ≤′ m) q q′ → PR (f n) (f′ n) q q′ → PR (f m) (f′ m) (proj₁ (MF.shift st p q)) (proj₁ (NB.shift st′ p q′))
shiftR h ≤′-refl q q′ e = e
shiftR h (≤′-step p) q q′ e = h _ _ _ (shiftR h p q q′ e)

substR : ∀ {a b c d : M.LF} {a′ b′ c′ d′ : N.LF} (p : a ≡ b) (q : c ≡ d) (p′ : a′ ≡ b′) (q′ : c′ ≡ d′)
  (w : MF.Way a c) (w′ : NB.Way a′ c′) → WR a a′ w w′ → WR b b′ (subst₂ MF.Way p q w) (subst₂ NB.Way p′ q′ w′)
substR refl refl refl refl w w′ h = h

cmpR : ∀ {k k′} {V : MF.Lv k} {V′ : NB.Lv k′} → VR V V′ → ∀ q q′ → PR k k′ q q′ → ∀ r r′ → PR k k′ r r′ →
  WR (MF.lev k q) (NB.lev k′ q′) (MF.cmp V q r) (NB.cmp V′ q′ r′)
cmpR v0R () q′ e r r′ e′
cmpR (vsR v) (inj₁ _) (inj₁ _) e (inj₁ _) (inj₁ _) e′ = tt
cmpR (vsR v) (inj₁ _) (inj₁ _) e (inj₂ r) (inj₂ r′) e′ = e′
cmpR (vsR v) (inj₂ q) (inj₂ q′) e (inj₁ _) (inj₁ _) e′ = tt
cmpR (vsR v) (inj₂ q) (inj₂ q′) e (inj₂ r) (inj₂ r′) e′ = cmpR v q q′ e r r′ e′
cmpR (vsR v) (inj₁ _) (inj₂ _) () r r′ e′
cmpR (vsR v) (inj₂ _) (inj₁ _) () r r′ e′
cmpR (vsR v) (inj₁ _) (inj₁ _) e (inj₁ _) (inj₂ _) ()
cmpR (vsR v) (inj₁ _) (inj₁ _) e (inj₂ _) (inj₁ _) ()
cmpR (vsR v) (inj₂ _) (inj₂ _) e (inj₁ _) (inj₂ _) ()
cmpR (vsR v) (inj₂ _) (inj₂ _) e (inj₂ _) (inj₁ _) ()
cmpR (vlR {st = st} {st′ = st′} v h) (n , q) (_ , q′) (refl , e) (m , r) (_ , r′) (refl , e′) =
  substR (proj₂ (MF.shift st (≤⇒≤′ (m≤m⊔n n m)) q)) (proj₂ (MF.shift st (≤⇒≤′ (m≤n⊔m n m)) r))
    (proj₂ (NB.shift st′ (≤⇒≤′ (m≤m⊔n n m)) q′)) (proj₂ (NB.shift st′ (≤⇒≤′ (m≤n⊔m n m)) r′)) _ _
    (cmpR (v (n ⊔ m)) _ _ (shiftR h (≤⇒≤′ (m≤m⊔n n m)) q q′ e) _ _ (shiftR h (≤⇒≤′ (m≤n⊔m n m)) r r′ e′))
```

## 3 加法与结点的两行

```agda
accR : ∀ {A : Set} {A′ : Set} (R : A → A′ → Set) {s : ℕ → A → A} {s′ : ℕ → A′ → A′} →
  (∀ n {y y′} → R y y′ → R (s n y) (s′ n y′)) → ∀ {x x′} → R x x′ → ∀ n → R (M.acc s x n) (N.acc s′ x′ n)
accR R h r zero = r
accR R h r (suc n) = h n (accR R h r n)

BR : (T : M.LF) (T′ : N.LF) (k : M.LF) (k′ : N.LF) → M.Bld T k → N.Bld T′ k′ → Set
BR T T′ k k′ B B′ = ∀ r r′ → PR k k′ r r′ → ∀ {g g′} →
  (∀ η η′ → LayRel k k′ r r′ η η′ → RR T T′ (g η) (g′ η′)) → RR T T′ (B r g) (B′ r′ g′)

lcBR : ∀ {T T′} → BR T T′ T T′ M.G.lc N.G.lc
lcBR r r′ q h = rc q h

addR : ∀ {T T′ k k′} → LR k k′ → ∀ {B B′} → BR T T′ k k′ B B′ → ∀ {x x′} → RR T T′ x x′ →
  ∀ {a a′} → RR k k′ a a′ → RR T T′ (M.add k B x a) (N.add k′ B′ x′ a′)
addR e b xr rz = xr
addR e b xr (rs d) = rs (addR e b xr d)
addR e b xr (rl d) = rl (λ n → addR e b xr (d n))
addR e b xr (rc {r = r} {r′ = r′} q h) = b r r′ q (λ η η′ h′ → addR e b xr (h η η′ h′))
addR lz b xr rt = rs xr
addR (ls e) b xr rt = b (inj₁ tt) (inj₁ tt) tt (λ η η′ h → addR e (λ r r′ q → b (inj₂ r) (inj₂ r′) q) xr h)
addR (ll e) b xr rt = rl (λ n → accR (RR _ _)
  (λ i d → addR (e i) (λ r r′ q → b (i , r) (i , r′) (refl , q)) d rt) xr (suc n))

plusR : ∀ {T T′} → LR T T′ → ∀ {x x′ a a′} → RR T T′ x x′ → RR T T′ a a′ → RR T T′ (M.plus T x a) (N.plus T′ x′ a′)
plusR e xr ar = addR e lcBR xr ar

succR : ∀ {m m′} → LR m m′ → ∀ {y y′} → RR m m′ y y′ → RR m m′ (MF.succ m y) (NB.succ m′ y′)
succR e d = rl (accR (RR _ _) (λ _ d′ → plusR e d d′) d)

psumR : ∀ {m m′} → LR m m′ → ∀ {h h′} → (∀ n → RR m m′ (h n) (h′ n)) → ∀ n → RR m m′ (MF.psum m h n) (NB.psum m′ h′ n)
psumR e hr = accR (RR _ _) (λ n d → plusR e d (hr (suc n))) (hr zero)

chainR : ∀ {j j′} → LR j j′ → ∀ {gk gk′} → (∀ η η′ → RR j j′ η η′ → RR j j′ (gk η) (gk′ η′)) →
  ∀ n → RR j j′ (MF.chain j gk n) (NB.chain j′ gk′ n)
chainR e hk zero = rt
chainR e hk (suc n) = plusR e (chainR e hk n) (hk _ _ (chainR e hk n))

nodeAtR : ∀ {T T′ m m′} → LR m m′ → ∀ p p′ → PR m m′ p p′ → ∀ {B B′} → BR T T′ m m′ B B′ → ∀ {g g′} →
  (∀ η η′ → RR (MF.lev m p) (NB.lev m′ p′) η η′ → RR T T′ (g η) (g′ η′)) →
  RR T T′ (MF.nodeAt m p B g) (NB.nodeAt m′ p′ B′ g′)
nodeAtR lz () p′ q b h
nodeAtR (ls e) (inj₁ _) (inj₁ _) q b h = b (inj₁ tt) (inj₁ tt) tt h
nodeAtR (ls e) (inj₂ p) (inj₂ p′) q b h = nodeAtR e p p′ q (λ r r′ q′ → b (inj₂ r) (inj₂ r′) q′) h
nodeAtR (ls e) (inj₁ _) (inj₂ _) () b h
nodeAtR (ls e) (inj₂ _) (inj₁ _) () b h
nodeAtR (ll e) (n , p) (_ , p′) (refl , q) b h = nodeAtR (e n) p p′ q (λ r r′ q′ → b (n , r) (n , r′) (refl , q′)) h

ΨnR : ∀ {m m′} → LR m m′ → ∀ {j j′} → LR j j′ → (w : MF.Way m j) (w′ : NB.Way m′ j′) → WR m m′ w w′ →
  ∀ {gm gm′ gk gk′} → (∀ η η′ → RR j j′ η η′ → RR m m′ (gm η) (gm′ η′)) →
  (∀ η η′ → RR j j′ η η′ → RR j j′ (gk η) (gk′ η′)) → RR m m′ (MF.Ψn m j w gm gk) (NB.Ψn m′ j′ w′ gm′ gk′)
ΨnR em ej (MF.keep p refl) (NB.keep p′ refl) q hm hk = nodeAtR em p p′ q lcBR hm
ΨnR em ej MF.fold NB.fold q hm hk = rl (λ n → hm _ _ (chainR ej hk n))
ΨnR em ej (MF.keep p e) NB.fold () hm hk
ΨnR em ej MF.fold (NB.keep p′ e) () hm hk

ΨNR : ∀ {m m′} → LR m m′ → ∀ {k k′} → LR k k′ → ∀ r r′ → PR k k′ r r′ →
  (w : MF.Way m (MF.lev k r)) (w′ : NB.Way m′ (NB.lev k′ r′)) → WR m m′ w w′ → ∀ {gm gm′ gk gk′} →
  (∀ η η′ → LayRel k k′ r r′ η η′ → RR m m′ (gm η) (gm′ η′)) →
  (∀ η η′ → LayRel k k′ r r′ η η′ → RR (MF.lev k r) (NB.lev k′ r′) (gk η) (gk′ η′)) →
  RR m m′ (MF.ΨN m k r w gm gk) (NB.ΨN m′ k′ r′ w′ gm′ gk′)
ΨNR em lz () r′ q
ΨNR em (ls ek) (inj₁ _) (inj₁ _) q = ΨnR em ek
ΨNR em (ls ek) (inj₂ r) (inj₂ r′) q = ΨNR em ek r r′ q
ΨNR em (ls ek) (inj₁ _) (inj₂ _) ()
ΨNR em (ls ek) (inj₂ _) (inj₁ _) ()
ΨNR em (ll ek) (n , r) (_ , r′) (refl , q) = ΨNR em (ek n) r r′ q
```

## 4 折叠

```agda
ΨR : ∀ {m m′} → LR m m′ → ∀ {k k′} {V : MF.Lv k} {V′ : NB.Lv k′} → VR V V′ → ∀ {x x′} → XR m m′ k k′ x x′ →
  ∀ {ξ ξ′} → RR k k′ ξ ξ′ → RR m m′ (MF.Ψ m V x ξ) (NF.Ψ m′ V′ x′ ξ′)
ΨR em v xr rz = rt
ΨR em v xr (rs d) = succR em (ΨR em v xr d)
ΨR em v xr (rl d) = rl (λ n → ΨR em v xr (d n))
ΨR em {V = V} {V′} v {x} {x′} xr (rc {r = r} {r′ = r′} q h) =
  ΨNR em (vLR v) r r′ q (x r) (x′ r′) (xr r r′ q) (λ η η′ h′ → ΨR em v xr (h η η′ h′))
    (λ η η′ h′ → ΨR (levR (vLR v) r r′ q) v (λ q₁ q₁′ e → cmpR v r r′ q q₁ q₁′ e) (h η η′ h′))
ΨR em v0R xr rt = succR em rt
ΨR em (vsR v) {x} {x′} xr rt = ΨnR em (vLR v) (x (inj₁ tt)) (x′ (inj₁ tt)) (xr (inj₁ tt) (inj₁ tt) tt)
  (λ η η′ h → ΨR em v (λ r r′ e → xr (inj₂ r) (inj₂ r′) e) h) (λ η η′ h → ΨR (vLR v) v (λ r r′ e → e) h)
ΨR em (vlR v s) xr rt = rl (psumR em (λ n → ΨR em (v n) (λ r r′ e → xr (n , r) (n , r′) (refl , e)) rt))
```

## 5 第 0 层的读回

```agda
read≅ : ∀ {a a′} → RR M.zero N.zero a a′ → MA.read a L.≅ NA.read a′
read≅ rz = L.z≅
read≅ (rs d) = L.s≅ (read≅ d)
read≅ (rl d) = L.l≅ (λ n → read≅ (d n))
read≅ (rc {r = ()} q h)
read≅ rt = L.s≅ L.z≅
```
