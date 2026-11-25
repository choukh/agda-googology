# YiNextVal 合法性：两个块的合法性证明对应

**验收文件，档位：编译定理，无前提。** `LglR`：两个合法性证明里每个第一位置证明的路径相同 (结点处对相关的合法下标逐支要求)。
加法、ω 倍、部分和、链、结点两行、折叠 `Ψ-lgl` 保持它 (`ΨLglR`)。公共上界的位置搬运 (`lv` 的 `sh`) 只读这些路径，下一个文件用它。
路径在 [YiNextValPath](YiNextValPath.lagda.md)，树在 [YiNextValRel](YiNextValRel.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNextValLgl where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiLeanCore as M
import OCF.Lean.YiLeanFold as MF
import OCF.Lean.YiLeanLegal as ML
import OCF.Lean.YiNextCore as N
import OCF.Lean.YiNextBase as NB
import OCF.Lean.YiNextFold as NF
open import OCF.Lean.YiNextValRel
open import OCF.Lean.YiNextValPath
```

## 1 关系

对树递归，不对树的关系的推导递归；结点处的单调证明只要求上端的下标相关 (路径只看上端的结构)。

```agda
LglR : (k : M.LF) (k′ : N.LF) (ξ : M.Raw k) (ξ′ : N.Raw k′) → M.Lgl k ξ → N.Lgl k′ ξ′ → Set
LayLgl : (k : M.LF) (k′ : N.LF) (r : M.Pre k) (r′ : N.Pre k′) (η : M.Lay.A (M.Lo k r)) (η′ : N.Lay.A (N.Lo k′ r′)) →
  M.Lay.lg (M.Lo k r) η → N.Lay.lg (N.Lo k′ r′) η′ → Set

LglR k k′ (M.G.suc a) (N.G.suc a′) l l′ = LglR k k′ a a′ l l′
LglR k k′ (M.G.lim f) (N.G.lim f′) l l′ =
  (∀ n → pCᴹ k (proj₁ l n) ≡ pCᴺ k′ (proj₁ l′ n)) × (∀ n → LglR k k′ (f n) (f′ n) (proj₂ l n) (proj₂ l′ n))
LglR k k′ (M.G.lc r g) (N.G.lc r′ g′) l l′ =
  (∀ η η′ → LayRel k k′ r r′ η η′ → ∀ lη lη′ → LayLgl k k′ r r′ η η′ lη lη′ →
     LglR k k′ (g η) (g′ η′) (proj₁ l η lη) (proj₁ l′ η′ lη′)) ×
  (∀ η₁ η₁′ η₂ η₂′ → LayRel k k′ r r′ η₂ η₂′ → ∀ l₁ l₁′ e e′ l₂ l₂′ → pLeᴹ k r e ≡ pLeᴺ k′ r′ e′ →
     pCᴹ k (proj₂ l η₁ η₂ l₁ e l₂) ≡ pCᴺ k′ (proj₂ l′ η₁′ η₂′ l₁′ e′ l₂′))
LglR _ _ _ _ _ _ = ⊤

LayLgl (M.suc k) (N.suc k′) (inj₁ _) (inj₁ _) η η′ = LglR k k′ η η′
LayLgl (M.suc k) (N.suc k′) (inj₂ r) (inj₂ r′) = LayLgl k k′ r r′
LayLgl (M.lim f) (N.lim f′) (n , r) (n′ , r′) = LayLgl (f n) (f′ n′) r r′
LayLgl _ _ _ _ _ _ _ _ = ⊤

BrR : (k : M.LF) (k′ : N.LF) (r : M.Pre k) (r′ : N.Pre k′) (T : M.LF) (T′ : N.LF)
  (g : M.Lay.A (M.Lo k r) → M.Raw T) (g′ : N.Lay.A (N.Lo k′ r′) → N.Raw T′) → ML.Br (M.Lo k r) T g → NB.Br (N.Lo k′ r′) T′ g′ → Set
BrR k k′ r r′ T T′ g g′ l l′ =
  (∀ η η′ → LayRel k k′ r r′ η η′ → ∀ lη lη′ → LayLgl k k′ r r′ η η′ lη lη′ →
     LglR T T′ (g η) (g′ η′) (proj₁ l η lη) (proj₁ l′ η′ lη′)) ×
  (∀ η₁ η₁′ η₂ η₂′ → LayRel k k′ r r′ η₂ η₂′ → ∀ l₁ l₁′ e e′ l₂ l₂′ → pLeᴹ k r e ≡ pLeᴺ k′ r′ e′ →
     pCᴹ T (proj₂ l η₁ η₂ l₁ e l₂) ≡ pCᴺ T′ (proj₂ l′ η₁′ η₂′ l₁′ e′ l₂′))

BrL : (j : M.LF) (j′ : N.LF) (T : M.LF) (T′ : N.LF) (g : M.Raw j → M.Raw T) (g′ : N.Raw j′ → N.Raw T′) → ML.Br (M.layer j) T g → NB.Br (N.layer j′) T′ g′ → Set
BrL j j′ T T′ g g′ l l′ =
  (∀ η η′ → RR j j′ η η′ → ∀ lη lη′ → LglR j j′ η η′ lη lη′ →
     LglR T T′ (g η) (g′ η′) (proj₁ l η lη) (proj₁ l′ η′ lη′)) ×
  (∀ η₁ η₁′ η₂ η₂′ → RR j j′ η₂ η₂′ → ∀ l₁ l₁′ e e′ l₂ l₂′ → pCᴹ j e ≡ pCᴺ j′ e′ →
     pCᴹ T (proj₂ l η₁ η₂ l₁ e l₂) ≡ pCᴺ T′ (proj₂ l′ η₁′ η₂′ l₁′ e′ l₂′))

LgBR : ∀ {T T′ k k′} (B : M.Bld T k) (B′ : N.Bld T′ k′) → ML.LgB B → NB.LgB B′ → Set
LgBR {T} {T′} {k} {k′} B B′ b b′ = ∀ r r′ → PR k k′ r r′ → ∀ g g′ br br′ → BrR k k′ r r′ T T′ g g′ br br′ →
  LglR T T′ (B r g) (B′ r′ g′) (b r g br) (b′ r′ g′ br′)

lgbLc : ∀ {T T′} → LgBR {T} {T′} M.G.lc N.G.lc ML.lgLc NB.lgLc
lgbLc r r′ q g g′ br br′ h = h
```

## 2 加法、ω 倍、部分和、链

```agda
accIndR : ∀ {A : Set} {A′ : Set} (R : A → A′ → Set) (P : A → Set) (P′ : A′ → Set) (Q : ∀ y y′ → P y → P′ y′ → Set)
  {s : ℕ → A → A} {s′ : ℕ → A′ → A′} (sR : ∀ n {y y′} → R y y′ → R (s n y) (s′ n y′))
  {h : ∀ n y → P y → P (s n y)} {h′ : ∀ n y → P′ y → P′ (s′ n y)} →
  (∀ n {y y′} → R y y′ → ∀ {py py′} → Q y y′ py py′ → Q (s n y) (s′ n y′) (h n y py) (h′ n y′ py′)) →
  ∀ {x x′} → R x x′ → ∀ {px px′} → Q x x′ px px′ → ∀ n →
  Q (M.acc s x n) (N.acc s′ x′ n) (ML.acc-ind P s h x px n) (NB.acc-ind P′ s′ h′ x′ px′ n)
accIndR R P P′ Q sR hR r q zero = q
accIndR R P P′ Q sR hR r q (suc n) = hR n (accR R sR r n) (accIndR R P P′ Q sR hR r q n)

addLglR : ∀ {T T′ k k′} → LR k k′ → ∀ {B B′ h h′ b b′} → BR T T′ k k′ B B′ → DBR {T} {T′} {k} {k′} B B′ h h′ →
  LgBR B B′ b b′ → ∀ {x x′} → RR T T′ x x′ → ∀ {a a′} → RR k k′ a a′ → ∀ {lx lx′ la la′} →
  LglR T T′ x x′ lx lx′ → LglR k k′ a a′ la la′ →
  LglR T T′ (M.add k B x a) (N.add k′ B′ x′ a′) (ML.add-lgl k B h b x a lx la) (NB.add-lgl k′ B′ h′ b′ x′ a′ lx′ la′)
addLglR e bB hb lb xr rz lxr lar = lxr
addLglR e bB hb lb xr (rs d) lxr lar = addLglR e bB hb lb xr d lxr lar
addLglR e bB hb lb {x} {x′} xr (rl d) lxr lar =
  (λ n → addCpP e hb x x′ (d (suc n)) _ _ (proj₁ lar n)) , (λ n → addLglR e bB hb lb xr (d n) lxr (proj₂ lar n))
addLglR e bB hb lb {x} {x′} xr (rc {r = r} {r′ = r′} q h) lxr lar = lb r r′ q _ _ _ _
  ((λ η η′ hr lη lη′ ll → addLglR e bB hb lb xr (h η η′ hr) lxr (proj₁ lar η η′ hr lη lη′ ll)) ,
   (λ η₁ η₁′ η₂ η₂′ hr₂ l₁ l₁′ u u′ l₂ l₂′ eq →
     addCpP e hb x x′ (h η₂ η₂′ hr₂) _ _ (proj₂ lar η₁ η₁′ η₂ η₂′ hr₂ l₁ l₁′ u u′ l₂ l₂′ eq)))
addLglR lz bB hb lb xr rt lxr lar = lxr
addLglR (ls e) bB hb lb {x} {x′} xr rt lxr lar = lb (inj₁ tt) (inj₁ tt) tt _ _ _ _
  ((λ η η′ hr lη lη′ ll → addLglR e (λ r r′ q → bB (inj₂ r) (inj₂ r′) q) (λ r r′ q → hb (inj₂ r) (inj₂ r′) q)
     (λ r r′ q → lb (inj₂ r) (inj₂ r′) q) xr hr lxr ll) ,
   (λ η₁ η₁′ η₂ η₂′ hr₂ l₁ l₁′ u u′ l₂ l₂′ eq → addCpP e (λ r r′ q → hb (inj₂ r) (inj₂ r′) q) x x′ hr₂ u u′ eq))
addLglR (ll e) bB hb lb xr rt lxr lar =
  (λ n → addWkP (e (suc n)) (λ r r′ q → hb (suc n , r) (suc n , r′) (refl , q)) _ _ rt) ,
  (λ n → accIndR (RR _ _) _ _ (LglR _ _) (λ i d → addR (e i) (λ r r′ q → bB (i , r) (i , r′) (refl , q)) d rt)
     (λ i yr ly → addLglR (e i) (λ r r′ q → bB (i , r) (i , r′) (refl , q)) (λ r r′ q → hb (i , r) (i , r′) (refl , q))
        (λ r r′ q → lb (i , r) (i , r′) (refl , q)) yr rt ly tt) xr lxr (suc n))

plusLglR : ∀ {T T′} → LR T T′ → ∀ {x x′ a a′} → RR T T′ x x′ → RR T T′ a a′ → ∀ {lx lx′ la la′} →
  LglR T T′ x x′ lx lx′ → LglR T T′ a a′ la la′ →
  LglR T T′ (M.plus T x a) (N.plus T′ x′ a′) (ML.plus-lgl T x a lx la) (NB.plus-lgl T′ x′ a′ lx′ la′)
plusLglR e xr ar = addLglR e lcBR dbLc lgbLc xr ar

succLglR : ∀ {m m′} → LR m m′ → ∀ {y y′} → RR m m′ y y′ → ∀ {ly ly′} → LglR m m′ y y′ ly ly′ →
  LglR m m′ (MF.succ m y) (NB.succ m′ y′) (ML.succ-lgl m y ly) (NB.succ-lgl m′ y′ ly′)
succLglR e yr lr = (λ n → succStepP e yr n) ,
  accIndR (RR _ _) _ _ (LglR _ _) (λ _ d → plusR e yr d) (λ _ d l → plusLglR e yr d lr l) yr lr

psumLglR : ∀ {m m′} → LR m m′ → ∀ {h h′} (hr : ∀ n → RR m m′ (h n) (h′ n)) {lh lh′} →
  (∀ n → LglR m m′ (h n) (h′ n) (lh n) (lh′ n)) →
  LglR m m′ (M.G.lim (MF.psum m h)) (N.G.lim (NB.psum m′ h′)) (ML.psum-lgl m h lh) (NB.psum-lgl m′ h′ lh′)
psumLglR e hr lr = (λ n → addWkP e dbLc _ _ (hr (suc n))) ,
  accIndR (RR _ _) _ _ (LglR _ _) (λ n d → plusR e d (hr (suc n)))
    (λ n d l → plusLglR e d (hr (suc n)) l (lr (suc n))) (hr zero) (lr zero)

chainLglR : ∀ {j j′} → LR j j′ → ∀ {gk gk′} (hk : ∀ η η′ → RR j j′ η η′ → RR j j′ (gk η) (gk′ η′)) {lk lk′} →
  (∀ η η′ → RR j j′ η η′ → ∀ l l′ → LglR j j′ η η′ l l′ → LglR j j′ (gk η) (gk′ η′) (lk η l) (lk′ η′ l′)) →
  ∀ n → LglR j j′ (MF.chain j gk n) (NB.chain j′ gk′ n) (ML.chain-lgl j gk lk n) (NB.chain-lgl j′ gk′ lk′ n)
chainLglR e hk hl zero = tt
chainLglR e hk hl (suc n) = plusLglR e (chainR e hk n) (hk _ _ (chainR e hk n)) (chainLglR e hk hl n)
  (hl _ _ (chainR e hk n) _ _ (chainLglR e hk hl n))
```

## 3 结点的两行与折叠

```agda
nodeAtLglR : ∀ {T T′ m m′} → LR m m′ → ∀ p p′ → PR m m′ p p′ → ∀ {B B′ b b′} → LgBR {T} {T′} {m} {m′} B B′ b b′ →
  ∀ g g′ br br′ → BrL (MF.lev m p) (NB.lev m′ p′) T T′ g g′ br br′ →
  LglR T T′ (MF.nodeAt m p B g) (NB.nodeAt m′ p′ B′ g′) (ML.nodeAt-lgl m p B b g br) (NB.nodeAt-lgl m′ p′ B′ b′ g′ br′)
nodeAtLglR lz () p′ e lb
nodeAtLglR (ls em) (inj₁ _) (inj₁ _) e lb = lb (inj₁ tt) (inj₁ tt) tt
nodeAtLglR (ls em) (inj₂ p) (inj₂ p′) e lb = nodeAtLglR em p p′ e (λ r r′ q → lb (inj₂ r) (inj₂ r′) q)
nodeAtLglR (ls em) (inj₁ _) (inj₂ _) () lb
nodeAtLglR (ls em) (inj₂ _) (inj₁ _) () lb
nodeAtLglR (ll em) (n , p) (_ , p′) (refl , e) lb = nodeAtLglR (em n) p p′ e (λ r r′ q → lb (n , r) (n , r′) (refl , q))

ΨnLglR : ∀ {m m′} → LR m m′ → ∀ {j j′} → LR j j′ → (w : MF.Way m j) (w′ : NB.Way m′ j′) → WR m m′ w w′ →
  ∀ {gm gm′ gk gk′} hm hm′ → BrL j j′ m m′ gm gm′ hm hm′ →
  (hk : ∀ η η′ → RR j j′ η η′ → RR j j′ (gk η) (gk′ η′)) → ∀ {lk lk′} →
  (∀ η η′ → RR j j′ η η′ → ∀ l l′ → LglR j j′ η η′ l l′ → LglR j j′ (gk η) (gk′ η′) (lk η l) (lk′ η′ l′)) →
  LglR m m′ (MF.Ψn m j w gm gk) (NB.Ψn m′ j′ w′ gm′ gk′) (ML.Ψn-lgl m j w gm gk hm lk) (NB.Ψn-lgl m′ j′ w′ gm′ gk′ hm′ lk′)
ΨnLglR em ej (MF.keep p refl) (NB.keep p′ refl) q hm hm′ br hk hl = nodeAtLglR em p p′ q lgbLc _ _ hm hm′ br
ΨnLglR em ej MF.fold NB.fold q hm hm′ br hk hl =
  (λ n → proj₂ br _ _ _ _ (chainR ej hk (suc n)) _ _ _ _ _ _ (addWkP ej dbLc _ _ (hk _ _ (chainR ej hk n)))) ,
  (λ n → proj₁ br _ _ (chainR ej hk n) _ _ (chainLglR ej hk hl n))
ΨnLglR em ej (MF.keep p _) NB.fold ()
ΨnLglR em ej MF.fold (NB.keep p′ _) ()

ΨNLglR : ∀ {m m′} → LR m m′ → ∀ {k k′} → LR k k′ → ∀ r r′ → PR k k′ r r′ →
  (w : MF.Way m (MF.lev k r)) (w′ : NB.Way m′ (NB.lev k′ r′)) → WR m m′ w w′ → ∀ {gm gm′ gk gk′} hm hm′ →
  BrR k k′ r r′ m m′ gm gm′ hm hm′ →
  (hk : ∀ η η′ → LayRel k k′ r r′ η η′ → RR (MF.lev k r) (NB.lev k′ r′) (gk η) (gk′ η′)) → ∀ {lk lk′} →
  (∀ η η′ → LayRel k k′ r r′ η η′ → ∀ l l′ → LayLgl k k′ r r′ η η′ l l′ →
     LglR (MF.lev k r) (NB.lev k′ r′) (gk η) (gk′ η′) (lk η l) (lk′ η′ l′)) →
  LglR m m′ (MF.ΨN m k r w gm gk) (NB.ΨN m′ k′ r′ w′ gm′ gk′) (ML.ΨN-lgl m k r w gm gk hm lk) (NB.ΨN-lgl m′ k′ r′ w′ gm′ gk′ hm′ lk′)
ΨNLglR em lz () r′ q
ΨNLglR em (ls ek) (inj₁ _) (inj₁ _) q = ΨnLglR em ek
ΨNLglR em (ls ek) (inj₂ r) (inj₂ r′) q = ΨNLglR em ek r r′ q
ΨNLglR em (ls ek) (inj₁ _) (inj₂ _) ()
ΨNLglR em (ls ek) (inj₂ _) (inj₁ _) ()
ΨNLglR em (ll ek) (n , r) (_ , r′) (refl , q) = ΨNLglR em (ek n) r r′ q

ΨLglR : ∀ {m m′} (em : LR m m′) {k k′} {V : MF.Lv k} {V′ : NB.Lv k′} (v : VR V V′) {x x′} (xr : XR m m′ k k′ x x′)
  {ξ ξ′} (d : RR k k′ ξ ξ′) {l l′} → LglR k k′ ξ ξ′ l l′ →
  LglR m m′ (MF.Ψ m V x ξ) (NF.Ψ m′ V′ x′ ξ′) (ML.Ψ-lgl m V x ξ l) (NF.Ψ-lgl m′ V′ x′ ξ′ l′)
ΨLglR em v xr rz lr = tt
ΨLglR em v xr (rs d) lr = succLglR em (ΨR em v xr d) (ΨLglR em v xr d lr)
ΨLglR em v xr (rl d) lr = (λ n → ΨCpP em v xr (d (suc n)) _ _ (proj₁ lr n)) , (λ n → ΨLglR em v xr (d n) (proj₂ lr n))
ΨLglR em v {x} {x′} xr (rc {r = r} {r′ = r′} q h) lr =
  ΨNLglR em (vLR v) r r′ q (x r) (x′ r′) (xr r r′ q) _ _
    ((λ η η′ hr lη lη′ ll → ΨLglR em v xr (h η η′ hr) (proj₁ lr η η′ hr lη lη′ ll)) ,
     (λ η₁ η₁′ η₂ η₂′ hr₂ l₁ l₁′ u u′ l₂ l₂′ eq →
       ΨCpP em v xr (h η₂ η₂′ hr₂) _ _ (proj₂ lr η₁ η₁′ η₂ η₂′ hr₂ l₁ l₁′ u u′ l₂ l₂′ eq)))
    (λ η η′ hr → ΨR (levR (vLR v) r r′ q) v (λ q₁ q₁′ e → cmpR v r r′ q q₁ q₁′ e) (h η η′ hr))
    (λ η η′ hr lη lη′ ll → ΨLglR (levR (vLR v) r r′ q) v (λ q₁ q₁′ e → cmpR v r r′ q q₁ q₁′ e) (h η η′ hr)
       (proj₁ lr η η′ hr lη lη′ ll))
ΨLglR em v0R xr rt lr = succLglR em rt tt
ΨLglR em (vsR v) {x} {x′} xr rt lr = ΨnLglR em (vLR v) (x (inj₁ tt)) (x′ (inj₁ tt)) (xr (inj₁ tt) (inj₁ tt) tt) _ _
  ((λ η η′ hr lη lη′ ll → ΨLglR em v (λ r r′ e → xr (inj₂ r) (inj₂ r′) e) hr ll) ,
   (λ η₁ η₁′ η₂ η₂′ hr₂ l₁ l₁′ u u′ l₂ l₂′ eq → ΨCpP em v (λ r r′ e → xr (inj₂ r) (inj₂ r′) e) hr₂ u u′ eq))
  (λ η η′ hr → ΨR (vLR v) v (λ r r′ e → e) hr) (λ η η′ hr l l′ ll → ΨLglR (vLR v) v (λ r r′ e → e) hr ll)
ΨLglR em (vlR v s) xr rt lr =
  psumLglR em (λ n → ΨR em (v n) (λ r r′ e → xr (n , r) (n , r′) (refl , e)) rt)
    (λ n → ΨLglR em (v n) (λ r r′ e → xr (n , r) (n , r′) (refl , e)) rt tt)
```
