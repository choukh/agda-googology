# 判决的规格: 搬运与 $\approx$-正确性 (底座)

> 底座, 不含记号. 结论写在 [VerdictSpec](VerdictSpec.lagda.md). [InaccThetaEq](InaccThetaEq.lagda.md) 的 `cvp` 要求路径**字面**落在节点层上. 这太窄 ([VerdictSpecEvid](VerdictSpecEvid.lagda.md) 的 `no-cv`, `cv-total→ext`). 这里放宽到 $\approx^\mathsf{B}$, 搬运用 `coe`: 一个不看证据、对层号结构递归的总函数. 字面的情形是特例 (`CV→CVx`, `OK→OKx`, `LvT→x`, `LvG→x`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.VerdictSpecBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; Low; Dn; DnT; at; down; outL; intoL; outD; intoD; Tree; limᵢ; up; Ω; toLv;
   Sim; σ-id; ι; _∘σ_; add; _+_; iter; Verdict; pen; rise)
open import OCF.Align.InaccFloorTree using (Sib; Mode; upM; verdict; chM; module PF)
open import OCF.Align.InaccThetaRel using (module Leaf)
open import OCF.Align.InaccThetaEq using (module Eqv)
```

## §1 `coe`

`coe a b x` 沿 $x$ 的结构把树从层 $a$ 搬到层 $b$. 形状对不上时给 `zero`: 它是总函数, **不要证据**, 证据只用来证明它在 $a\approx^\mathsf{B}b$ 时是对的 (`TL⁺`, `TR⁺`, 在 [VerdictSpecTwo](VerdictSpecTwo.lagda.md)). 参数层是 0 的 `limᴼ` 上分支指标字面不动: 这正是 `o≈` 要的. `coe⁺` 在第 0 层是恒等, 所以 `Bs` 不用任何条件就保持.

```agda
coe⁺ : (a b : Lv) → Ordᴸ a → Ordᴸ b
coe  : (a b : Lv) → Ordᴸ a → Ordᴸ b
coeP : (a b : Lv) (r : Pre a) → Maybe (Σ (Pre b) λ r′ → Ordᴸ (at b r′) → Ordᴸ (at a r))

coe⁺ zero zero x = x
coe⁺ a    b    x = coe a b x

coe a b Tree.zero = Tree.zero
coe a b (Tree.suc x) = Tree.suc (coe a b x)
coe a b (Tree.lim f) = Tree.lim (λ n → coe a b (f n))
coe a b (limᵢ r f) with coeP a b r
... | nothing = Tree.zero
... | just (r′ , back) = limᵢ r′ (λ y → coe a b (f (intoL a r (back (outL b r′ y)))))
coe (suc k) (suc k′) (up _ x) = up tt (coe⁺ k k′ x)
coe (suc k) zero (up _ x) = Tree.zero
coe (suc k) (lim _) (up _ x) = Tree.zero
coe (suc k) (limᴼ _ _) (up _ x) = Tree.zero
coe (lim f) (lim f′) (up n x) = up n (coe⁺ (f n) (f′ n) x)
coe (lim f) zero (up n x) = Tree.zero
coe (lim f) (suc _) (up n x) = Tree.zero
coe (lim f) (limᴼ _ _) (up n x) = Tree.zero
coe (limᴼ zero g) (limᴼ zero g′) (up x y) = up x (coe⁺ (g x) (g′ x) y)
coe (limᴼ k g) (limᴼ k′ g′) (up x y) = up (coe⁺ k k′ x) (coe⁺ (g x) (g′ (coe⁺ k k′ x)) y)
coe (limᴼ k g) zero (up x y) = Tree.zero
coe (limᴼ k g) (suc _) (up x y) = Tree.zero
coe (limᴼ k g) (lim _) (up x y) = Tree.zero

coeP (suc k) (suc k′) (inj₁ _) = just (inj₁ tt , coe⁺ k′ k)
coeP (suc k) (suc k′) (inj₂ r) with coeP k k′ r
... | nothing = nothing
... | just (r′ , b) = just (inj₂ r′ , b)
coeP (lim f) (lim f′) (n , r) with coeP (f n) (f′ n) r
... | nothing = nothing
... | just (r′ , b) = just ((n , r′) , b)
coeP (limᴼ k g) (limᴼ k′ g′) (inj₁ (inj₁ _)) = just (inj₁ (inj₁ tt) , coe⁺ k′ k)
coeP (limᴼ k g) (limᴼ k′ g′) (inj₁ (inj₂ r)) with coeP k k′ r
... | nothing = nothing
... | just (r′ , b) = just (inj₁ (inj₂ r′) , b)
coeP (limᴼ zero g) (limᴼ zero g′) (inj₂ (x , r)) with coeP (g x) (g′ x) r
... | nothing = nothing
... | just (r′ , b) = just (inj₂ (x , r′) , b)
coeP (limᴼ k g) (limᴼ k′ g′) (inj₂ (x , r)) with coeP (g x) (g′ (coe⁺ k k′ x)) r
... | nothing = nothing
... | just (r′ , b) = just (inj₂ (coe⁺ k k′ x , r′) , b)
coeP _ _ _ = nothing
```

## §2 $\approx$-正确性

`BT r b`: 穿透判决的搬运 `b` 是字面的 (`bl`) 或者是 `coe⁺` (`bc`). 其他形状不算正确: 否则任意的 `b` 都能过, 正确性就管不住树了. `bc` 带 `P0`: 参数层都是 0. `coe` 的参数层 $\ge1$ 的子句要 $x\approx$ `coe x`, 而原始的 $x$ 没有这个; [InaccThetaNeg](InaccThetaNeg.lagda.md) 的 `no-Ω₂` 已经说好层号的 `limᴼ` 只能是参数层 0.

```agda
module Eqx (S : Sib) (B₀ : Ordᴸ zero → Set) where
  open Leaf B₀ public
  open PF S public

  P0 : Lv → Set
  P0 zero              = ⊤
  P0 (suc k)           = P0 k
  P0 (lim f)           = ∀ n → P0 (f n)
  P0 (limᴼ zero g)     = ∀ x → Bs zero x → P0 (g x)
  P0 (limᴼ (suc _) _)  = ⊥
  P0 (limᴼ (lim _) _)  = ⊥
  P0 (limᴼ (limᴼ _ _) _) = ⊥

  data BT {j i : Lv} (r : Pre i) : (Ordᴸ (at i r) → Ordᴸ j) → Set where
    bl : (e : at i r ≡ j) → BT r (subst Ordᴸ e)
    bc : P0 (at i r) → P0 j → BT r (coe⁺ (at i r) j)

  data CVx {j i : Lv} : Verdict j i → Set where
    cvp : ∀ (r : Pre i) b → AdmB i r → j ≈ᴮ at i r → BT r b → CVx (pen r b)
    cvr : (∀ (r : Pre i) → AdmB i r → at i r ≈ᴮ j → ⊥) → CVx rise

  OK : (k : Lv) {i : Lv} → Mode k i → Set
  OK zero       m = ⊤
  OK (suc k)    m = (∀ r → AdmB (suc k) r → CVx (verdict S m r)) × OK k (upM (suc k) tt m)
  OK (lim f)    m = (∀ r → AdmB (lim f) r → CVx (verdict S m r)) × (∀ n → OK (f n) (upM (lim f) n m))
  OK (limᴼ k g) m = (∀ r → AdmB (limᴼ k g) r → CVx (verdict S m r)) × (∀ x → Bs k x → OK (g x) (upM (limᴼ k g) x m))

  DB : (k : Lv) → Dn k → Set
  DB (suc _)    _ = ⊤
  DB (lim _)    _ = ⊤
  DB (limᴼ k _) x = Bs k x

  okV : ∀ k {i} (m : Mode k i) → OK k m → ∀ r → AdmB k r → CVx (verdict S m r)
  okV (suc k)    m w = proj₁ w
  okV (lim f)    m w = proj₁ w
  okV (limᴼ k g) m w = proj₁ w

  okU : ∀ k {i} (m : Mode k i) → OK k m → ∀ d → DB k d → OK (down k d) (upM k d m)
  okU (suc k)    m w d _  = proj₂ w
  okU (lim f)    m w d _  = proj₂ w d
  okU (limᴼ k g) m w d db = proj₂ w d db

  Zt : Lv → Set
  Zt i = Σ (Pre i) λ r → AdmB i r × at i r ≡ zero

  ChOK : (k : Lv) → Pre k → Set
  ChOK k r = (at k r ≡ zero) ⊎ (OK k (chM k r) × Zt (at k r))

  rise≠0 : ∀ {i j} → (∀ (r : Pre i) → AdmB i r → at i r ≈ᴮ j → ⊥) → Zt i → j ≡ zero → ⊥
  rise≠0 k (r , d , e) refl = k r d (subst (_≈ᴮ zero) (sym e) z≈)

  Bs-nz : ∀ j → (j ≡ zero → ⊥) → (z : Ordᴸ j) → Bs j z
  Bs-nz zero       n z = ⊥-elim (n refl)
  Bs-nz (suc _)    n z = tt
  Bs-nz (lim _)    n z = tt
  Bs-nz (limᴼ _ _) n z = tt

  Bs-subst : ∀ {a b} (e : a ≡ b) {z : Ordᴸ a} → Bs a z → Bs b (subst Ordᴸ e z)
  Bs-subst refl d = d

  Bs-coe : ∀ {a b} → a ≈ᴮ b → (z : Ordᴸ a) → Bs a z → Bs b (coe⁺ a b z)
  Bs-coe z≈ z d = d
  Bs-coe (s≈ _) z d = tt
  Bs-coe (l≈ _) z d = tt
  Bs-coe (o≈ _) z d = tt

  ≈≡ : ∀ {a a′ b b′} → a ≡ a′ → b ≡ b′ → a′ ≈ᴮ b′ → a ≈ᴮ b
  ≈≡ refl refl e = e

  clash : ∀ {i i′ j j′} → i ≈ᴮ i′ → j ≈ᴮ j′ → (r : Pre i) → j ≈ᴮ at i r → AdmB i r →
          (∀ (r′ : Pre i′) → AdmB i′ r′ → at i′ r′ ≈ᴮ j′ → ⊥) → ⊥
  clash ii jj r e d k with path≈ ii r d
  ... | r′ , d′ , e′ = k r′ d′ (≈ᴮ-trans (≈ᴮ-sym e′) (≈ᴮ-trans (≈ᴮ-sym e) jj))

  LvT : Lv → Set
  LvT zero       = ⊤
  LvT (suc k)    = (∀ r → AdmB (suc k) r → ChOK (suc k) r) × LvT k
  LvT (lim f)    = (∀ r → AdmB (lim f) r → ChOK (lim f) r) × (∀ n → LvT (f n))
  LvT (limᴼ k g) = (∀ r → AdmB (limᴼ k g) r → ChOK (limᴼ k g) r) × LvT k × (∀ x → Bs k x → LvT (g x))

  lvCh : ∀ i → LvT i → ∀ r → AdmB i r → ChOK i r
  lvCh (suc k)    w = proj₁ w
  lvCh (lim f)    w = proj₁ w
  lvCh (limᴼ k g) w = proj₁ w

  lvt-at : ∀ i → LvT i → ∀ r → AdmB i r → LvT (at i r)
  lvt-at (suc k)    w (inj₁ _) _ = proj₂ w
  lvt-at (suc k)    w (inj₂ r) d = lvt-at k (proj₂ w) r d
  lvt-at (lim f)    w (n , r)  d = lvt-at (f n) (proj₂ w n) r d
  lvt-at (limᴼ k g) w (inj₁ (inj₁ _)) _ = proj₁ (proj₂ w)
  lvt-at (limᴼ k g) w (inj₁ (inj₂ r)) d = lvt-at k (proj₁ (proj₂ w)) r d
  lvt-at (limᴼ k g) w (inj₂ (x , r)) (a , d) = lvt-at (g x) (proj₂ (proj₂ w) x a) r d

  LvG : Lv → Set
  LvG zero       = ⊤
  LvG (suc k)    = ChOK (suc k) (inj₁ tt) × LvT k
  LvG (lim f)    = ∀ n → LvG (f n)
  LvG (limᴼ k g) = ChOK (limᴼ k g) (inj₁ (inj₁ tt)) × LvT k × (∀ x → Bs k x → LvG (g x))

  t→g : ∀ i → LvT i → LvG i
  t→g zero       w = tt
  t→g (suc k)    w = proj₁ w (inj₁ tt) tt , proj₂ w
  t→g (lim f)    w = λ n → t→g (f n) (proj₂ w n)
  t→g (limᴼ k g) w = proj₁ w (inj₁ (inj₁ tt)) tt , proj₁ (proj₂ w) , (λ x b → t→g (g x) (proj₂ (proj₂ w) x b))

  ND : (k : Lv) → Pre k → Set
  ND k r = AdmB k r × ChOK k r × LvT (at k r)

  nd-of : ∀ i → LvT i → ∀ r → AdmB i r → ND i r
  nd-of i w r d = d , lvCh i w r d , lvt-at i w r d

  out-into : ∀ k r y → outL k r (intoL k r y) ≡ y
  out-into (suc k)    (inj₁ _) y = refl
  out-into (suc k)    (inj₂ r) y = out-into k r y
  out-into (lim f)    (n , r)  y = out-into (f n) r y
  out-into (limᴼ k g) (inj₁ (inj₁ _)) y = refl
  out-into (limᴼ k g) (inj₁ (inj₂ r)) y = out-into k r y
  out-into (limᴼ k g) (inj₂ (x , r))  y = out-into (g x) r y

  SD : ∀ {k l} → Sim k l → Set
  SD {k} {l} σ = ∀ r → AdmB k r → AdmB l (proj₁ (σ r))

  sd-id : ∀ {k} → SD (σ-id k)
  sd-id r d = d

  sd∘ι : ∀ {l} k d (σ : Sim (k) l) → SD σ → DB k d → SD (σ ∘σ ι k d)
  sd∘ι (suc k) d σ s db r dr with σ (inj₂ r) | s (inj₂ r) dr
  ... | r″ , e′ | d″ = d″
  sd∘ι (lim f) n σ s db r dr with σ (n , r) | s (n , r) dr
  ... | r″ , e′ | d″ = d″
  sd∘ι (limᴼ k g) x σ s db r dr with σ (inj₂ (x , r)) | s (inj₂ (x , r)) (db , dr)
  ... | r″ , e′ | d″ = d″

  chOK : ∀ k r → ChOK k r → (at k r ≡ zero → ⊥) → OK k (chM k r) × Zt (at k r)
  chOK k r (inj₁ z) n = ⊥-elim (n z)
  chOK k r (inj₂ p) n = p
```

## §3 字面的正确性是特例

```agda
  private module O = Eqv S B₀

  CV→CVx : ∀ {j i} {v : Verdict j i} → O.CV v → CVx v
  CV→CVx (O.cvp r refl a) = cvp r _ a (≈ᴮ-refl _) (bl refl)
  CV→CVx (O.cvr k) = cvr k

  OK→OKx : ∀ k {i} (m : Mode k i) → O.OK k m → OK k m
  OK→OKx zero       m w = tt
  OK→OKx (suc k)    m w = (λ r d → CV→CVx (proj₁ w r d)) , OK→OKx k _ (proj₂ w)
  OK→OKx (lim f)    m w = (λ r d → CV→CVx (proj₁ w r d)) , (λ n → OK→OKx (f n) _ (proj₂ w n))
  OK→OKx (limᴼ k g) m w = (λ r d → CV→CVx (proj₁ w r d)) , (λ x b → OK→OKx (g x) _ (proj₂ w x b))

  Ch→x : ∀ k r → O.ChOK k r → ChOK k r
  Ch→x k r (inj₁ e) = inj₁ e
  Ch→x k r (inj₂ (ok , z , _)) = inj₂ (OK→OKx k _ ok , z)

  LvT→x : ∀ k → O.LvT k → LvT k
  LvT→x zero       w = tt
  LvT→x (suc k)    w = (λ r d → Ch→x (suc k) r (proj₁ w r d)) , LvT→x k (proj₂ w)
  LvT→x (lim f)    w = (λ r d → Ch→x (lim f) r (proj₁ w r d)) , (λ n → LvT→x (f n) (proj₂ w n))
  LvT→x (limᴼ k g) w = (λ r d → Ch→x (limᴼ k g) r (proj₁ w r d)) , LvT→x k (proj₁ (proj₂ w)) , (λ x b → LvT→x (g x) (proj₂ (proj₂ w) x b))

  LvG→x : ∀ k → O.LvG k → LvG k
  LvG→x zero       w = tt
  LvG→x (suc k)    w = Ch→x (suc k) (inj₁ tt) (proj₁ w) , LvT→x k (proj₂ w)
  LvG→x (lim f)    w = λ n → LvG→x (f n) (w n)
  LvG→x (limᴼ k g) w = Ch→x (limᴼ k g) (inj₁ (inj₁ tt)) (proj₁ w) , LvT→x k (proj₁ (proj₂ w)) , (λ x b → LvG→x (g x) (proj₂ (proj₂ w) x b))
```
