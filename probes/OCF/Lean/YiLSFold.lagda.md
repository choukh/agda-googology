# 合法块上的统一值模拟: 后继与 ℕ 极限层号上的折叠保持与 `lower`

> 验收文件. 编译定理, 无前提: 对一切由零, 后继, ℕ 极限生成的层号 ℓ (`NL`), 任意证据与路线, 底 B 逐分量不低于标准底 (`OKB`), 参照层号 i 与 ℓ 对应 (`Corr`), 有 `lower : ψ⁰(Ω i) ≼ read (ψ⊥ ℓ ε ρ B (Ωt ℓ))`.
> 证法: `YiLSRel` 的关系族; 沿帧的折叠状态 `St` (仍在折叠, 或已进入上折), 过一帧 `nxt` 对 ℕ 极限层号也有定义: 不同号孩子的两行各是一个状态 (前向一行经 `thru` 走完嵌入的各帧). 主引理 `MS`, 值引理 `VS`.
> 留空: `Ωₗ` 层号的帧 (参照框架没有对应的层号). 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLSFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath hiding (eq; lt; gt; here) renaming (psh to pshP; emb to embP; emb-nz to embP-nz; nxt to nxtₙ)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead
open import OCF.Lean.YiLeanValRel using (TRC)
open import OCF.Lean.YiLSRel

import OCF.Align.Level as L
open L using (_≅ᴵ_; _<ᴵ_; _≺ᴵ_)
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; l≼; ⊑→≼)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using () renaming (iter to iterᴸ)
```

## 底在折叠值之下 (一切层号)

```agda
+ι⊴ : ∀ {j} (b : Tr j) (c : Tr zero) → j ⊢ b ⊴ b + ι j c
+ι⊴ b zero          = ⊴r
+ι⊴ b (suc c)       = ⊴◃ (⊴-◃ (+ι⊴ b c) ◃s)
+ι⊴ b (lim f a)     = ⊴◃ (⊴-◃ (+ι⊴ b (f zero)) (◃l zero))
+ι⊴ b (Ω () _)
+ι⊴ b (up _ () _ _)

Up-⊵ : ∀ {ℓ} (j : LF) (d : Dn ℓ j) (b : Tr ℓ) (nb : ℓ ⊢ zero ◃ b) (y : Tr j) → ℓ ⊢ b ⊴ Up j d b nb y
Up-⊵ j d b nb zero      = ⊴r
Up-⊵ j d b nb (suc y)   = ⊴◃ (⊴-◃ (Up-⊵ j d b nb y) (◃l zero))
Up-⊵ j d b nb (lim f a) = ⊴◃ (⊴-◃ (Up-⊵ j d b nb (f zero)) (◃l zero))
Up-⊵ {ℓ} j d b nb (Ω p g) = ⊴◃ (⊴-◃ (Up-⊵ j d b nb (g (mvBr d p (br0 ℓ (mv d p))))) ◃w)
Up-⊵ (suc a)  d b nb (up y _ y′ _) = ⊴-trans (Up-⊵ (suc a) d b nb y) (Up-⊵ a (down d tt) _ _ y′)
Up-⊵ (lim g)  d b nb (up y n y′ _) = ⊴-trans (Up-⊵ (lim g) d b nb y) (Up-⊵ (g n) (down d n) _ _ y′)
Up-⊵ (Ωₗ k h) d b nb (up y c y′ _) = ⊴-trans (Up-⊵ (Ωₗ k h) d b nb y) (Up-⊵ (h c) (down d c) _ _ y′)
Up-⊵ zero     d b nb (up y () _ _)

Upc-⊵ : (ℓ : LF) (c : Ch ℓ) (b : Tr ℓ) (nb : ℓ ⊢ zero ◃ b) (y : ChT ℓ c) → ℓ ⊢ b ⊴ Upc ℓ c b nb y
Upc-⊵ (suc a)  c b nb y = Up-⊵ a (down stop c) b nb y
Upc-⊵ (lim g)  n b nb y = Up-⊵ (g n) (down stop n) b nb y
Upc-⊵ (Ωₗ k h) c b nb y = Up-⊵ (h c) (down stop c) b nb y

ψ⊥-⊵ : (ℓ : LF) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (x : Tr ℓ) → zero ⊢ b⊥ B ⊴ ψ⊥ ℓ ε ρ B x
ψ⊥-⊵ ℓ ε ρ B zero      = ⊴r
ψ⊥-⊵ ℓ ε ρ B (suc x)   = ⊴◃ (⊴-◃ (ψ⊥-⊵ ℓ ε ρ B x) (◃l zero))
ψ⊥-⊵ ℓ ε ρ B (lim f a) = ⊴◃ (⊴-◃ (ψ⊥-⊵ ℓ ε ρ B (f zero)) (◃l zero))
ψ⊥-⊵ ℓ ε ρ B (Ω p g)   = ⊴◃ (⊴-◃ (ψ⊥-⊵ ℓ ε ρ B (g (br0 ℓ p))) (◃l zero))
ψ⊥-⊵ zero     ε ρ B (up x () y e)
ψ⊥-⊵ (suc a)  ε ρ B (up x _ y e) = ⊴-trans (ψ⊥-⊵ (suc a) ε ρ B x) (ψ⊥-⊵ a ε ρ (dS a ε ρ B x) y)
ψ⊥-⊵ (lim g)  ε (ρc , R) B (up x n y e) =
  ⊴-trans (ψ⊥-⊵ (lim g) ε (ρc , R) B x) (ψ⊥-⊵ (g n) (ε n) (ρc n) (dL g ε (ρc , R) B n x) y)
ψ⊥-⊵ (Ωₗ k h) ε ρ B (up x c y e) =
  ⊴-trans (ψ⊥-⊵ (Ωₗ k h) ε ρ B x) (ψ⊥-⊵ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) y)

ψs-⊵ : (ℓ : LF) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (j : LF) (w : j ≤ ℓ) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr ℓ)
  → j ⊢ β ⊴ ψs ℓ ε ρ B j w β nβ x
ψs-⊵ ℓ ε ρ B j w β nβ zero      = ⊴r
ψs-⊵ ℓ ε ρ B j w β nβ (suc x)   = ⊴◃ (⊴-◃ (ψs-⊵ ℓ ε ρ B j w β nβ x) (◃l zero))
ψs-⊵ ℓ ε ρ B j w β nβ (lim f a) = ⊴◃ (⊴-◃ (ψs-⊵ ℓ ε ρ B j w β nβ (f zero)) (◃l zero))
ψs-⊵ ℓ ε ρ B j w β nβ (Ω p g) =
  kp-ind ℓ ε ρ p w (λ X → j ⊢ β ⊴ X)
    (λ q cv gd → ⊴◃ (⊴-◃ (ψs-⊵ ℓ ε ρ B j w β nβ (g (cv (br0 j q)))) ◃w))
    (⊴◃ (⊴-◃ (ψs-⊵ ℓ ε ρ B j w β nβ (g (br0 ℓ p))) (◃l zero)))
ψs-⊵ ℓ ε ρ B _ self β nβ (up x c y e) =
  ⊴-trans (ψs-⊵ ℓ ε ρ B ℓ self β nβ x) (Upc-⊵ ℓ c _ _ y)
ψs-⊵ (suc a) ε ρ B j (ins w) β nβ (up x _ y e) =
  ⊴-trans (ψs-⊵ (suc a) ε ρ B j (ins w) β nβ x) (ψs-⊵ a ε ρ (dS a ε ρ B x) j w _ _ y)
ψs-⊵ (lim g) ε (ρc , R) B j (inl n w) β nβ (up x m y e) =
  caseW-ind (λ Z → j ⊢ β ⊴ Z) (way g R m n)
    (λ v → ⊴-trans (ψs-⊵ (lim g) ε (ρc , R) B j (inl n w) β nβ x)
             (ψs-⊵ (g n) (ε n) (ρc n) (dL g ε (ρc , R) B n x) j w _ _ (embP (g n) (ε n) v y e)))
    (λ v → ⊴-trans (ψs-⊵ (lim g) ε (ρc , R) B j (inl n w) β nβ x)
             (ψs-⊵ (g m) (ε m) (ρc m) (dL g ε (ρc , R) B m x) j (w ∙ v) _ _ y))
ψs-⊵ (lim g) ε (ρc , R) B j (inlu ws) β nβ (up x m y e) =
  ⊴-trans (ψs-⊵ (lim g) ε (ρc , R) B j (inlu ws) β nβ x)
    (ψs-⊵ (g m) (ε m) (ρc m) (dL g ε (ρc , R) B m x) j (ws m) _ _ y)
ψs-⊵ (Ωₗ k h) ε ρ B j (ink w) β nβ (up x c y e) =
  ⊴-trans (ψs-⊵ (Ωₗ k h) ε ρ B j (ink w) β nβ x)
    (ψs-⊵ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) j (w ∙ proj₁ (proj₂ ε c)) _ _ y)
ψs-⊵ (Ωₗ k h) ε ρ B j (inu ws) β nβ (up x c y e) =
  ⊴-trans (ψs-⊵ (Ωₗ k h) ε ρ B j (inu ws) β nβ x)
    (ψs-⊵ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) j (ws c) _ _ y)
ψs-⊵ (Ωₗ k h) ε ρ B j (inb c′ w) β nβ (up x c y e) =
  ⊴-trans (ψs-⊵ (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) (+ι⊴ _ _)
```

底的条件: 逐分量不低于标准底. 对孩子的底封闭.

```agda
OKB : (ℓ : LF) → Base ℓ → Set
OKB ℓ B = (zero ⊢ suc zero ⊴ b⊥ B) × ((j : LF) (w : j ≤ ℓ) → j ⊢ Ωt j ⊴ bs B j w)

ok-B₀ : (ℓ : LF) → OKB ℓ (B₀ ℓ)
ok-B₀ ℓ = ⊴r , λ j w → ⊴r

ok-dS : ∀ {a} (ε : Ev (suc a)) (ρ : Rt (suc a)) (B : Base (suc a)) → OKB (suc a) B → (t : Tr (suc a))
  → OKB a (dS a ε ρ B t)
ok-dS {a} ε ρ B ok t = ⊴-trans (proj₁ ok) (ψ⊥-⊵ (suc a) ε ρ B t)
  , λ j w → ⊴-trans (proj₂ ok j (ins w)) (ψs-⊵ (suc a) ε ρ B j (ins w) _ _ t)

ok-dL : (g : ℕ → LF) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) → OKB (lim g) B → (n : ℕ) (t : Tr (lim g))
  → OKB (g n) (dL g ε ρ B n t)
ok-dL g ε ρ B ok n t = ⊴-trans (proj₁ ok) (ψ⊥-⊵ (lim g) ε ρ B t)
  , λ j w → ⊴-trans (proj₂ ok j (inl n w)) (ψs-⊵ (lim g) ε ρ B j (inl n w) _ _ t)
```

## 层号事实

`NL`: 只含零, 后继, ℕ 极限的层号. 槽位的层号严格低于所在层号 (`POS`, ℕ 极限处用 `Corr` 带的严格步进); 路径的起点不高于终点 (`notBelow`).

```agda
data NL : LF → Set where
  n0 : NL zero
  n+ : ∀ {a} → NL a → NL (suc a)
  nω : ∀ {g} → ((n : ℕ) → NL (g n)) → NL (lim g)

nlW : ∀ {j ℓ} → j ≤ ℓ → NL ℓ → NL j
nlW self      f      = f
nlW (ins w)   (n+ f) = nlW w f
nlW (inl n w) (nω f) = nlW w (f n)
nlW (inlu ws) (nω f) = nlW (ws zero) (f zero)
nlW (ink w)   ()
nlW (inb c w) ()
nlW (inu ws)  ()

mutual
  nl-at : ∀ {ℓ} → NL ℓ → (p : Pos ℓ) → NL (at ℓ p)
  nl-at (n+ f) t       = nl-at⁼ f t
  nl-at (nω f) (n , t) = nl-at⁼ (f n) t

  nl-at⁼ : ∀ {a} → NL a → (t : Pos⁼ a) → NL (at⁼ a t)
  nl-at⁼ f (inj₁ _) = f
  nl-at⁼ f (inj₂ p) = nl-at f p

POS : ∀ {m} → NL m → (s : Pos m) → ∀ {j i} → Corr j (at m s) → Corr i m → j ≺ᴵ i
POS (n+ f) (inj₁ _)     cj (cs c)    = L.via (Corr-uniq cj c) L.zero
POS (n+ f) (inj₂ r)     cj (cs c)    = L.≺-suc (POS f r cj c)
POS (nω f) (n , inj₁ _) cj (cl c st) = L.≺-lim (suc n) (L.≺ᴵ-respˡ (Corr-uniq cj (c n)) (st n))
POS (nω f) (n , inj₂ r) cj (cl c st) = L.≺-lim n (POS (f n) r cj (c n))

notBelow : ∀ {j a} (w : j ≤ a) → NL a → ∀ {i i′} → Corr i j → Corr i′ a → ¬ (i′ ≺ᴵ i)
notBelow self      f      ci ci′        bl = L.≺ᴵ-irrefl (L.≺ᴵ-respˡ (Corr-uniq ci ci′) bl)
notBelow (ins w)   (n+ f) ci (cs ci″)   bl =
  notBelow w f ci ci″ (L.≺ᴵ-trans (L.via (L.≅ᴵ-refl _) L.zero) bl)
notBelow (inl n w) (nω f) ci (cl c st)  bl =
  notBelow w (f n) ci (c n) (L.≺ᴵ-trans (L.≺-lim (suc n) (st n)) bl)
notBelow (inlu ws) (nω f) ci (cl c st)  bl =
  notBelow (ws zero) (f zero) ci (c zero) (L.≺ᴵ-trans (L.≺-lim (suc zero) (st zero)) bl)
notBelow (ink w)   ()
notBelow (inb c w) ()
notBelow (inu ws)  ()
```

## 保留判定

槽位沿路径搬进高层 (`pshP`) 不改它的层号, 槽位关系逐情形是恒等.

```agda
psh-at : ∀ {k a} (v : k ≤ a) (t : Pos⁼ k) → at⁼ a (pshP v t) ≡ at⁼ k t
psh-at self      t = refl
psh-at (ins v)   t = psh-at v t
psh-at (inl n v) t = psh-at v t
psh-at (inlu vs) t = psh-at (vs zero) t
psh-at (ink v)   t = psh-at v t
psh-at (inb c v) t = psh-at v t
psh-at (inu vs)  t = psh-at (vs zero) t

psh-rel : ∀ {k a} (v : k ≤ a) (t : Pos⁼ k) → ∀ {i} {y : L.Ordᶜ i} {z : Br⁼ a (pshP v t)}
  → RelP⁼ a (pshP v t) y z → RelP⁼ k t y (pshBr v t z)
psh-rel self      t r = r
psh-rel (ins v)   t r = psh-rel v t r
psh-rel (inl n v) t r = psh-rel v t r
psh-rel (inlu vs) t r = psh-rel (vs zero) t r
psh-rel (ink v)   t r = psh-rel v t r
psh-rel (inb c v) t r = psh-rel v t r
psh-rel (inu vs)  t r = psh-rel (vs zero) t r

record Keep (lv : LF) (BrT : Set) (RP : ∀ {i} → L.Ordᶜ i → BrT → Set)
            (j : LF) (q : Pos j) (cv : Br j q → BrT) : Set where
  field
    lev   : at j q ≡ lv
    conv  : ∀ {i} {y : L.Ordᶜ i} {c : Br j q} → RelP j q y c → RP y (cv c)
    below : ∀ {i′ i} → Corr i′ lv → Corr i j → i′ ≺ᴵ i

Dflt : LF → LF → Set
Dflt lv j = ∀ {i′ i} → Corr i′ lv → Corr i j → ¬ (i′ ≺ᴵ i)

keep-psh : ∀ {k a} (v : k ≤ a) (t : Pos⁼ k) {j : LF} {q : Pos j} {cv : Br j q → Br⁼ a (pshP v t)}
  → Keep (at⁼ a (pshP v t)) (Br⁼ a (pshP v t)) (RelP⁼ a (pshP v t)) j q cv
  → Keep (at⁼ k t) (Br⁼ k t) (RelP⁼ k t) j q (λ z → pshBr v t (cv z))
keep-psh v t kf = record
  { lev   = trans (Keep.lev kf) (psh-at v t)
  ; conv  = λ r → psh-rel v t (Keep.conv kf r)
  ; below = λ ci′ ci → Keep.below kf (subst (Corr _) (sym (psh-at v t)) ci′) ci }

dflt-psh : ∀ {k a} (v : k ≤ a) (t : Pos⁼ k) {j : LF} → Dflt (at⁼ a (pshP v t)) j → Dflt (at⁼ k t) j
dflt-psh v t df ci′ ci = df (subst (Corr _) (sym (psh-at v t)) ci′) ci

mutual
  kpF : ∀ {ℓ} (f : NL ℓ) (ε : Ev ℓ) (ρ : Rt ℓ) (p : Pos ℓ) {j : LF} (w : j ≤ ℓ) {X : Set} (R : X → Set)
    {K : (q : Pos j) → (Br j q → Br ℓ p) → X} {d : X}
    → ((q : Pos j) (cv : Br j q → Br ℓ p) → Keep (at ℓ p) (Br ℓ p) (RelP ℓ p) j q cv → R (K q cv))
    → (Dflt (at ℓ p) j → R d) → R (kp ℓ ε ρ p w K d)
  kpF f ε ρ p self R hk hd =
    hk p (λ z → z) (record { lev = refl ; conv = λ r → r ; below = λ cj ci → POS f p cj ci })
  kpF (n+ f) ε ρ p (ins w) R hk hd = kpF⁼ f ε ρ p w R hk hd
  kpF {ℓ = lim g} (nω f) ε (ρc , Rr) (m , p) (inl n w) R hk hd =
    caseW-ind R (way g Rr m n)
      (λ v → kpF⁼ (f n) (ε n) (ρc n) (pshP v p) w R
        (λ q cv kf → hk q (λ z → pshBr v p (cv z)) (keep-psh v p kf))
        (λ df → hd (dflt-psh v p df)))
      (λ v → kpF⁼ (f m) (ε m) (ρc m) p (w ∙ v) R hk hd)
  kpF (nω f) ε (ρc , Rr) (m , p) (inlu ws) R hk hd = kpF⁼ (f m) (ε m) (ρc m) p (ws m) R hk hd

  kpF⁼ : ∀ {a} (f : NL a) (ε : Ev a) (ρ : Rt a) (p : Pos⁼ a) {j : LF} (w : j ≤ a) {X : Set} (R : X → Set)
    {K : (q : Pos j) → (Br j q → Br⁼ a p) → X} {d : X}
    → ((q : Pos j) (cv : Br j q → Br⁼ a p) → Keep (at⁼ a p) (Br⁼ a p) (RelP⁼ a p) j q cv → R (K q cv))
    → (Dflt (at⁼ a p) j → R d) → R (kp⁼ a ε ρ p w K d)
  kpF⁼ f ε ρ (inj₁ _) w R hk hd = hd (λ ci′ ci → notBelow w f ci ci′)
  kpF⁼ f ε ρ (inj₂ p) w R hk hd = kpF f ε ρ p w R hk hd
```

## 槽位关系的换型

```agda
at-chP : (j : LF) (c : Ch j) (p : Pos (chL j c)) → at j (chP j c p) ≡ at (chL j c) p
at-chP (suc a)  _ p = refl
at-chP (lim g)  n p = refl
at-chP (Ωₗ k h) c p = refl

at-mv : ∀ {j jd} (d : Dn j jd) (p : Pos jd) → at j (mv d p) ≡ at jd p
at-mv stop            p = refl
at-mv (down {j = j′} d c) p = trans (at-mv d (chP j′ c p)) (at-chP j′ c p)

chRel : (j : LF) (c : Ch j) (p : Pos (chL j c)) → ∀ {i} {y : L.Ordᶜ i} {z : Br j (chP j c p)}
  → RelP j (chP j c p) y z → RelP (chL j c) p y (chBr j c p z)
chRel (suc a)  _ p r = r
chRel (lim g)  n p r = r
chRel (Ωₗ k h) c p r = r

mvRel : ∀ {j jd} (d : Dn j jd) (p : Pos jd) → ∀ {i} {y : L.Ordᶜ i} {z : Br j (mv d p)}
  → RelP j (mv d p) y z → RelP jd p y (mvBr d p z)
mvRel stop            p r = r
mvRel (down {j = j′} d c) p r = chRel j′ c p (mvRel d (chP j′ c p) r)

toSl : (ℓ : LF) {jd : LF} (d : Dc ℓ jd) (p : Pos jd) → ∀ {i} {y : L.Ordᶜ i} {c : Br jd p}
  → RelP jd p y c → SlOf ℓ d p y c
toSl ℓ        []       p r = r
toSl zero     (() ∷ d) p r
toSl (suc a)  (_ ∷ d)  p r = toSl a d p r
toSl (lim g)  (n ∷ d)  p r = toSl (g n) d p r
toSl (Ωₗ k h) (c ∷ d)  p r = toSl (h c) d p r

mutual
  relFrom : (ℓ : LF) (p : Pos ℓ) → ∀ {i} {y : L.Ordᶜ i} {c : Tr (at ℓ p)}
    → Rel (at ℓ p) y c → RelP ℓ p y (fromBr ℓ p c)
  relFrom (suc a)  t              r = relFrom⁼ a t r
  relFrom (lim g)  (n , t)        r = relFrom⁼ (g n) t r
  relFrom (Ωₗ k h) (inj₁ t)       r = relFrom⁼ k t r
  relFrom (Ωₗ k h) (inj₂ (c , t)) r = relFrom⁼ (h c) t r

  relFrom⁼ : (a : LF) (p : Pos⁼ a) → ∀ {i} {y : L.Ordᶜ i} {c : Tr (at⁼ a p)}
    → Rel (at⁼ a p) y c → RelP⁼ a p y (fromBr⁼ a p c)
  relFrom⁼ a (inj₁ _) r = r
  relFrom⁼ a (inj₂ p) r = relFrom a p r

Rel-⊴ : ∀ {j k} {X : L.Ordᶜ k} {t t′ : Tr j} → Rel j X t → j ⊢ t ⊴ t′ → Rel j X t′
Rel-⊴ r ⊴r     = r
Rel-⊴ r (⊴◃ d) = wk r d
```

## 起点

ℕ 极限层号: 参照的 Ω 是各孩子层的 Ω 的提升的极限, 块的 Ω 树第 n 项是前缀上嵌入第 n 个孩子层的 Ω 树.

```agda
START : ∀ {m i} → NL m → Corr i m → Rel m (L.Ω i) (Ωt m)
START n0     cz     = ss zr
START (n+ f) (cs c) = nd c (λ y₀ c₀ sl → ur (psh {Γ = []} (wk (emb zero sl) ◃s)))
START {m = lim g} (nω f) (cl c st) = ll (λ n → ul n (wk (go n (c n)) (◃l n)))
  where
  go : ∀ n {i} → Corr i (g n) → Rel (lim g) (L.Ω i) (cumΩ g n)
  go zero    ci = psh {Γ = []} (embL zero zero (START (f zero) ci))
  go (suc n) ci = psh {Γ = []} (embL (cumΩ g n) (suc n) (START (f (suc n)) ci))
```

## 沿帧的折叠状态

`fo C w β nβ`: 深层仍在按配置 C (证据, 路线, 底) 折到目标 (路径 w, 目标上的底 β); `uf d b nb`: 目标已是某个祖先层自身, 深层在上折.
`nxt` 是过一帧. ℕ 极限层的帧 (孩子 m), 目标 `inl n w`: 按 `way` 分两种, 后向一行仍是 `fo` (路径 w ∙ v, 目标上的底不再是底的分量, 所以状态单带 β); 前向一行是在孩子 n 的配置上走完嵌入 `embP … v` 的各帧 (`thru`).

```agda
Cfg : LF → Set
Cfg ℓ = Ev ℓ × Rt ℓ × Base ℓ

data St (j jd : LF) : Set where
  fo : Cfg jd → j ≤ jd → (β : Tr j) → j ⊢ zero ◃ β → St j jd
  uf : Dn j jd → (b : Tr j) → j ⊢ zero ◃ b → St j jd

run : ∀ {j jd} → St j jd → Tr jd → Tr j
run {j} {jd} (fo (ε , ρ , B) w β nβ) y = ψs jd ε ρ B j w β nβ y
run {j} {jd} (uf d b nb)             y = Up jd d b nb y

run-nz : ∀ {j jd} (s : St j jd) (y : Tr jd) → j ⊢ zero ◃ run s y
run-nz {j} {jd} (fo (ε , ρ , B) w β nβ) y = nzs jd ε ρ B j w β nβ y
run-nz {j} {jd} (uf d b nb)             y = Up-nz jd d b nb y

run-mono : ∀ {j jd} (s : St j jd) {y y′ : Tr jd} → jd ⊢ y ◃ y′ → j ⊢ run s y ◃ run s y′
run-mono {j} {jd} (fo (ε , ρ , B) w β nβ) e = monos jd ε ρ B j w β nβ e
run-mono {j} {jd} (uf d b nb)             e = Up-mono jd d b nb e

stβ : ∀ {j jd} → St j jd → Tr j
stβ (fo C w β nβ) = β
stβ (uf d b nb)   = b

run-⊵ : ∀ {j jd} (s : St j jd) (y : Tr jd) → j ⊢ stβ s ⊴ run s y
run-⊵ {j} {jd} (fo (ε , ρ , B) w β nβ) y = ψs-⊵ jd ε ρ B j w β nβ y
run-⊵ {j} {jd} (uf d b nb)             y = Up-⊵ jd d b nb y

can : ∀ {j a} → Cfg a → j ≤ a → St j a
can {j} (ε , ρ , B) w = fo (ε , ρ , B) w (bs B j w) (ns B j w)

mutual
  nxt : ∀ {jd} → NL jd → ∀ {j} → St j jd → Tr jd → (c : Ch jd) → St j (chL jd c)
  nxt n0 s t ()
  nxt (n+ {a} f) (fo (ε , ρ , B) self β nβ) t c =
    uf (down stop c) (ψs (suc a) ε ρ B (suc a) self β nβ t) (nzs (suc a) ε ρ B (suc a) self β nβ t)
  nxt (n+ {a} f) {j} (fo (ε , ρ , B) (ins w) β nβ) t c =
    fo (ε , ρ , dS a ε ρ B t) w (ψs (suc a) ε ρ B j (ins w) β nβ t) (nzs (suc a) ε ρ B j (ins w) β nβ t)
  nxt (n+ {a} f) (uf d b nb) t c = uf (down d c) (Up (suc a) d b nb t) (Up-nz (suc a) d b nb t)
  nxt (nω {g} f) (fo (ε , ρ , B) self β nβ) t m =
    uf (down stop m) (ψs (lim g) ε ρ B (lim g) self β nβ t) (nzs (lim g) ε ρ B (lim g) self β nβ t)
  nxt (nω {g} f) {j} (fo (ε , ρ , B) (inlu ws) β nβ) t m =
    fo (ε m , proj₁ ρ m , dL g ε ρ B m t) (ws m)
       (ψs (lim g) ε ρ B j (inlu ws) β nβ t) (nzs (lim g) ε ρ B j (inlu ws) β nβ t)
  nxt (nω {g} f) {j} (fo (ε , ρ , B) (inl n w) β nβ) t m =
    nxtW f (ε , ρ , B) t m n (way g (proj₂ ρ) m n) w
      (ψs (lim g) ε ρ B j (inl n w) β nβ t) (nzs (lim g) ε ρ B j (inl n w) β nβ t)
  nxt (nω {g} f) (uf d b nb) t m = uf (down d m) (Up (lim g) d b nb t) (Up-nz (lim g) d b nb t)

  nxtW : ∀ {g} (f : (n : ℕ) → NL (g n)) (C : Cfg (lim g)) (t : Tr (lim g)) (m n : ℕ) → Way g m n
    → ∀ {j} (w : j ≤ g n) (β′ : Tr j) → j ⊢ zero ◃ β′ → St j (g m)
  nxtW {g} f (ε , ρ , B) t m n (fwd v) w β′ nβ′ = thru (f n) v (fo (ε n , proj₁ ρ n , dL g ε ρ B n t) w β′ nβ′)
  nxtW {g} f (ε , ρ , B) t m n (bwd v) w β′ nβ′ = fo (ε m , proj₁ ρ m , dL g ε ρ B m t) (w ∙ v) β′ nβ′

  thru : ∀ {a} → NL a → ∀ {k} → k ≤ a → ∀ {j} → St j a → St j k
  thru f      self      s = s
  thru (n+ f) (ins v)   s = thru f v (nxt (n+ f) s zero tt)
  thru (nω f) (inl n v) s = thru (f n) v (nxt (nω f) s zero n)
  thru (nω f) (inlu vs) s = thru (f zero) (vs zero) (nxt (nω f) s zero zero)
  thru ()     (ink v)   s
  thru ()     (inb c v) s
  thru ()     (inu vs)  s
```

过一帧与折叠的嵌入行一致 (`run-up`); 前向一行: 折叠在嵌入后的树上的值就是 `thru` 之后的状态在原树上的值 (`run-thru`).

```agda
mutual
  run-up : ∀ {jd} (f : NL jd) {j} (s : St j jd) (t : Tr jd) (c : Ch jd) (y : ChT jd c) (e : RCh jd c (chZ jd c) y)
    → run s (up t c y e) ≡ run (nxt f s t c) (chT jd c y)
  run-up n0 s t () y e
  run-up (n+ f) (fo (ε , ρ , B) self β nβ)    t c y e = refl
  run-up (n+ f) (fo (ε , ρ , B) (ins w) β nβ) t c y e = refl
  run-up (n+ f) (uf d b nb)                   t c y e = refl
  run-up (nω f) (fo (ε , ρ , B) self β nβ)      t m y e = refl
  run-up (nω f) (fo (ε , ρ , B) (inlu ws) β nβ) t m y e = refl
  run-up (nω {g} f) {j} (fo (ε , ρ , B) (inl n w) β nβ) t m y e =
    run-upW f ε ρ B t m n (way g (proj₂ ρ) m n) w
      (ψs (lim g) ε ρ B j (inl n w) β nβ t) (nzs (lim g) ε ρ B j (inl n w) β nβ t) y e
  run-up (nω f) (uf d b nb)                     t m y e = refl

  run-upW : ∀ {g} (f : (n : ℕ) → NL (g n)) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (t : Tr (lim g))
    (m n : ℕ) (W : Way g m n) {j : LF} (w : j ≤ g n) (β′ : Tr j) (nβ′ : j ⊢ zero ◃ β′)
    (y : Tr (g m)) (e : g m ⊢ zero ◃ y)
    → caseW W (λ v → ψs (g n) (ε n) (proj₁ ρ n) (dL g ε ρ B n t) j w β′ nβ′ (embP (g n) (ε n) v y e))
              (λ v → ψs (g m) (ε m) (proj₁ ρ m) (dL g ε ρ B m t) j (w ∙ v) β′ nβ′ y)
      ≡ run (nxtW f (ε , ρ , B) t m n W w β′ nβ′) y
  run-upW {g} f ε ρ B t m n (fwd v) w β′ nβ′ y e =
    run-thru (f n) (ε n) v (fo (ε n , proj₁ ρ n , dL g ε ρ B n t) w β′ nβ′) y e
  run-upW f ε ρ B t m n (bwd v) w β′ nβ′ y e = refl

  run-thru : ∀ {a} (f : NL a) (ε : Ev a) {k} (v : k ≤ a) {j} (s : St j a) (y : Tr k) (nz : k ⊢ zero ◃ y)
    → run s (embP a ε v y nz) ≡ run (thru f v s) y
  run-thru f      ε self      s y nz = refl
  run-thru (n+ {a} f) ε (ins v) s y nz =
    trans (run-up (n+ f) s zero tt (embP a ε v y nz) (embP-nz a ε v y nz))
          (run-thru f ε v (nxt (n+ f) s zero tt) y nz)
  run-thru (nω {g} f) ε (inl n v) s y nz =
    trans (run-up (nω f) s zero n (embP (g n) (ε n) v y nz) (embP-nz (g n) (ε n) v y nz))
          (run-thru (f n) (ε n) v (nxt (nω f) s zero n) y nz)
  run-thru (nω {g} f) ε (inlu vs) s y nz =
    trans (run-up (nω f) s zero zero (embP (g zero) (ε zero) (vs zero) y nz) (embP-nz (g zero) (ε zero) (vs zero) y nz))
          (run-thru (f zero) (ε zero) (vs zero) (nxt (nω f) s zero zero) y nz)
  run-thru ()     ε (ink v)   s y nz
  run-thru ()     ε (inb c v) s y nz
  run-thru ()     ε (inu vs)  s y nz
```

过一帧不降.

```agda
mutual
  nxtβ : ∀ {jd} (f : NL jd) {j} (s : St j jd) (t : Tr jd) (c : Ch jd) → j ⊢ run s t ⊴ stβ (nxt f s t c)
  nxtβ n0 s t ()
  nxtβ (n+ f) (fo (ε , ρ , B) self β nβ)    t c = ⊴r
  nxtβ (n+ f) (fo (ε , ρ , B) (ins w) β nβ) t c = ⊴r
  nxtβ (n+ f) (uf d b nb)                   t c = ⊴r
  nxtβ (nω f) (fo (ε , ρ , B) self β nβ)      t m = ⊴r
  nxtβ (nω f) (fo (ε , ρ , B) (inlu ws) β nβ) t m = ⊴r
  nxtβ (nω {g} f) (fo (ε , ρ , B) (inl n w) β nβ) t m = nxtWβ f (ε , ρ , B) t m n (way g (proj₂ ρ) m n) w _ _
  nxtβ (nω f) (uf d b nb)                     t m = ⊴r

  nxtWβ : ∀ {g} (f : (n : ℕ) → NL (g n)) (C : Cfg (lim g)) (t : Tr (lim g)) (m n : ℕ) (W : Way g m n)
    {j : LF} (w : j ≤ g n) (β′ : Tr j) (nβ′ : j ⊢ zero ◃ β′) → j ⊢ β′ ⊴ stβ (nxtW f C t m n W w β′ nβ′)
  nxtWβ {g} f (ε , ρ , B) t m n (fwd v) w β′ nβ′ = thruβ (f n) v (fo (ε n , proj₁ ρ n , dL g ε ρ B n t) w β′ nβ′)
  nxtWβ f (ε , ρ , B) t m n (bwd v) w β′ nβ′ = ⊴r

  thruβ : ∀ {a} (f : NL a) {k} (v : k ≤ a) {j} (s : St j a) → j ⊢ stβ s ⊴ stβ (thru f v s)
  thruβ f      self      s = ⊴r
  thruβ (n+ f) (ins v)   s =
    ⊴-trans (⊴-trans (run-⊵ s zero) (nxtβ (n+ f) s zero tt)) (thruβ f v (nxt (n+ f) s zero tt))
  thruβ (nω f) (inl n v) s =
    ⊴-trans (⊴-trans (run-⊵ s zero) (nxtβ (nω f) s zero n)) (thruβ (f n) v (nxt (nω f) s zero n))
  thruβ (nω f) (inlu vs) s =
    ⊴-trans (⊴-trans (run-⊵ s zero) (nxtβ (nω f) s zero zero)) (thruβ (f zero) (vs zero) (nxt (nω f) s zero zero))
  thruβ ()     (ink v)   s
  thruβ ()     (inb c v) s
  thruβ ()     (inu vs)  s

nxt-⊵ : ∀ {jd} (f : NL jd) {j} (s : St j jd) (t : Tr jd) (c : Ch jd) (y : Tr (chL jd c))
  → j ⊢ run s t ⊴ run (nxt f s t c) y
nxt-⊵ f s t c y = ⊴-trans (nxtβ f s t c) (run-⊵ (nxt f s t c) y)
```

状态里的底满足 `OKB`, 过一帧保持.

```agda
OKst : ∀ {j jd} → St j jd → Set
OKst {jd = jd} (fo (ε , ρ , B) w β nβ) = OKB jd B
OKst (uf d b nb)                       = ⊤

mutual
  ok-nxt : ∀ {jd} (f : NL jd) {j} (s : St j jd) (t : Tr jd) (c : Ch jd) → OKst s → OKst (nxt f s t c)
  ok-nxt n0 s t ()
  ok-nxt (n+ f) (fo (ε , ρ , B) self β nβ)    t c ok = tt
  ok-nxt (n+ f) (fo (ε , ρ , B) (ins w) β nβ) t c ok = ok-dS ε ρ B ok t
  ok-nxt (n+ f) (uf d b nb)                   t c ok = tt
  ok-nxt (nω f) (fo (ε , ρ , B) self β nβ)      t m ok = tt
  ok-nxt (nω {g} f) (fo (ε , ρ , B) (inlu ws) β nβ) t m ok = ok-dL g ε ρ B ok m t
  ok-nxt (nω {g} f) (fo (ε , ρ , B) (inl n w) β nβ) t m ok =
    ok-nxtW f (ε , ρ , B) ok t m n (way g (proj₂ ρ) m n) w _ _
  ok-nxt (nω f) (uf d b nb)                     t m ok = tt

  ok-nxtW : ∀ {g} (f : (n : ℕ) → NL (g n)) (C : Cfg (lim g)) → OKB (lim g) (proj₂ (proj₂ C)) → (t : Tr (lim g))
    (m n : ℕ) (W : Way g m n) {j : LF} (w : j ≤ g n) (β′ : Tr j) (nβ′ : j ⊢ zero ◃ β′)
    → OKst (nxtW f C t m n W w β′ nβ′)
  ok-nxtW {g} f (ε , ρ , B) ok t m n (fwd v) w β′ nβ′ =
    ok-thru (f n) v (fo (ε n , proj₁ ρ n , dL g ε ρ B n t) w β′ nβ′) (ok-dL g ε ρ B ok n t)
  ok-nxtW {g} f (ε , ρ , B) ok t m n (bwd v) w β′ nβ′ = ok-dL g ε ρ B ok m t

  ok-thru : ∀ {a} (f : NL a) {k} (v : k ≤ a) {j} (s : St j a) → OKst s → OKst (thru f v s)
  ok-thru f      self      s ok = ok
  ok-thru (n+ f) (ins v)   s ok = ok-thru f v (nxt (n+ f) s zero tt) (ok-nxt (n+ f) s zero tt ok)
  ok-thru (nω f) (inl n v) s ok = ok-thru (f n) v (nxt (nω f) s zero n) (ok-nxt (nω f) s zero n ok)
  ok-thru (nω f) (inlu vs) s ok =
    ok-thru (f zero) (vs zero) (nxt (nω f) s zero zero) (ok-nxt (nω f) s zero zero ok)
  ok-thru ()     (ink v)   s ok
  ok-thru ()     (inb c v) s ok
  ok-thru ()     (inu vs)  s ok
```

## 换目标

状态变换 Φ 若把某个 `fo` 状态送到配置 C′ 上的 `fo` 状态, 则 C′ 上任何目标的标准状态都是 Φ 在某个标准状态上的值 (`Gd`). 过一帧, `thru`, 沿上下文都满足; 链步的折叠 (配置 C′, 目标是槽位的层) 由此接回顶层的某条目标路径.

```agda
cfgOf : ∀ {j jd} → St j jd → Maybe (Cfg jd)
cfgOf (fo C w β nβ) = just C
cfgOf (uf d b nb)   = nothing

no-nj : ∀ {A Z : Set} {x : A} → nothing ≡ just x → Z
no-nj ()

record Gd {a k : LF} (Φ : ∀ {j} → St j a → St j k) : Set where
  field
    g-uf : ∀ {j} (s : St j a) → cfgOf s ≡ nothing → cfgOf (Φ s) ≡ nothing
    g-fo : ∀ {j} (C : Cfg a) (w : j ≤ a) (β : Tr j) (nβ : j ⊢ zero ◃ β) {C′ : Cfg k}
         → cfgOf (Φ (fo C w β nβ)) ≡ just C′
         → ∀ {j₁} (w₁ : j₁ ≤ k) → Σ (j₁ ≤ a) (λ w₂ → Φ (can C w₂) ≡ can C′ w₁)
open Gd

good-id : ∀ {a} → Gd {a} {a} (λ s → s)
good-id = record { g-uf = λ s e → e ; g-fo = λ { C w β nβ refl w₁ → w₁ , refl } }

good-∘ : ∀ {a k k′} {Φ : ∀ {j} → St j a → St j k} {Ψ : ∀ {j} → St j k → St j k′}
  → Gd Φ → Gd Ψ → Gd (λ s → Ψ (Φ s))
good-∘ {a} {k} {k′} {Φ} {Ψ} GΦ GΨ = record { g-uf = λ s e → g-uf GΨ (Φ s) (g-uf GΦ s e) ; g-fo = gf }
  where
  aux : ∀ {j} (C : Cfg a) (w : j ≤ a) (β : Tr j) (nβ : j ⊢ zero ◃ β) {C″ : Cfg k′}
    (s′ : St j k) → Φ (fo C w β nβ) ≡ s′ → cfgOf (Ψ s′) ≡ just C″
    → ∀ {j₁} (w₁ : j₁ ≤ k′) → Σ (j₁ ≤ a) (λ w₂ → Ψ (Φ (can C w₂)) ≡ can C″ w₁)
  aux C w β nβ (uf d b nb)       e eq w₁ = no-nj (trans (sym (g-uf GΨ (uf d b nb) refl)) eq)
  aux C w β nβ (fo C′ w′ β′ nβ′) e eq w₁ =
    proj₁ (g-fo GΦ C w β nβ (cong cfgOf e) (proj₁ (g-fo GΨ C′ w′ β′ nβ′ eq w₁)))
    , trans (cong (λ s → Ψ s) (proj₂ (g-fo GΦ C w β nβ (cong cfgOf e) (proj₁ (g-fo GΨ C′ w′ β′ nβ′ eq w₁)))))
            (proj₂ (g-fo GΨ C′ w′ β′ nβ′ eq w₁))
  gf : ∀ {j} (C : Cfg a) (w : j ≤ a) (β : Tr j) (nβ : j ⊢ zero ◃ β) {C″ : Cfg k′}
    → cfgOf (Ψ (Φ (fo C w β nβ))) ≡ just C″
    → ∀ {j₁} (w₁ : j₁ ≤ k′) → Σ (j₁ ≤ a) (λ w₂ → Ψ (Φ (can C w₂)) ≡ can C″ w₁)
  gf C w β nβ eq w₁ = aux C w β nβ (Φ (fo C w β nβ)) refl eq w₁

nxt-same : ∀ {g} (f : (n : ℕ) → NL (g n)) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (t : Tr (lim g))
  (m : ℕ) {j : LF} (w : j ≤ g m) (β′ : Tr j) (nβ′ : j ⊢ zero ◃ β′)
  → nxtW f (ε , ρ , B) t m m (way g (proj₂ ρ) m m) w β′ nβ′ ≡ fo (ε m , proj₁ ρ m , dL g ε ρ B m t) w β′ nβ′
nxt-same {g} f ε ρ B t m w β′ nβ′ =
  cong (λ W → nxtW f (ε , ρ , B) t m m W w β′ nβ′) (way-refl g (proj₂ ρ) m)

mutual
  good-nxt : ∀ {jd} (f : NL jd) (t : Tr jd) (c : Ch jd) → Gd (λ s → nxt f s t c)
  good-nxt n0 t ()
  good-nxt (n+ {a} f) t c = record { g-uf = gu ; g-fo = gf }
    where
    gu : ∀ {j} (s : St j (suc a)) → cfgOf s ≡ nothing → cfgOf (nxt (n+ f) s t c) ≡ nothing
    gu (uf d b nb) e = refl
    gf : ∀ {j} (C : Cfg (suc a)) (w : j ≤ suc a) (β : Tr j) (nβ : j ⊢ zero ◃ β) {C′ : Cfg a}
      → cfgOf (nxt (n+ f) (fo C w β nβ) t c) ≡ just C′
      → ∀ {j₁} (w₁ : j₁ ≤ a) → Σ (j₁ ≤ suc a) (λ w₂ → nxt (n+ f) (can C w₂) t c ≡ can C′ w₁)
    gf (ε , ρ , B) (ins w) β nβ refl w₁ = ins w₁ , refl
  good-nxt (nω {g} f) t m = record { g-uf = gu ; g-fo = gf }
    where
    gu : ∀ {j} (s : St j (lim g)) → cfgOf s ≡ nothing → cfgOf (nxt (nω f) s t m) ≡ nothing
    gu (uf d b nb) e = refl
    gf : ∀ {j} (C : Cfg (lim g)) (w : j ≤ lim g) (β : Tr j) (nβ : j ⊢ zero ◃ β) {C′ : Cfg (g m)}
      → cfgOf (nxt (nω f) (fo C w β nβ) t m) ≡ just C′
      → ∀ {j₁} (w₁ : j₁ ≤ g m) → Σ (j₁ ≤ lim g) (λ w₂ → nxt (nω f) (can C w₂) t m ≡ can C′ w₁)
    gf (ε , ρ , B) (inlu ws) β nβ refl w₁ = inl m w₁ , nxt-same f ε ρ B t m w₁ _ _
    gf (ε , ρ , B) (inl n w) β nβ eq w₁ = goodW f ε ρ B t m n (way g (proj₂ ρ) m n) refl w _ _ eq w₁

  goodW : ∀ {g} (f : (n : ℕ) → NL (g n)) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (t : Tr (lim g))
    (m n : ℕ) (W : Way g m n) → way g (proj₂ ρ) m n ≡ W
    → ∀ {j} (w : j ≤ g n) (β′ : Tr j) (nβ′ : j ⊢ zero ◃ β′) {C′ : Cfg (g m)}
    → cfgOf (nxtW f (ε , ρ , B) t m n W w β′ nβ′) ≡ just C′
    → ∀ {j₁} (w₁ : j₁ ≤ g m) → Σ (j₁ ≤ lim g) (λ w₂ → nxt (nω f) (can (ε , ρ , B) w₂) t m ≡ can C′ w₁)
  goodW {g} f ε ρ B t m n (fwd v) eW w β′ nβ′ eq {j₁} w₁ =
    inl n (proj₁ R₂)
    , trans (cong (λ W → nxtW f (ε , ρ , B) t m n W (proj₁ R₂)
                     (bs (dL g ε ρ B n t) j₁ (proj₁ R₂)) (ns (dL g ε ρ B n t) j₁ (proj₁ R₂))) eW)
            (proj₂ R₂)
    where
    R₂ = g-fo (good-thru (f n) v) (ε n , proj₁ ρ n , dL g ε ρ B n t) w β′ nβ′ eq w₁
  goodW {g} f ε ρ B t m n (bwd v) eW w β′ nβ′ refl w₁ = inl m w₁ , nxt-same f ε ρ B t m w₁ _ _

  good-thru : ∀ {a} (f : NL a) {k} (v : k ≤ a) → Gd (λ s → thru f v s)
  good-thru f      self      = good-id
  good-thru (n+ f) (ins v)   = good-∘ (good-nxt (n+ f) zero tt) (good-thru f v)
  good-thru (nω f) (inl n v) = good-∘ (good-nxt (nω f) zero n) (good-thru (f n) v)
  good-thru (nω f) (inlu vs) = good-∘ (good-nxt (nω f) zero zero) (good-thru (f zero) (vs zero))
  good-thru ()     (ink v)
  good-thru ()     (inb c v)
  good-thru ()     (inu vs)
```

## 沿上下文

```agda
stOf : ∀ {ℓ j} → NL ℓ → St j ℓ → ∀ {jd} {d : Dc ℓ jd} → Ctx ℓ d → St j jd
stOf f      s []          = s
stOf (n+ f) s (fr t c Γ)  = stOf f (nxt (n+ f) s t c) Γ
stOf (nω f) s (fr t m Γ)  = stOf (f m) (nxt (nω f) s t m) Γ
stOf n0     s (fr t () Γ)

finD : ∀ {ℓ} → NL ℓ → ∀ {jd} {d : Dc ℓ jd} → Ctx ℓ d → NL jd
finD f      []          = f
finD (n+ f) (fr t _ Γ)  = finD f Γ
finD (nω f) (fr t m Γ)  = finD (f m) Γ
finD n0     (fr t () Γ)

stOf-▹ : ∀ {ℓ j jd} (f : NL ℓ) (s : St j ℓ) {d : Dc ℓ jd} (Γ : Ctx ℓ d) (t : Tr jd) (c : Ch jd)
  → stOf f s (snocC Γ t c) ≡ nxt (finD f Γ) (stOf f s Γ) t c
stOf-▹ (n+ f) s []           t c = refl
stOf-▹ (nω f) s []           t c = refl
stOf-▹ n0     s []           t ()
stOf-▹ (n+ f) s (fr t′ c′ Γ) t c = stOf-▹ f (nxt (n+ f) s t′ c′) Γ t c
stOf-▹ (nω f) s (fr t′ m Γ)  t c = stOf-▹ (f m) (nxt (nω f) s t′ m) Γ t c
stOf-▹ n0     s (fr t′ () Γ) t c

good-stOf : ∀ {ℓ} (f : NL ℓ) {jd} {d : Dc ℓ jd} (Γ : Ctx ℓ d) → Gd (λ s → stOf f s Γ)
good-stOf f      []          = good-id
good-stOf (n+ f) (fr t c Γ)  = good-∘ (good-nxt (n+ f) t c) (good-stOf f Γ)
good-stOf (nω f) (fr t m Γ)  = good-∘ (good-nxt (nω f) t m) (good-stOf (f m) Γ)
good-stOf n0     (fr t () Γ)

ok-stOf : ∀ {ℓ j} (f : NL ℓ) (s : St j ℓ) → OKst s → ∀ {jd} {d : Dc ℓ jd} (Γ : Ctx ℓ d) → OKst (stOf f s Γ)
ok-stOf f      s ok []          = ok
ok-stOf (n+ f) s ok (fr t c Γ)  = ok-stOf f (nxt (n+ f) s t c) (ok-nxt (n+ f) s t c ok) Γ
ok-stOf (nω f) s ok (fr t m Γ)  = ok-stOf (f m) (nxt (nω f) s t m) (ok-nxt (nω f) s t m ok) Γ
ok-stOf n0     s ok (fr t () Γ)
```

`ψ⊥` 一侧只经真实的帧: 深层的配置, 与它对应的目标路径.

```agda
stepD : ∀ {jd} → NL jd → Cfg jd → Tr jd → (c : Ch jd) → Cfg (chL jd c)
stepD n0 C t ()
stepD (n+ {a} f) (ε , ρ , B) t c = ε , ρ , dS a ε ρ B t
stepD (nω {g} f) (ε , ρ , B) t m = ε m , proj₁ ρ m , dL g ε ρ B m t

ψ⊥c : ∀ {jd} → Cfg jd → Tr jd → Tr zero
ψ⊥c {jd} (ε , ρ , B) y = ψ⊥ jd ε ρ B y

ψ⊥-up : ∀ {jd} (f : NL jd) (C : Cfg jd) (t : Tr jd) (c : Ch jd) (y : ChT jd c) (e : RCh jd c (chZ jd c) y)
  → ψ⊥c C (up t c y e) ≡ ψ⊥c (stepD f C t c) (chT jd c y)
ψ⊥-up n0 C t () y e
ψ⊥-up (n+ f) (ε , ρ , B) t c y e = refl
ψ⊥-up (nω f) (ε , ρ , B) t m y e = refl

stepD-⊵ : ∀ {jd} (f : NL jd) (C : Cfg jd) (t : Tr jd) (c : Ch jd) (y : Tr (chL jd c))
  → zero ⊢ ψ⊥c C t ⊴ ψ⊥c (stepD f C t c) y
stepD-⊵ n0 C t () y
stepD-⊵ (n+ {a} f) (ε , ρ , B) t c y = ψ⊥-⊵ a ε ρ (dS a ε ρ B t) y
stepD-⊵ (nω {g} f) (ε , ρ , B) t m y = ψ⊥-⊵ (g m) (ε m) (proj₁ ρ m) (dL g ε ρ B m t) y

deepOf : ∀ {ℓ} → NL ℓ → Cfg ℓ → ∀ {jd} {d : Dc ℓ jd} → Ctx ℓ d → Cfg jd
deepOf f      C []          = C
deepOf (n+ f) C (fr t c Γ)  = deepOf f (stepD (n+ f) C t c) Γ
deepOf (nω f) C (fr t m Γ)  = deepOf (f m) (stepD (nω f) C t m) Γ
deepOf n0     C (fr t () Γ)

deepOf-▹ : ∀ {ℓ jd} (f : NL ℓ) (C : Cfg ℓ) {d : Dc ℓ jd} (Γ : Ctx ℓ d) (t : Tr jd) (c : Ch jd)
  → deepOf f C (snocC Γ t c) ≡ stepD (finD f Γ) (deepOf f C Γ) t c
deepOf-▹ (n+ f) C []           t c = refl
deepOf-▹ (nω f) C []           t c = refl
deepOf-▹ n0     C []           t ()
deepOf-▹ (n+ f) C (fr t′ c′ Γ) t c = deepOf-▹ f (stepD (n+ f) C t′ c′) Γ t c
deepOf-▹ (nω f) C (fr t′ m Γ)  t c = deepOf-▹ (f m) (stepD (nω f) C t′ m) Γ t c
deepOf-▹ n0     C (fr t′ () Γ) t c

ok-step : ∀ {jd} (f : NL jd) (C : Cfg jd) → OKB jd (proj₂ (proj₂ C)) → (t : Tr jd) (c : Ch jd)
  → OKB (chL jd c) (proj₂ (proj₂ (stepD f C t c)))
ok-step n0 C ok t ()
ok-step (n+ f) (ε , ρ , B) ok t c = ok-dS ε ρ B ok t
ok-step (nω {g} f) (ε , ρ , B) ok t m = ok-dL g ε ρ B ok m t

ok-deep : ∀ {ℓ} (f : NL ℓ) (C : Cfg ℓ) → OKB ℓ (proj₂ (proj₂ C)) → ∀ {jd} {d : Dc ℓ jd} (Γ : Ctx ℓ d)
  → OKB jd (proj₂ (proj₂ (deepOf f C Γ)))
ok-deep f      C ok []          = ok
ok-deep (n+ f) C ok (fr t c Γ)  = ok-deep f (stepD (n+ f) C t c) (ok-step (n+ f) C ok t c) Γ
ok-deep (nω f) C ok (fr t m Γ)  = ok-deep (f m) (stepD (nω f) C t m) (ok-step (nω f) C ok t m) Γ
ok-deep n0     C ok (fr t () Γ)

liftW : ∀ {ℓ} → NL ℓ → ∀ {jd} {d : Dc ℓ jd} → Ctx ℓ d → ∀ {j} → j ≤ jd → j ≤ ℓ
liftW f      []          w = w
liftW (n+ f) (fr t _ Γ)  w = ins (liftW f Γ w)
liftW (nω f) (fr t m Γ)  w = inl m (liftW (f m) Γ w)
liftW n0     (fr t () Γ) w

stOf-can : ∀ {ℓ} (f : NL ℓ) (C : Cfg ℓ) {jd} {d : Dc ℓ jd} (Γ : Ctx ℓ d) {j} (w′ : j ≤ jd)
  → stOf f (can C (liftW f Γ w′)) Γ ≡ can (deepOf f C Γ) w′
stOf-can f      C []          w′ = refl
stOf-can (n+ f) (ε , ρ , B) (fr t c Γ) w′ = stOf-can f (stepD (n+ f) (ε , ρ , B) t c) Γ w′
stOf-can (nω {g} f) (ε , ρ , B) (fr t m Γ) w′ =
  trans (cong (λ s → stOf (f m) s Γ) (nxt-same f ε ρ B t m (liftW (f m) Γ w′) _ _))
        (stOf-can (f m) (stepD (nω f) (ε , ρ , B) t m) Γ w′)
stOf-can n0     C (fr t () Γ) w′
```

## 主引理与值引理

`MS`: 参照的 ψ (目标层号 i 与 j 对应) 对着深层状态的折叠. 结点处先按参照的三歧分情况, 再用 `kpF` (折叠中) 或上折的保留 (上折中) 对上; 不一致的组合由层号事实排除. 默认情形两边都是链 (`chainS`).
`VS`: ψ⁰ 对着 `ψ⊥` 的读回.

```agda
J′ : (ℓ : LF) → ∀ {j} {d : Dc ℓ j} → Ctx ℓ d → ∀ {k} → L.Ordᶜ k → Tr j → Set
J′ ℓ = Sim.J ℓ (SlOf ℓ)

Wch : ∀ {i′ K′} (q : i′ <ᴵ K′) (f′ : L.U i′ (L.<→◃ q) → L.Ordᶜ K′) → ℕ → L.Ordᶜ i′
Wch {i′} q f′ = iterᴸ (λ x → L.ψ q (λ r → r) (f′ (L.into (L.<→◃ q) x))) (L.Ω i′)

Dref : ∀ {i′ K′ L⁺ i} (p₀ : i <ᴵ L⁺) (σ : L.Simᴵ K′ L⁺) (q : i′ <ᴵ K′) (f′ : L.U i′ (L.<→◃ q) → L.Ordᶜ K′)
  → L.Ordᶜ i
Dref p₀ σ q f′ = L.lim (λ n → L.ψ p₀ σ (f′ (L.into (L.<→◃ q) (Wch q f′ n))))

Vch : ∀ {jd} (C : Cfg jd) (p : Pos jd) (g : Br jd p → Tr jd) → ℕ → Br jd p
Vch {jd} (ε , ρ , B) p g =
  iter (λ z → fromBr jd p (ψs jd ε ρ B (at jd p) (posW jd p) (bs B (at jd p) (posW jd p)) (ns B (at jd p) (posW jd p)) (g z)))
       (br0 jd p)

run-ss : ∀ {j jd} (s : St j jd) {k} {X : L.Ordᶜ k} {y : Tr jd}
  → Rel j X (run s y) → Rel j (L.lim (iterᴸ (X L.+_) L.zero)) (run s (suc y))
run-ss {j} {jd} (fo (ε , ρ , B) w β nβ) {y = y} r = Add.nextL j (SlOf j) (nzs jd ε ρ B j w β nβ y) r
run-ss {j} {jd} (uf d b nb)             {y = y} r = Add.nextL j (SlOf j) (Up-nz jd d b nb y) r

ok-cfg : ∀ {j jd} (s : St j jd) → OKst s → {C′ : Cfg jd} → cfgOf s ≡ just C′ → OKB jd (proj₂ (proj₂ C′))
ok-cfg (fo (ε , ρ , B) w β nβ) ok refl = ok

module M {ℓ : LF} (f : NL ℓ) (C₀ : Cfg ℓ) (ok : OKB ℓ (proj₂ (proj₂ C₀))) where

  top : ∀ {j} → j ≤ ℓ → St j ℓ
  top w = can C₀ w

  ReC : ∀ {jd} {d : Dc ℓ jd} → Ctx ℓ d → Cfg jd → Set
  ReC {jd} Γ C′ = ∀ {j₁} (w₁ : j₁ ≤ jd) → Σ (j₁ ≤ ℓ) (λ w₂ → stOf f (top w₂) Γ ≡ can C′ w₁)

  top-zr : ∀ {j} (w : j ≤ ℓ) {i} → Corr i j → (y : Tr ℓ) → Rel j (L.Ω i) (run (top w) y)
  top-zr {j} w ci y = Rel-⊴ (START (nlW w f) ci) (⊴-trans (proj₂ ok j w) (run-⊵ (top w) y))

  mutual
    MS : ∀ {j} (w : j ≤ ℓ) {jd} {d : Dc ℓ jd} {Γ : Ctx ℓ d} (s : St j jd) → s ≡ stOf f (top w) Γ
       → ∀ {k} {X : L.Ordᶜ k} {y : Tr jd} → J′ ℓ Γ X y
       → ∀ {L⁺ i} (p₀ : i <ᴵ L⁺) → Corr i j → (σ : L.Simᴵ k L⁺) → Rel j (L.ψ p₀ σ X) (run s y)
    MS {j} w s eq (zr {y = y}) p₀ ci σ =
      subst (λ s → Rel j (L.Ω _) (run s y)) (sym eq) (top-zr w ci y)
    MS {j} w s eq (pop {Γ = Γ₀} {t = t} {c = c} {y = y} r) p₀ ci σ =
      subst (λ s → Rel j _ (run s y)) (sym (trans eq (stOf-▹ f (top w) Γ₀ t c)))
        (Rel-⊴ (MS w (stOf f (top w) Γ₀) refl r p₀ ci σ) (nxt-⊵ (finD f Γ₀) (stOf f (top w) Γ₀) t c y))
    MS w s eq (ss r) p₀ ci σ = run-ss s (MS w s eq r p₀ ci σ)
    MS w s eq (wk r e) p₀ ci σ = wk (MS w s eq r p₀ ci σ) (run-mono s e)
    MS w s eq (ll h) p₀ ci σ = ll (λ n → MS w s eq (h n) p₀ ci σ)
    MS {j} w {jd} {Γ = Γ} (uf d b nb) eq (nd {q = q} {f = f′} {p = p} {g = g} lv h) p₀ ci σ
      with L.<ᴵ-dec (σ q) p₀
    ... | injᵃ (L.via e r) =
      nd (subst (Corr _) (sym (at-mv d p)) (Corr-≅ (L.≅ᴵ-sym e) lv))
        (λ y₀ c′ sl →
          subst (λ u → Rel j (L.ψ p₀ σ (f′ (L.into (L.<→◃ q) (L.tr⁻ e u)))) (Up jd d b nb (g (mvBr d p c′))))
            (sym (L.out-into (L.<→◃ r) y₀))
            (MS w (uf d b nb) eq
              (h (L.tr⁻ e y₀) (mvBr d p c′) (toSl ℓ _ p (mvRel d p (TRC.tr⁻ᴿ (trP j (mv d p)) e sl))))
              p₀ ci σ))
    ... | injᵇ x = ⊥-elim (L.clash₁ (L.≅ᴵ-refl _) (L.≅ᴵ-refl _)
        (POS (nlW w f) (mv d p) (subst (Corr _) (sym (at-mv d p)) lv) ci) x)
    ... | injᶜ x = ⊥-elim (L.clash₂ (L.≅ᴵ-refl _) (L.≅ᴵ-refl _)
        (POS (nlW w f) (mv d p) (subst (Corr _) (sym (at-mv d p)) lv) ci) x)
    MS {j} w {jd} {Γ = Γ} (fo (ε′ , ρ′ , B′) w′ β nβ) eq (nd {q = q} {f = f′} {p = p} {g = g} lv h) p₀ ci σ
      with L.<ᴵ-dec (σ q) p₀
    ... | injᵃ (L.via e r) =
      kpF (finD f Γ) ε′ ρ′ p w′
        (λ T → Rel j (L.limᵢ r (λ u → L.ψ p₀ σ (f′ (L.into (L.<→◃ q) (L.tr⁻ e (L.out (L.<→◃ r) u)))))) T)
        (λ q′ cv kf → nd (subst (Corr _) (sym (Keep.lev kf)) (Corr-≅ (L.≅ᴵ-sym e) lv))
          (λ y₀ c′ sl →
            subst (λ u → Rel j (L.ψ p₀ σ (f′ (L.into (L.<→◃ q) (L.tr⁻ e u))))
                               (ψs jd ε′ ρ′ B′ j w′ β nβ (g (cv c′))))
              (sym (L.out-into (L.<→◃ r) y₀))
              (MS w (fo (ε′ , ρ′ , B′) w′ β nβ) eq
                (h (L.tr⁻ e y₀) (cv c′) (toSl ℓ _ p (Keep.conv kf (TRC.tr⁻ᴿ (trP j q′) e sl))))
                p₀ ci σ)))
        (λ df → ⊥-elim (df lv ci (L.via e r)))
    ... | injᵇ x =
      kpF (finD f Γ) ε′ ρ′ p w′ (λ T → Rel j (Dref p₀ σ q f′) T)
        (λ q′ cv kf → ⊥-elim (L.clash₁ (L.≅ᴵ-refl _) (L.≅ᴵ-refl _) (Keep.below kf lv ci) x))
        (λ _ → Mdef w Γ (ε′ , ρ′ , B′) w′ β nβ eq lv h p₀ ci σ)
    ... | injᶜ x =
      kpF (finD f Γ) ε′ ρ′ p w′ (λ T → Rel j (Dref p₀ σ q f′) T)
        (λ q′ cv kf → ⊥-elim (L.clash₂ (L.≅ᴵ-refl _) (L.≅ᴵ-refl _) (Keep.below kf lv ci) x))
        (λ _ → Mdef w Γ (ε′ , ρ′ , B′) w′ β nβ eq lv h p₀ ci σ)
    MS w s eq (ur r) p₀ ci σ = MS w s eq r p₀ ci (λ q → σ (L.suc q))
    MS w s eq (ul n r) p₀ ci σ = MS w s eq r p₀ ci (λ q → σ (L.lim n q))
    MS {j} w s eq (psh {j = jp} {Γ = Γ₀} {t = t} {c = c} {y = y} {e = e} r) p₀ ci σ =
      subst (λ s → Rel j _ (run s (up t c y e))) (sym eq)
        (subst (Rel j _) (sym (run-up (finD f Γ₀) (stOf f (top w) Γ₀) t c y e))
          (subst (λ s → Rel j _ (run s (chT jp c y))) (stOf-▹ f (top w) Γ₀ t c)
            (MS w (stOf f (top w) (snocC Γ₀ t c)) refl r p₀ ci σ)))

    Mdef : ∀ {j} (w : j ≤ ℓ) {jd} {d : Dc ℓ jd} (Γ : Ctx ℓ d) (C′ : Cfg jd) (w′ : j ≤ jd)
      (β : Tr j) (nβ : j ⊢ zero ◃ β)
      → fo C′ w′ β nβ ≡ stOf f (top w) Γ
      → ∀ {i′ K′} {q : i′ <ᴵ K′} {f′ : L.U i′ (L.<→◃ q) → L.Ordᶜ K′} {p : Pos jd} {g : Br jd p → Tr jd}
      → Corr i′ (at jd p)
      → (∀ (y₀ : L.Ordᶜ i′) (c : Br jd p) → SlOf ℓ d p y₀ c → J′ ℓ Γ (f′ (L.into (L.<→◃ q) y₀)) (g c))
      → ∀ {L⁺ i} (p₀ : i <ᴵ L⁺) → Corr i j → (σ : L.Simᴵ K′ L⁺)
      → Rel j (Dref p₀ σ q f′)
          (limc (λ n → run (fo C′ w′ β nβ) (g (Vch C′ p g n))) (λ n → run-nz (fo C′ w′ β nβ) (g (Vch C′ p g n))))
    Mdef {j} w {jd} Γ C′ w′ β nβ eq {q = q} {f′ = f′} {p = p} {g = g} lv h p₀ ci σ =
      ll (λ n → Add.inCum j (SlOf j) (λ m → run (fo C′ w′ β nβ) (g (Vch C′ p g m)))
                  (λ m → run-nz (fo C′ w′ β nβ) (g (Vch C′ p g m))) (suc n)
        (MS w (fo C′ w′ β nβ) eq
          (h (Wch q f′ n) (Vch C′ p g (suc n))
             (toSl ℓ _ p (chainS Γ C′
               (g-fo (good-stOf f Γ) C₀ w _ _ (cong cfgOf (sym eq)))
               (ok-cfg (stOf f (top w) Γ) (ok-stOf f (top w) ok Γ) (cong cfgOf (sym eq)))
               lv h n)))
          p₀ ci σ))

    chainS : ∀ {jd} {d : Dc ℓ jd} (Γ : Ctx ℓ d) (C′ : Cfg jd) → ReC Γ C′ → OKB jd (proj₂ (proj₂ C′))
      → ∀ {i′ K′} {q : i′ <ᴵ K′} {f′ : L.U i′ (L.<→◃ q) → L.Ordᶜ K′} {p : Pos jd} {g : Br jd p → Tr jd}
      → Corr i′ (at jd p)
      → (∀ (y₀ : L.Ordᶜ i′) (c : Br jd p) → SlOf ℓ d p y₀ c → J′ ℓ Γ (f′ (L.into (L.<→◃ q) y₀)) (g c))
      → ∀ n → RelP jd p (Wch q f′ n) (Vch C′ p g (suc n))
    chainS {jd} Γ (ε′ , ρ′ , B′) rc okC {p = p} {g = g} lv h zero =
      relFrom jd p (Rel-⊴ (START (nl-at (finD f Γ) p) lv)
        (⊴-trans (proj₂ okC (at jd p) (posW jd p))
                 (ψs-⊵ jd ε′ ρ′ B′ (at jd p) (posW jd p) _ _ (g (br0 jd p)))))
    chainS {jd} Γ (ε′ , ρ′ , B′) rc okC {q = q} {f′ = f′} {p = p} {g = g} lv h (suc n) =
      relFrom jd p (MS (proj₁ (rc (posW jd p))) (can (ε′ , ρ′ , B′) (posW jd p)) (sym (proj₂ (rc (posW jd p))))
        (h (Wch q f′ n) (Vch (ε′ , ρ′ , B′) p g (suc n)) (toSl ℓ _ p (chainS Γ (ε′ , ρ′ , B′) rc okC lv h n)))
        q lv (λ r → r))

  okD : ∀ {jd} {d : Dc ℓ jd} (Γ : Ctx ℓ d) (C′ : Cfg jd) → deepOf f C₀ Γ ≡ C′ → OKB jd (proj₂ (proj₂ C′))
  okD Γ C′ de = subst (λ x → OKB _ (proj₂ (proj₂ x))) de (ok-deep f C₀ ok Γ)

  rcD : ∀ {jd} {d : Dc ℓ jd} (Γ : Ctx ℓ d) (C′ : Cfg jd) → deepOf f C₀ Γ ≡ C′ → ReC Γ C′
  rcD Γ C′ de w₁ = liftW f Γ w₁ , trans (stOf-can f C₀ Γ w₁) (cong (λ C → can C w₁) de)

  VS : ∀ {jd} {d : Dc ℓ jd} {Γ : Ctx ℓ d} (C′ : Cfg jd) → deepOf f C₀ Γ ≡ C′
     → ∀ {k} {X : L.Ordᶜ k} {y : Tr jd} → J′ ℓ Γ X y → L.ψ⁰ X ≼ read (ψ⊥c C′ y)
  VS (ε′ , ρ′ , B′) de (zr {y = y}) =
    ≼-trans (⊴→≼ (proj₁ (okD [] (ε′ , ρ′ , B′) de))) (⊴→≼ (ψ⊥-⊵ ℓ ε′ ρ′ B′ y))
  VS C′ de (pop {Γ = Γ₀} {X = X} {t = t} {c = c} {y = y} r) =
    subst (λ x → L.ψ⁰ X ≼ read (ψ⊥c x y)) (trans (sym (deepOf-▹ f C₀ Γ₀ t c)) de)
      (≼-trans (VS (deepOf f C₀ Γ₀) refl r) (⊴→≼ (stepD-⊵ (finD f Γ₀) (deepOf f C₀ Γ₀) t c y)))
  VS {jd} (ε′ , ρ′ , B′) de (ss {y = y} r) =
    next≽ (ψ⊥ jd ε′ ρ′ B′ y) (nz⊥ jd ε′ ρ′ B′ y) (VS (ε′ , ρ′ , B′) de r)
  VS {jd} (ε′ , ρ′ , B′) de (wk {y = y} r e) =
    ≼-trans (VS (ε′ , ρ′ , B′) de r) (⊑→≼ (read (ψ⊥ jd ε′ ρ′ B′ y)) (◃⊑ (mono⊥ jd ε′ ρ′ B′ e)))
  VS C′ de (ll h) = l≼ (λ n → VS C′ de (h n))
  VS {jd} {Γ = Γ} (ε′ , ρ′ , B′) de (nd {q = q} {f = f′} {p = p} {g = g} lv h) =
    l≼ (λ n → limcum≽ (λ m → ψ⊥ jd ε′ ρ′ B′ (g (Vch (ε′ , ρ′ , B′) p g m)))
                (λ m → nz⊥ jd ε′ ρ′ B′ (g (Vch (ε′ , ρ′ , B′) p g m))) (suc n)
      (VS (ε′ , ρ′ , B′) de (h (Wch q f′ n) (Vch (ε′ , ρ′ , B′) p g (suc n))
        (toSl ℓ _ p (chainS Γ (ε′ , ρ′ , B′) (rcD Γ (ε′ , ρ′ , B′) de) (okD Γ (ε′ , ρ′ , B′) de) lv h n)))))
  VS C′ de (ur {X = X} r) = VS C′ de {X = X} r
  VS C′ de (ul n {X = X} r) = VS C′ de {X = X} r
  VS C′ de (psh {j = jp} {Γ = Γ₀} {X = X} {t = t} {c = c} {y = y} {e = e} r) =
    subst (λ x → L.ψ⁰ X ≼ read x) (sym (ψ⊥-up (finD f Γ₀) C′ t c y e))
      (subst (λ x → L.ψ⁰ X ≼ read (ψ⊥c (stepD (finD f Γ₀) x t c) (chT jp c y))) de
        (subst (λ x → L.ψ⁰ X ≼ read (ψ⊥c x (chT jp c y))) (deepOf-▹ f C₀ Γ₀ t c)
          (VS (deepOf f C₀ (snocC Γ₀ t c)) refl r)))
```

## `lower`

```agda
lower : ∀ {ℓ i} (f : NL ℓ) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → OKB ℓ B → Corr i ℓ
  → L.ψ⁰ (L.Ω i) ≼ read (ψ⊥ ℓ ε ρ B (Ωt ℓ))
lower f ε ρ B ok c = M.VS f (ε , ρ , B) ok {Γ = []} (ε , ρ , B) refl (START f c)
```
