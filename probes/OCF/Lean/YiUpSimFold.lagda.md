# 统一值模拟: 后继层号上的折叠保持与 `lower-fin`

> 验收文件. 编译定理, 无前提: 对一切只含零与后继的层号 ℓ (`FinL`), 底 B 逐分量不低于标准底 (`OKB`), 参照层号 i 与 ℓ 对应 (`Corr`), 有 `lower-fin : ψ⁰(Ω i) ≼ read (ψ⊥ ℓ ε B (Ωt ℓ))`.
> 证法: `YiUpSimRel` 的关系族; 起点 `START`; 沿帧算出深层的折叠状态 (`stOf`: 仍在折叠, 或已进入上折); 主引理 `MS` (参照的 ψ 对着 `ψs`), 值引理 `VS` (ψ⁰ 对着 `ψ⊥`).
> 留空: ℕ 极限与 `Ωₗ` 层号的帧 (`nxt` 只对后继层定义), 见文末. `ψs-⊵`, `ψ⊥-⊵` 对一切层号成立. 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUpSimFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Maybe using (just; nothing)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Lean.YiFreshBlock renaming (L to LF)
open import OCF.Lean.YiFreshFold using (_+_; iter; next; cum; Ωt; ι; eqℕ)
open import OCF.Lean.YiFreshLegal using (_⊢_◃_; ◃s; ◃l; ◃w; ◃u; ◃c; ◃t)
open import OCF.Lean.YiFreshValRead using (T₀; read; ◃⊑; next≽; limcum≽)
open import OCF.Lean.YiLeanValRel using (TRC)
open import OCF.Lean.YiPhiBlock hiding (psh; pshBr)
open import OCF.Lean.YiPhiFold using (kp; kp⁼)
open import OCF.Lean.YiPhiLegal using (kp-ind)
open import OCF.Lean.YiUpBlock
open import OCF.Lean.YiUpFold
open import OCF.Lean.YiUpLegal using (mono⊥; monos; Up-mono; dS; dL; dW)
open import OCF.Lean.YiUpVal using (_⊢_⊴_; ⊴r; ⊴◃; ⊴-◃; ◃-⊴; ⊴-trans; ⊴→≼; Up-⊵)
open import OCF.Lean.YiUpSimRel

import OCF.Align.Level as L
open L using (_≅ᴵ_; _<ᴵ_; _≺ᴵ_)
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; l≼; ⊑→≼)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using () renaming (iter to iterᴸ)
```

## 底在折叠值之下 (一切层号)

```agda
+ι⊴ : ∀ {j} (b : Tr j) (c : Tr zero) → j ⊢ b ⊴ b + ι j c
+ι⊴ b zero    = ⊴r
+ι⊴ b (suc c) = ⊴◃ (⊴-◃ (+ι⊴ b c) ◃s)
+ι⊴ b (lim f) = ⊴◃ (⊴-◃ (+ι⊴ b (f zero)) (◃l zero))
+ι⊴ b (Ω () _)
+ι⊴ b (up _ () _)

ψ⊥-⊵ : (ℓ : LF) (ε : Ev ℓ) (B : Base ℓ) (x : Tr ℓ) → zero ⊢ b⊥ B ⊴ ψ⊥ ℓ ε B x
ψ⊥-⊵ ℓ ε B zero    = ⊴r
ψ⊥-⊵ ℓ ε B (suc x) = ⊴◃ (⊴-◃ (ψ⊥-⊵ ℓ ε B x) (◃l zero))
ψ⊥-⊵ ℓ ε B (lim f) = ⊴◃ (⊴-◃ (ψ⊥-⊵ ℓ ε B (f zero)) (◃l zero))
ψ⊥-⊵ ℓ ε B (Ω p g) = ⊴◃ (⊴-◃ (ψ⊥-⊵ ℓ ε B (g (fromBr ℓ p zero))) (◃l zero))
ψ⊥-⊵ zero     ε B (up x () y)
ψ⊥-⊵ (suc a)  ε B (up x _ y) = ⊴-trans (ψ⊥-⊵ (suc a) ε B x) (ψ⊥-⊵ a ε (dS a ε B x) y)
ψ⊥-⊵ (lim g)  ε B (up x n y) = ⊴-trans (ψ⊥-⊵ (lim g) ε B x) (ψ⊥-⊵ (g n) (ε n) (dL g ε B n x) y)
ψ⊥-⊵ (Ωₗ k h) ε B (up x c y) =
  ⊴-trans (ψ⊥-⊵ (Ωₗ k h) ε B x) (ψ⊥-⊵ (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) y)

ψs-⊵ : (ℓ : LF) (ε : Ev ℓ) (B : Base ℓ) (j : LF) (w : j ≤ ℓ) (β : Tr j) (x : Tr ℓ)
  → j ⊢ β ⊴ ψs ℓ ε B j w β x
ψs-⊵ ℓ ε B j w β zero    = ⊴r
ψs-⊵ ℓ ε B j w β (suc x) = ⊴◃ (⊴-◃ (ψs-⊵ ℓ ε B j w β x) (◃l zero))
ψs-⊵ ℓ ε B j w β (lim f) = ⊴◃ (⊴-◃ (ψs-⊵ ℓ ε B j w β (f zero)) (◃l zero))
ψs-⊵ ℓ ε B j w β (Ω p g) =
  kp-ind ℓ ε p w (λ X → j ⊢ β ⊴ X)
    (λ q cv gd → ⊴◃ (⊴-◃ (ψs-⊵ ℓ ε B j w β (g (cv (fromBr j q zero)))) ◃w))
    (⊴◃ (⊴-◃ (ψs-⊵ ℓ ε B j w β (g (fromBr ℓ p zero))) (◃l zero)))
ψs-⊵ ℓ ε B _ self β (up x c y) =
  ⊴-trans (ψs-⊵ ℓ ε B ℓ self β x) (Up-⊵ (chL ℓ c) (down stop c) _ (chT ℓ c y))
ψs-⊵ (suc a) ε B j (ins w) β (up x _ y) =
  ⊴-trans (ψs-⊵ (suc a) ε B j (ins w) β x) (ψs-⊵ a ε (dS a ε B x) j w _ y)
ψs-⊵ (lim g) ε B j (inl n w) β (up x m y) with eqℕ m n
... | just refl = ⊴-trans (ψs-⊵ (lim g) ε B j (inl m w) β x) (ψs-⊵ (g m) (ε m) (dL g ε B m x) j w _ y)
... | nothing   = ⊴-trans (ψs-⊵ (lim g) ε B j (inl n w) β x) (+ι⊴ _ _)
ψs-⊵ (lim g) ε B j (inlu ws) β (up x m y) =
  ⊴-trans (ψs-⊵ (lim g) ε B j (inlu ws) β x) (ψs-⊵ (g m) (ε m) (dL g ε B m x) j (ws m) _ y)
ψs-⊵ (Ωₗ k h) ε B j (ink w) β (up x c y) =
  ⊴-trans (ψs-⊵ (Ωₗ k h) ε B j (ink w) β x)
    (ψs-⊵ (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) j (w ∙ proj₁ (proj₂ ε c)) _ y)
ψs-⊵ (Ωₗ k h) ε B j (inu ws) β (up x c y) =
  ⊴-trans (ψs-⊵ (Ωₗ k h) ε B j (inu ws) β x)
    (ψs-⊵ (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) j (ws c) _ y)
ψs-⊵ (Ωₗ k h) ε B j (inb c′ w) β (up x c y) =
  ⊴-trans (ψs-⊵ (Ωₗ k h) ε B j (inb c′ w) β x) (+ι⊴ _ _)
```

底的条件: 逐分量不低于标准底 (第一位置序的自反闭包). 对孩子的底封闭.

```agda
OKB : (ℓ : LF) → Base ℓ → Set
OKB ℓ B = (zero ⊢ suc zero ⊴ b⊥ B) × ((j : LF) (w : j ≤ ℓ) → j ⊢ Ωt j ⊴ bs B j w)

ok-B₀ : (ℓ : LF) → OKB ℓ (B₀ ℓ)
ok-B₀ ℓ = ⊴r , λ j w → ⊴r

ok-dS : ∀ {a} (ε : Ev (suc a)) (B : Base (suc a)) → OKB (suc a) B → (t : Tr (suc a)) → OKB a (dS a ε B t)
ok-dS {a} ε B ok t = ⊴-trans (proj₁ ok) (ψ⊥-⊵ (suc a) ε B t)
  , λ j w → ⊴-trans (proj₂ ok j (ins w)) (ψs-⊵ (suc a) ε B j (ins w) _ t)

ok-dL : (g : ℕ → LF) (ε : Ev (lim g)) (B : Base (lim g)) → OKB (lim g) B → (n : ℕ) (t : Tr (lim g))
  → OKB (g n) (dL g ε B n t)
ok-dL g ε B ok n t = ⊴-trans (proj₁ ok) (ψ⊥-⊵ (lim g) ε B t)
  , λ j w → ⊴-trans (proj₂ ok j (inl n w)) (ψs-⊵ (lim g) ε B j (inl n w) _ t)
```

## 后继层号: 层号事实与保留判定

```agda
data FinL : LF → Set where
  fz : FinL zero
  fs : ∀ {a} → FinL a → FinL (suc a)

noL : ∀ {g} {A : Set} → FinL (lim g) → A
noL ()

noW : ∀ {k h} {A : Set} → FinL (Ωₗ k h) → A
noW ()

finW : ∀ {j ℓ} → j ≤ ℓ → FinL ℓ → FinL j
finW self    f      = f
finW (ins w) (fs f) = finW w f

at-fin : ∀ {ℓ} → FinL ℓ → (p : Pos ℓ) → FinL (at ℓ p)
at-fin (fs f) (inj₁ _) = f
at-fin (fs f) (inj₂ p) = at-fin f p

POS : ∀ {m} → FinL m → (s : Pos m) → ∀ {j i} → Corr j (at m s) → Corr i m → j ≺ᴵ i
POS (fs f) (inj₁ _) cj (cs c) = L.via (Corr-uniq cj c) L.zero
POS (fs f) (inj₂ r) cj (cs c) = L.≺-suc (POS f r cj c)

notBelow : ∀ {j a} (w : j ≤ a) → FinL a → ∀ {i i′} → Corr i j → Corr i′ a → ¬ (i′ ≺ᴵ i)
notBelow self    f      ci ci′      lt = L.≺ᴵ-irrefl (L.≺ᴵ-respˡ (Corr-uniq ci ci′) lt)
notBelow (ins w) (fs f) ci (cs ci″) lt =
  notBelow w f ci ci″ (L.≺ᴵ-trans (L.via (L.≅ᴵ-refl _) L.zero) lt)

record Keep (lv : LF) (BrT : Set) (RP : ∀ {i} → L.Ordᶜ i → BrT → Set)
            (j : LF) (q : Pos j) (cv : Br j q → BrT) : Set where
  field
    lev   : at j q ≡ lv
    conv  : ∀ {i} {y : L.Ordᶜ i} {c : Br j q} → RelP j q y c → RP y (cv c)
    below : ∀ {i′ i} → Corr i′ lv → Corr i j → i′ ≺ᴵ i

Dflt : LF → LF → Set
Dflt lv j = ∀ {i′ i} → Corr i′ lv → Corr i j → ¬ (i′ ≺ᴵ i)

mutual
  kpF : ∀ {ℓ} (f : FinL ℓ) (ε : Ev ℓ) (p : Pos ℓ) {j : LF} (w : j ≤ ℓ) {X : Set} (R : X → Set)
    {K : (q : Pos j) → (Br j q → Br ℓ p) → X} {d : X}
    → ((q : Pos j) (cv : Br j q → Br ℓ p) → Keep (at ℓ p) (Br ℓ p) (RelP ℓ p) j q cv → R (K q cv))
    → (Dflt (at ℓ p) j → R d) → R (kp ℓ ε p w K d)
  kpF f ε p self R hk hd =
    hk p (λ z → z) (record { lev = refl ; conv = λ r → r ; below = λ cj ci → POS f p cj ci })
  kpF (fs f) ε p (ins w) R hk hd = kpF⁼ f ε p w R hk hd

  kpF⁼ : ∀ {a} (f : FinL a) (ε : Ev a) (p : Pos⁼ a) {j : LF} (w : j ≤ a) {X : Set} (R : X → Set)
    {K : (q : Pos j) → (Br j q → Br⁼ a p) → X} {d : X}
    → ((q : Pos j) (cv : Br j q → Br⁼ a p) → Keep (at⁼ a p) (Br⁼ a p) (RelP⁼ a p) j q cv → R (K q cv))
    → (Dflt (at⁼ a p) j → R d) → R (kp⁼ a ε p w K d)
  kpF⁼ f ε (inj₁ _) w R hk hd = hd (λ ci′ ci → notBelow w f ci ci′)
  kpF⁼ f ε (inj₂ p) w R hk hd = kpF f ε p w R hk hd
```

## 槽位关系的换型

都按层号的形状逐情形给出, 每一情形是恒等; 没有沿命题相等的搬运, 只有层号对应 `Corr` 沿 `at-mv` 换一次.

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

```agda
START : ∀ {m i} → FinL m → Corr i m → Rel m (L.Ω i) (Ωt m)
START fz     cz     = ss zr
START (fs f) (cs c) = nd c (λ y₀ c₀ sl → ur (psh {Γ = []} (wk (emb zero sl) ◃s)))
```

## 沿帧的折叠状态

`fo ε B w`: 深层仍在按标准底折到目标 (路径 w); `uf d b`: 目标已是某个祖先层自身, 深层在上折. `nxt` 是过一帧 (这里只对后继层; ℕ 极限与 `Ωₗ` 的帧是留空的情形).

```agda
data St (j jd : LF) : Set where
  fo : Ev jd → Base jd → j ≤ jd → St j jd
  uf : Dn j jd → Tr j → St j jd

run : ∀ {j jd} → St j jd → Tr jd → Tr j
run {j} {jd} (fo ε B w) y = ψs jd ε B j w (bs B j w) y
run {j} {jd} (uf d b)   y = Up jd d b y

nxt : ∀ {j a} → St j (suc a) → Tr (suc a) → St j a
nxt {a = a} (fo ε B self)    t = uf (down stop tt) (ψs (suc a) ε B (suc a) self (bs B (suc a) self) t)
nxt {a = a} (fo ε B (ins w)) t = fo ε (dS a ε B t) w
nxt {a = a} (uf d b)         t = uf (down d tt) (Up (suc a) d b t)

run-up : ∀ {j a} (s : St j (suc a)) (t : Tr (suc a)) (y : Tr a) → run s (up t tt y) ≡ run (nxt s t) y
run-up (fo ε B self)    t y = refl
run-up (fo ε B (ins w)) t y = refl
run-up (uf d b)         t y = refl

nxt-⊵ : ∀ {j a} (s : St j (suc a)) (t : Tr (suc a)) (y : Tr a) → j ⊢ run s t ⊴ run (nxt s t) y
nxt-⊵ {a = a} (fo ε B self)    t y = Up-⊵ a (down stop tt) _ y
nxt-⊵ {j} {a} (fo ε B (ins w)) t y = ψs-⊵ a ε (dS a ε B t) j w _ y
nxt-⊵ {a = a} (uf d b)         t y = Up-⊵ a (down d tt) _ y

stOf : ∀ {ℓ j} → FinL ℓ → St j ℓ → ∀ {jd} {d : Dc ℓ jd} → Ctx ℓ d → St j jd
stOf f      s []          = s
stOf (fs f) s (fr t _ Γ)  = stOf f (nxt s t) Γ
stOf fz     s (fr t () Γ)

finD : ∀ {ℓ} → FinL ℓ → ∀ {jd} {d : Dc ℓ jd} → Ctx ℓ d → FinL jd
finD f      []          = f
finD (fs f) (fr t _ Γ)  = finD f Γ
finD fz     (fr t () Γ)

stOf-▹ : ∀ {ℓ j a} (f : FinL ℓ) (s : St j ℓ) {d : Dc ℓ (suc a)} (Γ : Ctx ℓ d) (t : Tr (suc a))
  → stOf f s (snocC Γ t tt) ≡ nxt (stOf f s Γ) t
stOf-▹ (fs f) s []          t = refl
stOf-▹ (fs f) s (fr t′ _ Γ) t = stOf-▹ f (nxt s t′) Γ t
stOf-▹ fz     s (fr t′ () Γ) t

deepOf : ∀ {ℓ} → FinL ℓ → Ev ℓ → Base ℓ → ∀ {jd} {d : Dc ℓ jd} → Ctx ℓ d → Ev jd × Base jd
deepOf f      ε B []          = ε , B
deepOf (fs f) ε B (fr t _ Γ)  = deepOf f ε (dS _ ε B t) Γ
deepOf fz     ε B (fr t () Γ)

stepD : ∀ {a} → Ev (suc a) × Base (suc a) → Tr (suc a) → Ev a × Base a
stepD {a} (ε , B) t = ε , dS a ε B t

deepOf-▹ : ∀ {ℓ a} (f : FinL ℓ) (ε : Ev ℓ) (B : Base ℓ) {d : Dc ℓ (suc a)} (Γ : Ctx ℓ d) (t : Tr (suc a))
  → deepOf f ε B (snocC Γ t tt) ≡ stepD (deepOf f ε B Γ) t
deepOf-▹ (fs f) ε B []          t = refl
deepOf-▹ (fs f) ε B (fr t′ _ Γ) t = deepOf-▹ f ε (dS _ ε B t′) Γ t
deepOf-▹ fz     ε B (fr t′ () Γ) t

ok-deep : ∀ {ℓ} (f : FinL ℓ) (ε : Ev ℓ) (B : Base ℓ) → OKB ℓ B → ∀ {jd} {d : Dc ℓ jd} (Γ : Ctx ℓ d)
  → OKB jd (proj₂ (deepOf f ε B Γ))
ok-deep f      ε B ok []          = ok
ok-deep (fs f) ε B ok (fr t _ Γ)  = ok-deep f ε (dS _ ε B t) (ok-dS ε B ok t) Γ
ok-deep fz     ε B ok (fr t () Γ)

liftW : ∀ {ℓ} → FinL ℓ → ∀ {jd} {d : Dc ℓ jd} → Ctx ℓ d → ∀ {j} → j ≤ jd → j ≤ ℓ
liftW f      []          w = w
liftW (fs f) (fr t _ Γ)  w = ins (liftW f Γ w)
liftW fz     (fr t () Γ) w

stOf-fo : ∀ {ℓ} (f : FinL ℓ) (ε : Ev ℓ) (B : Base ℓ) {jd} {d : Dc ℓ jd} (Γ : Ctx ℓ d) {j} (w′ : j ≤ jd)
  → stOf f (fo ε B (liftW f Γ w′)) Γ ≡ fo (proj₁ (deepOf f ε B Γ)) (proj₂ (deepOf f ε B Γ)) w′
stOf-fo f      ε B []          w′ = refl
stOf-fo (fs f) ε B (fr t _ Γ)  w′ = stOf-fo f ε (dS _ ε B t) Γ w′
stOf-fo fz     ε B (fr t () Γ) w′

uf-stays : ∀ {ℓ j} (f : FinL ℓ) (d₀ : Dn j ℓ) (b : Tr j) {jd} {d : Dc ℓ jd} (Γ : Ctx ℓ d)
  {ε′ : Ev jd} {B′ : Base jd} {w′ : j ≤ jd} → stOf f (uf d₀ b) Γ ≡ fo ε′ B′ w′ → ⊥
uf-stays f      d₀ b []          ()
uf-stays (fs f) d₀ b (fr t _ Γ)  e = uf-stays f _ _ Γ e
uf-stays fz     d₀ b (fr t () Γ) e

fo-inv : ∀ {ℓ j} (f : FinL ℓ) (ε : Ev ℓ) (B : Base ℓ) (w : j ≤ ℓ) {jd} {d : Dc ℓ jd} (Γ : Ctx ℓ d)
  {ε′ : Ev jd} {B′ : Base jd} {w′ : j ≤ jd} → stOf f (fo ε B w) Γ ≡ fo ε′ B′ w′
  → (deepOf f ε B Γ ≡ (ε′ , B′)) × (w ≡ liftW f Γ w′)
fo-inv f      ε B w       []          refl = refl , refl
fo-inv (fs f) ε B self    (fr t _ Γ)  e = ⊥-elim (uf-stays f _ _ Γ e)
fo-inv (fs f) ε B (ins w) (fr t _ Γ)  e =
  proj₁ (fo-inv f ε (dS _ ε B t) w Γ e) , cong ins (proj₂ (fo-inv f ε (dS _ ε B t) w Γ e))
fo-inv fz     ε B w       (fr t () Γ) e
```

## 主引理与值引理

`MS`: 参照的 ψ (目标层号 i 与 j 对应) 对着深层状态的折叠. 结点处先按参照的三歧分情况, 再用 `kpF` (折叠中) 或上折的保留 (上折中) 对上; 不一致的组合由层号事实排除. 默认情形两边都是链 (`chainS`), 参照从 Ω 起, 块从 0 起, 差一步.
`VS`: ψ⁰ 对着 `ψ⊥` 的读回.

```agda
J′ : (ℓ : LF) → ∀ {j} {d : Dc ℓ j} → Ctx ℓ d → ∀ {k} → L.Ordᶜ k → Tr j → Set
J′ ℓ = Sim.J ℓ (SlOf ℓ)

Wch : ∀ {i′ K′} (q : i′ <ᴵ K′) (f′ : L.U i′ (L.<→◃ q) → L.Ordᶜ K′) → ℕ → L.Ordᶜ i′
Wch {i′} q f′ = iterᴸ (λ x → L.ψ q (λ r → r) (f′ (L.into (L.<→◃ q) x))) (L.Ω i′)

Dref : ∀ {i′ K′ L⁺ i} (p₀ : i <ᴵ L⁺) (σ : L.Simᴵ K′ L⁺) (q : i′ <ᴵ K′) (f′ : L.U i′ (L.<→◃ q) → L.Ordᶜ K′)
  → L.Ordᶜ i
Dref p₀ σ q f′ = L.lim (λ n → L.ψ p₀ σ (f′ (L.into (L.<→◃ q) (Wch q f′ n))))

Vch : ∀ {jd} (ε′ : Ev jd) (B′ : Base jd) (p : Pos jd) (g : Br jd p → Tr jd) → ℕ → Br jd p
Vch {jd} ε′ B′ p g =
  iter (λ z → fromBr jd p (ψs jd ε′ B′ (at jd p) (posW jd p) (bs B′ (at jd p) (posW jd p)) (g z)))
       (fromBr jd p zero)

module M {ℓ : LF} (f : FinL ℓ) (ε : Ev ℓ) (B : Base ℓ) (ok : OKB ℓ B) where

  okD : ∀ {jd} {d : Dc ℓ jd} (Γ : Ctx ℓ d) (eb : Ev jd × Base jd) → deepOf f ε B Γ ≡ eb → OKB jd (proj₂ eb)
  okD Γ eb de = subst (λ x → OKB _ (proj₂ x)) de (ok-deep f ε B ok Γ)

  mutual
    MS : ∀ {j} (w : j ≤ ℓ) {jd} {d : Dc ℓ jd} {Γ : Ctx ℓ d} (s : St j jd) → s ≡ stOf f (fo ε B w) Γ
       → ∀ {k} {X : L.Ordᶜ k} {y : Tr jd} → J′ ℓ Γ X y
       → ∀ {L⁺ i} (p₀ : i <ᴵ L⁺) → Corr i j → (σ : L.Simᴵ k L⁺) → Rel j (L.ψ p₀ σ X) (run s y)
    MS {j} w s eq (zr {y = y}) p₀ ci σ =
      subst (λ s → Rel j (L.Ω _) (run s y)) (sym eq)
        (Rel-⊴ (START (finW w f) ci) (⊴-trans (proj₂ ok j w) (ψs-⊵ ℓ ε B j w _ y)))
    MS w s eq (pop {j = zero} {c = ()} r) p₀ ci σ
    MS w s eq (pop {j = lim g} {Γ = Γ₀} r) p₀ ci σ = noL (finD f Γ₀)
    MS w s eq (pop {j = Ωₗ k h} {Γ = Γ₀} r) p₀ ci σ = noW (finD f Γ₀)
    MS {j} w s eq (pop {j = suc a} {Γ = Γ₀} {t = t} {c = tt} {y = y} r) p₀ ci σ =
      subst (λ s → Rel j _ (run s y)) (sym (trans eq (stOf-▹ f (fo ε B w) Γ₀ t)))
        (Rel-⊴ (MS w (stOf f (fo ε B w) Γ₀) refl r p₀ ci σ) (nxt-⊵ (stOf f (fo ε B w) Γ₀) t y))
    MS {j} w (fo ε′ B′ w′) eq (ss r) p₀ ci σ = Add.nextL j (SlOf j) (MS w (fo ε′ B′ w′) eq r p₀ ci σ)
    MS {j} w (uf d b) eq (ss r) p₀ ci σ = Add.nextL j (SlOf j) (MS w (uf d b) eq r p₀ ci σ)
    MS {j} w {jd} (fo ε′ B′ w′) eq (wk r e) p₀ ci σ =
      wk (MS w (fo ε′ B′ w′) eq r p₀ ci σ) (monos jd ε′ B′ j w′ (bs B′ j w′) e)
    MS {j} w {jd} (uf d b) eq (wk r e) p₀ ci σ = wk (MS w (uf d b) eq r p₀ ci σ) (Up-mono jd d b e)
    MS w (fo ε′ B′ w′) eq (ll h) p₀ ci σ = ll (λ n → MS w (fo ε′ B′ w′) eq (h n) p₀ ci σ)
    MS w (uf d b) eq (ll h) p₀ ci σ = ll (λ n → MS w (uf d b) eq (h n) p₀ ci σ)
    MS {j} w {jd} {Γ = Γ} (uf d b) eq (nd {q = q} {f = f′} {p = p} {g = g} lv h) p₀ ci σ
      with L.<ᴵ-dec (σ q) p₀
    ... | injᵃ (L.via e r) =
      nd (subst (Corr _) (sym (at-mv d p)) (Corr-≅ (L.≅ᴵ-sym e) lv))
        (λ y₀ c′ sl →
          subst (λ u → Rel j (L.ψ p₀ σ (f′ (L.into (L.<→◃ q) (L.tr⁻ e u)))) (Up jd d b (g (mvBr d p c′))))
            (sym (L.out-into (L.<→◃ r) y₀))
            (MS w (uf d b) eq
              (h (L.tr⁻ e y₀) (mvBr d p c′) (toSl ℓ _ p (mvRel d p (TRC.tr⁻ᴿ (trP j (mv d p)) e sl))))
              p₀ ci σ))
    ... | injᵇ x = ⊥-elim (L.clash₁ (L.≅ᴵ-refl _) (L.≅ᴵ-refl _)
        (POS (finW w f) (mv d p) (subst (Corr _) (sym (at-mv d p)) lv) ci) x)
    ... | injᶜ x = ⊥-elim (L.clash₂ (L.≅ᴵ-refl _) (L.≅ᴵ-refl _)
        (POS (finW w f) (mv d p) (subst (Corr _) (sym (at-mv d p)) lv) ci) x)
    MS {j} w {jd} {Γ = Γ} (fo ε′ B′ w′) eq (nd {q = q} {f = f′} {p = p} {g = g} lv h) p₀ ci σ
      with L.<ᴵ-dec (σ q) p₀
    ... | injᵃ (L.via e r) =
      kpF (finD f Γ) ε′ p w′
        (λ T → Rel j (L.limᵢ r (λ u → L.ψ p₀ σ (f′ (L.into (L.<→◃ q) (L.tr⁻ e (L.out (L.<→◃ r) u)))))) T)
        (λ q′ cv kf → nd (subst (Corr _) (sym (Keep.lev kf)) (Corr-≅ (L.≅ᴵ-sym e) lv))
          (λ y₀ c′ sl →
            subst (λ u → Rel j (L.ψ p₀ σ (f′ (L.into (L.<→◃ q) (L.tr⁻ e u))))
                               (ψs jd ε′ B′ j w′ (bs B′ j w′) (g (cv c′))))
              (sym (L.out-into (L.<→◃ r) y₀))
              (MS w (fo ε′ B′ w′) eq
                (h (L.tr⁻ e y₀) (cv c′) (toSl ℓ _ p (Keep.conv kf (TRC.tr⁻ᴿ (trP j q′) e sl))))
                p₀ ci σ)))
        (λ df → ⊥-elim (df lv ci (L.via e r)))
    ... | injᵇ x =
      kpF (finD f Γ) ε′ p w′ (λ T → Rel j (Dref p₀ σ q f′) T)
        (λ q′ cv kf → ⊥-elim (L.clash₁ (L.≅ᴵ-refl _) (L.≅ᴵ-refl _) (Keep.below kf lv ci) x))
        (λ _ → Mdef w Γ ε′ B′ w′ eq (proj₁ (fo-inv f ε B w Γ (sym eq))) lv h p₀ ci σ)
    ... | injᶜ x =
      kpF (finD f Γ) ε′ p w′ (λ T → Rel j (Dref p₀ σ q f′) T)
        (λ q′ cv kf → ⊥-elim (L.clash₂ (L.≅ᴵ-refl _) (L.≅ᴵ-refl _) (Keep.below kf lv ci) x))
        (λ _ → Mdef w Γ ε′ B′ w′ eq (proj₁ (fo-inv f ε B w Γ (sym eq))) lv h p₀ ci σ)
    MS w s eq (ur r) p₀ ci σ = MS w s eq r p₀ ci (λ q → σ (L.suc q))
    MS w s eq (psh {j = zero} {c = ()} r) p₀ ci σ
    MS w s eq (psh {j = lim g} {Γ = Γ₀} r) p₀ ci σ = noL (finD f Γ₀)
    MS w s eq (psh {j = Ωₗ k h} {Γ = Γ₀} r) p₀ ci σ = noW (finD f Γ₀)
    MS {j} w s eq (psh {j = suc a} {Γ = Γ₀} {t = t} {c = tt} {y = y} r) p₀ ci σ =
      subst (λ s → Rel j _ (run s (up t tt y))) (sym eq)
        (subst (Rel j _) (sym (run-up (stOf f (fo ε B w) Γ₀) t y))
          (subst (λ s → Rel j _ (run s y)) (stOf-▹ f (fo ε B w) Γ₀ t)
            (MS w (stOf f (fo ε B w) (snocC Γ₀ t tt)) refl r p₀ ci σ)))

    Mdef : ∀ {j} (w : j ≤ ℓ) {jd} {d : Dc ℓ jd} (Γ : Ctx ℓ d) (ε′ : Ev jd) (B′ : Base jd) (w′ : j ≤ jd)
      → fo ε′ B′ w′ ≡ stOf f (fo ε B w) Γ → deepOf f ε B Γ ≡ (ε′ , B′)
      → ∀ {i′ K′} {q : i′ <ᴵ K′} {f′ : L.U i′ (L.<→◃ q) → L.Ordᶜ K′} {p : Pos jd} {g : Br jd p → Tr jd}
      → Corr i′ (at jd p)
      → (∀ (y₀ : L.Ordᶜ i′) (c : Br jd p) → SlOf ℓ d p y₀ c → J′ ℓ Γ (f′ (L.into (L.<→◃ q) y₀)) (g c))
      → ∀ {L⁺ i} (p₀ : i <ᴵ L⁺) → Corr i j → (σ : L.Simᴵ K′ L⁺)
      → Rel j (Dref p₀ σ q f′) (lim (cum (λ n → ψs jd ε′ B′ j w′ (bs B′ j w′) (g (Vch ε′ B′ p g n)))))
    Mdef {j} w {jd} Γ ε′ B′ w′ eq de {q = q} {f′ = f′} {p = p} {g = g} lv h p₀ ci σ =
      ll (λ n → Add.inCum j (SlOf j) (λ m → ψs jd ε′ B′ j w′ (bs B′ j w′) (g (Vch ε′ B′ p g m))) (suc n)
        (MS w (fo ε′ B′ w′) eq
          (h (Wch q f′ n) (Vch ε′ B′ p g (suc n)) (toSl ℓ _ p (chainS Γ ε′ B′ de lv h n))) p₀ ci σ))

    chainS : ∀ {jd} {d : Dc ℓ jd} (Γ : Ctx ℓ d) (ε′ : Ev jd) (B′ : Base jd) → deepOf f ε B Γ ≡ (ε′ , B′)
      → ∀ {i′ K′} {q : i′ <ᴵ K′} {f′ : L.U i′ (L.<→◃ q) → L.Ordᶜ K′} {p : Pos jd} {g : Br jd p → Tr jd}
      → Corr i′ (at jd p)
      → (∀ (y₀ : L.Ordᶜ i′) (c : Br jd p) → SlOf ℓ d p y₀ c → J′ ℓ Γ (f′ (L.into (L.<→◃ q) y₀)) (g c))
      → ∀ n → RelP jd p (Wch q f′ n) (Vch ε′ B′ p g (suc n))
    chainS {jd} Γ ε′ B′ de {p = p} {g = g} lv h zero =
      relFrom jd p (Rel-⊴ (START (at-fin (finD f Γ) p) lv)
        (⊴-trans (proj₂ (okD Γ (ε′ , B′) de) (at jd p) (posW jd p))
                 (ψs-⊵ jd ε′ B′ (at jd p) (posW jd p) _ (g (fromBr jd p zero)))))
    chainS {jd} Γ ε′ B′ de {q = q} {f′ = f′} {p = p} {g = g} lv h (suc n) =
      relFrom jd p (MS (liftW f Γ (posW jd p)) (fo ε′ B′ (posW jd p))
        (subst (λ eb → fo (proj₁ eb) (proj₂ eb) (posW jd p) ≡ stOf f (fo ε B (liftW f Γ (posW jd p))) Γ)
          de (sym (stOf-fo f ε B Γ (posW jd p))))
        (h (Wch q f′ n) (Vch ε′ B′ p g (suc n)) (toSl ℓ _ p (chainS Γ ε′ B′ de lv h n)))
        q lv (λ r → r))

  VS : ∀ {jd} {d : Dc ℓ jd} {Γ : Ctx ℓ d} (eb : Ev jd × Base jd) → deepOf f ε B Γ ≡ eb
     → ∀ {k} {X : L.Ordᶜ k} {y : Tr jd} → J′ ℓ Γ X y
     → L.ψ⁰ X ≼ read (ψ⊥ jd (proj₁ eb) (proj₂ eb) y)
  VS eb de (zr {y = y}) =
    ≼-trans (⊴→≼ (proj₁ (okD [] eb de))) (⊴→≼ (ψ⊥-⊵ ℓ (proj₁ eb) (proj₂ eb) y))
  VS eb de (pop {j = zero} {c = ()} r)
  VS eb de (pop {j = lim g} {Γ = Γ₀} r) = noL (finD f Γ₀)
  VS eb de (pop {j = Ωₗ k h} {Γ = Γ₀} r) = noW (finD f Γ₀)
  VS eb de (pop {j = suc a} {Γ = Γ₀} {X = X} {t = t} {c = tt} {y = y} r) =
    subst (λ x → L.ψ⁰ X ≼ read (ψ⊥ a (proj₁ x) (proj₂ x) y)) (trans (sym (deepOf-▹ f ε B Γ₀ t)) de)
      (≼-trans (VS (deepOf f ε B Γ₀) refl r)
        (⊴→≼ (ψ⊥-⊵ a (proj₁ (deepOf f ε B Γ₀)) (dS a (proj₁ (deepOf f ε B Γ₀)) (proj₂ (deepOf f ε B Γ₀)) t) y)))
  VS {jd} eb de (ss {y = y} r) = next≽ (ψ⊥ jd (proj₁ eb) (proj₂ eb) y) (VS eb de r)
  VS {jd} eb de (wk {y = y} r e) =
    ≼-trans (VS eb de r) (⊑→≼ (read (ψ⊥ jd (proj₁ eb) (proj₂ eb) y)) (◃⊑ (mono⊥ jd (proj₁ eb) (proj₂ eb) e)))
  VS eb de (ll h) = l≼ (λ n → VS eb de (h n))
  VS {jd} {Γ = Γ} eb de (nd {q = q} {f = f′} {p = p} {g = g} lv h) =
    l≼ (λ n → limcum≽ (λ m → ψ⊥ jd (proj₁ eb) (proj₂ eb) (g (Vch (proj₁ eb) (proj₂ eb) p g m))) (suc n)
      (VS eb de (h (Wch q f′ n) (Vch (proj₁ eb) (proj₂ eb) p g (suc n))
        (toSl ℓ _ p (chainS Γ (proj₁ eb) (proj₂ eb) de lv h n)))))
  VS eb de (ur {X = X} r) = VS eb de {X = X} r
  VS eb de (psh {j = zero} {c = ()} r)
  VS eb de (psh {j = lim g} {Γ = Γ₀} r) = noL (finD f Γ₀)
  VS eb de (psh {j = Ωₗ k h} {Γ = Γ₀} r) = noW (finD f Γ₀)
  VS eb de (psh {j = suc a} {Γ = Γ₀} {X = X} {t = t} {c = tt} {y = y} r) =
    subst (λ x → L.ψ⁰ X ≼ read (ψ⊥ a (proj₁ x) (dS a (proj₁ x) (proj₂ x) t) y)) de
      (subst (λ x → L.ψ⁰ X ≼ read (ψ⊥ a (proj₁ x) (proj₂ x) y)) (deepOf-▹ f ε B Γ₀ t)
        (VS (deepOf f ε B (snocC Γ₀ t tt)) refl r))
```

## `lower-fin`

```agda
lower-fin : ∀ {ℓ i} (f : FinL ℓ) (ε : Ev ℓ) (B : Base ℓ) → OKB ℓ B → Corr i ℓ
  → L.ψ⁰ (L.Ω i) ≼ read (ψ⊥ ℓ ε B (Ωt ℓ))
lower-fin f ε B ok c = M.VS f ε B ok {Γ = []} (ε , B) refl (START f c)
```

## 留空的情形

- `nxt` 在 ℕ 极限层 `lim g` 的帧 (孩子 m): 目标 `inl n w` 而 m 与 n 不同号时是折叠的回退行, 结点是 `kp` 的不同号行; 模拟在这两行上没有可用的规则 (`YiUpLimRows`). 同号, `inlu`, 自身三种情形与后继层同形.
- `POS` 与 `notBelow` 在 ℕ 极限层: 槽位 `(n , inj₁ tt)` (孩子层 g n 自身) 的层号低于 `lim g` 需要相邻项之间的路径.
- `Ωₗ` 层: 参照框架没有对应的层号 (`Corr` 没有这一种).
