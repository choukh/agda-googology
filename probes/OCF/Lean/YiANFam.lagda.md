# 验收: 按层号递归的记号直连关系族, 折到自身的保持 (一切有限层号)

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提, 对一切有限层号 n.
> `M n` 是 `YiMEBase.Mᴰ` 在层号 `fin n` 上的实例, 对 n 递归 (`M 0` 就是 `M⁰`); `Mβ`: Ω 树对着 Ω_{n+1}; `Pu`: 任意深度的上折保持; `Self.PF`: 折到自身带前缀的保持; `Self.sγ`: 回灌链对着 γ-链.
> 记号一侧: 层号是 `natT i` 时共尾比较的化简 (`cmp-gt`, `cmp-pen`). 不涉及折到低层 (见 [YiANLv](YiANLv.lagda.md)), 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiANFam where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins; Ev; Rt)
open import OCF.Lean.YiLegFold
import OCF.Align.EboLeanDef as E
open E using (cof; c1; cω; cΩ; pred; fsn; fsT; γT; ψ; 𝟏; natT; sucT; cmpᵀ; lt; eq; gt; cofψ₊; fsnc; fsTc)
open import OCF.Lean.YiMEBase hiding (Rt)
open import OCF.Lean.YiMENote
open import OCF.Lean.YiMEAnchor using (M¹; ++[]; module G⁰)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
```

## 有限层号与关系族

`slot n p` 是层号 `fin (suc n)` 上槽位 p 的分支所在的层号. `Lw n p` 是该槽位上分支的关系 (`M (slot n p)`), `Nw n p ν` 说共尾下标是 `natT (slot n p)`.

```agda
fin : ℕ → L
fin zero    = zero
fin (suc n) = suc (fin n)

slot : (n : ℕ) → Pos (fin (suc n)) → ℕ
slot n       (inj₁ _) = n
slot (suc n) (inj₂ p) = slot n p
slot zero    (inj₂ ())

slot≤ : ∀ n p → slot n p ≤ⁿ n
slot≤ zero    (inj₁ _) = z≤n
slot≤ (suc n) (inj₁ _) = s≤s (slot≤ n (inj₁ tt))
slot≤ (suc n) (inj₂ p) = ≤s (slot≤ n p)
  where
  ≤s : ∀ {a b} → a ≤ⁿ b → a ≤ⁿ suc b
  ≤s z≤n     = z≤n
  ≤s (s≤s l) = s≤s (≤s l)
slot≤ zero    (inj₂ ())

Nw : (n : ℕ) → Pos (fin (suc n)) → E.T → Set
Nw n p ν = ν ≡ natT (slot n p)

mutual
  M : (n : ℕ) → E.T → Tr (fin n) → Set
  M zero    = M⁰
  M (suc n) = Mᴰ (Sig (fin (suc n))) (Lw n) (λ _ → M n) (Nw n)

  Lw : (n : ℕ) (p : Pos (fin (suc n))) → E.T → Br (fin (suc n)) p → Set
  Lw n       (inj₁ _) = M n
  Lw (suc n) (inj₂ p) = Lw n p
  Lw zero    (inj₂ ())

module GM (n : ℕ) = Gen {Sig (fin (suc n))} {Lw n} {λ _ → M n} {Nw n}

mwN : ∀ n {s x x′} → M n s x → fin n ⊢ x ◃ x′ → M n s x′
mwN zero    = mw
mwN (suc n) = mw

m⊴N : ∀ n {s x x′} → M n s x → x ⊴ x′ → M n s x′
m⊴N n m ⊴r     = m
m⊴N n m (⊴◃ d) = mwN n m d

mzN : ∀ n {x} → M n [] x
mzN zero    = mz
mzN (suc n) = mz

mLN : ∀ n {s x} → cof s ≡ cω → (∀ k → M n (fsn s k) x) → M n s x
mLN zero    = mL
mLN (suc n) = mL

cumN : ∀ n {s} (G : ℕ → Tr (fin n)) (nz : ∀ k → fin n ⊢ zero ◃ G k) (k : ℕ) → M n s (G k) → M n s (limc G nz)
cumN zero    = G⁰.m-cum
cumN (suc n) = GM.m-cum n

to¹ : ∀ {s y} → M 1 s y → M¹ s y
to¹ mz                            = mz
to¹ (m1 e r)                      = m1 e (to¹ r)
to¹ (mL e h)                      = mL e (λ k → to¹ (h k))
to¹ (mΩ {p = inj₁ _} e nu h)      = mΩ e nu (λ η c l → to¹ (h η c l))
to¹ (mΩ {p = inj₂ ()} _ _ _)
to¹ (mU m ch)                     = mU (to¹ m) ch
to¹ (mw m d)                      = mw (to¹ m) d
```

## 记号一侧: 层号是自然数时的化简

`ψᴺ i a` 是 ψ_i(a), `Ωᴺ i` 是 Ω_i. `sucT (natT a)` 与 `natT b` 的比较: b ≤ a 时是 `gt` (规则 6), a < b 时是 `lt` 或 `eq` (规则 5Ω, `Pen`).

```agda
ψᴺ : ℕ → E.T → E.T
ψᴺ i a = ψ (natT i) a ∷ []

Ωᴺ : ℕ → E.T
Ωᴺ i = ψᴺ i []

cof-nat : ∀ i → cof (natT (suc i)) ≡ c1
cof-nat zero    = refl
cof-nat (suc i) = cof-nat i

pred-nat : ∀ i → pred (natT (suc i)) ≡ natT i
pred-nat zero    = refl
pred-nat (suc i) = cong (𝟏 ∷_) (pred-nat i)

cofΩ : ∀ i → cof (Ωᴺ (suc i)) ≡ cΩ (natT i)
cofΩ i = trans (cong (E.cofψ0 (natT (suc i))) (cof-nat i)) (cong cΩ (pred-nat i))

fsTΩ : ∀ i η → fsT (Ωᴺ (suc i)) η ≡ η
fsTΩ i η = cong (λ c → E.fsT0 (natT (suc i)) c η) (cof-nat i)

Pen : E.Cmp → Set
Pen m = (m ≡ lt) ⊎ (m ≡ eq)

cmp-gt : ∀ {b a} → b ≤ⁿ a → cmpᵀ (sucT (natT a)) (natT b) ≡ gt
cmp-gt {b = zero} {a = zero}  z≤n = refl
cmp-gt {b = zero} {a = suc a} z≤n = refl
cmp-gt {b = suc b} {a = suc a} (s≤s l) = cmp-gt {b = b} {a = a} l

cmp-pen : ∀ {a b} → suc a ≤ⁿ b → Pen (cmpᵀ (sucT (natT a)) (natT b))
cmp-pen {a = zero}  {b = suc zero}    (s≤s z≤n) = inj₂ refl
cmp-pen {a = zero}  {b = suc (suc b)} (s≤s z≤n) = inj₁ refl
cmp-pen {a = suc a} {b = suc b}       (s≤s l)   = cmp-pen {a = a} {b = b} l

cofK : ∀ u b {ν} → Pen (cmpᵀ (sucT ν) u) → cof b ≡ cΩ ν → cof (ψ u b ∷ []) ≡ cΩ ν
cofK u b {ν} (inj₁ q) e = trans (cofψΩ u b e) (cong (cofψ₊ u ν) q)
cofK u b {ν} (inj₂ q) e = trans (cofψΩ u b e) (cong (cofψ₊ u ν) q)

fsTK : ∀ u b {ν} η → Pen (cmpᵀ (sucT ν) u) → cof b ≡ cΩ ν → fsT (ψ u b ∷ []) η ≡ ψ u (fsT b η) ∷ []
fsTK u b {ν} η (inj₁ q) e = trans (fsTψΩ u b η e) (cong (λ m → fsTc u b ν m η) q)
fsTK u b {ν} η (inj₂ q) e = trans (fsTψΩ u b η e) (cong (λ m → fsTc u b ν m η) q)

cofG : ∀ u b {ν} → cmpᵀ (sucT ν) u ≡ gt → cof b ≡ cΩ ν → cof (ψ u b ∷ []) ≡ cω
cofG u b {ν} q e = trans (cofψΩ u b e) (cong (cofψ₊ u ν) q)

fsnG : ∀ u b {ν} k → cmpᵀ (sucT ν) u ≡ gt → cof b ≡ cΩ ν → fsn (ψ u b ∷ []) k ≡ ψ u (fsT b (γT b ν k)) ∷ []
fsnG u b {ν} k q e = trans (fsnψΩ u b k e) (cong (λ m → fsnc u b ν m k) q)

penN : ∀ n p {ν} → Nw n p ν → Pen (cmpᵀ (sucT ν) (natT (suc n)))
penN n p refl = cmp-pen (s≤s (slot≤ n p))
```

## Ω 树

```agda
Mβ : ∀ n → M (suc n) (Ωᴺ (suc n)) (Ωt (fin (suc n)))
Mβ n = mΩ (cofΩ n) refl
  (λ η c l → subst (λ s → M (suc n) s (up zero tt (suc c) (z◃s c))) (sym (fsTΩ n η)) (mU mz (mwN n l ◃s)))
```

## 上折的保持, 任意深度

`FD N j`: 从层号 N 向下走到 j 的一串后继孩子; `dn` 把它读成块上的 `Dn`. 槽位沿它搬上去, 所在层号不变 (`mvS`), 分支的关系对应 (`mvL`).

```agda
data FD (N : ℕ) : ℕ → Set where
  fd0 : FD N N
  fds : ∀ {j} → FD N (suc j) → FD N j

dn : ∀ {N j} → FD N j → Dn (fin N) (fin j)
dn fd0     = stop
dn (fds d) = down (dn d) tt

mvS : ∀ {N j} (d : FD (suc N) (suc j)) (p : Pos (fin (suc j))) → slot N (mv (dn d) p) ≡ slot j p
mvS fd0     p = refl
mvS (fds d) p = mvS d (inj₂ p)

mvN : ∀ {N j} (d : FD (suc N) (suc j)) (p : Pos (fin (suc j))) {ν} → Nw j p ν → Nw N (mv (dn d) p) ν
mvN d p nu = trans nu (cong natT (sym (mvS d p)))

mvL : ∀ {N j} (d : FD (suc N) (suc j)) (p : Pos (fin (suc j))) {η} (c : Br (fin (suc N)) (mv (dn d) p))
    → Lw N (mv (dn d) p) η c → Lw j p η (mvBr (dn d) p c)
mvL fd0     p c l = l
mvL (fds d) p c l = mvL d (inj₂ p) c l

Pu⁰ : ∀ {N} (d : FD (suc N) zero) (b : Tr (fin (suc N))) (nb : fin (suc N) ⊢ zero ◃ b) {t}
    → M (suc N) (ψᴺ (suc N) t) b
    → ∀ {s y} → M⁰ s y → M (suc N) (ψᴺ (suc N) (t ++ s)) (Up zero (dn d) b nb y)
Pu⁰ {N} d b nb {t} mb (mz {x = y}) =
  ++[] (λ r → M (suc N) (ψᴺ (suc N) r) (Up zero (dn d) b nb y)) t
    (GM.m-zl N (Up zero (dn d) b nb) (Up-mono zero (dn d) b nb) mb y)
Pu⁰ {N} d b nb {t} mb (m1 {t = s} {x = y} e r) =
  GM.m-next N (Up-nz zero (dn d) b nb y) (cofψ1 (natT (suc N)) (t ++ s) (cof++1 t s e))
    (λ k → trans (fsnψ1 (natT (suc N)) (t ++ s) k (cof++1 t s e))
             (cong (λ r → replicate k (ψ (natT (suc N)) r)) (pred++ t s e)))
    (Pu⁰ d b nb mb r)
Pu⁰ {N} d b nb {t} mb (mL {t = s} {x = y} e h) =
  mL (cofψω (natT (suc N)) (t ++ s) (cof++ω t s e))
    (λ k → subst (λ r → M (suc N) r (Up zero (dn d) b nb y))
      (sym (trans (fsnψω (natT (suc N)) (t ++ s) k (cof++ω t s e)) (cong (ψᴺ (suc N)) (fsn++ t s k e))))
      (Pu⁰ d b nb mb (h k)))
Pu⁰ d b nb mb (mΩ {p = ()} _ _ _)
Pu⁰ d b nb mb (mU {c = ()} _ _)
Pu⁰ d b nb mb (mw m r) = mw (Pu⁰ d b nb mb m) (Up-mono zero (dn d) b nb r)

mutual
  Pu : ∀ {N} j (d : FD (suc N) j) (b : Tr (fin (suc N))) (nb : fin (suc N) ⊢ zero ◃ b) {t}
     → M (suc N) (ψᴺ (suc N) t) b
     → ∀ {s y} → M j s y → M (suc N) (ψᴺ (suc N) (t ++ s)) (Up (fin j) (dn d) b nb y)
  Pu zero    = Pu⁰
  Pu (suc j) = Puˢ j

  Puˢ : ∀ {N} j (d : FD (suc N) (suc j)) (b : Tr (fin (suc N))) (nb : fin (suc N) ⊢ zero ◃ b) {t}
      → M (suc N) (ψᴺ (suc N) t) b
      → ∀ {s y} → M (suc j) s y → M (suc N) (ψᴺ (suc N) (t ++ s)) (Up (fin (suc j)) (dn d) b nb y)
  Puˢ {N} j d b nb {t} mb (mz {x = y}) =
    ++[] (λ r → M (suc N) (ψᴺ (suc N) r) (Up (fin (suc j)) (dn d) b nb y)) t
      (GM.m-zl N (Up (fin (suc j)) (dn d) b nb) (Up-mono (fin (suc j)) (dn d) b nb) mb y)
  Puˢ {N} j d b nb {t} mb (m1 {t = s} {x = y} e r) =
    GM.m-next N (Up-nz (fin (suc j)) (dn d) b nb y) (cofψ1 (natT (suc N)) (t ++ s) (cof++1 t s e))
      (λ k → trans (fsnψ1 (natT (suc N)) (t ++ s) k (cof++1 t s e))
               (cong (λ r → replicate k (ψ (natT (suc N)) r)) (pred++ t s e)))
      (Puˢ j d b nb mb r)
  Puˢ {N} j d b nb {t} mb (mL {t = s} {x = y} e h) =
    mL (cofψω (natT (suc N)) (t ++ s) (cof++ω t s e))
      (λ k → subst (λ r → M (suc N) r (Up (fin (suc j)) (dn d) b nb y))
        (sym (trans (fsnψω (natT (suc N)) (t ++ s) k (cof++ω t s e)) (cong (ψᴺ (suc N)) (fsn++ t s k e))))
        (Puˢ j d b nb mb (h k)))
  Puˢ {N} j d b nb {t} mb (mΩ {t = s} {p = p} {g = g} e nu h) =
    mΩ (cofK (natT (suc N)) (t ++ s) (penN N (mv (dn d) p) (mvN d p nu)) (cof++Ω t s e)) (mvN d p nu)
      (λ η c l → subst (λ r → M (suc N) r (Up (fin (suc j)) (dn d) b nb (g (mvBr (dn d) p c))))
        (sym (trans (fsTK (natT (suc N)) (t ++ s) η (penN N (mv (dn d) p) (mvN d p nu)) (cof++Ω t s e))
               (cong (ψᴺ (suc N)) (fsT++ t s η e))))
        (Puˢ j d b nb mb (h η (mvBr (dn d) p c) (mvL d p c l))))
  Puˢ {N} j d b nb {t} mb (mU {t = s₀} {s = s₁} {x = y₀} {y = y₁} m ch) =
    subst (λ r → M (suc N) (ψᴺ (suc N) r)
        (Up (fin j) (dn (fds d)) (Up (fin (suc j)) (dn d) b nb y₀) (Up-nz (fin (suc j)) (dn d) b nb y₀) y₁))
      (++-assoc t s₀ s₁)
      (Pu j (fds d) (Up (fin (suc j)) (dn d) b nb y₀) (Up-nz (fin (suc j)) (dn d) b nb y₀) (Puˢ j d b nb mb m) ch)
  Puˢ j d b nb mb (mw m r) = mw (Puˢ j d b nb mb m) (Up-mono (fin (suc j)) (dn d) b nb r)
```

## 折到自身, 带前缀

`F` 是层号 `fin (suc N)` 的树以 β 为底值折到自身 (自身一行不读底的其它分量). 一切结点都保留 (规则 5Ω); 孩子里的和经上折.
`z` 是回灌链, `gch P₀` 是 γ-链: γ₀ = Ω_{N+1}, γₖ₊₁ = ψ_{N+1}(P₀ + γₖ).

```agda
module Self (N : ℕ) (ε : Ev (fin (suc N))) (ρ : Rt (fin (suc N))) (B : Base (fin (suc N)))
            (β : Tr (fin (suc N))) (nβ : fin (suc N) ⊢ zero ◃ β) where

  F : Tr (fin (suc N)) → Tr (fin (suc N))
  F x = ψs (fin (suc N)) ε ρ B (fin (suc N)) self β nβ x

  nzF : (x : Tr (fin (suc N))) → fin (suc N) ⊢ zero ◃ F x
  nzF x = nzs (fin (suc N)) ε ρ B (fin (suc N)) self β nβ x

  monoF : {x y : Tr (fin (suc N))} → fin (suc N) ⊢ x ◃ y → fin (suc N) ⊢ F x ◃ F y
  monoF = monos (fin (suc N)) ε ρ B (fin (suc N)) self β nβ

  PF : ∀ {P₀} → M (suc N) (ψᴺ (suc N) P₀) β → ∀ {a x} → M (suc N) a x → M (suc N) (ψᴺ (suc N) (P₀ ++ a)) (F x)
  PF {P₀} hP (mz {x = x}) = ++[] (λ r → M (suc N) (ψᴺ (suc N) r) (F x)) P₀ (GM.m-zl N F monoF hP x)
  PF {P₀} hP (m1 {t = a} {x = x} e r) =
    GM.m-next N (nzF x) (cofψ1 (natT (suc N)) (P₀ ++ a) (cof++1 P₀ a e))
      (λ k → trans (fsnψ1 (natT (suc N)) (P₀ ++ a) k (cof++1 P₀ a e))
               (cong (λ r → replicate k (ψ (natT (suc N)) r)) (pred++ P₀ a e)))
      (PF hP r)
  PF {P₀} hP (mL {t = a} {x = x} e h) =
    mL (cofψω (natT (suc N)) (P₀ ++ a) (cof++ω P₀ a e))
      (λ k → subst (λ r → M (suc N) r (F x))
        (sym (trans (fsnψω (natT (suc N)) (P₀ ++ a) k (cof++ω P₀ a e)) (cong (ψᴺ (suc N)) (fsn++ P₀ a k e))))
        (PF hP (h k)))
  PF {P₀} hP (mΩ {t = a} {p = p} {g = g} e nu h) =
    mΩ (cofK (natT (suc N)) (P₀ ++ a) (penN N p nu) (cof++Ω P₀ a e)) nu
      (λ η c l → subst (λ r → M (suc N) r (F (g c)))
        (sym (trans (fsTK (natT (suc N)) (P₀ ++ a) η (penN N p nu) (cof++Ω P₀ a e))
               (cong (ψᴺ (suc N)) (fsT++ P₀ a η e))))
        (PF hP (h η c l)))
  PF {P₀} hP (mU {t = s₀} {s = s₁} {x = x} {y = y} m ch) =
    subst (λ r → M (suc N) (ψᴺ (suc N) r) (Up (fin N) (dn (fds fd0)) (F x) (nzF x) y)) (++-assoc P₀ s₀ s₁)
      (Pu N (fds fd0) (F x) (nzF x) (PF hP m) ch)
  PF hP (mw m d) = mw (PF hP m) (monoF d)

  z : ℕ → Tr (fin (suc N))
  z = iter (λ c → next (F c) (nzF c)) zero

  gch : E.T → ℕ → E.T
  gch P₀ zero    = Ωᴺ (suc N)
  gch P₀ (suc k) = ψᴺ (suc N) (P₀ ++ gch P₀ k)

  sγ : ∀ {P₀} → M (suc N) (Ωᴺ (suc N)) β → M (suc N) (ψᴺ (suc N) P₀) β → ∀ k → M (suc N) (gch P₀ k) (z (suc k))
  sγ hΩ hP zero    = mw hΩ (◃l zero)
  sγ hΩ hP (suc k) = mw (PF hP (sγ hΩ hP k)) (◃l zero)
```
