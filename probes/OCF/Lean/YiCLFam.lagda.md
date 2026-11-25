# 验收 (候选 A, 精简块): 层号读自有限树时的记号关系族, 上折与折到自身的保持

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提, 量化域是规范读回域的有限一段: 层号 `fn n = h₁ (nat n)` (第 0 层的树 `nat n` 读回的层号), 证据取 `o¹` 在该孩子处的分量.
> `M n` 对 n 递归 (`M 0` 是 `M⁰`); `Mβ`: Ω 树对着 Ω_{n+1}; `Pu`: 任意深度的上折保持; `Self.PF`: 候选 A 的折叠折到自身, 带前缀的保持; `Self.sγ`: 回灌链对着 γ-链. 是 `YiANFam` (F2 块, 主线折叠) 在精简块与候选 A 折叠上的对应物.
> 不涉及 ℕ 极限层号, 不涉及折到低层 (见 [YiCLLow](YiCLLow.lagda.md)), 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCLFam where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKVPath
open import OCF.Lean.YiKVFold
open import OCF.Lean.YiKVRel hiding (cof++Ω; fsT++; Pu)
open import OCF.Lean.YiKVCheck using (o¹; h₁)
open import OCF.Lean.YiCertFold using (Base)
import OCF.Align.EboLeanDef as E
open E using (cof; c1; cω; cΩ; pred; fsn; fsT; γT; natT; sucT; cmpᵀ)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ; cofΩ; fsTΩ; Pen; cmp-pen; cofK; fsTK)
```

## 有限层号与关系族

`nat n` 是第 0 层的树 n; `fn n` 是它读回的层号 (`fn (suc n)` 定义性地是后继形状, 孩子 `fn n`). `lev n t` 是 "层号 `fn n` 本身或其中的槽位" t 所在的层号, `slot n p = levP (suc n) p` 是槽位 p 的分支所在的层号; `Lw⁼`, `LwP` 是对应的分支关系.

```agda
nat : ℕ → Tr zero
nat zero    = zero
nat (suc n) = suc (nat n)

fn : ℕ → L
fn n = h₁ (nat n)

okf : (n : ℕ) → Ok (fn n)
okf n = proj₂ o¹ (nat n)

mutual
  lev : (n : ℕ) → Pos⁼ (fn n) → ℕ
  lev n (inj₁ tt) = n
  lev n (inj₂ p)  = levP n p

  levP : (n : ℕ) → Pos (fn n) → ℕ
  levP (suc n) (inj₂ (tt , t)) = lev n t

slot : (n : ℕ) → Pos (fn (suc n)) → ℕ
slot n = levP (suc n)

≤ⁿ-step : ∀ {a b} → a ≤ⁿ b → a ≤ⁿ suc b
≤ⁿ-step z≤n     = z≤n
≤ⁿ-step (s≤s l) = s≤s (≤ⁿ-step l)

≤ⁿ-refl : ∀ a → a ≤ⁿ a
≤ⁿ-refl zero    = z≤n
≤ⁿ-refl (suc a) = s≤s (≤ⁿ-refl a)

≤ⁿ-pred : ∀ {a b} → suc a ≤ⁿ b → a ≤ⁿ b
≤ⁿ-pred (s≤s l) = ≤ⁿ-step l

mutual
  lev≤ : ∀ n t → lev n t ≤ⁿ n
  lev≤ n (inj₁ tt) = ≤ⁿ-refl n
  lev≤ n (inj₂ p)  = ≤ⁿ-pred (levP< n p)

  levP< : ∀ n p → suc (levP n p) ≤ⁿ n
  levP< (suc n) (inj₂ (tt , t)) = s≤s (lev≤ n t)

Nw : (n : ℕ) → Pos (fn (suc n)) → E.T → Set
Nw n p ν = ν ≡ natT (slot n p)

mutual
  M : (n : ℕ) → E.T → Tr (fn n) → Set
  M zero    = M⁰
  M (suc n) = Mᴰ (Sig (fn (suc n))) (LwP (suc n)) (λ _ → M n) (Nw n)

  Lw⁼ : (n : ℕ) (t : Pos⁼ (fn n)) → E.T → Br⁼ (fn n) t → Set
  Lw⁼ n (inj₁ tt) = M n
  Lw⁼ n (inj₂ p)  = LwP n p

  LwP : (n : ℕ) (p : Pos (fn n)) → E.T → Br (fn n) p → Set
  LwP (suc n) (inj₂ (tt , t)) = Lw⁼ n t

Lw : (n : ℕ) (p : Pos (fn (suc n))) → E.T → Br (fn (suc n)) p → Set
Lw n = LwP (suc n)

module GM (n : ℕ) = Gen {Sig (fn (suc n))} {Lw n} {λ _ → M n} {Nw n}

mwN : ∀ n {s x x′} → M n s x → fn n ⊢ x ◃ x′ → M n s x′
mwN zero    = mw
mwN (suc n) = mw

m⊴N : ∀ n {s x x′} → M n s x → x ⊴ x′ → M n s x′
m⊴N n m ⊴r     = m
m⊴N n m (⊴◃ d) = mwN n m d

penN : ∀ n p {ν} → Nw n p ν → Pen (cmpᵀ (sucT ν) (natT (suc n)))
penN n p refl = cmp-pen (levP< (suc n) p)
```

第 1 层: `M 1` 与 `YiKVRel.M¹` 互相给出 (两边的槽位关系按不同的子句写, 不是定义性相等).

```agda
to¹ : ∀ {s y} → M 1 s y → M¹ s y
to¹ mz                                       = mz
to¹ (m1 e r)                                 = m1 e (to¹ r)
to¹ (mL e h)                                 = mL e (λ k → to¹ (h k))
to¹ (mΩ {p = inj₂ (tt , inj₁ tt)} e nu h)    = mΩ e nu (λ η c l → to¹ (h η c l))
to¹ (mΩ {p = inj₂ (tt , inj₂ ())} _ _ _)
to¹ (mU m ch)                                = mU (to¹ m) ch
to¹ (mw m d)                                 = mw (to¹ m) d

of¹ : ∀ {s y} → M¹ s y → M 1 s y
of¹ mz                                       = mz
of¹ (m1 e r)                                 = m1 e (of¹ r)
of¹ (mL e h)                                 = mL e (λ k → of¹ (h k))
of¹ (mΩ {p = inj₂ (tt , inj₁ tt)} e nu h)    = mΩ e nu (λ η c l → of¹ (h η c l))
of¹ (mΩ {p = inj₁ ()} _ _ _)
of¹ (mΩ {p = inj₂ (tt , inj₂ ())} _ _ _)
of¹ (mU m ch)                                = mU (of¹ m) ch
of¹ (mw m d)                                 = mw (of¹ m) d
```

## Ω 树

```agda
Mβ : ∀ n → M (suc n) (Ωᴺ (suc n)) (proj₁ (Ωt (fn (suc n))))
Mβ n = mΩ (cofΩ n) refl
  (λ η c l → subst (λ s → M (suc n) s (up zero tt (suc c) (z◃ c ◃s))) (sym (fsTΩ n η)) (mU mz (mwN n l ◃s)))
```

## 上折的保持, 任意深度

`FD N j`: 从层号 N 向下走到 j 的一串后继孩子; `dn` 读成块上的 `Dn`. 槽位沿它搬上去, 所在层号不变 (`mvS`), 分支的关系对应 (`mvL`).

```agda
data FD (N : ℕ) : ℕ → Set where
  fd0 : FD N N
  fds : ∀ {j} → FD N (suc j) → FD N j

dn : ∀ {N j} → FD N j → Dn (fn N) (fn j)
dn fd0     = stop
dn (fds d) = down (dn d) tt

mvS : ∀ {N j} (d : FD (suc N) (suc j)) (p : Pos (fn (suc j))) → slot N (mv (dn d) p) ≡ slot j p
mvS fd0     p = refl
mvS (fds d) p = mvS d (inj₂ (tt , inj₂ p))

mvN : ∀ {N j} (d : FD (suc N) (suc j)) (p : Pos (fn (suc j))) {ν} → Nw j p ν → Nw N (mv (dn d) p) ν
mvN d p nu = trans nu (cong natT (sym (mvS d p)))

mvL : ∀ {N j} (d : FD (suc N) (suc j)) (p : Pos (fn (suc j))) {η} (c : Br (fn (suc N)) (mv (dn d) p))
    → Lw N (mv (dn d) p) η c → Lw j p η (mvBr (dn d) p c)
mvL fd0     p c l = l
mvL (fds d) p c l = mvL d (inj₂ (tt , inj₂ p)) c l

Pu⁰ : ∀ {N} (d : FD (suc N) zero) (b : Tr⁺ (fn (suc N))) {t}
    → M (suc N) (ψᴺ (suc N) t) (proj₁ b)
    → ∀ {s y} → M⁰ s y → M (suc N) (ψᴺ (suc N) (t ++ s)) (proj₁ (Up zero (dn d) b y))
Pu⁰ {N} d b {t} mb (mz {x = y}) =
  ++[] (λ r → M (suc N) (ψᴺ (suc N) r) (proj₁ (Up zero (dn d) b y))) t
    (GM.m-zl N (λ y → proj₁ (Up zero (dn d) b y)) (Upm zero (dn d) b) mb y)
Pu⁰ {N} d b {t} mb (m1 {t = s} {x = y} e r) =
  GM.m-next N (Up zero (dn d) b y) (cofψ1 (natT (suc N)) (t ++ s) (cof++1 t s e))
    (λ k → trans (fsnψ1 (natT (suc N)) (t ++ s) k (cof++1 t s e))
             (cong (λ r → replicate k (E.ψ (natT (suc N)) r)) (pred++ t s e)))
    (Pu⁰ d b mb r)
Pu⁰ {N} d b {t} mb (mL {t = s} {x = y} e h) =
  mL (cofψω (natT (suc N)) (t ++ s) (cof++ω t s e))
    (λ k → subst (λ r → M (suc N) r (proj₁ (Up zero (dn d) b y)))
      (sym (trans (fsnψω (natT (suc N)) (t ++ s) k (cof++ω t s e)) (cong (ψᴺ (suc N)) (fsn++ t s k e))))
      (Pu⁰ d b mb (h k)))
Pu⁰ d b mb (mΩ {p = ()} _ _ _)
Pu⁰ d b mb (mU {c = ()} _ _)
Pu⁰ d b mb (mw m r) = mw (Pu⁰ d b mb m) (Upm zero (dn d) b r)

mutual
  Pu : ∀ {N} j (d : FD (suc N) j) (b : Tr⁺ (fn (suc N))) {t}
     → M (suc N) (ψᴺ (suc N) t) (proj₁ b)
     → ∀ {s y} → M j s y → M (suc N) (ψᴺ (suc N) (t ++ s)) (proj₁ (Up (fn j) (dn d) b y))
  Pu zero    = Pu⁰
  Pu (suc j) = Puˢ j

  Puˢ : ∀ {N} j (d : FD (suc N) (suc j)) (b : Tr⁺ (fn (suc N))) {t}
      → M (suc N) (ψᴺ (suc N) t) (proj₁ b)
      → ∀ {s y} → M (suc j) s y → M (suc N) (ψᴺ (suc N) (t ++ s)) (proj₁ (Up (fn (suc j)) (dn d) b y))
  Puˢ {N} j d b {t} mb (mz {x = y}) =
    ++[] (λ r → M (suc N) (ψᴺ (suc N) r) (proj₁ (Up (fn (suc j)) (dn d) b y))) t
      (GM.m-zl N (λ y → proj₁ (Up (fn (suc j)) (dn d) b y)) (Upm (fn (suc j)) (dn d) b) mb y)
  Puˢ {N} j d b {t} mb (m1 {t = s} {x = y} e r) =
    GM.m-next N (Up (fn (suc j)) (dn d) b y) (cofψ1 (natT (suc N)) (t ++ s) (cof++1 t s e))
      (λ k → trans (fsnψ1 (natT (suc N)) (t ++ s) k (cof++1 t s e))
               (cong (λ r → replicate k (E.ψ (natT (suc N)) r)) (pred++ t s e)))
      (Puˢ j d b mb r)
  Puˢ {N} j d b {t} mb (mL {t = s} {x = y} e h) =
    mL (cofψω (natT (suc N)) (t ++ s) (cof++ω t s e))
      (λ k → subst (λ r → M (suc N) r (proj₁ (Up (fn (suc j)) (dn d) b y)))
        (sym (trans (fsnψω (natT (suc N)) (t ++ s) k (cof++ω t s e)) (cong (ψᴺ (suc N)) (fsn++ t s k e))))
        (Puˢ j d b mb (h k)))
  Puˢ {N} j d b {t} mb (mΩ {t = s} {p = p} {g = g} e nu h) =
    mΩ (cofK (natT (suc N)) (t ++ s) (penN N (mv (dn d) p) (mvN d p nu)) (cof++Ω t s e)) (mvN d p nu)
      (λ η c l → subst (λ r → M (suc N) r (proj₁ (Up (fn (suc j)) (dn d) b (g (mvBr (dn d) p c)))))
        (sym (trans (fsTK (natT (suc N)) (t ++ s) η (penN N (mv (dn d) p) (mvN d p nu)) (cof++Ω t s e))
               (cong (ψᴺ (suc N)) (fsT++ t s η e))))
        (Puˢ j d b mb (h η (mvBr (dn d) p c) (mvL d p c l))))
  Puˢ {N} j d b {t} mb (mU {t = s₀} {s = s₁} {x = y₀} {y = y₁} m ch) =
    subst (λ r → M (suc N) (ψᴺ (suc N) r)
        (proj₁ (Up (fn j) (dn (fds d)) (Up (fn (suc j)) (dn d) b y₀) y₁)))
      (++-assoc t s₀ s₁)
      (Pu j (fds d) (Up (fn (suc j)) (dn d) b y₀) (Puˢ j d b mb m) ch)
  Puˢ j d b mb (mw m r) = mw (Puˢ j d b mb m) (Upm (fn (suc j)) (dn d) b r)
```

## 折到自身, 带前缀

`F⁺` 是层号 `fn (suc N)` 的树以 β 为起点折到自身 (候选 A 的 `ψ`, 路径 `self`; 这一行不读底). 一切结点都保留 (规则 5Ω); 孩子里的和经上折.
`z` 是回灌链, `gch P₀` 是 γ-链: γ₀ = Ω_{N+1}, γₖ₊₁ = ψ_{N+1}(P₀ + γₖ).

```agda
module Self (N : ℕ) (B : Base (fn (suc N))) (β : Tr⁺ (fn (suc N))) where

  F⁺ : Tr (fn (suc N)) → Tr⁺ (fn (suc N))
  F⁺ x = ψ (fn (suc N)) (okf (suc N)) B (fn (suc N)) self β x

  F : Tr (fn (suc N)) → Tr (fn (suc N))
  F x = proj₁ (F⁺ x)

  monoF : {x y : Tr (fn (suc N))} → fn (suc N) ⊢ x ◃ y → fn (suc N) ⊢ F x ◃ F y
  monoF = mono (fn (suc N)) (okf (suc N)) B (fn (suc N)) self β

  PF : ∀ {P₀} → M (suc N) (ψᴺ (suc N) P₀) (proj₁ β) → ∀ {a x} → M (suc N) a x → M (suc N) (ψᴺ (suc N) (P₀ ++ a)) (F x)
  PF {P₀} hP (mz {x = x}) = ++[] (λ r → M (suc N) (ψᴺ (suc N) r) (F x)) P₀ (GM.m-zl N F monoF hP x)
  PF {P₀} hP (m1 {t = a} {x = x} e r) =
    GM.m-next N (F⁺ x) (cofψ1 (natT (suc N)) (P₀ ++ a) (cof++1 P₀ a e))
      (λ k → trans (fsnψ1 (natT (suc N)) (P₀ ++ a) k (cof++1 P₀ a e))
               (cong (λ r → replicate k (E.ψ (natT (suc N)) r)) (pred++ P₀ a e)))
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
    subst (λ r → M (suc N) (ψᴺ (suc N) r) (proj₁ (Up (fn N) (dn (fds fd0)) (F⁺ x) y))) (++-assoc P₀ s₀ s₁)
      (Pu N (fds fd0) (F⁺ x) (PF hP m) ch)
  PF hP (mw m d) = mw (PF hP m) (monoF d)

  z : ℕ → Tr (fn (suc N))
  z = iter (λ c → proj₁ (next⁺ (F⁺ c))) zero

  gch : E.T → ℕ → E.T
  gch P₀ zero    = Ωᴺ (suc N)
  gch P₀ (suc k) = ψᴺ (suc N) (P₀ ++ gch P₀ k)

  sγ : ∀ {P₀} → M (suc N) (Ωᴺ (suc N)) (proj₁ β) → M (suc N) (ψᴺ (suc N) P₀) (proj₁ β) → ∀ k → M (suc N) (gch P₀ k) (z (suc k))
  sγ hΩ hP zero    = mw hΩ (◃l zero)
  sγ hΩ hP (suc k) = mw (PF hP (sγ hΩ hP k)) (◃l zero)
```
