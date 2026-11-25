# 验收一侧: 遗传封闭的关系族 (有限读回层号), Ω 树与上折的保持

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提, 量化域同 `YiCLFam` (层号 `fn n`). `M n` 是 [YiHCRel](YiHCRel.lagda.md) 的 `Mᴴ` 对 n 递归的族: 第 n+1 层的分支关系与孩子关系是低层的 `M`, 它们带 `mc`, 所以是封闭后的关系.
> `Mβ` (Ω 树对着 Ω_{n+1}), `Pu` (上折的保持), 以及对层号一般的几条 (`zlJ`, `nextJ`, `cumJ`, `mLJ`, `mcJ`, `mΩP`, `ΩJ`, `toLw`).
> 来源: 定义与证明照 `YiCLFam` (`M`, `Lw⁼`, `LwP`, `Mβ`, `mvL`, `Pu⁰`, `Pu`, `Puˢ`) 与 `YiCLLow` (`toLw`, `zlJ` 一组) 逐行搬到 `Mᴴ` 上, 每个对推导的归纳加 `mc` 一行 (用 `YiDCRel.app≤`); 与关系无关的 (`fn`, `lev`, `Nw`, `FD`, `Sb` 等) 直接引用原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiHCFam where

open import Data.Nat using (ℕ; zero; suc)
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
open import OCF.Lean.YiKVRel using (_⊴_; ⊴r; ⊴◃; ++[])
open import OCF.Lean.YiHCRel
import OCF.Align.EboLeanDef as E
open E using (cof; c1; cω; cΩ; pred; fsn; fsT; natT)
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ; cofΩ; fsTΩ; cofK; fsTK)
open import OCF.Lean.YiDCRel using (app≤)
open import OCF.Lean.YiCLFam using (nat; fn; lev; levP; slot; Nw; penN; FD; fd0; fds; dn; mvN)
open import OCF.Lean.YiCLLow using (Sb; s0; ss; pos⁼; toBr)
```

## 关系族

```agda
mutual
  M : (n : ℕ) → E.T → Tr (fn n) → Set
  M zero    = M⁰
  M (suc n) = Mᴴ (Sig (fn (suc n))) (LwP (suc n)) (λ _ → M n) (Nw n)

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

mcJ : ∀ n {s t x} → s ≤ᵀ t → M n t x → M n s x
mcJ zero    = mc
mcJ (suc n) = mc

toLw : ∀ {n i} (s : Sb n i) {η y} → M i η y → Lw⁼ n (pos⁼ s) η (toBr s y)
toLw s0     m = m
toLw (ss s) m = toLw s m
```

## Ω 树, 对层号一般的几条

```agda
Mβ : ∀ n → M (suc n) (Ωᴺ (suc n)) (proj₁ (Ωt (fn (suc n))))
Mβ n = mΩ (cofΩ n) refl
  (λ η c l → subst (λ s → M (suc n) s (up zero tt (suc c) (z◃ c ◃s))) (sym (fsTΩ n η)) (mU mz (mwN n l ◃s)))

zlJ : ∀ j {S′ : Sg} (Φ : T S′ → Tr (fn j)) → (∀ {x y} → Lt S′ x y → fn j ⊢ Φ x ◃ Φ y)
    → ∀ {t} → M j t (Φ zero) → (y : T S′) → M j t (Φ y)
zlJ zero    Φ mo m y = G⁰.m-zl Φ mo m y
zlJ (suc j) Φ mo m y = GM.m-zl j Φ mo m y

nextJ : ∀ j {t p} (b : Tr⁺ (fn j)) → cof t ≡ cω → (∀ n → fsn t n ≡ replicate n p)
      → M j (p ∷ []) (proj₁ b) → M j t (proj₁ (next⁺ b))
nextJ zero    b e q m = G⁰.m-next b e q m
nextJ (suc j) b e q m = GM.m-next j b e q m

cumJ : ∀ j {t} (F : ℕ → Tr⁺ (fn j)) (n : ℕ) → M j t (proj₁ (F n)) → M j t (proj₁ (limc⁺ F))
cumJ zero    F n m = G⁰.m-cum F n m
cumJ (suc j) F n m = GM.m-cum j F n m

mLJ : ∀ j {t x} → cof t ≡ cω → (∀ n → M j (fsn t n) x) → M j t x
mLJ zero    = mL
mLJ (suc j) = mL

mΩP : ∀ j {t ν} {q : Pos (fn j)} {g} → cof t ≡ cΩ ν → ν ≡ natT (levP j q)
    → (∀ η c → LwP j q η c → M j (fsT t η) (g c)) → M j t (Ω q g)
mΩP (suc j) = mΩ

ΩJ : ∀ i (y : Tr⁺ (fn i)) → proj₁ (Ωt (fn i)) ⊴ proj₁ y → M i (Ωᴺ i) (proj₁ y)
ΩJ zero    y le = pos⁰ (proj₁ y) (proj₂ y)
ΩJ (suc i) y le = m⊴N (suc i) (Mβ i) le
```

## 上折的保持, 任意深度

```agda
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
Pu⁰ {N} d b {t} mb (mc le m) = mc (app≤ (suc N) t le) (Pu⁰ d b mb m)

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
  Puˢ {N} j d b {t} mb (mc le m) = mc (app≤ (suc N) t le) (Puˢ j d b mb m)
```
