# 不同层号的分支类型之间的满射: 一个合法同值对

> 判决: 条件定理 (条件: 带计算律的函数外延 `FunextE`). 合法同值对 `sc (sc zero)`, `sc w₁` (没有同层号槽位, `YiQNReg.¬PE₂`) 有 `PS`, 所以前者的每棵树被后者的某棵树按值支配 (`tp₂`).
> 满射是按构造子的收拢 ρ (w₁ 的孩子 n 都收到 tt), 截面 σ; `ρ ∘ σ` 是恒等要外延 (Ω 的分支函数, ℕ 极限的序列) 与相邻证明的搬运相容 (`coh`).
> 只做这一对; 一般层号对的满射未做. 接口在 `YiQNReg`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiQNCollapse where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym; cong; cong₂)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
import OCF.Lean.YiVWVal as W
open W using (val; _≼_)
open import OCF.Lean.YiRVLevel using (sc)
open import OCF.Lean.YiQNReg using (Surj; PS; eqSurj; TpS; w₁)
```

`FunextE`: `happly` 有截面. 可满足: 立方类型论里 `funExt` 满足 `happly (funExt h) ≡ h` (逐点 `refl`); 只作模块参数.

```agda
FunextE : Set₁
FunextE = ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} (h : (x : A) → f x ≡ g x)
        → Σ (f ≡ g) λ E → (x : A) → cong (λ k → k x) E ≡ h x

one : L
one = sc zero

S₁ : Sg
S₁ = Sig one

q₁ : Pos one
q₁ = inj₂ (tt , inj₁ tt)
```

## 截面与收拢

```agda
mutual
  σ : Tr one → Tr w₁
  σ zero                        = zero
  σ (suc x)                     = suc (σ x)
  σ (lim f a)                   = lim (λ n → σ (f n)) (λ n → σm (a n))
  σ (Ω (inj₂ (tt , inj₁ tt)) g) = Ω (inj₂ (zero , inj₁ tt)) (λ z → σ (g z))
  σ (up x tt y e)               = up (σ x) zero y e

  σm : {x y : Tr one} → one ⊢ x ◃ y → w₁ ⊢ σ x ◃ σ y
  σm ◃s                                = ◃s
  σm (◃l n)                            = ◃l n
  σm (◃w {p = inj₂ (tt , inj₁ tt)})    = ◃w
  σm (◃u x tt y e)                     = ◃u (σ x) zero y e
  σm (◃c x tt d)                       = ◃c (σ x) zero d
  σm (◃t d e)                          = ◃t (σm d) (σm e)

mutual
  ρ : Tr w₁ → Tr one
  ρ zero                       = zero
  ρ (suc x)                    = suc (ρ x)
  ρ (lim f a)                  = lim (λ n → ρ (f n)) (λ n → ρm (a n))
  ρ (Ω (inj₂ (n , inj₁ tt)) g) = Ω q₁ (λ z → ρ (g z))
  ρ (up x n y e)               = up (ρ x) tt y e

  ρm : {x y : Tr w₁} → w₁ ⊢ x ◃ y → one ⊢ ρ x ◃ ρ y
  ρm ◃s                             = ◃s
  ρm (◃l n)                         = ◃l n
  ρm (◃w {p = inj₂ (n , inj₁ tt)})  = ◃w
  ρm (◃u x n y e)                   = ◃u (ρ x) tt y e
  ρm (◃c x n d)                     = ◃c (ρ x) tt d
  ρm (◃t d e)                       = ◃t (ρm d) (ρm e)
```

## 相邻证明的搬运 (无前提的 J 引理)

```agda
LT : Tr one → Tr one → Set
LT = Lt S₁

Ls : ∀ {u x : Tr one} (e : u ≡ x) → subst₂ LT e (cong suc e) ◃s ≡ ◃s
Ls refl = refl

Lu : ∀ {u x : Tr one} (y : Tr zero) (r : zero ⊢ zero ◃ y) (e : u ≡ x)
   → subst₂ LT e (cong (λ X → up X tt y r) e) (◃u u tt y r) ≡ ◃u x tt y r
Lu y r refl = refl

Lc : ∀ {u x : Tr one} {y′ y : Tr zero} {r′ : zero ⊢ zero ◃ y′} {r : zero ⊢ zero ◃ y} (d : zero ⊢ y′ ◃ y) (e : u ≡ x)
   → subst₂ LT (cong (λ X → up X tt y′ r′) e) (cong (λ X → up X tt y r) e) (◃c u tt d) ≡ ◃c x tt d
Lc d refl = refl

Lt3 : ∀ {x′ y′ z′ x y z : Tr one} (ex : x′ ≡ x) (ey : y′ ≡ y) (ez : z′ ≡ z) (d : LT x′ y′) (e : LT y′ z′)
    → subst₂ LT ex ez (◃t d e) ≡ ◃t (subst₂ LT ex ey d) (subst₂ LT ey ez e)
Lt3 refl refl refl d e = refl
```

## 带函数外延: ℕ 极限与 Ω 结点的相等, 连同 `◃l`, `◃w` 的搬运

```agda
module _ (fe : FunextE) where

  lim′ : {F G : ℕ → Tr one} {A : (n : ℕ) → LT (F n) (F (suc n))} {B : (n : ℕ) → LT (G n) (G (suc n))}
       → (E : F ≡ G) → ((n : ℕ) → subst₂ LT (cong (λ k → k n) E) (cong (λ k → k (suc n)) E) (A n) ≡ B n)
       → Σ (lim F A ≡ lim G B) λ Q → (n : ℕ) → subst₂ LT (cong (λ k → k n) E) Q (◃l n) ≡ ◃l n
  lim′ {F} {A = A} {B} refl k = inner (proj₁ (fe k))
    where
    inner : {B′ : (n : ℕ) → LT (F n) (F (suc n))} (E′ : A ≡ B′)
          → Σ (lim F A ≡ lim F B′) λ Q → (n : ℕ) → subst₂ LT refl Q (◃l n) ≡ ◃l n
    inner refl = refl , λ n → refl

  limEq : {F G : ℕ → Tr one} {A : (n : ℕ) → LT (F n) (F (suc n))} {B : (n : ℕ) → LT (G n) (G (suc n))}
        → (h : (n : ℕ) → F n ≡ G n) → ((n : ℕ) → subst₂ LT (h n) (h (suc n)) (A n) ≡ B n)
        → Σ (lim F A ≡ lim G B) λ Q → (n : ℕ) → subst₂ LT (h n) Q (◃l n) ≡ ◃l n
  limEq {A = A} {B} h k =
    let E  = proj₁ (fe h)
        c  = proj₂ (fe h)
        r  = lim′ E (λ n → subst₂ (λ u v → subst₂ LT u v (A n) ≡ B n) (sym (c n)) (sym (c (suc n))) (k n))
    in proj₁ r , λ n → subst (λ u → subst₂ LT u (proj₁ r) (◃l n) ≡ ◃l n) (c n) (proj₂ r n)

  Ωeq : {G H : Tr zero → Tr one} (h : (z : Tr zero) → G z ≡ H z)
      → Σ (Ω q₁ G ≡ Ω q₁ H) λ Q → subst₂ LT (h zero) Q (◃w {p = q₁}) ≡ ◃w
  Ωeq {G} h =
    let E = proj₁ (fe h)
        c = proj₂ (fe h)
    in cong (Ω q₁) E , subst (λ u → subst₂ LT u (cong (Ω q₁) E) ◃w ≡ ◃w) (c zero) (w′ E)
    where
    w′ : {H′ : Tr zero → Tr one} (E : G ≡ H′) → subst₂ LT (cong (λ k → k zero) E) (cong (Ω q₁) E) (◃w {p = q₁}) ≡ ◃w
    w′ refl = refl
```

## `ρ ∘ σ` 是恒等

```agda
  mutual
    RId : (z : Tr one) → ρ (σ z) ≡ z
    RId zero                        = refl
    RId (suc x)                     = cong suc (RId x)
    RId (lim f a)                   = proj₁ (limEq (λ n → RId (f n)) (λ n → coh (a n)))
    RId (Ω (inj₂ (tt , inj₁ tt)) g) = proj₁ (Ωeq (λ z → RId (g z)))
    RId (up x tt y e)               = cong (λ X → up X tt y e) (RId x)

    coh : {x y : Tr one} (d : one ⊢ x ◃ y) → subst₂ LT (RId x) (RId y) (ρm (σm d)) ≡ d
    coh {x} ◃s                                  = Ls (RId x)
    coh (◃l {f} {a} n)                          = proj₂ (limEq (λ m → RId (f m)) (λ m → coh (a m))) n
    coh (◃w {p = inj₂ (tt , inj₁ tt)} {g})      = proj₂ (Ωeq (λ z → RId (g z)))
    coh (◃u x tt y e)                           = Lu y e (RId x)
    coh (◃c x tt d)                             = Lc d (RId x)
    coh (◃t {x} {y} {z} d e)                    =
      Lt3 (RId x) (RId y) (RId z) (ρm (σm d)) (ρm (σm e)) ⟨trans⟩ cong₂ ◃t (coh d) (coh e)
      where
      open import Relation.Binary.PropositionalEquality using () renaming (trans to _⟨trans⟩_)

  surj₁ : Surj (Tr w₁) (Tr one)
  surj₁ = ρ , λ z → σ z , RId z

  ps₂ : PS (sc one) (sc w₁)
  ps₂ (inj₁ ())
  ps₂ (inj₂ (tt , inj₁ tt))                       = inj₂ (tt , inj₁ tt) , surj₁
  ps₂ (inj₂ (tt , inj₂ (inj₁ ())))
  ps₂ (inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt))))    = inj₂ (tt , inj₂ (inj₂ (zero , inj₁ tt))) , eqSurj refl
  ps₂ (inj₂ (tt , inj₂ (inj₂ (tt , inj₂ ()))))

  tp₂ : (x : Tr (sc one)) → Σ (Tr (sc w₁)) λ x′ → val (sc one) x ≼ val (sc w₁) x′
  tp₂ = TpS ps₂
```
