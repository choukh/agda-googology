# 验收: 层号 3 的带前缀锚点 (第 2 层的树折到低层, 带左加上下文)

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提, 对一切层号 3 的底与一切前缀 t (底的条件见 `Ctx3` 的模块参数).
> `Ctx3.anchor³ : M⁰ (ψ₀ᵗ (t ++ ψ₁ᵗ Ω₃ᵗ)) (ψ⊥ three tt tt B₃ (Ωt three))`: 底的第 0 层分量与 `b⊥` 不低于 ψ₀(t) 时, ψ₀(t+ψ₁(Ω₃)) 对着层号 3 的 Ω 树以该底的折叠.
> 做法: 对 `M² a x` 归纳, 陈述带左加上下文 C 与记号前缀 A₀ (`TC`): ψ₁(A₀+ψ₂(a)) 对着 `⟦C⟧ (F² x)` 折到第 1 层的树, ψ₀(t+ψ₁(A₀+ψ₂(a))) 对着它折到第 0 层的树与底折叠. 不涉及上界. 实例在 [YiPHEnd](YiPHEnd.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPHCtx where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSFold using (ψ⊥-⊵; ψs-⊵)
import OCF.Align.EboLeanDef as E
open E using (cof; c1; cω; cΩ; pred; fsn; fsT; γT; ψ; 𝟏; natT)
open import OCF.Lean.YiMEBase
open import OCF.Lean.YiMENote
open import OCF.Lean.YiMEAnchor using (one; two; M¹; u₀; u₁; ψ₀ᵗ; ψ₁ᵗ; Ω₁ᵗ; Ω₂ᵗ; ++[]; Pu; module G⁰; module G¹)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++; module Pre)
open import OCF.Lean.YiEVReach using (cv⊴)
open import OCF.Lean.YiPHBase
```

## 左加上下文

`⟦ C ⟧ y` 是 X₁ + (X₂ + (… + y)). 加法对右参数递归, 所以上下文向里扩展是定义性的 (`⟦ C ▸ X ⟧ y = ⟦ C ⟧ (X + y)`), 不需要结合律 (结合律在极限与结点处要函数外延). 上下文穿过结点与嵌入的等式对 C 归纳, 每一步是归纳假设的一个实例.

```agda
infixl 5 _▸_
data Ctx : Set where
  ε   : Ctx
  _▸_ : Ctx → Tr two → Ctx

⟦_⟧ : Ctx → Tr two → Tr two
⟦ ε ⟧     y = y
⟦ C ▸ X ⟧ y = ⟦ C ⟧ (X + y)

cm : ∀ C {x y : Tr two} → two ⊢ x ◃ y → two ⊢ ⟦ C ⟧ x ◃ ⟦ C ⟧ y
cm ε       d = d
cm (C ▸ X) d = cm C (+-mono X d)

c⊴ : ∀ C {x y : Tr two} → x ⊴ y → ⟦ C ⟧ x ⊴ ⟦ C ⟧ y
c⊴ C ⊴r     = ⊴r
c⊴ C (⊴◃ d) = ⊴◃ (cm C d)

eΩ : ∀ C (p : Pos two) (g : Br two p → Tr two) → ⟦ C ⟧ (Ω p g) ≡ Ω p (λ c → ⟦ C ⟧ (g c))
eΩ ε       p g = refl
eΩ (C ▸ X) p g = eΩ C p (λ c → X + g c)

eΩt : ∀ C (x₀ : Tr two) → ⟦ C ⟧ (Ω (inj₁ tt) (λ c → up x₀ tt (suc c) (z◃s c)))
                         ≡ Ω (inj₁ tt) (λ c → up (⟦ C ⟧ x₀) tt (suc c) (z◃s c))
eΩt ε       x₀ = refl
eΩt (C ▸ X) x₀ = eΩt C (X + x₀)

up⊵ : ∀ {ℓ} (j : L) (d : Dn ℓ j) (b : Tr ℓ) (nb : ℓ ⊢ zero ◃ b) (y : Tr j) → b ⊴ Up j d b nb y
up⊵ j d b nb y with zl y
... | inj₁ refl = ⊴r
... | inj₂ r    = ⊴◃ (Up-mono j d b nb r)
```

## 第 1 层: 折到自身带前缀, 底抬到层号 2

`L1 D`: 第 1 层的底 D 任意. `PFp` 是 `YiMEAnchor.At.PF` 加记号前缀 A. `lift` 把 D 抬成层号 2 的底, 它的孩子底 `dS one tt tt lift zero` 与 D 定义性相等 (记录的 η), 所以 `YiMWPre.Pre` 可以代入.

```agda
module L1 (D : Base one) where

  F¹ : Tr one → Tr one
  F¹ y = ψs one tt tt D one self (bs D one self) (ns D one self) y

  nzF¹ : (y : Tr one) → one ⊢ zero ◃ F¹ y
  nzF¹ y = nzs one tt tt D one self (bs D one self) (ns D one self) y

  monoF¹ : {x y : Tr one} → one ⊢ x ◃ y → one ⊢ F¹ x ◃ F¹ y
  monoF¹ = monos one tt tt D one self (bs D one self) (ns D one self)

  PFp : ∀ {A} → M¹ (ψ₁ᵗ A) (bs D one self) → ∀ {s y} → M¹ s y → M¹ (ψ₁ᵗ (A ++ s)) (F¹ y)
  PFp {A} hA (mz {x = y}) = ++[] (λ r → M¹ (ψ₁ᵗ r) (F¹ y)) A (G¹.m-zl F¹ monoF¹ hA y)
  PFp {A} hA (m1 {t = s} {x = y} e r) =
    G¹.m-next (nzF¹ y) (cofψ1 u₁ (A ++ s) (cof++1 A s e))
      (λ n → trans (fsnψ1 u₁ (A ++ s) n (cof++1 A s e)) (cong (λ r → replicate n (ψ u₁ r)) (pred++ A s e)))
      (PFp hA r)
  PFp {A} hA (mL {t = s} {x = y} e h) =
    mL (cofψω u₁ (A ++ s) (cof++ω A s e))
      (λ n → subst (λ r → M¹ r (F¹ y))
        (sym (trans (fsnψω u₁ (A ++ s) n (cof++ω A s e)) (cong ψ₁ᵗ (fsn++ A s n e))))
        (PFp hA (h n)))
  PFp {A} hA (mΩ {t = s} {p = inj₁ tt} {g = g} e refl h) =
    mΩ (cofψΩ u₁ (A ++ s) (cof++Ω A s e)) refl
      (λ η c l → subst (λ r → M¹ r (F¹ (g c)))
        (sym (trans (fsTψΩ u₁ (A ++ s) η (cof++Ω A s e)) (cong ψ₁ᵗ (fsT++ A s η e))))
        (PFp hA (h η c l)))
  PFp hA (mΩ {p = inj₂ ()} _ _ _)
  PFp {A} hA (mU {t = s₀} {s = s₁} {x = y₀} {y = y₁} m ch) =
    subst (λ r → M¹ (ψ₁ᵗ r) (Up zero (down stop tt) (F¹ y₀) (nzF¹ y₀) y₁)) (++-assoc A s₀ s₁)
      (Pu (F¹ y₀) (nzF¹ y₀) (PFp hA m) ch)
  PFp hA (mw m d) = mw (PFp hA m) (monoF¹ d)

  lbs : (j : L) → j ≤ two → Tr j
  lbs _ self    = Ωt two
  lbs j (ins w) = bs D j w

  lns : (j : L) (w : j ≤ two) → j ⊢ zero ◃ lbs j w
  lns _ self    = Ωt-nz two
  lns j (ins w) = ns D j w

  lift : Base two
  lift = base (b⊥ D) (n⊥ D) lbs lns
```

## 取定层号 3 的底与前缀

```agda
module Ctx3 (B₃ : Base three)
  (hβ₂ : M² Ω₂ᵗ (bs B₃ two (ins self)))
  (hΩ₂ : Ωt two ⊴ bs B₃ two (ins self))
  (hβ₁ : M¹ Ω₁ᵗ (bs B₃ one (ins (ins self))))
  (t : E.T)
  (hp0 : M⁰ (ψ₀ᵗ t) (bs B₃ zero (ins (ins (ins self)))))
  (hp⊥ : M⁰ (ψ₀ᵗ t) (b⊥ B₃)) where

  open P2 B₃ hβ₂ public

  β₁ : Tr one
  β₁ = bs B₃ one (ins (ins self))

  nβ₁ : one ⊢ zero ◃ β₁
  nβ₁ = ns B₃ one (ins (ins self))

  β₀ : Tr zero
  β₀ = bs B₃ zero (ins (ins (ins self)))

  nβ₀ : zero ⊢ zero ◃ β₀
  nβ₀ = ns B₃ zero (ins (ins (ins self)))

  F₁ : Tr two → Tr one
  F₁ x = ψs two tt tt Bᵃ one (ins self) β₁ nβ₁ x

  nzF₁ : (x : Tr two) → one ⊢ zero ◃ F₁ x
  nzF₁ x = nzs two tt tt Bᵃ one (ins self) β₁ nβ₁ x

  H : Tr two → Tr zero
  H x = ψs two tt tt Bᵃ zero (ins (ins self)) β₀ nβ₀ x

  nzH : (x : Tr two) → zero ⊢ zero ◃ H x
  nzH x = nzs two tt tt Bᵃ zero (ins (ins self)) β₀ nβ₀ x

  W : Tr two → Tr zero
  W x = ψ⊥ two tt tt Bᵃ x

  nzW : (x : Tr two) → zero ⊢ zero ◃ W x
  nzW x = nz⊥ two tt tt Bᵃ x

  F²⊵ : (x : Tr two) → Ωt two ⊴ F² x
  F²⊵ x = ⊴-trans hΩ₂ (cv⊴ (ψs-⊵ two tt tt Bᵃ two self β₂ nβ₂ x))

  m1F : (X : Tr two) → M¹ Ω₁ᵗ (F₁ X)
  m1F X = G¹.m⊴ hβ₁ (cv⊴ (ψs-⊵ two tt tt Bᵃ one (ins self) β₁ nβ₁ X))

  m0H : (X : Tr two) → M⁰ (ψ₀ᵗ t) (H X)
  m0H X = G⁰.m⊴ hp0 (cv⊴ (ψs-⊵ two tt tt Bᵃ zero (ins (ins self)) β₀ nβ₀ X))

  m0W : (X : Tr two) → M⁰ (ψ₀ᵗ t) (W X)
  m0W X = G⁰.m⊴ hp⊥ (cv⊴ (ψ⊥-⊵ two tt tt Bᵃ X))
```

## 三条结论一起带

`Cl q V`: 第 1 层的项 q 对着 V 折到第 1 层的树, ψ₀(t+q) 对着 V 折到第 0 层的树与底折叠. 对 V 向上封闭; q 的共尾为 ω 时可逐项给 (`Cl-lim`).

```agda
  record Cl (q : E.T) (V : Tr two) : Set where
    constructor cl
    field
      cF : M¹ q (F₁ V)
      cH : M⁰ (ψ₀ᵗ (t ++ q)) (H V)
      cW : M⁰ (ψ₀ᵗ (t ++ q)) (W V)
  open Cl

  Cl-up◃ : ∀ {q V V′} → Cl q V → two ⊢ V ◃ V′ → Cl q V′
  Cl-up◃ (cl a b c) d =
    cl (mw a (monos two tt tt Bᵃ one (ins self) β₁ nβ₁ d))
       (mw b (monos two tt tt Bᵃ zero (ins (ins self)) β₀ nβ₀ d))
       (mw c (mono⊥ two tt tt Bᵃ d))

  Cl-up⊴ : ∀ {q V V′} → Cl q V → V ⊴ V′ → Cl q V′
  Cl-up⊴ x ⊴r     = x
  Cl-up⊴ x (⊴◃ d) = Cl-up◃ x d

  Cl-lim : ∀ {q V} → cof q ≡ cω → (∀ n → Cl (fsn q n) V) → Cl q V
  Cl-lim {q} {V} e h =
    cl (mL e (λ n → cF (h n)))
       (mL (cofψω u₀ (t ++ q) (cof++ω t q e))
         (λ n → subst (λ s → M⁰ s (H V)) (sym (trans (fsnψω u₀ (t ++ q) n (cof++ω t q e)) (cong ψ₀ᵗ (fsn++ t q n e))))
           (cH (h n))))
       (mL (cofψω u₀ (t ++ q) (cof++ω t q e))
         (λ n → subst (λ s → M⁰ s (W V)) (sym (trans (fsnψω u₀ (t ++ q) n (cof++ω t q e)) (cong ψ₀ᵗ (fsn++ t q n e))))
           (cW (h n))))
```

## 两种结点的折叠形状

分支取第 1 层树的结点: 折到第 1 层与第 0 层都不保留, 回灌链 `vch` 走折到第 1 层的 `F₁`. 分支取第 0 层树的结点: 折到第 1 层保留, 折到第 0 层不保留, 回灌链 `wch` 走 `H`.

```agda
  module Nd1 (G : Tr one → Tr two) where
    vch : ℕ → Tr one
    vch = iter (λ c → F₁ (G c)) zero

    nodeF : ∀ {s} k → M¹ s (F₁ (G (vch k))) → M¹ s (F₁ (Ω (inj₁ tt) G))
    nodeF k = G¹.m-cum (λ m → F₁ (G (vch m))) (λ m → nzF₁ (G (vch m))) k

    nodeH : ∀ {s} k → M⁰ s (H (G (vch k))) → M⁰ s (H (Ω (inj₁ tt) G))
    nodeH k = G⁰.m-cum (λ m → H (G (vch m))) (λ m → nzH (G (vch m))) k

    nodeW : ∀ {s} k → M⁰ s (W (G (vch k))) → M⁰ s (W (Ω (inj₁ tt) G))
    nodeW k = G⁰.m-cum (λ m → W (G (vch m))) (λ m → nzW (G (vch m))) k

    nodeCl : ∀ {q} k → Cl q (G (vch k)) → Cl q (Ω (inj₁ tt) G)
    nodeCl k (cl a b c) = cl (nodeF k a) (nodeH k b) (nodeW k c)

  module Nd0 (G : Tr zero → Tr two) where
    wch : ℕ → Tr zero
    wch = iter (λ c → H (G c)) zero

    nodeH : ∀ {s} k → M⁰ s (H (G (wch k))) → M⁰ s (H (Ω (inj₂ (inj₁ tt)) G))
    nodeH k = G⁰.m-cum (λ m → H (G (wch m))) (λ m → nzH (G (wch m))) k

    nodeW : ∀ {s} k → M⁰ s (W (G (wch k))) → M⁰ s (W (Ω (inj₂ (inj₁ tt)) G))
    nodeW k = G⁰.m-cum (λ m → W (G (wch m))) (λ m → nzW (G (wch m))) k
```

## 叶: 上下文里的 Ω₂

`⟦ C ⟧ (Ωt two)` 是结点 c ↦ `up (⟦ C ⟧ zero) tt (suc c)`. 它的回灌链是第 1 层上以 `⟦ C ⟧ zero` 的折叠为底的链, 对着 ψ₁(A₀+Ω₂) 的 γ-链 (γ₀ = Ω₁, γₙ₊₁ = ψ₁(A₀+γₙ)); 折到第 0 层时每一项是第 1 层的树 γₙ₊₁ 的折叠, 前缀取 t (不取 t+ψ₁(A₀)).
只用到 "A₀ 的 ψ₁ 对着 `⟦ C ⟧ zero` 折到第 1 层的树" (`k1`).

```agda
  module Leaf (C : Ctx) (A₀ : E.T) (k1 : M¹ (ψ₁ᵗ A₀) (F₁ (⟦ C ⟧ zero))) where
    X₀ : Tr two
    X₀ = ⟦ C ⟧ zero

    D₁ : Base one
    D₁ = dS one tt tt Bᵃ X₀

    open L1 D₁
    module PL = Pre lift (m1F X₀) t (m0H X₀) (m0W X₀)

    gL : Tr one → Tr two
    gL c = up X₀ tt (suc c) (z◃s c)

    open Nd1 gL

    Q : E.T
    Q = A₀ ++ Ω₂ᵗ

    cQ : cof Q ≡ cΩ u₁
    cQ = cof++Ω A₀ Ω₂ᵗ refl

    fQ : ∀ η → fsT Q η ≡ A₀ ++ η
    fQ η = fsT++ A₀ Ω₂ᵗ η refl

    γ : ℕ → E.T
    γ = γT Q u₁

    sγ : ∀ n → M¹ (γ n) (vch (suc n))
    sγ zero    = mw (m1F X₀) (◃l zero)
    sγ (suc n) =
      mw (subst (λ s → M¹ (ψ₁ᵗ s) (F¹ (vch (suc n)))) (sym (fQ (γ n))) (PFp k1 (sγ n))) (◃l zero)

    lfH : ∀ n → M⁰ (ψ₀ᵗ (t ++ γ n)) (H (Ω (inj₁ tt) gL))
    lfH n = nodeH (suc n) (mw (PL.QHp (sγ n)) (◃l zero))

    lfW : ∀ n → M⁰ (ψ₀ᵗ (t ++ γ n)) (W (Ω (inj₁ tt) gL))
    lfW n = nodeW (suc n) (mw (PL.VWp (sγ n)) (◃l zero))

    leafΩ₁ : Cl Ω₁ᵗ (⟦ C ⟧ (Ωt two))
    leafΩ₁ = subst (Cl Ω₁ᵗ) (sym (eΩt C zero)) (cl (m1F (Ω (inj₁ tt) gL)) (lfH 0) (lfW 0))

    leafCl : Cl (ψ₁ᵗ Q) (⟦ C ⟧ (Ωt two))
    leafCl = subst (Cl (ψ₁ᵗ Q)) (sym (eΩt C zero))
      (Cl-lim (cofψΩ u₁ Q cQ)
        (λ n → subst (λ s → Cl s (Ω (inj₁ tt) gL)) (sym (fsnψΩ u₁ Q n cQ))
          (cl (nodeF (suc n) (sγ (suc n))) (lfH (suc n)) (lfW (suc n)))))
```

## 上下文的条件与带上下文的陈述

`Kn C A₀`: A₀ 的 ψ₁ 对着 `⟦ C ⟧ zero` 折到第 1 层的树, 且三条结论对 `⟦ C ⟧ y` 成立 (y 在 Ω₂ 之上). 空上下文与空前缀满足 (`kn₀`); 向里加一项保持 (`ext`).
`TC p Y`: 对一切满足条件的上下文, 三条结论对 ψ₁(A₀+p) 与 `⟦ C ⟧ Y` 成立.

```agda
  record Kn (C : Ctx) (A₀ : E.T) : Set where
    constructor kn
    field
      k1 : M¹ (ψ₁ᵗ A₀) (F₁ (⟦ C ⟧ zero))
      k0 : (y : Tr two) → Ωt two ⊴ y → Cl (ψ₁ᵗ A₀) (⟦ C ⟧ y)
  open Kn

  kn₀ : Kn ε []
  kn₀ = kn hβ₁ (λ y le → Cl-up⊴ (Leaf.leafΩ₁ ε [] hβ₁) le)

  TC : E.T → Tr two → Set
  TC p Y = (C : Ctx) (A₀ : E.T) → Kn C A₀ → Cl (ψ₁ᵗ (A₀ ++ p)) (⟦ C ⟧ Y)

  ext : ∀ {C A₀ p Y} → Kn C A₀ → TC p Y → Kn (C ▸ Y) (A₀ ++ p)
  ext {C} {A₀} {p} {Y} k tc = kn (cF (tc C A₀ k)) (λ y le → Cl-up⊴ (tc C A₀ k) (c⊴ C (+⊴ Y y)))

  TC-up◃ : ∀ {p Y Y′} → TC p Y → two ⊢ Y ◃ Y′ → TC p Y′
  TC-up◃ tc d C A₀ k = Cl-up◃ (tc C A₀ k) (cm C d)

  TC-up⊴ : ∀ {p Y Y′} → TC p Y → Y ⊴ Y′ → TC p Y′
  TC-up⊴ tc ⊴r     = tc
  TC-up⊴ tc (⊴◃ d) = TC-up◃ tc d

  leafTC : TC Ω₂ᵗ (Ωt two)
  leafTC C A₀ k = Leaf.leafCl C A₀ (k1 k)
```

## 极限, 后继, 两种结点

`limTC`: 规则 5 (ω). `Next.nextL`: 规则 4, ψ₂(b)[n] = ψ₂(b′)·n 对着 `next Y` 的第 n 项; 第 n 项是右结合的和, 逐项收进上下文 (`stepN`), 第 0 项用上下文的条件 `k0`.

```agda
  limTC : ∀ {b Y} → cof b ≡ cω → (∀ n → TC (ψ₂ᵗ (fsn b n)) Y) → TC (ψ₂ᵗ b) Y
  limTC {b} {Y} e h C A₀ k =
    Cl-lim (cofψω u₁ (A₀ ++ ψ₂ᵗ b) (cof++ω A₀ (ψ₂ᵗ b) (cofψω u₂ b e)))
      (λ n → subst (λ s → Cl s (⟦ C ⟧ Y))
        (sym (trans (fsnψω u₁ (A₀ ++ ψ₂ᵗ b) n (cof++ω A₀ (ψ₂ᵗ b) (cofψω u₂ b e)))
               (cong ψ₁ᵗ (trans (fsn++ A₀ (ψ₂ᵗ b) n (cofψω u₂ b e)) (cong (A₀ ++_) (fsnψω u₂ b n e))))))
        (h n C A₀ k))

  module Next (b : E.T) (e : cof b ≡ c1) (Y : Tr two) (nz : two ⊢ zero ◃ Y) (hY : Ωt two ⊴ Y)
              (tc : TC (ψ₂ᵗ (pred b)) Y) where
    p′ : E.PT
    p′ = ψ u₂ (pred b)

    stepN : ∀ m C A₀ → Kn C A₀ → Cl (ψ₁ᵗ (A₀ ++ replicate (suc m) p′)) (⟦ C ⟧ (iter (Y +_) Y m))
    stepN zero    C A₀ k = tc C A₀ k
    stepN (suc m) C A₀ k =
      subst (λ s → Cl (ψ₁ᵗ s) (⟦ C ⟧ (Y + iter (Y +_) Y m))) (++-assoc A₀ (p′ ∷ []) (replicate (suc m) p′))
        (stepN m (C ▸ Y) (A₀ ++ ψ₂ᵗ (pred b)) (ext k tc))

    nextL : TC (ψ₂ᵗ b) (next Y nz)
    nextL C A₀ k =
      Cl-lim (cofψω u₁ (A₀ ++ ψ₂ᵗ b) (cof++ω A₀ (ψ₂ᵗ b) (cofψ1 u₂ b e)))
        (λ n → subst (λ s → Cl s (⟦ C ⟧ (next Y nz)))
          (sym (trans (fsnψω u₁ (A₀ ++ ψ₂ᵗ b) n (cof++ω A₀ (ψ₂ᵗ b) (cofψ1 u₂ b e)))
                 (cong ψ₁ᵗ (trans (fsn++ A₀ (ψ₂ᵗ b) n (cofψ1 u₂ b e)) (cong (A₀ ++_) (fsnψ1 u₂ b n e))))))
          (go n))
      where
      go : ∀ n → Cl (ψ₁ᵗ (A₀ ++ replicate n p′)) (⟦ C ⟧ (next Y nz))
      go zero    = subst (λ s → Cl (ψ₁ᵗ s) (⟦ C ⟧ (next Y nz))) (sym (++-identityʳ A₀))
                     (k0 k (next Y nz) (⊴◃ (⊴-◃ hY (◃l zero))))
      go (suc m) = Cl-up◃ (stepN m C A₀ k) (cm C (◃l m))
```

分支取第 0 层树的结点 (共尾 Ω₁): 折到第 1 层保留, 记号是规则 5Ω; 折到第 0 层走规则 6 的 γ-链, 对着回灌链 `wch`.

```agda
  module Node0 (b : E.T) (e : cof b ≡ cΩ []) (G₀ : Tr zero → Tr two)
               (hyp : ∀ η c → M⁰ η c → TC (ψ₂ᵗ (fsT b η)) (G₀ c)) (C : Ctx) (A₀ : E.T) (k : Kn C A₀) where
    G : Tr zero → Tr two
    G c = ⟦ C ⟧ (G₀ c)

    open Nd0 G

    Q : E.T
    Q = A₀ ++ ψ₂ᵗ b

    cQ : cof Q ≡ cΩ []
    cQ = cof++Ω A₀ (ψ₂ᵗ b) (cofψΩ u₂ b e)

    fQ : ∀ η → fsT Q η ≡ A₀ ++ ψ₂ᵗ (fsT b η)
    fQ η = trans (fsT++ A₀ (ψ₂ᵗ b) η (cofψΩ u₂ b e)) (cong (A₀ ++_) (fsTψΩ u₂ b η e))

    B′ : E.T
    B′ = t ++ ψ₁ᵗ Q

    cB : cof B′ ≡ cΩ []
    cB = cof++Ω t (ψ₁ᵗ Q) (cofψΩ u₁ Q cQ)

    fB : ∀ η → fsT B′ η ≡ t ++ ψ₁ᵗ (A₀ ++ ψ₂ᵗ (fsT b η))
    fB η = trans (fsT++ t (ψ₁ᵗ Q) η (cofψΩ u₁ Q cQ))
             (cong (t ++_) (trans (fsTψΩ u₁ Q η cQ) (cong ψ₁ᵗ (fQ η))))

    atη : ∀ η c → M⁰ η c → Cl (ψ₁ᵗ (A₀ ++ ψ₂ᵗ (fsT b η))) (G c)
    atη η c l = hyp η c l C A₀ k

    chain : ∀ n → M⁰ (γT B′ [] n) (wch (suc n))
    chain zero    = pos⁰ (H (G zero)) (nzH (G zero))
    chain (suc n) =
      subst (λ s → M⁰ (ψ₀ᵗ s) (H (G (wch (suc n))))) (sym (fB (γT B′ [] n)))
        (cH (atη (γT B′ [] n) (wch (suc n)) (chain n)))

    node : Cl (ψ₁ᵗ Q) (⟦ C ⟧ (Ω (inj₂ (inj₁ tt)) G₀))
    node = subst (Cl (ψ₁ᵗ Q)) (sym (eΩ C (inj₂ (inj₁ tt)) G₀))
      (cl (mΩ (cofψΩ u₁ Q cQ) refl
            (λ η c l → subst (λ s → M¹ s (F₁ (G c))) (sym (trans (fsTψΩ u₁ Q η cQ) (cong ψ₁ᵗ (fQ η)))) (cF (atη η c l))))
          (mL (cofψΩ u₀ B′ cB)
            (λ n → subst (λ s → M⁰ s (H (Ω (inj₂ (inj₁ tt)) G))) (sym (fsnψΩ u₀ B′ n cB))
              (nodeH (suc n) (subst (λ s → M⁰ (ψ₀ᵗ s) (H (G (wch (suc n))))) (sym (fB (γT B′ [] n)))
                (cH (atη (γT B′ [] n) (wch (suc n)) (chain n)))))))
          (mL (cofψΩ u₀ B′ cB)
            (λ n → subst (λ s → M⁰ s (W (Ω (inj₂ (inj₁ tt)) G))) (sym (fsnψΩ u₀ B′ n cB))
              (nodeW (suc n) (subst (λ s → M⁰ (ψ₀ᵗ s) (W (G (wch (suc n))))) (sym (fB (γT B′ [] n)))
                (cW (atη (γT B′ [] n) (wch (suc n)) (chain n))))))))
```

分支取第 1 层树的结点 (共尾 Ω₂): ψ₁ 处走规则 6, γ-链对着回灌链 `vch`; 三条结论都逐项给.

```agda
  module Node1 (b : E.T) (e : cof b ≡ cΩ u₁) (G₀ : Tr one → Tr two)
               (hyp : ∀ η c → M¹ η c → TC (ψ₂ᵗ (fsT b η)) (G₀ c)) (C : Ctx) (A₀ : E.T) (k : Kn C A₀) where
    G : Tr one → Tr two
    G c = ⟦ C ⟧ (G₀ c)

    open Nd1 G

    Q : E.T
    Q = A₀ ++ ψ₂ᵗ b

    cQ : cof Q ≡ cΩ u₁
    cQ = cof++Ω A₀ (ψ₂ᵗ b) (cofψΩ u₂ b e)

    fQ : ∀ η → fsT Q η ≡ A₀ ++ ψ₂ᵗ (fsT b η)
    fQ η = trans (fsT++ A₀ (ψ₂ᵗ b) η (cofψΩ u₂ b e)) (cong (A₀ ++_) (fsTψΩ u₂ b η e))

    γ : ℕ → E.T
    γ = γT Q u₁

    atη : ∀ η c → M¹ η c → Cl (ψ₁ᵗ (A₀ ++ ψ₂ᵗ (fsT b η))) (G c)
    atη η c l = hyp η c l C A₀ k

    chain : ∀ n → M¹ (γ n) (vch (suc n))
    chain zero    = m1F (G zero)
    chain (suc n) =
      subst (λ s → M¹ (ψ₁ᵗ s) (F₁ (G (vch (suc n))))) (sym (fQ (γ n))) (cF (atη (γ n) (vch (suc n)) (chain n)))

    node : Cl (ψ₁ᵗ Q) (⟦ C ⟧ (Ω (inj₁ tt) G₀))
    node = subst (Cl (ψ₁ᵗ Q)) (sym (eΩ C (inj₁ tt) G₀))
      (Cl-lim (cofψΩ u₁ Q cQ)
        (λ n → subst (λ s → Cl s (Ω (inj₁ tt) G)) (sym (trans (fsnψΩ u₁ Q n cQ) (cong ψ₁ᵗ (fQ (γ n)))))
          (nodeCl (suc n) (atη (γ n) (vch (suc n)) (chain n)))))
```

## 主归纳

对 `M² a x` 归纳: ψ₂(a) 与 `F² x` 满足 `TC`. 孩子里的和 (`Tu¹`, `Tu⁰`) 对孩子的推导归纳, 上折的底 b 在 Ω₂ 之上.

```agda
  Tu⁰ : ∀ {t′} (d : Dn two zero) (b : Tr two) (nb : two ⊢ zero ◃ b) → Ωt two ⊴ b → TC (ψ₂ᵗ t′) b
      → ∀ {s y} → M⁰ s y → TC (ψ₂ᵗ (t′ ++ s)) (Up zero d b nb y)
  Tu⁰ {t′} d b nb hb tb (mz {x = y}) =
    ++[] (λ r → TC (ψ₂ᵗ r) (Up zero d b nb y)) t′ (TC-up⊴ tb (up⊵ zero d b nb y))
  Tu⁰ {t′} d b nb hb tb (m1 {t = s} {x = y} e r) =
    Next.nextL (t′ ++ s) (cof++1 t′ s e) (Up zero d b nb y) (Up-nz zero d b nb y) (⊴-trans hb (up⊵ zero d b nb y))
      (subst (λ r′ → TC (ψ₂ᵗ r′) (Up zero d b nb y)) (sym (pred++ t′ s e)) (Tu⁰ d b nb hb tb r))
  Tu⁰ {t′} d b nb hb tb (mL {t = s} {x = y} e h) =
    limTC (cof++ω t′ s e)
      (λ n → subst (λ r′ → TC (ψ₂ᵗ r′) (Up zero d b nb y)) (sym (fsn++ t′ s n e)) (Tu⁰ d b nb hb tb (h n)))
  Tu⁰ d b nb hb tb (mΩ {p = ()} _ _ _)
  Tu⁰ d b nb hb tb (mU {c = ()} _ _)
  Tu⁰ d b nb hb tb (mw m r) = TC-up◃ (Tu⁰ d b nb hb tb m) (Up-mono zero d b nb r)

  Tu¹ : ∀ {t′} (b : Tr two) (nb : two ⊢ zero ◃ b) → Ωt two ⊴ b → TC (ψ₂ᵗ t′) b
      → ∀ {s y} → M¹ s y → TC (ψ₂ᵗ (t′ ++ s)) (Up one (down stop tt) b nb y)
  Tu¹ {t′} b nb hb tb (mz {x = y}) =
    ++[] (λ r → TC (ψ₂ᵗ r) (Up one (down stop tt) b nb y)) t′ (TC-up⊴ tb (up⊵ one (down stop tt) b nb y))
  Tu¹ {t′} b nb hb tb (m1 {t = s} {x = y} e r) =
    Next.nextL (t′ ++ s) (cof++1 t′ s e) (Up one (down stop tt) b nb y) (Up-nz one (down stop tt) b nb y)
      (⊴-trans hb (up⊵ one (down stop tt) b nb y))
      (subst (λ r′ → TC (ψ₂ᵗ r′) (Up one (down stop tt) b nb y)) (sym (pred++ t′ s e)) (Tu¹ b nb hb tb r))
  Tu¹ {t′} b nb hb tb (mL {t = s} {x = y} e h) =
    limTC (cof++ω t′ s e)
      (λ n → subst (λ r′ → TC (ψ₂ᵗ r′) (Up one (down stop tt) b nb y)) (sym (fsn++ t′ s n e)) (Tu¹ b nb hb tb (h n)))
  Tu¹ {t′} b nb hb tb (mΩ {t = s} {p = inj₁ tt} {g = g} e refl h) =
    Node0.node (t′ ++ s) (cof++Ω t′ s e) (λ c → Up one (down stop tt) b nb (g c))
      (λ η c l → subst (λ r′ → TC (ψ₂ᵗ r′) (Up one (down stop tt) b nb (g c))) (sym (fsT++ t′ s η e))
        (Tu¹ b nb hb tb (h η c l)))
  Tu¹ b nb hb tb (mΩ {p = inj₂ ()} _ _ _)
  Tu¹ {t′} b nb hb tb (mU {t = s₀} {s = s₁} {x = y₀} {y = y₁} m ch) =
    subst (λ r′ → TC (ψ₂ᵗ r′)
        (Up zero (down (down stop tt) tt) (Up one (down stop tt) b nb y₀) (Up-nz one (down stop tt) b nb y₀) y₁))
      (++-assoc t′ s₀ s₁)
      (Tu⁰ (down (down stop tt) tt) (Up one (down stop tt) b nb y₀) (Up-nz one (down stop tt) b nb y₀)
        (⊴-trans hb (up⊵ one (down stop tt) b nb y₀)) (Tu¹ b nb hb tb m) ch)
  Tu¹ b nb hb tb (mw m r) = TC-up◃ (Tu¹ b nb hb tb m) (Up-mono one (down stop tt) b nb r)

  T² : ∀ {a x} → M² a x → TC (ψ₂ᵗ a) (F² x)
  T² (mz {x = x}) = TC-up⊴ leafTC (F²⊵ x)
  T² (m1 {t = a} {x = x} e r) = Next.nextL a e (F² x) (nzF² x) (F²⊵ x) (T² r)
  T² (mL e h) = limTC e (λ n → T² (h n))
  T² (mΩ {t = a} {p = inj₁ tt} {g = g} e refl h) =
    Node1.node a e (λ c → F² (g c)) (λ η c l → T² (h η c l))
  T² (mΩ {t = a} {p = inj₂ (inj₁ tt)} {g = g} e refl h) =
    Node0.node a e (λ c → F² (g c)) (λ η c l → T² (h η c l))
  T² (mΩ {p = inj₂ (inj₂ ())} _ _ _)
  T² (mU {x = x} m ch) = Tu¹ (F² x) (nzF² x) (F²⊵ x) (T² m) ch
  T² (mw m d) = TC-up◃ (T² m) (monoF² d)
```

## 层号 3 的 Ω 树

折叠是 `next (W (z k))` 的部分和极限 (`form³`, `refl`). 第 n+1 行在 `W (F² (z n))` 之上; `z n` 对着 aₙ (a₀ = 0, aₙ₊₁ = γ³ₙ), 所以它对着 ψ₀(t+ψ₁(ψ₂(aₙ))) = ψ₀(t+ψ₁(γ³ₙ)).

```agda
  Ω₃ᵗ : E.T
  Ω₃ᵗ = E.Ωs u₂

  form³ : ψ⊥ three tt tt B₃ (Ωt three)
        ≡ limc (λ k → next (W (z k)) (nzW (z k))) (λ k → nz⊥ three tt tt B₃ (up zero tt (suc (z k)) (z◃s (z k))))
  form³ = refl

  rowW : ∀ n → M⁰ (ψ₀ᵗ (t ++ ψ₁ᵗ (γ³ n))) (W (F² (z n)))
  rowW zero    = cW (T² (mz {x = zero}) ε [] kn₀)
  rowW (suc n) = cW (T² (sγ³ n) ε [] kn₀)

  row³ : ∀ n → M⁰ (ψ₀ᵗ (t ++ ψ₁ᵗ (γ³ n))) (ψ⊥ three tt tt B₃ (Ωt three))
  row³ n =
    G⁰.m-cum (λ k → next (W (z k)) (nzW (z k))) (λ k → nz⊥ three tt tt B₃ (up zero tt (suc (z k)) (z◃s (z k))))
      (suc n) (mw (mw (rowW n) (mono⊥ two tt tt Bᵃ (◃l zero))) (◃l zero))

  cΩ₃ : cof (ψ₁ᵗ Ω₃ᵗ) ≡ cω
  cΩ₃ = refl

  anchor³ : M⁰ (ψ₀ᵗ (t ++ ψ₁ᵗ Ω₃ᵗ)) (ψ⊥ three tt tt B₃ (Ωt three))
  anchor³ = mL (cofψω u₀ (t ++ ψ₁ᵗ Ω₃ᵗ) (cof++ω t (ψ₁ᵗ Ω₃ᵗ) cΩ₃))
    (λ n → subst (λ s → M⁰ s (ψ⊥ three tt tt B₃ (Ωt three)))
      (sym (trans (fsnψω u₀ (t ++ ψ₁ᵗ Ω₃ᵗ) n (cof++ω t (ψ₁ᵗ Ω₃ᵗ) cΩ₃)) (cong ψ₀ᵗ (fsn++ t (ψ₁ᵗ Ω₃ᵗ) n cΩ₃))))
      (row³ n))
```
