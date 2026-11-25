# 合法块的 kall

> 判决: 编译定理, 无前提, 成品候选. `kall`: 对任意带证据与路线的层号 a, 下一站 `Nx a` 折到下标层 a (路径 `ink self`) 时, 孩子 c 里槽位带见证且严格在基底 a 里的结点, 以同一基底槽位保留; 对一切孩子 c, 一切底. `kall-tw`: 塔各项的实例 (证据逐字是 `Ev-tw`, `Rt-tw`).
> 证法与 `YiCumKept.lemAᶜ`, `lemBᶜ`, `child-keptᶜ` 同文, 路线换成合法块的 `Rt⊕ a b ra rb`; 保留判定 `kp` 沿 `lift` 下行只经 `inlu`, `inu` 两行, 不比较孩子.
> 不否定什么. 只说保留, 不说分支.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLPKall where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLPIface using (Nx; evc; Ev-Nx; Rt-Nx; InB; ib0; ibS; ibL; ibW; ibK; prE; liftBr; brE; Kept)
```

## 保留判定沿 `lift` 下行

```agda
lemA : (a b : L) (ea : Ev a) (eb : EvO a b) (ra : Rt a) (rb : RtP b) {K : L} (v : K ≤ a) (t : Pos⁼ K)
  {j : L} (u : j ≤ a) {X : Set}
  (Kc : (q : Pos j) → (Br j q → Br⁼ (a ⊕ b) (psh (v ∙ lift a b) t)) → X) (d : X)
  → kp⁼ (a ⊕ b) (Ev⊕ a b ea eb) (Rt⊕ a b ra rb) (psh (v ∙ lift a b) t) (u ∙ lift a b) Kc d
  ≡ kp⁼ a ea ra (psh v t) u (λ q cv → Kc q (λ z → liftBr a b v t (cv z))) d
lemA a zero     ea eb            ra rb        v t u Kc d = refl
lemA a (suc b)  ea eb            ra rb        v t u Kc d = lemA a b ea eb ra rb v t u Kc d
lemA a (lim g)  ea eb            ra (rb , R)  v t u Kc d = lemA a (g zero) ea (eb zero) ra (rb zero) v t u Kc d
lemA a (Ωₗ k h) ea (w , ek , eb) ra (rk , rb) v t u Kc d = lemA a (h zero) ea (eb zero) ra (rb zero) v t u Kc d

lemB : (a b : L) (ea : Ev a) (ra : Rt a) {t : Pos (a ⊕ b)} (i : InB a b t) (eb : EvO a b) (rb : RtP b)
  {j : L} (u : j ≤ a) {X : Set} (Kc : (q : Pos j) → (Br j q → Br (a ⊕ b) t) → X) (d : X)
  → kp (a ⊕ b) (Ev⊕ a b ea eb) (Rt⊕ a b ra rb) t (u ∙ lift a b) Kc d
  ≡ kp⁼ a ea ra (prE i eb) u (λ q cv → Kc q (λ z → brE i eb (cv z))) d
lemB a _ ea ra (ib0 p)   eb            rb        u Kc d = refl
lemB a _ ea ra (ibS i)   eb            rb        u Kc d = lemB a _ ea ra i eb rb u Kc d
lemB a _ ea ra (ibL n i) eb            (rb , R)  u Kc d = lemB a _ ea ra i (eb n) (rb n) u Kc d
lemB a _ ea ra (ibW c i) (w , ek , eb) (rk , rb) u Kc d = lemB a _ ea ra i (eb c) (rb c) u Kc d
lemB a _ ea ra (ibK {h = h} t) (w , ek , eb) (rk , rb) u Kc d =
  lemA a (h zero) ea (eb zero) ra (rb zero) w t u _ d
```

## 保留

```agda
kept-self : (a : L) (ea : Ev a) (ra : Rt a) (s : Pos⁼ a) (p : Pos a) → s ≡ inj₂ p
  → (F : (q : Pos a) → (Br a q → Br⁼ a s) → Br a q → Tr a) (d : Tr a)
  → Kept p (kp⁼ a ea ra s self (λ q cv → Ω q (F q cv)) d)
kept-self a ea ra .(inj₂ p) p refl F d = F p (λ z → z) , refl

child-kept : (a b : L) (ea : Ev a) (eb : EvO a b) (ra : Rt a) (rb : RtP b) (B : Base (a ⊕ b))
  (β : Tr a) (nβ : a ⊢ zero ◃ β) {t : Pos (a ⊕ b)} (G : Br (a ⊕ b) t → Tr (a ⊕ b))
  (i : InB a b t) (p : Pos a) → prE i eb ≡ inj₂ p
  → Kept p (ψs (a ⊕ b) (Ev⊕ a b ea eb) (Rt⊕ a b ra rb) B a (self ∙ lift a b) β nβ (Ω t G))
child-kept a b ea eb ra rb B β nβ G i p e =
  subst (Kept p)
    (sym (lemB a b ea ra i eb rb self
      (λ q cv → Ω q (λ z → ψs (a ⊕ b) (Ev⊕ a b ea eb) (Rt⊕ a b ra rb) B a (self ∙ lift a b) β nβ (G (cv z)))) _))
    (kept-self a ea ra (prE i eb) p e
      (λ q cv z → ψs (a ⊕ b) (Ev⊕ a b ea eb) (Rt⊕ a b ra rb) B a (self ∙ lift a b) β nβ (G (brE i eb (cv z)))) _)
```

## kall

```agda
kall : (a : L) (ea : Ev a) (ra : Rt a) (B : Base (Nx a)) (β : Tr a) (nβ : a ⊢ zero ◃ β) (x : Tr (Nx a))
  (c : Tr a) {t : Pos (a ⊕ ↑ a c)} (G : Br (a ⊕ ↑ a c) t → Tr (a ⊕ ↑ a c)) (e : a ⊕ ↑ a c ⊢ zero ◃ Ω t G)
  (i : InB a (↑ a c) t) (p : Pos a) → prE i (evc a ea c) ≡ inj₂ p
  → Kept p (ψs (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B a (ink self) β nβ (up x c (Ω t G) e))
kall a ea ra B β nβ x c G e i p q =
  child-kept a (↑ a c) ea (evc a ea c) ra (RtP↑ a ra c) _ _ _ G i p q

kall-tw : (n : ℕ) (B : Base (tw (suc n))) (β : Tr (tw n)) (nβ : tw n ⊢ zero ◃ β) (x : Tr (tw (suc n)))
  (c : Tr (tw n)) {t : Pos (tw n ⊕ ↑ (tw n) c)} (G : Br (tw n ⊕ ↑ (tw n) c) t → Tr (tw n ⊕ ↑ (tw n) c))
  (e : tw n ⊕ ↑ (tw n) c ⊢ zero ◃ Ω t G)
  (i : InB (tw n) (↑ (tw n) c) t) (p : Pos (tw n)) → prE i (evc (tw n) (Ev-tw n) c) ≡ inj₂ p
  → Kept p (ψs (tw (suc n)) (Ev-tw (suc n)) (Rt-tw (suc n)) B (tw n) (ink self) β nβ (up x c (Ω t G) e))
kall-tw n = kall (tw n) (Ev-tw n) (Rt-tw n)
```
