# 累加的读回: 孩子结点的槽位保留

> 验收文件. 编译定理, 无前提: `kallᶜ`, 即 `YiLimIface.Iface` 的字段 `kall` 对累加的塔的对应物 (塔第 n+1 项里孩子层的结点, 槽位在下标层 tw n 里时, 折到 tw n 保留).
> 证法与 `YiLimCheck.lemA`, `lemB`, `child-kept` 同文, 路线换成 `Req→Rt (a ⊕ b) (Req⊕ a b ra rb)`; 沿 `lift` 下行只经 `inlu` 与 `inu` 的行.
> 不否定什么. `YiLimIface.Iface` 本身的字段写死了旧塔, 不能直接实填.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCumKept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiPhiNegK using (InB; ib0; ibS; ibL; ibW; ibK; prE; brE; liftBr; Kept)
open import OCF.Lean.YiLimBlock
open import OCF.Lean.YiLimFold
open import OCF.Lean.YiLimCheck using (kept-self)
open import OCF.Lean.YiCumBlock
```

```agda
lemAᶜ : (a b : L) (ea : Ev a) (eb : EvO a b) (ra : Req a) (rb : ReqP b) {K : L} (v : K ≤ a) (t : Pos⁼ K)
  {j : L} (u : j ≤ a) {X : Set}
  (Kc : (q : Pos j) → (Br j q → Br⁼ (a ⊕ b) (psh (v ∙ lift a b) t)) → X) (d : X)
  → kp⁼ (a ⊕ b) (Ev⊕ a b ea eb) (Req→Rt (a ⊕ b) (Req⊕ a b ra rb)) (psh (v ∙ lift a b) t) (u ∙ lift a b) Kc d
  ≡ kp⁼ a ea (Req→Rt a ra) (psh v t) u (λ q cv → Kc q (λ z → liftBr a b v t (cv z))) d
lemAᶜ a zero     ea eb            ra rb        v t u Kc d = refl
lemAᶜ a (suc b)  ea eb            ra rb        v t u Kc d = lemAᶜ a b ea eb ra rb v t u Kc d
lemAᶜ a (lim g)  ea eb            ra (rb , R)  v t u Kc d = lemAᶜ a (g zero) ea (eb zero) ra (rb zero) v t u Kc d
lemAᶜ a (Ωₗ k h) ea (w , ek , eb) ra (rk , rb) v t u Kc d = lemAᶜ a (h zero) ea (eb zero) ra (rb zero) v t u Kc d

lemBᶜ : (a b : L) (ea : Ev a) (ra : Req a) {t : Pos (a ⊕ b)} (i : InB a b t) (eb : EvO a b) (rb : ReqP b)
  {j : L} (u : j ≤ a) {X : Set} (Kc : (q : Pos j) → (Br j q → Br (a ⊕ b) t) → X) (d : X)
  → kp (a ⊕ b) (Ev⊕ a b ea eb) (Req→Rt (a ⊕ b) (Req⊕ a b ra rb)) t (u ∙ lift a b) Kc d
  ≡ kp⁼ a ea (Req→Rt a ra) (prE i eb) u (λ q cv → Kc q (λ z → brE i eb (cv z))) d
lemBᶜ a _ ea ra (ib0 p)   eb            rb        u Kc d = refl
lemBᶜ a _ ea ra (ibS i)   eb            rb        u Kc d = lemBᶜ a _ ea ra i eb rb u Kc d
lemBᶜ a _ ea ra (ibL n i) eb            (rb , R)  u Kc d = lemBᶜ a _ ea ra i (eb n) (rb n) u Kc d
lemBᶜ a _ ea ra (ibW c i) (w , ek , eb) (rk , rb) u Kc d = lemBᶜ a _ ea ra i (eb c) (rb c) u Kc d
lemBᶜ a _ ea ra (ibK {h = h} t) (w , ek , eb) (rk , rb) u Kc d =
  lemAᶜ a (h zero) ea (eb zero) ra (rb zero) w t u _ d

child-keptᶜ : (a b : L) (ea : Ev a) (eb : EvO a b) (ra : Req a) (rb : ReqP b) (B : Base (a ⊕ b)) (β : Tr a)
  {t : Pos (a ⊕ b)} (G : Br (a ⊕ b) t → Tr (a ⊕ b)) (i : InB a b t) (p : Pos a) → prE i eb ≡ inj₂ p
  → Kept p (ψs (a ⊕ b) (Ev⊕ a b ea eb) (Req→Rt (a ⊕ b) (Req⊕ a b ra rb)) B a (self ∙ lift a b) β (Ω t G))
child-keptᶜ a b ea eb ra rb B β G i p e =
  subst (Kept p)
    (sym (lemBᶜ a b ea ra i eb rb self
      (λ q cv → Ω q (λ z → ψs (a ⊕ b) (Ev⊕ a b ea eb) (Req→Rt (a ⊕ b) (Req⊕ a b ra rb)) B a (self ∙ lift a b) β (G (cv z)))) _))
    (kept-self a ea (Req→Rt a ra) (prE i eb) p e
      (λ q cv z → ψs (a ⊕ b) (Ev⊕ a b ea eb) (Req→Rt (a ⊕ b) (Req⊕ a b ra rb)) B a (self ∙ lift a b) β (G (brE i eb (cv z)))) _)

evcᶜ : (n : ℕ) (c : Tr (twᶜ n)) → EvO (twᶜ n) (↑ᶜ (twᶜ n) c)
evcᶜ n c = EvO↑ᶜ (twᶜ n) (twᶜ n) (Ev-twᶜ n) self c

kallᶜ : (n : ℕ) (B : Base (twᶜ (suc n))) (β : Tr (twᶜ n)) (x : Tr (twᶜ (suc n))) (c : Tr (twᶜ n))
  {t : Pos (twᶜ n ⊕ ↑ᶜ (twᶜ n) c)} (G : Br (twᶜ n ⊕ ↑ᶜ (twᶜ n) c) t → Tr (twᶜ n ⊕ ↑ᶜ (twᶜ n) c))
  (i : InB (twᶜ n) (↑ᶜ (twᶜ n) c) t) (p : Pos (twᶜ n)) → prE i (evcᶜ n c) ≡ inj₂ p
  → Kept p (ψs (twᶜ (suc n)) (Ev-twᶜ (suc n)) (Rtᶜ-tw (suc n)) B (twᶜ n) (ink self) β (up x c (Ω t G)))
kallᶜ n B β x c G i p e =
  child-keptᶜ (twᶜ n) (↑ᶜ (twᶜ n) c) (Ev-twᶜ n) (evcᶜ n c) (Req-twᶜ n) (ReqP↑ᶜ (twᶜ n) (Req-twᶜ n) c) _ _ G i p e
```
