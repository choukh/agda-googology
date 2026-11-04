# 折叠是和的作用 (三): 差的对应

> 不含记号. 入口 [TLRule](TLRule.lagda.md). `RS`: 输入按 `Rel` 走一段, 状态按 `Inv` 对上旧树, 那么折叠的差就是旧折叠在两端之间走过的路. 对被积函数参数化; 节点的分支是下一层的被积函数.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; Lg)
import OCF.Align.TLRuleSum as N′
module OCF.Align.TLRuleSim (W : A) (lW : Lg W) (S : ∀ {t} → N′.D t → N′.D t) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.CumReadCF hiding (A; Lg; _⊕_)
open import OCF.Align.CumReadCFEq
open import OCF.Align.CumReadCFThm using (_⊴_; ψL)
import OCF.Align.TLRuleSum as N
open N using (D; n0; n1; _⨾_; nl; ni; Int; AccL; acc; ≪≪)
open N.Fold W lW S
open import OCF.Align.TLRuleRel
```

## §1 状态

```agda
Diff : ∀ {M} → St → O M → O M → Set
Diff {M} Δ b y = ∀ {t} (τ : t ⊲ W) (T : Tg t M) (l : Lg M) (T′ : Tg t M) (l′ : Lg M) → Rel t (ψ t T l b) (Δ τ) (ψ t T′ l′ y)

Inv : ∀ {M} → St → O M → Set
Inv {M} Y b = ∀ {t} (τ : t ⊲ W) (T : Tg t M) (l : Lg M) → Rel t (Ω̇ t) (Y τ) (ψ t T l b)

inv+ : ∀ {M} {Y Δ : St} {b y : O M} → Inv Y b → Diff Δ b y → Inv (Y ⊕ Δ) y
inv+ v d τ T l = rc (v τ T l) (d τ T l T l)

inv≈ : ∀ {M} {Y : St} {b b′ : O M} → Inv Y b → b ≈ b′ → b′ ≈ b′ → Inv Y b′
inv≈ {b = b} {b′} v e p τ T l = rr (v τ T l) (ψQ b b′ T l T l e) (ψQ b′ b′ T l T l p)

record Itg {k M : A} (κ : ∀ {j} → j ≪ k → j ≪ M) (A₀ : D k → St → St) (H : O k → O M) (Cw : D k → O k → Set) : Set where
  field
    ict : ContF κ H
    i1  : ∀ w z₀ z₁ (Y : St) → Cw w z₀ → z₁ ≈ os z₀ → z₁ ≈ z₁ → Inv Y (H z₀) → Diff (A₀ w Y) (H z₀) (H z₁)
    icw : ∀ {w z₀ δ z₁} → Cw w z₀ → Rel k z₀ δ z₁ → Cw (w ⨾ δ) z₁
    icr : ∀ {w z z′} → Cw w z → z ≈ z′ → z′ ≈ z′ → Cw w z′
open Itg public
```

## §2 主定理

```agda
RS : ∀ {k M} {κ : ∀ {j} → j ≪ k → j ≪ M} {A₀ : D k → St → St} {H : O k → O M} {Cw : D k → O k → Set}
     (ac : AccL k) (kp : k ⊲ W) → Itg κ A₀ H Cw → ∀ {w z₀ δ z₁} → Cw w z₀ → Rel k z₀ δ z₁ →
     ∀ (Y : St) → Inv Y (H z₀) → Diff (Run ac kp A₀ w δ Y) (H z₀) (H z₁)

RptP : ∀ {k M} {κ : ∀ {j} → j ≪ k → j ≪ M} {A₀ : D k → St → St} {H : O k → O M} {Cw : D k → O k → Set}
       (ac : AccL k) (kp : k ⊲ W) → Itg κ A₀ H Cw → ∀ {w z₀} {d : ℕ → D k} (g : ℕ → O k) → Cw w z₀ → z₀ ≈ g 0 → (∀ n → g n ≈ g n) →
       (∀ m → Rel k (g m) (d m) (g (suc m))) → ∀ (Y : St) → Inv Y (H z₀) → ∀ m →
       Cw (proj₁ (Rpt ac kp A₀ w d Y m)) (g m) × Inv (proj₂ (Rpt ac kp A₀ w d Y m)) (H (g m))

IU : ∀ {j k M} {κ : ∀ {i} → i ≪ k → i ≪ M} {A₀ : D k → St → St} {H : O k → O M} {Cw : D k → O k → Set}
     (ac : AccL k) (ac′ : AccL j) (kp : k ⊲ W) → (I : Itg κ A₀ H Cw) → ∀ {w z₀} → Cw w z₀ →
     (r′ : j ≪ k) (u : N.Ws k (≪S r′) → D k) {κ₁ : ∀ {i} → i ≪ j → i ≪ k} (H₁ : O j → O k) →
     z₀ ≈ H₁ (Ω̇ j) → ContF κ₁ H₁ →
     (∀ w₁ z₀′ z₁′ → Rw k (≪S r′) (Ω̇ j) w₁ z₀′ → z₁′ ≈ os z₀′ → z₁′ ≈ z₁′ → Rel k (H₁ z₀′) (u (N.inS (≪S r′) w₁)) (H₁ z₁′)) →
     Itg (λ s₁ → κ (κ₁ s₁)) (Ai ac r′ kp ac′ A₀ w u) (λ z → H (H₁ z)) (Rel j (Ω̇ j))

RK : ∀ {j k M t} {κ : ∀ {i} → i ≪ k → i ≪ M} {A₀ : D k → St → St} {H : O k → O M} {Cw : D k → O k → Set}
     (ac : AccL k) (ac′ : AccL j) (kp : k ⊲ W) → (I : Itg κ A₀ H Cw) → ∀ {w z₀ z₁} → Cw w z₀ →
     (r′ : j ≪ k) (u : N.Ws k (≪S r′) → D k) (p : j ≪ k) (H₁ : O j → O k) →
     z₁ ≈ oi p (λ z → H₁ (outS (≪S p) z)) → z₁ ≈ z₁ → z₀ ≈ H₁ (Ω̇ j) → ContF (λ s₁ → ≪≪ s₁ p) H₁ →
     (∀ w₁ z₀′ z₁′ → Rw k (≪S r′) (Ω̇ j) w₁ z₀′ → z₁′ ≈ os z₀′ → z₁′ ≈ z₁′ → Rel k (H₁ z₀′) (u (N.inS (≪S r′) w₁)) (H₁ z₁′)) →
     ∀ (Y : St) → Inv Y (H z₀) → (τ : t ⊲ W) (T : Tg t M) (l : Lg M) (T′ : Tg t M) (l′ : Lg M) (rk : Rk j t) →
     Rel t (ψ t T l (H z₀)) (RunK ac ac′ kp A₀ w r′ u Y τ rk) (ψ t T′ l′ (H z₁))

ChnP : ∀ {j M} {κ : ∀ {i} → i ≪ j → i ≪ M} {A₀ : D j → St → St} {G₀ : O j → O M}
       (ac′ : AccL j) (ρ : j ⊲ W) → Itg κ A₀ G₀ (Rel j (Ω̇ j)) → ∀ (P : j ⊲ M) (l′ : Lg M) (Y : St) → Inv Y (G₀ (Ω̇ j)) → ∀ n →
       let γ = chainᵒ (λ z → ψ j (inj₁ P) l′ (G₀ z)) in
       Rel j (Ω̇ j) (proj₁ (Chn ac′ ρ A₀ Y n)) (γ n) ×
       (Rel j (γ n) (proj₁ (proj₂ (Chn ac′ ρ A₀ Y n))) (γ (suc n)) × Inv (proj₂ (proj₂ (Chn ac′ ρ A₀ Y n))) (G₀ (γ n)))

RS {H = H} ac kp I c (rz e p) Y v τ T l T′ l′ = rz (ψQ _ _ T l T′ l′ (cq (ict I) e)) (ψQ _ _ T′ l′ T′ l′ (cq (ict I) p))
RS ac kp I c (rs e p) Y v τ T l T′ l′ = i1 I _ _ _ Y c e p v τ T l T′ l′
RS ac kp I c (rc D₁ D₂) Y v τ T l T′ l′ =
  rc (RS ac kp I c D₁ Y v τ T l T′ l′)
     (RS ac kp I (icw I c D₁) D₂ _ (inv+ v (RS ac kp I c D₁ Y v)) τ T′ l′ T′ l′)
RS ac kp I c (rb e p D) Y v τ T l T′ l′ =
  rb (ψQ _ _ T l T l (cq (ict I) e)) (ψQ _ _ T l T l (cq (ict I) p)) (RS ac kp I (icr I c e p) D Y (inv≈ v (cq (ict I) e) (cq (ict I) p)) τ T l T′ l′)
RS ac kp I c (rr D e p) Y v τ T l T′ l′ =
  rr (RS ac kp I c D Y v τ T l T′ l′) (ψQ _ _ T′ l′ T′ l′ (cq (ict I) e)) (ψQ _ _ T′ l′ T′ l′ (cq (ict I) p))
RS {H = H} ac kp I c (rl g e p q e₀ st) Y v {t} τ T l T′ l′ =
  rl (λ n → ψ t T′ l′ (H (g n)))
     (ψQ _ _ T′ l′ T′ l′ (cl (ict I) g e))
     (ψQ _ _ T′ l′ T′ l′ (cq (ict I) p))
     (λ n → ψQ _ _ T′ l′ T′ l′ (cq (ict I) (q n)))
     (ψQ _ _ T l T′ l′ (cq (ict I) e₀))
     (λ m → RS ac kp I (proj₁ (RptP ac kp I g c e₀ q st Y v m)) (st m) _ (proj₂ (RptP ac kp I g c e₀ q st Y v m)) τ T′ l′ T′ l′)
RS {H = H} ac kp I c (rd g e p q f D) Y v {t} τ T l T′ l′ =
  rd (λ n → ψ t T′ l′ (H (g n)))
     (ψQ _ _ T′ l′ T′ l′ (cl (ict I) g e))
     (ψQ _ _ T′ l′ T′ l′ (cq (ict I) p))
     (λ n → ψQ _ _ T′ l′ T′ l′ (cq (ict I) (q n)))
     (ψL T′ l′ T′ l′ (cm (ict I) f))
     (rr (RS ac kp I c D Y v τ T l T′ l′) (ψQ _ _ T′ l′ T′ l′ (cl (ict I) (λ m → g (suc m)) (λ n → q (suc n)))) (λ n → ψQ _ _ T′ l′ T′ l′ (cq (ict I) (q (suc n)))))
RS (acc f) kp I c (ri r′ u p H₁ e pz e₀ C₁ ds) Y v τ T l T′ l′ =
  RK (acc f) (f r′) kp I c r′ u p H₁ e pz e₀ C₁ ds Y v τ T l T′ l′ (cmpN (≪∘ r′ kp) τ lW)

RptP ac kp I g c e₀ q st Y v zero = icr I c e₀ (q 0) , inv≈ v (cq (ict I) e₀) (cq (ict I) (q 0))
RptP ac kp I g c e₀ q st Y v (suc m) =
  icw I (proj₁ (RptP ac kp I g c e₀ q st Y v m)) (st m) ,
  inv+ (proj₂ (RptP ac kp I g c e₀ q st Y v m)) (RS ac kp I (proj₁ (RptP ac kp I g c e₀ q st Y v m)) (st m) _ (proj₂ (RptP ac kp I g c e₀ q st Y v m)))

IU {j} {k} {κ = κ} {H = H} ac ac′ kp I {w} {z₀} c r′ u H₁ e₀ C₁ ds = record
  { ict = comp C₁ (ict I)
  ; i1 = λ w₂ a₀ a₁ Y′ c₂ d p v′ →
      RS ac kp I (icw I c (rb e₀ (cq C₁ (Ω≈ j)) (IntRel ac′ r′ (λ z′ → u (N.inS (≪S r′) z′)) C₁
                     (λ w₁ z₀′ z₁′ c₁ d₁ p₁ → ds w₁ z₀′ z₁′ (→Rw (≪S r′) c₁) d₁ p₁) (rz (Ω≈ j) (Ω≈ j)) c₂)))
         (ds w₂ a₀ a₁ (→Rw (≪S r′) c₂) d p) Y′ v′
  ; icw = λ c₁ d → rc c₁ d
  ; icr = λ c₁ e p → rr c₁ e p
  }

ChnP {j} ac′ ρ I P l′ Y v zero =
  rz (Ω≈ j) (Ω≈ j) , (v ρ (inj₁ P) l′ , v)
ChnP {j} ac′ ρ I P l′ Y v (suc n) =
  rc (proj₁ ih) (proj₁ (proj₂ ih)) ,
  (RS ac′ ρ I (proj₁ ih) (proj₁ (proj₂ ih)) _ (proj₂ (proj₂ ih)) ρ (inj₁ P) l′ (inj₁ P) l′ ,
   inv+ (proj₂ (proj₂ ih)) (RS ac′ ρ I (proj₁ ih) (proj₁ (proj₂ ih)) _ (proj₂ (proj₂ ih))))
  where ih = ChnP ac′ ρ I P l′ Y v n
```

### 节点

`RK`: 新旧两边的比较要么都保留, 要么都上升. 保留时节点对节点; 上升时和对上升的 $\lim$.

```agda
RK {j} {k} {M} {t} {κ} {A₀} {H} ac ac′ kp I {w} {z₀} {z₁} c r′ u p H₁ e pz e₀ C₁ ds Y v τ T l T′ l′ rk with rkT (κ p) T′ l′ in eq | rk
... | keep s | rise q = ⊥-elim (no-keep-rise s q)
... | rise q | keep s = ⊥-elim (no-keep-rise s q)
... | keep s | keep s′ =
  ri s′ _ s H₂
     (≈-rp _ {r = s}
        (subst (λ v₀ → ψ t T′ l′ (H z₁) ≈ v₀) (ψ-keep T′ l′ (κ p) G₀ s eq) (ψQ _ _ T′ l′ T′ l′ (cn (ict I) p H₁ e (cq C₁))))
        (λ a → cong (λ b → ψ t T′ l′ (G₀ b)) (trans (out-inS (≪S (κ p)) _) (out-inS (≪S s) a))))
     (ψQ _ _ T′ l′ T′ l′ (cq (ict I) pz))
     (ψQ _ _ T l T′ l′ (cq (ict I) e₀))
     (ContF-κ (ψ-ContF T′ l′ s (comp C₁ (ict I))))
     (λ w₂ a₀ a₁ h d p₂ → subst
        (λ z → Rel t (H₂ a₀)
           (Run ac kp A₀ (w ⨾ Int ac′ r′ (λ z′ → u (N.inS (≪S r′) z′)) n0 z) (u (N.inS (≪S r′) z))
             (Y ⊕ Run ac′ ρ (Ai ac r′ kp ac′ A₀ w u) n0 z Y) τ) (H₂ a₁))
        (sym (N.out-inS (≪S s′) w₂))
        (RS ac kp I
           (icw I c (rb e₀ (cq C₁ (Ω≈ j)) (IntRel ac′ r′ (λ z′ → u (N.inS (≪S r′) z′)) C₁
              (λ w₁ z₀′ z₁′ c₁ d₁ p₁ → ds w₁ z₀′ z₁′ (→Rw (≪S r′) c₁) d₁ p₁) (rz (Ω≈ j) (Ω≈ j)) (Rw→ (≪S s′) h))))
           (ds w₂ a₀ a₁ (→Rw (≪S r′) (Rw→ (≪S s′) h)) d p₂)
           _
           (inv+ {b = H (H₁ (Ω̇ j))} (inv≈ v (cq (ict I) e₀) (cq (ict I) (cq C₁ (Ω≈ j))))
              (RS ac′ ρ IUU (rz (Ω≈ j) (Ω≈ j)) (Rw→ (≪S s′) h) Y (inv≈ v (cq (ict I) e₀) (cq (ict I) (cq C₁ (Ω≈ j))))))
           τ T′ l′ T′ l′))
  where
  G₀ = λ a → H (H₁ a)
  H₂ = λ a → ψ t T′ l′ (H (H₁ a))
  ρ = ⊲-tr (≪⊲ r′) kp
  IUU = IU ac ac′ kp I c r′ u H₁ e₀ C₁ ds
... | rise q | rise q′ =
  rl G
     (≈-ol _ (subst (λ v₀ → ψ t T′ l′ (H z₁) ≈ v₀) (ψ-rise T′ l′ (κ p) G₀ q eq) (ψQ _ _ T′ l′ T′ l′ (cn (ict I) p H₁ e (cq C₁))))
        (λ n → cong (λ b → ψ t T′ l′ (G₀ b))
           (trans (out-inS (≪S (κ p)) _)
             (chain≡ (λ z → cong (λ b → ψ j (inj₁ (≪⊲ (κ p))) l′ (G₀ b)) (out-inS (≪S (κ p)) z)) n))))
     (ψQ _ _ T′ l′ T′ l′ (cq (ict I) pz))
     (λ n → ψQ _ _ T′ l′ T′ l′ (cq (ict I) (cq C₁ (γ≈ n))))
     (ψQ _ _ T l T′ l′ (cq (ict I) e₀))
     (λ m → RS ac′ ρ IUU (proj₁ (CP m)) (proj₁ (proj₂ (CP m))) _ (proj₂ (proj₂ (CP m))) τ T′ l′ T′ l′)
  where
  G₀ = λ a → H (H₁ a)
  ρ = ⊲-tr (≪⊲ r′) kp
  IUU = IU ac ac′ kp I c r′ u H₁ e₀ C₁ ds
  P = ≪⊲ (κ p)
  γ = chainᵒ (λ z → ψ j (inj₁ P) l′ (G₀ z))
  G = λ n → ψ t T′ l′ (G₀ (γ n))
  γ≈ : ∀ n → γ n ≈ γ n
  γ≈ zero = Ω≈ j
  γ≈ (suc n) = ψQ _ _ (inj₁ P) l′ (inj₁ P) l′ (cq (ict I) (cq C₁ (γ≈ n)))
  CP = ChnP ac′ ρ IUU P l′ Y (inv≈ v (cq (ict I) e₀) (cq (ict I) (cq C₁ (Ω≈ j))))
```
