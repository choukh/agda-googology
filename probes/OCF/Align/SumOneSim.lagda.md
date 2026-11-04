# 和形式过 $\Omega_{\Omega+1}$ (五): 没有 `nκ` 的片段上的差

> 不含记号. 入口 [SumOne](SumOne.lagda.md). 同 [TLRuleSim](TLRuleSim.lagda.md), 加上世界. 状态换世界时不变量不变 (`cv-Inv`). 对被积函数和世界参数化.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumOneSim where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.CumReadCF hiding (_⊕_; rkT; keep; rise; Rk)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadCFEq
open import OCF.Align.CumReadCFThm using (_⊴_; ψL; z⊴)
open import OCF.Align.TLRuleRel using (ContF; cq; cl; cn; cm; comp; ContF-κ; ≈-rp; ≈-ol; ψ-keep; ψ-rise; chain≡; ψ-ContF)
import OCF.Align.SumOneTree as N
open N using (D; Dl; Ly; cnt; top; K; V; inV; outV; Zy; LW; LW↑; kk; n0; n1; _⨾_; nl; ni; nw; Int; AccL; accL)
open import OCF.Align.SumOneClosed hiding (keep; rise)
import OCF.Align.SumOneClosed as F
open import OCF.Align.SumOneRel
open import OCF.Align.TLRuleSum using (≪≪)
```

## §1 状态

```agda
Diff : ∀ {M W} → Df W → O M → O M → Set
Diff {M} {W} Δ b y = ∀ {t} (τ : Tg t W) (lt : Lg t) (T : Tg t M) (l : Lg M) (T′ : Tg t M) (l′ : Lg M) → Rel t (ψ t T l b) (yc Δ τ lt) (ψ t T′ l′ y)

record Inv {M W : A} (Y : St W) (b : O M) : Set where
  constructor mkI
  field
    un : ∀ {t} (τ : Tg t W) (lt : Lg t) (T : Tg t M) (l : Lg M) → Rel t (Ω̇ t) (yc (d Y) τ lt) (ψ t T l b)
open Inv public

inv+ : ∀ {M W} {Y : St W} {Δ : Df W} {b y : O M} → Inv Y b → Diff Δ b y → Inv (Y ⊕ Δ) y
inv+ v δ = mkI (λ τ lt T l → rc (un v τ lt T l) (δ τ lt T l T l))

inv≈ : ∀ {M W} {Y : St W} {b b′ : O M} → Inv Y b → b ≈ b′ → b′ ≈ b′ → Inv Y b′
inv≈ {b = b} {b′} v e p = mkI (λ τ lt T l → rr (un v τ lt T l) (ψQ b b′ T l T l e) (ψQ b′ b′ T l T l p))

cv-Inv : ∀ {M W W′} {Y : St W} {b : O M} (q : W ⊲ W′) (lW′ : Lg W′) → Inv Y b → Inv (cv q lW′ Y) b
cv-Inv {Y = Y} {b} q lW′ v = mkI go
  where
  go : ∀ {t} (τ : Tg t _) (lt : Lg t) (T : Tg t _) (l : Lg _) → Rel t (Ω̇ t) (yc (d (cv q lW′ Y)) τ lt) (ψ t T l b)
  go (inj₁ τ₁) lt T l with cmpF q τ₁ lW′
  ... | inj₁ t⊲W = rw (un v (inj₁ t⊲W) lt T l)
  ... | inj₂ W⊲t = rw (un v (inj₂ W⊲t) lt T l)
  go (inj₂ τ₂) lt T l = un v (inj₂ (⊲-tr q τ₂)) lt T l

record Itg {ly : Ly} {M₀ M W : A} (κ : ∀ {j} → j ≪ M₀ → j ≪ M) (A₀ : Ig ly W) (H : O M₀ → O M) (Cw : ∀ {W′} → Dl ly W′ → O M₀ → Set) : Set where
  field
    ict : ContF κ H
    i1  : ∀ {W′} (p : W ⊲ W′) (lW′ : Lg W′) w z₀ z₁ (Y : St W′) → Cw w z₀ → z₁ ≈ os z₀ → z₁ ≈ z₁ → Inv Y (H z₀) → Diff (A₀ p lW′ w Y) (H z₀) (H z₁)
    icw : ∀ {W′ w z₀ δ z₁} → Cw {W′} w z₀ → Rl ly M₀ {W′} z₀ δ z₁ → Cw (w ⨾ δ) z₁
    icn : ∀ {W₁ W′ w z} (q : W₁ ⊲ W′) → Cw {W₁} w z → Cw {W′} (nw q w) z
    icr : ∀ {W′ w z z′} → Cw {W′} w z → z ≈ z′ → z′ ≈ z′ → Cw w z′
open Itg public

Itg↾ : ∀ {ly M₀ M W W′} {κ : ∀ {j} → j ≪ M₀ → j ≪ M} {A₀ : Ig ly W} {H : O M₀ → O M} {Cw : ∀ {W′} → Dl ly W′ → O M₀ → Set} (p : W ⊲ W′) → Itg κ A₀ H Cw → Itg κ (Ig↾ p A₀) H Cw
Itg↾ p I = record { ict = ict I ; i1 = λ p′ → i1 I (⊲-tr p p′) ; icw = icw I ; icn = icn I ; icr = icr I }
```

## §2 主定理

```agda
S-irr : ∀ {a} → AccL a → Strict a a → ⊥
S-irr (N.acc f) R = S-irr (f R) R
```

```agda
RS : ∀ {ly M₀ M W₀ W} {κ : ∀ {j} → j ≪ M₀ → j ≪ M} {A₀ : Ig ly W} {H : O M₀ → O M} {Cw : ∀ {W′} → Dl ly W′ → O M₀ → Set}
     (ac : AccY ly) (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : LW ly W) → Itg κ A₀ H Cw → ∀ {w z₀ δ z₁} → Cw w z₀ → Rl ly M₀ {W₀} z₀ δ z₁ →
     ∀ (Y : St W) → Inv Y (H z₀) → Diff (Run ac δ q₀ lW ll A₀ w Y) (H z₀) (H z₁)

RptP : ∀ {ly M₀ M W₀ W} {κ : ∀ {j} → j ≪ M₀ → j ≪ M} {A₀ : Ig ly W} {H : O M₀ → O M} {Cw : ∀ {W′} → Dl ly W′ → O M₀ → Set}
       (ac : AccY ly) (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : LW ly W) → Itg κ A₀ H Cw → ∀ {w z₀} {d′ : ℕ → Dl ly W₀} (g : ℕ → O M₀) → Cw w z₀ → z₀ ≈ g 0 → (∀ n → g n ≈ g n) →
       (∀ m → Rl ly M₀ (g m) (d′ m) (g (suc m))) → ∀ (Y : St W) → Inv Y (H z₀) → ∀ m →
       Cw (proj₁ (Rpt ac d′ q₀ lW ll A₀ w Y m)) (g m) × Inv (proj₂ (Rpt ac d′ q₀ lW ll A₀ w Y m)) (H (g m))

IU : ∀ {ly j M₀ M W₀ W} {κ : ∀ {i} → i ≪ M₀ → i ≪ M} {A₀ : Ig ly W} {H : O M₀ → O M} {Cw : ∀ {W′} → Dl ly W′ → O M₀ → Set}
     (ac : AccY ly) (kW : j ⊲ W) (q₀ : W₀ ⊲ W) (ll : LW ly W) → Itg κ A₀ H Cw → ∀ {w z₀} → Cw w z₀ →
     (r : K ly W₀ j) (u : ∀ {W′} → W₀ ⊲ W′ → Lg W′ → V ly r W′ → Dl ly W′) {κ₁ : ∀ {i} → i ≪ j → i ≪ M₀} (H₁ : O j → O M₀) →
     z₀ ≈ H₁ (Ω̇ j) → ContF κ₁ H₁ →
     (∀ {W′} (q : W₀ ⊲ W′) (lW′ : Lg W′) (w₁ : D j W′) z₀′ z₁′ → Lwy ly r (Ω̇ j) w₁ z₀′ → z₁′ ≈ os z₀′ → z₁′ ≈ z₁′ → Rl ly M₀ (H₁ z₀′) (u q lW′ (inV ly r w₁)) (H₁ z₁′)) →
     Itg (λ s₁ → κ (κ₁ s₁)) (Ai ac r u q₀ kW ll A₀ w) (λ z → H (H₁ z)) (Rel j (Ω̇ j))

RK : ∀ {ly j M₀ M W₀ W t} {κ : ∀ {i} → i ≪ M₀ → i ≪ M} {A₀ : Ig ly W} {H : O M₀ → O M} {Cw : ∀ {W′} → Dl ly W′ → O M₀ → Set}
     (ac : AccY ly) (ac′ : AccY (cnt j)) (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : LW ly W) → (I : Itg κ A₀ H Cw) → ∀ {w z₀ z₁} → Cw w z₀ →
     (r : K ly W₀ j) (u : ∀ {W′} → W₀ ⊲ W′ → Lg W′ → V ly r W′ → Dl ly W′) (p : j ≪ M₀) (H₁ : O j → O M₀) →
     z₁ ≈ oi p (λ z → H₁ (outS (≪S p) z)) → z₁ ≈ z₁ → z₀ ≈ H₁ (Ω̇ j) → ContF (λ s₁ → ≪≪ s₁ p) H₁ →
     (∀ {W′} (q : W₀ ⊲ W′) (lW′ : Lg W′) (w₁ : D j W′) z₀′ z₁′ → Lwy ly r (Ω̇ j) w₁ z₀′ → z₁′ ≈ os z₀′ → z₁′ ≈ z₁′ → Rl ly M₀ (H₁ z₀′) (u q lW′ (inV ly r w₁)) (H₁ z₁′)) →
     ∀ (Y : St W) → Inv Y (H z₀) → (τ : Tg t W) (lt : Lg t) (T : Tg t M) (l : Lg M) (T′ : Tg t M) (l′ : Lg M) (rk : Rk′ j t) →
     Rel t (ψ t T l (H z₀)) (RKi ac ac′ r u q₀ lW ll A₀ w Y τ lt rk) (ψ t T′ l′ (H z₁))

ChnP : ∀ {j M W} {κ : ∀ {i} → i ≪ j → i ≪ M} {A₀ : Ig (cnt j) W} {G₀ : O j → O M}
       (ac′ : AccY (cnt j)) (ρ : j ⊲ W) (lW : Lg W) (lj : Lg j) → Itg κ A₀ G₀ (Rel j (Ω̇ j)) → ∀ (P : j ⊲ M) (l′ : Lg M) (Y : St W) → Inv Y (G₀ (Ω̇ j)) → ∀ n →
       let γ = chainᵒ (λ z → ψ j (inj₁ P) l′ (G₀ z)) in
       Rel j (Ω̇ j) (proj₁ (Chn ac′ ρ lW lj A₀ Y n)) (γ n) ×
       (Rel j (γ n) (proj₁ (proj₂ (Chn ac′ ρ lW lj A₀ Y n))) (γ (suc n)) × Inv (proj₂ (proj₂ (Chn ac′ ρ lW lj A₀ Y n))) (G₀ (γ n)))

RS ac q₀ lW ll I c (rz e p) Y v τ lt T l T′ l′ = rz (ψQ _ _ T l T′ l′ (cq (ict I) e)) (ψQ _ _ T′ l′ T′ l′ (cq (ict I) p))
RS ac q₀ lW ll I c (rs e p) Y v τ lt T l T′ l′ = i1 I C.self lW _ _ _ Y c e p v τ lt T l T′ l′
RS ac q₀ lW ll I c (rc D₁ D₂) Y v τ lt T l T′ l′ =
  rc (RS ac q₀ lW ll I c D₁ Y v τ lt T l T′ l′)
     (RS ac q₀ lW ll I (icw I c (rw {p = q₀} D₁)) D₂ _ (inv+ v (RS ac q₀ lW ll I c D₁ Y v)) τ lt T′ l′ T′ l′)
RS ac q₀ lW ll I c (rb e p D) Y v τ lt T l T′ l′ =
  rb (ψQ _ _ T l T l (cq (ict I) e)) (ψQ _ _ T l T l (cq (ict I) p)) (RS ac q₀ lW ll I (icr I c e p) D Y (inv≈ v (cq (ict I) e) (cq (ict I) p)) τ lt T l T′ l′)
RS ac q₀ lW ll I c (rr D e p) Y v τ lt T l T′ l′ =
  rr (RS ac q₀ lW ll I c D Y v τ lt T l T′ l′) (ψQ _ _ T′ l′ T′ l′ (cq (ict I) e)) (ψQ _ _ T′ l′ T′ l′ (cq (ict I) p))
RS ac q₀ lW ll I c (rw {p = p′} D) Y v τ lt T l T′ l′ = RS ac (⊲-tr p′ q₀) lW ll I c D Y v τ lt T l T′ l′
RS {H = H} ac q₀ lW ll I c (rl g e p q e₀ st′) Y v {t} τ lt T l T′ l′ =
  rl (λ n → ψ t T′ l′ (H (g n)))
     (ψQ _ _ T′ l′ T′ l′ (cl (ict I) g e))
     (ψQ _ _ T′ l′ T′ l′ (cq (ict I) p))
     (λ n → ψQ _ _ T′ l′ T′ l′ (cq (ict I) (q n)))
     (ψQ _ _ T l T′ l′ (cq (ict I) e₀))
     (λ m → RS ac q₀ lW ll I (proj₁ (RptP ac q₀ lW ll I g c e₀ q st′ Y v m)) (st′ m) _ (proj₂ (RptP ac q₀ lW ll I g c e₀ q st′ Y v m)) τ lt T′ l′ T′ l′)
RS {H = H} ac q₀ lW ll I c (rd g e p q f D) Y v {t} τ lt T l T′ l′ =
  rd (λ n → ψ t T′ l′ (H (g n)))
     (ψQ _ _ T′ l′ T′ l′ (cl (ict I) g e))
     (ψQ _ _ T′ l′ T′ l′ (cq (ict I) p))
     (λ n → ψQ _ _ T′ l′ T′ l′ (cq (ict I) (q n)))
     (ψL T′ l′ T′ l′ (cm (ict I) f))
     (rr (RS ac q₀ lW ll I c D Y v τ lt T l T′ l′) (ψQ _ _ T′ l′ T′ l′ (cl (ict I) (λ m → g (suc m)) (λ n → q (suc n)))) (λ n → ψQ _ _ T′ l′ T′ l′ (cq (ict I) (q (suc n)))))
RS {ly} (acc f) q₀ lW ll I c (ri r u p H₁ e pz e₀ C₁ ds) Y v τ lt T l T′ l′ =
  RK (acc f) (f r) q₀ lW ll I c r u p H₁ e pz e₀ C₁ ds Y v τ lt T l T′ l′ (F.rkT (kk ly r q₀ ll) τ lW)

RptP ac q₀ lW ll I g c e₀ q st′ Y v zero = icr I c e₀ (q 0) , inv≈ v (cq (ict I) e₀) (cq (ict I) (q 0))
RptP ac q₀ lW ll I g c e₀ q st′ Y v (suc m) =
  icw I (proj₁ (RptP ac q₀ lW ll I g c e₀ q st′ Y v m)) (rw {p = q₀} (st′ m)) ,
  inv+ (proj₂ (RptP ac q₀ lW ll I g c e₀ q st′ Y v m)) (RS ac q₀ lW ll I (proj₁ (RptP ac q₀ lW ll I g c e₀ q st′ Y v m)) (st′ m) _ (proj₂ (RptP ac q₀ lW ll I g c e₀ q st′ Y v m)))

IU {ly} {j} {κ = κ} {H = H} ac kW q₀ ll I {w} {z₀} c r u H₁ e₀ C₁ ds = record
  { ict = comp C₁ (ict I)
  ; i1 = λ {W′} p lW′ w₂ a₀ a₁ Y′ c₂ d pz v′ →
      RS ac C.self lW′ (LW↑ ly p ll) (Itg↾ p I)
         (icw I (icn I p c)
            (rb e₀ (cq C₁ (Ω≈ j)) (IntRel (accL j) C.self lW′ (⊲-tr kW p) (zyOf ly r) (mkOf ly r)
               (λ p′ l′ z′ → u (⊲-tr (⊲-tr q₀ p) p′) l′ (inV ly r z′)) C₁
               (λ q′ l′ w₁ z₀′ z₁′ c₁ d₁ p₁ → ds (⊲-tr (⊲-tr q₀ p) q′) l′ w₁ z₀′ z₁′ (→Lw ly r c₁) d₁ p₁) (rz (Ω≈ j) (Ω≈ j)) c₂)))
         (ds (⊲-tr q₀ p) lW′ w₂ a₀ a₁ (→Lw ly r c₂) d pz) Y′ v′
  ; icw = λ c₁ D → rc c₁ D
  ; icn = λ q c₁ → rw c₁
  ; icr = λ c₁ e p → rr c₁ e p
  }
```

```agda
ChnP {j} ac′ ρ lW lj I P l′ Y v zero =
  rz (Ω≈ j) (Ω≈ j) , (un v (inj₁ ρ) lj (inj₁ P) l′ , v)
ChnP {j} ac′ ρ lW lj I P l′ Y v (suc n) =
  rc (proj₁ ih) (proj₁ (proj₂ ih)) ,
  (RS ac′ C.self lW ρ I (proj₁ ih) (proj₁ (proj₂ ih)) _ (proj₂ (proj₂ ih)) (inj₁ ρ) lj (inj₁ P) l′ (inj₁ P) l′ ,
   inv+ (proj₂ (proj₂ ih)) (RS ac′ C.self lW ρ I (proj₁ ih) (proj₁ (proj₂ ih)) _ (proj₂ (proj₂ ih))))
  where ih = ChnP ac′ ρ lW lj I P l′ Y v n
```

### 节点

```agda
RK {ly} {j} {M₀} {M} {t = t} {κ} {A₀} {H} ac ac′ q₀ lW ll I {w} {z₀} {z₁} c r u p H₁ e pz e₀ C₁ ds Y v τ lt T l T′ l′ rk with C.rkT (κ p) T′ l′ in eq | rk
... | C.keep s | F.rise q = ⊥-elim (no-keep-rise s q)
... | C.rise q | F.keep R = ⊥-elim (S-irr (N.accL j) (N.Sk R q))
... | C.keep s | F.keep R =
  ri R _ s H₂
     (≈-rp _ {r = s}
        (subst (λ v₀ → ψ t T′ l′ (H z₁) ≈ v₀) (ψ-keep T′ l′ (κ p) G₀ s eq) (ψQ _ _ T′ l′ T′ l′ (cn (ict I) p H₁ e (cq C₁))))
        (λ a → cong (λ b → ψ t T′ l′ (G₀ b)) (trans (out-inS (≪S (κ p)) _) (out-inS (≪S s) a))))
     (ψQ _ _ T′ l′ T′ l′ (cq (ict I) pz))
     (ψQ _ _ T l T′ l′ (cq (ict I) e₀))
     (ContF-κ (ψ-ContF T′ l′ s (comp C₁ (ict I))))
     (λ {W′} q lW′ w₂ a₀ a₁ h d p₂ → subst
        (λ z → Rel t (H₂ a₀)
           (yc (BNi ac ac′ r u q₀ ll A₀ w Y kW (⊲-tr (W⊲wm τ) q) lW′ z) (inj₁ (⊲-tr (t⊲wm τ) q)) lt) (H₂ a₁))
        (sym (N.out-inS R w₂))
        (i1 IUU (⊲-tr (W⊲wm τ) q) lW′ w₂ a₀ a₁ _ (Rw→ R h) d p₂
           (inv+ (cv-Inv (⊲-tr (W⊲wm τ) q) lW′ v₀′)
              (RS ac′ C.self lW′ (⊲-tr kW (⊲-tr (W⊲wm τ) q)) (Itg↾ (⊲-tr (W⊲wm τ) q) IUU) (rz (Ω≈ j) (Ω≈ j)) (Rw→ R h) _ (cv-Inv (⊲-tr (W⊲wm τ) q) lW′ v₀′)))
           (inj₁ (⊲-tr (t⊲wm τ) q)) lt T′ l′ T′ l′))
  where
  G₀ = λ a → H (H₁ a)
  H₂ = λ a → ψ t T′ l′ (H (H₁ a))
  kW = kk ly r q₀ ll
  IUU = IU ac kW q₀ ll I c r u H₁ e₀ C₁ ds
  v₀′ = inv≈ v (cq (ict I) e₀) (cq (ict I) (cq C₁ (Ω≈ j)))
... | C.rise q | F.rise q′ =
  rl Gt
     (≈-ol _ (subst (λ v₀ → ψ t T′ l′ (H z₁) ≈ v₀) (ψ-rise T′ l′ (κ p) G₀ q eq) (ψQ _ _ T′ l′ T′ l′ (cn (ict I) p H₁ e (cq C₁))))
        (λ n → cong (λ b → ψ t T′ l′ (G₀ b))
           (trans (out-inS (≪S (κ p)) _)
             (chain≡ (λ z → cong (λ b → ψ j (inj₁ (≪⊲ (κ p))) l′ (G₀ b)) (out-inS (≪S (κ p)) z)) n))))
     (ψQ _ _ T′ l′ T′ l′ (cq (ict I) pz))
     (λ n → ψQ _ _ T′ l′ T′ l′ (cq (ict I) (cq C₁ (γ≈ n))))
     (ψQ _ _ T l T′ l′ (cq (ict I) e₀))
     (λ m → RS ac′ C.self lW kW IUU (proj₁ (CP m)) (proj₁ (proj₂ (CP m))) _ (proj₂ (proj₂ (CP m))) τ lt T′ l′ T′ l′)
  where
  G₀ = λ a → H (H₁ a)
  kW = kk ly r q₀ ll
  IUU = IU ac kW q₀ ll I c r u H₁ e₀ C₁ ds
  P = ≪⊲ (κ p)
  γ = chainᵒ (λ z → ψ j (inj₁ P) l′ (G₀ z))
  Gt = λ n → ψ t T′ l′ (G₀ (γ n))
  γ≈ : ∀ n → γ n ≈ γ n
  γ≈ zero = Ω≈ j
  γ≈ (suc n) = ψQ _ _ (inj₁ P) l′ (inj₁ P) l′ (cq (ict I) (cq C₁ (γ≈ n)))
  CP = ChnP ac′ kW lW (lg⊲ kW lW) IUU P l′ Y (inv≈ v (cq (ict I) e₀) (cq (ict I) (cq C₁ (Ω≈ j))))
```
