# 和形式过 $\Omega_{\Omega+1}$ (四): 与旧树的对应, 没有 `nκ` 的片段

> 不含记号. 入口 [SumOne](SumOne.lagda.md). 同 [TLRuleRel](TLRuleRel.lagda.md): `Rel L b x y`: 旧树从 $b$ 走 $x$ 到 $y$. 分支上量世界. **这里没有 `nκ` 的规则:** 只用来验 $\psi_0(\Omega_\Omega)$ 这一站. 带 `nκ` 的项上没有对应, 见 [SumOne](SumOne.lagda.md) 的第一个障碍.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumOneRel where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.CumReadCF
open import OCF.Align.CumReadCFEq
open import OCF.Align.CumReadCFThm using (_⊴_; rf; s; l; nd; eR; eL; add-mono; Ω⊴)
open import OCF.Align.TLRuleRel using (ContF; cq; cl; cn; cm; comp; ContF-κ; ≈-rp; ≈-rp′; ≈-ol; ≈-ol′; ≈-os′; add-ContF; emb; emb≈; emb≈ˡ; emb≈ʳ; emb⊴ˡ; emb⊴ʳ; idH; idH≈ˡ; idH≈ʳ; idH-ContF)
open import OCF.Align.TLRuleSum using (≪≪)
import OCF.Align.SumOneTree as N
open N using (D; Dl; Ly; cnt; top; K; V; inV; outV; Ws; Zy; D₊; n0; n1; _⨾_; nl; ni; nw; Int; IW; Pre; AccL; acc; accL; Sk; NZ-S; tailP; Dif; Ωd; ⊲S)
```

## §1 关系

```agda
module _ (ly : Ly) (M : A) (Lw : ∀ {W k} → K ly W k → ∀ {W′} → O k → D k W′ → O k → Set) where
  data Rel₊ : ∀ {W} → O M → Dl ly W → O M → Set where
    rz : ∀ {W b y} → b ≈ y → y ≈ y → Rel₊ {W} b n0 y
    rs : ∀ {W b y} → y ≈ os b → y ≈ y → Rel₊ {W} b n1 y
    rc : ∀ {W b c y x x′} → Rel₊ {W} b x c → Rel₊ c x′ y → Rel₊ b (x ⨾ x′) y
    rb : ∀ {W b b′ x y} → b′ ≈ b → b ≈ b → Rel₊ {W} b x y → Rel₊ b′ x y
    rr : ∀ {W b x y y′} → Rel₊ {W} b x y → y ≈ y′ → y′ ≈ y′ → Rel₊ b x y′
    rw : ∀ {W₀ W b x y} {p : W₀ ⊲ W} → Rel₊ {W₀} b x y → Rel₊ {W} b (nw p x) y
    rl : ∀ {W b y} {d : ℕ → Dl ly W} (g : ℕ → O M) → y ≈ ol g → y ≈ y → (∀ n → g n ≈ g n) → b ≈ g 0 →
         (∀ m → Rel₊ (g m) (d m) (g (suc m))) → Rel₊ b (nl d) y
    rd : ∀ {W b y} {d : ℕ → Dl ly W} (g : ℕ → O M) → y ≈ ol g → y ≈ y → (∀ n → g n ≈ g n) → g 0 ⊴ g 1 →
         Rel₊ b (nl d) (ol (λ m → g (suc m))) → Rel₊ b (nl d) y
    ri : ∀ {W b y k} (r : K ly W k) (u : ∀ {W′} → W ⊲ W′ → Lg W′ → V ly r W′ → Dl ly W′) (p : k ≪ M) (H : O k → O M) →
         y ≈ oi p (λ z → H (outS (≪S p) z)) → y ≈ y →
         b ≈ H (Ω̇ k) →
         ContF (λ s₁ → ≪≪ s₁ p) H →
         (∀ {W′} (q : W ⊲ W′) (lW′ : Lg W′) (w : D k W′) z₀ z₁ → Lw r (Ω̇ k) w z₀ → z₁ ≈ os z₀ → z₁ ≈ z₁ → Rel₊ (H z₀) (u q lW′ (inV ly r w)) (H z₁)) →
         Rel₊ b (ni r u) y

Rel : ∀ L {W} → O L → D L W → O L → Set
Rw  : ∀ L {a} → Strict a L → ∀ {W′} → O a → D a W′ → O a → Set
Rc  : ∀ b {a} → a ⊲ b → ∀ {W′} → O a → D a W′ → O a → Set
Rel L = Rel₊ (cnt L) L (λ {_} {_} R → Rw L R)
Rw (asuc b) (ss P) = Rc b P
Rw (alim f) (sl n P) = Rc (f n) P
Rc a self = Rel a
Rc (asuc b) (suc P) = Rc b P
Rc (alim f) (lim n P) = Rc (f n) P

Rc→ : ∀ {b a} (P : a ⊲ b) {W′ x} {y : D a W′} {z} → Rc b P x y z → Rel a x y z
Rc→ self d = d
Rc→ (suc P) d = Rc→ P d
Rc→ (lim n P) d = Rc→ P d

→Rc : ∀ {b a} (P : a ⊲ b) {W′ x} {y : D a W′} {z} → Rel a x y z → Rc b P x y z
→Rc self d = d
→Rc (suc P) d = →Rc P d
→Rc (lim n P) d = →Rc P d

Rw→ : ∀ {L a} (R : Strict a L) {W′ x} {y : D a W′} {z} → Rw L R x y z → Rel a x y z
Rw→ (ss P) d = Rc→ P d
Rw→ (sl n P) d = Rc→ P d

→Rw : ∀ {L a} (R : Strict a L) {W′ x} {y : D a W′} {z} → Rel a x y z → Rw L R x y z
→Rw (ss P) d = →Rc P d
→Rw (sl n P) d = →Rc P d

-- 顶层的项: 旧树在世界 M
Lwy : ∀ ly {W k} → K ly W k → ∀ {W′} → O k → D k W′ → O k → Set
Lwy (cnt L) R = Rw L R
Lwy top {k = k} _ = Rel k

Rl : ∀ ly M {W} → O M → Dl ly W → O M → Set
Rl ly M = Rel₊ ly M (Lwy ly)

Lw→ : ∀ ly {W k} (r : K ly W k) {W′ x} {y : D k W′} {z} → Lwy ly r x y z → Rel k x y z
Lw→ (cnt L) R d = Rw→ R d
Lw→ top r d = d

→Lw : ∀ ly {W k} (r : K ly W k) {W′ x} {y : D k W′} {z} → Rel k x y z → Lwy ly r x y z
→Lw (cnt L) R d = →Rw R d
→Lw top r d = d

relR : ∀ {ly M W b x y} → Rl ly M {W} b x y → y ≈ y
relR (rz _ p) = p
relR (rs _ p) = p
relR (rc _ D) = relR D
relR (rb _ _ D) = relR D
relR (rr _ _ p) = p
relR (rw D) = relR D
relR (rl _ _ p _ _ _) = p
relR (rd _ _ p _ _ _) = p
relR (ri _ _ _ _ _ p _ _ _) = p
```

## §2 加法

```agda
add-Rel : ∀ {L W} (B : O L) → B ≈ B → ∀ {b x y} → Rel L {W} b x y → Rel L (B ⊕ b) x (B ⊕ y)
add-Rel B e {b} {y = y} (rz d p) = rz (add≈ self self e b y d) (add≈ self self e y y p)
add-Rel B e {b} {y = y} (rs d p) = rs (add≈ self self e y (os b) d) (add≈ self self e y y p)
add-Rel B e (rc D₁ D₂) = rc (add-Rel B e D₁) (add-Rel B e D₂)
add-Rel B e {b} (rb {b = b₁} d p D) = rb (add≈ self self e b b₁ d) (add≈ self self e b₁ b₁ p) (add-Rel B e D)
add-Rel B e {y = y′} (rr {y = y} D d p) = rr (add-Rel B e D) (add≈ self self e y y′ d) (add≈ self self e y′ y′ p)
add-Rel B e (rw D) = rw (add-Rel B e D)
add-Rel B e {b} {y = y} (rl g d p q e₀ st) =
  rl (λ n → B ⊕ g n) (add≈ self self e y (ol g) d) (add≈ self self e y y p) (λ n → add≈ self self e (g n) (g n) (q n))
     (add≈ self self e b (g 0) e₀) (λ m → add-Rel B e (st m))
add-Rel B e {y = y} (rd g d p q f D) =
  rd (λ n → B ⊕ g n) (add≈ self self e y (ol g) d) (add≈ self self e y y p) (λ n → add≈ self self e (g n) (g n) (q n))
     (add-mono self self e f) (add-Rel B e D)
add-Rel B e {b} {y = y} (ri {k = k} r u p₀ H d p e₀ C ds) =
  ri r u p₀ (λ z → B ⊕ H z)
     (≈-rp (B ⊕ y) {r = p₀} (add≈ self self e y (oi p₀ (λ z → H (outS (≪S p₀) z))) d)
        (λ a → cong (λ v → B ⊕ H v) (trans (out-inS (≪S p₀) _) (out-inS (≪S p₀) a))))
     (add≈ self self e y y p)
     (add≈ self self e b (H (Ω̇ k)) e₀)
     (add-ContF B e C)
     (λ q lW′ w z₀ z₁ c d′ p′ → add-Rel B e (ds q lW′ w z₀ z₁ c d′ p′))
```

## §3 $\Omega$

```agda
drpn : ∀ {L W b} {d : ℕ → D L W} (n : ℕ) (G : ℕ → O L) {y : O L} → y ≈ ol G → y ≈ y → (∀ i → G i ≈ G i) → (∀ i → G i ⊴ G (suc i)) → b ≈ G n →
       (∀ m → Rel L (G (m + n)) (d m) (G (suc (m + n)))) → Rel L b (nl d) y
drpn {L} {d = d} zero G e p q h e₀ st = rl G e p q e₀ (λ m → subst (λ i → Rel L (G i) (d m) (G (suc i))) (+-identityʳ m) (st m))
drpn {L} {d = d} (suc n) G e p q h e₀ st =
  rd G e p q (h 0) (drpn n (λ i → G (suc i)) (λ i → q (suc i)) (λ i → q (suc i)) (λ i → q (suc i)) (λ i → h (suc i)) e₀
    (λ m → subst (λ i → Rel L (G i) (d m) (G (suc i))) (+-suc m n) (st m)))

seg-Rel : ∀ {c L W} (q : asuc c ⊲ L) → Rel L {W} (emb (⊲-tr (suc self) q) (Ω̇ c)) (ni (⊲S q) (λ _ _ _ → n1)) (emb q (Ω̇ (asuc c)))
seg-Rel {c} q =
  ri (⊲S q) (λ _ _ _ → n1) r′ (idH r′)
     (emb≈ˡ q (≈-rp′ (Ω̇ (asuc c)) {r = zero} {r″ = r′} (Ω≈ (asuc c))
        (λ x₀ z d → idH≈ʳ r′ (oe≈ x₀ (ss self) z d))))
     (emb≈ q q (Ω≈ (asuc c)))
     (emb≈ˡ (⊲-tr (suc self) q) (idH≈ʳ r′ (Ω≈ c)))
     (idH-ContF r′)
     (λ _ _ w₁ z₀ z₁ h d p → rs (idH≈ˡ r′ (≈-os′ z₁ d (λ x₀ e → idH≈ʳ r′ e))) (idH≈ˡ r′ (idH≈ʳ r′ p)))
  where
  r′ = ≪∘ zero q

Dif-Rel : ∀ b {a L W} (p : a ⊲ b) (q : b ⊲ L) (w : Lg b) → Rel L {W} (emb (⊲-tr p q) (Ω̇ a)) (Dif b p q w) (emb q (Ω̇ b))
Dif-Rel b self q w = rz (emb≈ (⊲-tr self q) q (Ω≈ b)) (emb≈ q q (Ω≈ b))
Dif-Rel (asuc c) {a} {L} (suc p) q w =
  rc (rb (emb≈ (⊲-tr (suc p) q) (⊲-tr p (⊲-tr (suc self) q)) (Ω≈ a)) (emb≈ (⊲-tr p (⊲-tr (suc self) q)) (⊲-tr p (⊲-tr (suc self) q)) (Ω≈ a)) (Dif-Rel c p (⊲-tr (suc self) q) w))
     (seg-Rel q)
Dif-Rel (alim f) {a} {L} (lim n p) q (st , w) =
  rc (rb (emb≈ (⊲-tr (lim n p) q) (⊲-tr p (qq n)) (Ω≈ a)) (emb≈ (⊲-tr p (qq n)) (⊲-tr p (qq n)) (Ω≈ a)) (Dif-Rel (f n) p (qq n) (w n)))
     (drpn n G (emb≈ˡ q (λ m → emb≈ʳ (qq m) (Ω≈ (f m)))) (emb≈ q q (Ω≈ (alim f))) (λ i → emb≈ (qq i) (qq i) (Ω≈ (f i)))
        (λ i → emb⊴ˡ (qq i) (emb⊴ʳ (qq (suc i)) (Ω⊴ (st i)))) (emb≈ (qq n) (qq n) (Ω≈ (f n)))
        (λ m → rb (emb≈ (qq (m + n)) (⊲-tr (st (m + n)) (qq (suc (m + n)))) (Ω≈ (f (m + n)))) (emb≈ (⊲-tr (st (m + n)) (qq (suc (m + n)))) (⊲-tr (st (m + n)) (qq (suc (m + n)))) (Ω≈ (f (m + n))))
                  (Dif-Rel (f (suc (m + n))) (st (m + n)) (qq (suc (m + n))) (w (suc (m + n))))))
  where
  qq : ∀ m → f m ⊲ L
  qq m = ⊲-tr (lim m self) q
  G : ℕ → O L
  G m = emb (qq m) (Ω̇ (f m))

Ω-Rel : ∀ a {L W} (q : a ⊲ L) (w : Lg a) → Rel L {W} o0 (Ωd a q w) (emb q (Ω̇ a))
Ω-Rel a q w = rc (rs (emb≈ˡ (⊲-tr (z⊲ a) q) tt) (emb≈ (⊲-tr (z⊲ a) q) (⊲-tr (z⊲ a) q) tt)) (Dif-Rel a (z⊲ a) q w)
```

## §4 积分

```agda
Pre-Rel : ∀ {k W₀ W} {q₀ : W₀ ⊲ W} {d : ℕ → D k W₀} {z₀} (g : ℕ → O k) → z₀ ≈ g 0 → (∀ n → g n ≈ g n) → (∀ m → Rel k (g m) (d m) (g (suc m))) → ∀ n → Rel k z₀ (Pre q₀ d n) (g n)
Pre-Rel g e p st zero = rz e (p 0)
Pre-Rel g e p st (suc n) = rc (Pre-Rel g e p st n) (rw (st n))

out-inV : ∀ ly {W₀ k W′} (r : K ly W₀ k) (z : D k W′) → outV ly r (inV ly r z) ≡ z
out-inV (cnt L) R z = N.out-inS R z
out-inV top r z = refl

IntRel : ∀ {ly M k W₀ W} (ac : AccL k) {κ : ∀ {i} → i ≪ k → i ≪ M} {H : O k → O M}
         (q₀ : W₀ ⊲ W) (lW : Lg W) (kW : k ⊲ W) (zy : Zy ly) (mk : ∀ {W₁ j} → k ⊲ W₁ → Strict j k → K ly W₁ j) (u : ∀ {W′} → W ⊲ W′ → Lg W′ → D k W′ → Dl ly W′) →
         ContF κ H →
         (∀ {W′} (q : W ⊲ W′) (lW′ : Lg W′) w z₀ z₁ → Rel k (Ω̇ k) w z₀ → z₁ ≈ os z₀ → z₁ ≈ z₁ → Rl ly M (H z₀) (u q lW′ w) (H z₁)) →
         ∀ {w z₀ δ z₁} → Rel k (Ω̇ k) w z₀ → Rel k {W₀} z₀ δ z₁ → Rl ly M (H z₀) (Int ac δ q₀ lW kW zy mk u w) (H z₁)
IntRel ac q₀ lW kW zy mk u C ds c (rz e p) = rz (cq C e) (cq C p)
IntRel ac q₀ lW kW zy mk u C ds c (rs e p) = ds self lW _ _ _ c e p
IntRel ac q₀ lW kW zy mk u C ds c (rc D₁ D₂) =
  rc (IntRel ac q₀ lW kW zy mk u C ds c D₁) (IntRel ac q₀ lW kW zy mk u C ds (rc c (rw D₁)) D₂)
IntRel ac q₀ lW kW zy mk u C ds c (rb e p D) = rb (cq C e) (cq C p) (IntRel ac q₀ lW kW zy mk u C ds (rr c e p) D)
IntRel ac q₀ lW kW zy mk u C ds c (rr D e p) = rr (IntRel ac q₀ lW kW zy mk u C ds c D) (cq C e) (cq C p)
IntRel ac q₀ lW kW zy mk u C ds c (rw {p = p′} D) = IntRel ac (⊲-tr p′ q₀) lW kW zy mk u C ds c D
IntRel ac {H = H} q₀ lW kW zy mk u C ds c (rl g e p q e₀ st) =
  rl (λ n → H (g n)) (cl C g e) (cq C p) (λ n → cq C (q n)) (cq C e₀)
     (λ m → IntRel ac q₀ lW kW zy mk u C ds (rc c (Pre-Rel g e₀ q st m)) (st m))
IntRel ac {H = H} q₀ lW kW zy mk u C ds c (rd g e p q f D) =
  rd (λ n → H (g n)) (cl C g e) (cq C p) (λ n → cq C (q n)) (cm C f)
     (rr (IntRel ac q₀ lW kW zy mk u C ds c D) (cl C (λ m → g (suc m)) (λ n → q (suc n))) (λ n → cq C (q (suc n))))
IntRel {ly} {M} {k} (acc g) {κ} {H} q₀ lW kW zy mk u C ds {w = w} c (ri {k = j} R v p₂ H₂ e p e₀ C₂ ds₂) =
  ri (mk kW R) _ (κ p₂) (λ z → H (H₂ z))
     (cn C p₂ H₂ e (cq C₂))
     (cq C p)
     (cq C e₀)
     (ContF-κ (comp C₂ C))
     (λ {W′} q lW′ w₂ a₀ a₁ h d pz → subst
        (λ z → Rl ly M (H (H₂ a₀))
           (Int (acc g) (v (⊲-tr q₀ q) lW′ (N.inS R z)) self lW′ (⊲-tr kW q) zy mk (λ p′ → u (⊲-tr q p′))
              (nw q w ⨾ Int {cnt k} (g R) z self lW′ (⊲-tr (⊲-tr (S→⊲ R) kW) q) (NZ-S R) (λ _ R′ → Sk R′ (S→⊲ R))
                          (λ p′ l′ z′ → v (⊲-tr (⊲-tr q₀ q) p′) l′ (N.inS R z′)) n0))
           (H (H₂ a₁)))
        (sym (out-inV ly (mk kW R) w₂))
        (IntRel (acc g) self lW′ (⊲-tr kW q) zy mk (λ p′ → u (⊲-tr q p′)) C (λ q′ → ds (⊲-tr q q′))
           (rc (rw c) (rb e₀ (cq C₂ (Ω≈ j))
              (IntRel {cnt k} {k} (g R) self lW′ (⊲-tr (⊲-tr (S→⊲ R) kW) q) (NZ-S R) (λ _ R′ → Sk R′ (S→⊲ R))
                 (λ p′ l′ z′ → v (⊲-tr (⊲-tr q₀ q) p′) l′ (N.inS R z′)) C₂
                 (λ q′ l′ w₁ z₀ z₁ c₁ d₁ p₁ → ds₂ (⊲-tr (⊲-tr q₀ q) q′) l′ w₁ z₀ z₁ (→Rw R c₁) d₁ p₁)
                 (rz (Ω≈ j) (Ω≈ j)) (Lw→ ly (mk kW R) h))))
           (ds₂ (⊲-tr q₀ q) lW′ w₂ a₀ a₁ (→Rw R (Lw→ ly (mk kW R) h)) d pz)))
```
