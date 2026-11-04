# 验收的桥: 累加前的折叠就是 Level 的折叠

> **验收文件**, 读 `OCF.Align.Level`. 判决: **HOLDS** (结构互模拟). 上一轮的折叠 [CumReadCF](CumReadCF.lagda.md) 的 `Y η` 与 Level 的 $\psi^0(\Omega_\ell)$, 当 $\eta$ 与 $\ell$ 逐构造子对应 (`Ix`) 时, 经第 0 层翻译 $\cong$ (`Y-sim`).
>
> 这条桥不说累加不改值. 它只说: **在同一个下标上, 两个折叠是同一棵树**, 所以 $T^c$ 与 $\psi_0(\Omega_\Omega)$ 的差别全在下标链上. 下标链的账在 [CumUpAcceptVal](CumUpAcceptVal.lagda.md).
>
> `Sm x y`: 左边 `O L` 的项, 右边 Level 的树, 按左边的层分层. `oe` 左透明, `up` 右透明. 不要 PER: `tr`, `back` 的四条引理与 Level 的 `tr-≅` 同形. `rep` (左结合) 对 `iter` (右结合) 的差用 `Asc` 消掉.
>
> 全文 `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumUpAcceptSim where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open Restr hiding (rep)
import OCF.Free.Level as FL
open import OCF.Align.CumReadBase using (Ord₀)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Strict; ss; sl; Lg; ≪S; ≪⊲; ≪∘; ⊲-tr; z⊲; Rk; keep; rise; O; Vs; Vc; O₊; o0; os; ol; oi; oe; inS; outS; inC; outC; out-inS; addS; addC; rep; _⊕_; chainᵒ; Ω̇; Tg; rkT; ψS; ψC)
import OCF.Align.CumReadCF as C
open C using () renaming (add to cadd)
open import OCF.Align.CumReadCFThm using (ord; Y)
```

## §1 下标的对应

```agda
data Ix : A → Ordᴵ → Set where
  iz : Ix azero zero
  is : ∀ {a b} → Ix a b → Ix (asuc a) (suc b)
  il : ∀ {f : ℕ → A} {g : ℕ → Ordᴵ} {s} → (∀ n → Ix (f n) (g n)) → Ix (alim f) (lim g s)

Ix-≅ : ∀ {a b b′} → Ix a b → Ix a b′ → b ≅ᴵ b′
Ix-≅ iz iz = z≅
Ix-≅ (is d) (is d′) = s≅ (Ix-≅ d d′)
Ix-≅ (il h) (il h′) = l≅ (λ n → Ix-≅ (h n) (h′ n))

Ix-r : ∀ {a b b′} → Ix a b → b ≅ᴵ b′ → Ix a b′
Ix-r iz z≅ = iz
Ix-r (is d) (s≅ e) = is (Ix-r d e)
Ix-r (il h) (l≅ e) = il (λ n → Ix-r (h n) (e n))

≅I→⊑ : ∀ {a b} → a ≅ᴵ b → a ⊑ᴵ b
≅I→⊑ z≅     = z⊑
≅I→⊑ (s≅ e) = s⊑ e zero
≅I→⊑ (l≅ h) = l⊑ (λ n → ⊑ᴵ-trans (≅I→⊑ (h n)) (Sim→⊑ᴵ (lim n)))

⊲→⊑ : ∀ {a b a′ b′} → a ⊲ b → Ix a a′ → Ix b b′ → a′ ⊑ᴵ b′
⊲→⊑ C.self ia ib = ≅I→⊑ (Ix-≅ ia ib)
⊲→⊑ (C.suc p) ia (is ib) = ⊑ᴵ-trans (⊲→⊑ p ia ib) (Sim→⊑ᴵ suc)
⊲→⊑ (C.lim n p) ia (il h) = ⊑ᴵ-trans (⊲→⊑ p ia (h n)) (Sim→⊑ᴵ (lim n))

≪→≺ : ∀ {k t k′ t′} → k ≪ t → Ix k k′ → Ix t t′ → k′ ≺ᴵ t′
≪→≺ C.zero ik (is it) = via (Ix-≅ ik it) zero
≪→≺ (C.suc r) ik (is it) = ≺ᴵ-trans (≪→≺ r ik it) (via (≅ᴵ-refl _) zero)
≪→≺ (C.lim n r) ik (il h) with ≪→≺ r ik (h n)
... | via e q = via e (lim n q)

≺⊑′ : ∀ {c b a} → c ≺ᴵ b → b ⊑ᴵ a → c ≺ᴵ a
≺⊑′ (via e q) k = ≺ᴵ-respˡ e (sim k q)
```

## §2 关系

```agda
module _ (L : A) (S< : ∀ {a} (R : Strict a L) → Vs L R → ∀ {ℓ} → Ordᶜ ℓ → Set) where
  data Sm₊ : ∀ {ℓ} → O L → Ordᶜ ℓ → Set where
    sz : ∀ {ℓ} → Sm₊ {ℓ} o0 zero
    su : ∀ {ℓ} {x : O L} {y : Ordᶜ ℓ} → Sm₊ x y → Sm₊ (os x) (suc y)
    sL : ∀ {ℓ} {F : ℕ → O L} {G : ℕ → Ordᶜ ℓ} → (∀ n → Sm₊ (F n) (G n)) → Sm₊ (ol F) (lim G)
    si : ∀ {ℓ j k} {r : k ≪ L} {q : j <ᴵ ℓ} {h : Vs L (≪S r) → O L} {g : U j (<→◃ q) → Ordᶜ ℓ} → Ix k j →
         (∀ (x : O k) (y : Ordᶜ j) → S< (≪S r) (inS (≪S r) x) y → Sm₊ (h (inS (≪S r) x)) (g (into (<→◃ q) y))) →
         Sm₊ (oi r h) (limᵢ q g)
    se : ∀ {ℓ a} {R : Strict a L} {x : Vs L R} {b : Ordᶜ ℓ} → S< R x b → Sm₊ (oe R x) b
    sU : ∀ {ℓ k} {a : O L} {r : k ◃₁ ℓ} {y : U k (◃₁→◃ r)} → Sm₊ a (out (◃₁→◃ r) y) → Sm₊ a (up r y)

Sm : ∀ {L ℓ} → O L → Ordᶜ ℓ → Set
SS : ∀ L {a} (R : Strict a L) → Vs L R → ∀ {ℓ} → Ordᶜ ℓ → Set
SC : ∀ b {a} (P : a ⊲ b) → Vc b P → ∀ {ℓ} → Ordᶜ ℓ → Set
Sm {L} = Sm₊ L (SS L)
SS (asuc b) (ss P) x y = SC b P x y
SS (alim f) (sl n P) x y = SC (f n) P x y
SC a C.self x y = Sm x y
SC (asuc b) (C.suc P) x y = SC b P x y
SC (alim f) (C.lim n P) x y = SC (f n) P x y

C→Sm : ∀ {b a ℓ} (P : a ⊲ b) {x : O a} {y : Ordᶜ ℓ} → SC b P (inC P x) y → Sm x y
C→Sm C.self d = d
C→Sm (C.suc P) d = C→Sm P d
C→Sm (C.lim n P) d = C→Sm P d

Sm→C : ∀ {b a ℓ} (P : a ⊲ b) {x : O a} {y : Ordᶜ ℓ} → Sm x y → SC b P (inC P x) y
Sm→C C.self d = d
Sm→C (C.suc P) d = Sm→C P d
Sm→C (C.lim n P) d = Sm→C P d

S→Sm : ∀ {b a ℓ} (R : Strict a b) {x : O a} {y : Ordᶜ ℓ} → SS b R (inS R x) y → Sm x y
S→Sm (ss P) d = C→Sm P d
S→Sm (sl n P) d = C→Sm P d

Sm→S : ∀ {b a ℓ} (R : Strict a b) {x : O a} {y : Ordᶜ ℓ} → Sm x y → SS b R (inS R x) y
Sm→S (ss P) d = Sm→C P d
Sm→S (sl n P) d = Sm→C P d
```

## §3 搬运不可见

与 Level 的 `tr-≅`, `tr⁻-≅`, `back-≅`, `back⁻-≅` 同形.

```agda
Sm-tr    : ∀ {a b L} (e : a ≅ᴵ b) {x : O L} {y : Ordᶜ a} → Sm x y → Sm x (tr e y)
Sm-tr⁻   : ∀ {a b L} (e : a ≅ᴵ b) {x : O L} {y : Ordᶜ b} → Sm x y → Sm x (tr⁻ e y)
Sm-back  : ∀ {j a b L} (q : j <ᴵ a) (e : a ≅ᴵ b) {x : O L} {u : Ordᶜ (Restr.rep (res q e))} → Sm x u → Sm x (back (res q e) u)
Sm-back⁻ : ∀ {j a b L} (q : j <ᴵ b) (e : a ≅ᴵ b) {x : O L} {u : Ordᶜ (Restr.rep (res⁻ q e))} → Sm x u → Sm x (back (res⁻ q e) u)
trS  : ∀ {a b L c} (e : a ≅ᴵ b) (R : Strict c L) {x : Vs L R} {y : Ordᶜ a} → SS L R x y → SS L R x (tr e y)
trC  : ∀ {a b L c} (e : a ≅ᴵ b) (P : c ⊲ L) {x : Vc L P} {y : Ordᶜ a} → SC L P x y → SC L P x (tr e y)
tr⁻S : ∀ {a b L c} (e : a ≅ᴵ b) (R : Strict c L) {x : Vs L R} {y : Ordᶜ b} → SS L R x y → SS L R x (tr⁻ e y)
tr⁻C : ∀ {a b L c} (e : a ≅ᴵ b) (P : c ⊲ L) {x : Vc L P} {y : Ordᶜ b} → SC L P x y → SC L P x (tr⁻ e y)

trS e (ss P) d = trC e P d
trS e (sl n P) d = trC e P d
trC e C.self d = Sm-tr e d
trC e (C.suc P) d = trC e P d
trC e (C.lim n P) d = trC e P d
tr⁻S e (ss P) d = tr⁻C e P d
tr⁻S e (sl n P) d = tr⁻C e P d
tr⁻C e C.self d = Sm-tr⁻ e d
tr⁻C e (C.suc P) d = tr⁻C e P d
tr⁻C e (C.lim n P) d = tr⁻C e P d

Sm-tr e (se {R = R} d) = se (trS e R d)
Sm-tr e sz = sz
Sm-tr e (su d) = su (Sm-tr e d)
Sm-tr e (sL h) = sL (λ n → Sm-tr e (h n))
Sm-tr e (si {r = r} {q = q} {h = h} {g = g} ij H) =
  si (Ix-r ij (eq (res q e))) λ x u d →
    subst (λ w → Sm (h (inS (≪S r) x)) (tr e (g (into (<→◃ q) (back (res q e) w)))))
          (sym (out-into (<→◃ (lt (res q e))) u))
          (Sm-tr e (H x _ (Sm→S (≪S r) (Sm-back q e (S→Sm (≪S r) d)))))
Sm-tr (s≅ e) (sU {r = zero} d) = sU {r = zero} (Sm-tr e d)
Sm-tr (l≅ h) (sU {r = self n} d) = sU {r = self n} (Sm-tr (h n) d)

Sm-tr⁻ e (se {R = R} d) = se (tr⁻S e R d)
Sm-tr⁻ e sz = sz
Sm-tr⁻ e (su d) = su (Sm-tr⁻ e d)
Sm-tr⁻ e (sL h) = sL (λ n → Sm-tr⁻ e (h n))
Sm-tr⁻ e (si {r = r} {q = q} {h = h} {g = g} ij H) =
  si (Ix-r ij (eq (res⁻ q e))) λ x u d →
    subst (λ w → Sm (h (inS (≪S r) x)) (tr⁻ e (g (into (<→◃ q) (back (res⁻ q e) w)))))
          (sym (out-into (<→◃ (lt (res⁻ q e))) u))
          (Sm-tr⁻ e (H x _ (Sm→S (≪S r) (Sm-back⁻ q e (S→Sm (≪S r) d)))))
Sm-tr⁻ (s≅ e) (sU {r = zero} d) = sU {r = zero} (Sm-tr⁻ e d)
Sm-tr⁻ (l≅ h) (sU {r = self n} d) = sU {r = self n} (Sm-tr⁻ (h n) d)

Sm-back zero      (s≅ e) d = Sm-tr⁻ e d
Sm-back (suc q)   (s≅ e) d = Sm-back q e d
Sm-back (lim n q) (l≅ h) d = Sm-back q (h n) d

Sm-back⁻ zero      (s≅ e) d = Sm-tr e d
Sm-back⁻ (suc q)   (s≅ e) d = Sm-back⁻ q e d
Sm-back⁻ (lim n q) (l≅ h) d = Sm-back⁻ q (h n) d
```

## §4 $\Omega$, 加法, 倍数

```agda
Sm-Ω : ∀ {L ℓ} → Ix L ℓ → Sm (Ω̇ L) (Ω ℓ)
Sm-Ω iz = su sz
Sm-Ω (is ij) = si ij (λ x y d → sU {r = zero} (se d))
Sm-Ω (il h) = sL (λ n → sU {r = self n} (se (Sm-Ω (h n))))

Sm-add : ∀ {L a ℓ k} {W : O L} {w : Ordᶜ ℓ} (P : a ⊲ L) (σ : Simᴵ k ℓ) {x : O a} {y : Ordᶜ k} → Sm W w → Sm x y → Sm (cadd W P x) (add w σ y)
aS : ∀ {L b a ℓ k} {W : O L} {w : Ordᶜ ℓ} (Q : b ⊲ L) (σ : Simᴵ k ℓ) (R : Strict a b) {x : Vs b R} {y : Ordᶜ k} → Sm W w → SS b R x y → Sm (addS W Q R x) (add w σ y)
aC : ∀ {L b a ℓ k} {W : O L} {w : Ordᶜ ℓ} (Q : b ⊲ L) (σ : Simᴵ k ℓ) (P : a ⊲ b) {x : Vc b P} {y : Ordᶜ k} → Sm W w → SC b P x y → Sm (addC W Q P x) (add w σ y)

aS Q σ (ss P) dW d = aC (⊲-tr (C.suc C.self) Q) σ P dW d
aS Q σ (sl n P) dW d = aC (⊲-tr (C.lim n C.self) Q) σ P dW d
aC Q σ C.self dW d = Sm-add Q σ dW d
aC Q σ (C.suc P) dW d = aC (⊲-tr (C.suc C.self) Q) σ P dW d
aC Q σ (C.lim n P) dW d = aC (⊲-tr (C.lim n C.self) Q) σ P dW d

Sm-add P σ dW (se {R = R} d) = aS P σ R dW d
Sm-add P σ dW sz = dW
Sm-add P σ dW (su d) = su (Sm-add P σ dW d)
Sm-add P σ dW (sL h) = sL (λ n → Sm-add P σ dW (h n))
Sm-add {W = W} {w = w} P σ dW (si {r = r} {q = q} {h = h} {g = g} ij H) =
  si ij λ x y d →
    subst₂ (λ u v → Sm (cadd W P (h (inS (≪S r) u))) (add w σ (g (into (<→◃ q) v))))
           (sym (out-inS (≪S (≪∘ r P)) x)) (sym (out-into (<→◃ (σ q)) y))
           (Sm-add P σ dW (H x y (Sm→S (≪S r) (S→Sm (≪S (≪∘ r P)) d))))
Sm-add P σ dW (sU {r = zero} d) = Sm-add P (λ q → σ (suc q)) dW d
Sm-add P σ dW (sU {r = self n} d) = Sm-add P (λ q → σ (lim n q)) dW d

Asc  : ∀ {L a ℓ} {A₀ y : O L} (P : a ⊲ L) (z : O a) {e : Ordᶜ ℓ} → Sm (cadd A₀ C.self (cadd y P z)) e → Sm (cadd (cadd A₀ C.self y) P z) e
AscS : ∀ {L b a ℓ} {A₀ y : O L} (Q : b ⊲ L) (R : Strict a b) (x : Vs b R) {e : Ordᶜ ℓ} → Sm (cadd A₀ C.self (addS y Q R x)) e → Sm (addS (cadd A₀ C.self y) Q R x) e
AscC : ∀ {L b a ℓ} {A₀ y : O L} (Q : b ⊲ L) (P : a ⊲ b) (x : Vc b P) {e : Ordᶜ ℓ} → Sm (cadd A₀ C.self (addC y Q P x)) e → Sm (addC (cadd A₀ C.self y) Q P x) e

AscS Q (ss P) x d = AscC (⊲-tr (C.suc C.self) Q) P x d
AscS Q (sl n P) x d = AscC (⊲-tr (C.lim n C.self) Q) P x d
AscC Q C.self x d = Asc Q x d
AscC Q (C.suc P) x d = AscC (⊲-tr (C.suc C.self) Q) P x d
AscC Q (C.lim n P) x d = AscC (⊲-tr (C.lim n C.self) Q) P x d

Asc P o0 d = d
Asc P (os x) (su d) = su (Asc P x d)
Asc P (os x) (sU {r = r} d) = sU {r = r} (Asc P (os x) d)
Asc P (ol F) (sL h) = sL (λ n → Asc P (F n) (h n))
Asc P (ol F) (sU {r = r} d) = sU {r = r} (Asc P (ol F) d)
Asc {A₀ = A₀} {y = y} P (oi r h) (si {q = q} {g = g} ij H) =
  si ij λ x₁ y₁ d →
    subst (λ u → Sm (cadd (cadd A₀ C.self y) P (h (inS (≪S r) u))) (g (into (<→◃ q) y₁)))
          (sym (out-inS (≪S (≪∘ r P)) x₁))
          (Asc P (h (inS (≪S r) x₁))
            (subst (λ u → Sm (cadd A₀ C.self (cadd y P (h (inS (≪S r) u)))) (g (into (<→◃ q) y₁)))
                   (trans (cong (outS (≪S (≪∘ r P))) (out-inS′ x₁)) (out-inS (≪S (≪∘ r P)) x₁))
                   (H x₁ y₁ d)))
  where
  out-inS′ : ∀ x → inS (≪S (≪∘ r P)) (outS (≪S (≪∘ r P)) (inS (≪S (≪∘ r P)) x)) ≡ inS (≪S (≪∘ r P)) x
  out-inS′ x = cong (inS (≪S (≪∘ r P))) (out-inS (≪S (≪∘ r P)) x)
Asc P (oi r h) (sU {r = r′} d) = sU {r = r′} (Asc P (oi r h) d)
Asc P (oe R x) d = AscS P R x d

module Rep {ℓ} (b : Ordᶜ ℓ) where
  itr : ℕ → Ordᶜ ℓ → Ordᶜ ℓ
  itr zero d = d
  itr (suc n) d = b + itr n d

  itr-c : ∀ n d → itr n (b + d) ≡ b + itr n d
  itr-c zero d = refl
  itr-c (suc n) d = cong (b +_) (itr-c n d)

  itr≡ : ∀ n → itr n zero ≡ iter (b +_) zero n
  itr≡ zero = refl
  itr≡ (suc n) = cong (b +_) (itr≡ n)

  repS : ∀ {L} {y : O L} → Sm y b → ∀ n {z : O L} {d : Ordᶜ ℓ} → Sm z d → Sm (rep y (suc n) ⊕ z) (itr (suc n) d)
  repS e zero dz = Sm-add C.self (λ q → q) e dz
  repS {y = y} e (suc n) {z} {d} dz =
    Asc C.self z (subst (Sm (rep y (suc n) ⊕ (y ⊕ z))) (itr-c (suc n) d) (repS e n (Sm-add C.self (λ q → q) e dz)))

  Sm-rep : ∀ {L} {y : O L} → Sm y b → ∀ n → Sm (rep y n) (iter (b +_) zero n)
  Sm-rep e zero = sz
  Sm-rep e (suc zero) = e
  Sm-rep {y = y} e (suc (suc n)) =
    subst (Sm (rep y (suc n) ⊕ y)) (trans (itr-c (suc n) zero) (cong (b +_) (itr≡ (suc n)))) (repS e n e)
```

## §5 折叠

```agda
Sm-ψ : ∀ {L t i ℓ k} {x : O L} {y : Ordᶜ k} (T : Tg t L) (w : Lg L) (p : i <ᴵ ℓ) (σ : Simᴵ k ℓ) → Ix t i → Sm x y → Sm (C.ψ t T w x) (ψ p σ y)
pS : ∀ {L a t i ℓ k} {y : Ordᶜ k} (R : Strict a L) (T : Tg t a) (w : Lg a) (p : i <ᴵ ℓ) (σ : Simᴵ k ℓ) {x : Vs L R} → Ix t i → SS L R x y → Sm (ψS t R T w x) (ψ p σ y)
pC : ∀ {b a t i ℓ k} {y : Ordᶜ k} (P : a ⊲ b) (T : Tg t a) (w : Lg a) (p : i <ᴵ ℓ) (σ : Simᴵ k ℓ) {x : Vc b P} → Ix t i → SC b P x y → Sm (ψC t P T w x) (ψ p σ y)

pS (ss P) T w p σ it d = pC P T w p σ it d
pS (sl n P) T w p σ it d = pC P T w p σ it d
pC C.self T w p σ it d = Sm-ψ T w p σ it d
pC (C.suc P) T w p σ it d = pC P T w p σ it d
pC (C.lim n P) T w p σ it d = pC P T w p σ it d

Sm-ψ {L} T w p σ it (se {R = R} d) = pS R (C.tgS R T w) (C.lgS R w) p σ it d
Sm-ψ T w p σ it sz = Sm-Ω it
Sm-ψ T w p σ it (su {y = y} d) = sL (Rep.Sm-rep (ψ p σ y) (Sm-ψ T w p σ it d))
Sm-ψ T w p σ it (sL h) = sL (λ n → Sm-ψ T w p σ it (h n))
Sm-ψ {t = t} T w p σ it (si {j = j} {k = k} {r = r} {q = q} {h = h} {g = g} ij H) with rkT r T w | <ᴵ-dec (σ q) p
... | keep s | injᵃ (via e r′) =
  si (Ix-r ij e) λ x₁ y₁ d →
    subst₂ (λ u v → Sm (C.ψ t T w (h (inS (≪S r) u))) (ψ p σ (g (into (<→◃ q) (tr⁻ e v)))))
           (sym (out-inS (≪S s) x₁)) (sym (out-into (<→◃ r′) y₁))
           (Sm-ψ T w p σ it (H x₁ (tr⁻ e y₁) (Sm→S (≪S r) (Sm-tr⁻ e (S→Sm (≪S s) d)))))
... | keep s | injᵇ c = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-trans (≪→≺ s ij it) c))
... | keep s | injᶜ c = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ (≪→≺ s ij it) (≅ᴵ-sym c)))
... | rise u | injᵃ c = ⊥-elim (≺ᴵ-irrefl (≺⊑′ c (⊲→⊑ u it ij)))
... | rise u | injᵇ _ = sL (λ n → Sm-ψ T w p σ it (H _ _ (Sm→S (≪S r) (chain n))))
  where
  chain : ∀ n → Sm (chainᵒ (λ z → C.ψ k (inj₁ (≪⊲ r)) w (h (inS (≪S r) z))) n) (iter (λ x → ψ q (λ r₁ → r₁) (g (into (<→◃ q) x))) (Ω j) n)
  chain zero = Sm-Ω ij
  chain (suc n) = Sm-ψ (inj₁ (≪⊲ r)) w q (λ r₁ → r₁) ij (H _ _ (Sm→S (≪S r) (chain n)))
... | rise u | injᶜ _ = sL (λ n → Sm-ψ T w p σ it (H _ _ (Sm→S (≪S r) (chain n))))
  where
  chain : ∀ n → Sm (chainᵒ (λ z → C.ψ k (inj₁ (≪⊲ r)) w (h (inS (≪S r) z))) n) (iter (λ x → ψ q (λ r₁ → r₁) (g (into (<→◃ q) x))) (Ω j) n)
  chain zero = Sm-Ω ij
  chain (suc n) = Sm-ψ (inj₁ (≪⊲ r)) w q (λ r₁ → r₁) ij (H _ _ (Sm→S (≪S r) (chain n)))
Sm-ψ T w p σ it (sU {r = zero} d) = Sm-ψ T w p (λ q → σ (suc q)) it d
Sm-ψ T w p σ it (sU {r = self n} d) = Sm-ψ T w p (λ q → σ (lim n q)) it d
```

## §6 第 0 层

```agda
fr : Ord₀ → Ordᶜ zero
fr FL.zero = zero
fr (FL.suc a) = suc (fr a)
fr (FL.lim f) = lim (λ n → fr (f n))
fr (FL.limᵢ () f)
fr (FL.up () x)

Sm₀ : {x : O azero} {y : Ordᶜ zero} → Sm x y → fr (ord x) ≅ y
Sm₀ sz = z≅
Sm₀ (su d) = s≅ (Sm₀ d)
Sm₀ (sL h) = l≅ (λ n → Sm₀ (h n))
Sm₀ (si {r = ()} _ _)
Sm₀ (se {R = ()} _)
Sm₀ (sU {r = ()} _)

Y-sim : ∀ {η ℓ} (w : Lg η) → Ix η ℓ → (p : zero <ᴵ ℓ) → fr (Y η w) ≅ ψ⁰ (Ω ℓ)
Y-sim {η} {ℓ} w ix p =
  ≅-trans (Sm₀ (Sm-ψ (inj₁ (z⊲ η)) w p (λ q → q) iz (Sm-Ω ix))) (≅-sym (ψ⁰≅ψ {p = p} {σ = λ q → q} (Ω-refl ℓ)))
```
