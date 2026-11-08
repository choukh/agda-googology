# 极限分量升层与结构搬运：单侧关系交换

与后继版本相同，逐构造保持原Rq；self分量无需按值严格。
在marker头部只消去构造子，不对函数分支断言字面相等。

```agda
{-# OPTIONS --safe --without-K #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueTransportLimit (𝕊 : HtB) where
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Free.Level
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdRel 𝕊

erase-tr-marker : ∀ {m a b c k φ χ} (e : a ≅ᴵ b)
  (r : k ◃₁ a) (z : Us m k (◃₁→◃ r) φ χ) (x : Q m a φ χ) (s : b ◃ c) →
  ι s (trQ e (omk r z x)) ≡ ι s (trQ e x)
erase-tr-marker (s≅ e) zero z x s = refl
erase-tr-marker (l≅ f) (self n) z x s = refl

data Frame : Ordᴵ → Ordᴵ → Ordᴵ → Ordᴵ → Set where
  at : ∀ {f sf g sg} (e : ∀ n → f n ≅ᴵ g n) (j : ℕ) →
    Frame (f j) (g j) (lim f sf) (lim g sg)
low-e : ∀ {a b A B} → Frame a b A B → a ≅ᴵ b
low-e (at e j) = e j
high-e : ∀ {a b A B} → Frame a b A B → A ≅ᴵ B
high-e (at e j) = l≅ e
src : ∀ {a b A B} → Frame a b A B → a ◃ A
src (at e j) = self j
dst : ∀ {a b A B} → Frame a b A B → b ◃ B
dst (at e j) = self j

frame-right : ∀ {m a a′ A B b φ χ ψ ρ} (z : Q m a ψ ρ)
  (fr : Frame a a′ A B) {x : Q m b φ χ} →
  Rq m b B x (trQ (high-e fr) (ι (src fr) z)) →
  Rq m b B x (ι (dst fr) (trQ (low-e fr) z))
frame-right z@q0 fr (rwkˡ rel) = rwkˡ (frame-right z fr rel)
frame-right z@(qs y) fr (rwkˡ rel) = rwkˡ (frame-right z fr rel)
frame-right z@(ql f) fr (rwkˡ rel) = rwkˡ (frame-right z fr rel)
frame-right z@(qi ac f) fr (rwkˡ rel) = rwkˡ (frame-right z fr rel)
frame-right z@(qŝ c t g) fr (rwkˡ rel) = rwkˡ (frame-right z fr rel)
frame-right z@(qĉ c t g o k) fr (rwkˡ rel) = rwkˡ (frame-right z fr rel)
frame-right z@(qclo t g) fr (rwkˡ rel) = rwkˡ (frame-right z fr rel)
frame-right z@(qcl q ψ s t g) fr (rwkˡ rel) = rwkˡ (frame-right z fr rel)
frame-right z@(qwk le lc y) fr (rwkˡ rel) = rwkˡ (frame-right z fr rel)
frame-right z@(qΩ↓ q fe ac h) fr (rwkˡ rel) = rwkˡ (frame-right z fr rel)
frame-right z@(qΩ fe q h) fr (rwkˡ rel) = rwkˡ (frame-right z fr rel)
frame-right q0 fr rz = rz
frame-right (qs z) fr (rs sf sc h) = rs sf sc (frame-right z fr h)
frame-right (ql f) fr (rl h) = rl (λ n → frame-right (f n) fr (h n))
frame-right (qi ac f) fr (ri ej h) = ri ej (λ x y d → frame-right (f y) fr (h x y d))
frame-right (qŝ c t g) fr (rŝ ec h hg) = rŝ ec (frame-right t fr h)
  (λ η ee η′ e′ d → frame-right (g η′ e′) fr (hg η ee η′ e′ d))
frame-right (qĉ c t g o h) fr (rĉ ec st sg ro rh) = rĉ ec st sg
  (frame-right o fr ro)
  (λ η ee η′ e′ d → frame-right (h η′ e′) fr (rh η ee η′ e′ d))
frame-right (qclo t g) fr (rclo sf h hg) = rclo sf (frame-right t fr h)
  (λ η η′ d → frame-right (g η′) fr (hg η η′ d))
frame-right (qcl q ψ s t g) fr (rcl eqn sf h hg) = rcl eqn sf (frame-right t fr h)
  (λ η η′ d → frame-right (g η′) fr (hg η η′ d))
frame-right (qwk le lc z) fr (rwkʳ h) = rwkʳ (frame-right z fr h)
frame-right (qΩ↓ q fe ac h) fr (rΩ↓ eqn ek sf sc rh) = rΩ↓ eqn ek sf sc
  (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → frame-right (h ξ′ ζ′ (intoV q z′)) fr
    (rh ξ ξ′ ζ ζ′ d dc dc′ z z′ l))
frame-right {m} {b = b} (qΩ fe q h) (at {f = f} {sf = sf₀} {g = g} {sg = sg} e j)
  (rΩ {r = r} {h = hx} ek sf sc rh) = rΩ ek sf sc
  (λ ξ ξ′ ζ ζ′ d dc z z′ l →
    subst
      (λ w → Rq m b (lim g sg) (hx ξ ζ (intoU (<→◃ r) z))
        (ι {b = lim g sg} (self j) (trQ (e j) (h ξ′ ζ′ (intoU (<→◃ q) (backQ (resQ q (e j)) w))))))
      (sym (trans
        (cong (λ w → outU (<→◃ (ltQ (resQ q (e j))))
          (intoU (<→◃ (ltQ (resQ q (e j)))) w))
          (out-intoU (<→◃ {b = lim g sg} (lim j (ltQ (resQ q (e j))))) z′))
        (out-intoU (<→◃ (ltQ (resQ q (e j)))) z′)))
      (frame-right (h ξ′ ζ′ (intoU (<→◃ q) (backQ (resQ q (e j)) z′))) (at {f = f} {sf = sf₀} {g = g} {sg = sg} e j)
        (subst
          (λ w → Rq m b (lim g sg) (hx ξ ζ (intoU (<→◃ r) z))
            (trQ (l≅ e) (ι {b = lim f sf₀} (self j) (h ξ′ ζ′ (intoU (<→◃ q) w)))))
          (trans
            (out-intoU (<→◃ {b = lim f sf₀} (lim j q)) _)
            (cong (backQ (resQ q (e j)))
              (out-intoU (<→◃ {b = lim g sg} (lim j (ltQ (resQ q (e j))))) z′)))
          (rh ξ ξ′ ζ ζ′ d dc z z′ l))))
frame-right (omk r z x) fr h =
  subst (λ w → Rq _ _ _ _ w)
    (sym (erase-tr-marker (low-e fr) r z x (dst fr)))
    (frame-right x fr h)

limit-marker : ∀ {m f sf g sg φ χ} (e : ∀ n → f n ≅ᴵ g n) (j : ℕ)
  {z : Q m (f j) φ χ} {body : Q m (lim f sf) φ χ} →
  Rq m (lim f sf) (lim f sf) body (ι (self j) z) →
  Rq m (lim g sg) (lim g sg) (trQ (l≅ e) body)
    (ι (self j) (trQ (e j) z))
limit-marker {f = f} {sf = sf} {g = g} {sg = sg} e j {z} h =
  frame-right z (at {f = f} {sf = sf} {g = g} {sg = sg} e j) (R-trʳ (l≅ e) (R-trˡ (l≅ e) h))

erase-tr-marker-back : ∀ {m a b c k φ χ} (e : b ≅ᴵ a)
  (r : k ◃₁ a) (z : Us m k (◃₁→◃ r) φ χ) (x : Q m a φ χ) (s : b ◃ c) →
  ι s (tr⁻Q e (omk r z x)) ≡ ι s (tr⁻Q e x)
erase-tr-marker-back (s≅ e) zero z x s = refl
erase-tr-marker-back (l≅ f) (self n) z x s = refl

frame-back-right : ∀ {m a a′ A B b φ χ ψ ρ} (z : Q m a′ ψ ρ)
  (fr : Frame a a′ A B) {x : Q m b φ χ} →
  Rq m b A x (tr⁻Q (high-e fr) (ι (dst fr) z)) →
  Rq m b A x (ι (src fr) (tr⁻Q (low-e fr) z))
frame-back-right z@q0 fr (rwkˡ rel) = rwkˡ (frame-back-right z fr rel)
frame-back-right z@(qs y) fr (rwkˡ rel) = rwkˡ (frame-back-right z fr rel)
frame-back-right z@(ql f) fr (rwkˡ rel) = rwkˡ (frame-back-right z fr rel)
frame-back-right z@(qi ac f) fr (rwkˡ rel) = rwkˡ (frame-back-right z fr rel)
frame-back-right z@(qŝ c t g) fr (rwkˡ rel) = rwkˡ (frame-back-right z fr rel)
frame-back-right z@(qĉ c t g o k) fr (rwkˡ rel) = rwkˡ (frame-back-right z fr rel)
frame-back-right z@(qclo t g) fr (rwkˡ rel) = rwkˡ (frame-back-right z fr rel)
frame-back-right z@(qcl q ψ s t g) fr (rwkˡ rel) = rwkˡ (frame-back-right z fr rel)
frame-back-right z@(qwk le lc y) fr (rwkˡ rel) = rwkˡ (frame-back-right z fr rel)
frame-back-right z@(qΩ↓ q fe ac h) fr (rwkˡ rel) = rwkˡ (frame-back-right z fr rel)
frame-back-right z@(qΩ fe q h) fr (rwkˡ rel) = rwkˡ (frame-back-right z fr rel)
frame-back-right q0 fr rz = rz
frame-back-right (qs z) fr (rs sf sc h) = rs sf sc (frame-back-right z fr h)
frame-back-right (ql f) fr (rl h) = rl (λ n → frame-back-right (f n) fr (h n))
frame-back-right (qi ac f) fr (ri ej h) = ri ej (λ x y d → frame-back-right (f y) fr (h x y d))
frame-back-right (qŝ c t g) fr (rŝ ec h hg) = rŝ ec (frame-back-right t fr h)
  (λ η ee η′ e′ d → frame-back-right (g η′ e′) fr (hg η ee η′ e′ d))
frame-back-right (qĉ c t g o h) fr (rĉ ec st sg ro rh) = rĉ ec st sg
  (frame-back-right o fr ro)
  (λ η ee η′ e′ d → frame-back-right (h η′ e′) fr (rh η ee η′ e′ d))
frame-back-right (qclo t g) fr (rclo sf h hg) = rclo sf (frame-back-right t fr h)
  (λ η η′ d → frame-back-right (g η′) fr (hg η η′ d))
frame-back-right (qcl q ψ s t g) fr (rcl eqn sf h hg) = rcl eqn sf (frame-back-right t fr h)
  (λ η η′ d → frame-back-right (g η′) fr (hg η η′ d))
frame-back-right (qwk le lc z) fr (rwkʳ h) = rwkʳ (frame-back-right z fr h)
frame-back-right (qΩ↓ q fe ac h) fr (rΩ↓ eqn ek sf sc rh) = rΩ↓ eqn ek sf sc
  (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → frame-back-right (h ξ′ ζ′ (intoV q z′)) fr
    (rh ξ ξ′ ζ ζ′ d dc dc′ z z′ l))
frame-back-right {m} {b = b} (qΩ fe q h) (at {f = f} {sf = sf₀} {g = g} {sg = sg} e j)
  (rΩ {r = r} {h = hx} ek sf sc rh) = rΩ ek sf sc
  (λ ξ ξ′ ζ ζ′ d dc z z′ l →
    subst
      (λ w → Rq m b (lim f sf₀) (hx ξ ζ (intoU (<→◃ r) z))
        (ι {b = lim f sf₀} (self j) (tr⁻Q (e j) (h ξ′ ζ′ (intoU (<→◃ q) (backQ (res⁻Q q (e j)) w))))))
      (sym (trans
        (cong (λ w → outU (<→◃ (ltQ (res⁻Q q (e j))))
          (intoU (<→◃ (ltQ (res⁻Q q (e j)))) w))
          (out-intoU (<→◃ {b = lim f sf₀} (lim j (ltQ (res⁻Q q (e j))))) z′))
        (out-intoU (<→◃ (ltQ (res⁻Q q (e j)))) z′)))
      (frame-back-right (h ξ′ ζ′ (intoU (<→◃ q) (backQ (res⁻Q q (e j)) z′))) (at {f = f} {sf = sf₀} {g = g} {sg = sg} e j)
        (subst
          (λ w → Rq m b (lim f sf₀) (hx ξ ζ (intoU (<→◃ r) z))
            (tr⁻Q (l≅ e) (ι {b = lim g sg} (self j) (h ξ′ ζ′ (intoU (<→◃ q) w)))))
          (trans
            (out-intoU (<→◃ {b = lim g sg} (lim j q)) _)
            (cong (backQ (res⁻Q q (e j)))
              (out-intoU (<→◃ {b = lim f sf₀} (lim j (ltQ (res⁻Q q (e j))))) z′)))
          (rh ξ ξ′ ζ ζ′ d dc z z′ l))))
frame-back-right (omk r z x) fr h =
  subst (λ w → Rq _ _ _ _ w)
    (sym (erase-tr-marker-back (low-e fr) r z x (src fr)))
    (frame-back-right x fr h)

limit-marker-back : ∀ {m f sf g sg φ χ} (e : ∀ n → f n ≅ᴵ g n) (j : ℕ)
  {z : Q m (g j) φ χ} {body : Q m (lim g sg) φ χ} →
  Rq m (lim g sg) (lim g sg) body (ι (self j) z) →
  Rq m (lim f sf) (lim f sf) (tr⁻Q (l≅ e) body)
    (ι (self j) (tr⁻Q (e j) z))
limit-marker-back {f = f} {sf = sf} {g = g} {sg = sg} e j {z} h =
  frame-back-right z (at {f = f} {sf = sf} {g = g} {sg = sg} e j)
    (R-tr⁻ʳ (l≅ e) (R-tr⁻ˡ (l≅ e) h))
```
