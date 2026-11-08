# 后继升层与结构搬运：单侧关系交换

只在同一字面后继上界内搬运，不要求函数外延。输入关系的右侧
是原升层后搬运的完整对象；结论改为先搬低层再原升层。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueTransportSuccessor (𝕊 : HtB) where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Free.Level
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdRel 𝕊

shift-right : ∀ {m a a′ b φ χ ψ ρ} (e : a ≅ᴵ a′)
  (z : Q m a ψ ρ) {x : Q m b φ χ} →
  Rq m b (suc a′) x (trQ (s≅ e) (ι zero z)) →
  Rq m b (suc a′) x (ι zero (trQ e z))
shift-right e z@q0 (rwkˡ rel) = rwkˡ (shift-right e z rel)
shift-right e z@(qs y) (rwkˡ rel) = rwkˡ (shift-right e z rel)
shift-right e z@(ql f) (rwkˡ rel) = rwkˡ (shift-right e z rel)
shift-right e z@(qi ac f) (rwkˡ rel) = rwkˡ (shift-right e z rel)
shift-right e z@(qŝ c t g) (rwkˡ rel) = rwkˡ (shift-right e z rel)
shift-right e z@(qĉ c t g o k) (rwkˡ rel) = rwkˡ (shift-right e z rel)
shift-right e z@(qclo t g) (rwkˡ rel) = rwkˡ (shift-right e z rel)
shift-right e z@(qcl q ψ s t g) (rwkˡ rel) = rwkˡ (shift-right e z rel)
shift-right e z@(qwk le lc y) (rwkˡ rel) = rwkˡ (shift-right e z rel)
shift-right e z@(qΩ↓ q fe ac h) (rwkˡ rel) = rwkˡ (shift-right e z rel)
shift-right e z@(qΩ fe q h) (rwkˡ rel) = rwkˡ (shift-right e z rel)
shift-right e q0 rz = rz
shift-right e (qs z) (rs sf sc h) = rs sf sc (shift-right e z h)
shift-right e (ql f) (rl h) = rl (λ n → shift-right e (f n) (h n))
shift-right e (qi ac f) (ri ej h) = ri ej (λ x y d → shift-right e (f y) (h x y d))
shift-right e (qŝ c t g) (rŝ ec h hg) = rŝ ec (shift-right e t h)
  (λ η ee η′ e′ d → shift-right e (g η′ e′) (hg η ee η′ e′ d))
shift-right e (qĉ c t g o h) (rĉ ec st sg ro rh) = rĉ ec st sg
  (shift-right e o ro)
  (λ η ee η′ e′ d → shift-right e (h η′ e′) (rh η ee η′ e′ d))
shift-right e (qclo t g) (rclo sf h hg) = rclo sf (shift-right e t h)
  (λ η η′ d → shift-right e (g η′) (hg η η′ d))
shift-right e (qcl q ψ s t g) (rcl eqn sf h hg) = rcl eqn sf (shift-right e t h)
  (λ η η′ d → shift-right e (g η′) (hg η η′ d))
shift-right e (qwk le lc z) (rwkʳ h) = rwkʳ (shift-right e z h)
shift-right e (qΩ↓ q fe ac h) (rΩ↓ eqn ek sf sc rh) = rΩ↓ eqn ek sf sc
  (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → shift-right e (h ξ′ ζ′ (intoV q z′))
    (rh ξ ξ′ ζ ζ′ d dc dc′ z z′ l))
shift-right {m} {a′ = a′} {b} e (qΩ fe q h)
  (rΩ {r = r} {h = hx} ek sf sc rh) = rΩ ek sf sc
  (λ ξ ξ′ ζ ζ′ d dc z z′ l →
    subst
      (λ w → Rq m b (suc a′) (hx ξ ζ (intoU (<→◃ r) z))
        (ι zero (trQ e (h ξ′ ζ′ (intoU (<→◃ q) (backQ (resQ q e) w))))))
      (sym (trans
        (cong (λ w → outU (<→◃ (ltQ (resQ q e)))
          (intoU (<→◃ (ltQ (resQ q e))) w))
          (out-intoU (<→◃ (suc (ltQ (resQ q e)))) z′))
        (out-intoU (<→◃ (ltQ (resQ q e))) z′)))
      (shift-right e (h ξ′ ζ′ (intoU (<→◃ q) (backQ (resQ q e) z′)))
        (subst
          (λ w → Rq m b (suc a′) (hx ξ ζ (intoU (<→◃ r) z))
            (trQ (s≅ e) (ι zero (h ξ′ ζ′ (intoU (<→◃ q) w)))))
          (trans
            (out-intoU (<→◃ (suc q)) _)
            (cong (backQ (resQ q e))
              (out-intoU (<→◃ (suc (ltQ (resQ q e)))) z′)))
          (rh ξ ξ′ ζ ζ′ d dc z z′ l))))
shift-right (s≅ e) (omk zero z x) h = shift-right (s≅ e) x h
shift-right (l≅ f) (omk (self n) z x) h = shift-right (l≅ f) x h

successor-marker : ∀ {m a a′ φ χ} (e : a ≅ᴵ a′)
  {z : Q m a φ χ} {body : Q m (suc a) φ χ} →
  Rq m (suc a) (suc a) body (ι zero z) →
  Rq m (suc a′) (suc a′) (trQ (s≅ e) body) (ι zero (trQ e z))
successor-marker e {z} h = shift-right e z (R-trʳ (s≅ e) (R-trˡ (s≅ e) h))

shift-back-right : ∀ {m a a′ b φ χ ψ ρ} (e : a′ ≅ᴵ a)
  (z : Q m a ψ ρ) {x : Q m b φ χ} →
  Rq m b (suc a′) x (tr⁻Q (s≅ e) (ι zero z)) →
  Rq m b (suc a′) x (ι zero (tr⁻Q e z))
shift-back-right e z@q0 (rwkˡ rel) = rwkˡ (shift-back-right e z rel)
shift-back-right e z@(qs y) (rwkˡ rel) = rwkˡ (shift-back-right e z rel)
shift-back-right e z@(ql f) (rwkˡ rel) = rwkˡ (shift-back-right e z rel)
shift-back-right e z@(qi ac f) (rwkˡ rel) = rwkˡ (shift-back-right e z rel)
shift-back-right e z@(qŝ c t g) (rwkˡ rel) = rwkˡ (shift-back-right e z rel)
shift-back-right e z@(qĉ c t g o k) (rwkˡ rel) = rwkˡ (shift-back-right e z rel)
shift-back-right e z@(qclo t g) (rwkˡ rel) = rwkˡ (shift-back-right e z rel)
shift-back-right e z@(qcl q ψ s t g) (rwkˡ rel) = rwkˡ (shift-back-right e z rel)
shift-back-right e z@(qwk le lc y) (rwkˡ rel) = rwkˡ (shift-back-right e z rel)
shift-back-right e z@(qΩ↓ q fe ac h) (rwkˡ rel) = rwkˡ (shift-back-right e z rel)
shift-back-right e z@(qΩ fe q h) (rwkˡ rel) = rwkˡ (shift-back-right e z rel)
shift-back-right e q0 rz = rz
shift-back-right e (qs z) (rs sf sc h) = rs sf sc (shift-back-right e z h)
shift-back-right e (ql f) (rl h) = rl (λ n → shift-back-right e (f n) (h n))
shift-back-right e (qi ac f) (ri ej h) = ri ej (λ x y d → shift-back-right e (f y) (h x y d))
shift-back-right e (qŝ c t g) (rŝ ec h hg) = rŝ ec (shift-back-right e t h)
  (λ η ee η′ e′ d → shift-back-right e (g η′ e′) (hg η ee η′ e′ d))
shift-back-right e (qĉ c t g o h) (rĉ ec st sg ro rh) = rĉ ec st sg
  (shift-back-right e o ro)
  (λ η ee η′ e′ d → shift-back-right e (h η′ e′) (rh η ee η′ e′ d))
shift-back-right e (qclo t g) (rclo sf h hg) = rclo sf (shift-back-right e t h)
  (λ η η′ d → shift-back-right e (g η′) (hg η η′ d))
shift-back-right e (qcl q ψ s t g) (rcl eqn sf h hg) = rcl eqn sf (shift-back-right e t h)
  (λ η η′ d → shift-back-right e (g η′) (hg η η′ d))
shift-back-right e (qwk le lc z) (rwkʳ h) = rwkʳ (shift-back-right e z h)
shift-back-right e (qΩ↓ q fe ac h) (rΩ↓ eqn ek sf sc rh) = rΩ↓ eqn ek sf sc
  (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → shift-back-right e (h ξ′ ζ′ (intoV q z′))
    (rh ξ ξ′ ζ ζ′ d dc dc′ z z′ l))
shift-back-right {m} {a′ = a′} {b} e (qΩ fe q h)
  (rΩ {r = r} {h = hx} ek sf sc rh) = rΩ ek sf sc
  (λ ξ ξ′ ζ ζ′ d dc z z′ l →
    subst
      (λ w → Rq m b (suc a′) (hx ξ ζ (intoU (<→◃ r) z))
        (ι zero (tr⁻Q e (h ξ′ ζ′ (intoU (<→◃ q) (backQ (res⁻Q q e) w))))))
      (sym (trans
        (cong (λ w → outU (<→◃ (ltQ (res⁻Q q e)))
          (intoU (<→◃ (ltQ (res⁻Q q e))) w))
          (out-intoU (<→◃ (suc (ltQ (res⁻Q q e)))) z′))
        (out-intoU (<→◃ (ltQ (res⁻Q q e))) z′)))
      (shift-back-right e (h ξ′ ζ′ (intoU (<→◃ q) (backQ (res⁻Q q e) z′)))
        (subst
          (λ w → Rq m b (suc a′) (hx ξ ζ (intoU (<→◃ r) z))
            (tr⁻Q (s≅ e) (ι zero (h ξ′ ζ′ (intoU (<→◃ q) w)))))
          (trans
            (out-intoU (<→◃ (suc q)) _)
            (cong (backQ (res⁻Q q e))
              (out-intoU (<→◃ (suc (ltQ (res⁻Q q e)))) z′)))
          (rh ξ ξ′ ζ ζ′ d dc z z′ l))))
shift-back-right (s≅ e) (omk zero z x) h = shift-back-right (s≅ e) x h
shift-back-right (l≅ f) (omk (self n) z x) h = shift-back-right (l≅ f) x h

successor-marker-back : ∀ {m a a′ φ χ} (e : a ≅ᴵ a′)
  {z : Q m a′ φ χ} {body : Q m (suc a′) φ χ} →
  Rq m (suc a′) (suc a′) body (ι zero z) →
  Rq m (suc a) (suc a) (tr⁻Q (s≅ e) body) (ι zero (tr⁻Q e z))
successor-marker-back e {z} h = shift-back-right e z
  (R-tr⁻ʳ (s≅ e) (R-tr⁻ˡ (s≅ e) h))
```
