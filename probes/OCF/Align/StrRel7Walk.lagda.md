# 结构关系, 第七轮: 带左边自洽的走法

> 入口见 [StrRel7](StrRel7.lagda.md). `StrRel5All.GoA` 的走法, 状态关系 `R` 多带一条: 左边的状态自洽 (`chL`). 推进状态时, 除了两边输出相关, 还给出**左边这一段输出自洽** (`cohWlk`, 由 [StrRel7Coh](StrRel7Coh.lagda.md) 的 `coh₁` 逐位置得出). 证明逐字沿用 `walkᴬ`, 只在三处推进状态的地方多传一个自洽证明.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel7Walk where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; Tg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.SumOneTree using (D; _⨾_; Cut; tailP)
import OCF.Align.SumOneClosed as F
open import OCF.Align.KValTree using (Bk)
open import OCF.Align.KValSem using (ac₁)
open import OCF.Align.KNestAdm using (Adm)
open import OCF.Align.StrRel4Walk using (Al; aS; aP; aR; aRL; aL)
open import OCF.Align.StrRel4Pr using (_⊑ᴾ_; z0; sq; lm; pr)
open import OCF.Align.StrRel5Walk using (Env; W; lW; ll; act; Rn; Wlk)
open import OCF.Align.StrRel5Suf using (rfx; fcs; fcl; e-suc; e-lim)
open import OCF.Align.StrRel5All using (OA)
open import OCF.Align.StrRel5Nest using (advA)
open import OCF.Align.StrRel7Coh using (Ch; CA; coh₁)
```

## 1 走法的输出自洽

对路径的终点归纳, 与 `Walk` 同形: 每个位置的分支由 `coh₁` 给出自洽, 状态由 `advA` 推进.

```agda
cohWlk : ∀ (s : Env) → CA (act s) → ∀ {V} (u : Bk V) b {a} (p : a ⊲ b) (ap : V ⊲ a) (lb : Lg b) (bV : b ⊲ W s) co Y → Ch Y →
         OA s s (Wlk s u p ap lb bV co Y) (Wlk s u p ap lb bV co Y)
cohWlk s cA u b C.self ap lb bV co Y r τ τ′ = z0
cohWlk s cA u (asuc c) (C.suc p) ap lb bV co Y r τ τ′ =
  sq (O τ τ′) (coh₁ ac₁ (u (⊲-tr ap p) lb) q (lW s) (ll s) (act s) cA _ (Y F.⊕ Δ) (advA {Y = Y} {Y′ = Y} Δ Δ r O) τ τ′)
  where
  q = ⊲-tr (C.suc C.self) bV
  Δ = Wlk s u p ap lb q co Y
  O = cohWlk s cA u c p ap lb q co Y r
cohWlk s cA u (alim f) (C.lim n p) ap (stp , wf) bV co Y r τ τ′ =
  sq (O τ τ′) (lm (λ m → cohWlk s cA u (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wf (suc (m + n)))
                           (fV (suc (m + n))) (proj₁ (Rp m)) (proj₂ (Rp m)) (st m) τ τ′))
  where
  fV : ∀ m → f m ⊲ W s
  fV m = ⊲-tr (C.lim m C.self) bV
  Δ = Wlk s u p ap (wf n) (fV n) co Y
  O = cohWlk s cA u (f n) p ap (wf n) (fV n) co Y r
  Rp = F.WRp ac₁ u f stp wf p ap fV (lW s) (ll s) (act s) (co ⨾ Cut u (f n) p ap (wf n) (fV n)) (Y F.⊕ Δ)
  st : ∀ m → Ch (proj₂ (Rp m))
  st zero = advA {Y = Y} {Y′ = Y} Δ Δ r O
  st (suc m) = advA {Y = proj₂ (Rp m)} {Y′ = proj₂ (Rp m)} Sg Sg (st m)
                    (cohWlk s cA u (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wf (suc (m + n)))
                            (fV (suc (m + n))) (proj₁ (Rp m)) (proj₂ (Rp m)) (st m))
    where Sg = Wlk s u (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wf (suc (m + n))) (fV (suc (m + n))) (proj₁ (Rp m)) (proj₂ (Rp m))
```

## 2 走法的比较, 左边带自洽

```agda
module GoC (s s′ : Env) (cA : CA (act s)) {V V′} (u : Bk V) (u′ : Bk V′) (R : F.St (W s) → F.St (W s′) → Set)
           (chL : ∀ {Y Y′} → R Y Y′ → Ch Y)
           (adv : ∀ {Y Y′} (Δ : F.Df (W s)) (Δ′ : F.Df (W s′)) → R Y Y′ → OA s s′ Δ Δ′ → OA s s Δ Δ → R (Y F.⊕ Δ) (Y′ F.⊕ Δ′))
           (br : ∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → c ≤ c′ → Adm c c′ (W s) (W s′) →
                 ∀ (q : c ⊲ W s) (q′ : c′ ⊲ W s′) → Al (W s) (W s′) q (lW s) q′ (lW s′) →
                 ∀ w w′ Y Y′ → R Y Y′ → OA s s′ (Rn s (u p lc) q w Y) (Rn s′ (u′ p′ lc′) q′ w′ Y′)) where

  AlW = Al (W s) (W s′)

  walkᶜ : ∀ {a b a′ b′} {p : a ⊲ b} {lb : Lg b} {p′ : a′ ⊲ b′} {lb′ : Lg b′} → AlW p lb p′ lb′ →
          ∀ ap ap′ (bV : b ⊲ W s) (bV′ : b′ ⊲ W s′) → AlW bV (lW s) bV′ (lW s′) → lb ≡ lg⊲ bV (lW s) → lb′ ≡ lg⊲ bV′ (lW s′) →
          ∀ co co′ Y Y′ → R Y Y′ → OA s s′ (Wlk s u p ap lb bV co Y) (Wlk s′ u′ p′ ap′ lb′ bV′ co′ Y′)
  walkᶜ (aS p′ lb′) ap ap′ bV bV′ hb e e′ co co′ Y Y′ r τ τ′ = z0
  walkᶜ (aR H) ap ap′ bV bV′ hb e e′ co co′ Y Y′ r τ τ′ =
    pr (walkᶜ H ap ap′ bV (⊲-tr (C.suc C.self) bV′) (rfx (C.suc C.self) hb) e (e-suc bV′ (lW s′) e′) co co′ Y Y′ r τ τ′)
  walkᶜ (aRL {n′ = n′} H) ap ap′ bV bV′ hb e e′ co co′ Y Y′ r τ τ′ =
    pr (walkᶜ H ap ap′ bV (⊲-tr (C.lim n′ C.self) bV′) (rfx (C.lim n′ C.self) hb) e (e-lim bV′ (lW s′) n′ e′) co co′ Y Y′ r τ τ′)
  walkᶜ (aP {c = c} {c′ = c′} {p = p} {lc} {p′} {lc′} H c≤ ad) ap ap′ bV bV′ hb e e′ co co′ Y Y′ r τ τ′ =
    sq (O τ τ′) (br (⊲-tr ap p) (⊲-tr ap′ p′) lc lc′ c≤ ad q q′ hq
             (co ⨾ Cut u c p ap lc q) (co′ ⨾ Cut u′ c′ p′ ap′ lc′ q′) (Y F.⊕ Δ) (Y′ F.⊕ Δ′) (adv Δ Δ′ r O (cohWlk s cA u _ p ap lc q co Y (chL r))) τ τ′)
    where
    q = ⊲-tr (C.suc C.self) bV
    q′ = ⊲-tr (C.suc C.self) bV′
    hq = fcs c≤ ad hb
    Δ = Wlk s u p ap lc q co Y
    Δ′ = Wlk s′ u′ p′ ap′ lc′ q′ co′ Y′
    O = walkᶜ H ap ap′ q q′ hq (e-suc bV (lW s) e) (e-suc bV′ (lW s′) e′) co co′ Y Y′ r
  walkᶜ (aL {f = f} {n} {f′ = f′} {n′} {p} {p′} {stp} {wl} {stp′} {wl′} H G) ap ap′ bV bV′ hb e e′ co co′ Y Y′ r τ τ′ =
    sq (O τ τ′) (lm (λ m → proj₁ (go m) τ τ′))
    where
    fV : ∀ m → f m ⊲ W s
    fV m = ⊲-tr (C.lim m C.self) bV
    fV′ : ∀ m → f′ m ⊲ W s′
    fV′ m = ⊲-tr (C.lim m C.self) bV′
    Gs : ∀ k → (∀ j → AlW (stp (j + k + n)) (wl (suc (j + k + n))) (stp′ (j + k + n′)) (wl′ (suc (j + k + n′)))) →
         ∀ j → AlW (stp (j + (k + n))) (wl (suc (j + (k + n)))) (stp′ (j + (k + n′))) (wl′ (suc (j + (k + n′))))
    Gs k g j = subst₂ (λ x x′ → AlW (stp x) (wl (suc x)) (stp′ x′) (wl′ (suc x′))) (+-assoc j k n) (+-assoc j k n′) (g j)
    hF : ∀ k → AlW (fV (k + n)) (lW s) (fV′ (k + n′)) (lW s′)
    hF k = fcl {N = k + n} {N′ = k + n′} hb (sym e) (sym e′) (Gs k (λ j → G (j + k)))
    Δ = Wlk s u p ap (wl n) (fV n) co Y
    Δ′ = Wlk s′ u′ p′ ap′ (wl′ n′) (fV′ n′) co′ Y′
    O = walkᶜ H ap ap′ (fV n) (fV′ n′) (hF 0) (e-lim bV (lW s) n e) (e-lim bV′ (lW s′) n′ e′) co co′ Y Y′ r
    Rp = F.WRp ac₁ u f stp wl p ap fV (lW s) (ll s) (act s) (co ⨾ Cut u (f n) p ap (wl n) (fV n)) (Y F.⊕ Δ)
    Rp′ = F.WRp ac₁ u′ f′ stp′ wl′ p′ ap′ fV′ (lW s′) (ll s′) (act s′) (co′ ⨾ Cut u′ (f′ n′) p′ ap′ (wl′ n′) (fV′ n′)) (Y′ F.⊕ Δ′)
    Sg : ℕ → F.Df (W s)
    Sg m = Wlk s u (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV (suc (m + n))) (proj₁ (Rp m)) (proj₂ (Rp m))
    Sg′ : ℕ → F.Df (W s′)
    Sg′ m = Wlk s′ u′ (stp′ (m + n′)) (⊲-tr ap′ (tailP f′ stp′ p′ m)) (wl′ (suc (m + n′))) (fV′ (suc (m + n′))) (proj₁ (Rp′ m)) (proj₂ (Rp′ m))
    st : ∀ m → R (proj₂ (Rp m)) (proj₂ (Rp′ m))
    go : ∀ m → OA s s′ (Sg m) (Sg′ m) × R (proj₂ (Rp m)) (proj₂ (Rp′ m))
    go m = walkᶜ (G m) _ _ (fV (suc (m + n))) (fV′ (suc (m + n′))) (hF (suc m))
                 (e-lim bV (lW s) (suc (m + n)) e) (e-lim bV′ (lW s′) (suc (m + n′)) e′) _ _ _ _ (st m) , st m
    st zero = adv Δ Δ′ r O (cohWlk s cA u _ p ap (wl n) (fV n) co Y (chL r))
    st (suc m) = adv (Sg m) (Sg′ m) (st m) (proj₁ (go m))
                     (cohWlk s cA u _ (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV (suc (m + n))) (proj₁ (Rp m)) (proj₂ (Rp m)) (chL (st m)))

  cellᶜ : ∀ {a a′} {p : a ⊲ W s} {p′ : a′ ⊲ W s′} → AlW p (lW s) p′ (lW s′) → ∀ ap ap′ co co′ Y Y′ → R Y Y′ →
          OA s s′ (Wlk s u p ap (lW s) C.self co Y) (Wlk s′ u′ p′ ap′ (lW s′) C.self co′ Y′)
  cellᶜ H ap ap′ co co′ Y Y′ r = walkᶜ H ap ap′ C.self C.self (aS C.self (lW s′)) refl refl co co′ Y Y′ r
```
