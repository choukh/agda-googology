# 结构关系, 第九轮 (一): 走法把树世界处的 `Lg` 等式交给分支

> 入口见 [StrRel9](StrRel9.lagda.md). 与 `StrRel7Walk.GoC` 逐字相同, 只改一处: 分支比较 `br` 多收两条等式 $l_c \equiv$ `lg⊲ q (lW s)` (两边各一条). 走法在 `aP` 一句本来就带着这条等式 (`e-suc bV (lW s) e`), 只是以前没有交出去. 新语义 (`StrRel9Snd`) 要它: 带前段的 `nw` 规则把前段的对齐 (`genᴾ`) 与运行路径拼接 (`cat`), 拼接点的 `Lg` 必须一致.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel9Walk where

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
open import OCF.Align.StrRel7Walk using (cohWlk)
```

## 1 走法

```agda
module GoD (s s′ : Env) (cA : CA (act s)) {V V′} (u : Bk V) (u′ : Bk V′) (R : F.St (W s) → F.St (W s′) → Set)
           (chL : ∀ {Y Y′} → R Y Y′ → Ch Y)
           (adv : ∀ {Y Y′} (Δ : F.Df (W s)) (Δ′ : F.Df (W s′)) → R Y Y′ → OA s s′ Δ Δ′ → OA s s Δ Δ → R (Y F.⊕ Δ) (Y′ F.⊕ Δ′))
           (br : ∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → c ≤ c′ → Adm c c′ (W s) (W s′) →
                 ∀ (q : c ⊲ W s) (q′ : c′ ⊲ W s′) → Al (W s) (W s′) q (lW s) q′ (lW s′) →
                 lc ≡ lg⊲ q (lW s) → lc′ ≡ lg⊲ q′ (lW s′) →
                 ∀ w w′ Y Y′ → R Y Y′ → OA s s′ (Rn s (u p lc) q w Y) (Rn s′ (u′ p′ lc′) q′ w′ Y′)) where

  AlW = Al (W s) (W s′)

  walkᵈ : ∀ {a b a′ b′} {p : a ⊲ b} {lb : Lg b} {p′ : a′ ⊲ b′} {lb′ : Lg b′} → AlW p lb p′ lb′ →
          ∀ ap ap′ (bV : b ⊲ W s) (bV′ : b′ ⊲ W s′) → AlW bV (lW s) bV′ (lW s′) → lb ≡ lg⊲ bV (lW s) → lb′ ≡ lg⊲ bV′ (lW s′) →
          ∀ co co′ Y Y′ → R Y Y′ → OA s s′ (Wlk s u p ap lb bV co Y) (Wlk s′ u′ p′ ap′ lb′ bV′ co′ Y′)
  walkᵈ (aS p′ lb′) ap ap′ bV bV′ hb e e′ co co′ Y Y′ r τ τ′ = z0
  walkᵈ (aR H) ap ap′ bV bV′ hb e e′ co co′ Y Y′ r τ τ′ =
    pr (walkᵈ H ap ap′ bV (⊲-tr (C.suc C.self) bV′) (rfx (C.suc C.self) hb) e (e-suc bV′ (lW s′) e′) co co′ Y Y′ r τ τ′)
  walkᵈ (aRL {n′ = n′} H) ap ap′ bV bV′ hb e e′ co co′ Y Y′ r τ τ′ =
    pr (walkᵈ H ap ap′ bV (⊲-tr (C.lim n′ C.self) bV′) (rfx (C.lim n′ C.self) hb) e (e-lim bV′ (lW s′) n′ e′) co co′ Y Y′ r τ τ′)
  walkᵈ (aP {c = c} {c′ = c′} {p = p} {lc} {p′} {lc′} H c≤ ad) ap ap′ bV bV′ hb e e′ co co′ Y Y′ r τ τ′ =
    sq (O τ τ′) (br (⊲-tr ap p) (⊲-tr ap′ p′) lc lc′ c≤ ad q q′ hq (e-suc bV (lW s) e) (e-suc bV′ (lW s′) e′)
             (co ⨾ Cut u c p ap lc q) (co′ ⨾ Cut u′ c′ p′ ap′ lc′ q′) (Y F.⊕ Δ) (Y′ F.⊕ Δ′) (adv Δ Δ′ r O (cohWlk s cA u _ p ap lc q co Y (chL r))) τ τ′)
    where
    q = ⊲-tr (C.suc C.self) bV
    q′ = ⊲-tr (C.suc C.self) bV′
    hq = fcs c≤ ad hb
    Δ = Wlk s u p ap lc q co Y
    Δ′ = Wlk s′ u′ p′ ap′ lc′ q′ co′ Y′
    O = walkᵈ H ap ap′ q q′ hq (e-suc bV (lW s) e) (e-suc bV′ (lW s′) e′) co co′ Y Y′ r
  walkᵈ (aL {f = f} {n} {f′ = f′} {n′} {p} {p′} {stp} {wl} {stp′} {wl′} H G) ap ap′ bV bV′ hb e e′ co co′ Y Y′ r τ τ′ =
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
    O = walkᵈ H ap ap′ (fV n) (fV′ n′) (hF 0) (e-lim bV (lW s) n e) (e-lim bV′ (lW s′) n′ e′) co co′ Y Y′ r
    Rp = F.WRp ac₁ u f stp wl p ap fV (lW s) (ll s) (act s) (co ⨾ Cut u (f n) p ap (wl n) (fV n)) (Y F.⊕ Δ)
    Rp′ = F.WRp ac₁ u′ f′ stp′ wl′ p′ ap′ fV′ (lW s′) (ll s′) (act s′) (co′ ⨾ Cut u′ (f′ n′) p′ ap′ (wl′ n′) (fV′ n′)) (Y′ F.⊕ Δ′)
    Sg : ℕ → F.Df (W s)
    Sg m = Wlk s u (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV (suc (m + n))) (proj₁ (Rp m)) (proj₂ (Rp m))
    Sg′ : ℕ → F.Df (W s′)
    Sg′ m = Wlk s′ u′ (stp′ (m + n′)) (⊲-tr ap′ (tailP f′ stp′ p′ m)) (wl′ (suc (m + n′))) (fV′ (suc (m + n′))) (proj₁ (Rp′ m)) (proj₂ (Rp′ m))
    st : ∀ m → R (proj₂ (Rp m)) (proj₂ (Rp′ m))
    go : ∀ m → OA s s′ (Sg m) (Sg′ m) × R (proj₂ (Rp m)) (proj₂ (Rp′ m))
    go m = walkᵈ (G m) _ _ (fV (suc (m + n))) (fV′ (suc (m + n′))) (hF (suc m))
                 (e-lim bV (lW s) (suc (m + n)) e) (e-lim bV′ (lW s′) (suc (m + n′)) e′) _ _ _ _ (st m) , st m
    st zero = adv Δ Δ′ r O (cohWlk s cA u _ p ap (wl n) (fV n) co Y (chL r))
    st (suc m) = adv (Sg m) (Sg′ m) (st m) (proj₁ (go m))
                     (cohWlk s cA u _ (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV (suc (m + n))) (proj₁ (Rp m)) (proj₂ (Rp m)) (chL (st m)))

  cellᵈ : ∀ {a a′} {p : a ⊲ W s} {p′ : a′ ⊲ W s′} → AlW p (lW s) p′ (lW s′) → ∀ ap ap′ co co′ Y Y′ → R Y Y′ →
          OA s s′ (Wlk s u p ap (lW s) C.self co Y) (Wlk s′ u′ p′ ap′ (lW s′) C.self co′ Y′)
  cellᵈ H ap ap′ co co′ Y Y′ r = walkᵈ H ap ap′ C.self C.self (aS C.self (lW s′)) refl refl co co′ Y Y′ r
```
