# 两种种类的单调 (七): 第 0 层的核与链

> 入口 [TpPort](TpPort.lagda.md). 不含记号. **生成文件**: 由 `probes/Survey/scripts/tpport/mk_tpport.py` 从 [MonoPort6Zero](MonoPort6Zero.lagda.md) 逐字节可重生成 (公共变换在同目录的 `tpgen.py`). 公共变换只改: 世界的类型与序 (`A`, `_⊲_` 换成两种种类的 `Wd₂`, `_≤ʷ_`; `C.self`, `C.⊲-tr` 换成 `≤rf`, `≤tr`; `Lg` 换成 `LgW₂`), 高度的类型 (`H` 换成 `Ht`, `LgH` 换成 `LgB`, `hΩ g` 换成 `hΩ κ g`), 模块参数多一个 `oΛ` (第 1 层是实例在一切世界里的第一位置, 两种种类的折叠要它), 数据树多一个构造子 `nμ` (每个 `nκ` 的空子句后加一句), `Step` 换名 `Stp`. 证明逐句不变. `preL≡` 由原文从 `MonoPort4Zero` 导入改为就地写出 (四行, 同原文).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`, 不改树、折叠、合法性.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.HtTowerTy using (HB; hz; hs; _⊲[_]_; LgB)
open import OCF.Align.HtTowerFTree using (Ht; Wd₂; LgW₂; AccY)
import OCF.Align.TpPortGen as Gen
module OCF.Align.TpPortZero (Λ : Ht) (lΛ : LgB Λ) (oΛ : ∀ {w} → hs hz ⊲[ w ] Λ) {W : Wd₂} (lW : LgW₂ W) (t₀ : hz ⊲[ W ] Λ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤l; l≤; ≤-refl)
open import OCF.Align.HtTowerFTree using (D; n0; n1; _⨾_; nl; ni; nκ; nμ; nw; sum; pt; ≤rf; ≤tr) renaming (_≤_ to _≤ʷ_)
open import OCF.Align.TpPortDef using (_⊑₀_; z0; o1; sq; lm; wl; wr; pr; tr; u0l; u0r; u1l; u1r; al; al′; ar; ar′; refl₀; nwd; nwd′) renaming (preL to preLˢ)


open Gen Λ lΛ oΛ lW t₀ using (module P; o₀; preL; module Core; OutLaws; PreLaw)

-- 两个 preL 字面相同 (原文从 MonoPort4Zero 导入)
preL≡ : ∀ {V} (d : ℕ → D hz V) k → preLˢ d k ≡ preL d k
preL≡ d zero = refl
preL≡ d (suc k) = cong (λ t → t ⨾ d k) (preL≡ d k)

module B (O : OutLaws) (Lpre : PreLaw O) (ac : AccY hz) (ll : hz ⊲[ W ] Λ)
  (prj : ∀ {Δ Δ′} → OutLaws._≼_ O Δ Δ′ → P.yc Δ (P.tg ≤rf ll lW) ⊑₀ P.yc Δ′ (P.tg ≤rf ll lW)) where
  module K = Core O hz ac ll Wd₂ (λ V → V) (λ V → V ≤ʷ W) (λ q → q) (λ w w′ → w ⊑₀ w′) (λ x x′ → x ⊑₀ x′)
  open K public

  cl₀ : CxLaws
  cl₀ = record
    { cxL = λ { (cx _) → cx (refl₀ _) }
    ; cxR = λ { (cx _) → cx (refl₀ _) }
    ; cx⨾ = λ { q q′ (cx hw) (inn hx) → cx (sq hw (wl (wr hx))) }
    ; cx0ˡ = λ { q (cx hw) → cx (tr (sq hw (wl z0)) (u1l (refl₀ _))) }
    ; cx0ʳ = λ { q (cx hw) → cx (tr (u1r (refl₀ _)) (sq hw (wr z0))) }
    ; cxas = λ { {x = x} {y} q (cx hw) _ _ → cx (ar′ (sq hw (nwd x y))) }
    ; cxas′ = λ { {x = x} {y} q (cx hw) _ _ → cx (al (sq hw (nwd′ x y))) }
    ; cxpre = λ { {w = w} {d = d} q q′ n (cx h) (inn he) → cx (tr (ar′ (sq (refl₀ w) (nwd (preL d n) (d n)))) (sq h (wl (wr he)))) }
    ; cxlim = λ { {w = w} {d = d} q n (cx h) (inn hd) → cx (tr (sq h (wl (wr hd))) (al (sq (refl₀ w) (nwd′ (preL d n) (d n))))) }
    }

  open Steps cl₀ public

  nwl : ∀ {Aᵢ Aⱼ : Act} {V₀ V V₂} {p : V₀ ≤ʷ V} {x : D hz V₀} {z : D hz V₂} → Sem Aᵢ Aⱼ x z → Sem Aᵢ Aⱼ (nw p x) z
  nwl {p = p} h q = h (≤tr p q)

  nwr : ∀ {Aᵢ Aⱼ : Act} {V₀ V V₁} {p : V₀ ≤ʷ V} {x : D hz V₀} {z : D hz V₁} → Sem Aᵢ Aⱼ z x → Sem Aᵢ Aⱼ z (nw p x)
  nwr {p = p} h q q′ = h q (≤tr p q′)

  rO : ∀ (A₀ : Act) → HA A₀ A₀ → ∀ {V} (x : D hz V) → Sem A₀ A₀ x x
  rO A₀ h n0 = n0S
  rO A₀ h n1 = n1S h
  rO A₀ h (x ⨾ y) = ⨾S (rO A₀ h x) (rO A₀ h x) (rO A₀ h x) (inn (refl₀ x)) (rO A₀ h y)
  rO A₀ h (nl d) = nlS (λ n → rO A₀ h (d n)) (λ n → rO A₀ h (d n)) (λ n → rO A₀ h (d n)) (λ n → inn (refl₀ (d n)))
  rO A₀ h (ni () u)
  rO A₀ h (nκ () u)
  rO A₀ h (nμ () u)
  rO A₀ h (nw p x) = nwl (nwr (rO A₀ h x))

  Sem₀ : ∀ {V₁ V₂} → D hz V₁ → D hz V₂ → Set
  Sem₀ x x′ = ∀ (Aᵢ Aⱼ : Act) → HA Aᵢ Aᵢ → HA Aⱼ Aⱼ → HA Aᵢ Aⱼ → Sem Aᵢ Aⱼ x x′

  snd₀ : ∀ {V₁ V₂} {x : D hz V₁} {x′ : D hz V₂} → x ⊑₀ x′ → Sem₀ x x′
  snd₀ z0 Aᵢ Aⱼ hi hj hij = n0S
  snd₀ o1 Aᵢ Aⱼ hi hj hij = n1S hij
  snd₀ (sq {x = x} {x′ = x′} hx hy) Aᵢ Aⱼ hi hj hij =
    ⨾S (rO Aᵢ hi x) (rO Aⱼ hj x′) (snd₀ hx Aᵢ Aⱼ hi hj hij) (inn hx) (snd₀ hy Aᵢ Aⱼ hi hj hij)
  snd₀ (lm {d = d} {d′} hd) Aᵢ Aⱼ hi hj hij =
    nlS (λ n → rO Aᵢ hi (d n)) (λ n → rO Aⱼ hj (d′ n)) (λ n → snd₀ (hd n) Aᵢ Aⱼ hi hj hij) (λ n → inn (hd n))
  snd₀ (wl h) Aᵢ Aⱼ hi hj hij = nwl (snd₀ h Aᵢ Aⱼ hi hj hij)
  snd₀ (wr h) Aᵢ Aⱼ hi hj hij = nwr (snd₀ h Aᵢ Aⱼ hi hj hij)
  snd₀ (pr {x = x} {x′} {d} {d′} hx hd k) Aᵢ Aⱼ hi hj hij =
    subst (λ t → Sem Aᵢ Aⱼ (x ⨾ t) (x′ ⨾ nl d′)) (sym (preL≡ d k))
      (preS Lpre (rO Aᵢ hi x) (rO Aⱼ hj x′) (λ n → rO Aᵢ hi (d n)) (λ n → rO Aⱼ hj (d′ n))
            (snd₀ hx Aᵢ Aⱼ hi hj hij) (inn hx) (λ n → snd₀ (hd n) Aᵢ Aⱼ hi hj hij) (λ n → inn (hd n)) k)
  snd₀ (tr h h′) Aᵢ Aⱼ hi hj hij = trS (snd₀ h Aᵢ Aᵢ hi hi hi) (snd₀ h′ Aᵢ Aⱼ hi hj hij)
  snd₀ (u0l h) Aᵢ Aⱼ hi hj hij = u0ˡS (snd₀ h Aᵢ Aⱼ hi hj hij)
  snd₀ (u0r h) Aᵢ Aⱼ hi hj hij = u0ʳS (snd₀ h Aᵢ Aⱼ hi hj hij)
  snd₀ (u1l h) Aᵢ Aⱼ hi hj hij = u1ˡS (snd₀ h Aᵢ Aⱼ hi hj hij)
  snd₀ (u1r h) Aᵢ Aⱼ hi hj hij = u1ʳS (snd₀ h Aᵢ Aⱼ hi hj hij)
  snd₀ (al {x = x} {y} {z} h) Aᵢ Aⱼ hi hj hij =
    asˡS (rO Aᵢ hi x) (rO Aᵢ hi y) (rO Aᵢ hi z) (inn (refl₀ x)) (inn (refl₀ y)) (snd₀ h Aᵢ Aⱼ hi hj hij)
  snd₀ (al′ {x = x} {y} {z} h) Aᵢ Aⱼ hi hj hij =
    asˡ′S (rO Aᵢ hi x) (rO Aᵢ hi y) (rO Aᵢ hi z) (inn (refl₀ x)) (inn (refl₀ y)) (snd₀ h Aᵢ Aⱼ hi hj hij)
  snd₀ (ar {x = x} {y} {z} h) Aᵢ Aⱼ hi hj hij =
    asʳS (rO Aⱼ hj x) (rO Aⱼ hj y) (rO Aⱼ hj z) (inn (refl₀ x)) (inn (refl₀ y)) (snd₀ h Aᵢ Aⱼ hi hj hij)
  snd₀ (ar′ {x = x} {y} {z} h) Aᵢ Aⱼ hi hj hij =
    asʳ′S (rO Aⱼ hj x) (rO Aⱼ hj y) (rO Aⱼ hj z) (inn (refl₀ x)) (inn (refl₀ y)) (snd₀ h Aᵢ Aⱼ hi hj hij)
```
```agda
  module Chain (Aᵢ Aⱼ : Act) (hi : HA Aᵢ Aᵢ) (hj : HA Aⱼ Aⱼ) (hij : HA Aᵢ Aⱼ) where
    CC : Act → P.St W → ℕ → D hz W × (D hz W × P.St W)
    CC A₂ Y = P.Chn ac ll lW A₂ Y

    outs : Act → P.St W → ℕ → P.Df W
    outs A₂ Y n = Run A₂ (proj₁ (proj₂ (CC A₂ Y n))) ≤rf (proj₁ (CC A₂ Y n)) (proj₂ (proj₂ (CC A₂ Y n)))

    chain₀ : ∀ (Y Y′ : P.St W) b b′ → Good Y → Good Y′ → SRel Y Y′ → b ≤ b′ →
             (sum b (nl (λ n → o₀ (outs Aᵢ Y n))) ≤ sum b′ (nl (λ n → o₀ (outs Aⱼ Y′ n)))) × (∀ n → outs Aᵢ Y n ≼ outs Aⱼ Y′ n)
    chain₀ Y Y′ b b′ g g′ s cb =
      l≤ (λ n → ≤l n (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (go n))))))) , (λ n → proj₂ (h n azero azero z≤))
      where
      c  = λ n → proj₁ (CC Aᵢ Y n)
      c′ = λ n → proj₁ (CC Aⱼ Y′ n)
      δ  = λ n → proj₁ (proj₂ (CC Aᵢ Y n))
      δ′ = λ n → proj₁ (proj₂ (CC Aⱼ Y′ n))
      Yn  = λ n → proj₂ (proj₂ (CC Aᵢ Y n))
      Yn′ = λ n → proj₂ (proj₂ (CC Aⱼ Y′ n))
      sg  = λ n → o₀ (outs Aᵢ Y n)
      sg′ = λ n → o₀ (outs Aⱼ Y′ n)
      go : ∀ n → (c n ⊑₀ c′ n) × ((δ n ⊑₀ δ′ n) × (Good (Yn n) × (Good (Yn′ n) ×
                 (SRel (Yn n) (Yn′ n) × (pt b sg n ≤ pt b′ sg′ n)))))
      h : ∀ n e₁ e₂ → e₁ ≤ e₂ → Obs e₁ e₂ (outs Aᵢ Y n) (outs Aⱼ Y′ n)
      h n e₁ e₂ eb = let (gc , (gd , (gy , (gy′ , (sy , _))))) = go n in
        snd₀ gd Aᵢ Aⱼ hi hj hij ≤rf ≤rf (c n) (c′ n) e₁ e₂ (Yn n) (Yn′ n) (cx gc) gy gy′ sy eb
      go zero = z0 , (prj (proj₂ s) , (g , (g′ , (s , cb))))
      go (suc n) =
        let (gc , (gd , (gy , (gy′ , (sy , gb))))) = go n
        in sq gc gd ,
           (prj (proj₂ (h n azero azero z≤)) ,
            (G⊕ {Yn n} gy (rf (rO Aᵢ hi (δ n)) ≤rf (c n) (Yn n) (cx (refl₀ _)) gy) ,
             (G⊕ {Yn′ n} gy′ (rf (rO Aⱼ hj (δ′ n)) ≤rf (c′ n) (Yn′ n) (cx (refl₀ _)) gy′) ,
              (S⊕ gy gy′ sy (h n _ _ (proj₁ sy)) ,
               proj₁ (h n _ _ gb)))))
```
