# 新旧块的逐层关系: 塔, Λ 与闭项

> 编译定理 (验收用, 无前提): 读出的层号相关 (`↑-L`), 塔各项与 Λ 的层号相关 (`tw-L`, `Λ-L`), 证据相关 (`tw-E`, `Λ-E`); 闭项相关 `twᶜ-R : ∀ n → RelT zero F.zero (twᶜ n) (F.twᶜ n)`, `EBOᶜ-R`, 层号 2 的 Ω 树的折叠 `two-R`.
> 证据里 ℕ 极限层号的相邻路径由树的推导读出 (`◃→⊑-V`), 这是推导进关系的用处. 不否定什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBRTw where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiLegFold as F
open import OCF.Lean.YiBRRel
open import OCF.Lean.YiBRLem
open import OCF.Lean.YiBROps
open import OCF.Lean.YiBRFold
```

## 读出的层号

```agda
⊕-L : ∀ {a a′ b b′} → RelL a a′ → RelL b b′ → RelL (a ⊕ b) (a′ F.⊕ b′)
⊕-L ra lz         = ra
⊕-L ra (lS rb)    = lS (⊕-L ra rb)
⊕-L ra (lL rb)    = lL (λ n → ⊕-L ra (rb n))
⊕-L ra (lΩ rk rh) = lΩ rk (λ c c′ r → ⊕-L ra (rh c c′ r))

↑-L : ∀ {k k′} → RelL k k′ → {x : Tr k} {x′ : F.Tr k′} → RelT k k′ x x′ → RelL (↑ k x) (F.↑ k′ x′)
↑-L rk {x = zero}    iz             = lz
↑-L rk {x = suc x}   (is r)         = lS (↑-L rk r)
↑-L rk {x = lim f a} (il (rf , _))  = lL (λ n → ↑-L rk (rf n))
↑-L rk {x = Ω p g} {F.Ω p′ g′} (iw (rp , rg)) =
  lΩ (at-L rk p p′ rp) (λ c c′ rc → ↑-L rk (rg _ _ (fromBr-R rk p p′ rp rc)))
↑-L (lS r)     {x = up x c y e} (iu (rx , (ry , _)))        = ⊕-L (↑-L (lS r) rx) (↑-L r ry)
↑-L (lL r)     {x = up x n y e} (iu (rx , (refl , ry , _))) = ⊕-L (↑-L (lL r) rx) (↑-L (r n) ry)
↑-L (lΩ rk rh) {x = up x c y e} {F.up _ c′ _ _} (iu (rx , (rc , ry , _))) = ⊕-L (↑-L (lΩ rk rh) rx) (↑-L (rh c c′ rc) ry)

tw-L : (n : ℕ) → RelL (tw n) (F.tw n)
tw-L zero    = lz
tw-L (suc n) = lΩ (tw-L n) (λ c c′ r → ⊕-L (tw-L n) (↑-L (tw-L n) r))

Λ-L : RelL Λ F.Λ
Λ-L = lL tw-L
```

## 路径的读出

```agda
lift-W : ∀ {a a′ b b′} → RelL b b′ → RelW (lift {true} a b) (F.lift a′ b′)
lift-W lz         = wself
lift-W (lS r)     = winuS (lift-W r)
lift-W (lL r)     = winuL (λ n → lift-W (r n))
lift-W (lΩ rk rh) = winuΩ (λ c c′ rc → lift-W (rh c c′ rc))

lift-V : ∀ {a a′ b b′} → RelL b b′ → RelV (lift {false} a b) (F.⊑lift a′ b′)
lift-V lz         = vself
lift-V (lS r)     = vinuS (lift-V r)
lift-V (lL r)     = vinuL (λ n → lift-V (r n))
lift-V (lΩ rk rh) = vinuΩ (λ c c′ rc → lift-V (rh c c′ rc))

⊕⊑-V : ∀ {a a′ u u₁ u′ u₁′} {v : u ⊑ u₁} {v′ : F._⊑_ u′ u₁′} → RelV v v′ → RelV (⊕⊑ a v) (F.⊕⊑ a′ v′)
⊕⊑-V vself         = vself
⊕⊑-V (vincS r)     = vincS (⊕⊑-V r)
⊕⊑-V (vinuS r)     = vinuS (⊕⊑-V r)
⊕⊑-V (vincL n r)   = vincL n (⊕⊑-V r)
⊕⊑-V (vinuL rs)    = vinuL (λ n → ⊕⊑-V (rs n))
⊕⊑-V (vincΩ rc r)  = vincΩ rc (⊕⊑-V r)
⊕⊑-V (vinuΩ rs)    = vinuΩ (λ c c′ r → ⊕⊑-V (rs c c′ r))

wk-V : ∀ {j ℓ j′ ℓ′} {v : j ⊑ ℓ} {v′ : F._⊑_ j′ ℓ′} → RelV v v′ → RelW (wk v) (F.⊑→≤ v′)
wk-V vself         = wself
wk-V (vincS r)     = wincS (wk-V r)
wk-V (vinuS r)     = winuS (wk-V r)
wk-V (vincL n r)   = wincL n (wk-V r)
wk-V (vinuL rs)    = winuL (λ n → wk-V (rs n))
wk-V (vincΩ rc r)  = wincΩ rc (wk-V r)
wk-V (vinuΩ rs)    = winuΩ (λ c c′ r → wk-V (rs c c′ r))

∙V-R : ∀ {i j ℓ i′ j′ ℓ′} {w : i ⊑ j} {w′ : F._⊑_ i′ j′} {v : j ⊑ ℓ} {v′ : F._⊑_ j′ ℓ′}
     → RelV w w′ → RelV v v′ → RelV (w ∙ v) (F.⊑-trans w′ v′)
∙V-R rw vself         = rw
∙V-R rw (vincS rv)    = vincS (∙V-R rw rv)
∙V-R rw (vinuS rv)    = vinuS (∙V-R rw rv)
∙V-R rw (vincL n rv)  = vincL n (∙V-R rw rv)
∙V-R rw (vinuL rvs)   = vinuL (λ n → ∙V-R rw (rvs n))
∙V-R rw (vincΩ rc rv) = vincΩ rc (∙V-R rw rv)
∙V-R rw (vinuΩ rvs)   = vinuΩ (λ c c′ r → ∙V-R rw (rvs c c′ r))

RelV-substʳ : ∀ {j ℓ} {v : j ⊑ ℓ} {A : Set} (X : A → F.L) (Y : F.L) {t₁ t₂ : A} (e : t₁ ≡ t₂) {v′ : F._⊑_ (X t₁) Y}
            → RelV v v′ → RelV v (subst (λ t → F._⊑_ (X t) Y) e v′)
RelV-substʳ X Y refl r = r

◃→⊑-V : ∀ {k k′} → RelL k k′ → {x y : Tr k} {x′ y′ : F.Tr k′} {d : k ⊢ x ◃ y} {d′ : F._⊢_◃_ k′ x′ y′}
      → RelD k k′ d d′ → RelV (◃→⊑ k d) (F.◃→⊑ k′ d′)
◃→⊑-V rk {d = ◃s}   ds = vincS vself
◃→⊑-V rk {d = ◃l n} dl = vincL n vself
◃→⊑-V {k} {k′} rk {d = ◃w {p = p} {g = g}} {d′ = F.◃w {p = p′} {g = g′}} (dw _) =
  RelV-substʳ (λ z → F.↑ k′ (g′ z)) (F.Ωₗ (F.at k′ p′) (λ c → F.↑ k′ (g′ (F.fromBr k′ p′ c)))) (sym (F.br0≡ k′ p′))
    (vincΩ {c = zero} {c′ = F.zero} iz vself)
◃→⊑-V (lS r)     {d = ◃u x c y e} (du (rx , (ry , _)))        = lift-V (↑-L r ry)
◃→⊑-V (lL r)     {d = ◃u x n y e} (du (rx , (refl , ry , _))) = lift-V (↑-L (r n) ry)
◃→⊑-V (lΩ rk rh) {d = ◃u x c y e} {d′ = F.◃u _ c′ _ _} (du (rx , (rc , ry , _))) = lift-V (↑-L (rh c c′ rc) ry)
◃→⊑-V (lS r)     {d = ◃c x c d} (dc (rx , rd))          = ⊕⊑-V (◃→⊑-V r rd)
◃→⊑-V (lL r)     {d = ◃c x n d} (dc (rx , (refl , rd))) = ⊕⊑-V (◃→⊑-V (r n) rd)
◃→⊑-V (lΩ rk rh) {d = ◃c x c d} {d′ = F.◃c _ c′ _} (dc (rx , (rc , rd))) = ⊕⊑-V (◃→⊑-V (rh c c′ rc) rd)
◃→⊑-V rk {d = ◃t d e} (dt (r₁ , r₂)) = ∙V-R (◃→⊑-V rk r₁) (◃→⊑-V rk r₂)
```

## 偏移的证据

精简块的 `OkO a b` 对 F2 的 `EvO a b` 与 `RtP b`.

```agda
data RelEO (a : L) (a′ : F.L) : (b : L) (b′ : F.L) → OkO a b → F.EvO a′ b′ → F.RtP b′ → Set where
  oz : ∀ {e eo rp} → RelEO a a′ zero F.zero e eo rp
  oS : ∀ {h b′} {e : OkO a (nd sS h)} {eo : F.EvO a′ b′} {rp : F.RtP b′}
     → RelEO a a′ (h tt) b′ (proj₂ e tt) eo rp → RelEO a a′ (nd sS h) (F.suc b′) e eo rp
  oL : ∀ {g g′} {e : OkO a (nd sL g)} {eo : F.EvO a′ (F.lim g′)} {rp : F.RtP (F.lim g′)}
     → ((n : ℕ) → RelV (proj₁ e n) (proj₂ rp n)) → ((n : ℕ) → RelEO a a′ (g n) (g′ n) (proj₂ e n) (eo n) (proj₁ rp n))
     → RelEO a a′ (nd sL g) (F.lim g′) e eo rp
  oΩ : ∀ {k h k′ h′} {e : OkO a (nd (sΩ k) h)} {eo : F.EvO a′ (F.Ωₗ k′ h′)} {rp : F.RtP (F.Ωₗ k′ h′)}
     → RelW (proj₁ (proj₁ e)) (proj₁ eo) → RelE k k′ (proj₂ (proj₁ e)) (proj₁ (proj₂ eo)) (proj₁ rp)
     → ((c : Tr k) (c′ : F.Tr k′) → RelT k k′ c c′ → RelEO a a′ (h c) (h′ c′) (proj₂ e c) (proj₂ (proj₂ eo) c′) (proj₂ rp c′))
     → RelEO a a′ (nd (sΩ k) h) (F.Ωₗ k′ h′) e eo rp

EO→L : ∀ {a a′ b b′ e eo rp} → RelEO a a′ b b′ e eo rp → RelL b b′
EO→L oz           = lz
EO→L (oS r)       = lS (EO→L r)
EO→L (oL _ r)     = lL (λ n → EO→L (r n))
EO→L (oΩ _ rk r)  = lΩ (E→L rk) (λ c c′ rc → EO→L (r c c′ rc))

⊕-E : ∀ {a a′ oa ea ra b b′ e eo rp} → RelE a a′ oa ea ra → RelEO a a′ b b′ e eo rp
    → RelE (a ⊕ b) (a′ F.⊕ b′) (Ok⊕ a b oa e) (F.Ev⊕ a′ b′ ea eo) (F.Rt⊕ a′ b′ ra rp)
⊕-E re oz            = re
⊕-E re (oS r)        = eS (⊕-E re r)
⊕-E re (oL rv r)     = eL (λ n → wk-V (⊕⊑-V (rv n))) (λ n → ⊕-E re (r n))
⊕-E re (oΩ rv rk r)  = eΩ rk (λ c c′ rc → ∙-R rv (lift-W (EO→L (r c c′ rc)))) (λ c c′ rc → ⊕-E re (r c c′ rc))

⊕-EO : ∀ {a a′ b₁ b₁′ e₁ eo₁ rp₁ b₂ b₂′ e₂ eo₂ rp₂} → RelEO a a′ b₁ b₁′ e₁ eo₁ rp₁ → RelEO a a′ b₂ b₂′ e₂ eo₂ rp₂
     → RelEO a a′ (b₁ ⊕ b₂) (b₁′ F.⊕ b₂′) (OkO⊕ a b₁ b₂ e₁ e₂) (F.EvO⊕ a′ b₁′ b₂′ eo₁ eo₂) (F.RtP⊕ b₁′ b₂′ rp₁ rp₂)
⊕-EO r₁ oz           = r₁
⊕-EO r₁ (oS r)       = oS (⊕-EO r₁ r)
⊕-EO r₁ (oL rv r)    = oL (λ n → ⊕⊑-V (rv n)) (λ n → ⊕-EO r₁ (r n))
⊕-EO r₁ (oΩ rv rk r) = oΩ rv rk (λ c c′ rc → ⊕-EO r₁ (r c c′ rc))

↑-EO : ∀ {a a′ k k′ ok ek ρ} → RelE k k′ ok ek ρ → {v : k ≤ a} {v′ : F._≤_ k′ a′} → RelW v v′
     → {x : Tr k} {x′ : F.Tr k′} → RelT k k′ x x′
     → RelEO a a′ (↑ k x) (F.↑ k′ x′) (OkO↑ a k ok v x) (F.EvO↑ a′ k′ ek v′ x′) (F.RtP↑ k′ ρ x′)
↑-EO re rv {x = zero}    iz            = oz
↑-EO re rv {x = suc x}   (is r)        = oS (↑-EO re rv r)
↑-EO re rv {x = lim f a} (il (rf , ra)) = oL (λ n → ◃→⊑-V (E→L re) (ra n)) (λ n → ↑-EO re rv (rf n))
↑-EO re rv {x = Ω p g} {F.Ω p′ g′} (iw (rp , rg)) =
  oΩ (∙-R (posW-R (E→L re) p p′ rp) rv) (E-at re p p′ rp) (λ c c′ rc → ↑-EO re rv (rg _ _ (fromBr-R (E→L re) p p′ rp rc)))
↑-EO (eS re)        rv {x = up x c y e} (iu (rx , (ry , _))) =
  ⊕-EO (↑-EO (eS re) rv rx) (↑-EO re (∙-R (wincS wself) rv) ry)
↑-EO (eL rr re)     rv {x = up x n y e} (iu (rx , (refl , ry , _))) =
  ⊕-EO (↑-EO (eL rr re) rv rx) (↑-EO (re n) (∙-R (wincL n wself) rv) ry)
↑-EO (eΩ rk rwc rc) rv {x = up x c y e} {F.up _ c′ _ _} (iu (rx , (rcc , ry , _))) =
  ⊕-EO (↑-EO (eΩ rk rwc rc) rv rx) (↑-EO (rc c c′ rcc) (∙-R (wincΩ rcc wself) rv) ry)
```

## 塔, Λ, 闭项

```agda
tw-E : (n : ℕ) → RelE (tw n) (F.tw n) (Ok-tw n) (F.Ev-tw n) (F.Rt-tw n)
tw-E zero    = ez
tw-E (suc n) = eΩ (tw-E n) (λ c c′ r → lift-W (↑-L (tw-L n) r)) (λ c c′ r → ⊕-E (tw-E n) (↑-EO (tw-E n) wself r))

Λ-E : RelE Λ F.Λ Ok-Λ F.Ev-Λ F.Rt-Λ
Λ-E = eL (λ n → wink wself) tw-E

ψ₀-R : ∀ {ℓ ℓ′ o ε ρ} → RelE ℓ ℓ′ o ε ρ → {x : Tr ℓ} {x′ : F.Tr ℓ′} → RelT ℓ ℓ′ x x′
     → RelT zero F.zero (proj₁ (ψ₀ ℓ o x)) (F.ψ₀ ℓ′ ε ρ x′)
ψ₀-R re rx = proj₁ (A re (B₀ _) (F.B₀ _) (B₀-R (E→L re)) (Ωt zero) (Ωt-R lz) (Ωn-R lz) rx)

twᶜ-R : (n : ℕ) → RelT zero F.zero (twᶜ n) (F.twᶜ n)
twᶜ-R n = ψ₀-R (tw-E n) (Ωt-R (tw-L n))

EBOᶜ-R : RelT zero F.zero EBOᶜ F.EBOᶜ
EBOᶜ-R = ψ₀-R Λ-E (Ωt-R Λ-L)

two : L
two = nd sS (λ _ → nd sS (λ _ → zero))

Ok-two : Ok two
Ok-two = tt , λ _ → tt , λ _ → tt

two-R : RelT zero F.zero (proj₁ (ψ₀ two Ok-two (proj₁ (Ωt two)))) (F.ψ₀ (F.suc (F.suc F.zero)) tt tt (F.Ωt (F.suc (F.suc F.zero))))
two-R = ψ₀-R (eS (eS ez)) (Ωt-R (lS (lS lz)))
```
