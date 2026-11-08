# 全部原Native地板的相对支持

证明对所有c:HB U成立，包括任意Ω分支和原NegRank后继组件；未把c
限制成有限自然数或纯坐标。输入仍是原flL(prefix⊕upL k c)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexSupportFloor where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (LH; Lv; ls; lz)
open import OCF.Lean.LHRecLay using (ΩL; _⊕L_; upL)
open import OCF.Lean.LHRecFl using (flL; ΣF; cxI; gcF)
open import OCF.Lean.LHRecLeg using (module New)
open import OCF.Lean.HigherIndexClassIf using (U; Native; prefix)
open import OCF.Lean.HigherIndexSupportIf
open import OCF.Lean.HigherIndexSupportClosure

base-part : ∀ β d → d ⊲ β → ∀ (a : HB (Lv (ΩL lz ⊕L upL lz d))) →
  Support hz β (ι (inj₂ d) a)
base-part β d bd hz = tt
base-part β d bd (hs a) = base-part β d bd a
base-part β d bd (hl f) = λ n → base-part β d bd (f n)
base-part β d bd (hΩ κ f) = bd , λ e ad → base-part β d bd (f e)

base-θ = New.θ (cxI lz (λ d → ΩL lz ⊕L upL lz d))
  (gcF (λ d → ι (inj₂ d) (flL (ΩL lz ⊕L upL lz d))))
base-θ-support : ∀ β e → e ⊲ β → Support hz β (base-θ e)
base-θ-support β hz p = tt
base-θ-support β (hs e) p = add hz β _ _
  (base-θ-support β e (⊲ᴮ-tr (hsuc hself) p))
  (base-part β e (⊲ᴮ-tr (hsuc hself) p) (flL (ΩL lz ⊕L upL lz e)))
base-θ-support β (hl f) p = λ n → base-θ-support β (f n) (⊲ᴮ-tr (hlim n hself) p)
base-θ-support β (hΩ () f) p

lim-part : ∀ f n β (a : HB (Native (f n))) → Support (f n) β a →
  Support (hl f) β (ι n a)
lim-part f n β hz s = tt
lim-part f n β (hs a) s = lim-part f n β a s
lim-part f n β (hl h) s = λ j → lim-part f n β (h j) (s j)
lim-part f n β (hΩ κ h) (ev , s) = ev , λ e ad →
  lim-part f n (next (f n) κ β e ad) (h e) (s e ad)

omega-part : ∀ f d β → d ⊲ β → ∀ (a : HB (Native (f d))) → Support (f d) β a →
  Support (hΩ (inj₂ tt) f) β (ι (inj₂ d) a)
omega-part f d β bd hz s = tt
omega-part f d β bd (hs a) s = omega-part f d β bd a s
omega-part f d β bd (hl h) s = λ n → omega-part f d β bd (h n) (s n)
omega-part f d β bd (hΩ κ h) (ev , s) = (bd , ev) , λ e ad →
  omega-part f d (next (f d) κ β e ad) (⊲ᴮ-tr bd (next-up (f d) κ β e ad))
    (h e) (s e ad)

level : HB U → LH
level c = prefix ⊕L upL (ls lz) c
floor : ∀ c → HB (Native c)
floor c = flL (level c)

sum-support : ∀ f β → (∀ n → Support (f n) β (floor (f n))) → ∀ n →
  Support (hl f) β (ΣF (λ n → level (f n)) n)
sum-support f β ih zero = lim-part f zero β _ (ih zero)
sum-support f β ih (suc n) = add (hl f) β _ _ (sum-support f β ih n)
  (lim-part f (suc n) β _ (ih (suc n)))

omega-θ : ∀ f → Cd → HB (Native (hΩ (inj₂ tt) f))
omega-θ f = New.θ (cxI lz (λ d → level (f d)))
  (gcF (λ d → ι (inj₂ d) (floor (f d))))
omega-θ-support : ∀ f → (∀ d β → Support (f d) β (floor (f d))) →
  ∀ β e → e ⊲ β → Support (hΩ (inj₂ tt) f) β (omega-θ f e)
omega-θ-support f ih β hz p = tt
omega-θ-support f ih β (hs e) p = add (hΩ (inj₂ tt) f) β _ _
  (omega-θ-support f ih β e (⊲ᴮ-tr (hsuc hself) p))
  (omega-part f e β (⊲ᴮ-tr (hsuc hself) p) _ (ih e β))
omega-θ-support f ih β (hl h) p = λ n →
  omega-θ-support f ih β (h n) (⊲ᴮ-tr (hlim n hself) p)
omega-θ-support f ih β (hΩ () h) p

floor-support : ∀ c β → Support c β (floor c)
floor-support hz β = tt , λ e ad → base-θ-support (hs e) e (hsuc hself)
floor-support (hs c) β = tt , λ e ad →
  up-support c (proj₁ ad) e (proj₂ (proj₂ (proj₂ ad)))
floor-support (hl f) β = sum-support f β (λ n → floor-support (f n) β)
floor-support (hΩ (inj₁ ()) f) β
floor-support (hΩ (inj₂ _) f) β = tt , λ e ad →
  omega-θ-support f (λ d β′ → floor-support (f d) β′) (hs e) e (hsuc hself)
```

floor-support是全结构参数的一步定理，不要求c合法、不读标签；准入只在
分支处要求所需的合法未来低界。它证明原地板在这套支持标准内，不证明
旧或新raw折叠已能消费它，更不证明输出合法或值。
