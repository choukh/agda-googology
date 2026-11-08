# 保留节点的旧代表元无关读回

旧via可选目标层中的另一字面代表元。先在native实际along种类上
构造Read，再用原分支的显式自相关和ψ-≅比较两个完整Ω节点；
不要求两条旧路径相等，也不假定任意原分支保持同形。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedKeepNode where
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf using (F; module C)
open import OCF.Lean.GeneralOmegaCountableNextCapturePointIf using (point-observe)
import OCF.Align.Level as L
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height; index-bound)
open import OCF.Align.GeneralOmegaCountableTypedIf
open import OCF.Align.GeneralOmegaCountableTypedClass
open import OCF.Align.GeneralOmegaCountableTypedKeepCoord

module Image {j ℓ target : L.Ordᴵ} (q : j L.<ᴵ ℓ)
  (f : L.U j (L.<→◃ q) → L.Ordᶜ ℓ)
  (eval : L.Ordᶜ ℓ → L.Ordᶜ target) where
  image : ∀ {k} → j L.≅ᴵ k → k L.<ᴵ target → L.Ordᶜ target
  image E r = L.limᵢ r (λ y → eval (f (L.into (L.<→◃ q) (L.tr⁻ E (L.out (L.<→◃ r) y)))))

  congruent : L.limᵢ q f L.≅ L.limᵢ q f →
    (∀ {a b} → a L.≅ b → eval a L.≅ eval b) →
    ∀ {k k′} (E : j L.≅ᴵ k) (E′ : j L.≅ᴵ k′) r r′ → image E r L.≅ image E′ r′
  congruent (L.lᵢ≅ self h) ev E E′ r r′ = L.lᵢ≅
    (L.≅ᴵ-trans (L.≅ᴵ-sym E) E′) (λ x y d →
      subst₂ (λ u v → eval (f (L.into (L.<→◃ q) (L.tr⁻ E u))) L.≅
                           eval (f (L.into (L.<→◃ q) (L.tr⁻ E′ v))))
        (sym (L.out-into (L.<→◃ r) x)) (sym (L.out-into (L.<→◃ r′) y))
        (ev (h _ _ (L.≅→R (L.<→◃ q)
          (L.tr⁻-≅ E (L.≅-tr⁻ E′ (L.R→≅ (L.<→◃ r) d)))))))

keep-read : ∀ B (lB : LgB B) t (ht : hs t ⊲ B)
  {ℓ} (σ : L.Simᴵ ℓ (height B lB)) (κ : K (F B))
  (q : rank B lB κ L.<ᴵ ℓ)
  {f : L.U (rank B lB κ) (L.<→◃ q) → L.Ordᶜ ℓ}
  {g : E (F B) κ → HB (F B)}
  {i pi encode} (cl : ClassLink B lB κ (C.nw i pi encode))
  (p : hs i ⊲ t) →
  L.limᵢ q f L.≅ L.limᵢ q f →
  (∀ x e → Coord B lB κ x e →
    Read t (lgB⊲ ht tt lB) (canonical t (lgB⊲ ht tt lB))
      (L.ψ (index-bound lB ht) σ (f (L.into (L.<→◃ q) x)))
      (point-observe B lB t (⊲ᴮ-tr (hsuc hself) ht) (g e))) →
  ∀ {j′} (E : rank B lB κ L.≅ᴵ j′) (r : j′ L.<ᴵ height t (lgB⊲ ht tt lB)) →
  Read t (lgB⊲ ht tt lB) (canonical t (lgB⊲ ht tt lB))
    (Image.image q f (L.ψ (index-bound lB ht) σ) E r)
    (hΩ (C.along p) (λ e → point-observe B lB t (⊲ᴮ-tr (hsuc hself) ht) (g (encode (C.frA p e)))))
keep-read B lB t ht σ κ q {f} {g} cl p self ih E r = rc
  (Image.congruent q f eval self (L.ψ-≅ (L.≅ᴵ-refl _)) E E′ r r′)
  (ro (C.along p) r′ refl
    (Image.congruent q f eval self (L.ψ-≅ (L.≅ᴵ-refl _)) E′ E′ r′ r′)
    (λ x e c → subst
      (λ u → Read t lt (canonical t lt)
        (eval (f (L.into (L.<→◃ q) (L.tr⁻ E′ u))))
        (point-observe B lB t (⊲ᴮ-tr (hsuc hself) ht) (g (_))))
      (sym (L.out-into (L.<→◃ r′) x))
      (ih _ _ (keep-move cl lt p E′ c))))
  where
  lt = lgB⊲ ht tt lB
  eval = L.ψ (index-bound lB ht) σ
  E′ = keep-shape cl lt p
  r′ = bound t lt (C.along p)
```
