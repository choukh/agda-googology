# 全部 $\theta$ 的证书: 世界 $\omega\cdot2+1$ 里 `S` 不被问到

> 底座, 不含记号. 结论写在 [InaccTheta](InaccTheta.lagda.md). 层号 $\omega+m$ 的链的模式是 `lt` 或 `fin`, 路径比较全在 `suc` 的脊上, 从不跨 `lim` 的分支, 所以 `Sz S` 不出现. `HE` 在世界 $\omega\cdot2+1$ 里是定理, 对**任何** `S`. 第 5 站在这个世界无条件 (`Station5ω2`). 下一步是 $\omega\cdot2+1$ 作节点层: 它的 $\Omega$ 节点的链的目标是 $\omega\cdot2$, 路径落在 `lim` 的不同分支上, `lit` 走 `Sz S`. 这是 `S` 第一次被问到的地方 (手算, 没有写成定理).

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.InaccThetaSpine where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤n⇒m≤1+n; <-irrefl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.InaccTreeBase using (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; at; σ-id; toLv; rise)
open import OCF.Align.InaccFloorTree using (Sib; Mode; lt; natL; chM; asN)
open import OCF.Align.InaccFloorBase using (em; Aℓ; module Rel)
open import OCF.Align.InaccThetaStation using (module St; lt-nat)
open import OCF.Align.InaccThetaNeg using (E; at-natE)
open import OCF.Align.InaccThetaRel using (module Back)
open import OCF.Align.Level using (Ordᴵ; _<ᴵ_; _⊑ᴵ_; zero; suc; lim; natᴵ; ωᴵ; Sim→⊑ᴵ)

spᴵ : ℕ → Ordᴵ
spᴵ zero    = ωᴵ
spᴵ (suc m) = suc (spᴵ m)

sp-step : ∀ m → spᴵ m ⊑ᴵ spᴵ (suc m)
sp-step m = Sim→⊑ᴵ suc

ω2ᴵ : Ordᴵ
ω2ᴵ = lim spᴵ sp-step

one-ω2 : suc zero <ᴵ suc ω2ᴵ
one-ω2 = suc (lim 0 (lim 2 zero))

sp : ℕ → Lv
sp m = E (spᴵ m)

lt-sp : ∀ {a} m → a <ᴵ spᴵ m → (Σ ℕ λ k → a ≡ spᴵ k) ⊎ (Σ ℕ λ k → a ≡ natᴵ k)
lt-sp zero (lim n q) = inj₂ (lt-nat n q)
lt-sp (suc m) zero = inj₁ (m , refl)
lt-sp (suc m) (suc q) = lt-sp m q

cl : ∀ m (r : Pre (sp m)) → (Σ ℕ λ n → at (sp m) r ≡ natL n) ⊎ (Σ ℕ λ m′ → (m′ < m) × at (sp m) r ≡ sp m′)
cl zero (n , r) = inj₁ (at-natE n r)
cl (suc m) (inj₁ _) = inj₂ (m , ≤-refl , refl)
cl (suc m) (inj₂ r) with cl m r
... | inj₁ p = inj₁ p
... | inj₂ (m′ , l , e) = inj₂ (m′ , m≤n⇒m≤1+n l , e)

module Sp (S : Sib) (B₀ : Ordᴸ zero → Set) (a⊆b : ∀ x → Aℓ (suc ω2ᴵ) zero x → B₀ x) where
  open St S (suc ω2ᴵ) one-ω2 B₀ a⊆b hiding (E)

  sp≈ : ∀ m m′ → sp m ≈ᴮ sp m′ → m ≡ m′
  sp≈ zero    zero     _      = refl
  sp≈ (suc m) (suc m′) (s≈ e) = cong suc (sp≈ m m′ e)

  nat≉sp : ∀ n m → natL n ≈ᴮ sp m → ⊥
  nat≉sp zero    zero    ()
  nat≉sp zero    (suc m) ()
  nat≉sp (suc n) zero    ()
  nat≉sp (suc n) (suc m) (s≈ e) = nat≉sp n m e

  ≡≉sp : ∀ {c} n m → c ≡ natL n → c ≈ᴮ sp m → ⊥
  ≡≉sp n m refl e = nat≉sp n m e

  rise-sp : ∀ i m′ m → i ≡ sp m′ → m′ ≤ m → ∀ (r : Pre i) → at i r ≈ᴮ sp m → ⊥
  rise-sp _ m′ m refl le r e with cl m′ r
  ... | inj₁ (n , e′) = ≡≉sp n m e′ e
  ... | inj₂ (m″ , l , e′) with sp≈ m″ m (subst (_≈ᴮ sp m) e′ e)
  ...   | refl = <-irrefl refl (≤-trans l le)

  okLt : ∀ m (q : Pre (sp m)) m′ → at (sp m) q ≡ sp m′ → OK (sp m) (lt q refl)
  okLt zero (n , r) m′ e with at-natE n r
  ... | k , e′ = ⊥-elim (≡≉sp k m′ e′ (subst (_≈ᴮ sp m′) (sym e) (≈ᴮ-refl (sp m′))))
  okLt (suc m) (inj₁ _) m′ e =
    (λ { (inj₁ _) _ → cvr (λ r d e′ → rise-sp (sp m) m m refl ≤-refl r e′)
       ; (inj₂ r) d → cvp r refl d })
    , okBel (sp m) (σ-id (sp m)) (sd-id {sp m})
  okLt (suc m) (inj₂ q) m′ e with cl m q
  ... | inj₁ (n , e′) = ⊥-elim (≡≉sp n m′ e′ (subst (_≈ᴮ sp m′) (sym e) (≈ᴮ-refl (sp m′))))
  ... | inj₂ (m″ , l , e′) with sp≈ m″ m′ (subst (_≈ᴮ sp m′) (trans (sym e) e′) (≈ᴮ-refl (sp m′)))
  ...   | refl =
    (λ { (inj₁ _) _ → cvr (λ r d e″ → rise-sp (at (sp m) q) m″ m e′ (≤-trans (m≤n⇒m≤1+n ≤-refl) l) r e″)
       ; (inj₂ r) d → okV (sp m) (lt q refl) (okLt m q m″ e′) r d })
    , okLt m q m″ e′

  zt-sp : ∀ m → Zt (sp m)
  zt-sp zero    = ((1 , inj₁ tt) , tt , refl) , zpL 0 (zpU zpZ)
  zt-sp (suc m) with zt-sp m
  ... | (r , d , e) , _ = (inj₂ r , d , e) , zpI

  okSp : ∀ m q m′ → at (sp m) q ≡ sp m′ → OK (sp m) (chM (sp m) q)
  okSp m q m′ e with asN (at (sp m) q)
  ... | just (n , e′) = okF (sp m) n e′
  ... | nothing       = okLt m q m′ e

  ch-sp : ∀ m q → ChOK (sp m) q
  ch-sp m q with cl m q
  ... | inj₁ (n , e) = ch-fin (sp m) q n e
  ... | inj₂ (m′ , _ , e) = inj₂ (okSp m q m′ e , subst Zt (sym e) (zt-sp m′))

  lvT-sp : ∀ m → LvT (sp m)
  lvT-sp zero    = (λ q _ → ch-sp zero q) , (λ n → lvt-fin (E (natᴵ n)) (at-natE n))
  lvT-sp (suc m) = (λ q _ → ch-sp (suc m) q) , lvT-sp m

  he-sp : ∀ m → LvG (sp m)
  he-sp m = t→g (sp m) (lvT-sp m)

  he-natE : ∀ n → LvG (E (natᴵ n))
  he-natE n = t→g (E (natᴵ n)) (lvt-fin (E (natᴵ n)) (at-natE n))

  HEω2 : HE
  HEω2 _ (a , zero , refl) = he-sp
  HEω2 _ (a , suc (lim m q) , refl) with lt-sp m q
  ... | inj₁ (k , refl) = he-sp k
  ... | inj₂ (k , refl) = he-natE k

  Station5ω2 : WFᴬ Lv₅
  Station5ω2 = Station5 HEω2

  cmp₅ω2 : (p q : Pre Lv₅) → Adm Lv₅ p → Adm Lv₅ q → Tri (at Lv₅ p) (at Lv₅ q)
  cmp₅ω2 = cmp₅ HEω2

  -- 边界是精确的: $\omega\cdot2+1$ 作节点层就要 `S` 在 $(\omega,\omega+1)$ 上正确
  frontier : LvG (E (suc ω2ᴵ)) → CV (S (sp 0) (sp 1))
  frontier (_ , w) with proj₁ w (2 , inj₁ tt) tt
  ... | inj₂ (ok , _) = proj₁ ok (1 , inj₁ tt) tt

-- `S = rise` 过不了边界
module NoRise where
  S₀ : Sib
  S₀ _ _ = rise
  open St S₀ (suc ω2ᴵ) one-ω2 (λ _ → ⊤) (λ _ _ → tt) hiding (E)
  open Sp S₀ (λ _ → ⊤) (λ _ _ → tt) using (frontier)

  ¬frontier : LvG (E (suc ω2ᴵ)) → ⊥
  ¬frontier w with frontier w
  ... | cvr k = k (inj₁ tt) tt (≈ᴮ-refl (sp 0))
```

## 回到原来的 `Rel`

叶子取 `⊤`: 第 5 站在世界 $\omega\cdot2+1$ 的证书与比较落在原来的 `Rel (Aℓ ℓ)` 上, 对任何 `S`.

```agda
module OrigSp (S : Sib) where
  open Sp S (λ _ → ⊤) (λ _ _ → tt) using (Station5ω2)
  open St S (suc ω2ᴵ) one-ω2 (λ _ → ⊤) (λ _ _ → tt) using (Lv₅; A⊆B)

  Station5ᴼ : Rel.WFᴬ (Aℓ (suc ω2ᴵ)) Lv₅
  Station5ᴼ = Back.WF′→WFᴬ (Aℓ (suc ω2ᴵ)) A⊆B Lv₅ Station5ω2

  cmp₅ᴼ : (p q : Pre Lv₅) → Rel.Adm (Aℓ (suc ω2ᴵ)) Lv₅ p → Rel.Adm (Aℓ (suc ω2ᴵ)) Lv₅ q →
          Rel.Tri (Aℓ (suc ω2ᴵ)) (at Lv₅ p) (at Lv₅ q)
  cmp₅ᴼ = Rel.<-decᴬ (Aℓ (suc ω2ᴵ)) Lv₅ Station5ᴼ
```
