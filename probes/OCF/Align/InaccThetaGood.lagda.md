# 全部 $\theta$ 的证书: 遗传的好树 (底座)

> 底座, 不含记号. 结论写在 [InaccTheta](InaccTheta.lagda.md). `Good` 是 [Uniform](Uniform.lagda.md) §6 的 `Good₊` 在 `Lv` 上的版本. **分支只在好输入上单调**: 第 0 层的好输入是 `Aℓ`, 第 $\ge1$ 层的好输入是好且自相似的树. 这就是 "$\theta=3$ 用分支单调代替 `Aℓ`" 的一般形式.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.InaccThetaGood where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; Low; Dn; DnT; at; down; outL; intoL; outD; intoD; Tree; limᵢ; up; Ω; toLv;
   Sim; σ-id; ι; _∘σ_; add; _+_; iter; Verdict; pen; rise)
open import OCF.Align.InaccFloorTree using (Sib; Mode; upM; verdict; chM)
open import OCF.Align.InaccFloorBase using (Aℓ; em; ≅→⊑ᴵ; ≺→⊑ᴵ)
open import OCF.Align.InaccThetaObs using (BL; b0; b1; module Core)
open import OCF.Align.Level using
  (Ordᴵ; _<ᴵ_; _≅ᴵ_; _⊑ᴵ_; _≺ᴵ_; via; zero; suc; lim; z≅; s≅; l≅; z⊑; s⊑; l⊑; <ᴵ-dec)
```

## §1 第 0 层: `Aℓ` 有向

有序性全在 `Aℓ` 上: `<ᴵ-dec` 给比较, `em-mono` 把它变成观测前序. 字面的 $a<^\mathsf{I}b$ 在第 0 层足以给 $a+1\sqsubseteq^\mathsf{o}b$, 因为观测里没有 $\psi_0$ 式的链, 第 0 层没有节点.

```agda
module Good (S : Sib) (ℓ : Ordᴵ) (one : suc zero <ᴵ ℓ) (B₀ : Ordᴸ zero → Set) (a⊆b : ∀ x → Aℓ ℓ zero x → B₀ x) where
  open Core S ℓ one B₀ a⊆b public

  ≅→Eq : ∀ {a b} → a ≅ᴵ b → Eq zero (em a) (em b)
  ≅→Eq z≅     = z≃
  ≅→Eq (s≅ e) = s≃ (≅→Eq e)
  ≅→Eq (l≅ h) = l≃ (λ n → ≅→Eq (h n))

  em< : ∀ {a a′ b} → a ≅ᴵ a′ → a′ <ᴵ b → em (suc a) ⊑ᵒ em b
  em< e zero      = ≃→⊑ᵒ (s≃ (≅→Eq e))
  em< e (suc q)   = suc-r (em< e q)
  em< e (lim n q) = lim-r n (em< e q)

  em-mono : ∀ {a b} → a ⊑ᴵ b → em a ⊑ᵒ em b
  em-mono {b = b} z⊑ = zero-l (eq₀ (em b))
  em-mono (s⊑ e q)   = em< e q
  em-mono (l⊑ k)     = lim-l (λ n → em-mono (k n))

  A-dir : ∀ x y → A zero x → A zero y → Σ (Ordᴸ zero) λ z → A zero z × x ⊑ᵒ z × y ⊑ᵒ z
  A-dir _ _ (a , pa , refl) (b , pb , refl) with <ᴵ-dec pa pb
  ... | injᵃ r = em b , (b , pb , refl) , em-mono (≺→⊑ᴵ r) , ≃→⊑ᵒ (eq₀ (em b))
  ... | injᵇ r = em a , (a , pa , refl) , ≃→⊑ᵒ (eq₀ (em a)) , em-mono (≺→⊑ᴵ r)
  ... | injᶜ e = em b , (b , pb , refl) , em-mono (≅→⊑ᴵ e) , ≃→⊑ᵒ (eq₀ (em b))
```

## §2 好树

`gi`: 分支在好输入上好, 在好输入上单调, 起点是好输入, 起点处的分支不低于 1. 没有 `Aℓ` 以外的第 0 层条件, 也没有第 $\ge1$ 层的有向性. 第 $\ge1$ 层只有链要走, 而链由 `chain-step` 自己单调.

```agda
  data Good₊ (k : Lv) (GL : (r : Pre k) → Ordᴸ (at k r) → Set) (GD : (d : Dn k) → Ordᴸ (down k d) → Set) : Ordᴸ k → Set where
    gz : Good₊ k GL GD Tree.zero
    gs : ∀ {a} → Good₊ k GL GD a → Good₊ k GL GD (Tree.suc a)
    gl : ∀ {h : ℕ → Ordᴸ k} → (∀ n → Good₊ k GL GD (h n)) → (∀ n → h n ⊑ᵒ h (suc n)) → Good₊ k GL GD (Tree.lim h)
    gi : ∀ {r} {f : Low k r → Ordᴸ k} →
         (∀ z → GL r z → Good₊ k GL GD (f (intoL k r z))) →
         (∀ z z′ → GL r z → GL r z′ → z ⊑ᵒ z′ → f (intoL k r z) ⊑ᵒ f (intoL k r z′)) →
         GL r (Ω (at k r)) →
         Ω zero ⊑ᵒ f (intoL k r (Ω (at k r))) →
         Good₊ k GL GD (limᵢ r f)
    gu : ∀ {d} {x : DnT k d} → DB k d → GD d (outD k d x) → Good₊ k GL GD (up d x)

  GoodT : (k : Lv) → Ordᴸ k → Set
  GLo : (k : Lv) (r : Pre k) → Ordᴸ (at k r) → Set
  GDn : (k : Lv) (d : Dn k) → Ordᴸ (down k d) → Set
  Gi : (j : Lv) → Ordᴸ j → Set

  GoodT k = Good₊ k (GLo k) (GDn k)

  GLo (suc k)    (inj₁ _)        z = Gi k z
  GLo (suc k)    (inj₂ r)        z = GLo k r z
  GLo (lim f)    (n , r)         z = GLo (f n) r z
  GLo (limᴼ k g) (inj₁ (inj₁ _)) z = Gi k z
  GLo (limᴼ k g) (inj₁ (inj₂ r)) z = GLo k r z
  GLo (limᴼ k g) (inj₂ (x , r))  z = GLo (g x) r z

  GDn (suc k)    _ z = GoodT k z
  GDn (lim f)    n z = GoodT (f n) z
  GDn (limᴼ k g) x z = GoodT (g x) z

  Gi zero         z = A zero z
  Gi (suc j)      z = GoodT (suc j) z × Eq (suc j) z z
  Gi (lim f)      z = GoodT (lim f) z × Eq (lim f) z z
  Gi (limᴼ j g)   z = GoodT (limᴼ j g) z × Eq (limᴼ j g) z z

  L→Gi : ∀ k r {z} → GLo k r z → Gi (at k r) z
  L→Gi (suc k)    (inj₁ _)        d = d
  L→Gi (suc k)    (inj₂ r)        d = L→Gi k r d
  L→Gi (lim f)    (n , r)         d = L→Gi (f n) r d
  L→Gi (limᴼ k g) (inj₁ (inj₁ _)) d = d
  L→Gi (limᴼ k g) (inj₁ (inj₂ r)) d = L→Gi k r d
  L→Gi (limᴼ k g) (inj₂ (x , r))  d = L→Gi (g x) r d

  Gi→L : ∀ k r {z} → Gi (at k r) z → GLo k r z
  Gi→L (suc k)    (inj₁ _)        d = d
  Gi→L (suc k)    (inj₂ r)        d = Gi→L k r d
  Gi→L (lim f)    (n , r)         d = Gi→L (f n) r d
  Gi→L (limᴼ k g) (inj₁ (inj₁ _)) d = d
  Gi→L (limᴼ k g) (inj₁ (inj₂ r)) d = Gi→L k r d
  Gi→L (limᴼ k g) (inj₂ (x , r))  d = Gi→L (g x) r d

  Gi-sub : ∀ {a b} (e : a ≡ b) {z : Ordᴸ a} → Gi a z → Gi b (subst Ordᴸ e z)
  Gi-sub refl d = d

  GiΩ-sub : ∀ {a b} (e : a ≡ b) → Gi b (Ω b) → Gi a (Ω a)
  GiΩ-sub refl d = d

  ⊑ᵒ-sub : ∀ {a b} (e : a ≡ b) {z z′ : Ordᴸ a} → z ⊑ᵒ z′ → subst Ordᴸ e z ⊑ᵒ subst Ordᴸ e z′
  ⊑ᵒ-sub refl p = p

  em-good : ∀ a → GoodT zero (em a)
  em-good zero      = gz
  em-good (suc a)   = gs (em-good a)
  em-good (lim f s) = gl (λ n → em-good (f n)) (λ n → em-mono (s n))

  Gi→G : ∀ j {z} → Gi j z → GoodT j z × Eq j z z
  Gi→G zero {z} (a , _ , refl) = em-good a , eq₀ (em a)
  Gi→G (suc _)    d = d
  Gi→G (lim _)    d = d
  Gi→G (limᴼ _ _) d = d

  G→Gi : ∀ j {z} → (j ≡ zero → ⊥) → GoodT j z → Eq j z z → Gi j z
  G→Gi zero       n _ _ = ⊥-elim (n refl)
  G→Gi (suc _)    n g e = g , e
  G→Gi (lim _)    n g e = g , e
  G→Gi (limᴼ _ _) n g e = g , e

  Gi→Bs : ∀ j {z} → Gi j z → Bs j z
  Gi→Bs zero d = A⊆B zero _ d
  Gi→Bs (suc _)    _ = tt
  Gi→Bs (lim _)    _ = tt
  Gi→Bs (limᴼ _ _) _ = tt

  gi∘ : ∀ {k} {r : Pre k} {g : Ordᴸ (at k r) → Ordᴸ k} →
        (∀ z → GLo k r z → GoodT k (g z)) →
        (∀ z z′ → GLo k r z → GLo k r z′ → z ⊑ᵒ z′ → g z ⊑ᵒ g z′) →
        GLo k r (Ω (at k r)) →
        Ω zero ⊑ᵒ g (Ω (at k r)) →
        GoodT k (limᵢ r (λ y → g (outL k r y)))
  gi∘ {k} {r} {g} hb hm gΩ pos = gi
    (λ z d → subst (λ u → GoodT k (g u)) (sym (out-into k r z)) (hb z d))
    (λ z z′ d d′ p → subst₂ (λ u v → g u ⊑ᵒ g v) (sym (out-into k r z)) (sym (out-into k r z′)) (hm z z′ d d′ p))
    gΩ
    (subst (λ u → Ω zero ⊑ᵒ g u) (sym (out-into k r (Ω (at k r)))) pos)
```

## §3 自相似的反演

```agda
  s-inv : ∀ {k} {a : Ordᴸ k} → Eq k (Tree.suc a) (Tree.suc a) → Eq k a a
  s-inv (s≃ e) = e

  l-inv : ∀ {k} {h : ℕ → Ordᴸ k} → Eq k (Tree.lim h) (Tree.lim h) → ∀ n → Eq k (h n) (h n)
  l-inv (l≃ h) = h

  i-nd : ∀ {k} {r : Pre k} {f : Low k r → Ordᴸ k} → Eq k (limᵢ r f) (limᵢ r f) → AdmB k r × ND k r × LRo k r
  i-nd (i≃ nd nd′ e lr h) = proj₁ nd , nd , lr

  i-self : ∀ {k} {r : Pre k} {f : Low k r → Ordᴸ k} → Eq k (limᵢ r f) (limᵢ r f) →
           ∀ z → Bs (at k r) z → Eq (at k r) z z → Eq k (f (intoL k r z)) (f (intoL k r z))
  i-self {k} {r} (i≃ nd nd′ e lr h) z b d = h z z b b (Eq→R k r d)

  stripL : ∀ k {d} {x : DnT k d} {k′} {b : Ordᴸ k′} → Eq k (up d x) b → Eq (down k d) (outD k d x) b
  stripL (suc k) (uˡ db e) = e
  stripL (lim f) (uˡ db e) = e
  stripL (limᴼ k g) (uˡ db e) = e
  stripL k (uʳ db e) = uʳ db (stripL k e)

  stripR : ∀ k {k′} {d} {y : DnT k′ d} {a : Ordᴸ k} → Eq k a (up d y) → Eq k a (outD k′ d y)
  stripR k (uʳ db e) = e
  stripR (suc k) (uˡ db e) = uˡ db (stripR k e)
  stripR (lim f) (uˡ {d = n} db e) = uˡ db (stripR (f n) e)
  stripR (limᴼ k g) (uˡ {d = x} db e) = uˡ db (stripR (g x) e)

  u-self : ∀ k {d} {x : DnT k d} → Eq k (up d x) (up d x) → Eq (down k d) (outD k d x) (outD k d x)
  u-self k {d} e = stripR (down k d) (stripL k e)
```
