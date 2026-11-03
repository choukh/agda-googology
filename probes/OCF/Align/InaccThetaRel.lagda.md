# 全部 $\theta$ 的证书: 叶子只看可容许分支的相对比较 (底座)

> 底座, 不含记号. 结论写在 [InaccTheta](InaccTheta.lagda.md). 本文是 [InaccFloorBase](InaccFloorBase.lagda.md) §1 的 `Rel` 把叶子 `≈` 换成 `≈ᴮ` 的版本, 证明逐字. `B₀` 取 `⊤` 时回到原来的 `Rel` (`≈ᵀ→≈`, `WF′→WFᴬ`), 所以这里的定理不弱于那里, 只是多一个旋钮.

**为什么要这个旋钮.** `≈` 的 `o≈` 要求在**全部**原始分支上逐点相关. 第 0 层的原始分支可以是任何树, 而证书只看 `A` 里的分支 (`Adm`). 让叶子也只看 `B₀` 里的分支, 证书就不必为不可容许的分支负责. `B₀` 只作用在参数层 0 上: 其余参数层的分支仍是全称的.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccThetaRel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.InaccTreeBase using (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; at)
open import OCF.Align.InaccFloorBase using (_≈_; z≈; s≈; l≈; o≈; module Rel; ≈-refl)
```

## §1 叶子

```agda
module Leaf (B₀ : Ordᴸ zero → Set) where

  Bs : (k : Lv) → Ordᴸ k → Set
  Bs zero       x = B₀ x
  Bs (suc _)    _ = ⊤
  Bs (lim _)    _ = ⊤
  Bs (limᴼ _ _) _ = ⊤

  infix 4 _≈ᴮ_
  data _≈ᴮ_ : Lv → Lv → Set where
    z≈ : zero ≈ᴮ zero
    s≈ : ∀ {a b} → a ≈ᴮ b → suc a ≈ᴮ suc b
    l≈ : ∀ {f g} → (∀ n → f n ≈ᴮ g n) → lim f ≈ᴮ lim g
    o≈ : ∀ {k g g′} → (∀ x → Bs k x → g x ≈ᴮ g′ x) → limᴼ k g ≈ᴮ limᴼ k g′

  ≈ᴮ-refl : ∀ a → a ≈ᴮ a
  ≈ᴮ-refl zero       = z≈
  ≈ᴮ-refl (suc a)    = s≈ (≈ᴮ-refl a)
  ≈ᴮ-refl (lim f)    = l≈ (λ n → ≈ᴮ-refl (f n))
  ≈ᴮ-refl (limᴼ k g) = o≈ (λ x _ → ≈ᴮ-refl (g x))

  ≈ᴮ-sym : ∀ {a b} → a ≈ᴮ b → b ≈ᴮ a
  ≈ᴮ-sym z≈     = z≈
  ≈ᴮ-sym (s≈ e) = s≈ (≈ᴮ-sym e)
  ≈ᴮ-sym (l≈ h) = l≈ (λ n → ≈ᴮ-sym (h n))
  ≈ᴮ-sym (o≈ h) = o≈ (λ x d → ≈ᴮ-sym (h x d))

  ≈ᴮ-trans : ∀ {a b c} → a ≈ᴮ b → b ≈ᴮ c → a ≈ᴮ c
  ≈ᴮ-trans z≈     z≈      = z≈
  ≈ᴮ-trans (s≈ e) (s≈ e′) = s≈ (≈ᴮ-trans e e′)
  ≈ᴮ-trans (l≈ h) (l≈ h′) = l≈ (λ n → ≈ᴮ-trans (h n) (h′ n))
  ≈ᴮ-trans (o≈ h) (o≈ h′) = o≈ (λ x d → ≈ᴮ-trans (h x d) (h′ x d))

  ≈→≈ᴮ : ∀ {a b} → a ≈ b → a ≈ᴮ b
  ≈→≈ᴮ z≈     = z≈
  ≈→≈ᴮ (s≈ e) = s≈ (≈→≈ᴮ e)
  ≈→≈ᴮ (l≈ h) = l≈ (λ n → ≈→≈ᴮ (h n))
  ≈→≈ᴮ (o≈ h) = o≈ (λ x _ → ≈→≈ᴮ (h x))

  -- `Adm` 与原来的 `Rel` 相同
  AdmB : (c : Lv) → Pre c → Set
  AdmB = Rel.Adm Bs

  -- 路径沿 `≈ᴮ` 搬
  path≈ : ∀ {a b} → a ≈ᴮ b → (r : Pre a) → AdmB a r → Σ (Pre b) λ r′ → AdmB b r′ × at a r ≈ᴮ at b r′
  path≈ (s≈ e) (inj₁ _) _ = inj₁ tt , tt , e
  path≈ (s≈ e) (inj₂ r) d with path≈ e r d
  ... | r′ , d′ , e′ = inj₂ r′ , d′ , e′
  path≈ (l≈ h) (n , r) d with path≈ (h n) r d
  ... | r′ , d′ , e′ = (n , r′) , d′ , e′
  path≈ (o≈ {k} h) (inj₁ (inj₁ _)) _ = inj₁ (inj₁ tt) , tt , ≈ᴮ-refl k
  path≈ (o≈ h) (inj₁ (inj₂ r)) d = inj₁ (inj₂ r) , d , ≈ᴮ-refl _
  path≈ (o≈ h) (inj₂ (x , r)) (a , d) with path≈ (h x a) r d
  ... | r′ , d′ , e′ = inj₂ (x , r′) , (a , d′) , e′

  module RelB (A : (k : Lv) → Ordᴸ k → Set) (A⊆B : ∀ k x → A k x → Bs k x) where
    open Rel A public using (Adm)
    open import OCF.Align.InaccTreeBase using (Pre; at)

    record _≺ᴬ_ (a b : Lv) : Set where
      constructor viaᴬ
      field
        pthᴬ : Pre b
        admᴬ : Adm b pthᴬ
        prfᴬ : a ≈ᴮ at b pthᴬ

    _⊑ᴬ_ : Lv → Lv → Set
    a ⊑ᴬ b = (r : Pre a) → Adm a r → at a r ≺ᴬ b

    ≺ᴬ-respˡ : ∀ {a a′ b} → a′ ≈ᴮ a → a ≺ᴬ b → a′ ≺ᴬ b
    ≺ᴬ-respˡ e (viaᴬ r d e′) = viaᴬ r d (≈ᴮ-trans e e′)

    ⊑ᴬ-trans : ∀ {a b c} → a ⊑ᴬ b → b ⊑ᴬ c → a ⊑ᴬ c
    ⊑ᴬ-trans σ τ r d with σ r d
    ... | viaᴬ s ds e = ≺ᴬ-respˡ e (τ s ds)

    ⊑ᴬ-refl : ∀ {a} → a ⊑ᴬ a
    ⊑ᴬ-refl r d = viaᴬ r d (≈ᴮ-refl _)

    ≺⊑ : ∀ {a b c} → a ≺ᴬ b → b ⊑ᴬ c → a ≺ᴬ c
    ≺⊑ (viaᴬ s ds e) τ = ≺ᴬ-respˡ e (τ s ds)

    ≈⊑ : ∀ {a b} → a ≈ᴮ b → a ⊑ᴬ b
    ≈⊑ (s≈ e) (inj₁ _) _ = viaᴬ (inj₁ tt) tt e
    ≈⊑ (s≈ e) (inj₂ r) d with ≈⊑ e r d
    ... | viaᴬ r′ d′ e′ = viaᴬ (inj₂ r′) d′ e′
    ≈⊑ (l≈ h) (n , r) d with ≈⊑ (h n) r d
    ... | viaᴬ r′ d′ e′ = viaᴬ (n , r′) d′ e′
    ≈⊑ (o≈ h) (inj₁ (inj₁ _)) _ = viaᴬ (inj₁ (inj₁ tt)) tt (≈ᴮ-refl _)
    ≈⊑ (o≈ h) (inj₁ (inj₂ r)) d = viaᴬ (inj₁ (inj₂ r)) d (≈ᴮ-refl _)
    ≈⊑ (o≈ {k} h) (inj₂ (x , r)) (a , d) with ≈⊑ (h x (A⊆B k x a)) r d
    ... | viaᴬ r′ d′ e′ = viaᴬ (inj₂ (x , r′)) (a , d′) e′

    ≺ᴬ-respʳ : ∀ {a b b′} → a ≺ᴬ b → b ≈ᴮ b′ → a ≺ᴬ b′
    ≺ᴬ-respʳ p e = ≺⊑ p (≈⊑ e)

    Tri : Lv → Lv → Set
    Tri a b = a ≺ᴬ b ⊎ b ≺ᴬ a ⊎ a ≈ᴮ b

    shL : ∀ {a a′ b} → a ≈ᴮ a′ → Tri a′ b → Tri a b
    shL e (injᵃ r) = injᵃ (≺ᴬ-respˡ e r)
    shL e (injᵇ r) = injᵇ (≺ᴬ-respʳ r (≈ᴮ-sym e))
    shL e (injᶜ r) = injᶜ (≈ᴮ-trans e r)

    shR : ∀ {a b b′} → b ≈ᴮ b′ → Tri a b′ → Tri a b
    shR e (injᵃ r) = injᵃ (≺ᴬ-respʳ r (≈ᴮ-sym e))
    shR e (injᵇ r) = injᵇ (≺ᴬ-respˡ e r)
    shR e (injᶜ r) = injᶜ (≈ᴮ-trans r (≈ᴮ-sym e))

    WFᴬ : Lv → Set
    WFᴬ zero       = ⊤
    WFᴬ (suc k)    = WFᴬ k
    WFᴬ (lim f)    = (∀ n → f n ⊑ᴬ f (suc n)) × (∀ n → WFᴬ (f n))
    WFᴬ (limᴼ k g) = (∀ x y → A k x → A k y → Σ (Ordᴸ k) λ z → A k z × g x ⊑ᴬ g z × g y ⊑ᴬ g z)
                   × (Σ (Ordᴸ k) λ x₀ → A k x₀ × k ≺ᴬ g x₀ × k ⊑ᴬ g x₀)
                   × (∀ x → A k x → WFᴬ (g x))

    stepsᴬ : ∀ {f : ℕ → Lv} → (∀ n → f n ⊑ᴬ f (suc n)) → ∀ {n m} → n <ᴺ m → f n ⊑ᴬ f m
    stepsᴬ s zero    = s _
    stepsᴬ s (suc p) = ⊑ᴬ-trans (stepsᴬ s p) (s _)

    branchᴬ : ∀ {k g} → (Σ (Ordᴸ k) λ x₀ → A k x₀ × k ≺ᴬ g x₀ × k ⊑ᴬ g x₀) → (p : Pre (limᴼ k g)) → Adm (limᴼ k g) p →
              Σ (Ordᴸ k) λ x → A k x × at (limᴼ k g) p ≺ᴬ g x
    branchᴬ (x₀ , ax , h , _) (inj₁ (inj₁ _)) _ = x₀ , ax , h
    branchᴬ (x₀ , ax , _ , h) (inj₁ (inj₂ r)) d = x₀ , ax , h r d
    branchᴬ _ (inj₂ (x , r)) (ax , d) = x , ax , viaᴬ r d (≈ᴮ-refl _)

    <-decᴬ : ∀ c → WFᴬ c → (p q : Pre c) → Adm c p → Adm c q → Tri (at c p) (at c q)
    <-decᴬ (suc k) w (inj₁ _) (inj₁ _) _ _ = injᶜ (≈ᴮ-refl k)
    <-decᴬ (suc k) w (inj₁ _) (inj₂ q) _ dq = injᵇ (viaᴬ q dq (≈ᴮ-refl _))
    <-decᴬ (suc k) w (inj₂ p) (inj₁ _) dp _ = injᵃ (viaᴬ p dp (≈ᴮ-refl _))
    <-decᴬ (suc k) w (inj₂ p) (inj₂ q) dp dq = <-decᴬ k w p q dp dq
    <-decᴬ (lim f) (s , w) (n , p) (m , q) dp dq with <ᴺ-dec n m
    ... | injᵃ n<m with stepsᴬ s n<m p dp
    ...   | viaᴬ p′ d′ e = shL e (<-decᴬ (f m) (w m) p′ q d′ dq)
    <-decᴬ (lim f) (s , w) (n , p) (m , q) dp dq | injᵇ m<n with stepsᴬ s m<n q dq
    ...   | viaᴬ q′ d′ e = shR e (<-decᴬ (f n) (w n) p q′ dp d′)
    <-decᴬ (lim f) (s , w) (n , p) (_ , q) dp dq | injᶜ refl = <-decᴬ (f n) (w n) p q dp dq
    <-decᴬ (limᴼ k g) (dir , par , w) p q dp dq with branchᴬ par p dp | branchᴬ par q dq
    ... | x , ax , viaᴬ p′ dp′ e | y , ay , viaᴬ q′ dq′ e′ with dir x y ax ay
    ...   | z , az , gx , gy with gx p′ dp′ | gy q′ dq′
    ...     | viaᴬ p″ dp″ f | viaᴬ q″ dq″ f′ =
      shL (≈ᴮ-trans e f) (shR (≈ᴮ-trans e′ f′) (<-decᴬ (g z) (w z az) p″ q″ dp″ dq″))
```

## §2 `B₀ = ⊤` 回到原来的 `Rel`

```agda
module Back (A : (k : Lv) → Ordᴸ k → Set) (h : ∀ k x → A k x → Leaf.Bs (λ _ → ⊤) k x) where
  open Leaf (λ _ → ⊤)
  B⊤ : ∀ k x → Bs k x
  B⊤ zero       _ = tt
  B⊤ (suc _)    _ = tt
  B⊤ (lim _)    _ = tt
  B⊤ (limᴼ _ _) _ = tt

  ≈ᵀ→≈ : ∀ {a b} → a ≈ᴮ b → a ≈ b
  ≈ᵀ→≈ z≈     = z≈
  ≈ᵀ→≈ (s≈ e) = s≈ (≈ᵀ→≈ e)
  ≈ᵀ→≈ (l≈ h) = l≈ (λ n → ≈ᵀ→≈ (h n))
  ≈ᵀ→≈ (o≈ {k} h) = o≈ (λ x → ≈ᵀ→≈ (h x (B⊤ k x)))

  private
    module N = RelB A h
    module O = Rel A

  ⊑→⊑ : ∀ {a b} → a N.⊑ᴬ b → a O.⊑ᴬ b
  ⊑→⊑ h r d with h r d
  ... | N.viaᴬ r′ d′ e = O.viaᴬ r′ d′ (≈ᵀ→≈ e)

  ≺→≺ : ∀ {a b} → a N.≺ᴬ b → a O.≺ᴬ b
  ≺→≺ (N.viaᴬ r′ d′ e) = O.viaᴬ r′ d′ (≈ᵀ→≈ e)

  WF′→WFᴬ : ∀ c → N.WFᴬ c → O.WFᴬ c
  WF′→WFᴬ zero w = tt
  WF′→WFᴬ (suc k) w = WF′→WFᴬ k w
  WF′→WFᴬ (lim f) (s , w) = (λ n → ⊑→⊑ (s n)) , (λ n → WF′→WFᴬ (f n) (w n))
  WF′→WFᴬ (limᴼ k g) (dir , (x₀ , a , h , h′) , w) =
    (λ x y ax ay → let z , az , p , q = dir x y ax ay in z , az , ⊑→⊑ p , ⊑→⊑ q) ,
    (x₀ , a , ≺→≺ h , ⊑→⊑ h′) ,
    (λ x a → WF′→WFᴬ (g x) (w x a))
```
