# 证书与阶段无关: 地板、相对比较与层号的好性 (底座)

> 底座, 不含记号. 结论写在 [LevelK](LevelK.lagda.md). `Fl` 是抽象的地板: 哪些层是**低层** (`Lw`), 低层上哪些树可容许 (`A`). 叶子 `Bs j x` 就是 `Lw j → A j x`: 高层全称, 低层只看地板. [InaccThetaRel](InaccThetaRel.lagda.md) 的 `Leaf` 只在第 0 层有旋钮, 这里每一层都有. §1, §2 的证明逐字. §3 是层号的好性 `Cx`, 它不提折叠, 不提观测, 也不提判决. §5 是 "加一层地板" 时这些东西怎么搬: 只有单步, 所以对 $k$ 递归时不需要跨阶段比较.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LevelKBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.InaccTreeBase using (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; at; toLv; toLvD; Tree; limᵢ; up; intoL; down; Dn; DnT; outD; Ω)
```

## §0 可容许路径与地板

`NoO k`: 层号里没有 `limᴼ`. `BL k`: 这一层的树可以直接取层号 (观测的底部): 没有 `limᴼ`, 全部前驱都低. 低层对前驱封闭, 所以低层都是 `BL`.

```agda
AdmOf : ((k : Lv) → Ordᴸ k → Set) → (c : Lv) → Pre c → Set
AdmOf B (suc k)    (inj₁ _)        = ⊤
AdmOf B (suc k)    (inj₂ r)        = AdmOf B k r
AdmOf B (lim f)    (n , r)         = AdmOf B (f n) r
AdmOf B (limᴼ k g) (inj₁ (inj₁ _)) = ⊤
AdmOf B (limᴼ k g) (inj₁ (inj₂ r)) = AdmOf B k r
AdmOf B (limᴼ k g) (inj₂ (x , r))  = B k x × AdmOf B (g x) r

NoO : Lv → Set
NoO zero       = ⊤
NoO (suc k)    = NoO k
NoO (lim f)    = ∀ n → NoO (f n)
NoO (limᴼ _ _) = ⊥

record Fl : Set₁ where
  field
    Lw : Lv → Set
    A   : (k : Lv) → Ordᴸ k → Set
    A→Lw   : ∀ k x → A k x → Lw k
    low-noo : ∀ j → Lw j → NoO j
    low-at  : ∀ j → Lw j → ∀ r → Lw (at j r)
    low-lim : ∀ f n → Lw (lim f) → Lw (f n)

  Bs : (k : Lv) → Ordᴸ k → Set
  Bs k x = Lw k → A k x

  A⊆B : ∀ k x → A k x → Bs k x
  A⊆B k x a _ = a

  BL : Lv → Set
  BL k = NoO k × (∀ r → Lw (at k r))

  lw→bl : ∀ {j} → Lw j → BL j
  lw→bl {j} l = low-noo j l , low-at j l

  bl-suc : ∀ {k} → BL (suc k) → BL k
  bl-suc (n , h) = n , (λ r → h (inj₂ r))

  bl-lim : ∀ {f} n → BL (lim f) → BL (f n)
  bl-lim m (n , h) = n m , (λ r → h (m , r))

  -- `toLv` 的参数层全低: 这一条对原始的树成立
  Lo : Lv → Set
  Lo zero       = ⊤
  Lo (suc k)    = Lo k
  Lo (lim f)    = ∀ n → Lo (f n)
  Lo (limᴼ k g) = Lw k × (∀ x → Lo (g x))

  noo→lo : ∀ j → NoO j → Lo j
  noo→lo zero    _ = tt
  noo→lo (suc j) n = noo→lo j n
  noo→lo (lim f) n = λ m → noo→lo (f m) (n m)

  lo-toLv : ∀ {k} → BL k → (x : Ordᴸ k) → Lo (toLv x)
  lo-toLv b Tree.zero     = tt
  lo-toLv b (Tree.suc x)  = lo-toLv b x
  lo-toLv b (Tree.lim h)  = λ n → lo-toLv b (h n)
  lo-toLv {k} b (limᵢ r f) = proj₂ b r , (λ y → lo-toLv b (f (intoL k r y)))
  lo-toLv {suc k} b (up d x) = lo-toLv (bl-suc b) x
  lo-toLv {lim f} b (up n x) = lo-toLv (bl-lim n b) x
  lo-toLv {limᴼ k g} (() , _) (up d x)

  lo-par : ∀ {k} → Lw k → Lo k
  lo-par {k} l = noo→lo k (low-noo k l)

  lo-at : ∀ a → Lo a → ∀ r → Lo (at a r)
  lo-at (suc k)    w (inj₁ _)        = w
  lo-at (suc k)    w (inj₂ r)        = lo-at k w r
  lo-at (lim f)    w (n , r)         = lo-at (f n) (w n) r
  lo-at (limᴼ k g) w (inj₁ (inj₁ _)) = lo-par (proj₁ w)
  lo-at (limᴼ k g) w (inj₁ (inj₂ r)) = lo-at k (lo-par (proj₁ w)) r
  lo-at (limᴼ k g) w (inj₂ (x , r))  = lo-at (g x) (proj₂ w x) r
```

## §1 叶子与相对比较

```agda
module Leaf (F : Fl) where
  open Fl F public

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

  -- `o≈` 两侧参数层不是变量时用
  o≈′ : ∀ {j j′ g g′} (e : j ≡ j′) → (∀ x → Bs j x → g x ≈ᴮ g′ (subst Ordᴸ e x)) → limᴼ j g ≈ᴮ limᴼ j′ g′
  o≈′ refl h = o≈ h

  o≈-inv : ∀ {j j′ g g′} → limᴼ j g ≈ᴮ limᴼ j′ g′ → Σ (j ≡ j′) λ e → ∀ x → Bs j x → g x ≈ᴮ g′ (subst Ordᴸ e x)
  o≈-inv (o≈ h) = refl , h

  AdmB : (c : Lv) → Pre c → Set
  AdmB = AdmOf Bs

  Adm : (c : Lv) → Pre c → Set
  Adm = AdmOf A

  Adm→B : ∀ c r → Adm c r → AdmB c r
  Adm→B (suc k)    (inj₁ _)        d = tt
  Adm→B (suc k)    (inj₂ r)        d = Adm→B k r d
  Adm→B (lim f)    (n , r)         d = Adm→B (f n) r d
  Adm→B (limᴼ k g) (inj₁ (inj₁ _)) d = tt
  Adm→B (limᴼ k g) (inj₁ (inj₂ r)) d = Adm→B k r d
  Adm→B (limᴼ k g) (inj₂ (x , r)) (a , d) = A⊆B k x a , Adm→B (g x) r d

  noo-adm : ∀ {B : (k : Lv) → Ordᴸ k → Set} k → NoO k → ∀ r → AdmOf B k r
  noo-adm (suc k) n (inj₁ _) = tt
  noo-adm (suc k) n (inj₂ r) = noo-adm k n r
  noo-adm (lim f) n (m , r)  = noo-adm (f m) (n m) r

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

  -- 路径的传递性: 严格小蕴含前序
  comp : ∀ b (r : Pre b) → Adm b r → (s : Pre (at b r)) → Adm (at b r) s → Σ (Pre b) λ t → Adm b t × at b t ≡ at (at b r) s
  comp (suc k)    (inj₁ _)        _ s ds = inj₂ s , ds , refl
  comp (suc k)    (inj₂ r)        d s ds with comp k r d s ds
  ... | t , dt , e = inj₂ t , dt , e
  comp (lim f)    (n , r)         d s ds with comp (f n) r d s ds
  ... | t , dt , e = (n , t) , dt , e
  comp (limᴼ k g) (inj₁ (inj₁ _)) _ s ds = inj₁ (inj₂ s) , ds , refl
  comp (limᴼ k g) (inj₁ (inj₂ r)) d s ds with comp k r d s ds
  ... | t , dt , e = inj₁ (inj₂ t) , dt , e
  comp (limᴼ k g) (inj₂ (x , r)) (a , d) s ds with comp (g x) r d s ds
  ... | t , dt , e = inj₂ (x , t) , (a , dt) , e

  ≈≡′ : ∀ {a b c} → a ≈ᴮ b → c ≡ b → a ≈ᴮ c
  ≈≡′ e refl = e

  ≡→≈′ : ∀ {a b} → a ≡ b → a ≈ᴮ b
  ≡→≈′ {a} refl = ≈ᴮ-refl a

  ≺→⊑ : ∀ {a b} → a ≺ᴬ b → a ⊑ᴬ b
  ≺→⊑ {a} {b} (viaᴬ q dq e) r d with ≈⊑ e r d
  ... | viaᴬ s ds e′ with comp b q dq s ds
  ...   | t , dt , et = viaᴬ t dt (≈≡′ e′ et)

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

## §2 字面的路径给 $\Omega$ 的路径

```agda
  path→Ω : ∀ i r → Adm i r → at i r ≺ᴬ toLv (Ω i)
  path→Ω (suc k)    (inj₁ _)        _ = viaᴬ (inj₁ (inj₁ tt)) tt (≈ᴮ-refl k)
  path→Ω (suc k)    (inj₂ r)        d = viaᴬ (inj₁ (inj₂ r)) d (≈ᴮ-refl _)
  path→Ω (lim f)    (n , r)         d with path→Ω (f n) r d
  ... | viaᴬ q dq e = viaᴬ (n , q) dq e
  path→Ω (limᴼ k g) (inj₁ (inj₁ _)) _ = viaᴬ (inj₁ (inj₁ tt)) tt (≈ᴮ-refl k)
  path→Ω (limᴼ k g) (inj₁ (inj₂ r)) d = viaᴬ (inj₁ (inj₂ r)) d (≈ᴮ-refl _)
  path→Ω (limᴼ k g) (inj₂ (x , r)) (a , d) with path→Ω (g x) r d
  ... | viaᴬ q dq e = viaᴬ (inj₂ (x , q)) (a , dq) e
```

## §3 层号的好性

`Cx a`: 可比较 (`WFᴬ`), 分支尊重 $\approx$ (`Rp`), 分支对比较单调 (`Mn`). 三者都只说 `Lv` 上的路径, 不提折叠. `Rp` 与 `Mn` 的前提是**层号上的**关系 `toLv z ≈ᴮ toLv z′`, `toLv z ⊑ᴬ toLv z′`, 这就是不进循环的原因: 地板上的相等与序都读层号, 不读观测.

`Cx` 对路径封闭 (`cx-at`, 要低层自己可比较), 对 $\approx$ 封闭 (`cx≈`).

```agda
  Rp : Lv → Set
  Rp zero       = ⊤
  Rp (suc k)    = Rp k
  Rp (lim f)    = ∀ n → Rp (f n)
  Rp (limᴼ k g) = (∀ x → Bs k x → Rp (g x)) × (∀ z z′ → Bs k z → Bs k z′ → toLv z ≈ᴮ toLv z′ → g z ≈ᴮ g z′)

  Mn : Lv → Set
  Mn zero       = ⊤
  Mn (suc k)    = Mn k
  Mn (lim f)    = ∀ n → Mn (f n)
  Mn (limᴼ k g) = (∀ x → A k x → Mn (g x)) × (∀ z z′ → A k z → A k z′ → toLv z ⊑ᴬ toLv z′ → g z ⊑ᴬ g z′)

  Cx : Lv → Set
  Cx a = WFᴬ a × Rp a × Mn a

  noo→rp : ∀ j → NoO j → Rp j
  noo→rp zero    _ = tt
  noo→rp (suc j) n = noo→rp j n
  noo→rp (lim f) n = λ m → noo→rp (f m) (n m)

  noo→mn : ∀ j → NoO j → Mn j
  noo→mn zero    _ = tt
  noo→mn (suc j) n = noo→mn j n
  noo→mn (lim f) n = λ m → noo→mn (f m) (n m)

  wf-at : (∀ j → Lw j → WFᴬ j) → ∀ a → Lo a → WFᴬ a → ∀ r → Adm a r → WFᴬ (at a r)
  wf-at lw (suc k)    l w (inj₁ _) _ = w
  wf-at lw (suc k)    l w (inj₂ r) d = wf-at lw k l w r d
  wf-at lw (lim f)    l w (n , r)  d = wf-at lw (f n) (l n) (proj₂ w n) r d
  wf-at lw (limᴼ k g) l w (inj₁ (inj₁ _)) _ = lw k (proj₁ l)
  wf-at lw (limᴼ k g) l w (inj₁ (inj₂ r)) d = wf-at lw k (lo-par (proj₁ l)) (lw k (proj₁ l)) r d
  wf-at lw (limᴼ k g) l w (inj₂ (x , r)) (a , d) = wf-at lw (g x) (proj₂ l x) (proj₂ (proj₂ w) x a) r d

  rp-at : ∀ a → Lo a → Rp a → ∀ r → Adm a r → Rp (at a r)
  rp-at (suc k)    l w (inj₁ _) _ = w
  rp-at (suc k)    l w (inj₂ r) d = rp-at k l w r d
  rp-at (lim f)    l w (n , r)  d = rp-at (f n) (l n) (w n) r d
  rp-at (limᴼ k g) l w (inj₁ (inj₁ _)) _ = noo→rp k (low-noo k (proj₁ l))
  rp-at (limᴼ k g) l w (inj₁ (inj₂ r)) d = rp-at k (lo-par (proj₁ l)) (noo→rp k (low-noo k (proj₁ l))) r d
  rp-at (limᴼ k g) l w (inj₂ (x , r)) (a , d) = rp-at (g x) (proj₂ l x) (proj₁ w x (A⊆B k x a)) r d

  mn-at : ∀ a → Lo a → Mn a → ∀ r → Adm a r → Mn (at a r)
  mn-at (suc k)    l w (inj₁ _) _ = w
  mn-at (suc k)    l w (inj₂ r) d = mn-at k l w r d
  mn-at (lim f)    l w (n , r)  d = mn-at (f n) (l n) (w n) r d
  mn-at (limᴼ k g) l w (inj₁ (inj₁ _)) _ = noo→mn k (low-noo k (proj₁ l))
  mn-at (limᴼ k g) l w (inj₁ (inj₂ r)) d = mn-at k (lo-par (proj₁ l)) (noo→mn k (low-noo k (proj₁ l))) r d
  mn-at (limᴼ k g) l w (inj₂ (x , r)) (a , d) = mn-at (g x) (proj₂ l x) (proj₁ w x a) r d

  cx-at : (∀ j → Lw j → WFᴬ j) → ∀ a → Lo a → Cx a → ∀ r → Adm a r → Cx (at a r)
  cx-at lw a l (w , rp , mn) r d = wf-at lw a l w r d , rp-at a l rp r d , mn-at a l mn r d

  ⊑≈ : ∀ {a a′ b b′} → a ≈ᴮ a′ → b′ ≈ᴮ b → a′ ⊑ᴬ b′ → a ⊑ᴬ b
  ⊑≈ e e′ σ = ⊑ᴬ-trans (≈⊑ e) (⊑ᴬ-trans σ (≈⊑ e′))

  wf≈ : ∀ {a b} → a ≈ᴮ b → WFᴬ b → WFᴬ a
  wf≈ z≈ w = tt
  wf≈ (s≈ e) w = wf≈ e w
  wf≈ (l≈ h) (s , w) =
    (λ n → ⊑≈ (h n) (≈ᴮ-sym (h (suc n))) (s n)) , (λ n → wf≈ (h n) (w n))
  wf≈ (o≈ {k} h) (dir , (x₀ , ax , p , q) , w) =
    (λ x y ax ay → let z , az , gx , gy = dir x y ax ay
                   in z , az , ⊑≈ (h x (A⊆B k x ax)) (≈ᴮ-sym (h z (A⊆B k z az))) gx ,
                               ⊑≈ (h y (A⊆B k y ay)) (≈ᴮ-sym (h z (A⊆B k z az))) gy) ,
    (x₀ , ax , ≺ᴬ-respʳ p (≈ᴮ-sym (h x₀ (A⊆B k x₀ ax))) , ⊑ᴬ-trans q (≈⊑ (≈ᴮ-sym (h x₀ (A⊆B k x₀ ax))))) ,
    (λ x a → wf≈ (h x (A⊆B k x a)) (w x a))

  rp≈ : ∀ {a b} → a ≈ᴮ b → Rp b → Rp a
  rp≈ z≈ w = tt
  rp≈ (s≈ e) w = rp≈ e w
  rp≈ (l≈ h) w = λ n → rp≈ (h n) (w n)
  rp≈ (o≈ h) (b , r) =
    (λ x d → rp≈ (h x d) (b x d)) ,
    (λ z z′ d d′ e → ≈ᴮ-trans (h z d) (≈ᴮ-trans (r z z′ d d′ e) (≈ᴮ-sym (h z′ d′))))

  mn≈ : ∀ {a b} → a ≈ᴮ b → Mn b → Mn a
  mn≈ z≈ w = tt
  mn≈ (s≈ e) w = mn≈ e w
  mn≈ (l≈ h) w = λ n → mn≈ (h n) (w n)
  mn≈ (o≈ {k} h) (b , r) =
    (λ x d → mn≈ (h x (A⊆B k x d)) (b x d)) ,
    (λ z z′ d d′ e → ⊑≈ (h z (A⊆B k z d)) (≈ᴮ-sym (h z′ (A⊆B k z′ d′))) (r z z′ d d′ e))

  cx≈ : ∀ {a b} → a ≈ᴮ b → Cx b → Cx a
  cx≈ e (w , r , m) = wf≈ e w , rp≈ e r , mn≈ e m
```

## §4 阶段

`Stage` 是一个可用的地板: 两个低层若 $\approx$ 就字面相同 (`low-≈`), 低层自己可比较, $\Omega_j$ 在地板里且 $j$ 是 $\Omega_j$ 的字面前驱, 地板上的元可比较 (`cmpA`, 这是有向性的唯一来源) 且它们的层号都好 (`cxA`). `cmpA` 只问同一层地板上的元, 全部是**有界的**: 下面 [LevelKTower](LevelKTower.lagda.md) 里它来自单个层号 $L$ 的 `<-decᴬ`.

```agda
record Stage : Set₁ where
  field fl : Fl
  open Leaf fl
  field
    low-≈  : ∀ {a b} → Lw a → Lw b → a ≈ᴮ b → a ≡ b
    low-wf : ∀ j → Lw j → WFᴬ j
    ΩA     : ∀ j → Lw j → A j (Ω j)
    pΩ     : ∀ j → Lw j → j ≺ᴬ toLv (Ω j)
    cmpA   : ∀ j x y → A j x → A j y → Tri (toLv x) (toLv y)
    cxA    : ∀ j x → A j x → Cx (toLv x)
```

## §5 加一层地板

`Ext F F′`: `F′` 只多了不在 `Lw` 里的层. 单调的方向 (`≈↑`, `≺↑`, `Tri↑`) 对一切层号成立, 反方向只对 `Lo` 成立: `Lo` 的层号的参数都在旧地板里, 新地板看不见它们. 所以好性可以搬到下一阶段 (`Cx↑`). 这里只有单步, 对 $k$ 递归时不需要跨阶段的比较.

```agda
record Ext (F F′ : Fl) : Set where
  private
    module F  = Fl F
    module F′ = Fl F′
  field
    low⊂ : ∀ {j} → F.Lw j → F′.Lw j
    A⊂   : ∀ {j x} → F.A j x → F′.A j x
    A⊃   : ∀ {j x} → F.Lw j → F′.A j x → F.A j x

module Move (F F′ : Fl) (X : Ext F F′) where
  open Ext X
  module L  = Leaf F
  module L′ = Leaf F′
  open L using (Lo; Bs; Lw; A; BL; lo-toLv; lo-at; lo-par; lw→bl)

  B′⊂B : ∀ {j x} → L′.Bs j x → Bs j x
  B′⊂B b l = A⊃ l (b (low⊂ l))

  B⊂B′ : ∀ {j x} → Lw j → Bs j x → L′.Bs j x
  B⊂B′ l b _ = A⊂ (b l)

  ≈↑ : ∀ {a b} → a L.≈ᴮ b → a L′.≈ᴮ b
  ≈↑ L.z≈ = L′.z≈
  ≈↑ (L.s≈ e) = L′.s≈ (≈↑ e)
  ≈↑ (L.l≈ h) = L′.l≈ (λ n → ≈↑ (h n))
  ≈↑ (L.o≈ h) = L′.o≈ (λ x b → ≈↑ (h x (B′⊂B b)))

  ≈↓ : ∀ {a b} → Lo a → a L′.≈ᴮ b → a L.≈ᴮ b
  ≈↓ l L′.z≈ = L.z≈
  ≈↓ l (L′.s≈ e) = L.s≈ (≈↓ l e)
  ≈↓ l (L′.l≈ h) = L.l≈ (λ n → ≈↓ (l n) (h n))
  ≈↓ (lk , lg) (L′.o≈ h) = L.o≈ (λ x b → ≈↓ (lg x) (h x (B⊂B′ lk b)))

  adm↑ : ∀ c r → L.Adm c r → L′.Adm c r
  adm↑ (suc k)    (inj₁ _)        d = tt
  adm↑ (suc k)    (inj₂ r)        d = adm↑ k r d
  adm↑ (lim f)    (n , r)         d = adm↑ (f n) r d
  adm↑ (limᴼ k g) (inj₁ (inj₁ _)) d = tt
  adm↑ (limᴼ k g) (inj₁ (inj₂ r)) d = adm↑ k r d
  adm↑ (limᴼ k g) (inj₂ (x , r)) (a , d) = A⊂ a , adm↑ (g x) r d

  adm↓ : ∀ c → Lo c → ∀ r → L′.Adm c r → L.Adm c r
  adm↓ (suc k)    l (inj₁ _)        d = tt
  adm↓ (suc k)    l (inj₂ r)        d = adm↓ k l r d
  adm↓ (lim f)    l (n , r)         d = adm↓ (f n) (l n) r d
  adm↓ (limᴼ k g) l (inj₁ (inj₁ _)) d = tt
  adm↓ (limᴼ k g) l (inj₁ (inj₂ r)) d = adm↓ k (lo-par (proj₁ l)) r d
  adm↓ (limᴼ k g) l (inj₂ (x , r)) (a , d) = A⊃ (proj₁ l) a , adm↓ (g x) (proj₂ l x) r d

  ≺↑ : ∀ {a b} → a L.≺ᴬ b → a L′.≺ᴬ b
  ≺↑ {b = b} (L.viaᴬ r d e) = L′.viaᴬ r (adm↑ b r d) (≈↑ e)

  Tri↑ : ∀ {a b} → L.Tri a b → L′.Tri a b
  Tri↑ (injᵃ p) = injᵃ (≺↑ p)
  Tri↑ (injᵇ p) = injᵇ (≺↑ p)
  Tri↑ (injᶜ e) = injᶜ (≈↑ e)

  ⊑↑ : ∀ {a b} → Lo a → a L.⊑ᴬ b → a L′.⊑ᴬ b
  ⊑↑ {a} l σ r d = ≺↑ (σ r (adm↓ a l r d))

  ≺↓ : ∀ {a b} → Lo b → a L′.≺ᴬ b → a L.≺ᴬ b
  ≺↓ {b = b} l (L′.viaᴬ r d e) =
    L.viaᴬ r (adm↓ b l r d) (L.≈ᴮ-sym (≈↓ (lo-at b l r) (L′.≈ᴮ-sym e)))

  ⊑↓ : ∀ {a b} → Lo b → a L′.⊑ᴬ b → a L.⊑ᴬ b
  ⊑↓ {a} l σ r d = ≺↓ l (σ r (adm↑ a r d))

  wf↑ : ∀ a → Lo a → L.WFᴬ a → L′.WFᴬ a
  wf↑ zero       l w = tt
  wf↑ (suc k)    l w = wf↑ k l w
  wf↑ (lim f)    l (s , w) = (λ n → ⊑↑ (l n) (s n)) , (λ n → wf↑ (f n) (l n) (w n))
  wf↑ (limᴼ k g) (lk , lg) (dir , (x₀ , ax , p , q) , w) =
    (λ x y ax ay → let z , az , gx , gy = dir x y (A⊃ lk ax) (A⊃ lk ay)
                   in z , A⊂ az , ⊑↑ (lg x) gx , ⊑↑ (lg y) gy) ,
    (x₀ , A⊂ ax , ≺↑ p , ⊑↑ (lo-par lk) q) ,
    (λ x a → wf↑ (g x) (lg x) (w x (A⊃ lk a)))

  rp↑ : ∀ a → Lo a → L.Rp a → L′.Rp a
  rp↑ zero       l w = tt
  rp↑ (suc k)    l w = rp↑ k l w
  rp↑ (lim f)    l w = λ n → rp↑ (f n) (l n) (w n)
  rp↑ (limᴼ k g) (lk , lg) (b , r) =
    (λ x d → rp↑ (g x) (lg x) (b x (B′⊂B d))) ,
    (λ z z′ d d′ e → ≈↑ (r z z′ (B′⊂B d) (B′⊂B d′) (≈↓ (lo-toLv (lw→bl lk) z) e)))

  mn↑ : ∀ a → Lo a → L.Mn a → L′.Mn a
  mn↑ zero       l w = tt
  mn↑ (suc k)    l w = mn↑ k l w
  mn↑ (lim f)    l w = λ n → mn↑ (f n) (l n) (w n)
  mn↑ (limᴼ k g) (lk , lg) (b , r) =
    (λ x d → mn↑ (g x) (lg x) (b x (A⊃ lk d))) ,
    (λ z z′ d d′ e → ⊑↑ (lg z) (r z z′ (A⊃ lk d) (A⊃ lk d′) (⊑↓ (lo-toLv (lw→bl lk) z′) e)))

  Cx↑ : ∀ a → Lo a → L.Cx a → L′.Cx a
  Cx↑ a l (w , r , m) = wf↑ a l w , rp↑ a l r , mn↑ a l m
```
