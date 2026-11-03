# 字面上界: `Lv` 上的相对比较 (底座)

> 底座, 不含记号. 结论写在 [InaccFloor](InaccFloor.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccFloorBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.InaccTreeBase
open import OCF.Align.Level using
  (Ordᴵ; _<ᴵ_; _≅ᴵ_; _⊑ᴵ_; _≺ᴵ_; via; zero; suc; lim; z≅; s≅; l≅; z⊑; s⊑; l⊑;
   ≅ᴵ-refl; ≅ᴵ-sym; <ᴵ-trans; <ᴵ-dec; ⊑ᴵ-trans; Sim→⊑ᴵ)
```

## §1 结构相等与相对的证书

`≈` 是 `≅` 的同分支版: `limᴼ` 上参数层字面相同, 分支逐点. 仓库的 `≅` 带 Aczel 式的互搬 `u`, `v`, 沿它搬路径时可容许性不保持; 这里用不到 `u`, `v`, 所以换掉. `≈→≅` 说它是 `≅` 的特例.

`<-decᴬ` 的递归只进入路径碰到的分支和 `dir` 给的 `z`. 所以把 "$x$ 取遍 `Ordᴸ k`" 换成一个任意的**可容许集** `A` 就够了. 这一节对 `A` 完全参数化.

```agda
infix 4 _≈_
data _≈_ : Lv → Lv → Set where
  z≈ : zero ≈ zero
  s≈ : ∀ {a b} → a ≈ b → suc a ≈ suc b
  l≈ : ∀ {f g} → (∀ n → f n ≈ g n) → lim f ≈ lim g
  o≈ : ∀ {k g g′} → (∀ x → g x ≈ g′ x) → limᴼ k g ≈ limᴼ k g′

≈-refl : ∀ a → a ≈ a
≈-refl zero       = z≈
≈-refl (suc a)    = s≈ (≈-refl a)
≈-refl (lim f)    = l≈ (λ n → ≈-refl (f n))
≈-refl (limᴼ k g) = o≈ (λ x → ≈-refl (g x))

≈-sym : ∀ {a b} → a ≈ b → b ≈ a
≈-sym z≈     = z≈
≈-sym (s≈ e) = s≈ (≈-sym e)
≈-sym (l≈ h) = l≈ (λ n → ≈-sym (h n))
≈-sym (o≈ h) = o≈ (λ x → ≈-sym (h x))

≈-trans : ∀ {a b c} → a ≈ b → b ≈ c → a ≈ c
≈-trans z≈     z≈      = z≈
≈-trans (s≈ e) (s≈ e′) = s≈ (≈-trans e e′)
≈-trans (l≈ h) (l≈ h′) = l≈ (λ n → ≈-trans (h n) (h′ n))
≈-trans (o≈ h) (o≈ h′) = o≈ (λ x → ≈-trans (h x) (h′ x))

≈→≅ : ∀ {a b} → a ≈ b → a ≅ b
≈→≅ z≈     = z≅
≈→≅ (s≈ e) = s≅ (≈→≅ e)
≈→≅ (l≈ h) = l≅ (λ n → ≈→≅ (h n))
≈→≅ {limᴼ k g} (o≈ h) = o≅ (≅-refl k) (λ x → x) (λ x → x) (λ x → ≈→≅ (h x)) (λ x → ≈→≅ (h x))

module Rel (A : (k : Lv) → Ordᴸ k → Set) where

  Adm : (c : Lv) → Pre c → Set
  Adm (suc k)    (inj₁ _)        = ⊤
  Adm (suc k)    (inj₂ r)        = Adm k r
  Adm (lim f)    (n , r)         = Adm (f n) r
  Adm (limᴼ k g) (inj₁ (inj₁ _)) = ⊤
  Adm (limᴼ k g) (inj₁ (inj₂ r)) = Adm k r
  Adm (limᴼ k g) (inj₂ (x , r))  = A k x × Adm (g x) r

  record _≺ᴬ_ (a b : Lv) : Set where
    constructor viaᴬ
    field
      pthᴬ : Pre b
      admᴬ : Adm b pthᴬ
      prfᴬ : a ≈ at b pthᴬ

  _⊑ᴬ_ : Lv → Lv → Set
  a ⊑ᴬ b = (r : Pre a) → Adm a r → at a r ≺ᴬ b

  ≺ᴬ-respˡ : ∀ {a a′ b} → a′ ≈ a → a ≺ᴬ b → a′ ≺ᴬ b
  ≺ᴬ-respˡ e (viaᴬ r d e′) = viaᴬ r d (≈-trans e e′)

  ⊑ᴬ-trans : ∀ {a b c} → a ⊑ᴬ b → b ⊑ᴬ c → a ⊑ᴬ c
  ⊑ᴬ-trans σ τ r d with σ r d
  ... | viaᴬ s ds e = ≺ᴬ-respˡ e (τ s ds)

  ⊑ᴬ-refl : ∀ {a} → a ⊑ᴬ a
  ⊑ᴬ-refl r d = viaᴬ r d (≈-refl _)

  ≺⊑ : ∀ {a b c} → a ≺ᴬ b → b ⊑ᴬ c → a ≺ᴬ c
  ≺⊑ (viaᴬ s ds e) τ = ≺ᴬ-respˡ e (τ s ds)

  -- `≈` 蕴含 `⊑ᴬ`: 路径的形状不变, 可容许性不变
  ≈⊑ : ∀ {a b} → a ≈ b → a ⊑ᴬ b
  ≈⊑ (s≈ e) (inj₁ _) _ = viaᴬ (inj₁ tt) tt e
  ≈⊑ (s≈ e) (inj₂ r) d with ≈⊑ e r d
  ... | viaᴬ r′ d′ e′ = viaᴬ (inj₂ r′) d′ e′
  ≈⊑ (l≈ h) (n , r) d with ≈⊑ (h n) r d
  ... | viaᴬ r′ d′ e′ = viaᴬ (n , r′) d′ e′
  ≈⊑ (o≈ h) (inj₁ (inj₁ _)) _ = viaᴬ (inj₁ (inj₁ tt)) tt (≈-refl _)
  ≈⊑ (o≈ h) (inj₁ (inj₂ r)) d = viaᴬ (inj₁ (inj₂ r)) d (≈-refl _)
  ≈⊑ (o≈ h) (inj₂ (x , r)) (a , d) with ≈⊑ (h x) r d
  ... | viaᴬ r′ d′ e′ = viaᴬ (inj₂ (x , r′)) (a , d′) e′

  ≺ᴬ-respʳ : ∀ {a b b′} → a ≺ᴬ b → b ≈ b′ → a ≺ᴬ b′
  ≺ᴬ-respʳ p e = ≺⊑ p (≈⊑ e)

  Tri : Lv → Lv → Set
  Tri a b = a ≺ᴬ b ⊎ b ≺ᴬ a ⊎ a ≈ b

  shL : ∀ {a a′ b} → a ≈ a′ → Tri a′ b → Tri a b
  shL e (injᵃ r) = injᵃ (≺ᴬ-respˡ e r)
  shL e (injᵇ r) = injᵇ (≺ᴬ-respʳ r (≈-sym e))
  shL e (injᶜ r) = injᶜ (≈-trans e r)

  shR : ∀ {a b b′} → b ≈ b′ → Tri a b′ → Tri a b
  shR e (injᵃ r) = injᵃ (≺ᴬ-respʳ r (≈-sym e))
  shR e (injᵇ r) = injᵇ (≺ᴬ-respˡ e r)
  shR e (injᶜ r) = injᶜ (≈-trans r (≈-sym e))

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
  branchᴬ _ (inj₂ (x , r)) (ax , d) = x , ax , viaᴬ r d (≈-refl _)

  -- 定理: 可容许路径之间的比较, 结果也是可容许的
  <-decᴬ : ∀ c → WFᴬ c → (p q : Pre c) → Adm c p → Adm c q → Tri (at c p) (at c q)
  <-decᴬ (suc k) w (inj₁ _) (inj₁ _) _ _ = injᶜ (≈-refl k)
  <-decᴬ (suc k) w (inj₁ _) (inj₂ q) _ dq = injᵇ (viaᴬ q dq (≈-refl _))
  <-decᴬ (suc k) w (inj₂ p) (inj₁ _) dp _ = injᵃ (viaᴬ p dp (≈-refl _))
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
    shL (≈-trans e f) (shR (≈-trans e′ f′) (<-decᴬ (g z) (w z az) p″ q″ dp″ dq″))
```

## §2 世界 ℓ: 可容许就是 `ℓ` 的字面前驱

`em` 忘掉证据. `A` 只在第 0 层有内容: $x$ 是 $\ell$ 的某个字面前驱的像. 下面的 `_+ᴵ_` 与 `times` 把 $L\mapsto L\cdot\Omega$ 写成 `Lv` 上的普通函数, 没有语法. `WF-times` 说它保持 `WFᴬ`.

```agda
em : Ordᴵ → Ordᴸ zero
em zero      = zero
em (suc a)   = suc (em a)
em (lim f s) = lim (λ n → em (f n))

_⊞_ : Lv → Ordᴸ zero → Lv
L ⊞ zero    = L
L ⊞ suc x   = suc (L ⊞ x)
L ⊞ lim f   = lim (λ n → L ⊞ f n)

times : Lv → Lv
times L = limᴼ zero (L ⊞_)

-- 与 `toLv (Ω 1)` 的关系
times0≈ : times zero ≈ limᴼ zero toLv
times0≈ = o≈ go where
  go : ∀ (x : Ordᴸ zero) → (zero ⊞ x) ≈ toLv x
  go zero    = z≈
  go (suc x) = s≈ (go x)
  go (lim f) = l≈ (λ n → go (f n))

≅→⊑ᴵ : ∀ {a b} → a ≅ᴵ b → a ⊑ᴵ b
≅→⊑ᴵ z≅     = z⊑
≅→⊑ᴵ (s≅ e) = s⊑ e zero
≅→⊑ᴵ (l≅ h) = l⊑ (λ n → ⊑ᴵ-trans (≅→⊑ᴵ (h n)) (Sim→⊑ᴵ (λ q → lim n q)))

≺→⊑ᴵ : ∀ {a b} → a ≺ᴵ b → a ⊑ᴵ b
≺→⊑ᴵ (via e q) = ⊑ᴵ-trans (≅→⊑ᴵ e) (Sim→⊑ᴵ (λ r → <ᴵ-trans r q))

Aℓ : Ordᴵ → (k : Lv) → Ordᴸ k → Set
Aℓ ℓ zero       x = Σ Ordᴵ λ a → a <ᴵ ℓ × em a ≡ x
Aℓ ℓ (suc _)    _ = ⊥
Aℓ ℓ (lim _)    _ = ⊥
Aℓ ℓ (limᴼ _ _) _ = ⊥

module World (ℓ : Ordᴵ) (one : suc zero <ᴵ ℓ) where
  open Rel (Aℓ ℓ) public

  _+ᴵ_ : Lv → Ordᴵ → Lv
  L +ᴵ a = L ⊞ em a

  inL : ∀ L a → L ⊑ᴬ (L +ᴵ a)
  inL L zero      r d = viaᴬ r d (≈-refl _)
  inL L (suc a)   r d with inL L a r d
  ... | viaᴬ r′ d′ e = viaᴬ (inj₂ r′) d′ e
  inL L (lim f s) r d with inL L (f 0) r d
  ... | viaᴬ r′ d′ e = viaᴬ (0 , r′) d′ e

  lit⊞ : ∀ {L a b} → a <ᴵ b → (L +ᴵ a) ≺ᴬ (L +ᴵ b)
  lit⊞ zero      = viaᴬ (inj₁ tt) tt (≈-refl _)
  lit⊞ (suc q)   with lit⊞ q
  ... | viaᴬ r d e = viaᴬ (inj₂ r) d e
  lit⊞ (lim n q) with lit⊞ q
  ... | viaᴬ r d e = viaᴬ (n , r) d e

  ≈⊞ : ∀ {L a b} → a ≅ᴵ b → (L +ᴵ a) ≈ (L +ᴵ b)
  ≈⊞ z≅     = ≈-refl _
  ≈⊞ (s≅ e) = s≈ (≈⊞ e)
  ≈⊞ (l≅ h) = l≈ (λ n → ≈⊞ (h n))

  -- `L +ᴵ a` 的字面前驱沿 `<ᴵ` 向上
  up⊞ : ∀ {L a b} → a <ᴵ b → (L +ᴵ a) ⊑ᴬ (L +ᴵ b)
  up⊞ zero      r d = viaᴬ (inj₂ r) d (≈-refl _)
  up⊞ (suc q)   r d with up⊞ q r d
  ... | viaᴬ r′ d′ e = viaᴬ (inj₂ r′) d′ e
  up⊞ (lim n q) r d with up⊞ q r d
  ... | viaᴬ r′ d′ e = viaᴬ (n , r′) d′ e

  res⊞ : ∀ {L a b} → a ≅ᴵ b → (L +ᴵ a) ⊑ᴬ (L +ᴵ b)
  res⊞ z≅     r d = viaᴬ r d (≈-refl _)
  res⊞ (s≅ e) (inj₁ _) d = viaᴬ (inj₁ tt) tt (≈⊞ e)
  res⊞ (s≅ e) (inj₂ r) d with res⊞ e r d
  ... | viaᴬ r′ d′ e′ = viaᴬ (inj₂ r′) d′ e′
  res⊞ (l≅ h) (n , r) d with res⊞ (h n) r d
  ... | viaᴬ r′ d′ e′ = viaᴬ (n , r′) d′ e′

  mono⊞ : ∀ {L a b} → a ⊑ᴵ b → (L +ᴵ a) ⊑ᴬ (L +ᴵ b)
  mono⊞ {L} {b = b} z⊑ r d = inL L b r d
  mono⊞ (s⊑ e q) (inj₁ _) _ with lit⊞ q
  ... | viaᴬ r′ d′ e′ = viaᴬ r′ d′ (≈-trans (≈⊞ e) e′)
  mono⊞ (s⊑ e q) (inj₂ r) d with res⊞ e r d
  ... | viaᴬ r′ d′ e′ = ≺ᴬ-respˡ e′ (up⊞ q r′ d′)
  mono⊞ (l⊑ h) (n , r) d = mono⊞ (h n) r d

  WF-+ : ∀ {L} → WFᴬ L → ∀ a → WFᴬ (L +ᴵ a)
  WF-+ w zero      = w
  WF-+ w (suc a)   = WF-+ w a
  WF-+ w (lim f s) = (λ n → mono⊞ (s n)) , (λ n → WF-+ w (f n))
```

**$L\mapsto L\cdot\Omega$ 保持证书.** `<ᴵ-dec` 给 `dir`. 没有 $\ell$ 这个界就没有 `dir`: `¬WF-L₁`.

```agda
  Has0 : Lv → Set
  Has0 L = zero ≺ᴬ suc L

  WF-times : ∀ {L} → WFᴬ L → Has0 L → WFᴬ (times L)
  WF-times {L} w h0 = dir , par , her where
    dir : ∀ x y → Aℓ ℓ zero x → Aℓ ℓ zero y → Σ (Ordᴸ zero) λ z → Aℓ ℓ zero z × (L ⊞ x) ⊑ᴬ (L ⊞ z) × (L ⊞ y) ⊑ᴬ (L ⊞ z)
    dir _ _ (a , pa , refl) (b , pb , refl) with <ᴵ-dec pa pb
    ... | injᵃ r = em b , (b , pb , refl) , mono⊞ (≺→⊑ᴵ r) , ⊑ᴬ-refl
    ... | injᵇ r = em a , (a , pa , refl) , ⊑ᴬ-refl , mono⊞ (≺→⊑ᴵ r)
    ... | injᶜ e = em b , (b , pb , refl) , res⊞ e , ⊑ᴬ-refl
    par : Σ (Ordᴸ zero) λ x₀ → Aℓ ℓ zero x₀ × zero ≺ᴬ (L ⊞ x₀) × zero ⊑ᴬ (L ⊞ x₀)
    par = suc zero , (suc zero , one , refl) , h0 , (λ ())
    her : ∀ x → Aℓ ℓ zero x → WFᴬ (L ⊞ x)
    her _ (a , _ , refl) = WF-+ w a

  -- `L ⊑ᴬ times L` (经分支 1)
  step-times : ∀ L → L ⊑ᴬ times L
  step-times L r d = viaᴬ (inj₂ (suc zero , inj₂ r)) ((suc zero , one , refl) , d) (≈-refl _)

  Has0-times : ∀ L → Has0 (times L)
  Has0-times L = viaᴬ (inj₂ (inj₁ (inj₁ tt))) tt z≈

-- Ω·m 与 Ω·ω: 对 m 一致, 没有语法
Ω·_ : ℕ → Lv
Ω· zero  = zero
Ω· suc m = times (Ω· m)

Ω·ω : Lv
Ω·ω = lim Ω·_

module WorldN (ℓ : Ordᴵ) (one : suc zero <ᴵ ℓ) where
  open World ℓ one

  Has0Ω : ∀ m → Has0 (Ω· m)
  Has0Ω zero    = viaᴬ (inj₁ tt) tt z≈
  Has0Ω (suc m) = Has0-times _

  WFΩ· : ∀ m → WFᴬ (Ω· m)
  WFΩ· zero    = tt
  WFΩ· (suc m) = WF-times (WFΩ· m) (Has0Ω m)

  WFΩ·ω : WFᴬ Ω·ω
  WFΩ·ω = (λ n → step-times (Ω· n)) , WFΩ·

  -- 比较: 两个可容许路径 (这就是 Uniform5 的 `ψ≡` 的层号版, 字面界是 (Ω·m)+ℓ)
  cmpΩ : ∀ m a b → a <ᴵ ℓ → b <ᴵ ℓ → Tri ((Ω· m) +ᴵ a) ((Ω· m) +ᴵ b)
  cmpΩ m a b pa pb with lit⊞ {Ω· m} pa | lit⊞ {Ω· m} pb
  ... | viaᴬ r dr e | viaᴬ r′ dr′ e′ =
    shL e (shR e′ (<-decᴬ ((Ω· m) +ᴵ ℓ) (WF-+ (WFΩ· m) ℓ) r r′ dr dr′))
```
