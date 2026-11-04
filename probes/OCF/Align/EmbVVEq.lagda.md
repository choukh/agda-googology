# 值验收 (层号): 去头关系

> 入口 [EmbVV](EmbVV.lagda.md). 不读记号. `a ≃ᴵ b`: 两个层号结构相同, 只在一些极限节点上左边多一个头 (`lh≃`). `≃ˢ`, `≃ᶻ`, `≈ᴴ` 是 `OCF.Free.Eq` 的 `≅ˢ`, `≅ᶻ`, `≈ᴿ` 的去头版本, 证明照抄.
>
> **关键 (`clash≃`).** `≃ᴵ` 不是确定的关系, 所以 `BTBOValLe` 的 `lt-pres` (字面的保序) 在这里不成立. 但派发不会错开, 只靠值: `≺ᴵ` 严格, `≅ᴵ` 同值, `≃ᴵ` 同值 (`≃→≼`, `≃→≽`). 比较总在同一个界下, 字面三歧总有答案, 答案只能与另一边一致.
>
> `ŝ≃` 不要求 $c\cong c'$: 地板的界只在 `Goodᴺ` 里用, 而下面的比较两边各带自己的证书.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EmbVVEq where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level
open import OCF.Free.Prefix
open import OCF.Free.Floor
open import OCF.Free.Aux using (kd; kd-≅; tf)
open import OCF.Align.LadderOrdCode using (_≼_; z≼; s≼; s≼ʳ; l≼; l≼ʳ; ≼-refl; ≼-trans)
open Ord-Ord using (iter)
open Restrˢ
```

## §1 层号

```agda
infix 4 _≃ᴵ_
data _≃ᴵ_ : Ordᴵ → Ordᴵ → Set where
  z≃  : zero ≃ᴵ zero
  s≃  : ∀ {a b} → a ≃ᴵ b → suc a ≃ᴵ suc b
  l≃  : ∀ {f g s t} → (∀ n → f n ≃ᴵ g n) → lim f s ≃ᴵ lim g t
  lh≃ : ∀ {f g s t} → (∀ n → f (suc n) ≃ᴵ g n) → lim f s ≃ᴵ lim g t
  lr≃ : ∀ {f g s t} → (∀ n → f (suc n) ≃ᴵ g (suc n)) → lim f s ≃ᴵ lim g t

≅→≃ : ∀ {a b} → a ≅ᴵ b → a ≃ᴵ b
≅→≃ z≅ = z≃
≅→≃ (s≅ e) = s≃ (≅→≃ e)
≅→≃ (l≅ h) = l≃ (λ n → ≅→≃ (h n))

≃-reflᴵ : ∀ a → a ≃ᴵ a
≃-reflᴵ a = ≅→≃ (≅ᴵ-refl a)

≃-respˡ : ∀ {a a′ b} → a ≅ᴵ a′ → a′ ≃ᴵ b → a ≃ᴵ b
≃-respˡ z≅ z≃ = z≃
≃-respˡ (s≅ e) (s≃ d) = s≃ (≃-respˡ e d)
≃-respˡ (l≅ h) (l≃ k) = l≃ (λ n → ≃-respˡ (h n) (k n))
≃-respˡ (l≅ h) (lh≃ k) = lh≃ (λ n → ≃-respˡ (h (suc n)) (k n))
≃-respˡ (l≅ h) (lr≃ k) = lr≃ (λ n → ≃-respˡ (h (suc n)) (k n))

≃-respʳ : ∀ {a b b′} → a ≃ᴵ b → b ≅ᴵ b′ → a ≃ᴵ b′
≃-respʳ z≃ z≅ = z≃
≃-respʳ (s≃ d) (s≅ e) = s≃ (≃-respʳ d e)
≃-respʳ (l≃ k) (l≅ h) = l≃ (λ n → ≃-respʳ (k n) (h n))
≃-respʳ (lh≃ k) (l≅ h) = lh≃ (λ n → ≃-respʳ (k n) (h n))
≃-respʳ (lr≃ k) (l≅ h) = lr≃ (λ n → ≃-respʳ (k n) (h (suc n)))

-- 夹在两个 ≅ᴵ 之间
≃-res : ∀ {a a′ b b′} → a ≅ᴵ a′ → a ≃ᴵ b → b ≅ᴵ b′ → a′ ≃ᴵ b′
≃-res e d e′ = ≃-respˡ (≅ᴵ-sym e) (≃-respʳ d e′)

kd-≃ : ∀ {a b} → a ≃ᴵ b → kd a ≡ kd b
kd-≃ z≃ = refl
kd-≃ (s≃ _) = refl
kd-≃ (l≃ _) = refl
kd-≃ (lh≃ _) = refl
kd-≃ (lr≃ _) = refl
```

## §2 值

```agda
≅→≼ᴵ : ∀ {a b} → a ≅ᴵ b → a ≼ b
≅→≼ᴵ z≅ = z≼
≅→≼ᴵ (s≅ e) = s≼ (≅→≼ᴵ e)
≅→≼ᴵ (l≅ h) = l≼ (λ n → l≼ʳ n (≅→≼ᴵ (h n)))

<→s≼ : ∀ {a b} → a <ᴵ b → suc a ≼ b
<→s≼ {a} zero = s≼ (≼-refl a)
<→s≼ (suc q) = s≼ʳ (<→s≼ q)
<→s≼ (lim n q) = l≼ʳ n (<→s≼ q)

≺→s≼ᴵ : ∀ {a b} → a ≺ᴵ b → suc a ≼ b
≺→s≼ᴵ (via e q) = ≼-trans (s≼ (≅→≼ᴵ e)) (<→s≼ q)

⊑→≼ᴵ : ∀ {a b} → a ⊑ᴵ b → a ≼ b
⊑→≼ᴵ z⊑ = z≼
⊑→≼ᴵ (s⊑ e q) = ≼-trans (s≼ (≅→≼ᴵ e)) (<→s≼ q)
⊑→≼ᴵ (l⊑ h) = l≼ (λ n → ⊑→≼ᴵ (h n))

≃→≼ : ∀ {a b} → a ≃ᴵ b → a ≼ b
≃→≼ z≃ = z≼
≃→≼ (s≃ d) = s≼ (≃→≼ d)
≃→≼ (l≃ k) = l≼ (λ n → l≼ʳ n (≃→≼ (k n)))
≃→≼ {a = lim f s} (lh≃ k) = l≼ go
  where
  go : ∀ n → f n ≼ _
  go zero = ≼-trans (⊑→≼ᴵ (s 0)) (l≼ʳ 0 (≃→≼ (k 0)))
  go (suc n) = l≼ʳ n (≃→≼ (k n))
≃→≼ {a = lim f s} (lr≃ k) = l≼ go
  where
  go : ∀ n → f n ≼ _
  go zero = ≼-trans (⊑→≼ᴵ (s 0)) (l≼ʳ 1 (≃→≼ (k 0)))
  go (suc n) = l≼ʳ (suc n) (≃→≼ (k n))

≃→≽ : ∀ {a b} → a ≃ᴵ b → b ≼ a
≃→≽ z≃ = z≼
≃→≽ (s≃ d) = s≼ (≃→≽ d)
≃→≽ (l≃ k) = l≼ (λ n → l≼ʳ n (≃→≽ (k n)))
≃→≽ (lh≃ k) = l≼ (λ n → l≼ʳ (suc n) (≃→≽ (k n)))
≃→≽ {b = lim g t} (lr≃ k) = l≼ go
  where
  go : ∀ n → g n ≼ _
  go zero = ≼-trans (⊑→≼ᴵ (t 0)) (l≼ʳ 1 (≃→≽ (k 0)))
  go (suc n) = l≼ʳ (suc n) (≃→≽ (k n))

≼-irr : ∀ {a} → suc a ≼ a → ⊥
≼-irr {a = zero} ()
≼-irr {a = suc a} (s≼ h) = ≼-irr h
≼-irr {a = suc a} (s≼ʳ h) = ≼-irr (≼-trans (s≼ʳ (≼-refl (suc a))) h)
≼-irr {a = lim f s} (l≼ʳ n h) = ≼-irr (≼-trans (s≼ (l≼ʳ n (≼-refl (f n)))) h)

-- 派发不错开: 左边 j ≺ i, 右边不可能 i′ ≺ j′ 或 i′ ≅ j′
clash≃ : ∀ {j j′ i i′} → j ≃ᴵ j′ → i ≃ᴵ i′ → j ≺ᴵ i → (i′ ≺ᴵ j′) ⊎ (i′ ≅ᴵ j′) → ⊥
clash≃ ej ei r (inj₁ r′) = ≼-irr (≼-trans (≺→s≼ᴵ r) (≼-trans (≃→≼ ei) (≼-trans (s≼ʳ (≼-refl _)) (≼-trans (≺→s≼ᴵ r′) (≃→≽ ej)))))
clash≃ ej ei r (inj₂ c) = ≼-irr (≼-trans (≺→s≼ᴵ r) (≼-trans (≃→≼ ei) (≼-trans (≅→≼ᴵ c) (≃→≽ ej))))

-- 反方向: 右边 j′ ≺ i′, 左边不可能 i ≺ j 或 i ≅ j
clash≃′ : ∀ {j j′ i i′} → j ≃ᴵ j′ → i ≃ᴵ i′ → j′ ≺ᴵ i′ → (i ≺ᴵ j) ⊎ (i ≅ᴵ j) → ⊥
clash≃′ ej ei r (inj₁ r′) = ≼-irr (≼-trans (≺→s≼ᴵ r′) (≼-trans (≃→≼ ej) (≼-trans (s≼ʳ (≼-refl _)) (≼-trans (≺→s≼ᴵ r) (≃→≽ ei)))))
clash≃′ ej ei r (inj₂ c) = ≼-irr (≼-trans (≺→s≼ᴵ r) (≼-trans (≃→≽ ei) (≼-trans (≅→≼ᴵ c) (≃→≼ ej))))
```

## §3 `Z`

```agda
infix 4 _≃ᶻ_
data _≃ᶻ_ : Z → Z → Set where
  zᶻ  : Z.zero ≃ᶻ Z.zero
  sᶻ  : ∀ {x y} → x ≃ᶻ y → Z.suc x ≃ᶻ Z.suc y
  lᶻ  : ∀ {f g : ℕ → Z} → (∀ n → f n ≃ᶻ g n) → Z.lim f ≃ᶻ Z.lim g
  lhᶻ : ∀ {f g : ℕ → Z} → (∀ n → f (suc n) ≃ᶻ g n) → Z.lim f ≃ᶻ Z.lim g
  lrᶻ : ∀ {f g : ℕ → Z} → (∀ n → f (suc n) ≃ᶻ g (suc n)) → Z.lim f ≃ᶻ Z.lim g
  ĉᶻ  : ∀ {c c′ t₀ t₀′ o₀ o₀′} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z} {g′ o′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Z} →
        t₀ ≃ᶻ t₀′ → (∀ η e η′ e′ → η ≃ᴵ η′ → g η e ≃ᶻ g′ η′ e′) →
        o₀ ≃ᶻ o₀′ → (∀ η e η′ e′ → η ≃ᴵ η′ → o η e ≃ᶻ o′ η′ e′) → ĉᴸ c t₀ g o₀ o ≃ᶻ ĉᴸ c′ t₀′ g′ o₀′ o′
```

## §4 `Ordˢ`

```agda
module _ (ℓ : Ordᴵ) (R : (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → ∀ {ℓ′} → Ordˢ ℓ′ → Set) where
  data Eq₊ˢ : ∀ {ℓ′} → Ordˢ ℓ → Ordˢ ℓ′ → Set where
    z≅  : ∀ {ℓ′} → Eq₊ˢ {ℓ′} Ord₊ˢ.zero Ord₊ˢ.zero
    s≅  : ∀ {ℓ′} {a : Ordˢ ℓ} {b : Ordˢ ℓ′} → Eq₊ˢ a b → Eq₊ˢ (Ord₊ˢ.suc a) (Ord₊ˢ.suc b)
    l≅  : ∀ {ℓ′} {f : ℕ → Ordˢ ℓ} {g : ℕ → Ordˢ ℓ′} → (∀ n → Eq₊ˢ (f n) (g n)) → Eq₊ˢ (Ord₊ˢ.lim f) (Ord₊ˢ.lim g)
    lh  : ∀ {ℓ′} {f : ℕ → Ordˢ ℓ} {g : ℕ → Ordˢ ℓ′} → (∀ n → Eq₊ˢ (f (suc n)) (g n)) → Eq₊ˢ (Ord₊ˢ.lim f) (Ord₊ˢ.lim g)
    lr  : ∀ {ℓ′} {f : ℕ → Ordˢ ℓ} {g : ℕ → Ordˢ ℓ′} → (∀ n → Eq₊ˢ (f (suc n)) (g (suc n))) → Eq₊ˢ (Ord₊ˢ.lim f) (Ord₊ˢ.lim g)
    lᵢ≅ : ∀ {ℓ′ j j′} {p : j <ᴵ ℓ} {q : j′ <ᴵ ℓ′} {f : Uˢ j (<→◃ p) → Ordˢ ℓ} {g : Uˢ j′ (<→◃ q) → Ordˢ ℓ′} →
          j ≃ᴵ j′ →
          (∀ (x : Ordˢ j) (y : Ordˢ j′) → R j (<→◃ p) (intoˢ (<→◃ p) x) y → Eq₊ˢ (f (intoˢ (<→◃ p) x)) (g (intoˢ (<→◃ q) y))) →
          Eq₊ˢ (Ord₊ˢ.limᵢ p f) (Ord₊ˢ.limᵢ q g)
    upˡ : ∀ {ℓ′ k} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} {b : Ordˢ ℓ′} → R k (◃₁→◃ r) x b → Eq₊ˢ (Ord₊ˢ.up r x) b
    upʳ : ∀ {ℓ′ k} {r : k ◃₁ ℓ′} {y : Uˢ k (◃₁→◃ r)} {a : Ordˢ ℓ} → Eq₊ˢ a (outˢ (◃₁→◃ r) y) → Eq₊ˢ a (Ord₊ˢ.up r y)
    ŝ≅  : ∀ {ℓ′ c c′} {t₀ : Ordˢ ℓ} {t₀′ : Ordˢ ℓ′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} {g′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Ordˢ ℓ′} →
          kd ℓ ≡ kd ℓ′ → Eq₊ˢ t₀ t₀′ → (∀ η e η′ e′ → η ≃ᴵ η′ → Eq₊ˢ (g η e) (g′ η′ e′)) →
          Eq₊ˢ (Ord₊ˢ.ŝ c t₀ g) (Ord₊ˢ.ŝ c′ t₀′ g′)
    ĉ≅  : ∀ {ℓ′ c c′ t₀ t₀′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {g′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Z}
          {o₀ : Ordˢ ℓ} {o₀′ : Ordˢ ℓ′} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} {o′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Ordˢ ℓ′} →
          t₀ ≃ᶻ t₀′ → (∀ η e η′ e′ → η ≃ᴵ η′ → g η e ≃ᶻ g′ η′ e′) →
          Eq₊ˢ o₀ o₀′ → (∀ η e η′ e′ → η ≃ᴵ η′ → Eq₊ˢ (o η e) (o′ η′ e′)) →
          Eq₊ˢ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) (Ord₊ˢ.ĉᴸ c′ t₀′ g′ o₀′ o′)

Rˢ : ∀ {ℓ} (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → ∀ {ℓ′} → Ordˢ ℓ′ → Set
Rˢ i zero         x b = Eq₊ˢ i Rˢ x b
Rˢ i (suc r)      x b = Rˢ i r x b
Rˢ _ (self {f} n) x b = Eq₊ˢ (f n) Rˢ x b
Rˢ i (lim n r)    x b = Rˢ i r x b

infix 4 _≃ˢ_
_≃ˢ_ : ∀ {ℓ₁ ℓ₂} → Ordˢ ℓ₁ → Ordˢ ℓ₂ → Set
_≃ˢ_ {ℓ₁} = Eq₊ˢ ℓ₁ Rˢ

R→≃ˢ : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) {x : Ordˢ i} {b : Ordˢ ℓ′} → Rˢ i r (intoˢ r x) b → x ≃ˢ b
R→≃ˢ zero      e = e
R→≃ˢ (suc r)   e = R→≃ˢ r e
R→≃ˢ (self n)  e = e
R→≃ˢ (lim n r) e = R→≃ˢ r e

≃→Rˢ : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) {x : Ordˢ i} {b : Ordˢ ℓ′} → x ≃ˢ b → Rˢ i r (intoˢ r x) b
≃→Rˢ zero      e = e
≃→Rˢ (suc r)   e = ≃→Rˢ r e
≃→Rˢ (self n)  e = e
≃→Rˢ (lim n r) e = ≃→Rˢ r e

R-convˢ : ∀ {j ℓ₁ ℓ₂ ℓ′} (r : j ◃ ℓ₁) (r′ : j ◃ ℓ₂) {x : Ordˢ j} {b : Ordˢ ℓ′} → Rˢ j r (intoˢ r x) b → Rˢ j r′ (intoˢ r′ x) b
R-convˢ r r′ e = ≃→Rˢ r′ (R→≃ˢ r e)
```

## §5 搬运

左边四个, 右边四个. 左边按 $x$ 的同一个位置归纳, 右边按 $y$.

```agda
trˢ-≃    : ∀ {a b ℓ′} (e : a ≅ᴵ b) {x : Ordˢ a} {y : Ordˢ ℓ′} → x ≃ˢ y → trˢ e x ≃ˢ y
tr⁻ˢ-≃   : ∀ {a b ℓ′} (e : a ≅ᴵ b) {x : Ordˢ b} {y : Ordˢ ℓ′} → x ≃ˢ y → tr⁻ˢ e x ≃ˢ y
backˢ-≃  : ∀ {j a b ℓ′} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} {v : Ordˢ ℓ′} → u ≃ˢ v → backˢ (resˢ q e) u ≃ˢ v
back⁻ˢ-≃ : ∀ {j a b ℓ′} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} {v : Ordˢ ℓ′} → u ≃ˢ v → backˢ (res⁻ˢ q e) u ≃ˢ v

trˢ-≃ e z≅     = z≅
trˢ-≃ e (s≅ d) = s≅ (trˢ-≃ e d)
trˢ-≃ e (l≅ h) = l≅ (λ n → trˢ-≃ e (h n))
trˢ-≃ e (lh h) = lh (λ n → trˢ-≃ e (h n))
trˢ-≃ e (lr h) = lr (λ n → trˢ-≃ e (h n))
trˢ-≃ e (lᵢ≅ {p = q} {q = q₂} {f = f} {g = g} ej h) =
  lᵢ≅ (≃-respˡ (≅ᴵ-sym (eqˢ (resˢ q e))) ej) λ u v d →
    subst (λ w → trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w))) ≃ˢ g (intoˢ (<→◃ q₂) v))
          (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) u))
          (trˢ-≃ e (h _ v (≃→Rˢ (<→◃ q) (backˢ-≃ q e (R→≃ˢ (<→◃ (ltˢ (resˢ q e))) d)))))
trˢ-≃ (s≅ e) (upˡ {r = zero} d)   = upˡ (trˢ-≃ e d)
trˢ-≃ (l≅ h) (upˡ {r = self n} d) = upˡ (trˢ-≃ (h n) d)
trˢ-≃ e (upʳ d) = upʳ (trˢ-≃ e d)
trˢ-≃ e (ŝ≅ k et eg) = ŝ≅ (trans (sym (kd-≅ e)) k) (trˢ-≃ e et) (λ η d η′ d′ eη → trˢ-≃ e (eg η d η′ d′ eη))
trˢ-≃ e (ĉ≅ dt dg eo eO) = ĉ≅ dt dg (trˢ-≃ e eo) (λ η d η′ d′ eη → trˢ-≃ e (eO η d η′ d′ eη))

tr⁻ˢ-≃ e z≅     = z≅
tr⁻ˢ-≃ e (s≅ d) = s≅ (tr⁻ˢ-≃ e d)
tr⁻ˢ-≃ e (l≅ h) = l≅ (λ n → tr⁻ˢ-≃ e (h n))
tr⁻ˢ-≃ e (lh h) = lh (λ n → tr⁻ˢ-≃ e (h n))
tr⁻ˢ-≃ e (lr h) = lr (λ n → tr⁻ˢ-≃ e (h n))
tr⁻ˢ-≃ e (lᵢ≅ {p = q} {q = q₂} {f = f} {g = g} ej h) =
  lᵢ≅ (≃-respˡ (≅ᴵ-sym (eqˢ (res⁻ˢ q e))) ej) λ u v d →
    subst (λ w → tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w))) ≃ˢ g (intoˢ (<→◃ q₂) v))
          (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) u))
          (tr⁻ˢ-≃ e (h _ v (≃→Rˢ (<→◃ q) (back⁻ˢ-≃ q e (R→≃ˢ (<→◃ (ltˢ (res⁻ˢ q e))) d)))))
tr⁻ˢ-≃ (s≅ e) (upˡ {r = zero} d)   = upˡ (tr⁻ˢ-≃ e d)
tr⁻ˢ-≃ (l≅ h) (upˡ {r = self n} d) = upˡ (tr⁻ˢ-≃ (h n) d)
tr⁻ˢ-≃ e (upʳ d) = upʳ (tr⁻ˢ-≃ e d)
tr⁻ˢ-≃ e (ŝ≅ k et eg) = ŝ≅ (trans (kd-≅ e) k) (tr⁻ˢ-≃ e et) (λ η d η′ d′ eη → tr⁻ˢ-≃ e (eg η d η′ d′ eη))
tr⁻ˢ-≃ e (ĉ≅ dt dg eo eO) = ĉ≅ dt dg (tr⁻ˢ-≃ e eo) (λ η d η′ d′ eη → tr⁻ˢ-≃ e (eO η d η′ d′ eη))

backˢ-≃ zero      (s≅ e) d = tr⁻ˢ-≃ e d
backˢ-≃ (suc q)   (s≅ e) d = backˢ-≃ q e d
backˢ-≃ (lim n q) (l≅ h) d = backˢ-≃ q (h n) d

back⁻ˢ-≃ zero      (s≅ e) d = trˢ-≃ e d
back⁻ˢ-≃ (suc q)   (s≅ e) d = back⁻ˢ-≃ q e d
back⁻ˢ-≃ (lim n q) (l≅ h) d = back⁻ˢ-≃ q (h n) d

≃-trˢ    : ∀ {a b ℓ} (e : a ≅ᴵ b) {x : Ordˢ ℓ} {y : Ordˢ a} → x ≃ˢ y → x ≃ˢ trˢ e y
≃-tr⁻ˢ   : ∀ {a b ℓ} (e : a ≅ᴵ b) {x : Ordˢ ℓ} {y : Ordˢ b} → x ≃ˢ y → x ≃ˢ tr⁻ˢ e y
≃-backˢ  : ∀ {j a b ℓ} (q : j <ᴵ a) (e : a ≅ᴵ b) {v : Ordˢ ℓ} {u : Ordˢ (repˢ (resˢ q e))} → v ≃ˢ u → v ≃ˢ backˢ (resˢ q e) u
≃-back⁻ˢ : ∀ {j a b ℓ} (q : j <ᴵ b) (e : a ≅ᴵ b) {v : Ordˢ ℓ} {u : Ordˢ (repˢ (res⁻ˢ q e))} → v ≃ˢ u → v ≃ˢ backˢ (res⁻ˢ q e) u

≃-trˢ e z≅     = z≅
≃-trˢ e (s≅ d) = s≅ (≃-trˢ e d)
≃-trˢ e (l≅ h) = l≅ (λ n → ≃-trˢ e (h n))
≃-trˢ e (lh h) = lh (λ n → ≃-trˢ e (h n))
≃-trˢ e (lr h) = lr (λ n → ≃-trˢ e (h n))
≃-trˢ e (lᵢ≅ {p = p₁} {q = q} {f = f} {g = g} ej h) =
  lᵢ≅ (≃-respʳ ej (eqˢ (resˢ q e))) λ u v d →
    subst (λ w → f (intoˢ (<→◃ p₁) u) ≃ˢ trˢ e (g (intoˢ (<→◃ q) (backˢ (resˢ q e) w))))
          (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) v))
          (≃-trˢ e (h u _ (≃→Rˢ (<→◃ p₁) (≃-backˢ q e (R→≃ˢ (<→◃ p₁) d)))))
≃-trˢ e (upˡ {r = zero} d)   = upˡ (≃-trˢ e d)
≃-trˢ e (upˡ {r = self n} d) = upˡ (≃-trˢ e d)
≃-trˢ (s≅ e) (upʳ {r = zero} d)   = upʳ (≃-trˢ e d)
≃-trˢ (l≅ h) (upʳ {r = self n} d) = upʳ (≃-trˢ (h n) d)
≃-trˢ e (ŝ≅ k et eg) = ŝ≅ (trans k (kd-≅ e)) (≃-trˢ e et) (λ η d η′ d′ eη → ≃-trˢ e (eg η d η′ d′ eη))
≃-trˢ e (ĉ≅ dt dg eo eO) = ĉ≅ dt dg (≃-trˢ e eo) (λ η d η′ d′ eη → ≃-trˢ e (eO η d η′ d′ eη))

≃-tr⁻ˢ e z≅     = z≅
≃-tr⁻ˢ e (s≅ d) = s≅ (≃-tr⁻ˢ e d)
≃-tr⁻ˢ e (l≅ h) = l≅ (λ n → ≃-tr⁻ˢ e (h n))
≃-tr⁻ˢ e (lh h) = lh (λ n → ≃-tr⁻ˢ e (h n))
≃-tr⁻ˢ e (lr h) = lr (λ n → ≃-tr⁻ˢ e (h n))
≃-tr⁻ˢ e (lᵢ≅ {p = p₁} {q = q} {f = f} {g = g} ej h) =
  lᵢ≅ (≃-respʳ ej (eqˢ (res⁻ˢ q e))) λ u v d →
    subst (λ w → f (intoˢ (<→◃ p₁) u) ≃ˢ tr⁻ˢ e (g (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w))))
          (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) v))
          (≃-tr⁻ˢ e (h u _ (≃→Rˢ (<→◃ p₁) (≃-back⁻ˢ q e (R→≃ˢ (<→◃ p₁) d)))))
≃-tr⁻ˢ e (upˡ {r = zero} d)   = upˡ (≃-tr⁻ˢ e d)
≃-tr⁻ˢ e (upˡ {r = self n} d) = upˡ (≃-tr⁻ˢ e d)
≃-tr⁻ˢ (s≅ e) (upʳ {r = zero} d)   = upʳ (≃-tr⁻ˢ e d)
≃-tr⁻ˢ (l≅ h) (upʳ {r = self n} d) = upʳ (≃-tr⁻ˢ (h n) d)
≃-tr⁻ˢ e (ŝ≅ k et eg) = ŝ≅ (trans k (sym (kd-≅ e))) (≃-tr⁻ˢ e et) (λ η d η′ d′ eη → ≃-tr⁻ˢ e (eg η d η′ d′ eη))
≃-tr⁻ˢ e (ĉ≅ dt dg eo eO) = ĉ≅ dt dg (≃-tr⁻ˢ e eo) (λ η d η′ d′ eη → ≃-tr⁻ˢ e (eO η d η′ d′ eη))

≃-backˢ zero      (s≅ e) d = ≃-tr⁻ˢ e d
≃-backˢ (suc q)   (s≅ e) d = ≃-backˢ q e d
≃-backˢ (lim n q) (l≅ h) d = ≃-backˢ q (h n) d

≃-back⁻ˢ zero      (s≅ e) d = ≃-trˢ e d
≃-back⁻ˢ (suc q)   (s≅ e) d = ≃-back⁻ˢ q e d
≃-back⁻ˢ (lim n q) (l≅ h) d = ≃-back⁻ˢ q (h n) d
```

## §6 运算

```agda
Ωˢ-≃ : ∀ {a b} → a ≃ᴵ b → Ωˢ a ≃ˢ Ωˢ b
Ωˢ-≃ z≃ = s≅ z≅
Ωˢ-≃ (s≃ e) = lᵢ≅ e (λ x y d → upˡ (upʳ d))
Ωˢ-≃ (l≃ h) = l≅ (λ n → upˡ (upʳ (Ωˢ-≃ (h n))))
Ωˢ-≃ (lh≃ h) = lh (λ n → upˡ (upʳ (Ωˢ-≃ (h n))))
Ωˢ-≃ (lr≃ h) = lr (λ n → upˡ (upʳ (Ωˢ-≃ (h n))))

toZ-≃ : ∀ {x y : Ordˢ zero} → x ≃ˢ y → toZ x ≃ᶻ toZ y
toZ-≃ z≅     = zᶻ
toZ-≃ (s≅ d) = sᶻ (toZ-≃ d)
toZ-≃ (l≅ h) = lᶻ (λ n → toZ-≃ (h n))
toZ-≃ (lh h) = lhᶻ (λ n → toZ-≃ (h n))
toZ-≃ (lr h) = lrᶻ (λ n → toZ-≃ (h n))
toZ-≃ (lᵢ≅ {p = ()} e h)
toZ-≃ (upˡ {r = ()} d)
toZ-≃ (upʳ {r = ()} d)
toZ-≃ (ŝ≅ k et eg) = ĉᶻ (toZ-≃ et) (λ η e η′ e′ eη → toZ-≃ (eg η e η′ e′ eη))
                        (toZ-≃ et) (λ η e η′ e′ eη → toZ-≃ (eg η e η′ e′ eη))
toZ-≃ (ĉ≅ dt dg eo eO) = ĉᶻ dt dg (toZ-≃ eo) (λ η e η′ e′ eη → toZ-≃ (eO η e η′ e′ eη))

addˢ-≃ : ∀ {k₁ ℓ₁ k₂ ℓ₂} {σ : Simᴵ k₁ ℓ₁} {σ′ : Simᴵ k₂ ℓ₂} {a : Ordˢ ℓ₁} {a′ : Ordˢ ℓ₂} {b : Ordˢ k₁} {b′ : Ordˢ k₂} →
         kd ℓ₁ ≡ kd ℓ₂ → a ≃ˢ a′ → b ≃ˢ b′ → addˢ a σ b ≃ˢ addˢ a′ σ′ b′
addˢ-≃ kℓ ea z≅     = ea
addˢ-≃ kℓ ea (s≅ e) = s≅ (addˢ-≃ kℓ ea e)
addˢ-≃ kℓ ea (l≅ h) = l≅ (λ n → addˢ-≃ kℓ ea (h n))
addˢ-≃ kℓ ea (lh h) = lh (λ n → addˢ-≃ kℓ ea (h n))
addˢ-≃ kℓ ea (lr h) = lr (λ n → addˢ-≃ kℓ ea (h n))
addˢ-≃ kℓ ea (upˡ {r = zero} e)   = addˢ-≃ kℓ ea e
addˢ-≃ kℓ ea (upˡ {r = self n} e) = addˢ-≃ kℓ ea e
addˢ-≃ kℓ ea (upʳ {r = zero} e)   = addˢ-≃ kℓ ea e
addˢ-≃ kℓ ea (upʳ {r = self n} e) = addˢ-≃ kℓ ea e
addˢ-≃ {σ = σ} {σ′ = σ′} {a = a} {a′ = a′} kℓ ea (lᵢ≅ {p = q} {q = q′} {f = f} {g = g} e h) = lᵢ≅ e λ x y d →
  subst₂ (λ u v → addˢ a σ (f (intoˢ (<→◃ q) u)) ≃ˢ addˢ a′ σ′ (g (intoˢ (<→◃ q′) v)))
         (sym (out-intoˢ (<→◃ (σ q)) x)) (sym (out-intoˢ (<→◃ (σ′ q′)) y))
         (addˢ-≃ kℓ ea (h x y (R-convˢ (<→◃ (σ q)) (<→◃ q) d)))
addˢ-≃ {k₁ = zero}    {k₂ = zero}    kℓ ea (ŝ≅ k et eg) =
  ĉ≅ (toZ-≃ et) (λ η e η′ e′ eη → toZ-≃ (eg η e η′ e′ eη)) (addˢ-≃ kℓ ea et) (λ η e η′ e′ eη → addˢ-≃ kℓ ea (eg η e η′ e′ eη))
addˢ-≃ {k₁ = zero}    {k₂ = suc _}   kℓ ea (ŝ≅ k et eg) = ⊥-elim (tf k)
addˢ-≃ {k₁ = zero}    {k₂ = lim _ _} kℓ ea (ŝ≅ k et eg) = ⊥-elim (tf k)
addˢ-≃ {k₁ = suc _}   {k₂ = zero}    kℓ ea (ŝ≅ k et eg) = ⊥-elim (tf (sym k))
addˢ-≃ {k₁ = lim _ _} {k₂ = zero}    kℓ ea (ŝ≅ k et eg) = ⊥-elim (tf (sym k))
addˢ-≃ {k₁ = suc _}   {k₂ = suc _}   kℓ ea (ŝ≅ k et eg) =
  ŝ≅ kℓ (addˢ-≃ kℓ ea et) (λ η e η′ e′ eη → addˢ-≃ kℓ ea (eg η e η′ e′ eη))
addˢ-≃ {k₁ = suc _}   {k₂ = lim _ _} kℓ ea (ŝ≅ k et eg) =
  ŝ≅ kℓ (addˢ-≃ kℓ ea et) (λ η e η′ e′ eη → addˢ-≃ kℓ ea (eg η e η′ e′ eη))
addˢ-≃ {k₁ = lim _ _} {k₂ = suc _}   kℓ ea (ŝ≅ k et eg) =
  ŝ≅ kℓ (addˢ-≃ kℓ ea et) (λ η e η′ e′ eη → addˢ-≃ kℓ ea (eg η e η′ e′ eη))
addˢ-≃ {k₁ = lim _ _} {k₂ = lim _ _} kℓ ea (ŝ≅ k et eg) =
  ŝ≅ kℓ (addˢ-≃ kℓ ea et) (λ η e η′ e′ eη → addˢ-≃ kℓ ea (eg η e η′ e′ eη))
addˢ-≃ kℓ ea (ĉ≅ dt dg eo eO) = ĉ≅ dt dg (addˢ-≃ kℓ ea eo) (λ η e η′ e′ eη → addˢ-≃ kℓ ea (eO η e η′ e′ eη))
```

## §7 `Run`

```agda
infix 4 _≈ᴴ_
_≈ᴴ_ : ∀ {φ ψ} → Run φ → Run ψ → Set
_≈ᴴ_ {φ} {ψ} R R′ = ∀ {i i′ ℓ ℓ′} (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (ev′ : Ev ℓ′ ψ) (p′ : i′ <ᴵ ℓ′) → i ≃ᴵ i′ → R ev p ≃ˢ R′ ev′ p′

limR : ∀ {φ ψ} {F : ℕ → Run φ} {G : ℕ → Run ψ} → (∀ n → F n ≈ᴴ G n) → limA 0 F ≈ᴴ limA 0 G
limR h ev p ev′ p′ ei = l≅ (λ n → h n ev p ev′ p′ ei)

limH : ∀ {φ ψ} {F : ℕ → Run φ} {G : ℕ → Run ψ} → (∀ n → F (suc n) ≈ᴴ G n) → limA 0 F ≈ᴴ limA 0 G
limH h ev p ev′ p′ ei = lh (λ n → h n ev p ev′ p′ ei)

limT : ∀ {φ ψ} {F : ℕ → Run φ} {G : ℕ → Run ψ} → (∀ n → F (suc n) ≈ᴴ G (suc n)) → limA 0 F ≈ᴴ limA 0 G
limT h ev p ev′ p′ ei = lr (λ n → h n ev p ev′ p′ ei)

sucR : ∀ {φ ψ} {R : Run φ} {R′ : Run ψ} → R ≈ᴴ R′ → sucRun R ≈ᴴ sucRun R′
sucR h ev p ev′ p′ ei = l≅ (iter-R _≃ˢ_ (λ e′ → addˢ-≃ (kd-≃ ei) (h ev p ev′ p′ ei) e′) z≅)

limᵢR : ∀ {φ ψ j j′} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → j′ <ᴵ L}
        {H : Ordˢ j → Run φ} {H′ : Ordˢ j′ → Run ψ} →
        j ≃ᴵ j′ → (∀ x y → x ≃ˢ y → H x ≈ᴴ H′ y) → limᵢA 0 ac H ≈ᴴ limᵢA 0 ac′ H′
limᵢR {ac = ac} {ac′ = ac′} {H = H} {H′ = H′} e h ev p ev′ p′ ei with <ᴵ-dec (ac ev) p | <ᴵ-dec (ac′ ev′) p′
... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) = lᵢ≅ (≃-res e₁ e e₂) λ x y d →
  subst₂ (λ u v → H (tr⁻ˢ e₁ u) ev p ≃ˢ H′ (tr⁻ˢ e₂ v) ev′ p′)
         (sym (out-intoˢ (<→◃ r₁) x)) (sym (out-intoˢ (<→◃ r₂) y))
         (h _ _ (tr⁻ˢ-≃ e₁ (≃-tr⁻ˢ e₂ (R→≃ˢ (<→◃ r₁) d))) ev p ev′ p′ ei)
... | injᵃ r | injᵇ s  = ⊥-elim (clash≃ e ei r (inj₁ s))
... | injᵃ r | injᶜ c  = ⊥-elim (clash≃ e ei r (inj₂ (≅ᴵ-sym c)))
... | injᵇ s | injᵃ r  = ⊥-elim (clash≃′ e ei r (inj₁ s))
... | injᶜ c | injᵃ r  = ⊥-elim (clash≃′ e ei r (inj₂ (≅ᴵ-sym c)))
... | injᵇ _ | injᵇ _  = l≅ (λ m → h _ _ (iter-R _≃ˢ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≃ e) m) ev p ev′ p′ ei)
... | injᵇ _ | injᶜ _  = l≅ (λ m → h _ _ (iter-R _≃ˢ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≃ e) m) ev p ev′ p′ ei)
... | injᶜ _ | injᵇ _  = l≅ (λ m → h _ _ (iter-R _≃ˢ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≃ e) m) ev p ev′ p′ ei)
... | injᶜ _ | injᶜ _  = l≅ (λ m → h _ _ (iter-R _≃ˢ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≃ e) m) ev p ev′ p′ ei)

ĉR : ∀ {φ ψ c c′ t₀ t₀′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {g′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Z}
     {O₀ : Run φ} {O : (η : Ordᴵ) → c ⊑ᴵ η → Run φ} {O₀′ : Run ψ} {O′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Run ψ} →
     t₀ ≃ᶻ t₀′ → (∀ η e η′ e′ → η ≃ᴵ η′ → g η e ≃ᶻ g′ η′ e′) →
     O₀ ≈ᴴ O₀′ → (∀ η e η′ e′ → η ≃ᴵ η′ → O η e ≈ᴴ O′ η′ e′) → ĉA 0 c t₀ g O₀ O ≈ᴴ ĉA 0 c′ t₀′ g′ O₀′ O′
ĉR dt dg h₀ h ev p ev′ p′ ei = ĉ≅ dt dg (h₀ ev p ev′ p′ ei) (λ η e η′ e′ eη → h η e η′ e′ eη ev p ev′ p′ ei)

ŝR : ∀ {φ ψ c c′} {T₀ : Run φ} {G : (η : Ordᴵ) → c ⊑ᴵ η → Run φ} {T₀′ : Run ψ} {G′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Run ψ} →
     T₀ ≈ᴴ T₀′ → (∀ η e η′ e′ → η ≃ᴵ η′ → G η e ≈ᴴ G′ η′ e′) → ŝA 0 c T₀ G ≈ᴴ ŝA 0 c′ T₀′ G′
ŝR h₀ h ev p ev′ p′ ei = ŝ≅ (kd-≃ ei) (h₀ ev p ev′ p′ ei) (λ η e η′ e′ eη → h η e η′ e′ eη ev p ev′ p′ ei)

cloR : ∀ {φ φ′} {t : Run (φ ⊔ fk zero)} {g : (η : Ordᴵ) → Run (φ ⊔ fk η)}
       {t′ : Run (φ′ ⊔ fk zero)} {g′ : (η : Ordᴵ) → Run (φ′ ⊔ fk η)} →
       t ≈ᴴ t′ → (∀ η η′ → η ≃ᴵ η′ → g η ≈ᴴ g′ η′) → cloA 0 t g ≈ᴴ cloA 0 t′ g′
cloR {φ} {φ′} ht hg ev p ev′ p′ ei =
  ŝ≅ (kd-≃ ei) (ht ev p ev′ p′ ei)
     (λ η e η′ e′ eη → hg η η′ eη _ (lim 0 (iF (bound (φ ⊔ fk zero) ev p))) _ (lim 0 (iF (bound (φ′ ⊔ fk zero) ev′ p′))) ei)

wkR : ∀ {φ φ′ ψ ψ′} {R : Run φ} {R′ : Run φ′} (le : ∀ {L} → Ev L ψ → Ev L φ) (le′ : ∀ {L} → Ev L ψ′ → Ev L φ′) →
      R ≈ᴴ R′ → wk 0 le R ≈ᴴ wk 0 le′ R′
wkR le le′ h ev p ev′ p′ ei = h (le ev) p (le′ ev′) p′ ei

r∅ : ∅ᴿ ≈ᴴ ∅ᴿ
r∅ ev p ev′ p′ ei = Ωˢ-≃ ei
```
