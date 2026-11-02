# 降维打击的检验: 底座 (去 `up` 的树与折叠)

> 底座, 结论写在 [InaccStrike](InaccStrike.lagda.md). 不含记号.

`up` 对折叠透明 (InaccTree 的 `up-any`), 所以比较树时应该把它抹掉. `St` 是抹掉 `up` 与层号下标后的树, `ψS` 是 `St` 上的折叠, `ψS-strip` 说它就是 `Fold.ψ`. 外延性 `Funext` 只作模块参数, 不是公设.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccStrikeBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import OCF.Align.InaccTreeBase
```

## §1 去 `up` 的树

```agda
Funext : Set₁
Funext = ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

data St : Set where
  zero : St
  suc  : St → St
  lim  : (ℕ → St) → St
  limᵢ : (ℓ : Lv) → (Ordᴸ ℓ → St) → St

strip : ∀ {k} → Ordᴸ k → St
strip zero    = zero
strip (suc x) = suc (strip x)
strip (lim f) = lim (λ n → strip (f n))
strip {k} (limᵢ r f) = limᵢ (at k r) (λ y → strip (f (intoL k r y)))
strip {suc k}    (up d x) = strip x
strip {lim f}    (up d x) = strip x
strip {limᴼ k g} (up d x) = strip x

addS : St → St → St
addS a zero       = a
addS a (suc b)    = suc (addS a b)
addS a (lim f)    = lim (λ n → addS a (f n))
addS a (limᵢ ℓ f) = limᵢ ℓ (λ y → addS a (f y))

toLvS : St → Lv
toLvS zero       = zero
toLvS (suc x)    = suc (toLvS x)
toLvS (lim f)    = lim (λ n → toLvS (f n))
toLvS (limᵢ ℓ f) = limᴼ ℓ (λ y → toLvS (f y))

dz : St → Ordᴸ zero
dz zero       = zero
dz (suc x)    = suc (dz x)
dz (lim f)    = lim (λ n → dz (f n))
dz (limᵢ _ _) = zero

out-into : ∀ ℓ r (y : Ordᴸ (at ℓ r)) → outL ℓ r (intoL ℓ r y) ≡ y
out-into (suc k)    (inj₁ _)        y = refl
out-into (suc k)    (inj₂ r)        y = out-into k r y
out-into (lim f)    (n , r)         y = out-into (f n) r y
out-into (limᴼ k g) (inj₁ (inj₁ _)) y = refl
out-into (limᴼ k g) (inj₁ (inj₂ r)) y = out-into k r y
out-into (limᴼ k g) (inj₂ (x , r))  y = out-into (g x) r y

```

```agda
into-out : ∀ ℓ r (y : Low ℓ r) → intoL ℓ r (outL ℓ r y) ≡ y
into-out (suc k)    (inj₁ _)        y = refl
into-out (suc k)    (inj₂ r)        y = into-out k r y
into-out (lim f)    (n , r)         y = into-out (f n) r y
into-out (limᴼ k g) (inj₁ (inj₁ _)) y = refl
into-out (limᴼ k g) (inj₁ (inj₂ r)) y = into-out k r y
into-out (limᴼ k g) (inj₂ (x , r))  y = into-out (g x) r y
```

## §2 折叠

`dispS` 是一等函数, 不用 `with`: 证明里可以按判决分情形而不被辅助函数挡住.

```agda
module FoldS (D : Oracle) where
  ψS    : ∀ {i} → St → Ordᴸ i
  dispS : ∀ {i ℓ} → (Ordᴸ ℓ → St) → Verdict ℓ i → Ordᴸ i

  ψS {i} zero       = Ω i
  ψS {i} (suc a)    = lim (iter (ψS {i} a +_) zero)
  ψS {i} (lim f)    = lim (λ n → ψS {i} (f n))
  ψS {i} (limᵢ ℓ f) = dispS f (D ℓ i)

  dispS {i} f (pen r b) = limᵢ r (λ y → ψS {i} (f (b (outL i r y))))
  dispS {i} {ℓ} f rise  = lim (λ n → ψS {i} (f (iter (λ x → ψS {ℓ} (f x)) (Ω ℓ) n)))
```

## §3 外延性下的引理

```agda
sucS : St → St
sucS = suc
limS : (ℕ → St) → St
limS = lim
limᵢS : (ℓ : Lv) → (Ordᴸ ℓ → St) → St
limᵢS = limᵢ
sucL : Lv → Lv
sucL = suc
limL : (ℕ → Lv) → Lv
limL = lim
limOL : (k : Lv) → (Ordᴸ k → Lv) → Lv
limOL = limᴼ

module Ext (fe : Funext) where
  limᵢ-cast : ∀ {m n : Lv} (e : m ≡ n) (G : Ordᴸ m → St) (H : Ordᴸ n → St) →
              (∀ y → G y ≡ H (subst Ordᴸ e y)) → limᵢS m G ≡ limᵢS n H
  limᵢ-cast refl G H h = cong (limᵢS _) (fe h)

  strip-add : ∀ {k ℓ} (a : Ordᴸ ℓ) (σ : Sim k ℓ) (b : Ordᴸ k) →
              strip (add a σ b) ≡ addS (strip a) (strip b)
  strip-add a σ zero    = refl
  strip-add a σ (suc b) = cong sucS (strip-add a σ b)
  strip-add a σ (lim f) = cong limS (fe (λ n → strip-add a σ (f n)))
  strip-add {k} {ℓ} a σ (limᵢ r f) =
    limᵢ-cast (proj₂ (σ r)) _ _ λ y →
      trans (strip-add a σ (f (intoL k r (subst Ordᴸ (proj₂ (σ r)) (outL ℓ (proj₁ (σ r)) (intoL ℓ (proj₁ (σ r)) y))))))
            (cong (λ z → addS (strip a) (strip (f (intoL k r (subst Ordᴸ (proj₂ (σ r)) z)))))
                  (out-into ℓ (proj₁ (σ r)) y))
  strip-add {suc k}    a σ (up d x) = strip-add a (σ ∘σ ι (suc k) d) x
  strip-add {lim f}    a σ (up d x) = strip-add a (σ ∘σ ι (lim f) d) x
  strip-add {limᴼ k g} a σ (up d x) = strip-add a (σ ∘σ ι (limᴼ k g) d) x

  toLv-strip : ∀ {k} (x : Ordᴸ k) → toLvS (strip x) ≡ toLv x
  toLv-strip zero    = refl
  toLv-strip (suc x) = cong sucL (toLv-strip x)
  toLv-strip (lim f) = cong limL (fe (λ n → toLv-strip (f n)))
  toLv-strip {k} (limᵢ r f) = cong (limOL (at k r)) (fe (λ y → toLv-strip (f (intoL k r y))))
  toLv-strip {suc k}    (up d x) = toLv-strip x
  toLv-strip {lim f}    (up d x) = toLv-strip x
  toLv-strip {limᴼ k g} (up d x) = toLv-strip x

  module Link (D : Oracle) where
    open FoldS D
    open Fold D using (ψ)

    ψS-strip : ∀ {i k} (x : Ordᴸ k) → ψS {i} (strip x) ≡ ψ {i} x
    ψS-strip zero    = refl
    ψS-strip {i} (suc a) = cong (λ z → lim (iter (z +_) zero)) (ψS-strip {i} a)
    ψS-strip {i} (lim f) = cong lim (fe (λ n → ψS-strip {i} (f n)))
    ψS-strip {i} {k} (limᵢ r f) with D (at k r) i
    ... | pen r′ b = cong (limᵢ r′) (fe (λ y → ψS-strip {i} (f (intoL k r (b (outL i r′ y))))))
    ... | rise     = cong lim (fe (λ n →
      trans (cong (λ h → ψS {i} (strip (f (intoL k r (iter h (Ω (at k r)) n)))))
                  (fe (λ x → ψS-strip {at k r} (f (intoL k r x)))))
            (ψS-strip {i} (f (intoL k r (iter (λ x → ψ {at k r} (f (intoL k r x))) (Ω (at k r)) n))))))
    ψS-strip {i} {suc k}    (up d x) = ψS-strip {i} x
    ψS-strip {i} {lim f}    (up d x) = ψS-strip {i} x
    ψS-strip {i} {limᴼ k g} (up d x) = ψS-strip {i} x
```
