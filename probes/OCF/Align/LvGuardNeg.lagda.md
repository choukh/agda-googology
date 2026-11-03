# 带守卫的层号上, 什么仍然是假的 (编译过的否定)

> 不含记号. 结论写在 [LvGuard](LvGuard.lagda.md). 好层号 `GLG` 与 `GL` 一样含 `Ordᴵ` 的全部 (`ofLᵍ`), 所以 `no-read` 不因换层号类型而消失 (`no-read-GLG`). **任意路径对任意路径的比较是 WLPO (`no-bra-cmp`).** 这里的比较 `cmpF`, `cmpP` 不是它的特例: 一边是第一路径. 守卫在这个层号上切开反例族 (`G-rise`, `G-exclᴸ`), 族内没有三歧 (`¬Gᴸ-tri`), 没有公共上界 (`Gᴸ-unbounded`).

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LvGuardNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.Level using (Ordᴵ; _<ᴵ_; _⊑ᴵ_; _≺ᴵ_; _≅ᴵ_; via; zero; suc; lim; s⊑; z⊑; z≅; ωᴵ; ≅ᴵ-refl; ≅ᴵ-sym)
open import OCF.Align.InaccFloorBase using (≅→⊑ᴵ)
open import Data.Unit using (tt)
open import OCF.Align.LvIRNeg using (WLPO)
open import OCF.Align.ScafOmega2Family using (yᴵ; ω⁺; no-read-ᴵ; G-excl; G-y-in; m₁; m₂; G-m₁; G-m₂; ¬≺₁₂; ¬≺₂₁; ¬≅₁₂; ≺→⊑; G-unbounded)
open import OCF.Align.LvGuardBase
open Lv Dom₀
open import OCF.Align.LvGuardFeed
```

## §1 反例族仍在好层号里

```agda
y∈GLG : (ℕ → Bool) → GLG
y∈GLG s = ofLᵍ (yᴵ s)

back : ∀ {a b} → Below (ofL a) (ofL b) → a ≺ᴵ b
back {a} {b} (pre d q) with pull b q
... | a′ , refl , q′ = via (ofL≈⁻ d) q′

-- 对全部好层号的目标判决: WLPO
no-read-GLG : (∀ (x : GLG) → Below (proj₁ x) (ofL ω⁺) ⊎ Below (ofL ωᴵ) (proj₁ x)) → WLPO
no-read-GLG d = no-read-ᴵ d′ where
  d′ : ∀ a → a ≺ᴵ ω⁺ ⊎ ω⁺ ⊑ᴵ a
  d′ a with d (ofLᵍ a)
  ... | inj₁ q = inj₁ (back q)
  ... | inj₂ q with back q
  ...   | via e r = inj₂ (s⊑ e r)
```

## §2 任意路径的比较是 WLPO

`no-bra-cmp`: $\Omega$ 上两条任意的路径若总有三歧, 就是 WLPO. 这就是不能写 "全分支比较" 的具体形式 (`noBT`, `dec→WLPO` 的同类). `no-bra-cmp` 不与 `cmpF` 矛盾: `cmpF` 的左边是第一路径, 而第一路径到不了分支 (`first-Ω`).

```agda
Ωˡ : LG
Ωˡ = lc zero zero (λ η _ → ofL η)

bra-of : ∀ a → ofL a < Ωˡ
bra-of a = bra (suc a) z⊑ zero

no-bra-cmp : (∀ {a b} → a < Ωˡ → b < Ωˡ → Below a b ⊎ Below b a ⊎ (a ≈ b)) → WLPO
no-bra-cmp d = no-read-ᴵ d′ where
  d′ : ∀ a → a ≺ᴵ ω⁺ ⊎ ω⁺ ⊑ᴵ a
  d′ a with d (bra-of a) (bra-of ω⁺)
  ... | inj₁ q = inj₁ (back q)
  ... | inj₂ (inj₁ q) = inj₂ (≺→⊑ (back q))
  ... | inj₂ (inj₂ e) = inj₂ (≅→⊑ᴵ (≅ᴵ-sym (ofL≈⁻ e)))

-- 第一路径到不了分支
first-Ω : ∀ {k} → k ≪ Ωᴸ → k ≡ zero
first-Ω (fst zero) = refl

first-Ωˡ : ∀ {k} → k ≪ Ωˡ → ⊥
first-Ωˡ (fst ())

Cf-Ωˡ : Cfˢ Ωˡ
Cf-Ωˡ = ((λ η e → ⊴-zero) , (λ η e η′ e′ d → ofL⊴ (≻ᴵ→⊑ d)) , tt , (λ η e → WF-ofL η)) ,
        o≈ z≅ z≈ (λ η e η′ e′ k → ofL≈ k)
```

## §3 守卫在这个层号上

与 [ScafOmega2Family](ScafOmega2Family.lagda.md) 的 `G` 同形, 搬到 `GLG`. `G-rise` 是定义本身: 证据就是答案, 不比较. 向上封闭由 `Below` 与 `⊑ⁿ` 给.

```agda
Gᴸ : Ordᴵ → GLG → Set
Gᴸ τ x = Below (ofL τ) (proj₁ x)

G-rise : ∀ {τ x} → Gᴸ τ x → Below (ofL τ) (proj₁ x)
G-rise e = e

Gᴸ-up : ∀ {τ} {x y : GLG} → Gᴸ τ x → proj₁ x ⊑ⁿ proj₁ y → Gᴸ τ y
Gᴸ-up (pre d p) h with h p
... | pre d′ p′ = pre (≈-trans d d′) p′

G-exclᴸ : ∀ s → Gᴸ ω⁺ (y∈GLG s) → (∀ n → s n ≡ false) → ⊥
G-exclᴸ s e af with back {a = ω⁺} {b = yᴵ s} e
... | via d q = G-excl s (s⊑ d q) af

-- 但不是把反例族整个排除
G-y-inᴸ : Gᴸ ω⁺ (y∈GLG (λ _ → true))
G-y-inᴸ with G-y-in
... | s⊑ e q = pre (ofL≈ e) (ofL< q)

toG : ∀ {τ a} → suc τ ⊑ᴵ a → Gᴸ τ (ofLᵍ a)
toG (s⊑ e q) = pre (ofL≈ e) (ofL< q)

-- 族内没有三歧
¬Gᴸ-tri : (∀ (x y : GLG) → Gᴸ ω⁺ x → Gᴸ ω⁺ y → Below (proj₁ x) (proj₁ y) ⊎ Below (proj₁ y) (proj₁ x) ⊎ (proj₁ x ≈ proj₁ y)) → ⊥
¬Gᴸ-tri t with t (ofLᵍ m₁) (ofLᵍ m₂) (toG G-m₁) (toG G-m₂)
... | inj₁ q = ¬≺₁₂ (back q)
... | inj₂ (inj₁ q) = ¬≺₂₁ (back q)
... | inj₂ (inj₂ e) = ¬≅₁₂ (ofL≈⁻ e)

-- 没有公共上界
Gᴸ-unbounded : ∀ τ b → (∀ (x : GLG) → Gᴸ τ x → Below (proj₁ x) (ofL b)) → ⊥
Gᴸ-unbounded τ b H = G-unbounded τ b (λ a e → back (H (ofLᵍ a) (toG e)))
```
