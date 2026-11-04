# 值验收 (计值): 去头关系落到树

> 入口 [EmbVV](EmbVV.lagda.md). 不读记号. `Hd⁰ a b`: 第 0 层的树只差头. `force≃`: `≃ᶻ` 相关的 `Z`, 两边各带自己的证书, 计值 `Hd⁰` 相关: 这里才用到闭包节点的链, 链点逐项相关, 层号因此 `≃ᴵ` 相关, 再喂回去. `Hd⁰→≈ᵛ`: 头被下一项支配 (`HS`), 所以同值. 这就是 `≼` 过得了, `⊑⁰` 过不了的那一步: `suc` 下面的头不再被吃掉, 但 `≼` 对 `suc` 单调.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EmbVVForce where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level hiding (z≅; s≅; l≅; lᵢ≅; upˡ; upʳ)
open import OCF.Free.Level using (s≅; l≅) renaming (z≅ to z≅₀)
open import OCF.Free.Prefix using (Z)
open import OCF.Free.Force using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; outsᴺ; outsᴺ-≅)
open import OCF.Align.ValueJudgeBase using (_≼_; _≈ᵛ_; ≼-trans; ≼lim; ⊑→≼; ≼-refl) renaming (z≼ to vz≼; s≼s to vs≼s; l≼ to vl≼)
open import OCF.Align.EmbVVEq
```

## §1 树上的关系

```agda
data Hd⁰ : Ordᶜ zero → Ordᶜ zero → Set where
  hz  : Hd⁰ zero zero
  hsu : ∀ {a b} → Hd⁰ a b → Hd⁰ (suc a) (suc b)
  hl  : ∀ {f g : ℕ → Ordᶜ zero} → (∀ n → Hd⁰ (f n) (g n)) → Hd⁰ (lim f) (lim g)
  hh  : ∀ {f g : ℕ → Ordᶜ zero} → (∀ n → Hd⁰ (f (suc n)) (g n)) → Hd⁰ (lim f) (lim g)
  hr  : ∀ {f g : ℕ → Ordᶜ zero} → (∀ n → Hd⁰ (f (suc n)) (g (suc n))) → Hd⁰ (lim f) (lim g)

Hd-≅ˡ : ∀ {a a′ b} → a ≅ a′ → Hd⁰ a′ b → Hd⁰ a b
Hd-≅ˡ OCF.Free.Level.z≅ hz = hz
Hd-≅ˡ (OCF.Free.Level.s≅ e) (hsu d) = hsu (Hd-≅ˡ e d)
Hd-≅ˡ (OCF.Free.Level.l≅ h) (hl k) = hl (λ n → Hd-≅ˡ (h n) (k n))
Hd-≅ˡ (OCF.Free.Level.l≅ h) (hh k) = hh (λ n → Hd-≅ˡ (h (suc n)) (k n))
Hd-≅ˡ (OCF.Free.Level.l≅ h) (hr k) = hr (λ n → Hd-≅ˡ (h (suc n)) (k n))
Hd-≅ˡ (OCF.Free.Level.lᵢ≅ {p = ()} e h) d
Hd-≅ˡ (OCF.Free.Level.upˡ {r = ()} e) d
Hd-≅ˡ (OCF.Free.Level.upʳ {r = ()} e) d

Hd-≅ʳ : ∀ {a b b′} → Hd⁰ a b → b ≅ b′ → Hd⁰ a b′
Hd-≅ʳ hz OCF.Free.Level.z≅ = hz
Hd-≅ʳ (hsu d) (OCF.Free.Level.s≅ e) = hsu (Hd-≅ʳ d e)
Hd-≅ʳ (hl k) (OCF.Free.Level.l≅ h) = hl (λ n → Hd-≅ʳ (k n) (h n))
Hd-≅ʳ (hh k) (OCF.Free.Level.l≅ h) = hh (λ n → Hd-≅ʳ (k n) (h n))
Hd-≅ʳ (hr k) (OCF.Free.Level.l≅ h) = hr (λ n → Hd-≅ʳ (k n) (h (suc n)))

Hd-lvl : ∀ {a b} (ha : HS a) (hb : HS b) → Hd⁰ a b → toLevel a ha ≃ᴵ toLevel b hb
Hd-lvl ha hb hz = z≃
Hd-lvl ha hb (hsu d) = s≃ (Hd-lvl (hs⁻ ha) (hs⁻ hb) d)
Hd-lvl ha hb (hl k) = l≃ (λ n → Hd-lvl (hl₁ ha n) (hl₁ hb n) (k n))
Hd-lvl ha hb (hh k) = lh≃ (λ n → Hd-lvl (hl₁ ha (suc n)) (hl₁ hb n) (k n))
Hd-lvl ha hb (hr k) = lr≃ (λ n → Hd-lvl (hl₁ ha (suc n)) (hl₁ hb (suc n)) (k n))

Hd→≼ : ∀ {a b} → HS a → HS b → Hd⁰ a b → a ≼ b
Hd→≼ ha hb hz = vz≼
Hd→≼ ha hb (hsu d) = vs≼s (Hd→≼ (hs⁻ ha) (hs⁻ hb) d)
Hd→≼ ha hb (hl k) = vl≼ (λ n → ≼lim n (Hd→≼ (hl₁ ha n) (hl₁ hb n) (k n)))
Hd→≼ {a = lim f} ha hb (hh k) = vl≼ go
  where
  go : ∀ n → f n ≼ _
  go zero = ≼-trans (⊑→≼ (f 0) (hl₂ ha 0)) (≼lim 0 (Hd→≼ (hl₁ ha 1) (hl₁ hb 0) (k 0)))
  go (suc n) = ≼lim n (Hd→≼ (hl₁ ha (suc n)) (hl₁ hb n) (k n))
Hd→≼ {a = lim f} ha hb (hr k) = vl≼ go
  where
  go : ∀ n → f n ≼ _
  go zero = ≼-trans (⊑→≼ (f 0) (hl₂ ha 0)) (≼lim 1 (Hd→≼ (hl₁ ha 1) (hl₁ hb 1) (k 0)))
  go (suc n) = ≼lim (suc n) (Hd→≼ (hl₁ ha (suc n)) (hl₁ hb (suc n)) (k n))

Hd→≽ : ∀ {a b} → HS a → HS b → Hd⁰ a b → b ≼ a
Hd→≽ ha hb hz = vz≼
Hd→≽ ha hb (hsu d) = vs≼s (Hd→≽ (hs⁻ ha) (hs⁻ hb) d)
Hd→≽ ha hb (hl k) = vl≼ (λ n → ≼lim n (Hd→≽ (hl₁ ha n) (hl₁ hb n) (k n)))
Hd→≽ ha hb (hh k) = vl≼ (λ n → ≼lim (suc n) (Hd→≽ (hl₁ ha (suc n)) (hl₁ hb n) (k n)))
Hd→≽ {b = lim g} ha hb (hr k) = vl≼ go
  where
  go : ∀ n → g n ≼ _
  go zero = ≼-trans (⊑→≼ (g 0) (hl₂ hb 0)) (≼lim 1 (Hd→≽ (hl₁ ha 1) (hl₁ hb 1) (k 0)))
  go (suc n) = ≼lim (suc n) (Hd→≽ (hl₁ ha (suc n)) (hl₁ hb (suc n)) (k n))

Hd→≈ᵛ : ∀ {a b} → HS a → HS b → Hd⁰ a b → a ≈ᵛ b
Hd→≈ᵛ ha hb d = Hd→≼ ha hb d , Hd→≽ ha hb d
```

## §2 计值

```agda
force≃ : ∀ {x y} → x ≃ᶻ y → (G : Goodᴺ x) (G′ : Goodᴺ y) → Hd⁰ (forceᴺ x G) (forceᴺ y G′)
force≃ zᶻ gz gz = hz
force≃ (sᶻ d) (gs G) (gs G′) = hsu (force≃ d G G′)
force≃ (lᶻ h) (gl G _) (gl G′ _) = hl (λ n → force≃ (h n) (G n) (G′ n))
force≃ (lhᶻ h) (gl G _) (gl G′ _) = hh (λ n → force≃ (h n) (G (suc n)) (G′ n))
force≃ (lrᶻ h) (gl G _) (gl G′ _) = hr (λ n → force≃ (h n) (G (suc n)) (G′ (suc n)))
force≃ (ĉᶻ dt dg dp dO) (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) (gc ys′ hy′ dy′ G₀′ l₀′ Gg′ lE′ Go₀′ Go′ mo₀′ mo′) = hl go
  where
  eY : ∀ m → Hd⁰ (ys m) (ys′ m)
  eY zero = Hd-≅ˡ (≅-sym l₀) (Hd-≅ʳ (force≃ dt G₀ G₀′) l₀′)
  eY (suc m) = Hd-≅ˡ (≅-sym (lE m)) (Hd-≅ʳ (force≃ (dg _ _ _ _ (Hd-lvl (hy m) (hy′ m) (eY m))) (Gg m) (Gg′ m)) (lE′ m))
  go : ∀ n → Hd⁰ (outsᴺ (forceᴺ _ Go₀) (λ k → forceᴺ _ (Go k)) n) (outsᴺ (forceᴺ _ Go₀′) (λ k → forceᴺ _ (Go′ k)) n)
  go zero = force≃ dp Go₀ Go₀′
  go (suc k) = force≃ (dO _ _ _ _ (Hd-lvl (hy k) (hy′ k) (eY k))) (Go k) (Go′ k)

-- 主定理的形状: 只要两边有证书
force≈ : ∀ {x y} → x ≃ᶻ y → (G : Goodᴺ x) (G′ : Goodᴺ y) → forceᴺ x G ≈ᵛ forceᴺ y G′
force≈ {x} {y} d G G′ = Hd→≈ᵛ (forceᴺ-HS x G) (forceᴺ-HS y G′) (force≃ d G G′)
```
