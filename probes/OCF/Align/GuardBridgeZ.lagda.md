# 桥 (二): 界只要一个方向的互模拟

> 不含记号. 结论写在 [GuardBridge](GuardBridge.lagda.md). `x ≲ᶻ y`: 同形, 闭包的界 $c\sqsubseteq c'$, 分支只在同一个 $\eta$ 上比较. `Good-≲`: 对面有 `Goodᴺ`, 这边就有, 而且计值 $\cong$. 这是 [GuardTightCert](GuardTightCert.lagda.md) 的 `Goodᴺ-c` 的递归版本: 那里只有最外层的界不同, 里面是 $\cong^{\mathsf z}$. **这条引理只需要下界的方向: 链 `ys` 不变, $c\sqsubseteq c'\sqsubseteq$ `ys`.**

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardBridgeZ where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z)
open import OCF.Free.Force using (Goodᴺ; gz; gs; gl; gc; forceᴺ; outsᴺ-≅)

infix 4 _≲ᶻ_
data _≲ᶻ_ : Z → Z → Set where
  zl : Z.zero ≲ᶻ Z.zero
  sl : ∀ {x y} → x ≲ᶻ y → Z.suc x ≲ᶻ Z.suc y
  ll : ∀ {f g : ℕ → Z} → (∀ n → f n ≲ᶻ g n) → Z.lim f ≲ᶻ Z.lim g
  ĉl : ∀ {c c′ t₀ t₀′ o₀ o₀′} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z} {g′ o′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Z} →
       c ⊑ᴵ c′ → t₀ ≲ᶻ t₀′ → (∀ η e e′ → g η e ≲ᶻ g′ η e′) →
       o₀ ≲ᶻ o₀′ → (∀ η e e′ → o η e ≲ᶻ o′ η e′) → Z.ĉᴸ c t₀ g o₀ o ≲ᶻ Z.ĉᴸ c′ t₀′ g′ o₀′ o′

Good-≲ : ∀ {x y} → x ≲ᶻ y → (G′ : Goodᴺ y) → Σ (Goodᴺ x) λ G → forceᴺ x G ≅ forceᴺ y G′
Good-≲ zl gz = gz , z≅
Good-≲ (sl d) (gs G′) with Good-≲ d G′
... | G , e = gs G , s≅ e
Good-≲ {x = Z.lim f} {y = Z.lim g} (ll h) (gl G′ st′) = gl Gs st , l≅ (λ n → proj₂ (Good-≲ (h n) (G′ n)))
  where
  Gs : ∀ n → Goodᴺ (f n)
  Gs n = proj₁ (Good-≲ (h n) (G′ n))
  st : ∀ n → forceᴺ (f n) (Gs n) ⊑⁰ forceᴺ (f (suc n)) (Gs (suc n))
  st n = ⊑-trans (≅→⊑ (proj₂ (Good-≲ (h n) (G′ n))))
         (⊑-trans (st′ n) (≅→⊑ (≅-sym (proj₂ (Good-≲ (h (suc n)) (G′ (suc n)))))))
Good-≲ {x = Z.ĉᴸ c t₀ g o₀ o} (ĉl {c′ = c′} {t₀′ = t₀′} {o₀′ = o₀′} {g′ = g′} {o′ = o′} ec dt dg dp dO) (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) =
  gc ys hy dy′ G₀′ l₀′ Gg′ lE′ Go₀′ Go′ mo₀′ mo′ , l≅ (outsᴺ-≅ (proj₂ (Good-≲ dp Go₀)) (λ k → proj₂ (Good-≲ (dOk k) (Go k))))
  where
  dy′ : ∀ m → c ⊑ᴵ toLevel (ys m) (hy m)
  dy′ m = ⊑ᴵ-trans ec (dy m)
  G₀′ : Goodᴺ t₀
  G₀′ = proj₁ (Good-≲ dt G₀)
  l₀′ : forceᴺ t₀ G₀′ ≅ ys 0
  l₀′ = ≅-trans (proj₂ (Good-≲ dt G₀)) l₀
  dgm : ∀ m → g (toLevel (ys m) (hy m)) (dy′ m) ≲ᶻ g′ (toLevel (ys m) (hy m)) (dy m)
  dgm m = dg _ (dy′ m) (dy m)
  Gg′ : ∀ m → Goodᴺ (g (toLevel (ys m) (hy m)) (dy′ m))
  Gg′ m = proj₁ (Good-≲ (dgm m) (Gg m))
  lE′ : ∀ m → forceᴺ _ (Gg′ m) ≅ ys (suc m)
  lE′ m = ≅-trans (proj₂ (Good-≲ (dgm m) (Gg m))) (lE m)
  Go₀′ : Goodᴺ o₀
  Go₀′ = proj₁ (Good-≲ dp Go₀)
  dOk : ∀ k → o (toLevel (ys k) (hy k)) (dy′ k) ≲ᶻ o′ (toLevel (ys k) (hy k)) (dy k)
  dOk k = dO _ (dy′ k) (dy k)
  Go′ : ∀ k → Goodᴺ (o (toLevel (ys k) (hy k)) (dy′ k))
  Go′ k = proj₁ (Good-≲ (dOk k) (Go k))
  mo₀′ : forceᴺ o₀ Go₀′ ⊑⁰ forceᴺ _ (Go′ 0)
  mo₀′ = ⊑-trans (≅→⊑ (proj₂ (Good-≲ dp Go₀))) (⊑-trans mo₀ (≅→⊑ (≅-sym (proj₂ (Good-≲ (dOk 0) (Go 0))))))
  mo′ : ∀ k → forceᴺ _ (Go′ k) ⊑⁰ forceᴺ _ (Go′ (suc k))
  mo′ k = ⊑-trans (≅→⊑ (proj₂ (Good-≲ (dOk k) (Go k)))) (⊑-trans (mo k) (≅→⊑ (≅-sym (proj₂ (Good-≲ (dOk (suc k)) (Go (suc k)))))))
```
