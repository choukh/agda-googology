# 层号判决的范数模: 可数下标标准形上的单调与有界共尾性 (验收)

> **验收节.** 对 [Standard](Standard.lagda.md) 的 `NF` (ψ-下标都可数): `fs-monoᴺ` 是 GoodLBase 的 `fs-mono₁` 换成 `NF`; `cofinB` 是 Standard 的 `cofin` 加上界: **`v < u ⟹ v < u[n]`, 其中 `n ≤ 1 + sz v`.** 上界不依赖 `u`. 证明逐支照抄, 只多记一个数. 结论在 [InaccModulus](InaccModulus.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccModulusNF where

open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s) renaming (_≤_ to _≤ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m≤n+m; <⇒≤; <-irrefl; ≤-<-trans; <-≤-trans; ≤-pred; n≤1+n)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_)
open import Data.List using (List; []; _∷_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)

open import OCF.Align.Closure using (lt→<ᴾ; eq→≡ᴾ; <ᵀ-trans)
open import OCF.Align.Bachmann using (<sucT; gt→≤; Hd≤; fs-gt; rep<)
open import OCF.Align.Correspond using (cof-ne; fs-rep; fs-ω)
open import OCF.Align.Standard
import OCF.Align.EBO as E
open E using (T; c0; c1; cω; cΩ; lt; eq; gt; cmpᵀ; cof; cofA; cofψ0; cofψ₊; pred; sucT; Ωt; fsn; fsT; γT; _<ᵀ_; []<; hd<; tl<; lv<; ar<) renaming (ψ to ψᵗ)
```

## §1 单调

```agda
fs-monoᴺ : ∀ {u} → NF u → cof u ≡ cω → ∀ n → fsn u n <ᵀ fsn u (suc n)
fs-monoL : ∀ {w ws} → NF (w ∷ ws) → ∀ k → cof (w ∷ ws) ≡ k → cofψ0 (w ∷ ws) k ≡ cω →
           ∀ n → fsn (Ωt (w ∷ ws)) n <ᵀ fsn (Ωt (w ∷ ws)) (suc n)
fs-monoA : ∀ {w y ys} → NF (y ∷ ys) → ∀ k → cof (y ∷ ys) ≡ k → cofA w k ≡ cω →
           ∀ n → fsn (ψᵗ w (y ∷ ys) ∷ []) n <ᵀ fsn (ψᵗ w (y ∷ ys) ∷ []) (suc n)

fs-monoᴺ n[] () n
fs-monoᴺ (n∷ nx (n∷ ny nys hy) hx) e n = tl< (fs-monoᴺ (n∷ ny nys hy) e n)
fs-monoᴺ (n∷ (nψ {u = []} {a = []} nw cw na g) n[] hx) () n
fs-monoᴺ (n∷ (nψ {u = w ∷ ws} {a = []} nw cw na g) n[] hx) e n = fs-monoL nw (cof (w ∷ ws)) refl e n
fs-monoᴺ (n∷ (nψ {u = w} {a = y ∷ ys} nw cw na g) n[] hx) e n = fs-monoA na (cof (y ∷ ys)) refl e n

fs-monoL nw c0 ke () n
fs-monoL nw c1 ke () n
fs-monoL {w} {ws} nw cω ke e n =
  subst₂ _<ᵀ_ (sym (E.fsn0-eq w ws n ke)) (sym (E.fsn0-eq w ws (suc n) ke)) (hd< (lv< (fs-monoᴺ nw ke n)))
fs-monoL nw (cΩ μ) ke () n

fs-monoA nb c0 ke e n = ⊥-elim (cof-ne _ _ ke)
fs-monoA {w} {y} {ys} nb c1 ke e n =
  subst₂ _<ᵀ_ (sym (fs-rep w y ys ke n)) (sym (fs-rep w y ys ke (suc n))) (rep< _ n)
fs-monoA {w} {y} {ys} nb cω ke e n =
  subst₂ _<ᵀ_ (sym (fs-ω w y ys ke n)) (sym (fs-ω w y ys ke (suc n))) (hd< (ar< (fs-monoᴺ nb ke n)))
fs-monoA {w} {y} {ys} nb (cΩ ν) ke e n = go (cmpᵀ (sucT ν) w) refl e
  where
  go : ∀ m → cmpᵀ (sucT ν) w ≡ m → cofψ₊ w ν m ≡ cω →
       fsn (ψᵗ w (y ∷ ys) ∷ []) n <ᵀ fsn (ψᵗ w (y ∷ ys) ∷ []) (suc n)
  go lt em ()
  go eq em ()
  go gt em _ = subst₂ _<ᵀ_ (sym (fs-gt w y ys ν ke em n)) (sym (fs-gt w y ys ν ke em (suc n)))
                      (hd< (ar< (fsT-mono nb ke (γ-mono nb ke n))))
```

## §2 带上界的共尾性

`Cof6B` 的 `n` 不超过燃料 `m`: 每次递归 `n` 加一, 燃料减一, 而燃料从 `sz c` 起算. 这就是规则 6 的范数论证: `γ` 链的第 `n` 项追上 `c` 所需的 `n`, 不超过 `c` 中可见参数的嵌套深度.

```agda
Cof6B : ∀ m {b ν w c} → NF b → cof b ≡ cΩ ν → w ≤ᵀ ν → sz c ≤ℕ m → c <ᵀ b →
        (∀ {ζ} → Vis w ζ c → ζ <ᵀ b) → Σ ℕ λ n → (n ≤ℕ m) × (c <ᵀ fsT b (γT b ν n))
Cof6B m {b} {ν} {w} {c} nb be wν hm p H with Ωcof nb be p
... | ωc [] θ< fθ hv = 0 , z≤n , fθ []<
... | ωc (ψᵗ x ζ′ ∷ θs) (hd< (lv< q)) fθ hv with <sucT ν q
...   | inj₁ r = 0 , z≤n , fθ (hd< (lv< r))
...   | inj₂ refl = go m hm
  where
  vz : Vis ν ζ′ c
  vz = hv refl (inj₂ refl)
  go : ∀ m′ → sz c ≤ℕ m′ → Σ ℕ λ n → (n ≤ℕ m′) × (c <ᵀ fsT b (γT b ν n))
  go zero h = ⊥-elim (<-irrefl refl (<-≤-trans (≤-<-trans z≤n (Vis-sz vz)) h))
  go (suc m′) h with Cof6B m′ nb be wν (≤-pred (≤-trans (Vis-sz vz) h)) (H (Vis-mono wν vz))
                         (λ v → H (Vis-trans v (Vis-mono wν vz)))
  ... | k , k≤ , r = suc k , s≤s k≤ , fθ (hd< (ar< r))
Cof6B m nb be wν hm p H | ωc (ψᵗ x ζ′ ∷ θs) (hd< (ar< ())) fθ hv
Cof6B m nb be wν hm p H | ωc (ψᵗ x ζ′ ∷ θs) (tl< ()) fθ hv

szᴾ≥1 : ∀ x → 1 ≤ℕ szᴾ x
szᴾ≥1 (ψᵗ u a) = s≤s z≤n

sz-cons : ∀ x xs → suc (sz xs) ≤ℕ sz (x ∷ xs)
sz-cons x xs = E′ (szᴾ≥1 x) where
  E′ : 1 ≤ℕ szᴾ x → suc (sz xs) ≤ℕ szᴾ x + sz xs
  E′ p = +-mono′ (szᴾ x) (sz xs) p
    where
      +-mono′ : ∀ a b → 1 ≤ℕ a → suc b ≤ℕ a + b
      +-mono′ (suc a) b (s≤s _) = s≤s (m≤n+m b a)

repbB : ∀ x {vs} → NF vs → Hd≤ vs x → Σ ℕ λ m → (m ≤ℕ suc (sz vs)) × (vs <ᵀ replicate m x)
repbB x n[] h = 1 , s≤s z≤n , []<
repbB x (n∷ {x = y} ny nzs hz₀) (inj₁ e) = 1 , s≤s z≤n , hd< (lt→<ᴾ y x e)
repbB x (n∷ {x = y} {xs = zs} ny nzs hz₀) (inj₂ e) with eq→≡ᴾ y x e
... | refl with repbB x nzs hz₀
...   | m , m≤ , q = suc m , s≤s (≤-trans m≤ (sz-cons y zs)) , tl< q

cofinB  : ∀ {u} → NF u → cof u ≡ cω → ∀ {v} → NF v → v <ᵀ u → Σ ℕ λ n → (n ≤ℕ suc (sz v)) × (v <ᵀ fsn u n)
cofinBL : ∀ {w ws} → NF (w ∷ ws) → ∀ k → cof (w ∷ ws) ≡ k → cofψ0 (w ∷ ws) k ≡ cω →
          ∀ {v} → NF v → v <ᵀ Ωt (w ∷ ws) → Σ ℕ λ n → (n ≤ℕ suc (sz v)) × (v <ᵀ fsn (Ωt (w ∷ ws)) n)
cofinBA : ∀ {w y ys} → NF (y ∷ ys) → ∀ k → cof (y ∷ ys) ≡ k → cofA w k ≡ cω →
          ∀ {v} → NF v → v <ᵀ (ψᵗ w (y ∷ ys) ∷ []) → Σ ℕ λ n → (n ≤ℕ suc (sz v)) × (v <ᵀ fsn (ψᵗ w (y ∷ ys) ∷ []) n)

cofinB n[] () nv p
cofinB (n∷ nx (n∷ ny nys hy) hx) e nv []<     = 0 , z≤n , []<
cofinB (n∷ nx (n∷ ny nys hy) hx) e nv (hd< q) = 0 , z≤n , hd< q
cofinB (n∷ nx (n∷ ny nys hy) hx) e (n∷ {x = x′} {xs = vs} _ nvs _) (tl< q) with cofinB (n∷ ny nys hy) e nvs q
... | n , n≤ , r = n , ≤-trans n≤ (s≤s (sz-tl x′ vs)) , tl< r
cofinB (n∷ (nψ {u = []} {a = []} nw cw na g) n[] hx) () nv p
cofinB (n∷ (nψ {u = w ∷ ws} {a = []} nw cw na g) n[] hx) e nv p = cofinBL nw (cof (w ∷ ws)) refl e nv p
cofinB (n∷ (nψ {u = w} {a = y ∷ ys} nw cw na g) n[] hx) e nv p = cofinBA na (cof (y ∷ ys)) refl e nv p

cofinBL nw c0 ke () nv p
cofinBL nw c1 ke () nv p
cofinBL {w} {ws} nw cω ke e nv []< = 0 , z≤n , subst ([] <ᵀ_) (sym (E.fsn0-eq w ws 0 ke)) []<
cofinBL {w} {ws} nw cω ke e (n∷ {xs = vs} (nψ {u = x} {a = c} nx _ _ _) _ _) (hd< (lv< q)) with cofinB nw ke nx q
... | n , n≤ , r = n , ≤-trans n≤ (s≤s (≤-trans (m≤m+n (sz x) (sz c)) (≤-trans (n≤1+n _) (m≤m+n _ (sz vs))))) ,
                   subst (_ <ᵀ_) (sym (E.fsn0-eq w ws n ke)) (hd< (lv< r))
cofinBL nw cω ke e nv (hd< (ar< ()))
cofinBL nw cω ke e nv (tl< ())
cofinBL nw (cΩ μ) ke () nv p

cofinBA nb c0 ke e nv p = ⊥-elim (cof-ne _ _ ke)
cofinBA {w} {y} {ys} nb c1 ke e n[] []< = 1 , s≤s z≤n , subst ([] <ᵀ_) (sym (fs-rep w y ys ke 1)) []<
cofinBA {w} {y} {ys} nb c1 ke e nv (hd< (lv< q)) = 1 , s≤s z≤n , subst (_ <ᵀ_) (sym (fs-rep w y ys ke 1)) (hd< (lv< q))
cofinBA {w} {y} {ys} nb c1 ke e (n∷ {x = ψᵗ _ c} {xs = vs} nc nvs hv) (hd< (ar< q))
  with <sucT (pred (y ∷ ys)) (subst (c <ᵀ_) (sym (E.pred-suc (y ∷ ys) ke)) q)
... | inj₁ r = 1 , s≤s z≤n , subst (_ <ᵀ_) (sym (fs-rep w y ys ke 1)) (hd< (ar< r))
... | inj₂ refl with repbB (ψᵗ w c) nvs hv
...   | m , m≤ , r = suc m , s≤s (≤-trans m≤ (sz-cons (ψᵗ w c) vs)) ,
                     subst (_ <ᵀ_) (sym (fs-rep w y ys ke (suc m))) (tl< r)
cofinBA nb c1 ke e nv (tl< ())
cofinBA {w} {y} {ys} nb cω ke e nv []< = 0 , z≤n , subst ([] <ᵀ_) (sym (fs-ω w y ys ke 0)) []<
cofinBA {w} {y} {ys} nb cω ke e nv (hd< (lv< q)) = 0 , z≤n , subst (_ <ᵀ_) (sym (fs-ω w y ys ke 0)) (hd< (lv< q))
cofinBA {w} {y} {ys} nb cω ke e (n∷ {x = ψᵗ w′ c} {xs = vs} (nψ _ _ nc _) _ _) (hd< (ar< q)) with cofinB nb ke nc q
... | n , n≤ , r = n , ≤-trans n≤ (s≤s (≤-trans (<⇒≤ (sz-hdarg w′ c vs)) ≤-refl)) ,
                   subst (_ <ᵀ_) (sym (fs-ω w y ys ke n)) (hd< (ar< r))
cofinBA nb cω ke e nv (tl< ())
cofinBA {w} {y} {ys} nb (cΩ ν) ke e nv p = go (cmpᵀ (sucT ν) w) refl e
  where
  go : ∀ m → cmpᵀ (sucT ν) w ≡ m → cofψ₊ w ν m ≡ cω →
       Σ ℕ λ n → (n ≤ℕ suc (sz _)) × (_ <ᵀ fsn (ψᵗ w (y ∷ ys) ∷ []) n)
  go lt em ()
  go eq em ()
  go gt em _ = h nv p
    where
    h : ∀ {v} → NF v → v <ᵀ (ψᵗ w (y ∷ ys) ∷ []) → Σ ℕ λ n → (n ≤ℕ suc (sz v)) × (v <ᵀ fsn (ψᵗ w (y ∷ ys) ∷ []) n)
    h nv []< = 0 , z≤n , subst ([] <ᵀ_) (sym (fs-gt w y ys ν ke em 0)) []<
    h nv (hd< (lv< q)) = 0 , z≤n , subst (_ <ᵀ_) (sym (fs-gt w y ys ν ke em 0)) (hd< (lv< q))
    h (n∷ {xs = vs} (nψ {u = w′} {a = c} _ _ nc gc) _ _) (hd< (ar< q))
      with Cof6B (sz c) nb ke (gt→≤ ν w em) ≤-refl q (λ vz → <ᵀ-trans (gc vz) q)
    ... | n , n≤ , r = n , ≤-trans n≤ (≤-trans (<⇒≤ (sz-hdarg w′ c vs)) (n≤1+n _)) ,
                       subst (_ <ᵀ_) (sym (fs-gt w y ys ν ke em n)) (hd< (ar< r))
    h nv (tl< ())
```
