# 计值判据: 第 0 层的树什么时候是序数

> 不含记号. 结论写在 [NoKCert](NoKCert.lagda.md). `T⁰ 0` 里的闭包是待计值的符号. 这里写清计值要什么: 与 [OCF.Free.Force](../Free/Force.lagda.md) 的 `Goodᴺ` 同形, 差别只在下标是 `Elt`, 守卫是 `⊑̂` (字面第一位置).
>
> - `Zᵁ`: 第 0 层树去掉包装 (`rdZ`).
> - `Goodᵁ`, `forceᵁ`, `forceᵁ-HS`: 链点由预言序列给出, 带下标的证据. `gŝ`: 链在第 0 层 (`oŝ`), 第 $m$ 个链点 $y_m$ 读成第 $j$ 层的值 `rdR j y`. `gĉ`: 链在高层 (`oĉ`), 链点 $z_m:$ `LG` 读成第 $j$ 层的值 $\eta_m$, 要 `toU (up j η) ≈ z`.
> - **这个判据的前提是字面的:** `e m : c ⊑̂ el j η_m` 含 `Lgl j η_m`, 即极限的相邻项是字面第一位置.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoKCertEval where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.LevelFixCore
open import OCF.Align.LevelFixVal
open import OCF.Align.LevelNoKU hiding (ŝ)
open import OCF.Align.LevelNoKLv using (module Lv)
open Lv 𝕌 using (LG; _≈_)
open import OCF.Free.Level using (Ordᶜ; HS; hz; hs; hl; _⊑⁰_; _≅_; FGH)
import OCF.Free.Level as FL
import OCF.Align.LevelNoKFold as FF
open FF using (O; T⁰)
open FF.TT using (o0; os; ol; oŝ; oĉ; owk; ocv; omk; oΩ; ocl)
```

## §1 第 0 层的只读像

```agda
Ord₀ : Set
Ord₀ = Ordᶜ FL.zero

data Zᵁ : Set where
  zero : Zᵁ
  suc  : Zᵁ → Zᵁ
  lim  : (ℕ → Zᵁ) → Zᵁ
  ŝ    : (c : Elt) → Zᵁ → ((η : Elt) → c ⊑̂ η → Zᵁ) → Zᵁ
  ĉ    : (c : Elt) → LG → ((η : Elt) → c ⊑̂ η → LG) → Zᵁ → ((η : Elt) → c ⊑̂ η → Zᵁ) → Zᵁ

rdZ : ∀ {π} → O U.zero π → Zᵁ
rdZ o0 = zero
rdZ (os a) = suc (rdZ a)
rdZ (ol F) = lim (λ n → rdZ (F n))
rdZ (oŝ c t g) = ŝ c (rdZ t) (λ η e → rdZ (g η e))
rdZ (oĉ c z zg o₀ o) = ĉ c z zg (rdZ o₀) (λ η e → rdZ (o η e))
rdZ (owk w x) = rdZ x
rdZ (ocv w x) = rdZ x
rdZ (omk () _ _ _ _)
rdZ (oΩ () _ _)
rdZ (ocl () _ _ _ _)

-- 第 0 层的值读成第 j 层的值: 只有 zero, suc, lim, 对一切 j
rdR : ∀ j → Ord₀ → Raw j
rdR j FL.zero = G.zero
rdR j (FL.suc a) = G.suc (rdR j a)
rdR j (FL.lim f) = G.lim (λ n → rdR j (f n))
rdR j (FL.limᵢ () f)
rdR j (FL.up () x)
```

## §2 证书

```agda
outs : Ord₀ → (ℕ → Ord₀) → ℕ → Ord₀
outs O₀ O zero = O₀
outs O₀ O (suc k) = O k

outs-HS : ∀ {O₀ O} → HS O₀ → (∀ k → HS (O k)) → ∀ n → HS (outs O₀ O n)
outs-HS h₀ h zero = h₀
outs-HS h₀ h (suc k) = h k

outs-step : ∀ {O₀ O} → O₀ ⊑⁰ O 0 → (∀ k → O k ⊑⁰ O (suc k)) → ∀ n → outs O₀ O n ⊑⁰ outs O₀ O (suc n)
outs-step m₀ m zero = m₀
outs-step m₀ m (suc k) = m k

data Goodᵁ : Zᵁ → Set
forceᵁ : (x : Zᵁ) → Goodᵁ x → Ord₀
forceᵁ-HS : (x : Zᵁ) (G : Goodᵁ x) → HS (forceᵁ x G)

data Goodᵁ where
  gz : Goodᵁ zero
  gs : ∀ {x} → Goodᵁ x → Goodᵁ (suc x)
  gl : ∀ {f : ℕ → Zᵁ} (G : ∀ n → Goodᵁ (f n)) →
       (∀ n → forceᵁ (f n) (G n) ⊑⁰ forceᵁ (f (suc n)) (G (suc n))) → Goodᵁ (lim f)
  -- 链在第 0 层: y₀ = t 的值, y_{m+1} = g(y_m) 的值. 同时是输出
  gŝ : ∀ {j c t₀} {g : (η : Elt) → el j c ⊑̂ η → Zᵁ}
       (ys : ℕ → Ord₀) (hy : ∀ m → HS (ys m)) (dy : ∀ m → el j c ⊑̂ el j (rdR j (ys m)))
       (G₀ : Goodᵁ t₀) (l₀ : forceᵁ t₀ G₀ ≅ ys 0)
       (Gg : ∀ m → Goodᵁ (g _ (dy m)))
       (lE : ∀ m → forceᵁ _ (Gg m) ≅ ys (suc m))
       (m₀ : forceᵁ t₀ G₀ ⊑⁰ forceᵁ _ (Gg 0))
       (mo : ∀ k → forceᵁ _ (Gg k) ⊑⁰ forceᵁ _ (Gg (suc k))) →
       Goodᵁ (ŝ (el j c) t₀ g)
  -- 链在第 j 层: z_m ≈ up j η_m
  gĉ : ∀ {j c z zg o₀} {o : (η : Elt) → el j c ⊑̂ η → Zᵁ}
       (ηs : ℕ → Raw j) (dy : ∀ m → el j c ⊑̂ el j (ηs m))
       (l₀ : z ≈ toU (up j (ηs 0)))
       (lE : ∀ m → zg _ (dy m) ≈ toU (up j (ηs (suc m))))
       (Go₀ : Goodᵁ o₀) (Go : ∀ k → Goodᵁ (o _ (dy k))) →
       (m₀ : forceᵁ o₀ Go₀ ⊑⁰ forceᵁ _ (Go 0)) →
       (mo : ∀ k → forceᵁ _ (Go k) ⊑⁰ forceᵁ _ (Go (suc k))) →
       Goodᵁ (ĉ (el j c) z zg o₀ o)

forceᵁ zero gz = FL.zero
forceᵁ (suc x) (gs G) = FL.suc (forceᵁ x G)
forceᵁ (lim f) (gl G st) = FL.lim (λ n → forceᵁ (f n) (G n))
forceᵁ (ŝ c t g) (gŝ ys hy dy G₀ l₀ Gg lE m₀ mo) = FL.lim (outs (forceᵁ t G₀) (λ k → forceᵁ _ (Gg k)))
forceᵁ (ĉ c z zg o₀ o) (gĉ ηs dy l₀ lE Go₀ Go m₀ mo) = FL.lim (outs (forceᵁ o₀ Go₀) (λ k → forceᵁ _ (Go k)))

forceᵁ-HS zero gz = hz
forceᵁ-HS (suc x) (gs G) = hs (forceᵁ-HS x G)
forceᵁ-HS (lim f) (gl G st) = hl (λ n → forceᵁ-HS (f n) (G n)) st
forceᵁ-HS (ŝ c t g) (gŝ ys hy dy G₀ l₀ Gg lE m₀ mo) =
  hl (outs-HS (forceᵁ-HS t G₀) (λ k → forceᵁ-HS _ (Gg k))) (outs-step m₀ mo)
forceᵁ-HS (ĉ c z zg o₀ o) (gĉ ηs dy l₀ lE Go₀ Go m₀ mo) =
  hl (outs-HS (forceᵁ-HS o₀ Go₀) (λ k → forceᵁ-HS _ (Go k))) (outs-step m₀ mo)

fgh : (x : Zᵁ) → Goodᵁ x → ℕ → ℕ
fgh x G = FGH (forceᵁ x G)
```
