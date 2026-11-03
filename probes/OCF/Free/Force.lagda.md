# 无记号主线 (六): 证书 `Goodᴺ` 与 `forceᴺ`

> **`Goodᴺ`, `forceᴺ`, `forceᴺ-HS`, `forceᴺ-≅`, `Goodᴺ-tr`.** `gc` 行的链 `ys` 是树, 没有 `T`. 这是证书的全部. 原文件里 `ofL` (把带标签的证书化成它) 留在 [Lab/NotFree](Lab/NotFree.lagda.md), 主线不需要.
> 脚本从 [NotFree](../Align/NotFree.lagda.md)、[UniformNF3NBase](../Align/UniformNF3NBase.lagda.md) 切出 (定义级切片), 代码行逐字, 讲解见原文件. 本文件的导入闭包不含记号或标签模块 (`probes/Survey/scripts/importclosure.py`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Force where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.Free.Level
open import OCF.Free.Prefix
open import OCF.Free.Eq
open import OCF.Free.Aux
```

## §1 `Goodᴺ`: 链点由预言序列给出

```agda
outsᴺ : Ordᶜ zero → (ℕ → Ordᶜ zero) → ℕ → Ordᶜ zero
outsᴺ O₀ O zero    = O₀
outsᴺ O₀ O (suc k) = O k

outsᴺ-HS : ∀ {O₀ O} → HS O₀ → (∀ k → HS (O k)) → ∀ n → HS (outsᴺ O₀ O n)
outsᴺ-HS h₀ h zero    = h₀
outsᴺ-HS h₀ h (suc k) = h k

outsᴺ-step : ∀ {O₀ O} → O₀ ⊑⁰ O 0 → (∀ k → O k ⊑⁰ O (suc k)) → ∀ n → outsᴺ O₀ O n ⊑⁰ outsᴺ O₀ O (suc n)
outsᴺ-step m₀ m zero    = m₀
outsᴺ-step m₀ m (suc k) = m k

outsᴺ-≅ : ∀ {O₀ O₀′ O O′} → O₀ ≅ O₀′ → (∀ k → O k ≅ O′ k) → ∀ n → outsᴺ O₀ O n ≅ outsᴺ O₀′ O′ n
outsᴺ-≅ e₀ e zero    = e₀
outsᴺ-≅ e₀ e (suc k) = e k
```

```agda
data Goodᴺ : Z → Set
forceᴺ    : (x : Z) → Goodᴺ x → Ordᶜ zero
forceᴺ-HS : (x : Z) (G : Goodᴺ x) → HS (forceᴺ x G)

data Goodᴺ where
  gz : Goodᴺ Z.zero
  gs : ∀ {x} → Goodᴺ x → Goodᴺ (Z.suc x)
  gl : ∀ {f : ℕ → Z} (G : ∀ n → Goodᴺ (f n)) →
       (∀ n → forceᴺ (f n) (G n) ⊑⁰ forceᴺ (f (suc n)) (G (suc n))) → Goodᴺ (Z.lim f)
  gc : ∀ {c t₀ o₀} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z}
       (ys : ℕ → Ordᶜ zero) (hy : ∀ m → HS (ys m)) (dy : ∀ m → c ⊑ᴵ toLevel (ys m) (hy m))
       (G₀ : Goodᴺ t₀) (l₀ : forceᴺ t₀ G₀ ≅ ys 0)
       (Gg : ∀ m → Goodᴺ (g (toLevel (ys m) (hy m)) (dy m)))
       (lE : ∀ m → forceᴺ _ (Gg m) ≅ ys (suc m))
       (Go₀ : Goodᴺ o₀) (Go : ∀ k → Goodᴺ (o (toLevel (ys k) (hy k)) (dy k))) →
       forceᴺ o₀ Go₀ ⊑⁰ forceᴺ _ (Go 0) →
       (∀ k → forceᴺ _ (Go k) ⊑⁰ forceᴺ _ (Go (suc k))) →
       Goodᴺ (ĉᴸ c t₀ g o₀ o)

forceᴺ Z.zero    gz        = zero
forceᴺ (Z.suc x) (gs G)    = suc (forceᴺ x G)
forceᴺ (Z.lim f) (gl G st) = lim (λ n → forceᴺ (f n) (G n))
forceᴺ (ĉᴸ c t₀ g o₀ o) (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = lim (outsᴺ (forceᴺ o₀ Go₀) (λ k → forceᴺ _ (Go k)))

forceᴺ-HS Z.zero    gz        = hz
forceᴺ-HS (Z.suc x) (gs G)    = hs (forceᴺ-HS x G)
forceᴺ-HS (Z.lim f) (gl G st) = hl (λ n → forceᴺ-HS (f n) (G n)) st
forceᴺ-HS (ĉᴸ c t₀ g o₀ o) (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) =
  hl (outsᴺ-HS (forceᴺ-HS o₀ Go₀) (λ k → forceᴺ-HS _ (Go k))) (outsᴺ-step mo₀ mo)
```

## §2 计值与证书无关

```agda
ys-≅ : ∀ {ys ys′ : ℕ → Ordᶜ zero} → ys 0 ≅ ys′ 0 → (∀ m → ys m ≅ ys′ m → ys (suc m) ≅ ys′ (suc m)) → ∀ m → ys m ≅ ys′ m
ys-≅ e₀ eS zero    = e₀
ys-≅ e₀ eS (suc m) = eS m (ys-≅ e₀ eS m)

forceᴺ-≅ : ∀ {x y} → x ≅ᶻ y → (G : Goodᴺ x) (G′ : Goodᴺ y) → forceᴺ x G ≅ forceᴺ y G′
forceᴺ-≅ zᶻ     gz gz = z≅
forceᴺ-≅ (sᶻ d) (gs G) (gs G′) = s≅ (forceᴺ-≅ d G G′)
forceᴺ-≅ (lᶻ h) (gl G _) (gl G′ _) = l≅ (λ n → forceᴺ-≅ (h n) (G n) (G′ n))
forceᴺ-≅ (ĉᶻ ec dt dg dp dO) (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) (gc ys′ hy′ dy′ G₀′ l₀′ Gg′ lE′ Go₀′ Go′ mo₀′ mo′) =
  l≅ (outsᴺ-≅ (forceᴺ-≅ dp Go₀ Go₀′)
              (λ k → forceᴺ-≅ (dO _ _ _ _ (toLevel-≅ (hy k) (hy′ k) (eY k))) (Go k) (Go′ k)))
  where
  eY : ∀ m → ys m ≅ ys′ m
  eY = ys-≅ (≅-trans (≅-sym l₀) (≅-trans (forceᴺ-≅ dt G₀ G₀′) l₀′))
            (λ m e → ≅-trans (≅-sym (lE m))
                     (≅-trans (forceᴺ-≅ (dg _ _ _ _ (toLevel-≅ (hy m) (hy′ m) e)) (Gg m) (Gg′ m)) (lE′ m)))
```

## §9 结论与边界

```agda
open Restrˢ
```

## §1 `Goodᴺ` 沿 `≅ᶻ` 搬运

```agda
Goodᴺ-tr : ∀ {x y} → x ≅ᶻ y → Goodᴺ x → Goodᴺ y
Goodᴺ-tr zᶻ     gz     = gz
Goodᴺ-tr (sᶻ d) (gs G) = gs (Goodᴺ-tr d G)
Goodᴺ-tr (lᶻ h) (gl G st) = gl (λ n → Goodᴺ-tr (h n) (G n))
  (λ n → ⊑-trans (≅→⊑ (≅-sym (forceᴺ-≅ (h n) (G n) (Goodᴺ-tr (h n) (G n)))))
         (⊑-trans (st n) (≅→⊑ (forceᴺ-≅ (h (suc n)) (G (suc n)) (Goodᴺ-tr (h (suc n)) (G (suc n)))))))
Goodᴺ-tr {y = ĉᴸ c′ t₀′ g′ o₀′ o′} (ĉᶻ {c = c} {t₀ = t₀} {o₀ = o₀} {g = g} {o = o} ec dt dg dp dO) (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) =
  gc ys hy dy′ G₀′ l₀′ Gg′ lE′ Go₀′ Go′ mo₀′ mo′
  where
  dy′ : ∀ m → c′ ⊑ᴵ toLevel (ys m) (hy m)
  dy′ m = ⊑ᴵ-≅ˡ ec (dy m)
  G₀′ : Goodᴺ t₀′
  G₀′ = Goodᴺ-tr dt G₀
  l₀′ : forceᴺ t₀′ G₀′ ≅ ys 0
  l₀′ = ≅-trans (≅-sym (forceᴺ-≅ dt G₀ G₀′)) l₀
  dgm : ∀ m → g (toLevel (ys m) (hy m)) (dy m) ≅ᶻ g′ (toLevel (ys m) (hy m)) (dy′ m)
  dgm m = dg _ (dy m) _ (dy′ m) (≅ᴵ-refl _)
  Gg′ : ∀ m → Goodᴺ (g′ (toLevel (ys m) (hy m)) (dy′ m))
  Gg′ m = Goodᴺ-tr (dgm m) (Gg m)
  lE′ : ∀ m → forceᴺ _ (Gg′ m) ≅ ys (suc m)
  lE′ m = ≅-trans (≅-sym (forceᴺ-≅ (dgm m) (Gg m) (Gg′ m))) (lE m)
  Go₀′ : Goodᴺ o₀′
  Go₀′ = Goodᴺ-tr dp Go₀
  dOk : ∀ k → o (toLevel (ys k) (hy k)) (dy k) ≅ᶻ o′ (toLevel (ys k) (hy k)) (dy′ k)
  dOk k = dO _ (dy k) _ (dy′ k) (≅ᴵ-refl _)
  Go′ : ∀ k → Goodᴺ (o′ (toLevel (ys k) (hy k)) (dy′ k))
  Go′ k = Goodᴺ-tr (dOk k) (Go k)
  mo₀′ : forceᴺ o₀′ Go₀′ ⊑⁰ forceᴺ _ (Go′ 0)
  mo₀′ = ⊑-trans (≅→⊑ (≅-sym (forceᴺ-≅ dp Go₀ Go₀′))) (⊑-trans mo₀ (≅→⊑ (forceᴺ-≅ (dOk 0) (Go 0) (Go′ 0))))
  mo′ : ∀ k → forceᴺ _ (Go′ k) ⊑⁰ forceᴺ _ (Go′ (suc k))
  mo′ k = ⊑-trans (≅→⊑ (≅-sym (forceᴺ-≅ (dOk k) (Go k) (Go′ k)))) (⊑-trans (mo k) (≅→⊑ (forceᴺ-≅ (dOk (suc k)) (Go (suc k)) (Go′ (suc k)))))
```

## §3 地板、严格、覆盖与支配 (`Goodᴺ` 版)
