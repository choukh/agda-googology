# 字面守卫与 `HS`: 编译过的否定

> 不含记号. 结论写在 [NoKCert](NoKCert.lagda.md). **只否定写明的东西.**
>
> - `no-HS→Lgl`: "第 0 层的值只要 `HS`, 读成下标就过 `Lgl`" 是假的. 反例 $Y=\lim F$, $F\,0=\omega$, $F(k+1)=\omega'+k+1$, $\omega'=\lim_n(n+1)$. $Y$ 是 `HS` (定理 `HS-Y`, 所以前提可满足), 但 `F 0` 不是 `F 1` 的字面第一位置: $\omega\cong\omega'$ 而 $\omega\neq\omega'$.
> - `no-⊑-Cp`: `⊑⁰` 推不出字面第一位置.
>
> **这条否定的意思.** [OCF.Free.Force](../Free/Force.lagda.md) 的 `Goodᴺ` 的链点只带 `HS` (`hy`), 下标是 `toLevel` 读出来的 `Ordᴵ`, 守卫 `⊑ᴵ` 是模 $\cong$ 的. [NoKCertEval](NoKCertEval.lagda.md) 的 `Goodᵁ` 要字面的 `Lgl`. 所以 `Good-≲` 那种桥只给 `HS` 时, 给不出 `dy`: 要么另证链点的步进是字面的 (Bachmann 型), 要么守卫模 $\cong$. **这不否定树的链点有字面的步进:** 那是有限测试一致 ([NoKCertProbe](NoKCertProbe.lagda.md)), 未证. 也不否定 `LF` 的路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoKCertNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Free.Level using (Ordᶜ; HS; hz; hs; hl; _⊑⁰_; _≅_; ≺z; ≺s; ≺l; lim-⊑)
import OCF.Free.Level as FL
open import OCF.Align.LevelFixCore
open import OCF.Align.NoKCertEval using (Ord₀; rdR)

natO : ℕ → Ord₀
natO zero = FL.zero
natO (suc n) = FL.suc (natO n)

ω₁ ω₂ : Ord₀
ω₁ = FL.lim natO
ω₂ = FL.lim (λ n → natO (suc n))

sucs₀ : Ord₀ → ℕ → Ord₀
sucs₀ a zero = a
sucs₀ a (suc k) = FL.suc (sucs₀ a k)

F : ℕ → Ord₀
F zero = ω₁
F (suc k) = FL.suc (sucs₀ ω₂ k)

Y : Ord₀
Y = FL.lim F

HS-nat : ∀ n → HS (natO n)
HS-nat zero = hz
HS-nat (suc n) = hs (HS-nat n)

nat-step : ∀ n → natO n ⊑⁰ natO (suc n)
nat-step n h = ≺s h

HS-ω₁ : HS ω₁
HS-ω₁ = hl HS-nat nat-step

HS-ω₂ : HS ω₂
HS-ω₂ = hl (λ n → HS-nat (suc n)) (λ n → nat-step (suc n))

HS-sucs : ∀ {a} → HS a → ∀ k → HS (sucs₀ a k)
HS-sucs h zero = h
HS-sucs h (suc k) = hs (HS-sucs h k)

ω₁⊑ : ω₁ ⊑⁰ FL.suc ω₂
ω₁⊑ = lim-⊑ (λ n h → ≺s (≺l n (≺s h)))

HS-F : ∀ n → HS (F n)
HS-F zero = HS-ω₁
HS-F (suc k) = hs (HS-sucs HS-ω₂ k)

F-step : ∀ n → F n ⊑⁰ F (suc n)
F-step zero = ω₁⊑
F-step (suc k) h = ≺s h

HS-Y : HS Y
HS-Y = hl HS-F F-step

-- 读成第 0 层的值
natR : ℕ → Raw LF.zero
natR n = rdR LF.zero (natO n)

lim-not-nat : ∀ {f : ℕ → Raw LF.zero} k → Cp LF.zero (G.lim f) (natR k) → ⊥
lim-not-nat zero (inj₁ ())
lim-not-nat zero (inj₂ ())
lim-not-nat (suc k) (inj₁ ())
lim-not-nat (suc k) (inj₂ p) = lim-not-nat k p

lim-inj₀ : ∀ {f h : ℕ → Raw LF.zero} → G.lim f ≡ G.lim h → f 0 ≡ h 0
lim-inj₀ refl = refl

ω≠ω : rdR LF.zero ω₁ ≡ rdR LF.zero ω₂ → ⊥
ω≠ω e with lim-inj₀ e
... | ()

no-cp : Cp LF.zero (rdR LF.zero ω₁) (rdR LF.zero ω₂) → ⊥
no-cp (inj₁ e) = ω≠ω e
no-cp (inj₂ (n , p)) = lim-not-nat (suc n) p

no-step : Cp LF.zero (rdR LF.zero (F 0)) (rdR LF.zero (F 1)) → ⊥
no-step (inj₁ ())
no-step (inj₂ p) = no-cp p

-- 定理: HS 推不出 Lgl. 前提可满足: HS-Y
no-Lgl-Y : Lgl LF.zero (rdR LF.zero Y) → ⊥
no-Lgl-Y (st , _) = no-step (st 0)

no-HS→Lgl : (∀ y → HS y → Lgl LF.zero (rdR LF.zero y)) → ⊥
no-HS→Lgl h = no-Lgl-Y (h Y HS-Y)

-- 字面第一位置不被 ⊑⁰ 蕴含
no-⊑-Cp : (∀ {a c : Ord₀} → a ⊑⁰ c → Cp LF.zero (rdR LF.zero a) (rdR LF.zero c)) → ⊥
no-⊑-Cp h = no-step (h {a = F 0} {c = F 1} ω₁⊑)
```
