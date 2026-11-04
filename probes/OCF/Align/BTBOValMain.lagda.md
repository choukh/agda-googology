# BTBOVal 的主定理: 折叠族的差异消失, 只剩层号

> 接 [BTBOValDn](BTBOValDn.lagda.md), [BTBOValUp](BTBOValUp.lagda.md). **验收文件, 读 `NoCumsum` 的对角线.** 把两个方向接起来, 得到对一切层号的值相等 (`ψ₀≈`), 再落到 src 的对角线: 每一项都是 Level 的折叠作用在累加过的层号上 (`x-step`). 前四步与 $\gamma$ 链交错 (`row₀`...`row₃`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BTBOValMain where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤′_; ≤′-refl; ≤′-step; z≤n; s≤s) renaming (_+_ to _+ᴺ_)
open import Data.Nat.Properties using (≤⇒≤′; m≤m+n; m≤n⇒m≤1+n)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.BTBO using (module Ord-Ord; module BoundedTrich)
module S = Ord-Ord
module B = BoundedTrich
open B using (Ordᴰ; cumsum) renaming (_+_ to _+ᴰ_)
open S using (iter; ordᴰ; ψⁿ; BTBO; zero; suc; lim; limᵢ)
open import OCF.Align.Level
import OCF.Align.NoCumsum as N
open N using (BTBOᴵ)
open import OCF.Align.BTBOValBase using (tr₀; fd; FGH-tr₀; ordᴰ-≥)
open import OCF.Align.BTBOValDn using (τ; τ-<; Ψ⁰≼<)
open import OCF.Align.BTBOValUp using (Ψ⁰≽<)
open import OCF.Align.Value using (_≼_; _≈ᵛ_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≅→≼; ⊑→≼)
```

## §1 对一切层号

`S.ψ₀` 在第 0 层是恒等, 所以层号 0 单独算: src 的 $\omega$ 与 Level 的 $\psi^0(1)$ 基本列逐项相同. src 的 `ω` 的基本列是 `where` 里的局部函数, 这里对满足同样方程的一切 $g$ 证, 用时取 `refl`.

```agda
T : ℕ → Ordᶜ Ordᴵ.zero
T = iter (suc zero +_) zero

1+nat : ∀ m → suc zero + natᶜ m ≡ natᶜ (suc m)
1+nat zero    = refl
1+nat (suc m) = cong suc (1+nat m)

T-nat : ∀ n → T n ≡ natᶜ n
T-nat zero    = refl
T-nat (suc n) = trans (cong (suc zero +_) (T-nat n)) (1+nat n)

g-nat : (g : ℕ → S.Ord₀) → g 0 ≡ zero → (∀ n → g (suc n) ≡ suc (g n)) → ∀ n → tr₀ (g n) ≡ natᶜ n
g-nat g g0 gs zero    = cong tr₀ g0
g-nat g g0 gs (suc n) = trans (cong tr₀ (gs n)) (cong suc (g-nat g g0 gs n))

ω≈g : (g : ℕ → S.Ord₀) → g 0 ≡ zero → (∀ n → g (suc n) ≡ suc (g n)) → tr₀ (lim g) ≈ᵛ ψ⁰ (Ω Ordᴵ.zero)
ω≈g g g0 gs = l≼ (λ n → ≼l n (subst₂′ n)) , l≼ (λ n → ≼l n (subst₂″ n))
  where
  e : ∀ n → tr₀ (g n) ≡ T n
  e n = trans (g-nat g g0 gs n) (sym (T-nat n))
  subst₂′ : ∀ n → tr₀ (g n) ≼ T n
  subst₂′ n = subst (λ u → u ≼ T n) (sym (e n)) (≼-refl (T n))
  subst₂″ : ∀ n → T n ≼ tr₀ (g n)
  subst₂″ n = subst (λ u → T n ≼ u) (sym (e n)) (≼-refl (T n))

ω≈ : tr₀ S.ω ≈ᵛ ψ⁰ (Ω Ordᴵ.zero)
ω≈ = ω≈g _ refl (λ _ → refl)

ψ₀≈ : ∀ a → tr₀ (S.ψ₀ (S.Ω a)) ≈ᵛ ψ⁰ (Ω (τ a))
ψ₀≈ B.zero      = ω≈
ψ₀≈ (B.suc a)   = Ψ⁰≽< (B.z<nz _) , Ψ⁰≼< (B.z<nz _)
ψ₀≈ (B.lim f m) = Ψ⁰≽< (B.z<nz _) , Ψ⁰≼< (B.z<nz _)
```

**这是本路第一个主结果.** 五处差异 ($\Omega_0$, 链起点, `lfp`, `↑`, 字面三歧) 都不改序数值, 对**任意** `Ordᴰ` 层号, 不要 `Good`, 不要任何前提. 两个方向分别在 `BTBOValDn`, `BTBOValUp` 证.

## §2 对角线

`x-step`: src 的每一项是 Level 的折叠作用在累加层号上. 于是整个问题只剩层号: $\tau(\mathsf{ord}^\mathsf{D}\,x_k)$ 对 $L_m$.

```agda
x : ℕ → S.Ord₀
x = ψⁿ

x-step : ∀ k → tr₀ (x (suc k)) ≈ᵛ ψ⁰ (Ω (τ (ordᴰ (x k))))
x-step k = ψ₀≈ (ordᴰ (x k))
```

**条件定理.** 如果层号一步能被 $\gamma$ 链控制, 对角线就同值. 前提就是吸收加上折叠对层号的单调. 这一条只是把上面拼起来, 内容全在前提里.

```agda
cond-main : (Up : ∀ k → Σ ℕ (λ m → ψ⁰ (Ω (τ (ordᴰ (x k)))) ≼ N.γ m)) →
            (Dn : ∀ m → Σ ℕ (λ k → N.γ (suc m) ≼ ψ⁰ (Ω (τ (ordᴰ (x k)))))) →
            ∀ (γ-mono : ∀ m → Σ ℕ (λ m′ → N.γ m ≼ N.γ (suc m′))) → tr₀ BTBO ≈ᵛ BTBOᴵ
cond-main Up Dn γ-mono = l≼ upˣ , l≼ dnˣ
  where
  upˣ : ∀ n → tr₀ (x n) ≼ BTBOᴵ
  upˣ zero    = z≼
  upˣ (suc k) with Up k | γ-mono (proj₁ (Up k))
  ... | m , d | m′ , g = ≼l m′ (≼-trans (proj₁ (x-step k)) (≼-trans d g))
  dnˣ : ∀ m → N.γ (suc m) ≼ tr₀ BTBO
  dnˣ m with Dn m
  ... | k , d = ≼l (suc k) (≼-trans d (proj₂ (x-step k)))
```

## §3 $\psi_0(\Omega_\omega)$: 累加的第一站

$x_2$ 的层号是 `ordᴰ ω`, 基本列 $0,2,5,9,\dots$. 它的值就是 Level 的 $\psi^0(\Omega_\omega)$, 基本列 $0,1,2,\dots$. 这一站层号都是有限数, 累加只是跳着走, 所以 `Ψ⁰-mono` 够用.

```agda
natᴰ : ℕ → Ordᴰ
natᴰ zero    = B.zero
natᴰ (suc n) = B.suc (natᴰ n)

τ-nat : ∀ n → τ (natᴰ n) ≡ natᴵ n
τ-nat zero    = refl
τ-nat (suc n) = cong suc (τ-nat n)

+ᴰ-nat : ∀ a b → natᴰ a +ᴰ natᴰ b ≡ natᴰ (b +ᴺ a)
+ᴰ-nat a zero    = refl
+ᴰ-nat a (suc b) = cong B.suc (+ᴰ-nat a b)

K : ℕ → ℕ
K zero    = 0
K (suc n) = suc (suc n) +ᴺ K n

ordᴰ-g : (g : ℕ → S.Ord₀) → g 0 ≡ zero → (∀ n → g (suc n) ≡ suc (g n)) → ∀ n → ordᴰ (g n) ≡ natᴰ n
ordᴰ-g g g0 gs zero    = cong ordᴰ g0
ordᴰ-g g g0 gs (suc n) = trans (cong ordᴰ (gs n)) (cong B.suc (ordᴰ-g g g0 gs n))

cum-K : (g : ℕ → S.Ord₀) → g 0 ≡ zero → (∀ n → g (suc n) ≡ suc (g n)) → ∀ n → cumsum (ordᴰ ∘ g) n ≡ natᴰ (K n)
cum-K g g0 gs zero    = ordᴰ-g g g0 gs zero
cum-K g g0 gs (suc n) =
  trans (cong₂′ (cum-K g g0 gs n) (cong B.suc (ordᴰ-g g g0 gs (suc n)))) (+ᴰ-nat (K n) (suc (suc n)))
  where
  cong₂′ : ∀ {a a′ b b′} → a ≡ a′ → b ≡ b′ → a +ᴰ b ≡ a′ +ᴰ b′
  cong₂′ refl refl = refl

n≤K : ∀ n → n ≤ K n
n≤K zero    = z≤n
n≤K (suc n) = s≤s (m≤n⇒m≤1+n (m≤m+n n (K n)))

nat< : ∀ {m k} → m ≤′ k → natᴵ m <ᴵ suc (natᴵ k)
nat< ≤′-refl     = zero
nat< (≤′-step p) = suc (nat< p)

nat⊑ : ∀ {m k} → m ≤ k → natᴵ m ⊑ᴵ natᴵ k
nat⊑ z≤n     = z⊑
nat⊑ (s≤s p) = s⊑ (≅ᴵ-refl _) (nat< (≤⇒≤′ p))

ωᴰ-lv : (g : ℕ → S.Ord₀) → ℕ → Ordᴵ
ωᴰ-lv g n = τ (cumsum (ordᴰ ∘ g) n)

BO≈g : (g : ℕ → S.Ord₀) → g 0 ≡ zero → (∀ n → g (suc n) ≡ suc (g n)) → ψ⁰ (Ω (τ (ordᴰ (lim g)))) ≈ᵛ ψ⁰ (Ω ωᴵ)
BO≈g g g0 gs = l≼ upᵇ , l≼ dnᵇ
  where
  e : ∀ n → τ (cumsum (ordᴰ ∘ g) n) ≡ natᴵ (K n)
  e n = trans (cong τ (cum-K g g0 gs n)) (τ-nat (K n))
  upᵇ : ∀ n → ψ⁰ (Ω (τ (cumsum (ordᴰ ∘ g) n))) ≼ ψ⁰ (Ω ωᴵ)
  upᵇ n = ≼l (K n) (subst (λ u → ψ⁰ (Ω u) ≼ ψ⁰ (Ω (natᴵ (K n)))) (sym (e n)) (≼-refl _))
  dnᵇ : ∀ n → ψ⁰ (Ω (natᴵ n)) ≼ ψ⁰ (Ω (τ (ordᴰ (lim g))))
  dnᵇ n = ≼l n (subst (λ u → ψ⁰ (Ω (natᴵ n)) ≼ ψ⁰ (Ω u)) (sym (e n)) (⊑→≼ _ (Ψ⁰-mono (nat⊑ (n≤K n)))))

x₂≈BO : tr₀ (x 2) ≈ᵛ ψ⁰ (Ω ωᴵ)
x₂≈BO = ≼-trans (proj₁ (x-step 1)) (proj₁ b) , ≼-trans (proj₂ b) (proj₂ (x-step 1))
  where b = BO≈g _ refl (λ _ → refl)
```

## §4 与 $\gamma$ 链交错的前几步

`row₀`...`row₃`: $\gamma_0\preccurlyeq x_1\preccurlyeq\gamma_1\preccurlyeq x_2\preccurlyeq\gamma_2$. 下一步 $\gamma_2\preccurlyeq x_3$ 是第一个真要比较累加层号与 `toLevel` 层号的地方, 没有证出 (见 [BTBOVal](BTBOVal.lagda.md)).

```agda
row₀ : N.γ 0 ≼ tr₀ (x 1)
row₀ = ≼l 1 (s≼s z≼)

row₁ : tr₀ (x 1) ≼ N.γ 1
row₁ = ≼-trans (proj₁ ω≈) (⊑→≼ _ (Ψ⁰0 (suc zero)))

row₂ : N.γ 1 ≼ tr₀ (x 2)
row₂ = ≼-trans (⊑→≼ _ (Ψ⁰-mono {a = suc zero} {b = ωᴵ} (s⊑ z≅ (lim 1 zero)))) (proj₂ x₂≈BO)

toLevel-nat : ∀ m → natᴵ m ≅ᴵ toLevel (natᶜ m) (natᶜ-HS m)
toLevel-nat zero    = z≅
toLevel-nat (suc m) = s≅ (toLevel-nat m)

nat≺γ₁ : ∀ m → natᶜ m ≺ N.γ 1
nat≺γ₁ m = ≺l 0 (≺l (suc m) (subst (natᶜ m ≺_) (sym (T-nat (suc m))) (≺z (≅-refl⁰ (natᶜ m)))))

nat≺L₁ : ∀ m → natᴵ m ≺ᴵ N.L 1
nat≺L₁ m = ≺ᴵ-respˡ (toLevel-nat m) (toLevel-≺ (natᶜ-HS m) (N.cert 1) (nat≺γ₁ m))

nat⊑L₁ : ∀ n → natᴵ n ⊑ᴵ N.L 1
nat⊑L₁ zero    = z⊑
nat⊑L₁ (suc m) = s⊑′ (nat≺L₁ m)

row₃ : tr₀ (x 2) ≼ N.γ 2
row₃ = ≼-trans (proj₁ x₂≈BO) (⊑→≼ _ (Ψ⁰-mono (l⊑ nat⊑L₁)))
```
