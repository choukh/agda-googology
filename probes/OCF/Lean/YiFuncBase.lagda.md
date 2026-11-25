# YiFunc 实例：ψ⁰∘Ω 对前驱嵌入的函子性的最小实例

**验收文件，档位：编译定理。** `FUNC` 的结论在三类输入上成立：有限层号 (`func-nat`，由嵌入数出 n ≤ m 再用结构可比)；两个方向都有保值嵌入的层号 (`func₂`，由 `YiEmb2.VMˣ₂` 经 `embˣ`)，含非结构可比的 ω+1 对 ω⁺+1 (`func-sω`)；链上第一个实例 `func-L1 : PEmb (L⁺ (D.L 1)) (L⁺ (κ 1))` (由 `YiEmb2.p1-one`，两个方向的值相等，不是把一般的 `FUNC` 用在 `emb₁ⁿ` 上)。
不给一般的 `FUNC`；单向值增大的嵌入的归约见 [YiFuncLim](YiFuncLim.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFuncBase where

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.Level as L
open L using (Ordᴵ; _<ᴵ_; _≅ᴵ_; _⊑ᴵ_; _≺ᴵ_; via)
import OCF.Align.Uniform as Un
open import OCF.Align.Value using (_≼_; z≼; l≼)
open import OCF.Align.BTBOFullEmb using (PEmb)
open PEmb
open import OCF.Align.YiMonoEmb using (PEmb-⊑; ω⁺ᴵ; ω⊑ω⁺)
open import OCF.Align.YiVmConExact using (XEmb; XEmb-⊑; XEmb-suc; V; V-≺; embˣ)
open import OCF.Lean.YiEmb2 using (VMˣ₂; p1-one)
open import OCF.Lean.YiPEStep using (L⁺; func-⊑; PEmb-≅ʳ)
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Lean.YiLeanValFin using (κ)
```

## 1 限制与有限层号

`PEmb-res`：嵌入限制到一个前驱 `c` 之下，目标取 `c` 的像。

```agda
PEmb-res : ∀ {a b c} (P : PEmb a b) (r : c ≺ᴵ a) → PEmb c (map P r)
map (PEmb-res P r) s = map P (L.≺ᴵ-trans s r)
bnd (PEmb-res P r) s = mono P (L.≺ᴵ-trans s r) r s
mono (PEmb-res P r) s t lt = mono P (L.≺ᴵ-trans s r) (L.≺ᴵ-trans t r) lt
coh (PEmb-res P r) s t e = coh P (L.≺ᴵ-trans s r) (L.≺ᴵ-trans t r) e

nat< : ∀ {c} m → c <ᴵ L.natᴵ m → Σ ℕ λ k → (suc k ≤ m) × (c ≅ᴵ L.natᴵ k)
nat< (suc m) L.zero = m , ≤-refl′ m , L.≅ᴵ-refl _
  where ≤-refl′ : ∀ m → suc m ≤ suc m
        ≤-refl′ zero = s≤s z≤n
        ≤-refl′ (suc m) = s≤s (≤-refl′ m)
nat< (suc m) (L.suc q) with nat< m q
... | k , p , e = k , ≤-trans p (n≤s _) , e
  where n≤s : ∀ n → n ≤ suc n
        n≤s zero = z≤n
        n≤s (suc n) = s≤s (n≤s n)

cnt : ∀ n m → PEmb (L.natᴵ n) (L.natᴵ m) → n ≤ m
cnt zero m P = z≤n
cnt (suc n) m P with bnd P (via (L.≅ᴵ-refl (L.natᴵ n)) L.zero)
... | via e q with nat< m q
...   | k , p , e′ = ≤-trans (s≤s (cnt n k (PEmb-≅ʳ (PEmb-res P r) (L.≅ᴵ-trans e e′)))) p
  where r = via (L.≅ᴵ-refl (L.natᴵ n)) L.zero

split : ∀ n m → n ≤ suc m → (n ≤ m) ⊎ (n ≡ suc m)
split zero m z≤n = inj₁ z≤n
split (suc n) zero (s≤s z≤n) = inj₂ refl
split (suc n) (suc m) (s≤s p) with split n m p
... | inj₁ q = inj₁ (s≤s q)
... | inj₂ refl = inj₂ refl

nat<s : ∀ n m → n ≤ m → L.natᴵ n <ᴵ L.suc (L.natᴵ m)
nat<s zero zero z≤n = L.zero
nat<s n (suc m) p with split n m p
... | inj₁ q = L.suc (nat<s n m q)
... | inj₂ refl = L.zero

nat⊑ : ∀ {n m} → n ≤ m → L.natᴵ n ⊑ᴵ L.natᴵ m
nat⊑ z≤n = L.z⊑
nat⊑ {suc n} {suc m} (s≤s p) = L.s⊑ (L.≅ᴵ-refl (L.natᴵ n)) (nat<s n m p)

func-nat : ∀ n m → PEmb (L.natᴵ n) (L.natᴵ m) → PEmb (L⁺ (L.natᴵ n)) (L⁺ (L.natᴵ m))
func-nat n m P = func-⊑ (nat⊑ (cnt n m P))
```

## 2 两个方向都有保值嵌入

ω 与 ω⁺ = lim (n+1) 互为 `⊑ᴵ`，所以 `FUNC` 的结论在 (ω, ω⁺) 两个方向上是 `func-⊑`；非结构可比的是它们的后继 (`YiMonoEmb.ω-not`)，那里用两个方向的保值嵌入。

```agda
ω⁺⊑ω : ω⁺ᴵ ⊑ᴵ L.ωᴵ
ω⁺⊑ω = L.l⊑ (λ n → L.Sim→⊑ᴵ (λ q → L.lim (suc n) q))

func-ω : PEmb (L⁺ L.ωᴵ) (L⁺ ω⁺ᴵ)
func-ω = func-⊑ ω⊑ω⁺

func-ω′ : PEmb (L⁺ ω⁺ᴵ) (L⁺ L.ωᴵ)
func-ω′ = func-⊑ ω⁺⊑ω

V-⊑ : ∀ {a b} → a ⊑ᴵ b → V a ≼ V b
V-⊑ L.z⊑ = z≼
V-⊑ (L.s⊑ e q) = V-≺ (via e q)
V-⊑ (L.l⊑ h) = l≼ (λ n → V-⊑ (h n))

func₂ : ∀ {a b} → XEmb a b → XEmb b a → PEmb (L⁺ a) (L⁺ b)
func₂ {a} {b} X Y = XEmb.P (embˣ _ (Un.Uniform a) _ (Un.Uniform b) (VMˣ₂ X Y))

Xω : XEmb (L.suc L.ωᴵ) (L.suc ω⁺ᴵ)
Xω = XEmb-suc (XEmb-⊑ ω⊑ω⁺) (V-⊑ ω⊑ω⁺) (V-⊑ ω⁺⊑ω)

Xω′ : XEmb (L.suc ω⁺ᴵ) (L.suc L.ωᴵ)
Xω′ = XEmb-suc (XEmb-⊑ ω⁺⊑ω) (V-⊑ ω⁺⊑ω) (V-⊑ ω⊑ω⁺)

func-sω : PEmb (L⁺ (L.suc L.ωᴵ)) (L⁺ (L.suc ω⁺ᴵ))
func-sω = func₂ Xω Xω′
```

## 3 链上第一个实例

`p1-one : ψ⁰ (Ω (D.L 1)) ≼ˣ ψ⁰ (Ω (κ 1))` 来自 `D.γ 1` 与链点 1 两个方向的值相等 (`YiChainBack.γ₁≈`)；`embˣ` 把它读成嵌入，两边的证书正是 `L⁺` 用的 `Uniform`。

```agda
func-L1 : PEmb (L⁺ (D.L 1)) (L⁺ (κ 1))
func-L1 = XEmb.P (embˣ _ (Un.Uniform (D.L 1)) _ (Un.Uniform (κ 1)) p1-one)
```
