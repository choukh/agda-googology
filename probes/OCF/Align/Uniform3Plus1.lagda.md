# 统一形 (三): 消费者的复查

> 接 [Uniform3Full](Uniform3Full.lagda.md) 与 [OmegaPlus1](OmegaPlus1.lagda.md), [OmegaPlus1Neg](OmegaPlus1Neg.lagda.md).
>
> 1. **`H1ʰ` (深度 1 的闭包前提, 层对齐的记录): 定理.** `GA1ʰ E ζ → GA1ʰ (Ω̂A 1 E) (ζ ++ Ω_Ω)`, 对一切好帧. `¬H1` 的论证不再适用: 它的来源 `¬TΩ2-label` 在修正的树上为假 (`no-¬TΩ2`).
> 2. **字面的 `tow1` 仍然不能用 (编译否定 `¬H1-lit`).** OmegaPlus1Base 的 `tow1` 在深度 1 取 Uniform2Depth1 的 `GA1`, 它的互模拟字段是 $\approx_1$ ($\cong^\mathsf s$, 允许单侧 `up`). 修正地板不改变 Relative §1 的现象: 两个 $\cong^\mathsf s$ 的底在分支 $\eta=3$ 的深处给出不同的界 ($2$ 与 $1$). 所以字面的闭包假设 `GA1 E ζ → GA1 (Ω̂A 1 E) …` 对修正的树仍无居留, **原因与 `up (self n)` 无关, 是记录的互模拟太强**; 换成 `GA1ʰ` 塔 ($\cong^\mathsf A$, `FlrLabΩ`, 带诚实性的 W) 才是对的接口.
> 3. **深度 $\ge2$ 的记录 (§3, 只给类型).** `GAʰ (suc (suc d)) E ζ` = "把好帧送到好帧", 加 $\approx^\mathsf A$ 的高阶形式. `H1ʰ` 正是 `GAʰ 2 (Ω̂A 1) []` (`H1-shape`). 未证: `GAʰ 3 (Ω̂A 2) []`, 即 $\psi_0(\Omega_{\Omega+1})[2]=\psi_0(\psi_\Omega(\psi_\Omega(\Omega_\Omega)))$ 的内容; 它要深度 2 的折叠定理 (`fold 2` 上的 `WH`/`OH`, 后继行是帧的副本 `repA 1`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform3Plus1 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Ord₊ˢ; Ordˢ; Ωˢ; sqˢ; walkˢ)
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.Stage2 using (Ωᵗ)
import OCF.Align.EBO as E
open E using (T)
open import OCF.Align.OmegaKBase using (tΩ2)
open import OCF.Align.Symbolic using (Mlev)
open import OCF.Align.UniformS
import OCF.Align.TopDown as TD
open import OCF.Align.Uniform3Base
open import OCF.Align.Uniform3Depth1 using (_≈₁_; GA1; gr1; goodΩ̂₀)
open import OCF.Align.Uniform3Rel using (three)
open import OCF.Align.Uniform3Full
```

## §1 否定: 字面的 `GA1` 闭包

```agda
record Lift′ (X : Set) : Set₁ where
  constructor lift′
  field lower′ : X
open Lift′


four : Ordᴵ
four = suc three

pickL : (i : Ordᴵ) → Ordˢ i
pickL zero = Ωˢ zero
pickL (suc zero) = Ωˢ (suc zero)
pickL (suc (suc zero)) = Ord₊ˢ.suc Ord₊ˢ.zero
pickL (suc (suc (suc i))) = Ωˢ _
pickL (suc (suc (lim f s))) = Ωˢ _
pickL (suc (lim f s)) = Ωˢ _
pickL (lim f s) = Ωˢ _

pickR : (i : Ordᴵ) → Ordˢ i
pickR zero = Ωˢ zero
pickR (suc zero) = Ωˢ (suc zero)
pickR (suc (suc zero)) = Ord₊ˢ.up zero (Ord₊ˢ.up zero (Ord₊ˢ.suc Ord₊ˢ.zero))
pickR (suc (suc (suc i))) = Ωˢ _
pickR (suc (suc (lim f s))) = Ωˢ _
pickR (suc (lim f s)) = Ωˢ _
pickR (lim f s) = Ωˢ _

PL PR : Run fz
PL {i} _ _ = pickL i
PR {i} _ _ = pickR i

Rb : A 1 (fk zero ⊔ fk three)
Rb = fold 1 (fk three) (λ e q → e (suc q)) (Ω̂A 0) (Ωˢ three)

ev : Ev four (fz ⊔ (fk zero ⊔ fk three))
ev = tt , ((λ q → suc (suc (suc q))) , (λ q → q))

p0 : zero <ᴵ four
p0 = suc (suc (suc zero))

TL TR : Ordˢ zero
TL = Rb PL ev p0
TR = Rb PR ev p0

path : List ℕ
path = 1 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 2 ∷ []

bndL : TD.bndOf (walkˢ TL path) ≡ suc (suc zero)
bndL = refl

bndR : TD.bndOf (walkˢ TR path) ≡ suc zero
bndR = refl


PL≈PR : PL ≈ᴿ PR
PL≈PR ev p ev′ p′ z≅ = Ωˢ-≅ z≅
PL≈PR ev p ev′ p′ (s≅ z≅) = Ωˢ-≅ (s≅ z≅)
PL≈PR ev p ev′ p′ (s≅ (s≅ z≅)) = upʳ (upʳ (s≅ z≅))
PL≈PR ev p ev′ p′ (s≅ (s≅ (s≅ e))) = Ωˢ-≅ (s≅ (s≅ (s≅ e)))
PL≈PR ev p ev′ p′ (s≅ (s≅ (l≅ h))) = Ωˢ-≅ (s≅ (s≅ (l≅ h)))
PL≈PR ev p ev′ p′ (s≅ (l≅ h)) = Ωˢ-≅ (s≅ (l≅ h))
PL≈PR ev p ev′ p′ (l≅ h) = Ωˢ-≅ (l≅ h)

sq-≅ : ∀ {x y : Ordˢ zero} n → x ≅ˢ y → sqˢ x n ≅ˢ sqˢ y n
sq-≅ n z≅ = z≅
sq-≅ n (s≅ d) = s≅ d
sq-≅ n (l≅ h) = h n
sq-≅ n (lᵢ≅ {p = ()} e h)
sq-≅ n (upˡ {r = ()} d)
sq-≅ n (upʳ {r = ()} d)
sq-≅ zero (ŝ≅ k ec et eg) = et
sq-≅ (suc n) (ŝ≅ k ec et eg) = ŝ≅ k ec et eg
sq-≅ zero (ĉ≅ ec dt dg eo eO) = eo
sq-≅ (suc n) (ĉ≅ ec dt dg eo eO) = ĉ≅ ec dt dg eo eO

walk-≅ : ∀ {x y : Ordˢ zero} ps → x ≅ˢ y → walkˢ x ps ≅ˢ walkˢ y ps
walk-≅ [] d = d
walk-≅ (n ∷ ps) d = walk-≅ ps (sq-≅ n d)

bnd-≅ : ∀ {x y : Ordˢ zero} → x ≅ˢ y → TD.bndOf x ≅ᴵ TD.bndOf y
bnd-≅ z≅ = z≅
bnd-≅ (s≅ d) = z≅
bnd-≅ (l≅ h) = z≅
bnd-≅ (lᵢ≅ {p = ()} e h)
bnd-≅ (upˡ {r = ()} d)
bnd-≅ (upʳ {r = ()} d)
bnd-≅ (ŝ≅ k ec et eg) = ec
bnd-≅ (ĉ≅ ec dt dg eo eO) = z≅

no21 : suc (suc zero) ≅ᴵ suc zero → ⊥
no21 (s≅ ())

¬bR : (∀ η η′ → η ≅ᴵ η′ → fold 1 (fk η) (λ e q → e (suc q)) (Ω̂A 0) (Ωˢ η) ≈₁ fold 1 (fk η′) (λ e q → e (suc q)) (Ω̂A 0) (Ωˢ η′)) → ⊥
¬bR br = no21 (bnd-≅ (walk-≅ path (br three three (≅ᴵ-refl three) fz∼ PL≈PR ev p0 ev p0 z≅)))

ev₀ : Ev (suc zero) (fz ⊔ (fk zero ⊔ fk zero))
ev₀ = tt , ((λ q → q) , (λ q → q))

e₃ : suc zero ⊑ᴵ three
e₃ = s⊑ z≅ (suc (suc zero))

¬H1-lit : (∀ {fl} {E : A 1 fl} {ζ} → GA1 E ζ → GA1 (Ω̂A 1 E) (ζ ++ ΩΩ ∷ [])) → ⊥
¬H1-lit H with gr1 (H goodΩ̂₀) fz∼ PL≈PR ev₀ zero ev₀ zero z≅
... | ŝ≅ k ec et eg = no21 (bnd-≅ (walk-≅ path (eg three e₃ three e₃ (≅ᴵ-refl three))))
```

## §2 正面

```agda
H1ʰ : ∀ {fl} {E : A 1 fl} {ζ} → GA1ʰ E ζ → GA1ʰ (Ω̂A 1 E) (ζ ++ ΩΩ ∷ [])
H1ʰ G = Main.goodΩ̂₁ʰ G

no-¬TΩ2 : ((∀ {ℓ} (ev : Ev ℓ (fz ⊔ (fk zero ⊔ (fk zero ⊔ fz)))) (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (Ψ (Ψ ∅ᵀ)) ev z) tΩ2) → ⊥) → ⊥
no-¬TΩ2 neg = neg TΩ2-label

-- 再迭代一次闭包: 帧 ψ_Ω(Ω_Ω)+Ω_Ω
ΩΩ² : GA1ʰ (Ω̂A 1 (Ω̂A 1 (Ω̂A 0))) ((ΩΩ ∷ []) ++ ΩΩ ∷ [])
ΩΩ² = H1ʰ (H1ʰ goodΩ̂₀ʰ)
```

## §3 深度 $\ge2$ 的记录 (只给类型)

```agda
GAʰ : ∀ d {φ} → A (suc d) φ → T → Set₁
GAʰ zero E ζ = Lift′ (GA1ʰ E ζ)
GAʰ (suc d) {φ} E ζ = ∀ {fl} {F : A (suc d) fl} {ζ′} → GAʰ d F ζ′ → GAʰ d (E F) (ζ′ ++ ψΩᵗ ζ)

-- H1ʰ 的形状: 深度 1 的闭包就是 GAʰ 1 (Ω̂A 1) []
H1-shape : GAʰ 1 (Ω̂A 1) []
H1-shape (lift′ G) = lift′ (H1ʰ G)

HΩ̂ʰ : ℕ → Set₁
HΩ̂ʰ d = GAʰ d (Ω̂A d) []
```
