# 累加的读回: 证据, 决定性测试, 毛刺

> 验收文件. 编译定理: 必带路径的证据在累加的塔第 1 项成立 (`req-twᶜ1`, 对照 `YiLimCheck.no-req`), 由任意树读出的 ℕ 极限都有路径 (`tw1ᶜ-just-all`, 对照 `tw1-none-all`); 有限的树读回不变 (`fin-same`).
> 有限测试: (a) ω+1 那一层用塔自己给的路线, 孩子 2 的底是结点 (`bωᶜ-tw`; 旧塔 `bω-tw` 是极限); (b) 毛刺: 层号 ω 的基本列成了 0, 1, 3, 6 (`tri`), 塔第 1 项链点 1 的孩子 1 从层号 2 变成层号 3 (`pt1-child`).
> 不否定什么. 值的比较在 `YiCumVal`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCumCheck where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (_+_; iter; cum; Ωt)
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiPhiCheck using (isΩ; isLim)
open import OCF.Lean.YiLimBlock
open import OCF.Lean.YiLimFold
open import OCF.Lean.YiLimLegal using (dL)
import OCF.Lean.YiLimCheck as LC
open import OCF.Lean.YiCumBlock
open import OCF.Lean.YiCumLegal using (ctwᶜ)
```

## 必带路径的证据 (对照 `no-req`)

`Req` 与 `LC.Req` 是同文的两个定义, `toLC` 逐字换型. 旧塔: `LC.no-req : LC.Req (tw 1) → ⊥`.

```agda
toLC : (ℓ : L) → Req ℓ → LC.Req ℓ
toLC zero     r        = tt
toLC (suc a)  r        = toLC a r
toLC (lim g)  (r , a)  = (λ n → toLC (g n) (r n)) , a
toLC (Ωₗ k h) (rk , r) = toLC k rk , λ c → toLC (h c) (r c)

req-twᶜ1 : LC.Req (twᶜ 1)
req-twᶜ1 = toLC (twᶜ 1) (Req-twᶜ 1)

req-all : (c : Tr zero) → LC.Req (zero ⊕ ↑ᶜ zero c)
req-all c = proj₂ req-twᶜ1 c

req-Λᶜ : LC.Req Λᶜ
req-Λᶜ = toLC Λᶜ Req-Λᶜ
```

`no-req` 的反例 `bad = lim (1, 0, 0, …)`: 累加后读成常值的 lim (1, 1, 1, …), 第 0 步的路径是 `self`.

```agda
bad-path : proj₂ (req-all LC.bad) zero ≡ self
bad-path = refl

bad-terms : (zero ⊕ cumₗ (λ n → ↑ᶜ zero (LC.badf n)) 0 ≡ suc zero) × (zero ⊕ cumₗ (λ n → ↑ᶜ zero (LC.badf n)) 3 ≡ suc zero)
bad-terms = refl , refl
```

## 由树读出的 ℕ 极限都有路径 (对照 `tw1-none-all`)

```agda
tw1ᶜ-just-all : (f : ℕ → Tr zero)
  → proj₂ (proj₂ (Rtᶜ-tw 1) (lim f))
  ≡ just (λ n → ⊑→≤ (⊕⊑ zero (⊑lift (cumₗ (λ m → ↑ᶜ zero (f m)) n) (↑ᶜ zero (f (suc n))))))
tw1ᶜ-just-all f = refl
```

ω+1 那一层 (塔第 1 项的分支 `suc ω₀`): 层号是 `suc (lim gωᶜ)`, 路线与层号证据都取自塔.

```agda
ω₀ : Tr zero
ω₀ = LC.ω₀

sω : ℕ → L
sω m = ↑ᶜ zero (iter suc zero m)

gωᶜ : ℕ → L
gωᶜ n = zero ⊕ cumₗ sω n

lv-ω+1 : zero ⊕ ↑ᶜ zero (suc ω₀) ≡ suc (lim gωᶜ)
lv-ω+1 = refl

εωᶜ : Ev (lim gωᶜ)
εωᶜ = proj₂ (proj₂ (Ev-twᶜ 1) (suc ω₀))

ρωᶜ : Rt (lim gωᶜ)
ρωᶜ = proj₂ (Rtᶜ-tw 1) (suc ω₀)

ω+1-just : proj₂ ρωᶜ ≡ just (λ n → ⊑→≤ (⊕⊑ zero (⊑lift (cumₗ sω n) (sω (suc n)))))
ω+1-just = refl

three : L
three = suc LC.two

ω+1-step1 : (gωᶜ 1 ≡ LC.one) × (gωᶜ 2 ≡ three)
ω+1-step1 = refl , refl
```

## 决定性测试: ω+1 那一层孩子 2 的底 (有限测试)

照 `LC.bω-tw`: 前缀里孩子 1 的 Ω 树对 "孩子 2 里的第 1 层" 的折叠. 孩子 2 现在是层号 3, 目标路径是 `ins (ins self)`.
塔自己给的路线: 结点 (`bωᶜ-tw`). 同一层号换成没有路径的 `Rt₀`: 极限 (`bωᶜ-none`), 即差别来自路径. 旧塔同一处: 极限 (`LC.bω-tw`).

```agda
preω : Tr (lim gωᶜ)
preω = up (up zero 0 (suc zero)) 1 (Ωt LC.one)

bωᶜ-tw : isΩ (bs (dL gωᶜ εωᶜ ρωᶜ (B₀ _) 2 preω) LC.one (ins (ins self)))
bωᶜ-tw = tt

bωᶜ-none : isLim (bs (dL gωᶜ εωᶜ (Rt₀ (lim gωᶜ)) (B₀ _) 2 preω) LC.one (ins (ins self)))
bωᶜ-none = tt
```

## 有限的树读回不变

```agda
fin-same : (n : ℕ) → ↑ᶜ zero (iter suc zero n) ≡ ↑ zero (iter suc zero n)
fin-same zero    = refl
fin-same (suc n) = cong suc (fin-same n)
```

## 毛刺 (有限测试)

层号 ω (读回 `ω₀`): 旧读回的基本列 0, 1, 2, 3; 累加后 0, 1, 3, 6.

```agda
tri : (gωᶜ 0 ≡ zero) × (gωᶜ 1 ≡ LC.one) × (gωᶜ 2 ≡ three) × (gωᶜ 3 ≡ suc (suc (suc three)))
tri = refl , refl , refl , refl

tri-old : (LC.gω 2 ≡ LC.two) × (LC.gω 3 ≡ three)
tri-old = refl , refl
```

ω+ω (`ωω = lim (ω, ω+1, …)`): 第 1 项旧读回是 ω+1, 累加后是 (ω ⊕ ω) + 1.

```agda
ωω : Tr zero
ωω = lim (iter suc ω₀)

ωω-term1 : cumₗ (λ n → ↑ᶜ zero (iter suc ω₀ n)) 1 ≡ suc (↑ᶜ zero ω₀ ⊕ ↑ᶜ zero ω₀)
ωω-term1 = refl
```

塔第 1 项闭项的链 (照 `YiLimVal` 的 `Gᴸ`, `Kᴸ`, `ptᴸ`): 闭项的形状不变, 链点 1 仍是 `lim (1, 1+1, …)`, 但它读成的层号 `lim g₁ᶜ` 的孩子 1 是层号 3, 不再是 2. `YiLimVal.low1-Ω₂` 在那里用的是层号 2 上的 `At.lower2`.

```agda
hᶜ : Tr zero → L
hᶜ x = zero ⊕ ↑ᶜ zero x

εhᶜ : (x : Tr zero) → Ev (hᶜ x)
εhᶜ x = proj₂ (proj₂ (Ev-twᶜ 1) x)

ρhᶜ : (x : Tr zero) → Rt (hᶜ x)
ρhᶜ x = proj₂ (Rtᶜ-tw 1) x

whᶜ : (x : Tr zero) → zero ≤ hᶜ x
whᶜ x = self ∙ lift zero (↑ᶜ zero x)

Gᶜ : Tr zero → Tr zero
Gᶜ x = ψ₀ (hᶜ x) (εhᶜ x) (ρhᶜ x) (Ωt (hᶜ x))

Kᶜ : Tr zero → Tr zero
Kᶜ x = ψs (hᶜ x) (εhᶜ x) (ρhᶜ x) (B₀ (hᶜ x)) zero (whᶜ x) (suc zero) (Ωt (hᶜ x))

ptᶜ : ℕ → Tr zero
ptᶜ = iter Kᶜ zero

ctwᶜ1-form : ctwᶜ 1 ≡ lim (cum (λ n → Gᶜ (ptᶜ n)))
ctwᶜ1-form = refl

pt1 : Tr zero
pt1 = lim (iter (suc zero +_) (suc zero))

pt1-same : ptᶜ 1 ≡ pt1
pt1-same = refl

g₁ g₁ᶜ : ℕ → L
g₁ n  = zero ⊕ ↑ zero (iter (suc zero +_) (suc zero) n)
g₁ᶜ n = zero ⊕ cumₗ (λ m → ↑ᶜ zero (iter (suc zero +_) (suc zero) m)) n

lv-pt1ᶜ : hᶜ (ptᶜ 1) ≡ lim g₁ᶜ
lv-pt1ᶜ = refl

pt1-child : (g₁ᶜ 0 ≡ LC.one) × (g₁ᶜ 1 ≡ three) × (g₁ 1 ≡ LC.two)
pt1-child = refl , refl , refl
```
