# FGH 式折叠 (原型): K(n) 的陈述与第一个挡住的引理

> 验收文件 (读记号), 不进成品; 折叠一行不改. 只是陈述, 未证: `Kᶠ n` (塔第 n 项 `twᶠ n` 不低于 ψ₀(Ω_{ΩTower n}) 的参照; `Kᶠ 1`, `Kᶠ 2` 逐字是简报的 K(1), K(2), `refl`), `Lowᶠ` (可数层号上的下界, K(1) 第一个要用的引理). 未走通, 没有编译的否定.
> 编译定理, 无前提: 底族条件 `OKᶠ` 对默认底族成立并被 `jB` 保持 (`ok-B₀`, `ok-jB`, 所以 `Lowᶠ` 的前提可满足); 读回带证书 (`HSrᶠ`); 塔第 1 项的每个迭代逐字是孩子层 `h₁ zᵢ` 上裸 Ω 树的折叠 (`TwOne.row`, `refl`); 条件定理 `TwOne.step-low`: 由 `Lowᶠ` 得每一步不低于下标以下的 ψ⁰(Ω_x).
> 不涉及上界. 主线的对应引理是 `YiLSTw1.lower-↑` (对 F2 的折叠); 这里的结点规则不同 (单次对角, 链在后继的迭代里), 不能搬.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFGValue where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiFGFold
open import OCF.Lean.YiBRValue using (readRW)
open import OCF.Lean.YiRefTw2 using (Rt)
import OCF.Align.EboLeanDef as E
open E using (HC; ΩTower; EBOψ)
import OCF.Align.Level as O
open import OCF.Align.Value using (_≼_)
```

## K(n)

```agda
Q₀ᶠ : (ℓ : L) → Ok ℓ → E.T → Set
Q₀ᶠ ℓ o ν = (h : HC (E.ψ [] (E.Ωt ν) ∷ [])) → Rt h ≼ readRW (proj₁ (ψ₀ᶠ ℓ o (suc (proj₁ (Ωt ℓ)))))

Kᶠ : ℕ → Set
Kᶠ n = Q₀ᶠ (tw n) (Ok-tw n) (ΩTower n)

_ : Kᶠ 1 ≡ ((h : HC (EBOψ 2)) → Rt h ≼ readRW (twᶠ 1))
_ = refl

_ : Kᶠ 2 ≡ ((h : HC (EBOψ 3)) → Rt h ≼ readRW (twᶠ 2))
_ = refl
```

## 底族条件

```agda
infix 4 _⊢_⊴_
_⊢_⊴_ : (j : L) → Tr j → Tr j → Set
j ⊢ x ⊴ y = (x ≡ y) ⊎ (j ⊢ x ◃ y)

⊴◃ : ∀ {j} {x y z : Tr j} → j ⊢ x ⊴ y → j ⊢ y ◃ z → j ⊢ x ◃ z
⊴◃ (inj₁ refl) d = d
⊴◃ (inj₂ d′)   d = ◃t d′ d

OKᶠ : (ℓ : L) → Base ℓ → Set
OKᶠ ℓ B = ∀ j (u : j ≤ ℓ) → j ⊢ proj₁ (Ωt j) ⊴ proj₁ (B j u)

ok-B₀ : ∀ ℓ → OKᶠ ℓ (B₀ ℓ)
ok-B₀ ℓ j u = inj₁ refl

ok-jB : ∀ ℓ o B x → OKᶠ ℓ B → OKᶠ ℓ (jB ℓ o B x)
ok-jB ℓ o B x ok j u = inj₂ (⊴◃ (ok j u) (infl ℓ o B j u (B j u) x))
```

## 读回的证书, 可数层号

```agda
◃⊑ᶠ : {x y : Tr zero} → zero ⊢ x ◃ y → readRW x O.⊑ readRW y
◃⊑ᶠ ◃s            h = O.≺s h
◃⊑ᶠ (◃l n)        h = O.≺l n h
◃⊑ᶠ (◃w {p = ()})
◃⊑ᶠ (◃u _ () _ _)
◃⊑ᶠ (◃c _ () _)
◃⊑ᶠ (◃t d e)      h = ◃⊑ᶠ e (◃⊑ᶠ d h)

HSrᶠ : (x : Tr zero) → O.HS (readRW x)
HSrᶠ zero          = O.hz
HSrᶠ (suc x)       = O.hs (HSrᶠ x)
HSrᶠ (lim f a)     = O.hl (λ n → HSrᶠ (f n)) (λ n → ◃⊑ᶠ (a n))
HSrᶠ (Ω () _)
HSrᶠ (up _ () _ _)

lvlᶠ : Tr zero → O.Ordᴵ
lvlᶠ x = O.toLevel (readRW x) (HSrᶠ x)

h₁ : Tr zero → L
h₁ x = zero ⊕ ↑ zero x

o₁ : (x : Tr zero) → Ok (h₁ x)
o₁ x = proj₂ (Ok-tw 1) x
```

## 第一个挡住的引理

`Lowᶠ`: 第 0 层的树 x 严格低于 z 时, 参照在层号 `toLevel x` 上的 ψ⁰(Ω) 不高于孩子层 `h₁ z` 上裸 Ω 树的折叠 (任意满足 `OKᶠ` 的底族, 任意目标底与路径). 移一层是因为结点只取一次对角, 层号 x 上的链要到上一层的后继迭代里才出现 (判断).

```agda
Lowᶠ : Set
Lowᶠ = (x z : Tr zero) → zero ⊢ x ◃ z → (B : Base (h₁ z)) → OKᶠ (h₁ z) B → (β : Tr⁺ zero) (w : zero ≤ h₁ z)
  → O.ψ⁰ (O.Ω (lvlᶠ x)) ≼ readRW (proj₁ (Φ (h₁ z) (o₁ z) B zero w β (proj₁ (Ωt (h₁ z)))))
```

塔第 1 项是 (底族, 底) 迭代的极限; 每一步 (任意底族 B, 底 β) 逐字是孩子层 `h₁ zᵢ` 上裸 Ω 树的折叠, 下标 `zᵢ` 是首分支折过的底族沿 `ink self` 在第 0 层的值, 孩子的底族由 B′ 沿 `inc zᵢ` 读出.

```agda
module TwOne (B : Base (tw 1)) (β : Tr⁺ zero) where
  g₁ : Tr zero → Tr (tw 1)
  g₁ c = up zero c (proj₁ (Ωt (h₁ c))) (proj₂ (Ωt (h₁ c)))

  B′ : Base (tw 1)
  B′ = jB (tw 1) (Ok-tw 1) B (g₁ zero)

  β′ : Tr⁺ zero
  β′ = Φ (tw 1) (Ok-tw 1) B zero (z≤ (tw 1)) β (g₁ zero)

  zᵢ : Tr zero
  zᵢ = proj₁ (B′ zero (ink self))

  row : Φ (tw 1) (Ok-tw 1) B zero (z≤ (tw 1)) β (proj₁ (Ωt (tw 1)))
      ≡ Φ (h₁ zᵢ) (o₁ zᵢ) (λ i u → Φ (tw 1) (Ok-tw 1) B′ i (inc zᵢ u) (B′ i (inc zᵢ u)) zero) zero (z≤ (h₁ zᵢ))
          (Φ (tw 1) (Ok-tw 1) B′ zero (z≤ (tw 1)) β′ zero) (proj₁ (Ωt (h₁ zᵢ)))
  row = refl
```

`Lowᶠ` 下的一步 (条件定理): 底族满足 `OKᶠ` 时, 塔第 1 项的每一步不低于下标以下一切 x 上的 ψ⁰(Ω_x). 孩子的底族满足 `OKᶠ` (`ok-child`) 是定理.

```agda
  ok-child : OKᶠ (tw 1) B → OKᶠ (h₁ zᵢ) (λ i u → Φ (tw 1) (Ok-tw 1) B′ i (inc zᵢ u) (B′ i (inc zᵢ u)) zero)
  ok-child ok i u = inj₂ (⊴◃ (ok-jB (tw 1) (Ok-tw 1) B (g₁ zero) ok i (inc zᵢ u)) ◃s)

  step-low : Lowᶠ → OKᶠ (tw 1) B → (x : Tr zero) → zero ⊢ x ◃ zᵢ
    → O.ψ⁰ (O.Ω (lvlᶠ x)) ≼ readRW (proj₁ (Φ (tw 1) (Ok-tw 1) B zero (z≤ (tw 1)) β (proj₁ (Ωt (tw 1)))))
  step-low low ok x d = low x zᵢ d _ (ok-child ok) _ (z≤ (h₁ zᵢ))
```
