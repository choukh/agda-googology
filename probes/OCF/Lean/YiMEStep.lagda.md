# 值接口的记号直连实例 (四): 朝 ψ₀(Ω_{Ω+1}) 的形式检验

> 验收文件 (读记号). 判决: 条件定理与有限测试, 一站本身未证. 合法块上的陈述 `Step₂⁺ᴸ` (ψ₀(Ω_{Ω+1}) 的记号参照 ≼ `read (twᶜ 2)`) 归约到逐行的 `M⁰` (`step⁺-red`, 条件定理); 第 0 行就是 BTBO 那一行落在层号 `tw 1 ⊕ ↑c₁` 上 (`row₀-btbo`), c₁ 是 Ω 结点层号自身行的输出 (`c₁-form`, 测试).
> 一切层号上的关系 `Mᴸ` (对层号递归, 检查器接受) 以 "层号对记号下标" 的关系 `Ix` 为参数; 这里没有给出 Ω 结点层号与 ℕ 极限层号上的 `Ix`.
> 不否定什么: 没有编译的否定; 未走通之处与所缺引理的形状见回报, 是判断.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMEStep where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ink; inb; posW; posW⁼; Ev; Ev-tw; Rt-tw) renaming (Rt to Rtᴾ)
open import OCF.Lean.YiLegFold
import OCF.Align.EboLeanDef as E
open E using (HC; γT)
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiMEBase
open import OCF.Lean.YiMEAnchor using (ψ₀ᵗ; Ω₁ᵗ; module G⁰)
```

## 一切层号上的关系

`Ix k ν`: 层号 k 的槽位对着记号的共尾下标 ν (余尾 Ω_{ν+1}). 槽位的低层关系与孩子层的关系由层号递归给出; 锚点用的 `M¹` 是 `Ix zero ν = (ν ≡ [])` 时第 1 层的情形.

```agda
module Lev (Ix : L → E.T → Set) where
  mutual
    Mᴸ : (j : L) → E.T → Tr j → Set
    Mᴸ j = Mᴰ (Sig j) (Lowᴸ j) (Chdᴸ j) (λ p ν → Ix (at j p) ν)

    Lowᴸ : (j : L) (p : Pos j) → E.T → Br j p → Set
    Lowᴸ (suc a)  t              = Low⁼ a t
    Lowᴸ (lim g)  (n , t)        = Low⁼ (g n) t
    Lowᴸ (Ωₗ k h) (inj₁ t)       = Low⁼ k t
    Lowᴸ (Ωₗ k h) (inj₂ (c , t)) = Low⁼ (h c) t

    Low⁼ : (a : L) (t : Pos⁼ a) → E.T → Br⁼ a t → Set
    Low⁼ a (inj₁ _) = Mᴸ a
    Low⁼ a (inj₂ p) = Lowᴸ a p

    Chdᴸ : (j : L) (c : Ch j) → E.T → ChT j c → Set
    Chdᴸ (suc a)  _ = Mᴸ a
    Chdᴸ (lim g)  n = Mᴸ (g n)
    Chdᴸ (Ωₗ k h) c = Mᴸ (h c)
```

## 陈述与归约

塔第 2 项的闭项是结点的折叠: 部分和的极限, 第 n 行的孩子下标 `c₂ n` 是折叠输出回灌 n 次. 记号一侧 t₊[n] = ψ₀(γ₊ n), γ₊ 0 = Ω_Ω, γ₊ (n+1) = ψ_Ω(γ₊ n).

```agda
t₊ : E.T
t₊ = ψ₀ᵗ (E.Ωs Ω₁ᵗ)

Step₂⁺ᴸ : Set
Step₂⁺ᴸ = (h : HC t₊) → Rt h ≼ read (twᶜ 2)

h₂ : Tr (tw 1) → L
h₂ c = tw 1 ⊕ ↑ (tw 1) c

G₂ : Tr (tw 1) → Tr (tw 2)
G₂ c = up zero c (Ωt (h₂ c)) (Ωt-nz (h₂ c))

c₂ : ℕ → Tr (tw 1)
c₂ = iter (λ z → ψs (tw 2) (Ev-tw 2) (Rt-tw 2) (B₀ (tw 2)) (tw 1) (ink self) (Ωt (tw 1)) (Ωt-nz (tw 1)) (G₂ z)) zero

row : ℕ → Tr zero
row n = ψ⊥ (tw 2) (Ev-tw 2) (Rt-tw 2) (B₀ (tw 2)) (G₂ (c₂ n))

nzrow : ∀ n → zero ⊢ zero ◃ row n
nzrow n = nz⊥ (tw 2) (Ev-tw 2) (Rt-tw 2) (B₀ (tw 2)) (G₂ (c₂ n))

form₂ : twᶜ 2 ≡ limc row nzrow
form₂ = refl

γ₊ : ℕ → E.T
γ₊ = γT (E.Ωs Ω₁ᵗ) Ω₁ᵗ

step⁺-red : (∀ n → M⁰ (ψ₀ᵗ (γ₊ n)) (row (suc n))) → Step₂⁺ᴸ
step⁺-red prem h = lower⁰ (mL refl (λ n → G⁰.m-cum row nzrow (suc n) (prem n))) h
```

第 0 行的前提就是 BTBO 那一行, 落在层号 `h₂ (c₂ 1)` 上: 行的折叠是孩子层的底折叠.

```agda
_ : ψ₀ᵗ (γ₊ 0) ≡ E.EBOψ 2
_ = refl

row-form : ∀ n → row n ≡ ψ⊥ (h₂ (c₂ n)) (proj₂ (proj₂ (Ev-tw 2) (c₂ n))) (proj₂ (Rt-tw 2) (c₂ n))
                           (dW (tw 1) h₂ (Ev-tw 2) (Rt-tw 2) (B₀ (tw 2)) (c₂ n) zero) (Ωt (h₂ (c₂ n)))
row-form n = refl

row₀-btbo : M⁰ (E.EBOψ 2) (row 1) → (h : HC (E.EBOψ 2)) → Rt h ≼ read (twᶜ 2)
row₀-btbo m h = lower⁰ (G⁰.m-cum row nzrow 1 m) h
```

## 形状 (有限测试)

`c₂ 1` 是层号 `tw 1` 的 Ω 树折到自身: 结点保留, 孩子走 Ω 结点层号的自身行 (上折 `Upc`). 它作孩子下标时, 层号 `h₂ (c₂ 1)` 又是 Ω 结点层号, 孩子层号读自上折的输出.

```agda
h₁ : Tr zero → L
h₁ z = zero ⊕ ↑ zero z

c₁-form : c₂ 1 ≡ Ω (inj₁ (inj₁ tt)) (λ z → Upc (tw 1) z (Ωt (tw 1)) (Ωt-nz (tw 1)) (Ωt (h₁ z)))
c₁-form = refl

lev₁-form : h₂ (c₂ 1) ≡ Ωₗ zero (λ z → tw 1 ⊕ ↑ (tw 1) (Upc (tw 1) z (Ωt (tw 1)) (Ωt-nz (tw 1)) (Ωt (h₁ z))))
lev₁-form = refl
```

上折造出的结点槽位在孩子一侧, 它的链步路径是 `inb`; 目标路径是 `inb c′ w` 时, 孩子一侧槽位的结点一律折叠, c′ 与 c 相同时也是 (摊平式丢掉的同支结点; 定义的展开).

```agda
_ : (k : L) (h : Tr k → L) (c : Tr k) (t : Pos⁼ (h c)) → posW (Ωₗ k h) (inj₂ (c , t)) ≡ inb c (posW⁼ (h c) t)
_ = λ k h c t → refl

drop-same : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rtᴾ (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L)
  (c : Tr k) (w : j ≤ h c) (β : Tr j) (nβ : j ⊢ zero ◃ β) (t : Pos⁼ (h c)) (G : Br⁼ (h c) t → Tr (Ωₗ k h))
  → ψs (Ωₗ k h) ε ρ B j (inb c w) β nβ (Ω (inj₂ (c , t)) G)
  ≡ limc (λ n → ψs (Ωₗ k h) ε ρ B j (inb c w) β nβ (G (iter (λ z → fromBr (Ωₗ k h) (inj₂ (c , t))
            (ψs (Ωₗ k h) ε ρ B (at⁼ (h c) t) (inb c (posW⁼ (h c) t))
              (bs B (at⁼ (h c) t) (inb c (posW⁼ (h c) t)))
              (ns B (at⁼ (h c) t) (inb c (posW⁼ (h c) t))) (G z))) (br0⁼ (h c) t) n)))
         (λ n → nzs (Ωₗ k h) ε ρ B j (inb c w) β nβ (G (iter (λ z → fromBr (Ωₗ k h) (inj₂ (c , t))
            (ψs (Ωₗ k h) ε ρ B (at⁼ (h c) t) (inb c (posW⁼ (h c) t))
              (bs B (at⁼ (h c) t) (inb c (posW⁼ (h c) t)))
              (ns B (at⁼ (h c) t) (inb c (posW⁼ (h c) t))) (G z))) (br0⁼ (h c) t) n)))
drop-same k h ε ρ B j c w β nβ t G = refl
```
