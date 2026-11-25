# V107 的实验 (三): 诊断：上界 的最小见证树 (有限测试与形状)

> 诊断：上界. 不进成品. 档: 有限测试 (`refl`) 与形状定理, 没有值. 见证树 `N₂ = Upc (tw 1) two Ωt (Ωt 2)` (自身行的输出, 读作 Ω_Ω·Ω₂) 是 `T⁺` 的链里第一种要过摊平式的树.
> 它的折叠沿链 `e₂` 取行 (`e-step`); 链步把上一个链点 z 放进指数再朝第 1 层折叠. `e₂ 1` 是回退行造的结点的 ℕ 极限 (`e1-seq`, `e1-Ω`); z 里的结点上折后再折叠一律成为 ℕ 极限 (`node-lim`, `e2-inner`), 所以回灌进指数的只有可数的数据.
> 不给出什么: 没有 `read (ψ₀ … N₂)` 的上界. 判断与估值在回报里. 一般的陈述见 [YiDecFlat](YiDecFlat.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDecWit where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins; inb)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSTw1 using (h₁; G)
open import OCF.Lean.YiT2Frame using (ε¹; ρ¹; β; two; IsLim; IsΩ)
```

## 见证树与它的链

`N₂` 是孩子一侧槽位的结点, 分支 z 取第 1 层的树, 分支上是 `next (Up … β z)` (读作 Ω_Ω·ω^(z+1)). 朝第 1 层的折叠 `Gw` 走的路径是 `inb two (ins self)`.

```agda
nb : tw 1 ⊢ zero ◃ β
nb = Ωt-nz (tw 1)

d₂ : Dn (tw 1) (suc zero)
d₂ = down (down stop two) tt

N₂ : Tr (tw 1)
N₂ = Upc (tw 1) two β nb (Ωt (h₁ two))

br₂ : Tr (suc zero) → Tr (tw 1)
br₂ z = next (Up (suc zero) d₂ β nb z) (Up-nz (suc zero) d₂ β nb z)

N₂-form : N₂ ≡ Ω (inj₂ (two , inj₂ (inj₁ tt))) br₂
N₂-form = refl

Gw : Tr (tw 1) → Tr (suc zero)
Gw = ψs (tw 1) ε¹ ρ¹ (B₀ (tw 1)) (suc zero) (inb two (ins self)) (Ωt (suc zero)) (Ωt-nz (suc zero))

e₂ : ℕ → Tr (suc zero)
e₂ = iter (λ z → Gw (br₂ z)) zero

e-step : ψ₀ (tw 1) ε¹ ρ¹ N₂
       ≡ limc (λ n → ψ₀ (tw 1) ε¹ ρ¹ (br₂ (e₂ n))) (λ n → nz⊥ (tw 1) ε¹ ρ¹ (B₀ (tw 1)) (br₂ (e₂ n)))
e-step = refl
```

## 链的第 1 项: 回退行造的结点的极限

`β₁`: `Ωt (tw 1)` 的结点保留, 分支 c 上是 `Ωt 1 + ι 1 (G c)` (`YiT2Frame.β₁-form` 的同一棵树). 朝孩子层的折叠对 `Ωt (tw 1)` 的倍数是加法式的: `Ωt·2` 的像是分支 `β₁ + ι 1 (G c)` 的结点 (`Gwββ`), 不是 `β₁ + β₁`. `e₂ 1` 是这些像的 ℕ 极限 (`e1-seq`), 每一项都是结点 (`e1-Ω`).

```agda
β₁ : Tr (suc zero)
β₁ = Ω (inj₁ tt) (λ c → Ωt (suc zero) + ι (suc zero) (G c))

Gwβ : Gw β ≡ β₁
Gwβ = refl

Gwββ : Gw (β + β) ≡ Ω (inj₁ tt) (λ c → β₁ + ι (suc zero) (G c))
Gwββ = refl

seq : {ℓ : LF} (t : Tr ℓ) → IsLim t → ℕ → Tr ℓ
seq (lim f _) _ = f

e1-lim : IsLim (e₂ 1)
e1-lim = tt

e1-seq : ∀ n → seq (e₂ 1) e1-lim n ≡ Gw (iter (β +_) β n)
e1-seq n = refl

IsM : Tr (tw 1) → Set
IsM (Ω (inj₁ (inj₁ tt)) _) = ⊤
IsM _                      = ⊥

plusM : (x y : Tr (tw 1)) → IsM y → IsM (x + y)
plusM x (Ω (inj₁ (inj₁ tt)) g) _ = tt

sumM : ∀ n → IsM (iter (β +_) β n)
sumM zero    = tt
sumM (suc n) = plusM β (iter (β +_) β n) (sumM n)

main-Ω : (y : Tr (tw 1)) → IsM y → IsΩ (Gw y)
main-Ω (Ω (inj₁ (inj₁ tt)) g) _ = tt

e1-Ω : ∀ n → IsΩ (Gw (iter (β +_) β n))
e1-Ω n = main-Ω (iter (β +_) β n) (sumM n)
```

## 指数里的结点不回灌

第 1 层的任何结点 y, 放进指数 (上折) 再朝第 1 层折叠, 是 ℕ 极限 (`node-lim`). `e₂ 1` 的各项都是结点, 所以算 `e₂ 2` 时它们各自成为 ℕ 极限 (`e2-inner`).

```agda
node-lim : (y : Tr (suc zero)) → IsΩ y → IsLim (Gw (Up (suc zero) d₂ β nb y))
node-lim (Ω (inj₁ tt) g) _ = tt

e2-inner : ∀ n → IsLim (Gw (Up (suc zero) d₂ β nb (Gw (iter (β +_) β n))))
e2-inner n = node-lim (Gw (iter (β +_) β n)) (e1-Ω n)
```
