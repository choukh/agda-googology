# 最小比较表: 每一层都给的表与闭项

> 定义候选（最小比较表），未经作者采纳. 不改块, 不改折叠: 给 `YiTBRow.Rb ℓ` 对一切层号 ℓ 的闭项 `rbᶻ` (对层号递归, 不要 `Ok`), 配 `YiTBRow` 的折叠得塔 `twᶻ` 与终点 `EBOᶻ`.
> 条目只有三种, 都只看构造子: 两个孩子字面都是 `zero` 给 `self`; 一个孩子字面是 `zero` 且孩子 0 的层号字面是 `zero` 时, 由 `z≤` 给孩子 0 的层到另一孩子的层的路径; 其余没有条目.
> 不否定什么. 那一行在闭项里走哪条分支见 [YiMTHit](YiMTHit.lagda.md), 对否定一族的前提见 [YiMTObs](YiMTObs.lagda.md), 值见 [YiMTValue](YiMTValue.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMTTab where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiTBRow using (Rb; ψ)
```

## 表

`lo a b`: a 字面是零层时 a ≤ b. `hi a b`: b 字面是零层时 b ≤ a. `tbᶻ k h c c′` 的类型就是 `YiTBRow.RbS (sΩ k) h` 的一个条目 (c 是嵌入所在的孩子, c′ 是目标经过的孩子).

```agda
lo : (a b : L) → Maybe ((b ≤ a) ⊎ (a ≤ b))
lo zero     b = just (inj₂ (z≤ b))
lo (nd _ _) b = nothing

hi : (a b : L) → Maybe ((b ≤ a) ⊎ (a ≤ b))
hi a zero     = just (inj₁ (z≤ a))
hi a (nd _ _) = nothing

tbᶻ : (k : L) (h : Tr k → L) (c c′ : Tr k) → Maybe ((h c′ ≤ h c) ⊎ (h c ≤ h c′))
tbᶻ k h zero zero = just (inj₁ self)
tbᶻ k h zero c′   = lo (h zero) (h c′)
tbᶻ k h c    zero = hi (h c) (h zero)
tbᶻ k h _    _    = nothing

rbᶻ : (ℓ : L) → Rb ℓ
rbᶻ zero          = tt
rbᶻ (nd sS h)     = tt , λ c → rbᶻ (h c)
rbᶻ (nd sL h)     = tt , λ c → rbᶻ (h c)
rbᶻ (nd (sΩ k) h) = tbᶻ k h , λ c → rbᶻ (h c)
```

对角线上的零对一切层号有条目; 后继对后继, ℕ 极限对 ℕ 极限没有 (表不是自反的证据函数).

```agda
ent-zz : ∀ k h → tbᶻ k h zero zero ≡ just (inj₁ self)
ent-zz k h = refl

ent-ss : ∀ k h c c′ → tbᶻ k h (suc c) (suc c′) ≡ nothing
ent-ss k h c c′ = refl

ent-ll : ∀ k h f a f′ a′ → tbᶻ k h (lim f a) (lim f′ a′) ≡ nothing
ent-ll k h f a f′ a′ = refl
```

## 闭项

```agda
ψ₀ᶻ : (ℓ : L) → Ok ℓ → Tr ℓ → Tr⁺ zero
ψ₀ᶻ ℓ o = ψ ℓ o (rbᶻ ℓ) (B₀ ℓ) zero (z≤ ℓ) (Ωt zero)

twᶻ : ℕ → Tr zero
twᶻ n = proj₁ (ψ₀ᶻ (tw n) (Ok-tw n) (proj₁ (Ωt (tw n))))

EBOᶻ : Tr zero
EBOᶻ = proj₁ (ψ₀ᶻ Λ Ok-Λ (proj₁ (Ωt Λ)))
```
