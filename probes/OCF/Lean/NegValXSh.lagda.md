# NegValX (四): `sh-not-mono≤` 的边界: 在 ValC 的关系下回灌单调且不降

> 不含记号. 入口 [NegValX](NegValX.lagda.md). 本篇**不依赖**构造一路 ValX 的接口. 只导入 [CRwBase](CRwBase.lagda.md), [CRwFold](CRwFold.lagda.md), [CRw](CRw.lagda.md) (实例 `I₁`), [ValCRel](ValCRel.lagda.md), [ValCBase](ValCBase.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** 否定一路 NegValC 的 `sh-not-mono≤` (定理): 在含 "极限在左边" (`l≤`) 的 Fab5 式关系下, `I₁` 的回灌 $\mathrm{sh}_0\,B\,c=B\boxplus\mathrm{leg}\,c$ 对坐标不单调 ($\lim(1,1,\dots)\le1$, 回灌后反向). ValC 的关系 (`ValCRel.LeAt`) 把 "极限在左边" 收窄为对严格增子列 (`l≤l σ`). 本篇问: 在这个关系下回灌还有问题吗?
>
> **`sh-mono` (定理).** 在第 0 层的 `LeAt hz` 下: $B\le B'$, $c\le c'$ ⟹ $\mathrm{sh}_0\,B\,c\le\mathrm{sh}_0\,B'\,c'$. **`sh-infl`**: $c\le\mathrm{sh}_0\,B\,c$, $B\le\mathrm{sh}_0\,B\,c$. 由 `leg-mono`, `≤leg` ($\mathrm{leg}$ 单调且不降) 与加法的单调给出.
>
> **`l11-unrelated` (定理).** $\lim(1,1,\dots)\not\le1$ 在 `LeAt hz` 下 (`sh-not-mono≤` 的那一对在 ValC 的关系下不相关). 这把 ValC 入口与 ValX 接口说明里的判断 "在 `l≤l` 关系下这一对不再相关" 写成定理.
>
> **前提实例.** 全称, 无额外前提.
>
> **只否定什么.** 本篇没有否定: 它划出 `sh-not-mono≤` 的范围: 它只否定含 `l≤` 的关系; 在 ValC 的关系下回灌不是障碍. **不说**跨底折叠在 ValC 式关系下单调 (那要处理世界的移动与本身/拷贝, 见 [NegValXSelf](NegValXSelf.lagda.md)).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegValXSh where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwIf using (CRwIf)
open import OCF.Lean.CRw using (I₁; leg; Σ₀)
open import OCF.Lean.CRwFold I₁ using (Σ⁺)
open import OCF.Lean.ValCRel I₁ using (LeAt; module Rel; module L)
open import OCF.Lean.ValCBase I₁ using (module Ac0)

infix 4 _≤₀_
_≤₀_ : Cd → Cd → Set
_≤₀_ = LeAt hz

open L hz using (≤-refl; ≤-trans; ⊞-mono; ≤⊞; ≤⊞ˡ; idInc)
```

## §1 `leg` 单调且不降

```agda
Σ₀≡ : ∀ f n → Σ₀ f n ≡ Σ⁺ f n
Σ₀≡ f zero = refl
Σ₀≡ f (suc n) = cong (λ z → z ⊞ f (suc n)) (Σ₀≡ f n)

Σ₀-ge : ∀ f n → f n ≤₀ Σ₀ f n
Σ₀-ge f n = subst₂ _≤₀_ refl (sym′ (Σ₀≡ f n)) (Ac0.Σ-ge hz f n)
  where sym′ : ∀ {a b : Cd} → a ≡ b → b ≡ a
        sym′ refl = refl

leg-mono : ∀ {c c′} → c ≤₀ c′ → leg c ≤₀ leg c′
leg-mono Rel.z≤ = Rel.z≤
leg-mono (Rel.s≤s p) = Rel.s≤s (leg-mono p)
leg-mono (Rel.≤s p) = Rel.≤s (leg-mono p)
leg-mono {hl f} {hl g} (Rel.l≤l σ i h) =
  Rel.l≤l σ i (λ n → subst₂ _≤₀_ (sym′ (Σ₀≡ _ n)) (sym′ (Σ₀≡ _ (σ n)))
    (Ac0.Σ-sub hz (λ k → leg (f k)) (λ k → leg (g k)) σ i (λ k → leg-mono (h k)) n))
  where sym′ : ∀ {a b : Cd} → a ≡ b → b ≡ a
        sym′ refl = refl
leg-mono {c} {hl g} (Rel.≤l n p) = Rel.≤l n (≤-trans (leg-mono p) (Σ₀-ge (λ k → leg (g k)) n))
leg-mono (Rel.≤Ω {κ = ()} _ _ _ _)
leg-mono (Rel.Ω≤Ω {κ = ()} _ _)

≤leg : ∀ c → c ≤₀ leg c
≤leg hz = Rel.z≤
≤leg (hs c) = Rel.s≤s (≤leg c)
≤leg (hl f) = Rel.l≤l (λ n → n) idInc (λ n → ≤-trans (≤leg (f n)) (Σ₀-ge (λ k → leg (f k)) n))
≤leg (hΩ () _)
```

## §2 回灌

```agda
sh : Cd → Cd → Cd
sh = CRwIf.sh₀ I₁

sh-mono : ∀ {B B′ c c′} → B ≤₀ B′ → c ≤₀ c′ → sh B c ≤₀ sh B′ c′
sh-mono p q = ⊞-mono p (leg-mono q)

sh-infl : ∀ B c → (c ≤₀ sh B c) × (B ≤₀ sh B c)
sh-infl B c = ≤-trans (≤leg c) (≤⊞ˡ B (leg c)) , ≤⊞ B (leg c)
```

## §3 `sh-not-mono≤` 的那一对在这里不相关

```agda
l11 one : Cd
l11 = hl (λ _ → hs hz)
one = hs hz

l11-unrelated : ¬ (l11 ≤₀ one)
l11-unrelated (Rel.≤s ())
```

## 结论 (按档)

- **[定理]** `leg-mono`, `≤leg`, `sh-mono` (回灌对世界与坐标单调, 第 0 层的 `LeAt hz`), `sh-infl` (不降), `l11-unrelated`.
- **[判断]** 由此, 跨底折叠在 ValC 式关系下的障碍不在回灌本身, 而在本身/拷贝的区分与世界的移动 (后者本篇没有测).
