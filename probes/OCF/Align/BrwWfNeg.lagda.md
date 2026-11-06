# 沿 View 递归 (八): 为什么度量不能是值

> 不含记号. 入口 [BrwWf](BrwWf.lagda.md). 两条编译过的否定, 说明度量为什么取直接子树 (第 0 层、高度) 与秩 (第 1 层), 而不取值的序:
>
> 1. `no-strict₀`: 第 0 层 View 的部分**不**在值上严格下降. 反例 `nl (λ _ → n0)`: 值 $\lim(0,0,\dots)$, 它的第 0 个部分值 $0$, 而 $0+1\not\le\lim(0,0,\dots)$. 这是 [BrwViewNeg](BrwViewNeg.lagda.md) (`strict→LPO`, 极限步进不严格) 在部分关系上的样子. 所以 "值严格下降" (`asuc (val o′) ≤ val o`) 不能当度量.
> 2. `no-wf-⊏ᵥ`: "低于整体的某个直接子树, 按值" (`a ⊏ᵥ b`: $b$ 有直接子树 $b'$ 使 $a\le b'$) **不良基**, 即使只看合法的树: $x=\lim(\omega,\omega,\dots)$ 合法 (`Lg-x`), 而 $x\le\omega$, 所以 $x ⊏ᵥ x$. 所以 "部分的值 $\le$ 整体的值的直接子树" 这种度量不行, 要把值的序换成秩的比较 ([BrwWfRank](BrwWfRank.lagda.md)), 它在极限处不把 $\lim(\omega,\omega,\dots)$ 与 $\omega$ 等同.
>
> 范围: 两条都只否定度量的一种取法, 不否定良基本身 (良基在 [BrwWfZero](BrwWfZero.lagda.md), [BrwWfOne](BrwWfOne.lagda.md) 里证了).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwWfNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤lim⁻)
open import OCF.Align.SumOneTree using (D; n0; nl; pt)
open import OCF.Align.BrwWfDef using (p-l)
open import OCF.Align.BrwWfZero using (_◁₀_; vo₀; SubA; sa-l)
```

## §1 值上不严格下降

```agda
z∞ : D azero azero
z∞ = nl (λ _ → n0)

pt0 : ∀ n → pt {azero} azero (λ _ → n0) n ≡ azero
pt0 zero = refl
pt0 (suc n) = pt0 n

no1 : ¬ (asuc azero ≤ alim (pt {azero} azero (λ _ → n0)))
no1 h with ≤lim⁻ h
... | n , q = bad (subst (λ a → asuc azero ≤ a) (pt0 n) q)
  where
  bad : ¬ (asuc azero ≤ azero)
  bad ()

no-strict₀ : ¬ (∀ {o o′} → _◁₀_ azero o′ o → asuc (vo₀ azero o′) ≤ vo₀ azero o)
no-strict₀ h = no1 (h {tt , z∞ , tt} (p-l 0))
```

## §2 "按值低于直接子树" 不良基

```agda
infix 4 _⊏ᵥ_
_⊏ᵥ_ : A → A → Set
a ⊏ᵥ b = Σ A (λ b′ → SubA b′ b × (a ≤ b′))

fin : ℕ → A
fin zero = azero
fin (suc n) = asuc (fin n)

ω x : A
ω = alim fin
x = alim (λ _ → ω)

Lg-fin : ∀ n → Lg (fin n)
Lg-fin zero = tt
Lg-fin (suc n) = Lg-fin n

Lg-x : Lg x
Lg-x = (λ n → C.self) , (λ n → (λ m → C.suc C.self) , Lg-fin)

x⊏x : x ⊏ᵥ x
x⊏x = ω , sa-l 0 , l≤ (λ n → ≤-refl ω)

no-acc : ¬ Acc _⊏ᵥ_ x
no-acc (acc rs) = no-acc (rs x⊏x)

no-wf-⊏ᵥ : ¬ WellFounded _⊏ᵥ_
no-wf-⊏ᵥ wf = no-acc (wf x)
```
