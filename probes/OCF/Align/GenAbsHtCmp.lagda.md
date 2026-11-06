# 规范形论证对树类型抽象 (六): 与 `MonoPortZero` 对照

> 不含记号. 入口 [GenAbs](GenAbs.lagda.md). 同样的参数下, [GenAbsHt](GenAbsHt.lagda.md) 的关系与 [MonoPortZero](MonoPortZero.lagda.md) 的关系定义性相等 (`Rl≡`, `refl`), 两边的 `cong0`, `chain` 互为对方类型的居民 (`cong0ᴺ`, `cong0ᴼ`, `chainᴺ`). 所以新文件的结论就是原来的结论.
>
> 本文件是对照, 导入 `MonoPortZero` (从而导入 `MonoPortBridge`); `GenAbsHt` 本身不导入它们.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
open import OCF.Align.HtFeedTree using (D₊; H; LgH; hz; _⊲[_]_; AccY)
module OCF.Align.GenAbsHtCmp
  (S : ∀ {Kd : A → H → Set} {V′ : ∀ {W k} → Kd W k → A → Set} {Z : Set} {W} → D₊ Kd V′ Z W → D₊ Kd V′ Z W)
  (Λ : H) (lΛ : LgH Λ) {W : A} (lW : Lg W) (hk : hz ⊲[ W ] Λ) (ac₀ : AccY hz) where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.HtFeedTree using (D; nl; sum)
import OCF.Align.HtFeedFold as Fold
import OCF.Align.MonoPortBridge as MB
import OCF.Align.MonoPortZero as MZ₀
import OCF.Align.GenAbsHt as GH₀
open import OCF.Align.GenAbsHtInst using (valᴴ)

module F = Fold S Λ lΛ
module MZ = MZ₀ S Λ lΛ lW hk ac₀
module GH = GH₀ S Λ lΛ lW hk ac₀

Rl≡ : ∀ {A₀ A₁ : MZ.Act} {V₁ V₂} (z : D hz V₁) (z′ : D hz V₂) → MZ.Rl A₀ A₁ z z′ ≡ GH.Rl A₀ A₁ z z′
Rl≡ z z′ = refl

-- 新的 cong0 有原来的类型
cong0ᴺ : ∀ {A₀ A₁ : MZ.Act} → MZ.HAᶜ A₀ A₀ → MZ.HAᶜ A₁ A₁ → MZ.HAᶜ A₀ A₁ →
         ∀ {W₀ W₀′} (z : D hz W₀) (z′ : D hz W₀′) → MB.val z ≤ MB.val z′ → MZ.Rl A₀ A₁ z z′
cong0ᴺ = GH.cong0

-- 原来的 cong0 有新的类型
cong0ᴼ : ∀ {A₀ A₁ : GH.Act} → GH.HAᶜ A₀ A₀ → GH.HAᶜ A₁ A₁ → GH.HAᶜ A₀ A₁ →
         ∀ {W₀ W₀′} (z : D hz W₀) (z′ : D hz W₀′) → valᴴ z ≤ valᴴ z′ → GH.Rl A₀ A₁ z z′
cong0ᴼ = MZ.cong0

-- 新的 chain 有原来的类型
chainᴺ : ∀ {A₀ A₁ : MZ.Act} (ha : MZ.HAᶜ A₀ A₀) (ha′ : MZ.HAᶜ A₁ A₁) (hx : MZ.HAᶜ A₀ A₁) (Y Y′ : F.St W) b b′ →
         b ≤ b′ → MZ.vY Y ≤ MZ.vY Y′ → sum b (nl (MZ.segs {A₀} {A₁} ha ha′ hx A₀ Y)) ≤ sum b′ (nl (MZ.segs {A₀} {A₁} ha ha′ hx A₁ Y′))
chainᴺ {A₀} {A₁} ha ha′ hx = GH.chain {A₀} {A₁} ha ha′ hx
```
