# 无记号主线 (二): 层号上的小引理

> **`Mlev`, `≅ᴵ→⊑ᴵ`, `⊑ᴵ-≅ˡ`, `σ⊥`, `one⁰` 等.** 这几个定义原来分散在带记号的文件里, 它们本身不读记号: 主线对这些文件的依赖只有这些字面定义.
> 脚本从 [Symbolic](../Align/Symbolic.lagda.md)、[UniformS](../Align/UniformS.lagda.md)、[OmegaExpBase](../Align/OmegaExpBase.lagda.md)、[Stage2Label](../Align/Stage2Label.lagda.md) 切出 (定义级切片), 代码行逐字, 讲解见原文件. 本文件的导入闭包不含记号或标签模块 (`probes/Survey/scripts/importclosure.py`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Aux where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Free.Level
```

```agda

```

## §4 逐步现造的公共层号与上下文链

```agda
Fs : Ordᴵ → Ordᴵ → ℕ → Ordᴵ
Fs c η zero    = c
Fs c η (suc _) = η

Fst : ∀ {c η} → c ⊑ᴵ η → ∀ n → Fs c η n ⊑ᴵ Fs c η (suc n)
Fst e zero    = e
Fst e (suc n) = ⊑ᴵ-refl

Mlev : (c η : Ordᴵ) → c ⊑ᴵ η → Ordᴵ
Mlev c η e = lim (Fs c η) (Fst e)
```

## §12 结论与边界

```agda

```

## §0 层号的种类与几条 $\sqsubseteq^\mathsf I$ 小引理

```agda
kd : Ordᴵ → Bool
kd zero      = true
kd (suc _)   = false
kd (lim _ _) = false

kd-≅ : ∀ {a b} → a ≅ᴵ b → kd a ≡ kd b
kd-≅ z≅     = refl
kd-≅ (s≅ _) = refl
kd-≅ (l≅ _) = refl

≅ᴵ→⊑ᴵ : ∀ {a b} → a ≅ᴵ b → a ⊑ᴵ b
≅ᴵ→⊑ᴵ z≅     = z⊑
≅ᴵ→⊑ᴵ (s≅ e) = s⊑ e zero
≅ᴵ→⊑ᴵ (l≅ h) = l⊑ (λ n → ⊑ᴵ-trans (≅ᴵ→⊑ᴵ (h n)) (Sim→⊑ᴵ (lim n)))

⊑ᴵ-≅ˡ : ∀ {a a′ b} → a ≅ᴵ a′ → a ⊑ᴵ b → a′ ⊑ᴵ b
⊑ᴵ-≅ˡ e h = ⊑ᴵ-trans (≅ᴵ→⊑ᴵ (≅ᴵ-sym e)) h

⊑ᴵ-≅ʳ : ∀ {a b b′} → a ⊑ᴵ b → b ≅ᴵ b′ → a ⊑ᴵ b′
⊑ᴵ-≅ʳ h e = ⊑ᴵ-trans h (≅ᴵ→⊑ᴵ e)
```

## §3 $\Omega$、加法、`toZ` 与两种栈的折叠

```agda
tf : true ≡ false → ⊥
tf ()
```

## §2 折叠

```agda
σ⊥ : ∀ {ℓ} → Simᴵ zero ℓ
σ⊥ ()
```

## §4 严格性引理

```agda
one⁰ two⁰ : Ordᶜ zero
one⁰ = suc zero
two⁰ = suc one⁰
```

## §13 结论与边界
