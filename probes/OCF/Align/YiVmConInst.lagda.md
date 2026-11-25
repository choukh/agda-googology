# YiVmCon：`Crux` 在四对结构不可比的层号上

**验收文件，档位：编译定理。** `Crux` 的四个闭实例：(ω, ω⁺)、(ω+1, ω⁺+1)、(ω·2, (1+ω)·2 的左加写法)、(`D.γ 1`, 它的基本列平移一位的写法)，都经 `YiVmConExact.Cruxᵖ`。
每一对的结论层号都不是结构可比的 (`not-A` 到 `not-D`, 经 `no-⊑-suc`: 顶值不增且两顶不 `≅ᴵ` 就没有 `⊑ᴵ`)，所以 `Ψ⁰-mono` 用不上。C 与 D 在左极限之下用到保值 (`sˣ` 的值相等，或结构步进 `⊑→≼ˣ`)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiVmConInst where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (proj₂)
open import Relation.Nullary using (¬_)
import OCF.Align.Level as L
open L using (Ordᴵ; Ordᶜ; _≅ᴵ_; _⊑ᴵ_; HS; toLevel; ωᶜ; ωᶜ-HS; natᶜ; natᶜ-HS)
open import OCF.Align.Value using (_≼_; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ω⁺; ω≈ω⁺)
open import OCF.Align.YiVmConExact
open import OCF.Align.YiBtValBT using (module D)
```

## 1 结构不可比的判据

```agda
no-⊑-suc : ∀ {a b} → V b ≼ V a → ¬ (a ≅ᴵ b) → ¬ (L.suc a ⊑ᴵ L.suc b)
no-⊑-suc ba ne (L.s⊑ e L.zero) = ne e
no-⊑-suc {a} ba ne (L.s⊑ e (L.suc q)) = irr (V a) (≼-trans (≼-trans (s≼s (V-≅ e)) (V-< q)) ba)

vlev : ∀ {x y} (hx : HS x) (hy : HS y) → y ≼ x → V (toLevel y hy) ≼ V (toLevel x hx)
vlev {x} {y} hx hy d = ≼-trans (Vt y hy) (≼-trans d (tV x hx))

ω⁺-HS : HS ω⁺
ω⁺-HS = L.hl (λ n → natᶜ-HS (suc n)) (λ n h → L.≺s h)

ω⁺≼ω : ω⁺ ≼ ωᶜ
ω⁺≼ω = proj₂ ω≈ω⁺

ω≇ᴵ : ∀ h h′ → ¬ (toLevel ωᶜ h ≅ᴵ toLevel ω⁺ h′)
ω≇ᴵ h h′ (L.l≅ k) with k 0
... | ()
```

## 2 A：(ω, ω⁺)；B：(ω+1, ω⁺+1)

A 的嵌入：ω 的前驱 n 映到 ω⁺ 里的 n (`wˣ`, 自反)；左极限的各项保值，自动一致。B 在 A 外再套一层后继 (`sᵖ`)，顶 ω 映到顶 ω⁺，这一步不保值也不需要保值。

```agda
dA : ωᶜ ≼ˣ ω⁺
dA = lˣ (λ n → ≼lˣ n (wˣ (reflˣ (natᶜ n))))

crux-A : L.ψ⁰ (L.Ω (L.suc (toLevel ωᶜ ωᶜ-HS))) ≼ L.ψ⁰ (L.Ω (L.suc (toLevel ω⁺ ω⁺-HS)))
crux-A = Cruxᵖ ωᶜ ωᶜ-HS ω⁺ ω⁺-HS (ˣ→ᵖ dA)

not-A : ¬ (L.suc (toLevel ωᶜ ωᶜ-HS) ⊑ᴵ L.suc (toLevel ω⁺ ω⁺-HS))
not-A = no-⊑-suc (vlev ωᶜ-HS ω⁺-HS ω⁺≼ω) (ω≇ᴵ ωᶜ-HS ω⁺-HS)

crux-B : L.ψ⁰ (L.Ω (L.suc (toLevel (L.suc ωᶜ) (L.hs ωᶜ-HS)))) ≼ L.ψ⁰ (L.Ω (L.suc (toLevel (L.suc ω⁺) (L.hs ω⁺-HS))))
crux-B = Cruxᵖ (L.suc ωᶜ) (L.hs ωᶜ-HS) (L.suc ω⁺) (L.hs ω⁺-HS) (sᵖ (ˣ→ᵖ dA))

not-B : ¬ (L.suc (toLevel (L.suc ωᶜ) (L.hs ωᶜ-HS)) ⊑ᴵ L.suc (toLevel (L.suc ω⁺) (L.hs ω⁺-HS)))
not-B = no-⊑-suc (vlev (L.hs ωᶜ-HS) (L.hs ω⁺-HS) (s≼s ω⁺≼ω)) (λ { (L.s≅ e) → ω≇ᴵ ωᶜ-HS ω⁺-HS e })
```

## 3 C：ω·2 对 (1+ω)·2

`ω2` 的第 n 项是 ω+n，`ω⁺2` 的第 n 项是 ω⁺+n (1+ω·2 按左加展开)。各项的嵌入 ω+n ↦ ω⁺+n 在每个后继处保值 (`⊕≼` 给顶的反向不等式)，所以 `lᵖ` 拼得起来。

```agda
_⊕_ : Ordᶜ L.zero → ℕ → Ordᶜ L.zero
a ⊕ zero  = a
a ⊕ suc n = L.suc (a ⊕ n)

⊕-HS : ∀ {a} → HS a → ∀ n → HS (a ⊕ n)
⊕-HS h zero    = h
⊕-HS h (suc n) = L.hs (⊕-HS h n)

ω2 ω⁺2 : Ordᶜ L.zero
ω2  = L.lim (λ n → ωᶜ ⊕ n)
ω⁺2 = L.lim (λ n → ω⁺ ⊕ n)

ω2-HS : HS ω2
ω2-HS = L.hl (⊕-HS ωᶜ-HS) (λ n h → L.≺s h)

ω⁺2-HS : HS ω⁺2
ω⁺2-HS = L.hl (⊕-HS ω⁺-HS) (λ n h → L.≺s h)

⊕≼ : ∀ n → ω⁺ ⊕ n ≼ ωᶜ ⊕ n
⊕≼ zero    = ω⁺≼ω
⊕≼ (suc n) = s≼s (⊕≼ n)

⊕ˣ : ∀ n → ωᶜ ⊕ n ≼ˣ ω⁺ ⊕ n
⊕ˣ zero    = dA
⊕ˣ (suc n) = sˣ (⊕ˣ n) (⊕≼ n)

crux-C : L.ψ⁰ (L.Ω (L.suc (toLevel ω2 ω2-HS))) ≼ L.ψ⁰ (L.Ω (L.suc (toLevel ω⁺2 ω⁺2-HS)))
crux-C = Cruxᵖ ω2 ω2-HS ω⁺2 ω⁺2-HS (lᵖ (λ n → ≼lˣ n (⊕ˣ n)))

not-C : ¬ (L.suc (toLevel ω2 ω2-HS) ⊑ᴵ L.suc (toLevel ω⁺2 ω⁺2-HS))
not-C = no-⊑-suc (vlev ω2-HS ω⁺2-HS (l≼ (λ n → ≼l n (⊕≼ n)))) (λ { (L.l≅ k) → ω≇ᴵ ωᶜ-HS ω⁺-HS (k 0) })
```

## 4 D：`D.γ 1` 对它的平移写法

`D.γ 1` 是 lim (ψ⁰ (G n))；`γ₁′` 取 lim (ψ⁰ (G (n+1)))，值相同。各项的嵌入来自 `D.cert 1` 的结构步进 (`⊑→≼ˣ`)，结构步进本来就保值。两者的层号不 `≅ᴵ`：第 0 项的第 0 项是 0 对 1。

```agda
γ₁′ : Ordᶜ L.zero
γ₁′ = L.lim (λ n → L.ψ⁰ (D.G (suc n)))

γ₁′-HS : HS γ₁′
γ₁′-HS = L.hl (λ n → L.hl₁ (D.cert 1) (suc n)) (λ n → L.hl₂ (D.cert 1) (suc n))

crux-D : L.ψ⁰ (L.Ω (L.suc (toLevel (D.γ 1) (D.cert 1)))) ≼ L.ψ⁰ (L.Ω (L.suc (toLevel γ₁′ γ₁′-HS)))
crux-D = Cruxᵖ (D.γ 1) (D.cert 1) γ₁′ γ₁′-HS
  (lᵖ (λ n → ≼lˣ n (⊑→≼ˣ (L.ψ⁰ (D.G n)) (L.hl₂ (D.cert 1) n))))

γ≇ : ∀ h h′ → ¬ (toLevel (D.γ 1) h ≅ᴵ toLevel γ₁′ h′)
γ≇ h h′ (L.l≅ k) with k 0
... | L.l≅ k′ with k′ 0
...   | ()

not-D : ¬ (L.suc (toLevel (D.γ 1) (D.cert 1)) ⊑ᴵ L.suc (toLevel γ₁′ γ₁′-HS))
not-D = no-⊑-suc (vlev (D.cert 1) γ₁′-HS (l≼ (λ n → ≼l (suc n) (≼-refl _)))) (γ≇ (D.cert 1) γ₁′-HS)
```
