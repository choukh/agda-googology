# YiVmNeg：不读推导的 `VMᴸ` 推出 Markov 原则

**验收文件，档位：编译定理。** 否定的是 `VMᴸ` 的两种 "只依赖 (x, y)、不依赖推导" 的写法：前提换成 `¬ ¬ (x ≼ y)` (`VM¬¬ → MP`)，或换成无关参数 `.(x ≼ y)` (`VMⁱ → MPⁱ`)；前驱嵌入的同样两种写法更强，同样推出 (`embV¬¬→MP`, `embVⁱ→MPⁱ`)。探针严格 (`YiVmNegBase.SHS`)，探针族上的命题与 MP 等价 (`MP→fam`)。
不否定 `VMᴸ` 本身 (它的前提是带数据的推导)，也不否定 `EmbV`。前置引理在 `YiVmNegBase`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiVmNegIrr where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.Level
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≼-suc; ≼lim⁻; ⊑→≼; +-mono; 1≼ψ⁰)
open import OCF.Align.RR4MonoFragment using (irr)
open import OCF.Align.BTBOFullEmb using (PEmb; Ψ-emb)
open import OCF.Align.YiMonoEmb using (PEmb-⊑)
open import OCF.Align.YiVmNegBase
```

## 1 陈述

```agda
MP : Set
MP = ∀ (α : ℕ → Bool) → ¬ ¬ (Σ ℕ λ k → α k ≡ true) → Σ ℕ λ k → α k ≡ true

MPⁱ : Set
MPⁱ = ∀ (α : ℕ → Bool) → .(Σ ℕ λ k → α k ≡ true) → Σ ℕ λ k → α k ≡ true

VM¬¬ : Set
VM¬¬ = ∀ (x : Ordᶜ zero) (hx : HS x) (y : Ordᶜ zero) (hy : HS y) → ¬ ¬ (x ≼ y) →
  ψ⁰ (Ω (toLevel x hx)) ≼ ψ⁰ (Ω (toLevel y hy))

VMⁱ : Set
VMⁱ = ∀ (x : Ordᶜ zero) (hx : HS x) (y : Ordᶜ zero) (hy : HS y) → .(x ≼ y) →
  ψ⁰ (Ω (toLevel x hx)) ≼ ψ⁰ (Ω (toLevel y hy))

EmbV¬¬ : Set
EmbV¬¬ = ∀ (x : Ordᶜ zero) (hx : HS x) (y : Ordᶜ zero) (hy : HS y) → ¬ ¬ (x ≼ y) → PEmb (toLevel x hx) (toLevel y hy)

EmbVⁱ : Set
EmbVⁱ = ∀ (x : Ordᶜ zero) (hx : HS x) (y : Ordᶜ zero) (hy : HS y) → .(x ≼ y) → PEmb (toLevel x hx) (toLevel y hy)

⊥-irr : .⊥ → ⊥
⊥-irr ()

MP→MPⁱ : MP → MPⁱ
MP→MPⁱ mp α w = mp α (λ k → ⊥-irr (k w))
```

## 2 探针

x = ω+1，y = `Y α` (α 全假时值 ω，否则 ω·2)。x ≼ y 恰当 α 有真 (`der`, `der⁻`)。

```agda
xI : Ordᶜ zero
xI = suc ωᶜ

hxI : HS xI
hxI = hs hω

ω≼sω : ∀ k → ωᶜ ≼ sω k
ω≼sω zero    = ≼-refl ωᶜ
ω≼sω (suc k) = ≼-suc (ω≼sω k)

x≼hbT : ∀ b k → b ≡ true → xI ≼ hb b (suc k)
x≼hbT true k refl = s≼s (ω≼sω k)

der : ∀ α → (Σ ℕ λ k → α k ≡ true) → xI ≼ Y α
der α (k , ek) = ≼l (suc k) (x≼hbT (seen α (suc k)) k (seen-mono α k (seen-of α k ek)))

x⋠hbF : ∀ b n → b ≡ false → ¬ (xI ≼ hb b n)
x⋠hbF false n refl d = irr ωᶜ (≼-trans d (≼l n (≼-refl (natᶜ n))))

der⁻ : ∀ α → xI ≼ Y α → Σ ℕ λ k → α k ≡ true
der⁻ α d with ≼lim⁻ d
... | n , d′ with seen α n in st
...   | true  = seen→Σ α n st
...   | false = ⊥-elim (x⋠hbF false n refl d′)
```

## 3 否定

`sψ`：ψ⁰ 在后继处严格上升 (任意层)。`strictΩ`：ψ₀(Ω_ω)+1 ≼ ψ₀(Ω_{ω+1})，全靠归约。`key`：若 ψ₀(Ω_{ω+1}) ≼ ψ⁰(Ω_{B α})，则 α 有真；否则 ψ₀(Ω_{ω+1}) 落在某个 ψ₀(Ω_n) 之下，与 `irr` 矛盾。

```agda
sψ : ∀ {k} (a : Ordᶜ k) → suc (ψ⁰ a) ≼ ψ⁰ (suc a)
sψ a = ≼l 2 (+-mono (≼-refl (ψ⁰ a)) (1≼ψ⁰ a))

strictΩ : suc (ψ⁰ (Ω A)) ≼ ψ⁰ (Ω (suc A))
strictΩ = ≼l 1 (≼l 0 (≼l 2 (≼l 0 (sψ (Ω A)))))

small : ∀ b n (hh : HS (hb b n)) → b ≡ false → ψ⁰ (Ω (toLevel (hb b n) hh)) ≼ ψ⁰ (Ω A)
small false n hh refl = ⊑→≼ _ (Ψ⁰-mono (toLevel-⊑ hh hω (λ d → ≺l n d)))

key : ∀ α → ψ⁰ (Ω (toLevel xI hxI)) ≼ ψ⁰ (Ω (B α)) → Σ ℕ λ k → α k ≡ true
key α D with ≼lim⁻ (≼-trans strictΩ D)
... | n , d with seen α n in st
...   | true  = seen→Σ α n st
...   | false = ⊥-elim (irr (ψ⁰ (Ω A)) (≼-trans d (small false n _ refl)))

vm¬¬→MP : VM¬¬ → MP
vm¬¬→MP vm α nn = key α (vm xI hxI (Y α) (hY α) (λ k → nn (λ w → k (der α w))))

vmⁱ→MPⁱ : VMⁱ → MPⁱ
vmⁱ→MPⁱ vm α w = key α (vm xI hxI (Y α) (hY α) (der α w))

embV¬¬→MP : EmbV¬¬ → MP
embV¬¬→MP ev = vm¬¬→MP (λ x hx y hy nn → Ψ-emb (ev x hx y hy nn))

embVⁱ→MPⁱ : EmbVⁱ → MPⁱ
embVⁱ→MPⁱ ev = vmⁱ→MPⁱ (λ x hx y hy d → Ψ-emb (ev x hx y hy d))
```

## 4 前提的可满足性

有 MP 时探针族上的命题都成立 (`MP→fam`)：由双重否定的前提得 α 有真，于是 ω+1 的前驱结构可比地放进 `B α`。所以 `vm¬¬→MP` 在探针族上是等价。

```agda
Fam¬¬ : Set
Fam¬¬ = ∀ α → ¬ ¬ (xI ≼ Y α) → PEmb (toLevel xI hxI) (B α)

emb-wit : ∀ α → (Σ ℕ λ k → α k ≡ true) → PEmb (toLevel xI hxI) (B α)
emb-wit α (k , ek) = PEmb-⊑ (s⊑′ (≺ᴵ-respˡ (toLevel-ω hω) (ω≺B α k ek)))

MP→fam : MP → Fam¬¬
MP→fam mp α nn = emb-wit α (mp α (λ k → nn (λ d → k (der⁻ α d))))

fam→MP : Fam¬¬ → MP
fam→MP F α nn = key α (Ψ-emb (F α (λ k → nn (λ w → k (der α w)))))
```

前提是带数据的推导时 (即 `VMᴸ`、`EmbV` 的原写法)，探针族上的嵌入与不等式直接由推导给出 (`emb-rel`, `vm-rel`)：这里的否定不碰原写法。

```agda
emb-rel : ∀ α → xI ≼ Y α → PEmb (toLevel xI hxI) (B α)
emb-rel α d = emb-wit α (der⁻ α d)

vm-rel : ∀ α → xI ≼ Y α → ψ⁰ (Ω (toLevel xI hxI)) ≼ ψ⁰ (Ω (B α))
vm-rel α d = Ψ-emb (emb-rel α d)
```
