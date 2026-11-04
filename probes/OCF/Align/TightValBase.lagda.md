# 紧界树比值 (一): 类 `C`, 占位封顶的底座

> [TightVal](TightVal.lagda.md) 的底座. 对象是 [OmegaSqBase](OmegaSqBase.lagda.md) 的紧界折叠 `ψᵉ′`: 第 0, 1 层指数的后继是真帧, 第 $\ge2$ 层指数的后继是占位 $0$.
>
> 本文只有两样东西, 都不读记号:
>
> 1. **`Cp B x`: "`x` 的任何证书计值都 $\preccurlyeq B$".** 证书只用 `Goodᴺ`. `Cp` 对 `lim` 与 `ĉᴸ` 逐点封闭, 闭包的链点是什么都无所谓.
> 2. **类 `C`: 第 $i$ 层的树, 只由 $\Omega_i$, $0$, 任意后继, `lim`, `limᵢ`, `ŝ`, `ĉᴸ` 拼成, 没有裸的 `up`.** `cloE`: 只要栈在一切目标上落进 `C`, `ψᵉ′` 对**任意**指数 (任意层) 的输出就落进 `C`. 这是占位封顶的结构原因: 高层目标上折叠的输出, 除了 $\Omega_i$ 那个节点, 不暴露低层子树.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 不引用记号的定义: `ψᵉ′` 所在的模块导入闭包里有记号, 定义本身不读.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TightValBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; coeˢ; toZ; Ωˢ; addˢ; _+ˢ_)
open import OCF.Align.NotFree using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; outsᴺ)
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans)
open import OCF.Align.OmegaExpBase using (Stk; ψˢ; ∅ˢ; _▹Ω̂)
open import OCF.Align.OmegaSqBase using (ψᵉ′; repᴷ; _▹[_]_)
```

## §1 `Cp`

```agda
Cp : Ordᶜ zero → Z → Set
Cp B x = (G : Goodᴺ x) → _≼_ {zero} {zero} (forceᴺ x G) B

cp-zero : ∀ {B} → Cp B Z.zero
cp-zero gz = z≼

cp-lim : ∀ {B} {f : ℕ → Z} → (∀ n → Cp B (f n)) → Cp B (Z.lim f)
cp-lim h (gl G st) = l≼ (λ n → h n (G n))

outs-≼ : ∀ {B O₀ : Ordᶜ zero} {O : ℕ → Ordᶜ zero} → O₀ ≼ B → (∀ k → O k ≼ B) → ∀ n → outsᴺ O₀ O n ≼ B
outs-≼ h₀ h zero    = h₀
outs-≼ h₀ h (suc k) = h k

cp-ĉ : ∀ {B c t₀ o₀} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z} →
       Cp B o₀ → (∀ η e → Cp B (o η e)) → Cp B (ĉᴸ c t₀ g o₀ o)
cp-ĉ h₀ h (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = l≼ (outs-≼ (h₀ Go₀) (λ k → h _ _ (Go k)))

s≼-irrefl : (a : Ordᶜ zero) → suc a ≼ a → ⊥
s≼-irrefl zero ()
s≼-irrefl (suc a) (s≼s p) = s≼-irrefl a p
s≼-irrefl (lim f) (≼l n p) = s≼-irrefl (f n) (≼-trans {ℓ₂ = zero} (s≼s {ℓ₁ = zero} {ℓ₂ = zero} (≼l n (≼-refl (f n)))) p)
s≼-irrefl (limᵢ () f)
s≼-irrefl (up () x)
```

## §2 类 `C` 与它对 `addˢ`, `ψˢ`, `ψᵉ′` 的封闭

```agda
data C {i : Ordᴵ} : Ordˢ i → Set where
  cΩ : C (Ωˢ i)
  c0 : C Ord₊ˢ.zero
  cs : ∀ {a} → C (Ord₊ˢ.suc a)
  cl : ∀ {f : ℕ → Ordˢ i} → (∀ n → C (f n)) → C (Ord₊ˢ.lim f)
  ci : ∀ {j} {q : j <ᴵ i} {f : Uˢ j (<→◃ q) → Ordˢ i} → (∀ y → C (f y)) → C (Ord₊ˢ.limᵢ q f)
  cŝ : ∀ {c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ i} → C t₀ → (∀ η e → C (g η e)) → C (Ord₊ˢ.ŝ c t₀ g)
  cĉ : ∀ {c t₀ g o₀} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ i} → C o₀ → (∀ η e → C (o η e)) → C (Ord₊ˢ.ĉᴸ c t₀ g o₀ o)

cAdd : ∀ {k i} {a : Ordˢ i} (σ : Simᴵ k i) → C a → (b : Ordˢ k) → C (addˢ a σ b)
cAdd σ h Ord₊ˢ.zero           = h
cAdd σ h (Ord₊ˢ.suc b)        = cs
cAdd σ h (Ord₊ˢ.lim f)        = cl (λ n → cAdd σ h (f n))
cAdd σ h (Ord₊ˢ.limᵢ q f)     = ci (λ y → cAdd σ h (f (coeˢ (<→◃ (σ q)) (<→◃ q) y)))
cAdd σ h (Ord₊ˢ.up zero x)    = cAdd (λ q → σ (suc q)) h x
cAdd σ h (Ord₊ˢ.up (self n) x) = cAdd (λ q → σ (lim n q)) h x
cAdd {k = zero}    σ h (Ord₊ˢ.ŝ c t₀ g) = cĉ (cAdd σ h t₀) (λ η e → cAdd σ h (g η e))
cAdd {k = suc _}   σ h (Ord₊ˢ.ŝ c t₀ g) = cŝ (cAdd σ h t₀) (λ η e → cAdd σ h (g η e))
cAdd {k = lim _ _} σ h (Ord₊ˢ.ŝ c t₀ g) = cŝ (cAdd σ h t₀) (λ η e → cAdd σ h (g η e))
cAdd σ h (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) = cĉ (cAdd σ h o₀) (λ η e → cAdd σ h (o η e))

cIter : ∀ {i} {a : Ordˢ i} → C a → ∀ m → C (iter (a +ˢ_) Ord₊ˢ.zero m)
cIter h zero    = c0
cIter h (suc m) = cAdd (λ q → q) h _

CStk : Stk → Set
CStk S = ∀ {i ℓ} (z : zero <ᴵ ℓ) (p : i <ᴵ ℓ) → C (S z p)

cloS : ∀ (S : Stk) → CStk S → ∀ {i k ℓ} (z : zero <ᴵ ℓ) (p : i <ᴵ ℓ) (σ : Simᴵ k ℓ) (x : Ordˢ k) → C (ψˢ S z p σ x)
cloS S hS z p σ Ord₊ˢ.zero    = hS z p
cloS S hS z p σ (Ord₊ˢ.suc a) = cl (cIter (cloS S hS z p σ a))
cloS S hS z p σ (Ord₊ˢ.lim f) = cl (λ m → cloS S hS z p σ (f m))
cloS S hS z p σ (Ord₊ˢ.limᵢ {i = j} q f) with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = ci (λ y → cloS S hS z p σ _)
... | injᵇ _ = cl (λ m → cloS S hS z p σ _)
... | injᶜ _ = cl (λ m → cloS S hS z p σ _)
cloS S hS z p σ (Ord₊ˢ.up zero x)     = cloS S hS z p (λ q → σ (suc q)) x
cloS S hS z p σ (Ord₊ˢ.up (self m) x) = cloS S hS z p (λ q → σ (lim m q)) x
cloS S hS {k = zero}    z p σ (Ord₊ˢ.ŝ c t₀ g) = cĉ (cloS S hS z p σ t₀) (λ η e → cloS S hS z p σ (g η e))
cloS S hS {k = suc _}   z p σ (Ord₊ˢ.ŝ c t₀ g) = cŝ (cloS S hS z p σ t₀) (λ η e → cloS S hS z p σ (g η e))
cloS S hS {k = lim _ _} z p σ (Ord₊ˢ.ŝ c t₀ g) = cŝ (cloS S hS z p σ t₀) (λ η e → cloS S hS z p σ (g η e))
cloS S hS z p σ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) = cĉ (cloS S hS z p σ o₀) (λ η e → cloS S hS z p σ (o η e))

cloΩ̂ : ∀ (S : Stk) → CStk S → CStk (S ▹Ω̂)
cloΩ̂ S hS z p = cŝ (cloS S hS _ _ _ _) (λ η e → cloS S hS _ _ _ _)

cloE : ∀ (S : Stk) → CStk S → ∀ {i k ℓ} (z : zero <ᴵ ℓ) (p : i <ᴵ ℓ) (σ : Simᴵ k ℓ) (x : Ordˢ k) → C (ψᵉ′ S z p σ x)
cRep : ∀ (S : Stk) → CStk S → ∀ {k} (s : ∀ {ℓ} → zero <ᴵ ℓ → Simᴵ k ℓ) (a : Ordˢ k) m → CStk (repᴷ S s a m)

cloE S hS z p σ Ord₊ˢ.zero = cloΩ̂ S hS z p
cloE S hS {k = zero}        z p σ (Ord₊ˢ.suc a) = cl (λ m → cRep S hS _ a m z p)
cloE S hS {k = suc zero}    z p σ (Ord₊ˢ.suc a) = cl (λ m → cRep S hS _ a m z p)
cloE S hS {k = suc (suc _)}   z p σ (Ord₊ˢ.suc a) = c0
cloE S hS {k = suc (lim _ _)} z p σ (Ord₊ˢ.suc a) = c0
cloE S hS {k = lim _ _}       z p σ (Ord₊ˢ.suc a) = c0
cloE S hS z p σ (Ord₊ˢ.lim f) = cl (λ m → cloE S hS z p σ (f m))
cloE S hS z p σ (Ord₊ˢ.limᵢ {i = j} q f) with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = ci (λ y → cloE S hS z p σ _)
... | injᵇ _ = cl (λ m → cloE S hS z p σ _)
... | injᶜ _ = cl (λ m → cloE S hS z p σ _)
cloE S hS z p σ (Ord₊ˢ.up zero x)     = cloE S hS z p (λ q → σ (suc q)) x
cloE S hS z p σ (Ord₊ˢ.up (self m) x) = cloE S hS z p (λ q → σ (lim m q)) x
cloE S hS {k = zero}    z p σ (Ord₊ˢ.ŝ c t₀ g) = cĉ (cloE S hS z p σ t₀) (λ η e → cloE S hS z p σ (g η e))
cloE S hS {k = suc _}   z p σ (Ord₊ˢ.ŝ c t₀ g) = cŝ (cloE S hS z p σ t₀) (λ η e → cloE S hS z p σ (g η e))
cloE S hS {k = lim _ _} z p σ (Ord₊ˢ.ŝ c t₀ g) = cŝ (cloE S hS z p σ t₀) (λ η e → cloE S hS z p σ (g η e))
cloE S hS z p σ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) = cĉ (cloE S hS z p σ o₀) (λ η e → cloE S hS z p σ (o η e))

cRep S hS s a zero    z p = hS z p
cRep S hS s a (suc m) z p = cloE (repᴷ S s a m) (cRep S hS s a m) z p (s z) a

c∅ : CStk ∅ˢ
c∅ z p = cΩ
```

**读法.** 三处 `cl (λ m → … _)`, `ci (λ y → … _)` 的 `_` 由目标解出, 就是定义里的分支输入. `cloE` 对指数的层号与形状没有任何要求: 它只看输出的外形. 第 $\ge2$ 层后继的占位 $0$ 落进 `c0`, 真帧的 `repᴷ` 落进 `cl`.
