# BTBOVal 的底座: 翻译, 层号的遗忘, 累加放大

> 接 [BTBOVal](BTBOVal.lagda.md). 只导入 src 的 `OCF.BTBO` 和 probes 的 `Level`, `Value`. 本文件放定义和无条件的小引理.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. src 的 `OCF.BTBO` 选项相同 (`--safe --without-K --lossy-unification`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BTBOValBase where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import OCF.BTBO using (module Ord-Ord; module BoundedTrich)
module S = Ord-Ord
module B = BoundedTrich
open B using (Ordᴰ; cumsum; cumsum-mono) renaming (_+_ to _+ᴰ_)
open S using (iter; ordᴰ; ψⁿ; BTBO; zero; suc; lim; limᵢ)
open import OCF.Align.Level
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≼-suc; _≈ᵛ_; +-mono; ψ⁰-mono⁰; 1≼ψ⁰)
```

## §1 第 0 层的翻译

两个树族的第 0 层是不同的类型, 但构造子一一对应: 两边第 0 层都只有 `zero`, `suc`, `lim` (`limᵢ` 要 $i<0$, `up` 要 $k\triangleleft_1 0$, 都空). 翻译是逐构造子的, 没有任何信息损失.

```agda
tr₀ : S.Ord₀ → Ordᶜ zero
tr₀ zero        = zero
tr₀ (suc a)     = suc (tr₀ a)
tr₀ (lim f)     = lim (λ n → tr₀ (f n))
tr₀ (limᵢ () f)

FGH-tr₀ : ∀ (a : S.Ord₀) n → S.FGH a n ≡ FGH (tr₀ a) n
FGH-tr₀ zero        n = refl
FGH-tr₀ (suc a)     n = iter-ext (FGH-tr₀ a) n n
FGH-tr₀ (lim f)     n = FGH-tr₀ (f n) n
FGH-tr₀ (limᵢ () f) n
```

`FGH-tr₀` 说翻译不改大数: src 的 `FGH` 就是翻译后的 `FGH`.

## §2 层号的遗忘

`Ordᴰ` 的树读回第 0 层. `_+ᴰ_` 与 `_+_` 只差遗忘.

```agda
fd : Ordᴰ → Ordᶜ zero
fd B.zero      = zero
fd (B.suc a)   = suc (fd a)
fd (B.lim f _) = lim (λ n → fd (f n))

fd-+ : ∀ a b → fd (a +ᴰ b) ≼ fd a + fd b
fd-+ a B.zero      = ≼-refl (fd a)
fd-+ a (B.suc b)   = s≼s (fd-+ a b)
fd-+ a (B.lim f m) = l≼ (λ n → ≼l n (fd-+ a (f n)))
```

## §3 累加只放大

`cumsum` 的第 $n$ 项不小于原序列的第 $n$ 项, 所以 `ordᴰ x` 的值不小于 $x$, 对**一切**树, 不要任何前提. 这是下界一半在层号上的部分.

```agda
≼-+ᴰ : ∀ a b → fd b ≼ fd (a +ᴰ b)
≼-+ᴰ a B.zero      = z≼
≼-+ᴰ a (B.suc b)   = s≼s (≼-+ᴰ a b)
≼-+ᴰ a (B.lim f m) = l≼ (λ n → ≼l n (≼-+ᴰ a (f n)))

cumsum-≥ : ∀ (f : ℕ → Ordᴰ) n → fd (f n) ≼ fd (cumsum f n)
cumsum-≥ f zero    = ≼-refl (fd (f zero))
cumsum-≥ f (suc n) = ≼-suc (≼-+ᴰ (cumsum f n) (f (suc n)))

ordᴰ-≥ : ∀ (x : S.Ord₀) → tr₀ x ≼ fd (ordᴰ x)
ordᴰ-≥ zero        = z≼
ordᴰ-≥ (suc a)     = s≼s (ordᴰ-≥ a)
ordᴰ-≥ (lim f)     = l≼ (λ n → ≼l n (≼-trans (ordᴰ-≥ (f n)) (cumsum-≥ (ordᴰ ∘ f) n)))
ordᴰ-≥ (limᵢ () f)
```
