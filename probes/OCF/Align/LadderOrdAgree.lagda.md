# 序数高度: 与 `HS∞`, `HS₂` 的值一致

> **判决: HOLDS (编译过, 无条件).** 结论写在 [LadderOrd](LadderOrd.lagda.md). 仿 [LadderInfAgree](LadderInfAgree.lagda.md). 这里只有定理, 没有假设.
>
> 1. **`agree₂`, `fgh₂`:** `HS₂` 的每个高度 $m$ (有限, $\omega$, $\omega+n$), 一切 $\alpha$: 那边证书的计值与码 `ω·ᶜ 1` 上位置 `e₂ m` 的证书计值 $\cong$; FGH 逐点相等.
> 2. **`agree∞`, `fgh∞`:** `HS∞` 与码 `ωᶜ` 同样. 包括 $\infty$: `HS∞` 的 `∞` 对应 `ωᶜ` 的顶.
> 3. **`agree-NF`, `fgh-NF`:** 接上已有的 `agree-fin`: 原来的 `LadderNFMain` 与码 `ωᶜ` 的有限高度 $\cong$. **`anchor-ω`, `fgh-ω`:** 接上已有的 `forceᴺ-∞0`: `GᴺTω` (已验收过标签的 $\psi_0(\Omega_{\psi_1(1)})$) 与码 `ωᶜ` 的顶 $\cong$.
>
> 4. **`agree²`, `fgh²`:** 同一段放进码 `ω²ᶜ`, 值同样不变.
> 5. **`cross₂`, `cross²`:** `HS₂` 的每一个第 0 项都严格低于 `ω·ᶜ 1` 的顶与 `ω²ᶜ` 的顶. 字面的 $\prec$.
>
> 所以 `HB` 的值在 `HS∞`, `HS₂` 已有的范围内没有变, 新的高度确实更高.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderOrdAgree where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Free.Level
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Eq using (z≅; toZ-≅)
open import OCF.Free.Floor using (Ev)
open import OCF.Free.Force using (forceᴺ; forceᴺ-≅)
open import OCF.Free.Tree using (Fl)
import OCF.Align.LadderNFMain as NM
import OCF.Align.LadderMonoMain as MM
open import OCF.Align.LadderInfAgree using (agree-fin; forceᴺ-∞0)
open import OCF.Align.LadderInfTop using (HS∞; fin; ∞)
open import OCF.Align.LadderInfTop2 using (HS₂; top) renaming (fin to fin₂)
import OCF.Align.LadderInfMain
import OCF.Align.LadderOrdMain
import OCF.Align.LadderOrdGrow
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode
open import OCF.Align.LadderOrdInst
open import OCF.Align.LadderOrdStrict3 (HB M₂) using (≺-≅ˡ)
module I₂ = OCF.Align.LadderInfMain HS₂
module I∞ = OCF.Align.LadderInfMain HS∞
module G₂ = OCF.Align.LadderOrdMain (HB M₂)
module Gω = OCF.Align.LadderOrdMain (HB ωᶜ)

agree₂ : ∀ m α {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → forceᴺ _ (I₂.GᴺTᵠ m α ev z) ≅ forceᴺ _ (G₂.GᴺTᵠ (e₂ m) α ev z)
agree₂ m α ev z = forceᴺ-≅ (toZ-≅ (bridge₂ m α α (≅ᴵ-refl α) ev z ev z z≅)) _ _

fgh₂ : ∀ m α {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) n → FGH (forceᴺ _ (I₂.GᴺTᵠ m α ev z)) n ≡ FGH (forceᴺ _ (G₂.GᴺTᵠ (e₂ m) α ev z)) n
fgh₂ m α ev z = FGH-≅ (agree₂ m α ev z)

agree∞ : ∀ m α {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → forceᴺ _ (I∞.GᴺTᵠ m α ev z) ≅ forceᴺ _ (Gω.GᴺTᵠ (e∞ m) α ev z)
agree∞ m α ev z = forceᴺ-≅ (toZ-≅ (bridge∞ m α α (≅ᴵ-refl α) ev z ev z z≅)) _ _

fgh∞ : ∀ m α {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) n → FGH (forceᴺ _ (I∞.GᴺTᵠ m α ev z)) n ≡ FGH (forceᴺ _ (Gω.GᴺTᵠ (e∞ m) α ev z)) n
fgh∞ m α ev z = FGH-≅ (agree∞ m α ev z)

agree-NF : ∀ m α {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → forceᴺ _ (NM.GᴺTᵠ m α ev z) ≅ forceᴺ _ (Gω.GᴺTᵠ (e∞ (fin m)) α ev z)
agree-NF m α ev z = ≅-trans (agree-fin m α ev z) (agree∞ (fin m) α ev z)

fgh-NF : ∀ m α {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) n → FGH (forceᴺ _ (NM.GᴺTᵠ m α ev z)) n ≡ FGH (forceᴺ _ (Gω.GᴺTᵠ (e∞ (fin m)) α ev z)) n
fgh-NF m α ev z = FGH-≅ (agree-NF m α ev z)

anchor-ω : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → forceᴺ _ (MM.GᴺTω ev z) ≅ forceᴺ _ (Gω.GᴺTᵠ end zero ev z)
anchor-ω ev z = ≅-trans (forceᴺ-∞0 ev z) (agree∞ ∞ zero ev z)

fgh-ω : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) n → FGH (forceᴺ _ (MM.GᴺTω ev z)) n ≡ FGH (forceᴺ _ (Gω.GᴺTᵠ end zero ev z)) n
fgh-ω ev z = FGH-≅ (anchor-ω ev z)
```

## §2 第一个跨过去的高度确实更高

`HS₂` 的每一行第 0 项都严格低于码 `ω·ᶜ 1` 的顶 (`cross₂`), 也严格低于码 `ω²ᶜ` 的顶 (`cross²`). 用 `grow` 与 §1.

```agda
module Gr₂ = OCF.Align.LadderOrdGrow (HB M₂)
module Gr² = OCF.Align.LadderOrdGrow (HB ω²ᶜ)
module G² = OCF.Align.LadderOrdMain (HB ω²ᶜ)

cross₂ : ∀ m {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → forceᴺ _ (I₂.GᴺTᵠ m zero ev z) ≺ forceᴺ _ (G₂.GᴺTᵠ end zero ev z)
cross₂ m ev z = ≺-≅ˡ (agree₂ m zero ev z) (Gr₂.grow (e₂<end m) ev z)
  where
  e₂<end : ∀ m → e₂ m <ᴾ end
  e₂<end (fin₂ n) = tt
  e₂<end (top n) = tt

agree² : ∀ m α {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → forceᴺ _ (I₂.GᴺTᵠ m α ev z) ≅ forceᴺ _ (G².GᴺTᵠ (e² m) α ev z)
agree² m α ev z = forceᴺ-≅ (toZ-≅ (bridge² m α α (≅ᴵ-refl α) ev z ev z z≅)) _ _

fgh² : ∀ m α {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) n → FGH (forceᴺ _ (I₂.GᴺTᵠ m α ev z)) n ≡ FGH (forceᴺ _ (G².GᴺTᵠ (e² m) α ev z)) n
fgh² m α ev z = FGH-≅ (agree² m α ev z)

cross² : ∀ m {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → forceᴺ _ (I₂.GᴺTᵠ m zero ev z) ≺ forceᴺ _ (G².GᴺTᵠ end zero ev z)
cross² m ev z = ≺-≅ˡ (agree² m zero ev z) (Gr².grow (e²<end m) ev z)
  where
  e²<end : ∀ m → e² m <ᴾ end
  e²<end (fin₂ n) = tt
  e²<end (top zero) = tt
  e²<end (top (suc n)) = tt
```
