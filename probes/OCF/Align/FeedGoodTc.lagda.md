# 第二项的紧读法: `feedL u₀` 的 `Tc`, 由 `Tc-Lv₅` 搬来 (判决: HOLDS, 只到 $u_1$)

> 不含记号. 结论写在 [FeedGood](FeedGood.lagda.md). 读法 [GuardReadRd](GuardReadRd.lagda.md) 的 `Tc-Lv₅` 写在界为 1 的 `Lv₅` 上, `feedL u₀` 的界是 2. 这里两步:
>
> - `rd²`: 界 1 的读法改成界 2: 读到分支 1 的改成第一支 (第一支就是 `F 1`), 其余的分支 $a$ 都有 $2\sqsubseteq a$. **这一步比较 $\mathrm{pr}\,a$ 与 1, 公共上界是字面的 $\eta$ (`<ᴵ-dec`), 没有比较两个分支, 不碰壁垒.**
> - `Tc-≈`: `Tc` 沿 $\approx$ 搬运, 对一切层号.
>
> `Tc-u₁`, `u₁ᵗ`, `T₁ᵗ`: **第二项带紧读法, 无条件.** 这不是 `Goodᴺ`, 只是层号与读法合法.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FeedGoodTc where

open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Free.Prefix using (Z)
open import OCF.Align.GuardTightCum using (Ordᴵ; _⊑ᴵ_; _≅ᴵ_; _<ᴵ_; <ᴵ-dec; via; zero; suc; lim; z≅; s≅; l≅; s⊑; z⊑; ≅ᴵ-refl; ≅ᴵ-sym; ⊑ᴵ-trans)
open import OCF.Align.GuardTightLv
open Lv Dom₀ hiding (zero; suc; lim)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTree using (T₀)
open import OCF.Align.GuardTightUp using (feedL; u₀; GL; gl; lvl; cfG; tcG)
open import OCF.Align.GuardReadRd using (Tc-F; module RdLv₅)
open import OCF.Align.FeedGoodFirst using (two; Lv₅²; feed≈; Cf-u₁; u₁; path-from; first-of)
import OCF.Align.GuardTightUni as Uni
private module U = Uni Dom₀
open U using (F)
```

## §1 `Tc` 沿 $\approx$

```agda
Tc-≈ : ∀ {a b} → a ≈ b → Tc b → Tc a
Tc-≈ Lv.z≈ tb = tb
Tc-≈ (Lv.s≈ e) tb = Tc-≈ e tb
Tc-≈ (Lv.l≈ h) tb = λ n → Tc-≈ (h n) (tb n)
Tc-≈ {Lv.lc c t g} {Lv.lc c′ t′ g′} (Lv.o≈ d e h) (rd′ , tt′ , tg′) =
  rd″ , Tc-≈ e tt′ , (λ η e₁ → Tc-≈ (h η e₁ η (conv d e₁) (≅ᴵ-refl η)) (tg′ η (conv d e₁)))
  where
  rd″ : Rdr c t g
  rd″ η e₁ P with mvC P (h η e₁ η (conv d e₁) (≅ᴵ-refl η))
  ... | mvc d₁ P′ t₁ with rd′ η (conv d e₁) P′
  ...   | rdF d₂ Q tr with mvC Q (≈-sym e)
  ...     | mvc d₃ Q′ t₃ = rdF (lkC d₁ (lkC d₂ d₃)) Q′ (λ E x → t₃ E (tr E (t₁ E x)))
  rd″ η e₁ P | mvc d₁ P′ t₁ | rdB a ea l d₂ Q tr with mvC Q (≈-sym (h a (conv (≅ᴵ-sym d) ea) a ea (≅ᴵ-refl a)))
  ...     | mvc d₃ Q′ t₃ = rdB a (conv (≅ᴵ-sym d) ea) l (lkC d₁ (lkC d₂ d₃)) Q′ (λ E x → t₃ E (tr E (t₁ E x)))
```

## §2 界 1 的读法改成界 2

```agda
one⊑two : suc zero ⊑ᴵ two
one⊑two = s⊑ z≅ (suc zero)

up2 : ∀ {η} (e : two ⊑ᴵ η) a → suc zero ⊑ᴵ a → a ⊲ η → (two ⊑ᴵ a) ⊎ (a ≡ suc zero)
up2 e a ea ⊲= = inj₁ e
up2 e zero (s⊑ _ ()) (⊲ˢ h)
up2 {η} (s⊑ (s≅ z≅) q₀) (suc b) ea (⊲ˢ h) with <ᴵ-dec (h {η} (λ r → r)) q₀
... | injᵃ (via z≅ zero) = inj₂ refl
... | injᵃ (via e₁ (suc ()))
... | injᵇ (via e₁ r) = inj₁ (s⊑ e₁ (suc r))
... | injᶜ c = inj₁ (s⊑ (≅ᴵ-sym c) zero)
up2 {η} (s⊑ (s≅ z≅) q₀) (lim f s) ea (⊲ˢ h) with <ᴵ-dec (h {η} (λ r → r)) q₀
... | injᵃ (via () zero)
... | injᵃ (via e₁ (suc ()))
... | injᵇ (via e₁ r) = inj₁ (s⊑ e₁ r)
... | injᶜ ()

rd² : Rdr two (F (suc zero)) (λ η e → F η)
rd² η e P with RdLv₅.rdU η (⊑ᴵ-trans one⊑two e) P
... | rdF d Q tr = rdF d Q tr
... | rdB a ea l d Q tr with up2 e a ea l
...   | inj₁ ea′ = rdB a ea′ l d Q tr
...   | inj₂ refl = rdF d Q tr

Tc-Lv₅² : Tc Lv₅²
Tc-Lv₅² = rd² , Tc-F (suc zero) , (λ η e → Tc-F η)

Tc-u₁ : Tc (feedL u₀)
Tc-u₁ = Tc-≈ feed≈ Tc-Lv₅²

u₁ᵗ : GL
u₁ᵗ = gl (feedL u₀) Cf-u₁ Tc-u₁ (GL.entG u₁) (GL.pthG u₁) (GL.admG u₁)

T₁ᵗ : Z
T₁ᵗ = T₀ (lvl u₁ᵗ) (cfG u₁ᵗ) (tcG u₁ᵗ)
```
