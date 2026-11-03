# 脚手架 (四): [LvKeyStep](LvKeyStep.lagda.md) 的 `GL` 含反例族

> 不含记号. 结论写在 [ScafOmega2](ScafOmega2.lagda.md). `GL` 的分支类型自带证书, 与 `Ordᴵ` 的 `lim` 同形. 这里证明同形到底: `Ordᴵ` 整个嵌进 `GL` (`em`, `WF-em`), 所以 `y s` 在 `GL` 里 (`y∈GL`), 对 `GL` 的无条件判决是 WLPO (`no-read-GL`). **`GL` 单独逃不掉 `no-read`.** 它的比较是局部于世界的 (`Bel`), 世界的表项要提供字面前驱; 表项从哪里来是下界证据那件事.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafOmega2GL where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Level hiding (_⊑_)
import OCF.Align.LvKeyBase as B
open B using (LI; _≈_; _<ᴸ_; Cp; Adm; WF; _⊴_; _⊑_; _⊑ᴷ_; viaᴸ; viaᴷ)
open import OCF.Align.LvKeyStep using (S₀; module Next)
open import OCF.Align.LvIRNeg using (WLPO)
open import OCF.Align.ScafOmega2Family using (yᴵ; ω⁺; no-read-ᴵ; G-excl)
open import Data.Bool using (Bool; false)

open Next S₀ using (GL; gl; ⌞_⌟)
```

## §1 嵌入

```agda
em : Ordᴵ → LI
em zero      = LI.zero
em (suc a)   = LI.suc (em a)
em (lim f s) = LI.lim (λ n → em (f n))

em≈ : ∀ {a b} → a ≅ᴵ b → em a ≈ em b
em≈ z≅     = B.z≈
em≈ (s≅ e) = B.s≈ (em≈ e)
em≈ (l≅ h) = B.l≈ (λ n → em≈ (h n))

em≈⁻ : ∀ {a b} → em a ≈ em b → a ≅ᴵ b
em≈⁻ {a = zero}    {b = zero}    B.z≈     = z≅
em≈⁻ {a = suc a}   {b = suc b}   (B.s≈ e) = s≅ (em≈⁻ e)
em≈⁻ {a = lim f s} {b = lim g t} (B.l≈ h) = l≅ (λ n → em≈⁻ (h n))

em< : ∀ {a b} → a <ᴵ b → em a <ᴸ em b
em< zero      = B.zero
em< (suc q)   = B.suc (em< q)
em< (lim n q) = B.lim n (em< q)

adm : ∀ {a b} (q : a <ᴵ b) E → Adm E (em< q)
adm zero      E = tt
adm (suc q)   E = adm q E
adm (lim n q) E = adm q E

pull : ∀ a {k} → k <ᴸ em a → Σ Ordᴵ λ a′ → (k ≡ em a′) × (a′ <ᴵ a)
pull (suc a) B.zero = a , refl , zero
pull (suc a) (B.suc r) with pull a r
... | a′ , e , q = a′ , e , suc q
pull (lim f s) (B.lim n r) with pull (f n) r
... | a′ , e , q = a′ , e , lim n q

noCp : ∀ a {g} → Cp (LI.lcl g) (em a) → ⊥
noCp (suc a) (B.suc p) = noCp a p
noCp (lim f s) (B.lim n p) = noCp (f n) p

em⊑ : ∀ {a b} → a ⊑ᴵ b → em a ⊑ em b
em⊑ {a} {b} e r with pull a r
... | a′ , refl , q with sim e q
... | via d q′ = viaᴸ (em≈ d) (em< q′) (λ E _ → adm q′ E)

em⊑ᴷ : ∀ {a b} → em a ⊑ᴷ em b
em⊑ᴷ {a} p = ⊥-elim (noCp a p)

WF-em : ∀ a → WF (em a)
WF-em zero      = tt
WF-em (suc a)   = WF-em a
WF-em (lim f s) = (λ n → em⊑ (s n) , em⊑ᴷ) , (λ n → WF-em (f n))
```

## §2 `GL` 含 `Ordᴵ`, 所以含反例族

```agda
emG : Ordᴵ → GL
emG a = gl (em a) (WF-em a) (em≈ (≅ᴵ-refl a))

y∈GL : (ℕ → Bool) → GL
y∈GL s = emG (yᴵ s)

_≺ᴸ_ : LI → LI → Set
a ≺ᴸ b = Σ LI λ r → (a ≈ r) × (r <ᴸ b)

back : ∀ {a b} → em a ≺ᴸ em b → a ≺ᴵ b
back {a} {b} (r , d , q) with pull b q
... | a′ , refl , q′ = via (em≈⁻ d) q′

no-read-GL : (∀ (x : GL) → (⌞ x ⌟ ≺ᴸ em ω⁺) ⊎ (em ωᴵ ≺ᴸ ⌞ x ⌟)) → WLPO
no-read-GL d = no-read-ᴵ d′ where
  d′ : ∀ a → a ≺ᴵ ω⁺ ⊎ ω⁺ ⊑ᴵ a
  d′ a with d (emG a)
  ... | inj₁ q = inj₁ (back q)
  ... | inj₂ q with back q
  ...   | via e r = inj₂ (s⊑ e r)
```

## §3 下界证据同样切开这个族

把 [ScafOmega2Family](ScafOmega2Family.lagda.md) 的 `G` 搬到 `GL` 上. 这里的 `⊑` 是 `LvKeyBase` 的路径搬运, 带对一切表的转移. `Step` 的局部版本没有写; 下面只说明守卫的形状在这一层仍然起作用, 不说明 `Step` 已经有了它.

```agda
Gᴸ : Ordᴵ → GL → Set
Gᴸ τ x = em (suc τ) ⊑ ⌞ x ⌟

Gᴸ-rise : ∀ {τ x} → Gᴸ τ x → em τ ≺ᴸ ⌞ x ⌟
Gᴸ-rise e with e B.zero
... | viaᴸ d p t = _ , d , p

Gᴸ-excl : ∀ s → Gᴸ ω⁺ (emG (yᴵ s)) → (∀ n → s n ≡ false) → ⊥
Gᴸ-excl s e af = G-excl s (s⊑-from (back {a = ω⁺} {b = yᴵ s} (Gᴸ-rise {ω⁺} {emG (yᴵ s)} e))) af where
  s⊑-from : ∀ {τ η} → τ ≺ᴵ η → suc τ ⊑ᴵ η
  s⊑-from (via d q) = s⊑ d q
```
