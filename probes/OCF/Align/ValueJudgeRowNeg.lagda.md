# 值判据 (八): `Rows` 不决定值

> **判决: HOLDS (编译过的否定).** 底座. 结论写在 [ValueJudge](ValueJudge.lagda.md). 只有一个高度的结构 `HS₁`. 层号自己的值 `lvT` 满足 `Rows`, 证书的计值也满足, 第 0 项不同 (`rows-blind`). 所以 `Rows` 是相对的判据: 第 0 行和后继行的数值要由别的东西定. 这是编译过的否定, 否定的只是 "`Rows` 单独决定值". 另有: `Rows` 确实能拒绝 (`const-rejected`, `top-low-rejected`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValueJudgeRowNeg where

open import Agda.Primitive using (Level)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level
open import OCF.Free.Prefix using (toZ; Ord₊ˢ)
open import OCF.Free.Force using (Goodᴺ; gz; gs; forceᴺ)
open import OCF.Align.LadderInfBase
open import OCF.Align.ValueJudgeBase
import OCF.Align.ValueJudgeRow
import OCF.Align.ValueJudgeRowV
import OCF.Align.ValueJudgeLadder
import OCF.Align.LadderInfTree
import OCF.Align.LadderInfRules
import OCF.Align.LadderInfCx
import OCF.Align.LadderInfStrict2

HS₁ : HtS
HS₁ = record
  { Ht = ⊤ ; _<ᴸ_ = λ _ _ → ⊥ ; h₀ = tt
  ; tr< = λ () ; irr = λ () ; no< = λ ()
  ; bot = λ { tt → inj₁ refl }
  ; tri = λ { tt tt → teq refl }
  ; Rec = λ X F m () ; Rec-β = λ X F m ()
  ; view = λ { tt → base }
  ; tr-assoc = λ ()
  ; view-step = λ {m} {F} {qs} e i → ⊥-elim (qs 0)
  }

module R₁ = OCF.Align.ValueJudgeRow HS₁
module V₁ = OCF.Align.ValueJudgeRowV HS₁
module J₁ = OCF.Align.ValueJudgeLadder HS₁

lvT : Ordᴵ → Ordᶜ zero
lvT zero = zero
lvT (suc a) = suc (lvT a)
lvT (lim f s) = lim (λ n → lvT (f n))

lvT-≅ : ∀ {a b} → a ≅ᴵ b → lvT a ≅ lvT b
lvT-≅ z≅ = z≅
lvT-≅ (s≅ e) = s≅ (lvT-≅ e)
lvT-≅ (l≅ h) = l≅ (λ n → lvT-≅ (h n))

W₁ : ⊤ → Ordᴵ → Ordᶜ zero
W₁ _ = lvT

rows-W₁ : R₁.Rows W₁
rows-W₁ = record
  { r-cong   = λ m e → ≅→≈ᵛ (lvT-≅ e)
  ; r-strict = λ m a → ≼-refl (suc (lvT a))
  ; r-limit  = λ m f s → ≼-refl _ , ≼-refl _
  ; r-chain  = λ { tt F qq () }
  ; r-clos   = λ ()
  }
```

`V≥2`: 证书的计值至少是 2 (`S1ᵀ`), 所以不等于 `lvT 0`.

```agda
open OCF.Align.LadderInfTree HS₁ using (Tᵠ; ok₀; Ω̇; ψ̄ᵠ)
open OCF.Align.LadderInfStrict2 HS₁ using (S1ᵀ; ⊑→One; 𝟏⊑Ω̇)
open OCF.Align.LadderInfCx HS₁ using (idO)

V≥2 : ∀ a → suc (suc (zero {zero})) ≼ J₁.V tt a
V≥2 a = go (S1ᵀ {t = Ω̇ tt a} {ok = ok₀} {e = J₁.e₀} {ev = J₁.ev₀} {p = zero} (⊑→One (𝟏⊑Ω̇ tt a)) idO (J₁.GV tt a))
  where
  go : (Σ (Goodᴺ (toZ (Ord₊ˢ.suc (Ord₊ˢ.suc Ord₊ˢ.zero)))) λ H → forceᴺ _ H ⊑ forceᴺ _ (J₁.GV tt a)) → suc (suc zero) ≼ J₁.V tt a
  go (gs (gs gz) , le) = ≼-trans (⊑→≼ (suc (suc zero)) le) (≅→≼ (J₁.V-G tt a (J₁.GV tt a)))

rows-blind : R₁.Rows J₁.V × R₁.Rows W₁ × ¬ (J₁.V tt zero ≼ W₁ tt zero)
rows-blind = V₁.V-rows , rows-W₁ , λ le → no (≼-trans (V≥2 zero) le)
  where
  no : ¬ (suc (suc (zero {zero})) ≼ zero {zero})
  no ()
```

**能拒绝的.** 常值函数过不了 `r-strict`. 把顶层的值换成低一层的值过不了 `r-clos`: 对一切有闭包行的结构. 这只说明 `Rows` 不是空的条件.

```agda
const-rejected : ∀ (𝕊 : HtS) (c : Ordᶜ zero) → ¬ OCF.Align.ValueJudgeRow.Rows 𝕊 (λ _ _ → c)
const-rejected 𝕊 c R = ≺ᵛ-irrefl c (OCF.Align.ValueJudgeRow.r-strict R (HtS.h₀ 𝕊) zero)

top-low-rejected : ∀ (𝕊 : HtS) (W : HtS.Ht 𝕊 → Ordᴵ → Ordᶜ zero) {n m} (r : HtS._<ᴸ_ 𝕊 n m) → HtS.view 𝕊 m ≡ clos r →
                   W m zero ≼ W n zero → ¬ OCF.Align.ValueJudgeRow.Rows 𝕊 W
top-low-rejected 𝕊 W {n} r ev le R = ≺ᵛ-irrefl (W n zero) (≼-trans (OCF.Align.ValueJudgeRow.r-clos R r ev) le)
```
