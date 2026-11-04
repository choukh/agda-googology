# 严格列 (四): 闭包定理的特例, 闭项

> 入口 [TLCode](TLCode.lagda.md). **判决: HOLDS (编译过, 无条件; 读法是判断).** 全部是 `GᴺTᵠ` 对 `HL h` 的特例, 闭包定理一行没改. 高度的值是字面的 $t$, 所以 `dom₀` 这种 "只保证不低" 的引理没有位置: 对应的陈述是 `rk-top` (`refl`).
>
> - `Gᴸ h p α`: 对一切带证书的 $t$, 位置 $p$, $\alpha$ 有 `Goodᴺ`, 无条件.
> - `growᴸ h r`: $n<m$ 时第 0 行的计值严格增长.
> - `val≼ᴸ h`: 第 0 行的层号不低于 $t$. 不用 `plus`: 秩是字面子项, 对子项归纳, 位置由 `find` 给.
> - 闭项 `Tω·2ᴸ`, `Tω²ᴸ`, `Tω^ωᴸ`, `Tε₀ᴸ` 与 FGH. 读法是判断.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLCodeCert where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import OCF.Free.Level hiding (up)
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Floor using (Ev; Run)
open import OCF.Free.Force using (Goodᴺ; forceᴺ; forceᴺ-HS)
open import OCF.Free.Class using (lvG)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdBase using (Tri; tlt; teq; tgt)
open import OCF.Align.TLCodeShape
open import OCF.Align.TLCodeLit
open import OCF.Align.TLCodeLe using (_≼_; z≼; s≼; l≼; l≼ʳ; ≼-refl; ≼-trans; ≺→s≼; ≺→≼)
open import OCF.Align.TLCodeArith
import OCF.Align.LadderOrdTree
import OCF.Align.LadderOrdMain
import OCF.Align.LadderOrdGrow

ev₀ : Ev (suc zero) Fl
ev₀ = tt , (λ q → q)

Ptᴸ : ∀ {t} → Lit t → Set
Ptᴸ h = Pos (ss (shape h))

Tᴸ : ∀ {t} (h : Lit t) → Ptᴸ h → Ordᴵ → Run Fl
Tᴸ h = OCF.Align.LadderOrdTree.Tᵠ (HL h)

Gᴸ : ∀ {t} (h : Lit t) (p : Ptᴸ h) α → Goodᴺ (toZ (Tᴸ h p α ev₀ zero))
Gᴸ h p α = OCF.Align.LadderOrdMain.GᴺTᵠ (HL h) p α ev₀ zero

growᴸ : ∀ {t} (h : Lit t) {n m : Ptᴸ h} → n <ᴾ m → forceᴺ _ (Gᴸ h n zero) ≺ forceᴺ _ (Gᴸ h m zero)
growᴸ h r = OCF.Align.LadderOrdGrow.grow (HL h) r ev₀ zero
```

## §1 第 0 行的层号不低于 $t$

```agda
pos< : ∀ {t} (h : Lit t) (p r : Ptᴸ h) {x y} → rkT h p ≡ x → rkT h r ≡ y → x <ᴵ y → p <ᴾ r
pos< h p r refl e x with <ᴾ-tri p r
... | tlt l = l
... | teq refl = ⊥-elim (irrᴵ (subst (_ <ᴵ_) (sym e) x))
... | tgt l = ⊥-elim (irrᴵ (<ᴵ-trans (rk< h r p l) (subst (_ <ᴵ_) (sym e) x)))

dom≼ : ∀ {t} (h : Lit t) (f : Ptᴸ h → Ordᴵ) → (∀ p q → p <ᴾ q → f p ≺ᴵ f q) → ∀ {a} → Lit a → (q : a <ᴵ suc t) → a ≼ f (proj₁ (find h q))
dom≼ h f inc lz q = z≼
dom≼ h f inc (ls {a = b} hb) q =
  ≼-trans (s≼ (dom≼ h f inc hb r)) (≺→s≼ (inc _ _ (pos< h _ _ (proj₂ (find h r)) (proj₂ (find h q)) zero)))
  where
  r : b <ᴵ suc _
  r = <ᴵ-trans zero q
dom≼ h f inc (ll {f = g} hg hr) q = l≼ go
  where
  go : ∀ n → g n ≼ f (proj₁ (find h q))
  go n = ≼-trans (dom≼ h f inc (hg n) r) (≺→≼ (inc _ _ (pos< h _ _ (proj₂ (find h r)) (proj₂ (find h q)) (lim (suc n) (hr n)))))
    where
    r : g n <ᴵ suc _
    r = <ᴵ-trans (lim (suc n) (hr n)) q

val≼ᴸ : ∀ {t} (h : Lit t) → t ≼ lvG (Gᴸ h end zero)
val≼ᴸ h = dom≼ h (λ p → lvG (Gᴸ h p zero))
  (λ p q r → toLevel-≺ (forceᴺ-HS _ (Gᴸ h p zero)) (forceᴺ-HS _ (Gᴸ h q zero)) (growᴸ h {p} {q} r)) h zero
```

## §2 闭项

```agda
Tᶜᴸ : ∀ {t} → Lit t → Ordᶜ zero
Tᶜᴸ h = forceᴺ _ (Gᴸ h end zero)

Tω·2ᴸ Tω²ᴸ Tω^ωᴸ Tε₀ᴸ : Ordᶜ zero
Tω·2ᴸ = Tᶜᴸ Lω·2
Tω²ᴸ  = Tᶜᴸ Lω²
Tω^ωᴸ = Tᶜᴸ Lω^ω
Tε₀ᴸ  = Tᶜᴸ Lε₀

fghω·2ᴸ fghω²ᴸ fghω^ωᴸ fghε₀ᴸ : ℕ → ℕ
fghω·2ᴸ = FGH Tω·2ᴸ
fghω²ᴸ  = FGH Tω²ᴸ
fghω^ωᴸ = FGH Tω^ωᴸ
fghε₀ᴸ  = FGH Tε₀ᴸ
```
