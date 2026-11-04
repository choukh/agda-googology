# 序数高度: 与 `HS∞`, `HS₂` 的模拟

> **判决: HOLDS (编译过, 无条件).** 结论写在 [LadderOrd](LadderOrd.lagda.md). 实例 `HS∞`, `HS₂` 的高度保序地映到码 `ωᶜ`, `ω·ᶜ 1` 的位置, 第 0 行逐字对齐, 右边 `tri` 的对角线是 `teq refl`. 所以 `LadderOrdCross` 的三个参数都闭合地给出, 没有假设:
>
> - `bridge∞ m α α′ d : T∞.Tᵠ m α ≈ᴿ Oω.Tᵠ (e∞ m) α′`
> - `bridge₂ m α α′ d : T₂.Tᵠ m α ≈ᴿ O₂.Tᵠ (e₂ m) α′`
>
> - `bridge² m α α′ d : T₂.Tᵠ m α ≈ᴿ O².Tᵠ (e² m) α′`: 同一段放进 $\omega^2$
>
> 码 `ω·ᶜ 1` 的顶 `end` 不在 $e_2$ 的像里: 那是第一个跨过 `HS₂` 的高度.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderOrdInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Free.Level using (Ordᴵ; _≅ᴵ_)
open import OCF.Free.Eq using (_≈ᴿ_)
open import OCF.Free.Floor using (Run)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderNFTree using (_<ᴸ_; zero; suc; dn)
open import OCF.Align.LadderOrdBase
open import OCF.Align.LadderInfBase using (HtS)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode
open import OCF.Align.LadderInfTop using (HS∞; fin; ∞; inf) renaming (H to H∞; _<∞_ to _<∞_)
open import OCF.Align.LadderInfTop2 using (HS₂; top) renaming (fin to fin₂; H to H₂; _<₂_ to _<₂_)
import OCF.Align.LadderInfTop as Top
import OCF.Align.LadderInfTop2 as Top2
import OCF.Align.LadderOrdCross
import OCF.Align.LadderInfTree
import OCF.Align.LadderOrdTree
```

## §1 块号上的序

```agda
ltB-lt : ∀ g {j k} (l : j <ᴸ k) (p : Pos (cs (g j))) (q : Pos (cs (g k))) → ltB g j k p q
ltB-lt g {j = zero} {k = suc k} l p q = tt
ltB-lt g {j = suc j} {k = suc k} l p q = ltB-lt (λ i → g (suc i)) (dn l) p q
```

## §2 实例 ℕ∪{∞}

```agda
e∞ : H∞ → Pos (cs ωᶜ)
e∞ (fin n) = low (blk n end)
e∞ ∞ = end

ε∞ : ∀ {n m} → n <∞ m → e∞ n <ᴾ e∞ m
ε∞ (fin l) = ltB-lt (λ _ → cz) l end end
ε∞ (inf n) = tt

module O∞ = OCF.Align.LadderOrdTree (HB ωᶜ)
module T∞ = OCF.Align.LadderInfTree HS∞
import OCF.Align.LadderOrdCrossEq as CE

rowq∞ : ∀ m → CE.RowEq HS∞ (HB ωᶜ) e∞ ε∞ m (HtS.view HS∞ m)
rowq∞ (fin zero) = refl
rowq∞ (fin (suc m)) = cong clos (<ᴾ-prop {p = e∞ (fin m)} {q = e∞ (fin (suc m))} _ _)
rowq∞ ∞ = refl

module C∞ = OCF.Align.LadderOrdCross HS∞ (HB ωᶜ) e∞ ε∞ <ᴾ-tri-self rowq∞

bridge∞ : ∀ m α α′ → α ≅ᴵ α′ → T∞.Tᵠ m α ≈ᴿ O∞.Tᵠ (e∞ m) α′
bridge∞ = C∞.bridge
```

## §3 实例 ω+ω

```agda
M₂ : Code
M₂ = ω·ᶜ 1

e₂ : H₂ → Pos (cs M₂)
e₂ (fin₂ n) = low (blk 0 (low (blk n end)))
e₂ (top n) = low (blk n end)

ε₂ : ∀ {n m} → n <₂ m → e₂ n <ᴾ e₂ m
ε₂ (Top2.fin l) = ltB-lt (λ _ → cz) l end end
ε₂ (Top2.sw n zero) = tt
ε₂ (Top2.sw n (suc m)) = tt
ε₂ (Top2.top l) = ltB-lt _ l end end

module O₂ = OCF.Align.LadderOrdTree (HB M₂)
module T₂ = OCF.Align.LadderInfTree HS₂

rowq₂ : ∀ m → CE.RowEq HS₂ (HB M₂) e₂ ε₂ m (HtS.view HS₂ m)
rowq₂ (fin₂ zero) = refl
rowq₂ (fin₂ (suc m)) = cong clos (<ᴾ-prop {p = e₂ (fin₂ m)} {q = e₂ (fin₂ (suc m))} _ _)
rowq₂ (top zero) = refl
rowq₂ (top (suc m)) = cong clos (<ᴾ-prop {p = e₂ (top m)} {q = e₂ (top (suc m))} _ _)

module C₂ = OCF.Align.LadderOrdCross HS₂ (HB M₂) e₂ ε₂ <ᴾ-tri-self rowq₂

bridge₂ : ∀ m α α′ → α ≅ᴵ α′ → T₂.Tᵠ m α ≈ᴿ O₂.Tᵠ (e₂ m) α′
bridge₂ = C₂.bridge
```

## §4 同一段放进 $\omega^2$

顶不同, 位置的路径也不同 (`top (n+1)` 进第 1 块), 值不变. 这是 "树不依赖字面上界" 在一个实例上的定理, 不是一般的 $M\subset M'$ 定理 (后者没有写).

```agda
e²  : H₂ → Pos (cs ω²ᶜ)
e² (fin₂ n) = low (blk 0 (low (blk n end)))
e² (top zero) = low (blk 0 end)
e² (top (suc n)) = low (blk 1 (low (blk n end)))

ε² : ∀ {n m} → n <₂ m → e² n <ᴾ e² m
ε² (Top2.fin l) = ltB-lt (λ _ → cz) l end end
ε² (Top2.sw n zero) = tt
ε² (Top2.sw n (suc m)) = tt
ε² (Top2.top {n = zero} {m = suc m} l) = tt
ε² (Top2.top {n = suc n} {m = suc m} l) = ltB-lt (λ _ → cz) (dn l) end end

module O² = OCF.Align.LadderOrdTree (HB ω²ᶜ)

rowq² : ∀ m → CE.RowEq HS₂ (HB ω²ᶜ) e² ε² m (HtS.view HS₂ m)
rowq² (fin₂ zero) = refl
rowq² (fin₂ (suc m)) = cong clos (<ᴾ-prop {p = e² (fin₂ m)} {q = e² (fin₂ (suc m))} _ _)
rowq² (top zero) = refl
rowq² (top (suc zero)) = cong clos (<ᴾ-prop {p = e² (top zero)} {q = e² (top (suc zero))} _ _)
rowq² (top (suc (suc m))) = cong clos (<ᴾ-prop {p = e² (top (suc m))} {q = e² (top (suc (suc m)))} _ _)

module C² = OCF.Align.LadderOrdCross HS₂ (HB ω²ᶜ) e² ε² <ᴾ-tri-self rowq²

bridge² : ∀ m α α′ → α ≅ᴵ α′ → T₂.Tᵠ m α ≈ᴿ O².Tᵠ (e² m) α′
bridge² = C².bridge
```

## §5 秩读出的高度

位置的秩就是它的序数值. 这是读法 "高度 $p$ 是 $\Omega\cdot(1+\mathrm{rk}\,p)+\alpha$" 里的 $\mathrm{rk}\,p$; 读法本身是判断, 这几个等式是定理.

```agda
natO : ℕ → Ordᴵ
natO zero = Ordᴵ.zero
natO (suc n) = Ordᴵ.suc (natO n)

rk-fin₂ : ∀ n → rkP Ordᴵ.zero (e₂ (fin₂ n)) ≡ natO n
rk-fin₂ zero = refl
rk-fin₂ (suc n) = cong Ordᴵ.suc (rk-fin₂ n)

rk-top₀ : rkP Ordᴵ.zero (e₂ (top 0)) ≡ val ωᶜ
rk-top₀ = refl

rk-top-suc : ∀ n → rkP Ordᴵ.zero (e₂ (top (suc n))) ≡ Ordᴵ.suc (rkP Ordᴵ.zero (e₂ (top n)))
rk-top-suc n = refl

rk-end₂ : rkP Ordᴵ.zero (end {M₂}) ≡ val M₂
rk-end₂ = refl
```
