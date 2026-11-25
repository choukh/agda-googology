# YiLvFold 第 3 站：`tw 3` 的根，闭项合法，派发未到位

**判决：部分。编译定理：对任意派发 `way`，`ψ way zero (tw 3)` 合法 (`T-legal`)；取 `wayᵇ` 得闭项 `T₃` 与 `T₃-legal`，没有前提；
根上的行是 `refl`；每个 `ψ₀ (Ω̂ (sucⁿ 0))` 都是 `T₃` 的第一位置 (`fin-below-T₃`)。** 没有的：`wayᵇ` 在链点的层号上是否完全没有证，
它在 `suc ω` 上不完全，而在一切带守卫的分支上完全的派发推出 LPO ([YiLvFoldLim](YiLvFoldLim.lagda.md) 的 `bare-incomplete`, `branch-complete→lpo`)。
所以 `T₃` 的读法不写成 ψ₀(Ω_Ω)，只有下界的读法 ψ₀(Ω_n) 对一切 n；没有参照族的值定理。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLvFoldTw3 where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; trans)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (Ω̂; up; tw; raw1)
open import OCF.Align.YiIrrIf using (R; one; CP; self; fst; iterate; read0; read0-cp)
open import OCF.Align.YiIrrFoldSeed using (seed-tw)
open import OCF.Align.YiIrrNegLegal using (Legal-tw; Ω̂-CP)
open import OCF.Align.YiIrrFbIf using (Pt; pt; at)
open import OCF.Align.YiLvIf using (tw3-onlyP)
open import OCF.Align.YiLvFoldAdd
open import OCF.Align.YiLvFoldBase
open import OCF.Align.YiLvFold using (module Fold)
open import OCF.Align.YiLvFoldFin
```

## 1 闭项与合法性

`tw 3` 在定义域里 (已有的三条闭包定理)。合法性对任意派发成立，所以这一条不说明派发对不对。

```agda
dom-tw3 : Dom (tw 3)
dom-tw3 = tw3-onlyP , Legal-tw 3 , seed-tw 3

T : (∀ m k → Way m k) → R
T way = Fold.ψ way zero (tw 3) dom-tw3

T-legal : ∀ way → Lgl zero (T way)
T-legal way = Fold.ψ-legal way zero tt (tw 3) dom-tw3

T₃ : R
T₃ = ψ zero (tw 3) dom-tw3

T₃-legal : Lgl zero T₃
T₃-legal = ψ-legal zero tt (tw 3) dom-tw3
```

## 2 根上的行

根是层号 0 的结点，下界 1，第 `η` 支是 `Ω̂ (read0 η)`。链在第 0 层：`ηₙ₊₁ = ηₙ + ψ₀ (Ω̂ (read0 ηₙ))`，
`T₃` 是 `ψ₀ (Ω̂ (read0 ηₙ))` 的极限；各支上的折叠就是同一个 `ψ zero`。`guards₃` 是同一列坐标上相关的守卫，只用来写陈述。

```agda
br : (η : R) → .(Gd zero raw1 η) → LF
br η e = Ω̂ (up zero η (proj₂ (proj₂ e)))

tw3-form : tw 3 ≡ lc zero raw1 tt tt (tw 2) br
tw3-form = refl

dom-br : ∀ η (e : Gd zero raw1 η) → Dom (br η e)
dom-br = Node.branch zero raw1 tt tt (tw 2) br dom-tw3

points₃ : ℕ → Pt zero raw1
points₃ = iterate (next zero raw1 tt tt (tw 2) br dom-tw3) (startᴸ zero raw1 tt tt)

guards₃ : ∀ n → Gd zero raw1 (at (points₃ n))
guards₃ = ChainLegal.guards zero tt raw1
  (λ η e → ψ zero (br η e) (dom-br η e))
  (λ η e → ψ-legal zero tt (br η e) (dom-br η e))
  (λ η e → ψ-nested zero (br η e) (dom-br η e))
  (λ η e → ψ-pos zero (br η e) (dom-br η e))
  (startᴸ zero raw1 tt tt) (inj₁ refl , tt , tt)

T₃-row : T₃ ≡
  G.lim (λ i → out zero zero raw1 tt tt (tw 2) br dom-tw3 (points₃ i))
T₃-row = refl

out-at : ∀ p (e : Gd zero raw1 (at p)) →
  out zero zero raw1 tt tt (tw 2) br dom-tw3 p ≡
  ψ zero (Ω̂ (read0 (at p))) (dom-br (at p) e)
out-at (pt η e′) e = refl

-- 第 i 项是第 ηᵢ 支的折叠; 下一点是这一点加上它.
T₃-term : ∀ i → out zero zero raw1 tt tt (tw 2) br dom-tw3 (points₃ i) ≡
  ψ zero (Ω̂ (read0 (at (points₃ i)))) (dom-br (at (points₃ i)) (guards₃ i))
T₃-term i = out-at (points₃ i) (guards₃ i)

T₃-feedback : ∀ i → at (points₃ (suc i)) ≡
  plus zero (at (points₃ i))
    (ψ zero (Ω̂ (read0 (at (points₃ i)))) (dom-br (at (points₃ i)) (guards₃ i)))
T₃-feedback i =
  trans (next-additive zero raw1 tt tt (tw 2) br dom-tw3 (points₃ i))
    (cong (plus zero (at (points₃ i))) (T₃-term i))

T₃-start : at (points₃ 0) ≡ one
T₃-start = refl
```

## 3 下界：有限层号的闭项都是 `T₃` 的第一位置

第 1 个链点是 `1 + ψ₀ (Ω̂ 1)`，它的第一位置里有一切 `n + 2`；读回、`Ω̂` 与折叠都保持第一位置。
这是块内的第一位置关系 (编译定理)，不是对参照族的值定理。

```agda
num : ℕ → R
num zero = G.zero
num (suc n) = G.suc (num n)

read0-num : ∀ n → read0 (num n) ≡ fin n
read0-num zero = refl
read0-num (suc n) = cong suc (read0-num n)

plus-one : ∀ k → plus zero one (num k) ≡ num (suc k)
plus-one zero = refl
plus-one (suc k) = cong G.suc (plus-one k)

copies-num : ∀ n → copies zero one n ≡ num (suc n)
copies-num zero = refl
copies-num (suc n) =
  trans (cong (plus zero one) (copies-num n)) (plus-one (suc n))

num-below : ∀ n → Cp zero (num (suc (suc n))) (at (points₃ 1))
num-below n = inj₂ (zero , inj₂ (n , inj₁ (sym (copies-num (suc n)))))

fin-below : ∀ n → CP (fin (suc (suc n))) (read0 (at (points₃ 1)))
fin-below n =
  subst (λ z → CP z (read0 (at (points₃ 1)))) (read0-num (suc (suc n)))
    (read0-cp (at (points₃ 1)) (num-below n))

fin-below-T₃ : ∀ n → Cp zero (foldᶠ n) T₃
fin-below-T₃ zero =
  ψ-position zero (Ω̂ (fin 0)) (tw 3) (dom-Ωᶠ 0) dom-tw3 (fst (fst self))
fin-below-T₃ (suc zero) =
  ψ-position zero (Ω̂ (fin 1)) (tw 3) (dom-Ωᶠ 1) dom-tw3 (fst self)
fin-below-T₃ (suc (suc n)) =
  inj₂ (1 , ψ-position zero (Ω̂ (fin (suc (suc n))))
    (br (at (points₃ 1)) (guards₃ 1))
    (dom-Ωᶠ (suc (suc n))) (dom-br (at (points₃ 1)) (guards₃ 1))
    (Ω̂-CP (fin-below n)))
```
