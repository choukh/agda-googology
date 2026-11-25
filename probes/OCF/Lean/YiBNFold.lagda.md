# 一致槽位行的实际折叠（原型）
编译定理：任意旧层号上的新树都折到一个有指定槽位的目标层；对新第一位置单调，输出非零。
后继迭代沿用 `YiFWNode.next⁺`，旧树嵌入与孩子递归沿用 `YiFWCompat.embed`；没有查表或派发。
Ω 行忽略非第一分支，嵌入行一律进入原孩子；不声称实现主线的分层 FGH 规则。
第 0 层不能给指定槽位，值与旧反例验收见 `YiBNAccept`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBNFold where
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst)
import OCF.Lean.YiRWBlock as O
open import OCF.Lean.YiFWBlock
open import OCF.Lean.YiFWCompat
import OCF.Lean.YiFWNode as W
open import OCF.Lean.YiBNRow using (row; row-step)

module Fold {j : O.L} (q : O.Pos j) where
  local-row⁺ : ∀ {ℓ} (p : O.Pos ℓ) → (O.Br ℓ p → W.T⁺ j) → W.T⁺ j
  local-row⁺ {ℓ} p G = row {S = Sig ℓ} q p (λ z → proj₁ (G z)) , ◃t (proj₂ (G (O.fromBr ℓ p O.zero))) ◃w

  mutual
    φ : (ℓ : O.L) → W.T⁺ j → T (Sig ℓ) → W.T⁺ j
    φ ℓ β zero = β
    φ ℓ β (suc x) = W.next⁺ (φ ℓ β x)
    φ ℓ β (lim f a) = lim (λ n → proj₁ (φ ℓ β (f n))) (λ n → mono ℓ β (a n)) , ◃t (proj₂ (φ ℓ β (f 0))) (◃l 0)
    φ ℓ β (Ω p g) = local-row⁺ p (λ z → φ ℓ β (g z))
    φ (O.nd s h) β (up x c y e) = old (h c) (φ (O.nd s h) β x) y

    old : (ℓ : O.L) → W.T⁺ j → O.Tr ℓ → W.T⁺ j
    old ℓ β x = φ ℓ β (embed ℓ x)

    mono : (ℓ : O.L) (β : W.T⁺ j) {x y : T (Sig ℓ)}
      → Lt (Sig ℓ) x y → Lt (Sig j) (proj₁ (φ ℓ β x)) (proj₁ (φ ℓ β y))
    mono ℓ β ◃s = ◃l 0
    mono ℓ β (◃l n) = ◃l n
    mono ℓ β ◃w = ◃w
    mono (O.nd s h) β (◃u x c y e) = old-mono (h c) (φ (O.nd s h) β x) e
    mono (O.nd s h) β (◃c x c d) = old-mono (h c) (φ (O.nd s h) β x) d
    mono ℓ β (◃t d e) = ◃t (mono ℓ β d) (mono ℓ β e)
    mono ℓ β (◃σ {p = p} {p′ = p′} {g = g} {g′ = g′} e h) =
      row-step {S = Sig ℓ} {S′ = Sig j} q {p = p} {p′ = p′} e
        (λ z → proj₁ (φ ℓ β (g z))) (λ z → proj₁ (φ ℓ β (g′ z)))
        (λ z → mono ℓ β (h z))

    old-mono : (ℓ : O.L) (β : W.T⁺ j) {x y : O.Tr ℓ}
      → O.Lt (O.Sig ℓ) x y → Lt (Sig j) (proj₁ (old ℓ β x)) (proj₁ (old ℓ β y))
    old-mono ℓ β d = mono ℓ β (embed-mono ℓ d)

  legal : (ℓ : O.L) (β : W.T⁺ j) (x : T (Sig ℓ)) → Lt (Sig j) zero (proj₁ (φ ℓ β x))
  legal ℓ β x = proj₂ (φ ℓ β x)
```
