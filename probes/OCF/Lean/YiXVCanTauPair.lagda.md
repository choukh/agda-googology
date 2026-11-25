# YiXV: 运输的双向受限比较
> 验收文件。档位：编译定理。沿 YiXVCanTau 的运输形状递归；层 1 好树与其运输互相 ≤ₚ，供孩子的后继余量搬运。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCanTauPair where
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-trans; u≼)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVCanTau as T

pair : ∀ {X} → O.Gd X → (X R.≤ₚ T.τ X) × (T.τ X R.≤ₚ X)
pair O.gz = R.zz , R.zz
pair (O.gs g) = R.ss (proj₁ (pair g)) , R.ss (proj₂ (pair g))
pair (O.gl g) = R.l≤ (λ n → R.≤l n (proj₁ (pair (g n)))) , R.l≤ (λ n → R.≤l n (proj₂ (pair (g n))))
pair (O.gi {f = f} law gb) =
  R.ii (λ x y o q → R.trans (O.SC.mo law x (T.τ₀⁺ y) o (≼-trans q (proj₂ (T.plus≈ y))))
    (proj₁ (pair (gb (T.τ₀⁺ y) (T.pos⁺ (≼-trans o q)))))) ,
  R.ii (λ x y o q → R.trans (proj₂ (pair (gb (T.τ₀⁺ x) (T.pos⁺ o))))
    (O.SC.mo law (T.τ₀⁺ x) y (T.pos⁺ o) (≼-trans (proj₁ (T.plus≈ x)) q)))
pair (O.gu {y}) = R.fu R.fu (u≼ (proj₂ (O.tr⁻≈ y))) , R.fu R.fu (u≼ (proj₁ (O.tr⁻≈ y)))
```
