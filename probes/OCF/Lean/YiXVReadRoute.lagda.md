# YiXVReadRoute
> 验收文件。档位：编译定理。Route 对原路径复合封闭，且原 wh 对每棵实际零层树都有 Route，含 pt 2。
> 从 SourceWorld*/ReadAffineLift 推广，树、原折叠与 UR 未改；未交自然极限跨分支和节点的完整世界输出、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadRoute where
open import Data.Nat using (ℕ; suc)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLSTw1 as T
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadRouteInput as R
zero : ∀ r → R.Route r S.zero (T.wh r)
zero S.zero = R.here
zero (S.suc r) = R.ins (zero r)
zero (S.lim f d) = R.inlu (λ n → zero (f n))
zero (S.Ω () g)
zero (S.up r () y ny)

within : ∀ {top y v} → R.Route top y v → y P.≤ᵀ top
within R.here = P.here
within (R.ins h) = P.below (P.advance (within h) P.root)
within (R.inl n h) = P.below (P.advance (within h) (P.branch n))
within (R.inlu h) = P.below (P.advance (within (h 0)) (P.branch 0))

compose : ∀ {top mid y v w} → R.Route top mid v → R.Route mid y w → R.Route top y (Path._∙_ w v)
compose R.here h = h
compose (R.ins k) h = R.ins (compose k h)
compose (R.inl n k) h = R.inl n (compose k h)
compose (R.inlu k) h = R.inlu (λ n → compose (k n) h)

actual₂ : R.Route (T.pt 2) S.zero (T.wh (T.pt 2))
actual₂ = zero (T.pt 2)
```
