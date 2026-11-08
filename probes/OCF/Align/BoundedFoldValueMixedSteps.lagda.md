# 全混合折叠部分和的第一位置步进

证明具体运行器保持左前缀的位置，不假设它保持一般值关系。
这个律覆盖所有目标与所有输入后缀；公共源界仍是固定实际 B=Ω。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedFoldValueMixedSteps where
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₂)
open import Data.Nat using (ℕ; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldIf using (T)
open import OCF.Lean.BoundedFoldClass using (decide; classify; keep; same; above)
import OCF.Align.BoundedFoldValueMixed as M
import OCF.Lean.BoundedContextClosed as C

prefix-position : ∀ t pt a b {W} →
  M.Fold.fold t pt a ⊲[ W ] M.Fold.fold t pt (a ⊞ b)
prefix-position t pt a hz = hself
prefix-position t pt a (hs b) = hlim 0 (prefix-position t pt a b)
prefix-position t pt a (hl f) = hlim 0 (prefix-position t pt a (f 0))
prefix-position t pt a (hΩ (κ , p) g) {W}
  with decide M.β pt (proj₂ C.legal-w) C.legal-B (classify M.β C.B κ p)
... | keep κ′ fr = hLim (botBd (T t) κ′ W)
  (prefix-position t pt a (g (fr (bot (T t) κ′))))
... | same to = hlim 0 (prefix-position t pt a (g (to (hs hz))))
... | above i pi ti to = hlim 0 (prefix-position t pt a (g (to (hs hz))))

folded-step : ∀ n {W} →
  M.Fold.fold hz (z⊲ᴮ C.B) (M.sums n) ⊲[ W ]
  M.Fold.fold hz (z⊲ᴮ C.B) (M.sums (suc n))
folded-step n = prefix-position hz (z⊲ᴮ C.B) (M.sums n) (M.floor (suc n))
```

全混合输出的外层 ℕ-极限步进已无条件获得。完整 LgB 仍要求每个
fold(sums n) 合法；本篇不把步进本身误报为全部合法性。
