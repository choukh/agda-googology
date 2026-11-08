# 原 θ 的常值极限与实际路由

本实验直接使用原 θ 和 θ-path；公共界与目标同为 lim(const 2)。
检查第0支到第1支的第一位置，不假定路径证明无关。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedThetaRouteLimit where
open import Data.Nat using (ℕ)

open import Data.Unit using (tt)
open import Data.Sum using (inj₂)
open import OCF.Lean.LHRecTy using (lz; ls)
open import OCF.Lean.LHRecFl using (flL; Lg-flL; Lg-ι)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedDescentValueBridge using (Native)
import OCF.Align.BoundedNativeFloor as N
import OCF.Align.BoundedNativeFoldRun as R

two : Cd
two = hs (hs hz)
B : Cd
B = hl (λ _ → two)
legal-B : LgB B
legal-B = (λ n → hself) , (λ n → tt)

W : Wd (Native B)
W n = ((tt , hz) , hz) , hz

legal-W : LgW (Native B) W
legal-W n = ((tt , tt) , tt) , tt

legal-θ-two : LgB (N.θ two)
legal-θ-two = Lg-⊞ _ _
  (Lg-⊞ _ _ tt (Lg-ι (inj₂ hz) (flL (ls lz)) (Lg-flL (ls lz))))
  (Lg-ι (inj₂ (hs hz)) (flL (ls (ls lz))) (Lg-flL (ls (ls lz))))

legal-θ-B : LgB (N.θ B)
legal-θ-B = (λ n → hself) , (λ n → legal-θ-two)

output : HB (Native B)
output = R.fold B legal-B B hself (N.θ B) (N.θ-path B B hself)

branch : ℕ → HB (Native B)
branch n = R.fold B legal-B B hself (N.θ two)
  (N.θ-path two B (hlim n hself))

no-step : branch 0 ⊲[ W ] branch 1 → ⊥
no-step (hLim hself (hLim hself (hsuc ())))

no-legal-output : LgB output → ⊥
no-legal-output l = no-step (proj₁ l 0)
```

共同界 B、目标路径 hself、原输入 θ B、原 θ-path 与目标世界 W 全部实际给出且合法。
`no-step` 精确否定原输出的第0支到第1支第一位置；`no-legal-output` 因而
否定该非零目标处的原运行结果。没有改动 θ、路径或运行器。

此结果不是 countable-output 的非法定理：目标0没有本例的两个目标副本；
但凡要用“原 θ-path 自动保证任意共同目标处相邻步进”的引理证明内部 above
调用，必须避开本例，不能仅把证书限制为原 θ-path 就取得该引理。
翻译账：新增真实输入的树侧否定，不增加记号规则或新源语言。
