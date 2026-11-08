# 重定位运行的合法可数闭项

从真实两层地板开始，每步保留旧树并加入其act输出。每个阶段经
重定位、原Native运行与原末段折叠得到可数树；最后完成其输出和。
这是新研究闭项，不替换原C，大小定理独立验收。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.RebaseCountableClosed where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg; Σ₀)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.CountableCompletionRun using (inflation)
open import OCF.Align.BoundedWorldValueTwoSlot using (V)
open import OCF.Align.BoundedWorldCoverIf using (act)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)
open import OCF.Lean.RebaseMiddleIf using (eval)
import OCF.Align.BoundedNativeTerminalReady as T
import OCF.Lean.Fold1 as F

levels : ℕ → HB V
levels zero = floor 1
levels (suc n) = levels n ⊞ act (levels n)

output : ℕ → Cd
output n = T.fold hz (eval (floor zero) (levels n))
raw : Cd
raw = hl (Σ₀ output)
tree : Cd
tree = leg raw
legal-tree : LgB tree
legal-tree = Lg-leg raw
raw-lower : raw ≤ᵛ tree
raw-lower = inflation raw

fgh : ℕ → ℕ
fgh = F.FGH tree
```

所有定义无接口参数，FGH只在已经合法的树上求值。原始阶段输出与
完成项可能不同值；本篇不声称强度ψ₀Λ、不声称优于C，也不靠输入
的高层裸值序推断折叠结果。与原Old3的关系另篇证明。
