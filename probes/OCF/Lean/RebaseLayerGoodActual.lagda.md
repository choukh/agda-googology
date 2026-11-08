# 全有限编码地板的真实一步下降及可数观测

一步输入是原floor经过通用重定位，运行仍为原at。n是结构参数，
不是给Old4另写一个阶段模型。最低层观测明确使用原T.fold。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.RebaseLayerGoodActual where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.RebaseLayerIf using (vz; vs; vr; vl; vli; vo; vor)
open import OCF.Lean.RebaseLayerGoodIf
open import OCF.Lean.RebaseLayerGoodClosure
open import OCF.Lean.RebaseLayerGoodRun using (preserve; compare)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunFloor using (legal-num)
open import OCF.Align.BoundedCompletionFiniteRunIf using (at)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)
import OCF.Lean.GeneralRebaseDomainActual as Code
import OCF.Align.BoundedCompletionUniformIf as Old
import OCF.Align.BoundedCompletionUniformClosure as OldC
import OCF.Align.BoundedCompletionTerminalValueRun as Terminal
import OCF.Align.BoundedNativeTerminalReady as T

encoded-floor-good : ∀ n → Good (num n)
  (at (suc n) n {B = num (suc n)} (legal-num (suc n)) hself (hsuc hself)
    (Code.enc (num n) (floor n) (floor (suc n))))
encoded-floor-good n = preserve (suc n) n {B = num (suc n)} (legal-num (suc n)) hself (hsuc hself)
  (Code.enc (num n) (floor n) (floor (suc n))) (Code.floor-encoded-good n)

zero-to-old : ∀ {a b} → Value hz a b → Old.Value hz a b
zero-to-old vz = Old.vz
zero-to-old (vs p) = Old.vs (zero-to-old p)
zero-to-old (vr p) = Old.vr (zero-to-old p)
zero-to-old (vl p) = Old.vl (λ n → zero-to-old (p n))
zero-to-old (vli n p) = Old.vli n (zero-to-old p)
zero-to-old (vo {κ = inj₁ ()} p)
zero-to-old (vo {κ = inj₂ _} p) = Old.vo (λ x y xy → zero-to-old (p x y xy))
zero-to-old (vor {κ = inj₁ ()} p)
zero-to-old (vor {κ = inj₂ _} p) = Old.vor (λ e → zero-to-old (p e tt))

terminal : ∀ {a b x y} → Value hz a b → x ≤ᵛ y → T.fold x a ≤ᵛ T.fold y b
terminal p xy = Terminal.eval (OldC.value-zero (zero-to-old p)) xy

observed : ∀ n {B B′} (lB : LgB B) (lB′ : LgB B′)
  (pc : num n ⊲ B) (pc′ : num n ⊲ B′) (pt : hz ⊲ B) (pt′ : hz ⊲ B′)
  {a b x y} → Good (num n) a → Good (num n) b → Value (num n) a b → x ≤ᵛ y →
  T.fold x (at n zero lB pc pt a) ≤ᵛ T.fold y (at n zero lB′ pc′ pt′ b)
observed n lB lB′ pc pc′ pt pt′ ga gb ab xy =
  terminal (compare n zero lB lB′ pc pc′ pt pt′ ga gb ab) xy
```

encoded-floor-good覆盖所有有限层真实非零输入。observed给可数树值
比较，仍要求输入Good；它没有证明原多槽Old全族由这些编码输出覆盖，
也没有把任意有限层族当EBO共尾族。下一步需统一动态世界消去及高于
全部有限层的实际指标族。
