# 原γ₂的完整极限公式与候选的原累计分量

验收专用。以下是对全部n的定义等式，不是有限测试。记号和HS只在
本文件及接口侧出现，未进入消费者、code或成品证书。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaGammaActual where
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.LHRecTy using (LH; ll)
open import OCF.Lean.LHRecFl using (ΣF)
open import OCF.Lean.GeneralOmegaConsumeRun using (run)
import OCF.Align.Level as L
import OCF.Align.NoCumsum as N
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.BoundedCompletionStageCore as Stage
open import OCF.Align.GeneralOmegaGammaIf

input : L.Ordᶜ L.zero
input = N.γ 1
input-HS : L.HS input
input-HS = N.cert 1
component : ℕ → L.Ordᶜ L.zero
component n = L.ψ⁰ (N.D.G n)
component-HS : ∀ n → L.HS (component n)
component-HS n = L.hl₁ input-HS n
component-source : ℕ → LH
component-source n = source (component n)

reference-branch : ℕ → Cd
reference-branch n = reference (component n) (component-HS n)
candidate-branch : ℕ → Cd
candidate-branch n = run (source input) (ΣF component-source n)

input-shape : input ≡ L.lim component
input-shape = refl
source-shape : source input ≡ ll component-source
source-shape = refl
actual-second : reference input input-HS ≡ B.forget (N.γ 2)
actual-second = refl
stage-family-second : reference input input-HS ≡ Stage.family 1
stage-family-second = refl
reference-shape : reference input input-HS ≡ hl reference-branch
reference-shape = refl
candidate-shape : candidate input ≡ hl candidate-branch
candidate-shape = refl

CallbackObligation : ℕ → Set
CallbackObligation n = reference-branch n ≤ᵛ candidate-branch n
```

这里精确定位同源方案的整族义务：左侧每项仍是原
ψ⁰(Ω(toLevel (ψ⁰(G n))))，右侧是原新运行器对所有已访问分量的ΣF，
没有把右侧改成孤立floor(component-source n)。尚未给CallbackObligation
全族实例，也没有推出γ₂≤candidate input。最终Λ下界允许错位覆盖、
更高源层或共尾重排，不要求这个同源逐项义务必须成立。

真正的原typed反馈还保留ψ q在高层零叶输出Ω_j、及其全部高层坐标。
新算法的零叶输出为1、code只注入低层floor加纯完成反馈；两者不能
逐项按读法等同。下一证明需把这些高层typed坐标的整棵树送到实际
更高ΩL分量，而不是仅增加纯P闭包次数。本段是缺口定位，不是值上界
或路线否定。
