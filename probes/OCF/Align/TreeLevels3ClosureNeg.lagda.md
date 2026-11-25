# 第三轮：原闭项不满足指定的反馈 Shape 闭包

本篇把实际路径与否定接到共享子合同，不从任意 raw 反例推断候选失败。
`whole` 是原 `LevelNoKFold.ψ₀Λ` 的只读像；其第 2 个 ℕ 分支确为 `ŝ`，
取该闭包的实际初值，得到 `actual-seed`。这两步由构造子见证确认，
不使用选择器的默认零分支。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevels3ClosureNeg where

open import Data.Nat using (ℕ)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (sym; subst)
import OCF.Align.NoKCertEval as E
import OCF.Align.LevelNoKFold as Original
import OCF.Align.TreeLevels3FeedbackShape as F
open import OCF.Align.TreeLevels3EnvContract

seed-of-self : ∀ z → F.IsSelfClosure z → SeedOf (F.first z) z
seed-of-self (E.ŝ c seed g) F.is-self-closure = initial-ŝ

lift-limit : ∀ z n → F.IsLimit z → ∀ {seed} →
  SeedOf seed (F.lim-at z n) → SeedOf seed z
lift-limit (E.lim f) n F.is-limit p = in-lim n p

actual-seed-path : SeedOf F.actual-seed F.whole
actual-seed-path = lift-limit F.whole 2 F.whole-is-limit
  (seed-of-self F.actual-branch F.branch-is-self-closure)

no-feedback-shape-closure : ¬ FeedbackShapeClosure F.whole
no-feedback-shape-closure closure = F.no-shape-realisation (closure actual-seed-path)

no-feedback-shape-representatives : ¬ FeedbackShapeRepresentatives F.whole
no-feedback-shape-representatives closure with closure actual-seed-path
... | G , y , eq , shape = F.no-shape-representative G y eq shape

no-original-shape-closure : ¬ FeedbackShapeClosure (E.rdZ Original.ψ₀Λ)
no-original-shape-closure closure = no-feedback-shape-closure
  (subst FeedbackShapeClosure (sym F.whole-origin) closure)

no-original-shape-representatives : ¬ FeedbackShapeRepresentatives (E.rdZ Original.ψ₀Λ)
no-original-shape-representatives closure = no-feedback-shape-representatives
  (subst FeedbackShapeRepresentatives (sym F.whole-origin) closure)

reject-self-initial : ∀ z → F.IsSelfClosure z → F.BadPair (F.first z) →
  (G : E.Goodᵁ z) → ShapedInitials G → ⊥
reject-self-initial (E.ŝ c seed g) F.is-self-closure bad
  (E.gŝ ys hy dy G₀ l₀ Gg lE m₀ mo) shape =
  F.no-bad-pair-shape-bisim seed bad G₀ (ys 0) l₀ shape

reject-limit-initial : ∀ z → F.IsLimit z →
  F.IsSelfClosure (F.lim-at z 2) → F.BadPair (F.first (F.lim-at z 2)) →
  (G : E.Goodᵁ z) → ShapedInitials G → ⊥
reject-limit-initial (E.lim f) F.is-limit branch bad (E.gl G step) shapes =
  reject-self-initial (f 2) branch bad (G 2) (shapes 2)

no-good-with-shaped-initials : ¬ GoodWithShapedInitials F.whole
no-good-with-shaped-initials (G , shapes) = reject-limit-initial F.whole
  F.whole-is-limit F.branch-is-self-closure F.actual-bad-pair G shapes

no-original-good-with-shaped-initials : ¬ GoodWithShapedInitials (E.rdZ Original.ψ₀Λ)
no-original-good-with-shaped-initials certificate = no-good-with-shaped-initials
  (subst GoodWithShapedInitials (sym F.whole-origin) certificate)
```

**只否定什么。** 原程序不能满足本轮指定的“实际反馈初值具有
`Goodᵁ` 计值及原 Shape”闭包。路径起点是真正的原闭项；源合法性是
已有 `Legal-Λ`，没有假定未知的合法闭项或外部环境。子合同自身的
非空实例见 `zero-initial-ŝ` / `zero-initial-ĉ`，不是自相矛盾的接口。

这条否定不声称原反馈没有 `Lgl`，不声称所有计值证书均不可能，
也不是原闭项值低于 EBO 的定理。失败来自原 Shape 的额外零支脊柱
约束。若按作者本轮约定把这项 Shape 闭包作为候选的门槛，这条接线
由定理否定；换形状判据或改原定义不由本篇自动授权。

`no-original-shape-representatives` 还排除了原 `gŝ` 允许的逃口：给初值
挑一个结构互模拟的代表，再只要求代表有 Shape。有限头的反例在结构
互模拟下保持。这里不排除仅序数值相等、但基本列不同的改写。

最直接的主定理是 `no-original-good-with-shaped-initials`：原闭项没有
同时满足原 `Goodᵁ` 与弱初值 Shape 条件的联合证书。它只用原第 2 支
闭包的 `gŝ` 初始链点，保留原 l₀ : forceᵁ seed G₀ ≅ ys 0 的自由，
没有要求所有输出字面相等或后续高层链点都有 Shape。因此不是仅仅
“还没有写出 Env t”：本轮指定的这项必要条件已经被实际运行否定。
