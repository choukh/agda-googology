# 第三轮：原 Λ 闭项的实际反馈种子与指定 Shape

本篇只检查原 `LevelNoKFold.ψ₀Λ`，不换折叠或计值规则。
先沿其实际 ℕ 极限第 2 支到 `oŝ`，再取这个闭包的实际初始种子。
选择器是全函数，但另用构造子见证证明这些位置确实命中，不依赖
默认零值。有限头观察不把整条基本列当作记号验收。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevels3FeedbackShape where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.Product using (Σ)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.LevelNoKFold as Original
import OCF.Align.NoKCertEval as E
import OCF.Free.Level as F
open import OCF.Align.TreeLevelsO3Shape using (Shape)
open import OCF.Align.TreeLevels3FeedbackSpine public

-- 对外封住具体闭项，后续证明只使用下面有限的头观察。
opaque
  whole : E.Zᵁ
  whole = E.rdZ Original.ψ₀Λ

  whole-origin : whole ≡ E.rdZ Original.ψ₀Λ
  whole-origin = refl

actual-branch : E.Zᵁ
actual-branch = lim-at whole 2

actual-seed : E.Zᵁ
actual-seed = first actual-branch

opaque
  unfolding whole

  whole-head : is-limit? whole ≡ true
  whole-head = refl

  branch-head : is-self-closure? actual-branch ≡ true
  branch-head = refl

  seed-head : is-limit? actual-seed ≡ true
  seed-head = refl

  seed-zero-head : is-limit? (lim-at actual-seed 0) ≡ true
  seed-zero-head = refl

  seed-one-head : is-limit? (lim-at actual-seed 1) ≡ true
  seed-one-head = refl

  seed-zero-zero-head : is-zero? (lim-at (lim-at actual-seed 0) 0) ≡ true
  seed-zero-zero-head = refl

  seed-one-zero-head : is-one? (lim-at (lim-at actual-seed 1) 0) ≡ true
  seed-one-zero-head = refl

whole-is-limit : IsLimit whole
whole-is-limit = reflect-limit whole whole-head

branch-is-self-closure : IsSelfClosure actual-branch
branch-is-self-closure = reflect-self-closure actual-branch branch-head

actual-bad-pair : BadPair actual-seed
actual-bad-pair = bad-pair
  (reflect-limit actual-seed seed-head)
  (reflect-limit (lim-at actual-seed 0) seed-zero-head)
  (reflect-limit (lim-at actual-seed 1) seed-one-head)
  (reflect-zero (lim-at (lim-at actual-seed 0) 0) seed-zero-zero-head)
  (reflect-one (lim-at (lim-at actual-seed 1) 0) seed-one-zero-head)

no-shape-realisation : ¬ (Σ (E.Goodᵁ actual-seed) (λ G → Shape (E.forceᵁ actual-seed G)))
no-shape-realisation = no-bad-pair-shape actual-seed actual-bad-pair

no-shape-representative : (G : E.Goodᵁ actual-seed) (y : E.Ord₀) →
  E.forceᵁ actual-seed G F.≅ y → Shape y → ⊥
no-shape-representative = no-bad-pair-shape-bisim actual-seed actual-bad-pair
```

`whole-is-limit` 与 `branch-is-self-closure` 认证实际路径的两个构造子。
`actual-bad-pair` 只观察该种子、前两支及这两支的第零项：它们的
值若存在，前两支分别是第零项为 0 和 1 的 ℕ 极限。
`TreeLevels3FeedbackSpine.shape→spine` 要求任何指定 `Shape` 的相邻
极限分支按零支脊柱相接；上述两支不能这样相接。

**范围。** `no-shape-realisation` 排除这个实际初始反馈种子的联合
`Goodᵁ` / `Shape` 证书；不预设整棵原程序已经可以计值，不以矛盾
前提作实例，也不否定字面 `Lgl` 或其他合法性标准。
`no-shape-representative` 进一步排除同在第 0 层、与该计值输出结构
互模拟的任何 `Shape` 代表，覆盖 `Goodᵁ.gŝ` 允许以 `≅` 选链点的
这一个逃口；没有排除只要求序数值相等的其他代表。

**可满足性。** `actual-bad-pair` 已在原闭项上实填全部有限头条件，
不是把某个任意 raw 对象塞进接口。`Goodᵁ` 与 `Shape` 的联合要求
在零上可由 E.gz , shaped idle refl 实填；本轮共享合同还应分别
核对实际路径和合同自身的实例。这里不证明也不否定
Goodᵁ actual-seed 单独是否存在：`no-shape-realisation` 没有前提，
其目标正是排除共同提供计值与指定形状的证书，不把未知的 `Goodᵁ`
当作已满足的假设。

**编译记录。** 以下最终命令均退出 0，各次只运行一个 Agda，堆上限 6G：

```text
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/TreeLevels3FeedbackSpine.lagda.md +RTS -M6G -RTS
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/TreeLevels3FeedbackShape.lagda.md +RTS -M6G -RTS
```

首次把具体 `whole` 全部透明展开、以 `refl` 比较整条极限函数的版本
退出 251。报错原文如下；它是堆墙，不是类型错误或数学否定：

```text
agda: Heap exhausted;
agda: Current maximum heap size is 6442450944 bytes (6144 MB).
agda: Use `+RTS -M<size>' to increase it.
```

最终版本把一般证明放在 `TreeLevels3FeedbackSpine`，具体闭项放在 opaque 中，只导出
七个有限布尔头观察及其反射结果，不改原树、折叠或合法性定义。
本篇没有公设、洞、停机或正性指示，没有 Funext、UIP 或 trustMe。
