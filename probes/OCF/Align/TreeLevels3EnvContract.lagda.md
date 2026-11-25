# 第三轮：原程序的实际反馈 Shape 必要条件

**第 4 层共享接口。** 作者本轮要求原候选的实际运行生成可入环境，
并让回灌输出满足第二轮的 Shape。这里仅固定其中一个必要子合同：
沿原数据树的后继与 ℕ 分支到达的闭包，其初始反馈输出须能计值，
计值结果须有原 Shape。完整的 Env t 还要包含子项与后续 ψ / 回灌的
环境保持；本篇没有把这个必要子合同冒充完整 Env。

`SeedOf` 是原 `Zᵁ` 上的实际路径，不是任意 raw 对象列表。
它不任选尚未被反馈取到的守卫分支，也不重写原树或折叠。
`ŝ` 的初值与 `ĉ` 的低输出初值均被原 `Goodᵁ` 的计值规则实际消费。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevels3EnvContract where

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Unit using (⊤; tt)
import OCF.Free.Level as F
open import OCF.Align.NoKCertEval using (Zᵁ; zero; suc; lim; ŝ; ĉ; Goodᵁ; forceᵁ; gz)
import OCF.Align.NoKCertEval as E
open import OCF.Align.TreeLevelsO3Shape using (Shape; generated-shape; idle)

data SeedOf (seed : Zᵁ) : Zᵁ → Set where
  initial-ŝ : ∀ {c g} → SeedOf seed (ŝ c seed g)
  initial-ĉ : ∀ {c z zg g} → SeedOf seed (ĉ c z zg seed g)
  in-suc : ∀ {x} → SeedOf seed x → SeedOf seed (suc x)
  in-lim : ∀ {f} n → SeedOf seed (f n) → SeedOf seed (lim f)
  in-ŝ-initial : ∀ {c x g} → SeedOf seed x → SeedOf seed (ŝ c x g)
  in-ĉ-initial : ∀ {c z zg x g} → SeedOf seed x → SeedOf seed (ĉ c z zg x g)

FeedbackShapeClosure : Zᵁ → Set
FeedbackShapeClosure program = ∀ {seed} → SeedOf seed program →
  Σ (Goodᵁ seed) (λ G → Shape (forceᵁ seed G))

zero-initial-ŝ : ∀ c g → FeedbackShapeClosure (ŝ c zero g)
zero-initial-ŝ c g initial-ŝ = gz , generated-shape idle
zero-initial-ŝ c g (in-ŝ-initial ())

zero-initial-ĉ : ∀ c z zg g → FeedbackShapeClosure (ĉ c z zg zero g)
zero-initial-ĉ c z zg g initial-ĉ = gz , generated-shape idle
zero-initial-ĉ c z zg g (in-ĉ-initial ())

-- 原 gŝ 允许把初值换成一个结构互模拟的 ys 代表。
FeedbackShapeRepresentatives : Zᵁ → Set
FeedbackShapeRepresentatives program = ∀ {seed} → SeedOf seed program →
  Σ (Goodᵁ seed) (λ G → Σ (F.Ordᶜ F.zero)
    (λ y → (forceᵁ seed G F.≅ y) × Shape y))

zero-representative-ŝ : ∀ c g → FeedbackShapeRepresentatives (ŝ c zero g)
zero-representative-ŝ c g initial-ŝ = gz , F.zero , F.z≅ , generated-shape idle
zero-representative-ŝ c g (in-ŝ-initial ())

-- 更直接地约束原计值证书：只要求普通分支到达的 gŝ 的首链点有 Shape。
-- 没有对后续链点、高层 ĉ 或所有回灌另加更强要求。
ShapedInitials : ∀ {z} → Goodᵁ z → Set
ShapedInitials E.gz = ⊤
ShapedInitials (E.gs G) = ShapedInitials G
ShapedInitials (E.gl G step) = ∀ n → ShapedInitials (G n)
ShapedInitials (E.gŝ ys hy dy G₀ l₀ Gg lE m₀ mo) = Shape (ys 0)
ShapedInitials (E.gĉ ηs dy l₀ lE Go₀ Go m₀ mo) = ⊤

zero-shaped-initials : ShapedInitials E.gz
zero-shaped-initials = tt

GoodWithShapedInitials : Zᵁ → Set
GoodWithShapedInitials z = Σ (Goodᵁ z) (λ G → ShapedInitials G)

zero-good-with-shaped-initials : GoodWithShapedInitials zero
zero-good-with-shaped-initials = gz , tt
```

这个合同没有假定任意下标可比，也没有把手工填表实例当作原运行。
要否定原候选的这一必要子合同，必须给实际闭项中的 `SeedOf` 见证，
再排除该实际种子的联合计值 / Shape 证书。只否定任意 raw 树不够。

**可满足性。** 初值为零的 `ŝ`、`ĉ` 对这项子合同有直接实例
`zero-initial-ŝ`、`zero-initial-ĉ`；这不说明原高闭项满足它。若实际反例成立，
它排除的是本轮指定的 Shape 环境闭包，不是所有可能的合法性判据。

`ShapedInitials` 直接读取原 `Goodᵁ` 证书，只要求普通 ℕ 分支到达的
`gŝ` 初始链点 ys 0 有 Shape；后续链点和高层 `gĉ` 都不加要求。
这比全域环境/反馈闭包更弱。`zero-good-with-shaped-initials` 给联合
证书的实际实例，避免把这个条件本身矛盾当作原程序反例。
