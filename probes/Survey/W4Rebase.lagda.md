# W4 上的换基：在塔上是折叠的一行，过不了读回

形状与保持两档，无前提；没有值定理。换基（分支下标 d 换成 c′ + d，第十五次审查称 "换参数"；即台账 V149、V153 在 W4 上的重新得到）在塔上有字面路径，落成折叠的一行已在候选 W6 上编译；孩子族对右加法的字面单调被 "规范 Ω 树的读回" 与 "左接层号" 保持，被折叠破坏（规范实例上的否定）。不否定：别的取得证据的手段；W4 的值。模块原件是留档附件，用 `scripts/w4rebase/materialize.py` 抄成实验目录再编译。[审查](Reports-2026-11-25/RR15-第十五次独立审查.md) · [KQ](Reports-2026-11-25/KQ-沿层号路径的字面单调.md) · [W6](Reports-2026-11-25/W6-依赖分支与换参数.md) · 对应表在 [LOG](../LOG.md) 11-25 "更正：换参数就是换基"

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4Rebase where

open import Data.Nat.Base using (ℕ)
open import Data.Empty using (⊥)
open import W4Block
open import W4Ops
import R15Mono
import R15Steer
import KQBlock as Q
import KQLev
import KQOut
import KQOutNeg
import W6Shape
import W6TraceZ
import W6VsW5
```

现行 W4 上（块与折叠都没有改）。塔的孩子族对右加法有字面路径；把塔型层号的孩子族换成 d ↦ h (c′ + d) 之后，现行折叠朝孩子 c′ 里的层折规范 Ω 树，每个分支逐字是孩子 c′ + d 里沿字面路径的折叠（`steer₄`，`refl`）。

```agda
rebase-path : (n : ℕ) (c d : Tr (tw n)) → R15Mono.hN n c ≤ R15Mono.hN n (c + d)
rebase-path = R15Mono.tw-mono

steer₄ = R15Steer.Steer.steer-node
```

保持（在把 `_⊕_` 改成对左参数分情形的块 `KQBlock` 上；`RMono k h` 是 "对一切 c d，`h c` 到 `h (c + d)` 有只走 ℕ 极限第 0 个成员的路径"）。

```agda
rmono-tw : (n : ℕ) → KQLev.RMono (Q.tw n) (KQLev.hN n)
rmono-tw = KQLev.tw-RMono

rmono-read : (k : Q.L) (h : Q.Tr k → Q.L) → KQLev.RMono k h → KQLev.RMono k (λ c → KQLev.Ω̂ (h c))
rmono-read = KQLev.Ω̂-RMono

rmono-left : (a k : Q.L) (h : Q.Tr k → Q.L) → KQLev.RMono k h → KQLev.RMono k (λ c → a Q.⊕ h c)
rmono-left = KQLev.⊕-RMono
```

两条否定，都在规范实例上。规范 Ω 树的读回对层号的序不单调（ω 的第 1 个成员）；现行折叠朝私有层的输出读回以后，孩子 1 上分支 0 与分支 1 之间没有路径。原因都是累加：后一项出现在 "前缀 ⊕ 它" 的位置上。累加之前的单项是字面单调的（`single₀`、`single`）。

```agda
no-order : KQLev.lev (Q.suc Q.zero) Q.⊑ KQLev.lev KQLev.ω → ⊥
no-order = KQLev.no-lim-member

no-fold : KQOutNeg.A ⊑ KQOutNeg.Bt → ⊥
no-fold = KQOutNeg.no-01

single₀ = KQOut.st-sum
single  = KQOut.sumD
```

候选 W6（依赖分支构造子、证书的可选单调字段；不替换 W4）。换基是原层号上折叠的一行（`steer₆`，`refl`）；真实运行里候选 W5 在第 ω 层回退的一处（`back₅`），W6 走这一行；W6 仍然回退的一处在读回出来的层号上，那里证书没有证据（`cert₆`、`back₆`）。

```agda
steer₆ = W6Shape.Steer.steer-node
back₅  = W6VsW5.fallback-ω₅
cert₆  = W6TraceZ.cert-none
back₆  = W6TraceZ.fallback-Z
```

范围。`steer₄`、`steer₆` 只说折叠的形状，换基后那一族分支与全体分支同值要 "c′ + d 在孩子里共尾"，没有证。`rmono-*` 在改过的块上，那里值的模块没有检查。`back₆` 是 "仍然回退的一处"，是不是第一处是判断。翻译账：理由全在树侧（分支层低于目标时保留结点的一种不判定的实现），不读记号；属于 "加法代替比较" 一类（台账 V158、V160）。
