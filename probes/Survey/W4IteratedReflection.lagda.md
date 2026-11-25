# 新的原记号初段与 W4 反射理论

第四层。对 θ=(ω^ω)^ω，真实完整塔分别接收 g(θ·n) 的地址，合在一起接收 g(θ·ω) 的地址。由此可把一个只用原记号定义的理论同树侧反射比较。[原记号端点 X](W4OriginalIteratedBound.lagda.md) · [反射进程的定义及文献假设](W4ReflectionStages.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4IteratedReflection where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Maybe.Base using (Maybe)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; s≼s)
import B20StandardInside as Std
import Survey.W4RoomDerivative as G
import Survey.W4IteratedLiftValue as V
import Survey.W4ReturnRendezvous as T
import Survey.W4ReflectionStages as S
open import Survey.W4ReflectionFixed using (loosen)
import Survey.W4PTOAddresses as A
import Survey.W4PTOOrderMap as M
import Survey.W4OriginalThirdIteration as I
import Survey.W4OriginalVeblenRows as R
import Survey.W4IteratedLiftOrdinal as O
import Survey.W4RouteTests as Target
import B18Product as Mul
open import OCF.Lean.YiRefTw2 using (Rt)

source-budget : I.walk (Rt R.d-h) (O.width Mul.· L.ωᶜ) ≼ Target.Y
source-budget = ≼-trans {b = V.bound} (I.original (O.width Mul.· L.ωᶜ)) V.whole

stage = λ n → G.g (V.index n)
at-root : V.bound ≡ L.lim stage
at-root = refl
paid : ∀ n → L.suc (stage n) ≼ T.tower (S.host n)
paid n = ≼-trans {b = L.suc (Std.std (suc (suc (suc n))))} (s≼s (V.paid n))
  (S.physical (suc (suc n)))

map-address : A.Node → Maybe S.SumNode
map-address = S.assemble-map λ n → M.address {x = stage n} {y = T.tower (S.host n)}
  (loosen {a = stage n} {b = T.tower (S.host n)} (paid n))
```

**经典纸面证明。** 令 $I_{<X}$ 为严格低于 X 的全部原可数标准项组成的递归线序。在 ACA₀ 上，按每个原标准项 $b<X$ 分别加入 $\mathrm{WO}(I_{<b})$，得仅用原记号定义的理论 $T_X$。标准形比较可判定，$I_{<b}$ 的序型为 $|b|$。任一证明只用有限条公理，取其中最大的 $b$ 即可涵盖其余有限初段，所需的有限初段识别也可用先前的原始递归项表示在 ACA₀ 中验证。对单良序公理使用 PTO 公式得 $|T_X|=\sup_{b<X}\varepsilon^+(|b|)=|X|$。最后等式用到 $|X|=I_3(D,\omega^{\omega^2+1})$ 是 φ₃ 值，因而是 ε 数的极限，且原初段各项的值穷尽它的所有严格前驱。[原初段理论的同一计算](EboPTOSegments.lagda.md) · [单公理公式](W4PTOTowerTheory.lagda.md)

置 $v=\theta\cdot\omega$。沿 $g(v)$ 的有效地址序在 ACA₀ 上迭代 Π¹₁ 反射，得 $S(v)$。Pakhomov–Walsh 定理 1.5 与已证的 $\varepsilon_{g(v)}=g(v)$ 给 $|S(v)|=g(v)$。于是 $|T_X|\le |S(v)|\le Y$。在 $\mathsf{ACA}_0$ 加同一条真 Σ¹₁ 辅助句后，还有
\[
 \mathrm{RFN}(T^{\mathrm W})\;\longrightarrow\;
 \mathrm{RFN}(S(v))\;\longrightarrow\;
 \mathrm{RFN}(T_X).
\]
第一步使用 `at-root`、`map-address`。首票进入分支 n，保留原首键决定和序分量，映到第 n+4 座完整塔。塔理论的反射统一给出这些分量良序。对 $S(v)$ 的可证良序，辅助句按证明码选到其指标地址序的嵌入，故由 Walsh 引理 3.6 得第一步。对第二步，每个 $T_X$ 可证良序的序型都严格低于 $|T_X|$（附加一个最大元仍可证良序）。由于 $|T_X|\le |S(v)|$，它可嵌入某个 $S(v)$ 可证良序。按证明码一次选择这些递归线序的证明码和相应嵌入，所得真 Σ¹₁ 句可并入前一句，由 $\mathrm{RFN}(S(v))$ 及同一引理得结论。这些辅助句的外部真值分别来自两套理论的独立定值及上文的树值比较；此处拿到的原理论是 $T_X$，整套 EBO 理论 $T^{\mathrm R}$ 的比较仍待证明。[Pakhomov–Walsh，定理 1.5](https://arxiv.org/pdf/1805.02095#page=2) · [Walsh，引理 3.6](https://arxiv.org/pdf/2209.09765#page=12)
