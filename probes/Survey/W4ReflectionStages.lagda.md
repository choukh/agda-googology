# W4 可接收的超限反射理论

第四层。h 枚举参照函数 H 的正不动点，g 枚举 h 的不动点。对任意指标 a，g(a) 既固定 ε 数枚举，也固定 ζ 数枚举。由此可按 Pakhomov–Walsh 定理为这些界逐一指定具有精确 PTO 的迭代反射理论。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4ReflectionStages where

open import Data.Nat.Base using (ℕ; suc)
open import OCF.Align.Value using (_≼_; ≼-trans)
import OCF.Align.Level as L
import B20StandardGoal as Real
import Survey.W4ReturnRendezvous as Call
import Survey.W4RoomDerivative as D
open import Survey.W4ReflectionFixed using (loosen; epsilon-index; zeta-index; address-index)
```

对每个**有效**指标 a，给 g(a) 的地址序加一个最末点，沿该点的严格下锥在 ACA₀ 上迭代 Π¹₁ 反射，记所得理论为 S(a)。地址定理和 address-index 给出下锥序型 ω^g(a)=g(a)。为满足 Pakhomov–Walsh 对记号的要求，以自然数键表作地址，域元素附确定性验收机唯一的首次接受记录。域可有界核验，先按键表的 KB 序比较，相等时按整个编码的自然数序打破平局。用有界的首异位置就能在 EA 中证明线性。标准模型中每个键表的有效记录唯一，故次键不会改变序型。定理 1.5 给出 **|S(a)|=ε_{g(a)}=g(a)**。反射进程只使用参照函数 h、g 及固定基理论；树侧的工作是下面的具体嵌入。[地址序型](W4PTOAddresses.lagda.md) · [Pakhomov–Walsh，定理 1.5 与 §2.2](https://arxiv.org/pdf/1805.02095#page=2)

```agda
import Data.Nat.Properties as Nat
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product using (_,_; _×_)
import B20StandardInside as Std
import Survey.W4PTOAddresses as A
import Survey.W4PTOOrderMap as Map
import Survey.W4NextLiftValue as V

-- 从独立标准塔转到上一轮理论真正使用的完整塔公理。
opaque
  physical : ∀ m → L.suc (Std.std (suc m)) ≼ Call.tower (suc (suc m))
  physical m = ≼-trans {a = L.suc (Std.std (suc m))} {b = Call.unit (suc m) 0} {c = Call.tower (suc (suc m))}
    (Real.At.child m 0 (suc m) Nat.≤-refl) (Call.within (suc m) 0)

u = V.exponent
stage = λ n → D.g (u L.+ D.index n)
host = λ n → suc (suc (suc (suc n)))

opaque
  base-cap : D.g u ≼ Call.tower 3
  base-cap = ≼-trans {a = D.g u} {b = Std.std 2} {c = Call.tower 3} V.second
    (loosen {a = Std.std 2} {b = Call.tower 3} (physical 1))
  installed : ∀ n → stage n ≼ Call.tower (host n)
  installed n = ≼-trans {a = stage n} {b = Std.std (suc (suc (suc n)))} {c = Call.tower (host n)} (V.after n)
    (loosen {a = Std.std (suc (suc (suc n)))} {b = Call.tower (host n)} (physical (suc (suc n))))

base-map : A.Node → Maybe A.Node
base-map = Map.address {x = D.g u} {y = Call.tower 3} base-cap

-- 源的第一个自然数极限是阶段号。保留整个首键作为和序的分量号。
SumNode = ℕ × A.Node
assemble-map : (ℕ → A.Node → Maybe A.Node) → A.Node → Maybe SumNode
assemble-map f nothing = just (0 , nothing)
assemble-map f (just (((n ∷ ns) , i) ∷ ps)) with f n (just ((ns , i) ∷ ps))
... | nothing = nothing
... | just z = just (A.key ((n ∷ ns) , i) , z)
assemble-map f (just _) = nothing

family-map : A.Node → Maybe SumNode
family-map = assemble-map λ n → Map.address {x = stage n} {y = Call.tower (host n)} (installed n)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

boundary : V.bound ≡ L.lim stage
boundary = refl
```

令 u=ω^ω，v=u+ω²，aₙ=u+ω·n。以下区分一座塔公理与对塔理论的整体反射。

* 第 3 座完整塔的地址公理已经接收 S(u) 的指标良序。base-map 直接把 A_{g(u)} 的任意合法地址保序送入 A_{t₃}。这一步在 ACA₀ 上只用该公理及明确的真算术求值事实。
* 对全段 v，源 g(v) 的根是以 g(aₙ) 为孩子的极限。其第一张票的极限路径必以某个 n 起头。按第一张完整票的自然数键 k 排列分量。去掉已进入的根分支 n，余下的首票及其后续票是 g(aₙ) 的一个非空合法地址，installed n 将它送入第 n+4 座完整塔。family-map 对相同 k 使用同一嵌入，对不同 k 保留大小。零分量接收独立最小元。所得是到一个递归序数和的单一可执行嵌入。无效键的分量可取任意固定完整塔。ACA₀ 证明，若各分量良序，沿自然数作的和也良序，因为降链的分量号最终恒定。
* RFN(Tᵂ) 给出所有完整塔公理的真实性。每个 n 的公理都有统一的一行公理证明，故在 ACA₀ 中可对 n 全称化。由此结合 family-map 的真算术性质导出 WO(A_{g(v)})。这个全域结论目前以 RFN(Tᵂ) 为前提；单座塔的接收仅在上述已标定的地址上使用。

**从良序到反射（经典纸面证明）。** 对任何上面固定的有效 a，若原始递归线序 L 有 S(a) 对 WF(L) 的证明，则 otp(L)<|S(a)|=g(a)。严格号来自可在 S(a) 中再证明 L+1 良序。故 L 可保序嵌入 A_{g(a)}。把这些嵌入按证明码和序的编码选成一个集合；“存在这样一个集合，且其每个适用分量都是指定的嵌入”是一个真 Σ¹₁ 句。真值的依据是反射进程的独立 PTO 计算。对 u、v 和可数个 aₙ，可再编码在同一个集合中。ACA₀ 加这一辅助句，从 WO(A_{g(a)}) 可推出每个 S(a) 可证良基的原始递归线序确实良基。Walsh 引理 3.6 随即给出 RFN(S(a))。[Walsh，引理 3.6 与证明](https://arxiv.org/pdf/2209.09765#page=12)

于是存在同一条真 Σ¹₁ 辅助句 σ（可合取上述已证真的算术求值性质），满足
$$
\begin{aligned}
\mathsf{ACA}_0+\sigma+\mathrm{WO}(A_{t_3})&\vdash \mathrm{RFN}(S(u)),\\
\mathsf{ACA}_0+\sigma&\vdash\mathrm{RFN}(T^{\mathrm W})\to\mathrm{RFN}(S(v)).
\end{aligned}
$$
把 a 换成 aₙ 时，对各个固定 n 分别只需第 n+4 塔的公理。这里的 σ 量化一族嵌入，是解析辅助句；只有 W4 地址之间的映射已给成递归程序。这些结论接收了 PTO 分别为 g(u)、g(v) 的整套反射进程。它们与原记号理论 Tᴿ 的全体公理还有距离待定。

同一证明也给全 EBO 的一个单一目标。取原可数标准项全序 I，由 |Tᴿ|=otp(I) 可以独立在记号侧构造真 Σ¹₁ 句 τ，使 ACA₀+τ 证明 WO(I)→RFN(Tᴿ)。反之，RFN(Tᴿ) 给所有严格塔初段 Iₖ 的良序性；任一假想降链的首项属于一个 Iₖ，此后各项仍在其中。这里仅用可合入 τ 的真算术事实，即各初段的塔公理有统一证明且它们穷尽 I。因此在该基础上 RFN(Tᴿ)↔WO(I)。若能将 I 的假想降链统一变为某个从 RFN(Tᵂ) 可证良序的地址和中的降链，就会得到 R≤Y。此处已实现的整段是 g(v)，尚无针对全部 I 的实际转换。[原记号初段与精确序型](EboPTOSegments.lagda.md) · [整树比较的两个方向](W4PTOTowerTheory.lagda.md)

首座完整塔还有一个精确的实例。其值 t₁ 满足 h(t₁)=t₁。由 enum≤h 和 zeta≤h，结合两个枚举都支配指标，得到 ε_{t₁}=ζ_{t₁}=t₁，特别是 ω^{t₁}=t₁。于是沿 A_{t₁} 迭代 Π¹₁ 反射的理论 U₁ 满足 **|U₁|=t₁**。上面同一族嵌入的证明给出 ACA₀+σ+WO(A_{t₁}) ⊢ RFN(U₁)，可在原 σ 中再编码这一族。反向，对 A_{t₁} 的每个元素 p，其严格初段的序型小于 |U₁|，故存在一个 U₁ 可证良序的递归线序以及该初段到其中的嵌入。把这些证明码与嵌入按 p 编成一个真 Σ¹₁ 辅助句。RFN(U₁) 于是保证所有这些初段良序，舍去假想降链的第一项即排除整序的降链。因此在 ACA₀ 加上述共同辅助句后，**WO(A_{t₁}) ↔ RFN(U₁)**。这一对接使用整座实际塔，原记号对 t₁ 的上界仍待证明。[首塔的三步反馈及不动点](W4NextBoundFirst.lagda.md) · [两种枚举的比较](W4ReflectionFixed.lagda.md)
