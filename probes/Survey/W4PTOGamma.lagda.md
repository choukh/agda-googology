# 在 W4 真实返回中实现强临界序数的闭包

第四层。Agda 将整个参数族及一个共同严格上界接到 W4 既有的三级返回，终点取原 Λ 闭项。经典序型推论见文末。
以下 $D_i$ 为本地第 $i$ 个塌缩。用 $O(p)=D_0D_2p$ 把阶段送回可数标准形。[带有限支撑的塌缩](EboPTOGamma.lagda.md) · [W4 的三级返回](W4PTOFinite.lagda.md#第二个有限理论的塔项)

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module Survey.W4PTOGamma where

open import OCF.Align.EboLeanDef using (HC)
open import OCF.Align.EboLeanBase using (c∷; c[])
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Lean.YiRefTw2 using (Rt)
open import OCF.Lean.YiCFMono using (mono<ⁿ)
open import OCF.Align.Value using (_≼_; ≼-trans)
import OCF.Align.Level as L
open import Survey.EboPTOPadding using (Stage; p; low; out; out<; out-normal)
open import Survey.EboPTOGamma using (capStage)
import Survey.EboPTOFinite as B
import Survey.W4PTOFinite as Actual
import B12Terminal as Runs
import B12ActualSlots as Slots
open import WKShape using (lvl3)
open import W4Fold using (EBOᶜ)
open import WVOne using (read)

opaque
  stage-h : (s : Stage) → HC (out (p s))
  stage-h s = hc (out-normal s) (c∷ c[])

stage-in-two : (s : Stage) → L.suc (Rt (stage-h s)) ≼ Rt (B.tower-h 2 2)
stage-in-two s = mono<ⁿ (out-normal s) (B.nf-collapsed 2 2) (c∷ c[])
  (stage-h s) (B.tower-h 2 2) (out< (low s))

cap-in-run : (r : Runs.Run lvl3) → Slots.Covered r →
  L.suc (Rt (stage-h capStage)) ≼ read (Runs.value r)
cap-in-run r cv = ≼-trans {b = Rt (B.tower-h 2 2)} (stage-in-two capStage) (Actual.two-in-run r cv)

cap-in-terminal : L.suc (Rt (stage-h capStage)) ≼ read EBOᶜ
cap-in-terminal = ≼-trans {b = Rt (B.tower-h 2 2)} (stage-in-two capStage) Actual.two-in-terminal
```

## 整个区间的序型

**经典纸面证明。** 令 $K$ 为 `capStage` 的参数，$S$ 为所有严格低于 $K$ 且具有 `Stage` 证书的项，按原记号的序比较。以项为载体，对每个项取一份证书即可。$p\mapsto O(p)$ 严格保序，像严格低于可数标准形 $O(K)$，故 $S$ 是可数良序。写 $\zeta=\mathrm{otp}(S)$。给定 $s\in S$，令 $X_s$ 为严格低于 $O(s)$ 的全部可数标准形。上一轮已证明它的序型为 $\rho(\mathrm{Rt}(O(s)))$。[可数初段的序型](EboPTOFinite.lagda.md)

对 $1+2\times S^2+X_s$ 取 `θ`。前两坐标的字典序由 `pair-first`、`pair-second` 实现，其余比较由两行与常量的比较实现。两条塌缩律分别为 `conditional-order` 和 `support-up`，输出仍在 $S$ 由 `bounded` 给出。Freund 定理 3.5 因此给出 $\Gamma_{\mathrm{otp}(X_s)}\le\zeta$。设 $s$ 在 $S$ 中的序号为 $\xi$，则 $O$ 将它的严格初段嵌入 $X_s$，故 $\Gamma_\xi\le\zeta$。每个 $s$ 的空询问给出严格较大的阶段且仍低于 $K$，所以 $\zeta$ 是非零极限。由 $\Gamma$ 正规且 $\Gamma_\eta\ge\eta$，得到 $\Gamma_\zeta=\zeta$。[Freund，定义 1.3、定理 3.5](https://arxiv.org/pdf/1906.07448) · [两条律及共同上界](EboPTOGamma.lagda.md)

置 $b=|ID_1|$。空阶段的 $O(0)=D_0D_2 0$ 是对应 $b$ 的本地整行。`positive-seed` 位于 $S$ 中，其像严格大于 $O(0)$，所以这个阶段的 $X_s$ 已含整个旧初段及其端点，给出 $b<\zeta$。从而，记 $\lambda_b$ 为严格大于 $b$ 的第一个 $\Gamma$ 不动点，则对每个有槽覆盖证书的 W4 三级运行 $r$ 都有
\[
 \lambda_b\le\zeta\le\rho(\mathrm{Rt}(O(K)))<
 \rho(\mathrm{Rt}(D_0D_2^2 0))\le\rho(\mathrm{read}(\mathrm{value}(r))).
\]
同一不等式适用于 $Y=\mathrm{read}(\mathrm{EBO}^{\mathrm c})$。末尾比较有实际的 $r$，终点证明使用第 2 号规范有限运行。[实际实例](W4PTOFinite.lagda.md#第二个有限理论的塔项) · [有限理论对照](EboPTOFinite.lagda.md)

## Rathjen 参数的端点

在 Rathjen 的约定中取 $\Omega=\omega_1$、$\Delta=\varepsilon_{\Omega+1}$，写 $q(\delta)=\psi^{\mathrm R}_0(\Delta+\delta)$。由既有的两种塌缩比较，$q(0)=b$，并且 $b$ 强临界。唯一写成 $b=\Gamma_\iota$。则
\[
 q(\delta)=\Gamma_{\iota+\delta}\quad(\delta<\lambda_b),
 \qquad q(\Omega)=\lambda_b.
\]
这里的第一个不动点是对枚举函数 $\xi\mapsto\Gamma_\xi$ 而言。[Rathjen，定义 10.1、命题 10.3](https://eprints.whiterose.ac.uk/76751/1/Diss.pdf) · [初值比较](W4PTOFinite.lagda.md#rathjen-塌缩中的一个完整参数区间)

**小参数。** 对 $0<\delta<\lambda_b$ 作归纳。生成可数值时只用加法、可数输入的 $\varphi$ 及先前的零下标塌缩。参数小于 $\Delta$ 的塌缩至多为 $b$。其余可用的参数为 $\Delta+\eta$，$\eta<\delta$。故所有这类输出均严格小于强临界序数 $\Gamma_{\iota+\delta}$。对闭包的生成步数归纳可知该序数没有被生成，即得上界。为证下界，先观察 $\eta<\Gamma_{\iota+\eta}$ 对 $\eta<\lambda_b$ 成立。若 $\eta<b$，右端至少为 $b$。若 $b<\eta<\lambda_b$，用 $\eta<\Gamma_\eta$。剩余 $\eta=b$ 时，如 $\Gamma_b>b$ 即已满足，如 $\Gamma_b=b$ 则 $\iota=b>0$，从而 $\Gamma_{\iota+b}>b$。在后继步 $\delta=\eta+1$，归纳假设给出 $\eta<q(\eta)$。命题 10.3(vi) 保证 $\eta$ 在上一阶段闭包中，$\Delta=\varphi_1(\Omega+1)$ 也由种子生成。于是 $\Delta+\eta$ 已能生成，在下一阶段可对它施加零下标塌缩。故 $q(\eta+1)>q(\eta)$，且为强临界序数，得到所需下界。极限步由弱单调性、加法对右变量连续及 $\Gamma$ 的连续性给出。

**不可数端点。** 对 $C^{\mathrm R}_0(\Delta+\Omega)$ 的有限生成步数同时归纳两个断言。每个可数成员都 $<\lambda_b$，而每个落在 $[\Delta,\Delta+\Omega)$ 的成员都形如 $\Delta+\eta$，其中 $\eta<\lambda_b$。加法生成区间内的值时，若右项在区间内，左项必须 $<\Delta$，因而被 $\Delta$ 吸收。若右项 $<\Delta$，则左项必须在区间内，且右项必须可数，两个尾部相加仍 $<\lambda_b$。$\varphi$ 的输出与正下标塌缩均为加法主序数，该区间内唯一可能的此类值是 $\Delta$。$\Phi$ 的输出为不可数基数，区间内没有基数。零下标塌缩要求参数严格小于 $\Delta+\Omega$，故其输出至多为 $b$，或等于某个 $q(\eta)=\Gamma_{\iota+\eta}<\lambda_b$；这里用了尾部归纳断言及 $\lambda_b$ 对加法、$\Gamma$ 在严格初段上的封闭性。生成可数值的加法和 $\varphi$ 也保持该初段。故 $q(\Omega)\le\lambda_b$。反向由弱单调性及 $\sup_{\eta<\lambda_b}\Gamma_{\iota+\eta}=\lambda_b$ 得到。对 $\lambda_b\le\delta\le\Omega$ 再用单调性，前面的上确界与端点同时给出 $q(\delta)=\lambda_b$。因此 $[\Delta,\Delta+\Omega]$ 的每个参数都有精确值，且全部严格低于上述真实返回。[Rathjen，§§9–10](https://eprints.whiterose.ac.uk/76751/1/Diss.pdf)

这一比较使用既有返回中的 $D_0D_2^20$。整个 $ID_2$ 共尾塔的实际覆盖、$\psi^{\mathrm R}_0(\Gamma_{\Omega+1})$ 的覆盖，以及原 EBO 终点的两向比较仍开放。

## 下一层塔项的具体缺口

在同一把 $ID_2$ 标尺上，首座正塔的第 2 个真实单位严格超过深度 2。已有的全局下界见证 $W$ 严格低于深度 3。后一个比较可由 $W$ 所处的原参照分支读出，右端保留本地正规项的值证书。

```agda
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import OCF.Align.EboLeanDef using (T; cof; cω; h0; h1; hω; fsn)
open import OCF.Align.EboLeanBase using (NF; Ctbl)
open import OCF.Align.EboLeanClosure using (cl-fsn-NF; trian-fsn)
open import OCF.Align.EboLeanTrian using (t<)
open import OCF.Align.Value using (≅→≼; s≼s)
open import OCF.Align.TightValBase using (s≼-irrefl)
import B12Omega3Ref as Three
import B12BtboCut as Cut
import B28FFinite as Finite
import B29SFirst as First
import B25AOrbit as Orbit
import B23NDomain as Domain

first-unit : L.suc (Rt (B.tower-h 2 2)) ≼ First.f 2
first-unit = ≼-trans {b = L.suc (Three.at (Cut.finite 3) 1)}
  (s≼s (proj₁ (Actual.id₂-branch 1))) First.floor

child-iso : ∀ {t : T} (h : HC t) → cof t ≡ cω → (y : L.Ordᶜ L.zero) → Rt h L.≅ y →
  ∀ k {s} → fsn t k ≡ s → Σ (HC s) λ hs → Rt hs L.≅ Three.at y k
child-iso (h0 e) w y iso k eq with trans (sym e) w
... | ()
child-iso (h1 e h) w y iso k eq with trans (sym e) w
... | ()
child-iso (hω e f) w (L.lim g) (L.l≅ d) k refl = f k , d k

child-strict : ∀ {t : T} (nt : NF t) (ct : Ctbl t) (h : HC t) (w : cof t ≡ cω) →
  (y : L.Ordᶜ L.zero) → Rt h L.≅ y → ∀ k → L.suc (Three.at y k) ≼ Rt h
child-strict nt ct h w y iso k = ≼-trans {b = L.suc (Rt hs)}
  (s≼s (≅→≼ (L.≅-sym (proj₂ witness))))
  (mono<ⁿ (cl-fsn-NF nt w k) nt ct hs h (t< (trian-fsn nt w k)))
  where
  witness = child-iso h w y iso k refl
  hs = proj₁ witness

child<depth-three : L.suc Domain.child ≼ Rt (B.tower-h 2 3)
child<depth-three = ≼-trans {b = Rt hs}
    (child-strict (B.nf-collapsed 2 3) (c∷ c[]) hs refl (Three.at (Cut.finite 3) 2) (proj₂ witness) 0)
    (OCF.Lean.YiRefTw2.tree-≼ refl hs (B.tower-h 2 3))
  where
  witness = child-iso (B.row-h 2) refl (Cut.finite 3) (Finite.Fin.same 3 (B.row-h 2)) 2 (Actual.align-term 2)
  hs = proj₁ witness

old-bound<depth-three : L.suc Orbit.whole ≼ Rt (B.tower-h 2 3)
old-bound<depth-three = ≼-trans {b = L.suc Domain.child} (s≼s Orbit.child) child<depth-three

depth-three-unpaid-by-W : Rt (B.tower-h 2 3) ≼ Orbit.whole → ⊥
depth-three-unpaid-by-W h = s≼-irrefl Orbit.whole (≼-trans {b = Rt (B.tower-h 2 3)} old-bound<depth-three h)
```

取下一塔项的第 0 枝。它从 1 开始反复施加原参照函数 $G$。已知见证 $W$ 甚至严格低于该枝的第二次迭代。对每个深度，以下判据允许分别实现每个有限询问，然后对两个自然数坐标取上确界。

```agda
open import Relation.Binary.PropositionalEquality using (subst)
open import OCF.Align.Value using (≼-refl; ≼l; l≼)
open import WVOne using (𝟏; T₀)
import B13Target as Target
import B14RefAllRows as Rows
import B23RKernel as Kernels
import B24ROrbit as Lower
import B25ABounds as Bounds

small-input : L.suc Lower.omega ≼ Domain.G 𝟏
small-input = ≼-trans {b = Lower.orbit 1} Lower.w₁
  (≼-trans {b = L.lim (λ j → Lower.orbit (suc j))} (≼l 0 (≼-refl _))
    (≼-trans {b = Lower.D} (≅→≼ (L.≅-sym Lower.shape)) Bounds.starts))

second-query : L.suc Orbit.whole ≼ Rows.chain 1 0 2
second-query = ≼-trans {b = L.suc (Domain.G Lower.omega)} (s≼s Orbit.omega)
  (≼-trans {b = Domain.G (L.suc Lower.omega)} (Domain.Growth.next Lower.omega)
    (Kernels.At.monotone 1 0 {L.suc Lower.omega} {Domain.G 𝟏} small-input))

query-in-next : L.suc (Rows.chain 1 0 2) ≼ Rt (B.tower-h 2 3)
query-in-next = ≼-trans {b = L.suc Domain.child} (s≼s (Domain.in-child 1)) child<depth-three

Pieces : ℕ → T₀ → Set
Pieces m y = ∀ n j → Rows.chain m n (suc j) ≼ y

from-pieces : ∀ m y → Pieces m y → Rt (B.tower-h 2 (suc (suc m))) ≼ y
from-pieces m y h = ≼-trans {b = Three.at (Cut.finite 3) (suc m)} (proj₁ (Actual.id₂-branch (suc m)))
  (subst (_≼ y) (sym (Target.row (suc m))) (l≼ each))
  where
  each : ∀ n → L.ψ⁰ (Target.asked (suc m) n) ≼ y
  each n = subst (_≼ y) (Rows.shape m n)
    (≼-trans {b = L.lim (λ j → Rows.chain m n (suc j))} (≅→≼ (Rows.as-chain m n)) (l≼ (h n)))

to-pieces : ∀ m y → Rt (B.tower-h 2 (suc (suc m))) ≼ y → Pieces m y
to-pieces m y h n j = ≼-trans {b = L.lim (λ j′ → Rows.chain m n (suc j′))} (≼l j (≼-refl _))
  (≼-trans {b = Rows.node m n} (≅→≼ (L.≅-sym (Rows.as-chain m n)))
    (≼-trans {b = Three.at (Cut.finite 3) (suc m)} (Three.at-below (Three.at (Cut.finite 3) (suc m)) n)
      (≼-trans {b = Rt (B.tower-h 2 (suc (suc m)))} (proj₂ (Actual.id₂-branch (suc m))) h)))
```
