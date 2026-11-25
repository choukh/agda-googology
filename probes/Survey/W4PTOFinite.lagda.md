# W4 的有限迭代归纳定义初段

第四层，无条件。每座正塔的每个单位重置返回都严格超过首个有限理论对应的整段。实际系数的上确界盖住规则 (48) 的首轮门槛，恰好当它盖住每个正有限理论的每个塔项。
Agda 结论按本地树值陈述。与 $|ID_n|$ 的对照有单列的经典证明。[有限下标](EboPTOFinite.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module Survey.W4PTOFinite where

open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import OCF.Align.EboLeanDef using (natT; 𝟏; HC)
open import OCF.Lean.YiRefTw2 using (Rt; tree-≼)
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans; ≅→≼; ≼-refl; ≼-suc; l≼; ≼l; ⊑→≼)
import OCF.Align.Level as L
import Survey.EboPTOFinite as B
import Survey.W4Rule48 as W
import B26OSparse as Name
import B27Joint as Unit
import B27UEnvelope as Units
import B28FFinite as Finite
import B12BtboCut as Cut
import B12EboRows as Rows

word : ∀ n → natT n ≡ Finite.word n
word zero = refl
word (suc n) = cong (𝟏 ∷_) (word n)

scale : ∀ n → Rt (B.row-h n) ≈ᵛ Cut.finite (suc n)
scale n = ≼-trans {b = Rt h} (tree-≼ eq (B.row-h n) h) (≅→≼ iso) ,
  ≼-trans {b = Rt h} (≅→≼ (L.≅-sym iso)) (tree-≼ (sym eq) h (B.row-h n))
  where
  eq = cong Name.collapse (word (suc n))
  h = subst HC eq (B.row-h n)
  iso = Finite.Fin.same (suc n) h

base : ∀ n j → L.suc (Rt (B.row-h 1)) ≼ Unit.f (suc n) j
base n j = Finite.paid n j (B.row-h 1)

Paid = ∀ n k → Rt (B.tower-h (suc n) k) ≼ Units.U

necessary : W.Start.H.middle ≼ Units.U → Paid
necessary h n k = ≼-trans {b = Rt (B.row-h (suc n))} into-row
  (≼-trans {b = Cut.finite (suc (suc n))} (proj₁ (scale (suc n)))
    (≼-trans {b = W.Start.H.middle} (≼-trans (≼-suc (≼-refl _)) (W.finite-short (suc (suc n)))) h))
  where
  into-row = ≼-trans {b = L.lim (λ i → Rt (B.tower-h (suc n) i))}
    (≼l {f = λ i → Rt (B.tower-h (suc n) i)} k (≼-refl _)) (proj₂ (B.row-sup (suc n)))

sufficient : Paid → W.Start.H.middle ≼ Units.U
sufficient h = ≼-trans {b = Cut.omega-cut} (proj₁ W.first-scale) (l≼ each)
  where
  low : Cut.finite 2 ≼ Units.U
  low = Unit.bound (Cut.finite 2) Units.U Units.component W.paid-two
  one : Cut.finite 1 ≼ Units.U
  one = ≼-trans {b = Cut.finite 2} Rows.epsilon-in-Ω₂ low
  each : ∀ k → Cut.finite k ≼ Units.U
  each zero = ≼-trans {b = Cut.finite 1} (⊑→≼ (Cut.finite 0) (L.Ψ⁰0 (L.natᴵ 1))) one
  each (suc zero) = one
  each (suc (suc n)) = ≼-trans {b = Rt (B.row-h (suc n))} (proj₂ (scale (suc n)))
    (≼-trans {b = L.lim (λ k → Rt (B.tower-h (suc n) k))} (proj₁ (B.row-sup (suc n))) (l≼ (h n)))
```

## Rathjen 塌缩中的一个完整参数区间

**经典纸面证明。** 令 $\Omega=\omega_1$，以上标 BJS 表示 Buchholtz、Jäger 与 Strahm 的单个不可数基数塌缩。令 $\Delta=\varepsilon_{\Omega+1}$，即 $\Omega$ 以上的第一个 ε 不动点。对每个 $\alpha\leq\Delta$ 有
\[
\psi^{\mathrm R}_0(\alpha)=\psi^{\mathrm{BJS}}(\alpha).
\]
对 $\alpha$ 归纳，在该阶段按有限闭包构造步数比较 $C^{\mathrm R}_0(\alpha)\cap\Delta$ 与 $C^{\mathrm{BJS}}(\alpha,0)\cap\Delta$。BJS 的种子 $\Omega$ 在 Rathjen 一边由 $\Phi_0(0)$ 产生。区间内的其余规则如下。加法或 $\varphi$ 的值小于 $\Delta$ 时，两输入均小于 $\Delta$。由于 $\Delta$ 可由从 $\Omega+1$ 开始的有限 $\omega$ 幂迭代取上确界得到，基数仍为 $\aleph_1$，故 $\Phi$ 的值落在这里时只能是 $\Omega$。任何正下标的 Rathjen 塌缩都是严格大于 $\Omega$ 的强临界序数，因而至少为 $\Delta$。剩下的塌缩是对 $\xi<\alpha\leq\Delta$ 施加零下标运算，外层归纳假设识别其值，内层归纳搬运其参数。故两闭包在 $\Delta$ 以下相同。限制到 $\Omega$，再用 Rathjen 命题 10.3(vi) 和 BJS 引理 4(2,8)，得到上式，包括 $\alpha=\Delta$ 的端点。[Rathjen，§10](https://eprints.whiterose.ac.uk/76751/1/Diss.pdf) · [Buchholtz、Jäger、Strahm，§2 定义 3、引理 4](https://home.inf.unibe.ch/thomas.strahm/download/pdf/proof_humboldt_bjs.pdf)

记 $\Gamma$ 为强临界序数的正规枚举函数，$\Xi_0=1$，$\Xi_1=\Omega$。BJS 在引理 4 后计算了 $\psi^{\mathrm{BJS}}$ 直到 $\Omega$ 的值，从而两项分别为 $\Gamma_1$ 和 $\Gamma$ 的第一个不动点。由引理 4(6) 及 $\Omega$ 是种子，两项都严格小于 $\psi_0^{\mathrm R}(\Delta)=\psi^{\mathrm{BJS}}(\Delta)=|ID_1|$。结合 `base`、有限下标的序型比较和塌缩的弱单调性，整个参数区间 $\alpha\leq\Delta$ 的每个 $\psi_0^{\mathrm R}(\alpha)$ 都严格低于每座正塔的每个实际单位重置返回。[BJS，§§1–2](https://home.inf.unibe.ch/thomas.strahm/download/pdf/proof_humboldt_bjs.pdf) · [有限初段的序型](EboPTOFinite.lagda.md)

对下一项已有严格的反向定位。令 $a$ 是本地可数标准形 $\omega=\psi_0(1)$，则 $r=\psi_0(\Omega_a)$ 正规（两次标准形守卫只检查 $0,1$），其树值即 `W.Start.H.middle`。由文献标尺的纸面比较，$F(a)$ 可数，故 $J(F(a))^+<\Omega_{\Omega}=\Xi_2$。于是 $F(\Omega_a)=\psi^{\mathrm R}_{J(F(a))}(0)<\Xi_2$，比较两个已正规的零下标塌缩得到
\[
\sup_{1\leq n<\omega}|ID_n|
 =\rho(\mathrm{Start.H.middle})\leq F(r)<\psi^{\mathrm R}_0(\Xi_2).
\]
等号来自 `scale`、`first-scale` 与有限初段定理，有限序列的头两项已被其余项盖住。因此若在某个 W4 值界中实现文献第 2 项，该界就同时盖住整个首轮门槛。上式比较的是三个标尺，本轮没有取得第 2 项的实际返回见证。[文献翻译](EboPTORank.lagda.md) · [首轮校准](W4Rule48.lagda.md) · [Rathjen，命题 10.3–10.4、引理 12.9](https://eprints.whiterose.ac.uk/76751/1/Diss.pdf)

还可定位第 2 项会使用的一个具体参数。取 $\tau=\psi^{\mathrm R}_{\Omega}(0)$，$\theta=\Gamma_{\Omega+1}$。命题 10.3 给出 $\Omega<\tau<\Omega_2$ 且 $\tau$ 强临界，故 $\theta\leq\tau<\Omega_2$。在 $C^{\mathrm R}_{\Omega}(0)$ 中，种子均小于 $\theta$，没有前阶段塌缩。加法与 $\varphi$ 从小于 $\theta$ 的输入只能得到小于 $\theta$ 的值，从至少为 $\theta$ 的输入也不能回落到 $\theta$（若 $\theta$ 首次出现，其输入尚不等于它）；$\Phi$ 的每个值都是基数，而 $\Omega<\theta<\Omega_2$。故 $\theta$ 缺于这个闭包，按最小缺口定义有 $\tau\leq\theta$，亦即 $\tau=\theta$。上面对 $\Delta$ 以下的闭包比较现在逐字适用于 $\theta$ 以下，因为正下标塌缩至少为 $\theta$。特别地
\[
 |ID_1|<\psi^{\mathrm R}_0(\tau)
   =\psi^{\mathrm{BJS}}(\Gamma_{\Omega+1})
   =|\mathcal U(ID_1)|<\psi^{\mathrm R}_0(\Xi_2).
\]
这里 $\mathcal U(ID_1)$ 是 $ID_1$ 的展开理论。左端的严格性用 $\Delta<\theta$ 与 $\Delta=\varphi_1(\Omega+1)$ 在相应闭包中；右端用 $\tau<\Xi_2$，以及 $\tau$ 在 $C_0^{\mathrm R}(\tau)$ 中有上述正下标表达式。实际上 $\tau$ 在 $C^{\mathrm R}_0(\Xi_2)$ 中可再作零下标塌缩的参数，而 BJS 的 $C^{\mathrm{BJS}}(\Xi_2,0)$ 整体低于 $\theta$，因为其塌缩输出一律可数。这指出了单基数闭包比较在第 2 项遇到的具体差异。W4 是否覆盖这一中间理论的强度仍待验收。[Rathjen，§10](https://eprints.whiterose.ac.uk/76751/1/Diss.pdf) · [BJS，§2、推论 30](https://home.inf.unibe.ch/thomas.strahm/download/pdf/proof_humboldt_bjs.pdf)

紧接已兑现区间的参数也有精确验收标准。令 $b=|ID_1|$，取 $g$ 为严格大于 $b$ 的第一个强临界序数，则 $\psi_0^{\mathrm R}(\Delta+1)=g$。$\Delta$ 在 $C^{\mathrm R}_0(\Delta+1)$ 中可由种子生成，故其塌缩 $b$ 在该闭包中，新的最小缺口严格大于 $b$，且本身强临界。另一方面，生成可数值时只能使用加法、$\varphi$，或在参数不大于 $\Delta$ 处作零下标塌缩。后一类输出全都不超过 $b$，前两种操作保持严格低于 $g$，故 $g$ 缺于闭包。于是只需问某个真实返回能否盖住 $g$，就能检验这一个后继参数；实际值已经严格超过 $b$，尚未由此推出它达到 $g$。[Rathjen，定义 10.1 与命题 10.3](https://eprints.whiterose.ac.uk/76751/1/Diss.pdf)

## 第二个有限理论的塔项

将第 18 批实际三级运行已覆盖的完整外行，定位到 $ID_2$ 的共尾塔。每个 $D_0D_2^{k+1}0$ 都与本地 ψ₀(Ω₃) 参照树的第 k 支同值。k=1 时，第 18 批定理对所有带已有槽覆盖证据的三级运行给出整支下界，包括通向 Λ 的规范运行。

```agda
open import OCF.Align.EboLeanDef using (cof; cω; h0; h1; hω; fsn; γT; ψ; Ωt)
open import Relation.Binary.PropositionalEquality using (trans)
import B12Omega3Ref as Three
import B18OrbitRows as Actual
import B12Terminal as Runs
import B12ActualSlots as Slots
open import WKShape using (lvl3)
open import W4Fold using (EBOᶜ)
open import WVOne using (read)

align-index : ∀ k → γT (Ωt (natT 3)) (natT 2) k ≡ B.tower 2 (suc k)
align-index zero = refl
align-index (suc k) = cong (λ t → ψ (natT 2) t ∷ []) (align-index k)

align-term : ∀ k → fsn (B.row 2) k ≡ B.collapsed 2 (suc k)
align-term k = cong (λ t → ψ [] t ∷ []) (align-index k)

branch-value : ∀ {t} (h : HC t) → cof t ≡ cω → (y : L.Ordᶜ L.zero) → Rt h L.≅ y →
  ∀ k {s} → fsn t k ≡ s → (hs : HC s) → Rt hs ≈ᵛ Three.at y k
branch-value (h0 e) w y iso k eq hs with trans (sym e) w
... | ()
branch-value (h1 e _) w y iso k eq hs with trans (sym e) w
... | ()
branch-value (hω _ f) w (L.lim g) (L.l≅ iso) k eq hs =
  ≼-trans {b = Rt (f k)} (tree-≼ (sym eq) hs (f k)) (≅→≼ (iso k)) ,
  ≼-trans {b = Rt (f k)} (≅→≼ (L.≅-sym (iso k))) (tree-≼ eq (f k) hs)

id₂-branch : ∀ k → Rt (B.tower-h 2 (suc k)) ≈ᵛ Three.at (Cut.finite 3) k
id₂-branch k = branch-value (B.row-h 2) refl (Cut.finite 3) (Finite.Fin.same 3 (B.row-h 2))
  k (align-term k) (B.tower-h 2 (suc k))

two-in-run : (r : Runs.Run lvl3) → Slots.Covered r → Rt (B.tower-h 2 2) ≼ read (Runs.value r)
two-in-run r cv = ≼-trans {b = Three.at (Cut.finite 3) 1} (proj₁ (id₂-branch 1)) (Actual.At.whole r cv)

two-in-terminal : Rt (B.tower-h 2 2) ≼ read EBOᶜ
two-in-terminal = ≼-trans {b = Three.at (Cut.finite 3) 1} (proj₁ (id₂-branch 1)) Actual.terminal
```
