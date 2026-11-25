# 原 EBO 各初段的良序理论

第四层。原参照 R 是严格低于它的 ε 数的上确界。Agda 证明无条件的严格封闭，以及排中律下 R ≤ ε⁺(y) 蕴含 R ≤ y。末节用这两条性质作经典纸面 PTO 校准。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.EboPTOSegments where

open import Data.Nat.Base using (ℕ; suc; _≤_; s≤s; z≤n)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (sym; subst)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-refl; ≼-trans; ≼-suc; s≼s; l≼; ≼l; ≼lim⁻)
open import OCF.Align.TightValBase using (s≼-irrefl)
open import OCF.Lean.YiRefTw2 using (endpoint)
open import OCF.Lean.YiRVLevel using (LEM)
import B17Cofinal as C
import B17ValueDich as Comp
import B22MovingIndex as Eps
import B22TowerCut as Mono
import B26Names as A
import B26Depth as D
import B27Epsilon as Lift
open import OCF.Align.EboLeanDef using (hd<; ar<)
open import OCF.Lean.YiCFMono using (mono<ⁿ)

row : ℕ → A.T₀
row k = A.value (D.tower k)
rise : ∀ k → L.suc (row k) ≼ row (suc k)
rise k = mono<ⁿ {s = A.name a} {t = A.name b} (A.nt a) (A.nt b) (A.ct b) (A.hcN a) (A.hcN b) (hd< (ar< (C.rise k)))
  where
  a = D.tower k
  b = D.tower (suc k)

row-ceiling : ∀ k → L.suc (Eps.above (row k)) ≼ A.E
row-ceiling k = ≼-trans {b = L.suc (Eps.above (row (suc k)))}
  (s≼s (Mono.advance {row k} {row (suc k)} (≼-trans {b = L.suc (row k)} (≼-suc (≼-refl (row k))) (rise k))))
  (≼-trans {b = L.suc (A.value (proj₁ cover))} (s≼s (proj₂ (proj₂ cover))) (A.strict (proj₁ cover)))
  where
  a = D.tower (suc k)
  high : 2 ≤ D.height a
  high = subst (2 ≤_) (sym (D.calibrate (suc k))) (s≤s (s≤s z≤n))
  cover = Lift.cover a high

cofinal : A.E ≈ᵛ L.lim (λ k → Eps.above (row k))
cofinal = endpoint (L.lim (λ k → Eps.above (row k)))
          (λ k → ≼l k (≼-trans {b = L.suc (row k)} (≼-suc (≼-refl (row k))) (Eps.strict (row k)))) ,
          l≼ (λ k → ≼-trans {b = L.suc (Eps.above (row k))} (≼-suc (≼-refl (Eps.above (row k)))) (row-ceiling k))

module Limit (e : A.T₀) (r : ℕ → A.T₀) (upper : e ≼ L.lim r)
             (inside : ∀ k → L.suc (Eps.above (r k)) ≼ e) where
  stable : ∀ {x} → L.suc x ≼ e → L.suc (Eps.above x) ≼ e
  stable {x} low with ≼lim⁻ {a = x} {f = r} (≼-trans {a = L.suc x} {b = e} {c = L.lim r} low upper)
  ... | k , d = ≼-trans {b = L.suc (Eps.above (r k))}
    (s≼s (Mono.advance {x} {r k} (≼-trans {b = L.suc x} (≼-suc (≼-refl x)) d))) (inside k)

  strip : LEM → ∀ y → e ≼ Eps.above y → e ≼ y
  strip lem y h with Comp.Classical.compare lem e y
  ... | inj₁ d = d
  ... | inj₂ d = ⊥-elim (s≼-irrefl (Eps.above y) (≼-trans {b = e} (stable {y} d) h))

module Reference = Limit A.E row (endpoint (L.lim row) (λ k → ≼l {f = row} k (≼-refl (row k)))) row-ceiling

closed : ∀ {x} → L.suc x ≼ A.E → L.suc (Eps.above x) ≼ A.E
closed {x} = Reference.stable {x}
recover : LEM → ∀ y → A.E ≼ Eps.above y → A.E ≼ y
recover = Reference.strip
```

## 经典纸面证明 · 一个 PTO 恰为本地 EBO 的理论

以 $|T|$ 记 $T$ 可证良序的递归线序的序型上确界。$I$ 是所有可数标准项在本地项序下构成的线序，$I_k$ 是严格小于第 $k$ 个塔项 `EBOψ k` 的限制。有限项的编码、首下标、标准形和项序均可有效检验，$I_k$ 是统一递归的线序族。记 $r_k=\operatorname{otp}(I_k)$。对可数标准项 $t$ 按项序归纳，其参照树值等于其前驱初段的序型。严格保序给出树值的下界，后继的前驱和极限的每个分支都属于该初段，给出上界。因而 $r_k$ 正是代码中的 `row k`。每个可数标准项都低于某个塔项，且塔项严格递增，故 $R=\operatorname{otp}(I)=\sup_k r_k$。[可判定项序和标准形](../OCF/Align/EboLeanBase.lagda.md) · [严格保序与初段上界](EboPTORank.lagda.md) · [塔项的严格增长与穷尽](Reports-2026-11-18/attachments/B17Cofinal.agda.txt)

取递归可枚举的二阶算术理论

$$
T_R=\mathsf{ACA}_0+\{\mathrm{WO}(I_k)\mid k\in\mathbb N\}.
$$

每个标准自然数给一条独立公理。对每对固定的 $j\le k$，$\mathsf{ACA}_0$ 可证 $I_j$ 的域包含在 $I_k$ 的域中，恒等包含保序。这里仅用有限项比较的传递性和对两个给定塔项的计算。因此 $T_R$ 的每份证明用到的有限条附加公理都可由其中最大下标的一条导出。令 $\varepsilon^+(x)$ 为严格大于 $x$ 的最小 ε 数。单良序公理的经典公式与上面的 `cofinal` 给出

$$
|T_R|=\sup_k |\mathsf{ACA}_0+\mathrm{WO}(I_k)|
     =\sup_k\varepsilon^+(r_k)=R.
$$

这项校准只依赖原记号。单独把全序 $I$ 的良序性加入 $\mathsf{ACA}_0$ 会得到 $\varepsilon^+(R)>R$。独立候选 $\Pi^1_1\text{-}\mathrm{TR}_0$ 另已有 $R\le\psi^{\mathrm R}_0(\Phi_1(0))\le |\Pi^1_1\text{-}\mathrm{TR}_0|$，反向比较开放。[Aguilera–Pakhomov，定理 21 的证明](https://backoffice.biblio.ugent.be/download/01H3WWR51BSZ686FK04YGPVW1Y/01H3WWSW11Q004X3M39D6NSW9R) · [本地严格保序翻译](EboPTORank.lagda.md#文献标尺) · [Rathjen，定理 12.11(i)](https://eprints.whiterose.ac.uk/76751/1/Diss.pdf#page=52)

## W4 下界的逐公理判据

沿用下降地址线序 $A_Y$ 的经典序型计算 $\operatorname{otp}(A_Y)=\omega^Y$。下式以给出这条线序的忠实递归表示为前提。令 $U_Y=\mathsf{ACA}_0+\mathrm{WO}(A_Y)$，则 $|U_Y|=\varepsilon^+(\omega^Y)=\varepsilon^+(Y)$。最后一个等式由 $Y\le\omega^Y<\varepsilon^+(Y)$ 得到。`recover` 与 $Y<\varepsilon^+(Y)$ 给出

$$
R\le Y\quad\Longleftrightarrow\quad |T_R|\le|U_Y|.
$$

所以只要对每个固定 $k$ 在 $U_Y$ 中证明 $\mathrm{WO}(I_k)$，就能推出 EBO 下界。各个证明可以依赖 $k$。序数比较的反向不提供这些公理的形式推导。参照实例可取 $Y=R$，用 $I$ 表示序型 $\omega^R=R$ 的输入良序，限制到 $I_k$ 就给出每条证明。实际 W4 的地址编码及其与原记号初段间的降链转换仍待建立。[地址线序的序型与有效化条件](../LOG.md#w4-kb-comparison) · [弱理论中降链转换的先例](https://math.berkeley.edu/~antonio/papers/veblen.pdf)

还可以在上述各份证明中调用已在外部证明为真的算术句子，例如一个指定数值求值器在合法的自然数编码输入上总停机（合法性须为算术谓词）。Kreisel 定理允许给递归可公理化的 Π¹₁ 可靠的 $\mathsf{ACA}_0$ 扩张加入一条真 Σ¹₁ 句子而保持 PTO；一份证明用到的有限组算术事实合取后满足该条件。故若每个 $k$ 有这样的辅助事实 $\sigma_k$，且 $U_Y+\sigma_k\vdash\mathrm{WO}(I_k)$，每个 $r_k$ 仍严格低于同一 $|U_Y|$，上确界仍给出 $R\le Y$。编码的忠实性与所加事实的真实性须另证。相同定理也说明，单把一个固定数值程序的真实全域停机断言加到 $\mathsf{ACA}_0$，所得 PTO 仍是 ε₀。[Walsh，定理 1.2（Kreisel）](https://arxiv.org/pdf/2209.09765#page=2)

若允许任意真 Σ¹₁ 辅助句，上述逐项条件也是必要的。由 $R\le Y$ 得 $r_k<R\le |U_Y|$，故有一条 $U_Y$ 可证良序的递归序 $D$ 满足 $r_k<\operatorname{otp}(D)$。存在 $I_k$ 到 $D$ 的保序嵌入是一条真 Σ¹₁ 句子；有了嵌入，$\mathsf{ACA}_0$ 可把假想降链映为降链。由此得到允许真 Σ¹₁ 辅助句的双向刻画。用它给实际树证下界时，需要独立建立所用辅助句的真实性。[Walsh 对带真 Σ¹₁ 辅助句的理论比较，定义 1.7 与定理 1.10](https://arxiv.org/pdf/2209.09765)
