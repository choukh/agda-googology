# 原参照树与可证良序的秩

第四层，无条件的 Agda 定理。每个较小标准项都能转到一个严格降低高度的见证时，原参照树的值由当前见证的高度界住。同一项可有多份见证。
文末另给本地标准形到 Rathjen 记号的严格保序解释，属经典纸面证明。[文献标尺](#文献标尺)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.EboPTORank where

open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import OCF.Align.EboLeanDef using (T; EBOψ; _<ᵀ_; HC; h0; h1; hω)
open import OCF.Align.EboLeanBase using (NF; Ctbl; nf-pred; Ctbl-pred; c∷; c[])
open import OCF.Align.EboLeanTree using (hc; nf-tower; hc-tower)
open import OCF.Align.EboLeanTrian using (t<; T-pred)
open import OCF.Align.EboLeanClosure using (cl-fsn-NF; Ctbl-fsn; trian-fsn)
open import OCF.Align.EboLeanTau using (AccNF; accNF; wfNF′)
open import OCF.Lean.YiRefTw2 using (Rt; endpoint)
open import OCF.Lean.YiCFMono using (mono<ⁿ)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; ≼-suc; s≼s; l≼; z≼)
open import OCF.Align.EboLeanTree using (EBO-tree′)
open import OCF.Lean.YiMonoExit using (toL)

ZeroTree = L.Ordᶜ L.zero

initial : ∀ {t} (nt : NF t) (ct : Ctbl t) (h : HC t) (y : ZeroTree) →
  (∀ {s} → NF s → Ctbl s → (hs : HC s) → s <ᵀ t → L.suc (Rt hs) ≼ y) → Rt h ≼ y
initial nt ct (h0 _) y smaller = z≼
initial nt ct (h1 e h) y smaller =
  smaller (nf-pred nt) (Ctbl-pred ct) h (t< (T-pred _ e))
initial nt ct (hω e hs) y smaller = l≼ λ i →
  ≼-trans {b = L.suc (Rt (hs i))} (≼-suc (≼-refl _))
    (smaller (cl-fsn-NF nt e i) (Ctbl-fsn ct e i) (hs i) (t< (trian-fsn nt e i)))

module Witnesses {ℓ} (D : T → Set ℓ) (height : ∀ {t} → D t → ZeroTree)
  (descend : ∀ {s t} → NF s → Ctbl s → NF t → Ctbl t → s <ᵀ t → (d : D t) →
     Σ (D s) λ e → L.suc (height e) ≼ height d) where

  private
    follow : ∀ {t} → AccNF t → (nt : NF t) (ct : Ctbl t) (h : HC t) (d : D t) → Rt h ≼ height d
    follow (accNF children) nt ct h d = initial nt ct h (height d) λ ns cs hs lt →
      let step = descend ns cs nt ct lt d in
      ≼-trans {b = L.suc (height (proj₁ step))}
        (s≼s (follow (children ns cs lt) ns cs hs (proj₁ step))) (proj₂ step)

  bound : ∀ {t} (nt : NF t) (ct : Ctbl t) (h : HC t) (d : D t) → Rt h ≼ height d
  bound nt ct = follow (wfNF′ nt ct) nt ct

  whole : ∀ (y : ZeroTree) → (∀ k → Σ (D (EBOψ k)) λ d → height d ≼ y) → toL EBO-tree′ ≼ y
  whole y towers = endpoint y λ k →
    ≼-trans {b = height (proj₁ (towers k))}
      (bound (nf-tower k) (c∷ c[]) (hc-tower k) (proj₁ (towers k))) (proj₂ (towers k))

module Increasing (rank : T → ZeroTree)
  (strict : ∀ {s t} → NF s → Ctbl s → NF t → Ctbl t → s <ᵀ t → L.suc (rank s) ≼ rank t) where
  module R = Witnesses (λ _ → ⊤) (λ {t} _ → rank t)
    (λ ns cs nt ct lt _ → tt , strict ns cs nt ct lt)
  least : ∀ {t} (nt : NF t) (ct : Ctbl t) (h : HC t) → Rt h ≼ rank t
  least nt ct h = R.bound nt ct h tt

attains : ∀ {s t} → NF s → NF t → Ctbl t → (a : HC s) (b : HC t) →
  s <ᵀ t → L.suc (Rt a) ≼ Rt b
attains = mono<ⁿ

module Reference = Witnesses HC Rt
  (λ ns cs nt ct lt h → hc ns cs , attains ns nt ct (hc ns cs) h lt)
```

## 文献标尺

以下在经典集合论中比较序型。取 Rathjen 的 $\lambda=\Phi_1(0)$、$\Xi_0=1$、$\Xi_{k+1}=\Omega_{\Xi_k}$，上标 R 标出他的塌缩。令 $J(0)=0$，$x>0$ 时 $J(x)=\Phi_0(x+1)$。定义 $F([])=0$，按原顺序取有限序数和，把每个主项 $\psi_u(a)$ 送到 $\psi^{\mathrm R}_{J(F(u))}(F(a))$。特别地，本地的一送到 $\psi^{\mathrm R}_0(0)$。这里要用的是严格保序。[Rathjen，定义 9.2、10.1、推论 12.3](https://eprints.whiterose.ac.uk/76751/1/Diss.pdf)

**正规性与保序。** 先对已在每个节点取得文献标准形的两个译项作比较。对两项的大小之和归纳，正规主项依次比较下标与参数，降序排列的正加法主项和按字典序比较。$J$ 严格递增，因此比较结果与本地一致。这个引理的量化域允许在建立一个新主项的正规性之前使用它。[Rathjen，定义 9.6、命题 10.3–10.4](https://eprints.whiterose.ac.uk/76751/1/Diss.pdf)

现在对本地标准形证书归纳。所有子表达式的译值都小于 $\lambda$，因为这是 $\Phi_0$ 的首个不动点，也是极限基数，而 $\psi^{\mathrm R}_\nu$ 的值小于 $\nu^+$。对已取得文献标准形的像 $x$，有 $K_\nu(J(x))=K_\nu(x)$。零时两边为空。正时 $x+1<\Phi_0(x+1)$，新增的 $1=\varphi_0(0)$ 具有空支撑，有限和在末尾添加一项即为标准形。考虑新的 $\psi_u(a)$，其中 $u,a$ 及其子项已经取得标准形。置 $\nu=J(F(u))$。遍历 $a$，和取并，遇到 $\psi_w(b)$ 时按已取得正规性的 $u,w$ 比较。恰在 $u\leq w$ 时加入 $F(b)$ 并继续遍历 $b,w$。这逐条给出
\[
K_\nu(F(a))=\{F(z)\mid \mathrm{InG}(u,z,a)\}.
\]
本地守卫 $\mathrm{GB}(u,a,a)$ 给出每个这样的 $z<a$，对已经正规的 $z,a$ 使用比较引理，得到 $K_\nu(F(a))<F(a)$。文献引理 10.9 此时给出 $F(a)\in C_\nu(F(a))$，完成新主项的正规性。和式的顺序由本地首项证书及同一比较引理保证，空和与单项分别直接取零与主项。这同时证明全部标准形的翻译有定义且严格保序。[本地 InG 与标准形](../OCF/Align/EboLeanBase.lagda.md) · [Rathjen，定义 10.5–10.8、引理 10.9](https://eprints.whiterose.ac.uk/76751/1/Diss.pdf)

**逐塔位置。** 令 $x_k=F(\mathrm{ΩTower}(k))$。有 $1<x_0=\psi^{\mathrm R}_0(0)<\Omega_1$。由归纳假设 $\Xi_k<x_k<\Xi_{k+1}$，得到
\[
\Xi_{k+1}<J(x_k)<x_{k+1}=\psi^{\mathrm R}_{J(x_k)}(0)
 <J(x_k)^+<\Xi_{k+2}.
\]
最后一个不等式用 $x_k$ 为无限序数、$x_k+2<\Xi_{k+1}$，以及 $J(x_k)^+=\Omega_{x_k+2}$。文献引理 12.9 保证 $\psi^{\mathrm R}_0(\Xi_k)$ 正规，本地塔的翻译已证正规。因此本地第 $k$ 个可数塔项的像严格夹在文献第 $k$ 与第 $k+1$ 个可数塔项之间。也可直接看出，所有译项均在 $C_0(\lambda)$ 中，而可数标准项的所有首下标为零，故其像低于 $\Omega_1$，从而低于 $\psi^{\mathrm R}_0(\lambda)$。[Rathjen，命题 10.3、引理 12.9](https://eprints.whiterose.ac.uk/76751/1/Diss.pdf)

以 $\rho$ 记零层树的经典序数值。沿参照树的证书归纳，后继的前驱和极限的每个分支对应更小的标准项，给出 $\rho(\mathrm{Rt}(t))\leq F(t)$。逐塔取上确界，得到 $\rho(R)\leq\psi^{\mathrm R}_0(\lambda)\leq|\Pi^1_1\text{-}\mathrm{TR}_0|$。前一个比较是上面的纸面证明，后一个是文献定理。若实际 W4 返回的序数值支配每个 $\psi^{\mathrm R}_0(\Xi_k)$，引理 12.9 已足以推出 $\rho(R)\leq\rho(Y)$。该实际返回条件仍开放。[Rathjen，定理 12.11(i)](https://eprints.whiterose.ac.uk/76751/1/Diss.pdf)
