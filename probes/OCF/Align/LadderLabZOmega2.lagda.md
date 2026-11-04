> **机械克隆, 验收用.** 由 `ScafLadderZOmega2` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.

> **机械克隆.** 由 `Omega2` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# $\psi_0(\Omega_\Omega\cdot2)$: 沿链的良基序列与 `Lab T2 t2`

> 接 [Omega2Base](Omega2Base.lagda.md) (参数化的界、`GX₃`、任意目标层的带前缀标签) 与 [Decouple](Decouple.lagda.md) §11 的障碍 (3). 本文把证书与标签沿 $t_2=\psi_0(\Omega_\Omega\cdot2)$ 的链组织成良基序列, 给出 `Lab T2 t2`, 并精确定位证书一侧的停点.
>
> 结论先说:
>
> 1. **对任意证书的标签 (§2).** $t_2$ 的符号树 `t2ˢ` 字面是第 0 层的闭包 `ŝ 1 t₀ᵗ gᵗ` (`refl`), $t_0=\psi^{[\hat\Omega]}_0(\Omega_1)$, $g\,\eta\,e=\psi^{[\hat\Omega]}_0(\Omega_\eta)$. **`t2ˢ-label : (G : Goodᶻ (toZ t2ˢ)) → Lab (force (toZ t2ˢ) G) t2`**, 对 Prefix 意义下的**一切**证书: 链点的标签逐点前进, 第 $k$ 个链点的标签 $\gamma'_{k+1}$ 经 `LabS-Ω` 变成下一个计值点的尾巴 $\Omega_{\mathtt{lvl}\,\chi_k}$ 的标签, 再经 Omega2Base 的 `Pre0V` 给出第 $k+1$ 个链点的标签 $\gamma'_{k+2}$ (`lab-g`). 所以 Symbolic 的 `C2-unlabel` 那种失败在符号族上不会出现: 计值树只要存在, 就带 $t_2$ 的标签.
> 2. **良基序列 (§3).** 模块 `Chain Cert`, 参数 `CertOracle`: "第 $k$ 个链点 (带标签 $\gamma'_{k+1}$) $\Rightarrow$ 第 $k+1$ 个计值点的证书". 包 `Pkg k` = (树, `HS`, `Lab … (γ′ᴱ (k+1))`, 支配 $1\sqsubseteq^\mathsf I$ 层号), `pkg (k+1) = next k (pkg k)`; 证书 $\to$ 标签 (`lab-g`) $\to$ 下一点的层号与支配 (`Strict₁`) $\to$ (oracle) 下一点的证书. 单调性也来自标签 (`Lab-oc` + `γ′-mono`), 不需要观测前序. **`T2-label : Lab T2 t2`**, `T2-HS`, `T2-step : FGH T2 n ≡ FGH (χ n) n` (`refl`), Stage2 的 `Q′` 路径在新树上带标签且终点 $\cong$ `BTBOᴵ` (`Q′-label`, `Q′-end`), 与 Symbolic 的旧树不 $\cong$ (`old≇new`), 与任何完整证书的计值树 $\cong$ (`agree`); 一个完整证书给出 oracle (`fromCert`). 第 0 点的证书无条件 (`G₀ᵗ`, 环境层号 1).
> 3. **停点: 链指标 $k=1$ (§4–§5).** 缺的恰是 `CertOracle 0`, 即 $\gamma'_2=\psi_0(\Omega_\Omega+\Omega_{\gamma'_1})$ 的计值树的证书. (i) Omega2Base 的全局界路线在这里不可能 (**`no-Bound`, 已编译**: 对 $\gamma'_2$ 的环境层号 `Mlev 1 (lvl χ₀) e` $\sqsubseteq\beta$ 的任何 $\beta$, `Strictᵝ β` 为假). 记号侧第一处越界的闭包: $t_2$ 沿 `1 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 1 ∷ 1` 到 $\psi_0(\Omega_\Omega+\psi_{\psi_0(\Omega_\Omega)}(\Omega_\Omega+\Omega_{\psi_0(\Omega_\Omega)}))$ (`first-wall`, `refl`), 目标为 BTBO 的弹栈闭包界为 $\mathtt{lvl}\,\mathrm{BTBO}+1$; 下一项 (`second-wall`) 的目标是 BTBO$+1$. (ii) 逐个闭包由标签给支配 (Decouple 设想的 `Strictⱼ`) 对链的第 0 点够用, 但 Prefix 的证书 `Goodᶻ.gc` 要求闭包在**一切** $\eta\sqsupseteq c$ 处的计值都有证书, 而 $\eta$ 任意时那些位置没有标签 (§5). 缺的是一种只在带标签的计值点处量化的证书, 或带 "地板" 的闭包定理; 本文未写.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块与 Omega2Base, 不改任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLabZOmega2 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import OCF.Align.Level
open import OCF.Align.Symbolic using (Ctx; Pt; Γᶜ; lvP; Mlev; σ1)
open import OCF.Align.LadderLabZPrefix using (Ord₊ˢ; Ordˢ; Ωˢ; toZ; Goodᶻ; force; force-HS; outs; t2ˢ)
import OCF.Align.NoCumsum as N
import OCF.Align.EBO as E
open E using (T; natT; fsn; Ωt; _<ᵀ_) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; lω; Lab-≅)
open import OCF.Align.LadderLabZStandardOmega using (γ′-NF; γ′-mono)
open import OCF.Align.Stage2 using (t2; γ′ᴱ; diag2-fs; Q′; sq; walk; walkᵀ; Lab-walk; Lab-uniq; ctx)
open import OCF.Align.Label using (BTBO-label)
open import OCF.Align.LadderLabZUniformS using (ψ1; Ωˢ-refl)
import OCF.Align.LadderLabZUniformS as US
open import OCF.Align.LadderLabZStage2Label using (one⁰; Strict₁; one⊑two; Lab-oc; BTBO-NF; pop0≅; σ00)
open import OCF.Align.Closure using (lt→<)
import OCF.Align.Symbolic as Sy
import OCF.Align.LadderLabZStage2Label as S2L
open import OCF.Align.Stage2 using (≺→⊑)
open import OCF.Align.LadderLabZDecoupleBase using (cc; toC; ΩΩ)
open import OCF.Align.LadderLabZPrefix using (z2)
open import OCF.Align.LadderLabZUniformS using (𝟎ˢ; z≅)
open import OCF.Align.LadderLabZOmega2Base using (Pre0V; LabS-Ω; lab1; nf1; module Bound; popG; ≺⊑ᴵ)
```


## §1 外层闭包

Prefix 的 `t2ˢ-shape`: 弹出 $[\hat\Omega,\hat\Omega]$ 的第一个 $\hat\Omega$ 后, $t_2$ 的符号树是界为 1 的第 0 层闭包, 第 0 点 `t₀ᵗ` $=\psi^{[\hat\Omega]}_0(\Omega_1)$ (环境层号 1), 在 $\eta$ 处 `gᵗ η e` $=\psi^{[\hat\Omega]}_0(\Omega_\eta)$ (环境层号 `Mlev 1 η e`). 两者都是单 $\hat\Omega$ 栈的 `ψ1`. 记号侧 $\gamma'_{k+1}=\psi_0(\Omega_\Omega+\Omega_{\gamma'_k})$ 是定义性的.

```agda
t₀ᵗ : Ordˢ zero
t₀ᵗ = ψ1 {ℓ = suc zero} zero (σ1 zero) zero (Ωˢ (suc zero))

gᵗ : (η : Ordᴵ) → suc zero ⊑ᴵ η → Ordˢ zero
gᵗ η e = ψ1 {ℓ = Mlev (suc zero) η e} (lim 0 zero) (λ q → lim 1 q) (lim 0 zero) (Ωˢ η)

_ : t2ˢ ≡ Ord₊ˢ.ŝ (suc zero) t₀ᵗ gᵗ
_ = refl

_ : ∀ k → γ′ᴱ (suc k) ≡ ctx (Ωt (γ′ᴱ k))
_ = λ k → refl
```


## §2 链点的标签, 对任意证书

`lab-t₀`: 第 0 点的标签 $\gamma'_1$ (`Pre0V` 作用于 $\Omega_1$ 的 `LabS`). `lab-g k`: 若 $Y$ 带标签 $\gamma'_{k+1}$, 则 $\psi^{[\hat\Omega]}_0(\Omega_{\mathtt{lvl}\,Y})$ 的计值树 (任意证书) 带标签 $\gamma'_{k+2}$; 标准形是 StandardOmega 的 `γ′-NF`. 这就是 Decouple §11 (3) 的 "标签 $\to$ 下一点" 一环, 对 $\gamma'_{k+1}$ 的子层号 (闭包的目标层) 的标签由 `Pre0V` 内部的 `PreS₊`/`foldLab` 逐个现造.

```agda
lab-t₀ : (G : Goodᶻ (toZ t₀ᵗ)) → Lab (force _ G) (γ′ᴱ 1)
lab-t₀ G = Pre0V {p = zero} {σ = σ1 zero} {z = zero} (LabS-Ω one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _)) (Ωˢ-refl (suc zero)) (γ′-NF 1) G

lab-g : ∀ k {Y} (hY : HS Y) → Lab Y (γ′ᴱ (suc k)) → (e : suc zero ⊑ᴵ toLevel Y hY) →
        (G : Goodᶻ (toZ (gᵗ (toLevel Y hY) e))) → Lab (force _ G) (γ′ᴱ (suc (suc k)))
lab-g k {Y} hY lY e G =
  Pre0V {p = lim 0 zero} {σ = λ q → lim 1 q} {z = lim 0 zero} (LabS-Ω Y hY lY (γ′-NF (suc k)) (≅ᴵ-refl _))
        (Ωˢ-refl _) (γ′-NF (suc (suc k))) G
```


**定理 `t2ˢ-label`.** 证书 `gc` 的前六个字段组成链 `C` (DecoupleBase 的 `toC`, 与 `force` 内部的记录逐字段相同). 链点的标签对 $k$ 归纳 (`ptL`), 输出与链点只差证书 (`outL`, 输出在第 $k$ 个链点的层号处计值).

```agda
t2ˢ-label : (G : Goodᶻ (toZ t2ˢ)) → Lab (force (toZ t2ˢ) G) t2
t2ˢ-label (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) =
  lω refl (l≅ (λ n → ≅-refl⁰ _)) (λ n → subst (Lab _) (sym (diag2-fs n)) (outL n))
  where
  C : Ctx
  C = toC (cc G₀ Gg d₀ dE m₀ mE)
  ptL : ∀ k → Lab (Pt.x (Γᶜ C k)) (γ′ᴱ (suc k))
  ptL zero    = lab-t₀ G₀
  ptL (suc k) = lab-g k (Pt.hx (Γᶜ C k)) (ptL k) (Pt.dx (Γᶜ C k)) (Gg _ _)
  outL : ∀ n → Lab (outs C (force _ Go₀) (λ η e → force _ (Go η e)) n) (γ′ᴱ (suc n))
  outL zero    = lab-t₀ Go₀
  outL (suc k) = lab-g k (Pt.hx (Γᶜ C k)) (ptL k) (Pt.dx (Γᶜ C k)) (Go _ _)
```


**读法.** 这里没有阶段系统、公共上界或翻译: 链点 $k$ 的标签提供链点 $k+1$ 的尾巴 $\Omega_{\mathtt{lvl}\,\chi_k}$ 的 `Idx`, 其余由 Omega2Base 的上下文引理完成. 前提只有 "计值树存在" (证书 $G$).

## §3 良基序列

`CertOracle`: 给定第 $k$ 个链点 $Y$ (`HS`、标签 $\gamma'_{k+1}$、支配 $1\sqsubseteq^\mathsf I\mathtt{lvl}\,Y$), 给出第 $k+1$ 个计值点 `gᵗ (lvl Y) e` 的 Prefix 证书. 模块 `Chain Cert` 对 $k$ 递归地造包: 第 0 包的证书 `G₀ᵗ` 由 Stage2Label 的 `Good-ψ1` (环境层号 $1\sqsubseteq2$) 无条件给出; 第 $k+1$ 包: 证书 (oracle) $\to$ 标签 (`lab-g`) $\to$ 支配 (`dom1`: Stage2Label 的 `Strict₁` 给 $\sqsupseteq2$). 序列良基: 第 $k+1$ 包只用第 $k$ 包.

```agda
G₀ᵗ : Goodᶻ (toZ t₀ᵗ)
G₀ᵗ = US.Good→Goodᶻ (S2L.Good-ψ1 {p = zero} {σ = σ1 zero} {z = zero} one⊑two (US.Good-Ω (suc zero)) (Ωˢ-refl (suc zero)))

dom1 : ∀ {L k} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} {y : Ordˢ k} → y US.≅ˢ y →
       (G : Goodᶻ (toZ (ψ1 p σ z y))) → suc zero ⊑ᴵ toLevel (force _ G) (force-HS _ G)
dom1 {y = y} ey G = ⊑ᴵ-trans one⊑two (Strict₁ y ey G)

CertOracle : Set
CertOracle = ∀ k {Y} (hY : HS Y) → Lab Y (γ′ᴱ (suc k)) → (e : suc zero ⊑ᴵ toLevel Y hY) → Goodᶻ (toZ (gᵗ (toLevel Y hY) e))

module Chain (Cert : CertOracle) where
  record Pkg (k : ℕ) : Set where
    constructor pk
    field
      Y  : Ordᶜ zero
      hY : HS Y
      lY : Lab Y (γ′ᴱ (suc k))
      dY : suc zero ⊑ᴵ toLevel Y hY
  open Pkg

  next : ∀ k → Pkg k → Pkg (suc k)
  next k (pk Y hY lY dY) = pk (force _ G) (force-HS _ G) (lab-g k hY lY dY G)
                                (dom1 {p = lim 0 zero} {σ = λ q → lim 1 q} {z = lim 0 zero} (Ωˢ-refl _) G)
    where G = Cert k hY lY dY

  pkg : ∀ k → Pkg k
  pkg zero    = pk (force _ G₀ᵗ) (force-HS _ G₀ᵗ) (lab-t₀ G₀ᵗ)
                   (dom1 {p = zero} {σ = σ1 zero} {z = zero} (Ωˢ-refl (suc zero)) G₀ᵗ)
  pkg (suc k) = next k (pkg k)

  χ : ℕ → Ordᶜ zero
  χ k = Y (pkg k)

  χ-step : ∀ k → χ k ⊑⁰ χ (suc k)
  χ-step k = ≺→⊑ (Lab-oc (lY (pkg (suc k))) (γ′-NF (suc (suc k))) (lY (pkg k)) (γ′-NF (suc k)) (γ′-mono (suc k)))

  T2 : Ordᶜ zero
  T2 = lim χ

  T2-HS : HS T2
  T2-HS = hl (λ k → hY (pkg k)) χ-step

  T2-label : Lab T2 t2
  T2-label = lω refl (l≅ (λ n → ≅-refl⁰ _)) (λ n → subst (Lab _) (sym (diag2-fs n)) (lY (pkg n)))

  T2-step : ∀ n → FGH T2 n ≡ FGH (χ n) n
  T2-step n = refl

  Q′-label : Lab (walk (sq T2 1) Q′) (E.EBOψ 2)
  Q′-label = Lab-walk Q′ (lY (pkg 1)) (refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl ,
                                       refl , refl , refl , refl , refl , refl , tt)

  Q′-end : walk (sq T2 1) Q′ ≅ N.BTBOᴵ
  Q′-end = Lab-uniq Q′-label BTBO-label

  agree : (G : Goodᶻ (toZ t2ˢ)) → force (toZ t2ˢ) G ≅ T2
  agree G = Lab-uniq (t2ˢ-label G) T2-label

  old≇new : ¬ (Sy.T2 ≅ T2)
  old≇new e = Sy.C2-unlabel (Lab-≅ e T2-label)
```


**读法.** `χ-step` 由标签得到: $\gamma'_{k+1}<\gamma'_{k+2}$ (`γ′-mono`) 经 `Lab-oc` 给出树的 $\prec$, 再 `≺→⊑`. 所以 `T2` 的 `HS` 也不需要观测前序. `Q′-label`: Stage2 的 `Q′` (17 步, 静态前缀的旧树在终点是 `zero`, Symbolic 的 `C2-unlabel`) 在新树上带标签 $\psi_0(\Omega_\Omega)$, 终点 $\cong$ `BTBOᴵ`. `old≇new`: Symbolic 的 `T2` 与本文的 `T2` 不 $\cong$ (否则前者带标签).

一个完整的 Prefix 证书给出 oracle (在链点的层号处取 `Gg`); 于是 `t2ˢ-label` 与 `Chain (fromCert G)` 给出同一棵树 (模 $\cong$, `agree`):

```agda
fromCert : Goodᶻ (toZ t2ˢ) → CertOracle
fromCert (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) k hY lY e = Gg _ e
```


## §4 停点: $k=1$

`no-Bound`: 对 $t_2$ 的第 0 个链点 $\chi_0$ (任意证书) 与任意支配 $e$, 若 $\gamma'_2$ 的环境层号 `Mlev 1 (lvl χ₀) e` $\sqsubseteq^\mathsf I\beta$, 则 `Strictᵝ β` 为假. 证明: `Strictᵝ β` 在尾巴 $0$ 处给 $\beta\sqsubseteq\mathtt{lvl}\,\mathrm{BTBO}$ (`pop0≅`), 而 $\mathtt{lvl}\,\mathrm{BTBO}\prec^\mathsf I\mathtt{lvl}\,\chi_0\sqsubseteq^\mathsf I$ `Mlev …` $\sqsubseteq^\mathsf I\beta$ (`lab-t₀` 与 `Lab-oc`). 所以 Omega2Base 的 `Bound β` 对 $\gamma'_2$ 无用, 无论 $\beta$ 取什么. 记号侧第一处越界: $t_2$ 的 7 步后代里, 目标为 $\psi_0(\Omega_\Omega)$ 的带前缀节点, 它弹栈产生界为 $\mathtt{lvl}\,\mathrm{BTBO}+1$ 的闭包 (Python 模拟器的宽度 3 搜索, 499 个后代里第一个下标非有限的带前缀节点; 路径与终点 `refl`). `second-wall` 是同一处的下一项 ($[2]$ 代替 $[1]$): 目标 $\psi_0(\Omega_\Omega)+1$, 界 $\mathtt{lvl}\,\mathrm{BTBO}+2$, 它在 §5 里是第一个连 "对一切 $\eta$ 的计值" 都超出全局界的闭包:

```agda
first-wall : walkᵀ t2 (1 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ []) ≡ ctx (ψᵗ (E.EBOψ 2) (ΩΩ ∷ Ωt (E.EBOψ 2)) ∷ [])
first-wall = refl

second-wall : walkᵀ t2 (1 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ []) ≡ ctx (ψᵗ (E.sucT (E.EBOψ 2)) (ΩΩ ∷ Ωt (E.sucT (E.EBOψ 2))) ∷ [])
second-wall = refl
```


```agda
η⊑Mlev : ∀ {c η} (e : c ⊑ᴵ η) → η ⊑ᴵ Mlev c η e
η⊑Mlev e = Sim→⊑ᴵ (λ q → lim 1 q)

no-Bound : (G : Goodᶻ (toZ t₀ᵗ)) (e : suc zero ⊑ᴵ toLevel (force _ G) (force-HS _ G)) →
           ∀ β → Mlev (suc zero) (toLevel (force _ G) (force-HS _ G)) e ⊑ᴵ β → ¬ Bound.Strictᵝ β
no-Bound G e β h S =
  ≺ᴵ-irrefl (≺ᴵ-respʳ (≺⊑ᴵ (≺⊑ᴵ bl< (⊑ᴵ-trans (η⊑Mlev e) h)) (S {p = z2} {σ = σ00} {z = z2} 𝟎ˢ z≅ Gp))
                      (toLevel-≅ (force-HS _ Gp) N.BTBO-HS (pop0≅ z2 σ00 z2 Gp)))
  where
  Gp = popG z2 σ00 z2
  bl< : toLevel N.BTBOᴵ N.BTBO-HS ≺ᴵ toLevel (force _ G) (force-HS _ G)
  bl< = toLevel-≺ N.BTBO-HS (force-HS _ G)
                  (Lab-oc (lab-t₀ G) (γ′-NF 1) BTBO-label BTBO-NF (lt→< (E.EBOψ 2) (γ′ᴱ 1) refl))
```


## §5 为什么 Prefix 的证书在 $k=1$ 需要新东西

逐个闭包的支配本身不难: `first-wall` 处的闭包 (目标 $\delta=\mathtt{lvl}\,\mathrm{BTBO}$, 界 $\delta+1$) 被外层 $\psi_0$ 折成链时, 第 0 个链点 $\psi_0(\Omega_\Omega+\cdots\psi_\delta(\Omega_1)\cdots)$ 与 $\delta$ 都带标签, `Lab-oc` 给 $\delta\prec^\mathsf I$ 链点的层号, 即 `d₀`; `dE` 由单调性. 这就是 Decouple §11 设想的 `Strictⱼ`, 在本文的工具里是一行.

难在 Prefix 的 `Goodᶻ.gc` 的 `Gg : ∀ η e → Goodᶻ (g η e)`: 第 0 层的链对**一切** $\eta\sqsupseteq c$ 的计值都要证书, 而 `force` 只在链点处用它. 闭包在 $\eta$ 处的值含不带前缀的 $\psi_\delta(\Omega_\eta)$, 它的穿透节点在 $\eta$ 的子层号 $j\prec\delta$ 上; 外层带前缀的 $\psi^{[\hat\Omega]}_0$ (以及中间的 $\psi^{[\hat\Omega]}_i$) 在这些节点折叠, 链点 $\psi^{[\hat\Omega]}_j(\cdots)$ 弹栈出界为 $j+1$ 的新闭包, 位置依赖 $\eta$ 的树. $\eta$ 任意时 (例如 $\eta\cong\mathtt{lvl}\,T_2+1$) 这些位置没有标签.

- 对 `first-wall` 的闭包, 新闭包的界 $j+1\sqsubseteq\delta=\mathtt{lvl}\,\mathrm{BTBO}$, 支配是全局的 (Omega2Base 的 `Strict-BTBO`: 一切输出 $\sqsupseteq$ BTBO). 但 `Bound.Good-ψ1` 从环境层号 ($\ell\sqsubseteq\beta$) 读出弹栈目标的界, 这里的环境层号 $\sqsupseteq\mathtt{lvl}\,\gamma'_1$ (`no-Bound`); 需要一个以 "尾巴的节点层号 $\prec\beta$" 代替 $\ell\sqsubseteq\beta$ 的变体. 未写.
- 对下一个闭包 (`second-wall`: 目标 $\mu=\mathtt{lvl}\,\mathrm{BTBO}+1$, 在 $\psi_0(\Omega_\Omega+\Omega_{\mathrm{BTBO}+2})$ 里), $j\prec\mu$ 包括 $j\cong\mathtt{lvl}\,\mathrm{BTBO}$, 新闭包的界是 $\mathtt{lvl}\,\mathrm{BTBO}+1$, 而全局界到此不可能 (`Sβ-fails⁺`). 它们的支配只能这样得到: 链点 $\sqsupseteq^\mathsf o\psi^{[\hat\Omega]}_0(C[\Omega_\mu])$ (`B1₀`/`B1₁` 的单调性), 后者带标签且 $\succ\mu$. 这是 "相对于带标签的地板 $\mu$" 的严格性, 既不是全局界, 也不是位置上的标签.

把地板做成 `Good` 的不变量, 要求 `Dom` 记下每个闭包的地板, 并在 $\psi$ 逐点映射闭包时更新; 而闭包刚弹出时 (目标层 $j$ 未带标签) 地板只能是 $j$ 自己, 要等外层的 $\psi_\mu$ 把它包住后才能换成 $\mu$, 一般的 `Good-ψ1` 递归里看不到这件事. 本文没有做.

两条可行的出路 (纸面, 未写):

- **只在带标签的计值点处量化的证书 `Goodᴸ`.** `gc` 多一个可容许谓词 `Adm : Ordᴵ → Set` (例如 "层号 $\cong$ 某个带标签 $\theta$ 的树, 且 $\psi_0(\Omega_\Omega+b[\theta])$ 是标准形"), `Gg`/`dE`/`mE` 只对 `Adm η` 量化, 外加 "链点的层号仍可容许" 的字段; `force` 只在链点处计值, 所以照样良定 (`Goodᴸ` 落在 `Set₁`). 证书与标签由同一个对 `LabS` 推导的递归造出 (`Pre0S₊` 的结构), 支配与单调都来自 `Lab-oc` (需要 `NF₁` 上的 `fs-mono`, StandardOmega 只有 `γ-mono₁`/`fsT-mono₁`, 缺 `cω` 的一般情形). 原子 (`Atom`) 也要换成 `Goodᴸ` 版本, 即 DecoupleBase 整份重写.
- **带地板的闭包定理.** 保留 Prefix 的 `Goodᶻ`, 给非零层闭包的 `Dom` 加 "地板 $\lambda$ 与 $\Omega_\lambda\sqsubseteq^\mathsf o t_0$", 在不带前缀的 $\psi_\delta$ 映射闭包时把地板提到 $\delta$ (要 $\lambda\preceq\delta$ 的证据, 来自穿透的派发), 到第 0 层时用地板的标签. 难点见上一段.

## §6 对比表

| | Symbolic / Decouple §11 | 本文 |
|---|---|---|
| $t_2$ 的树 | `C2` (静态前缀, 外面装配), `C2-unlabel` | 符号族的 `t2ˢ`; 计值树对**任意**证书带标签 (`t2ˢ-label`) |
| 链上的环 | 证书 $\leftrightarrow$ 标签互相依赖 | 良基序列 `pkg`: 证书 $\to$ 标签 $\to$ 层号与支配 $\to$ 下一个证书 |
| 链点标签 | 未得 | `lab-t₀`, `lab-g` (Omega2Base 的 `Pre0V` + `LabS-Ω`) |
| 链的单调 | 观测前序 | 由标签 (`Lab-oc` + `γ′-mono`) |
| `Lab T2 t2` | 未得 | **`Chain.T2-label`** (以 `CertOracle` 为参数); `t2ˢ-label` (以完整证书为前提) |
| `Q′` | 旧树走到 `zero` | `Q′-label`, `Q′-end : … ≅ BTBOᴵ` |
| 证书 | $k\ge1$ 未得 | $k=0$ 无条件 (`G₀ᵗ`); $k=1$ 停 (`no-Bound`, `first-wall`, §5) |

## §7 结论与边界

**字面成立 (`refl`):** `t2ˢ ≡ ŝ 1 t₀ᵗ gᵗ`; `γ′ᴱ (k+1) ≡ ctx (Ωt (γ′ᴱ k))`; `T2-step` (FGH 在极限处取第 $n$ 项); `Q′-label` 用到的 17 个 `cof … ≡ cω`; `first-wall`, `second-wall` (两条 7 步路径的终点).

**定理 (模 $\cong$; 标签按 Correspond 的 `Lab`):**

1. `lab-t₀`, `lab-g`; **`t2ˢ-label : (G : Goodᶻ (toZ t2ˢ)) → Lab (force (toZ t2ˢ) G) t2`** (无其他前提).
2. `Chain Cert`: `pkg`, `χ-step`, `T2-HS`, **`T2-label : Lab T2 t2`**, `T2-step`, `Q′-label`, `Q′-end`, `agree`, `old≇new`; `fromCert`; `G₀ᵗ` (第 0 点的证书, 无条件).
3. 否定: **`no-Bound`** (全局界的证书路线对 $\gamma'_2$ 不可能).

**标签状态.** $\psi_0(\Omega_\Omega\cdot2)$: 标签定理**以证书为前提**: 对 Prefix 的任意证书 (`t2ˢ-label`), 或对链点处的证书 oracle (`Chain.T2-label`). 前提在 $k=0$ (链点 $\gamma'_1$) 成立, 在 $k=1$ ($\gamma'_2$ 的计值树的证书) 未得. 所以按 README 的认证准则, `Lab T2 t2` **不是**无条件定理; 无条件的是 "一旦计值树存在, 标签自动成立" 以及 $\gamma'_1$、$X_2$、$X_3$ 的标签. `C2-unlabel` 的失败已解除 (新树沿 `Q′` 带标签), Stage2 的 `Q′` 路径同.

**精确停点.** 链指标 $k=1$; 项 $\gamma'_2=\psi_0(\Omega_\Omega+\Omega_{\gamma'_1})$, 第一处越过全局界的闭包在 $t_2$ 的 `1 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 1 ∷ 1` (目标 $\psi_0(\Omega_\Omega)$, 界 $\mathtt{lvl}\,\mathrm{BTBO}+1$), 第一个在 "对一切 $\eta$ 的计值" 里也越界的闭包在 `1 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 2 ∷ 1` (目标 $\psi_0(\Omega_\Omega)+1$); 缺的引理: `CertOracle 0`, 即 `Goodᶻ (toZ (gᵗ (lvl χ₀) e))`; 全局界不可能 (`no-Bound`), 逐闭包的标签式支配对 `d₀` 够用, 但 `Goodᶻ.gc` 对一切 $\eta$ 的量化碰到无标签位置上界为 $\mathtt{lvl}\,\mathrm{BTBO}+1$ 的闭包, 它们的支配要 "相对地板" 的严格性 (§5).

**边界.**

- 本文的 `T2` 是链点处计值的树 (以 oracle 为参数), 与 Prefix 意义下 `force (toZ t2ˢ) G` 在证书存在时 $\cong$ (`agree`); 两者都只到 $\cong$ (`lim` 下的函数头不同).
- 工程注记: `dom1` 的隐式参数 (`p`/`σ`/`z`) 不写时报 `[UnsolvedConstraints] … ψᴾ 1 _p_257 _σ_258 … | <ᴵ-dec (_σ_258 zero) _p_257 = …` (折叠的 `with` 阻塞了合一), 写出即过; `𝟎ˢ ≅ˢ 𝟎ˢ` 的 `z≅` 要从 UniformS 导入 (`[ConstructorDoesNotTargetGivenType]`).
- §4 的 Python 搜索是有界的数值观察, 只用于找路径; 路径与终点由 `refl` 核对.
- 不改 `src/`、`archive/` 与已有的 Align 文件, README 未改.
