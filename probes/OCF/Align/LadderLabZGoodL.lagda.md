> **机械克隆, 验收用.** 由 `ScafLadderZGoodL` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.

> **机械克隆.** 由 `GoodL` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# $\psi_0(\Omega_\Omega\cdot2)$ 的无条件遗传标签

> 接 [GoodLBase](GoodLBase.lagda.md) (证书 `Goodᴸ`, `fs-mono₁`, 产出式的 `Pre0Vᴸ`) 与 [Omega2](Omega2.lagda.md) §3–§5. 本文是 Omega2 §5 出路 (a) 的决定性检验: 用 `Goodᴸ` 证书造出 $t_2=\psi_0(\Omega_\Omega\cdot2)$ 的计值树, 不带任何 oracle.
>
> 结论先说:
>
> 1. **`T2-label : Lab T2ᴸ t2` 是无条件定理 (§2)**, `T2ᴸ = forceᴸ (toZ t2ˢ) G2`, `G2 : Goodᴸ (toZ t2ˢ)` 是闭项. 第 $k$ 个链点的证书由同一个递归 (`Pre0Vᴸ`) 与它的标签一起造出, 输入是第 $k-1$ 个链点 (带标签 $\gamma'_k$) 的层号; Omega2 §3 的 `CertOracle` 不再需要. Omega2 停住的 $k=1$ (`γ′₂` 的证书) 与 `first-wall`/`second-wall` 处的闭包都在这个递归里: 它们的支配是 GoodLBase 的 `domᴸ` (闭包自带的地板 $w$ + `occ<` + `Lab-oc`).
> 2. **推论 (§3).** `T2-HS`, `T2-step : FGH T2ᴸ n ≡ FGH (χ n) n` (`refl`), `Q′-label`/`Q′-end` (Stage2 的 `Q′` 路径在新树上带标签 $\psi_0(\Omega_\Omega)$, 终点 $\cong$ `BTBOᴵ`), 与 Omega2 的树逐个 $\cong$: 对任意 oracle 的 `Chain.T2` (`agree-chain`), 对任意 Prefix 证书的 `force (toZ t2ˢ) G` (`agree-force`); 与 Symbolic 的静态前缀树不 $\cong$ (`old≇new`). 链点证书的 `Goodᴸ` 版 oracle 是定理 (`certᴸ`).
> 3. **$X_2$, $X_3$ 也由同一个递归得到** (`X₂L`, `X₃L`, 与 Stage2Label/Omega2Base 的计值树 $\cong$), 不再需要 `Good-ψ1` 或 `Bound`.
> 4. **对比表 (§4) 与下一阶段 (§5).** `Goodᴸ` 与阶段无关, 带标签地板在任意可数层都被覆盖; 需要改的是 `gŝ` 行的地板字段与 `domᴸ` ($\psi_\Omega$ 帧的地板 $\Omega$ 不可数), 以及多 $\hat\Omega$ 帧时的 `popL`.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块与 GoodLBase, 不改任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLabZGoodL where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import OCF.Align.Level
open import OCF.Align.LadderLabZPrefix using (Ord₊ˢ; Ordˢ; Ωˢ; toZ; Goodᶻ; force; t2ˢ)
import OCF.Align.NoCumsum as N
import OCF.Align.EBO as E
open E using (T; fsn; _<ᵀ_; []<)
open import OCF.Align.Correspond using (Lab; Lab-≅)
open import OCF.Align.LadderLabZStandardOmega using (γ′-NF; t2-NF)
open import OCF.Align.Stage2 using (t2; γ′ᴱ; diag2-fs; Q′; sq; walk; Lab-walk; Lab-uniq; ctx)
open import OCF.Align.Label using (BTBO-label)
open import OCF.Align.LadderLabZUniformS using (Ωˢ-refl; Ωˢ-≅; ψ1-≅; toZ-≅; _≅ˢ_; ŝ≅; z≅)
open import OCF.Align.LadderLabZStage2Label using (one⁰)
import OCF.Align.Symbolic as Sy
import OCF.Align.LadderLabZOmega2 as O2
open O2 using (t₀ᵗ; gᵗ; CertOracle; t2ˢ-label)
open import OCF.Align.LadderLabZGoodLBase
open import OCF.Align.Correspond using (l0; l1)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; n∷; nψ)
open import OCF.Align.LadderLabZPrefix using (X₂ˢ; X₂-NF; z2)
open import OCF.Align.Symbolic using (X₂ᵗ; X₃ᵗ)
open import OCF.Align.LadderLabZStage2Label using (X₃ˢ; z3; three; X₂ᶠ)
open import OCF.Align.LadderLabZDecouple using (X₂-label)
open import OCF.Align.LadderLabZOmega2Base using (X₃ᶠ; X₃-label; X₃-NF; nf3; lab3)
```


## §1 链点: 证书与标签一起

`lab-t₀ᴸ`/`lab-gᴸ` 是 Omega2 的 `lab-t₀`/`lab-g` 的产出式版本: 不再以证书为前提, 而是由 `Pre0Vᴸ` 对尾巴 $\Omega_1$ (或 $\Omega_{\mathtt{lvl}\,Y}$) 的 `LabL` 推导 (`LabL-Ω`) 递归造出证书与标签. 第 $k$ 个计值点 `gᵗ (lvl Y) e` $=\psi^{[\hat\Omega]}_0(\Omega_{\mathtt{lvl}\,Y})$ 对**一切**带标签 $\gamma'_{k+1}$ 的树 $Y$ 有 `Goodᴸ` 证书, 标签 $\gamma'_{k+2}$.

```agda
lab-t₀ᴸ : Σ (Goodᴸ (toZ t₀ᵗ)) λ G → Lab (forceᴸ _ G) (γ′ᴱ 1)
lab-t₀ᴸ = Pre0Vᴸ {p = zero} {σ = Sy.σ1 zero} {z = zero} (LabL-Ω one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _))
                (Ωˢ-refl (suc zero)) (γ′-NF 1)

lab-gᴸ : ∀ k Y (hY : HS Y) → Lab Y (γ′ᴱ (suc k)) → (e : suc zero ⊑ᴵ toLevel Y hY) →
         Σ (Goodᴸ (toZ (gᵗ (toLevel Y hY) e))) λ G → Lab (forceᴸ _ G) (γ′ᴱ (suc (suc k)))
lab-gᴸ k Y hY lY e =
  Pre0Vᴸ {p = lim 0 zero} {σ = λ q → lim 1 q} {z = lim 0 zero} (LabL-Ω Y hY lY (γ′-NF (suc k)) (≅ᴵ-refl _))
         (Ωˢ-refl _) (γ′-NF (suc (suc k)))
```


**`CertOracle` 的 `Goodᴸ` 版是定理.** Omega2 的 oracle 要的是 Prefix 的 `Goodᶻ`; 换成 `Goodᴸ` 后同一陈述无条件成立:

```agda
CertOracleᴸ : Set
CertOracleᴸ = ∀ k {Y} (hY : HS Y) → Lab Y (γ′ᴱ (suc k)) → (e : suc zero ⊑ᴵ toLevel Y hY) → Goodᴸ (toZ (gᵗ (toLevel Y hY) e))

certᴸ : CertOracleᴸ
certᴸ k {Y} hY lY e = proj₁ (lab-gᴸ k Y hY lY e)
```


## §2 $t_2$ 的证书与标签

`t2ˢ` 字面是第 0 层的闭包 `ŝ 1 t₀ᵗ gᵗ` (Omega2 §1), `toZ` 后是以自己为输出的待计值链. 链证书 `K2`: 标签序列 $\gamma'_{m+1}$, 第 0 点与分支取自 §1, 支配 $1\sqsubseteq^\mathsf I$ 由 `one⊑lab` (标签非零). 证书 `G2` 由 GoodLBase 的 `ĉᴸ-mk`: 输出就是链点 (`Gg` 在第 $k$ 个链点处), 单调由标签 (`mono-lab`, 即 `Lab-oc` + `fs-mono₁` 于 $t_2$).

```agda
K2 : CCᴸ (suc zero) (toZ t₀ᵗ) (λ η e → toZ (gᵗ η e))
K2 = ccᴸ (λ m → γ′ᴱ (suc m)) (proj₁ lab-t₀ᴸ) (proj₂ lab-t₀ᴸ) (one⊑lab _ (proj₂ lab-t₀ᴸ) (γ′-NF 1) []<)
         (λ m Y hY lY e → proj₁ (lab-gᴸ m Y hY lY e)) (λ m Y hY lY e → proj₂ (lab-gᴸ m Y hY lY e))
         (λ m Y hY lY e → one⊑lab _ (proj₂ (lab-gᴸ m Y hY lY e)) (γ′-NF (suc (suc m))) []<)

pt2 : ∀ k → Ptᴸ (suc zero) (λ m → γ′ᴱ (suc m)) k
pt2 = ptK K2

GL2 : Σ (Goodᴸ (toZ t2ˢ)) λ G → Lab (forceᴸ _ G) t2
GL2 = ĉᴸ-mk t2-NF refl K2 (proj₁ lab-t₀ᴸ) (subst (Lab _) (sym (diag2-fs 0)) (proj₂ lab-t₀ᴸ))
            (λ k → CCᴸ.Gg K2 k (Ptᴸ.x (pt2 k)) (Ptᴸ.hx (pt2 k)) (Ptᴸ.lx (pt2 k)) (Ptᴸ.dx (pt2 k)))
            (λ k → subst (Lab _) (sym (diag2-fs (suc k)))
                         (CCᴸ.lE K2 k (Ptᴸ.x (pt2 k)) (Ptᴸ.hx (pt2 k)) (Ptᴸ.lx (pt2 k)) (Ptᴸ.dx (pt2 k))))

G2 : Goodᴸ (toZ t2ˢ)
G2 = proj₁ GL2

T2ᴸ : Ordᶜ zero
T2ᴸ = forceᴸ (toZ t2ˢ) G2

T2-label : Lab T2ᴸ t2
T2-label = proj₂ GL2
```


**读法.** 这里没有 oracle、阶段系统或全局界. 第 $k+1$ 个链点 $\gamma'_{k+2}$ 的证书是 `lab-gᴸ k` 在第 $k$ 个链点 (`pt2 k`, 带标签 $\gamma'_{k+1}$) 的层号处的值; 它内部的一切闭包 (包括 Omega2 §4 的 `first-wall`: 目标 $\psi_0(\Omega_\Omega)$, 界 $\mathtt{lvl}\,\mathrm{BTBO}+1$; `second-wall`: 目标 $\psi_0(\Omega_\Omega)+1$) 都由 `Pre0L₊ᴸ` 的 `gŝ` 情形 (`ŝChainᴸ`) 处理, 支配 `domᴸ` 只用该闭包的地板 $w$ 与链点的标签. 闭包只在带标签的点处计值, 所以 Omega2 §5 说的 "无标签位置上界为 $\mathtt{lvl}\,\mathrm{BTBO}+1$ 的闭包" 根本不出现.

## §3 推论

`χ n` 是第 $n$ 项 (`χ 0` 是第 0 个链点, `χ (k+1)` 是第 $k$ 个链点处的计值, 即第 $k+1$ 个链点). FGH 的递归方程是 `refl`: `forceᴸ` 在 `gc` 处字面是 `lim (outsᴸ …)`.

```agda
χ : ℕ → Ordᶜ zero
χ = outsᴸ (forceᴸ _ (proj₁ lab-t₀ᴸ))
          (λ k → forceᴸ _ (CCᴸ.Gg K2 k (Ptᴸ.x (pt2 k)) (Ptᴸ.hx (pt2 k)) (Ptᴸ.lx (pt2 k)) (Ptᴸ.dx (pt2 k))))

_ : T2ᴸ ≡ lim χ
_ = refl

T2-HS : HS T2ᴸ
T2-HS = forceᴸ-HS _ G2

T2-step : ∀ n → FGH T2ᴸ n ≡ FGH (χ n) n
T2-step n = refl

χ-label : ∀ k → Lab (χ (suc k)) (γ′ᴱ (suc (suc k)))
χ-label k = CCᴸ.lE K2 k (Ptᴸ.x (pt2 k)) (Ptᴸ.hx (pt2 k)) (Ptᴸ.lx (pt2 k)) (Ptᴸ.dx (pt2 k))

_ : ∀ k → χ (suc k) ≡ Ptᴸ.x (pt2 (suc k))
_ = λ k → refl
```


**Stage2 的 `Q′`.** 17 步, 旧的静态前缀树走到 `zero` (Symbolic 的 `C2-unlabel`); 新树上带标签 $\psi_0(\Omega_\Omega)$, 终点 $\cong$ `BTBOᴵ`. 与 Omega2 的 `Q′-label` 同一个证明, 链点标签换成 `χ-label 0`.

```agda
Q′-label : Lab (walk (sq T2ᴸ 1) Q′) (E.EBOψ 2)
Q′-label = Lab-walk Q′ (χ-label 0) (refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl ,
                                    refl , refl , refl , refl , refl , refl , tt)

Q′-end : walk (sq T2ᴸ 1) Q′ ≅ N.BTBOᴵ
Q′-end = Lab-uniq Q′-label BTBO-label
```


**与已有的树对上.** 遗传标签决定树 (模 $\cong$, Stage2 的 `Lab-uniq`). 所以 Omega2 的两个条件定理的树都 $\cong$ 本文的树: 对任意 oracle 的 `Chain.T2`, 对任意 Prefix 证书的计值树. Symbolic 的静态前缀树 `Sy.T2` 不 $\cong$ (否则它带标签, 与 `C2-unlabel` 矛盾).

```agda
agree-chain : (Cert : CertOracle) → O2.Chain.T2 Cert ≅ T2ᴸ
agree-chain Cert = Lab-uniq (O2.Chain.T2-label Cert) T2-label

agree-force : (G : Goodᶻ (toZ t2ˢ)) → force (toZ t2ˢ) G ≅ T2ᴸ
agree-force G = Lab-uniq (t2ˢ-label G) T2-label

t2-refl : t2ˢ ≅ˢ t2ˢ
t2-refl = ŝ≅ refl (≅ᴵ-refl _)
  (ψ1-≅ {p = zero} {σ = Sy.σ1 zero} {p′ = zero} {σ′ = Sy.σ1 zero} {z = zero} {z′ = zero} z≅ (Ωˢ-refl (suc zero)))
  (λ η e η′ e′ eη → ψ1-≅ {p = lim 0 zero} {σ = λ q → lim 1 q} {p′ = lim 0 zero} {σ′ = λ q → lim 1 q}
                          {z = lim 0 zero} {z′ = lim 0 zero} z≅ (Ωˢ-≅ eη))

agree-self : (G : Goodᴸ (toZ t2ˢ)) → forceᴸ (toZ t2ˢ) G ≅ T2ᴸ
agree-self G = forceᴸ-≅ (toZ-≅ t2-refl) G G2

old≇new : ¬ (Sy.T2 ≅ T2ᴸ)
old≇new e = Sy.C2-unlabel (Lab-≅ e T2-label)
```


**$X_2$, $X_3$ 也由同一个递归得出.** $X_2=\psi_0(\Omega_\Omega+\Omega_2)$ 与 $X_3=\psi_0(\Omega_\Omega+\Omega_3)$ 的 `Goodᴸ` 证书与标签由 `Pre0Vᴸ` 一次给出 (不用 Stage2Label 的 `Good-ψ1` 或 Omega2Base 的 `Bound three`), 计值树与已有的 `X₂ᶠ`/`X₃ᶠ` 逐个 $\cong$ (`Lab-uniq` 对 Decouple 的 `X₂-label`、Omega2Base 的 `X₃-label`).

```agda
nf2 : NF₁ (E.natT 2)
nf2 = ext X₂-NF
  where
  ext : NF₁ X₂ᵗ → NF₁ (E.natT 2)
  ext (n∷ (nψ _ _ (n∷ _ (n∷ (nψ n2 _ _ _) _ _) _) _) _ _) = n2

lab2 : Lab (natᶜ 2) (E.natT 2)
lab2 = l1 refl (≅-refl⁰ _) (l1 refl (≅-refl⁰ _) (l0 refl z≅))

X₂L : Σ (Goodᴸ (toZ X₂ˢ)) λ G → Lab (forceᴸ _ G) X₂ᵗ
X₂L = Pre0Vᴸ {p = z2} {σ = λ q → q} {z = z2} (LabL-Ω (natᶜ 2) (natᶜ-HS 2) lab2 nf2 (≅ᴵ-refl _)) (Ωˢ-refl _) X₂-NF

X₃L : Σ (Goodᴸ (toZ X₃ˢ)) λ G → Lab (forceᴸ _ G) X₃ᵗ
X₃L = Pre0Vᴸ {p = z3} {σ = λ q → q} {z = z3} (LabL-Ω (natᶜ 3) (natᶜ-HS 3) lab3 nf3 (≅ᴵ-refl three)) (Ωˢ-refl three) X₃-NF

X₂-agree : forceᴸ _ (proj₁ X₂L) ≅ X₂ᶠ
X₂-agree = Lab-uniq (proj₂ X₂L) X₂-label

X₃-agree : forceᴸ _ (proj₁ X₃L) ≅ X₃ᶠ
X₃-agree = Lab-uniq (proj₂ X₃L) X₃-label
```


**小输入.** `FGH T2ᴸ 0` 算得出 (`refl`, 约 5 秒); `FGH T2ᴸ 1` 在 300 秒内未算完 (临时文件, 不进本文), 与 NoCumsum 里参数 2 起的超时同类.

```agda
_ : FGH T2ᴸ 0 ≡ 1
_ = refl
```


## §4 对比表: `Goodᶻ` 与 `Goodᴸ`

| | Prefix 的 `Goodᶻ` (+ UniformS/Omega2Base 的 `Good`/`Bound`) | GoodLBase 的 `Goodᴸ` |
|---|---|---|
| 分支的证书 `Gg` | 一切 $\eta\sqsupseteq c$ | 只在带标签 $\gamma_m$ 的树 $Y$ 的层号处 |
| 可容许性 | 无 | 证书字段 `γ : ℕ → T` + `l₀`/`lE` (下一点带标签 $\gamma_{m+1}$) |
| 支配 `d₀`/`dE` | 一切 $\eta$; 由全局界 `Strictᵝ β` (只到 $\mathtt{lvl}\,\mathrm{BTBO}$, `no-Bound`) | 只在链点处; 由闭包自己的地板 $w$ + `occ<` + `Lab-oc` (`domᴸ`) |
| 链的单调 `m₀`/`mE` | 有 (一切 $\eta\sqsubseteq\eta'$) | 无 (不需要) |
| 输出证书 `Go` | 一切 $\eta$ | 只在链点处 (类型里由 `ptsᴸ` 生成链点) |
| 输出单调 | 一切 $\eta\sqsubseteq\eta'$; 观测前序 $\sqsubseteq^\mathsf o$ | 相邻链点; 由标签 (`Lab-oc` + `fs-mono₁`) |
| 宇宙 | `Set` | `Set` |
| 证书的来源 | 好性理论 (`Good-ψ1`, 观测前序, 严格性) | 与标签同一个递归 (`Pre0Vᴸ`) |
| 标签的形式 | `∀ G → Lab (force G) t` | `Σ G (Lab (forceᴸ G) t)` |
| `t₂` 的证书 | $k=0$ 无条件, $k=1$ 停 | **全部链点, 无条件** (`G2`) |
| `Lab T2 t2` | 以 `CertOracle` 为前提 | **无条件** (`T2-label`) |

## §5 对下一阶段的影响

- **`Goodᴸ` 本身与阶段无关.** 它只说第 0 层的待计值链在带标签的点处计值, 标签序列 $\gamma$ 是任意的记号项序列; 可容许点覆盖一切 "带标签的可数树的层号", 在任意 (可数) 高度上都适用, 例如 $\mathtt{lvl}\,\mathrm{BTBO}+1$、$\mathtt{lvl}\,\gamma'_k$ 及以上. 所以 "带标签的地板在任意层" 已被覆盖, 不需要再改 `Goodᴸ`.
- **$\psi_0(\Omega_\Omega\cdot k)$, $\psi_0(\Omega_\Omega^2)$ 一类 (多个 $\hat\Omega$ 帧).** Prefix 的 $\psi^P$ 已支持长度 $n$ 的栈, 但本文的 `PreL₊`/`Pre0Vᴸ` 只写了单帧 `ψ1`; 多帧时弹出一帧得到的闭包的第 0 点与分支仍带前缀 (不是 `PsiVL` 能处理的无前缀树), `popL` 的分支要改调带前缀的引理, `ctx`/`ctxw` 要带前缀长度. 地板字段与 `domᴸ` 不变 ($w$ 仍是弹栈目标的可数下标, 出现在链点里).
- **$\psi_0(\Omega_{\Omega+1})$ 与 $\psi_\Omega$ 帧.** StandardOmega 记下: $\psi_0(\Omega_{\Omega+1})$ 的链在层 $\Omega$. 树侧没有层号为 $\Omega$ 的树, 需要新的栈帧 (例如 "$\psi_\Omega$ 帧", 其弹出产生以 $\Omega$ 为目标的闭包). 那种闭包的地板是 $w=\Omega$: 它没有 `Idx` (不是可数树的标签), `occ<` 也不适用 ($\Omega$ 不小于任何可数链点). 所以需要 $\psi_\Omega$ 帧的字段恰是 `LabL` 的 `gŝ` 行的地板 (`Iw`, 界 $c\sqsubseteq\mathtt{lvl}\,w+1$, `Occ`) 与 `domᴸ`; 那里的支配要换成 "层 $\Omega$ 的链由下一层的对角线计值" 的新论证. `Goodᴸ` 的 `gc`、`limᴸ`/`ĉᴸ-mk`、`mono-lab`/`fs-mono₁` 不受影响 (`fs-mono₁` 已对 `Sb` 的 $\Omega+c$ 下标成立, 只要整项是 `NF₁`).

## §6 结论与边界

**字面成立 (`refl`):** `T2ᴸ ≡ lim χ`; `T2-step : FGH T2ᴸ n ≡ FGH (χ n) n`; `χ (suc k) ≡ Ptᴸ.x (pt2 (suc k))` (输出就是链点); `Q′-label` 用到的 17 个 `cof … ≡ cω`; `FGH T2ᴸ 0 ≡ 1`.

**定理 (标签按 Correspond 的 `Lab`, 树只到 $\cong$):**

1. `lab-t₀ᴸ`, `lab-gᴸ`, **`certᴸ : CertOracleᴸ`** (Omega2 的 oracle 的 `Goodᴸ` 版, 无条件).
2. `K2`, **`G2 : Goodᴸ (toZ t2ˢ)`** (闭项), **`T2-label : Lab T2ᴸ t2`** (无条件), `T2-HS`, `χ-label`.
3. `Q′-label`, `Q′-end : walk (sq T2ᴸ 1) Q′ ≅ BTBOᴵ`; `agree-chain : ∀ Cert → O2.Chain.T2 Cert ≅ T2ᴸ`; `agree-force : ∀ (G : Goodᶻ (toZ t2ˢ)) → force (toZ t2ˢ) G ≅ T2ᴸ`; `agree-self : ∀ (G : Goodᴸ (toZ t2ˢ)) → forceᴸ (toZ t2ˢ) G ≅ T2ᴸ`; `old≇new`.
4. `X₂L`, `X₃L` 与 `X₂-agree`/`X₃-agree`.

**标签状态.** 按 README 的认证准则: $\psi_0(\Omega_\Omega\cdot2)$ 的遗传标签是**无条件定理** (`T2-label`; 树是 `Goodᴸ` 证书下的计值树 `T2ᴸ`, 外层 FGH 方程字面成立, 每一层的方程模 $\cong$). 所以 $\psi_0(\Omega_\Omega\cdot2)$ 的树 `T2ᴸ` 的 FGH 在每个深度满足 EBO 沿 $\psi_0(\Omega_\Omega\cdot2)$ 的递归方程. Omega2 的两个条件定理的前提 (`Goodᶻ` 证书 / `CertOracle`) 仍未得, 但它们的树 (若存在) 都 $\cong$ `T2ᴸ`.

**精确的停点 (Omega2 §4) 如何解除.** $k=1$ 的 $\gamma'_2$ 的证书是 `lab-gᴸ 0` 在第 0 个链点处的第一分量. `first-wall` 处的闭包 (目标 $\psi_0(\Omega_\Omega)$, 界 $\mathtt{lvl}\,\mathrm{BTBO}+1$) 与 `second-wall` 处的闭包 (目标 $\psi_0(\Omega_\Omega)+1$) 在 `Pre0L₊ᴸ` 的 `gŝ` 子句里得到证书: 它们的地板分别是 $\psi_0(\Omega_\Omega)$ 与 $\psi_0(\Omega_\Omega)+1$ (由 `popL` 记下), 链点 $\psi_0(\Omega_\Omega+\cdots\psi_{w}(\Omega_{\theta_m})\cdots)$ 带标签, `occ<` 给 $w<$ 链点. Omega2 §5 说的 "无标签的 $\eta$ 处界为 $\mathtt{lvl}\,\mathrm{BTBO}+1$ 的新闭包" 在 `Goodᴸ` 下不需要证书.

**边界.**

- 新树 `T2ᴸ` 与 Omega2 的条件树、Prefix 的计值树只到 $\cong$ (`lim` 下的函数头不同, 且证书不同); 与 Symbolic 的静态前缀树不 $\cong$.
- `FGH T2ᴸ 1` 未在 300 秒内算完 (数值核对只到参数 0).
- 本文只处理 $\psi_0(\Omega_\Omega\cdot2)$ 及其后代 (单 $\hat\Omega$ 帧). $\psi_0(\Omega_\Omega^\Omega)$、$\psi_0(\Omega_{\Omega+1})$ 见 §5.
- 不改 `src/`、`archive/` 与已有的 Align 文件, README 未改.
