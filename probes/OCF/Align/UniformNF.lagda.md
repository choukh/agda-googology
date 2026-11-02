# 统一折叠上的记号无关证书 (三): `Goodᴺ`、四个决定性检验与验收

> 接 [UniformNFBase](UniformNFBase.lagda.md) (统一折叠上的观测前序、地板、出现不变量) 与 [UniformNFDepth0](UniformNFDepth0.lagda.md) (`Floor`、参数化折叠定理、$\Omega_\Omega$ 闭包的好性、`Strict₁`). 本文做记号无关的证书与验收.
>
> 结论先说:
>
> 1. **`Goodᴺ` 在统一形上不需要新定义 (§1).** 统一折叠在第 0 层的输出是 `Ordˢ zero`, 经 `toZ` 就是 Prefix 的 `Z`; NotFree 的 `Goodᴺ`/`forceᴺ`/`forceᴺ-≅`/`ofZ`/`ofL` 原样适用. 本文的证书先以 Prefix 的 `Goodᶻ` 形式造出 (`Floor.Good→Goodᶻ`), 再经 `ofZ` 得 `Goodᴺ`; 计值与证书无关 (`forceᴺ-≅`), 所以验收只需一个带标签的证书.
> 2. **自举 (§2).** 第 0 级: `Floor` 在 $\beta=0$、支配平凡处实例化, 得 $\Omega_\Omega$ 闭包 (BTBO, `GᵁBTBO`, 任意环境) 与 $\gamma'_1=\psi_0(\Omega_\Omega+\Omega_1)$ 的证书 `Gγ′₁` (环境 `suc zero`, 唯一目标 0, 没有非零目标的弹栈). 第 1 级: 以 $\gamma'_1$ 的证书为覆盖 (`cov₁ : CovΛ P̂ 1 β₀`, $\beta_0=\mathtt{lvl}\,\gamma'_1$), 支配 `S⁺₁ = dom-cov · cov₁`, 得 **$X_2=\psi_0(\Omega_\Omega+\Omega_2)$ 的证书 `GX₂`** (环境 2, 目标 1 的弹栈界 $2\sqsubseteq\beta_0$ 由 `Strict₁`) 与 **$\gamma'_2=\psi_0(\Omega_\Omega+\Omega_{\beta_0})$ 的证书 `Gγ′₂`** (环境 $\beta_0+1$; 目标 $\beta_0$ 永不到达, 目标条件只对 $\beta_0$ 的子层号), 以及一切 $\psi_0(\Omega_\Omega+\Omega_\eta)$, $\eta\sqsubseteq\beta_0$ (`cert-g`). 全部不读记号.
> 3. **验收 (§3, 记号只在这里).** 标签由 Uniform2Base 的 `GA0-Ω̂`/`tlGR` 对**同一棵** $P̂$-树给出 (对一切环境与证据), 经 `forceᴺ-≅` 搬到记号无关的证书上: `BTBOᵁ` 的计值 $\cong$ NoCumsum 的 `BTBOᴵ`, $\gamma'_1$、$X_2$ 的计值 $\cong$ Uniform2 的 `pΩ-label`/`pΩ₂-label` 的树, $\gamma'_2$ 带标签 $\gamma'_2$. $\psi_0(\Omega_\Omega\cdot2)$ 不在本文 (并行工作).
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件. §1–§2 不引用记号; §3 导入记号模块.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Ordˢ; toZ; Ωˢ; Goodᶻ; force; force-HS)
open import OCF.Align.UniformS using (_≅ˢ_; z≅; ≅ˢ-sym; Ωˢ-refl; Ωˢ-≅; toZ-≅; two; force-≅; Goodᶻ-tr)
open import OCF.Align.Uniform2Base using (Flr; fz; fk; _⊔_; Ev; Run; fold; Ω̂A; ∅ᴿ; flo; cvFlo; _≈ᴿ_; fold-≅0)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-HS; forceᴺ-≅; ofZ; ofZ-≅; ofL; ofL-≅)
open import OCF.Align.UniformNFBase
open import OCF.Align.UniformNFDepth0
```

## §1 `Goodᴺ` 在统一形上

统一折叠的目标 0 输出 `x : Ordˢ zero` 经 `toZ` 是 `Z`, NotFree 的 `Goodᴺ (toZ x)` 直接是它的记号无关证书类型: 预言链 `ys`, 可容许点 = 闭包自己的链点, `forceᴺ` 只读输出. 两个桥: `ofZ` (从 Prefix 证书, 本文的证书都这样造) 与 `ofL` (从 Uniform2 的 `Lab₀` 证书遗忘标签, §3). 计值与证书无关 (`forceᴺ-≅`), 在自互模拟的树上: 同一棵树的任意两个 `Goodᴺ` 证书计值 $\cong$.

```agda
Goodᴺᵁ : Ordˢ zero → Set
Goodᴺᵁ x = Goodᴺ (toZ x)

indepᴺ : ∀ {x : Ordˢ zero} → x ≅ˢ x → (G G′ : Goodᴺᵁ x) → forceᴺ _ G ≅ forceᴺ _ G′
indepᴺ ex G G′ = forceᴺ-≅ (toZ-≅ ex) G G′
```

## §2 自举: 从 $\beta=0$ 到 $\beta_0=\mathtt{lvl}\,\gamma'_1$

**前缀.** $P̂=$ `Ω̂A 0 ∅ᴿ` ($\Omega_\Omega$ 闭包作用于空前缀), `Run (fz ⊔ fk zero)`; 自互模拟与地板由 Base.

```agda
P̂ : Run (fz ⊔ fk zero)
P̂ = Ω̂A 0 ∅ᴿ

rP̂ : P̂ ≈ᴿ P̂
rP̂ = rΩ̂ r∅

fP̂ : FlR P̂
fP̂ = FlR-Ω̂ r∅ FlR-∅
```

**第 0 级: $\beta=0$.** 支配 `ColC P̂ 0 y` 平凡 (`z⊑`), 再生条件平凡. 这一级能证的是环境里没有非零目标的树: $\Omega_\Omega$ 闭包本身在目标 0 (任意环境, `Tgβ 0` 空真), 与 $\gamma'_1$ 在环境 `suc zero`.

```agda
module F0 = FloorΩ̂ zero zero (λ _ _ _ → z⊑) (λ _ _ _ → z⊑)

BTBOᵁ : ∀ {ℓ} (ev : Ev ℓ (fz ⊔ fk zero)) (z : zero <ᴵ ℓ) → Ordˢ zero
BTBOᵁ ev z = P̂ ev z

GᵁBTBO : ∀ {ℓ} (ev : Ev ℓ (fz ⊔ fk zero)) (z : zero <ᴵ ℓ) → Goodᶻ (toZ (BTBOᵁ ev z))
GᵁBTBO ev z = F0.Good→Goodᶻ (F0.Pop.goodΩ̂∅ ev z (λ ()))

GᴺBTBO : ∀ {ℓ} (ev : Ev ℓ (fz ⊔ fk zero)) (z : zero <ᴵ ℓ) → Goodᴺᵁ (BTBOᵁ ev z)
GᴺBTBO ev z = ofZ (GᵁBTBO ev z)

ev₁ : Ev (suc zero) ((fz ⊔ fk zero) ⊔ flo (suc zero))
ev₁ = (tt , (λ q → q)) , (λ q → q)

γ′₁ᵁ : Ordˢ zero
γ′₁ᵁ = χ̂ P̂ (suc zero) ev₁ zero

tk₁ : ∀ {j} → j <ᴵ suc zero → F0.Tgβ j
tk₁ zero    = λ ()
tk₁ (suc ())

Gγ′₁ : Goodᶻ (toZ γ′₁ᵁ)
Gγ′₁ = F0.Good→Goodᶻ (F0.Good-foldP {φ = flo (suc zero)} {cv = cvFlo (suc zero)} ev₁ zero (λ ()) tk₁ (F0.Good-Ω (suc zero)) (Ωˢ-refl (suc zero)))

Gᴺγ′₁ : Goodᴺᵁ γ′₁ᵁ
Gᴺγ′₁ = ofZ Gγ′₁
```

**第 1 级: 以 $\gamma'_1$ 为覆盖.** 以 $\gamma'_1$ 的任一证书 $G_1$ 为参数 (工程注记: 证书别名写进类型会让检查器展开它, NotFree/TreeNF 的 300 s 教训), $\beta_0$ 是它的层号. $1\sqsubseteq\beta_0$ 由 `Strict₀` (前缀有地板), $2\sqsubseteq\beta_0$ 由 `Strict₁` (以 BTBO 闭包的证书为参数). 覆盖 `cov₁`、支配 `S⁺₁`, 实例 `F1`.

```agda
zlt : ∀ {b} → suc zero ⊑ᴵ b → zero <ᴵ b
zlt (s⊑ z≅ q) = q

module Chain (G₁ : Goodᶻ (toZ γ′₁ᵁ)) where
  β₀ : Ordᴵ
  β₀ = toLevel (force _ G₁) (force-HS _ G₁)

  1⊑β₀ : suc zero ⊑ᴵ β₀
  1⊑β₀ = Strict₀ {φ = flo (suc zero)} {P = P̂} {cv = cvFlo (suc zero)} {ev = ev₁} {z = zero} rP̂ fP̂ (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)) G₁

  G₀ : Goodᶻ (toZ (P̂ (proj₁ ev₁) zero))
  G₀ = GᵁBTBO (proj₁ ev₁) zero

  2⊑β₀ : two ⊑ᴵ β₀
  2⊑β₀ = Strict₁ (proj₁ ev₁) zero {φ = flo (suc zero)} {cv = cvFlo (suc zero)} ev₁ refl G₀ (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)) G₁

  cov₁ : CovΛ P̂ (suc zero) β₀
  cov₁ = suc zero , ev₁ , zero , G₁ , ⊑ᴵ-refl

  S⁺₁ : ∀ {k} {y : Ordˢ k} → FlΛ (suc zero) y → ColC P̂ β₀ y
  S⁺₁ fl = dom-cov rP̂ fl cov₁

  module F1 = FloorΩ̂ (suc zero) β₀ S⁺₁ one⊑
```

**$X_2=\psi_0(\Omega_\Omega+\Omega_2)$.** 环境 `two`, 尾巴 $\Omega_2$ 的地板 `flo two = fk 1`; 目标 1 的弹栈界 2 由 `2⊑β₀` 覆盖.

```agda
  ev₂ : Ev two ((fz ⊔ fk zero) ⊔ flo two)
  ev₂ = (tt , (λ q → suc q)) , (λ q → q)

  X₂ᵁ : Ordˢ zero
  X₂ᵁ = χ̂ P̂ two ev₂ (suc zero)

  tk₂ : ∀ {j} → j <ᴵ two → F1.Tgβ j
  tk₂ zero          = λ _ → 2⊑β₀
  tk₂ (suc zero)    = λ ()
  tk₂ (suc (suc ()))

  GX₂ : Goodᶻ (toZ X₂ᵁ)
  GX₂ = F1.Good→Goodᶻ (F1.Good-foldP {φ = flo two} {cv = cvFlo two} ev₂ (suc zero) (λ ()) tk₂ (F1.Good-Ω two) (Ωˢ-refl two))

  GᴺX₂ : Goodᴺᵁ X₂ᵁ
  GᴺX₂ = ofZ GX₂
```

**$\gamma'_2=\psi_0(\Omega_\Omega+\Omega_{\beta_0})$ 与一切 $\psi_0(\Omega_\Omega+\Omega_\eta)$, $\eta\sqsubseteq\beta_0$.** 尾巴 $\Omega_\eta$ 的地板取 `fk η` (证据 `Simᴵ (suc η) ℓ`, 与 $\beta_0$ 的形状无关), 环境 `suc η`; 到达的目标是 0 与 $\eta$ 的子层号 $j<^\mathsf I\eta\sqsubseteq\beta_0$, 弹栈界 $j+1\sqsubseteq\beta_0$ (`sim`). 目标 $\eta$ 本身在环境里但永不到达 (Depth0 §6 第 3 条).

```agda
  σ₁ : ∀ η → zero <ᴵ η → Simᴵ (suc zero) (suc η)
  σ₁ η z zero    = suc z
  σ₁ η z (suc ())

  evη : ∀ η → zero <ᴵ η → Ev (suc η) ((fz ⊔ fk zero) ⊔ fk η)
  evη η z = (tt , σ₁ η z) , (λ q → q)

  Xη : ∀ η → zero <ᴵ η → Ordˢ zero
  Xη η z = fold 0 (fk η) (λ e q → e (suc q)) P̂ (Ωˢ η) (evη η z) (suc z)

  cert-g : ∀ η (z : zero <ᴵ η) → η ⊑ᴵ β₀ → Goodᶻ (toZ (Xη η z))
  cert-g η z h = F1.Good→Goodᶻ (F1.Good-foldP {φ = fk η} {cv = λ e q → e (suc q)} (evη η z) (suc z) (λ ())
                                              (λ j< _ → s⊑′ (sim h j<)) (F1.Good-Ω η) (Ωˢ-refl η))

  z<β₀ : zero <ᴵ β₀
  z<β₀ = zlt 1⊑β₀

  γ′₂ᵁ : Ordˢ zero
  γ′₂ᵁ = Xη β₀ z<β₀

  Gγ′₂ : Goodᶻ (toZ γ′₂ᵁ)
  Gγ′₂ = cert-g β₀ z<β₀ ⊑ᴵ-refl

  Gᴺγ′₂ : Goodᴺᵁ γ′₂ᵁ
  Gᴺγ′₂ = ofZ Gγ′₂

module C = Chain Gγ′₁
```

**读法.** 四个证书 (`GᵁBTBO`、`Gγ′₁`、`C.GX₂`、`C.Gγ′₂`) 的构造只用 Base/Depth0 的定理: 观测前序、地板、覆盖、支配定理、折叠定理. 与 TreeNF 的 `cert-g` 对比: 那里 `Floor.Good-ψ1` 要 `ℓ ⊑ᴵ β`, 环境取 `Mlev 1 η e`; 这里统一形的地板证据 `Simᴵ (suc η) ℓ` 迫使环境 $\ell\sqsupseteq\eta+1$, 所以环境条件换成只对到达目标的 `tk`.

## §3 验收 (记号只在这里)

标签全部由 Uniform2Base 的深度 0 标签理论对**同一棵** $P̂$-树给出: `GA0-Ω̂ good∅ᴿ : GA0 P̂ (ΩΩ ∷ [])` (对一切环境与证据), 尾巴 $\Omega_\eta$ 的折叠经 `tlGR` 与 `LabL-Ω`. 验收的形式 (NotFree `any-T2` 的形式): 记号无关证书 $G$ 与带标签证书 $L$ 在同一棵自互模拟的树上, `forceᴺ-≅` 给 `force G ≅ forceᴸ L`, 标签经 `Lab-≅` 搬到 $G$ 的计值上. 再用 `Lab-uniq` 与 Uniform2 的校准树 (`pΩ-label`/`pΩ₂-label`) 或 NoCumsum 的 `BTBOᴵ` 对上.

```agda
open import Data.List using ([]; _∷_; _++_)
import OCF.Align.EBO as E
open E using (T; natT; Ωt)
open import OCF.Align.Correspond using (Lab; Lab-≅)
open import OCF.Align.Stage2 using (Lab-uniq; γ′ᴱ)
open import OCF.Align.StandardOmega using (NF₁; γ′-NF)
open import OCF.Align.Stage2Label using (one⁰; BTBO-NF)
open import OCF.Align.Label using (BTBO-label)
import OCF.Align.NoCumsum as N
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.GoodLBase using (LabL; LabL-Ω; lab1; nf1; Goodᴸ; forceᴸ)
open import OCF.Align.Prefix using (X₂-NF)
open import OCF.Align.Symbolic using (X₂ᵗ)
open import OCF.Align.Uniform2Base using (GR; g0; GA0; GA0-Ω̂; tlGR; Lab₀; ψ₀ᵗ)
open import OCF.Align.Uniform2 using (good∅ᴿ; LΩ2; nf-pΩ; pΩ-label; pΩ₂-label)

GRP̂ : GR P̂ (ΩΩ ∷ [])
GRP̂ = proj₂ (GA0-Ω̂ good∅ᴿ)

module Accept {x : Ordˢ zero} {t : T} (G : Goodᶻ (toZ x)) (L : Lab₀ x t) (ex : x ≅ˢ x) where
  agree : force _ G ≅ forceᴸ _ (proj₁ L)
  agree = ≅-trans (≅-sym (ofZ-≅ G)) (≅-trans (forceᴺ-≅ (toZ-≅ ex) (ofZ G) (ofL (proj₁ L))) (ofL-≅ (proj₁ L)))

  label : Lab (force _ G) t
  label = Lab-≅ agree (proj₂ L)

  labelᴺ : Lab (forceᴺ _ (ofZ G)) t
  labelᴺ = Lab-≅ (ofZ-≅ G) label
```

**BTBO.** $P̂$ 在目标 0 的值带标签 $\psi_0(\Omega_\Omega)$ (`g0 GRP̂`); 与 NoCumsum 的 `BTBOᴵ` 同标签 (`BTBO-label`), 故计值 $\cong$ `BTBOᴵ`, 对一切环境与证据.

```agda
LBTBO : ∀ {ℓ} (ev : Ev ℓ (fz ⊔ fk zero)) (z : zero <ᴵ ℓ) → Lab₀ (BTBOᵁ ev z) (ψ₀ᵗ (ΩΩ ∷ []))
LBTBO ev z = g0 GRP̂ ev z BTBO-NF

module AB {ℓ} (ev : Ev ℓ (fz ⊔ fk zero)) (z : zero <ᴵ ℓ) = Accept (GᵁBTBO ev z) (LBTBO ev z) (rP̂ ev z ev z (≅ᴵ-refl zero))

BTBO-label′ : ∀ {ℓ} (ev : Ev ℓ (fz ⊔ fk zero)) (z : zero <ᴵ ℓ) → Lab (force _ (GᵁBTBO ev z)) (ψ₀ᵗ (ΩΩ ∷ []))
BTBO-label′ ev z = AB.label ev z

BTBOᵁ-≅ : ∀ {ℓ} (ev : Ev ℓ (fz ⊔ fk zero)) (z : zero <ᴵ ℓ) → force _ (GᵁBTBO ev z) ≅ N.BTBOᴵ
BTBOᵁ-≅ ev z = Lab-uniq (BTBO-label′ ev z) BTBO-label
```

**$\gamma'_1$.** 标签 $\psi_0(\Omega_\Omega+\Omega_1)=\gamma'^{\mathsf E}_1$; 与 Uniform2 `pΩ-label` 的树 (任意环境) 计值 $\cong$.

```agda
Lγ′₁ : Lab₀ γ′₁ᵁ (ψ₀ᵗ (ΩΩ ∷ Ωt (natT 1)))
Lγ′₁ = g0 (tlGR {P = P̂} GRP̂ {φ = flo (suc zero)} {cv = cvFlo (suc zero)} (LabL-Ω one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _)) (Ωˢ-refl (suc zero)))
          ev₁ zero nf-pΩ

exγ′₁ : γ′₁ᵁ ≅ˢ γ′₁ᵁ
exγ′₁ = fold-≅0 {φ = flo (suc zero)} {φ′ = flo (suc zero)} {cv = cvFlo (suc zero)} {cv′ = cvFlo (suc zero)} {P = P̂} {P′ = P̂}
                rP̂ (Ωˢ-refl (suc zero)) ev₁ zero ev₁ zero (≅ᴵ-refl zero)

module A₁ = Accept Gγ′₁ Lγ′₁ exγ′₁

γ′₁-label : Lab (force _ Gγ′₁) (γ′ᴱ 1)
γ′₁-label = A₁.label

γ′₁ᵁ-≅ : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → force _ Gγ′₁ ≅ forceᴸ _ (proj₁ (pΩ-label ev z))
γ′₁ᵁ-≅ ev z = Lab-uniq γ′₁-label (proj₂ (pΩ-label ev z))
```

**$X_2$ 与 $\gamma'_2$** (在 `Chain Gγ′₁` 内; $\gamma'_2$ 的尾巴 $\Omega_{\beta_0}$ 的标签 `LabL-Ω` 以 $\gamma'_1$ 的标签为见证).

```agda
module AcceptChain where
  open C

  LX₂ : Lab₀ X₂ᵁ X₂ᵗ
  LX₂ = g0 (tlGR {P = P̂} GRP̂ {φ = flo two} {cv = cvFlo two} LΩ2 (Ωˢ-refl two)) ev₂ (suc zero) X₂-NF

  exX₂ : X₂ᵁ ≅ˢ X₂ᵁ
  exX₂ = fold-≅0 {φ = flo two} {φ′ = flo two} {cv = cvFlo two} {cv′ = cvFlo two} {P = P̂} {P′ = P̂} rP̂ (Ωˢ-refl two) ev₂ (suc zero) ev₂ (suc zero) (≅ᴵ-refl zero)

  module A₂ = Accept GX₂ LX₂ exX₂

  X₂-label : Lab (force _ GX₂) X₂ᵗ
  X₂-label = A₂.label

  X₂ᵁ-≅ : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → force _ GX₂ ≅ forceᴸ _ (proj₁ (pΩ₂-label ev z))
  X₂ᵁ-≅ ev z = Lab-uniq X₂-label (proj₂ (pΩ₂-label ev z))

  Lγ′₂ : Lab₀ γ′₂ᵁ (γ′ᴱ 2)
  Lγ′₂ = g0 (tlGR {P = P̂} GRP̂ {φ = fk β₀} {cv = λ e q → e (suc q)}
                  (LabL-Ω (force _ Gγ′₁) (force-HS _ Gγ′₁) γ′₁-label (γ′-NF 1) (≅ᴵ-refl β₀)) (Ωˢ-refl β₀))
            (evη β₀ z<β₀) (suc z<β₀) (γ′-NF 2)

  exγ′₂ : γ′₂ᵁ ≅ˢ γ′₂ᵁ
  exγ′₂ = fold-≅0 {φ = fk β₀} {φ′ = fk β₀} {cv = λ e q → e (suc q)} {cv′ = λ e q → e (suc q)} {P = P̂} {P′ = P̂} rP̂ (Ωˢ-refl β₀)
                  (evη β₀ z<β₀) (suc z<β₀) (evη β₀ z<β₀) (suc z<β₀) (≅ᴵ-refl zero)

  module A₃ = Accept Gγ′₂ Lγ′₂ exγ′₂

  γ′₂-label : Lab (force _ Gγ′₂) (γ′ᴱ 2)
  γ′₂-label = A₃.label

  γ′₂ᴺ-label : Lab (forceᴺ _ Gᴺγ′₂) (γ′ᴱ 2)
  γ′₂ᴺ-label = A₃.labelᴺ
```

## §4 结论与边界

**定理 (编译, 记号无关, §2).** `GᵁBTBO`/`GᴺBTBO` (任意环境); `Gγ′₁`/`Gᴺγ′₁`; 在 `Chain G₁` 内 (实例 `C`): `1⊑β₀`、`2⊑β₀`、`cov₁`、`S⁺₁`、**`GX₂`/`GᴺX₂`**、**`cert-g` (一切 $\eta\sqsubseteq\beta_0$)、`Gγ′₂`/`Gᴺγ′₂`**.

**验收 (编译, §3).** `BTBOᵁ-≅ : force (GᵁBTBO ev z) ≅ BTBOᴵ`; `γ′₁-label`、`γ′₁ᵁ-≅` (与 `pΩ-label` 的树); `X₂-label`、`X₂ᵁ-≅` (与 `pΩ₂-label` 的树); `γ′₂-label`、`γ′₂ᴺ-label`. 标签对记号无关证书的计值成立是因为 `forceᴺ-≅` (任意两个证书计值 $\cong$), 不是因为证书读了标签.

**记号出现的位置.** Base、Depth0、本文 §1–§2 的类型与证明都不引用 `T`/`Lab`/`NF₁` (它们导入的 Uniform2Base/Stage2Label 本身导入记号模块, 但所用的名字 `fold`/`Ω̂A`/`one⁰`/`two⊑`/`h2` 的定义不读记号; NotFree/TreeNFBase 的边界注记同). §3 导入记号模块, 只作验收.

**未做.** $\psi_0(\Omega_\Omega\cdot2)$ (并行工作, 悬置不变量); 深度 $\ge1$ 的观测前序 (Base §1 读法); 一般 `Occ≺ᴳ` 分层覆盖的 `Floor` (TreeNF §4). 只导入已有模块, 不改任何已有文件; README 未改.
