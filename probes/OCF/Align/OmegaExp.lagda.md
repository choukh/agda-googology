# $\psi_0(\Omega_\Omega\cdot\omega^\eta)$ 的无条件遗传标签, 与 $\psi_0(\Omega_\Omega^2)$ 的第一个链点

> 接 [OmegaExpBase](OmegaExpBase.lagda.md) (续延式前缀栈 `Stk`, 指数折叠 `ψᵉ`, 好栈 `Goodˢ`) 与 [OmegaK](OmegaK.lagda.md). 本文是决定性检验.
>
> 结论先说:
>
> 1. **(a) `Tω2-label : Lab Tω2ᴸ tω2` 是无条件定理 (§1)**, $t_{\omega2}=\psi_0(\psi_\Omega(2))=\psi_0(\Omega_\Omega\cdot\omega^2)$. 树 `Tω2ˢ = (∅ˢ ▹ω 2) z1 z1`, 字面是 $\lim_m$ `rep ∅ˢ 1 m z1 z1` (`refl`), 第 $m$ 项是 $m$ 个 $\Omega_\Omega\cdot\omega$ 帧; 证书与标签是 `GoodE Good∅` 的目标 0 字段. **`mixed` $=\psi_0(\Omega_\Omega\cdot\omega+\Omega_\Omega)$ 可达**: 记号 `walk tω2 [2,1] ≡ mixed`, 树 `sqˢ (sqˢ Tω2ˢ 2) 1 ≡ ((∅ˢ ▹ω 1) ▹Ω̂) z1 z1` (都 `refl`), 标签 `GLmixed`. `Tω2ᴸ ≡ lim χω2`, `Tω2-step`, `FGH Tω2ᴸ 0 ≡ 0` 都 `refl`.
> 2. **(b) `Tωω-label : Lab Tωωᴸ tωω` 是无条件定理 (§2)**, $t_{\omega\omega}=\psi_0(\psi_\Omega(\omega))=\psi_0(\Omega_\Omega\cdot\omega^\omega)$, 指数树 `lim natˢ`, 树 `Tωωˢ ≡ lim (λ n → Tηˢ (natˢ n))` (`refl`), `Tωω-step`, `FGH Tωωᴸ 0 ≡ 1` (`refl`).
> 3. **(d) 一般可数指数 (§3).** **`GLη : Lab0ᴸ X η → X ≅ˢ X → NF₁ (ψ₀(ψ_Ω(η))) → Σ (Goodᴸ (toZ (Tηˢ X))) λ G → Lab (forceᴸ _ G) (ψ₀(ψ_Ω(η)))`**, 对第 0 层任意带结构标签的符号树 $X$ (含待计值链), 前提只有标准形. 更一般地, 由 OmegaExpBase 的 `GoodΩ`/`GoodE` 堆出的每个栈 $\Omega_\Omega\cdot\omega^{\eta_1}+\cdots+\Omega_\Omega\cdot\omega^{\eta_r}$ (各 $\eta_i$ 带结构标签) 都给出 $\psi_0$ 的标签. 与 OmegaK 一致: `Tω-agree` ($\psi_0(\Omega_\Omega\cdot\omega)$, 经 `Lab-uniq`), `Tk-agree` (一切 $k$, $\psi_0(\Omega_\Omega\cdot k)$ = `rep ∅ˢ 0 k`, §5).
> 4. **(c) $\psi_0(\Omega_\Omega^2)$: 树已定义, 第一个链点已标, 整体标签未得 (§4).** 树 `TΩ2ˢ = (∅ˢ ▹Ω̂²) z1 z1` 是界为 1 的闭包, 第 0 点 `t₀Ω` $=\psi_0(\Omega_\Omega\cdot\Omega_1)$, 分支 $\psi_0(\Omega_\Omega\cdot\Omega_\eta)$ (`refl`): **不可数指数帧 $\Omega_\Omega\cdot\Omega_\gamma=\Omega_\Omega\cdot\omega^{\Omega_\gamma}$ 是第三种帧 `▹Ω̂²`**, 它弹出为闭包, 闭包的点上指数 $\Omega_\eta$ 在第 $\eta$ 层, 由 `ψᵉ` 作栈顶处理 (共尾度 $\Omega_\eta$ 的 `limᵢ` 子句: 穿透或沿链折叠). **`TΩ2-0-label : Lab TΩ2-0ᴸ (fsn tΩ2 0)` 是无条件定理**: $\psi_0(\Omega_\Omega\cdot\Omega)$ 的链 $\gamma_0=1$, $\gamma_{m+1}=\psi_0(\Omega_\Omega\cdot\omega^{\gamma_m})$ 在第 0 层, 每个链点由 (d) 标. 整体标签所缺: 分支 $\psi_0(\Omega_\Omega\cdot\Omega_{\delta_m})$ ($\delta_m$ 是第 $m$ 个链点, 层号任意大) 要 "以第 $\ge1$ 层的指数为尾巴" 的带前缀引理, 未写; 而且其中第 $\ge1$ 层的后继指数在树里是占位值. 精确停点: 后代 $\psi_0(\psi_\Omega(\Omega_3))$ (路径 $[1,0,1,0,0,3]$, `refl`), 它的 $[1]=\psi_0(\psi_\Omega(\psi_2(\psi_\Omega(\Omega_2))))$ 的链点 $\psi_2(\psi_\Omega(\Omega_2))$ 在第 2 层穿透到一切第 1 层的 $y$, $y=\Omega_1+1$ 时要指数在第 1 层的帧. 第 1 层的帧可写 (`σ1 z`, 临时文件通过), 未接入; 第 $k\ge2$ 层的帧在目标 $<k-1$ 的紧界闭包里放不下: **`noSim2 : Simᴵ 2 (Mlev 1 1 e) → ⊥`** (编译的否定, §4).
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块与 OmegaExpBase, 不改任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OmegaExp where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev; σ1)
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Ordˢ; toZ; Ωˢ; z<suc; z1; intoˢ; sqˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; cω; cΩ; Ωt; γT) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; Lab-≅; l0; l1; fs-rep; fs-ω)
open import OCF.Align.Bachmann using (fs-gt)
open import OCF.Align.Stage2 using (Lab-uniq; Ωᵗ; tO)
open import OCF.Align.StandardOmega using (NF₁; NF₁-fsn; walk; walkD; tO-desc-NF)
open import OCF.Align.Standard using (d₀)
open import OCF.Align.UniformS using (_≅ˢ_; z≅; s≅; l≅; toZ-≅; ≅ˢ-sym; Ωˢ-refl)
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.GoodLBase
open import OCF.Align.OmegaKBase using (tω; tΩ2; tk; tω-NF; tΩ2-NF; tk-NF; ΠΩ-rep)
open import OCF.Align.OmegaK using (Tωᴸ; Tω-label; Tkᴸ; Tk-label)
open import OCF.Align.OmegaExpBase
```

## §1 (a) $t_{\omega2}=\psi_0(\Omega_\Omega\cdot\omega^2)$

**有限指数.** `natˢ n`: 第 0 层的自然数树, 结构标签 `natL n : Lab0ᴸ (natˢ n) (natT n)` (EBO 的 `cof-natT`/`pred-natT`). $t_{\omega2}$ 是 $\psi_0(\Omega_{\Omega+1})$ 的后代, 路径由 `refl` 核对, `NF₁` 由 `tO-desc-NF`.

```agda
natˢ : ℕ → Ordˢ zero
natˢ zero    = Ord₊ˢ.zero
natˢ (suc n) = Ord₊ˢ.suc (natˢ n)

nat-≅ : ∀ n → natˢ n ≅ˢ natˢ n
nat-≅ zero    = z≅
nat-≅ (suc n) = s≅ (nat-≅ n)

natL : ∀ n → Lab0ᴸ (natˢ n) (natT n)
natL zero    = lz refl
natL (suc n) = ls (E.cof-natT n) (subst (Lab0ᴸ (natˢ n)) (sym (E.pred-natT n)) (natL n))

ψΩ₀ : T → T
ψΩ₀ η = ψᵗ [] (ψᵗ Ωᵗ η ∷ []) ∷ []

tω2 : T
tω2 = ψΩ₀ (natT 2)

_ : walk tO (1 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ []) ≡ tω2
_ = refl

tω2-NF : NF₁ tω2
tω2-NF = tO-desc-NF (walkD d₀ (1 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ []) (refl , refl , refl , refl , refl , refl , refl , tt))
```

**树、证书与标签.** `Tηˢ X = (∅ˢ ▹ω X) z1 z1`: 空栈上一个 $\Omega_\Omega\cdot\omega^X$ 帧, 目标 0、环境层号 1 (与 OmegaK 的 `tkˢ` 同). `GLη`: 好栈 `GoodE Good∅ l ex` 的目标 0 字段在 `z1 z1` 处. 第一个 `refl` 是 $\omega$-帧的弹出: $\psi_0(\Omega_\Omega\cdot\omega^2)=\lim_m\psi_0(\Omega_\Omega\cdot\omega\cdot m)$, 第 $m$ 项的栈是 `rep ∅ˢ 1 m`.

```agda
Tηˢ : Ordˢ zero → Ordˢ zero
Tηˢ X = (∅ˢ ▹ω X) z1 z1

GLη : ∀ {X η} → Lab0ᴸ X η → X ≅ˢ X → NF₁ (ψΩ₀ η) → Σ (Goodᴸ (toZ (Tηˢ X))) λ G → Lab (forceᴸ _ G) (ψΩ₀ η)
GLη l ex nf = h0 (GoodE Good∅ l ex) z1 z1 nf

Tω2ˢ : Ordˢ zero
Tω2ˢ = Tηˢ (natˢ 2)

_ : Tω2ˢ ≡ Ord₊ˢ.lim (λ m → rep ∅ˢ (natˢ 1) m z1 z1)
_ = refl

GLω2 : Σ (Goodᴸ (toZ Tω2ˢ)) λ G → Lab (forceᴸ _ G) tω2
GLω2 = GLη (natL 2) (nat-≅ 2) tω2-NF

Tω2ᴸ : Ordᶜ zero
Tω2ᴸ = forceᴸ (toZ Tω2ˢ) (proj₁ GLω2)

Tω2-label : Lab Tω2ᴸ tω2
Tω2-label = proj₂ GLω2
```

**读法.** 证书 `proj₁ GLω2` 的第 $m$ 项是 `repGood Good∅ (natL 1) _ m` 的目标 0 字段, 它再展开为 $\Omega_\Omega\cdot\omega$ 帧的 `GoodE` (指数 1: 后继, 每项是 $n$ 个 $\hat\Omega$ 帧的 `repGood`) 与 `GoodΩ` 的链证书. 没有 oracle、阶段系统或全局界.

外层 FGH 方程 (`refl`, 同 OmegaK 的 `T3-step`), 与 `mixed`: $t_{\omega2}[2][1]=\psi_0(\psi_\Omega(1)+\Omega_\Omega)$, 它的折叠栈是 "一个 $\Omega_\Omega\cdot\omega$ 帧, 其上一个 $\hat\Omega$ 帧" (OmegaK §4 的首个混合栈), 记号与树的位置都 `refl`, 标签由 `GoodΩ (GoodE …)`.

```agda
χω2 : ℕ → Ordᶜ zero
χω2 n = sq′ Tω2ᴸ n
  where
  sq′ : Ordᶜ zero → ℕ → Ordᶜ zero
  sq′ (Ord₊.lim f) n = f n
  sq′ x n = x

_ : Tω2ᴸ ≡ Ord₊.lim χω2
_ = refl

Tω2-step : ∀ n → FGH Tω2ᴸ n ≡ FGH (χω2 n) n
Tω2-step n = refl

mixed : T
mixed = ψᵗ [] (ψᵗ Ωᵗ (natT 1) ∷ ΩΩ ∷ []) ∷ []

_ : walk tω2 (2 ∷ 1 ∷ []) ≡ mixed
_ = refl

_ : sqˢ (sqˢ Tω2ˢ 2) 1 ≡ ((∅ˢ ▹ω natˢ 1) ▹Ω̂) z1 z1
_ = refl

mixed-NF : NF₁ mixed
mixed-NF = tO-desc-NF (walkD d₀ (1 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ 2 ∷ 1 ∷ [])
                             (refl , refl , refl , refl , refl , refl , refl , refl , refl , tt))

GLmixed : Σ (Goodᴸ (toZ (((∅ˢ ▹ω natˢ 1) ▹Ω̂) z1 z1))) λ G → Lab (forceᴸ _ G) mixed
GLmixed = h0 (GoodΩ (GoodE Good∅ (natL 1) (nat-≅ 1))) z1 z1 mixed-NF
```

**读法.** `mixed` 的标签同时是 `Tω2-label` 的遗传部分 (`Lab` 沿 $[2][1]$ 下降); `GLmixed` 把它单独写出, 说明混合栈本身是好栈, 不依赖它在 $t_{\omega2}$ 里的位置.

## §2 (b) $t_{\omega\omega}=\psi_0(\Omega_\Omega\cdot\omega^\omega)$

指数 $\omega=\psi_0(1)$, 树 `lim natˢ`, 结构标签 `ωL` (`ll`; $\psi_0(1)[n]=\psi_0(0)\cdot n=n$, `fs-rep` 与 `natT-rep`). 树的外层是指数的极限: $\psi_0(\Omega_\Omega\cdot\omega^\omega)=\lim_n\psi_0(\Omega_\Omega\cdot\omega^n)$ (`refl`).

```agda
ω₀ : T
ω₀ = ψᵗ [] (natT 1) ∷ []

natT-rep : ∀ n → replicate n (ψᵗ [] []) ≡ natT n
natT-rep zero    = refl
natT-rep (suc n) = cong (ψᵗ [] [] ∷_) (natT-rep n)

ωL : Lab0ᴸ (Ord₊ˢ.lim natˢ) ω₀
ωL = ll refl (λ n → subst (Lab0ᴸ (natˢ n)) (sym (trans (fs-rep [] (ψᵗ [] []) [] refl n) (natT-rep n))) (natL n))

tωω : T
tωω = ψΩ₀ ω₀

_ : walk tO (1 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ []) ≡ tωω
_ = refl

tωω-NF : NF₁ tωω
tωω-NF = tO-desc-NF (walkD d₀ (1 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ []) (refl , refl , refl , refl , refl , refl , tt))

Tωωˢ : Ordˢ zero
Tωωˢ = Tηˢ (Ord₊ˢ.lim natˢ)

_ : Tωωˢ ≡ Ord₊ˢ.lim (λ n → Tηˢ (natˢ n))
_ = refl

GLωω : Σ (Goodᴸ (toZ Tωωˢ)) λ G → Lab (forceᴸ _ G) tωω
GLωω = GLη ωL (l≅ nat-≅) tωω-NF

Tωωᴸ : Ordᶜ zero
Tωωᴸ = forceᴸ (toZ Tωωˢ) (proj₁ GLωω)

Tωω-label : Lab Tωωᴸ tωω
Tωω-label = proj₂ GLωω

Tωω-step : ∀ n → FGH Tωωᴸ n ≡ FGH (forceᴸ (toZ (Tηˢ (natˢ n))) _) n
Tωω-step n = refl
```

**读法.** 第 $n$ 项是 `Tηˢ (natˢ n)`, 其证书是 `GoodE` 在 `natL n` 上, 它又是 $n$ 层嵌套的 `repGood`: 弹出 $\omega^{k+1}$ 得 $m$ 个 $\omega^k$, 对 $k$ 下降, 每层对重数 $m$ 归纳.

## §3 (d) 一般可数指数, 与 OmegaK 一致

`Tη-label`: 对第 0 层任意带结构标签 $\eta$ 的符号树 $X$ (零、后继、极限、两种待计值链; 自互模拟; $\psi_0(\psi_\Omega(\eta))$ 标准形). `Tω-agree`: 新折叠的 $\psi_0(\Omega_\Omega\cdot\omega^1)$ 与 OmegaK 的 `Tωᴸ` (Prefix 的 `lim tkˢ`) $\cong$, 因为两者带同一个遗传标签 (`Lab-uniq`).

```agda
Tη-label : ∀ {X η} (l : Lab0ᴸ X η) (ex : X ≅ˢ X) (nf : NF₁ (ψΩ₀ η)) → Lab (forceᴸ (toZ (Tηˢ X)) (proj₁ (GLη l ex nf))) (ψΩ₀ η)
Tη-label l ex nf = proj₂ (GLη l ex nf)

GLω′ : Σ (Goodᴸ (toZ (Tηˢ (natˢ 1)))) λ G → Lab (forceᴸ _ G) tω
GLω′ = GLη (natL 1) (nat-≅ 1) tω-NF

Tω-agree : forceᴸ _ (proj₁ GLω′) ≅ Tωᴸ
Tω-agree = Lab-uniq (proj₂ GLω′) Tω-label
```

**读法.** (d) 的前提 `NF₁ (ψΩ₀ η)` 不能去掉: `GoodE` 的单调性来自 `mono-lab`, 即 `fs-mono₁` 于 $\psi_0(\psi_\Omega(\eta))$, 它要标准形. 对 $\psi_0(\Omega_{\Omega+1})$ 的后代 (`tO-desc-NF`) 它总成立.

## §4 (c) $\psi_0(\Omega_\Omega^2)$

**树.** `TΩ2ˢ = (∅ˢ ▹Ω̂²) z1 z1`: 记号侧 $\psi_0(\Omega_\Omega^2)[m]=\psi_0(\psi_\Omega(\Omega_{\gamma_m}))$ (OmegaKBase §1), 链点前缀是单个不可数指数帧 $\Omega_\Omega\cdot\Omega_\gamma$. 第一个 `refl`: 树是界为 1 的闭包, 第 0 点 `t₀Ω` $=\psi_0(\Omega_\Omega\cdot\Omega_1)$ (指数 $\Omega_1$ 在第 1 层, 经 `σ1`), 分支 $\psi_0(\Omega_\Omega\cdot\Omega_\eta)$ (指数经 `lim 1` 进入 `Mlev 1 η e`). 第二个 `refl`: `t₀Ω` 是 `ψᵉ` 的 `limᵢ` 子句在目标 0 的折叠, 链 `chainE` 在第 0 层, $\chi_0=\Omega_0=1$, $\chi_{m+1}=\psi_0(\Omega_\Omega\cdot\omega^{\chi_m})$, 输出就是下一个链点. 这正是 $\psi_\Omega$ 作用于 $\Omega$-共尾参数 $\Omega_1$ 时的规则 6: 目标 0 不大于共尾度的下标, 折叠.

```agda
TΩ2ˢ : Ordˢ zero
TΩ2ˢ = (∅ˢ ▹Ω̂²) z1 z1

σΩ : Simᴵ zero (suc zero)
σΩ q = σ1 z1 (suc q)

chainE : ℕ → Ordˢ zero
chainE = iter (λ x → ψᵉ ∅ˢ z1 z1 σΩ x) (Ωˢ zero)

t₀Ω : Ordˢ zero
t₀Ω = ψᵉ ∅ˢ z1 z1 (σ1 z1) (Ωˢ (suc zero))

_ : TΩ2ˢ ≡ Ord₊ˢ.ŝ (suc zero) t₀Ω (λ η e → ψᵉ ∅ˢ {ℓ = Mlev (suc zero) η e} (lim 0 z1) (lim 0 zero) (λ q → lim 1 q) (Ωˢ η))
_ = refl

_ : t₀Ω ≡ Ord₊ˢ.lim (λ m → chainE (suc m))
_ = refl

tΩ1 : T
tΩ1 = ψΩ₀ (Ωt (natT 1))

_ : fsn tΩ2 0 ≡ tΩ1
_ = refl

tΩ1-NF : NF₁ tΩ1
tΩ1-NF = NF₁-fsn tΩ2-NF refl 0

bΩ : T
bΩ = ψᵗ Ωᵗ (Ωt (natT 1)) ∷ []

γΩ : ℕ → T
γΩ = γT bΩ []

_ : ∀ m → γΩ (suc m) ≡ ψΩ₀ (γΩ m)
_ = λ m → refl

fsΩ : ∀ m → fsn tΩ1 m ≡ γΩ (suc m)
fsΩ m = fs-gt [] (ψᵗ Ωᵗ (Ωt (natT 1))) [] [] refl refl m

atomE : ∀ m → Atomᴸ (chainE m) (γΩ m)
atomE zero    = Ωˢ-refl zero , gs gz , l1 refl (s≅ z≅) (l0 refl z≅)
atomE (suc m) = Atomᴸ-≅ (ψᵉ0-≅ ∅-≈ z≅ ex , h0 (GoodE Good∅ (atomL (atomE m)) ex) z1 z1 nf) (ψᵉ0-≅ ∅-≈ z≅ ex)
  where
  ex = proj₁ (atomE m)
  nf : NF₁ (ψΩ₀ (γΩ m))
  nf = subst NF₁ (fsΩ m) (NF₁-fsn tΩ1-NF refl m)

GLΩ0 : Σ (Goodᴸ (toZ t₀Ω)) λ G → Lab (forceᴸ _ G) tΩ1
GLΩ0 = limᴸ tΩ1-NF refl (λ m → proj₁ (proj₂ (atomE (suc m))))
            (λ m → subst (Lab _) (sym (fsΩ m)) (proj₂ (proj₂ (atomE (suc m)))))

TΩ2-0ᴸ : Ordᶜ zero
TΩ2-0ᴸ = forceᴸ (toZ t₀Ω) (proj₁ GLΩ0)

TΩ2-0-label : Lab TΩ2-0ᴸ (fsn tΩ2 0)
TΩ2-0-label = proj₂ GLΩ0
```

**读法.** 链原子 `atomE (m+1)` 由 (d) 给出: 链点 $\chi_{m+1}$ 与 `(∅ˢ ▹ω χ_m) z1 z1` 只差指数折叠的 `Sim` (`σΩ` 与 `σ⊥`; 第 0 层的指数不读 `Sim`), 经 `ψᵉ0-≅` 互模拟, `Atomᴸ-≅` 搬运证书与标签. 标签序列就是 EBO 的 $\gamma$-链 `γT bΩ []` (`γΩ (suc m) ≡ ψΩ₀ (γΩ m)` 是 `refl`). 所以 $\psi_0(\Omega_\Omega\cdot\Omega)$ 是 "以可数指数帧的标签为链点" 的一条第 0 层的链: 不需要任何第 $\ge1$ 层的指数理论.

**停点.** 整体标签要 `TΩ2ˢ` 的链证书: 在每个带标签 $\delta_m=t_{\Omega2}[m]$ 的点 $Y$ 处, 分支 $\psi_0(\Omega_\Omega\cdot\Omega_{\mathtt{lvl}\,Y})$ 的证书与标签. 指数 $\Omega_{\mathtt{lvl}\,Y}$ 的结构标签 (`LabL-Ω`) 在第 $\ge1$ 层有 `gi` 行, 节点层非零时折叠, 链点 $\psi_j(\Omega_\Omega\cdot\omega^{\chi})$ 在第 $j$ 层, 要 "以第 $j$ 层的指数为尾巴" 的目标 $w\ne0$ 引理 (OmegaExpBase `PreS₊` 的指数版), 它的 `gi` 穿透行对一切带标签的低层 $y$ 量化, 其中有第 $\ge1$ 层的后继. 这个引理没有写; 它要的第 $\ge1$ 层后继在 `ψᵉ` 里是占位值. 下面的 `refl` 给出第一个需要它的后代: $\psi_0(\psi_\Omega(\Omega_3))$ (路径 $[1,0,1,0,0,3]$; 临时脚本 `search.py` 以分支 $0..3$ 做广度搜索得到的最短路径), 它的 $[1]$ 的链点 $\psi_2(\psi_\Omega(\Omega_2))$ 在第 2 层对第 1 层的一切 $y$ 穿透, $y=\Omega_1+1$ 时是第 1 层的后继指数. ($\psi_0(\psi_\Omega(\Omega_n))$, $n\le2$ 的穿透只在第 1 层, 只碰到第 0 层的 $y$; 它们的标签只差 "第 $\ge1$ 层指数的带前缀引理" 这一件, 没有占位值问题.)

**编译的否定, 与帧层号的三种情形.** 指数在第 $k$ 层的帧要在以后每个环境层号上有 `Simᴵ k ℓ′`.

1. $k=1$: 帧证据给出 `σ1 z`, 可写 (OmegaExpBase §2 的临时文件 `NegLv1.agda` 通过). $\psi_0(\psi_\Omega(\Omega_3))$ 需要的正是这一种.
2. $k\ge2$, 帧在目标 $i\ge k-1$ 处产生 (穿透产生的帧都如此: 穿透到第 $k$ 层的 $y$ 要目标 $>k$): 折叠的目标只升不降 (链点的目标 $\sigma q\succeq i$, 弹 $\hat\Omega$ 不换目标), 以后的紧界 $i'+1\sqsupseteq k$, 帧放得下; 但多态的 `Stk` 只带 $0<^\mathsf I\ell$, 要改成带地板 $k\sqsubseteq^\mathsf I i$ 的栈 (`NegLv2.agda` 的 `UnequalTerms` 就是缺这一项). 未做.
3. $k\ge2$, 帧在目标 $i<k-1$ 处产生 (第 $k$ 层的和 $a+1$ 在低目标处被折叠访问, 例如指数 $a+\Omega_3$ 在目标 0 的链从 $\Omega_0=1$ 起): 紧界不可能. 闭包的分支 $g\,\eta\,e$ 必须对一切 $\eta\sqsupseteq1$ 有定义, 在 $\eta=1$ 处公共层号 `Mlev 1 1 e` $=\lim[1,1,1,\ldots]$ 不含第 2 层: `noSim2` (从 `Simᴵ 2 (Mlev 1 1 e)` 取 $1<^\mathsf I$ `Mlev 1 1 e`, 即某个 $1<^\mathsf I1$, 矛盾). 要以帧的层号为地板的非紧界 (GoodLBase `gŝ` 行的地板已允许界 $c\sqsubseteq\mathtt{lvl}\,w+1$) 与 "地板出现在链点标签里" 的支配论证. $\psi_0(\Omega_\Omega^2)$ 的带标签点里是否出现这一情形未定: 临时脚本 `search2.py` 对 $t_{\Omega2}$ 的 $\omega$-后代 (分支 $0..3$, 深 11, 约 $1.2\times10^6$ 项) 搜索形如 $\psi_0(\psi_\Omega(\zeta)+\cdots+\Omega_\Omega)$、$\zeta$ 含自然数下标 $\ge2$ 的项, 没有找到; 但 `LabL` 的 `gi` 行对一切带标签的点量化, 不只 $\omega$-后代.

```agda
_ : walk tΩ2 (1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 3 ∷ []) ≡ ψΩ₀ (Ωt (natT 3))
_ = refl

_ : fsn (ψΩ₀ (Ωt (natT 3))) 1 ≡ ψΩ₀ (ψᵗ (natT 2) (ψᵗ Ωᵗ (Ωt (natT 2)) ∷ []) ∷ [])
_ = refl

noSim2 : (e : suc zero ⊑ᴵ suc zero) → Simᴵ (suc (suc zero)) (Mlev (suc zero) (suc zero) e) → ⊥
noSim2 e σ with σ {suc zero} zero
... | lim zero    (suc ())
... | lim (suc n) (suc ())
```

## §5 与 OmegaK 的 $t_k$ 一致, 数值

`rep ∅ˢ 0 k`: $k$ 个指数为 0 的帧, 即 $k$ 个 $\hat\Omega$ 帧; 标签 $\psi_0(\Omega_\Omega\cdot k)$ 由 `repGood Good∅ (lz refl)`. 与 OmegaK 的 `Tkᴸ k` (Prefix 的 $k$ 帧 `ψᴾ`) 对一切 $k$ $\cong$.

```agda
Tk′ˢ : ℕ → Ordˢ zero
Tk′ˢ k = rep ∅ˢ Ord₊ˢ.zero k z1 z1

GLk′ : ∀ k → Σ (Goodᴸ (toZ (Tk′ˢ k))) λ G → Lab (forceᴸ _ G) (ψᵗ [] (replicate k ΩΩ) ∷ [])
GLk′ k = h0 (repGood Good∅ (lz refl) z≅ k) z1 z1 (subst (λ t → NF₁ (ψᵗ [] t ∷ [])) (ΠΩ-rep k) (tk-NF k))

Tk-agree : ∀ k → forceᴸ _ (proj₁ (GLk′ k)) ≅ Tkᴸ k
Tk-agree k = Lab-uniq (proj₂ (GLk′ k)) (subst (Lab (Tkᴸ k)) (cong (λ t → ψᵗ [] t ∷ []) (ΠΩ-rep k)) (Tk-label k))
```

数值 (`refl`, 几秒): $t_{\omega2}[0]=\psi_0(0)=1$, 所以 $f_{t_{\omega2}}(0)=f_1(0)=0$; $t_{\omega\omega}[0]=\psi_0(\Omega_\Omega)$, $f(0)=1$.

```agda
_ : FGH Tω2ᴸ 0 ≡ 0
_ = refl

_ : FGH Tωωᴸ 0 ≡ 1
_ = refl
```

## §6 对比表

| | OmegaK | 本文 |
|---|---|---|
| 折叠 | Prefix `ψᴾ`, 栈 `Vec` | OmegaExpBase `ψˢ`/`ψᵉ`, 栈 `Stk` (续延) |
| 停机 | (帧数, 尾巴) | (指数, 重数); 栈无下标 |
| $\psi_0(\Omega_\Omega\cdot k)$ | `Tk-label` | `GLk′` (`repGood`), `Tk-agree` |
| $\psi_0(\Omega_\Omega\cdot\omega)$ | `Tω-label` (`lim tkˢ`) | `GLω′`, `Tω-agree` |
| $\psi_0(\Omega_\Omega\cdot\omega^2)$ | `ψ²` 停机, 无标签 | **`Tω2-label`**, `Tω2-step`, `mixed` (`GLmixed`) |
| $\psi_0(\Omega_\Omega\cdot\omega^\omega)$ | — | **`Tωω-label`**, `Tωω-step` |
| $\psi_0(\Omega_\Omega\cdot\omega^\eta)$, $\eta$ 可数带结构标签 | — | **`GLη`/`Tη-label`** |
| $\psi_0(\Omega_\Omega^2)$ | 树未定义 | 树 `TΩ2ˢ` (`▹Ω̂²`); **`TΩ2-0-label`** ($[0]$); 整体未得 |
| 否定 | `Vec` 长度下标 `TerminationIssue` | `NegLv2` (`UnequalTerms`), **`noSim2`** |

## §7 结论与边界

**字面成立 (`refl`):** `walk tO [1,0,1,1,0,0,2] ≡ tω2`, `walk tO [1,0,1,1,0,0] ≡ tωω`, `walk tω2 [2,1] ≡ mixed`, `walk tΩ2 [1,0,1,0,0,3] ≡ ψ₀(ψ_Ω(Ω_3))`, `fsn ψ₀(ψ_Ω(Ω_3)) 1 ≡ ψ₀(ψ_Ω(ψ_2(ψ_Ω(Ω_2))))`, `fsn tΩ2 0 ≡ tΩ1`; `Tω2ˢ ≡ lim (rep ∅ˢ 1 · z1 z1)`, `sqˢ (sqˢ Tω2ˢ 2) 1 ≡ ((∅ˢ ▹ω 1) ▹Ω̂) z1 z1`, `Tωωˢ ≡ lim (Tηˢ ∘ natˢ)`, `TΩ2ˢ ≡ ŝ 1 t₀Ω …`, `t₀Ω ≡ lim (chainE ∘ suc)`, `γΩ (suc m) ≡ ψΩ₀ (γΩ m)`; `Tω2ᴸ ≡ lim χω2`, `Tω2-step`, `Tωω-step`; `FGH Tω2ᴸ 0 ≡ 0`, `FGH Tωωᴸ 0 ≡ 1`.

**定理 (标签按 Correspond 的 `Lab`, 树只到 $\cong$):**

1. (a) **`Tω2-label : Lab Tω2ᴸ tω2`**, `GLω2`; `GLmixed` (`mixed` 的证书与标签).
2. (b) **`Tωω-label : Lab Tωωᴸ tωω`**, `GLωω`.
3. (d) **`GLη`/`Tη-label`**: 一切第 0 层带结构标签的指数. 与 OmegaK 一致: `Tω-agree`, `Tk-agree` (一切 $k$).
4. (c) **`TΩ2-0-label : Lab TΩ2-0ᴸ (fsn tΩ2 0)`**, `GLΩ0`, `atomE`, `fsΩ`; 编译的否定 **`noSim2`**.

**标签状态.** 按 README 的认证准则: $\psi_0(\Omega_\Omega\cdot\omega^2)$、$\psi_0(\Omega_\Omega\cdot\omega^\omega)$、一般的 $\psi_0(\Omega_\Omega\cdot\omega^\eta)$ ($\eta$ 为第 0 层带结构标签的树, 且 $\psi_0(\psi_\Omega(\eta))$ 标准形) 与 $\psi_0(\Omega_\Omega\cdot\Omega)=\psi_0(\Omega_\Omega^2)[0]$ 的遗传标签是**无条件定理**. $\psi_0(\Omega_\Omega^2)$ 本身: 树已定义, 标签未得 (缺第 $\ge1$ 层指数的带前缀引理, 及第 $\ge1$ 层后继指数的帧; 第 2 层起后者在紧界下不可能, `noSim2`).

**边界.**

- 树只到 $\cong$; 对抽象的指数, 外层形状只经 `GoodE` 的命题; 对具体的 2、$\omega$ 都化简 (`refl`).
- `TΩ2ˢ` 的第 $\ge1$ 层后继指数处是占位值 $\Omega_i$ (OmegaExpBase §2); 本文的定理不经过它.
- 数值只到 `FGH … 0`.
- 不改 `src/`、`archive/` 与已有的 Align 文件, README 未改.
