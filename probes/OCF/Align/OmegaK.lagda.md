# $\psi_0(\Omega_\Omega\cdot k)$ 与 $\psi_0(\Omega_\Omega\cdot\omega)$ 的无条件遗传标签

> 接 [OmegaKBase](OmegaKBase.lagda.md) (多帧的带前缀引理) 与 [GoodL](GoodL.lagda.md) (单帧, $\psi_0(\Omega_\Omega\cdot2)$). 本文是决定性检验.
>
> 结论先说:
>
> 1. **(a) `Tk-label : ∀ k → Lab (Tkᴸ k) (tk k)` 是无条件定理 (§1)**, `Tkᴸ k = forceᴸ (toZ (tkˢ k)) (Gk k)`, `tkˢ k = ψᴾ k z1 id (replicate k (fΩ̂ z1)) zero` (Prefix 的 $k$ 帧折叠, `tkˢ 2 ≡ t2ˢ` 字面), 证书 `Gk k : Goodᴸ (toZ (tkˢ k))` 是对 $k$ 的闭项 (`OmegaKBase.Pre0K₊` 在尾巴 $0$ 处). $k=3$ 显式: `G3`, `T3ᴸ`, `T3-label`, `T3ᴸ ≡ lim χ3` 与 `T3-step : FGH T3ᴸ n ≡ FGH (χ3 n) n` 为 `refl`, `FGH T3ᴸ 0 ≡ 1` 为 `refl`. 一般 $k\ge1$ 的外层形状经 `pop-eq` (`Tk-lim`, `Tk-step`). $k=2$ 与 GoodL 的树 $\cong$ (`T2-agree`).
> 2. **与 Prefix 的折叠一致 (§2).** `cross : x ≅ᶻ y → (G : Goodᶻ x) (G′ : Goodᴸ y) → force x G ≅ forceᴸ y G′` (Prefix 的旧证书与 `Goodᴸ` 计值出 $\cong$ 的树, 链点逐个 $\cong$). 推论 **`agree-forceK : ∀ k (G : Goodᶻ (toZ (tkˢ k))) → force _ G ≅ Tkᴸ k`** 与 `forced-labelK`: Prefix 的 `ψᴾ k …` 在**任意** `Goodᶻ` 证书下强制出的树都带标签 $\psi_0(\Omega_\Omega\cdot k)$ (这类证书是否存在仍未知; GoodL 的 `agree-force` 是 $k=2$ 且走标签).
> 3. **(b) `Tω-label : Lab Tωᴸ tω` 是无条件定理 (§3)**, `Tωˢ = lim tkˢ`, 证书 `Gω` 由 GoodLBase 的 `limᴸ` (单调来自 `mono-lab`, 即 `fs-mono₁` 于 $\psi_0(\Omega_\Omega\cdot\omega)$); `Tωᴸ ≡ lim Tkᴸ` 与 `Tω-step` 为 `refl`. 它同时是 $\psi_0(\Omega_\Omega^2)[0][0]$ 的标签.
> 4. **(c) $\psi_0(\Omega_\Omega^2)$ 未得 (§4), 精确停点与所缺.** 记号侧 (OmegaKBase §1): $\psi_0(\Omega_\Omega^2)[m]=\psi_0(\psi_\Omega(\Omega_{\gamma_m}))$, 链点前缀是单个主项 $\Omega_\Omega\cdot\Omega_{\gamma_m}$, 不是 $\gamma_m$ 个 $\hat\Omega$ 帧; 帧数只在 $\psi_\Omega(1)[n]=\Omega_\Omega\cdot n$ 处出现, 而那里的 $n$ 是**外层**基本列的下标 ((b) 的 `lim`). 一般地需要 "$\Omega_\Omega\cdot\omega^\eta$ 帧" ($\eta$ 是可数的树, 本身可带 $\hat\Omega$ 帧, 例如 $[0][1]=\psi_0(\psi_\Omega(t_\omega))$). 第一个同时含 $\hat\Omega$ 帧与 $\omega$-帧的后代是 `mixed` $=\psi_0(\psi_\Omega(1)+\Omega_\Omega)$, 路径 $[0,1,1,0,0,2,2,1]$ (`refl`). **编译的否定**: 给 Prefix 的折叠加一种帧 `fω` (弹出为 $\lim_m$ 个 $m$ 个 $\hat\Omega$), 以 `Vec` 长度为下标, 停机检查失败 (报错原文见 §4); 对照组 (同一文件, `fω` 弹出不增帧) 通过. **编译的肯定**: 两个计数器 $(c_1,c_0)$ 表示栈 $\Omega_\Omega\cdot\omega\cdot c_1+\Omega_\Omega\cdot c_0$, 字典序停机通过 (`ψ²`), 覆盖到 $\psi_0(\Omega_\Omega\cdot\omega^2)$ 之下; 指数为可数树时计数器序列本身要以序数为下标, 结构递归的字典序不够.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块与 OmegaKBase, 不改任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OmegaK where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_) renaming (replicate to replicateV)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Ctx; Pt; lvP; Γᶜ; Mlev; σ1)
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Ordˢ; toZ; ψᴾ; fΩ̂; Goodᶻ; force; force-HS; outs; t2ˢ; z1;
  intoˢ; outˢ; Ωˢ; _+ˢ_; z<suc; tr⁻ˢ)
import OCF.Align.EBO as E
open E using (T; fsn; natT; Ωt) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; Lab-≅; l0; l1)
open import OCF.Align.Stage2 using (t2; Lab-uniq; Ωᵗ)
open import OCF.Align.StandardOmega using (walk)
open import OCF.Align.UniformS using (_≅ᶻ_; zᶻ; sᶻ; lᶻ; ĉᶻ; _≅ˢ_; toZ-≅; z≅)
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.GoodLBase
open import OCF.Align.GoodL using (T2ᴸ; T2-label)
open import OCF.Align.OmegaKBase
```

## §1 (a) $t_k=\psi_0(\Omega_\Omega\cdot k)$

`tkˢ k`: Prefix 的 $\psi^P$ 以 $k$ 个 $\hat\Omega$ 帧、尾巴 $0$、目标 $0$ (环境层号 $1$, 帧证据 `z1`). `GLk`: $k=0$ 是 $\Omega_0=1$; $k=n+1$ 是 OmegaKBase 的 `Pre0K₊ n` 在尾巴 `zero` (第 1 层, 标签 `gz refl`) 处, 输入 `ctxK-NF n`. 没有 oracle、阶段系统或全局界.

```agda
tkˢ : ℕ → Ordˢ zero
tkˢ k = ψᴾ k z1 (λ q → q) (replicateV k (fΩ̂ z1)) Ord₊ˢ.zero

_ : tkˢ 2 ≡ t2ˢ
_ = refl

GLk : ∀ k → Σ (Goodᴸ (toZ (tkˢ k))) λ G → Lab (forceᴸ _ G) (tk k)
GLk zero    = gs gz , l1 refl (s≅ z≅) (l0 refl z≅)
GLk (suc n) = Pre0K₊ n {p = z1} {σ = λ q → q} {P = replicateV (suc n) (fΩ̂ z1)} (AΩ-rep (suc n)) (gz refl) z≅ (ctxK-NF n)

Gk : ∀ k → Goodᴸ (toZ (tkˢ k))
Gk k = proj₁ (GLk k)

Tkᴸ : ℕ → Ordᶜ zero
Tkᴸ k = forceᴸ (toZ (tkˢ k)) (Gk k)

Tk-label : ∀ k → Lab (Tkᴸ k) (tk k)
Tk-label k = proj₂ (GLk k)

Tk-HS : ∀ k → HS (Tkᴸ k)
Tk-HS k = forceᴸ-HS _ (Gk k)
```

**读法.** 证书 `Gk (n+2)` 的第 $j$ 个链点 $\delta_j=\psi_0(\Omega_\Omega\cdot(n+1)+\Omega_{\delta_{j-1}})$ 的证书由 `Pre0VK n` 在前一个链点的层号处造出, 它内部又在每个弹栈处递归到更少的帧, 直到单帧的 `pop0ᴸ`; 一切闭包 (`gŝ` 行) 的支配仍是 GoodLBase 的 `domᴸ` (闭包的地板 $w$ + `occ<` + `Lab-oc`).

$k=3$ 显式:

```agda
G3 : Goodᴸ (toZ (tkˢ 3))
G3 = Gk 3

T3ᴸ : Ordᶜ zero
T3ᴸ = forceᴸ (toZ (tkˢ 3)) G3

T3-label : Lab T3ᴸ (ψᵗ [] (ΩΩ ∷ ΩΩ ∷ ΩΩ ∷ []) ∷ [])
T3-label = Tk-label 3
```

FGH 的外层方程: 对具体的 $k$ (此处 $3$), `forceᴸ` 在 `gc` 处字面是 `lim (outsᴸ …)`, `pop-eq` 化为 `refl`, 所以是 `refl`.

```agda
χ3 : ℕ → Ordᶜ zero
χ3 n = sq′ T3ᴸ n
  where
  sq′ : Ordᶜ zero → ℕ → Ordᶜ zero
  sq′ (Ord₊.lim f) n = f n
  sq′ x n = x

_ : T3ᴸ ≡ Ord₊.lim χ3
_ = refl

T3-step : ∀ n → FGH T3ᴸ n ≡ FGH (χ3 n) n
T3-step n = refl
```

**$k=2$ 与 GoodL 一致.** 遗传标签决定树 (模 $\cong$, `Lab-uniq`).

```agda
T2-agree : Tkᴸ 2 ≅ T2ᴸ
T2-agree = Lab-uniq (Tk-label 2) T2-label
```

## §2 与 Prefix 的任意 `Goodᶻ` 证书一致

`cross`: 对两种证书同时归纳. `gc` 情形: Prefix 的链点 `Γᶜ C k` 与 `Goodᴸ` 的链点 `P k` 逐个 $\cong$ (`ep`, 第 0 点由 $t_0$ 的递归, 第 $k+1$ 点由分支 $g$ 在 $\cong^\mathsf I$ 的层号处的递归, 用 `≅ᶻ` 的 `dg`), 输出随之逐个 $\cong$ (`oc`). `Goodᶻ` 在一切 $\eta$ 处有分支, `Goodᴸ` 只在带标签的点, 但计值只用链点, 所以对上. 这不需要标签.

```agda
cross : ∀ {x y} → x ≅ᶻ y → (G : Goodᶻ x) (G′ : Goodᴸ y) → force x G ≅ forceᴸ y G′
cross zᶻ Goodᶻ.gz gz = z≅
cross (sᶻ d) (Goodᶻ.gs G) (gs G′) = s≅ (cross d G G′)
cross (lᶻ h) (Goodᶻ.gl G _) (gl G′ _) = l≅ (λ n → cross (h n) (G n) (G′ n))
cross {x = ĉᴸ c t₀ g o₀ o} (ĉᶻ ec dt dg dp dO) (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo)
      (gc γ G₀′ l₀′ d₀′ Gg′ lE′ dE′ Go₀′ Go′ mo₀′ mo′) = l≅ oc
  where
  C : Ctx
  C = record { c = c ; t₀ = force t₀ G₀ ; E = λ η e → force (g η e) (Gg η e)
             ; h₀ = force-HS t₀ G₀ ; hE = λ η e → force-HS (g η e) (Gg η e)
             ; d₀ = d₀ ; dE = dE ; m₀ = m₀ ; mE = mE }
  P = ptsᴸ (forceᴸ _ G₀′) (forceᴸ-HS _ G₀′) l₀′ d₀′ (λ m Y hY lY e → forceᴸ _ (Gg′ m Y hY lY e))
           (λ m Y hY lY e → forceᴸ-HS _ (Gg′ m Y hY lY e)) lE′ dE′
  ep : ∀ k → Pt.x (Γᶜ C k) ≅ Ptᴸ.x (P k)
  ep zero    = cross dt G₀ G₀′
  ep (suc k) = cross (dg _ (Pt.dx (Γᶜ C k)) _ (Ptᴸ.dx (P k)) (toLevel-≅ _ _ (ep k)))
                     (Gg _ (Pt.dx (Γᶜ C k))) (Gg′ k (Ptᴸ.x (P k)) (Ptᴸ.hx (P k)) (Ptᴸ.lx (P k)) (Ptᴸ.dx (P k)))
  oc : ∀ n → outs C (force o₀ Go₀) (λ η e → force (o η e) (Go η e)) n ≅ outsᴸ (forceᴸ _ Go₀′) (λ k → forceᴸ _ (Go′ k)) n
  oc zero    = cross dp Go₀ Go₀′
  oc (suc k) = cross (dO _ (Pt.dx (Γᶜ C k)) _ (Ptᴸ.dx (P k)) (toLevel-≅ _ _ (ep k))) (Go _ (Pt.dx (Γᶜ C k))) (Go′ k)
```

**推论.** `tkˢ k` 自相似 (`ψK-≅`), 所以 Prefix 的 `ψᴾ k …` 在**任意** `Goodᶻ` 证书下的计值 $\cong$ `Tkᴸ k`, 从而带标签 $\psi_0(\Omega_\Omega\cdot k)$; 任意 `Goodᴸ` 证书亦然 (`agree-selfK`).

```agda
tk-refl : ∀ k → tkˢ k ≅ˢ tkˢ k
tk-refl k = ψK-≅ k (AΩ-rep k) (AΩ-rep k) (≅ᴵ-refl zero) z≅

agree-forceK : ∀ k (G : Goodᶻ (toZ (tkˢ k))) → force (toZ (tkˢ k)) G ≅ Tkᴸ k
agree-forceK k G = cross (toZ-≅ (tk-refl k)) G (Gk k)

forced-labelK : ∀ k (G : Goodᶻ (toZ (tkˢ k))) → Lab (force (toZ (tkˢ k)) G) (tk k)
forced-labelK k G = Lab-≅ (agree-forceK k G) (Tk-label k)

agree-selfK : ∀ k (G : Goodᴸ (toZ (tkˢ k))) → forceᴸ (toZ (tkˢ k)) G ≅ Tkᴸ k
agree-selfK k G = forceᴸ-≅ (toZ-≅ (tk-refl k)) G (Gk k)
```

## §3 (b) $\psi_0(\Omega_\Omega\cdot\omega)$

$\psi_0(\Omega_\Omega\cdot\omega)=\psi_0(\psi_\Omega(1))$ 的共尾度 $\omega$, 第 $k$ 项 $\psi_0(\Omega_\Omega\cdot k)$ (`fs-tω`; 规则 5ω 再规则 4). 树是 $t_k$ 的 $\omega$-极限, 证书与标签由 GoodLBase 的 `limᴸ` 从 (a) 的 `GLk` 得出; 相邻项的单调是 `mono-lab` (标签 + `fs-mono₁`), 不需要树侧论证.

```agda
Tωˢ : Ordˢ zero
Tωˢ = Ord₊ˢ.lim tkˢ

GLω : Σ (Goodᴸ (toZ Tωˢ)) λ G → Lab (forceᴸ _ G) tω
GLω = limᴸ tω-NF refl (λ k → proj₁ (GLk k)) (λ k → subst (Lab _) (sym (fs-tω k)) (proj₂ (GLk k)))

Gω : Goodᴸ (toZ Tωˢ)
Gω = proj₁ GLω

Tωᴸ : Ordᶜ zero
Tωᴸ = forceᴸ (toZ Tωˢ) Gω

Tω-label : Lab Tωᴸ tω
Tω-label = proj₂ GLω

_ : Tωᴸ ≡ Ord₊.lim Tkᴸ
_ = refl

Tω-step : ∀ n → FGH Tωᴸ n ≡ FGH (Tkᴸ n) n
Tω-step n = refl

Tω-in-tΩ2 : Lab Tωᴸ (walk tΩ2 (0 ∷ 0 ∷ []))
Tω-in-tΩ2 = Tω-label
```

**一般 $k$ 的外层形状, 与数值.** `lim-shape`: 证书下的计值在 `ĉᴸ` 处是 `lim`; 经 `pop-eq` 得 `Tk-lim`/`Tk-step` (对一切 $k\ge1$, 命题等式). `FGH T3ᴸ 0 ≡ 1` 是 `refl` (几秒).

```agda
lim-shape : ∀ {x c t₀ g o₀ o} → x ≡ ĉᴸ c t₀ g o₀ o → (G : Goodᴸ x) → Σ (ℕ → Ordᶜ zero) λ χ → forceᴸ x G ≡ Ord₊.lim χ
lim-shape refl (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) = _ , refl

Tk-lim : ∀ n → Σ (ℕ → Ordᶜ zero) λ χ → Tkᴸ (suc n) ≡ Ord₊.lim χ
Tk-lim n = lim-shape (cong toZ (pop-eq {p = z1} {σ = λ q → q} {z = z1} (AΩ-rep n))) (Gk (suc n))

Tk-step : ∀ n m → FGH (Tkᴸ (suc n)) m ≡ FGH (proj₁ (Tk-lim n) m) m
Tk-step n m = cong (λ X → FGH X m) {x = Tkᴸ (suc n)} {y = Ord₊.lim (proj₁ (Tk-lim n))} (proj₂ (Tk-lim n))

_ : FGH T3ᴸ 0 ≡ 1
_ = refl
```

## §4 (c) $\psi_0(\Omega_\Omega^2)$: 停点与所缺

**记号侧 (`refl`).** OmegaKBase §1: $\psi_0(\Omega_\Omega^2)[m]=\psi_0(\psi_\Omega(\Omega_{\gamma_m}))$; $[0][n]=\psi_0(\psi_\Omega(t_\omega[n]))$; $[0][0]=t_\omega$ (已标, `Tω-in-tΩ2`). 沿 $[0,1,1,0,0]$ 到 $\psi_0(\psi_\Omega(\psi_0(1)))$, 再 $[2]$ 到 $\psi_0(\psi_\Omega(2))=\psi_0(\Omega_\Omega\cdot\omega^2)$, 再 $[2]$ 到 $\psi_0(\psi_\Omega(1)\cdot2)$, 再 $[1]$ 到 `mixed` $=\psi_0(\Omega_\Omega\cdot\omega+\Omega_\Omega)$: 它的折叠要的栈是 "一个 $\Omega_\Omega\cdot\omega$ 帧, 其上一个 $\hat\Omega$ 帧". 第三个 `refl` 说 $[0][n]$ 的 $\psi_\Omega$ 参数就是 $t_\omega[n]=t_n$: 参数是带 $\hat\Omega$ 帧的可数树, 不是自然数.

```agda
mixed : T
mixed = ψᵗ [] (ψᵗ Ωᵗ (natT 1) ∷ ΩΩ ∷ []) ∷ []

_ : walk tΩ2 (0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ 2 ∷ 1 ∷ []) ≡ mixed
_ = refl

_ : walk tΩ2 (0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ []) ≡ ψᵗ [] (ψᵗ Ωᵗ (natT 2) ∷ []) ∷ []
_ = refl

_ : ∀ n → walk tΩ2 (0 ∷ 1 ∷ n ∷ []) ≡ ψᵗ [] (ψᵗ Ωᵗ (fsn tω n) ∷ []) ∷ []
_ = λ n → refl
```

**所缺, 精确地.**

1. **帧种类.** Prefix 的 `Frame` 只有 `fΩ̂` ($\Omega_\Omega$) 与 `fT` (可数层的树前缀). $\psi_0(\Omega_\Omega^2)$ 的后代需要 $\Omega_\Omega\cdot\omega^\eta$ 帧 ($\eta$ 可数): 弹出规则 $\omega^{\eta+1}\mapsto\lim_m(\omega^\eta)^m$ (帧数由**这一层的基本列下标** $m$ 决定, 即 "帧数是链点/基本列数据"), $\omega^{\lambda}\mapsto\lim_m\omega^{\lambda[m]}$; 链点 $\psi_0(\psi_\Omega(\Omega_{\gamma_m}))$ 处还要 $\psi_\Omega$ 作用于不可数参数 $\Omega_{\gamma_m}$ (一个以 $\Omega$-共尾为参数的帧, 其 $\Omega$-基本列 $[\eta]=\psi_\Omega(\eta)$ 把可数的树 $\eta$ 变成帧指数).
2. **停机的度量.** Prefix 的 $\psi^P$ 以栈长 $n$ 为下标, 停机度量 ($n$, 尾巴). 帧数可增 (弹出一个 $\omega$-帧得到任意多个 $\hat\Omega$) 时这个度量失效. 编译的否定 (临时文件 `NegFω.agda`, 不进本文): 在 Prefix 的折叠上加帧 `fω z`, 子句 `ψᵛ (suc n) p σ (fω z ∷ P) zero = lim (λ m → ψᵛ (m +ℕ n) p σ (replicate m (fΩ̂ z) ++ P) zero)`, 其余子句与 `ψᴾ` 相同 (弹 $\hat\Omega$ 时用 `relevel` 重建栈):

        [TerminationIssue]
        Termination checking failed for the following functions:
          ψᵛ
        Problematic calls:
          ψᵛ n p σ P (limᵢ q f) | <ᴵ-dec (σ q) p
          ψᵛ n (σ q) σ P (f (intoˢ (<→◃ q) x))
          ψᵛ n (lim 0 zero) (lim 1) (relevel (lim 0 (z<suc z p)) P) (Ωˢ η)
          ψᵛ (m +ℕ n) p σ (replicate m (fΩ̂ z) ++ P) zero

    对照组 (`NegFωCtrl.agda`, 同一文件, 只把 `fω` 的子句换成 `lim (λ m → ψᵛ n p σ P zero)`) 编译通过, 所以失败只来自 "帧数增加" 这一条.
3. **有限指数时的修补 (编译的肯定).** 把栈写成计数器: $\Omega_\Omega\cdot\omega\cdot c_1+\Omega_\Omega\cdot c_0$, 弹 $\hat\Omega$ 时 $c_0$ 降, 弹 $\omega$-帧时 $c_1$ 降而 $c_0:=m$ 任意; 检查器找到 $(c_1,c_0,\text{尾巴})$ 的字典序. 下面的 `ψ²` 编译通过, $\omega$-帧的弹出字面是 $\lim_m\psi^{[\hat\Omega]^m}$ (`refl`). 它覆盖 $\psi_0(\Omega_\Omega\cdot\omega\cdot c_1+\Omega_\Omega\cdot c_0+a)$, 即 $\psi_0(\Omega_\Omega\cdot\omega^2)$ 之下 (包括 `mixed`). 但 (i) 本文的标签理论 (OmegaKBase 的 `Pre0K₊` 等) 是对 `ψᴾ` 写的, 对 `ψ²` 要整套重写 (弹 $\omega$-帧的子句是 `limᴸ` 加对 $c_0$ 的递归, 其余逐字), 未做; (ii) 指数 $d$ 个计数器的版本要 $d+1$ 个显式参数, 对一切有限 $d$ 统一写须以 `Vec` 存计数器, 字典序不再是结构的; (iii) $\psi_0(\Omega_\Omega^2)$ 要可数**树**为指数 ($\eta=t_\omega,t_1,\ldots$), 计数器序列以序数为下标, 度量至少是 $\omega^{\eta}$ 型的序数, 需要以 `Acc` 或树本身为度量的折叠, 那会失去 `ψᴾ` 子句的定义性展开 (本文所有 `refl` 依赖它).

```agda
ψ² : ∀ (c₁ c₀ : ℕ) {i k ℓ} → i <ᴵ ℓ → Simᴵ k ℓ → zero <ᴵ ℓ → Ordˢ k → Ordˢ i
ψ² c₁ c₀ p σ z (Ord₊ˢ.suc a) = Ord₊ˢ.lim (iter (ψ² c₁ c₀ p σ z a +ˢ_) Ord₊ˢ.zero)
ψ² c₁ c₀ p σ z (Ord₊ˢ.lim f) = Ord₊ˢ.lim (λ m → ψ² c₁ c₀ p σ z (f m))
ψ² c₁ c₀ p σ z (Ord₊ˢ.limᵢ {i = j} q f) with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = Ord₊ˢ.limᵢ r (λ y → ψ² c₁ c₀ p σ z (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) y)))))
... | injᵇ _ = Ord₊ˢ.lim (λ m → ψ² c₁ c₀ p σ z (f (intoˢ (<→◃ q) (iter (λ x → ψ² c₁ c₀ (σ q) σ z (f (intoˢ (<→◃ q) x))) (Ωˢ j) m))))
... | injᶜ _ = Ord₊ˢ.lim (λ m → ψ² c₁ c₀ p σ z (f (intoˢ (<→◃ q) (iter (λ x → ψ² c₁ c₀ (σ q) σ z (f (intoˢ (<→◃ q) x))) (Ωˢ j) m))))
ψ² c₁ c₀ p σ z (Ord₊ˢ.up zero x)     = ψ² c₁ c₀ p (λ q → σ (suc q)) z x
ψ² c₁ c₀ p σ z (Ord₊ˢ.up (self m) x) = ψ² c₁ c₀ p (λ q → σ (lim m q)) z x
ψ² c₁ c₀ p σ z (Ord₊ˢ.ŝ c t₀ g)       = Ord₊ˢ.ŝ c (ψ² c₁ c₀ p σ z t₀) (λ η e → ψ² c₁ c₀ p σ z (g η e))
ψ² c₁ c₀ p σ z (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) = Ord₊ˢ.ĉᴸ c t₀ g (ψ² c₁ c₀ p σ z o₀) (λ η e → ψ² c₁ c₀ p σ z (o η e))
ψ² zero     zero     p σ z Ord₊ˢ.zero = Ωˢ _
ψ² c₁       (suc c₀) {i} p σ z Ord₊ˢ.zero =
  Ord₊ˢ.ŝ (suc i) (ψ² c₁ c₀ zero (σ1 (z<suc z p)) (z<suc z p) (Ωˢ (suc zero)))
          (λ η e → ψ² c₁ c₀ {ℓ = Mlev (suc i) η e} (lim 0 zero) (λ q → lim 1 q) (lim 0 (z<suc z p)) (Ωˢ η))
ψ² (suc c₁) zero     p σ z Ord₊ˢ.zero = Ord₊ˢ.lim (λ m → ψ² c₁ m p σ z Ord₊ˢ.zero)

_ : ψ² 1 0 z1 (λ q → q) z1 Ord₊ˢ.zero ≡ Ord₊ˢ.lim (λ m → ψ² 0 m z1 (λ q → q) z1 Ord₊ˢ.zero)
_ = refl
```

**对 (c) 的结论.** $\psi_0(\Omega_\Omega^2)$ 的标签**未得**; 已得的是它的子项 $[0][0]=\psi_0(\Omega_\Omega\cdot\omega)$ (`Tω-in-tΩ2`) 与一切 $\psi_0(\Omega_\Omega\cdot k+a)$ 型后代 (OmegaKBase 的 `Pre0VK`, 只要尾巴 $a$ 有 `LabL` 推导). 第一个不在覆盖内的后代: $[0][1]=\psi_0(\psi_\Omega(t_\omega))$ (需 $\Omega_\Omega\cdot\omega^{t_\omega}$ 帧); 第一个 "混合栈" 后代: `mixed`, 路径 $[0,1,1,0,0,2,2,1]$. 缺的引理: 带 $\omega^\eta$-帧的折叠 (停机度量为序数) 及其上的 `Pre0K₊`/`PreK₊` 类比; 弹 $\omega^{\eta+1}$-帧的标签就是 (b) 的 `limᴸ` 论证 (外层基本列下标选帧数), 弹 $\psi_\Omega(\Omega_\theta)$ 的标签是 $\Omega$-共尾的 `gi`/`gŝ` 类行, 其地板是 $\psi_\Omega$ 的可数下标位置, 与 GoodL §5 的 $\psi_\Omega$ 帧 (地板 $\Omega$ 不可数, `occ<` 失效) 不同, 上面算出的基本列里 $\psi_\Omega$ 只穿透不折叠 (参数的共尾度 $\Omega_\theta$, $\theta$ 可数, 都 $<\Omega$), 它出现在 $\psi_0$ 的参数里而不是弹栈目标 (观察, 只核对了上述路径).

## §5 对比表

| | GoodL (单帧) | 本文 |
|---|---|---|
| 树 | `t2ˢ = ψᴾ 2 …` | `tkˢ k = ψᴾ k … (replicate k (fΩ̂ z1)) zero`, `Tωˢ = lim tkˢ` |
| 带前缀引理 | `Pre0Vᴸ`/`PreL₊` (`ψ1`) | `Pre0VK n`/`PreK₊ n` (`ψᴾ (suc n)`, `AΩ P`) |
| 用到帧数的引理 | (无) | `popLK`, `pop0K` (递归到 $n-1$ 帧), `ψK-≅`, `pop-eq` |
| 链证书 | `K2`: 点由 `Pre0Vᴸ` | `pop0K (suc m)` 的 `K`: 点由 `Pre0VK m` |
| 证书 | `G2` 闭项 | `Gk k` 对 $k$ 的闭项, `G3`, `Gω` |
| 标签 | `T2-label` | **`Tk-label : ∀ k`**, **`Tω-label`** |
| 外层 FGH 方程 | `T2-step` (`refl`) | `T3-step`, `Tω-step` (`refl`); `Tk-step` (一切 $k\ge1$, 经 `pop-eq`) |
| 与 Prefix 证书 | `agree-force` ($k=2$, 经 Omega2 的标签) | `agree-forceK` (一切 $k$, 经 `cross`, 不用标签) |
| $\psi_0(\Omega_\Omega^2)$ | — | 未得; `[0][0]` 已标; 缺 $\omega^\eta$-帧 (否定已编译) |

## §6 结论与边界

**字面成立 (`refl`):** `tkˢ 2 ≡ t2ˢ`; `T3ᴸ ≡ lim χ3`, `T3-step`; `Tωᴸ ≡ lim Tkᴸ`, `Tω-step`; `FGH T3ᴸ 0 ≡ 1`; `walk tΩ2 [0,1,1,0,0,2,2,1] ≡ mixed`, `walk tΩ2 [0,1,1,0,0,2] ≡ ψ₀(ψ_Ω(2))`, `walk tΩ2 [0,1,n] ≡ ψ₀(ψ_Ω(tω[n]))`; `ψ² 1 0 … zero ≡ lim (λ m → ψ² 0 m … zero)`.

**定理 (标签按 Correspond 的 `Lab`, 树只到 $\cong$):**

1. **`Tk-label : ∀ k → Lab (Tkᴸ k) (tk k)`**, `GLk`, `Gk`, `Tk-HS`; `G3`, `T3ᴸ`, **`T3-label`**; `T2-agree : Tkᴸ 2 ≅ T2ᴸ`; `Tk-lim`, `Tk-step`.
2. `cross`, `tk-refl`, **`agree-forceK`**, `forced-labelK`, `agree-selfK`.
3. **`Tω-label : Lab Tωᴸ tω`**, `GLω`, `Gω`, `Tω-step`, `Tω-in-tΩ2`.
4. `lim-shape`, `ψ²` (停机).

**标签状态.** 按 README 的认证准则: $\psi_0(\Omega_\Omega\cdot k)$ (一切 $k$) 与 $\psi_0(\Omega_\Omega\cdot\omega)$ 的遗传标签是**无条件定理** (树是 `Goodᴸ` 证书下的计值树, 外层 FGH 方程字面成立 ($k$ 具体时) 或经 `pop-eq` 命题成立 (一切 $k$), 每一层的方程模 $\cong$). $\psi_0(\Omega_\Omega^2)$ 仍是估计以外的未定项: 树侧的折叠尚未定义.

**边界.**

- 树只到 $\cong$; `Tkᴸ` 与 Prefix 证书的计值 $\cong$ (`agree-forceK`), 但 `Goodᶻ (toZ (tkˢ k))` 是否存在仍未知 ($k=2$ 时 Omega2 也未得).
- 对抽象 $k$, 外层形状经 `pop-eq` (命题等式), 不是 `refl`.
- 数值核对只到 `FGH T3ᴸ 0`.
- 不改 `src/`、`archive/` 与已有的 Align 文件, README 未改.
