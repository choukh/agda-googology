# $\psi_0(\Omega_\Omega^2)$ 的前半: 低目标帧真实出现, 第 1 层指数帧与它的带前缀引理

> 接 [OmegaExpBase](OmegaExpBase.lagda.md) 与 [OmegaExp](OmegaExp.lagda.md) §4. 本文是 [OmegaSq](OmegaSq.lagda.md) 的前半: 低目标问题的判定 (任务 1)、新的指数折叠 `ψᵉ′` (任务 2)、第 0 与第 1 层指数的带前缀引理与好栈 (任务 3). 决定性检验 (`TΩ2-label` 的状态) 在 OmegaSq.
>
> 结论先说:
>
> 1. **低目标情形真实出现 (§1, 编译的反例).** $t_{\Omega2}=\psi_0(\psi_\Omega(\Omega_\Omega))$ 沿 $\omega$-路径 `pathLow` $=[1,0,1,0,0,3,1,0,0,1,0,0]$ 到达 $\psi_0(\psi_\Omega(\psi_2(1)))$, 再走 $[2,0,0]$ 到达 $\psi_0(\psi_\Omega(\Omega_2+1))$ (都 `refl`). 这里指数 $\Omega_2+1$ 是第 2 层的后继, 而目标是 $0<2-1$: 弹出 $\omega^{\Omega_2+1}$ 要压第 2 层指数的帧 $\psi_\Omega(\Omega_2)$, 帧产生于目标 0. 它不是穿透产生的, 而是 "第 2 层的和 $\Omega_2+\Omega_1$ 在目标 0 被折叠访问, 链的第 0 点 $\Omega_0=1$ 落进和的末项" (`walk (ψΩ₀ ψ₂1) [2] ≡ ψΩ₀ (Ω₂+Ω₂)`, `[2,0] ↦ Ω₂+Ω₁`). 再走 $[2,0,0,1]$ 到 $\psi_0(\psi_\Omega(\Omega_2)+\Omega_\Omega)$: 第 2 层的帧之上弹出 $\hat\Omega$, 闭包的第 0 点 $\psi_0(\psi_\Omega(\Omega_2)+\Omega_1)$ 在紧界的环境层号 $1$ 上计算第 2 层的帧, 要 `Simᴵ 2 1`, 编译的否定 **`noSim21 : Simᴵ 2 1 → ⊥`** (分支处是 OmegaExp 的 `noSim2`). 树侧 (§3): 同一位置上的符号树 (`ψᵉ′`, 第 $\ge2$ 层后继的占位值取为 $0$, 而 $\psi$ 的值从不是 $0$) 字面是 `Ord₊ˢ.zero` (`kind … ≡ kz`, `refl`), 记号侧是 $\omega$-共尾的极限 (`cof … ≡ cω`, `refl`). 所以 OmegaExp §4 的情形 3 **出现在 $t_{\Omega2}$ 的带标签点中**, 只给栈类型加地板 $k\sqsubseteq i$ 不够: 还要非紧的闭包 (界与第 0 点的环境层号取 "目标与帧层号之大者 $+1$") 以及它的支配论证.
> 2. **新的指数折叠 `ψᵉ′` (§2).** OmegaExpBase 的 `ψᵉ` 的复制, 只改后继子句: 第 0 层与第 1 层的后继 $Y+1$ 都给 $\lim_m$ `repᴷ S s Y m` ($m$ 个指数为 $Y$ 的帧 `S ▹[ s ] Y`), 帧的 `Sim` 由帧证据 $z:0<^\mathsf I\ell$ 现造: 第 0 层是常量 `s₀ = λ _ → σ⊥`, 第 1 层是 `σ1`. 第 $\ge2$ 层的后继仍是占位值 (改为 $0$, 以便树侧检验能认出它); §1 说明它在 $t_{\Omega2}$ 中可达, 且不是写法问题. 停机度量仍是 (指数, 重数), 一次通过; 栈类型 `Stk` 不变.
> 3. **第 0、1 层指数的带前缀引理与好栈 (§4–§6).** 以指数为 "尾巴": `WE₀`/`ZE₀` (对 `Lab0ᴸ` 递归) 与 `WE₁`/`ZE₁` (对第 1 层的 `LabL₊` 推导递归), 分别是目标 $w\ne0$ 的 `LabL₊` 与目标 $0$ 的证书和标签, 前缀任意 (`Goodˢ S ps`). 新的好栈构造 **`GoodE₀`** (第 0 层指数帧, 与 OmegaExpBase 的 `GoodE` 同) 与 **`GoodE₁`** (第 1 层指数帧), 分别与 `repGood₀`/`repGood₁` 互递归. 第 1 层的 `gi` 行 ($j=0$) 在目标 $\ne0$ 时穿透 (`giPreE`), 在目标 $0$ 时折叠成第 0 层的链 (`liLabE`); `gŝ` 行 (第 1 层的闭包, 来自目标 1 的弹栈) 在目标 $\ne0$ 时仍是带同一地板的闭包, 在目标 $0$ 时是链证书 (`ŝChainG`, 支配用 `domS`). 互模拟 `ψᵉ′-≅` 只对第 $\le1$ 层的指数陈述 (`Lo`), 因为第 $\ge2$ 层的后继是占位值.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件; `ψᵉ` 的新版本以新名字 `ψᵉ′` 复制在本文.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OmegaSqBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import Data.List.Properties using (++-identityʳ)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev; σ1)
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; z<suc; H1-pen;
  tr⁻ˢ; sqˢ; walkˢ; kind; Kind; kz; ks; kl; kĉ; kc)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; γT; sucT; cmpᵀ; lt; eq; gt;
              cofA; 𝟏) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fs-rep; fs-ω)
open import OCF.Align.Bachmann using (fs-gt; pen→<; gt→≤; clash)
open import OCF.Align.Closure using (Pen; fsT₊-pen′)
open import OCF.Align.StandardOmega using (NF₁; NF₁-fsn; walk; walkD; tO-desc-NF)
open import OCF.Align.Standard using (d₀)
open import OCF.Align.SystemOmega using (Occ; od; cmp-CΩ; Ctbl-suc)
open import OCF.Align.Stage2 using (Ωᵗ; tO)
open import OCF.Align.UniformS
open import OCF.Align.DecoupleBase using (ΩΩ; ŝ-reflg)
open import OCF.Align.Decouple using (Idx; lvI; Ilt; Ieq; kdI; kdI′; gtν; kdI[]; cofP)
open import OCF.Align.GoodLBase
open import OCF.Align.OmegaKBase using (tΩ2)
open import OCF.Align.OmegaExp using (ψΩ₀)
open import OCF.Align.OmegaExpBase
```

## §1 任务 1: 低目标情形出现在 $t_{\Omega2}$ 的带标签点中

**问题.** OmegaExp §4 把第 $k$ 层指数的帧分成三种: $k\le1$ (帧证据够用); $k\ge2$ 且帧在目标 $i\succeq k-1$ 处产生 (栈类型带地板即可); $k\ge2$ 且帧在目标 $i<k-1$ 处产生 (紧界闭包放不下, `noSim2`). 第三种是否出现在 $t_{\Omega2}$ 的带标签点中, 当时未定 (深度 11 的搜索未见).

**判定: 出现.** 下面的路径都是 $\omega$-基本列 (`fsn`), 全部 `refl`. 机制: 第 2 层的 $\psi_2(1)=\Omega_2\cdot\omega$ 作为指数, $[2]$ 给和 $\Omega_2+\Omega_2$; 它的共尾度 $\Omega_2$ 在目标 0 处折叠 (链在目标 1, 链的第 0 点 $\Omega_1$), $[0]$ 给 $\Omega_2+\Omega_1$; 再折叠 (链在目标 0, 第 0 点 $\Omega_0=1$), $[0]$ 给 $\Omega_2+1$. 于是目标 0 处出现第 2 层的后继指数. 路径的前半段 `pathLow` 从 $t_{\Omega2}$ 经 OmegaExp 的 $\psi_0(\psi_\Omega(\Omega_3))$ (前 6 步) 到 $\psi_0(\psi_\Omega(\psi_2(1)))$: $\psi_2(\psi_\Omega(\Omega_2))$ 两次折叠到 $\psi_2(\psi_\Omega(1))$, $[1]$ 给 $\psi_2(\Omega_\Omega)$, 闭包的第 0 点 $\psi_2(\Omega_1)$, 再折叠到 $\psi_2(1)$. (临时脚本 `exp/omegasq/path.py` 用 `ebo.py` 逐步算出; `bfs2.py` 从 $\psi_0(\psi_\Omega(\Omega_3))$ 以分支 $0..2$ 广度搜索 "某个 $\psi_\delta(\cdots\psi_\Omega(\eta)\cdots)$, $\eta$ 后继且层号 $\ge\delta+2$", 最短就是这里的 9 步. OmegaExp 的 `search2.py` 深度 11 未见, 因为从 $t_{\Omega2}$ 起这条路径长 15, 到 $\hat\Omega$ 弹栈长 19.)

```agda
ψ₂1 Ω₂ Ω₂+1 : T
ψ₂1  = ψᵗ (natT 2) (natT 1) ∷ []
Ω₂   = Ωt (natT 2)
Ω₂+1 = ψᵗ (natT 2) [] ∷ 𝟏 ∷ []

pathLow : List ℕ
pathLow = 1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 3 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ []

_ : walk tΩ2 (1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 3 ∷ []) ≡ ψΩ₀ (Ωt (natT 3))
_ = refl

low-walk : walk tΩ2 pathLow ≡ ψΩ₀ ψ₂1
low-walk = refl

_ : walk (ψΩ₀ ψ₂1) (2 ∷ []) ≡ ψΩ₀ (ψᵗ (natT 2) [] ∷ ψᵗ (natT 2) [] ∷ [])
_ = refl

_ : walk (ψΩ₀ ψ₂1) (2 ∷ 0 ∷ []) ≡ ψΩ₀ (ψᵗ (natT 2) [] ∷ ψᵗ (natT 1) [] ∷ [])
_ = refl

low-term : walk (ψΩ₀ ψ₂1) (2 ∷ 0 ∷ 0 ∷ []) ≡ ψΩ₀ Ω₂+1
low-term = refl

low-cof : cof (ψΩ₀ Ω₂+1) ≡ cω
low-cof = refl

low-c1 : cof Ω₂+1 ≡ c1
low-c1 = refl

low-pop : walk (ψΩ₀ Ω₂+1) (2 ∷ 0 ∷ 0 ∷ 1 ∷ []) ≡ ψᵗ [] (ψᵗ Ωᵗ Ω₂ ∷ ΩΩ ∷ []) ∷ []
low-pop = refl

low-NF : NF₁ (ψΩ₀ Ω₂+1)
low-NF = tO-desc-NF (walkD d₀ (1 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 3 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ [])
                             (refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl ,
                              refl , refl , refl , refl , tt))
```

**读法.** `low-term` 是第三种情形: 目标 $0$, 指数 $\Omega_2+1$ (`low-c1`: 后继), 其前驱 $\Omega_2$ 在第 2 层, $0<2-1$. 记号侧这一点是合法的标准形 ψ₀(Ω_{Ω+1}) 后代 (`low-NF`), 共尾度 $\omega$ (`low-cof`, 规则 4: $\psi_\Omega(\Omega_2+1)[m]=\psi_\Omega(\Omega_2)\cdot m$). `low-pop` 是后果: 第 2 层指数的帧 $\psi_\Omega(\Omega_2)$ 之上弹出 $\hat\Omega$. `Lab` 是遗传的, 所以 `Lab TΩ2ᴸ tΩ2` 蕴含这些点都带标签; 它们不在任何可以绕开的分支上 (都是 `fsn`, 不是 `fsT` 的特殊 $\theta$).

**为什么地板不够.** 地板方案 (栈对 $k\sqsubseteq i$ 的目标多态) 只覆盖帧产生于目标 $\succeq k-1$ 的情形, 因为它靠 "目标只升不降". 这里帧产生于目标 0: 弹出 $\hat\Omega$ 的紧界闭包 (界 $0+1$) 的第 0 点 $\psi_0(\psi_\Omega(\Omega_2)+\Omega_1)$ 在环境层号 $1$ 上计算, 而帧的指数 $\Omega_2$ 在目标 0 处要沿第 1 层的链折叠 ($\Omega_2$ 的共尾度 $\Omega_2$, $1\succ0$), 链点 $\psi_1(\cdots)$ 的目标 $1$ 必须 $<^\mathsf I$ 环境层号. 任何以 `Simᴵ k ℓ` 计算第 $k$ 层指数的帧都要 `Simᴵ 2 1`:

```agda
noSim21 : Simᴵ (suc (suc zero)) (suc zero) → ⊥
noSim21 σ with σ {suc zero} zero
... | suc ()
```

所以要的不是地板, 而是**非紧的闭包**: 弹出 $\hat\Omega$ 时的界与第 0 点的环境层号取 $\max(i,F)+1$, $F$ 是剩余栈中帧指数的层号 (此例 $F=1$, 界 $2$). 支配: 闭包的链点标签是 $\psi_0(\psi_\Omega(\Omega_2)+\Omega_\theta)$, 下标 $2$ 出现在每个 $t[\theta]$ 里, 所以 GoodLBase 的 `gŝ` 行的地板字段 (任意带 `Idx` 且在一切 $t[\theta]$ 中出现的 $w$, 界 $c\sqsubseteq\mathtt{lvl}\,w+1$) 已经容许它 ($w=2$, $c=3$). 缺的是树侧: 栈要暴露 $F$ (栈类型以 $F$ 为下标, 帧的 `Sim` 由 $F\prec^\mathsf I\ell$ 现造), 以及标签侧把树的层号 $F$ 对上某个在标签中出现的下标的引理. 见 OmegaSq §4 的结论.

## §2 任务 2: 新的指数折叠 `ψᵉ′`

OmegaExpBase `ψᵉ` 的复制; 不同只在后继子句:

- 第 $k$ 层 ($k\in\{0,1\}$) 的后继 $Y+1$: $\psi_\Omega(\eta+1)[m]=\psi_\Omega(\eta)\cdot m$, 给 $\lim_m$ `repᴷ S s Y m z p`, `repᴷ S s Y (m+1) = repᴷ S s Y m ▹[ s ] Y`, 帧 `(S ▹[ s ] Y) z p = ψᵉ′ S z p (s z) Y`. 帧的 `Sim` 由帧证据 $z$ 现造: `s₀ _ = σ⊥` (第 0 层; 唯一常量, 见 OmegaExpBase 的技术点), `σ1` (第 1 层: $0<^\mathsf I\ell$ 就是 `Simᴵ 1 ℓ`).
- 第 $\ge2$ 层的后继: 占位值 `Ord₊ˢ.zero`. 改用 $0$ (OmegaExpBase 用 $\Omega_i$) 是为了树侧检验 (§3): $\psi_i(\cdots)$ 从不等于 $0$, 所以 `kind … ≡ kz` 精确地指出占位子句被走到.

其余子句 (零、极限、`limᵢ` 的穿透与折叠、`up`、`ŝ`、`ĉᴸ`) 与 `ψᵉ` 逐字. `▹Ω̂²′`: `▹Ω̂²` 改用 `ψᵉ′`.

```agda
s₀ : ∀ {ℓ} → zero <ᴵ ℓ → Simᴵ zero ℓ
s₀ _ = σ⊥

ψᵉ′  : Stk → ∀ {i k ℓ} → zero <ᴵ ℓ → i <ᴵ ℓ → Simᴵ k ℓ → Ordˢ k → Ordˢ i
repᴷ : Stk → ∀ {k} → (∀ {ℓ} → zero <ᴵ ℓ → Simᴵ k ℓ) → Ordˢ k → ℕ → Stk
_▹[_]_ : Stk → ∀ {k} → (∀ {ℓ} → zero <ᴵ ℓ → Simᴵ k ℓ) → Ordˢ k → Stk

ψᵉ′ S z p σ Ord₊ˢ.zero = (S ▹Ω̂) z p
ψᵉ′ S {k = zero}        z p σ (Ord₊ˢ.suc a) = Ord₊ˢ.lim (λ m → repᴷ S s₀ a m z p)
ψᵉ′ S {k = suc zero}    z p σ (Ord₊ˢ.suc a) = Ord₊ˢ.lim (λ m → repᴷ S σ1 a m z p)
ψᵉ′ S {k = suc (suc _)}   z p σ (Ord₊ˢ.suc a) = Ord₊ˢ.zero
ψᵉ′ S {k = suc (lim _ _)} z p σ (Ord₊ˢ.suc a) = Ord₊ˢ.zero
ψᵉ′ S {k = lim _ _}       z p σ (Ord₊ˢ.suc a) = Ord₊ˢ.zero
ψᵉ′ S z p σ (Ord₊ˢ.lim f) = Ord₊ˢ.lim (λ m → ψᵉ′ S z p σ (f m))
ψᵉ′ S z p σ (Ord₊ˢ.limᵢ {i = j} q f) with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = Ord₊ˢ.limᵢ r (λ y → ψᵉ′ S z p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) y)))))
... | injᵇ _ = Ord₊ˢ.lim (λ m → ψᵉ′ S z p σ (f (intoˢ (<→◃ q) (iter (λ x → ψᵉ′ S z (σ q) σ (f (intoˢ (<→◃ q) x))) (Ωˢ j) m))))
... | injᶜ _ = Ord₊ˢ.lim (λ m → ψᵉ′ S z p σ (f (intoˢ (<→◃ q) (iter (λ x → ψᵉ′ S z (σ q) σ (f (intoˢ (<→◃ q) x))) (Ωˢ j) m))))
ψᵉ′ S z p σ (Ord₊ˢ.up zero x)     = ψᵉ′ S z p (λ q → σ (suc q)) x
ψᵉ′ S z p σ (Ord₊ˢ.up (self m) x) = ψᵉ′ S z p (λ q → σ (lim m q)) x
ψᵉ′ S {k = zero}    z p σ (Ord₊ˢ.ŝ c t₀ g) = Ord₊ˢ.ĉᴸ c (toZ t₀) (λ η e → toZ (g η e)) (ψᵉ′ S z p σ t₀) (λ η e → ψᵉ′ S z p σ (g η e))
ψᵉ′ S {k = suc _}   z p σ (Ord₊ˢ.ŝ c t₀ g) = Ord₊ˢ.ŝ c (ψᵉ′ S z p σ t₀) (λ η e → ψᵉ′ S z p σ (g η e))
ψᵉ′ S {k = lim _ _} z p σ (Ord₊ˢ.ŝ c t₀ g) = Ord₊ˢ.ŝ c (ψᵉ′ S z p σ t₀) (λ η e → ψᵉ′ S z p σ (g η e))
ψᵉ′ S z p σ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) = Ord₊ˢ.ĉᴸ c t₀ g (ψᵉ′ S z p σ o₀) (λ η e → ψᵉ′ S z p σ (o η e))

(S ▹[ s ] a) z p = ψᵉ′ S z p (s z) a

repᴷ S s a zero    = S
repᴷ S s a (suc m) = repᴷ S s a m ▹[ s ] a

_▹Ω̂²′ : Stk → Stk
(S ▹Ω̂²′) {i} z p =
  Ord₊ˢ.ŝ (suc i) (ψᵉ′ S (z<suc z p) zero (σ1 (z<suc z p)) (Ωˢ (suc zero)))
          (λ η e → ψᵉ′ S {ℓ = Mlev (suc i) η e} (lim 0 (z<suc z p)) (lim 0 zero) (λ q → lim 1 q) (Ωˢ η))
```

**读法 (停机).** 与 `ψᵉ` 相同, 一次通过: `ψᵉ′ … (suc Y)` → `repᴷ S s Y m` (指数降), `repᴷ (suc m)` → `repᴷ m` (重数降) 与 `ψᵉ′ (repᴷ …) … Y` (指数同). `repᴷ` 对层号 $k$ 多态, 帧证据函数 `s` 只是参数. 第 1 层的帧之所以可写, 是因为 `σ1 : 0 <ᴵ ℓ → Simᴵ 1 ℓ` 不需要任何关于 $\ell$ 的额外信息; 第 2 层要 `1 <ᴵ ℓ`, 多态的 `Stk` 不提供 (OmegaExpBase 的 `NegLv2`), §1 说明即使提供 "目标的地板" 也不够.

**旧定理不受影响.** 本文不改 OmegaExpBase/OmegaExp; 旧的 `ψᵉ`/`rep`/`GoodE`/`Tη-label` 原样成立. 新旧折叠在第 0 层指数上给出带同一标签的树, 所以经 `Lab-uniq` 互为 $\cong$ (OmegaSq §1 的 `Tη-agree`); 第 1 层的指数在旧折叠里从未被标过 (OmegaExp 的 `TΩ2-0-label` 只在第 0 层的链点处计值), OmegaSq §1 用新的 `ZE₁` 重新得到 $\psi_0(\Omega_\Omega\cdot\Omega)$ 的标签并与旧的对上 (`TΩ2-0-agree`).

## §3 树侧检验: 占位子句在 $t_{\Omega2}$ 的后代处被走到

$\psi_0(\psi_\Omega(\psi_2(1)))$ 的符号树: 指数 `ψ₂1ˢ` 是空栈在目标 2、环境层号 3 处对尾巴 $1$ 的折叠 ($\psi_2(1)=\lim_m\Omega_2\cdot m$), 外层在目标 0、环境层号 3 处 (`σ` 把第 2 层嵌进 3; `two` 取自 UniformS). 沿 $[2,0,0]$ 下降 (`walkˢ`: 走 `lim` 的第 $n$ 项): $[2]$ 是 $\Omega_2+\Omega_2$ 的折叠 (`kl`), $[2,0]$ 是 $\Omega_2+\Omega_1$ 的折叠 (`kl`), $[2,0,0]$ 是 `ψᵉ′` 作用于第 2 层的 `Ord₊ˢ.suc` 的占位值 $0$ (`kz`). 记号侧同一点是 $\omega$-共尾的极限 (§1 `low-cof`).

```agda
three : Ordᴵ
three = suc two

z3 : zero <ᴵ three
z3 = suc (suc zero)

ψ₂1ˢ : Ordˢ two
ψ₂1ˢ = ψˢ ∅ˢ {ℓ = three} z3 zero σ⊥ (Ord₊ˢ.suc Ord₊ˢ.zero)

lowˢ : Ordˢ zero
lowˢ = ψᵉ′ ∅ˢ z3 z3 (λ q → suc q) ψ₂1ˢ

_ : kind (walkˢ lowˢ (2 ∷ [])) ≡ kl
_ = refl

_ : kind (walkˢ lowˢ (2 ∷ 0 ∷ [])) ≡ kl
_ = refl

low-tree : kind (walkˢ lowˢ (2 ∷ 0 ∷ 0 ∷ [])) ≡ kz
low-tree = refl

low-unlab : (G : Goodᴸ (toZ (walkˢ lowˢ (2 ∷ 0 ∷ 0 ∷ [])))) → Lab (forceᴸ _ G) (ψΩ₀ Ω₂+1) → ⊥
low-unlab gz (l0 () e)
low-unlab gz (l1 () e l)
low-unlab gz (lω c () h)
```

**读法.** `low-tree` 是编译的失配: 树在 $[2,0,0]$ 处是 $0$ (占位), 记号是 $\psi_0(\psi_\Omega(\Omega_2+1))$, 共尾度 $\omega$. `low-unlab`: 这棵树上的任何证书 (只有 `gz`) 计值后都不带这个标签 (`l0` 要共尾度 $0$, `lω` 要 $0\cong\lim$, `l1` 要 $1$; 三者都由 `()` 排除). 把占位换成任何真的帧都要在 §1 的 `low-pop` 处计算 `Simᴵ 2 1` (`noSim21`), 或者换成非紧的闭包.

## §4 互模拟, 折叠方程, 记号

**互模拟只对第 $\le1$ 层的指数.** `Lo k`: $k$ 字面为 $0$ 或 $1$. `ψᵉ′-≅` 是 OmegaExpBase `ψˢ-≅`/`ψᵉ0-≅` 的合体: 尾巴 $0$ 处用 `▹Ω̂-≈`, 后继处 `repᴷ-≈` (对重数, 与 `ψᵉ′-≅` 互递归), `limᵢ` 处照 `liS` 把两个递归调用当 λ 传给 `liE`. 后继在两侧层号不同 ($0$ 与 $1$, 经 `up` 的互模拟) 时也成立, 因为 `repᴷ-≈` 对帧证据函数 `s`、`s′` 多态. 第 $\ge2$ 层的后继是占位值, 一般不与真值互模拟, 所以需要 `Lo`; 推导经 `up` 只会降层, `Lo` 随之保持.

```agda
data Lo : Ordᴵ → Set where
  lo0 : Lo zero
  lo1 : Lo (suc zero)

liE : ∀ {S S′ : Stk} {i i′ k₁ ℓ₁ k₂ ℓ₂ j j′} {z : zero <ᴵ ℓ₁} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁}
      {z′ : zero <ᴵ ℓ₂} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂}
      {q : j <ᴵ k₁} {q′ : j′ <ᴵ k₂} {f : Uˢ j (<→◃ q) → Ordˢ k₁} {g : Uˢ j′ (<→◃ q′) → Ordˢ k₂} →
      i ≅ᴵ i′ → j ≅ᴵ j′ →
      (∀ (x : Ordˢ j) (y : Ordˢ j′) → Rˢ j (<→◃ q) (intoˢ (<→◃ q) x) y →
         ψᵉ′ S z p σ (f (intoˢ (<→◃ q) x)) ≅ˢ ψᵉ′ S′ z′ p′ σ′ (g (intoˢ (<→◃ q′) y))) →
      (∀ (x : Ordˢ j) (y : Ordˢ j′) → Rˢ j (<→◃ q) (intoˢ (<→◃ q) x) y →
         ψᵉ′ S z (σ q) σ (f (intoˢ (<→◃ q) x)) ≅ˢ ψᵉ′ S′ z′ (σ′ q′) σ′ (g (intoˢ (<→◃ q′) y))) →
      ψᵉ′ S z p σ (Ord₊ˢ.limᵢ q f) ≅ˢ ψᵉ′ S′ z′ p′ σ′ (Ord₊ˢ.limᵢ q′ g)
liE {S = S} {S′ = S′} {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} {q = q} {q′ = q′} {f = f} {g = g} ei e rec recC
  with <ᴵ-dec (σ q) p | <ᴵ-dec (σ′ q′) p′
... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) = lᵢ≅ (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans e e₂)) λ x y d →
  subst₂ (λ u v → ψᵉ′ S z p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e₁ u))) ≅ˢ ψᵉ′ S′ z′ p′ σ′ (g (intoˢ (<→◃ q′) (tr⁻ˢ e₂ v))))
         (sym (out-intoˢ (<→◃ r₁) x)) (sym (out-intoˢ (<→◃ r₂) y))
         (rec _ _ (≅→Rˢ (<→◃ q) (tr⁻ˢ-≅ e₁ (≅-tr⁻ˢ e₂ (R→≅ˢ (<→◃ r₁) d)))))
... | injᵃ r | injᵇ s  = ⊥-elim (clash₁ e ei r s)
... | injᵃ r | injᶜ c  = ⊥-elim (clash₂ e ei r c)
... | injᵇ s | injᵃ r  = ⊥-elim (clash₁ (≅ᴵ-sym e) (≅ᴵ-sym ei) r s)
... | injᶜ c | injᵃ r  = ⊥-elim (clash₂ (≅ᴵ-sym e) (≅ᴵ-sym ei) r c)
... | injᵇ _ | injᵇ _  = l≅ (λ m → rec _ _ (≅→Rˢ (<→◃ q) (chain m)))
  where chain = iter-R _≅ˢ_ (λ d → recC _ _ (≅→Rˢ (<→◃ q) d)) (Ωˢ-≅ e)
... | injᵇ _ | injᶜ _  = l≅ (λ m → rec _ _ (≅→Rˢ (<→◃ q) (chain m)))
  where chain = iter-R _≅ˢ_ (λ d → recC _ _ (≅→Rˢ (<→◃ q) d)) (Ωˢ-≅ e)
... | injᶜ _ | injᵇ _  = l≅ (λ m → rec _ _ (≅→Rˢ (<→◃ q) (chain m)))
  where chain = iter-R _≅ˢ_ (λ d → recC _ _ (≅→Rˢ (<→◃ q) d)) (Ωˢ-≅ e)
... | injᶜ _ | injᶜ _  = l≅ (λ m → rec _ _ (≅→Rˢ (<→◃ q) (chain m)))
  where chain = iter-R _≅ˢ_ (λ d → recC _ _ (≅→Rˢ (<→◃ q) d)) (Ωˢ-≅ e)

ψᵉ′-≅ : ∀ {S S′ : Stk} → S ≈ˢ S′ → ∀ {i i′ k₁ ℓ₁ k₂ ℓ₂} {z : zero <ᴵ ℓ₁} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁}
        {z′ : zero <ᴵ ℓ₂} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂} {a : Ordˢ k₁} {b : Ordˢ k₂} →
        Lo k₁ → Lo k₂ → i ≅ᴵ i′ → a ≅ˢ b → ψᵉ′ S z p σ a ≅ˢ ψᵉ′ S′ z′ p′ σ′ b
repᴷ-≈ : ∀ {S S′ : Stk} → S ≈ˢ S′ → ∀ {k₁ k₂} {s : ∀ {ℓ} → zero <ᴵ ℓ → Simᴵ k₁ ℓ} {s′ : ∀ {ℓ} → zero <ᴵ ℓ → Simᴵ k₂ ℓ}
         {a : Ordˢ k₁} {b : Ordˢ k₂} → Lo k₁ → Lo k₂ → a ≅ˢ b → ∀ m → repᴷ S s a m ≈ˢ repᴷ S′ s′ b m

ψᵉ′-≅ H {z = z} {p = p} {z′ = z′} {p′ = p′} l₁ l₂ ei z≅ = ▹Ω̂-≈ H z p z′ p′ ei
ψᵉ′-≅ H {z = z} {p = p} {z′ = z′} {p′ = p′} lo0 lo0 ei (s≅ e) = l≅ (λ m → repᴷ-≈ H lo0 lo0 e m z p z′ p′ ei)
ψᵉ′-≅ H {z = z} {p = p} {z′ = z′} {p′ = p′} lo0 lo1 ei (s≅ e) = l≅ (λ m → repᴷ-≈ H lo0 lo1 e m z p z′ p′ ei)
ψᵉ′-≅ H {z = z} {p = p} {z′ = z′} {p′ = p′} lo1 lo0 ei (s≅ e) = l≅ (λ m → repᴷ-≈ H lo1 lo0 e m z p z′ p′ ei)
ψᵉ′-≅ H {z = z} {p = p} {z′ = z′} {p′ = p′} lo1 lo1 ei (s≅ e) = l≅ (λ m → repᴷ-≈ H lo1 lo1 e m z p z′ p′ ei)
ψᵉ′-≅ H l₁ l₂ ei (l≅ h) = l≅ (λ n → ψᵉ′-≅ H l₁ l₂ ei (h n))
ψᵉ′-≅ H lo1 l₂ ei (upˡ {r = zero} e) = ψᵉ′-≅ H lo0 l₂ ei e
ψᵉ′-≅ H l₁ lo1 ei (upʳ {r = zero} e) = ψᵉ′-≅ H l₁ lo0 ei e
ψᵉ′-≅ H lo0 lo0 ei (ŝ≅ k ec et eg) =
  ĉ≅ ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη)) (ψᵉ′-≅ H lo0 lo0 ei et) (λ η e η′ e′ eη → ψᵉ′-≅ H lo0 lo0 ei (eg η e η′ e′ eη))
ψᵉ′-≅ H lo0 lo1 ei (ŝ≅ k ec et eg) = ⊥-elim (tf k)
ψᵉ′-≅ H lo1 lo0 ei (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
ψᵉ′-≅ H lo1 lo1 ei (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ ei) ec (ψᵉ′-≅ H lo1 lo1 ei et) (λ η e η′ e′ eη → ψᵉ′-≅ H lo1 lo1 ei (eg η e η′ e′ eη))
ψᵉ′-≅ H l₁ l₂ ei (ĉ≅ ec dt dg eo eO) = ĉ≅ ec dt dg (ψᵉ′-≅ H l₁ l₂ ei eo) (λ η e η′ e′ eη → ψᵉ′-≅ H l₁ l₂ ei (eO η e η′ e′ eη))
ψᵉ′-≅ {S = S} {S′ = S′} H {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} l₁ l₂ ei (lᵢ≅ {p = q} {q = q′} {f = f} {g = g} e h) =
  liE {S = S} {S′ = S′} {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} {q = q} {q′ = q′} {f = f} {g = g} ei e
      (λ x y d → ψᵉ′-≅ H {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} l₁ l₂ ei (h x y d))
      (λ x y d → ψᵉ′-≅ H {z = z} {p = σ q} {σ = σ} {z′ = z′} {p′ = σ′ q′} {σ′ = σ′} l₁ l₂ e (h x y d))

repᴷ-≈ H l₁ l₂ e zero    = H
repᴷ-≈ H l₁ l₂ e (suc m) z p z′ p′ ei = ψᵉ′-≅ (repᴷ-≈ H l₁ l₂ e m) l₁ l₂ ei e

▹-≈ : ∀ {S S′ : Stk} → S ≈ˢ S′ → ∀ {k₁ k₂} {s : ∀ {ℓ} → zero <ᴵ ℓ → Simᴵ k₁ ℓ} {s′ : ∀ {ℓ} → zero <ᴵ ℓ → Simᴵ k₂ ℓ}
      {a : Ordˢ k₁} {b : Ordˢ k₂} → Lo k₁ → Lo k₂ → a ≅ˢ b → (S ▹[ s ] a) ≈ˢ (S′ ▹[ s′ ] b)
▹-≈ H l₁ l₂ e z p z′ p′ ei = ψᵉ′-≅ H l₁ l₂ ei e
```

**读法.** 停机一次通过: `ψᵉ′-≅` 对互模拟推导结构递归, `repᴷ-≈ (suc m)` 调 `ψᵉ′-≅` 于同一个 `e` (它是 `s≅ e` 的真子项) 与 `repᴷ-≈ m`. `upˡ {r = self m}` 与 `Lo` 冲突 (极限层), 覆盖检查器自动排除; `Lo` 两侧不同的 `ŝ≅` 由种类字段 `k` 排除.

**折叠方程.** `chainE`/`fold1E`/`pen1E`: OmegaExpBase 的 `chainS`/`fold1S`/`pen1S` 的 `ψᵉ′` 版, 证明逐字.

```agda
chainE : ∀ (S : Stk) {j k ℓ} (z : zero <ᴵ ℓ) (σ : Simᴵ k ℓ) (q : j <ᴵ k) (f : Uˢ j (<→◃ q) → Ordˢ k) → ℕ → Ordˢ j
chainE S {j} z σ q f = iter (λ x → ψᵉ′ S z (σ q) σ (f (intoˢ (<→◃ q) x))) (Ωˢ j)

fold1E : ∀ {S : Stk} {i k ℓ j} {z : zero <ᴵ ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
         (i ≺ᴵ j) ⊎ (i ≅ᴵ j) →
         ψᵉ′ S z p σ (Ord₊ˢ.limᵢ q f) ≡ Ord₊ˢ.lim (λ m → ψᵉ′ S z p σ (f (intoˢ (<→◃ q) (chainE S z σ q f m))))
fold1E {p = p} {σ = σ} {q = q} h with <ᴵ-dec (σ q) p
... | injᵃ s = ⊥-elim (clash s h)
... | injᵇ _ = refl
... | injᶜ _ = refl

pen1E : ∀ {S : Stk} {i k ℓ j N} {z : zero <ᴵ ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
        j ≅ᴵ N → N ≺ᴵ i →
        Σ Ordᴵ λ j′ → Σ (j ≅ᴵ j′) λ e → Σ (j′ <ᴵ i) λ r →
        ψᵉ′ S z p σ (Ord₊ˢ.limᵢ q f) ≡ Ord₊ˢ.limᵢ r (λ y → ψᵉ′ S z p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) y)))))
pen1E {p = p} {σ = σ} {q = q} ej νi with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = _ , e , r , refl
... | injᵇ s = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ (≺ᴵ-trans νi s) ej))
... | injᶜ c = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ νi (≅ᴵ-trans (≅ᴵ-sym c) ej)))
```

**记号: 指数作尾巴.** 前缀之后的尾巴是单个主项 $\psi_\Omega(\eta)$, `ψΩ η = ψ_Ω(η) ∷ []`. 它的共尾度与基本列由 $\eta$ 的决定: $\eta$ 后继或极限时 $\omega$ (`cE₁`/`cEω`, $[m]$ 是 $\psi_\Omega(\eta-1)\cdot m$ 或 $\psi_\Omega(\eta[m])$, 经 `ωW` 带上前缀); $\eta$ 的共尾度 $\Omega_{\nu+1}$ ($\nu$ 带 `Idx`, 可数) 时 $\nu+1<\Omega$ (`cmpΩ`, 即 SystemOmega 的 `cmp-CΩ`), $\psi_\Omega$ 穿透: 共尾度不变 (`cofΩc`), $[\theta]$ 进入参数 (`fsTΩ`).

```agda
ψΩ : T → T
ψΩ η = ψᵗ Ωᵗ η ∷ []

cmpΩ : ∀ {ν} → Idx ν → cmpᵀ (sucT ν) Ωᵗ ≡ lt
cmpΩ I = cmp-CΩ (Ctbl-suc (Idx-Ctbl I)) []

cofΩc : ∀ {η ν} → cof η ≡ cΩ ν → Idx ν → cof (ψΩ η) ≡ cΩ ν
cofΩc {η = []} () I
cofΩc {η = y ∷ ys} {ν} c I = trans (cong (cofA Ωᵗ) c) (cofP {w = Ωᵗ} {ν = ν} (inj₁ (cmpΩ I)))

fsTΩ : ∀ {η ν} → cof η ≡ cΩ ν → Idx ν → ∀ θ → fsT (ψΩ η) θ ≡ ψΩ (fsT η θ)
fsTΩ {η = []} () I θ
fsTΩ {η = y ∷ ys} {ν} c I θ = fsT₊-pen′ Ωᵗ (y ∷ ys) ν (cof (y ∷ ys)) c (inj₁ (cmpΩ I)) θ

cE₁ : ∀ w ps {y ys} → cof (y ∷ ys) ≡ c1 → cof (πw w ps (ψΩ (y ∷ ys))) ≡ cω
cE₁ w ps {y} {ys} c = trans (cofW w ps (ψᵗ Ωᵗ (y ∷ ys)) []) (cong (cofA w) (cong (cofA Ωᵗ) c))

fE₁ : ∀ w ps {y ys} (c : cof (y ∷ ys) ≡ c1) m →
      fsn (πw w ps (ψΩ (y ∷ ys))) m ≡ πw w ps (replicate m (ψᵗ Ωᵗ (pred (y ∷ ys))))
fE₁ w ps {y} {ys} c m = trans (ωW w ps (ψᵗ Ωᵗ (y ∷ ys)) [] (cong (cofA Ωᵗ) c) m) (cong (πw w ps) (fs-rep Ωᵗ y ys c m))

cEω : ∀ w ps {y ys} → cof (y ∷ ys) ≡ cω → cof (πw w ps (ψΩ (y ∷ ys))) ≡ cω
cEω w ps {y} {ys} c = trans (cofW w ps (ψᵗ Ωᵗ (y ∷ ys)) []) (cong (cofA w) (cong (cofA Ωᵗ) c))

fEω : ∀ w ps {y ys} (c : cof (y ∷ ys) ≡ cω) n → fsn (πw w ps (ψΩ (y ∷ ys))) n ≡ πw w ps (ψΩ (fsn (y ∷ ys) n))
fEω w ps {y} {ys} c n = trans (ωW w ps (ψᵗ Ωᵗ (y ∷ ys)) [] (cong (cofA Ωᵗ) c) n) (cong (πw w ps) (fs-ω Ωᵗ y ys c n))

nfγ′ : ∀ ps {y ys} → NF₁ (πw [] ps (y ∷ ys)) → (c : cof (y ∷ ys) ≡ cΩ []) → ∀ m →
       NF₁ (πw [] ps (fsT (y ∷ ys) (γW ps (y ∷ ys) [] m)))
nfγ′ ps {y} {ys} nu c m = subst NF₁ (gtW [] ps y ys [] c refl m) (NF₁-fsn nu (trans (cofW [] ps y ys) (cong (cofA []) c)) m)
```

## §5 三个通用的行: 穿透/折叠、第 0 层的链、闭包的链证书

`giPreE`: OmegaExpBase `PreW.giPreS` 的 `ψᵉ′` 版 (逐字, 只换折叠方程); 它不用弹栈假设, 所以只以栈与前缀为参数. `liLabE`: `Pre0.liLabS` 的 `ψᵉ′` 版, 链原子的自互模拟用 `ψᵉ′-≅` (要 `Lo k`). `ŝChainG`: `Pre0.ŝChainS` 对任意两棵树 $A$、$B$ 的版本 (证明不看树), 支配用 `domS`.

```agda
module GiE (S : Stk) (ps : T) where

  giPreE : ∀ {k ℓ i w ν j y ys} {z : zero <ᴵ ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
           (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
           (rec : ∀ η (x : Ordˢ j) → LabL x η → LabL₊ i Ll (ψᵉ′ S z p σ (f (intoˢ (<→◃ q) x))) (πw w ps (fsT (y ∷ ys) η))) →
           (recC : kd j ≡ false → ∀ η (x : Ordˢ j) → LabL x η →
                   LabL₊ j Ll (ψᵉ′ S z (σ q) σ (f (intoˢ (<→◃ q) x))) (πw ν ps (fsT (y ∷ ys) η))) →
           LabL₊ i Ll (ψᵉ′ S z p σ (Ord₊ˢ.limᵢ q f)) (πw w ps (y ∷ ys))
  giPreE {i = i} {w = w} {ν = ν} {j = j} {y = y} {ys = ys} {z = z} {p = p} {σ = σ} {q = q} {f = f} Iw ei ki c Iν ej rec recC =
    go (cmpᵀ (sucT ν) w) refl
    where
    pen : Pen (cmpᵀ (sucT ν) w) → LabL₊ i Ll (ψᵉ′ S z p σ (Ord₊ˢ.limᵢ q f)) (πw w ps (y ∷ ys))
    pen pn with pen1E {S = S} {z = z} {p = p} {σ = σ} {q = q} {f = f} (≅ᴵ-refl j)
                      (≺ᴵ-respʳ (≺ᴵ-respˡ ej (Ilt Iν Iw (pen→< ν w pn))) (≅ᴵ-sym ei))
    ... | j′ , e , r , eqn =
      subst (λ W → LabL₊ i Ll W (πw w ps (y ∷ ys))) (sym eqn)
            (gi cofE Iν (≅ᴵ-trans (≅ᴵ-sym e) ej)
                (λ η x l → subst (λ v → LabL₊ i Ll (ψᵉ′ S z p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e v)))) (fsT (πw w ps (y ∷ ys)) η))
                                 (sym (out-intoˢ (<→◃ r) x))
                                 (subst (LabL₊ i Ll _) (sym (penW w ps y ys ν c pn η))
                                        (rec η (tr⁻ˢ e x) (LabL-tr⁻ e (Ll→ (<→◃ r) l))))))
      where
      cofE : cof (πw w ps (y ∷ ys)) ≡ cΩ ν
      cofE = trans (cofW w ps y ys) (trans (cong (cofA w) c) (cofP pn))
    fold : cmpᵀ (sucT ν) w ≡ gt → LabL₊ i Ll (ψᵉ′ S z p σ (Ord₊ˢ.limᵢ q f)) (πw w ps (y ∷ ys))
    fold em =
      subst (λ W → LabL₊ i Ll W (πw w ps (y ∷ ys))) (sym (fold1E {S = S} {z = z} {p = p} {σ = σ} {q = q} {f = f} ij))
            (gl (trans (cofW w ps y ys) (trans (cong (cofA w) c) (cong (E.cofψ₊ w ν) em)))
                (λ m → subst (LabL₊ i Ll _) (sym (gtW w ps y ys ν c em m)) (rec _ _ (chainL m))))
      where
      gev : (lvI Iw ≺ᴵ lvI Iν) ⊎ (lvI Iw ≅ᴵ lvI Iν)
      gev with gt→≤ ν w em
      ... | inj₁ pw   = inj₁ (Ilt Iw Iν pw)
      ... | inj₂ refl = inj₂ (Ieq Iw Iν)
      ij : (i ≺ᴵ j) ⊎ (i ≅ᴵ j)
      ij with gev
      ... | inj₁ s  = inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ ei s) (≅ᴵ-sym ej))
      ... | inj₂ c′ = inj₂ (≅ᴵ-trans ei (≅ᴵ-trans c′ (≅ᴵ-sym ej)))
      kj : kd j ≡ false
      kj = trans (kd-≅ ej) (kdI′ Iν (gtν em (ne-w Iw ei ki)))
      chainL : ∀ m → LabL (chainE S z σ q f m) (γW ps (y ∷ ys) ν m)
      chainL zero    = LabL-Ω (proj₁ Iν) (proj₁ (proj₂ Iν)) (proj₁ (proj₂ (proj₂ Iν))) (proj₂ (proj₂ (proj₂ Iν))) ej
      chainL (suc m) = frL₊ kj (recC kj _ _ (chainL m))
    go : ∀ m → cmpᵀ (sucT ν) w ≡ m → LabL₊ i Ll (ψᵉ′ S z p σ (Ord₊ˢ.limᵢ q f)) (πw w ps (y ∷ ys))
    go lt em = pen (inj₁ em)
    go eq em = pen (inj₂ em)
    go gt em = fold em

module LiE (S : Stk) (ps : T) (HR : S ≈ˢ S) where

  liLabE : ∀ {L k} {z p : zero <ᴵ L} {σ : Simᴵ k L} {q : zero <ᴵ k} {f : Uˢ zero (<→◃ q) → Ordˢ k} {y ys} →
           Lo k → cof (y ∷ ys) ≡ cΩ [] → Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → NF₁ (πw [] ps (y ∷ ys)) →
           (rec : ∀ (p′ : zero <ᴵ L) θ (x : Ordˢ zero) → Atomᴸ x θ → f (intoˢ (<→◃ q) x) ≅ˢ f (intoˢ (<→◃ q) x) →
                  NF₁ (πw [] ps (fsT (y ∷ ys) θ)) →
                  Σ (Goodᴸ (toZ (ψᵉ′ S z p′ σ (f (intoˢ (<→◃ q) x))))) λ G → Lab (forceᴸ _ G) (πw [] ps (fsT (y ∷ ys) θ))) →
           Σ (Goodᴸ (toZ (ψᵉ′ S z p σ (Ord₊ˢ.limᵢ q f)))) λ G → Lab (forceᴸ _ G) (πw [] ps (y ∷ ys))
  liLabE {z = z} {p = p} {σ = σ} {q = q} {f = f} {y = y} {ys = ys} lk c ex nu rec =
    subst (λ W → Σ (Goodᴸ (toZ W)) λ G → Lab (forceᴸ _ G) (πw [] ps (y ∷ ys))) (sym eqf)
          (limᴸ nu (trans (cofW [] ps y ys) (cong (cofA []) c)) (λ m → proj₁ (outp m))
                (λ m → subst (Lab _) (sym (gtW [] ps y ys [] c refl m)) (proj₂ (outp m))))
    where
    eqf = fold1E {S = S} {z = z} {p = p} {σ = σ} {q = q} {f = f} (inj₂ z≅)
    atm : ∀ m → Atomᴸ (chainE S z σ q f m) (γW ps (y ∷ ys) [] m)
    atm zero    = Ωˢ-refl zero , gs gz , l1 refl (s≅ z≅) (l0 refl z≅)
    atm (suc m) = ψᵉ′-≅ HR {z = z} {p = σ q} {σ = σ} {z′ = z} {p′ = σ q} {σ′ = σ} lk lk z≅ (i-respˢ ex (proj₁ (atm m))) ,
                  rec (σ q) _ _ (atm m) (i-respˢ ex (proj₁ (atm m))) (nfγ′ ps nu c m)
    outp : ∀ m → Σ (Goodᴸ (toZ (ψᵉ′ S z p σ (f (intoˢ (<→◃ q) (chainE S z σ q f m)))))) λ G →
                Lab (forceᴸ _ G) (πw [] ps (fsT (y ∷ ys) (γW ps (y ∷ ys) [] m)))
    outp m = rec p _ _ (atm m) (i-respˢ ex (proj₁ (atm m))) (nfγ′ ps nu c m)

ŝChainG : ∀ {c w} ps {A : Ordˢ zero} {B : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ zero} {y ys} →
          cof (y ∷ ys) ≡ cΩ [] → NF₁ (πw [] ps (y ∷ ys)) → (Iw : Idx w) → c ⊑ᴵ suc (lvI Iw) → (∀ θ → Occ w (fsT (y ∷ ys) θ)) →
          (rec₀ : Σ (Goodᴸ (toZ A)) λ G → Lab (forceᴸ _ G) (γW ps (y ∷ ys) [] 1)) →
          (rec : ∀ m Y (hY : HS Y) → Lab Y (γW ps (y ∷ ys) [] (suc m)) → (e : c ⊑ᴵ toLevel Y hY) →
                 Σ (Goodᴸ (toZ (B (toLevel Y hY) e))) λ G → Lab (forceᴸ _ G) (γW ps (y ∷ ys) [] (suc (suc m)))) →
          Σ (Goodᴸ (ĉᴸ c (toZ A) (λ η e → toZ (B η e)) (toZ A) (λ η e → toZ (B η e)))) λ G →
            Lab (forceᴸ _ G) (πw [] ps (y ∷ ys))
ŝChainG ps {y = y} {ys = ys} c nu Iw bw ow rec₀ rec =
  ĉᴸ-mk nu (trans (cofW [] ps y ys) (cong (cofA []) c)) K (proj₁ rec₀) (subst (Lab _) (sym (gtW [] ps y ys [] c refl 0)) (proj₂ rec₀))
        (λ k → CCᴸ.Gg K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k)))
        (λ k → subst (Lab _) (sym (gtW [] ps y ys [] c refl (suc k)))
                     (CCᴸ.lE K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k))))
  where
  K = ccᴸ (λ m → γW ps (y ∷ ys) [] (suc m)) (proj₁ rec₀) (proj₂ rec₀)
          (domS ps _ Iw bw (ow (natT 1)) (proj₂ rec₀) (nfγ′ ps nu c 0))
          (λ m Y hY lY e → proj₁ (rec m Y hY lY e)) (λ m Y hY lY e → proj₂ (rec m Y hY lY e))
          (λ m Y hY lY e → domS ps _ Iw bw (ow (γW ps (y ∷ ys) [] (suc m))) (proj₂ (rec m Y hY lY e)) (nfγ′ ps nu c (suc m)))
```

**读法.** 三者都不递归: 递归调用作为参数传入 (`rec`/`recC`), 这正是 OmegaKBase §2 记下的停机写法. 对下面的互递归块, 它们是 "行" 的组合子.

## §6 第 0 层指数: `WE₀`/`ZE₀`, `GoodE₀`

OmegaExpBase 的 `GoodE` 把 "指数为 $X$ 的帧" 的三个字段直接写在帧上 (`Sim` 固定为 `σ⊥`). 这里同样的推导拆成两个对**任意** `Sim` 成立的引理: `WE₀` (目标 $w\ne0$ 的 `LabL₊`) 与 `ZE₀` (目标 $0$ 的证书和标签), 都对 `Lab0ᴸ X η` 递归; 结论的标签是 $\psi_w(ps+\psi_\Omega(\eta))$. 之所以要任意 `Sim`: 第 1 层的指数经 `up` 下到第 0 层时, `Sim` 是 `λ q → σ (suc q)`, 不是 `σ⊥`, 而对抽象的 $X$, `ψᵉ′ S z p σ X` 与 `ψᵉ′ S z p σ⊥ X` 不定义性相等 (要函数外延). 情形:

- `lz` ($\eta=0$): `ψᵉ′ … zero` 定义性地是 `(S ▹Ω̂) z p`, 字段取自 `GoodΩ G`.
- `ls`: 第 $m$ 项是 `repᴷ S s₀ Y m`, 由 `repGood₀` (对 $m$ 归纳, 每步 `GoodE₀`) 是好栈.
- `ll`/`lŝ₀`/`lĉ`: 逐项递归; 待计值链的链证书 `K` 原样交给 `gĉ`/`ĉᴸ-mk`.

```agda
WE₀ : ∀ {S : Stk} {ps} → Goodˢ S ps → ∀ {X : Ordˢ zero} {η} → Lab0ᴸ X η → X ≅ˢ X →
      ∀ {i ℓ w} (z : zero <ᴵ ℓ) (p : i <ᴵ ℓ) (σ : Simᴵ zero ℓ) (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
      LabL₊ i Ll (ψᵉ′ S z p σ X) (πw w ps (ψΩ η))
ZE₀ : ∀ {S : Stk} {ps} → Goodˢ S ps → ∀ {X : Ordˢ zero} {η} → Lab0ᴸ X η → X ≅ˢ X →
      ∀ {L} (z p : zero <ᴵ L) (σ : Simᴵ zero L) → NF₁ (πw [] ps (ψΩ η)) →
      Σ (Goodᴸ (toZ (ψᵉ′ S z p σ X))) λ G → Lab (forceᴸ _ G) (πw [] ps (ψΩ η))
repGood₀ : ∀ {S : Stk} {ps} → Goodˢ S ps → ∀ {Y : Ordˢ zero} {θ} → Lab0ᴸ Y θ → Y ≅ˢ Y → ∀ m →
           Goodˢ (repᴷ S s₀ Y m) (ps ++ replicate m (ψᵗ Ωᵗ θ))
GoodE₀ : ∀ {S : Stk} {ps} → Goodˢ S ps → ∀ {X : Ordˢ zero} {η} → Lab0ᴸ X η → X ≅ˢ X → Goodˢ (S ▹[ s₀ ] X) (ps ++ ψᵗ Ωᵗ η ∷ [])

GoodE₀ G l ex = good (λ z p Iw ei ki → WE₀ G l ex z p σ⊥ Iw ei ki) (λ z p nf → ZE₀ G l ex z p σ⊥ nf) (▹-≈ (hR G) lo0 lo0 ex)

repGood₀ {S = S} {ps} G l ey zero    = subst (Goodˢ S) (sym (++-identityʳ ps)) G
repGood₀ {S = S} {ps} G {Y} {θ} l ey (suc m) =
  subst (Goodˢ (repᴷ S s₀ Y (suc m))) (snoc ps m (ψᵗ Ωᵗ θ)) (GoodE₀ (repGood₀ G l ey m) l ey)

WE₀ G {η = []} (lz c) ex z p σ Iw ei ki = hW (GoodΩ G) z p Iw ei ki
WE₀ G {η = y ∷ ys} (lz c) ex z p σ Iw ei ki = ⊥-elim (cof-ne y ys c)
WE₀ G {η = []} (ls () l) ex z p σ Iw ei ki
WE₀ {ps = ps} G {η = y ∷ ys} (ls c l) ex {w = w} z p σ Iw ei ki =
  gl (cE₁ w ps c) (λ m → subst (LabL₊ _ Ll _) (sym (fE₁ w ps c m)) (hW (repGood₀ G l (s-invˢ ex) m) z p Iw ei ki))
WE₀ G {η = []} (ll () h) ex z p σ Iw ei ki
WE₀ {ps = ps} G {η = y ∷ ys} (ll c h) ex {w = w} z p σ Iw ei ki =
  gl (cEω w ps c) (λ n → subst (LabL₊ _ Ll _) (sym (fEω w ps c n)) (WE₀ G (h n) (l-invˢ ex n) z p σ Iw ei ki))
WE₀ G {η = []} (lŝ₀ () K h₀ hk) ex z p σ Iw ei ki
WE₀ {ps = ps} G {η = y ∷ ys} (lŝ₀ c K h₀ hk) ex {w = w} z p σ Iw ei ki =
  gĉ (cEω w ps c) K (subst (LabL₊ _ Ll _) (sym (fEω w ps c 0)) (WE₀ G h₀ (ŝ-refl₀ ex) z p σ Iw ei ki))
     (λ k → subst (LabL₊ _ Ll _) (sym (fEω w ps c (suc k)))
                  (WE₀ G (hk k) (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) z p σ Iw ei ki))
WE₀ G {η = []} (lĉ () K h₀ hk) ex z p σ Iw ei ki
WE₀ {ps = ps} G {η = y ∷ ys} (lĉ c K h₀ hk) ex {w = w} z p σ Iw ei ki =
  gĉ (cEω w ps c) K (subst (LabL₊ _ Ll _) (sym (fEω w ps c 0)) (WE₀ G h₀ (ĉ-refl₀ ex) z p σ Iw ei ki))
     (λ k → subst (LabL₊ _ Ll _) (sym (fEω w ps c (suc k))) (WE₀ G (hk k) (ĉ-reflg ex _ _) z p σ Iw ei ki))

ZE₀ G {η = []} (lz c) ex z p σ nf = h0 (GoodΩ G) z p nf
ZE₀ G {η = y ∷ ys} (lz c) ex z p σ nf = ⊥-elim (cof-ne y ys c)
ZE₀ G {η = []} (ls () l) ex z p σ nf
ZE₀ {ps = ps} G {η = y ∷ ys} (ls c l) ex z p σ nf =
  limᴸ nf (cE₁ [] ps c)
       (λ m → proj₁ (h0 (repGood₀ G l (s-invˢ ex) m) z p (subst NF₁ (fE₁ [] ps c m) (NF₁-fsn nf (cE₁ [] ps c) m))))
       (λ m → subst (Lab _) (sym (fE₁ [] ps c m))
                    (proj₂ (h0 (repGood₀ G l (s-invˢ ex) m) z p (subst NF₁ (fE₁ [] ps c m) (NF₁-fsn nf (cE₁ [] ps c) m)))))
ZE₀ G {η = []} (ll () h) ex z p σ nf
ZE₀ {ps = ps} G {η = y ∷ ys} (ll c h) ex z p σ nf =
  limᴸ nf (cEω [] ps c)
       (λ n → proj₁ (ZE₀ G (h n) (l-invˢ ex n) z p σ (subst NF₁ (fEω [] ps c n) (NF₁-fsn nf (cEω [] ps c) n))))
       (λ n → subst (Lab _) (sym (fEω [] ps c n))
                    (proj₂ (ZE₀ G (h n) (l-invˢ ex n) z p σ (subst NF₁ (fEω [] ps c n) (NF₁-fsn nf (cEω [] ps c) n)))))
ZE₀ G {η = []} (lŝ₀ () K h₀ hk) ex z p σ nf
ZE₀ {ps = ps} G {η = y ∷ ys} (lŝ₀ c K h₀ hk) ex z p σ nf =
  ĉᴸ-mk nf (cEω [] ps c) K
        (proj₁ (ZE₀ G h₀ (ŝ-refl₀ ex) z p σ (nfk 0)))
        (subst (Lab _) (sym (fEω [] ps c 0)) (proj₂ (ZE₀ G h₀ (ŝ-refl₀ ex) z p σ (nfk 0))))
        (λ k → proj₁ (ZE₀ G (hk k) (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) z p σ (nfk (suc k))))
        (λ k → subst (Lab _) (sym (fEω [] ps c (suc k)))
                     (proj₂ (ZE₀ G (hk k) (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) z p σ (nfk (suc k)))))
  where nfk = λ n → subst NF₁ (fEω [] ps c n) (NF₁-fsn nf (cEω [] ps c) n)
ZE₀ G {η = []} (lĉ () K h₀ hk) ex z p σ nf
ZE₀ {ps = ps} G {η = y ∷ ys} (lĉ c K h₀ hk) ex z p σ nf =
  ĉᴸ-mk nf (cEω [] ps c) K
        (proj₁ (ZE₀ G h₀ (ĉ-refl₀ ex) z p σ (nfk 0)))
        (subst (Lab _) (sym (fEω [] ps c 0)) (proj₂ (ZE₀ G h₀ (ĉ-refl₀ ex) z p σ (nfk 0))))
        (λ k → proj₁ (ZE₀ G (hk k) (ĉ-reflg ex _ _) z p σ (nfk (suc k))))
        (λ k → subst (Lab _) (sym (fEω [] ps c (suc k))) (proj₂ (ZE₀ G (hk k) (ĉ-reflg ex _ _) z p σ (nfk (suc k)))))
  where nfk = λ n → subst NF₁ (fEω [] ps c n) (NF₁-fsn nf (cEω [] ps c) n)
```

**读法.** 停机一次通过: `WE₀ (ls c l) → repGood₀ … l … m → GoodE₀ … l → WE₀ … l` 中推导严格下降, `repGood₀ (suc m) → repGood₀ m` 中重数下降. 与 OmegaExpBase `GoodE` 的差别只在 "字段对任意 `Sim`" 与帧 `▹[ s₀ ]` 用新折叠.

## §7 第 1 层指数: `WE₁`/`ZE₁`, `GoodE₁`

对第 1 层的 `LabL₊ (suc zero)` 推导递归; 结论同 §6. 各行:

- `gz`: `GoodΩ G`. `gs`: 第 $m$ 项是 `repᴷ S σ1 Y m`, 由 `repGood₁` 是好栈 (帧 `▹[ σ1 ]`, 本文新增的帧).
- `gl`/`gĉ`: 逐项递归, 链证书原样.
- `gu`: 第 1 层的 `up` 只能是 `up zero x` ($x$ 在第 0 层, 推导是原子), 经 `ψᵉ′` 的 `up` 子句到 §6 (`Sim` 为 `λ q → σ (suc q)`).
- `gi`: 第 1 层的 `limᵢ q f` 只能 $q$ = `zero`, $j=0$. 记号: $\psi_\Omega$ 穿透 (`cofΩc`, `fsTΩ`). 目标 $w\ne0$ 时 `giPreE` 走穿透分支 (折叠分支要 $\mathrm{kd}\,j$ = false, $j=0$ 时空: `λ ()`); 目标 $0$ 时 `liLabE` 折叠成第 0 层的链 (共尾度 $\Omega_1$, $\nu=[]$ 由 `kdI`).
- `gŝ` (第 1 层的闭包 $\hat s\,c\,t_0\,g$, 来自目标 1 的弹栈, 标签共尾度 $\Omega_1$): 目标 $w\ne0$ 时输出仍是带**同一地板** (`Ib`, `bb`) 的闭包, 出现经 `od (OccΣ ps (od _))` 往外包两层 ($\psi_\Omega$ 与 $\psi_w$), 记号 `H1W` 与 `fsTΩ`; 目标 $0$ 时是 `ŝChainG` 的链证书.

```agda
WE₁ : ∀ {S : Stk} {ps} → Goodˢ S ps → ∀ {X : Ordˢ (suc zero)} {η} → LabL₊ (suc zero) Ll X η → X ≅ˢ X →
      ∀ {i ℓ w} (z : zero <ᴵ ℓ) (p : i <ᴵ ℓ) (σ : Simᴵ (suc zero) ℓ) (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
      LabL₊ i Ll (ψᵉ′ S z p σ X) (πw w ps (ψΩ η))
ZE₁ : ∀ {S : Stk} {ps} → Goodˢ S ps → ∀ {X : Ordˢ (suc zero)} {η} → LabL₊ (suc zero) Ll X η → X ≅ˢ X →
      ∀ {L} (z p : zero <ᴵ L) (σ : Simᴵ (suc zero) L) → NF₁ (πw [] ps (ψΩ η)) →
      Σ (Goodᴸ (toZ (ψᵉ′ S z p σ X))) λ G → Lab (forceᴸ _ G) (πw [] ps (ψΩ η))
repGood₁ : ∀ {S : Stk} {ps} → Goodˢ S ps → ∀ {Y : Ordˢ (suc zero)} {θ} → LabL₊ (suc zero) Ll Y θ → Y ≅ˢ Y → ∀ m →
           Goodˢ (repᴷ S σ1 Y m) (ps ++ replicate m (ψᵗ Ωᵗ θ))
GoodE₁ : ∀ {S : Stk} {ps} → Goodˢ S ps → ∀ {X : Ordˢ (suc zero)} {η} → LabL₊ (suc zero) Ll X η → X ≅ˢ X →
         Goodˢ (S ▹[ σ1 ] X) (ps ++ ψᵗ Ωᵗ η ∷ [])

GoodE₁ G d ex = good (λ z p Iw ei ki → WE₁ G d ex z p (σ1 z) Iw ei ki) (λ z p nf → ZE₁ G d ex z p (σ1 z) nf) (▹-≈ (hR G) lo1 lo1 ex)

repGood₁ {S = S} {ps} G d ey zero    = subst (Goodˢ S) (sym (++-identityʳ ps)) G
repGood₁ {S = S} {ps} G {Y} {θ} d ey (suc m) =
  subst (Goodˢ (repᴷ S σ1 Y (suc m))) (snoc ps m (ψᵗ Ωᵗ θ)) (GoodE₁ (repGood₁ G d ey m) d ey)

WE₁ G {η = []} (gz c) ex z p σ Iw ei ki = hW (GoodΩ G) z p Iw ei ki
WE₁ G {η = y ∷ ys} (gz c) ex z p σ Iw ei ki = ⊥-elim (cof-ne y ys c)
WE₁ G {η = []} (gs () d) ex z p σ Iw ei ki
WE₁ {ps = ps} G {η = y ∷ ys} (gs c d) ex {w = w} z p σ Iw ei ki =
  gl (cE₁ w ps c) (λ m → subst (LabL₊ _ Ll _) (sym (fE₁ w ps c m)) (hW (repGood₁ G d (s-invˢ ex) m) z p Iw ei ki))
WE₁ G {η = []} (gl () h) ex z p σ Iw ei ki
WE₁ {ps = ps} G {η = y ∷ ys} (gl c h) ex {w = w} z p σ Iw ei ki =
  gl (cEω w ps c) (λ n → subst (LabL₊ _ Ll _) (sym (fEω w ps c n)) (WE₁ G (h n) (l-invˢ ex n) z p σ Iw ei ki))
WE₁ G (gu {r = zero} at) ex z p σ Iw ei ki = WE₀ G (atomL at) (proj₁ at) z p (λ q → σ (suc q)) Iw ei ki
WE₁ {S = S} {ps} G {η = η} (gi {q = zero} {f = f} c I ej h) ex {w = w} z p σ Iw ei ki =
  GiE.giPreE S ps {z = z} {p = p} {σ = σ} {q = zero} {f = f} Iw ei ki (cofΩc c I) I ej
    (λ θ x l → subst (LabL₊ _ Ll _) (cong (πw w ps) (sym (fsTΩ c I θ)))
                     (WE₁ G (h θ x l) (i-respˢ ex (proj₁ l)) z p σ Iw ei ki))
    (λ ())
WE₁ G (gi {q = suc ()} c I ej h) ex z p σ Iw ei ki
WE₁ G {η = []} (gĉ () K h₀ hk) ex z p σ Iw ei ki
WE₁ {ps = ps} G {η = y ∷ ys} (gĉ c K h₀ hk) ex {w = w} z p σ Iw ei ki =
  gĉ (cEω w ps c) K (subst (LabL₊ _ Ll _) (sym (fEω w ps c 0)) (WE₁ G h₀ (ĉ-refl₀ ex) z p σ Iw ei ki))
     (λ k → subst (LabL₊ _ Ll _) (sym (fEω w ps c (suc k))) (WE₁ G (hk k) (ĉ-reflg ex _ _) z p σ Iw ei ki))
WE₁ G {η = η} (gŝ kk c Ib bb ob h₀ hg) ex {w = []} z p σ Iw ei ki = ⊥-elim (ne-w Iw ei ki refl)
WE₁ {ps = ps} G {η = η} (gŝ kk c Ib bb ob h₀ hg) ex {w = x ∷ xs} z p σ Iw ei ki =
  gŝ ki (trans (cofW (x ∷ xs) ps (ψᵗ Ωᵗ η) []) (trans (cong (cofA (x ∷ xs)) (cofΩc c I0)) (H1-pen x xs))) Ib bb
     (λ θ → subst (Occ _) (sym (fsTw θ)) (od (OccΣ ps (od (ob θ)))))
     (subst (LabL₊ _ Ll _) (sym (fsTw (natT 1))) (WE₁ G h₀ (ŝ-refl₀ ex) z p σ Iw ei ki))
     (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (fsTw θ))
                                  (WE₁ G (hg θ Y hY lY nθ lt e) (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) z p σ Iw ei ki))
  where
  fsTw : ∀ θ → fsT (πw (x ∷ xs) ps (ψΩ η)) θ ≡ πw (x ∷ xs) ps (ψΩ (fsT η θ))
  fsTw θ = trans (H1W x xs ps (ψᵗ Ωᵗ η) [] (cofΩc c I0) θ) (cong (πw (x ∷ xs) ps) (fsTΩ c I0 θ))

ZE₁ G {η = []} (gz c) ex z p σ nf = h0 (GoodΩ G) z p nf
ZE₁ G {η = y ∷ ys} (gz c) ex z p σ nf = ⊥-elim (cof-ne y ys c)
ZE₁ G {η = []} (gs () d) ex z p σ nf
ZE₁ {ps = ps} G {η = y ∷ ys} (gs c d) ex z p σ nf =
  limᴸ nf (cE₁ [] ps c)
       (λ m → proj₁ (h0 (repGood₁ G d (s-invˢ ex) m) z p (subst NF₁ (fE₁ [] ps c m) (NF₁-fsn nf (cE₁ [] ps c) m))))
       (λ m → subst (Lab _) (sym (fE₁ [] ps c m))
                    (proj₂ (h0 (repGood₁ G d (s-invˢ ex) m) z p (subst NF₁ (fE₁ [] ps c m) (NF₁-fsn nf (cE₁ [] ps c) m)))))
ZE₁ G {η = []} (gl () h) ex z p σ nf
ZE₁ {ps = ps} G {η = y ∷ ys} (gl c h) ex z p σ nf =
  limᴸ nf (cEω [] ps c)
       (λ n → proj₁ (ZE₁ G (h n) (l-invˢ ex n) z p σ (subst NF₁ (fEω [] ps c n) (NF₁-fsn nf (cEω [] ps c) n))))
       (λ n → subst (Lab _) (sym (fEω [] ps c n))
                    (proj₂ (ZE₁ G (h n) (l-invˢ ex n) z p σ (subst NF₁ (fEω [] ps c n) (NF₁-fsn nf (cEω [] ps c) n)))))
ZE₁ G (gu {r = zero} at) ex z p σ nf = ZE₀ G (atomL at) (proj₁ at) z p (λ q → σ (suc q)) nf
ZE₁ {S = S} {ps} G {η = η} (gi {q = zero} {f = f} c I ej h) ex z p σ nf =
  LiE.liLabE S ps (hR G) {z = z} {p = p} {σ = σ} {q = zero} {f = f} lo1 (cofΩc c₀ I0) ex nf
    (λ p′ θ x at br nf′ →
       subst (λ t → Σ (Goodᴸ (toZ (ψᵉ′ S z p′ σ (f x)))) λ G′ → Lab (forceᴸ _ G′) (πw [] ps t)) (sym (fsTΩ c₀ I0 θ))
             (ZE₁ G (h θ x at) br z p′ σ (subst (λ t → NF₁ (πw [] ps t)) (fsTΩ c₀ I0 θ) nf′)))
  where
  c₀ : cof η ≡ cΩ []
  c₀ = trans c (cong cΩ (kdI I (sym (kd-≅ ej))))
ZE₁ G (gi {q = suc ()} c I ej h) ex z p σ nf
ZE₁ G {η = []} (gĉ () K h₀ hk) ex z p σ nf
ZE₁ {ps = ps} G {η = y ∷ ys} (gĉ c K h₀ hk) ex z p σ nf =
  ĉᴸ-mk nf (cEω [] ps c) K
        (proj₁ (ZE₁ G h₀ (ĉ-refl₀ ex) z p σ (nfk 0)))
        (subst (Lab _) (sym (fEω [] ps c 0)) (proj₂ (ZE₁ G h₀ (ĉ-refl₀ ex) z p σ (nfk 0))))
        (λ k → proj₁ (ZE₁ G (hk k) (ĉ-reflg ex _ _) z p σ (nfk (suc k))))
        (λ k → subst (Lab _) (sym (fEω [] ps c (suc k))) (proj₂ (ZE₁ G (hk k) (ĉ-reflg ex _ _) z p σ (nfk (suc k)))))
  where nfk = λ n → subst NF₁ (fEω [] ps c n) (NF₁-fsn nf (cEω [] ps c) n)
ZE₁ {S = S} {ps} G {η = η} (gŝ kk c Ib bb ob h₀ hg) ex z p σ nf =
  ŝChainG ps (cofΩc c I0) nf Ib bb (λ θ → subst (Occ _) (sym (fsTΩ c I0 θ)) (od (ob θ)))
          (subst (λ t → Σ (Goodᴸ _) λ G′ → Lab (forceᴸ _ G′) (πw [] ps t)) (sym (fsTΩ c I0 (natT 1)))
                 (ZE₁ G h₀ (ŝ-refl₀ ex) z p σ (subst (λ t → NF₁ (πw [] ps t)) (fsTΩ c I0 (natT 1)) (nfγ′ ps nf (cofΩc c I0) 0))))
          (λ m Y hY lY e →
             subst (λ t → Σ (Goodᴸ _) λ G′ → Lab (forceᴸ _ G′) (πw [] ps t)) (sym (fsTΩ c I0 _))
                   (ZE₁ G (hg _ Y hY lY (nfγ′ ps nf (cofΩc c I0) m) (1<γ ps (ψᵗ Ωᵗ η) [] (cofΩc c I0) m) e)
                        (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) z p σ
                        (subst (λ t → NF₁ (πw [] ps t)) (fsTΩ c I0 _) (nfγ′ ps nf (cofΩc c I0) (suc m)))))
```

**读法.** 停机一次通过; 互递归 `WE₁ (gs c d) → repGood₁ … d … m → GoodE₁ … d → WE₁ … d` 与 §6 同形, 推导严格下降; `gu` 行降到 §6 (那是更早的互递归块, 不回到本块). 第 1 层的 `gi` 行只有 $j=0$ 一种, 所以本块不需要 OmegaExpBase `Pre0` 的 `foldLabS` (那是 $j\ne0$ 的折叠, 链点在第 $j$ 层; §8 的第 2 层指数 $\Omega_2$ 才用到它).

## §8 对比表

| | OmegaExpBase | 本文 |
|---|---|---|
| 指数折叠 | `ψᵉ` | `ψᵉ′` (复制; 第 1 层后继真, 第 $\ge2$ 层占位改为 $0$) |
| 帧 | `▹ω X` (第 0 层, `σ⊥`), `▹Ω̂`, `▹Ω̂²` | `▹[ s ] X` (第 $k\le1$ 层, `s₀`/`σ1`), `▹Ω̂` (原样), `▹Ω̂²′` |
| 栈类型 | `Stk` | `Stk` (不变; 地板不够, 见 §1) |
| 互模拟 | `ψᵉ0-≅`/`rep-≈` | `ψᵉ′-≅`/`repᴷ-≈` (第 $\le1$ 层, `Lo`), `liE` |
| 目标 $w\ne0$ 的带前缀引理 | `PreW.PreS₊` (尾巴) | `WE₀` (第 0 层指数), `WE₁` (第 1 层指数), 行组合子 `giPreE` |
| 目标 $0$ | `Pre0.Pre0S₊` (尾巴) | `ZE₀`, `ZE₁`, 行组合子 `liLabE`, `ŝChainG` |
| 好栈 | `Good∅`, `GoodΩ`, `GoodE` | 原样导入 `Good∅`/`GoodΩ`; 新增 `GoodE₀`, `GoodE₁` |
| `Goodᴸ`/`gc`/`forceᴸ`/`limᴸ`/`ĉᴸ-mk`/`LabL`/`gŝ` 地板/`domS` | 原样 | 原样 |
| 低目标 | 未定 | **出现**: `low-walk`/`low-term`/`low-pop` (`refl`), `low-tree`/`low-unlab`, `noSim21` |

## §9 结论与边界

**任务 1 (低目标) 的答案.** 出现. 精确陈述: 从 $t_{\Omega2}$ 出发的 $\omega$-路径 `pathLow ++ [2,0,0]` 到达 $\psi_0(\psi_\Omega(\Omega_2+1))$, 那里目标 $0$, 指数是第 2 层的后继, $0<2-1$; 其后 $[2,0,0,1]$ 在第 2 层帧之上弹出 $\hat\Omega$. 产生方式不是穿透, 而是 "第 $k$ 层的和 $a+\Omega_{j}$ 在目标 $<j$ 处被折叠访问, 一路折到 $\Omega_0=1$ 落进末项". 所以 "穿透产生的帧只需地板" 的设计不够; 要非紧的闭包 (OmegaSq §3).

**任务 2.** `ψᵉ′`: 第 0 层后继 `lim (repᴷ S s₀ Y ·)`, 第 1 层后继 `lim (repᴷ S σ1 Y ·)`, 第 $\ge2$ 层占位 $0$; 栈类型不变 (任务 1 说明地板不足以覆盖已出现的情形, 故未引入). 旧定理不受影响: 旧文件未改, 新旧折叠在第 0 层指数上 $\cong$ (OmegaSq `Tη-agree`), $\psi_0(\Omega_\Omega\cdot\Omega)$ 的标签由新引理重得且 $\cong$ (`TΩ2-0-agree`).

**任务 3.** `PreW`/`Pre0`/`GoodE` 移植到第 0、1 层的指数: `WE₀`/`ZE₀`/`GoodE₀` (对任意 `Sim`), `WE₁`/`ZE₁`/`GoodE₁`. `gŝ` 地板与 `domS` 不变 (`ŝChainG` 原样用 `domS`; `WE₁` 的 `gŝ` 输出保留输入的地板). 第 $\ge2$ 层未移植: 第 2 层的后继在 $t_{\Omega2}$ 中出现于低目标处, 紧界下没有正确的帧.

**边界.** 互模拟与好栈只到第 1 层的指数; 第 2 层只在 OmegaSq 的 `ZΩ₂` 里以 "`limᵢ` 折叠到第 1 层" 的形式出现. 不改 `src/`、`archive/` 与已有的 Align 文件, README 未改.
