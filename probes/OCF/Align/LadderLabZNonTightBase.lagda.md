> **机械克隆, 验收用.** 由 `ScafLadderZNonTightBase` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.

> **机械克隆.** 由 `NonTightBase` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 非紧闭包: 带帧层地板的栈、非紧弹栈与第 $\ge2$ 层指数帧

> 接 [OmegaSqBase](OmegaSqBase.lagda.md) 与 [OmegaSq](OmegaSq.lagda.md). 本文是 [NonTight](NonTight.lagda.md) 的前半: 任务 1–3 (栈类型带地板、非紧闭包、第 $\ge2$ 层指数子句与它们的带前缀引理). 决定性检验 (`TΩ2-label` 的状态) 在 NonTight.
>
> 结论先说:
>
> 1. **栈类型带地板 (§1).** 地板是一个记录 `Flr` = $(F, B, \iota_B : B<^\mathsf I F, \iota_z : 0<^\mathsf I F, F\sqsubseteq^\mathsf I B+1)$: $B$ 是字面的帧层号 (语义地板), $F$ 是 "字面上装着 $B$ 的、语义上 $=B+1$ 的层号", 栈类型 `Stkᶠ φ` 要求的帧证据是 `Simᴵ (Fᶠ φ) ℓ` (而不是 OmegaExpBase 的 `zero <ᴵ ℓ`). 初始地板 `flr₁` $=(1,0)$, 此时 `Simᴵ 1 ℓ` 与旧的 $0<^\mathsf I\ell$ 等价, 所以没有高层帧的栈就是旧栈. 第 0、1 层指数帧 (`▹[ σ⊥ ∣ … ]`, `▹[ σ1 … ∣ … ]`) 与 $\hat\Omega$、$\hat\Omega^2$ 帧不动地板; 第 $k$ 层后继指数 ($k=K'+1$, $K'\ge1$; 或 $k$ 为极限且带字面把手) 用 `raise` 把地板提到 $\max(B,K)$, 其中 $K$ 是 $k-1$ (或极限 $k$ 本身). 提升用有界三歧性 `<ᴵ-dec` 比较 $K$ 与 $B$ (二者都字面地 $<^\mathsf I\ell$), 新的 $F$ 是 `Mlev` 形的两项极限, 字面装着旧的 $F$ 与 $K+1$.
> 2. **非紧闭包 (§2).** 弹出 $\hat\Omega$ 时比较目标 $i$ 与地板 $B$ (同样字面地 $<^\mathsf I\ell$): $B\preceq i$ 时界 $c=i+1$ (与紧界同), $i\prec B$ 时界 $c=F\ (\cong B+1)$; 第 0 点的环境层号是 `Mlev`$\,[\cdot,\cdot]$ (字面装着 $i$ 与 $F$ 的子项), 分支 $\eta$ 处是三项极限 `Mlev3`$\,[\cdot,\cdot,\eta]$. 这就是 "界与第 0 点环境取 $\max(i,F)+1$". `▹Ω̂²ᶠ` 同式.
> 3. **`noSim21` 的阻碍消失 (§3, `refl`).** OmegaSqBase 的 `lowˢ` 在新折叠下: $[2,0,0]$ (指数 $\Omega_2+1$, 第 2 层后继) 不再是占位 $0$ 而是真的极限 (`kl`); 其后的 $\hat\Omega$ 弹出 (OmegaSqBase 的 `low-pop`) 是界为 `Mlev 1 2 _` ($\cong2$) 的非紧闭包, 第 0 点在含 $1$ 的环境层号上计算第 2 层帧, 帧的折叠走到第 1 层的链 (`kl`). 极限层的类比 $\psi_0(\psi_\Omega(\Omega_\omega+1))$ 同样是真极限, 它上面的弹栈界为 `Mlev 1 (ω+1) _`.
> 4. **标签侧 (§4–§9).** 互模拟、PreW/Pre0、$\hat\Omega$ 好栈都移植到 `Stkᶠ` (证明逐字, 只换帧证据的类型); 好栈记录多一个**地板见证** `FW φ ps`: $B=0$, 或某个带 `Idx` 的下标 $w$ 出现在前缀 `ps` 中且 $B\preceq\mathtt{lvl}\,w$. 非紧闭包的支配 (`d₀`/`dE` 与 `gŝ` 行的界) 由 `domP` (前缀中的出现 + `occ<` + `Lab-oc`) 给出; `gŝ` 行、`Goodᴸ`、`gc`、`forceᴸ`、`limᴸ`、`ĉᴸ-mk`、`LabL` 原样. 第 0、1 层指数的引理 `WE₀`…`GoodE₁` 移植 (`…ᶠ`), 另有不需要自互模拟的 W 版 (`…ʷ`). **第 2 层帧 $\psi_\Omega(\Omega_2)$ 的好栈 `GoodE₂`/`GoodE₂⟨⟩`/`repGood₂` 与 $\psi_0(ps+\psi_\Omega(\Omega_2+1))$ 的证书和标签 `ZE₂₊` 是定理**; 地板见证由下标 $2$ 出现于帧标签给出 (`FWR`, `o₂`, `b₂`).
> 5. **一个设计修正 (§2 读法).** 提升地板的帧在第一份 ($m=1$) 必须在**旧地板**上折叠下面的栈 (`▹⟨ ρ ∣ s ∣ hp ⟩`, `repᴿ`), 只有含该帧的栈才用新地板; 否则帧值内部 (还没有这个帧) 的弹栈也会拿到被提升的界, 而前缀里没有任何下标能支配它.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件; 移植的定义都以新名字 (`…ᶠ`, `…ʷ`) 复制在本文.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLabZNonTightBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import Data.List.Properties using (++-identityʳ; ++-assoc)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev; Fs; Fst; σ1)
open import OCF.Align.LadderLabZPrefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_;
  z<suc; H1-pen; H1-fsT; trˢ; tr⁻ˢ; sqˢ; walkˢ; kind; Kind; kz; ks; kl; kĉ; kc)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; γT; sucT; cmpᵀ; Cmp; lt; eq; gt;
              []<; hd<; tl<; lv<; ar<; cofA; cofψ0; cofψ₊) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fs-rep; fs-ω)
open import OCF.Align.Bachmann using (fs-gt; pen→<; gt→≤; clash)
open import OCF.Align.Closure using (Pen; fsT₊-pen′; lt→<)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; NF₁-pred; NF₁-fsn; walk; walkD; tO-desc-NF)
open import OCF.Align.Standard using (Desc; d₀; Ctbl; c[]; c∷)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts; occ<)
open import OCF.Align.Stage2 using (Ωᵗ; tO)
open import OCF.Align.LadderLabZUniformS hiding (run)
open import OCF.Align.LadderLabZStage2Label using (one⁰; Lab-oc)
open import OCF.Align.LadderLabZDecoupleBase using (ΩΩ; ŝ-reflg)
open import OCF.Align.LadderLabZDecouple using (Idx; lvI; Ilt; Ieq; kdI; kdI′; gtν; kdI[]; cofP)
open import OCF.Align.LadderLabZGoodLBase
open import OCF.Align.LadderLabZOmegaExpBase using (σ⊥; πw; onCons; cofΣ; predΣ; fsnΣ; fsTΣ; OccΣ; cofW; repW; ωW; γW; γW-eq;
  gtW; penW; H1W; 1<π; ne-w; domS; 1<γ; rep-snoc; snoc)
open import OCF.Align.LadderLabZOmegaSqBase using (Lo; lo0; lo1; ψΩ; cmpΩ; cofΩc; fsTΩ; cE₁; fE₁; cEω; fEω; nfγ′; ŝChainG; Ω₂; Ω₂+1; low-NF)
open import OCF.Align.LadderLabZGoodL using (nf2; lab2)
```

## §1 地板与栈类型

**问题.** OmegaExpBase 的栈 `Stk = ∀ {i ℓ} → zero <ᴵ ℓ → i <ᴵ ℓ → Ordˢ i` 只带 "$0<^\mathsf I\ell$" 一种帧证据, 足以现造第 0、1 层指数的 `Sim`, 但第 $k\ge2$ 层要 `Simᴵ k ℓ`, 而紧界闭包的第 0 点环境层号是 $i+1$ (OmegaSqBase 的 `noSim21`). 所以栈类型要暴露帧需要的层号, 弹栈要据此选环境.

**字面性.** `Simᴵ a b` 是字面子项的嵌入, `<ᴵ` 是字面子项关系; 有界三歧性 `<ᴵ-dec` 只比较同一个 $\ell$ 的两个字面子项, 结果只模 $\cong^\mathsf I$. 所以地板要同时满足: (a) 帧证据 `Simᴵ F ℓ` 能字面地给出帧的 `Sim`; (b) 语义地板 $B$ 字面地在 $\ell$ 里 ($\iota_B$), 弹栈时能与目标 $i$ 比较; (c) $F\sqsubseteq B+1$, 使得以 $F$ 为界的闭包在语义上就是 "$B+1$". `Fs3`/`Mlev3` 是三项版的 `Mlev` ($[a,b,c,c,\dots]$), 闭包分支的环境层号要同时字面地装着目标、地板与 $\eta$. `simS`/`simM` 是 "字面装着" 的嵌入.

```agda
record Flr : Set where
  constructor flr
  field
    Fᶠ  : Ordᴵ
    Bᶠ  : Ordᴵ
    ιᶠ  : Bᶠ <ᴵ Fᶠ
    ιz  : zero <ᴵ Fᶠ
    FBᶠ : Fᶠ ⊑ᴵ suc Bᶠ
open Flr public

flr₁ : Flr
flr₁ = flr (suc zero) zero zero zero ⊑ᴵ-refl

record Stkᶠ (φ : Flr) : Set where
  constructor stk
  field run : ∀ {i ℓ} → Simᴵ (Fᶠ φ) ℓ → i <ᴵ ℓ → Ordˢ i
open Stkᶠ public

Fs3 : Ordᴵ → Ordᴵ → Ordᴵ → ℕ → Ordᴵ
Fs3 a b c zero          = a
Fs3 a b c (suc zero)    = b
Fs3 a b c (suc (suc _)) = c

Fst3 : ∀ {a b c} → a ⊑ᴵ b → b ⊑ᴵ c → ∀ n → Fs3 a b c n ⊑ᴵ Fs3 a b c (suc n)
Fst3 ab bc zero          = ab
Fst3 ab bc (suc zero)    = bc
Fst3 ab bc (suc (suc n)) = ⊑ᴵ-refl

Mlev3 : (a b c : Ordᴵ) → a ⊑ᴵ b → b ⊑ᴵ c → Ordᴵ
Mlev3 a b c ab bc = lim (Fs3 a b c) (Fst3 ab bc)

⊑-suc : ∀ a → a ⊑ᴵ suc a
⊑-suc a = Sim→⊑ᴵ suc

FsUB : ∀ {a b c} → a ⊑ᴵ c → b ⊑ᴵ c → ∀ n → Fs a b n ⊑ᴵ c
FsUB ac bc zero    = ac
FsUB ac bc (suc n) = bc

simS : ∀ {K ℓ} → K <ᴵ ℓ → Simᴵ (suc K) ℓ
simS κ zero    = κ
simS κ (suc q) = <ᴵ-trans q κ

simM : ∀ {a b e ℓ} → Simᴵ a ℓ → Simᴵ b ℓ → Simᴵ (Mlev a b e) ℓ
simM sa sb (lim zero q)    = sa q
simM sa sb (lim (suc n) q) = sb q
```

**读法.** `flr₁` 的 $F=1$: `Simᴵ 1 ℓ` 恰是 $0<^\mathsf I\ell$ (经 `σ1`), 所以 `Stkᶠ flr₁` 与旧 `Stk` 只差一个包装 (`stk`/`run`, 记录类型便于推断 $\varphi$). `FBᶠ` 只在语义上说 $F\le B+1$; 由于 Level 的 $\sqsubseteq^\mathsf I$ 对 `suc` 不单调, 凡要 "$c\sqsubseteq\mathtt{lvl}\,w+1$" 的地方都经 `s⊑` 从字面的 $B\preceq\mathtt{lvl}\,w$ 得到 (§6 的 `sB`).

## §2 折叠与非紧弹栈

**尾巴折叠** `ψˢᶠ` 与 OmegaExpBase 的 `ψˢ` 逐字, 只把 `S z p` 换成 `run S ζ p`.

**非紧弹栈.** `popI` (界 $i+1$) 与 `popF` (界 $F$) 只差环境层号的两项顺序: `popI` 用 `Mlev F (i+1)` (目标经 `lim 1 zero`, 栈经 `lim 0`), `popF` 用 `Mlev (i+1) F` (目标经 `lim 0 zero`, 栈经 `lim 1`); 分支 $\eta$ 处是 `Mlev3 … η`, $\Omega_\eta$ 经 `lim 2`. `popΩ` 按 `<ᴵ-dec (ζ ιᶠ) p` 三种情况取其一: $B\prec i$ 或 $B\cong i$ 走 `popI`, $i\prec B$ 走 `popF`. 步进证据都由 `s⊑` 从三歧的字面见证现造.

```agda
ψˢᶠ : ∀ {φ} → Stkᶠ φ → ∀ {i k ℓ} → Simᴵ (Fᶠ φ) ℓ → i <ᴵ ℓ → Simᴵ k ℓ → Ordˢ k → Ordˢ i
ψˢᶠ S ζ p σ Ord₊ˢ.zero    = run S ζ p
ψˢᶠ S ζ p σ (Ord₊ˢ.suc a) = Ord₊ˢ.lim (iter (ψˢᶠ S ζ p σ a +ˢ_) Ord₊ˢ.zero)
ψˢᶠ S ζ p σ (Ord₊ˢ.lim f) = Ord₊ˢ.lim (λ m → ψˢᶠ S ζ p σ (f m))
ψˢᶠ S ζ p σ (Ord₊ˢ.limᵢ {i = j} q f) with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = Ord₊ˢ.limᵢ r (λ y → ψˢᶠ S ζ p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) y)))))
... | injᵇ _ = Ord₊ˢ.lim (λ m → ψˢᶠ S ζ p σ (f (intoˢ (<→◃ q) (iter (λ x → ψˢᶠ S ζ (σ q) σ (f (intoˢ (<→◃ q) x))) (Ωˢ j) m))))
... | injᶜ _ = Ord₊ˢ.lim (λ m → ψˢᶠ S ζ p σ (f (intoˢ (<→◃ q) (iter (λ x → ψˢᶠ S ζ (σ q) σ (f (intoˢ (<→◃ q) x))) (Ωˢ j) m))))
ψˢᶠ S ζ p σ (Ord₊ˢ.up zero x)     = ψˢᶠ S ζ p (λ q → σ (suc q)) x
ψˢᶠ S ζ p σ (Ord₊ˢ.up (self m) x) = ψˢᶠ S ζ p (λ q → σ (lim m q)) x
ψˢᶠ S {k = zero}    ζ p σ (Ord₊ˢ.ŝ c t₀ g) = Ord₊ˢ.ĉᴸ c (toZ t₀) (λ η e → toZ (g η e)) (ψˢᶠ S ζ p σ t₀) (λ η e → ψˢᶠ S ζ p σ (g η e))
ψˢᶠ S {k = suc _}   ζ p σ (Ord₊ˢ.ŝ c t₀ g) = Ord₊ˢ.ŝ c (ψˢᶠ S ζ p σ t₀) (λ η e → ψˢᶠ S ζ p σ (g η e))
ψˢᶠ S {k = lim _ _} ζ p σ (Ord₊ˢ.ŝ c t₀ g) = Ord₊ˢ.ŝ c (ψˢᶠ S ζ p σ t₀) (λ η e → ψˢᶠ S ζ p σ (g η e))
ψˢᶠ S ζ p σ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) = Ord₊ˢ.ĉᴸ c t₀ g (ψˢᶠ S ζ p σ o₀) (λ η e → ψˢᶠ S ζ p σ (o η e))

∅ᶠ : Stkᶠ flr₁
∅ᶠ = stk (λ {i} ζ p → Ωˢ i)

popI : ∀ {φ} → Stkᶠ φ → ∀ {i} → Fᶠ φ ⊑ᴵ suc i → Ordˢ i
popI {φ} S {i} fi =
  Ord₊ˢ.ŝ (suc i) (ψˢᶠ S {ℓ = Mlev (Fᶠ φ) (suc i) fi} (λ q → lim 0 q) (lim 1 zero) (σ1 (lim 0 (ιz φ))) (Ωˢ (suc zero)))
          (λ η e → ψˢᶠ S {ℓ = Mlev3 (Fᶠ φ) (suc i) η fi e} (λ q → lim 0 q) (lim 1 zero) (λ q → lim 2 q) (Ωˢ η))

popF : ∀ {φ} → Stkᶠ φ → ∀ {i} → suc i ⊑ᴵ Fᶠ φ → Ordˢ i
popF {φ} S {i} sf =
  Ord₊ˢ.ŝ (Fᶠ φ) (ψˢᶠ S {ℓ = Mlev (suc i) (Fᶠ φ) sf} (λ q → lim 1 q) (lim 0 zero) (σ1 (lim 1 (ιz φ))) (Ωˢ (suc zero)))
          (λ η e → ψˢᶠ S {ℓ = Mlev3 (suc i) (Fᶠ φ) η sf e} (λ q → lim 1 q) (lim 0 zero) (λ q → lim 2 q) (Ωˢ η))

Dec3 : Ordᴵ → Ordᴵ → Set
Dec3 a b = (a ≺ᴵ b) ⊎ (b ≺ᴵ a) ⊎ (a ≅ᴵ b)

popΩ : ∀ {φ} → Stkᶠ φ → ∀ {i} → Dec3 (Bᶠ φ) i → Ordˢ i
popΩ {φ} S (injᵃ (via e r)) = popI S (⊑ᴵ-trans (FBᶠ φ) (s⊑ e (suc r)))
popΩ {φ} S (injᵇ (via e r)) = popF S (s⊑ e (<ᴵ-trans r (ιᶠ φ)))
popΩ {φ} S (injᶜ e)         = popI S (⊑ᴵ-trans (FBᶠ φ) (s⊑ e zero))

_▹Ω̂ᶠ : ∀ {φ} → Stkᶠ φ → Stkᶠ φ
_▹Ω̂ᶠ {φ} S = stk (λ ζ p → popΩ S (<ᴵ-dec (ζ (ιᶠ φ)) p))
```

**读法.** $B=0$ (没有第 $\ge2$ 层帧) 时 $i\prec0$ 不可能, 弹栈总是界 $i+1$, 与紧界设计同界 (环境层号不同, 树经互模拟一致, 见 NonTight §1). 与 Prefix §7 的 `c = ℓ` 不同, 这里的界是语义上的 $\max(i,B)+1$, 不随环境层号膨胀.

**提升地板.** `raise φ κ ζ` ($\kappa : K<^\mathsf I\ell$) 给出新地板 $\varphi'$、旧 $F$ 到新 $F'$ 的嵌入 `ρF`、$K+1$ 到 $F'$ 的嵌入 `ρK`, 以及当前环境的新帧证据 `ζ′`. 三种情况: $K\prec B$ 或 $K\cong B$ 时 $B'=B$, $F'=[K+1, F, F,\dots]$; $B\prec K$ 时 $B'=K$, $F'=[F, K+1, K+1,\dots]$.

```agda
record Raise (φ : Flr) (K ℓ : Ordᴵ) : Set where
  constructor rz
  field
    φ′ : Flr
    ρF : Simᴵ (Fᶠ φ) (Fᶠ φ′)
    ρK : Simᴵ (suc K) (Fᶠ φ′)
    ζ′ : Simᴵ (Fᶠ φ′) ℓ

raise′ : ∀ (φ : Flr) {K ℓ} → K <ᴵ ℓ → Simᴵ (Fᶠ φ) ℓ → Dec3 K (Bᶠ φ) → Raise φ K ℓ
raise′ φ {K} κ ζ (injᵃ (via e r)) =
  rz (flr (Mlev (suc K) (Fᶠ φ) (s⊑ e (<ᴵ-trans r (ιᶠ φ)))) (Bᶠ φ) (lim 1 (ιᶠ φ)) (lim 1 (ιz φ))
          (l⊑ (FsUB (s⊑ e (suc r)) (FBᶠ φ))))
     (λ q → lim 1 q) (λ q → lim 0 q) (simM (simS κ) ζ)
raise′ φ {K} κ ζ (injᵇ (via e r)) =
  rz (flr (Mlev (Fᶠ φ) (suc K) (⊑ᴵ-trans (FBᶠ φ) (s⊑ e (suc r)))) K (lim 1 zero) (lim 0 (ιz φ))
          (l⊑ (FsUB (⊑ᴵ-trans (FBᶠ φ) (s⊑ e (suc r))) ⊑ᴵ-refl)))
     (λ q → lim 0 q) (λ q → lim 1 q) (simM ζ (simS κ))
raise′ φ {K} κ ζ (injᶜ e) =
  rz (flr (Mlev (suc K) (Fᶠ φ) (s⊑ e (ιᶠ φ))) (Bᶠ φ) (lim 1 (ιᶠ φ)) (lim 1 (ιz φ))
          (l⊑ (FsUB (s⊑ e zero) (FBᶠ φ))))
     (λ q → lim 1 q) (λ q → lim 0 q) (simM (simS κ) ζ)

raise : ∀ (φ : Flr) {K ℓ} → K <ᴵ ℓ → Simᴵ (Fᶠ φ) ℓ → Raise φ K ℓ
raise φ κ ζ = raise′ φ κ ζ (<ᴵ-dec κ (ζ (ιᶠ φ)))
```

**指数折叠** `ψᵉᶠ` 是 OmegaSqBase `ψᵉ′` 的推广, 多一个**把手** `Hd k ℓ` (可选的字面 $k<^\mathsf I\ell$). 后继子句:

- 第 0 层: `repᶠ` 帧 `(λ _ → σ⊥)` (唯一常量), 地板不动.
- 第 1 层: 帧 `σ1 (ζ′ ιz)`, 地板不动.
- 第 $K'+2$ 层或第 $(\lim)+1$ 层: $K = $ 前驱层号, $\kappa=\sigma\,0$, `raise`, 帧 `λ ζ′ q → ζ′ (ρK q)`, 栈 `repᴿ`.
- 极限层且带把手 `hyes κ`: $K=k$ 本身, 帧经 `ρK (suc q)`; 新帧带把手 `hyes (ζ′ (ρK zero))`.
- 极限层无把手: **占位** $0$ (唯一剩下的占位; NonTight §4 有它的编译见证).

把手的来源: `up zero x` 子句 (从 $k'+1$ 降到 $k'$) 给 `hyes (σ zero)`; `up (self m)` 给 `hno`; 其余子句原样传递. `▹⟨ ρ ∣ s ∣ hp ⟩` 是**在旧地板上**折叠下面栈的帧, `repᴿ` 的第 1 份用它, 第 $m+2$ 份才在新地板上叠 `▹[ s ∣ hp ]`.

```agda
data Hd (k ℓ : Ordᴵ) : Set where
  hno  : Hd k ℓ
  hyes : k <ᴵ ℓ → Hd k ℓ

FrS : Flr → Ordᴵ → Set
FrS φ k = ∀ {ℓ} → Simᴵ (Fᶠ φ) ℓ → Simᴵ k ℓ

FrH : Flr → Ordᴵ → Set
FrH φ k = ∀ {ℓ} → Simᴵ (Fᶠ φ) ℓ → Hd k ℓ

ψᵉᶠ  : ∀ {φ} → Stkᶠ φ → ∀ {i k ℓ} → Simᴵ (Fᶠ φ) ℓ → i <ᴵ ℓ → Simᴵ k ℓ → Hd k ℓ → Ordˢ k → Ordˢ i
repᶠ : ∀ {φ k} → Stkᶠ φ → (φ′ : Flr) → Simᴵ (Fᶠ φ) (Fᶠ φ′) → FrS φ′ k → FrH φ′ k → Ordˢ k → ℕ → Stkᶠ φ′
_▹[_∣_]_ : ∀ {φ k} → Stkᶠ φ → FrS φ k → FrH φ k → Ordˢ k → Stkᶠ φ
repᴿ : ∀ {φ k} → Stkᶠ φ → (φ′ : Flr) → Simᴵ (Fᶠ φ) (Fᶠ φ′) → FrS φ′ k → FrH φ′ k → Ordˢ k → ℕ → Stkᶠ φ′
_▹⟨_∣_∣_⟩_ : ∀ {φ φ′ k} → Stkᶠ φ → Simᴵ (Fᶠ φ) (Fᶠ φ′) → FrS φ′ k → FrH φ′ k → Ordˢ k → Stkᶠ φ′

ψᵉᶠ S ζ p σ h Ord₊ˢ.zero = run (S ▹Ω̂ᶠ) ζ p
ψᵉᶠ {φ} S {k = zero} ζ p σ h (Ord₊ˢ.suc a) =
  Ord₊ˢ.lim (λ m → run (repᶠ S φ (λ q → q) (λ _ → σ⊥) (λ _ → hno) a m) ζ p)
ψᵉᶠ {φ} S {k = suc zero} ζ p σ h (Ord₊ˢ.suc a) =
  Ord₊ˢ.lim (λ m → run (repᶠ S φ (λ q → q) (λ ζ′ → σ1 (ζ′ (ιz φ))) (λ _ → hno) a m) ζ p)
ψᵉᶠ {φ} S {k = suc (suc K)} ζ p σ h (Ord₊ˢ.suc a) =
  let R = raise φ (σ zero) ζ in
  Ord₊ˢ.lim (λ m → run (repᴿ S (Raise.φ′ R) (Raise.ρF R) (λ ζ′ q → ζ′ (Raise.ρK R q)) (λ _ → hno) a m) (Raise.ζ′ R) p)
ψᵉᶠ {φ} S {k = suc (lim f s)} ζ p σ h (Ord₊ˢ.suc a) =
  let R = raise φ (σ zero) ζ in
  Ord₊ˢ.lim (λ m → run (repᴿ S (Raise.φ′ R) (Raise.ρF R) (λ ζ′ q → ζ′ (Raise.ρK R q)) (λ _ → hno) a m) (Raise.ζ′ R) p)
ψᵉᶠ {φ} S {k = lim f s} ζ p σ (hyes κ) (Ord₊ˢ.suc a) =
  let R = raise φ κ ζ in
  Ord₊ˢ.lim (λ m → run (repᴿ S (Raise.φ′ R) (Raise.ρF R) (λ ζ′ q → ζ′ (Raise.ρK R (suc q)))
                                (λ ζ′ → hyes (ζ′ (Raise.ρK R zero))) a m) (Raise.ζ′ R) p)
ψᵉᶠ S {k = lim f s} ζ p σ hno (Ord₊ˢ.suc a) = Ord₊ˢ.zero
ψᵉᶠ S ζ p σ h (Ord₊ˢ.lim f) = Ord₊ˢ.lim (λ m → ψᵉᶠ S ζ p σ h (f m))
ψᵉᶠ S ζ p σ h (Ord₊ˢ.limᵢ {i = j} q f) with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = Ord₊ˢ.limᵢ r (λ y → ψᵉᶠ S ζ p σ h (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) y)))))
... | injᵇ _ = Ord₊ˢ.lim (λ m → ψᵉᶠ S ζ p σ h (f (intoˢ (<→◃ q) (iter (λ x → ψᵉᶠ S ζ (σ q) σ h (f (intoˢ (<→◃ q) x))) (Ωˢ j) m))))
... | injᶜ _ = Ord₊ˢ.lim (λ m → ψᵉᶠ S ζ p σ h (f (intoˢ (<→◃ q) (iter (λ x → ψᵉᶠ S ζ (σ q) σ h (f (intoˢ (<→◃ q) x))) (Ωˢ j) m))))
ψᵉᶠ S ζ p σ h (Ord₊ˢ.up zero x)     = ψᵉᶠ S ζ p (λ q → σ (suc q)) (hyes (σ zero)) x
ψᵉᶠ S ζ p σ h (Ord₊ˢ.up (self m) x) = ψᵉᶠ S ζ p (λ q → σ (lim m q)) hno x
ψᵉᶠ S {k = zero}    ζ p σ h (Ord₊ˢ.ŝ c t₀ g) = Ord₊ˢ.ĉᴸ c (toZ t₀) (λ η e → toZ (g η e)) (ψᵉᶠ S ζ p σ h t₀) (λ η e → ψᵉᶠ S ζ p σ h (g η e))
ψᵉᶠ S {k = suc _}   ζ p σ h (Ord₊ˢ.ŝ c t₀ g) = Ord₊ˢ.ŝ c (ψᵉᶠ S ζ p σ h t₀) (λ η e → ψᵉᶠ S ζ p σ h (g η e))
ψᵉᶠ S {k = lim _ _} ζ p σ h (Ord₊ˢ.ŝ c t₀ g) = Ord₊ˢ.ŝ c (ψᵉᶠ S ζ p σ h t₀) (λ η e → ψᵉᶠ S ζ p σ h (g η e))
ψᵉᶠ S ζ p σ h (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) = Ord₊ˢ.ĉᴸ c t₀ g (ψᵉᶠ S ζ p σ h o₀) (λ η e → ψᵉᶠ S ζ p σ h (o η e))

S ▹[ s ∣ hp ] a = stk (λ ζ p → ψᵉᶠ S ζ p (s ζ) (hp ζ) a)

repᶠ S φ′ ρ s hp a zero    = stk (λ ζ p → run S (λ q → ζ (ρ q)) p)
repᶠ S φ′ ρ s hp a (suc m) = repᶠ S φ′ ρ s hp a m ▹[ s ∣ hp ] a

S ▹⟨ ρ ∣ s ∣ hp ⟩ a = stk (λ ζ p → ψᵉᶠ S (λ q → ζ (ρ q)) p (s ζ) (hp ζ) a)

repᴿ S φ′ ρ s hp a zero          = stk (λ ζ p → run S (λ q → ζ (ρ q)) p)
repᴿ S φ′ ρ s hp a (suc zero)    = S ▹⟨ ρ ∣ s ∣ hp ⟩ a
repᴿ S φ′ ρ s hp a (suc (suc m)) = repᴿ S φ′ ρ s hp a (suc m) ▹[ s ∣ hp ] a
```

**读法 (停机).** 一次通过: `ψᵉᶠ … (suc a)` → `repᶠ`/`repᴿ … a m` (指数降), `repᴿ (suc (suc m))` → `repᴿ (suc m)` (重数降), `▹⟨⟩`/`▹[]` → `ψᵉᶠ … a` (指数同). `raise` 不递归, 用 `let` 放在子句右边, 不需要 `with`.

**读法 (为什么第 1 份在旧地板上).** 最初的写法让 `repᴿ = repᶠ` (第 $0$ 份是把 $S$ 搬到新地板的 $S$, 其上逐份叠帧). 那样第 1 份帧的指数 $\Omega_2$ 在**新地板**的 $S$ 上折叠, 折叠到指数 $0$ 时的弹栈是 $\psi_0(ps+\Omega_\Omega)$ 而前缀里还没有 $\psi_\Omega(\Omega_2)$, 却拿到被提升的界 $\cong2$; 它的支配需要一个出现在 `ps` 里、层号 $\succeq1$ 的下标, 一般不存在 (例如 `ps = []`: $\psi_0(\Omega_\theta)$ 的链点层号确实 $\ge2$, 但没有任何下标出现; 这是纸面论证, 那个写法编译通过, 失败在标签侧的支配). 改成 `▹⟨⟩` 后, 只有真正含该帧的栈 (第 $m\ge2$ 份之下) 用新地板, §9 的地板见证就是帧标签里的下标 $2$.

**$\hat\Omega^2$ 帧** 同式; 分支处的指数 $\Omega_\eta$ 在 `Mlev3 … (η+1)` 上计算并带把手 `hyes (lim 2 zero)`, 以便极限层的 $\Omega_\eta$ 的后继有字面层号可比.

```agda
popI² : ∀ {φ} → Stkᶠ φ → ∀ {i} → Fᶠ φ ⊑ᴵ suc i → Ordˢ i
popI² {φ} S {i} fi =
  Ord₊ˢ.ŝ (suc i) (ψᵉᶠ S {ℓ = Mlev (Fᶠ φ) (suc i) fi} (λ q → lim 0 q) (lim 1 zero) (σ1 (lim 0 (ιz φ))) hno (Ωˢ (suc zero)))
          (λ η e → ψᵉᶠ S {ℓ = Mlev3 (Fᶠ φ) (suc i) (suc η) fi (⊑ᴵ-trans e (⊑-suc η))} (λ q → lim 0 q) (lim 1 zero)
                       (λ q → lim 2 (suc q)) (hyes (lim 2 zero)) (Ωˢ η))

popF² : ∀ {φ} → Stkᶠ φ → ∀ {i} → suc i ⊑ᴵ Fᶠ φ → Ordˢ i
popF² {φ} S {i} sf =
  Ord₊ˢ.ŝ (Fᶠ φ) (ψᵉᶠ S {ℓ = Mlev (suc i) (Fᶠ φ) sf} (λ q → lim 1 q) (lim 0 zero) (σ1 (lim 1 (ιz φ))) hno (Ωˢ (suc zero)))
          (λ η e → ψᵉᶠ S {ℓ = Mlev3 (suc i) (Fᶠ φ) (suc η) sf (⊑ᴵ-trans e (⊑-suc η))} (λ q → lim 1 q) (lim 0 zero)
                       (λ q → lim 2 (suc q)) (hyes (lim 2 zero)) (Ωˢ η))

popΩ² : ∀ {φ} → Stkᶠ φ → ∀ {i} → Dec3 (Bᶠ φ) i → Ordˢ i
popΩ² {φ} S (injᵃ (via e r)) = popI² S (⊑ᴵ-trans (FBᶠ φ) (s⊑ e (suc r)))
popΩ² {φ} S (injᵇ (via e r)) = popF² S (s⊑ e (<ᴵ-trans r (ιᶠ φ)))
popΩ² {φ} S (injᶜ e)         = popI² S (⊑ᴵ-trans (FBᶠ φ) (s⊑ e zero))

_▹Ω̂²ᶠ : ∀ {φ} → Stkᶠ φ → Stkᶠ φ
_▹Ω̂²ᶠ {φ} S = stk (λ ζ p → popΩ² S (<ᴵ-dec (ζ (ιᶠ φ)) p))
```

## §3 树侧检验: 低目标帧与它上面的弹栈

**低目标.** `lowᶠ` 是 OmegaSqBase §3 的 `lowˢ` 在新折叠下的版本 ($\psi_0(\psi_\Omega(\psi_2(1)))$, 环境层号 $3$). OmegaSqBase 里 $[2,0,0]$ 处是占位 $0$ (`low-tree : … ≡ kz`), 这里是真的极限; $[2,0,0,2,0,0,1]$ 是第二份 $\psi_\Omega(\Omega_2)$ 帧之上弹出 $\hat\Omega$ (记号侧即 OmegaSqBase 的 `low-pop`), 结果是界为 `Mlev 1 2 _` 的闭包 (目标 $0\prec B'=1$, 走 `popF`); 再往下 $[\dots,1,0,0,1,1]$ 进入闭包的第 0 点, 第 2 层帧的指数 $\Omega_2$ 在目标 $0$ 处沿第 1 层的链折叠, 是极限 (`kl`), 不再需要 `Simᴵ 2 1`.

**极限层.** `limᶠ` 是 $\psi_0(\psi_\Omega(\Omega_{\omega+1}))$ ($\omega$ 的层号是 `toLevel ωᶜ ωᶜ-HS`); $[1,0,1,0,0,2,0]$ 处的指数 $\Omega_\omega+1$ 是**极限层**的后继 (记号侧见 NonTight §4 的 `lim-term`), 经 `up zero` 带着把手, 所以也是真的极限; 其后 $[2,0,1]$ 的弹栈界为 `Mlev 1 (ω+1) _` (`limbound`).

```agda
three : Ordᴵ
three = suc two

z3 : zero <ᴵ three
z3 = suc (suc zero)

ψ₂1ᶠ : Ordˢ two
ψ₂1ᶠ = ψˢᶠ ∅ᶠ {ℓ = three} (σ1 z3) zero σ⊥ (Ord₊ˢ.suc Ord₊ˢ.zero)

lowᶠ : Ordˢ zero
lowᶠ = ψᵉᶠ ∅ᶠ (σ1 z3) z3 (λ q → suc q) (hyes zero) ψ₂1ᶠ

_ : kind (walkˢ lowᶠ (2 ∷ 0 ∷ [])) ≡ kl
_ = refl

_ : kind (walkˢ lowᶠ (2 ∷ 0 ∷ 0 ∷ [])) ≡ kl
_ = refl

_ : kind (walkˢ lowᶠ (2 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 1 ∷ [])) ≡ kc (Mlev (suc zero) two (⊑ᴵ-trans ⊑ᴵ-refl (s⊑ (≅ᴵ-refl zero) (suc zero))))
_ = refl

_ : kind (walkˢ lowᶠ (2 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ [])) ≡ kl
_ = refl

ωᵗ : Ordᴵ
ωᵗ = toLevel ωᶜ ωᶜ-HS

z<ω : zero <ᴵ ωᵗ
z<ω = lim 1 zero

limᶠ : Ordˢ zero
limᶠ = ψᵉᶠ ∅ᶠ {ℓ = suc (suc ωᵗ)} (σ1 (suc (suc z<ω))) (suc (suc z<ω)) (λ q → suc q) (hyes zero) (Ωˢ (suc ωᵗ))

_ : kind (walkˢ limᶠ (1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ [])) ≡ kl
_ = refl

_ : kind (walkˢ limᶠ (1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 2 ∷ 1 ∷ [])) ≡ kl
_ = refl


limbound : kind (walkˢ limᶠ (1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 2 ∷ 0 ∷ 1 ∷ [])) ≡
           kc (Mlev (suc zero) (suc ωᵗ) (⊑ᴵ-trans (s⊑ (≅ᴵ-refl zero) zero) (s⊑ (≅ᴵ-refl zero) (suc z<ω))))
limbound = refl
```

**读法.** 对照 OmegaSqBase: `low-tree` 与 `noSim21` 说明紧界设计在这个位置只能放占位; 这里同一位置是真的树, 而且弹栈的界恰是 "$\max(0,1)+1 = 2$" (第 2 层的帧 $\psi_\Omega(\Omega_2)$, 地板 $B=1$), 与 OmegaSqBase §1 的设计预期一致. 第 0 点环境层号 `Mlev (1) (F′)` 字面装着 $1$ (经 `F′ = Mlev 1 2 _` 的第 1 项), 所以第 2 层帧的 `Sim` 是 `λ q → lim 1 (ρK q)` 一类的项, 不再撞上 `noSim21`.

## §4 互模拟

`_≈ᶠ_` 允许两侧地板不同 (OmegaExpBase `≈ˢ` 的推广); `liSᶠ`/`ψˢᶠ-≅` 逐字. 弹栈的互模拟 `popΩ-≈` 要两侧同地板: 两侧的三歧结果在 $i\cong i'$ 下只能同为 "界 $i+1$" 或同为 "界 $F$" (交叉的四种情况由 `≺ᴵ-irrefl` 排除), 于是 `ŝ≅` 要的 "界 $\cong$" (UniformS §2 的传递性所需) 成立: $i+1\cong i'+1$ 或 $F\cong F$.

```agda
_≈ᶠ_ : ∀ {φ φ′} → Stkᶠ φ → Stkᶠ φ′ → Set
_≈ᶠ_ {φ} {φ′} S S′ = ∀ {i i′ ℓ ℓ′} (z : Simᴵ (Fᶠ φ) ℓ) (p : i <ᴵ ℓ) (z′ : Simᴵ (Fᶠ φ′) ℓ′) (p′ : i′ <ᴵ ℓ′) → i ≅ᴵ i′ → run S z p ≅ˢ run S′ z′ p′

liSᶠ : ∀ {φ φ′} {S : Stkᶠ φ} {S′ : Stkᶠ φ′} {i i′ k₁ ℓ₁ k₂ ℓ₂ j j′} {z : Simᴵ (Fᶠ φ) ℓ₁} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁}
      {z′ : Simᴵ (Fᶠ φ′) ℓ₂} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂}
      {q : j <ᴵ k₁} {q′ : j′ <ᴵ k₂} {f : Uˢ j (<→◃ q) → Ordˢ k₁} {g : Uˢ j′ (<→◃ q′) → Ordˢ k₂} →
      i ≅ᴵ i′ → j ≅ᴵ j′ →
      (∀ (x : Ordˢ j) (y : Ordˢ j′) → Rˢ j (<→◃ q) (intoˢ (<→◃ q) x) y →
         ψˢᶠ S z p σ (f (intoˢ (<→◃ q) x)) ≅ˢ ψˢᶠ S′ z′ p′ σ′ (g (intoˢ (<→◃ q′) y))) →
      (∀ (x : Ordˢ j) (y : Ordˢ j′) → Rˢ j (<→◃ q) (intoˢ (<→◃ q) x) y →
         ψˢᶠ S z (σ q) σ (f (intoˢ (<→◃ q) x)) ≅ˢ ψˢᶠ S′ z′ (σ′ q′) σ′ (g (intoˢ (<→◃ q′) y))) →
      ψˢᶠ S z p σ (Ord₊ˢ.limᵢ q f) ≅ˢ ψˢᶠ S′ z′ p′ σ′ (Ord₊ˢ.limᵢ q′ g)
liSᶠ {S = S} {S′ = S′} {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} {q = q} {q′ = q′} {f = f} {g = g} ei e rec recC
  with <ᴵ-dec (σ q) p | <ᴵ-dec (σ′ q′) p′
... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) = lᵢ≅ (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans e e₂)) λ x y d →
  subst₂ (λ u v → ψˢᶠ S z p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e₁ u))) ≅ˢ ψˢᶠ S′ z′ p′ σ′ (g (intoˢ (<→◃ q′) (tr⁻ˢ e₂ v))))
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

ψˢᶠ-≅ : ∀ {φ φ′} {S : Stkᶠ φ} {S′ : Stkᶠ φ′} → S ≈ᶠ S′ → ∀ {i i′ k₁ ℓ₁ k₂ ℓ₂} {z : Simᴵ (Fᶠ φ) ℓ₁} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁}
       {z′ : Simᴵ (Fᶠ φ′) ℓ₂} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂} {a : Ordˢ k₁} {b : Ordˢ k₂} →
       i ≅ᴵ i′ → a ≅ˢ b → ψˢᶠ S z p σ a ≅ˢ ψˢᶠ S′ z′ p′ σ′ b
ψˢᶠ-≅ H {z = z} {p = p} {z′ = z′} {p′ = p′} ei z≅ = H z p z′ p′ ei
ψˢᶠ-≅ H ei (s≅ e) = l≅ (iter-R _≅ˢ_ (λ e′ → addˢ-≅ (kd-≅ ei) (ψˢᶠ-≅ H ei e) e′) z≅)
ψˢᶠ-≅ H ei (l≅ h) = l≅ (λ n → ψˢᶠ-≅ H ei (h n))
ψˢᶠ-≅ H ei (upˡ {r = zero} e)   = ψˢᶠ-≅ H ei e
ψˢᶠ-≅ H ei (upˡ {r = self m} e) = ψˢᶠ-≅ H ei e
ψˢᶠ-≅ H ei (upʳ {r = zero} e)   = ψˢᶠ-≅ H ei e
ψˢᶠ-≅ H ei (upʳ {r = self m} e) = ψˢᶠ-≅ H ei e
ψˢᶠ-≅ H {k₁ = zero}    {k₂ = zero}    ei (ŝ≅ k ec et eg) =
  ĉ≅ ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη)) (ψˢᶠ-≅ H ei et) (λ η e η′ e′ eη → ψˢᶠ-≅ H ei (eg η e η′ e′ eη))
ψˢᶠ-≅ H {k₁ = zero}    {k₂ = suc _}   ei (ŝ≅ k ec et eg) = ⊥-elim (tf k)
ψˢᶠ-≅ H {k₁ = zero}    {k₂ = lim _ _} ei (ŝ≅ k ec et eg) = ⊥-elim (tf k)
ψˢᶠ-≅ H {k₁ = suc _}   {k₂ = zero}    ei (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
ψˢᶠ-≅ H {k₁ = lim _ _} {k₂ = zero}    ei (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
ψˢᶠ-≅ H {k₁ = suc _}   {k₂ = suc _}   ei (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ ei) ec (ψˢᶠ-≅ H ei et) (λ η e η′ e′ eη → ψˢᶠ-≅ H ei (eg η e η′ e′ eη))
ψˢᶠ-≅ H {k₁ = suc _}   {k₂ = lim _ _} ei (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ ei) ec (ψˢᶠ-≅ H ei et) (λ η e η′ e′ eη → ψˢᶠ-≅ H ei (eg η e η′ e′ eη))
ψˢᶠ-≅ H {k₁ = lim _ _} {k₂ = suc _}   ei (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ ei) ec (ψˢᶠ-≅ H ei et) (λ η e η′ e′ eη → ψˢᶠ-≅ H ei (eg η e η′ e′ eη))
ψˢᶠ-≅ H {k₁ = lim _ _} {k₂ = lim _ _} ei (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ ei) ec (ψˢᶠ-≅ H ei et) (λ η e η′ e′ eη → ψˢᶠ-≅ H ei (eg η e η′ e′ eη))
ψˢᶠ-≅ H ei (ĉ≅ ec dt dg eo eO) = ĉ≅ ec dt dg (ψˢᶠ-≅ H ei eo) (λ η e η′ e′ eη → ψˢᶠ-≅ H ei (eO η e η′ e′ eη))
ψˢᶠ-≅ {S = S} {S′ = S′} H {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} ei (lᵢ≅ {p = q} {q = q′} {f = f} {g = g} e h) =
  liSᶠ {S = S} {S′ = S′} {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} {q = q} {q′ = q′} {f = f} {g = g} ei e
      (λ x y d → ψˢᶠ-≅ H {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} ei (h x y d))
      (λ x y d → ψˢᶠ-≅ H {z = z} {p = σ q} {σ = σ} {z′ = z′} {p′ = σ′ q′} {σ′ = σ′} e (h x y d))


popI-≈ : ∀ {φ} {S S′ : Stkᶠ φ} → S ≈ᶠ S′ → ∀ {i i′} (fi : Fᶠ φ ⊑ᴵ suc i) (fi′ : Fᶠ φ ⊑ᴵ suc i′) → i ≅ᴵ i′ →
         popI S fi ≅ˢ popI S′ fi′
popI-≈ H fi fi′ ei = ŝ≅ (kd-≅ ei) (s≅ ei) (ψˢᶠ-≅ H ei (Ωˢ-refl (suc zero))) (λ η e η′ e′ eη → ψˢᶠ-≅ H ei (Ωˢ-≅ eη))

popF-≈ : ∀ {φ} {S S′ : Stkᶠ φ} → S ≈ᶠ S′ → ∀ {i i′} (sf : suc i ⊑ᴵ Fᶠ φ) (sf′ : suc i′ ⊑ᴵ Fᶠ φ) → i ≅ᴵ i′ →
         popF S sf ≅ˢ popF S′ sf′
popF-≈ H sf sf′ ei = ŝ≅ (kd-≅ ei) (≅ᴵ-refl _) (ψˢᶠ-≅ H ei (Ωˢ-refl (suc zero))) (λ η e η′ e′ eη → ψˢᶠ-≅ H ei (Ωˢ-≅ eη))

popΩ-≈ : ∀ {φ} {S S′ : Stkᶠ φ} → S ≈ᶠ S′ → ∀ {i i′} (d : Dec3 (Bᶠ φ) i) (d′ : Dec3 (Bᶠ φ) i′) → i ≅ᴵ i′ →
         popΩ S d ≅ˢ popΩ S′ d′
popΩ-≈ {φ} H (injᵃ (via _ _)) (injᵃ (via _ _)) ei = popI-≈ {φ} H _ _ ei
popΩ-≈ {φ} H (injᵃ (via _ _)) (injᶜ _) ei = popI-≈ {φ} H _ _ ei
popΩ-≈ {φ} H (injᶜ _) (injᵃ (via _ _)) ei = popI-≈ {φ} H _ _ ei
popΩ-≈ {φ} H (injᶜ _) (injᶜ _) ei = popI-≈ {φ} H _ _ ei
popΩ-≈ {φ} H (injᵇ (via _ _)) (injᵇ (via _ _)) ei = popF-≈ {φ} H _ _ ei
popΩ-≈ H (injᵃ r) (injᵇ s) ei = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-trans (≺ᴵ-respʳ r ei) s))
popΩ-≈ H (injᵇ s) (injᵃ r) ei = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-trans (≺ᴵ-respʳ r (≅ᴵ-sym ei)) s))
popΩ-≈ H (injᶜ c) (injᵇ s) ei = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ s (≅ᴵ-trans c ei)))
popΩ-≈ H (injᵇ s) (injᶜ c) ei = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ s (≅ᴵ-trans c (≅ᴵ-sym ei))))

∅-≈ᶠ : ∅ᶠ ≈ᶠ ∅ᶠ
∅-≈ᶠ z p z′ p′ ei = Ωˢ-≅ ei

▹Ω̂ᶠ-≈ : ∀ {φ} {S S′ : Stkᶠ φ} → S ≈ᶠ S′ → (S ▹Ω̂ᶠ) ≈ᶠ (S′ ▹Ω̂ᶠ)
▹Ω̂ᶠ-≈ {φ} H z p z′ p′ ei = popΩ-≈ H (<ᴵ-dec (z (ιᶠ φ)) p) (<ᴵ-dec (z′ (ιᶠ φ)) p′) ei
```

**读法.** 地板的非紧性对互模拟是透明的: 界由三歧的**语义**结果决定, 而三歧对 $\cong^\mathsf I$ 稳定 (`clash` 一类的论证). 要求同地板不是限制: 递归中两侧的栈总是同一个栈 (自互模拟) 或由同一组帧堆成.

## §5 一般栈上的带前缀引理 (移植)

OmegaExpBase §4–§5 的 `chainS`/`fold1S`/`pen1S`、`HypW`/`Hyp0`、模块 `PreW`/`Pre0` 逐字移植到 `Stkᶠ`: 只换帧证据的类型 (`z : Simᴵ (Fᶠ φ) ℓ`) 与弹栈值 (`run S z p`). 证明一行不改, 因为它们从不看帧证据. 记号引理 (`πw`, `cofW`, `gtW`, `H1W`, `domS`, `1<γ`, …) 从 OmegaExpBase 导入.

```agda
chainSᶠ : ∀ {φ : Flr} (S : Stkᶠ φ) {j k ℓ} (z : Simᴵ (Fᶠ φ) ℓ) (σ : Simᴵ k ℓ) (q : j <ᴵ k) (f : Uˢ j (<→◃ q) → Ordˢ k) → ℕ → Ordˢ j
chainSᶠ S {j} z σ q f = iter (λ x → ψˢᶠ S z (σ q) σ (f (intoˢ (<→◃ q) x))) (Ωˢ j)

chainSᶠ-≅ : ∀ {φ} {S : Stkᶠ φ} {j k k′ ℓ} {z : Simᴵ (Fᶠ φ) ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} {b : Ordˢ k′} →
           S ≈ᶠ S → Ord₊ˢ.limᵢ q f ≅ˢ b → ∀ m → chainSᶠ S z σ q f m ≅ˢ chainSᶠ S z σ q f m
chainSᶠ-≅ {j = j} H e zero    = Ωˢ-refl j
chainSᶠ-≅ {j = j} H e (suc m) = ψˢᶠ-≅ H (≅ᴵ-refl j) (i-respˢ e (chainSᶠ-≅ H e m))

fold1Sᶠ : ∀ {φ} {S : Stkᶠ φ} {i k ℓ j} {z : Simᴵ (Fᶠ φ) ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
         (i ≺ᴵ j) ⊎ (i ≅ᴵ j) →
         ψˢᶠ S z p σ (Ord₊ˢ.limᵢ q f) ≡ Ord₊ˢ.lim (λ m → ψˢᶠ S z p σ (f (intoˢ (<→◃ q) (chainSᶠ S z σ q f m))))
fold1Sᶠ {p = p} {σ = σ} {q = q} h with <ᴵ-dec (σ q) p
... | injᵃ s = ⊥-elim (clash s h)
... | injᵇ _ = refl
... | injᶜ _ = refl

pen1Sᶠ : ∀ {φ} {S : Stkᶠ φ} {i k ℓ j N} {z : Simᴵ (Fᶠ φ) ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
        j ≅ᴵ N → N ≺ᴵ i →
        Σ Ordᴵ λ j′ → Σ (j ≅ᴵ j′) λ e → Σ (j′ <ᴵ i) λ r →
        ψˢᶠ S z p σ (Ord₊ˢ.limᵢ q f) ≡ Ord₊ˢ.limᵢ r (λ y → ψˢᶠ S z p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) y)))))
pen1Sᶠ {p = p} {σ = σ} {q = q} ej νi with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = _ , e , r , refl
... | injᵇ s = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ (≺ᴵ-trans νi s) ej))
... | injᶜ c = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ νi (≅ᴵ-trans (≅ᴵ-sym c) ej)))

HypWᶠ : ∀ {φ} → Stkᶠ φ → T → Set
HypWᶠ {φ} S ps = ∀ {i ℓ w} (z : Simᴵ (Fᶠ φ) ℓ) (p : i <ᴵ ℓ) (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
            LabL₊ i Ll (run S z p) (ψᵗ w ps ∷ [])

module PreWᶠ {φ : Flr} (S : Stkᶠ φ) (ps : T) (H : HypWᶠ S ps) where

  giPreS : ∀ {k ℓ i w ν j y ys} {z : Simᴵ (Fᶠ φ) ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
           (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
           (rec : ∀ η (x : Ordˢ j) → LabL x η → LabL₊ i Ll (ψˢᶠ S z p σ (f (intoˢ (<→◃ q) x))) (πw w ps (fsT (y ∷ ys) η))) →
           (recC : kd j ≡ false → ∀ η (x : Ordˢ j) → LabL x η →
                   LabL₊ j Ll (ψˢᶠ S z (σ q) σ (f (intoˢ (<→◃ q) x))) (πw ν ps (fsT (y ∷ ys) η))) →
           LabL₊ i Ll (ψˢᶠ S z p σ (Ord₊ˢ.limᵢ q f)) (πw w ps (y ∷ ys))
  giPreS {i = i} {w = w} {ν = ν} {j = j} {y = y} {ys = ys} {z = z} {p = p} {σ = σ} {q = q} {f = f} Iw ei ki c Iν ej rec recC =
    go (cmpᵀ (sucT ν) w) refl
    where
    pen : Pen (cmpᵀ (sucT ν) w) → LabL₊ i Ll (ψˢᶠ S z p σ (Ord₊ˢ.limᵢ q f)) (πw w ps (y ∷ ys))
    pen pn with pen1Sᶠ {S = S} {z = z} {p = p} {σ = σ} {q = q} {f = f} (≅ᴵ-refl j)
                      (≺ᴵ-respʳ (≺ᴵ-respˡ ej (Ilt Iν Iw (pen→< ν w pn))) (≅ᴵ-sym ei))
    ... | j′ , e , r , eqn =
      subst (λ W → LabL₊ i Ll W (πw w ps (y ∷ ys))) (sym eqn)
            (gi cofE Iν (≅ᴵ-trans (≅ᴵ-sym e) ej)
                (λ η x l → subst (λ v → LabL₊ i Ll (ψˢᶠ S z p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e v)))) (fsT (πw w ps (y ∷ ys)) η))
                                 (sym (out-intoˢ (<→◃ r) x))
                                 (subst (LabL₊ i Ll _) (sym (penW w ps y ys ν c pn η))
                                        (rec η (tr⁻ˢ e x) (LabL-tr⁻ e (Ll→ (<→◃ r) l))))))
      where
      cofE : cof (πw w ps (y ∷ ys)) ≡ cΩ ν
      cofE = trans (cofW w ps y ys) (trans (cong (cofA w) c) (cofP pn))
    fold : cmpᵀ (sucT ν) w ≡ gt → LabL₊ i Ll (ψˢᶠ S z p σ (Ord₊ˢ.limᵢ q f)) (πw w ps (y ∷ ys))
    fold em =
      subst (λ W → LabL₊ i Ll W (πw w ps (y ∷ ys))) (sym (fold1Sᶠ {S = S} {z = z} {p = p} {σ = σ} {q = q} {f = f} ij))
            (gl (trans (cofW w ps y ys) (trans (cong (cofA w) c) (cong (cofψ₊ w ν) em)))
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
      chainL : ∀ m → LabL (chainSᶠ S z σ q f m) (γW ps (y ∷ ys) ν m)
      chainL zero    = LabL-Ω (proj₁ Iν) (proj₁ (proj₂ Iν)) (proj₁ (proj₂ (proj₂ Iν))) (proj₂ (proj₂ (proj₂ Iν))) ej
      chainL (suc m) = frL₊ kj (recC kj _ _ (chainL m))
    go : ∀ m → cmpᵀ (sucT ν) w ≡ m → LabL₊ i Ll (ψˢᶠ S z p σ (Ord₊ˢ.limᵢ q f)) (πw w ps (y ∷ ys))
    go lt em = pen (inj₁ em)
    go eq em = pen (inj₂ em)
    go gt em = fold em

  popW : ∀ {i ℓ w} {z : Simᴵ (Fᶠ φ) ℓ} {p : i <ᴵ ℓ} (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
         LabL₊ i Ll (run S z p) (πw w ps [])
  popW {i = i} {w = w} {z = z} {p = p} Iw ei ki =
    subst (λ t → LabL₊ i Ll (run S z p) (ψᵗ w t ∷ [])) (sym (++-identityʳ ps)) (H z p Iw ei ki)

  PreAS : ∀ {ℓ i w} {z : Simᴵ (Fᶠ φ) ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ zero ℓ} {X : Ordˢ zero} {b} →
          (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → Lab0ᴸ X b → LabL₊ i Ll (ψˢᶠ S z p σ X) (πw w ps b)
  PreVS : ∀ {k ℓ i w} {z : Simᴵ (Fᶠ φ) ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {X : Ordˢ k} {b} →
          (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → LabL X b → LabL₊ i Ll (ψˢᶠ S z p σ X) (πw w ps b)
  PreS₊ : ∀ {k ℓ i w} {z : Simᴵ (Fᶠ φ) ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {X : Ordˢ k} {b} →
          (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → LabL₊ k Ll X b → LabL₊ i Ll (ψˢᶠ S z p σ X) (πw w ps b)

  PreAS {z = z} {p = p} {b = []} Iw ei ki (lz c) = popW {z = z} {p = p} Iw ei ki
  PreAS {b = y ∷ ys} Iw ei ki (lz c) = ⊥-elim (cof-ne y ys c)
  PreAS {b = []} Iw ei ki (ls () l)
  PreAS {w = w} {z = z} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (ls c l) =
    gl (trans (cofW w ps y ys) (cong (cofA w) c))
       (λ m → subst (LabL₊ _ Ll _) (sym (repW w ps y ys c m)) (LRep ki (PreAS {z = z} {p = p} {σ = σ} Iw ei ki l) m))
  PreAS {b = []} Iw ei ki (ll () h)
  PreAS {w = w} {z = z} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (ll c h) =
    gl (trans (cofW w ps y ys) (cong (cofA w) c))
       (λ m → subst (LabL₊ _ Ll _) (sym (ωW w ps y ys c m)) (PreAS {z = z} {p = p} {σ = σ} Iw ei ki (h m)))
  PreAS {b = []} Iw ei ki (lŝ₀ () K h₀ hk)
  PreAS {w = w} {z = z} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (lŝ₀ c K h₀ hk) =
    gĉ (trans (cofW w ps y ys) (cong (cofA w) c)) K
       (subst (LabL₊ _ Ll _) (sym (ωW w ps y ys c 0)) (PreAS {z = z} {p = p} {σ = σ} Iw ei ki h₀))
       (λ m → subst (LabL₊ _ Ll _) (sym (ωW w ps y ys c (suc m))) (PreAS {z = z} {p = p} {σ = σ} Iw ei ki (hk m)))
  PreAS {b = []} Iw ei ki (lĉ () K h₀ hk)
  PreAS {w = w} {z = z} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (lĉ c K h₀ hk) =
    gĉ (trans (cofW w ps y ys) (cong (cofA w) c)) K
       (subst (LabL₊ _ Ll _) (sym (ωW w ps y ys c 0)) (PreAS {z = z} {p = p} {σ = σ} Iw ei ki h₀))
       (λ m → subst (LabL₊ _ Ll _) (sym (ωW w ps y ys c (suc m))) (PreAS {z = z} {p = p} {σ = σ} Iw ei ki (hk m)))

  PreVS {k = zero}    {z = z} {p = p} {σ = σ} Iw ei ki at = PreAS {z = z} {p = p} {σ = σ} Iw ei ki (atomL at)
  PreVS {k = suc _}   {z = z} {p = p} {σ = σ} Iw ei ki h  = PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki h
  PreVS {k = lim _ _} {z = z} {p = p} {σ = σ} Iw ei ki h  = PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki h

  PreS₊ {z = z} {p = p} {b = []} Iw ei ki (gz c) = popW {z = z} {p = p} Iw ei ki
  PreS₊ {b = y ∷ ys} Iw ei ki (gz c) = ⊥-elim (cof-ne y ys c)
  PreS₊ {b = []} Iw ei ki (gs () l)
  PreS₊ {w = w} {z = z} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gs c l) =
    gl (trans (cofW w ps y ys) (cong (cofA w) c))
       (λ m → subst (LabL₊ _ Ll _) (sym (repW w ps y ys c m)) (LRep ki (PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki l) m))
  PreS₊ {b = []} Iw ei ki (gl () h)
  PreS₊ {w = w} {z = z} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gl c h) =
    gl (trans (cofW w ps y ys) (cong (cofA w) c))
       (λ m → subst (LabL₊ _ Ll _) (sym (ωW w ps y ys c m)) (PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki (h m)))
  PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki (gu {r = zero} h)   = PreVS {z = z} {p = p} {σ = λ q → σ (suc q)} Iw ei ki h
  PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki (gu {r = self m} h) = PreVS {z = z} {p = p} {σ = λ q → σ (lim m q)} Iw ei ki h
  PreS₊ {b = []} Iw ei ki (gi () Iν ej h)
  PreS₊ {z = z} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gi {q = q} {f = f} c Iν ej h) =
    giPreS {z = z} {p = p} {σ = σ} {q = q} {f = f} Iw ei ki c Iν ej
           (λ η x l → PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki (h η x (→Ll (<→◃ q) l)))
           (λ kj η x l → PreS₊ {z = z} {p = σ q} {σ = σ} Iν ej kj (h η x (→Ll (<→◃ q) l)))
  PreS₊ {b = []} Iw ei ki (gĉ () K h₀ hk)
  PreS₊ {w = w} {z = z} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gĉ c K h₀ hk) =
    gĉ (trans (cofW w ps y ys) (cong (cofA w) c)) K
       (subst (LabL₊ _ Ll _) (sym (ωW w ps y ys c 0)) (PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki h₀))
       (λ m → subst (LabL₊ _ Ll _) (sym (ωW w ps y ys c (suc m))) (PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki (hk m)))
  PreS₊ {k = zero} Iw ei ki (gŝ () c Ib bb ob h₀ hg)
  PreS₊ {k = suc _} {w = []} Iw ei ki (gŝ kk c Ib bb ob h₀ hg) = ⊥-elim (ne-w Iw ei ki refl)
  PreS₊ {k = suc _} {w = x ∷ xs} {b = []} Iw ei ki (gŝ kk () Ib bb ob h₀ hg)
  PreS₊ {k = suc _} {w = x ∷ xs} {z = z} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gŝ kk c Ib bb ob h₀ hg) =
    gŝ ki (trans (cofW (x ∷ xs) ps y ys) (trans (cong (cofA (x ∷ xs)) c) (H1-pen x xs))) Ib bb
       (λ θ → subst (Occ _) (sym (H1W x xs ps y ys c θ)) (od (OccΣ ps (ob θ))))
       (subst (LabL₊ _ Ll _) (sym (H1W x xs ps y ys c (natT 1))) (PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki h₀))
       (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (H1W x xs ps y ys c θ))
                                    (PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki (hg θ Y hY lY nθ lt e)))
  PreS₊ {k = lim _ _} {w = []} Iw ei ki (gŝ kk c Ib bb ob h₀ hg) = ⊥-elim (ne-w Iw ei ki refl)
  PreS₊ {k = lim _ _} {w = x ∷ xs} {b = []} Iw ei ki (gŝ kk () Ib bb ob h₀ hg)
  PreS₊ {k = lim _ _} {w = x ∷ xs} {z = z} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gŝ kk c Ib bb ob h₀ hg) =
    gŝ ki (trans (cofW (x ∷ xs) ps y ys) (trans (cong (cofA (x ∷ xs)) c) (H1-pen x xs))) Ib bb
       (λ θ → subst (Occ _) (sym (H1W x xs ps y ys c θ)) (od (OccΣ ps (ob θ))))
       (subst (LabL₊ _ Ll _) (sym (H1W x xs ps y ys c (natT 1))) (PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki h₀))
       (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (H1W x xs ps y ys c θ))
                                    (PreS₊ {z = z} {p = p} {σ = σ} Iw ei ki (hg θ Y hY lY nθ lt e)))
```

**读法.** `PreWᶠ` 是目标 $w\ne0$ 的部分 (`giPreS`/`popW`/`PreAS`/`PreVS`/`PreS₊`), 只用假设 `HypWᶠ`. 下面的 `Pre0ᶠ` 是目标 $0$ 的部分 (证书与标签一起), 另用 `Hyp0ᶠ` 与栈的自互模拟; `domS`/`1<γ` 导入.

```agda
Hyp0ᶠ : ∀ {φ} → Stkᶠ φ → T → Set
Hyp0ᶠ {φ} S ps = ∀ {L} (z : Simᴵ (Fᶠ φ) L) (p : zero <ᴵ L) → NF₁ (ψᵗ [] ps ∷ []) →
            Σ (Goodᴸ (toZ (run S z p))) λ G → Lab (forceᴸ _ G) (ψᵗ [] ps ∷ [])

module Pre0ᶠ {φ : Flr} (S : Stkᶠ φ) (ps : T) (HW : HypWᶠ S ps) (H0 : Hyp0ᶠ S ps) (HR : S ≈ᶠ S) where
  open PreWᶠ S ps HW

  cofω : ∀ {y ys} → cof (y ∷ ys) ≡ cΩ [] → cof (πw [] ps (y ∷ ys)) ≡ cω
  cofω {y} {ys} c = trans (cofW [] ps y ys) (cong (cofA []) c)

  cofω′ : ∀ {y ys} → cof (y ∷ ys) ≡ cω → cof (πw [] ps (y ∷ ys)) ≡ cω
  cofω′ {y} {ys} c = trans (cofW [] ps y ys) (cong (cofA []) c)

  nfγ : ∀ {y ys} → NF₁ (πw [] ps (y ∷ ys)) → (c : cof (y ∷ ys) ≡ cΩ []) → ∀ m →
        NF₁ (πw [] ps (fsT (y ∷ ys) (γW ps (y ∷ ys) [] m)))
  nfγ {y} {ys} nu c m = subst NF₁ (gtW [] ps y ys [] c refl m) (NF₁-fsn nu (cofω c) m)

  nfω : ∀ {y ys} → NF₁ (πw [] ps (y ∷ ys)) → (c : cof (y ∷ ys) ≡ cω) → ∀ m → NF₁ (πw [] ps (fsn (y ∷ ys) m))
  nfω {y} {ys} nu c m = subst NF₁ (ωW [] ps y ys c m) (NF₁-fsn nu (cofω′ c) m)

  liLabS : ∀ {L k} {z : Simᴵ (Fᶠ φ) L} {p : zero <ᴵ L} {σ : Simᴵ k L} {q : zero <ᴵ k} {f : Uˢ zero (<→◃ q) → Ordˢ k} {y ys} →
           cof (y ∷ ys) ≡ cΩ [] → Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → NF₁ (πw [] ps (y ∷ ys)) →
           (rec : ∀ (p′ : zero <ᴵ L) θ (x : Ordˢ zero) → Atomᴸ x θ → f (intoˢ (<→◃ q) x) ≅ˢ f (intoˢ (<→◃ q) x) →
                  NF₁ (πw [] ps (fsT (y ∷ ys) θ)) →
                  Σ (Goodᴸ (toZ (ψˢᶠ S z p′ σ (f (intoˢ (<→◃ q) x))))) λ G → Lab (forceᴸ _ G) (πw [] ps (fsT (y ∷ ys) θ))) →
           Σ (Goodᴸ (toZ (ψˢᶠ S z p σ (Ord₊ˢ.limᵢ q f)))) λ G → Lab (forceᴸ _ G) (πw [] ps (y ∷ ys))
  liLabS {z = z} {p = p} {σ = σ} {q = q} {f = f} {y = y} {ys = ys} c ex nu rec =
    subst (λ W → Σ (Goodᴸ (toZ W)) λ G → Lab (forceᴸ _ G) (πw [] ps (y ∷ ys))) (sym eqf)
          (limᴸ nu (cofω c) (λ m → proj₁ (outp m))
                (λ m → subst (Lab _) (sym (gtW [] ps y ys [] c refl m)) (proj₂ (outp m))))
    where
    eqf = fold1Sᶠ {S = S} {z = z} {p = p} {σ = σ} {q = q} {f = f} (inj₂ z≅)
    atm : ∀ m → Atomᴸ (chainSᶠ S z σ q f m) (γW ps (y ∷ ys) [] m)
    atm zero    = Ωˢ-refl zero , gs gz , l1 refl (s≅ z≅) (l0 refl z≅)
    atm (suc m) = ψˢᶠ-≅ HR {z = z} {p = σ q} {σ = σ} {z′ = z} {p′ = σ q} {σ′ = σ} z≅ (i-respˢ ex (proj₁ (atm m))) ,
                  rec (σ q) _ _ (atm m) (i-respˢ ex (proj₁ (atm m))) (nfγ nu c m)
    outp : ∀ m → Σ (Goodᴸ (toZ (ψˢᶠ S z p σ (f (intoˢ (<→◃ q) (chainSᶠ S z σ q f m)))))) λ G →
                Lab (forceᴸ _ G) (πw [] ps (fsT (y ∷ ys) (γW ps (y ∷ ys) [] m)))
    outp m = rec p _ _ (atm m) (i-respˢ ex (proj₁ (atm m))) (nfγ nu c m)

  foldLabS : ∀ {L k j y ys v vs} {z : Simᴵ (Fᶠ φ) L} {p : zero <ᴵ L} {σ : Simᴵ k L} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
             cof (y ∷ ys) ≡ cΩ (v ∷ vs) → (I : Idx (v ∷ vs)) → j ≅ᴵ lvI I → kd j ≡ false →
             Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → NF₁ (πw [] ps (y ∷ ys)) →
             (h : ∀ η (x : Ordˢ j) → LabL x η → LabL₊ k Ll (f (intoˢ (<→◃ q) x)) (fsT (y ∷ ys) η)) →
             (rec : ∀ η (x : Ordˢ j) → LabL x η → f (intoˢ (<→◃ q) x) ≅ˢ f (intoˢ (<→◃ q) x) →
                    NF₁ (πw [] ps (fsT (y ∷ ys) η)) →
                    Σ (Goodᴸ (toZ (ψˢᶠ S z p σ (f (intoˢ (<→◃ q) x))))) λ G → Lab (forceᴸ _ G) (πw [] ps (fsT (y ∷ ys) η))) →
             Σ (Goodᴸ (toZ (ψˢᶠ S z p σ (Ord₊ˢ.limᵢ q f)))) λ G → Lab (forceᴸ _ G) (πw [] ps (y ∷ ys))
  foldLabS {y = y} {ys = ys} {v = v} {vs = vs} {z = z} {p = p} {σ = σ} {q = q} {f = f} c I ej kj ex nu h rec =
    subst (λ W → Σ (Goodᴸ (toZ W)) λ G → Lab (forceᴸ _ G) (πw [] ps (y ∷ ys))) (sym eqf)
          (limᴸ nu cω′ (λ m → proj₁ (outp m))
                (λ m → subst (Lab _) (sym (gtW [] ps y ys (v ∷ vs) c refl m)) (proj₂ (outp m))))
    where
    cω′ : cof (πw [] ps (y ∷ ys)) ≡ cω
    cω′ = trans (cofW [] ps y ys) (cong (cofA []) c)
    eqf = fold1Sᶠ {S = S} {z = z} {p = p} {σ = σ} {q = q} {f = f} (inj₁ (z≺I I ej (λ ())))
    chainL : ∀ m → LabL (chainSᶠ S z σ q f m) (γW ps (y ∷ ys) (v ∷ vs) m)
    chainL zero    = LabL-Ω (proj₁ I) (proj₁ (proj₂ I)) (proj₁ (proj₂ (proj₂ I))) (proj₂ (proj₂ (proj₂ I))) ej
    chainL (suc m) = frL₊ kj (PreS₊ {z = z} {p = σ q} {σ = σ} I ej kj (h _ _ (chainL m)))
    nf : ∀ m → NF₁ (πw [] ps (fsT (y ∷ ys) (γW ps (y ∷ ys) (v ∷ vs) m)))
    nf m = subst NF₁ (gtW [] ps y ys (v ∷ vs) c refl m) (NF₁-fsn nu cω′ m)
    outp : ∀ m → Σ (Goodᴸ (toZ (ψˢᶠ S z p σ (f (intoˢ (<→◃ q) (chainSᶠ S z σ q f m)))))) λ G →
                Lab (forceᴸ _ G) (πw [] ps (fsT (y ∷ ys) (γW ps (y ∷ ys) (v ∷ vs) m)))
    outp m = rec _ _ (chainL m) (i-respˢ ex (chainSᶠ-≅ HR ex m)) (nf m)

  ŝChainS : ∀ {L k c w} {z : Simᴵ (Fᶠ φ) L} {p : zero <ᴵ L} {σ : Simᴵ k L} {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} {y ys} →
            cof (y ∷ ys) ≡ cΩ [] → NF₁ (πw [] ps (y ∷ ys)) → (Iw : Idx w) → c ⊑ᴵ suc (lvI Iw) → (∀ θ → Occ w (fsT (y ∷ ys) θ)) →
            (rec₀ : Σ (Goodᴸ (toZ (ψˢᶠ S z p σ t₀))) λ G → Lab (forceᴸ _ G) (γW ps (y ∷ ys) [] 1)) →
            (rec : ∀ m Y (hY : HS Y) → Lab Y (γW ps (y ∷ ys) [] (suc m)) → (e : c ⊑ᴵ toLevel Y hY) →
                   Σ (Goodᴸ (toZ (ψˢᶠ S z p σ (g (toLevel Y hY) e)))) λ G → Lab (forceᴸ _ G) (γW ps (y ∷ ys) [] (suc (suc m)))) →
            Σ (Goodᴸ (ĉᴸ c (toZ (ψˢᶠ S z p σ t₀)) (λ η e → toZ (ψˢᶠ S z p σ (g η e)))
                           (toZ (ψˢᶠ S z p σ t₀)) (λ η e → toZ (ψˢᶠ S z p σ (g η e))))) λ G →
              Lab (forceᴸ _ G) (πw [] ps (y ∷ ys))
  ŝChainS {y = y} {ys = ys} c nu Iw bw ow rec₀ rec =
    ĉᴸ-mk nu (cofω c) K (proj₁ rec₀) (subst (Lab _) (sym (gtW [] ps y ys [] c refl 0)) (proj₂ rec₀))
          (λ k → CCᴸ.Gg K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k)))
          (λ k → subst (Lab _) (sym (gtW [] ps y ys [] c refl (suc k)))
                       (CCᴸ.lE K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k))))
    where
    K = ccᴸ (λ m → γW ps (y ∷ ys) [] (suc m)) (proj₁ rec₀) (proj₂ rec₀)
            (domS ps _ Iw bw (ow (natT 1)) (proj₂ rec₀) (nfγ nu c 0))
            (λ m Y hY lY e → proj₁ (rec m Y hY lY e)) (λ m Y hY lY e → proj₂ (rec m Y hY lY e))
            (λ m Y hY lY e → domS ps _ Iw bw (ow (γW ps (y ∷ ys) [] (suc m))) (proj₂ (rec m Y hY lY e)) (nfγ nu c (suc m)))

  pop0 : ∀ {L} {z : Simᴵ (Fᶠ φ) L} {p : zero <ᴵ L} → NF₁ (πw [] ps []) → Σ (Goodᴸ (toZ (run S z p))) λ G → Lab (forceᴸ _ G) (πw [] ps [])
  pop0 {z = z} {p = p} nu =
    subst (λ t → Σ (Goodᴸ (toZ (run S z p))) λ G → Lab (forceᴸ _ G) (ψᵗ [] t ∷ [])) (sym (++-identityʳ ps))
          (H0 z p (subst (λ t → NF₁ (ψᵗ [] t ∷ [])) (++-identityʳ ps) nu))

  Pre0AS : ∀ {L} {z : Simᴵ (Fᶠ φ) L} {p : zero <ᴵ L} {σ : Simᴵ zero L} {x : Ordˢ zero} {a} →
           Lab0ᴸ x a → x ≅ˢ x → NF₁ (πw [] ps a) → Σ (Goodᴸ (toZ (ψˢᶠ S z p σ x))) λ G → Lab (forceᴸ _ G) (πw [] ps a)
  Pre0VS : ∀ {L k} {z : Simᴵ (Fᶠ φ) L} {p : zero <ᴵ L} {σ : Simᴵ k L} {x : Ordˢ k} {a} →
           LabL x a → x ≅ˢ x → NF₁ (πw [] ps a) → Σ (Goodᴸ (toZ (ψˢᶠ S z p σ x))) λ G → Lab (forceᴸ _ G) (πw [] ps a)
  Pre0S₊ : ∀ {L k} {z : Simᴵ (Fᶠ φ) L} {p : zero <ᴵ L} {σ : Simᴵ k L} {x : Ordˢ k} {a} →
           LabL₊ k Ll x a → x ≅ˢ x → NF₁ (πw [] ps a) → Σ (Goodᴸ (toZ (ψˢᶠ S z p σ x))) λ G → Lab (forceᴸ _ G) (πw [] ps a)

  Pre0AS {z = z} {p = p} {a = []} (lz c) ex nu = pop0 {z = z} {p = p} nu
  Pre0AS {a = y ∷ ys} (lz c) ex nu = ⊥-elim (cof-ne y ys c)
  Pre0AS {a = []} (ls () l) ex nu
  Pre0AS {z = z} {p = p} {σ = σ} {a = y ∷ ys} (ls c l) ex nu =
    limᴸ nu cω′ (λ m → proj₁ (Rs m)) (λ m → subst (Lab _) (sym (repW [] ps y ys c m)) (proj₂ (Rs m)))
    where
    cω′ = trans (cofW [] ps y ys) (cong (cofA []) c)
    Rp = Pre0AS {z = z} {p = p} {σ = σ} l (s-invˢ ex) (subst NF₁ (repW [] ps y ys c 1) (NF₁-fsn nu cω′ 1))
    Rs = repᴸ (proj₁ Rp) (proj₂ Rp) (λ m → subst NF₁ (repW [] ps y ys c m) (NF₁-fsn nu cω′ m))
  Pre0AS {a = []} (ll () h) ex nu
  Pre0AS {z = z} {p = p} {σ = σ} {a = y ∷ ys} (ll c h) ex nu =
    limᴸ nu (cofω′ c)
         (λ m → proj₁ (Pre0AS {z = z} {p = p} {σ = σ} (h m) (l-invˢ ex m) (nfω nu c m)))
         (λ m → subst (Lab _) (sym (ωW [] ps y ys c m)) (proj₂ (Pre0AS {z = z} {p = p} {σ = σ} (h m) (l-invˢ ex m) (nfω nu c m))))
  Pre0AS {a = []} (lŝ₀ () K h₀ hk) ex nu
  Pre0AS {z = z} {p = p} {σ = σ} {a = y ∷ ys} (lŝ₀ c K h₀ hk) ex nu =
    ĉᴸ-mk nu (cofω′ c) K (proj₁ R₀) (subst (Lab _) (sym (ωW [] ps y ys c 0)) (proj₂ R₀))
          (λ k → proj₁ (Rk k)) (λ k → subst (Lab _) (sym (ωW [] ps y ys c (suc k))) (proj₂ (Rk k)))
    where
    R₀ = Pre0AS {z = z} {p = p} {σ = σ} h₀ (ŝ-refl₀ ex) (nfω nu c 0)
    Rk = λ k → Pre0AS {z = z} {p = p} {σ = σ} (hk k) (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) (nfω nu c (suc k))
  Pre0AS {a = []} (lĉ () K h₀ hk) ex nu
  Pre0AS {z = z} {p = p} {σ = σ} {a = y ∷ ys} (lĉ c K h₀ hk) ex nu =
    ĉᴸ-mk nu (cofω′ c) K (proj₁ R₀) (subst (Lab _) (sym (ωW [] ps y ys c 0)) (proj₂ R₀))
          (λ k → proj₁ (Rk k)) (λ k → subst (Lab _) (sym (ωW [] ps y ys c (suc k))) (proj₂ (Rk k)))
    where
    R₀ = Pre0AS {z = z} {p = p} {σ = σ} h₀ (ĉ-refl₀ ex) (nfω nu c 0)
    Rk = λ k → Pre0AS {z = z} {p = p} {σ = σ} (hk k) (ĉ-reflg ex _ _) (nfω nu c (suc k))

  Pre0VS {k = zero}    {z = z} {p = p} {σ = σ} at ex nu = Pre0AS {z = z} {p = p} {σ = σ} (atomL at) ex nu
  Pre0VS {k = suc _}   {z = z} {p = p} {σ = σ} h  ex nu = Pre0S₊ {z = z} {p = p} {σ = σ} h ex nu
  Pre0VS {k = lim _ _} {z = z} {p = p} {σ = σ} h  ex nu = Pre0S₊ {z = z} {p = p} {σ = σ} h ex nu

  Pre0S₊ {z = z} {p = p} {a = []} (gz c) ex nu = pop0 {z = z} {p = p} nu
  Pre0S₊ {a = y ∷ ys} (gz c) ex nu = ⊥-elim (cof-ne y ys c)
  Pre0S₊ {a = []} (gs () l) ex nu
  Pre0S₊ {z = z} {p = p} {σ = σ} {a = y ∷ ys} (gs c l) ex nu =
    limᴸ nu cω′ (λ m → proj₁ (Rs m)) (λ m → subst (Lab _) (sym (repW [] ps y ys c m)) (proj₂ (Rs m)))
    where
    cω′ = trans (cofW [] ps y ys) (cong (cofA []) c)
    Rp = Pre0S₊ {z = z} {p = p} {σ = σ} l (s-invˢ ex) (subst NF₁ (repW [] ps y ys c 1) (NF₁-fsn nu cω′ 1))
    Rs = repᴸ (proj₁ Rp) (proj₂ Rp) (λ m → subst NF₁ (repW [] ps y ys c m) (NF₁-fsn nu cω′ m))
  Pre0S₊ {a = []} (gl () h) ex nu
  Pre0S₊ {z = z} {p = p} {σ = σ} {a = y ∷ ys} (gl c h) ex nu =
    limᴸ nu (cofω′ c)
         (λ m → proj₁ (Pre0S₊ {z = z} {p = p} {σ = σ} (h m) (l-invˢ ex m) (nfω nu c m)))
         (λ m → subst (Lab _) (sym (ωW [] ps y ys c m)) (proj₂ (Pre0S₊ {z = z} {p = p} {σ = σ} (h m) (l-invˢ ex m) (nfω nu c m))))
  Pre0S₊ {z = z} {p = p} {σ = σ} (gu {r = zero} l) ex nu =
    Pre0VS {z = z} {p = p} {σ = λ q → σ (suc q)} l (u-reflˢ zero ex) nu
  Pre0S₊ {z = z} {p = p} {σ = σ} (gu {r = self m} l) ex nu =
    Pre0VS {z = z} {p = p} {σ = λ q → σ (lim m q)} l (u-reflˢ (self m) ex) nu
  Pre0S₊ {a = []} (gi () I ej h) ex nu
  Pre0S₊ {z = z} {p = p} {σ = σ} {a = y ∷ ys} (gi {j = zero} {q = q} {f = f} c I ej h) ex nu =
    liLabS {z = z} {p = p} {σ = σ} {q = q} {f = f} (trans c (cong cΩ (kdI I (sym (kd-≅ ej))))) ex nu
           (λ p′ θ x at br nf → Pre0S₊ {z = z} {p = p′} {σ = σ} (h θ x (→Ll (<→◃ q) at)) br nf)
  Pre0S₊ {a = y ∷ ys} (gi {ν = []} {j = suc _} c I ej h) ex nu = ⊥-elim (tf (trans (sym (kdI[] I)) (sym (kd-≅ ej))))
  Pre0S₊ {z = z} {p = p} {σ = σ} {a = y ∷ ys} (gi {ν = v ∷ vs} {j = suc _} {q = q} {f = f} c I ej h) ex nu =
    foldLabS {z = z} {p = p} {σ = σ} {q = q} {f = f} c I ej refl ex nu (λ η x l → h η x (→Ll (<→◃ q) l))
             (λ η x l br nf → Pre0S₊ {z = z} {p = p} {σ = σ} (h η x (→Ll (<→◃ q) l)) br nf)
  Pre0S₊ {a = y ∷ ys} (gi {ν = []} {j = lim _ _} c I ej h) ex nu = ⊥-elim (tf (trans (sym (kdI[] I)) (sym (kd-≅ ej))))
  Pre0S₊ {z = z} {p = p} {σ = σ} {a = y ∷ ys} (gi {ν = v ∷ vs} {j = lim _ _} {q = q} {f = f} c I ej h) ex nu =
    foldLabS {z = z} {p = p} {σ = σ} {q = q} {f = f} c I ej refl ex nu (λ η x l → h η x (→Ll (<→◃ q) l))
             (λ η x l br nf → Pre0S₊ {z = z} {p = p} {σ = σ} (h η x (→Ll (<→◃ q) l)) br nf)
  Pre0S₊ {k = zero} (gŝ () c Iw bw ow h₀ hg) ex nu
  Pre0S₊ {k = suc _} {a = []} (gŝ kk () Iw bw ow h₀ hg) ex nu
  Pre0S₊ {k = suc _} {z = z} {p = p} {σ = σ} {a = y ∷ ys} (gŝ kk c Iw bw ow h₀ hg) ex nu =
    ŝChainS {z = z} {p = p} {σ = σ} c nu Iw bw ow
            (Pre0S₊ {z = z} {p = p} {σ = σ} h₀ (ŝ-refl₀ ex) (nfγ nu c 0))
            (λ m Y hY lY e → Pre0S₊ {z = z} {p = p} {σ = σ} (hg _ Y hY lY (nfγ nu c m) (1<γ ps y ys c m) e)
                                    (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) (nfγ nu c (suc m)))
  Pre0S₊ {k = lim _ _} {a = []} (gŝ kk () Iw bw ow h₀ hg) ex nu
  Pre0S₊ {k = lim _ _} {z = z} {p = p} {σ = σ} {a = y ∷ ys} (gŝ kk c Iw bw ow h₀ hg) ex nu =
    ŝChainS {z = z} {p = p} {σ = σ} c nu Iw bw ow
            (Pre0S₊ {z = z} {p = p} {σ = σ} h₀ (ŝ-refl₀ ex) (nfγ nu c 0))
            (λ m Y hY lY e → Pre0S₊ {z = z} {p = p} {σ = σ} (hg _ Y hY lY (nfγ nu c m) (1<γ ps y ys c m) e)
                                    (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) (nfγ nu c (suc m)))
  Pre0S₊ {a = []} (gĉ () K h₀ hk) ex nu
  Pre0S₊ {z = z} {p = p} {σ = σ} {a = y ∷ ys} (gĉ c K h₀ hk) ex nu =
    ĉᴸ-mk nu (cofω′ c) K (proj₁ R₀) (subst (Lab _) (sym (ωW [] ps y ys c 0)) (proj₂ R₀))
          (λ k → proj₁ (Rk k)) (λ k → subst (Lab _) (sym (ωW [] ps y ys c (suc k))) (proj₂ (Rk k)))
    where
    R₀ = Pre0S₊ {z = z} {p = p} {σ = σ} h₀ (ĉ-refl₀ ex) (nfω nu c 0)
    Rk = λ k → Pre0S₊ {z = z} {p = p} {σ = σ} (hk k) (ĉ-reflg ex _ _) (nfω nu c (suc k))
```

**读法.** 停机与原文相同, 一次通过. 这是本文唯一大段的机械复制; 不能直接实例化 OmegaExpBase 的模块, 因为它的栈类型固定为 `zero <ᴵ ℓ` 的帧证据.

## §6 地板见证与 $\hat\Omega$ 好栈

**地板见证** `FW φ ps`: 要么 $B=0$ (`fw0`), 要么有 `Idx w`、$w$ 作为下标出现在前缀 `ps` 中 (`Occ w ps`)、且 $B\prec\mathtt{lvl}\,w$ 或 $B\cong\mathtt{lvl}\,w$ (`fwI`). `OccPre`: 前缀中的出现在加尾巴后保持. `domP`: `domS` 的 "出现在前缀里" 版本, 同样经 `occ<` 与 `Lab-oc` 把 $c\sqsubseteq\mathtt{lvl}\,w+1$ 变成链点层号的支配. `Goodˢᶠ` = OmegaExpBase `Goodˢ` 的三个字段 + `fwᶠ`.

```agda
data FW (φ : Flr) (ps : T) : Set where
  fw0 : Bᶠ φ ≡ zero → FW φ ps
  fwI : ∀ {w} (Iw : Idx w) → Occ w ps → (Bᶠ φ ≺ᴵ lvI Iw) ⊎ (Bᶠ φ ≅ᴵ lvI Iw) → FW φ ps

OccPre : ∀ {w ps} b → Occ w ps → Occ w (ps ++ b)
OccPre b oh     = oh
OccPre b (od o) = od o
OccPre b (os o) = os o
OccPre b (oτ t) = oτ t
OccPre b (ot o) = ot (OccPre b o)

FW++ : ∀ {φ ps} b → FW φ ps → FW φ (ps ++ b)
FW++ b (fw0 e)       = fw0 e
FW++ b (fwI Iw o bw) = fwI Iw (OccPre b o) bw

sB : ∀ {a b} → (a ≺ᴵ b) ⊎ (a ≅ᴵ b) → suc a ⊑ᴵ suc b
sB (inj₁ (via e r)) = s⊑ e (suc r)
sB (inj₂ e)         = s⊑ e zero

no<0 : ∀ {a b} → b ≡ zero → a <ᴵ b → ⊥
no<0 refl ()

domP : ∀ {c w Y} ps b (hY : HS Y) (Iw : Idx w) → c ⊑ᴵ suc (lvI Iw) → Occ w ps → Lab Y (πw [] ps b) → NF₁ (πw [] ps b) →
       c ⊑ᴵ toLevel Y hY
domP ps b hY (W , hW , lW , nW) bw o lY nb =
  ⊑ᴵ-trans bw (s⊑′ (toLevel-≺ hW hY (Lab-oc lY nb lW nW (occ< nb (c∷ c[]) (od (OccPre b o)) (Lab→Ctbl lW nW)))))

record Goodˢᶠ {φ : Flr} (S : Stkᶠ φ) (ps : T) : Set where
  constructor goodᶠ
  field
    hWᶠ : HypWᶠ S ps
    h0ᶠ : Hyp0ᶠ S ps
    hRᶠ : S ≈ᶠ S
    fwᶠ : FW φ ps
open Goodˢᶠ public

Good∅ᶠ : Goodˢᶠ ∅ᶠ []
Good∅ᶠ = goodᶠ (λ { z p (Y , hY , lY , nY) ei ki → toL₊ ki (LabL-Ω Y hY lY nY ei) })
               (λ z p nf → gs gz , l1 refl (s≅ z≅) (l0 refl z≅))
               ∅-≈ᶠ (fw0 refl)
```

**非紧 $\hat\Omega$ 好栈.** 目标 $w\ne0$ (`PopΩW`, 只用 `HypW` 与地板见证): 界 $i+1$ 时 (`WI`) 与 OmegaExpBase `GoodΩ` 的 `gŝ` 行相同 (地板 = 目标下标 $w$, 出现 `oh`); 界 $F$ 时 (`WF`) `gŝ` 行的地板是 `FW` 里的下标 $w_F$, 界 $F\sqsubseteq\mathtt{lvl}\,w_F+1$ 经 `FBᶠ` 与 `sB`, 出现经 `od (OccPre …)` (下标在前缀里, 也就在每个 $t[\theta]=\psi_w(ps+\Omega_\theta)$ 里). `fw0` 情况与 $i\prec B=0$ 矛盾 (`no<0`). 目标 $0$ (`PopΩ`): 链证书, 界 $1$ 时第 0 点与分支的支配是 `one⊑lab`, 界 $F$ 时是 `domP` (地板下标 $w_F$ 出现于前缀). 第 0 点与分支都由 §5 的 `Pre0VS` 在 `Mlev`/`Mlev3` 环境上标记.

```agda
module PopΩW {φ : Flr} {S : Stkᶠ φ} {ps : T} (HW : HypWᶠ S ps) (FWS : FW φ ps) where
  open PreWᶠ S ps HW

  fsTe : ∀ x xs θ → fsT (πw (x ∷ xs) ps (ΩΩ ∷ [])) θ ≡ πw (x ∷ xs) ps (Ωt θ)
  fsTe x xs θ = H1W x xs ps ΩΩ [] refl θ

  LΩ₁ : LabL (Ωˢ (suc zero)) (Ωt (natT 1))
  LΩ₁ = LabL-Ω one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _)

  WI : ∀ {i w} (fi : Fᶠ φ ⊑ᴵ suc i) (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
       LabL₊ i Ll (popI S fi) (ψᵗ w (ps ++ ΩΩ ∷ []) ∷ [])
  WI {w = []} fi Iw ei ki = ⊥-elim (ne-w Iw ei ki refl)
  WI {i = i} {w = x ∷ xs} fi Iw ei ki =
    gŝ ki (trans (cofW (x ∷ xs) ps ΩΩ []) (H1-pen x xs)) Iw (⊑ᴵ-≅ʳ ⊑ᴵ-refl (s≅ ei))
       (λ θ → subst (Occ (x ∷ xs)) (sym (fsTe x xs θ)) oh)
       (subst (LabL₊ _ Ll _) (sym (fsTe x xs (natT 1)))
              (PreVS {z = λ q → lim 0 q} {p = lim 1 zero} {σ = σ1 (lim 0 (ιz φ))} Iw ei ki LΩ₁))
       (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (fsTe x xs θ))
              (PreVS {z = λ q → lim 0 q} {p = lim 1 zero} {σ = λ q → lim 2 q} Iw ei ki (LabL-Ω Y hY lY nθ (≅ᴵ-refl _))))

  WF : ∀ {i w} (sf : suc i ⊑ᴵ Fᶠ φ) → i ≺ᴵ Bᶠ φ → FW φ ps → (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
       LabL₊ i Ll (popF S sf) (ψᵗ w (ps ++ ΩΩ ∷ []) ∷ [])
  WF sf (via e r) (fw0 b0) Iw ei ki = ⊥-elim (no<0 b0 r)
  WF {w = []} sf ib (fwI IF o bw) Iw ei ki = ⊥-elim (ne-w Iw ei ki refl)
  WF {i = i} {w = x ∷ xs} sf ib (fwI IF o bw) Iw ei ki =
    gŝ ki (trans (cofW (x ∷ xs) ps ΩΩ []) (H1-pen x xs)) IF (⊑ᴵ-trans (FBᶠ φ) (sB bw))
       (λ θ → subst (Occ _) (sym (fsTe x xs θ)) (od (OccPre (Ωt θ) o)))
       (subst (LabL₊ _ Ll _) (sym (fsTe x xs (natT 1)))
              (PreVS {z = λ q → lim 1 q} {p = lim 0 zero} {σ = σ1 (lim 1 (ιz φ))} Iw ei ki LΩ₁))
       (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (fsTe x xs θ))
              (PreVS {z = λ q → lim 1 q} {p = lim 0 zero} {σ = λ q → lim 2 q} Iw ei ki (LabL-Ω Y hY lY nθ (≅ᴵ-refl _))))

  hW′ : HypWᶠ (S ▹Ω̂ᶠ) (ps ++ ΩΩ ∷ [])
  hW′ z p Iw ei ki = go (<ᴵ-dec (z (ιᶠ φ)) p)
    where
    go : ∀ d → LabL₊ _ Ll (popΩ S d) (ψᵗ _ (ps ++ ΩΩ ∷ []) ∷ [])
    go (injᵃ (via e r)) = WI _ Iw ei ki
    go (injᵇ (via e r)) = WF _ (via e r) FWS Iw ei ki
    go (injᶜ e)         = WI _ Iw ei ki


module PopΩ {φ : Flr} {S : Stkᶠ φ} {ps : T} (G : Goodˢᶠ S ps) where
  open PreWᶠ S ps (hWᶠ G)
  open Pre0ᶠ S ps (hWᶠ G) (h0ᶠ G) (hRᶠ G)
  open PopΩW (hWᶠ G) (fwᶠ G) public

  t : T
  t = πw [] ps (ΩΩ ∷ [])
  γs : ℕ → T
  γs j = γW ps (ΩΩ ∷ []) [] (suc j)
  fsγ : ∀ j → fsn t j ≡ γs j
  fsγ j = gtW [] ps ΩΩ [] [] refl refl j
  cofE : cof t ≡ cω
  cofE = cofW [] ps ΩΩ []

  ZI : (fi : Fᶠ φ ⊑ᴵ suc zero) → NF₁ (ψᵗ [] (ps ++ ΩΩ ∷ []) ∷ []) →
       Σ (Goodᴸ (toZ (popI S fi))) λ G′ → Lab (forceᴸ _ G′) (ψᵗ [] (ps ++ ΩΩ ∷ []) ∷ [])
  ZI fi nf =
    ĉᴸ-mk nf cofE K (proj₁ R₀) (subst (Lab _) (sym (fsγ 0)) (proj₂ R₀))
          (λ k → CCᴸ.Gg K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k)))
          (λ k → subst (Lab _) (sym (fsγ (suc k)))
                       (CCᴸ.lE K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k))))
    where
    nfγs : ∀ j → NF₁ (γs j)
    nfγs j = subst NF₁ (fsγ j) (NF₁-fsn nf cofE j)
    R₀ = Pre0VS {z = λ q → lim 0 q} {p = lim 1 zero} {σ = σ1 (lim 0 (ιz φ))} LΩ₁ (Ωˢ-refl (suc zero)) (nfγs 0)
    Rg : ∀ j Y (hY : HS Y) → Lab Y (γs j) → (e : suc zero ⊑ᴵ toLevel Y hY) →
         Σ (Goodᴸ (toZ (ψˢᶠ S {ℓ = Mlev3 (Fᶠ φ) (suc zero) (toLevel Y hY) fi e} (λ q → lim 0 q) (lim 1 zero) (λ q → lim 2 q)
                            (Ωˢ (toLevel Y hY))))) λ G′ → Lab (forceᴸ _ G′) (γs (suc j))
    Rg j Y hY lY e = Pre0VS {z = λ q → lim 0 q} {p = lim 1 zero} {σ = λ q → lim 2 q}
                            (LabL-Ω Y hY lY (nfγs j) (≅ᴵ-refl _)) (Ωˢ-refl _) (nfγs (suc j))
    K = ccᴸ γs (proj₁ R₀) (proj₂ R₀) (one⊑lab _ (proj₂ R₀) (nfγs 0) []<)
            (λ j Y hY lY e → proj₁ (Rg j Y hY lY e)) (λ j Y hY lY e → proj₂ (Rg j Y hY lY e))
            (λ j Y hY lY e → one⊑lab _ (proj₂ (Rg j Y hY lY e)) (nfγs (suc j)) []<)

  ZF : (sf : suc zero ⊑ᴵ Fᶠ φ) → zero ≺ᴵ Bᶠ φ → FW φ ps → NF₁ (ψᵗ [] (ps ++ ΩΩ ∷ []) ∷ []) →
       Σ (Goodᴸ (toZ (popF S sf))) λ G′ → Lab (forceᴸ _ G′) (ψᵗ [] (ps ++ ΩΩ ∷ []) ∷ [])
  ZF sf (via e r) (fw0 b0) nf = ⊥-elim (no<0 b0 r)
  ZF sf ib (fwI IF o bw) nf =
    ĉᴸ-mk nf cofE K (proj₁ R₀) (subst (Lab _) (sym (fsγ 0)) (proj₂ R₀))
          (λ k → CCᴸ.Gg K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k)))
          (λ k → subst (Lab _) (sym (fsγ (suc k)))
                       (CCᴸ.lE K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k))))
    where
    bF : Fᶠ φ ⊑ᴵ suc (lvI IF)
    bF = ⊑ᴵ-trans (FBᶠ φ) (sB bw)
    nfγs : ∀ j → NF₁ (γs j)
    nfγs j = subst NF₁ (fsγ j) (NF₁-fsn nf cofE j)
    R₀ = Pre0VS {z = λ q → lim 1 q} {p = lim 0 zero} {σ = σ1 (lim 1 (ιz φ))} LΩ₁ (Ωˢ-refl (suc zero)) (nfγs 0)
    Rg : ∀ j Y (hY : HS Y) → Lab Y (γs j) → (e : Fᶠ φ ⊑ᴵ toLevel Y hY) →
         Σ (Goodᴸ (toZ (ψˢᶠ S {ℓ = Mlev3 (suc zero) (Fᶠ φ) (toLevel Y hY) sf e} (λ q → lim 1 q) (lim 0 zero) (λ q → lim 2 q)
                            (Ωˢ (toLevel Y hY))))) λ G′ → Lab (forceᴸ _ G′) (γs (suc j))
    Rg j Y hY lY e = Pre0VS {z = λ q → lim 1 q} {p = lim 0 zero} {σ = λ q → lim 2 q}
                            (LabL-Ω Y hY lY (nfγs j) (≅ᴵ-refl _)) (Ωˢ-refl _) (nfγs (suc j))
    K = ccᴸ γs (proj₁ R₀) (proj₂ R₀) (domP ps (Ωt (Ωt [])) _ IF bF o (proj₂ R₀) (nfγs 0))
            (λ j Y hY lY e → proj₁ (Rg j Y hY lY e)) (λ j Y hY lY e → proj₂ (Rg j Y hY lY e))
            (λ j Y hY lY e → domP ps (Ωt (γs j)) _ IF bF o (proj₂ (Rg j Y hY lY e)) (nfγs (suc j)))

  h0′ : Hyp0ᶠ (S ▹Ω̂ᶠ) (ps ++ ΩΩ ∷ [])
  h0′ z p nf = go (<ᴵ-dec (z (ιᶠ φ)) p)
    where
    go : ∀ d → Σ (Goodᴸ (toZ (popΩ S d))) λ G′ → Lab (forceᴸ _ G′) (ψᵗ [] (ps ++ ΩΩ ∷ []) ∷ [])
    go (injᵃ (via e r)) = ZI _ nf
    go (injᵇ (via e r)) = ZF _ (via e r) (fwᶠ G) nf
    go (injᶜ e)         = ZI _ nf

GoodΩᶠ : ∀ {φ} {S : Stkᶠ φ} {ps} → Goodˢᶠ S ps → Goodˢᶠ (S ▹Ω̂ᶠ) (ps ++ ΩΩ ∷ [])
GoodΩᶠ G = goodᶠ (PopΩ.hW′ G) (PopΩ.h0′ G) (▹Ω̂ᶠ-≈ (hRᶠ G)) (FW++ (ΩΩ ∷ []) (fwᶠ G))
```

**读法.** `GoodΩᶠ` 不对帧数递归, 与 OmegaExpBase 的 `GoodΩ` 同构; 新增的只有 `WF`/`ZF` 两种情况与它们对 `FW` 的使用. `gŝ` 行、`Goodᴸ`、`gc`、`forceᴸ`、`ĉᴸ-mk`、`ccᴸ` 都没有改动: GoodLBase 的 `gŝ` 地板字段本来就对任意出现于一切 $t[\theta]$ 的带 `Idx` 下标成立, 非紧闭包只是第一次真正用到 "地板不是目标下标" 这种情形.

## §7 第 0、1 层指数 (移植)

OmegaSqBase §4–§7 移植到 `ψᵉᶠ`: `liE`/`ψᵉ′-≅`/`repᴷ-≈`/`▹-≈` (只对 `Lo` 层, 两侧同地板), `chainE`/`fold1E`/`pen1E` (多一个把手参数), 行组合子 `GiE.giPreE`/`LiE.liLabE` (`ŝChainG` 与记号引理 `ψΩ`/`cofΩc`/`fsTΩ`/`cE₁`/… 直接从 OmegaSqBase 导入, 它们不碰栈), `WE₀`/`ZE₀`/`repGood₀`/`GoodE₀` 与 `WE₁`/`ZE₁`/`repGood₁`/`GoodE₁`. 改动: 帧证据类型、把手参数 (`up zero` 处是 `hyes (σ zero)`)、帧写成 `▹[ (λ _ → σ⊥) ∣ (λ _ → hno) ]` 与 `▹[ (λ ζ′ → σ1 (ζ′ (ιz φ))) ∣ (λ _ → hno) ]`, 好栈多 `FW++`. 第 0、1 层的帧不动地板, 所以 `repᶠ` 的第 0 份就是 $S$ 本身 (记录与函数的 η).

```agda
liEᶠ : ∀ {φ} {S S′ : Stkᶠ φ} {i i′ k₁ ℓ₁ k₂ ℓ₂ j j′} {z : Simᴵ (Fᶠ φ) ℓ₁} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁} {hd : Hd k₁ ℓ₁}
      {z′ : Simᴵ (Fᶠ φ) ℓ₂} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂} {hd′ : Hd k₂ ℓ₂}
      {q : j <ᴵ k₁} {q′ : j′ <ᴵ k₂} {f : Uˢ j (<→◃ q) → Ordˢ k₁} {g : Uˢ j′ (<→◃ q′) → Ordˢ k₂} →
      i ≅ᴵ i′ → j ≅ᴵ j′ →
      (∀ (x : Ordˢ j) (y : Ordˢ j′) → Rˢ j (<→◃ q) (intoˢ (<→◃ q) x) y →
         ψᵉᶠ S z p σ hd (f (intoˢ (<→◃ q) x)) ≅ˢ ψᵉᶠ S′ z′ p′ σ′ hd′ (g (intoˢ (<→◃ q′) y))) →
      (∀ (x : Ordˢ j) (y : Ordˢ j′) → Rˢ j (<→◃ q) (intoˢ (<→◃ q) x) y →
         ψᵉᶠ S z (σ q) σ hd (f (intoˢ (<→◃ q) x)) ≅ˢ ψᵉᶠ S′ z′ (σ′ q′) σ′ hd′ (g (intoˢ (<→◃ q′) y))) →
      ψᵉᶠ S z p σ hd (Ord₊ˢ.limᵢ q f) ≅ˢ ψᵉᶠ S′ z′ p′ σ′ hd′ (Ord₊ˢ.limᵢ q′ g)
liEᶠ {S = S} {S′ = S′} {z = z} {p = p} {σ = σ} {hd = hd} {z′ = z′} {p′ = p′} {σ′ = σ′} {hd′ = hd′} {q = q} {q′ = q′} {f = f} {g = g} ei e rec recC
  with <ᴵ-dec (σ q) p | <ᴵ-dec (σ′ q′) p′
... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) = lᵢ≅ (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans e e₂)) λ x y d →
  subst₂ (λ u v → ψᵉᶠ S z p σ hd (f (intoˢ (<→◃ q) (tr⁻ˢ e₁ u))) ≅ˢ ψᵉᶠ S′ z′ p′ σ′ hd′ (g (intoˢ (<→◃ q′) (tr⁻ˢ e₂ v))))
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

ψᵉᶠ-≅ : ∀ {φ} {S S′ : Stkᶠ φ} → S ≈ᶠ S′ → ∀ {i i′ k₁ ℓ₁ k₂ ℓ₂} {z : Simᴵ (Fᶠ φ) ℓ₁} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁} {hd : Hd k₁ ℓ₁}
        {z′ : Simᴵ (Fᶠ φ) ℓ₂} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂} {hd′ : Hd k₂ ℓ₂} {a : Ordˢ k₁} {b : Ordˢ k₂} →
        Lo k₁ → Lo k₂ → i ≅ᴵ i′ → a ≅ˢ b → ψᵉᶠ S z p σ hd a ≅ˢ ψᵉᶠ S′ z′ p′ σ′ hd′ b
repᶠ-≈ : ∀ {φ} {S S′ : Stkᶠ φ} → S ≈ᶠ S′ → ∀ {k₁ k₂} {s : FrS φ k₁} {s′ : FrS φ k₂} {hp : FrH φ k₁} {hp′ : FrH φ k₂}
         {a : Ordˢ k₁} {b : Ordˢ k₂} → Lo k₁ → Lo k₂ → a ≅ˢ b → ∀ m → repᶠ S φ (λ q → q) s hp a m ≈ᶠ repᶠ S′ φ (λ q → q) s′ hp′ b m

ψᵉᶠ-≅ H {z = z} {p = p} {z′ = z′} {p′ = p′} l₁ l₂ ei z≅ = ▹Ω̂ᶠ-≈ H z p z′ p′ ei
ψᵉᶠ-≅ H {z = z} {p = p} {z′ = z′} {p′ = p′} lo0 lo0 ei (s≅ e) = l≅ (λ m → repᶠ-≈ H lo0 lo0 e m z p z′ p′ ei)
ψᵉᶠ-≅ H {z = z} {p = p} {z′ = z′} {p′ = p′} lo0 lo1 ei (s≅ e) = l≅ (λ m → repᶠ-≈ H lo0 lo1 e m z p z′ p′ ei)
ψᵉᶠ-≅ H {z = z} {p = p} {z′ = z′} {p′ = p′} lo1 lo0 ei (s≅ e) = l≅ (λ m → repᶠ-≈ H lo1 lo0 e m z p z′ p′ ei)
ψᵉᶠ-≅ H {z = z} {p = p} {z′ = z′} {p′ = p′} lo1 lo1 ei (s≅ e) = l≅ (λ m → repᶠ-≈ H lo1 lo1 e m z p z′ p′ ei)
ψᵉᶠ-≅ H l₁ l₂ ei (l≅ h) = l≅ (λ n → ψᵉᶠ-≅ H l₁ l₂ ei (h n))
ψᵉᶠ-≅ H lo1 l₂ ei (upˡ {r = zero} e) = ψᵉᶠ-≅ H lo0 l₂ ei e
ψᵉᶠ-≅ H l₁ lo1 ei (upʳ {r = zero} e) = ψᵉᶠ-≅ H l₁ lo0 ei e
ψᵉᶠ-≅ H lo0 lo0 ei (ŝ≅ k ec et eg) =
  ĉ≅ ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη)) (ψᵉᶠ-≅ H lo0 lo0 ei et) (λ η e η′ e′ eη → ψᵉᶠ-≅ H lo0 lo0 ei (eg η e η′ e′ eη))
ψᵉᶠ-≅ H lo0 lo1 ei (ŝ≅ k ec et eg) = ⊥-elim (tf k)
ψᵉᶠ-≅ H lo1 lo0 ei (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
ψᵉᶠ-≅ H lo1 lo1 ei (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ ei) ec (ψᵉᶠ-≅ H lo1 lo1 ei et) (λ η e η′ e′ eη → ψᵉᶠ-≅ H lo1 lo1 ei (eg η e η′ e′ eη))
ψᵉᶠ-≅ H l₁ l₂ ei (ĉ≅ ec dt dg eo eO) = ĉ≅ ec dt dg (ψᵉᶠ-≅ H l₁ l₂ ei eo) (λ η e η′ e′ eη → ψᵉᶠ-≅ H l₁ l₂ ei (eO η e η′ e′ eη))
ψᵉᶠ-≅ {S = S} {S′ = S′} H {z = z} {p = p} {σ = σ} {hd = hd} {z′ = z′} {p′ = p′} {σ′ = σ′} {hd′ = hd′} l₁ l₂ ei (lᵢ≅ {p = q} {q = q′} {f = f} {g = g} e h) =
  liEᶠ {S = S} {S′ = S′} {z = z} {p = p} {σ = σ} {hd = hd} {z′ = z′} {p′ = p′} {σ′ = σ′} {hd′ = hd′} {q = q} {q′ = q′} {f = f} {g = g} ei e
      (λ x y d → ψᵉᶠ-≅ H {z = z} {p = p} {σ = σ} {hd = hd} {z′ = z′} {p′ = p′} {σ′ = σ′} {hd′ = hd′} l₁ l₂ ei (h x y d))
      (λ x y d → ψᵉᶠ-≅ H {z = z} {p = σ q} {σ = σ} {hd = hd} {z′ = z′} {p′ = σ′ q′} {σ′ = σ′} {hd′ = hd′} l₁ l₂ e (h x y d))

repᶠ-≈ H l₁ l₂ e zero    = H
repᶠ-≈ H l₁ l₂ e (suc m) z p z′ p′ ei = ψᵉᶠ-≅ (repᶠ-≈ H l₁ l₂ e m) l₁ l₂ ei e

▹ᶠ-≈ : ∀ {φ} {S S′ : Stkᶠ φ} → S ≈ᶠ S′ → ∀ {k₁ k₂} {s : FrS φ k₁} {s′ : FrS φ k₂} {hp : FrH φ k₁} {hp′ : FrH φ k₂}
      {a : Ordˢ k₁} {b : Ordˢ k₂} → Lo k₁ → Lo k₂ → a ≅ˢ b → (S ▹[ s ∣ hp ] a) ≈ᶠ (S′ ▹[ s′ ∣ hp′ ] b)
▹ᶠ-≈ H l₁ l₂ e z p z′ p′ ei = ψᵉᶠ-≅ H l₁ l₂ ei e
```

**读法.** 互模拟: 尾巴 $0$ 处是 `▹Ω̂ᶠ-≈`, 后继处 `repᶠ-≈` (两侧帧证据函数 `s`、`s′` 与把手函数任意), `limᵢ` 处两个递归调用当 λ 传给 `liEᶠ`. 下面是折叠方程与两个行组合子 (穿透/折叠 `giPreEᶠ`, 第 0 层的链 `liLabEᶠ`).

```agda
chainEᶠ : ∀ {φ : Flr} (S : Stkᶠ φ) {j k ℓ} (z : Simᴵ (Fᶠ φ) ℓ) (σ : Simᴵ k ℓ) (hd : Hd k ℓ) (q : j <ᴵ k) (f : Uˢ j (<→◃ q) → Ordˢ k) → ℕ → Ordˢ j
chainEᶠ S {j} z σ hd q f = iter (λ x → ψᵉᶠ S z (σ q) σ hd (f (intoˢ (<→◃ q) x))) (Ωˢ j)

fold1Eᶠ : ∀ {φ} {S : Stkᶠ φ} {i k ℓ j} {z : Simᴵ (Fᶠ φ) ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {hd : Hd k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
         (i ≺ᴵ j) ⊎ (i ≅ᴵ j) →
         ψᵉᶠ S z p σ hd (Ord₊ˢ.limᵢ q f) ≡ Ord₊ˢ.lim (λ m → ψᵉᶠ S z p σ hd (f (intoˢ (<→◃ q) (chainEᶠ S z σ hd q f m))))
fold1Eᶠ {p = p} {σ = σ} {hd = hd} {q = q} h with <ᴵ-dec (σ q) p
... | injᵃ s = ⊥-elim (clash s h)
... | injᵇ _ = refl
... | injᶜ _ = refl

pen1Eᶠ : ∀ {φ} {S : Stkᶠ φ} {i k ℓ j N} {z : Simᴵ (Fᶠ φ) ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {hd : Hd k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
        j ≅ᴵ N → N ≺ᴵ i →
        Σ Ordᴵ λ j′ → Σ (j ≅ᴵ j′) λ e → Σ (j′ <ᴵ i) λ r →
        ψᵉᶠ S z p σ hd (Ord₊ˢ.limᵢ q f) ≡ Ord₊ˢ.limᵢ r (λ y → ψᵉᶠ S z p σ hd (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) y)))))
pen1Eᶠ {p = p} {σ = σ} {hd = hd} {q = q} ej νi with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = _ , e , r , refl
... | injᵇ s = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ (≺ᴵ-trans νi s) ej))
... | injᶜ c = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ νi (≅ᴵ-trans (≅ᴵ-sym c) ej)))

module GiEᶠ {φ : Flr} (S : Stkᶠ φ) (ps : T) where

  giPreEᶠ : ∀ {k ℓ i w ν j y ys} {z : Simᴵ (Fᶠ φ) ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {hd : Hd k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
           (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
           (rec : ∀ η (x : Ordˢ j) → LabL x η → LabL₊ i Ll (ψᵉᶠ S z p σ hd (f (intoˢ (<→◃ q) x))) (πw w ps (fsT (y ∷ ys) η))) →
           (recC : kd j ≡ false → ∀ η (x : Ordˢ j) → LabL x η →
                   LabL₊ j Ll (ψᵉᶠ S z (σ q) σ hd (f (intoˢ (<→◃ q) x))) (πw ν ps (fsT (y ∷ ys) η))) →
           LabL₊ i Ll (ψᵉᶠ S z p σ hd (Ord₊ˢ.limᵢ q f)) (πw w ps (y ∷ ys))
  giPreEᶠ {i = i} {w = w} {ν = ν} {j = j} {y = y} {ys = ys} {z = z} {p = p} {σ = σ} {hd = hd} {q = q} {f = f} Iw ei ki c Iν ej rec recC =
    go (cmpᵀ (sucT ν) w) refl
    where
    pen : Pen (cmpᵀ (sucT ν) w) → LabL₊ i Ll (ψᵉᶠ S z p σ hd (Ord₊ˢ.limᵢ q f)) (πw w ps (y ∷ ys))
    pen pn with pen1Eᶠ {S = S} {z = z} {p = p} {σ = σ} {hd = hd} {q = q} {f = f} (≅ᴵ-refl j)
                      (≺ᴵ-respʳ (≺ᴵ-respˡ ej (Ilt Iν Iw (pen→< ν w pn))) (≅ᴵ-sym ei))
    ... | j′ , e , r , eqn =
      subst (λ W → LabL₊ i Ll W (πw w ps (y ∷ ys))) (sym eqn)
            (gi cofE Iν (≅ᴵ-trans (≅ᴵ-sym e) ej)
                (λ η x l → subst (λ v → LabL₊ i Ll (ψᵉᶠ S z p σ hd (f (intoˢ (<→◃ q) (tr⁻ˢ e v)))) (fsT (πw w ps (y ∷ ys)) η))
                                 (sym (out-intoˢ (<→◃ r) x))
                                 (subst (LabL₊ i Ll _) (sym (penW w ps y ys ν c pn η))
                                        (rec η (tr⁻ˢ e x) (LabL-tr⁻ e (Ll→ (<→◃ r) l))))))
      where
      cofE : cof (πw w ps (y ∷ ys)) ≡ cΩ ν
      cofE = trans (cofW w ps y ys) (trans (cong (cofA w) c) (cofP pn))
    fold : cmpᵀ (sucT ν) w ≡ gt → LabL₊ i Ll (ψᵉᶠ S z p σ hd (Ord₊ˢ.limᵢ q f)) (πw w ps (y ∷ ys))
    fold em =
      subst (λ W → LabL₊ i Ll W (πw w ps (y ∷ ys))) (sym (fold1Eᶠ {S = S} {z = z} {p = p} {σ = σ} {hd = hd} {q = q} {f = f} ij))
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
      chainL : ∀ m → LabL (chainEᶠ S z σ hd q f m) (γW ps (y ∷ ys) ν m)
      chainL zero    = LabL-Ω (proj₁ Iν) (proj₁ (proj₂ Iν)) (proj₁ (proj₂ (proj₂ Iν))) (proj₂ (proj₂ (proj₂ Iν))) ej
      chainL (suc m) = frL₊ kj (recC kj _ _ (chainL m))
    go : ∀ m → cmpᵀ (sucT ν) w ≡ m → LabL₊ i Ll (ψᵉᶠ S z p σ hd (Ord₊ˢ.limᵢ q f)) (πw w ps (y ∷ ys))
    go lt em = pen (inj₁ em)
    go eq em = pen (inj₂ em)
    go gt em = fold em

module LiEᶠ {φ : Flr} (S : Stkᶠ φ) (ps : T) (HR : S ≈ᶠ S) where

  liLabEᶠ : ∀ {L k} {z : Simᴵ (Fᶠ φ) L} {p : zero <ᴵ L} {σ : Simᴵ k L} {hd : Hd k L} {q : zero <ᴵ k} {f : Uˢ zero (<→◃ q) → Ordˢ k} {y ys} →
           Lo k → cof (y ∷ ys) ≡ cΩ [] → Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → NF₁ (πw [] ps (y ∷ ys)) →
           (rec : ∀ (p′ : zero <ᴵ L) θ (x : Ordˢ zero) → Atomᴸ x θ → f (intoˢ (<→◃ q) x) ≅ˢ f (intoˢ (<→◃ q) x) →
                  NF₁ (πw [] ps (fsT (y ∷ ys) θ)) →
                  Σ (Goodᴸ (toZ (ψᵉᶠ S z p′ σ hd (f (intoˢ (<→◃ q) x))))) λ G → Lab (forceᴸ _ G) (πw [] ps (fsT (y ∷ ys) θ))) →
           Σ (Goodᴸ (toZ (ψᵉᶠ S z p σ hd (Ord₊ˢ.limᵢ q f)))) λ G → Lab (forceᴸ _ G) (πw [] ps (y ∷ ys))
  liLabEᶠ {z = z} {p = p} {σ = σ} {hd = hd} {q = q} {f = f} {y = y} {ys = ys} lk c ex nu rec =
    subst (λ W → Σ (Goodᴸ (toZ W)) λ G → Lab (forceᴸ _ G) (πw [] ps (y ∷ ys))) (sym eqf)
          (limᴸ nu (trans (cofW [] ps y ys) (cong (cofA []) c)) (λ m → proj₁ (outp m))
                (λ m → subst (Lab _) (sym (gtW [] ps y ys [] c refl m)) (proj₂ (outp m))))
    where
    eqf = fold1Eᶠ {S = S} {z = z} {p = p} {σ = σ} {hd = hd} {q = q} {f = f} (inj₂ z≅)
    atm : ∀ m → Atomᴸ (chainEᶠ S z σ hd q f m) (γW ps (y ∷ ys) [] m)
    atm zero    = Ωˢ-refl zero , gs gz , l1 refl (s≅ z≅) (l0 refl z≅)
    atm (suc m) = ψᵉᶠ-≅ HR {z = z} {p = σ q} {σ = σ} {hd = hd} {z′ = z} {p′ = σ q} {σ′ = σ} lk lk z≅ (i-respˢ ex (proj₁ (atm m))) ,
                  rec (σ q) _ _ (atm m) (i-respˢ ex (proj₁ (atm m))) (nfγ′ ps nu c m)
    outp : ∀ m → Σ (Goodᴸ (toZ (ψᵉᶠ S z p σ hd (f (intoˢ (<→◃ q) (chainEᶠ S z σ hd q f m)))))) λ G →
                Lab (forceᴸ _ G) (πw [] ps (fsT (y ∷ ys) (γW ps (y ∷ ys) [] m)))
    outp m = rec p _ _ (atm m) (i-respˢ ex (proj₁ (atm m))) (nfγ′ ps nu c m)
```

**读法.** 证明与 OmegaSqBase 逐字, 链与折叠方程多一个把手参数 `hd` (链点与输出用同一个把手). 下面是第 0 层指数的 `WE₀ᶠ`/`ZE₀ᶠ`/`GoodE₀ᶠ`.

```agda
WE₀ᶠ : ∀ {φ} {S : Stkᶠ φ} {ps} → Goodˢᶠ S ps → ∀ {X : Ordˢ zero} {η} → Lab0ᴸ X η → X ≅ˢ X →
      ∀ {i ℓ w} (z : Simᴵ (Fᶠ φ) ℓ) (p : i <ᴵ ℓ) (σ : Simᴵ zero ℓ) (hd : Hd zero ℓ) (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
      LabL₊ i Ll (ψᵉᶠ S z p σ hd X) (πw w ps (ψΩ η))
ZE₀ᶠ : ∀ {φ} {S : Stkᶠ φ} {ps} → Goodˢᶠ S ps → ∀ {X : Ordˢ zero} {η} → Lab0ᴸ X η → X ≅ˢ X →
      ∀ {L} (z : Simᴵ (Fᶠ φ) L) (p : zero <ᴵ L) (σ : Simᴵ zero L) (hd : Hd zero L) → NF₁ (πw [] ps (ψΩ η)) →
      Σ (Goodᴸ (toZ (ψᵉᶠ S z p σ hd X))) λ G → Lab (forceᴸ _ G) (πw [] ps (ψΩ η))
repGood₀ᶠ : ∀ {φ} {S : Stkᶠ φ} {ps} → Goodˢᶠ S ps → ∀ {Y : Ordˢ zero} {θ} → Lab0ᴸ Y θ → Y ≅ˢ Y → ∀ m →
           Goodˢᶠ (repᶠ S φ (λ q → q) (λ _ → σ⊥) (λ _ → hno) Y m) (ps ++ replicate m (ψᵗ Ωᵗ θ))
GoodE₀ᶠ : ∀ {φ} {S : Stkᶠ φ} {ps} → Goodˢᶠ S ps → ∀ {X : Ordˢ zero} {η} → Lab0ᴸ X η → X ≅ˢ X → Goodˢᶠ (S ▹[ (λ _ → σ⊥) ∣ (λ _ → hno) ] X) (ps ++ ψᵗ Ωᵗ η ∷ [])

GoodE₀ᶠ G {η = η} l ex = goodᶠ (λ z p Iw ei ki → WE₀ᶠ G l ex z p σ⊥ hno Iw ei ki) (λ z p nf → ZE₀ᶠ G l ex z p σ⊥ hno nf) (▹ᶠ-≈ (hRᶠ G) lo0 lo0 ex)
  (FW++ (ψᵗ Ωᵗ η ∷ []) (fwᶠ G))

repGood₀ᶠ {S = S} {ps} G l ey zero    = subst (Goodˢᶠ S) (sym (++-identityʳ ps)) G
repGood₀ᶠ {φ} {S = S} {ps} G {Y} {θ} l ey (suc m) =
  subst (Goodˢᶠ (repᶠ S φ (λ q → q) (λ _ → σ⊥) (λ _ → hno) Y (suc m))) (snoc ps m (ψᵗ Ωᵗ θ)) (GoodE₀ᶠ (repGood₀ᶠ G l ey m) l ey)

WE₀ᶠ G {η = []} (lz c) ex z p σ hd Iw ei ki = hWᶠ (GoodΩᶠ G) z p Iw ei ki
WE₀ᶠ G {η = y ∷ ys} (lz c) ex z p σ hd Iw ei ki = ⊥-elim (cof-ne y ys c)
WE₀ᶠ G {η = []} (ls () l) ex z p σ hd Iw ei ki
WE₀ᶠ {ps = ps} G {η = y ∷ ys} (ls c l) ex {w = w} z p σ hd Iw ei ki =
  gl (cE₁ w ps c) (λ m → subst (LabL₊ _ Ll _) (sym (fE₁ w ps c m)) (hWᶠ (repGood₀ᶠ G l (s-invˢ ex) m) z p Iw ei ki))
WE₀ᶠ G {η = []} (ll () h) ex z p σ hd Iw ei ki
WE₀ᶠ {ps = ps} G {η = y ∷ ys} (ll c h) ex {w = w} z p σ hd Iw ei ki =
  gl (cEω w ps c) (λ n → subst (LabL₊ _ Ll _) (sym (fEω w ps c n)) (WE₀ᶠ G (h n) (l-invˢ ex n) z p σ hd Iw ei ki))
WE₀ᶠ G {η = []} (lŝ₀ () K h₀ hk) ex z p σ hd Iw ei ki
WE₀ᶠ {ps = ps} G {η = y ∷ ys} (lŝ₀ c K h₀ hk) ex {w = w} z p σ hd Iw ei ki =
  gĉ (cEω w ps c) K (subst (LabL₊ _ Ll _) (sym (fEω w ps c 0)) (WE₀ᶠ G h₀ (ŝ-refl₀ ex) z p σ hd Iw ei ki))
     (λ k → subst (LabL₊ _ Ll _) (sym (fEω w ps c (suc k)))
                  (WE₀ᶠ G (hk k) (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) z p σ hd Iw ei ki))
WE₀ᶠ G {η = []} (lĉ () K h₀ hk) ex z p σ hd Iw ei ki
WE₀ᶠ {ps = ps} G {η = y ∷ ys} (lĉ c K h₀ hk) ex {w = w} z p σ hd Iw ei ki =
  gĉ (cEω w ps c) K (subst (LabL₊ _ Ll _) (sym (fEω w ps c 0)) (WE₀ᶠ G h₀ (ĉ-refl₀ ex) z p σ hd Iw ei ki))
     (λ k → subst (LabL₊ _ Ll _) (sym (fEω w ps c (suc k))) (WE₀ᶠ G (hk k) (ĉ-reflg ex _ _) z p σ hd Iw ei ki))

ZE₀ᶠ G {η = []} (lz c) ex z p σ hd nf = h0ᶠ (GoodΩᶠ G) z p nf
ZE₀ᶠ G {η = y ∷ ys} (lz c) ex z p σ hd nf = ⊥-elim (cof-ne y ys c)
ZE₀ᶠ G {η = []} (ls () l) ex z p σ hd nf
ZE₀ᶠ {ps = ps} G {η = y ∷ ys} (ls c l) ex z p σ hd nf =
  limᴸ nf (cE₁ [] ps c)
       (λ m → proj₁ (h0ᶠ (repGood₀ᶠ G l (s-invˢ ex) m) z p (subst NF₁ (fE₁ [] ps c m) (NF₁-fsn nf (cE₁ [] ps c) m))))
       (λ m → subst (Lab _) (sym (fE₁ [] ps c m))
                    (proj₂ (h0ᶠ (repGood₀ᶠ G l (s-invˢ ex) m) z p (subst NF₁ (fE₁ [] ps c m) (NF₁-fsn nf (cE₁ [] ps c) m)))))
ZE₀ᶠ G {η = []} (ll () h) ex z p σ hd nf
ZE₀ᶠ {ps = ps} G {η = y ∷ ys} (ll c h) ex z p σ hd nf =
  limᴸ nf (cEω [] ps c)
       (λ n → proj₁ (ZE₀ᶠ G (h n) (l-invˢ ex n) z p σ hd (subst NF₁ (fEω [] ps c n) (NF₁-fsn nf (cEω [] ps c) n))))
       (λ n → subst (Lab _) (sym (fEω [] ps c n))
                    (proj₂ (ZE₀ᶠ G (h n) (l-invˢ ex n) z p σ hd (subst NF₁ (fEω [] ps c n) (NF₁-fsn nf (cEω [] ps c) n)))))
ZE₀ᶠ G {η = []} (lŝ₀ () K h₀ hk) ex z p σ hd nf
ZE₀ᶠ {ps = ps} G {η = y ∷ ys} (lŝ₀ c K h₀ hk) ex z p σ hd nf =
  ĉᴸ-mk nf (cEω [] ps c) K
        (proj₁ (ZE₀ᶠ G h₀ (ŝ-refl₀ ex) z p σ hd (nfk 0)))
        (subst (Lab _) (sym (fEω [] ps c 0)) (proj₂ (ZE₀ᶠ G h₀ (ŝ-refl₀ ex) z p σ hd (nfk 0))))
        (λ k → proj₁ (ZE₀ᶠ G (hk k) (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) z p σ hd (nfk (suc k))))
        (λ k → subst (Lab _) (sym (fEω [] ps c (suc k)))
                     (proj₂ (ZE₀ᶠ G (hk k) (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) z p σ hd (nfk (suc k)))))
  where nfk = λ n → subst NF₁ (fEω [] ps c n) (NF₁-fsn nf (cEω [] ps c) n)
ZE₀ᶠ G {η = []} (lĉ () K h₀ hk) ex z p σ hd nf
ZE₀ᶠ {ps = ps} G {η = y ∷ ys} (lĉ c K h₀ hk) ex z p σ hd nf =
  ĉᴸ-mk nf (cEω [] ps c) K
        (proj₁ (ZE₀ᶠ G h₀ (ĉ-refl₀ ex) z p σ hd (nfk 0)))
        (subst (Lab _) (sym (fEω [] ps c 0)) (proj₂ (ZE₀ᶠ G h₀ (ĉ-refl₀ ex) z p σ hd (nfk 0))))
        (λ k → proj₁ (ZE₀ᶠ G (hk k) (ĉ-reflg ex _ _) z p σ hd (nfk (suc k))))
        (λ k → subst (Lab _) (sym (fEω [] ps c (suc k))) (proj₂ (ZE₀ᶠ G (hk k) (ĉ-reflg ex _ _) z p σ hd (nfk (suc k)))))
  where nfk = λ n → subst NF₁ (fEω [] ps c n) (NF₁-fsn nf (cEω [] ps c) n)
```

**读法.** 第 0 层的帧不动地板, 地板见证经 `FW++` 往后传. 下面是第 1 层指数的 `WE₁ᶠ`/`ZE₁ᶠ`/`GoodE₁ᶠ`; `gu` 行降到第 0 层时把手是 `hyes (σ zero)`.

```agda
WE₁ᶠ : ∀ {φ} {S : Stkᶠ φ} {ps} → Goodˢᶠ S ps → ∀ {X : Ordˢ (suc zero)} {η} → LabL₊ (suc zero) Ll X η → X ≅ˢ X →
      ∀ {i ℓ w} (z : Simᴵ (Fᶠ φ) ℓ) (p : i <ᴵ ℓ) (σ : Simᴵ (suc zero) ℓ) (hd : Hd (suc zero) ℓ) (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
      LabL₊ i Ll (ψᵉᶠ S z p σ hd X) (πw w ps (ψΩ η))
ZE₁ᶠ : ∀ {φ} {S : Stkᶠ φ} {ps} → Goodˢᶠ S ps → ∀ {X : Ordˢ (suc zero)} {η} → LabL₊ (suc zero) Ll X η → X ≅ˢ X →
      ∀ {L} (z : Simᴵ (Fᶠ φ) L) (p : zero <ᴵ L) (σ : Simᴵ (suc zero) L) (hd : Hd (suc zero) L) → NF₁ (πw [] ps (ψΩ η)) →
      Σ (Goodᴸ (toZ (ψᵉᶠ S z p σ hd X))) λ G → Lab (forceᴸ _ G) (πw [] ps (ψΩ η))
repGood₁ᶠ : ∀ {φ} {S : Stkᶠ φ} {ps} → Goodˢᶠ S ps → ∀ {Y : Ordˢ (suc zero)} {θ} → LabL₊ (suc zero) Ll Y θ → Y ≅ˢ Y → ∀ m →
           Goodˢᶠ (repᶠ S φ (λ q → q) (λ ζ′ → σ1 (ζ′ (ιz φ))) (λ _ → hno) Y m) (ps ++ replicate m (ψᵗ Ωᵗ θ))
GoodE₁ᶠ : ∀ {φ} {S : Stkᶠ φ} {ps} → Goodˢᶠ S ps → ∀ {X : Ordˢ (suc zero)} {η} → LabL₊ (suc zero) Ll X η → X ≅ˢ X →
         Goodˢᶠ (S ▹[ (λ ζ′ → σ1 (ζ′ (ιz φ))) ∣ (λ _ → hno) ] X) (ps ++ ψᵗ Ωᵗ η ∷ [])

GoodE₁ᶠ {φ} G {η = η} d ex = goodᶠ (λ z p Iw ei ki → WE₁ᶠ G d ex z p (σ1 (z (ιz φ))) hno Iw ei ki) (λ z p nf → ZE₁ᶠ G d ex z p (σ1 (z (ιz φ))) hno nf)
  (▹ᶠ-≈ (hRᶠ G) lo1 lo1 ex) (FW++ (ψᵗ Ωᵗ η ∷ []) (fwᶠ G))

repGood₁ᶠ {S = S} {ps} G d ey zero    = subst (Goodˢᶠ S) (sym (++-identityʳ ps)) G
repGood₁ᶠ {φ} {S = S} {ps} G {Y} {θ} d ey (suc m) =
  subst (Goodˢᶠ (repᶠ S φ (λ q → q) (λ ζ′ → σ1 (ζ′ (ιz φ))) (λ _ → hno) Y (suc m))) (snoc ps m (ψᵗ Ωᵗ θ)) (GoodE₁ᶠ (repGood₁ᶠ G d ey m) d ey)

WE₁ᶠ G {η = []} (gz c) ex z p σ hd Iw ei ki = hWᶠ (GoodΩᶠ G) z p Iw ei ki
WE₁ᶠ G {η = y ∷ ys} (gz c) ex z p σ hd Iw ei ki = ⊥-elim (cof-ne y ys c)
WE₁ᶠ G {η = []} (gs () d) ex z p σ hd Iw ei ki
WE₁ᶠ {ps = ps} G {η = y ∷ ys} (gs c d) ex {w = w} z p σ hd Iw ei ki =
  gl (cE₁ w ps c) (λ m → subst (LabL₊ _ Ll _) (sym (fE₁ w ps c m)) (hWᶠ (repGood₁ᶠ G d (s-invˢ ex) m) z p Iw ei ki))
WE₁ᶠ G {η = []} (gl () h) ex z p σ hd Iw ei ki
WE₁ᶠ {ps = ps} G {η = y ∷ ys} (gl c h) ex {w = w} z p σ hd Iw ei ki =
  gl (cEω w ps c) (λ n → subst (LabL₊ _ Ll _) (sym (fEω w ps c n)) (WE₁ᶠ G (h n) (l-invˢ ex n) z p σ hd Iw ei ki))
WE₁ᶠ G (gu {r = zero} at) ex z p σ hd Iw ei ki = WE₀ᶠ G (atomL at) (proj₁ at) z p (λ q → σ (suc q)) (hyes (σ zero)) Iw ei ki
WE₁ᶠ {S = S} {ps} G {η = η} (gi {q = zero} {f = f} c I ej h) ex {w = w} z p σ hd Iw ei ki =
  GiEᶠ.giPreEᶠ S ps {z = z} {p = p} {σ = σ} {hd = hd} {q = zero} {f = f} Iw ei ki (cofΩc c I) I ej
    (λ θ x l → subst (LabL₊ _ Ll _) (cong (πw w ps) (sym (fsTΩ c I θ)))
                     (WE₁ᶠ G (h θ x l) (i-respˢ ex (proj₁ l)) z p σ hd Iw ei ki))
    (λ ())
WE₁ᶠ G (gi {q = suc ()} c I ej h) ex z p σ hd Iw ei ki
WE₁ᶠ G {η = []} (gĉ () K h₀ hk) ex z p σ hd Iw ei ki
WE₁ᶠ {ps = ps} G {η = y ∷ ys} (gĉ c K h₀ hk) ex {w = w} z p σ hd Iw ei ki =
  gĉ (cEω w ps c) K (subst (LabL₊ _ Ll _) (sym (fEω w ps c 0)) (WE₁ᶠ G h₀ (ĉ-refl₀ ex) z p σ hd Iw ei ki))
     (λ k → subst (LabL₊ _ Ll _) (sym (fEω w ps c (suc k))) (WE₁ᶠ G (hk k) (ĉ-reflg ex _ _) z p σ hd Iw ei ki))
WE₁ᶠ G {η = η} (gŝ kk c Ib bb ob h₀ hg) ex {w = []} z p σ hd Iw ei ki = ⊥-elim (ne-w Iw ei ki refl)
WE₁ᶠ {ps = ps} G {η = η} (gŝ kk c Ib bb ob h₀ hg) ex {w = x ∷ xs} z p σ hd Iw ei ki =
  gŝ ki (trans (cofW (x ∷ xs) ps (ψᵗ Ωᵗ η) []) (trans (cong (cofA (x ∷ xs)) (cofΩc c I0)) (H1-pen x xs))) Ib bb
     (λ θ → subst (Occ _) (sym (fsTw θ)) (od (OccΣ ps (od (ob θ)))))
     (subst (LabL₊ _ Ll _) (sym (fsTw (natT 1))) (WE₁ᶠ G h₀ (ŝ-refl₀ ex) z p σ hd Iw ei ki))
     (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (fsTw θ))
                                  (WE₁ᶠ G (hg θ Y hY lY nθ lt e) (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) z p σ hd Iw ei ki))
  where
  fsTw : ∀ θ → fsT (πw (x ∷ xs) ps (ψΩ η)) θ ≡ πw (x ∷ xs) ps (ψΩ (fsT η θ))
  fsTw θ = trans (H1W x xs ps (ψᵗ Ωᵗ η) [] (cofΩc c I0) θ) (cong (πw (x ∷ xs) ps) (fsTΩ c I0 θ))

ZE₁ᶠ G {η = []} (gz c) ex z p σ hd nf = h0ᶠ (GoodΩᶠ G) z p nf
ZE₁ᶠ G {η = y ∷ ys} (gz c) ex z p σ hd nf = ⊥-elim (cof-ne y ys c)
ZE₁ᶠ G {η = []} (gs () d) ex z p σ hd nf
ZE₁ᶠ {ps = ps} G {η = y ∷ ys} (gs c d) ex z p σ hd nf =
  limᴸ nf (cE₁ [] ps c)
       (λ m → proj₁ (h0ᶠ (repGood₁ᶠ G d (s-invˢ ex) m) z p (subst NF₁ (fE₁ [] ps c m) (NF₁-fsn nf (cE₁ [] ps c) m))))
       (λ m → subst (Lab _) (sym (fE₁ [] ps c m))
                    (proj₂ (h0ᶠ (repGood₁ᶠ G d (s-invˢ ex) m) z p (subst NF₁ (fE₁ [] ps c m) (NF₁-fsn nf (cE₁ [] ps c) m)))))
ZE₁ᶠ G {η = []} (gl () h) ex z p σ hd nf
ZE₁ᶠ {ps = ps} G {η = y ∷ ys} (gl c h) ex z p σ hd nf =
  limᴸ nf (cEω [] ps c)
       (λ n → proj₁ (ZE₁ᶠ G (h n) (l-invˢ ex n) z p σ hd (subst NF₁ (fEω [] ps c n) (NF₁-fsn nf (cEω [] ps c) n))))
       (λ n → subst (Lab _) (sym (fEω [] ps c n))
                    (proj₂ (ZE₁ᶠ G (h n) (l-invˢ ex n) z p σ hd (subst NF₁ (fEω [] ps c n) (NF₁-fsn nf (cEω [] ps c) n)))))
ZE₁ᶠ G (gu {r = zero} at) ex z p σ hd nf = ZE₀ᶠ G (atomL at) (proj₁ at) z p (λ q → σ (suc q)) (hyes (σ zero)) nf
ZE₁ᶠ {S = S} {ps} G {η = η} (gi {q = zero} {f = f} c I ej h) ex z p σ hd nf =
  LiEᶠ.liLabEᶠ S ps (hRᶠ G) {z = z} {p = p} {σ = σ} {hd = hd} {q = zero} {f = f} lo1 (cofΩc c₀ I0) ex nf
    (λ p′ θ x at br nf′ →
       subst (λ t → Σ (Goodᴸ (toZ (ψᵉᶠ S z p′ σ hd (f x)))) λ G′ → Lab (forceᴸ _ G′) (πw [] ps t)) (sym (fsTΩ c₀ I0 θ))
             (ZE₁ᶠ G (h θ x at) br z p′ σ hd (subst (λ t → NF₁ (πw [] ps t)) (fsTΩ c₀ I0 θ) nf′)))
  where
  c₀ : cof η ≡ cΩ []
  c₀ = trans c (cong cΩ (kdI I (sym (kd-≅ ej))))
ZE₁ᶠ G (gi {q = suc ()} c I ej h) ex z p σ hd nf
ZE₁ᶠ G {η = []} (gĉ () K h₀ hk) ex z p σ hd nf
ZE₁ᶠ {ps = ps} G {η = y ∷ ys} (gĉ c K h₀ hk) ex z p σ hd nf =
  ĉᴸ-mk nf (cEω [] ps c) K
        (proj₁ (ZE₁ᶠ G h₀ (ĉ-refl₀ ex) z p σ hd (nfk 0)))
        (subst (Lab _) (sym (fEω [] ps c 0)) (proj₂ (ZE₁ᶠ G h₀ (ĉ-refl₀ ex) z p σ hd (nfk 0))))
        (λ k → proj₁ (ZE₁ᶠ G (hk k) (ĉ-reflg ex _ _) z p σ hd (nfk (suc k))))
        (λ k → subst (Lab _) (sym (fEω [] ps c (suc k))) (proj₂ (ZE₁ᶠ G (hk k) (ĉ-reflg ex _ _) z p σ hd (nfk (suc k)))))
  where nfk = λ n → subst NF₁ (fEω [] ps c n) (NF₁-fsn nf (cEω [] ps c) n)
ZE₁ᶠ {S = S} {ps} G {η = η} (gŝ kk c Ib bb ob h₀ hg) ex z p σ hd nf =
  ŝChainG ps (cofΩc c I0) nf Ib bb (λ θ → subst (Occ _) (sym (fsTΩ c I0 θ)) (od (ob θ)))
          (subst (λ t → Σ (Goodᴸ _) λ G′ → Lab (forceᴸ _ G′) (πw [] ps t)) (sym (fsTΩ c I0 (natT 1)))
                 (ZE₁ᶠ G h₀ (ŝ-refl₀ ex) z p σ hd (subst (λ t → NF₁ (πw [] ps t)) (fsTΩ c I0 (natT 1)) (nfγ′ ps nf (cofΩc c I0) 0))))
          (λ m Y hY lY e →
             subst (λ t → Σ (Goodᴸ _) λ G′ → Lab (forceᴸ _ G′) (πw [] ps t)) (sym (fsTΩ c I0 _))
                   (ZE₁ᶠ G (hg _ Y hY lY (nfγ′ ps nf (cofΩc c I0) m) (1<γ ps (ψᵗ Ωᵗ η) [] (cofΩc c I0) m) e)
                        (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) z p σ hd
                        (subst (λ t → NF₁ (πw [] ps t)) (fsTΩ c I0 _) (nfγ′ ps nf (cofΩc c I0) (suc m)))))
```

**读法.** 停机一次通过, 与 OmegaSqBase 相同. 互模拟仍只对 `Lo` 层: 第 $\ge2$ 层的后继会提升地板, 而 `≅ˢ` 可以经 `upˡ`/`upʳ` 把不同层号的后继联系起来 (例如第 2 层的 $(\uparrow\Omega_1)+1$ 与第 1 层的 $\Omega_1+1$), 两侧的地板因而不同, 弹出的闭包的界不再 $\cong$; 所以 `ψᵉᶠ-≅` 不能逐字推广到一切层, 需要 "层号对齐" 的互模拟 (见 NonTight §4).

## §8 不需要自互模拟的 W 版

`WE`/`ZE` 里自互模拟 `X ≅ˢ X` 只为了好栈的第三个字段 (栈的自互模拟, 供第 0 层链原子) 而传递; 目标 $w\ne0$ 的引理只用 `HypW` 与地板见证. 第 2 层帧的穿透分支要在**任意**带标签的第 1 层输入 $x$ 上标记 $\psi_w(ps+\psi_\Omega(x))$, 而第 1 层的 `LabL` 不含 $x\cong^\mathsf s x$, 所以需要不带自互模拟的版本: `GoodWᶠ` (只有 `hWʷ`、`fwʷ`), `GoodΩʷ` (= `PopΩW`), `WE₀ʷ`/`repGood₀ʷ`/`GoodE₀ʷ`, `WE₁ʷ`/`repGood₁ʷ`/`GoodE₁ʷ`. 文本是 §7 去掉 `ex` 及其派生参数.

```agda
record GoodWᶠ {φ : Flr} (S : Stkᶠ φ) (ps : T) : Set where
  constructor goodʷ
  field
    hWʷ : HypWᶠ S ps
    fwʷ : FW φ ps
open GoodWᶠ public

toW : ∀ {φ} {S : Stkᶠ φ} {ps} → Goodˢᶠ S ps → GoodWᶠ S ps
toW G = goodʷ (hWᶠ G) (fwᶠ G)

GoodΩʷ : ∀ {φ} {S : Stkᶠ φ} {ps} → GoodWᶠ S ps → GoodWᶠ (S ▹Ω̂ᶠ) (ps ++ ΩΩ ∷ [])
GoodΩʷ G = goodʷ (PopΩW.hW′ (hWʷ G) (fwʷ G)) (FW++ (ΩΩ ∷ []) (fwʷ G))

WE₀ʷ : ∀ {φ} {S : Stkᶠ φ} {ps} → GoodWᶠ S ps → ∀ {X : Ordˢ zero} {η} → Lab0ᴸ X η →
      ∀ {i ℓ w} (z : Simᴵ (Fᶠ φ) ℓ) (p : i <ᴵ ℓ) (σ : Simᴵ zero ℓ) (hd : Hd zero ℓ) (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
      LabL₊ i Ll (ψᵉᶠ S z p σ hd X) (πw w ps (ψΩ η))
repGood₀ʷ : ∀ {φ} {S : Stkᶠ φ} {ps} → GoodWᶠ S ps → ∀ {Y : Ordˢ zero} {θ} → Lab0ᴸ Y θ → ∀ m →
           GoodWᶠ (repᶠ S φ (λ q → q) (λ _ → σ⊥) (λ _ → hno) Y m) (ps ++ replicate m (ψᵗ Ωᵗ θ))
GoodE₀ʷ : ∀ {φ} {S : Stkᶠ φ} {ps} → GoodWᶠ S ps → ∀ {X : Ordˢ zero} {η} → Lab0ᴸ X η →
          GoodWᶠ (S ▹[ (λ _ → σ⊥) ∣ (λ _ → hno) ] X) (ps ++ ψᵗ Ωᵗ η ∷ [])

GoodE₀ʷ G {η = η} l = goodʷ (λ z p Iw ei ki → WE₀ʷ G l z p σ⊥ hno Iw ei ki) (FW++ (ψᵗ Ωᵗ η ∷ []) (fwʷ G))

repGood₀ʷ {S = S} {ps} G l zero    = subst (GoodWᶠ S) (sym (++-identityʳ ps)) G
repGood₀ʷ {φ} {S = S} {ps} G {Y} {θ} l (suc m) =
  subst (GoodWᶠ (repᶠ S φ (λ q → q) (λ _ → σ⊥) (λ _ → hno) Y (suc m))) (snoc ps m (ψᵗ Ωᵗ θ)) (GoodE₀ʷ (repGood₀ʷ G l m) l)

WE₀ʷ G {η = []} (lz c) z p σ hd Iw ei ki = hWʷ (GoodΩʷ G) z p Iw ei ki
WE₀ʷ G {η = y ∷ ys} (lz c) z p σ hd Iw ei ki = ⊥-elim (cof-ne y ys c)
WE₀ʷ G {η = []} (ls () l) z p σ hd Iw ei ki
WE₀ʷ {ps = ps} G {η = y ∷ ys} (ls c l) {w = w} z p σ hd Iw ei ki =
  gl (cE₁ w ps c) (λ m → subst (LabL₊ _ Ll _) (sym (fE₁ w ps c m)) (hWʷ (repGood₀ʷ G l m) z p Iw ei ki))
WE₀ʷ G {η = []} (ll () h) z p σ hd Iw ei ki
WE₀ʷ {ps = ps} G {η = y ∷ ys} (ll c h) {w = w} z p σ hd Iw ei ki =
  gl (cEω w ps c) (λ n → subst (LabL₊ _ Ll _) (sym (fEω w ps c n)) (WE₀ʷ G (h n) z p σ hd Iw ei ki))
WE₀ʷ G {η = []} (lŝ₀ () K h₀ hk) z p σ hd Iw ei ki
WE₀ʷ {ps = ps} G {η = y ∷ ys} (lŝ₀ c K h₀ hk) {w = w} z p σ hd Iw ei ki =
  gĉ (cEω w ps c) K (subst (LabL₊ _ Ll _) (sym (fEω w ps c 0)) (WE₀ʷ G h₀ z p σ hd Iw ei ki))
     (λ k → subst (LabL₊ _ Ll _) (sym (fEω w ps c (suc k)))
                  (WE₀ʷ G (hk k) z p σ hd Iw ei ki))
WE₀ʷ G {η = []} (lĉ () K h₀ hk) z p σ hd Iw ei ki
WE₀ʷ {ps = ps} G {η = y ∷ ys} (lĉ c K h₀ hk) {w = w} z p σ hd Iw ei ki =
  gĉ (cEω w ps c) K (subst (LabL₊ _ Ll _) (sym (fEω w ps c 0)) (WE₀ʷ G h₀ z p σ hd Iw ei ki))
     (λ k → subst (LabL₊ _ Ll _) (sym (fEω w ps c (suc k))) (WE₀ʷ G (hk k) z p σ hd Iw ei ki))


WE₁ʷ : ∀ {φ} {S : Stkᶠ φ} {ps} → GoodWᶠ S ps → ∀ {X : Ordˢ (suc zero)} {η} → LabL₊ (suc zero) Ll X η →
      ∀ {i ℓ w} (z : Simᴵ (Fᶠ φ) ℓ) (p : i <ᴵ ℓ) (σ : Simᴵ (suc zero) ℓ) (hd : Hd (suc zero) ℓ) (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
      LabL₊ i Ll (ψᵉᶠ S z p σ hd X) (πw w ps (ψΩ η))
repGood₁ʷ : ∀ {φ} {S : Stkᶠ φ} {ps} → GoodWᶠ S ps → ∀ {Y : Ordˢ (suc zero)} {θ} → LabL₊ (suc zero) Ll Y θ → ∀ m →
           GoodWᶠ (repᶠ S φ (λ q → q) (λ ζ′ → σ1 (ζ′ (ιz φ))) (λ _ → hno) Y m) (ps ++ replicate m (ψᵗ Ωᵗ θ))
GoodE₁ʷ : ∀ {φ} {S : Stkᶠ φ} {ps} → GoodWᶠ S ps → ∀ {X : Ordˢ (suc zero)} {η} → LabL₊ (suc zero) Ll X η →
          GoodWᶠ (S ▹[ (λ ζ′ → σ1 (ζ′ (ιz φ))) ∣ (λ _ → hno) ] X) (ps ++ ψᵗ Ωᵗ η ∷ [])

GoodE₁ʷ {φ} G {η = η} d = goodʷ (λ z p Iw ei ki → WE₁ʷ G d z p (σ1 (z (ιz φ))) hno Iw ei ki) (FW++ (ψᵗ Ωᵗ η ∷ []) (fwʷ G))

repGood₁ʷ {S = S} {ps} G d zero    = subst (GoodWᶠ S) (sym (++-identityʳ ps)) G
repGood₁ʷ {φ} {S = S} {ps} G {Y} {θ} d (suc m) =
  subst (GoodWᶠ (repᶠ S φ (λ q → q) (λ ζ′ → σ1 (ζ′ (ιz φ))) (λ _ → hno) Y (suc m))) (snoc ps m (ψᵗ Ωᵗ θ)) (GoodE₁ʷ (repGood₁ʷ G d m) d)

WE₁ʷ G {η = []} (gz c) z p σ hd Iw ei ki = hWʷ (GoodΩʷ G) z p Iw ei ki
WE₁ʷ G {η = y ∷ ys} (gz c) z p σ hd Iw ei ki = ⊥-elim (cof-ne y ys c)
WE₁ʷ G {η = []} (gs () d) z p σ hd Iw ei ki
WE₁ʷ {ps = ps} G {η = y ∷ ys} (gs c d) {w = w} z p σ hd Iw ei ki =
  gl (cE₁ w ps c) (λ m → subst (LabL₊ _ Ll _) (sym (fE₁ w ps c m)) (hWʷ (repGood₁ʷ G d m) z p Iw ei ki))
WE₁ʷ G {η = []} (gl () h) z p σ hd Iw ei ki
WE₁ʷ {ps = ps} G {η = y ∷ ys} (gl c h) {w = w} z p σ hd Iw ei ki =
  gl (cEω w ps c) (λ n → subst (LabL₊ _ Ll _) (sym (fEω w ps c n)) (WE₁ʷ G (h n) z p σ hd Iw ei ki))
WE₁ʷ G (gu {r = zero} at) z p σ hd Iw ei ki = WE₀ʷ G (atomL at) z p (λ q → σ (suc q)) (hyes (σ zero)) Iw ei ki
WE₁ʷ {S = S} {ps} G {η = η} (gi {q = zero} {f = f} c I ej h) {w = w} z p σ hd Iw ei ki =
  GiEᶠ.giPreEᶠ S ps {z = z} {p = p} {σ = σ} {hd = hd} {q = zero} {f = f} Iw ei ki (cofΩc c I) I ej
    (λ θ x l → subst (LabL₊ _ Ll _) (cong (πw w ps) (sym (fsTΩ c I θ)))
                     (WE₁ʷ G (h θ x l) z p σ hd Iw ei ki))
    (λ ())
WE₁ʷ G (gi {q = suc ()} c I ej h) z p σ hd Iw ei ki
WE₁ʷ G {η = []} (gĉ () K h₀ hk) z p σ hd Iw ei ki
WE₁ʷ {ps = ps} G {η = y ∷ ys} (gĉ c K h₀ hk) {w = w} z p σ hd Iw ei ki =
  gĉ (cEω w ps c) K (subst (LabL₊ _ Ll _) (sym (fEω w ps c 0)) (WE₁ʷ G h₀ z p σ hd Iw ei ki))
     (λ k → subst (LabL₊ _ Ll _) (sym (fEω w ps c (suc k))) (WE₁ʷ G (hk k) z p σ hd Iw ei ki))
WE₁ʷ G {η = η} (gŝ kk c Ib bb ob h₀ hg) {w = []} z p σ hd Iw ei ki = ⊥-elim (ne-w Iw ei ki refl)
WE₁ʷ {ps = ps} G {η = η} (gŝ kk c Ib bb ob h₀ hg) {w = x ∷ xs} z p σ hd Iw ei ki =
  gŝ ki (trans (cofW (x ∷ xs) ps (ψᵗ Ωᵗ η) []) (trans (cong (cofA (x ∷ xs)) (cofΩc c I0)) (H1-pen x xs))) Ib bb
     (λ θ → subst (Occ _) (sym (fsTw θ)) (od (OccΣ ps (od (ob θ)))))
     (subst (LabL₊ _ Ll _) (sym (fsTw (natT 1))) (WE₁ʷ G h₀ z p σ hd Iw ei ki))
     (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (fsTw θ))
                                  (WE₁ʷ G (hg θ Y hY lY nθ lt e) z p σ hd Iw ei ki))
  where
  fsTw : ∀ θ → fsT (πw (x ∷ xs) ps (ψΩ η)) θ ≡ πw (x ∷ xs) ps (ψΩ (fsT η θ))
  fsTw θ = trans (H1W x xs ps (ψᵗ Ωᵗ η) [] (cofΩc c I0) θ) (cong (πw (x ∷ xs) ps) (fsTΩ c I0 θ))
```

**读法.** 与 §7 的 `WE₀ᶠ`/`WE₁ᶠ` 逐行对应, 只是不传 `ex`; `GoodΩʷ` 就是 §6 的 `PopΩW`. 停机一次通过 (`WE₁ʷ (gs …) → repGood₁ʷ → GoodE₁ʷ → WE₁ʷ` 推导严格下降). `toW` 把完整的好栈忘成 W 版.

## §9 第 2 层帧 $\psi_\Omega(\Omega_2)$: 提升地板的第一个实例

**目标 $w\ne0$** (`WE₂`): $\Omega_2$ = `limᵢ zero (up zero)`, 共尾度 $\Omega_2=\Omega_{1+1}$, 由 `giPreEᶠ`: 穿透时逐点是 `WE₁ʷ` (任意带标签的第 1 层输入, 经 `up zero` 带把手), 折叠时 (目标 $1$) 链点也是 `WE₁ʷ`. **目标 $0$** (`Z₂.ZE₂`): 沿第 1 层的链折叠 (OmegaSq 的 `ZΩ₂` 在地板栈上的版本), 链点由 `WE₁ʷ` 标记, 自互模拟由 `ψᵉᶠ-≅` (第 1 层), 输出由 `ZE₁ᶠ`. `Ω₂-≅`: 帧的互模拟, `liEᶠ` + 第 1 层的 `ψᵉᶠ-≅`.

**好栈.** `GoodE₂` (同地板叠一份) 与 `GoodE₂⟨⟩` (在旧地板上折叠下面的栈, 新地板 $\varphi'$, 地板见证作参数); `repGood₂` 把它们拼成 `repᴿ` 的第 $m+1$ 份. **地板见证** `FWR`: 对 `raise′` 的三种情况, 不提升时沿用旧见证 (`FWc refl`: 新旧 $B$ 定义性相同), 提升时 ($B'=K=1$) 用下标 $2$: `I₂ : Idx 2`、`o₂ : Occ 2 (ψ_Ω(Ω₂))`、`b₂ : 1 ≺ lvl 2`.

**`ZE₂₊`.** 对任意好栈 `G : Goodˢᶠ S ps` 与任意环境, $\psi_0(ps+\psi_\Omega(\Omega_2+1))$ 的符号树 `ψᵉᶠ S z p σ hd (suc (Ωˢ two))` 带证书与标签: 第 $m$ 项 ($\psi_0(ps+\psi_\Omega(\Omega_2)\cdot m)$) 在 $m=0$ 是 `h0ᶠ G`, 在 $m+1$ 是 `repGood₂` 的目标 0 字段.

```agda
I₁ : Idx (natT 1)
I₁ = one⁰ , hs hz , lab1 , nf1

I₂ : Idx (natT 2)
I₂ = natᶜ 2 , natᶜ-HS 2 , lab2 , nf2

LΩ1 : LabL (Ωˢ (suc zero)) (Ωt (natT 1))
LΩ1 = LabL-Ω one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _)

WE₂ : ∀ {φ} {S : Stkᶠ φ} {ps} → GoodWᶠ S ps → ∀ {i ℓ w} (z : Simᴵ (Fᶠ φ) ℓ) (p : i <ᴵ ℓ) (σ : Simᴵ two ℓ) (hd : Hd two ℓ)
      (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → LabL₊ i Ll (ψᵉᶠ S z p σ hd (Ωˢ two)) (πw w ps (ψΩ Ω₂))
WE₂ {S = S} {ps} G z p σ hd Iw ei ki =
  GiEᶠ.giPreEᶠ S ps {z = z} {p = p} {σ = σ} {hd = hd} {q = zero} {f = Ord₊ˢ.up zero} Iw ei ki refl I₁ (≅ᴵ-refl _)
    (λ η x l → WE₁ʷ G l z p (λ q → σ (suc q)) (hyes (σ zero)) Iw ei ki)
    (λ kj η x l → WE₁ʷ G l z (σ zero) (λ q → σ (suc q)) (hyes (σ zero)) I₁ (≅ᴵ-refl _) refl)

module Z₂ {φ} {S : Stkᶠ φ} {ps} (G : Goodˢᶠ S ps) {L} (z : Simᴵ (Fᶠ φ) L) (p : zero <ᴵ L) (σ : Simᴵ two L) (hd : Hd two L) where

  σ₁ : Simᴵ (suc zero) L
  σ₁ q = σ (suc q)

  chainΩ : ℕ → Ordˢ (suc zero)
  chainΩ = iter (λ x → ψᵉᶠ S z (σ zero) σ₁ (hyes (σ zero)) x) (Ωˢ (suc zero))

  chainΩ-≅ : ∀ m → chainΩ m ≅ˢ chainΩ m
  chainΩ-≅ zero    = Ωˢ-refl (suc zero)
  chainΩ-≅ (suc m) = ψᵉᶠ-≅ (hRᶠ G) {z = z} {p = σ zero} {σ = σ₁} {hd = hyes (σ zero)} {z′ = z} {p′ = σ zero} {σ′ = σ₁} {hd′ = hyes (σ zero)}
                            lo1 lo1 (≅ᴵ-refl _) (chainΩ-≅ m)

  γΩ₂ : ℕ → T
  γΩ₂ = γW ps (ψΩ Ω₂) (natT 1)

  chainΩL : ∀ m → LabL (chainΩ m) (γΩ₂ m)
  chainΩL zero    = LΩ1
  chainΩL (suc m) = WE₁ʷ (toW G) (chainΩL m) z (σ zero) σ₁ (hyes (σ zero)) I₁ (≅ᴵ-refl _) refl

  ZE₂ : NF₁ (πw [] ps (ψΩ Ω₂)) → Σ (Goodᴸ (toZ (ψᵉᶠ S z p σ hd (Ωˢ two)))) λ G′ → Lab (forceᴸ _ G′) (πw [] ps (ψΩ Ω₂))
  ZE₂ nu =
    subst (λ W → Σ (Goodᴸ (toZ W)) λ G′ → Lab (forceᴸ _ G′) (πw [] ps (ψΩ Ω₂))) (sym eqf)
          (limᴸ nu cω′ (λ m → proj₁ (outp m)) (λ m → subst (Lab _) (sym (fsm m)) (proj₂ (outp m))))
    where
    eqf = fold1Eᶠ {S = S} {z = z} {p = p} {σ = σ} {hd = hd} {q = zero} {f = Ord₊ˢ.up zero} (inj₁ (via z≅ zero))
    cω′ : cof (πw [] ps (ψΩ Ω₂)) ≡ cω
    cω′ = cofW [] ps (ψᵗ Ωᵗ Ω₂) []
    fsm : ∀ m → fsn (πw [] ps (ψΩ Ω₂)) m ≡ πw [] ps (ψΩ (γΩ₂ m))
    fsm m = gtW [] ps (ψᵗ Ωᵗ Ω₂) [] (natT 1) refl refl m
    outp : ∀ m → Σ (Goodᴸ (toZ (ψᵉᶠ S z p σ₁ (hyes (σ zero)) (chainΩ m)))) λ G′ → Lab (forceᴸ _ G′) (πw [] ps (ψΩ (γΩ₂ m)))
    outp m = ZE₁ᶠ G (chainΩL m) (chainΩ-≅ m) z p σ₁ (hyes (σ zero)) (subst NF₁ (fsm m) (NF₁-fsn nu cω′ m))

Ω₂-≅ : ∀ {φ} {S S′ : Stkᶠ φ} → S ≈ᶠ S′ → ∀ {i i′ ℓ₁ ℓ₂} {z : Simᴵ (Fᶠ φ) ℓ₁} {p : i <ᴵ ℓ₁} {σ : Simᴵ two ℓ₁} {hd : Hd two ℓ₁}
       {z′ : Simᴵ (Fᶠ φ) ℓ₂} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ two ℓ₂} {hd′ : Hd two ℓ₂} → i ≅ᴵ i′ →
       ψᵉᶠ S z p σ hd (Ωˢ two) ≅ˢ ψᵉᶠ S′ z′ p′ σ′ hd′ (Ωˢ two)
Ω₂-≅ {S = S} {S′} H {z = z} {p} {σ} {hd} {z′} {p′} {σ′} {hd′} ei =
  liEᶠ {S = S} {S′ = S′} {z = z} {p = p} {σ = σ} {hd = hd} {z′ = z′} {p′ = p′} {σ′ = σ′} {hd′ = hd′}
       {q = zero} {q′ = zero} {f = Ord₊ˢ.up zero} {g = Ord₊ˢ.up zero} ei (≅ᴵ-refl _)
       (λ x y d → ψᵉᶠ-≅ H lo1 lo1 ei (R→≅ˢ zero d))
       (λ x y d → ψᵉᶠ-≅ H lo1 lo1 (≅ᴵ-refl _) (R→≅ˢ zero d))

FWc : ∀ {φ φ′ ps} → Bᶠ φ ≡ Bᶠ φ′ → FW φ ps → FW φ′ ps
FWc e (fw0 b0)      = fw0 (trans (sym e) b0)
FWc e (fwI Iw o bw) = fwI Iw o (subst (λ B → (B ≺ᴵ _) ⊎ (B ≅ᴵ _)) e bw)

GoodE₂ : ∀ {φ} {S : Stkᶠ φ} {ps} → Goodˢᶠ S ps → (s : FrS φ two) (hp : FrH φ two) →
         Goodˢᶠ (S ▹[ s ∣ hp ] Ωˢ two) (ps ++ ψᵗ Ωᵗ Ω₂ ∷ [])
GoodE₂ G s hp = goodᶠ (λ z p Iw ei ki → WE₂ (toW G) z p (s z) (hp z) Iw ei ki)
                      (λ z p nf → Z₂.ZE₂ G z p (s z) (hp z) nf)
                      (λ z p z′ p′ ei → Ω₂-≅ (hRᶠ G) ei)
                      (FW++ (ψᵗ Ωᵗ Ω₂ ∷ []) (fwᶠ G))

GoodE₂⟨⟩ : ∀ {φ φ′} {S : Stkᶠ φ} {ps} → Goodˢᶠ S ps → (ρ : Simᴵ (Fᶠ φ) (Fᶠ φ′)) (s : FrS φ′ two) (hp : FrH φ′ two) →
           FW φ′ (ps ++ ψᵗ Ωᵗ Ω₂ ∷ []) → Goodˢᶠ (S ▹⟨ ρ ∣ s ∣ hp ⟩ Ωˢ two) (ps ++ ψᵗ Ωᵗ Ω₂ ∷ [])
GoodE₂⟨⟩ G ρ s hp fw = goodᶠ (λ z p Iw ei ki → WE₂ (toW G) (λ q → z (ρ q)) p (s z) (hp z) Iw ei ki)
                              (λ z p nf → Z₂.ZE₂ G (λ q → z (ρ q)) p (s z) (hp z) nf)
                              (λ z p z′ p′ ei → Ω₂-≅ (hRᶠ G) ei)
                              fw

repGood₂ : ∀ {φ φ′} {S : Stkᶠ φ} {ps} → Goodˢᶠ S ps → (ρ : Simᴵ (Fᶠ φ) (Fᶠ φ′)) (s : FrS φ′ two) (hp : FrH φ′ two) →
           FW φ′ (ps ++ ψᵗ Ωᵗ Ω₂ ∷ []) → ∀ m →
           Goodˢᶠ (repᴿ S φ′ ρ s hp (Ωˢ two) (suc m)) (ps ++ replicate (suc m) (ψᵗ Ωᵗ Ω₂))
repGood₂ G ρ s hp fw zero = GoodE₂⟨⟩ G ρ s hp fw
repGood₂ {φ′ = φ′} {S = S} {ps} G ρ s hp fw (suc m) =
  subst (Goodˢᶠ (repᴿ S φ′ ρ s hp (Ωˢ two) (suc (suc m)))) (snoc ps (suc m) (ψᵗ Ωᵗ Ω₂))
        (GoodE₂ (repGood₂ G ρ s hp fw m) s hp)

FWR : ∀ {φ ps x K ℓ w} (κ : K <ᴵ ℓ) (ζ : Simᴵ (Fᶠ φ) ℓ) (d : Dec3 K (Bᶠ φ)) → FW φ ps →
      (Iw : Idx w) → Occ w (x ∷ []) → (K ≺ᴵ lvI Iw) ⊎ (K ≅ᴵ lvI Iw) →
      FW (Raise.φ′ (raise′ φ κ ζ d)) (ps ++ x ∷ [])
FWR {x = x} κ ζ (injᵃ (via e r)) fw Iw o b = FWc refl (FW++ (x ∷ []) fw)
FWR {ps = ps} κ ζ (injᵇ (via e r)) fw Iw o b = fwI Iw (OccΣ ps o) b
FWR {x = x} κ ζ (injᶜ e) fw Iw o b = FWc refl (FW++ (x ∷ []) fw)

o₂ : Occ (natT 2) (ψᵗ Ωᵗ Ω₂ ∷ [])
o₂ = od oh

b₂ : (suc zero ≺ᴵ lvI I₂) ⊎ (suc zero ≅ᴵ lvI I₂)
b₂ = inj₁ (via (≅ᴵ-refl _) zero)

ZE₂₊ : ∀ {φ} {S : Stkᶠ φ} {ps} → Goodˢᶠ S ps → ∀ {L} (z : Simᴵ (Fᶠ φ) L) (p : zero <ᴵ L) (σ : Simᴵ two L) (hd : Hd two L) →
       NF₁ (πw [] ps (ψΩ Ω₂+1)) →
       Σ (Goodᴸ (toZ (ψᵉᶠ S z p σ hd (Ord₊ˢ.suc (Ωˢ two))))) λ G′ → Lab (forceᴸ _ G′) (πw [] ps (ψΩ Ω₂+1))
ZE₂₊ {φ} {S} {ps} G z p σ hd nf =
  limᴸ nf (cE₁ [] ps refl) (λ m → proj₁ (outm m)) (λ m → subst (Lab _) (sym (fE₁ [] ps refl m)) (proj₂ (outm m)))
  where
  Rz = raise φ (σ zero) z
  fwR : FW (Raise.φ′ Rz) (ps ++ ψᵗ Ωᵗ Ω₂ ∷ [])
  fwR = FWR (σ zero) z (<ᴵ-dec (σ zero) (z (ιᶠ φ))) (fwᶠ G) I₂ o₂ b₂
  nfm : ∀ m → NF₁ (πw [] ps (replicate m (ψᵗ Ωᵗ Ω₂)))
  nfm m = subst NF₁ (fE₁ [] ps refl m) (NF₁-fsn nf (cE₁ [] ps refl) m)
  outm : ∀ m → Σ (Goodᴸ (toZ (run (repᴿ S (Raise.φ′ Rz) (Raise.ρF Rz) (λ ζ′ q → ζ′ (Raise.ρK Rz q)) (λ _ → hno) (Ωˢ two) m)
                                (Raise.ζ′ Rz) p))) λ G′ → Lab (forceᴸ _ G′) (πw [] ps (replicate m (ψᵗ Ωᵗ Ω₂)))
  outm zero    = subst (λ t → Σ (Goodᴸ (toZ (run S (λ q → Raise.ζ′ Rz (Raise.ρF Rz q)) p))) λ G′ → Lab (forceᴸ _ G′) (ψᵗ [] t ∷ []))
                       (sym (++-identityʳ ps))
                       (h0ᶠ G (λ q → Raise.ζ′ Rz (Raise.ρF Rz q)) p (subst (λ t → NF₁ (ψᵗ [] t ∷ [])) (++-identityʳ ps) (nfm 0)))
  outm (suc m) = h0ᶠ (repGood₂ G (Raise.ρF Rz) (λ ζ′ q → ζ′ (Raise.ρK Rz q)) (λ _ → hno) fwR m) (Raise.ζ′ Rz) p (nfm (suc m))
```

**读法.** 推导链: `ZE₂₊` → `repGood₂` → `GoodE₂⟨⟩`/`GoodE₂` → (`WE₂` → `WE₁ʷ` → … → `GoodΩʷ`) 与 (`ZE₂` → `ZE₁ᶠ` → … → `GoodΩᶠ`). 低目标的弹栈 (OmegaSqBase 的 `low-pop`) 正是 `GoodΩᶠ` 的 `ZF` 情况: 第二份 $\Omega_2$ 帧的折叠落到指数 $0$ 时, 栈是 "第一份帧 + 新地板", 三歧给 $0\prec B'=1$, 闭包界为 $F'\cong2$, 支配由地板见证的下标 $2$ (出现于第一份帧的标签 $\psi_\Omega(\Omega_2)$) 经 `domP` 给出. 这里地板见证是**按帧**给的 (`o₂`, `b₂`), 不是从一般的推导里读出来的; 一般的第 $k$ 层后继需要的就是这样一个见证, 见 §11.

## §10 对比表: 紧界与非紧

| | 紧界 (OmegaExpBase/OmegaSqBase) | 非紧 (本文) |
|---|---|---|
| 栈类型 | `Stk`: 帧证据 `zero <ᴵ ℓ` | `Stkᶠ φ`: 帧证据 `Simᴵ (Fᶠ φ) ℓ`, 地板 `Flr` $(F,B,\iota_B,\iota_z,F\sqsubseteq B+1)$ |
| $\hat\Omega$ 弹出的界 | $i+1$ | $B\preceq i$: $i+1$; $i\prec B$: $F\ (\cong B+1)$ |
| 第 0 点环境层号 | $i+1$ | `Mlev F (i+1)` 或 `Mlev (i+1) F` |
| 分支环境层号 | `Mlev (i+1) η e` | `Mlev3 · · η` (三项) |
| 第 0/1 层后继指数 | `repᴷ` (`s₀`/`σ1`) | `repᶠ`, 地板不动 |
| 第 $\ge2$ 层后继 | 占位 $0$ | `raise` + `repᴿ` (第 1 份在旧地板上); 极限层要把手 `hyes` |
| 剩余占位 | 第 $\ge2$ 层的一切后继 | 只剩 "极限层、无字面把手" 的后继 |
| `low-pop` 处 | `noSim21`, `low-tree ≡ kz` | 闭包界 `Mlev 1 2 _`, 第 0 点可算 (`refl`) |
| 互模拟 `ŝ≅` 的界 | $i+1\cong i'+1$ | 同, 或 $F\cong F$ (三歧语义稳定) |
| 支配 | `domS` (尾巴中的出现) / `one⊑lab` | 另加 `domP` (前缀中的出现, 地板见证) |
| `Goodᴸ`/`gc`/`forceᴸ`/`limᴸ`/`ĉᴸ-mk`/`LabL`/`gŝ` | 原样 | 原样 |
| 好栈 | `Goodˢ` (3 字段) | `Goodˢᶠ` (+ `FW`), W 版 `GoodWᶠ` |
| 指数引理 | 第 $\le1$ 层 | 第 $\le1$ 层 (`…ᶠ`, `…ʷ`) + 帧 $\psi_\Omega(\Omega_2)$ (`WE₂`, `ZE₂`, `ZE₂₊`) |

## §11 结论与边界

**任务 1 (栈类型带地板).** `Stkᶠ φ`, `φ : Flr`; 地板随帧变化: $\hat\Omega$、$\hat\Omega^2$、第 0、1 层指数帧不动, 第 $k$ 层后继 ($k=K+1$, $K\ne0$, 或极限 $k$ 带把手时 $K=k$) 经 `raise` 变为 "$\max(B,K)$" (字面上是两项 `Mlev`, 语义上 $F'\cong\max(B,K)+1$). 证据以 `Sim` 形式携带, 不是 $\sqsubseteq$: 字面性要求 (帧的 `Sim`、三歧的输入) 迫使地板本身字面地出现在环境层号里.

**任务 2 (非紧闭包).** `popΩ`/`popΩ²` 按 $B$ 与 $i$ 的三歧取界 $i+1$ 或 $F$, 环境层号字面装着二者. `noSim21` 的阻碍在 `low-pop` 处消失 (§3, `refl`). `GoodΩᶠ` 给出非紧闭包的证书与标签, 新增的支配论证是 `domP` + 地板见证; `GoodLBase` 的 `gŝ` 地板与 `Goodᴸ` 都未改. 互模拟只需两侧同地板.

**任务 3 (第 $\ge2$ 层指数子句).** 树侧: 一切后继层 ($k=K+1$) 与带把手的极限层都是真子句; 只剩 "极限层、经 `up (self n)` 丢了把手" 的后继是占位 (NonTight §4 有编译见证, 是否在 $t_{\Omega2}$ 中可达未定). 标签侧: 第 0、1 层全部移植; 第 2 层只对帧 $\psi_\Omega(\Omega_2)$ (及其重复) 证明, 即 `ZE₂₊`. **一般的 `WEₖ`/`ZEₖ` 未写**, 精确缺口两条: (a) 第 $k\ge2$ 层的 `gs` 行要一个地板见证 "前驱标签中有带 `Idx` 的下标 $w$, $K\preceq\mathtt{lvl}\,w$", `LabL` 不排斥小标签的高层树 (如第 2 层的 $\uparrow\uparrow5$, 其后继提升地板而标签里没有 $\ge1$ 的下标), 所以要么是推导上的遗传前提 (对 `gi` 行的输入逆变地要求), 要么要换一种不经出现的支配论证; (b) 目标 $0$ 的引理要第 $\ge2$ 层的自互模拟, 而 §7 读法说明 `≅ˢ` 的层号不对齐会使两侧地板不同, 需要层号对齐的互模拟.

**边界.** 不改 `src/`、`archive/` 与已有的 Align 文件, README 未改. 停机与正性检查全部默认通过.

