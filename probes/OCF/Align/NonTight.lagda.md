# 非紧闭包下的 $\psi_0(\Omega_\Omega^2)$: 低目标后代带标签, 全标签仍差一般层的指数引理

> 接 [NonTightBase](NonTightBase.lagda.md) (地板栈 `Stkᶠ`、非紧弹栈 `popΩ`、指数折叠 `ψᵉᶠ`、移植的带前缀引理与好栈、第 2 层帧 $\psi_\Omega(\Omega_2)$ 的 `ZE₂₊`). 本文是决定性检验 (任务 4).
>
> 结论先说:
>
> 1. **`TΩ2-label` 未得 (§3–§4).** 非紧树 `TΩ2ᶠˢ = (∅ᶠ ▹Ω̂²ᶠ) …` 的形状是 `ŝ 1 t₀ᶠ gΩᶠ` (`refl`), 第 0 点无条件带标签 (`GLΩ0ᶠ`), 条件定理 **`TΩ2-condᶠ : BranchΩᶠ → Σ (Goodᴸ (toZ TΩ2ᶠˢ)) λ G → Lab (forceᴸ _ G) tΩ2`** 已证, 其下 `TΩ2-stepᶠ` 是 `refl`. `BranchΩᶠ` (每个带标签链点 $Y$ 处分支 $\psi_0(\Omega_\Omega\cdot\Omega_{\mathtt{lvl}\,Y})$ 的证书与标签) 仍未证: 它要对指数 $\Omega_\eta$ ($\eta=\mathtt{lvl}\,Y$ 是巨大的可数层号) 做**一般层**的 `WEₖ`/`ZEₖ`, 本文与 NonTightBase 只做到第 $\le1$ 层与第 2 层的帧 $\psi_\Omega(\Omega_2)$. 缺的两条引理精确地在 NonTightBase §11 (a)(b) 与本文 §4. 第一个在新树上无标签的有限情形是 $\psi_0(\Omega_\Omega\cdot\Omega_3)$: 它的链点是任意的第 2 层指数 $\psi_2(\cdots)$.
> 2. **低目标后代现在带标签 (§2).** OmegaSqBase 的 `low-unlab` 的那个记号点 $\psi_0(\psi_\Omega(\Omega_2+1))$ ($t_{\Omega2}$ 沿 `pathLow ++ [2,0,0]` 的后代, 也是 $t_{\Omega2}[1]$ 沿 OmegaSq `branch-low` 的后代) 在非紧树上**无条件带标签**: **`TΩ₂₊-label : Lab (forceᴸ _ (proj₁ GLΩ₂₊)) (ψΩ₀ Ω₂+1)`**. 标签是遗传的, 所以它下面的 `low-pop` 点 $\psi_0(\psi_\Omega(\Omega_2)+\Omega_\Omega)$ (非紧闭包, 界 $\cong2$) 也带标签. 这是第一个越过紧界上限 $\psi_0(\Omega_\Omega\cdot\Omega_2)$ 的 $\Omega$-指数标签: $\psi_0(\Omega_\Omega\cdot\Omega_2\cdot\omega)$.
> 3. **一致性 (§1).** 第 0 层指数 (`Tη-agreeᶠ`, 一切带结构标签的 $\eta$)、$\psi_0(\Omega_\Omega\cdot\Omega)$ (`TΩ2-0-agreeᶠ`)、$\psi_0(\Omega_\Omega\cdot\Omega_2)$ (`TΩ₂-agree`) 的新树与 OmegaExp/OmegaSq 的树经 `Lab-uniq` 互为 $\cong$ (字面不等: 环境层号不同).
> 4. **剩余的树侧占位 (§4).** 极限层的低目标后继真实出现在 $t_{\Omega2}$ 的后代中 (`lim-walk`/`lim-term`/`lim-pop`, `refl`): $\psi_0(\psi_\Omega(\Omega_\omega+1))$ 与其上的弹栈 $\psi_0(\psi_\Omega(\Omega_\omega)+\Omega_\Omega)$. 在带字面把手的折叠里它是真树 (NonTightBase §3 的 `limᶠ`, `limbound`). 无把手的极限层后继仍是占位 (`res-tree`, `res-unlab`, 合成例); 它在 $t_{\Omega2}$ 中是否可达未定.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块与 NonTightBase, 不改任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NonTight where
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
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_;
  z<suc; H1-pen; H1-fsT; trˢ; tr⁻ˢ; sqˢ; walkˢ; kind; Kind; kz; ks; kl; kĉ; kc)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; γT; sucT; cmpᵀ; Cmp; lt; eq; gt;
              []<; hd<; tl<; lv<; ar<; cofA; cofψ0; cofψ₊) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fs-rep; fs-ω)
open import OCF.Align.Bachmann using (fs-gt; pen→<; gt→≤; clash)
open import OCF.Align.Closure using (Pen; fsT₊-pen′; lt→<)
open import OCF.Align.StandardOmega using (NF₁; NF₁-pred; NF₁-fsn; walk; walkD; tO-desc-NF)
open import OCF.Align.Standard using (Desc; d₀; Ctbl; c[]; c∷)
open import OCF.Align.SystemOmega using (Occ; oh; od; os; ot; occ<)
open import OCF.Align.Stage2 using (Ωᵗ; tO)
open import OCF.Align.UniformS hiding (run)
open import OCF.Align.Stage2Label using (one⁰; Lab-oc)
open import OCF.Align.DecoupleBase using (ΩΩ; ŝ-reflg)
open import OCF.Align.Decouple using (Idx; lvI; Ilt; Ieq; kdI; kdI′; gtν; kdI[]; cofP)
open import OCF.Align.GoodLBase
open import OCF.Align.OmegaExpBase using (σ⊥; πw; onCons; cofΣ; predΣ; fsnΣ; fsTΣ; OccΣ; cofW; repW; ωW; γW; γW-eq;
  gtW; penW; H1W; 1<π; ne-w; domS; 1<γ; rep-snoc; snoc)
open import OCF.Align.OmegaExp using (ψΩ₀; GLη; Tη-label; tΩ1-NF; TΩ2-0ᴸ; TΩ2-0-label)
open import OCF.Align.OmegaKBase using (tΩ2; tΩ2-NF)
open import OCF.Align.OmegaSq using (tΩ₂; tΩ₂-NF; TΩ₂ᴸ; TΩ₂-label)
open import OCF.Align.Stage2 using (Lab-uniq)
open import OCF.Align.Prefix using (z1)
open import OCF.Align.NonTightBase
open import OCF.Align.OmegaSqBase using (ψΩ; Ω₂; Ω₂+1; low-NF; low-term; pathLow)
open import OCF.Align.OmegaSq using (branch-low)
```

## §1 一致性: 新树与旧定理

**第 0 层指数.** `Tηᶠ X` 是非紧折叠下的 $\psi_0(\Omega_\Omega\cdot\omega^X)$, 证书与标签是 `GoodE₀ᶠ Good∅ᶠ` 的目标 0 字段; 与 OmegaExp 的 `Tη-label` 同标签.

```agda
Tηᶠ : Ordˢ zero → Ordˢ zero
Tηᶠ X = run (∅ᶠ ▹[ (λ _ → σ⊥) ∣ (λ _ → hno) ] X) (σ1 z1) z1

GLηᶠ : ∀ {X η} → Lab0ᴸ X η → X ≅ˢ X → NF₁ (ψΩ₀ η) → Σ (Goodᴸ (toZ (Tηᶠ X))) λ G → Lab (forceᴸ _ G) (ψΩ₀ η)
GLηᶠ l ex nf = h0ᶠ (GoodE₀ᶠ Good∅ᶠ l ex) (σ1 z1) z1 nf

Tη-agreeᶠ : ∀ {X η} (l : Lab0ᴸ X η) (ex : X ≅ˢ X) (nf : NF₁ (ψΩ₀ η)) →
            forceᴸ _ (proj₁ (GLηᶠ l ex nf)) ≅ forceᴸ _ (proj₁ (GLη l ex nf))
Tη-agreeᶠ l ex nf = Lab-uniq (proj₂ (GLηᶠ l ex nf)) (Tη-label l ex nf)
```

**$\psi_0(\Omega_\Omega\cdot\Omega_2)$.** 非紧树 `TΩ₂ᶠˢ` 由 `Z₂.ZE₂` 标记 (NonTightBase §9; 这里没有提升地板, 链与输出的指数都在第 1 层), 与 OmegaSq 的 `TΩ₂-label` 同标签.

```agda
TΩ₂ᶠˢ : Ordˢ zero
TΩ₂ᶠˢ = ψᵉᶠ ∅ᶠ (σ1 z3) z3 (λ q → suc q) (hyes zero) (Ωˢ two)

GLΩ₂ᶠ : Σ (Goodᴸ (toZ TΩ₂ᶠˢ)) λ G → Lab (forceᴸ _ G) tΩ₂
GLΩ₂ᶠ = Z₂.ZE₂ Good∅ᶠ (σ1 z3) z3 (λ q → suc q) (hyes zero) tΩ₂-NF

TΩ₂-agree : forceᴸ _ (proj₁ GLΩ₂ᶠ) ≅ TΩ₂ᴸ
TΩ₂-agree = Lab-uniq (proj₂ GLΩ₂ᶠ) TΩ₂-label
```

**读法.** 两个 $\cong$ 都是 `Lab-uniq` (Stage2): 同一个标准形标签的两棵计值树互模拟. 字面上不等, 因为非紧弹栈的环境层号是 `Mlev F (i+1)` 而不是 $i+1$ (即使地板 $B=0$, 界仍是 $i+1$).

## §2 低目标后代: $\psi_0(\psi_\Omega(\Omega_2+1))$ 带标签

**记号.** OmegaSqBase 的 `low-term` 与 OmegaSq 的 `branch-low`: 这个点是 $t_{\Omega2}$ 的后代, 也是第一个链点分支 $t_{\Omega2}[1]$ 的后代; 它是第 2 层后继指数在目标 $0$ 处 (低目标), 紧界下只能放占位 (`low-unlab`).

**定理.** 空栈, 目标 $0$, 环境层号 $3$; 树是 `ψᵉᶠ ∅ᶠ … (suc (Ωˢ two))`, 后继子句在第 2 层, 经 `raise` 把地板从 $B=0$ 提到 $B'=1$.

```agda
_ : walk (ψΩ₀ (E.ψ (natT 2) (natT 1) ∷ [])) (2 ∷ 0 ∷ 0 ∷ []) ≡ ψΩ₀ Ω₂+1
_ = low-term

_ : walk (fsn tΩ2 1) (0 ∷ 1 ∷ 0 ∷ 0 ∷ 3 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ []) ≡ ψΩ₀ Ω₂+1
_ = branch-low
```

```agda
TΩ₂₊ˢ : Ordˢ zero
TΩ₂₊ˢ = ψᵉᶠ ∅ᶠ (σ1 z3) z3 (λ q → suc q) (hyes zero) (Ord₊ˢ.suc (Ωˢ two))

GLΩ₂₊ : Σ (Goodᴸ (toZ TΩ₂₊ˢ)) λ G → Lab (forceᴸ _ G) (ψΩ₀ Ω₂+1)
GLΩ₂₊ = ZE₂₊ Good∅ᶠ (σ1 z3) z3 (λ q → suc q) (hyes zero) low-NF

TΩ₂₊-label : Lab (forceᴸ _ (proj₁ GLΩ₂₊)) (ψΩ₀ Ω₂+1)
TΩ₂₊-label = proj₂ GLΩ₂₊
```

**读法.** 推导在 NonTightBase §9 的读法里: 第 $m$ 项 $\psi_0(\psi_\Omega(\Omega_2)\cdot m)$ 的栈是 `repᴿ` 的第 $m$ 份, 第 1 份在旧地板上 (`GoodE₂⟨⟩`), 其后在新地板上 (`GoodE₂`); 每份帧的值 (指数 $\Omega_2$) 在目标 0 处沿第 1 层的链折叠 (`ZE₂`), 在目标 $\ne0$ 处穿透或沿第 1 层折叠 (`WE₂`). 第二份帧值里的 $\hat\Omega$ 弹出 (`low-pop`) 在 `GoodΩᶠ` 的 `ZF` 情况: $0\prec B'=1$, 界 $F'\cong2$, 支配由第一份帧标签里的下标 $2$ 经 `domP` 给出. OmegaSqBase 的 `low-unlab` 说的是紧界折叠的树 (占位 $0$) 上没有证书能带这个标签; 这里换成非紧折叠后, 证书与标签都是构造出来的.

## §3 $\psi_0(\Omega_\Omega^2)$ 的非紧树与条件定理

**树.** `TΩ2ᶠˢ` = 空栈上的 $\hat\Omega^2$ 帧在目标 0、环境层号 1 处的弹出. 空栈地板 $B=0$, 三歧给 $0\cong0$, 界 $1$, 第 0 点 `t₀ᶠ` 的指数是 $\Omega_1$ (第 1 层), 分支 `gΩᶠ η e` 的指数是 $\Omega_\eta$, 在 `Mlev3 1 1 (η+1)` 上计算并带字面把手 `hyes (lim 2 zero)`.

```agda
TΩ2ᶠˢ : Ordˢ zero
TΩ2ᶠˢ = run (∅ᶠ ▹Ω̂²ᶠ) (σ1 z1) z1

t₀ᶠ : Ordˢ zero
t₀ᶠ = ψᵉᶠ ∅ᶠ {ℓ = Mlev (suc zero) (suc zero) (⊑ᴵ-trans ⊑ᴵ-refl (s⊑ z≅ zero))} (λ q → lim 0 q) (lim 1 zero)
          (σ1 (lim 0 zero)) hno (Ωˢ (suc zero))

gΩᶠ : (η : Ordᴵ) → suc zero ⊑ᴵ η → Ordˢ zero
gΩᶠ η e = ψᵉᶠ ∅ᶠ {ℓ = Mlev3 (suc zero) (suc zero) (suc η) (⊑ᴵ-trans ⊑ᴵ-refl (s⊑ z≅ zero)) (⊑ᴵ-trans e (⊑-suc η))}
              (λ q → lim 0 q) (lim 1 zero) (λ q → lim 2 (suc q)) (hyes (lim 2 zero)) (Ωˢ η)

_ : TΩ2ᶠˢ ≡ Ord₊ˢ.ŝ (suc zero) t₀ᶠ gΩᶠ
_ = refl
```

**条件定理.** 与 OmegaSq 的 `TΩ2-cond` 同构: 第 0 点由 `ZE₁ᶠ` 无条件标记 (与 OmegaExp 的 `TΩ2-0ᴸ` $\cong$), 支配是 `one⊑lab` (界 $1$), 唯一前提是分支引理 `BranchΩᶠ`.

```agda
GLΩ0ᶠ : Σ (Goodᴸ (toZ t₀ᶠ)) λ G → Lab (forceᴸ _ G) (fsn tΩ2 0)
GLΩ0ᶠ = ZE₁ᶠ Good∅ᶠ LΩ1 (Ωˢ-refl (suc zero)) {L = Mlev (suc zero) (suc zero) (⊑ᴵ-trans ⊑ᴵ-refl (s⊑ z≅ zero))} (λ q → lim 0 q) (lim 1 zero) (σ1 (lim 0 zero)) hno tΩ1-NF

TΩ2-0-agreeᶠ : forceᴸ _ (proj₁ GLΩ0ᶠ) ≅ TΩ2-0ᴸ
TΩ2-0-agreeᶠ = Lab-uniq (proj₂ GLΩ0ᶠ) TΩ2-0-label

BranchΩᶠ : Set
BranchΩᶠ = ∀ m Y (hY : HS Y) → Lab Y (fsn tΩ2 m) → (e : suc zero ⊑ᴵ toLevel Y hY) →
           Σ (Goodᴸ (toZ (gΩᶠ (toLevel Y hY) e))) λ G → Lab (forceᴸ _ G) (fsn tΩ2 (suc m))

TΩ2-condᶠ : BranchΩᶠ → Σ (Goodᴸ (toZ TΩ2ᶠˢ)) λ G → Lab (forceᴸ _ G) tΩ2
TΩ2-condᶠ B =
  ĉᴸ-mk tΩ2-NF refl K (proj₁ GLΩ0ᶠ) (proj₂ GLΩ0ᶠ)
        (λ k → CCᴸ.Gg K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k)))
        (λ k → CCᴸ.lE K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k)))
  where
  K = ccᴸ (fsn tΩ2) (proj₁ GLΩ0ᶠ) (proj₂ GLΩ0ᶠ) (one⊑lab _ (proj₂ GLΩ0ᶠ) tΩ1-NF []<)
          (λ m Y hY lY e → proj₁ (B m Y hY lY e)) (λ m Y hY lY e → proj₂ (B m Y hY lY e))
          (λ m Y hY lY e → one⊑lab _ (proj₂ (B m Y hY lY e)) (NF₁-fsn tΩ2-NF refl (suc m)) []<)

module _ (B : BranchΩᶠ) where
  TΩ2ᶠᴸ : Ordᶜ zero
  TΩ2ᶠᴸ = forceᴸ (toZ TΩ2ᶠˢ) (proj₁ (TΩ2-condᶠ B))

  χΩ2ᶠ : ℕ → Ordᶜ zero
  χΩ2ᶠ n = sq′ TΩ2ᶠᴸ n
    where
    sq′ : Ordᶜ zero → ℕ → Ordᶜ zero
    sq′ (Ord₊.lim f) n = f n
    sq′ x n = x

  _ : TΩ2ᶠᴸ ≡ Ord₊.lim χΩ2ᶠ
  _ = refl

  TΩ2-stepᶠ : ∀ n → FGH TΩ2ᶠᴸ n ≡ FGH (χΩ2ᶠ n) n
  TΩ2-stepᶠ n = refl
```

**读法.** 外层的链证书、第 0 点、支配与单调都已无条件; `BranchΩᶠ` 的第 $m$ 个实例要的是 $\psi_0(\Omega_\Omega\cdot\Omega_{\mathtt{lvl}\,Y})$ 的证书和标签, $Y$ 带标签 $t_{\Omega2}[m]$. 对它做的折叠: 指数 `Ωˢ η` 在第 $\eta$ 层 ($\eta$ 是 `toLevel` 造的大层号), `lim` 逐项降到 `Ωˢ (f n)`, 后继层 $f\,n=j+1$ 处沿第 $j$ 层的链折叠, 链点 $\psi_j(\cdots\psi_\Omega(\chi))$ 的指数 $\chi$ 是**任意第 $j$ 层**的树 (由 `WEⱼ` 标记), 输出要 `ZEⱼ`. 所以需要一般层的 `WEₖ`/`ZEₖ`.

## §4 精确的停点

**(i) 极限层的低目标后继真实出现.** 用 `ebo.py` 的广度搜索 (临时脚本 `exp/nontight/bfst.py`, 分支 $0..2$, 约 19 万个后代) 找到: $t_{\Omega2}$ 沿 `limPath` (8 步) 到 $\psi_0(\psi_\Omega(\Omega_{\omega+1}))$, 再 7 步到 $\psi_0(\psi_\Omega(\Omega_\omega+1))$ ($\omega=\psi_0(1)$, 指数是**极限层** $\omega$ 的后继, 目标 0), 再 $[2,0,1]$ 是它上面的 $\hat\Omega$ 弹栈. 全部 `refl`:

```agda
ωᵀ : T
ωᵀ = ψᵗ [] (natT 1) ∷ []

limPath : List ℕ
limPath = 1 ∷ 0 ∷ 1 ∷ 0 ∷ 1 ∷ 2 ∷ 2 ∷ 1 ∷ []

lim-walk : walk tΩ2 limPath ≡ ψΩ₀ (Ωt (E.sucT ωᵀ))
lim-walk = refl

lim-term : walk (ψΩ₀ (Ωt (E.sucT ωᵀ))) (1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ []) ≡ ψΩ₀ (Ωt ωᵀ ++ E.𝟏 ∷ [])
lim-term = refl

lim-pop : walk (ψΩ₀ (Ωt ωᵀ ++ E.𝟏 ∷ [])) (2 ∷ 0 ∷ 1 ∷ []) ≡ ψᵗ [] (ψᵗ Ωᵗ (Ωt ωᵀ) ∷ ΩΩ ∷ []) ∷ []
lim-pop = refl
```

树侧: NonTightBase §3 的 `limᶠ` 在同一相对路径上是真的极限, 弹栈界为 `Mlev 1 (ω+1) _` (`limbound`): $\Omega_{\omega+1}$ 的折叠沿第 $\omega$ 层的链, 链点经 `up zero` 进入, 带着字面把手 $\omega<^\mathsf I\ell$, `raise` 用它与地板比较. 在真正的 `TΩ2ᶠˢ` 里, 这个指数的层号是某个带标签 $\omega+1$ 的树的 `toLevel`, 即 `suc (lim …)`, 情形相同.

**(ii) 剩余的占位.** 若极限层的后继经 `up (self n)` 到达 (丢了把手), `ψᵉᶠ` 仍给占位 $0$; 下面是一个合成的编译见证 (指数 `up (self 0) (suc zero)`, 第 $\omega$ 层的后继). 它是否出现在 $t_{\Omega2}$ 的带标签点中未定: `up (self n)` 在指数里只来自 `Ωˢ` 在极限层上的展开, 而 `Ωˢ (f n)` 在自己的层上没有后继; 一个反例要求某个链点输出在极限层 $f\,n$ 上有后继且经 `self n` 进入.

```agda
Λ : Ordᴵ
Λ = lim (λ _ → ωᵗ) (λ _ → ⊑ᴵ-refl)

resX : Ordˢ Λ
resX = Ord₊ˢ.up (self 0) (Ord₊ˢ.suc Ord₊ˢ.zero)

resˢ : Ordˢ zero
resˢ = ψᵉᶠ ∅ᶠ {ℓ = suc Λ} (σ1 (suc (lim 0 z<ω))) (suc (lim 0 z<ω)) suc (hyes zero) resX

res-tree : kind resˢ ≡ kz
res-tree = refl

res-unlab : (G : Goodᴸ (toZ resˢ)) → Lab (forceᴸ _ G) (ψΩ₀ (natT 1)) → ⊥
res-unlab gz (l0 () e)
res-unlab gz (l1 () e l)
res-unlab gz (lω c () h)
```

**(iii) 缺的引理 (精确).** `BranchΩᶠ 0` 要 $\psi_0(\psi_\Omega(\Omega_{t_{\Omega2}[0]}))$ 的证书与标签; 按 §3 的读法, 需要:

1. **一般层的 `WEₖ`**: 对第 $k$ 层 `LabL₊ k` 推导递归 (行 `gz`/`gl`/`gu`/`gi`/`gĉ`/`gŝ` 与 NonTightBase 的 `WE₁ʷ` 同形, `gi` 行的 $j\ne0$ 折叠用 `WEⱼ` 标链点); `gs` 行在 $k=K+1$, $K\ne0$ (或极限 $k$) 时提升地板, 需要地板见证: **前驱标签 $\theta$ 中有带 `Idx` 的下标 $w$ 出现, $K\preceq\mathtt{lvl}\,w$.** 这不能从 `LabL` 读出 (`LabL` 不排斥小标签的高层树, 例如第 2 层的 $\uparrow\uparrow5$ 的后继提升地板到 $1$, 而标签 $5$ 里没有 $\ge1$ 的下标). 可行的形式是推导上的遗传前提 `HD`: `gs` 节点带见证, `gi` 行对**输入**逆变地要求 `HD`; 于是 `WEₖ` 的输出 (它们作为链点又成为 `gi` 行的输入) 也要带 `HD`, 即 GoodLBase/OmegaExpBase 的 `PreS₊`、`LRep`、`LabL-Ω`、`gŝ` 搬运都要配 `HD` 的保持引理. 语义上见证总是存在 (第 $j$ 层的树的首项下标层号 $\cong j$, 和的后继的前驱以它开头), 但这是关于 $\psi$ 输出形状的新不变量, 未写.
2. **一般层的 `ZEₖ`**: 除上一条外还要第 $k\ge2$ 层指数的自互模拟 (第 0 层链原子 `Atomᴸ` 需要 $x\cong^\mathsf s x$). `ψᵉᶠ-≅` 只对 `Lo` 层成立: `≅ˢ` 可以经 `upˡ`/`upʳ` 让两侧在不同层号的后继上对齐, 一侧提升地板一侧不提升, 弹出闭包的界不 $\cong$, `ŝ≅` 失败. 需要 "层号对齐的" 互模拟, 或只对自互模拟 (同一棵树) 陈述并证明对齐.

第一个在非紧树上无标签的有限情形: $\psi_0(\Omega_\Omega\cdot\Omega_3)=\psi_0(\psi_\Omega(\Omega_3))$; 沿第 2 层的链折叠, 链点是 $\psi_2(\cdots\psi_\Omega(\chi))$, $\chi$ 是一般的第 2 层树 (例如 OmegaSqBase `pathLow` 上的 $\psi_2(1)=\Omega_2\cdot\omega$, 它的后继 $\Omega_2+1$ 在 §2 只因为指数恰是 `Ωˢ two` 才有了地板见证 `o₂`/`b₂`).

## §5 对比表

| | OmegaSq (紧界) | 本文 (非紧) |
|---|---|---|
| 栈 | `Stk` | `Stkᶠ φ` (地板 `Flr`) |
| $\psi_0(\psi_\Omega(\Omega_2+1))$ (`low-term`) | 占位 $0$, `low-unlab` | **`TΩ₂₊-label`** |
| `low-pop` 的弹栈 | `noSim21` | 界 `Mlev 1 2 _` 的闭包, 由 `GoodΩᶠ`/`ZF` 标记 |
| 极限层后继 ($\Omega_\omega+1$) | 占位 | 带把手时真树 (`limᶠ`); 无把手时占位 (`res-tree`) |
| $\psi_0(\Omega_\Omega\cdot\omega^\eta)$ | `GLη′` | `GLηᶠ`, `Tη-agreeᶠ` ($\cong$) |
| $\psi_0(\Omega_\Omega\cdot\Omega)$ | `TΩ2-0′-label` | `GLΩ0ᶠ`, `TΩ2-0-agreeᶠ` ($\cong$) |
| $\psi_0(\Omega_\Omega\cdot\Omega_2)$ | `TΩ₂-label` | `GLΩ₂ᶠ`, `TΩ₂-agree` ($\cong$) |
| $\psi_0(\Omega_\Omega^2)$ | `TΩ2-cond` (前提 `BranchΩ`) | `TΩ2-condᶠ` (前提 `BranchΩᶠ`) |
| `BranchΩ` 的阻碍 | 低目标帧放不进紧闭包 | 一般层 `WEₖ`/`ZEₖ` 未写: 地板见证的遗传前提 + 层号对齐的互模拟 |

## §6 结论与边界

**字面成立 (`refl`):** `TΩ2ᶠˢ ≡ ŝ 1 t₀ᶠ gΩᶠ`; `lim-walk`, `lim-term`, `lim-pop`; `res-tree`; 条件下 `TΩ2ᶠᴸ ≡ lim χΩ2ᶠ` 与 `TΩ2-stepᶠ`; NonTightBase §3 的 `lowᶠ` 与 `limᶠ` 各点的 `kind` (含界 `Mlev 1 2 _` 与 `limbound`); 引用的 `low-term`, `branch-low`.

**定理 (标签按 Correspond 的 `Lab`, 树只到 $\cong$):**

1. **`TΩ₂₊-label : Lab (forceᴸ _ (proj₁ GLΩ₂₊)) (ψΩ₀ Ω₂+1)`** (无条件), 一般形式 NonTightBase 的 `ZE₂₊` (任意好栈前缀、任意环境).
2. `Tη-agreeᶠ`, `TΩ2-0-agreeᶠ`, `TΩ₂-agree`.
3. **`TΩ2-condᶠ : BranchΩᶠ → Σ (Goodᴸ (toZ TΩ2ᶠˢ)) λ G → Lab (forceᴸ _ G) tΩ2`** (条件定理).
4. 编译的否定: `res-unlab` (无把手的极限层后继仍是占位).

**标签状态.** $\psi_0(\Omega_\Omega\cdot\Omega_2\cdot\omega)$ ($=\psi_0(\psi_\Omega(\Omega_2+1))$) 的遗传标签是**无条件定理**, 越过了紧界设计的上限 $\psi_0(\Omega_\Omega\cdot\Omega_2)$. **$\psi_0(\Omega_\Omega^2)$ 的标签未得**; 非紧闭包本身 (弹栈、证书、支配) 不再是阻碍, 停点是 `BranchΩᶠ 0`, 缺 §4 (iii) 的两条一般层引理; 第一个无标签的有限情形是 $\psi_0(\Omega_\Omega\cdot\Omega_3)$. 封存的 src BTBO 不受影响.

**边界.** 不改 `src/`、`archive/` 与已有的 Align 文件, README 未改. 数值未算.

