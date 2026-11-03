> **机械克隆.** 由 `GoodLBase` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 只在带标签的计值点处量化的证书 `Goodᴸ`

> 接 [Omega2](Omega2.lagda.md) §5 的出路 (a). 本文是 [GoodL](GoodL.lagda.md) 的前半: 定义证书 `Goodᴸ`, 补上记号侧缺的 `fs-mono₁`, 并把 DecoupleBase 的原子与一级标签、Omega2Base 的 `LabS`/`PreS₊`/`Pre0V` 改写成 "证书与标签由同一个递归造出" 的形式. 决定性检验 (无条件的 `Lab T2 t2`) 在 GoodL.
>
> 结论先说:
>
> 1. **`Goodᴸ` (§1).** 可容许的计值点 = "某个带标签 $\gamma_m$ 的树的层号", 标签序列 $\gamma:\mathbb N\to T$ 是证书 `gc` 的字段; `Gg`/`lE`/`dE` 只对这样的点量化 (`∀ m Y hY → Lab Y (γ m) → …`), 稳定性是字段 `lE` (在带标签 $\gamma_m$ 的点处计值带标签 $\gamma_{m+1}$). 输出证书 `Go` **只在链点处**给出, 链点由证书字段生成 (`ptsᴸ`, 在 `gc` 的类型里用 `let`). 去掉了 `Goodᶻ` 的链单调 `m₀`/`mE`, 输出单调只要求相邻链点. `Goodᴸ : Z → Set` (不需要 `Set₁`: 序列是数据, 不是谓词). `forceᴸ` 只读输出, 停机与正性一次通过.
> 2. **计值与证书无关、证书搬运 (§2).** `forceᴸ-≅`, `Goodᴸ-tr`; 后者的新链点与旧链点同标签, 由 `Lab-uniq` 直接 $\cong$.
> 3. **记号侧 (§3).** **`fs-mono₁ : NF₁ u → cof u ≡ cω → ∀ n → fsn u n <ᵀ fsn u (suc n)` 已证** (StandardOmega 缺的是 $\omega$-基本列的一般情形: 和、叶 $\Omega_w$、规则 4、规则 5ω、规则 6 五种; 规则 6 由 `γ-mono₁` 与 `fsT-mono₁` 组合). 推论 `mono-lab`: 相邻基本列项的计值树 $\sqsubseteq$. 另证 **`Lab→Ctbl`** (带标签的标准形项可数), 于是 `Idx` 的下标都可数 (`Idx-Ctbl`), 这是 `occ<` 的前提.
> 4. **原子与产出式标签 (§4–§7, §12).** DecoupleBase 的 `Atom`/`Lab₁`/`Pre0` 与 Omega2Base 的 `LabS`/`PsiS₊`/`PreS₊`/`Pre0V` 改写为 `Atomᴸ`/`Lab0ᴸ`/`Pre0ᴸ` 与 `LabL`/`PsiL₊`/`PreL₊`/`Pre0Vᴸ`. 结论从 "对任意证书 $G$, `Lab (force G) (ctx a)`" 变成 **"`Σ (Goodᴸ …) (λ G → Lab (forceᴸ _ G) (ctx a))`"**: 证书与标签由同一个对 `LabL` 推导的递归造出. 单调一律来自 `Lab-oc` + `fs-mono₁` (`limᴸ`, `ĉᴸ-mk`), 不用观测前序; UniformS §8–§10 与 Omega2Base 的 `Bound` (`Good`, `Good-ψ1`, `Strictᵝ`) 都不再需要.
> 5. **闭包的支配 (§12 的 `domᴸ`).** `LabL` 的 `gŝ` 行记下闭包的**地板**: 弹栈时的目标下标 $w$ (带 `Idx`)、界 $c\sqsubseteq^\mathsf I\mathtt{lvl}\,w+1$、$w$ 在每个 $t[\theta]$ 里出现. $\psi_0$ 前缀下第 $m$ 个链点带标签 $\psi_0(\Omega_\Omega+a[\theta_m])$, SystemOmega 的 `occ<` 给 $w<$ 链点, `Lab-oc` 给树的 $\prec$, 于是 $c\sqsubseteq$ 链点的层号. 这是 Omega2 §5 设想的 "相对带标签地板" 的严格性, 由于只在带标签的点处计值, 它对**一切**链点 (包括 `first-wall`/`second-wall` 处界为 $\mathtt{lvl}\,\mathrm{BTBO}+1$、$+2$ 的闭包) 一致成立.
>
> 决定性检验 (无条件的 `Lab T2 t2`) 在 [GoodL](GoodL.lagda.md). 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件; 被改写的部分以新名字复制在本文.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderZGoodLBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Vec using (Vec; []; _∷_)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Uniform using (Uniform)
open import OCF.Align.Symbolic using (Mlev; σ1)
open import OCF.Align.ScafLadderZPrefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; fΩ̂; ψᴾ;
  trˢ; tr⁻ˢ; z<suc; H₊; _~_; empty~; HS-≅; H1-pen; H1-fsT; Restrˢ; resˢ; res⁻ˢ)
open Restrˢ
import OCF.Align.NoCumsum as N
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; γT; sucT; cmpᵀ; Cmp; lt; eq; gt;
              []<; hd<; tl<; lv<; ar<; cofA; cofψ0; cofψ₊) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fs-rep; fs-ω; fsT-c1; γᴱ; diag-fs)
open import OCF.Align.Bachmann using (fs-gt; rep<; pen→<; gt→≤; clash; cofA≢c1)
open import OCF.Align.Closure using (lt→<; Pen; fsT₊-pen′)
open import OCF.Align.Standard using (Ctbl; c[]; c∷; Ctbl-pred; Ctbl-fsn; cofψ0≢c1)
open import OCF.Align.ScafLadderZStandardOmega using (NF₁; NFᴾ₁; n[]; n∷; nψ; NF₁-pred; NF₁-fsn; γ-mono₁; fsT-mono₁; γ′-NF)
open import OCF.Align.ScafLadderZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts; occ<)
open import OCF.Align.Stage2 using (ctx; Lab-+; Lab-uniq; ≺→⊑)
open import OCF.Align.Label using (BTBO-label; γ-label)
open import OCF.Align.ScafLadderZUniformS
open import OCF.Align.ScafLadderZStage2Label using (chain0; chain1; chain1-≅; t₀pop; gpop; Lab-oc; one⁰; BTBO-NF)
open import OCF.Align.ScafLadderZDecoupleBase using (fold1; pen1; ΩΩ; γP; 1<ctx; nfγ; nfω; ŝ-reflg; force-subst)
open import OCF.Align.ScafLadderZDecouple using (Idx; lvI; Ilt; Ieq; Lab0[]; kdI; kdI′; gtν; kdI[]; cofP; fold0; pen0)
```


## §1 `Goodᴸ`: 链点带标签的证书

**设计.** Prefix 的 `Goodᶻ.gc` 对一切 $\eta\sqsupseteq c$ 要分支的证书 (`Gg : ∀ η e`), 而 `force` 只在链点处计值. 这里把可容许的计值点取为 "某个带标签 $\gamma_m$ 的树 $Y$ 的层号", 标签序列 $\gamma$ 是证书的一个字段:

$$\mathtt{Adm}_\gamma(\eta)\;:=\;\eta\ \text{形如}\ \mathtt{toLevel}\,Y\,h_Y,\quad Y\ \text{带标签}\ \gamma_m\ \text{(某个}\ m\text{)}.$$

可容许性写成量化的前提 (`∀ m Y hY → Lab Y (γ m) → …`), 而不是一个独立的谓词 `Adm : Ordᴵ → Set`; 所以 `Goodᴸ` 仍在 `Set` 里 (序列 $\gamma:\mathbb N\to T$ 是数据). 对计值点的稳定性是一个字段 `lE`: 在带标签 $\gamma_m$ 的点处的计值带标签 $\gamma_{m+1}$, 于是下一个链点仍可容许; 第 0 点由 `l₀` 带标签 $\gamma_0$.

字段 (`gc`): 标签序列 `γ`; 第 0 点的证书 `G₀`、标签 `l₀`、支配 `d₀`; 分支在可容许点处的证书 `Gg`、标签 `lE`、支配 `dE`; 输出的证书 `Go₀` 与 **只在链点处的** `Go k`, 以及输出的逐项单调 `mo₀`/`mo`. 与 `Goodᶻ` 相比去掉了链的单调 `m₀`/`mE` (链点只被用作计值位置, 不需要单调), 输出单调只要求相邻链点之间 (`Goodᶻ` 要求一切 $\eta\sqsubseteq\eta'$).

链点由证书字段生成 (`ptsᴸ`), 这个函数只依赖 `Ordᶜ` 上的数据, 所以可以在 `Goodᴸ` 之前定义, `gc` 的类型里把 `forceᴸ` 填进去.

```agda
record Ptᴸ (c : Ordᴵ) (γ : ℕ → T) (m : ℕ) : Set where
  constructor ptᴸ
  field
    x  : Ordᶜ zero
    hx : HS x
    lx : Lab x (γ m)
    dx : c ⊑ᴵ toLevel x hx

lvᴸ : ∀ {c γ m} → Ptᴸ c γ m → Ordᴵ
lvᴸ p = toLevel (Ptᴸ.x p) (Ptᴸ.hx p)

ptsᴸ : ∀ {c γ} (x₀ : Ordᶜ zero) (h₀ : HS x₀) → Lab x₀ (γ 0) → c ⊑ᴵ toLevel x₀ h₀ →
       (F : ∀ m Y (hY : HS Y) → Lab Y (γ m) → c ⊑ᴵ toLevel Y hY → Ordᶜ zero) →
       (hF : ∀ m Y hY lY e → HS (F m Y hY lY e)) →
       (∀ m Y hY lY e → Lab (F m Y hY lY e) (γ (suc m))) →
       (∀ m Y hY lY e → c ⊑ᴵ toLevel (F m Y hY lY e) (hF m Y hY lY e)) → ∀ k → Ptᴸ c γ k
ptsᴸ x₀ h₀ l₀ d₀ F hF lF dF zero    = ptᴸ x₀ h₀ l₀ d₀
ptsᴸ x₀ h₀ l₀ d₀ F hF lF dF (suc k) =
  ptᴸ (F k (Ptᴸ.x p) (Ptᴸ.hx p) (Ptᴸ.lx p) (Ptᴸ.dx p)) (hF k (Ptᴸ.x p) (Ptᴸ.hx p) (Ptᴸ.lx p) (Ptᴸ.dx p))
      (lF k (Ptᴸ.x p) (Ptᴸ.hx p) (Ptᴸ.lx p) (Ptᴸ.dx p)) (dF k (Ptᴸ.x p) (Ptᴸ.hx p) (Ptᴸ.lx p) (Ptᴸ.dx p))
  where p = ptsᴸ x₀ h₀ l₀ d₀ F hF lF dF k

outsᴸ : Ordᶜ zero → (ℕ → Ordᶜ zero) → ℕ → Ordᶜ zero
outsᴸ O₀ O zero    = O₀
outsᴸ O₀ O (suc k) = O k

outsᴸ-HS : ∀ {O₀ O} → HS O₀ → (∀ k → HS (O k)) → ∀ n → HS (outsᴸ O₀ O n)
outsᴸ-HS h₀ h zero    = h₀
outsᴸ-HS h₀ h (suc k) = h k

outsᴸ-step : ∀ {O₀ O} → O₀ ⊑⁰ O 0 → (∀ k → O k ⊑⁰ O (suc k)) → ∀ n → outsᴸ O₀ O n ⊑⁰ outsᴸ O₀ O (suc n)
outsᴸ-step m₀ m zero    = m₀
outsᴸ-step m₀ m (suc k) = m k
```


```agda
data Goodᴸ : Z → Set
forceᴸ    : (x : Z) → Goodᴸ x → Ordᶜ zero
forceᴸ-HS : (x : Z) (G : Goodᴸ x) → HS (forceᴸ x G)

data Goodᴸ where
  gz : Goodᴸ Z.zero
  gs : ∀ {x} → Goodᴸ x → Goodᴸ (Z.suc x)
  gl : ∀ {f : ℕ → Z} (G : ∀ n → Goodᴸ (f n)) →
       (∀ n → forceᴸ (f n) (G n) ⊑⁰ forceᴸ (f (suc n)) (G (suc n))) → Goodᴸ (Z.lim f)
  gc : ∀ {c t₀ o₀} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z} (γ : ℕ → T)
       (G₀ : Goodᴸ t₀) (l₀ : Lab (forceᴸ t₀ G₀) (γ 0)) (d₀ : c ⊑ᴵ toLevel (forceᴸ t₀ G₀) (forceᴸ-HS t₀ G₀))
       (Gg : ∀ m Y (hY : HS Y) → Lab Y (γ m) → (e : c ⊑ᴵ toLevel Y hY) → Goodᴸ (g (toLevel Y hY) e))
       (lE : ∀ m Y hY lY e → Lab (forceᴸ _ (Gg m Y hY lY e)) (γ (suc m)))
       (dE : ∀ m Y hY lY e → c ⊑ᴵ toLevel (forceᴸ _ (Gg m Y hY lY e)) (forceᴸ-HS _ (Gg m Y hY lY e)))
       (Go₀ : Goodᴸ o₀) →
       let P = ptsᴸ (forceᴸ t₀ G₀) (forceᴸ-HS t₀ G₀) l₀ d₀ (λ m Y hY lY e → forceᴸ _ (Gg m Y hY lY e))
                    (λ m Y hY lY e → forceᴸ-HS _ (Gg m Y hY lY e)) lE dE in
       (Go : ∀ k → Goodᴸ (o (lvᴸ (P k)) (Ptᴸ.dx (P k)))) →
       forceᴸ o₀ Go₀ ⊑⁰ forceᴸ _ (Go 0) →
       (∀ k → forceᴸ _ (Go k) ⊑⁰ forceᴸ _ (Go (suc k))) →
       Goodᴸ (ĉᴸ c t₀ g o₀ o)

forceᴸ Z.zero    gz        = zero
forceᴸ (Z.suc x) (gs G)    = suc (forceᴸ x G)
forceᴸ (Z.lim f) (gl G st) = lim (λ n → forceᴸ (f n) (G n))
forceᴸ (ĉᴸ c t₀ g o₀ o) (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) = lim (outsᴸ (forceᴸ o₀ Go₀) (λ k → forceᴸ _ (Go k)))

forceᴸ-HS Z.zero    gz        = hz
forceᴸ-HS (Z.suc x) (gs G)    = hs (forceᴸ-HS x G)
forceᴸ-HS (Z.lim f) (gl G st) = hl (λ n → forceᴸ-HS (f n) (G n)) st
forceᴸ-HS (ĉᴸ c t₀ g o₀ o) (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) =
  hl (outsᴸ-HS (forceᴸ-HS o₀ Go₀) (λ k → forceᴸ-HS _ (Go k))) (outsᴸ-step mo₀ mo)
```


**读法.** `forceᴸ` 只读输出: 第 0 项是 $o_0$, 第 $k+1$ 项是 $o$ 在第 $k$ 个链点处的值, 链点本身只出现在 `Go` 的类型里 (计值位置). 停机对 `Z` 结构递归, 与 `force` 相同. `let` 在构造子类型里被展开, 正性检查不受影响.

**链证书.** `CCᴸ` 是 `gc` 的前七个字段 (不含输出), 第 $k$ 个链点 `ptK K k` 与 `gc` 的类型里的 `P k` 定义性相同. DecoupleBase 的标签行 `lŝ₀`/`lĉ` 与 Omega2Base 的 `gĉ` 在本文里都携带一个链证书 (存在量化), 而不是对一切链证书量化.

```agda
record CCᴸ (c : Ordᴵ) (t₀ : Z) (g : (η : Ordᴵ) → c ⊑ᴵ η → Z) : Set where
  constructor ccᴸ
  field
    γ  : ℕ → T
    G₀ : Goodᴸ t₀
    l₀ : Lab (forceᴸ t₀ G₀) (γ 0)
    d₀ : c ⊑ᴵ toLevel (forceᴸ t₀ G₀) (forceᴸ-HS t₀ G₀)
    Gg : ∀ m Y (hY : HS Y) → Lab Y (γ m) → (e : c ⊑ᴵ toLevel Y hY) → Goodᴸ (g (toLevel Y hY) e)
    lE : ∀ m Y hY lY e → Lab (forceᴸ _ (Gg m Y hY lY e)) (γ (suc m))
    dE : ∀ m Y hY lY e → c ⊑ᴵ toLevel (forceᴸ _ (Gg m Y hY lY e)) (forceᴸ-HS _ (Gg m Y hY lY e))

ptK : ∀ {c t₀ g} (K : CCᴸ c t₀ g) k → Ptᴸ c (CCᴸ.γ K) k
ptK K = ptsᴸ (forceᴸ _ (CCᴸ.G₀ K)) (forceᴸ-HS _ (CCᴸ.G₀ K)) (CCᴸ.l₀ K) (CCᴸ.d₀ K)
             (λ m Y hY lY e → forceᴸ _ (CCᴸ.Gg K m Y hY lY e)) (λ m Y hY lY e → forceᴸ-HS _ (CCᴸ.Gg K m Y hY lY e))
             (CCᴸ.lE K) (CCᴸ.dE K)

lvK : ∀ {c t₀ g} → CCᴸ c t₀ g → ℕ → Ordᴵ
lvK K k = lvᴸ (ptK K k)

dxK : ∀ {c t₀ g} (K : CCᴸ c t₀ g) k → c ⊑ᴵ lvK K k
dxK K k = Ptᴸ.dx (ptK K k)
```


## §2 计值与证书无关, 证书沿 `≅ᶻ` 搬运

UniformS 的 `force-≅`/`Goodᶻ-tr` 的 `Goodᴸ` 版. `pts-≅`: 两条链的第 0 点 $\cong$、计值在 $\cong^\mathsf I$ 的层号处 $\cong$, 则链点逐个 $\cong$ (UniformS 的 `chain≅`; 两条链的标签序列可以不同). 搬运时新旧两个证书**用同一个标签序列** $\gamma$, 所以新链点与旧链点由 `Lab-uniq` 直接 $\cong$, 不需要 `pts-≅`.

```agda
module _ {c c′ : Ordᴵ} {γ γ′ : ℕ → T} {x₀ x₀′ : Ordᶜ zero} {h₀ : HS x₀} {h₀′ : HS x₀′}
         {l₀ : Lab x₀ (γ 0)} {l₀′ : Lab x₀′ (γ′ 0)} {d₀ : c ⊑ᴵ toLevel x₀ h₀} {d₀′ : c′ ⊑ᴵ toLevel x₀′ h₀′}
         {F : ∀ m Y (hY : HS Y) → Lab Y (γ m) → c ⊑ᴵ toLevel Y hY → Ordᶜ zero}
         {F′ : ∀ m Y (hY : HS Y) → Lab Y (γ′ m) → c′ ⊑ᴵ toLevel Y hY → Ordᶜ zero}
         {hF : ∀ m Y hY lY e → HS (F m Y hY lY e)} {hF′ : ∀ m Y hY lY e → HS (F′ m Y hY lY e)}
         {lF : ∀ m Y hY lY e → Lab (F m Y hY lY e) (γ (suc m))} {lF′ : ∀ m Y hY lY e → Lab (F′ m Y hY lY e) (γ′ (suc m))}
         {dF : ∀ m Y hY lY e → c ⊑ᴵ toLevel (F m Y hY lY e) (hF m Y hY lY e)}
         {dF′ : ∀ m Y hY lY e → c′ ⊑ᴵ toLevel (F′ m Y hY lY e) (hF′ m Y hY lY e)} where
  pts-≅ : x₀ ≅ x₀′ →
          (∀ m Y hY lY e Y′ hY′ lY′ e′ → toLevel Y hY ≅ᴵ toLevel Y′ hY′ → F m Y hY lY e ≅ F′ m Y′ hY′ lY′ e′) →
          ∀ k → Ptᴸ.x (ptsᴸ x₀ h₀ l₀ d₀ F hF lF dF k) ≅ Ptᴸ.x (ptsᴸ x₀′ h₀′ l₀′ d₀′ F′ hF′ lF′ dF′ k)
  pts-≅ e₀ eF zero    = e₀
  pts-≅ e₀ eF (suc k) = eF k _ _ _ _ _ _ _ _ (toLevel-≅ _ _ (pts-≅ e₀ eF k))

outs-≅ᴸ : ∀ {O₀ O₀′ O O′} → O₀ ≅ O₀′ → (∀ k → O k ≅ O′ k) → ∀ n → outsᴸ O₀ O n ≅ outsᴸ O₀′ O′ n
outs-≅ᴸ e₀ e zero    = e₀
outs-≅ᴸ e₀ e (suc k) = e k

forceᴸ-≅ : ∀ {x y} → x ≅ᶻ y → (G : Goodᴸ x) (G′ : Goodᴸ y) → forceᴸ x G ≅ forceᴸ y G′
forceᴸ-≅ zᶻ     gz gz = z≅
forceᴸ-≅ (sᶻ d) (gs G) (gs G′) = s≅ (forceᴸ-≅ d G G′)
forceᴸ-≅ (lᶻ h) (gl G _) (gl G′ _) = l≅ (λ n → forceᴸ-≅ (h n) (G n) (G′ n))
forceᴸ-≅ (ĉᶻ ec dt dg dp dO) (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) (gc γ′ G₀′ l₀′ d₀′ Gg′ lE′ dE′ Go₀′ Go′ mo₀′ mo′) =
  l≅ (outs-≅ᴸ (forceᴸ-≅ dp Go₀ Go₀′)
              (λ k → forceᴸ-≅ (dO _ _ _ _ (toLevel-≅ _ _ (pts-≅ (forceᴸ-≅ dt G₀ G₀′)
                        (λ m Y hY lY e Y′ hY′ lY′ e′ eq → forceᴸ-≅ (dg _ e _ e′ eq) (Gg m Y hY lY e) (Gg′ m Y′ hY′ lY′ e′)) k)))
                        (Go k) (Go′ k)))
```


```agda
Goodᴸ-tr : ∀ {x y} → x ≅ᶻ y → Goodᴸ x → Goodᴸ y
Goodᴸ-tr zᶻ     gz     = gz
Goodᴸ-tr (sᶻ d) (gs G) = gs (Goodᴸ-tr d G)
Goodᴸ-tr (lᶻ h) (gl G st) = gl (λ n → Goodᴸ-tr (h n) (G n))
  (λ n → ⊑-trans (≅→⊑ (≅-sym (forceᴸ-≅ (h n) (G n) (Goodᴸ-tr (h n) (G n)))))
         (⊑-trans (st n) (≅→⊑ (forceᴸ-≅ (h (suc n)) (G (suc n)) (Goodᴸ-tr (h (suc n)) (G (suc n)))))))
Goodᴸ-tr {y = ĉᴸ c′ t₀′ g′ o₀′ o′} (ĉᶻ {c = c} {t₀ = t₀} {o₀ = o₀} {g = g} {o = o} ec dt dg dp dO)
         (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) =
  gc γ G₀′ l₀′ d₀′ Gg′ lE′ dE′ Go₀′ Go′ mo₀′ mo′
  where
  cv : ∀ {η} → c′ ⊑ᴵ η → c ⊑ᴵ η
  cv = ⊑ᴵ-≅ˡ (≅ᴵ-sym ec)
  G₀′ : Goodᴸ t₀′
  G₀′ = Goodᴸ-tr dt G₀
  ft : forceᴸ t₀ G₀ ≅ forceᴸ t₀′ G₀′
  ft = forceᴸ-≅ dt G₀ G₀′
  l₀′ : Lab (forceᴸ t₀′ G₀′) (γ 0)
  l₀′ = Lab-≅ (≅-sym ft) l₀
  d₀′ : c′ ⊑ᴵ toLevel (forceᴸ t₀′ G₀′) (forceᴸ-HS t₀′ G₀′)
  d₀′ = ⊑ᴵ-≅ˡ ec (⊑ᴵ-≅ʳ d₀ (toLevel-≅ _ _ ft))
  Gg′ : ∀ m Y (hY : HS Y) → Lab Y (γ m) → (e : c′ ⊑ᴵ toLevel Y hY) → Goodᴸ (g′ (toLevel Y hY) e)
  Gg′ m Y hY lY e = Goodᴸ-tr (dg _ (cv e) _ e (≅ᴵ-refl _)) (Gg m Y hY lY (cv e))
  fg : ∀ m Y (hY : HS Y) (lY : Lab Y (γ m)) (e : c′ ⊑ᴵ toLevel Y hY) →
       forceᴸ _ (Gg m Y hY lY (cv e)) ≅ forceᴸ _ (Gg′ m Y hY lY e)
  fg m Y hY lY e = forceᴸ-≅ (dg _ (cv e) _ e (≅ᴵ-refl _)) (Gg m Y hY lY (cv e)) (Gg′ m Y hY lY e)
  lE′ : ∀ m Y hY lY e → Lab (forceᴸ _ (Gg′ m Y hY lY e)) (γ (suc m))
  lE′ m Y hY lY e = Lab-≅ (≅-sym (fg m Y hY lY e)) (lE m Y hY lY (cv e))
  dE′ : ∀ m Y hY lY e → c′ ⊑ᴵ toLevel (forceᴸ _ (Gg′ m Y hY lY e)) (forceᴸ-HS _ (Gg′ m Y hY lY e))
  dE′ m Y hY lY e = ⊑ᴵ-≅ˡ ec (⊑ᴵ-≅ʳ (dE m Y hY lY (cv e)) (toLevel-≅ _ _ (fg m Y hY lY e)))
  Go₀′ : Goodᴸ o₀′
  Go₀′ = Goodᴸ-tr dp Go₀
  P : ∀ k → Ptᴸ c γ k
  P = ptsᴸ (forceᴸ t₀ G₀) (forceᴸ-HS t₀ G₀) l₀ d₀ (λ m Y hY lY e → forceᴸ _ (Gg m Y hY lY e))
           (λ m Y hY lY e → forceᴸ-HS _ (Gg m Y hY lY e)) lE dE
  P′ : ∀ k → Ptᴸ c′ γ k
  P′ = ptsᴸ (forceᴸ t₀′ G₀′) (forceᴸ-HS t₀′ G₀′) l₀′ d₀′ (λ m Y hY lY e → forceᴸ _ (Gg′ m Y hY lY e))
            (λ m Y hY lY e → forceᴸ-HS _ (Gg′ m Y hY lY e)) lE′ dE′
  eP : ∀ k → lvᴸ (P k) ≅ᴵ lvᴸ (P′ k)
  eP k = toLevel-≅ _ _ (Lab-uniq (Ptᴸ.lx (P k)) (Ptᴸ.lx (P′ k)))
  dOk : ∀ k → o (lvᴸ (P k)) (Ptᴸ.dx (P k)) ≅ᶻ o′ (lvᴸ (P′ k)) (Ptᴸ.dx (P′ k))
  dOk k = dO _ _ _ _ (eP k)
  Go′ : ∀ k → Goodᴸ (o′ (lvᴸ (P′ k)) (Ptᴸ.dx (P′ k)))
  Go′ k = Goodᴸ-tr (dOk k) (Go k)
  fo : ∀ k → forceᴸ _ (Go k) ≅ forceᴸ _ (Go′ k)
  fo k = forceᴸ-≅ (dOk k) (Go k) (Go′ k)
  fo₀ : forceᴸ o₀ Go₀ ≅ forceᴸ o₀′ Go₀′
  fo₀ = forceᴸ-≅ dp Go₀ Go₀′
  mo₀′ : forceᴸ o₀′ Go₀′ ⊑⁰ forceᴸ _ (Go′ 0)
  mo₀′ = ⊑-trans (≅→⊑ (≅-sym fo₀)) (⊑-trans mo₀ (≅→⊑ (fo 0)))
  mo′ : ∀ k → forceᴸ _ (Go′ k) ⊑⁰ forceᴸ _ (Go′ (suc k))
  mo′ k = ⊑-trans (≅→⊑ (≅-sym (fo k))) (⊑-trans (mo k) (≅→⊑ (fo (suc k))))
```


## §3 记号侧: `fs-mono₁`

`Lab-oc` 把记号的 $<$ 变成树的 $\prec$. `Goodᴸ` 的一切单调字段 (`gl` 的 `st`, `gc` 的 `mo₀`/`mo`) 都是 "同一个极限项的相邻基本列项", 所以需要的记号事实恰是 Bachmann 的 `fs-mono` 在 `NF₁` 上的版本. StandardOmega 只有 Ω-基本列的 `fsT-mono₁` 与 γ-链的 `γ-mono₁`, 缺 $\omega$-基本列的一般情形; 下面按 `cofin₁` 的分情况补上: 和 (尾巴归纳), 叶 $\Omega_w$ ($w$ 极限, 对下标归纳), $\psi_w(a)$ 且 $a$ 后继 (规则 4, Bachmann 的 `rep<`), $a$ 极限 (对参数归纳), $a$ 的共尾度 $\Omega_{\nu+1}$ 而折叠 (规则 6: `γ-mono₁` 再 `fsT-mono₁`). 穿透情形共尾度不是 $\omega$, 由 `cofψ₊` 的计算排除.

```agda
fs-mono₁ : ∀ {u} → NF₁ u → cof u ≡ cω → ∀ n → fsn u n <ᵀ fsn u (suc n)
fs-monoL : ∀ {w ws} → NF₁ (w ∷ ws) → ∀ k → cof (w ∷ ws) ≡ k → cofψ0 (w ∷ ws) k ≡ cω →
           ∀ n → fsn (Ωt (w ∷ ws)) n <ᵀ fsn (Ωt (w ∷ ws)) (suc n)
fs-monoA : ∀ {w y ys} → NF₁ (y ∷ ys) → ∀ k → cof (y ∷ ys) ≡ k → cofA w k ≡ cω →
           ∀ n → fsn (ψᵗ w (y ∷ ys) ∷ []) n <ᵀ fsn (ψᵗ w (y ∷ ys) ∷ []) (suc n)

fs-mono₁ n[] () n
fs-mono₁ (n∷ nx (n∷ ny nys hy) hx) e n = tl< (fs-mono₁ (n∷ ny nys hy) e n)
fs-mono₁ (n∷ (nψ {u = []} {a = []} nw cw na g) n[] hx) () n
fs-mono₁ (n∷ (nψ {u = w ∷ ws} {a = []} nw cw na g) n[] hx) e n = fs-monoL nw (cof (w ∷ ws)) refl e n
fs-mono₁ (n∷ (nψ {u = w} {a = y ∷ ys} nw cw na g) n[] hx) e n = fs-monoA na (cof (y ∷ ys)) refl e n

fs-monoL nw c0 ke () n
fs-monoL nw c1 ke () n
fs-monoL {w} {ws} nw cω ke e n =
  subst₂ _<ᵀ_ (sym (E.fsn0-eq w ws n ke)) (sym (E.fsn0-eq w ws (suc n) ke)) (hd< (lv< (fs-mono₁ nw ke n)))
fs-monoL nw (cΩ μ) ke () n

fs-monoA nb c0 ke e n = ⊥-elim (cof-ne _ _ ke)
fs-monoA {w} {y} {ys} nb c1 ke e n =
  subst₂ _<ᵀ_ (sym (fs-rep w y ys ke n)) (sym (fs-rep w y ys ke (suc n))) (rep< _ n)
fs-monoA {w} {y} {ys} nb cω ke e n =
  subst₂ _<ᵀ_ (sym (fs-ω w y ys ke n)) (sym (fs-ω w y ys ke (suc n))) (hd< (ar< (fs-mono₁ nb ke n)))
fs-monoA {w} {y} {ys} nb (cΩ ν) ke e n = go (cmpᵀ (sucT ν) w) refl e
  where
  go : ∀ m → cmpᵀ (sucT ν) w ≡ m → cofψ₊ w ν m ≡ cω →
       fsn (ψᵗ w (y ∷ ys) ∷ []) n <ᵀ fsn (ψᵗ w (y ∷ ys) ∷ []) (suc n)
  go lt em ()
  go eq em ()
  go gt em _ = subst₂ _<ᵀ_ (sym (fs-gt w y ys ν ke em n)) (sym (fs-gt w y ys ν ke em (suc n)))
                      (hd< (ar< (fsT-mono₁ nb ke (γ-mono₁ nb ke n))))
```


**带标签的项都可数.** `Lab→Ctbl`: 计值树带标签的标准形项, 其各加项的 $\psi$-下标都是 $0$ (Standard 的 `Ctbl`). `Lab` 没有 $\Omega$-共尾度的行, 所以对标签推导归纳: 后继行由 `pred` 只剥一个 $\mathbf 1$ 得到 (`Ctbl-c1`), 极限行看第 $1$ 项 (`Ctbl-ω`: 若首个非零下标的加项在末尾, 它的第 $1$ 项仍以同一个下标开头; 叶 $\Omega_w$ 的第 $1$ 项是 $\Omega_{w[1]}$, 而 $w[1]\ne0$ 由 `fs-mono₁`). 用途: Decouple 的 `Idx` 的下标都可数 (`Idx-Ctbl`), 这是 SystemOmega 的 `occ<` 的前提; 于是不必把 `Ctbl` 加进 `Idx` 或 `gi` 行.

```agda
ctbl-hd : ∀ {v a xs} → Ctbl (ψᵗ v a ∷ xs) → v ≡ []
ctbl-hd (c∷ c) = refl

ctbl-one : ∀ {v a} → v ≡ [] → Ctbl (ψᵗ v a ∷ [])
ctbl-one refl = c∷ c[]

Ctbl-c1 : ∀ u → cof u ≡ c1 → Ctbl (pred u) → Ctbl u
Ctbl-c1 [] () c
Ctbl-c1 (x ∷ y ∷ ys) e (c∷ ct) = c∷ (Ctbl-c1 (y ∷ ys) e ct)
Ctbl-c1 (ψᵗ [] [] ∷ []) e c = c∷ c[]
Ctbl-c1 (ψᵗ (w ∷ ws) [] ∷ []) e c = ⊥-elim (cofψ0≢c1 (w ∷ ws) (cof (w ∷ ws)) e)
Ctbl-c1 (ψᵗ u (y ∷ ys) ∷ []) e c = ⊥-elim (cofA≢c1 u (cof (y ∷ ys)) e)

Ctbl-ω : ∀ {u} → NF₁ u → cof u ≡ cω → Ctbl (fsn u 1) → Ctbl u
Ctbl-ω n[] () c
Ctbl-ω (n∷ nx (n∷ ny nys hy) hx) e (c∷ ct) = c∷ (Ctbl-ω (n∷ ny nys hy) e ct)
Ctbl-ω (n∷ (nψ {u = []} {a = []} nw cw na g) n[] hx) () c
Ctbl-ω (n∷ (nψ {u = w ∷ ws} {a = []} nw cw na g) n[] hx) e c = go (cof (w ∷ ws)) refl e c
  where
  go : ∀ k → cof (w ∷ ws) ≡ k → cofψ0 (w ∷ ws) k ≡ cω → Ctbl (fsn (Ωt (w ∷ ws)) 1) → Ctbl (Ωt (w ∷ ws))
  go c0 ke () c
  go c1 ke () c
  go (cΩ μ) ke () c
  go cω ke _ c with subst (_<ᵀ_ (fsn (w ∷ ws) 0)) (ctbl-hd (subst Ctbl (E.fsn0-eq w ws 1 ke) c)) (fs-mono₁ nw ke 0)
  ... | ()
Ctbl-ω (n∷ (nψ {u = w} {a = y ∷ ys} nw cw na g) n[] hx) e c = go (cof (y ∷ ys)) refl e c
  where
  go : ∀ k → cof (y ∷ ys) ≡ k → cofA w k ≡ cω → Ctbl (fsn (ψᵗ w (y ∷ ys) ∷ []) 1) → Ctbl (ψᵗ w (y ∷ ys) ∷ [])
  go c0 ke _ c = ⊥-elim (cof-ne y ys ke)
  go c1 ke _ c = ctbl-one (ctbl-hd (subst Ctbl (fs-rep w y ys ke 1) c))
  go cω ke _ c = ctbl-one (ctbl-hd (subst Ctbl (fs-ω w y ys ke 1) c))
  go (cΩ ν) ke e′ c = gc′ (cmpᵀ (sucT ν) w) refl e′
    where
    gc′ : ∀ m → cmpᵀ (sucT ν) w ≡ m → cofψ₊ w ν m ≡ cω → Ctbl (ψᵗ w (y ∷ ys) ∷ [])
    gc′ lt em ()
    gc′ eq em ()
    gc′ gt em _ = ctbl-one (ctbl-hd (subst Ctbl (fs-gt w y ys ν ke em 1) c))

Lab→Ctbl : ∀ {Y t} → Lab Y t → NF₁ t → Ctbl t
Lab→Ctbl {t = []} (l0 c e) nt = c[]
Lab→Ctbl {t = x ∷ xs} (l0 c e) nt = ⊥-elim (cof-ne x xs c)
Lab→Ctbl {t = t} (l1 c e l) nt = Ctbl-c1 t c (Lab→Ctbl l (NF₁-pred nt c))
Lab→Ctbl (lω c e h) nt = Ctbl-ω nt c (Lab→Ctbl (h 1) (NF₁-fsn nt c 1))

Idx-Ctbl : ∀ {ν} → Idx ν → Ctbl ν
Idx-Ctbl (Y , hY , lY , nY) = Lab→Ctbl lY nY
```


`mono-lab`: 相邻基本列项的计值树, 由标签得 $\sqsubseteq$ (`Lab-oc` + `fs-mono₁` + Stage2 的 `≺→⊑`). `dom-lab`: 层号 $\sqsupseteq1$ 只要标签非零.

```agda
mono-lab : ∀ {u X Y} → NF₁ u → (c : cof u ≡ cω) → ∀ n → Lab X (fsn u n) → Lab Y (fsn u (suc n)) → X ⊑⁰ Y
mono-lab nu c n lX lY = ≺→⊑ (Lab-oc lY (NF₁-fsn nu c (suc n)) lX (NF₁-fsn nu c n) (fs-mono₁ nu c n))

lab0 : Lab Ord₊.zero []
lab0 = l0 refl z≅

one⊑lab : ∀ {Y t} (hY : HS Y) → Lab Y t → NF₁ t → [] <ᵀ t → suc zero ⊑ᴵ toLevel Y hY
one⊑lab hY lY nt p = s⊑′ (toLevel-≺ hz hY (Lab-oc lY nt lab0 n[] p))
```


## §4 无符号的树, $\psi_0(\Omega_\Omega)$

Prefix §5 的 `force~`/`plainGood` 的 `Goodᴸ` 版: 与旧族的树相关的无符号树 (第 0 层只有 `zero`/`suc`/`lim`) 有 `Goodᴸ`, 计值 $\cong$ 旧树. `pop0ᴸ`: 目标 0、单 $\hat\Omega$ 帧、尾巴 0 的折叠 $\psi^{[\hat\Omega]}_0(0)$ 是界为 1 的闭包, 链 $\psi^{[]}_0(\Omega_1),\psi^{[]}_0(\Omega_{\mathtt{lvl}\,\chi_k}),\ldots$ 与 NoCumsum 的 $\gamma$ 逐项 $\cong$ (Stage2Label 的 `pop0≅`); 证书的标签序列是 $\gamma^{\mathsf E}_{m+1}$ (Label 的 `γ-label`), 可容许点 $Y$ 带标签 $\gamma^{\mathsf E}_{m+1}$ 时由 `Lab-uniq` 得 $Y\cong\gamma_{m+1}$, 于是计值 $\cong\gamma_{m+2}$. 单调用 `BTBO-HS` 的步进 (树侧), 支配用 `one⊑lab`.

```agda
force~ᴸ : ∀ {x : Ordˢ zero} {y : Ordᶜ zero} → x ~ y → (G : Goodᴸ (toZ x)) → forceᴸ (toZ x) G ≅ y
force~ᴸ H₊.z~     gz        = z≅
force~ᴸ (H₊.s~ d) (gs G)    = s≅ (force~ᴸ d G)
force~ᴸ (H₊.l~ h) (gl G st) = l≅ (λ n → force~ᴸ (h n) (G n))
force~ᴸ (H₊.lᵢ~ {p = ()} e h) G
force~ᴸ (H₊.upˡ {r = ()} e) G
force~ᴸ (H₊.upʳ {r = ()} e) G

plainᴸ : ∀ {x : Ordˢ zero} {y : Ordᶜ zero} → x ~ y → HS y → Goodᴸ (toZ x)
plainᴸ H₊.z~     hz        = gz
plainᴸ (H₊.s~ d) (hs h)    = gs (plainᴸ d h)
plainᴸ (H₊.l~ k) (hl h st) = gl (λ n → plainᴸ (k n) (h n))
  (λ n → ⊑-trans (≅→⊑ (force~ᴸ (k n) _)) (⊑-trans (st n) (≅→⊑ (≅-sym (force~ᴸ (k (suc n)) _)))))
plainᴸ (H₊.lᵢ~ {p = ()} e k) h
plainᴸ (H₊.upˡ {r = ()} e) h
plainᴸ (H₊.upʳ {r = ()} e) h

emptyᴸ : ∀ {ℓ a} (p : zero <ᴵ ℓ) (σ : Simᴵ a ℓ) → Goodᴸ (toZ (ψᴾ 0 p σ [] (Ωˢ a)))
emptyᴸ {a = a} p σ = plainᴸ (empty~ p σ) (HS-≅ (ψ⁰≅ψ {p = p} {σ = σ} (Ω-refl a)) (Uniform a))

emptyᴸ≅ : ∀ {ℓ a} (p : zero <ᴵ ℓ) (σ : Simᴵ a ℓ) (G : Goodᴸ (toZ (ψᴾ 0 p σ [] (Ωˢ a)))) →
          forceᴸ (toZ (ψᴾ 0 p σ [] (Ωˢ a))) G ≅ ψ⁰ (Ω a)
emptyᴸ≅ {a = a} p σ G = ≅-trans (force~ᴸ (empty~ p σ) G) (≅-sym (ψ⁰≅ψ {p = p} {σ = σ} (Ω-refl a)))
```


```agda
γE-NF : ∀ m → NF₁ (γᴱ (suc m))
γE-NF m = subst NF₁ (diag-fs m) (NF₁-fsn BTBO-NF refl m)

pop0ᴸ : ∀ {L k} (p : zero <ᴵ L) (σ : Simᴵ k L) (z : zero <ᴵ L) →
        Σ (Goodᴸ (toZ (ψ1 p σ z Ord₊ˢ.zero))) λ G → Lab (forceᴸ _ G) (E.EBOψ 2)
pop0ᴸ p σ z = gc γ G₀ l₀ d₀ Gg lE dE G₀ Go mo₀ mo , Lab-≅ (l≅ eo) BTBO-label
  where
  γ : ℕ → T
  γ m = γᴱ (suc m)
  G₀ : Goodᴸ (toZ (t₀pop p z))
  G₀ = emptyᴸ zero (σ1 (z<suc z p))
  a₀ : forceᴸ _ G₀ ≅ N.γ 1
  a₀ = emptyᴸ≅ zero (σ1 (z<suc z p)) G₀
  l₀ : Lab (forceᴸ _ G₀) (γ 0)
  l₀ = Lab-≅ a₀ (γ-label 0)
  d₀ : suc zero ⊑ᴵ toLevel (forceᴸ _ G₀) (forceᴸ-HS _ G₀)
  d₀ = one⊑lab _ l₀ (γE-NF 0) []<
  Gg : ∀ m Y (hY : HS Y) → Lab Y (γ m) → (e : suc zero ⊑ᴵ toLevel Y hY) → Goodᴸ (toZ (gpop p z (toLevel Y hY) e))
  Gg m Y hY lY e = emptyᴸ (lim 0 zero) (λ q → lim 1 q)
  ag : ∀ m Y hY (lY : Lab Y (γ m)) e → forceᴸ _ (Gg m Y hY lY e) ≅ N.γ (suc (suc m))
  ag m Y hY lY e = ≅-trans (emptyᴸ≅ (lim 0 zero) (λ q → lim 1 q) (Gg m Y hY lY e))
                           (ψ⁰-≅ (Ω-≅ (toLevel-≅ hY (N.cert (suc m)) (Lab-uniq lY (γ-label m)))))
  lE : ∀ m Y hY lY e → Lab (forceᴸ _ (Gg m Y hY lY e)) (γ (suc m))
  lE m Y hY lY e = Lab-≅ (ag m Y hY lY e) (γ-label (suc m))
  dE : ∀ m Y hY lY e → suc zero ⊑ᴵ toLevel (forceᴸ _ (Gg m Y hY lY e)) (forceᴸ-HS _ (Gg m Y hY lY e))
  dE m Y hY lY e = one⊑lab _ (lE m Y hY lY e) (γE-NF (suc m)) []<
  P : ∀ k → Ptᴸ (suc zero) γ k
  P = ptsᴸ (forceᴸ _ G₀) (forceᴸ-HS _ G₀) l₀ d₀ (λ m Y hY lY e → forceᴸ _ (Gg m Y hY lY e))
           (λ m Y hY lY e → forceᴸ-HS _ (Gg m Y hY lY e)) lE dE
  Go : ∀ k → Goodᴸ (toZ (gpop p z (lvᴸ (P k)) (Ptᴸ.dx (P k))))
  Go k = Gg k (Ptᴸ.x (P k)) (Ptᴸ.hx (P k)) (Ptᴸ.lx (P k)) (Ptᴸ.dx (P k))
  ao : ∀ k → forceᴸ _ (Go k) ≅ N.γ (suc (suc k))
  ao k = ag k (Ptᴸ.x (P k)) (Ptᴸ.hx (P k)) (Ptᴸ.lx (P k)) (Ptᴸ.dx (P k))
  mo₀ : forceᴸ _ G₀ ⊑⁰ forceᴸ _ (Go 0)
  mo₀ = ⊑-trans (≅→⊑ a₀) (⊑-trans (hl₂ N.BTBO-HS 0) (≅→⊑ (≅-sym (ao 0))))
  mo : ∀ k → forceᴸ _ (Go k) ⊑⁰ forceᴸ _ (Go (suc k))
  mo k = ⊑-trans (≅→⊑ (ao k)) (⊑-trans (hl₂ N.BTBO-HS (suc k)) (≅→⊑ (≅-sym (ao (suc k)))))
  eo : ∀ n → outsᴸ (forceᴸ _ G₀) (λ k → forceᴸ _ (Go k)) n ≅ N.γ (suc n)
  eo zero    = a₀
  eo (suc k) = ao k
```


## §5 两个构造器, 原子与第 0 层的结构标签

**构造器.** `limᴸ`: 第 0 层的极限, 各项的证书与标签给定 (标签是同一个极限项 $u$ 的基本列), 单调由 `mono-lab`. `ĉᴸ-mk`: 待计值链, 链证书 `K` 给定, 输出只在 `K` 的链点处给出, 单调同样由标签. 这是 "证书由标签造出" 的全部机制: `Goodᴸ` 的单调字段一律来自 `Lab-oc` + `fs-mono₁`.

```agda
outsLab : ∀ {O₀ O t} → Lab O₀ (fsn t 0) → (∀ k → Lab (O k) (fsn t (suc k))) → ∀ n → Lab (outsᴸ O₀ O n) (fsn t n)
outsLab l₀ lk zero    = l₀
outsLab l₀ lk (suc k) = lk k

limᴸ : ∀ {u} {f : ℕ → Z} → NF₁ u → cof u ≡ cω → (Gs : ∀ n → Goodᴸ (f n)) → (∀ n → Lab (forceᴸ _ (Gs n)) (fsn u n)) →
       Σ (Goodᴸ (Z.lim f)) λ G → Lab (forceᴸ _ G) u
limᴸ nu c Gs lab = gl Gs (λ n → mono-lab nu c n (lab n) (lab (suc n))) , lω c (l≅ (λ n → ≅-refl⁰ _)) lab

ĉᴸ-mk : ∀ {u c t₀ o₀} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z} → NF₁ u → cof u ≡ cω → (K : CCᴸ c t₀ g) →
        (Go₀ : Goodᴸ o₀) → Lab (forceᴸ _ Go₀) (fsn u 0) →
        (Go : ∀ k → Goodᴸ (o (lvK K k) (dxK K k))) → (∀ k → Lab (forceᴸ _ (Go k)) (fsn u (suc k))) →
        Σ (Goodᴸ (ĉᴸ c t₀ g o₀ o)) λ G → Lab (forceᴸ _ G) u
ĉᴸ-mk nu c K Go₀ l₀ Go lk =
  gc (CCᴸ.γ K) (CCᴸ.G₀ K) (CCᴸ.l₀ K) (CCᴸ.d₀ K) (CCᴸ.Gg K) (CCᴸ.lE K) (CCᴸ.dE K) Go₀ Go
     (mono-lab nu c 0 l₀ (lk 0)) (λ k → mono-lab nu c (suc k) (lk k) (lk (suc k))) ,
  lω c (l≅ (λ n → ≅-refl⁰ _)) (outsLab l₀ lk)
```


**原子与第 0 层的结构标签.** `Atomᴸ` 同 DecoupleBase 的 `Atom`, 证书换成 `Goodᴸ`. `Lab0ᴸ` 是 DecoupleBase 的 `Lab₁` 在第 0 层的部分 (`li`/`lŝ`/`lu` 在第 0 层不出现; Omega2Base 只在第 0 层经 `atomL` 用 `Lab₁`, 非零层用 `LabS`). 改动只在两行待计值链: `lŝ₀`/`lĉ` 不再 "对一切链证书 `K`", 而是**携带**一个链证书, 输出只在它的链点处带标签. `atomL` (原子 $\Rightarrow$ 结构标签) 读的正是原子自带证书的链证书与输出, 所以与 DecoupleBase 不同, 不需要 `chain≅` 把别的证书的链点对上.

```agda
Atomᴸ : Ordˢ zero → T → Set
Atomᴸ x θ = (x ≅ˢ x) × Σ (Goodᴸ (toZ x)) (λ G → Lab (forceᴸ (toZ x) G) θ)

Atomᴸ-≅ : ∀ {x y : Ordˢ zero} {θ} → Atomᴸ x θ → y ≅ˢ x → Atomᴸ y θ
Atomᴸ-≅ (ex , G , l) d = ≅ˢ-reflˡ d , Goodᴸ-tr (toZ-≅ (≅ˢ-sym d)) G , Lab-≅ (forceᴸ-≅ (toZ-≅ d) _ G) l

data Lab0ᴸ : Ordˢ zero → T → Set where
  lz  : ∀ {t} → cof t ≡ c0 → Lab0ᴸ Ord₊ˢ.zero t
  ls  : ∀ {t y} → cof t ≡ c1 → Lab0ᴸ y (pred t) → Lab0ᴸ (Ord₊ˢ.suc y) t
  ll  : ∀ {t} {F : ℕ → Ordˢ zero} → cof t ≡ cω → (∀ n → Lab0ᴸ (F n) (fsn t n)) → Lab0ᴸ (Ord₊ˢ.lim F) t
  lŝ₀ : ∀ {t c} {t₀ : Ordˢ zero} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ zero} → cof t ≡ cω →
        (K : CCᴸ c (toZ t₀) (λ η e → toZ (g η e))) → Lab0ᴸ t₀ (fsn t 0) →
        (∀ k → Lab0ᴸ (g (lvK K k) (dxK K k)) (fsn t (suc k))) → Lab0ᴸ (Ord₊ˢ.ŝ {ℓ = zero} c t₀ g) t
  lĉ  : ∀ {t c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {o₀ : Ordˢ zero} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ zero} → cof t ≡ cω →
        (K : CCᴸ c t₀ g) → Lab0ᴸ o₀ (fsn t 0) → (∀ k → Lab0ᴸ (o (lvK K k) (dxK K k)) (fsn t (suc k))) →
        Lab0ᴸ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) t

atomL : ∀ {x : Ordˢ zero} {θ} → Atomᴸ x θ → Lab0ᴸ x θ
atomL {x = Ord₊ˢ.zero} (ex , gz , l0 c e) = lz c
atomL {x = Ord₊ˢ.zero} (ex , gz , l1 c () l)
atomL {x = Ord₊ˢ.zero} (ex , gz , lω c () h)
atomL {x = Ord₊ˢ.suc x} (ex , gs G , l0 c ())
atomL {x = Ord₊ˢ.suc x} (ex , gs G , l1 c (s≅ e) l) = ls c (atomL (s-invˢ ex , G , Lab-≅ e l))
atomL {x = Ord₊ˢ.suc x} (ex , gs G , lω c () h)
atomL {x = Ord₊ˢ.lim f} (ex , gl G st , l0 c ())
atomL {x = Ord₊ˢ.lim f} (ex , gl G st , l1 c () l)
atomL {x = Ord₊ˢ.lim f} (ex , gl G st , lω c (l≅ k) h) = ll c (λ n → atomL (l-invˢ ex n , G n , Lab-≅ (k n) (h n)))
atomL {x = Ord₊ˢ.limᵢ () f} at
atomL {x = Ord₊ˢ.up () x} at
atomL {x = Ord₊ˢ.ŝ c t₀ g} (ex , gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo , l0 c′ ())
atomL {x = Ord₊ˢ.ŝ c t₀ g} (ex , gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo , l1 c′ () l)
atomL {x = Ord₊ˢ.ŝ c t₀ g} (ex , gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo , lω cw (l≅ k) h) =
  lŝ₀ cw (ccᴸ γ G₀ l₀ d₀ Gg lE dE) (atomL (ŝ-refl₀ ex , Go₀ , Lab-≅ (k 0) (h 0)))
      (λ m → atomL (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _) , Go m , Lab-≅ (k (suc m)) (h (suc m))))
atomL {x = Ord₊ˢ.ĉᴸ c t₀ g o₀ o} (ex , gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo , l0 c′ ())
atomL {x = Ord₊ˢ.ĉᴸ c t₀ g o₀ o} (ex , gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo , l1 c′ () l)
atomL {x = Ord₊ˢ.ĉᴸ c t₀ g o₀ o} (ex , gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo , lω cw (l≅ k) h) =
  lĉ cw (ccᴸ γ G₀ l₀ d₀ Gg lE dE) (atomL (ĉ-refl₀ ex , Go₀ , Lab-≅ (k 0) (h 0)))
     (λ m → atomL (ĉ-reflg ex _ _ , Go m , Lab-≅ (k (suc m)) (h (suc m))))
```


## §6 第 0 层的和与规则 4

`addᴸ`: $a+b$ 的证书与标签 (DecoupleBase 的 `faddᶻ` + Stage2 的 `Lab-+` 的合体, 但直接对 $b$ 的证书与计值标签递归, 不经 "计值与证书无关"): 后继、极限逐项, 待计值链保留 $b$ 的链证书、输出加 $a$. 单调由标签 (要 $x+ys$ 是标准形). `repᴸ`: $P\cdot n$.

```agda
addᴸ : ∀ {a b : Ordˢ zero} {x ys} (Ga : Goodᴸ (toZ a)) → Lab (forceᴸ _ Ga) (x ∷ []) →
       (Gb : Goodᴸ (toZ b)) → Lab (forceᴸ _ Gb) ys → NF₁ (x ∷ ys) →
       Σ (Goodᴸ (toZ (a +ˢ b))) λ G → Lab (forceᴸ _ G) (x ∷ ys)
addᴸ {b = Ord₊ˢ.zero} {ys = []} Ga la gz lb nf = Ga , la
addᴸ {b = Ord₊ˢ.zero} {ys = y ∷ ys} Ga la gz (l0 c e) nf = ⊥-elim (cof-ne y ys c)
addᴸ {b = Ord₊ˢ.zero} {ys = y ∷ ys} Ga la gz (l1 c () l) nf
addᴸ {b = Ord₊ˢ.zero} {ys = y ∷ ys} Ga la gz (lω c () h) nf
addᴸ {b = Ord₊ˢ.suc b} Ga la (gs Gb) (l0 c ()) nf
addᴸ {b = Ord₊ˢ.suc b} {ys = []} Ga la (gs Gb) (l1 () e l) nf
addᴸ {b = Ord₊ˢ.suc b} {ys = y ∷ ys} Ga la (gs Gb) (l1 c (s≅ e) l) nf =
  gs (proj₁ Rb) , l1 c (s≅ (≅-refl⁰ _)) (proj₂ Rb)
  where Rb = addᴸ Ga la Gb (Lab-≅ e l) (NF₁-pred nf c)
addᴸ {b = Ord₊ˢ.suc b} Ga la (gs Gb) (lω c () h) nf
addᴸ {b = Ord₊ˢ.lim f} Ga la (gl Gb st) (l0 c ()) nf
addᴸ {b = Ord₊ˢ.lim f} Ga la (gl Gb st) (l1 c () l) nf
addᴸ {b = Ord₊ˢ.lim f} {ys = []} Ga la (gl Gb st) (lω () e h) nf
addᴸ {b = Ord₊ˢ.lim f} {ys = y ∷ ys} Ga la (gl Gb st) (lω c (l≅ k) h) nf =
  limᴸ nf c (λ n → proj₁ (addᴸ Ga la (Gb n) (Lab-≅ (k n) (h n)) (NF₁-fsn nf c n)))
            (λ n → proj₂ (addᴸ Ga la (Gb n) (Lab-≅ (k n) (h n)) (NF₁-fsn nf c n)))
addᴸ {b = Ord₊ˢ.limᵢ () f} Ga la Gb lb nf
addᴸ {b = Ord₊ˢ.up () x} Ga la Gb lb nf
addᴸ {b = Ord₊ˢ.ŝ c t₀ g} Ga la (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) (l0 c′ ()) nf
addᴸ {b = Ord₊ˢ.ŝ c t₀ g} Ga la (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) (l1 c′ () l) nf
addᴸ {b = Ord₊ˢ.ŝ c t₀ g} {ys = []} Ga la (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) (lω () e h) nf
addᴸ {b = Ord₊ˢ.ŝ c t₀ g} {ys = y ∷ ys} Ga la (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) (lω cw (l≅ k) h) nf =
  ĉᴸ-mk nf cw (ccᴸ γ G₀ l₀ d₀ Gg lE dE)
        (proj₁ (addᴸ Ga la Go₀ (Lab-≅ (k 0) (h 0)) (NF₁-fsn nf cw 0)))
        (proj₂ (addᴸ Ga la Go₀ (Lab-≅ (k 0) (h 0)) (NF₁-fsn nf cw 0)))
        (λ m → proj₁ (addᴸ Ga la (Go m) (Lab-≅ (k (suc m)) (h (suc m))) (NF₁-fsn nf cw (suc m))))
        (λ m → proj₂ (addᴸ Ga la (Go m) (Lab-≅ (k (suc m)) (h (suc m))) (NF₁-fsn nf cw (suc m))))
addᴸ {b = Ord₊ˢ.ĉᴸ c t₀ g o₀ o} Ga la (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) (l0 c′ ()) nf
addᴸ {b = Ord₊ˢ.ĉᴸ c t₀ g o₀ o} Ga la (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) (l1 c′ () l) nf
addᴸ {b = Ord₊ˢ.ĉᴸ c t₀ g o₀ o} {ys = []} Ga la (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) (lω () e h) nf
addᴸ {b = Ord₊ˢ.ĉᴸ c t₀ g o₀ o} {ys = y ∷ ys} Ga la (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) (lω cw (l≅ k) h) nf =
  ĉᴸ-mk nf cw (ccᴸ γ G₀ l₀ d₀ Gg lE dE)
        (proj₁ (addᴸ Ga la Go₀ (Lab-≅ (k 0) (h 0)) (NF₁-fsn nf cw 0)))
        (proj₂ (addᴸ Ga la Go₀ (Lab-≅ (k 0) (h 0)) (NF₁-fsn nf cw 0)))
        (λ m → proj₁ (addᴸ Ga la (Go m) (Lab-≅ (k (suc m)) (h (suc m))) (NF₁-fsn nf cw (suc m))))
        (λ m → proj₂ (addᴸ Ga la (Go m) (Lab-≅ (k (suc m)) (h (suc m))) (NF₁-fsn nf cw (suc m))))

repᴸ : ∀ {P : Ordˢ zero} {x} (GP : Goodᴸ (toZ P)) → Lab (forceᴸ _ GP) (x ∷ []) → (∀ n → NF₁ (replicate n x)) →
       ∀ n → Σ (Goodᴸ (toZ (iter (P +ˢ_) Ord₊ˢ.zero n))) λ G → Lab (forceᴸ _ G) (replicate n x)
repᴸ GP lP nf zero    = gz , l0 refl z≅
repᴸ GP lP nf (suc n) = addᴸ GP lP (proj₁ (repᴸ GP lP nf n)) (proj₂ (repᴸ GP lP nf n)) (nf (suc n))
```


## §7 `Pre0ᴸ`: 第 0 层尾巴上的带前缀 $\psi_0$, 证书与标签一起

DecoupleBase 的 `Pre0` (只取第 0 层的尾巴, 那是 Omega2Base 经 `atomL` 用到的唯一部分) 的产出式版本: 不再 "对给定的证书 $G$ 给标签", 而是对 `Lab0ᴸ` 推导递归**造出**证书与标签的对. 尾巴 0 是 `pop0ᴸ`; 后继是规则 4 (`repᴸ` 与 `limᴸ`); 极限逐项 (`limᴸ`); 待计值链保留行里携带的链证书, 输出由递归 (`ĉᴸ-mk`). 第 $n$ 项的标签都是 $\psi_0(\Omega_\Omega+a)[n]$, 单调全由 `mono-lab`.

```agda
Pre0ᴸ : ∀ {L} {p : zero <ᴵ L} {σ : Simᴵ zero L} {z : zero <ᴵ L} {x : Ordˢ zero} {a} →
        Lab0ᴸ x a → x ≅ˢ x → NF₁ (ctx a) → Σ (Goodᴸ (toZ (ψ1 p σ z x))) λ G → Lab (forceᴸ _ G) (ctx a)
Pre0ᴸ {p = p} {σ = σ} {z = z} {a = []} (lz c) ex nu = pop0ᴸ p σ z
Pre0ᴸ {a = y ∷ ys} (lz c) ex nu = ⊥-elim (cof-ne y ys c)
Pre0ᴸ {a = []} (ls () l) ex nu
Pre0ᴸ {p = p} {σ = σ} {z = z} {a = y ∷ ys} (ls c l) ex nu =
  limᴸ nu (cong (cofA []) c) (λ n → proj₁ (Rs n)) (λ n → subst (Lab _) (sym (fs-rep [] ΩΩ (y ∷ ys) c n)) (proj₂ (Rs n)))
  where
  Rp = Pre0ᴸ {p = p} {σ = σ} {z = z} l (s-invˢ ex) (subst NF₁ (fs-rep [] ΩΩ (y ∷ ys) c 1) (NF₁-fsn nu (cong (cofA []) c) 1))
  Rs = repᴸ (proj₁ Rp) (proj₂ Rp) (λ n → subst NF₁ (fs-rep [] ΩΩ (y ∷ ys) c n) (NF₁-fsn nu (cong (cofA []) c) n))
Pre0ᴸ {a = []} (ll () h) ex nu
Pre0ᴸ {p = p} {σ = σ} {z = z} {a = y ∷ ys} (ll c h) ex nu =
  limᴸ nu (cong (cofA []) c) (λ n → proj₁ (Pre0ᴸ {p = p} {σ = σ} {z = z} (h n) (l-invˢ ex n) (nfω nu c n)))
       (λ n → subst (Lab _) (sym (fs-ω [] ΩΩ (y ∷ ys) c n)) (proj₂ (Pre0ᴸ {p = p} {σ = σ} {z = z} (h n) (l-invˢ ex n) (nfω nu c n))))
Pre0ᴸ {a = []} (lŝ₀ () K h₀ hk) ex nu
Pre0ᴸ {p = p} {σ = σ} {z = z} {a = y ∷ ys} (lŝ₀ c K h₀ hk) ex nu =
  ĉᴸ-mk nu (cong (cofA []) c) K (proj₁ R₀) (subst (Lab _) (sym (fs-ω [] ΩΩ (y ∷ ys) c 0)) (proj₂ R₀))
        (λ k → proj₁ (Rk k)) (λ k → subst (Lab _) (sym (fs-ω [] ΩΩ (y ∷ ys) c (suc k))) (proj₂ (Rk k)))
  where
  R₀ = Pre0ᴸ {p = p} {σ = σ} {z = z} h₀ (ŝ-refl₀ ex) (nfω nu c 0)
  Rk = λ k → Pre0ᴸ {p = p} {σ = σ} {z = z} (hk k) (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) (nfω nu c (suc k))
Pre0ᴸ {a = []} (lĉ () K h₀ hk) ex nu
Pre0ᴸ {p = p} {σ = σ} {z = z} {a = y ∷ ys} (lĉ c K h₀ hk) ex nu =
  ĉᴸ-mk nu (cong (cofA []) c) K (proj₁ R₀) (subst (Lab _) (sym (fs-ω [] ΩΩ (y ∷ ys) c 0)) (proj₂ R₀))
        (λ k → proj₁ (Rk k)) (λ k → subst (Lab _) (sym (fs-ω [] ΩΩ (y ∷ ys) c (suc k))) (proj₂ (Rk k)))
  where
  R₀ = Pre0ᴸ {p = p} {σ = σ} {z = z} h₀ (ĉ-refl₀ ex) (nfω nu c 0)
  Rk = λ k → Pre0ᴸ {p = p} {σ = σ} {z = z} (hk k) (ĉ-reflg ex _ _) (nfω nu c (suc k))
```


## §8 全层级的关系式标签 `LabL`

Omega2Base §6 的 `LabS` 的复制 (改名 `LabL`; 不导入 Omega2Base, 因为它的第 0 层是 `Goodᶻ` 的原子). 与 `LabS` 的区别只在三处, 其余行逐字:

- 第 0 层 (`LvL zero`) 是 §5 的 `Atomᴸ` (证书换成 `Goodᴸ`).
- `gĉ` (任意层的待计值链 `ĉᴸ`) **携带**一个链证书 `K : CCᴸ c t₀ g`, 输出只在 `K` 的链点处带标签. `LabS` 的 `gĉ` 对一切 Prefix 链证书量化; 那样的行在产出式的递归里用不上 (§12 要的是一个现成的链证书), 而且 `Goodᴸ` 的链证书与 `Goodᶻ` 的不是同一种东西.
- `gŝ` (非零层闭包 $\psi_w(\Omega_\Omega+\cdots)$) 多三个字段, 都是闭包的**地板**: 弹栈时的目标下标 $w$ 与它的 `Idx`, 界 $c\sqsubseteq^\mathsf I\mathtt{lvl}\,w+1$, 以及 "$w$ 在每个 $t[\theta]$ 里作为下标出现" (SystemOmega 的 `Occ`). 它们由 `popL` (§11) 生成, 其余构造只搬运 (`Occ` 经 `od`/`ot` 往外包一层), 在 §12 的 `domᴸ` 里变成链点的支配. 分支仍只对带标签的 $Y$ 量化, 与 `LabS` 相同.

```agda
module _ (ℓ : Ordᴵ) (L< : (j : Ordᴵ) (r : j ◃ ℓ) → Uˢ j r → T → Set) where
  data LabL₊ : Ordˢ ℓ → T → Set where
    gz : ∀ {t} → cof t ≡ c0 → LabL₊ Ord₊ˢ.zero t
    gs : ∀ {t y} → cof t ≡ c1 → LabL₊ y (pred t) → LabL₊ (Ord₊ˢ.suc y) t
    gl : ∀ {t} {F : ℕ → Ordˢ ℓ} → cof t ≡ cω → (∀ n → LabL₊ (F n) (fsn t n)) → LabL₊ (Ord₊ˢ.lim F) t
    gu : ∀ {t k} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} → L< k (◃₁→◃ r) x t → LabL₊ (Ord₊ˢ.up r x) t
    gi : ∀ {t ν j} {q : j <ᴵ ℓ} {f : Uˢ j (<→◃ q) → Ordˢ ℓ} → cof t ≡ cΩ ν → (I : Idx ν) → j ≅ᴵ lvI I →
         (∀ η (x : Ordˢ j) → L< j (<→◃ q) (intoˢ (<→◃ q) x) η → LabL₊ (f (intoˢ (<→◃ q) x)) (fsT t η)) →
         LabL₊ (Ord₊ˢ.limᵢ q f) t
    gĉ : ∀ {t c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {o₀ : Ordˢ ℓ} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} → cof t ≡ cω →
         (K : CCᴸ c t₀ g) → LabL₊ o₀ (fsn t 0) →
         (∀ k → LabL₊ (o (lvK K k) (dxK K k)) (fsn t (suc k))) →
         LabL₊ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) t
    gŝ : ∀ {t c w} {t₀ : Ordˢ ℓ} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} → kd ℓ ≡ false → cof t ≡ cΩ [] →
         (Iw : Idx w) → c ⊑ᴵ suc (lvI Iw) → (∀ θ → Occ w (fsT t θ)) →
         LabL₊ t₀ (fsT t (natT 1)) →
         (∀ θ (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → (e : c ⊑ᴵ toLevel Y hY) →
          LabL₊ (g (toLevel Y hY) e) (fsT t θ)) →
         LabL₊ (Ord₊ˢ.ŝ c t₀ g) t

LvL : (i : Ordᴵ) → ((j : Ordᴵ) (r : j ◃ i) → Uˢ j r → T → Set) → Ordˢ i → T → Set
LvL zero      L x t = Atomᴸ x t
LvL (suc i)   L x t = LabL₊ (suc i) L x t
LvL (lim f s) L x t = LabL₊ (lim f s) L x t

Ll : ∀ {ℓ} (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → T → Set
Ll i zero         x t = LvL i Ll x t
Ll i (suc r)      x t = Ll i r x t
Ll _ (self {f} n) x t = LvL (f n) Ll x t
Ll i (lim n r)    x t = Ll i r x t

LabL : ∀ {ℓ} → Ordˢ ℓ → T → Set
LabL {ℓ} x t = LvL ℓ Ll x t

Ll→ : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordˢ i} {t} → Ll i r (intoˢ r x) t → LabL x t
Ll→ zero      h = h
Ll→ (suc r)   h = Ll→ r h
Ll→ (self n)  h = h
Ll→ (lim n r) h = Ll→ r h

→Ll : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordˢ i} {t} → LabL x t → Ll i r (intoˢ r x) t
→Ll zero      h = h
→Ll (suc r)   h = →Ll r h
→Ll (self n)  h = h
→Ll (lim n r) h = →Ll r h

toL₊ : ∀ {i} {x : Ordˢ i} {t} → kd i ≡ false → LabL x t → LabL₊ i Ll x t
toL₊ {i = zero}    () h
toL₊ {i = suc _}   k h = h
toL₊ {i = lim _ _} k h = h

frL₊ : ∀ {i} {x : Ordˢ i} {t} → kd i ≡ false → LabL₊ i Ll x t → LabL x t
frL₊ {i = zero}    () h
frL₊ {i = suc _}   k h = h
frL₊ {i = lim _ _} k h = h
```


**读法.** 为什么非零层要单独的 `LabL` 而不能沿用 Decouple 的 `LabG`, 见 Omega2Base §6 的读法 (`gi` 行的逆变位置). 本文的新字段都在 `gŝ`/`gĉ` 两行; `gi` 行与 `LabS` 逐字; `domᴸ` 要的 "地板可数" 由 §3 的 `Idx-Ctbl` 从标签读出, 不必放进 `Idx` 或 `gi` 行.

## §9 搬运与 $\Omega$

Omega2Base §7 逐字改名. `gŝ` 的搬运逐点, 地板字段原样传递 (界 $c$ 不动); `gĉ` 的链证书不动 (`trˢ` 对 `ĉᴸ` 不碰 `Z` 里的链). 第 0 层的搬运是 `Atomᴸ-≅`, 它用 §2 的 `Goodᴸ-tr`/`forceᴸ-≅`. `LabL-Ω` 与 Omega2Base 的 `LabS-Ω` 逐字 (第 0 层的 $\Omega_0=1$ 的证书换成 `gs gz`).

```agda
LabL-tr    : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ a} {t} → LabL x t → LabL (trˢ e x) t
LabL-tr⁻   : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ b} {t} → LabL x t → LabL (tr⁻ˢ e x) t
LabL-back  : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} {t} → LabL u t → LabL (backˢ (resˢ q e) u) t
LabL-back⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} {t} → LabL u t → LabL (backˢ (res⁻ˢ q e) u) t
L-tr  : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ a} {t} → LabL₊ a Ll x t → LabL₊ b Ll (trˢ e x) t
L-tr⁻ : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ b} {t} → LabL₊ b Ll x t → LabL₊ a Ll (tr⁻ˢ e x) t

LabL-tr z≅ at = Atomᴸ-≅ at (trˢ-≅ z≅ (proj₁ at))
LabL-tr (s≅ e) h = L-tr (s≅ e) h
LabL-tr (l≅ k) h = L-tr (l≅ k) h
LabL-tr⁻ z≅ at = Atomᴸ-≅ at (tr⁻ˢ-≅ z≅ (proj₁ at))
LabL-tr⁻ (s≅ e) h = L-tr⁻ (s≅ e) h
LabL-tr⁻ (l≅ k) h = L-tr⁻ (l≅ k) h

L-tr e (gz c)   = gz c
L-tr e (gs c h) = gs c (L-tr e h)
L-tr e (gl c h) = gl c (λ n → L-tr e (h n))
L-tr (s≅ e) (gu {r = zero} h)   = gu (LabL-tr e h)
L-tr (l≅ k) (gu {r = self n} h) = gu (LabL-tr (k n) h)
L-tr e {t = t} (gi {q = q} {f = f} c I ej h) =
  gi c I (≅ᴵ-trans (≅ᴵ-sym (eqˢ (resˢ q e))) ej)
     (λ η x l → subst (λ v → LabL₊ _ Ll (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) v)))) (fsT t η))
                      (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) x))
                      (L-tr e (h η (backˢ (resˢ q e) x) (→Ll (<→◃ q) (LabL-back q e (Ll→ (<→◃ (ltˢ (resˢ q e))) l))))))
L-tr e (gĉ c K h₀ hk) = gĉ c K (L-tr e h₀) (λ k → L-tr e (hk k))
L-tr e (gŝ kk c Ib bb ob h₀ hg) = gŝ (trans (sym (kd-≅ e)) kk) c Ib bb ob (L-tr e h₀) (λ θ Y hY lY nθ lt d → L-tr e (hg θ Y hY lY nθ lt d))

L-tr⁻ e (gz c)   = gz c
L-tr⁻ e (gs c h) = gs c (L-tr⁻ e h)
L-tr⁻ e (gl c h) = gl c (λ n → L-tr⁻ e (h n))
L-tr⁻ (s≅ e) (gu {r = zero} h)   = gu (LabL-tr⁻ e h)
L-tr⁻ (l≅ k) (gu {r = self n} h) = gu (LabL-tr⁻ (k n) h)
L-tr⁻ e {t = t} (gi {q = q} {f = f} c I ej h) =
  gi c I (≅ᴵ-trans (≅ᴵ-sym (eqˢ (res⁻ˢ q e))) ej)
     (λ η x l → subst (λ v → LabL₊ _ Ll (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) v)))) (fsT t η))
                      (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) x))
                      (L-tr⁻ e (h η (backˢ (res⁻ˢ q e) x) (→Ll (<→◃ q) (LabL-back⁻ q e (Ll→ (<→◃ (ltˢ (res⁻ˢ q e))) l))))))
L-tr⁻ e (gĉ c K h₀ hk) = gĉ c K (L-tr⁻ e h₀) (λ k → L-tr⁻ e (hk k))
L-tr⁻ e (gŝ kk c Ib bb ob h₀ hg) = gŝ (trans (kd-≅ e) kk) c Ib bb ob (L-tr⁻ e h₀) (λ θ Y hY lY nθ lt d → L-tr⁻ e (hg θ Y hY lY nθ lt d))

LabL-back zero      (s≅ e) h = LabL-tr⁻ e h
LabL-back (suc q)   (s≅ e) h = LabL-back q e h
LabL-back (lim n q) (l≅ k) h = LabL-back q (k n) h

LabL-back⁻ zero      (s≅ e) h = LabL-tr e h
LabL-back⁻ (suc q)   (s≅ e) h = LabL-back⁻ q e h
LabL-back⁻ (lim n q) (l≅ k) h = LabL-back⁻ q (k n) h
```


```agda
LabL-Ω : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → ∀ {a} → a ≅ᴵ toLevel Y hY → LabL (Ωˢ a) (Ωt θ)
LabL-Ω {θ = []} Ord₊.zero hY l nθ z≅ = Ωˢ-refl zero , gs gz , l1 refl (s≅ z≅) (l0 refl z≅)
LabL-Ω {θ = y ∷ ys} Ord₊.zero hY l nθ z≅ with Lab0[] l
... | ()
LabL-Ω {θ = θ} (Ord₊.suc Y) hY (l0 c ()) nθ (s≅ e)
LabL-Ω {θ = θ} (Ord₊.suc Y) hY (lω c () h) nθ (s≅ e)
LabL-Ω {θ = []} (Ord₊.suc Y) hY (l1 () (s≅ e′) l) nθ (s≅ e)
LabL-Ω {θ = w ∷ ws} (Ord₊.suc Y) hY (l1 c (s≅ e′) l) nθ (s≅ e) =
  gi (cong (E.cofψ0 (w ∷ ws)) c) (Y , hs⁻ hY , Lab-≅ e′ l , NF₁-pred nθ c) e
     (λ η x lx → gu (subst (LabL x) (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) c η)) lx))
LabL-Ω {θ = θ} (Ord₊.lim F) hY (l0 c ()) nθ (l≅ k)
LabL-Ω {θ = θ} (Ord₊.lim F) hY (l1 c () l) nθ (l≅ k)
LabL-Ω {θ = []} (Ord₊.lim F) hY (lω () (l≅ k′) h) nθ (l≅ k)
LabL-Ω {θ = w ∷ ws} (Ord₊.lim F) hY (lω c (l≅ k′) h) nθ (l≅ k) =
  gl (cong (E.cofψ0 (w ∷ ws)) c)
     (λ n → gu (subst (LabL _) (sym (E.fsn0-eq w ws n c))
                      (LabL-Ω (F n) (hl₁ hY n) (Lab-≅ (k′ n) (h n)) (NF₁-fsn nθ c n) (k n))))
LabL-Ω (Ord₊.limᵢ () f) hY l nθ e
LabL-Ω (Ord₊.up () x) hY l nθ e
```


## §10 不带前缀的 $\psi_w$

Omega2Base §8 逐字改名, 改动: 第 0 层的和 `LSumA` 与 `PsiAL` 对 `Lab0ᴸ` 归纳 (DecoupleBase 的 `Lab₁` 在第 0 层的 `lu`/`li`/`lŝ` 行不出现, 删去), 待计值链的行把链证书 `K` 原样交给 `gĉ`; `gŝ` 情形把 $w$ 的出现往外包一层 (`LSum₊`: $x+t[\theta]$ 用 `ot`; `PsiL₊`: $\psi_{w′}(t[\theta])$ 用 `od`, 经 Prefix 的 `H1-fsT`).

```agda
LSumA : ∀ {ℓ} {a : Ordˢ ℓ} {σ : Simᴵ zero ℓ} {b : Ordˢ zero} {x ys} → LabL₊ ℓ Ll a (x ∷ []) → Lab0ᴸ b ys →
        LabL₊ ℓ Ll (addˢ a σ b) (x ∷ ys)
LSumA {ys = []} la (lz c) = la
LSumA {ys = y ∷ ys} la (lz c) = ⊥-elim (cof-ne y ys c)
LSumA {ys = []} la (ls () l)
LSumA {ys = y ∷ ys} la (ls c l) = gs c (LSumA la l)
LSumA {ys = []} la (ll () h)
LSumA {ys = y ∷ ys} la (ll c h) = gl c (λ n → LSumA la (h n))
LSumA {ys = []} la (lŝ₀ () K h₀ hk)
LSumA {ys = y ∷ ys} la (lŝ₀ c K h₀ hk) = gĉ c K (LSumA la h₀) (λ m → LSumA la (hk m))
LSumA {ys = []} la (lĉ () K h₀ hk)
LSumA {ys = y ∷ ys} la (lĉ c K h₀ hk) = gĉ c K (LSumA la h₀) (λ m → LSumA la (hk m))

LSum  : ∀ {k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} {x ys} → kd ℓ ≡ false → LabL₊ ℓ Ll a (x ∷ []) → LabL b ys →
        LabL₊ ℓ Ll (addˢ a σ b) (x ∷ ys)
LSum₊ : ∀ {k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} {x ys} → kd ℓ ≡ false → LabL₊ ℓ Ll a (x ∷ []) → LabL₊ k Ll b ys →
        LabL₊ ℓ Ll (addˢ a σ b) (x ∷ ys)
LSum {k = zero} kl la at = LSumA la (atomL at)
LSum {k = suc _} kl la h = LSum₊ kl la h
LSum {k = lim _ _} kl la h = LSum₊ kl la h
LSum₊ {ys = []} kl la (gz c) = la
LSum₊ {ys = y ∷ ys} kl la (gz c) = ⊥-elim (cof-ne y ys c)
LSum₊ {ys = []} kl la (gs () h)
LSum₊ {ys = y ∷ ys} kl la (gs c h) = gs c (LSum₊ kl la h)
LSum₊ {ys = []} kl la (gl () h)
LSum₊ {ys = y ∷ ys} kl la (gl c h) = gl c (λ n → LSum₊ kl la (h n))
LSum₊ {σ = σ} kl la (gu {r = zero} h) = LSum {σ = λ q → σ (suc q)} kl la h
LSum₊ {σ = σ} kl la (gu {r = self n} h) = LSum {σ = λ q → σ (lim n q)} kl la h
LSum₊ {ys = []} kl la (gi () I ej h)
LSum₊ {a = a} {σ = σ} {x = x} {ys = y ∷ ys} kl la (gi {q = q} {f = f} c I ej h) =
  gi c I ej (λ η w l → subst (λ v → LabL₊ _ Ll (addˢ a σ (f (intoˢ (<→◃ q) v))) (x ∷ fsT (y ∷ ys) η))
                             (sym (out-intoˢ (<→◃ (σ q)) w))
                             (LSum₊ kl la (h η w (→Ll (<→◃ q) (Ll→ (<→◃ (σ q)) l)))))
LSum₊ {ys = []} kl la (gĉ () K h₀ hk)
LSum₊ {ys = y ∷ ys} kl la (gĉ c K h₀ hk) = gĉ c K (LSum₊ kl la h₀) (λ m → LSum₊ kl la (hk m))
LSum₊ {k = zero} kl la (gŝ () c Ib bb ob h₀ hg)
LSum₊ {k = suc _} {ys = []} kl la (gŝ kk () Ib bb ob h₀ hg)
LSum₊ {k = suc _} {ys = y ∷ ys} kl la (gŝ kk c Ib bb ob h₀ hg) =
  gŝ kl c Ib bb (λ θ → ot (ob θ)) (LSum₊ kl la h₀) (λ θ Y hY lY nθ lt e → LSum₊ kl la (hg θ Y hY lY nθ lt e))
LSum₊ {k = lim _ _} {ys = []} kl la (gŝ kk () Ib bb ob h₀ hg)
LSum₊ {k = lim _ _} {ys = y ∷ ys} kl la (gŝ kk c Ib bb ob h₀ hg) =
  gŝ kl c Ib bb (λ θ → ot (ob θ)) (LSum₊ kl la h₀) (λ θ Y hY lY nθ lt e → LSum₊ kl la (hg θ Y hY lY nθ lt e))

LRep : ∀ {ℓ} {P : Ordˢ ℓ} {x} → kd ℓ ≡ false → LabL₊ ℓ Ll P (x ∷ []) → ∀ n →
       LabL₊ ℓ Ll (iter (P +ˢ_) Ord₊ˢ.zero n) (replicate n x)
LRep kl lP zero    = gz refl
LRep kl lP (suc n) = LSum₊ kl lP (LRep kl lP n)
```


```agda
-- the Ω_{ν+1}-row of ψ_w, given the two recursive calls as oracles
giPsiL : ∀ {k ℓ i w ν j y ys} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
        (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
        (rec : ∀ η (x : Ordˢ j) → LabL x η → LabL₊ i Ll (ψ0 p σ (f (intoˢ (<→◃ q) x))) (ψᵗ w (fsT (y ∷ ys) η) ∷ [])) →
        (recC : kd j ≡ false → ∀ η (x : Ordˢ j) → LabL x η →
                LabL₊ j Ll (ψ0 (σ q) σ (f (intoˢ (<→◃ q) x))) (ψᵗ ν (fsT (y ∷ ys) η) ∷ [])) →
        LabL₊ i Ll (ψ0 p σ (Ord₊ˢ.limᵢ q f)) (ψᵗ w (y ∷ ys) ∷ [])
giPsiL {i = i} {w = w} {ν = ν} {j = j} {y = y} {ys = ys} {p = p} {σ = σ} {q = q} {f = f} Iw ei ki c Iν ej rec recC =
  go (cmpᵀ (sucT ν) w) refl
  where
  pen : Pen (cmpᵀ (sucT ν) w) → LabL₊ i Ll (ψ0 p σ (Ord₊ˢ.limᵢ q f)) (ψᵗ w (y ∷ ys) ∷ [])
  pen pn with pen0 {p = p} {σ = σ} {q = q} {f = f} (≅ᴵ-refl j)
                   (≺ᴵ-respʳ (≺ᴵ-respˡ ej (Ilt Iν Iw (pen→< ν w pn))) (≅ᴵ-sym ei))
  ... | j′ , e , r , eqn =
    subst (λ W → LabL₊ i Ll W (ψᵗ w (y ∷ ys) ∷ [])) (sym eqn)
          (gi cofE Iν (≅ᴵ-trans (≅ᴵ-sym e) ej)
              (λ η x l → subst (λ v → LabL₊ i Ll (ψ0 p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e v)))) (fsT (ψᵗ w (y ∷ ys) ∷ []) η))
                               (sym (out-intoˢ (<→◃ r) x))
                               (subst (LabL₊ i Ll _) (sym (fsT₊-pen′ w (y ∷ ys) ν (cof (y ∷ ys)) c pn η))
                                      (rec η (tr⁻ˢ e x) (LabL-tr⁻ e (Ll→ (<→◃ r) l))))))
    where
    cofE : cof (ψᵗ w (y ∷ ys) ∷ []) ≡ cΩ ν
    cofE = trans (cong (E.cofA w) c) (cofP pn)
  ne-w : w ≡ [] → ⊥
  ne-w refl = tf (trans (sym (kdI[] Iw)) (trans (sym (kd-≅ ei)) ki))
  fold : cmpᵀ (sucT ν) w ≡ gt → LabL₊ i Ll (ψ0 p σ (Ord₊ˢ.limᵢ q f)) (ψᵗ w (y ∷ ys) ∷ [])
  fold em =
    subst (λ W → LabL₊ i Ll W (ψᵗ w (y ∷ ys) ∷ [])) (sym (fold0 {p = p} {σ = σ} {q = q} {f = f} ij))
          (gl (trans (cong (E.cofA w) c) (cong (E.cofψ₊ w ν) em))
              (λ m → subst (LabL₊ i Ll _) (sym (fs-gt w y ys ν c em m)) (rec _ _ (chainL m))))
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
    kj = trans (kd-≅ ej) (kdI′ Iν (gtν em ne-w))
    chainL : ∀ m → LabL (chain0 σ q f m) (γT (y ∷ ys) ν m)
    chainL zero    = LabL-Ω (proj₁ Iν) (proj₁ (proj₂ Iν)) (proj₁ (proj₂ (proj₂ Iν))) (proj₂ (proj₂ (proj₂ Iν))) ej
    chainL (suc m) = frL₊ kj (recC kj _ _ (chainL m))
  go : ∀ m → cmpᵀ (sucT ν) w ≡ m → LabL₊ i Ll (ψ0 p σ (Ord₊ˢ.limᵢ q f)) (ψᵗ w (y ∷ ys) ∷ [])
  go lt em = pen (inj₁ em)
  go eq em = pen (inj₂ em)
  go gt em = fold em
```


```agda
PsiAL : ∀ {ℓ i w} {p : i <ᴵ ℓ} {σ : Simᴵ zero ℓ} {X : Ordˢ zero} {b} (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
       Lab0ᴸ X b → LabL₊ i Ll (ψ0 p σ X) (ψᵗ w b ∷ [])
PsiAL {b = []} (Y , hY , lY , nY) ei ki (lz c) = toL₊ ki (LabL-Ω Y hY lY nY ei)
PsiAL {b = y ∷ ys} Iw ei ki (lz c) = ⊥-elim (cof-ne y ys c)
PsiAL {b = []} Iw ei ki (ls () l)
PsiAL {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (ls c l) =
  gl (cong (E.cofA w) c) (λ n → subst (LabL₊ _ Ll _) (sym (fs-rep w y ys c n)) (LRep ki (PsiAL {p = p} {σ = σ} Iw ei ki l) n))
PsiAL {b = []} Iw ei ki (ll () h)
PsiAL {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (ll c h) =
  gl (cong (E.cofA w) c) (λ n → subst (LabL₊ _ Ll _) (sym (fs-ω w y ys c n)) (PsiAL {p = p} {σ = σ} Iw ei ki (h n)))
PsiAL {b = []} Iw ei ki (lŝ₀ () K h₀ hk)
PsiAL {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (lŝ₀ c K h₀ hk) =
  gĉ (cong (E.cofA w) c) K (subst (LabL₊ _ Ll _) (sym (fs-ω w y ys c 0)) (PsiAL {p = p} {σ = σ} Iw ei ki h₀))
     (λ m → subst (LabL₊ _ Ll _) (sym (fs-ω w y ys c (suc m))) (PsiAL {p = p} {σ = σ} Iw ei ki (hk m)))
PsiAL {b = []} Iw ei ki (lĉ () K h₀ hk)
PsiAL {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (lĉ c K h₀ hk) =
  gĉ (cong (E.cofA w) c) K (subst (LabL₊ _ Ll _) (sym (fs-ω w y ys c 0)) (PsiAL {p = p} {σ = σ} Iw ei ki h₀))
     (λ m → subst (LabL₊ _ Ll _) (sym (fs-ω w y ys c (suc m))) (PsiAL {p = p} {σ = σ} Iw ei ki (hk m)))

PsiVL  : ∀ {k ℓ i w} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {X : Ordˢ k} {b} (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
        LabL X b → LabL₊ i Ll (ψ0 p σ X) (ψᵗ w b ∷ [])
PsiL₊ : ∀ {k ℓ i w} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {X : Ordˢ k} {b} (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
        LabL₊ k Ll X b → LabL₊ i Ll (ψ0 p σ X) (ψᵗ w b ∷ [])
PsiVL {k = zero}    {p = p} {σ = σ} Iw ei ki at = PsiAL {p = p} {σ = σ} Iw ei ki (atomL at)
PsiVL {k = suc _}   {p = p} {σ = σ} Iw ei ki h  = PsiL₊ {p = p} {σ = σ} Iw ei ki h
PsiVL {k = lim _ _} {p = p} {σ = σ} Iw ei ki h  = PsiL₊ {p = p} {σ = σ} Iw ei ki h

PsiL₊ {b = []} (Y , hY , lY , nY) ei ki (gz c) = toL₊ ki (LabL-Ω Y hY lY nY ei)
PsiL₊ {b = y ∷ ys} Iw ei ki (gz c) = ⊥-elim (cof-ne y ys c)
PsiL₊ {b = []} Iw ei ki (gs () l)
PsiL₊ {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gs c l) =
  gl (cong (E.cofA w) c) (λ n → subst (LabL₊ _ Ll _) (sym (fs-rep w y ys c n)) (LRep ki (PsiL₊ {p = p} {σ = σ} Iw ei ki l) n))
PsiL₊ {b = []} Iw ei ki (gl () h)
PsiL₊ {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gl c h) =
  gl (cong (E.cofA w) c) (λ n → subst (LabL₊ _ Ll _) (sym (fs-ω w y ys c n)) (PsiL₊ {p = p} {σ = σ} Iw ei ki (h n)))
PsiL₊ {p = p} {σ = σ} Iw ei ki (gu {r = zero} h)   = PsiVL {p = p} {σ = λ q → σ (suc q)} Iw ei ki h
PsiL₊ {p = p} {σ = σ} Iw ei ki (gu {r = self n} h) = PsiVL {p = p} {σ = λ q → σ (lim n q)} Iw ei ki h
PsiL₊ {b = []} Iw ei ki (gi () Iν ej h)
PsiL₊ {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gi {q = q} {f = f} c Iν ej h) =
  giPsiL {p = p} {σ = σ} {q = q} {f = f} Iw ei ki c Iν ej
        (λ η x l → PsiL₊ {p = p} {σ = σ} Iw ei ki (h η x (→Ll (<→◃ q) l)))
        (λ kj η x l → PsiL₊ {p = σ q} {σ = σ} Iν ej kj (h η x (→Ll (<→◃ q) l)))
PsiL₊ {b = []} Iw ei ki (gĉ () K h₀ hk)
PsiL₊ {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gĉ c K h₀ hk) =
  gĉ (cong (E.cofA w) c) K (subst (LabL₊ _ Ll _) (sym (fs-ω w y ys c 0)) (PsiL₊ {p = p} {σ = σ} Iw ei ki h₀))
     (λ m → subst (LabL₊ _ Ll _) (sym (fs-ω w y ys c (suc m))) (PsiL₊ {p = p} {σ = σ} Iw ei ki (hk m)))
PsiL₊ {k = zero} Iw ei ki (gŝ () c Ib bb ob h₀ hg)
PsiL₊ {k = suc _} {w = []} Iw ei ki (gŝ kk c Ib bb ob h₀ hg) = ⊥-elim (tf (trans (sym (kdI[] Iw)) (trans (sym (kd-≅ ei)) ki)))
PsiL₊ {k = suc _} {w = x ∷ xs} {b = []} Iw ei ki (gŝ kk () Ib bb ob h₀ hg)
PsiL₊ {k = suc _} {w = x ∷ xs} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gŝ kk c Ib bb ob h₀ hg) =
  gŝ ki (trans (cong (E.cofA (x ∷ xs)) c) (H1-pen x xs)) Ib bb (λ θ → subst (Occ _) (sym (H1-fsT x xs y ys c θ)) (od (ob θ)))
     (subst (LabL₊ _ Ll _) (sym (H1-fsT x xs y ys c (natT 1))) (PsiL₊ {p = p} {σ = σ} Iw ei ki h₀))
     (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (H1-fsT x xs y ys c θ))
                                  (PsiL₊ {p = p} {σ = σ} Iw ei ki (hg θ Y hY lY nθ lt e)))
PsiL₊ {k = lim _ _} {w = []} Iw ei ki (gŝ kk c Ib bb ob h₀ hg) = ⊥-elim (tf (trans (sym (kdI[] Iw)) (trans (sym (kd-≅ ei)) ki)))
PsiL₊ {k = lim _ _} {w = x ∷ xs} {b = []} Iw ei ki (gŝ kk () Ib bb ob h₀ hg)
PsiL₊ {k = lim _ _} {w = x ∷ xs} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gŝ kk c Ib bb ob h₀ hg) =
  gŝ ki (trans (cong (E.cofA (x ∷ xs)) c) (H1-pen x xs)) Ib bb (λ θ → subst (Occ _) (sym (H1-fsT x xs y ys c θ)) (od (ob θ)))
     (subst (LabL₊ _ Ll _) (sym (H1-fsT x xs y ys c (natT 1))) (PsiL₊ {p = p} {σ = σ} Iw ei ki h₀))
     (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (H1-fsT x xs y ys c θ))
                                  (PsiL₊ {p = p} {σ = σ} Iw ei ki (hg θ Y hY lY nθ lt e)))
```


## §11 带前缀的 $\psi_w$, 目标 $w\ne0$

记号: `ctxw w b` $=\psi_w(\Omega_\Omega+b)$. `PreL₊ Iw : LabL₊ k X b → LabL₊ i (ψ1 p σ z X) (ctxw w b)`, 目标层 $i\cong^\mathsf I$ `lvI Iw` 非零, 环境层号、`Sim`、帧证据任意. 这是 DecoupleBase 的 `Pre1` (只有 $w=1$, 只收 `Lab0ᴸ`) 的推广, 证明照 `PsiL₊` 的结构, 参数列表前多一个 $\Omega_\Omega$:

- `gz`: 弹栈闭包 `popL` $=\psi_w(\Omega_\Omega)$: 字面是 `ŝ (suc i) (t₀pop p z) (gpop p z)`, 第 0 点 $\psi_w(\Omega_1)$ 与分支 $\psi_w(\Omega_{\mathtt{lvl}\,Y})$ 都不带前缀, 由 `PsiVL` 与 `LabL-Ω`. **地板在这里生成**: 下标 $w$ 与它的 `Iw`, 界 $i+1\sqsubseteq^\mathsf I\mathtt{lvl}\,w+1$ (由 $i\cong^\mathsf I\mathtt{lvl}\,w$), $t[\theta]=\psi_w(\Omega_\theta)$ 的首项下标就是 $w$ (`oh`).
- `gs`/`gl`/`gĉ`: 规则 4/逐项, 记号侧 `fs-rep w ΩΩ (y ∷ ys)` 等 (参数是 $\Omega_\Omega+b$).
- `gi`: `giPreL`, 与 `giPsiL` 同: `lt`/`eq` 由 `pen1` 穿透 (`fsT₊-pen′ w (ΩΩ ∷ y ∷ ys)`), `gt` 由 `fold1` 折叠, 链点 $\gamma_{m+1}=\psi^{[\hat\Omega]}_\nu(f\,\gamma_m)$ 的标签由递归 `recC` 在节点层 $\nu$ 上给出 (**带前缀的链**, 链点 $\psi_\nu(\Omega_\Omega+b[\gamma_m])$).
- `gŝ`: 逐点, `H1-fsT x xs ΩΩ (y ∷ ys)`; 出现包成 $\psi_{w′}(\Omega_\Omega+t[\theta])$ (`od (ot …)`).
- `gu` 下到第 0 层时是原子: `PreAL` 对原子的 `Lab0ᴸ` (经 `atomL`) 做同样的事.

```agda
ctxw : T → T → T
ctxw w b = ψᵗ w (ΩΩ ∷ b) ∷ []

nf1 : NF₁ (natT 1)
nf1 = γ′-NF 0

lab1 : Lab one⁰ (natT 1)
lab1 = l1 refl (s≅ z≅) (l0 refl z≅)

popL : ∀ {i k ℓ w} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
       LabL₊ i Ll (ψ1 p σ z Ord₊ˢ.zero) (ctxw w [])
popL {w = []} Iw ei ki = ⊥-elim (tf (trans (sym (kdI[] Iw)) (trans (sym (kd-≅ ei)) ki)))
popL {w = x ∷ xs} {p = p} {z = z} Iw ei ki =
  gŝ ki (H1-pen x xs) Iw (⊑ᴵ-≅ʳ ⊑ᴵ-refl (s≅ ei)) (λ θ → subst (Occ (x ∷ xs)) (sym (H1-fsT x xs ΩΩ [] refl θ)) oh)
     (subst (LabL₊ _ Ll _) (sym (H1-fsT x xs ΩΩ [] refl (natT 1)))
            (PsiVL {p = zero} {σ = σ1 (z<suc z p)} Iw ei ki (LabL-Ω one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _))))
     (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (H1-fsT x xs ΩΩ [] refl θ))
            (PsiVL {p = lim 0 zero} {σ = λ q → lim 1 q} Iw ei ki (LabL-Ω Y hY lY nθ (≅ᴵ-refl _))))
```


```agda
giPreL : ∀ {k ℓ i w ν j y ys} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
        (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
        (rec : ∀ η (x : Ordˢ j) → LabL x η → LabL₊ i Ll (ψ1 p σ z (f (intoˢ (<→◃ q) x))) (ctxw w (fsT (y ∷ ys) η))) →
        (recC : kd j ≡ false → ∀ η (x : Ordˢ j) → LabL x η →
                LabL₊ j Ll (ψ1 (σ q) σ z (f (intoˢ (<→◃ q) x))) (ctxw ν (fsT (y ∷ ys) η))) →
        LabL₊ i Ll (ψ1 p σ z (Ord₊ˢ.limᵢ q f)) (ctxw w (y ∷ ys))
giPreL {i = i} {w = w} {ν = ν} {j = j} {y = y} {ys = ys} {p = p} {σ = σ} {z = z} {q = q} {f = f} Iw ei ki c Iν ej rec recC =
  go (cmpᵀ (sucT ν) w) refl
  where
  pen : Pen (cmpᵀ (sucT ν) w) → LabL₊ i Ll (ψ1 p σ z (Ord₊ˢ.limᵢ q f)) (ctxw w (y ∷ ys))
  pen pn with pen1 {p = p} {σ = σ} {z = z} {q = q} {f = f} (≅ᴵ-refl j)
                   (≺ᴵ-respʳ (≺ᴵ-respˡ ej (Ilt Iν Iw (pen→< ν w pn))) (≅ᴵ-sym ei))
  ... | j′ , e , r , eqn =
    subst (λ W → LabL₊ i Ll W (ctxw w (y ∷ ys))) (sym eqn)
          (gi cofE Iν (≅ᴵ-trans (≅ᴵ-sym e) ej)
              (λ η x l → subst (λ v → LabL₊ i Ll (ψ1 p σ z (f (intoˢ (<→◃ q) (tr⁻ˢ e v)))) (fsT (ctxw w (y ∷ ys)) η))
                               (sym (out-intoˢ (<→◃ r) x))
                               (subst (LabL₊ i Ll _) (sym (fsT₊-pen′ w (ΩΩ ∷ y ∷ ys) ν (cof (y ∷ ys)) c pn η))
                                      (rec η (tr⁻ˢ e x) (LabL-tr⁻ e (Ll→ (<→◃ r) l))))))
    where
    cofE : cof (ctxw w (y ∷ ys)) ≡ cΩ ν
    cofE = trans (cong (E.cofA w) c) (cofP pn)
  ne-w : w ≡ [] → ⊥
  ne-w refl = tf (trans (sym (kdI[] Iw)) (trans (sym (kd-≅ ei)) ki))
  fold : cmpᵀ (sucT ν) w ≡ gt → LabL₊ i Ll (ψ1 p σ z (Ord₊ˢ.limᵢ q f)) (ctxw w (y ∷ ys))
  fold em =
    subst (λ W → LabL₊ i Ll W (ctxw w (y ∷ ys))) (sym (fold1 {p = p} {σ = σ} {z = z} {q = q} {f = f} ij))
          (gl (trans (cong (E.cofA w) c) (cong (E.cofψ₊ w ν) em))
              (λ m → subst (LabL₊ i Ll _) (sym (fs-gt w ΩΩ (y ∷ ys) ν c em m)) (rec _ _ (chainL m))))
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
    kj = trans (kd-≅ ej) (kdI′ Iν (gtν em ne-w))
    chainL : ∀ m → LabL (chain1 σ z q f m) (γT (ΩΩ ∷ y ∷ ys) ν m)
    chainL zero    = LabL-Ω (proj₁ Iν) (proj₁ (proj₂ Iν)) (proj₁ (proj₂ (proj₂ Iν))) (proj₂ (proj₂ (proj₂ Iν))) ej
    chainL (suc m) = frL₊ kj (recC kj _ _ (chainL m))
  go : ∀ m → cmpᵀ (sucT ν) w ≡ m → LabL₊ i Ll (ψ1 p σ z (Ord₊ˢ.limᵢ q f)) (ctxw w (y ∷ ys))
  go lt em = pen (inj₁ em)
  go eq em = pen (inj₂ em)
  go gt em = fold em
```


```agda
PreAL : ∀ {ℓ i w} {p : i <ᴵ ℓ} {σ : Simᴵ zero ℓ} {z : zero <ᴵ ℓ} {X : Ordˢ zero} {b} (Iw : Idx w) → i ≅ᴵ lvI Iw →
        kd i ≡ false → Lab0ᴸ X b → LabL₊ i Ll (ψ1 p σ z X) (ctxw w b)
PreAL {b = []} Iw ei ki (lz c) = popL Iw ei ki
PreAL {b = y ∷ ys} Iw ei ki (lz c) = ⊥-elim (cof-ne y ys c)
PreAL {b = []} Iw ei ki (ls () l)
PreAL {w = w} {p = p} {σ = σ} {z = z} {b = y ∷ ys} Iw ei ki (ls c l) =
  gl (cong (E.cofA w) c)
     (λ n → subst (LabL₊ _ Ll _) (sym (fs-rep w ΩΩ (y ∷ ys) c n)) (LRep ki (PreAL {p = p} {σ = σ} {z = z} Iw ei ki l) n))
PreAL {b = []} Iw ei ki (ll () h)
PreAL {w = w} {p = p} {σ = σ} {z = z} {b = y ∷ ys} Iw ei ki (ll c h) =
  gl (cong (E.cofA w) c)
     (λ n → subst (LabL₊ _ Ll _) (sym (fs-ω w ΩΩ (y ∷ ys) c n)) (PreAL {p = p} {σ = σ} {z = z} Iw ei ki (h n)))
PreAL {b = []} Iw ei ki (lŝ₀ () K h₀ hk)
PreAL {w = w} {p = p} {σ = σ} {z = z} {b = y ∷ ys} Iw ei ki (lŝ₀ c K h₀ hk) =
  gĉ (cong (E.cofA w) c) K
     (subst (LabL₊ _ Ll _) (sym (fs-ω w ΩΩ (y ∷ ys) c 0)) (PreAL {p = p} {σ = σ} {z = z} Iw ei ki h₀))
     (λ m → subst (LabL₊ _ Ll _) (sym (fs-ω w ΩΩ (y ∷ ys) c (suc m))) (PreAL {p = p} {σ = σ} {z = z} Iw ei ki (hk m)))
PreAL {b = []} Iw ei ki (lĉ () K h₀ hk)
PreAL {w = w} {p = p} {σ = σ} {z = z} {b = y ∷ ys} Iw ei ki (lĉ c K h₀ hk) =
  gĉ (cong (E.cofA w) c) K
     (subst (LabL₊ _ Ll _) (sym (fs-ω w ΩΩ (y ∷ ys) c 0)) (PreAL {p = p} {σ = σ} {z = z} Iw ei ki h₀))
     (λ m → subst (LabL₊ _ Ll _) (sym (fs-ω w ΩΩ (y ∷ ys) c (suc m))) (PreAL {p = p} {σ = σ} {z = z} Iw ei ki (hk m)))

PreVL : ∀ {k ℓ i w} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {X : Ordˢ k} {b} (Iw : Idx w) → i ≅ᴵ lvI Iw →
        kd i ≡ false → LabL X b → LabL₊ i Ll (ψ1 p σ z X) (ctxw w b)
PreL₊ : ∀ {k ℓ i w} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {X : Ordˢ k} {b} (Iw : Idx w) → i ≅ᴵ lvI Iw →
        kd i ≡ false → LabL₊ k Ll X b → LabL₊ i Ll (ψ1 p σ z X) (ctxw w b)
PreVL {k = zero}    {p = p} {σ = σ} {z = z} Iw ei ki at = PreAL {p = p} {σ = σ} {z = z} Iw ei ki (atomL at)
PreVL {k = suc _}   {p = p} {σ = σ} {z = z} Iw ei ki h  = PreL₊ {p = p} {σ = σ} {z = z} Iw ei ki h
PreVL {k = lim _ _} {p = p} {σ = σ} {z = z} Iw ei ki h  = PreL₊ {p = p} {σ = σ} {z = z} Iw ei ki h

PreL₊ {b = []} Iw ei ki (gz c) = popL Iw ei ki
PreL₊ {b = y ∷ ys} Iw ei ki (gz c) = ⊥-elim (cof-ne y ys c)
PreL₊ {b = []} Iw ei ki (gs () l)
PreL₊ {w = w} {p = p} {σ = σ} {z = z} {b = y ∷ ys} Iw ei ki (gs c l) =
  gl (cong (E.cofA w) c)
     (λ n → subst (LabL₊ _ Ll _) (sym (fs-rep w ΩΩ (y ∷ ys) c n)) (LRep ki (PreL₊ {p = p} {σ = σ} {z = z} Iw ei ki l) n))
PreL₊ {b = []} Iw ei ki (gl () h)
PreL₊ {w = w} {p = p} {σ = σ} {z = z} {b = y ∷ ys} Iw ei ki (gl c h) =
  gl (cong (E.cofA w) c)
     (λ n → subst (LabL₊ _ Ll _) (sym (fs-ω w ΩΩ (y ∷ ys) c n)) (PreL₊ {p = p} {σ = σ} {z = z} Iw ei ki (h n)))
PreL₊ {p = p} {σ = σ} {z = z} Iw ei ki (gu {r = zero} h)   = PreVL {p = p} {σ = λ q → σ (suc q)} {z = z} Iw ei ki h
PreL₊ {p = p} {σ = σ} {z = z} Iw ei ki (gu {r = self n} h) = PreVL {p = p} {σ = λ q → σ (lim n q)} {z = z} Iw ei ki h
PreL₊ {b = []} Iw ei ki (gi () Iν ej h)
PreL₊ {p = p} {σ = σ} {z = z} {b = y ∷ ys} Iw ei ki (gi {q = q} {f = f} c Iν ej h) =
  giPreL {p = p} {σ = σ} {z = z} {q = q} {f = f} Iw ei ki c Iν ej
        (λ η x l → PreL₊ {p = p} {σ = σ} {z = z} Iw ei ki (h η x (→Ll (<→◃ q) l)))
        (λ kj η x l → PreL₊ {p = σ q} {σ = σ} {z = z} Iν ej kj (h η x (→Ll (<→◃ q) l)))
PreL₊ {b = []} Iw ei ki (gĉ () K h₀ hk)
PreL₊ {w = w} {p = p} {σ = σ} {z = z} {b = y ∷ ys} Iw ei ki (gĉ c K h₀ hk) =
  gĉ (cong (E.cofA w) c) K
     (subst (LabL₊ _ Ll _) (sym (fs-ω w ΩΩ (y ∷ ys) c 0)) (PreL₊ {p = p} {σ = σ} {z = z} Iw ei ki h₀))
     (λ m → subst (LabL₊ _ Ll _) (sym (fs-ω w ΩΩ (y ∷ ys) c (suc m))) (PreL₊ {p = p} {σ = σ} {z = z} Iw ei ki (hk m)))
PreL₊ {k = zero} Iw ei ki (gŝ () c Ib bb ob h₀ hg)
PreL₊ {k = suc _} {w = []} Iw ei ki (gŝ kk c Ib bb ob h₀ hg) = ⊥-elim (tf (trans (sym (kdI[] Iw)) (trans (sym (kd-≅ ei)) ki)))
PreL₊ {k = suc _} {w = x ∷ xs} {b = []} Iw ei ki (gŝ kk () Ib bb ob h₀ hg)
PreL₊ {k = suc _} {w = x ∷ xs} {p = p} {σ = σ} {z = z} {b = y ∷ ys} Iw ei ki (gŝ kk c Ib bb ob h₀ hg) =
  gŝ ki (trans (cong (E.cofA (x ∷ xs)) c) (H1-pen x xs)) Ib bb
     (λ θ → subst (Occ _) (sym (H1-fsT x xs ΩΩ (y ∷ ys) c θ)) (od (ot (ob θ))))
     (subst (LabL₊ _ Ll _) (sym (H1-fsT x xs ΩΩ (y ∷ ys) c (natT 1))) (PreL₊ {p = p} {σ = σ} {z = z} Iw ei ki h₀))
     (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (H1-fsT x xs ΩΩ (y ∷ ys) c θ))
                                  (PreL₊ {p = p} {σ = σ} {z = z} Iw ei ki (hg θ Y hY lY nθ lt e)))
PreL₊ {k = lim _ _} {w = []} Iw ei ki (gŝ kk c Ib bb ob h₀ hg) = ⊥-elim (tf (trans (sym (kdI[] Iw)) (trans (sym (kd-≅ ei)) ki)))
PreL₊ {k = lim _ _} {w = x ∷ xs} {b = []} Iw ei ki (gŝ kk () Ib bb ob h₀ hg)
PreL₊ {k = lim _ _} {w = x ∷ xs} {p = p} {σ = σ} {z = z} {b = y ∷ ys} Iw ei ki (gŝ kk c Ib bb ob h₀ hg) =
  gŝ ki (trans (cong (E.cofA (x ∷ xs)) c) (H1-pen x xs)) Ib bb
     (λ θ → subst (Occ _) (sym (H1-fsT x xs ΩΩ (y ∷ ys) c θ)) (od (ot (ob θ))))
     (subst (LabL₊ _ Ll _) (sym (H1-fsT x xs ΩΩ (y ∷ ys) c (natT 1))) (PreL₊ {p = p} {σ = σ} {z = z} Iw ei ki h₀))
     (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (H1-fsT x xs ΩΩ (y ∷ ys) c θ))
                                  (PreL₊ {p = p} {σ = σ} {z = z} Iw ei ki (hg θ Y hY lY nθ lt e)))
```


**读法.** `PreL₊` 与 `PsiL₊` 互不调用对方的递归 (弹栈闭包的分支调用已定义好的 `PsiVL`), 停机一次通过; 两个 oracle 都是对 `gi` 行分支的直接递归调用 (目标 $(i,w)$ 与 $(j,\nu)$), 同 Decouple §8.



## §12 带前缀的 $\psi_0$, 任意层的尾巴: 证书与标签一起

Omega2Base §10 的 `Pre0V`/`Pre0S₊` 的产出式版本. 结构不变 (对尾巴的 `LabL` 推导递归; 节点 0 走链 `liLabᴸ`, 节点非零走 `foldLabᴸ`, 链点由 §11 的 `PreL₊` 标), 区别有三:

1. 结论是 `Σ (Goodᴸ …) (λ G → Lab (forceᴸ _ G) (ctx a))`, 证书在递归里造出; 极限的单调一律由 `limᴸ` (标签).
2. `liLabᴸ` 的链点 $c_{m+1}=\psi^{[\hat\Omega]}_0(f\,c_m)$ (目标证明 `σ q`) 的原子由**递归在另一个目标证明处**给出 (`rec` 对目标证明 `p′` 多态), 不再像 DecoupleBase 的 `liBody` 那样把输出的证书沿 `≅ᶻ` 搬过去.
3. **闭包 (`gŝ` 行) 的支配 `d₀`/`dE`**, 这是 Omega2 §5 的缺口所在. 行里记着闭包的界 $c\sqsubseteq^\mathsf I\mathtt{lvl}\,w+1$ ($w$ 是弹栈时的目标下标, 带 `Idx`) 与 "$w$ 出现在 $t[\theta]$ 里" (`Occ`). 在 $\psi_0$ 前缀下, 第 $m$ 个链点的标签是 $\psi_0(\Omega_\Omega+a[\theta_m])$, 它是可数标准形且含 $w$ 作下标, 所以 SystemOmega 的 `occ<` 给 $w<\psi_0(\Omega_\Omega+a[\theta_m])$, `Lab-oc` 把它变成树的 $\prec$, 于是 $c\sqsubseteq\mathtt{lvl}\,w+1\sqsubseteq$ 链点的层号 (`domᴸ`). 这正是 "逐个闭包、相对带标签的地板" 的支配: 地板 $w$ 来自闭包自己, 链点的标签来自同一个递归. 无标签的计值点不出现: `Goodᴸ` 只在带标签的点处要分支.

```agda
I0 : Idx []
I0 = Ord₊.zero , hz , l0 refl z≅ , n[]

z≺I : ∀ {ν j} → (I : Idx ν) → j ≅ᴵ lvI I → (ν ≡ [] → ⊥) → zero ≺ᴵ j
z≺I {ν = []}    I ej ne = ⊥-elim (ne refl)
z≺I {ν = v ∷ vs} I ej ne = ≺ᴵ-respʳ (Ilt I0 I []<) (≅ᴵ-sym ej)

domᴸ : ∀ {c w b Y} (hY : HS Y) (Iw : Idx w) → c ⊑ᴵ suc (lvI Iw) → Occ w b → Lab Y (ctx b) → NF₁ (ctx b) → c ⊑ᴵ toLevel Y hY
domᴸ hY (W , hW , lW , nW) bw o lY nb =
  ⊑ᴵ-trans bw (s⊑′ (toLevel-≺ hW hY (Lab-oc lY nb lW nW (occ< nb (c∷ c[]) (od (ot o)) (Lab→Ctbl lW nW)))))
```


`liLabᴸ`: 节点层 0, 目标 0 (`fold1` 的 `inj₂ z≅`). 原子 $c_m$ 与输出都由 `rec` 给出.

```agda
liLabᴸ : ∀ {L k} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} {q : zero <ᴵ k} {f : Uˢ zero (<→◃ q) → Ordˢ k} {y ys} →
         cof (y ∷ ys) ≡ cΩ [] → Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → NF₁ (ctx (y ∷ ys)) →
         (rec : ∀ (p′ : zero <ᴵ L) θ (x : Ordˢ zero) → Atomᴸ x θ → f (intoˢ (<→◃ q) x) ≅ˢ f (intoˢ (<→◃ q) x) →
                NF₁ (ctx (fsT (y ∷ ys) θ)) →
                Σ (Goodᴸ (toZ (ψ1 p′ σ z (f (intoˢ (<→◃ q) x))))) λ G → Lab (forceᴸ _ G) (ctx (fsT (y ∷ ys) θ))) →
         Σ (Goodᴸ (toZ (ψ1 p σ z (Ord₊ˢ.limᵢ q f)))) λ G → Lab (forceᴸ _ G) (ctx (y ∷ ys))
liLabᴸ {p = p} {σ = σ} {z = z} {q = q} {f = f} {y = y} {ys = ys} c ex nu rec =
  subst (λ W → Σ (Goodᴸ (toZ W)) λ G → Lab (forceᴸ _ G) (ctx (y ∷ ys))) (sym eqf)
        (limᴸ nu (cong (cofA []) c) (λ m → proj₁ (outp m))
              (λ m → subst (Lab _) (sym (fs-gt [] ΩΩ (y ∷ ys) [] c refl m)) (proj₂ (outp m))))
  where
  eqf = fold1 {p = p} {σ = σ} {z = z} {q = q} {f = f} (inj₂ z≅)
  atm : ∀ m → Atomᴸ (chain1 σ z q f m) (γP (y ∷ ys) m)
  atm zero    = Ωˢ-refl zero , gs gz , l1 refl (s≅ z≅) (l0 refl z≅)
  atm (suc m) = ψ1-≅ {p = σ q} {σ = σ} {p′ = σ q} {σ′ = σ} {z = z} {z′ = z} z≅ (i-respˢ ex (proj₁ (atm m))) ,
                rec (σ q) _ _ (atm m) (i-respˢ ex (proj₁ (atm m))) (nfγ nu c m)
  outp : ∀ m → Σ (Goodᴸ (toZ (ψ1 p σ z (f (intoˢ (<→◃ q) (chain1 σ z q f m)))))) λ G →
              Lab (forceᴸ _ G) (ctx (fsT (y ∷ ys) (γP (y ∷ ys) m)))
  outp m = rec p _ _ (atm m) (i-respˢ ex (proj₁ (atm m))) (nfγ nu c m)
```


`foldLabᴸ`: 节点层 $j\ne0$, 链点在第 $j$ 层, 由 §11 的 `PreL₊` 标 (不需要证书); 输出由 `rec`.

```agda
foldLabᴸ : ∀ {L k j y ys v vs} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
           cof (y ∷ ys) ≡ cΩ (v ∷ vs) → (I : Idx (v ∷ vs)) → j ≅ᴵ lvI I → kd j ≡ false →
           Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → NF₁ (ctx (y ∷ ys)) →
           (h : ∀ η (x : Ordˢ j) → LabL x η → LabL₊ k Ll (f (intoˢ (<→◃ q) x)) (fsT (y ∷ ys) η)) →
           (rec : ∀ η (x : Ordˢ j) → LabL x η → f (intoˢ (<→◃ q) x) ≅ˢ f (intoˢ (<→◃ q) x) →
                  NF₁ (ctx (fsT (y ∷ ys) η)) →
                  Σ (Goodᴸ (toZ (ψ1 p σ z (f (intoˢ (<→◃ q) x))))) λ G → Lab (forceᴸ _ G) (ctx (fsT (y ∷ ys) η))) →
           Σ (Goodᴸ (toZ (ψ1 p σ z (Ord₊ˢ.limᵢ q f)))) λ G → Lab (forceᴸ _ G) (ctx (y ∷ ys))
foldLabᴸ {y = y} {ys = ys} {v = v} {vs = vs} {p = p} {σ = σ} {z = z} {q = q} {f = f} c I ej kj ex nu h rec =
  subst (λ W → Σ (Goodᴸ (toZ W)) λ G → Lab (forceᴸ _ G) (ctx (y ∷ ys))) (sym eqf)
        (limᴸ nu (cong (cofA []) c) (λ m → proj₁ (outp m))
              (λ m → subst (Lab _) (sym (fs-gt [] ΩΩ (y ∷ ys) (v ∷ vs) c refl m)) (proj₂ (outp m))))
  where
  eqf = fold1 {p = p} {σ = σ} {z = z} {q = q} {f = f} (inj₁ (z≺I I ej (λ ())))
  chainL : ∀ m → LabL (chain1 σ z q f m) (γT (ΩΩ ∷ y ∷ ys) (v ∷ vs) m)
  chainL zero    = LabL-Ω (proj₁ I) (proj₁ (proj₂ I)) (proj₁ (proj₂ (proj₂ I))) (proj₂ (proj₂ (proj₂ I))) ej
  chainL (suc m) = frL₊ kj (PreL₊ {p = σ q} {σ = σ} {z = z} I ej kj (h _ _ (chainL m)))
  nf : ∀ m → NF₁ (ctx (fsT (y ∷ ys) (γT (ΩΩ ∷ y ∷ ys) (v ∷ vs) m)))
  nf m = subst NF₁ (fs-gt [] ΩΩ (y ∷ ys) (v ∷ vs) c refl m) (NF₁-fsn nu (cong (cofA []) c) m)
  outp : ∀ m → Σ (Goodᴸ (toZ (ψ1 p σ z (f (intoˢ (<→◃ q) (chain1 σ z q f m)))))) λ G →
              Lab (forceᴸ _ G) (ctx (fsT (y ∷ ys) (γT (ΩΩ ∷ y ∷ ys) (v ∷ vs) m)))
  outp m = rec _ _ (chainL m) (i-respˢ ex (chain1-≅ ex m)) (nf m)
```


`ŝChainᴸ`: 非零层闭包 $\hat s\,c\,t_0\,g$ 在 $\psi_0$ 前缀下成为第 0 层的待计值链 (输出就是链). 证书 `gc` 的标签序列 $\gamma_m=\gamma^P_{a,m+1}=\psi_0(\Omega_\Omega+a[\gamma^P_{a,m}])$; `Gg`/`lE` 都取自同一个递归调用 `rec` (第一、第二分量), `d₀`/`dE` 由 `domᴸ`, 输出 = 链点, 单调由 `ĉᴸ-mk`.

```agda
ŝChainᴸ : ∀ {L k c w} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} {y ys} →
          cof (y ∷ ys) ≡ cΩ [] → NF₁ (ctx (y ∷ ys)) → (Iw : Idx w) → c ⊑ᴵ suc (lvI Iw) → (∀ θ → Occ w (fsT (y ∷ ys) θ)) →
          (rec₀ : Σ (Goodᴸ (toZ (ψ1 p σ z t₀))) λ G → Lab (forceᴸ _ G) (γP (y ∷ ys) 1)) →
          (rec : ∀ m Y (hY : HS Y) → Lab Y (γP (y ∷ ys) (suc m)) → (e : c ⊑ᴵ toLevel Y hY) →
                 Σ (Goodᴸ (toZ (ψ1 p σ z (g (toLevel Y hY) e)))) λ G → Lab (forceᴸ _ G) (γP (y ∷ ys) (suc (suc m)))) →
          Σ (Goodᴸ (ĉᴸ c (toZ (ψ1 p σ z t₀)) (λ η e → toZ (ψ1 p σ z (g η e)))
                         (toZ (ψ1 p σ z t₀)) (λ η e → toZ (ψ1 p σ z (g η e))))) λ G → Lab (forceᴸ _ G) (ctx (y ∷ ys))
ŝChainᴸ {y = y} {ys = ys} c nu Iw bw ow rec₀ rec =
  ĉᴸ-mk nu (cong (cofA []) c) K (proj₁ rec₀) (subst (Lab _) (sym (fs-gt [] ΩΩ (y ∷ ys) [] c refl 0)) (proj₂ rec₀))
        (λ k → CCᴸ.Gg K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k)))
        (λ k → subst (Lab _) (sym (fs-gt [] ΩΩ (y ∷ ys) [] c refl (suc k)))
                     (CCᴸ.lE K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k))))
  where
  K = ccᴸ (λ m → γP (y ∷ ys) (suc m)) (proj₁ rec₀) (proj₂ rec₀)
          (domᴸ _ Iw bw (ow (natT 1)) (proj₂ rec₀) (nfγ nu c 0))
          (λ m Y hY lY e → proj₁ (rec m Y hY lY e)) (λ m Y hY lY e → proj₂ (rec m Y hY lY e))
          (λ m Y hY lY e → domᴸ _ Iw bw (ow (γP (y ∷ ys) (suc m))) (proj₂ (rec m Y hY lY e)) (nfγ nu c (suc m)))
```


**`Pre0Vᴸ`/`Pre0L₊ᴸ`.** 递归调用一律作为 λ 参数传入 (DecoupleBase §4 的写法).

```agda
Pre0Vᴸ  : ∀ {L k} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} {x : Ordˢ k} {a} →
          LabL x a → x ≅ˢ x → NF₁ (ctx a) → Σ (Goodᴸ (toZ (ψ1 p σ z x))) λ G → Lab (forceᴸ _ G) (ctx a)
Pre0L₊ᴸ : ∀ {L k} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} {x : Ordˢ k} {a} →
          LabL₊ k Ll x a → x ≅ˢ x → NF₁ (ctx a) → Σ (Goodᴸ (toZ (ψ1 p σ z x))) λ G → Lab (forceᴸ _ G) (ctx a)
Pre0Vᴸ {k = zero}    {p = p} {σ = σ} {z = z} at ex nu = Pre0ᴸ {p = p} {σ = σ} {z = z} (atomL at) ex nu
Pre0Vᴸ {k = suc _}   {p = p} {σ = σ} {z = z} h  ex nu = Pre0L₊ᴸ {p = p} {σ = σ} {z = z} h ex nu
Pre0Vᴸ {k = lim _ _} {p = p} {σ = σ} {z = z} h  ex nu = Pre0L₊ᴸ {p = p} {σ = σ} {z = z} h ex nu

Pre0L₊ᴸ {p = p} {σ = σ} {z = z} {a = []} (gz c) ex nu = pop0ᴸ p σ z
Pre0L₊ᴸ {a = y ∷ ys} (gz c) ex nu = ⊥-elim (cof-ne y ys c)
Pre0L₊ᴸ {a = []} (gs () l) ex nu
Pre0L₊ᴸ {p = p} {σ = σ} {z = z} {a = y ∷ ys} (gs c l) ex nu =
  limᴸ nu (cong (cofA []) c) (λ n → proj₁ (Rs n)) (λ n → subst (Lab _) (sym (fs-rep [] ΩΩ (y ∷ ys) c n)) (proj₂ (Rs n)))
  where
  Rp = Pre0L₊ᴸ {p = p} {σ = σ} {z = z} l (s-invˢ ex) (subst NF₁ (fs-rep [] ΩΩ (y ∷ ys) c 1) (NF₁-fsn nu (cong (cofA []) c) 1))
  Rs = repᴸ (proj₁ Rp) (proj₂ Rp) (λ n → subst NF₁ (fs-rep [] ΩΩ (y ∷ ys) c n) (NF₁-fsn nu (cong (cofA []) c) n))
Pre0L₊ᴸ {a = []} (gl () h) ex nu
Pre0L₊ᴸ {p = p} {σ = σ} {z = z} {a = y ∷ ys} (gl c h) ex nu =
  limᴸ nu (cong (cofA []) c) (λ n → proj₁ (Pre0L₊ᴸ {p = p} {σ = σ} {z = z} (h n) (l-invˢ ex n) (nfω nu c n)))
       (λ n → subst (Lab _) (sym (fs-ω [] ΩΩ (y ∷ ys) c n)) (proj₂ (Pre0L₊ᴸ {p = p} {σ = σ} {z = z} (h n) (l-invˢ ex n) (nfω nu c n))))
Pre0L₊ᴸ {p = p} {σ = σ} {z = z} (gu {r = zero} l) ex nu =
  Pre0Vᴸ {p = p} {σ = λ q → σ (suc q)} {z = z} l (u-reflˢ zero ex) nu
Pre0L₊ᴸ {p = p} {σ = σ} {z = z} (gu {r = self n} l) ex nu =
  Pre0Vᴸ {p = p} {σ = λ q → σ (lim n q)} {z = z} l (u-reflˢ (self n) ex) nu
Pre0L₊ᴸ {a = []} (gi () I ej h) ex nu
Pre0L₊ᴸ {p = p} {σ = σ} {z = z} {a = y ∷ ys} (gi {j = zero} {q = q} {f = f} c I ej h) ex nu =
  liLabᴸ {p = p} {σ = σ} {z = z} {q = q} {f = f} (trans c (cong cΩ (kdI I (sym (kd-≅ ej))))) ex nu
         (λ p′ θ x at br nf → Pre0L₊ᴸ {p = p′} {σ = σ} {z = z} (h θ x (→Ll (<→◃ q) at)) br nf)
Pre0L₊ᴸ {a = y ∷ ys} (gi {ν = []} {j = suc _} c I ej h) ex nu = ⊥-elim (tf (trans (sym (kdI[] I)) (sym (kd-≅ ej))))
Pre0L₊ᴸ {p = p} {σ = σ} {z = z} {a = y ∷ ys} (gi {ν = v ∷ vs} {j = suc _} {q = q} {f = f} c I ej h) ex nu =
  foldLabᴸ {p = p} {σ = σ} {z = z} {q = q} {f = f} c I ej refl ex nu (λ η x l → h η x (→Ll (<→◃ q) l))
           (λ η x l br nf → Pre0L₊ᴸ {p = p} {σ = σ} {z = z} (h η x (→Ll (<→◃ q) l)) br nf)
Pre0L₊ᴸ {a = y ∷ ys} (gi {ν = []} {j = lim _ _} c I ej h) ex nu = ⊥-elim (tf (trans (sym (kdI[] I)) (sym (kd-≅ ej))))
Pre0L₊ᴸ {p = p} {σ = σ} {z = z} {a = y ∷ ys} (gi {ν = v ∷ vs} {j = lim _ _} {q = q} {f = f} c I ej h) ex nu =
  foldLabᴸ {p = p} {σ = σ} {z = z} {q = q} {f = f} c I ej refl ex nu (λ η x l → h η x (→Ll (<→◃ q) l))
           (λ η x l br nf → Pre0L₊ᴸ {p = p} {σ = σ} {z = z} (h η x (→Ll (<→◃ q) l)) br nf)
Pre0L₊ᴸ {k = zero} (gŝ () c Iw bw ow h₀ hg) ex nu
Pre0L₊ᴸ {k = suc _} {a = []} (gŝ kk () Iw bw ow h₀ hg) ex nu
Pre0L₊ᴸ {k = suc _} {p = p} {σ = σ} {z = z} {a = y ∷ ys} (gŝ kk c Iw bw ow h₀ hg) ex nu =
  ŝChainᴸ {p = p} {σ = σ} {z = z} c nu Iw bw ow (Pre0L₊ᴸ {p = p} {σ = σ} {z = z} h₀ (ŝ-refl₀ ex) (nfγ nu c 0))
          (λ m Y hY lY e → Pre0L₊ᴸ {p = p} {σ = σ} {z = z} (hg _ Y hY lY (nfγ nu c m) (1<ctx _) e)
                                   (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) (nfγ nu c (suc m)))
Pre0L₊ᴸ {k = lim _ _} {a = []} (gŝ kk () Iw bw ow h₀ hg) ex nu
Pre0L₊ᴸ {k = lim _ _} {p = p} {σ = σ} {z = z} {a = y ∷ ys} (gŝ kk c Iw bw ow h₀ hg) ex nu =
  ŝChainᴸ {p = p} {σ = σ} {z = z} c nu Iw bw ow (Pre0L₊ᴸ {p = p} {σ = σ} {z = z} h₀ (ŝ-refl₀ ex) (nfγ nu c 0))
          (λ m Y hY lY e → Pre0L₊ᴸ {p = p} {σ = σ} {z = z} (hg _ Y hY lY (nfγ nu c m) (1<ctx _) e)
                                   (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) (nfγ nu c (suc m)))
Pre0L₊ᴸ {a = []} (gĉ () K h₀ hk) ex nu
Pre0L₊ᴸ {p = p} {σ = σ} {z = z} {a = y ∷ ys} (gĉ c K h₀ hk) ex nu =
  ĉᴸ-mk nu (cong (cofA []) c) K (proj₁ R₀) (subst (Lab _) (sym (fs-ω [] ΩΩ (y ∷ ys) c 0)) (proj₂ R₀))
        (λ k → proj₁ (Rk k)) (λ k → subst (Lab _) (sym (fs-ω [] ΩΩ (y ∷ ys) c (suc k))) (proj₂ (Rk k)))
  where
  R₀ = Pre0L₊ᴸ {p = p} {σ = σ} {z = z} h₀ (ĉ-refl₀ ex) (nfω nu c 0)
  Rk = λ k → Pre0L₊ᴸ {p = p} {σ = σ} {z = z} (hk k) (ĉ-reflg ex _ _) (nfω nu c (suc k))
```


**读法.** `Pre0L₊ᴸ` 的每个子句都是 Omega2Base 的 `Pre0S₊` 的同一子句, 只是把 "拆开给定的证书 $G$" 换成 "用递归结果的第一分量拼出证书": `gs`/`gl` 用 `limᴸ`, `gŝ` 用 `ŝChainᴸ`, `gĉ` 用 `ĉᴸ-mk` 并沿用行里的链证书. 停机一次通过: 递归调用都作用在 `LabL₊` 推导的模式子项上 (`h θ x …`、`hg _ Y …`、`h₀`、`hk k`), 链点处的调用经 λ 参数传入 `liLabᴸ`/`foldLabᴸ`/`ŝChainᴸ`.

## §13 结论与边界

**字面成立 (`refl` / 定义性):** `forceᴸ` 在 `gc` 处是 `lim (outsᴸ …)`; `ptK K` 与 `gc` 类型里的链点定义性相同 (`ĉᴸ-mk`、`atomL`、`ŝChainᴸ` 的类型检查); `ψ1 p σ z zero` 是弹栈闭包 (`pop0ᴸ` 的类型检查); `fsn (x ∷ y ∷ ys) n ≡ x ∷ fsn (y ∷ ys) n` 等 (`fs-mono₁`、`addᴸ`).

**定理 (标签按 Correspond 的 `Lab`, 模 $\cong$):**

1. `Goodᴸ`/`forceᴸ`/`forceᴸ-HS`; `CCᴸ`/`ptK`; `pts-≅`, `forceᴸ-≅`, `Goodᴸ-tr`.
2. **`fs-mono₁`**, `mono-lab`, `one⊑lab`; **`Lab→Ctbl`**, `Idx-Ctbl`.
3. `plainᴸ`/`force~ᴸ`/`emptyᴸ`/`emptyᴸ≅`; **`pop0ᴸ`** ($\psi^{[\hat\Omega]}_0(0)$ 的证书与标签 $\psi_0(\Omega_\Omega)$, 任意环境层号).
4. `limᴸ`, `ĉᴸ-mk`, `Atomᴸ`, `Atomᴸ-≅`, `Lab0ᴸ`, `atomL`, `addᴸ`, `repᴸ`, **`Pre0ᴸ`**.
5. `LabL` 全套 (搬运, `LabL-Ω`, `LSum₊`/`LRep`, `giPsiL`, `PsiAL`/`PsiVL`/`PsiL₊`, `popL`, `giPreL`, `PreAL`/`PreVL`/`PreL₊`).
6. `domᴸ`, `liLabᴸ`, `foldLabᴸ`, `ŝChainᴸ`, **`Pre0Vᴸ`/`Pre0L₊ᴸ`**: 对尾巴的 `LabL` 推导, $\psi^{[\hat\Omega]}_0$ 的计值树的 `Goodᴸ` 证书与标签 `ctx a` 一起存在 (任意环境层号、`Sim`、帧证据).

**边界.**

- `Goodᴸ` 不是 "纯好性": 证书本身带链点的标签, 所以有证书的树都已在标签理论里. 这正是路线 (a) 的代价与要点: 证书与标签不再分开证明. 旧的 `Goodᶻ` 证书 (以及由它算出的树) 与新证书不直接互换 (`Goodᶻ → Goodᴸ` 要给链点造标签), 只在标签层面对上 (GoodL 的 `agree-*`).
- `Lab0ᴸ`/`LabL` 的待计值链行携带**一个**链证书, 不再对一切链证书量化; `atomL` 读原子自带的证书, 所以不需要 DecoupleBase 的 `chain≅` 对齐.
- 地板字段只为 "弹栈闭包被 $\psi_0$ 前缀折成链" 设计, 用到 `occ<` (可数下标、可数链点). 不可数地板 ($\psi_\Omega$ 帧) 不在本文范围 (GoodL §5).
- 工程注记: (i) `pts-≅` 写成顶层函数、隐式参数在递归调用里不写时报 `[UnsolvedConstraints] … _546 (m = x) = γ x : List PT (blocked on _546) …` (递归调用的 `γ`/`l₀` 推不出), 改成带隐式参数的匿名模块即过 (模块参数在递归里自动传递). (ii) 局部名 `R`、`out` 与 Level 的 `R`/`out` 冲突 (`[ClashingDefinition] Multiple definitions of R`), 改名 `Rb`/`Rp`/`outp`. (iii) `gc` 的类型里用 `let P = ptsᴸ … in` 一次通过, 正性检查不受影响.
