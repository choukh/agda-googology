> **机械克隆.** 由 `Omega2Base` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# $\psi_0(\Omega_\Omega\cdot2)$ 之前: 参数化的界与任意目标层的带前缀标签

> 接 [Decouple](Decouple.lagda.md) §11 的三条障碍. 本文是 [Omega2](Omega2.lagda.md) 的前半 (步骤 1–2): (1) 把 UniformS/Stage2Label 的证书理论里写死的界 $2$ 参数化; (2) 把 DecoupleBase/Decouple 的关系式标签推广到带标签的目标层 $\delta\ge2$. 步骤 3 (沿 $t_2$ 的链的良基序列与 `Lab T2 t2`) 在 Omega2.
>
> 结论先说:
>
> 1. **参数化的界 (§1–§3).** UniformS §8–§10 与 Stage2Label §3–§5 整份复制进模块 `Bound β`, 唯一的定义改动是非零层闭包的支配 `Dom (suc _) c … = c ⊑ᴵ β` (原为 `two`). 闭包定理 `Bound.Good-ψ0` 原样, **`Bound.Clos.Good-ψ1 : ℓ ⊑ᴵ β → Good x → x ≅ˢ x → Good (ψ1 p σ z x)`**; 原证明里的 `Strict₁` ($\psi^{[\hat\Omega]}_0$ 的输出 $\sqsupseteq2$) 换成模块参数 `Sβ : Strictᵝ` (单 $\hat\Omega$ 栈、目标 0、任意尾巴、任意证书, 输出层号 $\sqsupseteq\beta$). 前提 $\ell\sqsubseteq\beta$ 只在弹栈的支配 `popDom` 用, `Sβ` 只在非零层闭包被折叠到第 0 层的 `Dom-ψ1` 用.
> 2. **`Strictᵝ` 的确切范围 (§4).** 对一切有限 $n$ 成立 (`StrictN`), 对 $\beta=\mathtt{lvl}\,\mathrm{BTBO}$ 成立 (`Strict-BTBO`), **对 $\beta=\mathtt{lvl}\,\mathrm{BTBO}+1$ 为假 (`Sβ-fails⁺`, 已编译)**: 尾巴 $0$ 的输出 $\cong$ BTBO. 推论 `Sβ-fails`: $\beta=\mathtt{lvl}\,\gamma'_1$ ($t_2$ 的第 0 个链点的层号; $\gamma'_2$ 的环境层号 $\sqsupseteq$ 它) 为假; Omega2 的 `no-Bound` 把它推到 $\gamma'_2$ 的环境层号之上的一切 $\beta$. 一个全局的界恰好走到 $\mathtt{lvl}\,\mathrm{BTBO}$ 为止.
> 3. **检验 `GX₃` (§5).** $X_3=\psi_0(\Omega_\Omega+\Omega_3)$ (环境层号 3) 的证书 **`GX₃ : Goodᶻ (toZ X₃ˢ)`** 与计值树 `X₃ᶠ`, 由 `Bound three` 与 `StrictN 3`. 这正是 Decouple §11 的障碍 (1): 界为 3 的闭包现在有证书.
> 4. **任意带标签目标层的标签 (§6–§10).** Decouple 的 `LabG` 加一行 `gŝ` (非零层闭包, 同 DecoupleBase `Lab₁` 的 `lŝ`) 成为 `LabS`. 第 $j$ 层的分支对一切带 `LabS` 的输入匹配, 输入可以含闭包; 这对 $\delta\ge2$ 是必须的 (§6 的读法). 三个上下文引理: 不带前缀的 `PsiS₊` (`PsiG₊` 加 `gŝ` 逐点), **带前缀、目标 $w\ne0$ 的 `PreS₊`** (`Pre1` 推广到任意带 `Idx` 的目标; 弹栈闭包 `popS`, 派发 `giPre` 由两个 `Idx` 决定, 折叠的链点由递归在节点层给标签), **带前缀、目标 0 的 `Pre0V`/`Pre0S₊`** (`Pre0` 推广到任意层的尾巴: 节点 0 走 DecoupleBase 的 `liLab`, 节点非零走新的 `foldLab`, 链点由 `PreS₊` 标).
> 5. **检验 `X₃-label : Lab X₃ᶠ X₃ᵗ` (§11)**, 树是 §5 的计值树, 记号是 Symbolic 的 `X₃ᵗ`. 这是 Decouple §11 的障碍 (2).
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件 (UniformS/Stage2Label/Decouple 的被改动部分以新名字复制在本文).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderZOmega2Base where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Vec using (Vec; []; _∷_)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Ctx; Pt; pt; lvP; Γᶜ; Mlev; σ1; X₃ᵗ)
open import OCF.Align.ScafLadderZPrefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Restrˢ; trˢ; tr⁻ˢ; resˢ; res⁻ˢ;
  Ωˢ; addˢ; _+ˢ_; fΩ̂; ψᴾ; outs; Goodᶻ; force; force-HS; H₊; z<suc; z2; z1; H1-pen; H1-fsT)
open Restrˢ
import OCF.Align.NoCumsum as N
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; γT; sucT; cmpᵀ; Cmp; lt; eq; gt;
              []<; hd<; tl<; lv<; ar<) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fs-rep; fs-ω; fsT-c1)
open import OCF.Align.Bachmann using (fs-gt; pen→<; gt→≤; gt→<; clash)
open import OCF.Align.Closure using (Pen; fsT₊-pen′)
open import OCF.Align.Standard using () renaming (d₀ to d₀ᴰ)
open import OCF.Align.ScafLadderZStandardOmega using (NF₁; NFᴾ₁; n[]; n∷; nψ; NF₁-pred; NF₁-fsn; γ′-NF; diag₁-desc-NF; walkD)
open import OCF.Align.Stage2 using (Lab-uniq; ctx)
open import OCF.Align.ScafLadderZUniformS hiding (Dom; Good₊; Gd; Good; Gd→Good; Good→Gd; Gd-conv; Good→Goodᶻ;
  Dom0-≅; Dom-tr; Dom-tr⁻; Good-tr; Good-tr⁻; Good-back; Good-back⁻; Good-Ω; Good-add; Good-iter;
  bz; bs; bl; bi; bu; bŝ; bĉ)
import OCF.Align.ScafLadderZUniformS as US
open import OCF.Align.ScafLadderZStage2Label using (Pl; Ok; Ok-Pl; Ok-suc; Ok-lim; Ok-up; Ok-col; Ok-pen; ~ŝ; ~ĉ; Pl-Ω;
  chain0; chain1; chain0-≅; chain1-≅; chain0-step; chain1-step; Ω⊑pop; Strict₀; t₀pop; gpop;
  one⁰; three; z3; X₃ˢ; pop0≅; pop0-label; χ1ˢ; BTBO≺χ1ˢ; σ00; Lab-oc)
import OCF.Align.ScafLadderZStage2Label as S2L
open import OCF.Align.ScafLadderZDecoupleBase using (CC; cc; toC; lvK; dxK; Atom; Lab₁; lz; ls; ll; lu; li; lŝ; lŝ₀; lĉ;
  atomL; fold1; pen1; ΩΩ; γP; force-subst; nfγ; nfω; liLab; ŝOut; pOut; Lab-repᶻ; Pre0; ŝ-reflg)
open import OCF.Align.ScafLadderZDecouple using (Idx; lvI; Ilt; Ieq; Lab0[]; kdI; kdI′; gtν; kdI[]; cofP; Atom-≅; fold0; pen0)
```


## §1 参数化的界: `Bound β` 里的遗传好树

UniformS 的 `Good` 有两种支配: 第 0 层的闭包 (将被 `toZ` 读成链) 对一切证书要 "$c\sqsubseteq^\mathsf I$ 链点的层号"; 非零层的闭包还不是链, 只记 $c\sqsubseteq^\mathsf I2$, 到第 0 层时由 `Strict₁` 补出链点的支配. 界 $2$ 写死在 `Dom` 的两行里. 这里把整份定义放进以 $\beta$ 为参数的模块, 只改这两行; 其余 (`Good₊` 的七个构造子、`Gd`、`Good→Goodᶻ`) 逐字. 这些名字与 UniformS 的同名, 所以导入 UniformS 时把它们 `hiding`, UniformS 自己的版本以 `US.` 前缀使用.

```agda
module Bound (β : Ordᴵ) where
  Dom : (ℓ c : Ordᴵ) → Ordˢ ℓ → ((η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ) → Set
  Dom zero      c t₀ g = (∀ G → c ⊑ᴵ toLevel (force (toZ t₀) G) (force-HS _ G)) ×
                         (∀ η e G → c ⊑ᴵ toLevel (force (toZ (g η e)) G) (force-HS _ G))
  Dom (suc _)   c t₀ g = c ⊑ᴵ β
  Dom (lim _ _) c t₀ g = c ⊑ᴵ β

  module _ (ℓ : Ordᴵ) (G< : (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → Set) where
    data Good₊ : Ordˢ ℓ → Set where
      bz : Good₊ Ord₊ˢ.zero
      bs : ∀ {a} → Good₊ a → Good₊ (Ord₊ˢ.suc a)
      bl : ∀ {h : ℕ → Ordˢ ℓ} → (∀ n → Good₊ (h n)) → (∀ n → h n ⊑ᵒ h (suc n)) → Good₊ (Ord₊ˢ.lim h)
      bi : ∀ {j} {p : j <ᴵ ℓ} {f : Uˢ j (<→◃ p) → Ordˢ ℓ} →
           (∀ (z : Ordˢ j) → z ≅ˢ z → G< j (<→◃ p) (intoˢ (<→◃ p) z) → Good₊ (f (intoˢ (<→◃ p) z))) →
           (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ p) z) ⊑ᵒ f (intoˢ (<→◃ p) z′)) →
           Good₊ (Ord₊ˢ.limᵢ p f)
      bu : ∀ {k} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} → G< k (◃₁→◃ r) x → Good₊ (Ord₊ˢ.up r x)
      bŝ : ∀ {c} {t₀ : Ordˢ ℓ} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} →
           Good₊ t₀ → (∀ η e → Good₊ (g η e)) →
           t₀ ≅ˢ t₀ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ˢ g η′ e′) →
           (∀ η e → t₀ ⊑ᵒ g η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → g η e ⊑ᵒ g η′ e′) →
           Dom ℓ c t₀ g → Good₊ (Ord₊ˢ.ŝ c t₀ g)
      bĉ : ∀ {c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {o₀ : Ordˢ ℓ} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ}
           (G₀ : Goodᶻ t₀) (Gg : ∀ η e → Goodᶻ (g η e)) →
           c ⊑ᴵ toLevel (force t₀ G₀) (force-HS t₀ G₀) →
           (∀ η e → c ⊑ᴵ toLevel (force (g η e) (Gg η e)) (force-HS (g η e) (Gg η e))) →
           (∀ η e → force t₀ G₀ ⊑⁰ force (g η e) (Gg η e)) →
           (∀ η e η′ e′ → η ⊑ᴵ η′ → force (g η e) (Gg η e) ⊑⁰ force (g η′ e′) (Gg η′ e′)) →
           Good₊ o₀ → (∀ η e → Good₊ (o η e)) →
           (∀ η e → o₀ ⊑ᵒ o η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → o η e ⊑ᵒ o η′ e′) →
           Good₊ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o)

  Gd : ∀ {ℓ} (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → Set
  Gd i zero         x = Good₊ i Gd x
  Gd i (suc r)      x = Gd i r x
  Gd _ (self {f} n) x = Good₊ (f n) Gd x
  Gd i (lim n r)    x = Gd i r x

  Good : ∀ {ℓ} → Ordˢ ℓ → Set
  Good {ℓ} = Good₊ ℓ Gd

  Gd→Good : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordˢ i} → Gd i r (intoˢ r x) → Good x
  Gd→Good zero      g = g
  Gd→Good (suc r)   g = Gd→Good r g
  Gd→Good (self n)  g = g
  Gd→Good (lim n r) g = Gd→Good r g

  Good→Gd : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordˢ i} → Good x → Gd i r (intoˢ r x)
  Good→Gd zero      g = g
  Good→Gd (suc r)   g = Good→Gd r g
  Good→Gd (self n)  g = g
  Good→Gd (lim n r) g = Good→Gd r g

  Gd-conv : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) (r′ : i ◃ ℓ′) {x : Ordˢ i} → Gd i r (intoˢ r x) → Gd i r′ (intoˢ r′ x)
  Gd-conv r r′ g = Good→Gd r′ (Gd→Good r g)

  Good→Goodᶻ : ∀ {x : Ordˢ zero} → Good x → Goodᶻ (toZ x)
  Good→Goodᶻ bz         = Goodᶻ.gz
  Good→Goodᶻ (bs g)     = Goodᶻ.gs (Good→Goodᶻ g)
  Good→Goodᶻ (bl hg st) = Goodᶻ.gl (λ n → Good→Goodᶻ (hg n)) (λ n → st n idO (Good→Goodᶻ (hg n)) (Good→Goodᶻ (hg (suc n))))
  Good→Goodᶻ (bi {p = ()} hb hm)
  Good→Goodᶻ (bu {r = ()} g)
  Good→Goodᶻ (bŝ g₀ gg et eg m mm (d₀ , dE)) =
    Goodᶻ.gc G₀ Gg (d₀ G₀) (λ η e → dE η e (Gg η e))
             (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
             G₀ Gg (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
    where
    G₀ = Good→Goodᶻ g₀
    Gg = λ η e → Good→Goodᶻ (gg η e)
  Good→Goodᶻ (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
    Goodᶻ.gc G₀ Gg d₀ dE m₀ mE (Good→Goodᶻ go) (λ η e → Good→Goodᶻ (gO η e))
             (λ η e → mo η e idO (Good→Goodᶻ go) (Good→Goodᶻ (gO η e)))
             (λ η e η′ e′ h → mO η e η′ e′ h idO (Good→Goodᶻ (gO η e)) (Good→Goodᶻ (gO η′ e′)))
```


**读法.** 第 0 层的 `Dom` 与 UniformS 逐字相同, 所以 Stage2Label 的 `popDom₀` (目标 0 的弹栈闭包, 界 1, 由 `Strict₀`) 的类型在两边定义性地相同, 可以直接用. 非零层只记 "$c\sqsubseteq^\mathsf I\beta$", 一个与树无关的数据.

## §2 搬运、$\Omega$ 与加法

UniformS §9–§10 逐字 (`Dom-tr`/`Dom-tr⁻` 在非零层原样传递 $c\sqsubseteq^\mathsf I\beta$). 不依赖 `Good` 的引理 (`back-mono`、`self-back`、`Lv`、`rule4ᵒ` 等) 不复制, 直接用 UniformS 的; 照抄进来报 `[ClashingDefinition] Multiple definitions of back-mono`.

```agda
  Dom0-≅ : ∀ {c} {t₀ t₀′ : Ordˢ zero} {g g′ : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ zero} →
           Good t₀ → (∀ η d → Good (g η d)) → t₀′ ≅ˢ t₀ → (∀ η d → g′ η d ≅ˢ g η d) →
           Dom zero c t₀ g → Dom zero c t₀′ g′
  Dom0-≅ g0 gg et eg (d₀ , dE) =
    (λ G → ⊑ᴵ-≅ʳ (d₀ (Good→Goodᶻ g0)) (toLevel-≅ (force-HS _ (Good→Goodᶻ g0)) (force-HS _ G)
              (force-≅ (toZ-≅ (≅ˢ-sym et)) (Good→Goodᶻ g0) G))) ,
    (λ η d G → ⊑ᴵ-≅ʳ (dE η d (Good→Goodᶻ (gg η d))) (toLevel-≅ (force-HS _ (Good→Goodᶻ (gg η d))) (force-HS _ G)
              (force-≅ (toZ-≅ (≅ˢ-sym (eg η d))) (Good→Goodᶻ (gg η d)) G)))

  Dom-tr : ∀ {a b c} (e : a ≅ᴵ b) {t₀ : Ordˢ a} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ a} →
           Good t₀ → (∀ η d → Good (g η d)) → t₀ ≅ˢ t₀ → (∀ η d → g η d ≅ˢ g η d) →
           Dom a c t₀ g → Dom b c (trˢ e t₀) (λ η d → trˢ e (g η d))
  Dom-tr z≅     g0 gg et eg h = Dom0-≅ g0 gg (trˢ-≅ z≅ et) (λ η d → trˢ-≅ z≅ (eg η d)) h
  Dom-tr (s≅ _) g0 gg et eg h = h
  Dom-tr (l≅ _) g0 gg et eg h = h

  Dom-tr⁻ : ∀ {a b c} (e : a ≅ᴵ b) {t₀ : Ordˢ b} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ b} →
            Good t₀ → (∀ η d → Good (g η d)) → t₀ ≅ˢ t₀ → (∀ η d → g η d ≅ˢ g η d) →
            Dom b c t₀ g → Dom a c (tr⁻ˢ e t₀) (λ η d → tr⁻ˢ e (g η d))
  Dom-tr⁻ z≅     g0 gg et eg h = Dom0-≅ g0 gg (tr⁻ˢ-≅ z≅ et) (λ η d → tr⁻ˢ-≅ z≅ (eg η d)) h
  Dom-tr⁻ (s≅ _) g0 gg et eg h = h
  Dom-tr⁻ (l≅ _) g0 gg et eg h = h

  Good-tr    : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ a} → Good x → Good (trˢ e x)
  Good-tr⁻   : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ b} → Good x → Good (tr⁻ˢ e x)
  Good-back  : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} → Good u → Good (backˢ (resˢ q e) u)
  Good-back⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} → Good u → Good (backˢ (res⁻ˢ q e) u)

  Good-tr e bz         = bz
  Good-tr e (bs g)     = bs (Good-tr e g)
  Good-tr e (bl hg st) = bl (λ n → Good-tr e (hg n)) (λ n → tr-cong (st n))
  Good-tr e (bi {p = q} {f = f} hb hm) = bi
    (λ z ez g → subst (λ w → Good (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w))))) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z))
                      (Good-tr e (hb (backˢ (resˢ q e) z) (self-back q e ez)
                                     (Good→Gd (<→◃ q) (Good-back q e (Gd→Good (<→◃ (ltˢ (resˢ q e))) g))))))
    (λ {z} {z′} h → subst₂ (λ w w′ → trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w))) ⊑ᵒ trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w′))))
                           (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z)) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z′))
                           (tr-cong (hm (back-mono q e h))))
  Good-tr (s≅ e) (bu {r = zero} g)   = bu (Good-tr e g)
  Good-tr (l≅ f) (bu {r = self n} g) = bu (Good-tr (f n) g)
  Good-tr e (bŝ g0 gg et eg m mm dm) =
    bŝ (Good-tr e g0) (λ η d → Good-tr e (gg η d)) (self-trˢ e et)
       (λ η d η′ d′ eη → trˢ-≅ e (≅-trˢ e (eg η d η′ d′ eη)))
       (λ η d → tr-cong (m η d)) (λ η d η′ d′ h → tr-cong (mm η d η′ d′ h))
       (Dom-tr e g0 gg et (λ η d → eg η d η d (≅ᴵ-refl η)) dm)
  Good-tr e (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
    bĉ G₀ Gg d₀ dE m₀ mE (Good-tr e go) (λ η d → Good-tr e (gO η d))
       (λ η d → tr-cong (mo η d)) (λ η d η′ d′ h → tr-cong (mO η d η′ d′ h))

  Good-tr⁻ e bz         = bz
  Good-tr⁻ e (bs g)     = bs (Good-tr⁻ e g)
  Good-tr⁻ e (bl hg st) = bl (λ n → Good-tr⁻ e (hg n)) (λ n → tr⁻-cong (st n))
  Good-tr⁻ e (bi {p = q} {f = f} hb hm) = bi
    (λ z ez g → subst (λ w → Good (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w))))) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z))
                      (Good-tr⁻ e (hb (backˢ (res⁻ˢ q e) z) (self-back⁻ q e ez)
                                      (Good→Gd (<→◃ q) (Good-back⁻ q e (Gd→Good (<→◃ (ltˢ (res⁻ˢ q e))) g))))))
    (λ {z} {z′} h → subst₂ (λ w w′ → tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w))) ⊑ᵒ tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w′))))
                           (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z)) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z′))
                           (tr⁻-cong (hm (back⁻-mono q e h))))
  Good-tr⁻ (s≅ e) (bu {r = zero} g)   = bu (Good-tr⁻ e g)
  Good-tr⁻ (l≅ f) (bu {r = self n} g) = bu (Good-tr⁻ (f n) g)
  Good-tr⁻ e (bŝ g0 gg et eg m mm dm) =
    bŝ (Good-tr⁻ e g0) (λ η d → Good-tr⁻ e (gg η d)) (self-tr⁻ˢ e et)
       (λ η d η′ d′ eη → tr⁻ˢ-≅ e (≅-tr⁻ˢ e (eg η d η′ d′ eη)))
       (λ η d → tr⁻-cong (m η d)) (λ η d η′ d′ h → tr⁻-cong (mm η d η′ d′ h))
       (Dom-tr⁻ e g0 gg et (λ η d → eg η d η d (≅ᴵ-refl η)) dm)
  Good-tr⁻ e (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
    bĉ G₀ Gg d₀ dE m₀ mE (Good-tr⁻ e go) (λ η d → Good-tr⁻ e (gO η d))
       (λ η d → tr⁻-cong (mo η d)) (λ η d η′ d′ h → tr⁻-cong (mO η d η′ d′ h))

  Good-back zero      (s≅ e) g = Good-tr⁻ e g
  Good-back (suc q)   (s≅ e) g = Good-back q e g
  Good-back (lim n q) (l≅ f) g = Good-back q (f n) g

  Good-back⁻ zero      (s≅ e) g = Good-tr e g
  Good-back⁻ (suc q)   (s≅ e) g = Good-back⁻ q e g
  Good-back⁻ (lim n q) (l≅ f) g = Good-back⁻ q (f n) g

  Good-Ω : ∀ a → Good (Ωˢ a)
  Good-Ω zero      = bs bz
  Good-Ω (suc c)   = bi (λ z ez g → bu g) (λ {z} {z′} h → up-l {r = zero} {x = z} (up-r {r = zero} {y = z′} h))
  Good-Ω (lim g s) = bl (λ n → bu (Good-Ω (g n))) (λ n → up-l {r = self n} (up-r {r = self (suc n)} (Ω-monoᵒ (s n))))

  Good-add : ∀ {k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} → Lv k ℓ → Good a → a ≅ˢ a → Good b → Good (addˢ a σ b)
  Good-add lv ga ea bz          = ga
  Good-add lv ga ea (bs g)      = bs (Good-add lv ga ea g)
  Good-add lv ga ea (bl hg st)  = bl (λ n → Good-add lv ga ea (hg n)) (λ n → add-cong refl ea (st n))
  Good-add {a = a} {σ = σ} lv ga ea (bi {p = q} {f = f} hb hm) = bi
    (λ z ez g → subst (λ u → Good (addˢ a σ (f (intoˢ (<→◃ q) u)))) (sym (out-intoˢ (<→◃ (σ q)) z))
                      (Good-add lv ga ea (hb z ez (Gd-conv (<→◃ (σ q)) (<→◃ q) g))))
    (λ {z} {z′} h → subst₂ (λ u v → addˢ a σ (f (intoˢ (<→◃ q) u)) ⊑ᵒ addˢ a σ (f (intoˢ (<→◃ q) v)))
                           (sym (out-intoˢ (<→◃ (σ q)) z)) (sym (out-intoˢ (<→◃ (σ q)) z′)) (add-cong refl ea (hm h)))
  Good-add lv ga ea (bu {r = zero} g)   = Good-add (Lv-up zero lv) ga ea g
  Good-add lv ga ea (bu {r = self n} g) = Good-add (Lv-up (self n) lv) ga ea g
  Good-add {k = zero} lv ga ea (bŝ g0 gg et eg m mm dm) =
    bĉ G₀ Gg (proj₁ dm G₀) (λ η e → proj₂ dm η e (Gg η e))
       (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
       (Good-add lv ga ea g0) (λ η e → Good-add lv ga ea (gg η e))
       (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h))
    where
    G₀ = Good→Goodᶻ g0
    Gg = λ η e → Good→Goodᶻ (gg η e)
  Good-add {k = suc _} {ℓ = zero} lv ga ea (bŝ g0 gg et eg m mm dm) = ⊥-elim (tf (sym lv))
  Good-add {k = lim _ _} {ℓ = zero} lv ga ea (bŝ g0 gg et eg m mm dm) = ⊥-elim (tf (sym lv))
  Good-add {k = suc _} {ℓ = suc _} lv ga ea (bŝ g0 gg et eg m mm dm) =
    bŝ (Good-add lv ga ea g0) (λ η e → Good-add lv ga ea (gg η e)) (addˢ-≅ refl ea et)
       (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
       (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h)) dm
  Good-add {k = suc _} {ℓ = lim _ _} lv ga ea (bŝ g0 gg et eg m mm dm) =
    bŝ (Good-add lv ga ea g0) (λ η e → Good-add lv ga ea (gg η e)) (addˢ-≅ refl ea et)
       (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
       (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h)) dm
  Good-add {k = lim _ _} {ℓ = suc _} lv ga ea (bŝ g0 gg et eg m mm dm) =
    bŝ (Good-add lv ga ea g0) (λ η e → Good-add lv ga ea (gg η e)) (addˢ-≅ refl ea et)
       (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
       (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h)) dm
  Good-add {k = lim _ _} {ℓ = lim _ _} lv ga ea (bŝ g0 gg et eg m mm dm) =
    bŝ (Good-add lv ga ea g0) (λ η e → Good-add lv ga ea (gg η e)) (addˢ-≅ refl ea et)
       (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
       (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h)) dm
  Good-add lv ga ea (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
    bĉ G₀ Gg d₀ dE m₀ mE (Good-add lv ga ea go) (λ η e → Good-add lv ga ea (gO η e))
       (λ η e → add-cong refl ea (mo η e)) (λ η e η′ e′ h → add-cong refl ea (mO η e η′ e′ h))

  Good-iter : ∀ {ℓ} {c : Ordˢ ℓ} → Good c → c ≅ˢ c → ∀ n → Good (iter (c +ˢ_) Ord₊ˢ.zero n)
  Good-iter {ℓ} gc ec zero    = bz
  Good-iter {ℓ} gc ec (suc n) = Good-add (Lv-refl ℓ) gc ec (Good-iter gc ec n)
```


## §3 闭包定理, 以 `Strictᵝ` 为参数

`Strictᵝ`: 单 $\hat\Omega$ 栈、目标 0 的折叠, 对任意环境层号、任意 `Sim`、任意自反尾巴与任意证书, 输出的层号 $\sqsupseteq^\mathsf I\beta$. Stage2Label 的 `Strict₁` 就是 `Strictᵝ two`. `mkĉ`、`Good-ψ0` (空栈, 需要 `Ok`)、`chain0-good`、`popGood` 逐字; `popDom` 的前提从 $\ell\sqsubseteq^\mathsf I2$ 换成 $\ell\sqsubseteq^\mathsf I\beta$ (由 $i<^\mathsf I\ell\sqsubseteq^\mathsf I\beta$ 得 $i+1\sqsubseteq^\mathsf I\beta$, 证明不变).

```agda
  Strictᵝ : Set
  Strictᵝ = ∀ {L k} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} (y : Ordˢ k) → y ≅ˢ y →
            (G : Goodᶻ (toZ (ψ1 p σ z y))) → β ⊑ᴵ toLevel (force _ G) (force-HS _ G)

  mkĉ : ∀ {ℓ c} {t₀ : Ordˢ zero} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ zero} {o₀ : Ordˢ ℓ} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} →
        Good t₀ → (∀ η e → Good (g η e)) → (∀ η e → t₀ ⊑ᵒ g η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → g η e ⊑ᵒ g η′ e′) →
        Dom zero c t₀ g → Good o₀ → (∀ η e → Good (o η e)) →
        (∀ η e → o₀ ⊑ᵒ o η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → o η e ⊑ᵒ o η′ e′) →
        Good (Ord₊ˢ.ĉᴸ c (toZ t₀) (λ η e → toZ (g η e)) o₀ o)
  mkĉ g0 gg m mm (d₀ , dE) go gO mo mO =
    bĉ G₀ Gg (d₀ G₀) (λ η e → dE η e (Gg η e))
       (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
       go gO mo mO
    where
    G₀ = Good→Goodᶻ g0
    Gg = λ η e → Good→Goodᶻ (gg η e)

  Good-ψ0 : ∀ {i k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {x : Ordˢ k} → Good x → x ≅ˢ x → Ok i x → Good (ψ0 p σ x)
  chain0-good : ∀ {j k ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
                (∀ (z : Ordˢ j) → z ≅ˢ z → Gd j (<→◃ q) (intoˢ (<→◃ q) z) → Good (f (intoˢ (<→◃ q) z))) →
                Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → (∀ n → Ok j (f (intoˢ (<→◃ q) (chain0 σ q f n)))) →
                ∀ n → Good (chain0 σ q f n)
  chain0-good {j} hb e ok zero = Good-Ω j
  chain0-good {σ = σ} {q = q} {f = f} hb e ok (suc n) =
    Good-ψ0 (hb (chain0 σ q f n) (chain0-≅ e n) (Good→Gd (<→◃ q) (chain0-good hb e ok n))) (i-respˢ e (chain0-≅ e n)) (ok n)

  Good-ψ0 {i} bz ex ok = Good-Ω i
  Good-ψ0 {i} {p = p} {σ = σ} (bs g) ex ok = bl (Good-iter (Good-ψ0 g ea (Ok-suc i ok)) eψ) (rule4ᵒ eψ)
    where ea = s-invˢ ex
          eψ = ψ0-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} (≅ᴵ-refl i) ea
  Good-ψ0 {i} (bl hg st) ex ok = bl (λ n → Good-ψ0 (hg n) (l-invˢ ex n) (Ok-lim i ok n)) (λ n → ψ0-cong (st n))
  Good-ψ0 {i} {p = p} {σ = σ} (bi {j = j} {p = q} {f = f} hb hm) ex ok with <ᴵ-dec (σ q) p
  ... | injᵃ (via e r) = bi
    (λ z ez g → subst (λ u → Good (ψ0 p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))))) (sym (out-intoˢ (<→◃ r) z))
                      (Good-ψ0 (hb (tr⁻ˢ e z) (self-tr⁻ˢ e ez) (Good→Gd (<→◃ q) (Good-tr⁻ e (Gd→Good (<→◃ r) g))))
                               (i-respˢ ex (self-tr⁻ˢ e ez)) (Ok-pen r)))
    (λ {z} {z′} h → subst₂ (λ u v → ψ0 p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ⊑ᵒ ψ0 p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e v))))
                           (sym (out-intoˢ (<→◃ r) z)) (sym (out-intoˢ (<→◃ r) z′)) (ψ0-cong (hm (tr⁻-cong h))))
  ... | injᵇ c = bl (λ n → Good-ψ0 (hb (chain0 σ q f n) (chain0-≅ ex n)
                                         (Good→Gd (<→◃ q) (chain0-good hb ex (λ m → proj₁ (Ok-col σ (inj₁ c) ok m)) n)))
                                    (i-respˢ ex (chain0-≅ ex n)) (proj₂ (Ok-col σ (inj₁ c) ok n)))
                    (λ n → ψ0-cong (hm (chain0-step ex hm n)))
  ... | injᶜ c = bl (λ n → Good-ψ0 (hb (chain0 σ q f n) (chain0-≅ ex n)
                                         (Good→Gd (<→◃ q) (chain0-good hb ex (λ m → proj₁ (Ok-col σ (inj₂ c) ok m)) n)))
                                    (i-respˢ ex (chain0-≅ ex n)) (proj₂ (Ok-col σ (inj₂ c) ok n)))
                    (λ n → ψ0-cong (hm (chain0-step ex hm n)))
  Good-ψ0 {i} (bu {r = zero} g) ex ok   = Good-ψ0 g (u-reflˢ zero ex) (Ok-up i zero ok)
  Good-ψ0 {i} (bu {r = self n} g) ex ok = Good-ψ0 g (u-reflˢ (self n) ex) (Ok-up i (self n) ok)
  Good-ψ0 {i = zero} (bŝ g0 gg et eg m mm dm) ex (_ , _ , d) = ⊥-elim (~ŝ d)
  Good-ψ0 {i = suc _} {k = zero} (bŝ g0 gg et eg m mm dm) ex ok =
    mkĉ g0 gg m mm dm (Good-ψ0 g0 et tt) (λ η e → Good-ψ0 (gg η e) (eg η e η e (≅ᴵ-refl η)) tt)
        (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h))
  Good-ψ0 {i = lim _ _} {k = zero} (bŝ g0 gg et eg m mm dm) ex ok =
    mkĉ g0 gg m mm dm (Good-ψ0 g0 et tt) (λ η e → Good-ψ0 (gg η e) (eg η e η e (≅ᴵ-refl η)) tt)
        (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h))
  Good-ψ0 {i = suc _} {k = suc _} (bŝ g0 gg et eg m mm dm) ex ok =
    bŝ (Good-ψ0 g0 et tt) (λ η e → Good-ψ0 (gg η e) (eg η e η e (≅ᴵ-refl η)) tt)
       (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
       (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h)) dm
  Good-ψ0 {i = suc _} {k = lim _ _} (bŝ g0 gg et eg m mm dm) ex ok =
    bŝ (Good-ψ0 g0 et tt) (λ η e → Good-ψ0 (gg η e) (eg η e η e (≅ᴵ-refl η)) tt)
       (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
       (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h)) dm
  Good-ψ0 {i = lim _ _} {k = suc _} (bŝ g0 gg et eg m mm dm) ex ok =
    bŝ (Good-ψ0 g0 et tt) (λ η e → Good-ψ0 (gg η e) (eg η e η e (≅ᴵ-refl η)) tt)
       (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
       (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h)) dm
  Good-ψ0 {i = lim _ _} {k = lim _ _} (bŝ g0 gg et eg m mm dm) ex ok =
    bŝ (Good-ψ0 g0 et tt) (λ η e → Good-ψ0 (gg η e) (eg η e η e (≅ᴵ-refl η)) tt)
       (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
       (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h)) dm
  Good-ψ0 {i = zero} (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex (_ , _ , d) = ⊥-elim (~ĉ d)
  Good-ψ0 {i = suc _} (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex ok =
    bĉ G₀ Gg d₀ dE m₀ mE (Good-ψ0 go (ĉ-refl₀ ex) tt) (λ η e → Good-ψ0 (gO η e) (ĉ-reflg ex η e) tt)
       (λ η e → ψ0-cong (mo η e)) (λ η e η′ e′ h → ψ0-cong (mO η e η′ e′ h))
  Good-ψ0 {i = lim _ _} (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex ok =
    bĉ G₀ Gg d₀ dE m₀ mE (Good-ψ0 go (ĉ-refl₀ ex) tt) (λ η e → Good-ψ0 (gO η e) (ĉ-reflg ex η e) tt)
       (λ η e → ψ0-cong (mo η e)) (λ η e η′ e′ h → ψ0-cong (mO η e η′ e′ h))
```


```agda
  popGood : ∀ {i k ℓ} (p : i <ᴵ ℓ) (σ : Simᴵ k ℓ) (z : zero <ᴵ ℓ) → Dom i (suc i) (t₀pop p z) (gpop p z) →
            Good (ψ1 p σ z Ord₊ˢ.zero)
  popGood {i} p σ z dm =
    bŝ (Good-ψ0 (Good-Ω (suc zero)) (Ωˢ-refl (suc zero)) (Ok-Pl i (Pl-Ω (suc zero))))
       (λ η e → Good-ψ0 (Good-Ω η) (Ωˢ-refl η) (Ok-Pl i (Pl-Ω η)))
       (ψ0-≅ (≅ᴵ-refl i) (Ωˢ-refl (suc zero))) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl i) (Ωˢ-≅ eη))
       (λ η e → ψ0-cong (Ω-monoᵒ (⊑ᴵ-trans (s⊑ z≅ (z<suc z p)) e))) (λ η e η′ e′ h → ψ0-cong (Ω-monoᵒ h)) dm

  popDom₀ : ∀ {ℓ} (p : zero <ᴵ ℓ) (z : zero <ᴵ ℓ) → Dom zero (suc zero) (t₀pop p z) (gpop p z)
  popDom₀ p z = (λ G → Strict₀ (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)) G) , (λ η e G → Strict₀ (Ωˢ η) (Ωˢ-refl η) G)

  popDom : ∀ {i ℓ} (p : i <ᴵ ℓ) (z : zero <ᴵ ℓ) → ℓ ⊑ᴵ β → Dom i (suc i) (t₀pop p z) (gpop p z)
  popDom {i = zero}    p z h = popDom₀ p z
  popDom {i = suc _}   p z h = s⊑′ (sim h p)
  popDom {i = lim _ _} p z h = s⊑′ (sim h p)
```


**`Good-ψ1`, 在子模块 `Clos Sβ` 里.** `Dom-ψ1`: 非零层的闭包 (界 $c\sqsubseteq^\mathsf I\beta$) 被目标 0 的折叠映到第 0 层, 新链的链点是 $\psi^{[\hat\Omega]}_0(t_0)$ 与 $\psi^{[\hat\Omega]}_0(g\,\eta\,e)$, 支配由 $c\sqsubseteq^\mathsf I\beta$ 与 `Sβ` 复合. 其余与 Stage2Label 逐字.

```agda
  module Clos (Sβ : Strictᵝ) where
    Dom-ψ1 : ∀ {L k c} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} →
             c ⊑ᴵ β → t₀ ≅ˢ t₀ → (∀ η e → g η e ≅ˢ g η e) →
             Dom zero c (ψ1 p σ z t₀) (λ η e → ψ1 p σ z (g η e))
    Dom-ψ1 {t₀ = t₀} {g = g} dm et eg =
      (λ G → ⊑ᴵ-trans dm (Sβ t₀ et G)) , (λ η e G → ⊑ᴵ-trans dm (Sβ (g η e) (eg η e) G))

    Good-ψ1 : ∀ {i k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {x : Ordˢ k} → ℓ ⊑ᴵ β → Good x → x ≅ˢ x →
              Good (ψ1 p σ z x)
    chain1-good : ∀ {j k ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} → ℓ ⊑ᴵ β →
                  (∀ (y : Ordˢ j) → y ≅ˢ y → Gd j (<→◃ q) (intoˢ (<→◃ q) y) → Good (f (intoˢ (<→◃ q) y))) →
                  Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → ∀ n → Good (chain1 σ z q f n)
    chain1-good {j} h hb e zero = Good-Ω j
    chain1-good {σ = σ} {z = z} {q = q} {f = f} h hb e (suc n) =
      Good-ψ1 h (hb (chain1 σ z q f n) (chain1-≅ e n) (Good→Gd (<→◃ q) (chain1-good h hb e n))) (i-respˢ e (chain1-≅ e n))

    Good-ψ1 {p = p} {σ = σ} {z = z} h bz ex = popGood p σ z (popDom p z h)
    Good-ψ1 {i} {p = p} {σ = σ} {z = z} h (bs g) ex = bl (Good-iter (Good-ψ1 h g ea) eψ) (rule4ᵒ eψ)
      where ea = s-invˢ ex
            eψ = ψ1-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} {z = z} {z′ = z} (≅ᴵ-refl i) ea
    Good-ψ1 h (bl hg st) ex = bl (λ n → Good-ψ1 h (hg n) (l-invˢ ex n)) (λ n → ψ1-cong (st n))
    Good-ψ1 {p = p} {σ = σ} {z = z} h (bi {j = j} {p = q} {f = f} hb hm) ex with <ᴵ-dec (σ q) p
    ... | injᵃ (via e r) = bi
      (λ y ey g → subst (λ u → Good (ψ1 p σ z (f (intoˢ (<→◃ q) (tr⁻ˢ e u))))) (sym (out-intoˢ (<→◃ r) y))
                        (Good-ψ1 h (hb (tr⁻ˢ e y) (self-tr⁻ˢ e ey) (Good→Gd (<→◃ q) (Good-tr⁻ e (Gd→Good (<→◃ r) g))))
                                   (i-respˢ ex (self-tr⁻ˢ e ey))))
      (λ {y} {y′} hy → subst₂ (λ u v → ψ1 p σ z (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ⊑ᵒ ψ1 p σ z (f (intoˢ (<→◃ q) (tr⁻ˢ e v))))
                              (sym (out-intoˢ (<→◃ r) y)) (sym (out-intoˢ (<→◃ r) y′)) (ψ1-cong (hm (tr⁻-cong hy))))
    ... | injᵇ _ = bl (λ n → Good-ψ1 h (hb (chain1 σ z q f n) (chain1-≅ ex n) (Good→Gd (<→◃ q) (chain1-good h hb ex n)))
                                        (i-respˢ ex (chain1-≅ ex n)))
                      (λ n → ψ1-cong (hm (chain1-step ex hm n)))
    ... | injᶜ _ = bl (λ n → Good-ψ1 h (hb (chain1 σ z q f n) (chain1-≅ ex n) (Good→Gd (<→◃ q) (chain1-good h hb ex n)))
                                        (i-respˢ ex (chain1-≅ ex n)))
                      (λ n → ψ1-cong (hm (chain1-step ex hm n)))
    Good-ψ1 h (bu {r = zero} g) ex   = Good-ψ1 h g (u-reflˢ zero ex)
    Good-ψ1 h (bu {r = self n} g) ex = Good-ψ1 h g (u-reflˢ (self n) ex)
    Good-ψ1 {i = zero} {k = zero} h (bŝ g0 gg et eg m mm dm) ex =
      mkĉ g0 gg m mm dm (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
          (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh))
    Good-ψ1 {i = suc _} {k = zero} h (bŝ g0 gg et eg m mm dm) ex =
      mkĉ g0 gg m mm dm (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
          (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh))
    Good-ψ1 {i = lim _ _} {k = zero} h (bŝ g0 gg et eg m mm dm) ex =
      mkĉ g0 gg m mm dm (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
          (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh))
    Good-ψ1 {i = zero} {k = suc _} h (bŝ g0 gg et eg m mm dm) ex =
      bŝ (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
         (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
         (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh))
         (Dom-ψ1 dm et (λ η e → eg η e η e (≅ᴵ-refl η)))
    Good-ψ1 {i = zero} {k = lim _ _} h (bŝ g0 gg et eg m mm dm) ex =
      bŝ (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
         (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
         (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh))
         (Dom-ψ1 dm et (λ η e → eg η e η e (≅ᴵ-refl η)))
    Good-ψ1 {i = suc _} {k = suc _} h (bŝ g0 gg et eg m mm dm) ex =
      bŝ (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
         (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
         (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh)) dm
    Good-ψ1 {i = suc _} {k = lim _ _} h (bŝ g0 gg et eg m mm dm) ex =
      bŝ (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
         (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
         (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh)) dm
    Good-ψ1 {i = lim _ _} {k = suc _} h (bŝ g0 gg et eg m mm dm) ex =
      bŝ (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
         (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
         (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh)) dm
    Good-ψ1 {i = lim _ _} {k = lim _ _} h (bŝ g0 gg et eg m mm dm) ex =
      bŝ (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
         (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
         (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh)) dm
    Good-ψ1 h (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex =
      bĉ G₀ Gg d₀ dE m₀ mE (Good-ψ1 h go (ĉ-refl₀ ex)) (λ η e → Good-ψ1 h (gO η e) (ĉ-reflg ex η e))
         (λ η e → ψ1-cong (mo η e)) (λ η e η′ e′ hh → ψ1-cong (mO η e η′ e′ hh))
```


**读法.** 两个前提各用一次: $\ell\sqsubseteq^\mathsf I\beta$ 管弹栈处新闭包的界 ($i+1$, 由目标层 $i<\ell$ 得出), `Sβ` 管闭包到第 0 层后的链点. 一切别的情况 (后继、极限、`up`、穿透、带同一个栈的折叠链、`ĉᴸ`) 与 $\beta$ 无关. 所以 "界参数化" 本身是机械的; 数学全在 `Strictᵝ` 能对哪些 $\beta$ 成立 (§4).

## §4 `Strictᵝ` 的范围: 有限、到 BTBO 为止

**有限的 $\beta$.** $\psi^{[\hat\Omega]}_0(y)\sqsupseteq\psi^{[\hat\Omega]}_0(0)$ (`B1₁`), 后者是弹栈闭包, 它的第 0 个输出是 $\psi^{[]}_0(\Omega_1)\sqsupseteq\psi^{[]}_0(1)=\lim(0,1,2,\ldots)$ (Stage2Label 的 `one≺` 的推广, 观测证明). 第 $m$ 项的计值字面是 $m$ (`iter-sucs`, `force-sucs`), 所以每个有限 $n\prec$ 输出, `nat⊑` 把它变成 $n\sqsubseteq$ 输出.

```agda
sucsˢ : ℕ → Ordˢ zero
sucsˢ zero    = Ord₊ˢ.zero
sucsˢ (suc m) = Ord₊ˢ.suc (sucsˢ m)

add1 : ∀ m → Ord₊ˢ.suc Ord₊ˢ.zero +ˢ sucsˢ m ≡ sucsˢ (suc m)
add1 zero    = refl
add1 (suc m) = cong Ord₊ˢ.suc (add1 m)

iter-sucs : ∀ m → iter (Ord₊ˢ.suc Ord₊ˢ.zero +ˢ_) Ord₊ˢ.zero m ≡ sucsˢ m
iter-sucs zero    = refl
iter-sucs (suc m) = trans (cong (Ord₊ˢ.suc Ord₊ˢ.zero +ˢ_) (iter-sucs m)) (add1 m)

force-sucs : ∀ m {x : Ordˢ zero} → x ≡ sucsˢ m → (G : Goodᶻ (toZ x)) → force _ G ≅ natᶜ m
force-sucs zero    refl Goodᶻ.gz     = z≅
force-sucs (suc m) refl (Goodᶻ.gs G) = s≅ (force-sucs m refl G)

nat≺ω : ∀ n (G : Goodᶻ (toZ (Ord₊ˢ.lim (iter (Ord₊ˢ.suc Ord₊ˢ.zero +ˢ_) Ord₊ˢ.zero)))) → natᶜ n ≺ force _ G
nat≺ω n (Goodᶻ.gl Gs st) =
  ≺l (suc n) (≺-respʳ (≺z (≅-refl⁰ (natᶜ n))) (≅-sym (force-sucs (suc n) (iter-sucs (suc n)) (Gs (suc n)))))

nat≺ : ∀ {L} {p : zero <ᴵ L} (σ : Simᴵ (suc zero) L) n (G : Goodᶻ (toZ (ψ0 p σ (Ωˢ (suc zero))))) → natᶜ n ≺ force _ G
nat≺ {p = p} σ n G = le idO G₁ G (nat≺ω n G₁)
  where
  u : Ordˢ (suc zero)
  u = Ord₊ˢ.up zero (Ord₊ˢ.suc Ord₊ˢ.zero)
  u⊑ : u ⊑ᵒ Ωˢ (suc zero)
  u⊑ = limᵢ-r (λ z d → up-l {r = zero} (up-r {r = zero} {y = z} (≅→⊑ᵒ (≅ˢ-sym d))))
  le : ψ0 p σ u ⊑ᵒ ψ0 p σ (Ωˢ (suc zero))
  le = ψ0-cong {p = p} {p′ = p} {σ = σ} {σ′ = σ} u⊑
  G₁ : Goodᶻ (toZ (ψ0 p σ u))
  G₁ = US.Good→Goodᶻ (S2L.Good-ψ0 (US.bu (US.bs US.bz)) (upˡ (upʳ (s≅ z≅))) (zero , one⁰ , H₊.upˡ (H₊.s~ H₊.z~)))

natpop : ∀ {L k} (p : zero <ᴵ L) (σ : Simᴵ k L) (z : zero <ᴵ L) n (G : Goodᶻ (toZ (ψ1 p σ z Ord₊ˢ.zero))) →
         natᶜ n ≺ force _ G
natpop p σ z n (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) = ≺l 0 (nat≺ (σ1 (z<suc z p)) n Go₀)

nat⊑ : ∀ {X : Ordᶜ zero} → (∀ n → natᶜ n ≺ X) → ∀ n → natᶜ n ⊑ X
nat⊑ h zero    ()
nat⊑ h (suc n) (≺z e)  = ≺-respˡ (≅-sym e) (h n)
nat⊑ h (suc n) (≺s h′) = nat⊑ h n h′

StrictN : ∀ n → Bound.Strictᵝ (toLevel (natᶜ n) (natᶜ-HS n))
StrictN n {k = k} {p = p} {σ = σ} {z = z} y ey G =
  toLevel-⊑ (natᶜ-HS n) (force-HS _ G)
    (nat⊑ (λ m → B1₁ {q = p} {σ = σ} {z₁ = z} {x = ψ1 p σ z (𝟎ˢ {k})}
                      (≅→⊑ᵒ (ψ1-≅ {k₁ = k} {k₂ = k} {p = p} {σ = σ} {p′ = p} {σ′ = σ} {z = z} {z′ = z} (≅ᴵ-refl zero) z≅))
                      y ey idO G₀ G (natpop p σ z m G₀)) n)
  where G₀ = US.Good→Goodᶻ (S2L.popGood p σ z (S2L.popDom₀ p z))
```


**到 BTBO 为止.** `Strict-BTBO`: $\beta=\mathtt{lvl}\,\mathrm{BTBO}$ 成立, 因为尾巴 $0$ 的输出 $\cong$ BTBO (Stage2Label 的 `pop0≅`) 而一切输出 $\sqsupseteq$ 它 (`B1₁`). **否定 `Sβ-fails⁺`**: $\beta=\mathtt{lvl}\,\mathrm{BTBO}+1$ 时取尾巴 $0$, 得 $\mathtt{lvl}\,\mathrm{BTBO}\prec^\mathsf I\mathtt{lvl}\,\mathrm{BTBO}$. `Sβ-fails` 是 $\beta=\mathtt{lvl}\,\gamma'_1$ 的同一论证 (经 Stage2Label 的 `BTBO≺χ1ˢ`): $t_2$ 的链的第 1 个计值点 $\gamma'_2=\psi_0(\Omega_\Omega+\Omega_{\gamma'_1})$ 的环境层号 `Mlev 1 (lvl γ′₁) e` $\sqsupseteq\mathtt{lvl}\,\gamma'_1$, 而 `Good-ψ1` 要 $\ell\sqsubseteq^\mathsf I\beta$, 所以 `Bound` 路线给不出 $\gamma'_2$ 的证书 (Omega2 的 `no-Bound`).

```agda
popG : ∀ {L k} (p : zero <ᴵ L) (σ : Simᴵ k L) (z : zero <ᴵ L) → Goodᶻ (toZ (ψ1 p σ z Ord₊ˢ.zero))
popG p σ z = US.Good→Goodᶻ (S2L.popGood p σ z (S2L.popDom₀ p z))

Strict-BTBO : Bound.Strictᵝ (toLevel N.BTBOᴵ N.BTBO-HS)
Strict-BTBO {k = k} {p = p} {σ = σ} {z = z} y ey G =
  toLevel-⊑ N.BTBO-HS (force-HS _ G)
    (⊑-trans (≅→⊑ (≅-sym (pop0≅ p σ z (popG p σ z))))
             (B1₁ {q = p} {σ = σ} {z₁ = z} {x = ψ1 p σ z (𝟎ˢ {k})}
                  (≅→⊑ᵒ (ψ1-≅ {k₁ = k} {k₂ = k} {p = p} {σ = σ} {p′ = p} {σ′ = σ} {z = z} {z′ = z} (≅ᴵ-refl zero) z≅))
                  y ey idO (popG p σ z) G))

Sβ-fails⁺ : ¬ Bound.Strictᵝ (suc (toLevel N.BTBOᴵ N.BTBO-HS))
Sβ-fails⁺ S = ≺ᴵ-irrefl (≺ᴵ-respʳ (sim (S {p = z2} {σ = σ00} {z = z2} 𝟎ˢ z≅ Gp) zero)
                                  (toLevel-≅ (force-HS _ Gp) N.BTBO-HS (pop0≅ z2 σ00 z2 Gp)))
  where Gp = popG z2 σ00 z2
```


```agda
≺⊑ᴵ : ∀ {a b c} → a ≺ᴵ b → b ⊑ᴵ c → a ≺ᴵ c
≺⊑ᴵ (via e r) h = ≺ᴵ-respˡ e (sim h r)

Sβ-fails : (G : Goodᶻ (toZ χ1ˢ)) → ¬ Bound.Strictᵝ (toLevel (force _ G) (force-HS _ G))
Sβ-fails G S = ≺ᴵ-irrefl (≺ᴵ-respʳ (≺⊑ᴵ bl< (S {p = z2} {σ = σ00} {z = z2} 𝟎ˢ z≅ Gp))
                                   (toLevel-≅ (force-HS _ Gp) N.BTBO-HS (pop0≅ z2 σ00 z2 Gp)))
  where
  Gp : Goodᶻ (toZ (ψ1 z2 σ00 z2 Ord₊ˢ.zero))
  Gp = US.Good→Goodᶻ (S2L.popGood z2 σ00 z2 (S2L.popDom₀ z2 z2))
  bl< : toLevel N.BTBOᴵ N.BTBO-HS ≺ᴵ toLevel (force _ G) (force-HS _ G)
  bl< = toLevel-≺ N.BTBO-HS (force-HS _ G) (BTBO≺χ1ˢ G)
```


**读法.** 一个全局的界 $\beta$ 必须被**一切** $\psi^{[\hat\Omega]}_0$ 输出支配, 而最小的输出就是 $\psi^{[\hat\Omega]}_0(0)\cong$ BTBO. Decouple §11 设想的 `Strictⱼ` ($\mathtt{lvl}\,\psi^{[\hat\Omega]}_0(\Omega_j)\sqsupseteq j+1$) 是**逐个闭包**的界, 不是全局的; 它与证书的关系在 Omega2 §5 讨论.

## §5 检验: $X_3$ 的证书

$X_3=\psi_0(\Omega_\Omega+\Omega_3)$ 取环境层号 3 (Stage2Label 的 `X₃ˢ`; Stage2Label §11 编译了它在 `1 ∷ 1 ∷ 0 ∷ 2` 处有界为 3 的闭包, 那里 `Good-ψ1` 的前提 $\ell\sqsubseteq^\mathsf I2$ 不成立).

```agda
module B3 = Bound three
module C3 = B3.Clos (StrictN 3)

X₃-goodᵝ : B3.Good X₃ˢ
X₃-goodᵝ = C3.Good-ψ1 {p = z3} {σ = λ q → q} {z = z3} ⊑ᴵ-refl (B3.Good-Ω three) (Ωˢ-refl three)

GX₃ : Goodᶻ (toZ X₃ˢ)
GX₃ = B3.Good→Goodᶻ X₃-goodᵝ

X₃ᶠ : Ordᶜ zero
X₃ᶠ = force (toZ X₃ˢ) GX₃
```


**读法.** `GX₃` 是 Decouple §11 障碍 (1) 的解除: 界为 3 的闭包的十个字段齐全. 同法对一切有限环境层号 (`StrictN n`), 以及环境层号 $\sqsubseteq\mathtt{lvl}\,\mathrm{BTBO}$ (`Strict-BTBO`) 给出证书.

## §6 全层级的关系式标签 `LabS`

Decouple 的 `LabG₊` 加一行:

- `gŝ`: 非零层的闭包 `ŝ c t₀ g` ($\psi_\delta(\Omega_\Omega+\cdots)$, 共尾度 $\Omega_1$): 第 0 点匹配 $t[1]$, 分支在一切带标签 $\theta$ 的计值树 $Y$ 的层号处匹配 $t[\theta]$ (与 DecoupleBase 的 `lŝ` 相同, 带种类前提 `kd ℓ ≡ false`).

第 0 层仍是 DecoupleBase 的原子 (带证书与计值标签的第 0 层符号树, 第 0 层的闭包即待计值链也在其中). `LvS`/`Ls`/`LabS` 与 `LvG`/`Lg`/`LabG` 同构 (对 $\triangleleft$ 的递归, 正性与停机一次通过).

```agda
module _ (ℓ : Ordᴵ) (L< : (j : Ordᴵ) (r : j ◃ ℓ) → Uˢ j r → T → Set) where
  data LabS₊ : Ordˢ ℓ → T → Set where
    gz : ∀ {t} → cof t ≡ c0 → LabS₊ Ord₊ˢ.zero t
    gs : ∀ {t y} → cof t ≡ c1 → LabS₊ y (pred t) → LabS₊ (Ord₊ˢ.suc y) t
    gl : ∀ {t} {F : ℕ → Ordˢ ℓ} → cof t ≡ cω → (∀ n → LabS₊ (F n) (fsn t n)) → LabS₊ (Ord₊ˢ.lim F) t
    gu : ∀ {t k} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} → L< k (◃₁→◃ r) x t → LabS₊ (Ord₊ˢ.up r x) t
    gi : ∀ {t ν j} {q : j <ᴵ ℓ} {f : Uˢ j (<→◃ q) → Ordˢ ℓ} → cof t ≡ cΩ ν → (I : Idx ν) → j ≅ᴵ lvI I →
         (∀ η (x : Ordˢ j) → L< j (<→◃ q) (intoˢ (<→◃ q) x) η → LabS₊ (f (intoˢ (<→◃ q) x)) (fsT t η)) →
         LabS₊ (Ord₊ˢ.limᵢ q f) t
    gĉ : ∀ {t c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {o₀ : Ordˢ ℓ} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} → cof t ≡ cω →
         (∀ (K : CC c t₀ g) → LabS₊ o₀ (fsn t 0)) →
         (∀ (K : CC c t₀ g) k → LabS₊ (o (lvK K k) (dxK K k)) (fsn t (suc k))) →
         LabS₊ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) t
    gŝ : ∀ {t c} {t₀ : Ordˢ ℓ} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} → kd ℓ ≡ false → cof t ≡ cΩ [] →
         LabS₊ t₀ (fsT t (natT 1)) →
         (∀ θ (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → (e : c ⊑ᴵ toLevel Y hY) →
          LabS₊ (g (toLevel Y hY) e) (fsT t θ)) →
         LabS₊ (Ord₊ˢ.ŝ c t₀ g) t

LvS : (i : Ordᴵ) → ((j : Ordᴵ) (r : j ◃ i) → Uˢ j r → T → Set) → Ordˢ i → T → Set
LvS zero      L x t = Atom x t
LvS (suc i)   L x t = LabS₊ (suc i) L x t
LvS (lim f s) L x t = LabS₊ (lim f s) L x t

Ls : ∀ {ℓ} (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → T → Set
Ls i zero         x t = LvS i Ls x t
Ls i (suc r)      x t = Ls i r x t
Ls _ (self {f} n) x t = LvS (f n) Ls x t
Ls i (lim n r)    x t = Ls i r x t

LabS : ∀ {ℓ} → Ordˢ ℓ → T → Set
LabS {ℓ} x t = LvS ℓ Ls x t

Ls→ : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordˢ i} {t} → Ls i r (intoˢ r x) t → LabS x t
Ls→ zero      h = h
Ls→ (suc r)   h = Ls→ r h
Ls→ (self n)  h = h
Ls→ (lim n r) h = Ls→ r h

→Ls : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordˢ i} {t} → LabS x t → Ls i r (intoˢ r x) t
→Ls zero      h = h
→Ls (suc r)   h = →Ls r h
→Ls (self n)  h = h
→Ls (lim n r) h = →Ls r h

toS₊ : ∀ {i} {x : Ordˢ i} {t} → kd i ≡ false → LabS x t → LabS₊ i Ls x t
toS₊ {i = zero}    () h
toS₊ {i = suc _}   k h = h
toS₊ {i = lim _ _} k h = h

frS₊ : ∀ {i} {x : Ordˢ i} {t} → kd i ≡ false → LabS₊ i Ls x t → LabS x t
frS₊ {i = zero}    () h
frS₊ {i = suc _}   k h = h
frS₊ {i = lim _ _} k h = h
```


**读法: 为什么不能沿用 `LabG`.** `gi` 行的分支对 "下一层带标签的输入" 匹配, 这是逆变的位置. Decouple 只用到第 1 层的 `limᵢ` (节点 0, 输入是原子), 所以 `LabG` 的输入不含非零层的闭包也够. 目标 $\delta\ge2$ 时, 折叠在节点层 $j\ge1$ 上造链, 链点 $\psi^{[\hat\Omega]}_j(\cdots)$ 含界为 $j+1$ 的闭包, 而它们正是下一个分支的输入 ($X_3$ 的第 $m$ 项: 第 2 层的链点再被节点 1 折叠, 链点 $\psi^{[\hat\Omega]}_1(\cdots)$ 进入第 2 层树的分支). `LabG` 的 `gi` 行收不到这种输入, 而 `LabG → LabS` 在 `gi` 行要反向转换输入, 不可能. 所以整套 (搬运、$\Omega$、和、派发、上下文引理) 在 `LabS` 上重写, 下面三节是 Decouple §4–§8 的逐字改名加 `gŝ` 的情况.

## §7 搬运与 $\Omega$

`gŝ` 的搬运逐点 (`trˢ` 对 `ŝ` 逐点), 层号种类沿 $\cong^\mathsf I$ 传递 (`kd-≅`). `LabS-Ω` 与 `LabG-Ω` 逐字.

```agda
LabS-tr    : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ a} {t} → LabS x t → LabS (trˢ e x) t
LabS-tr⁻   : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ b} {t} → LabS x t → LabS (tr⁻ˢ e x) t
LabS-back  : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} {t} → LabS u t → LabS (backˢ (resˢ q e) u) t
LabS-back⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} {t} → LabS u t → LabS (backˢ (res⁻ˢ q e) u) t
S-tr  : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ a} {t} → LabS₊ a Ls x t → LabS₊ b Ls (trˢ e x) t
S-tr⁻ : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ b} {t} → LabS₊ b Ls x t → LabS₊ a Ls (tr⁻ˢ e x) t

LabS-tr z≅ at = Atom-≅ at (trˢ-≅ z≅ (proj₁ at))
LabS-tr (s≅ e) h = S-tr (s≅ e) h
LabS-tr (l≅ k) h = S-tr (l≅ k) h
LabS-tr⁻ z≅ at = Atom-≅ at (tr⁻ˢ-≅ z≅ (proj₁ at))
LabS-tr⁻ (s≅ e) h = S-tr⁻ (s≅ e) h
LabS-tr⁻ (l≅ k) h = S-tr⁻ (l≅ k) h

S-tr e (gz c)   = gz c
S-tr e (gs c h) = gs c (S-tr e h)
S-tr e (gl c h) = gl c (λ n → S-tr e (h n))
S-tr (s≅ e) (gu {r = zero} h)   = gu (LabS-tr e h)
S-tr (l≅ k) (gu {r = self n} h) = gu (LabS-tr (k n) h)
S-tr e {t = t} (gi {q = q} {f = f} c I ej h) =
  gi c I (≅ᴵ-trans (≅ᴵ-sym (eqˢ (resˢ q e))) ej)
     (λ η x l → subst (λ v → LabS₊ _ Ls (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) v)))) (fsT t η))
                      (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) x))
                      (S-tr e (h η (backˢ (resˢ q e) x) (→Ls (<→◃ q) (LabS-back q e (Ls→ (<→◃ (ltˢ (resˢ q e))) l))))))
S-tr e (gĉ c h₀ hk) = gĉ c (λ K → S-tr e (h₀ K)) (λ K k → S-tr e (hk K k))
S-tr e (gŝ kk c h₀ hg) = gŝ (trans (sym (kd-≅ e)) kk) c (S-tr e h₀) (λ θ Y hY lY nθ lt d → S-tr e (hg θ Y hY lY nθ lt d))

S-tr⁻ e (gz c)   = gz c
S-tr⁻ e (gs c h) = gs c (S-tr⁻ e h)
S-tr⁻ e (gl c h) = gl c (λ n → S-tr⁻ e (h n))
S-tr⁻ (s≅ e) (gu {r = zero} h)   = gu (LabS-tr⁻ e h)
S-tr⁻ (l≅ k) (gu {r = self n} h) = gu (LabS-tr⁻ (k n) h)
S-tr⁻ e {t = t} (gi {q = q} {f = f} c I ej h) =
  gi c I (≅ᴵ-trans (≅ᴵ-sym (eqˢ (res⁻ˢ q e))) ej)
     (λ η x l → subst (λ v → LabS₊ _ Ls (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) v)))) (fsT t η))
                      (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) x))
                      (S-tr⁻ e (h η (backˢ (res⁻ˢ q e) x) (→Ls (<→◃ q) (LabS-back⁻ q e (Ls→ (<→◃ (ltˢ (res⁻ˢ q e))) l))))))
S-tr⁻ e (gĉ c h₀ hk) = gĉ c (λ K → S-tr⁻ e (h₀ K)) (λ K k → S-tr⁻ e (hk K k))
S-tr⁻ e (gŝ kk c h₀ hg) = gŝ (trans (kd-≅ e) kk) c (S-tr⁻ e h₀) (λ θ Y hY lY nθ lt d → S-tr⁻ e (hg θ Y hY lY nθ lt d))

LabS-back zero      (s≅ e) h = LabS-tr⁻ e h
LabS-back (suc q)   (s≅ e) h = LabS-back q e h
LabS-back (lim n q) (l≅ k) h = LabS-back q (k n) h

LabS-back⁻ zero      (s≅ e) h = LabS-tr e h
LabS-back⁻ (suc q)   (s≅ e) h = LabS-back⁻ q e h
LabS-back⁻ (lim n q) (l≅ k) h = LabS-back⁻ q (k n) h
```


```agda
LabS-Ω : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → ∀ {a} → a ≅ᴵ toLevel Y hY → LabS (Ωˢ a) (Ωt θ)
LabS-Ω {θ = []} Ord₊.zero hY l nθ z≅ = Ωˢ-refl zero , Goodᶻ.gs Goodᶻ.gz , l1 refl (s≅ z≅) (l0 refl z≅)
LabS-Ω {θ = y ∷ ys} Ord₊.zero hY l nθ z≅ with Lab0[] l
... | ()
LabS-Ω {θ = θ} (Ord₊.suc Y) hY (l0 c ()) nθ (s≅ e)
LabS-Ω {θ = θ} (Ord₊.suc Y) hY (lω c () h) nθ (s≅ e)
LabS-Ω {θ = []} (Ord₊.suc Y) hY (l1 () (s≅ e′) l) nθ (s≅ e)
LabS-Ω {θ = w ∷ ws} (Ord₊.suc Y) hY (l1 c (s≅ e′) l) nθ (s≅ e) =
  gi (cong (E.cofψ0 (w ∷ ws)) c) (Y , hs⁻ hY , Lab-≅ e′ l , NF₁-pred nθ c) e
     (λ η x lx → gu (subst (LabS x) (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) c η)) lx))
LabS-Ω {θ = θ} (Ord₊.lim F) hY (l0 c ()) nθ (l≅ k)
LabS-Ω {θ = θ} (Ord₊.lim F) hY (l1 c () l) nθ (l≅ k)
LabS-Ω {θ = []} (Ord₊.lim F) hY (lω () (l≅ k′) h) nθ (l≅ k)
LabS-Ω {θ = w ∷ ws} (Ord₊.lim F) hY (lω c (l≅ k′) h) nθ (l≅ k) =
  gl (cong (E.cofψ0 (w ∷ ws)) c)
     (λ n → gu (subst (LabS _) (sym (E.fsn0-eq w ws n c))
                      (LabS-Ω (F n) (hl₁ hY n) (Lab-≅ (k′ n) (h n)) (NF₁-fsn nθ c n) (k n))))
LabS-Ω (Ord₊.limᵢ () f) hY l nθ e
LabS-Ω (Ord₊.up () x) hY l nθ e
```


## §8 不带前缀的 $\psi_w$

和 (`SSum₊`/`SRep`) 多一个前提 `kd ℓ ≡ false` (被加数所在层非零): 尾巴是非零层闭包时和仍是闭包 ($a+\hat s$ 逐点), 它的 `gŝ` 行要这个前提. 派发 `giPsiS` 与 Decouple 的 `giPsi` 逐字. `PsiS₊` 多 `gŝ` 的情况: 非零目标 $w$ 对共尾度 $\Omega_1$ 的参数逐点穿透 (Prefix 的 `H1-pen`/`H1-fsT`, 要 $w\ne[]$, 由目标层非零与 `kdI[]` 得出).

```agda
SSumA : ∀ {ℓ} {a : Ordˢ ℓ} {σ : Simᴵ zero ℓ} {b : Ordˢ zero} {x ys} → LabS₊ ℓ Ls a (x ∷ []) → Lab₁ b ys →
        LabS₊ ℓ Ls (addˢ a σ b) (x ∷ ys)
SSumA {ys = []} la (lz c) = la
SSumA {ys = y ∷ ys} la (lz c) = ⊥-elim (cof-ne y ys c)
SSumA {ys = []} la (ls () l)
SSumA {ys = y ∷ ys} la (ls c l) = gs c (SSumA la l)
SSumA {ys = []} la (ll () h)
SSumA {ys = y ∷ ys} la (ll c h) = gl c (λ n → SSumA la (h n))
SSumA la (lu {r = ()} l)
SSumA la (li {q = ()} c h)
SSumA la (lŝ () c h₀ hg)
SSumA {ys = []} la (lŝ₀ () h₀ hk)
SSumA {ys = y ∷ ys} la (lŝ₀ c h₀ hk) = gĉ c (λ K → SSumA la (h₀ K)) (λ K m → SSumA la (hk K m))
SSumA {ys = []} la (lĉ () h₀ hk)
SSumA {ys = y ∷ ys} la (lĉ c h₀ hk) = gĉ c (λ K → SSumA la (h₀ K)) (λ K m → SSumA la (hk K m))

SSum  : ∀ {k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} {x ys} → kd ℓ ≡ false → LabS₊ ℓ Ls a (x ∷ []) → LabS b ys →
        LabS₊ ℓ Ls (addˢ a σ b) (x ∷ ys)
SSum₊ : ∀ {k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} {x ys} → kd ℓ ≡ false → LabS₊ ℓ Ls a (x ∷ []) → LabS₊ k Ls b ys →
        LabS₊ ℓ Ls (addˢ a σ b) (x ∷ ys)
SSum {k = zero} kl la at = SSumA la (atomL at)
SSum {k = suc _} kl la h = SSum₊ kl la h
SSum {k = lim _ _} kl la h = SSum₊ kl la h
SSum₊ {ys = []} kl la (gz c) = la
SSum₊ {ys = y ∷ ys} kl la (gz c) = ⊥-elim (cof-ne y ys c)
SSum₊ {ys = []} kl la (gs () h)
SSum₊ {ys = y ∷ ys} kl la (gs c h) = gs c (SSum₊ kl la h)
SSum₊ {ys = []} kl la (gl () h)
SSum₊ {ys = y ∷ ys} kl la (gl c h) = gl c (λ n → SSum₊ kl la (h n))
SSum₊ {σ = σ} kl la (gu {r = zero} h) = SSum {σ = λ q → σ (suc q)} kl la h
SSum₊ {σ = σ} kl la (gu {r = self n} h) = SSum {σ = λ q → σ (lim n q)} kl la h
SSum₊ {ys = []} kl la (gi () I ej h)
SSum₊ {a = a} {σ = σ} {x = x} {ys = y ∷ ys} kl la (gi {q = q} {f = f} c I ej h) =
  gi c I ej (λ η w l → subst (λ v → LabS₊ _ Ls (addˢ a σ (f (intoˢ (<→◃ q) v))) (x ∷ fsT (y ∷ ys) η))
                             (sym (out-intoˢ (<→◃ (σ q)) w))
                             (SSum₊ kl la (h η w (→Ls (<→◃ q) (Ls→ (<→◃ (σ q)) l)))))
SSum₊ {ys = []} kl la (gĉ () h₀ hk)
SSum₊ {ys = y ∷ ys} kl la (gĉ c h₀ hk) = gĉ c (λ K → SSum₊ kl la (h₀ K)) (λ K m → SSum₊ kl la (hk K m))
SSum₊ {k = zero} kl la (gŝ () c h₀ hg)
SSum₊ {k = suc _} {ys = []} kl la (gŝ kk () h₀ hg)
SSum₊ {k = suc _} {ys = y ∷ ys} kl la (gŝ kk c h₀ hg) =
  gŝ kl c (SSum₊ kl la h₀) (λ θ Y hY lY nθ lt e → SSum₊ kl la (hg θ Y hY lY nθ lt e))
SSum₊ {k = lim _ _} {ys = []} kl la (gŝ kk () h₀ hg)
SSum₊ {k = lim _ _} {ys = y ∷ ys} kl la (gŝ kk c h₀ hg) =
  gŝ kl c (SSum₊ kl la h₀) (λ θ Y hY lY nθ lt e → SSum₊ kl la (hg θ Y hY lY nθ lt e))

SRep : ∀ {ℓ} {P : Ordˢ ℓ} {x} → kd ℓ ≡ false → LabS₊ ℓ Ls P (x ∷ []) → ∀ n →
       LabS₊ ℓ Ls (iter (P +ˢ_) Ord₊ˢ.zero n) (replicate n x)
SRep kl lP zero    = gz refl
SRep kl lP (suc n) = SSum₊ kl lP (SRep kl lP n)
```


```agda
-- the Ω_{ν+1}-row of ψ_w, given the two recursive calls as oracles
giPsiS : ∀ {k ℓ i w ν j y ys} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
        (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
        (rec : ∀ η (x : Ordˢ j) → LabS x η → LabS₊ i Ls (ψ0 p σ (f (intoˢ (<→◃ q) x))) (ψᵗ w (fsT (y ∷ ys) η) ∷ [])) →
        (recC : kd j ≡ false → ∀ η (x : Ordˢ j) → LabS x η →
                LabS₊ j Ls (ψ0 (σ q) σ (f (intoˢ (<→◃ q) x))) (ψᵗ ν (fsT (y ∷ ys) η) ∷ [])) →
        LabS₊ i Ls (ψ0 p σ (Ord₊ˢ.limᵢ q f)) (ψᵗ w (y ∷ ys) ∷ [])
giPsiS {i = i} {w = w} {ν = ν} {j = j} {y = y} {ys = ys} {p = p} {σ = σ} {q = q} {f = f} Iw ei ki c Iν ej rec recC =
  go (cmpᵀ (sucT ν) w) refl
  where
  pen : Pen (cmpᵀ (sucT ν) w) → LabS₊ i Ls (ψ0 p σ (Ord₊ˢ.limᵢ q f)) (ψᵗ w (y ∷ ys) ∷ [])
  pen pn with pen0 {p = p} {σ = σ} {q = q} {f = f} (≅ᴵ-refl j)
                   (≺ᴵ-respʳ (≺ᴵ-respˡ ej (Ilt Iν Iw (pen→< ν w pn))) (≅ᴵ-sym ei))
  ... | j′ , e , r , eqn =
    subst (λ W → LabS₊ i Ls W (ψᵗ w (y ∷ ys) ∷ [])) (sym eqn)
          (gi cofE Iν (≅ᴵ-trans (≅ᴵ-sym e) ej)
              (λ η x l → subst (λ v → LabS₊ i Ls (ψ0 p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e v)))) (fsT (ψᵗ w (y ∷ ys) ∷ []) η))
                               (sym (out-intoˢ (<→◃ r) x))
                               (subst (LabS₊ i Ls _) (sym (fsT₊-pen′ w (y ∷ ys) ν (cof (y ∷ ys)) c pn η))
                                      (rec η (tr⁻ˢ e x) (LabS-tr⁻ e (Ls→ (<→◃ r) l))))))
    where
    cofE : cof (ψᵗ w (y ∷ ys) ∷ []) ≡ cΩ ν
    cofE = trans (cong (E.cofA w) c) (cofP pn)
  ne-w : w ≡ [] → ⊥
  ne-w refl = tf (trans (sym (kdI[] Iw)) (trans (sym (kd-≅ ei)) ki))
  fold : cmpᵀ (sucT ν) w ≡ gt → LabS₊ i Ls (ψ0 p σ (Ord₊ˢ.limᵢ q f)) (ψᵗ w (y ∷ ys) ∷ [])
  fold em =
    subst (λ W → LabS₊ i Ls W (ψᵗ w (y ∷ ys) ∷ [])) (sym (fold0 {p = p} {σ = σ} {q = q} {f = f} ij))
          (gl (trans (cong (E.cofA w) c) (cong (E.cofψ₊ w ν) em))
              (λ m → subst (LabS₊ i Ls _) (sym (fs-gt w y ys ν c em m)) (rec _ _ (chainL m))))
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
    chainL : ∀ m → LabS (chain0 σ q f m) (γT (y ∷ ys) ν m)
    chainL zero    = LabS-Ω (proj₁ Iν) (proj₁ (proj₂ Iν)) (proj₁ (proj₂ (proj₂ Iν))) (proj₂ (proj₂ (proj₂ Iν))) ej
    chainL (suc m) = frS₊ kj (recC kj _ _ (chainL m))
  go : ∀ m → cmpᵀ (sucT ν) w ≡ m → LabS₊ i Ls (ψ0 p σ (Ord₊ˢ.limᵢ q f)) (ψᵗ w (y ∷ ys) ∷ [])
  go lt em = pen (inj₁ em)
  go eq em = pen (inj₂ em)
  go gt em = fold em
```


```agda
PsiAS : ∀ {ℓ i w} {p : i <ᴵ ℓ} {σ : Simᴵ zero ℓ} {X : Ordˢ zero} {b} (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
       Lab₁ X b → LabS₊ i Ls (ψ0 p σ X) (ψᵗ w b ∷ [])
PsiAS {b = []} (Y , hY , lY , nY) ei ki (lz c) = toS₊ ki (LabS-Ω Y hY lY nY ei)
PsiAS {b = y ∷ ys} Iw ei ki (lz c) = ⊥-elim (cof-ne y ys c)
PsiAS {b = []} Iw ei ki (ls () l)
PsiAS {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (ls c l) =
  gl (cong (E.cofA w) c) (λ n → subst (LabS₊ _ Ls _) (sym (fs-rep w y ys c n)) (SRep ki (PsiAS {p = p} {σ = σ} Iw ei ki l) n))
PsiAS {b = []} Iw ei ki (ll () h)
PsiAS {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (ll c h) =
  gl (cong (E.cofA w) c) (λ n → subst (LabS₊ _ Ls _) (sym (fs-ω w y ys c n)) (PsiAS {p = p} {σ = σ} Iw ei ki (h n)))
PsiAS Iw ei ki (lu {r = ()} l)
PsiAS Iw ei ki (li {q = ()} c h)
PsiAS Iw ei ki (lŝ () c h₀ hg)
PsiAS {b = []} Iw ei ki (lŝ₀ () h₀ hk)
PsiAS {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (lŝ₀ c h₀ hk) =
  gĉ (cong (E.cofA w) c) (λ K → subst (LabS₊ _ Ls _) (sym (fs-ω w y ys c 0)) (PsiAS {p = p} {σ = σ} Iw ei ki (h₀ K)))
     (λ K m → subst (LabS₊ _ Ls _) (sym (fs-ω w y ys c (suc m))) (PsiAS {p = p} {σ = σ} Iw ei ki (hk K m)))
PsiAS {b = []} Iw ei ki (lĉ () h₀ hk)
PsiAS {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (lĉ c h₀ hk) =
  gĉ (cong (E.cofA w) c) (λ K → subst (LabS₊ _ Ls _) (sym (fs-ω w y ys c 0)) (PsiAS {p = p} {σ = σ} Iw ei ki (h₀ K)))
     (λ K m → subst (LabS₊ _ Ls _) (sym (fs-ω w y ys c (suc m))) (PsiAS {p = p} {σ = σ} Iw ei ki (hk K m)))

PsiVS  : ∀ {k ℓ i w} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {X : Ordˢ k} {b} (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
        LabS X b → LabS₊ i Ls (ψ0 p σ X) (ψᵗ w b ∷ [])
PsiS₊ : ∀ {k ℓ i w} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {X : Ordˢ k} {b} (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
        LabS₊ k Ls X b → LabS₊ i Ls (ψ0 p σ X) (ψᵗ w b ∷ [])
PsiVS {k = zero}    {p = p} {σ = σ} Iw ei ki at = PsiAS {p = p} {σ = σ} Iw ei ki (atomL at)
PsiVS {k = suc _}   {p = p} {σ = σ} Iw ei ki h  = PsiS₊ {p = p} {σ = σ} Iw ei ki h
PsiVS {k = lim _ _} {p = p} {σ = σ} Iw ei ki h  = PsiS₊ {p = p} {σ = σ} Iw ei ki h

PsiS₊ {b = []} (Y , hY , lY , nY) ei ki (gz c) = toS₊ ki (LabS-Ω Y hY lY nY ei)
PsiS₊ {b = y ∷ ys} Iw ei ki (gz c) = ⊥-elim (cof-ne y ys c)
PsiS₊ {b = []} Iw ei ki (gs () l)
PsiS₊ {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gs c l) =
  gl (cong (E.cofA w) c) (λ n → subst (LabS₊ _ Ls _) (sym (fs-rep w y ys c n)) (SRep ki (PsiS₊ {p = p} {σ = σ} Iw ei ki l) n))
PsiS₊ {b = []} Iw ei ki (gl () h)
PsiS₊ {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gl c h) =
  gl (cong (E.cofA w) c) (λ n → subst (LabS₊ _ Ls _) (sym (fs-ω w y ys c n)) (PsiS₊ {p = p} {σ = σ} Iw ei ki (h n)))
PsiS₊ {p = p} {σ = σ} Iw ei ki (gu {r = zero} h)   = PsiVS {p = p} {σ = λ q → σ (suc q)} Iw ei ki h
PsiS₊ {p = p} {σ = σ} Iw ei ki (gu {r = self n} h) = PsiVS {p = p} {σ = λ q → σ (lim n q)} Iw ei ki h
PsiS₊ {b = []} Iw ei ki (gi () Iν ej h)
PsiS₊ {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gi {q = q} {f = f} c Iν ej h) =
  giPsiS {p = p} {σ = σ} {q = q} {f = f} Iw ei ki c Iν ej
        (λ η x l → PsiS₊ {p = p} {σ = σ} Iw ei ki (h η x (→Ls (<→◃ q) l)))
        (λ kj η x l → PsiS₊ {p = σ q} {σ = σ} Iν ej kj (h η x (→Ls (<→◃ q) l)))
PsiS₊ {b = []} Iw ei ki (gĉ () h₀ hk)
PsiS₊ {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gĉ c h₀ hk) =
  gĉ (cong (E.cofA w) c) (λ K → subst (LabS₊ _ Ls _) (sym (fs-ω w y ys c 0)) (PsiS₊ {p = p} {σ = σ} Iw ei ki (h₀ K)))
     (λ K m → subst (LabS₊ _ Ls _) (sym (fs-ω w y ys c (suc m))) (PsiS₊ {p = p} {σ = σ} Iw ei ki (hk K m)))
PsiS₊ {k = zero} Iw ei ki (gŝ () c h₀ hg)
PsiS₊ {k = suc _} {w = []} Iw ei ki (gŝ kk c h₀ hg) = ⊥-elim (tf (trans (sym (kdI[] Iw)) (trans (sym (kd-≅ ei)) ki)))
PsiS₊ {k = suc _} {w = x ∷ xs} {b = []} Iw ei ki (gŝ kk () h₀ hg)
PsiS₊ {k = suc _} {w = x ∷ xs} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gŝ kk c h₀ hg) =
  gŝ ki (trans (cong (E.cofA (x ∷ xs)) c) (H1-pen x xs))
     (subst (LabS₊ _ Ls _) (sym (H1-fsT x xs y ys c (natT 1))) (PsiS₊ {p = p} {σ = σ} Iw ei ki h₀))
     (λ θ Y hY lY nθ lt e → subst (LabS₊ _ Ls _) (sym (H1-fsT x xs y ys c θ))
                                  (PsiS₊ {p = p} {σ = σ} Iw ei ki (hg θ Y hY lY nθ lt e)))
PsiS₊ {k = lim _ _} {w = []} Iw ei ki (gŝ kk c h₀ hg) = ⊥-elim (tf (trans (sym (kdI[] Iw)) (trans (sym (kd-≅ ei)) ki)))
PsiS₊ {k = lim _ _} {w = x ∷ xs} {b = []} Iw ei ki (gŝ kk () h₀ hg)
PsiS₊ {k = lim _ _} {w = x ∷ xs} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gŝ kk c h₀ hg) =
  gŝ ki (trans (cong (E.cofA (x ∷ xs)) c) (H1-pen x xs))
     (subst (LabS₊ _ Ls _) (sym (H1-fsT x xs y ys c (natT 1))) (PsiS₊ {p = p} {σ = σ} Iw ei ki h₀))
     (λ θ Y hY lY nθ lt e → subst (LabS₊ _ Ls _) (sym (H1-fsT x xs y ys c θ))
                                  (PsiS₊ {p = p} {σ = σ} Iw ei ki (hg θ Y hY lY nθ lt e)))
```


## §9 带前缀的 $\psi_w$, 目标 $w\ne0$

记号: `ctxw w b` $=\psi_w(\Omega_\Omega+b)$. `PreS₊ Iw : LabS₊ k X b → LabS₊ i (ψ1 p σ z X) (ctxw w b)`, 目标层 $i\cong^\mathsf I$ `lvI Iw` 非零, 环境层号、`Sim`、帧证据任意. 这是 DecoupleBase 的 `Pre1` (只有 $w=1$, 只收 `Lab₁`) 的推广, 证明照 `PsiS₊` 的结构, 参数列表前多一个 $\Omega_\Omega$:

- `gz`: 弹栈闭包 `popS` $=\psi_w(\Omega_\Omega)$: 字面是 `ŝ (suc i) (t₀pop p z) (gpop p z)`, 第 0 点 $\psi_w(\Omega_1)$ 与分支 $\psi_w(\Omega_{\mathtt{lvl}\,Y})$ 都不带前缀, 由 `PsiVS` 与 `LabS-Ω` (Decouple 的 `Hθ′` 对任意 $w$).
- `gs`/`gl`/`gĉ`: 规则 4/逐项, 记号侧 `fs-rep w ΩΩ (y ∷ ys)` 等 (参数是 $\Omega_\Omega+b$).
- `gi`: `giPre`, 与 `giPsiS` 同: `lt`/`eq` 由 `pen1` 穿透 (`fsT₊-pen′ w (ΩΩ ∷ y ∷ ys)`), `gt` 由 `fold1` 折叠, 链点 $\gamma_{m+1}=\psi^{[\hat\Omega]}_\nu(f\,\gamma_m)$ 的标签由递归 `recC` 在节点层 $\nu$ 上给出 (**带前缀的链**, 链点 $\psi_\nu(\Omega_\Omega+b[\gamma_m])$).
- `gŝ`: 逐点, `H1-fsT x xs ΩΩ (y ∷ ys)`.
- `gu` 下到第 0 层时是原子: `PreAS` 对原子的 `Lab₁` (经 `atomL`) 做同样的事.

```agda
ctxw : T → T → T
ctxw w b = ψᵗ w (ΩΩ ∷ b) ∷ []

nf1 : NF₁ (natT 1)
nf1 = γ′-NF 0

lab1 : Lab one⁰ (natT 1)
lab1 = l1 refl (s≅ z≅) (l0 refl z≅)

popS : ∀ {i k ℓ w} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
       LabS₊ i Ls (ψ1 p σ z Ord₊ˢ.zero) (ctxw w [])
popS {w = []} Iw ei ki = ⊥-elim (tf (trans (sym (kdI[] Iw)) (trans (sym (kd-≅ ei)) ki)))
popS {w = x ∷ xs} {p = p} {z = z} Iw ei ki =
  gŝ ki (H1-pen x xs)
     (subst (LabS₊ _ Ls _) (sym (H1-fsT x xs ΩΩ [] refl (natT 1)))
            (PsiVS {p = zero} {σ = σ1 (z<suc z p)} Iw ei ki (LabS-Ω one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _))))
     (λ θ Y hY lY nθ lt e → subst (LabS₊ _ Ls _) (sym (H1-fsT x xs ΩΩ [] refl θ))
            (PsiVS {p = lim 0 zero} {σ = λ q → lim 1 q} Iw ei ki (LabS-Ω Y hY lY nθ (≅ᴵ-refl _))))
```


```agda
giPre : ∀ {k ℓ i w ν j y ys} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
        (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
        (rec : ∀ η (x : Ordˢ j) → LabS x η → LabS₊ i Ls (ψ1 p σ z (f (intoˢ (<→◃ q) x))) (ctxw w (fsT (y ∷ ys) η))) →
        (recC : kd j ≡ false → ∀ η (x : Ordˢ j) → LabS x η →
                LabS₊ j Ls (ψ1 (σ q) σ z (f (intoˢ (<→◃ q) x))) (ctxw ν (fsT (y ∷ ys) η))) →
        LabS₊ i Ls (ψ1 p σ z (Ord₊ˢ.limᵢ q f)) (ctxw w (y ∷ ys))
giPre {i = i} {w = w} {ν = ν} {j = j} {y = y} {ys = ys} {p = p} {σ = σ} {z = z} {q = q} {f = f} Iw ei ki c Iν ej rec recC =
  go (cmpᵀ (sucT ν) w) refl
  where
  pen : Pen (cmpᵀ (sucT ν) w) → LabS₊ i Ls (ψ1 p σ z (Ord₊ˢ.limᵢ q f)) (ctxw w (y ∷ ys))
  pen pn with pen1 {p = p} {σ = σ} {z = z} {q = q} {f = f} (≅ᴵ-refl j)
                   (≺ᴵ-respʳ (≺ᴵ-respˡ ej (Ilt Iν Iw (pen→< ν w pn))) (≅ᴵ-sym ei))
  ... | j′ , e , r , eqn =
    subst (λ W → LabS₊ i Ls W (ctxw w (y ∷ ys))) (sym eqn)
          (gi cofE Iν (≅ᴵ-trans (≅ᴵ-sym e) ej)
              (λ η x l → subst (λ v → LabS₊ i Ls (ψ1 p σ z (f (intoˢ (<→◃ q) (tr⁻ˢ e v)))) (fsT (ctxw w (y ∷ ys)) η))
                               (sym (out-intoˢ (<→◃ r) x))
                               (subst (LabS₊ i Ls _) (sym (fsT₊-pen′ w (ΩΩ ∷ y ∷ ys) ν (cof (y ∷ ys)) c pn η))
                                      (rec η (tr⁻ˢ e x) (LabS-tr⁻ e (Ls→ (<→◃ r) l))))))
    where
    cofE : cof (ctxw w (y ∷ ys)) ≡ cΩ ν
    cofE = trans (cong (E.cofA w) c) (cofP pn)
  ne-w : w ≡ [] → ⊥
  ne-w refl = tf (trans (sym (kdI[] Iw)) (trans (sym (kd-≅ ei)) ki))
  fold : cmpᵀ (sucT ν) w ≡ gt → LabS₊ i Ls (ψ1 p σ z (Ord₊ˢ.limᵢ q f)) (ctxw w (y ∷ ys))
  fold em =
    subst (λ W → LabS₊ i Ls W (ctxw w (y ∷ ys))) (sym (fold1 {p = p} {σ = σ} {z = z} {q = q} {f = f} ij))
          (gl (trans (cong (E.cofA w) c) (cong (E.cofψ₊ w ν) em))
              (λ m → subst (LabS₊ i Ls _) (sym (fs-gt w ΩΩ (y ∷ ys) ν c em m)) (rec _ _ (chainL m))))
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
    chainL : ∀ m → LabS (chain1 σ z q f m) (γT (ΩΩ ∷ y ∷ ys) ν m)
    chainL zero    = LabS-Ω (proj₁ Iν) (proj₁ (proj₂ Iν)) (proj₁ (proj₂ (proj₂ Iν))) (proj₂ (proj₂ (proj₂ Iν))) ej
    chainL (suc m) = frS₊ kj (recC kj _ _ (chainL m))
  go : ∀ m → cmpᵀ (sucT ν) w ≡ m → LabS₊ i Ls (ψ1 p σ z (Ord₊ˢ.limᵢ q f)) (ctxw w (y ∷ ys))
  go lt em = pen (inj₁ em)
  go eq em = pen (inj₂ em)
  go gt em = fold em
```


```agda
PreAS : ∀ {ℓ i w} {p : i <ᴵ ℓ} {σ : Simᴵ zero ℓ} {z : zero <ᴵ ℓ} {X : Ordˢ zero} {b} (Iw : Idx w) → i ≅ᴵ lvI Iw →
        kd i ≡ false → Lab₁ X b → LabS₊ i Ls (ψ1 p σ z X) (ctxw w b)
PreAS {b = []} Iw ei ki (lz c) = popS Iw ei ki
PreAS {b = y ∷ ys} Iw ei ki (lz c) = ⊥-elim (cof-ne y ys c)
PreAS {b = []} Iw ei ki (ls () l)
PreAS {w = w} {p = p} {σ = σ} {z = z} {b = y ∷ ys} Iw ei ki (ls c l) =
  gl (cong (E.cofA w) c)
     (λ n → subst (LabS₊ _ Ls _) (sym (fs-rep w ΩΩ (y ∷ ys) c n)) (SRep ki (PreAS {p = p} {σ = σ} {z = z} Iw ei ki l) n))
PreAS {b = []} Iw ei ki (ll () h)
PreAS {w = w} {p = p} {σ = σ} {z = z} {b = y ∷ ys} Iw ei ki (ll c h) =
  gl (cong (E.cofA w) c)
     (λ n → subst (LabS₊ _ Ls _) (sym (fs-ω w ΩΩ (y ∷ ys) c n)) (PreAS {p = p} {σ = σ} {z = z} Iw ei ki (h n)))
PreAS Iw ei ki (lu {r = ()} l)
PreAS Iw ei ki (li {q = ()} c h)
PreAS Iw ei ki (lŝ () c h₀ hg)
PreAS {b = []} Iw ei ki (lŝ₀ () h₀ hk)
PreAS {w = w} {p = p} {σ = σ} {z = z} {b = y ∷ ys} Iw ei ki (lŝ₀ c h₀ hk) =
  gĉ (cong (E.cofA w) c)
     (λ K → subst (LabS₊ _ Ls _) (sym (fs-ω w ΩΩ (y ∷ ys) c 0)) (PreAS {p = p} {σ = σ} {z = z} Iw ei ki (h₀ K)))
     (λ K m → subst (LabS₊ _ Ls _) (sym (fs-ω w ΩΩ (y ∷ ys) c (suc m))) (PreAS {p = p} {σ = σ} {z = z} Iw ei ki (hk K m)))
PreAS {b = []} Iw ei ki (lĉ () h₀ hk)
PreAS {w = w} {p = p} {σ = σ} {z = z} {b = y ∷ ys} Iw ei ki (lĉ c h₀ hk) =
  gĉ (cong (E.cofA w) c)
     (λ K → subst (LabS₊ _ Ls _) (sym (fs-ω w ΩΩ (y ∷ ys) c 0)) (PreAS {p = p} {σ = σ} {z = z} Iw ei ki (h₀ K)))
     (λ K m → subst (LabS₊ _ Ls _) (sym (fs-ω w ΩΩ (y ∷ ys) c (suc m))) (PreAS {p = p} {σ = σ} {z = z} Iw ei ki (hk K m)))

PreVS : ∀ {k ℓ i w} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {X : Ordˢ k} {b} (Iw : Idx w) → i ≅ᴵ lvI Iw →
        kd i ≡ false → LabS X b → LabS₊ i Ls (ψ1 p σ z X) (ctxw w b)
PreS₊ : ∀ {k ℓ i w} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {X : Ordˢ k} {b} (Iw : Idx w) → i ≅ᴵ lvI Iw →
        kd i ≡ false → LabS₊ k Ls X b → LabS₊ i Ls (ψ1 p σ z X) (ctxw w b)
PreVS {k = zero}    {p = p} {σ = σ} {z = z} Iw ei ki at = PreAS {p = p} {σ = σ} {z = z} Iw ei ki (atomL at)
PreVS {k = suc _}   {p = p} {σ = σ} {z = z} Iw ei ki h  = PreS₊ {p = p} {σ = σ} {z = z} Iw ei ki h
PreVS {k = lim _ _} {p = p} {σ = σ} {z = z} Iw ei ki h  = PreS₊ {p = p} {σ = σ} {z = z} Iw ei ki h

PreS₊ {b = []} Iw ei ki (gz c) = popS Iw ei ki
PreS₊ {b = y ∷ ys} Iw ei ki (gz c) = ⊥-elim (cof-ne y ys c)
PreS₊ {b = []} Iw ei ki (gs () l)
PreS₊ {w = w} {p = p} {σ = σ} {z = z} {b = y ∷ ys} Iw ei ki (gs c l) =
  gl (cong (E.cofA w) c)
     (λ n → subst (LabS₊ _ Ls _) (sym (fs-rep w ΩΩ (y ∷ ys) c n)) (SRep ki (PreS₊ {p = p} {σ = σ} {z = z} Iw ei ki l) n))
PreS₊ {b = []} Iw ei ki (gl () h)
PreS₊ {w = w} {p = p} {σ = σ} {z = z} {b = y ∷ ys} Iw ei ki (gl c h) =
  gl (cong (E.cofA w) c)
     (λ n → subst (LabS₊ _ Ls _) (sym (fs-ω w ΩΩ (y ∷ ys) c n)) (PreS₊ {p = p} {σ = σ} {z = z} Iw ei ki (h n)))
PreS₊ {p = p} {σ = σ} {z = z} Iw ei ki (gu {r = zero} h)   = PreVS {p = p} {σ = λ q → σ (suc q)} {z = z} Iw ei ki h
PreS₊ {p = p} {σ = σ} {z = z} Iw ei ki (gu {r = self n} h) = PreVS {p = p} {σ = λ q → σ (lim n q)} {z = z} Iw ei ki h
PreS₊ {b = []} Iw ei ki (gi () Iν ej h)
PreS₊ {p = p} {σ = σ} {z = z} {b = y ∷ ys} Iw ei ki (gi {q = q} {f = f} c Iν ej h) =
  giPre {p = p} {σ = σ} {z = z} {q = q} {f = f} Iw ei ki c Iν ej
        (λ η x l → PreS₊ {p = p} {σ = σ} {z = z} Iw ei ki (h η x (→Ls (<→◃ q) l)))
        (λ kj η x l → PreS₊ {p = σ q} {σ = σ} {z = z} Iν ej kj (h η x (→Ls (<→◃ q) l)))
PreS₊ {b = []} Iw ei ki (gĉ () h₀ hk)
PreS₊ {w = w} {p = p} {σ = σ} {z = z} {b = y ∷ ys} Iw ei ki (gĉ c h₀ hk) =
  gĉ (cong (E.cofA w) c)
     (λ K → subst (LabS₊ _ Ls _) (sym (fs-ω w ΩΩ (y ∷ ys) c 0)) (PreS₊ {p = p} {σ = σ} {z = z} Iw ei ki (h₀ K)))
     (λ K m → subst (LabS₊ _ Ls _) (sym (fs-ω w ΩΩ (y ∷ ys) c (suc m))) (PreS₊ {p = p} {σ = σ} {z = z} Iw ei ki (hk K m)))
PreS₊ {k = zero} Iw ei ki (gŝ () c h₀ hg)
PreS₊ {k = suc _} {w = []} Iw ei ki (gŝ kk c h₀ hg) = ⊥-elim (tf (trans (sym (kdI[] Iw)) (trans (sym (kd-≅ ei)) ki)))
PreS₊ {k = suc _} {w = x ∷ xs} {b = []} Iw ei ki (gŝ kk () h₀ hg)
PreS₊ {k = suc _} {w = x ∷ xs} {p = p} {σ = σ} {z = z} {b = y ∷ ys} Iw ei ki (gŝ kk c h₀ hg) =
  gŝ ki (trans (cong (E.cofA (x ∷ xs)) c) (H1-pen x xs))
     (subst (LabS₊ _ Ls _) (sym (H1-fsT x xs ΩΩ (y ∷ ys) c (natT 1))) (PreS₊ {p = p} {σ = σ} {z = z} Iw ei ki h₀))
     (λ θ Y hY lY nθ lt e → subst (LabS₊ _ Ls _) (sym (H1-fsT x xs ΩΩ (y ∷ ys) c θ))
                                  (PreS₊ {p = p} {σ = σ} {z = z} Iw ei ki (hg θ Y hY lY nθ lt e)))
PreS₊ {k = lim _ _} {w = []} Iw ei ki (gŝ kk c h₀ hg) = ⊥-elim (tf (trans (sym (kdI[] Iw)) (trans (sym (kd-≅ ei)) ki)))
PreS₊ {k = lim _ _} {w = x ∷ xs} {b = []} Iw ei ki (gŝ kk () h₀ hg)
PreS₊ {k = lim _ _} {w = x ∷ xs} {p = p} {σ = σ} {z = z} {b = y ∷ ys} Iw ei ki (gŝ kk c h₀ hg) =
  gŝ ki (trans (cong (E.cofA (x ∷ xs)) c) (H1-pen x xs))
     (subst (LabS₊ _ Ls _) (sym (H1-fsT x xs ΩΩ (y ∷ ys) c (natT 1))) (PreS₊ {p = p} {σ = σ} {z = z} Iw ei ki h₀))
     (λ θ Y hY lY nθ lt e → subst (LabS₊ _ Ls _) (sym (H1-fsT x xs ΩΩ (y ∷ ys) c θ))
                                  (PreS₊ {p = p} {σ = σ} {z = z} Iw ei ki (hg θ Y hY lY nθ lt e)))
```


**读法.** `PreS₊` 与 `PsiS₊` 互不调用对方的递归 (弹栈闭包的分支调用已定义好的 `PsiVS`), 停机一次通过; 两个 oracle 都是对 `gi` 行分支的直接递归调用 (目标 $(i,w)$ 与 $(j,\nu)$), 同 Decouple §8.

## §10 带前缀的 $\psi_0$: 任意层的尾巴

`Pre0V`/`Pre0S₊`: 对尾巴的 `LabS` 推导递归, 对一切证书 $G$ 给出计值树的 `Lab … (ctx a)`. 与 DecoupleBase 的 `Pre0` 的区别只在 `gi` 行 (节点层任意):

- 节点层字面为 `zero`: 节点下标是 $0$ (`kdI`), 用 DecoupleBase 的 `liLab` (第 0 层的链, 链点是原子).
- 节点层非零: 先由标签得 $0\prec^\mathsf Ij$ (`z≺I`: 下标非零, `Ilt` 对 `I0`), `fold1` 给出字面的规则 6 树; `foldLab` 的链点 $\psi^{[\hat\Omega]}_j(f\,\gamma_m)$ 的标签由 §9 的 `PreS₊` 给出 (目标层 $j$, 带前缀), 第 $m$ 个输出由递归 (作为 λ 参数传入) 给出, 记号侧 Bachmann 的 `fs-gt [] ΩΩ`.
- 节点层非零而下标为 $0$: 由 `kdI[]` 排除.

`gŝ`/`gĉ`/`gs`/`gl` 与 `Pre0` 的 `lŝ`/`lĉ`/`ls`/`ll` 逐字 (`ŝOut`、`pOut`、`Lab-repᶻ`), `gu` 下到第 0 层时调用 `Pre0` 本身.

```agda
I0 : Idx []
I0 = Ord₊.zero , hz , l0 refl z≅ , n[]

z≺I : ∀ {ν j} → (I : Idx ν) → j ≅ᴵ lvI I → (ν ≡ [] → ⊥) → zero ≺ᴵ j
z≺I {ν = []}    I ej ne = ⊥-elim (ne refl)
z≺I {ν = v ∷ vs} I ej ne = ≺ᴵ-respʳ (Ilt I0 I []<) (≅ᴵ-sym ej)

foldLab : ∀ {L k j y ys v vs} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
          cof (y ∷ ys) ≡ cΩ (v ∷ vs) → (I : Idx (v ∷ vs)) → j ≅ᴵ lvI I → kd j ≡ false →
          Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → NF₁ (ctx (y ∷ ys)) →
          (h : ∀ η (x : Ordˢ j) → LabS x η → LabS₊ k Ls (f (intoˢ (<→◃ q) x)) (fsT (y ∷ ys) η)) →
          (rec : ∀ η (x : Ordˢ j) → LabS x η → f (intoˢ (<→◃ q) x) ≅ˢ f (intoˢ (<→◃ q) x) →
                 NF₁ (ctx (fsT (y ∷ ys) η)) → ∀ G → Lab (force (toZ (ψ1 p σ z (f (intoˢ (<→◃ q) x)))) G) (ctx (fsT (y ∷ ys) η))) →
          ∀ G → Lab (force (toZ (ψ1 p σ z (Ord₊ˢ.limᵢ q f))) G) (ctx (y ∷ ys))
foldLab {y = y} {ys = ys} {v = v} {vs = vs} {p = p} {σ = σ} {z = z} {q = q} {f = f} c I ej kj ex nu h rec G =
  subst (λ W → Lab W (ctx (y ∷ ys))) (sym (force-subst eqf G)) (go (subst (λ W → Goodᶻ (toZ W)) eqf G))
  where
  eqf = fold1 {p = p} {σ = σ} {z = z} {q = q} {f = f} (inj₁ (z≺I I ej (λ ())))
  chainL : ∀ m → LabS (chain1 σ z q f m) (γT (ΩΩ ∷ y ∷ ys) (v ∷ vs) m)
  chainL zero    = LabS-Ω (proj₁ I) (proj₁ (proj₂ I)) (proj₁ (proj₂ (proj₂ I))) (proj₂ (proj₂ (proj₂ I))) ej
  chainL (suc m) = frS₊ kj (PreS₊ {p = σ q} {σ = σ} {z = z} I ej kj (h _ _ (chainL m)))
  nf : ∀ m → NF₁ (ctx (fsT (y ∷ ys) (γT (ΩΩ ∷ y ∷ ys) (v ∷ vs) m)))
  nf m = subst NF₁ (fs-gt [] ΩΩ (y ∷ ys) (v ∷ vs) c refl m) (NF₁-fsn nu (cong (E.cofA []) c) m)
  go : ∀ G′ → Lab (force (toZ (Ord₊ˢ.lim (λ m → ψ1 p σ z (f (intoˢ (<→◃ q) (chain1 σ z q f m)))))) G′) (ctx (y ∷ ys))
  go (Goodᶻ.gl Gs st) = lω (cong (E.cofA []) c) (l≅ (λ m → ≅-refl⁰ _))
    (λ m → subst (Lab _) (sym (fs-gt [] ΩΩ (y ∷ ys) (v ∷ vs) c refl m))
                 (rec _ _ (chainL m) (i-respˢ ex (chain1-≅ ex m)) (nf m) (Gs m)))
```


```agda
Pre0V  : ∀ {L k} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} {x : Ordˢ k} {a} →
         LabS x a → x ≅ˢ x → NF₁ (ctx a) → (G : Goodᶻ (toZ (ψ1 p σ z x))) → Lab (force _ G) (ctx a)
Pre0S₊ : ∀ {L k} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} {x : Ordˢ k} {a} →
         LabS₊ k Ls x a → x ≅ˢ x → NF₁ (ctx a) → (G : Goodᶻ (toZ (ψ1 p σ z x))) → Lab (force _ G) (ctx a)
Pre0V {k = zero}    {p = p} {σ = σ} {z = z} at ex nu G = Pre0 {p = p} {σ = σ} {z = z} (atomL at) ex nu G
Pre0V {k = suc _}   {p = p} {σ = σ} {z = z} h  ex nu G = Pre0S₊ {p = p} {σ = σ} {z = z} h ex nu G
Pre0V {k = lim _ _} {p = p} {σ = σ} {z = z} h  ex nu G = Pre0S₊ {p = p} {σ = σ} {z = z} h ex nu G

Pre0S₊ {a = []} (gz c) ex nu G = pop0-label _ _ _ G
Pre0S₊ {a = y ∷ ys} (gz c) ex nu G = ⊥-elim (cof-ne y ys c)
Pre0S₊ {a = []} (gs () l) ex nu G
Pre0S₊ {p = p} {σ = σ} {z = z} {a = y ∷ ys} (gs c l) ex nu (Goodᶻ.gl Gs st) =
  lω (cong (E.cofA []) c) (l≅ (λ n → ≅-refl⁰ _))
     (λ n → subst (Lab _) (sym (fs-rep [] ΩΩ (y ∷ ys) c n))
                  (Lab-repᶻ (ψ1-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} {z = z} {z′ = z} z≅ (s-invˢ ex)) Gs
                            (λ G → Pre0S₊ {p = p} {σ = σ} {z = z} l (s-invˢ ex)
                                        (subst NF₁ (fs-rep [] ΩΩ (y ∷ ys) c 1) (NF₁-fsn nu (cong (E.cofA []) c) 1)) G) n))
Pre0S₊ {a = []} (gl () h) ex nu G
Pre0S₊ {p = p} {σ = σ} {z = z} {a = y ∷ ys} (gl c h) ex nu (Goodᶻ.gl Gs st) =
  lω (cong (E.cofA []) c) (l≅ (λ n → ≅-refl⁰ _))
     (λ n → subst (Lab _) (sym (fs-ω [] ΩΩ (y ∷ ys) c n))
                  (Pre0S₊ {p = p} {σ = σ} {z = z} (h n) (l-invˢ ex n) (nfω nu c n) (Gs n)))
Pre0S₊ {p = p} {σ = σ} {z = z} (gu {r = zero} l) ex nu G =
  Pre0V {p = p} {σ = λ q → σ (suc q)} {z = z} l (u-reflˢ zero ex) nu G
Pre0S₊ {p = p} {σ = σ} {z = z} (gu {r = self n} l) ex nu G =
  Pre0V {p = p} {σ = λ q → σ (lim n q)} {z = z} l (u-reflˢ (self n) ex) nu G
Pre0S₊ {a = []} (gi () I ej h) ex nu G
Pre0S₊ {p = p} {σ = σ} {z = z} {a = y ∷ ys} (gi {j = zero} {q = q} {f = f} c I ej h) ex nu G =
  liLab {p = p} {σ = σ} {z = z} {q = q} {f = f} (trans c (cong cΩ (kdI I (sym (kd-≅ ej))))) ex nu
        (λ θ x at br nf G′ → Pre0S₊ {p = p} {σ = σ} {z = z} (h θ x (→Ls (<→◃ q) at)) br nf G′) G
Pre0S₊ {a = y ∷ ys} (gi {ν = []} {j = suc _} c I ej h) ex nu G = ⊥-elim (tf (trans (sym (kdI[] I)) (sym (kd-≅ ej))))
Pre0S₊ {p = p} {σ = σ} {z = z} {a = y ∷ ys} (gi {ν = v ∷ vs} {j = suc _} {q = q} {f = f} c I ej h) ex nu G =
  foldLab {p = p} {σ = σ} {z = z} {q = q} {f = f} c I ej refl ex nu (λ η x l → h η x (→Ls (<→◃ q) l))
          (λ η x l br nf G′ → Pre0S₊ {p = p} {σ = σ} {z = z} (h η x (→Ls (<→◃ q) l)) br nf G′) G
Pre0S₊ {a = y ∷ ys} (gi {ν = []} {j = lim _ _} c I ej h) ex nu G = ⊥-elim (tf (trans (sym (kdI[] I)) (sym (kd-≅ ej))))
Pre0S₊ {p = p} {σ = σ} {z = z} {a = y ∷ ys} (gi {ν = v ∷ vs} {j = lim _ _} {q = q} {f = f} c I ej h) ex nu G =
  foldLab {p = p} {σ = σ} {z = z} {q = q} {f = f} c I ej refl ex nu (λ η x l → h η x (→Ls (<→◃ q) l))
          (λ η x l br nf G′ → Pre0S₊ {p = p} {σ = σ} {z = z} (h η x (→Ls (<→◃ q) l)) br nf G′) G
Pre0S₊ {k = zero} (gŝ () c h₀ hg) ex nu G
Pre0S₊ {k = suc _} {a = []} (gŝ kk () h₀ hg) ex nu G
Pre0S₊ {k = suc _} {p = p} {σ = σ} {z = z} {a = y ∷ ys} (gŝ kk c h₀ hg) ex nu (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) =
  lω (cong (E.cofA []) c) (l≅ (λ n → ≅-refl⁰ _))
     (ŝOut {p = p} {σ = σ} {z = z} c nu (λ G′ → Pre0S₊ {p = p} {σ = σ} {z = z} h₀ (ŝ-refl₀ ex) (nfγ nu c 0) G′)
           (λ θ Y hY lY nθ lt e nf G′ → Pre0S₊ {p = p} {σ = σ} {z = z} (hg θ Y hY lY nθ lt e) (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) nf G′)
           (cc G₀ Gg d₀ dE m₀ mE) Go₀ Go)
Pre0S₊ {k = lim _ _} {a = []} (gŝ kk () h₀ hg) ex nu G
Pre0S₊ {k = lim _ _} {p = p} {σ = σ} {z = z} {a = y ∷ ys} (gŝ kk c h₀ hg) ex nu (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) =
  lω (cong (E.cofA []) c) (l≅ (λ n → ≅-refl⁰ _))
     (ŝOut {p = p} {σ = σ} {z = z} c nu (λ G′ → Pre0S₊ {p = p} {σ = σ} {z = z} h₀ (ŝ-refl₀ ex) (nfγ nu c 0) G′)
           (λ θ Y hY lY nθ lt e nf G′ → Pre0S₊ {p = p} {σ = σ} {z = z} (hg θ Y hY lY nθ lt e) (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) nf G′)
           (cc G₀ Gg d₀ dE m₀ mE) Go₀ Go)
Pre0S₊ {a = []} (gĉ () h₀ hk) ex nu G
Pre0S₊ {p = p} {σ = σ} {z = z} {a = y ∷ ys} (gĉ c h₀ hk) ex nu (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) =
  lω (cong (E.cofA []) c) (l≅ (λ n → ≅-refl⁰ _))
     (pOut {p = p} {σ = σ} {z = z} c K Go₀ Go
           (Pre0S₊ {p = p} {σ = σ} {z = z} (h₀ K) (ĉ-refl₀ ex) (nfω nu c 0) Go₀)
           (λ m → Pre0S₊ {p = p} {σ = σ} {z = z} (hk K m) (ĉ-reflO ex _ _ _ _ (≅ᴵ-refl _)) (nfω nu c (suc m)) (Go _ _)))
  where K = cc G₀ Gg d₀ dE m₀ mE
```


**读法.** 链点标签的来源分两层: 第 0 层的链 (节点 0 或闭包) 在 `Pre0` 的结构递归里逐点前进; 节点层 $j\ne0$ 的链的链点是第 $j$ 层的带前缀树, 它们的标签由已定义好的 `PreS₊` 造出, 不进 `Pre0S₊` 的递归. 递归调用一律作为 λ 参数传入 (DecoupleBase §4 的写法), 停机一次通过.

## §11 检验: $X_3$ 的遗传标签

$X_3=\psi_0(\Omega_\Omega+\Omega_3)$: 标准形来自 $t_2$ 的路径 `1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 3` (Symbolic 的 `t2-to-X₃`) 与 StandardOmega 的 `diag₁-desc-NF`; 尾巴 $\Omega_3$ 的 `LabS` 由 `LabS-Ω` (层号 3 的树 `natᶜ 3` 带标签 $3$).

```agda
X₃-NF : NF₁ X₃ᵗ
X₃-NF = diag₁-desc-NF (walkD d₀ᴰ (1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 3 ∷ []) (refl , refl , refl , refl , refl , refl , tt))

nf3 : NF₁ (natT 3)
nf3 = ext X₃-NF
  where
  ext : NF₁ X₃ᵗ → NF₁ (natT 3)
  ext (n∷ (nψ _ _ (n∷ _ (n∷ (nψ n3 _ _ _) _ _) _) _) _ _) = n3

lab3 : Lab (natᶜ 3) (natT 3)
lab3 = l1 refl (≅-refl⁰ _) (l1 refl (≅-refl⁰ _) (l1 refl (≅-refl⁰ _) (l0 refl z≅)))

X₃-label : Lab X₃ᶠ X₃ᵗ
X₃-label = Pre0V {p = z3} {σ = λ q → q} {z = z3} (LabS-Ω (natᶜ 3) (natᶜ-HS 3) lab3 nf3 (≅ᴵ-refl three)) (Ωˢ-refl three) X₃-NF GX₃
```


**读法.** 树是 §5 的 `X₃ᶠ = force (toZ X₃ˢ) GX₃`. 计算路径: `Pre0V` → 尾巴 $\Omega_3$ 的 `gi` 行 (节点 2, 下标 2) → `foldLab`: 第 2 层的链 $\gamma_0=\Omega_2$, $\gamma_{m+1}=\psi^{[\hat\Omega]}_2(\gamma_m)$ 由 `PreS₊` (目标 2) 标; 每个链点里 $\Omega_2$ 的节点 1 在 `PreS₊` 里穿透 (`giPre` 的 `pen`), 弹栈得界 3 的闭包 (`popS`), 第 $m$ 项 $\psi^{[\hat\Omega]}_0(\gamma_m)$ 在 `Pre0S₊` 里再遇到节点 1 (折叠, 第 1 层的带前缀链) 与节点 0 (`liLab`) 及界 2、3 的闭包 (`ŝOut`). 这就是 Decouple §11 的障碍 (2) 的解除.

## §12 对比表

| | Decouple / Stage2Label | 本文 |
|---|---|---|
| 非零层闭包的支配 | `c ⊑ᴵ two` | `Bound β`: `c ⊑ᴵ β` |
| `Good-ψ1` 的前提 | $\ell\sqsubseteq^\mathsf I2$ | $\ell\sqsubseteq^\mathsf I\beta$, 外加 `Strictᵝ β` |
| 严格性 | `Strict₁` ($\beta=2$) | `StrictN n`, `Strict-BTBO`; `Sβ-fails⁺` ($\beta=\mathtt{lvl}\,\mathrm{BTBO}+1$ 为假), `Sβ-fails` ($\beta=\mathtt{lvl}\,\gamma'_1$) |
| $X_3$ 的证书 | 无 (Stage2Label §11) | **`GX₃`**, `X₃ᶠ` |
| 关系式标签 | `Lab₁` (第 $\le1$ 层), `LabG` (无闭包行) | `LabS` (`LabG` + `gŝ`), 第 $j$ 层分支收含闭包的输入 |
| 不带前缀的 $\psi_w$ | `PsiG₊` | `PsiS₊` (+ `gŝ` 逐点) |
| 带前缀的 $\psi_w$ | `Pre1` ($w=1$, 参数 `H₀`/`Hθ`) | **`PreS₊`** (任意带 `Idx` 的 $w\ne0$), `popS`, `giPre` |
| 带前缀的 $\psi_0$ | `Pre0` (尾巴第 $\le1$ 层) | **`Pre0V`/`Pre0S₊`** (任意层; `foldLab` 处理节点层 $\ge1$) |
| $X_3$ 的标签 | 无 | **`X₃-label : Lab X₃ᶠ X₃ᵗ`** |

## §13 结论与边界

**字面成立 (`refl`):** `Bound` 第 0 层的 `Dom` 与 UniformS 的定义性相同 (`popDom₀` 直接复用); 弹栈闭包的形状 (`popS` 的类型检查); `toLevel (natᶜ 3) (natᶜ-HS 3)` 归约为 `three` (`StrictN 3` 的类型即 `Strictᵝ three`); `fsT (ΩΩ ∷ y ∷ ys) η ≡ ΩΩ ∷ fsT (y ∷ ys) η` 与 `pred`/`cof` 的同类等式 (带前缀的引理全靠它们定义性成立); $t_2$ 到 $X_3$ 的路径.

**定理 (模 $\cong$; 标签按 Correspond 的 `Lab`):**

1. `Bound β`: `Good`, `Good→Goodᶻ`, 搬运, `Good-Ω`, `Good-add`, `Good-ψ0`, `popGood`/`popDom`; `Clos Sβ`: `Dom-ψ1`, **`Good-ψ1`**.
2. 严格性: `StrictN`, `Strict-BTBO`; 否定 **`Sβ-fails⁺`**, `Sβ-fails`.
3. **`GX₃ : Goodᶻ (toZ X₃ˢ)`**.
4. `LabS` 及其搬运、`LabS-Ω`、`SSum₊`/`SRep`, `giPsiS`, `PsiAS`/`PsiVS`/`PsiS₊`; `popS`, `giPre`, `PreAS`/`PreVS`/**`PreS₊`**; `z≺I`, `foldLab`, **`Pre0V`/`Pre0S₊`**.
5. **`X₃-label : Lab X₃ᶠ X₃ᵗ`**.

**标签状态.** $\psi_0(\Omega_\Omega+\Omega_3)$: 定理 (本文). 同一套引理对任意带标签的 $\Omega$-下标 $\theta$ 给出 $\psi_0(\Omega_\Omega+\Omega_\theta)$ 的标签, **只要该计值树有证书**, 且 $\psi_0(\Omega_\Omega+\Omega_\theta)$ 是标准形 (Omega2 的 `lab-g`). 证书一侧本文只到环境层号 $\sqsubseteq\mathtt{lvl}\,\mathrm{BTBO}$.

**边界.**

- `Bound` 的界是**全局**的: 同一个 `Good` 推导里一切非零层闭包共用 $\beta$, 而 `Strictᵝ` 要求一切 $\psi^{[\hat\Omega]}_0$ 输出 $\sqsupseteq\beta$, 恰好只到 $\mathtt{lvl}\,\mathrm{BTBO}$ (`Strict-BTBO` 与 `Sβ-fails⁺`). $\gamma'_2$ 的证书因此不在本文范围内 (Omega2 §5).
- `LabS` 与 `Lab` 同样只对树的字面构造子归纳, 穿透处显式搬运; 结论 `Lab` 模 $\cong$.
- 工程注记: 照抄 UniformS §9 的全部引理报 `[ClashingDefinition] Multiple definitions of back-mono`, 只复制依赖 `Good` 的部分; 局部名 `lt` 与 EBO 的构造子 `lt` 冲突 (`[ClashingDefinition] Multiple definitions of lt`), 改名 `bl<`.
- 不改 `src/`、`archive/` 与已有的 Align 文件, README 未改.
