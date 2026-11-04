> **机械克隆, 验收用.** 由 `ScafLadderZDecouple` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.

> **机械克隆.** 由 `Decouple` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 证书与标签的解耦: $\psi_0(\Omega_\Omega+\Omega_2)$ 的遗传标签

> 接 [Stage2Label](Stage2Label.lagda.md) §9–§11 与 [DecoupleBase](DecoupleBase.lagda.md). Stage2Label 造出了 $X_2=\psi_0(\Omega_\Omega+\Omega_2)$ 的计值树 `X₂ᶠ` 与证书 `GX₂`, 但遗传标签只到第 0 项, 停在 "带前缀的 `Generic`" 与 "沿 $A$ 的链的阶段归纳" 两处, 并为步骤 2 记下证书与标签沿链互相依赖的环. 本文的任务是拆开这个环并得到 `Lab X₂ᶠ X₂ᵗ`.
>
> 结论先说:
>
> 1. **`X₂-label : Lab X₂ᶠ X₂ᵗ` 是定理 (§9).** 树是 Stage2Label 的 `X₂ᶠ = force (toZ X₂ˢ) GX₂`, 记号是 Symbolic 的 `X₂ᵗ`. 按 [probes/README](../../README.md) 的认证准则: 符号树族上 $\psi_0(\Omega_\Omega+\Omega_2)$ 的计值树的 FGH 在任意深度满足 EBO 的递归方程. 推论: Stage2Label 的第一个缺口 $X_2[1]$, 它的后代 $A=\psi_0(\Omega_\Omega+\psi_1(\Omega_\Omega))$ 与 $A[1]=\psi_0(\Omega_\Omega+\psi_1(\Omega_{\eta_1}))$ (`A-label`, `A1-label`) 都带标签; Symbolic 的 `PB` 路径的终点 $\cong$ `BTBOᴵ` (`B-end`, Stage2Label §6 只有纸面论证).
> 2. **R1 与 R2 (§1).** 对 $X_2$, 证书一侧没有环: `GX₂` 已证一切闭包的界 $\le2$ (数值核对: 深度 13 的 46 万个后代里, 带前缀的节点下标只有 $0,1$). 缺的是标签一侧. **采用 R2 的关系形式**: 标签本身携带它用到的每个下标的标签 (`Idx`: 计值树、证书、`Lab`、标准形), 比较 (`Slt`/`Seq`) 在用到的那一刻由 Stage2Label 的 `Lab-oc` 与 Stage2 的 `Lab-uniq` 现造 (`Ilt`/`Ieq`). 不需要 `Generic`、下标系统 `System`、公共上界 `A`, 也不需要沿链的阶段 `St k`: 链点的标签在同一个结构递归里逐点前进. **R1 不采用**, 精确原因: 句法一半成立 (对 $X_2$ 平凡, 一般地是 `NF₁` 上的 Bachmann 性质加 `cofin₁`), 树的一半 ("沿 fs 下降 $\Rightarrow$ 层号 $\prec$") 要求沿下降路径的每一步树都有对应的一步形状, 而这些树是符号族的计值树 (链点), 不是任何翻译的像, 一步形状恰好就是被构造的标签在这条路径上的限制; 没有不经标签的来源.
> 3. **方法 (§2–§8).** 全层级的关系式遗传标签 `LabG` (对符号树的字面构造子归纳; 第 0 层就是 DecoupleBase 的原子; `limᵢ` 行带节点下标的 `Idx` 与层号 $\cong^\mathsf I$ 证据, 分支对一切带下一层 `LabG` 的输入匹配), 定义为对 $\triangleleft$ 的递归 (`Lg`, 同 UniformS 的 `Gd`), 所以分支前提是正的. 上下文引理 `PsiG₊`/`PsiV`/`PsiA`: 不带前缀的 $\psi_w$ 把 `LabG b` 变成 `LabG (ψ_w b)`, 派发由两个 `Idx` 决定 (`giPsi`), 规则 6 的链点标签逐点由递归给出. `LabG-Ω`: 带标签的层号上的 $\Omega$. 于是 DecoupleBase 的两个假设 `H₀`、`Hθ` 成立 (`conv` 把第 1 层的 `LabG` 变回 `Lab₁`).
> 4. **步骤 2 未做 (§11).** $\psi_0(\Omega_\Omega\cdot2)$ 的链点 $\gamma'_2$ 内有界为 3 的闭包, UniformS 的 `Good` 在非零层把支配写死成 `c ⊑ᴵ two`, 那里没有证书, 也就没有计值树可标. 用本文的关系式标签, 环变成良基的顺序归纳 (第 $k+1$ 点的证书要第 $k$ 点及其子层号的标签, 后者来自第 $k$ 点证书之后的 `Pre0`), 但需要以当前链点为界的新 `Good` 与 `Pre0`/`Pre1` 对目标层 $\delta\ge2$ 的推广. `Strictⱼ`、`Lab T2 t2` 未得, `C2-unlabel` 与 Stage2 的 `Q′` 仍开放.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块与 DecoupleBase, 不改任何已有文件.


```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLabZDecouple where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.LadderLabZPrefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; coeˢ; toZ; Ωˢ; addˢ; _+ˢ_; ψᴾ;
  Restrˢ; trˢ; tr⁻ˢ; resˢ; res⁻ˢ; Goodᶻ; force; force-HS)
open Restrˢ
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; γT; sucT; cmpᵀ; Cmp; lt; eq; gt; []<; hd<; tl<; lv<; ar<)
  renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fs-rep; fs-ω; fsT-c1)
open import OCF.Align.Bachmann using (fs-gt; pen→<; gt→≤; gt→<; clash)
open import OCF.Align.Closure using (Pen; fsT₊-pen′)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; NF₁-pred; NF₁-fsn; γ′-NF)
open import OCF.Align.Stage2 using (Lab-uniq; walk; walkᵀ; Lab-walk)
open import OCF.Align.LadderLabZUniformS
open import OCF.Align.LadderLabZStage2Label using (chain0; Lab-oc; X₂ᶠ; GX₂)
open import OCF.Align.LadderLabZDecoupleBase
open import OCF.Align.Symbolic using (X₂ᵗ; Aᵗ)
open import OCF.Align.Label using (BTBO-label)
import OCF.Align.NoCumsum as N
import Data.List
```


## §1 R1 与 R2: 草稿里的检验与选择

**数值核对** (Python 模拟器 `ebo.py`, 宽度 3 的基本列搜索, 脚本在草稿目录 `exp/decouple/`, 不进本文):

| 检验 | 深度 | 项数 | 结果 |
|---|---|---|---|
| C1: 带前缀的节点 $\psi_\delta(\Omega_\Omega+\cdots)$ 的下标 | 13 | 460768 | 只有 $\delta\in\{0,1\}$ |
| C2: 带前缀的 $\psi_1$ 出现在不带前缀的 $\psi_w$ ($w\ne0$) 的参数里 (不算可数子项内部) | 13 | 460768 | 无 |
| C3: 不带前缀的 $\psi_0$ 的参数含 $\Omega_\Omega$ | 12 | 190016 | 无 (与 Stage2Label 的 `Ok` 一致) |
| C4: $\Omega$-下标本身含 $\Omega_\Omega$ (阶段 2 的下标) | 12 | 190016 | 出现; 第一个是 $A[1]=\psi_0(\Omega_\Omega+\psi_1(\Omega_{\eta_1}))$ |
| C5: 带前缀的可数项 (原子) 出现在不带前缀的 $\psi$ 的参数里 | 13 | 460768 | 出现, 嵌套到 10 层, 如 $\psi_0(\Omega_\Omega+\psi_1(\psi_1(\psi_1(\psi_0(\Omega_\Omega+\cdots)))))$ |

C1 说明 $X_2$ 的闭包的界都 $\le2$, Stage2Label 的 `Good-ψ1` (前提 $\ell\sqsubseteq^\mathsf I2$) 已经给出全部证书 (`GX₂`): **对 $X_2$, 证书与标签之间没有环**, 缺的只是标签一侧. C2/C3 决定了结构: 带前缀的部分只在第 0/1 层的骨架上 (DecoupleBase 的 `Pre0`/`Pre1` 处理), 不带前缀的部分以带前缀的可数项为原子 (C5), 以阶段 2 的项为 $\Omega$-下标 (C4).

**R1** (记号定理 + 不经标签的树引理). 句法一半: 对 $X_2$, C1 已使它平凡 ($\delta\le1$ 由 `Strict₁` 给支配); 一般地, "$\delta$ 是界 $\beta$ 的真 fs-后代" 由 `NF₁` 上的 Bachmann 性质与 StandardOmega 的 `cofin₁` 得到 (对任何 $\delta<\beta$). 树的一半要从 "$\delta=\beta[n_1]\cdots[n_r]$" 得到 $\mathtt{lvl}\,\delta\prec^\mathsf I\mathtt{lvl}\,\beta$, 即 $\beta$ 的计值树沿这条路径逐步是 `lim`/`suc` 且第 $n_i$ 项是 $\delta_i$ 的树. Correspond 的 `Ω-shapeω`/`toLevel-≺` 之所以不需要遗传标签, 是因为那里的树是翻译 `⟦_⟧` 的像, 一步形状从翻译的定义读出; 这里 $\beta$ 是规则 6 的链点, 它的树是 `force` 在证书下的计值, 没有翻译可读, 一步形状只能从 $\beta$ 的标签来. 所以 R1 的树引理等价于 $\beta$ 的标签在下降路径上的限制, 不是解耦. (R1 的另一条思路是不经路径、只用单调性: `Strictⱼ` 对 $j\prec^\mathsf I\mathtt{lvl}\,\gamma'_{k-1}$ 归纳, 在 $\mathtt{lvl}\,\gamma'_{k-1}\sqsubseteq^\mathsf Ij\prec^\mathsf I\mathtt{lvl}\,\gamma'_k$ 时由 $\psi^{[\hat\Omega]}_0(\Omega_j)\sqsupseteq\gamma'_k$ 得出. 它在对角的一步 $j=\mathtt{lvl}\,\gamma'_{k-1}$ 断: 要 $\gamma'_k\succ\gamma'_{k-1}$, 即一条跨层的增长引理 $x\sqsubseteq\psi^{[\hat\Omega]}_0(\Omega_{\mathtt{lvl}\,x})$ 的严格版, 本文没有; 而且它只给支配, 不给标签.)

**R2** (同时归纳). 要的东西是: 第 $k+1$ 个链点的形状要用到第 $k$ 个链点及其后代作为下标时的比较. Label 的做法是把 "到目前为止的下标" 打包成 `System` 再实例化 `Generic`; 在符号族上照做需要一个带前缀的 `Generic` 与翻译到公共上界层 $A$ 的树, 而带前缀的折叠 `ψ1` 的证书要环境层号 $\le2$ (`Good-ψ1`), 与 "翻译到大的公共层 $A$" 冲突. 本文改用关系形式: 不翻译, 直接对实际的树陈述标签, 每个 `limᵢ` 行**自带**节点下标的 `Idx`, 比较在派发时由 `Lab-oc` 现造. 上一个链点的标签由递归的上一步给出, 作为下一步分支的 `Idx`/原子传入. 这就是 R2, 且 `Lab-oc` 确实使 `Generic` 的重新参数化完全不必要 (前任的猜测成立, 而且连 `Generic` 本身都不用).

## §2 带标签的下标

`Idx ν`: 一棵第 0 层的计值树、它的证书、`Lab Y ν`、`NF₁ ν`. 层号 `lvI`. **解耦的核心**: 两个带标签下标的序的对应 `Ilt` (由 `Lab-oc`, 对一切 `NF₁` 项) 与 `Ieq` (由 `Lab-uniq`), 不经任何下标系统. 其余是层号种类 (`kd`) 与空下标之间的小引理: 标签为 0 的树字面是 `zero` (`Lab0[]`), 层号为 `zero` 种类的下标是 $0$ (`kdI`), 非零下标的层号非零 (`kdI′`), $w<1\Rightarrow w=0$, 以及 `cmpᵀ (ν+1) w ≡ gt` 且 $w\ne0$ 时 $\nu\ne0$ (`gtν`).

```agda
Idx : T → Set
Idx ν = Σ (Ordᶜ zero) λ Y → Σ (HS Y) λ hY → Lab Y ν × NF₁ ν

lvI : ∀ {ν} → Idx ν → Ordᴵ
lvI (Y , hY , _) = toLevel Y hY

Ilt : ∀ {v u} (Iv : Idx v) (Iu : Idx u) → v <ᵀ u → lvI Iv ≺ᴵ lvI Iu
Ilt (Y , hY , lY , nY) (X , hX , lX , nX) p = toLevel-≺ hY hX (Lab-oc lX nX lY nY p)

Ieq : ∀ {u} (I I′ : Idx u) → lvI I ≅ᴵ lvI I′
Ieq (Y , hY , lY , _) (X , hX , lX , _) = toLevel-≅ hY hX (Lab-uniq lY lX)

Lab0[] : ∀ {ν} → Lab Ord₊.zero ν → ν ≡ []
Lab0[] {ν = []} l = refl
Lab0[] {ν = y ∷ ys} (l0 c e) = ⊥-elim (cof-ne y ys c)
Lab0[] {ν = y ∷ ys} (l1 c () l)
Lab0[] {ν = y ∷ ys} (lω c () h)

kdI : ∀ {ν} (I : Idx ν) → kd (lvI I) ≡ true → ν ≡ []
kdI (Ord₊.zero , hY , lY , nY) k = Lab0[] lY
kdI (Ord₊.suc Y , hY , lY , nY) ()
kdI (Ord₊.lim F , hY , lY , nY) ()
kdI (Ord₊.limᵢ () f , hY , lY , nY) k
kdI (Ord₊.up () x , hY , lY , nY) k

kdI′ : ∀ {ν} (I : Idx ν) → (ν ≡ [] → ⊥) → kd (lvI I) ≡ false
kdI′ (Ord₊.zero , hY , lY , nY) ne = ⊥-elim (ne (Lab0[] lY))
kdI′ (Ord₊.suc Y , hY , lY , nY) ne = refl
kdI′ (Ord₊.lim F , hY , lY , nY) ne = refl
kdI′ (Ord₊.limᵢ () f , hY , lY , nY) ne
kdI′ (Ord₊.up () x , hY , lY , nY) ne

<1→[] : ∀ {w} → w <ᵀ natT 1 → w ≡ []
<1→[] []< = refl
<1→[] (hd< (lv< ()))
<1→[] (hd< (ar< ()))
<1→[] (tl< ())

gtν : ∀ {ν w} → cmpᵀ (sucT ν) w ≡ gt → (w ≡ [] → ⊥) → ν ≡ [] → ⊥
gtν {ν = []} {w = w} em ne refl = ne (<1→[] (gt→< (natT 1) w em))
```


## §3 全层级的关系式遗传标签 `LabG`

`LabG₊ ℓ L<` 以 "下一层的标签" `L<` 为参数 (同 UniformS 的 `Good₊`), 行:

- `gz`/`gs`/`gl`: 字面的 `zero`/`suc`/`lim`.
- `gu`: `up r x`, 用下一层的标签.
- `gi`: `limᵢ q f`, 记号侧 `cof t ≡ cΩ ν`, 带 `I : Idx ν` 与节点层号 $j\cong^\mathsf I$ `lvI I`; 分支对一切带下一层标签 $\eta$ 的输入 $x$ 匹配 $t[\eta]$.
- `gĉ`: 待计值链 (原子浮上来的), 同 DecoupleBase 的 `lĉ`.

`LvG i L`: 第 0 层是原子 (DecoupleBase 的 `Atom`), 非零层是 `LabG₊`. `Lg` 对 $\triangleleft$ 的证明递归 (同 `Gd`), `LabG x t = LvG ℓ Lg x t`. 停机与正性一次通过 (`Lg` 不应用地出现在 `LvG` 的参数里, 与 `Gd` 出现在 `Good₊` 的参数里一样被接受). 名字 `Lv` 与 UniformS 的冲突 (`[ClashingDefinition] Multiple definitions of Lv`), 改名 `LvG`.

```agda
module _ (ℓ : Ordᴵ) (L< : (j : Ordᴵ) (r : j ◃ ℓ) → Uˢ j r → T → Set) where
  data LabG₊ : Ordˢ ℓ → T → Set where
    gz : ∀ {t} → cof t ≡ c0 → LabG₊ Ord₊ˢ.zero t
    gs : ∀ {t y} → cof t ≡ c1 → LabG₊ y (pred t) → LabG₊ (Ord₊ˢ.suc y) t
    gl : ∀ {t} {F : ℕ → Ordˢ ℓ} → cof t ≡ cω → (∀ n → LabG₊ (F n) (fsn t n)) → LabG₊ (Ord₊ˢ.lim F) t
    gu : ∀ {t k} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} → L< k (◃₁→◃ r) x t → LabG₊ (Ord₊ˢ.up r x) t
    gi : ∀ {t ν j} {q : j <ᴵ ℓ} {f : Uˢ j (<→◃ q) → Ordˢ ℓ} → cof t ≡ cΩ ν → (I : Idx ν) → j ≅ᴵ lvI I →
         (∀ η (x : Ordˢ j) → L< j (<→◃ q) (intoˢ (<→◃ q) x) η → LabG₊ (f (intoˢ (<→◃ q) x)) (fsT t η)) →
         LabG₊ (Ord₊ˢ.limᵢ q f) t
    gĉ : ∀ {t c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {o₀ : Ordˢ ℓ} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} → cof t ≡ cω →
         (∀ (K : CC c t₀ g) → LabG₊ o₀ (fsn t 0)) →
         (∀ (K : CC c t₀ g) k → LabG₊ (o (lvK K k) (dxK K k)) (fsn t (suc k))) →
         LabG₊ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) t

LvG : (i : Ordᴵ) → ((j : Ordᴵ) (r : j ◃ i) → Uˢ j r → T → Set) → Ordˢ i → T → Set
LvG zero      L x t = Atom x t
LvG (suc i)   L x t = LabG₊ (suc i) L x t
LvG (lim f s) L x t = LabG₊ (lim f s) L x t

Lg : ∀ {ℓ} (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → T → Set
Lg i zero         x t = LvG i Lg x t
Lg i (suc r)      x t = Lg i r x t
Lg _ (self {f} n) x t = LvG (f n) Lg x t
Lg i (lim n r)    x t = Lg i r x t

LabG : ∀ {ℓ} → Ordˢ ℓ → T → Set
LabG {ℓ} x t = LvG ℓ Lg x t
```


`Lg→`/`→Lg`: 沿 $\triangleleft$ 证明的换包装 (同 `Gd→Good`). `toG₊`/`frG₊`: 非零层上 `LabG` 就是 `LabG₊`. `Atom-≅`: 原子沿 $\cong^\mathsf s$ 搬运.

```agda
Lg→ : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordˢ i} {t} → Lg i r (intoˢ r x) t → LabG x t
Lg→ zero      h = h
Lg→ (suc r)   h = Lg→ r h
Lg→ (self n)  h = h
Lg→ (lim n r) h = Lg→ r h

→Lg : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordˢ i} {t} → LabG x t → Lg i r (intoˢ r x) t
→Lg zero      h = h
→Lg (suc r)   h = →Lg r h
→Lg (self n)  h = h
→Lg (lim n r) h = →Lg r h

toG₊ : ∀ {i} {x : Ordˢ i} {t} → kd i ≡ false → LabG x t → LabG₊ i Lg x t
toG₊ {i = zero}    () h
toG₊ {i = suc _}   k h = h
toG₊ {i = lim _ _} k h = h

frG₊ : ∀ {i} {x : Ordˢ i} {t} → kd i ≡ false → LabG₊ i Lg x t → LabG x t
frG₊ {i = zero}    () h
frG₊ {i = suc _}   k h = h
frG₊ {i = lim _ _} k h = h

Atom-≅ : ∀ {x y : Ordˢ zero} {θ} → Atom x θ → y ≅ˢ x → Atom y θ
Atom-≅ (ex , G , l) d = ≅ˢ-reflˡ d , Goodᶻ-tr (toZ-≅ (≅ˢ-sym d)) G , Lab-≅ (force-≅ (toZ-≅ d) _ G) l
```


## §4 沿 $\cong^\mathsf I$ 搬运

穿透时分支的输入要经 `tr⁻ˢ` 换层 (Level §4), 所以标签要能搬运. 四重互递归照 UniformS 的 `Good-tr`/`Good-tr⁻`/`Good-back`/`Good-back⁻`: 第 0 层是原子 (由 $\cong^\mathsf s$), `gi` 行的新节点层号是 `repˢ`, 与旧的差 `eqˢ`, 分支输入经 `backˢ` 回到旧层. 停机由 ($\cong^\mathsf I$ 证明, 推导) 的字典序, 检查器自己找到. 工程注记: 隐式参数在显式参数之后时要写 `G-tr e {t = t} (gi …)`, 写在前面报 `[WrongHidingInLHS] Unexpected implicit argument`.

```agda
LabG-tr    : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ a} {t} → LabG x t → LabG (trˢ e x) t
LabG-tr⁻   : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ b} {t} → LabG x t → LabG (tr⁻ˢ e x) t
LabG-back  : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} {t} → LabG u t → LabG (backˢ (resˢ q e) u) t
LabG-back⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} {t} → LabG u t → LabG (backˢ (res⁻ˢ q e) u) t
G-tr  : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ a} {t} → LabG₊ a Lg x t → LabG₊ b Lg (trˢ e x) t
G-tr⁻ : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ b} {t} → LabG₊ b Lg x t → LabG₊ a Lg (tr⁻ˢ e x) t

LabG-tr z≅ at = Atom-≅ at (trˢ-≅ z≅ (proj₁ at))
LabG-tr (s≅ e) h = G-tr (s≅ e) h
LabG-tr (l≅ k) h = G-tr (l≅ k) h
LabG-tr⁻ z≅ at = Atom-≅ at (tr⁻ˢ-≅ z≅ (proj₁ at))
LabG-tr⁻ (s≅ e) h = G-tr⁻ (s≅ e) h
LabG-tr⁻ (l≅ k) h = G-tr⁻ (l≅ k) h

G-tr e (gz c)   = gz c
G-tr e (gs c h) = gs c (G-tr e h)
G-tr e (gl c h) = gl c (λ n → G-tr e (h n))
G-tr (s≅ e) (gu {r = zero} h)   = gu (LabG-tr e h)
G-tr (l≅ k) (gu {r = self n} h) = gu (LabG-tr (k n) h)
G-tr e {t = t} (gi {q = q} {f = f} c I ej h) =
  gi c I (≅ᴵ-trans (≅ᴵ-sym (eqˢ (resˢ q e))) ej)
     (λ η x l → subst (λ v → LabG₊ _ Lg (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) v)))) (fsT t η))
                      (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) x))
                      (G-tr e (h η (backˢ (resˢ q e) x) (→Lg (<→◃ q) (LabG-back q e (Lg→ (<→◃ (ltˢ (resˢ q e))) l))))))
G-tr e (gĉ c h₀ hk) = gĉ c (λ K → G-tr e (h₀ K)) (λ K k → G-tr e (hk K k))

G-tr⁻ e (gz c)   = gz c
G-tr⁻ e (gs c h) = gs c (G-tr⁻ e h)
G-tr⁻ e (gl c h) = gl c (λ n → G-tr⁻ e (h n))
G-tr⁻ (s≅ e) (gu {r = zero} h)   = gu (LabG-tr⁻ e h)
G-tr⁻ (l≅ k) (gu {r = self n} h) = gu (LabG-tr⁻ (k n) h)
G-tr⁻ e {t = t} (gi {q = q} {f = f} c I ej h) =
  gi c I (≅ᴵ-trans (≅ᴵ-sym (eqˢ (res⁻ˢ q e))) ej)
     (λ η x l → subst (λ v → LabG₊ _ Lg (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) v)))) (fsT t η))
                      (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) x))
                      (G-tr⁻ e (h η (backˢ (res⁻ˢ q e) x) (→Lg (<→◃ q) (LabG-back⁻ q e (Lg→ (<→◃ (ltˢ (res⁻ˢ q e))) l))))))
G-tr⁻ e (gĉ c h₀ hk) = gĉ c (λ K → G-tr⁻ e (h₀ K)) (λ K k → G-tr⁻ e (hk K k))

LabG-back zero      (s≅ e) h = LabG-tr⁻ e h
LabG-back (suc q)   (s≅ e) h = LabG-back q e h
LabG-back (lim n q) (l≅ k) h = LabG-back q (k n) h

LabG-back⁻ zero      (s≅ e) h = LabG-tr e h
LabG-back⁻ (suc q)   (s≅ e) h = LabG-back⁻ q e h
LabG-back⁻ (lim n q) (l≅ k) h = LabG-back⁻ q (k n) h
```


## §5 带标签的层号上的 $\Omega$

`LabG-Ω`: 若 $Y$ 带标签 $\theta$ 且 $a\cong^\mathsf I$ `toLevel Y`, 则 $\Omega_a$ (`Ωˢ a`) 带标签 $\Omega_\theta$. 对 $Y$ 递归: $Y=0$ 时 $\theta=0$, $\Omega_0=1$ 是原子; $Y$ 后继时 $\Omega_a$ 是 `limᵢ zero (up zero)`, `gi` 行的 `Idx` 是 $(Y', \theta-1)$, 分支 `up zero x` 匹配 $\Omega_\theta[\eta]=\eta$ (Correspond 的 `fsT-c1`); $Y$ 极限时 $\Omega_a$ 是 `lim`, 第 $n$ 项递归, 记号侧 $\Omega_\theta[n]=\Omega_{\theta[n]}$ (EBO 的 `fsn0-eq`). 层号证据 $a\cong^\mathsf I$ `toLevel Y` 对 `z≅`/`s≅`/`l≅` 的匹配使 $a$ 字面有正确的头.

```agda
LabG-Ω : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → ∀ {a} → a ≅ᴵ toLevel Y hY → LabG (Ωˢ a) (Ωt θ)
LabG-Ω {θ = []} Ord₊.zero hY l nθ z≅ = Ωˢ-refl zero , Goodᶻ.gs Goodᶻ.gz , l1 refl (s≅ z≅) (l0 refl z≅)
LabG-Ω {θ = y ∷ ys} Ord₊.zero hY l nθ z≅ with Lab0[] l
... | ()
LabG-Ω {θ = θ} (Ord₊.suc Y) hY (l0 c ()) nθ (s≅ e)
LabG-Ω {θ = θ} (Ord₊.suc Y) hY (lω c () h) nθ (s≅ e)
LabG-Ω {θ = []} (Ord₊.suc Y) hY (l1 () (s≅ e′) l) nθ (s≅ e)
LabG-Ω {θ = w ∷ ws} (Ord₊.suc Y) hY (l1 c (s≅ e′) l) nθ (s≅ e) =
  gi (cong (E.cofψ0 (w ∷ ws)) c) (Y , hs⁻ hY , Lab-≅ e′ l , NF₁-pred nθ c) e
     (λ η x lx → gu (subst (LabG x) (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) c η)) lx))
LabG-Ω {θ = θ} (Ord₊.lim F) hY (l0 c ()) nθ (l≅ k)
LabG-Ω {θ = θ} (Ord₊.lim F) hY (l1 c () l) nθ (l≅ k)
LabG-Ω {θ = []} (Ord₊.lim F) hY (lω () (l≅ k′) h) nθ (l≅ k)
LabG-Ω {θ = w ∷ ws} (Ord₊.lim F) hY (lω c (l≅ k′) h) nθ (l≅ k) =
  gl (cong (E.cofψ0 (w ∷ ws)) c)
     (λ n → gu (subst (LabG _) (sym (E.fsn0-eq w ws n c))
                      (LabG-Ω (F n) (hl₁ hY n) (Lab-≅ (k′ n) (h n)) (NF₁-fsn nθ c n) (k n))))
LabG-Ω (Ord₊.limᵢ () f) hY l nθ e
LabG-Ω (Ord₊.up () x) hY l nθ e
```


## §6 和

规则 4 的 $\psi_w(b)\cdot n$ 与穿透后分支里的和: 加法只动尾巴. 尾巴在第 0 层时是原子, 经 DecoupleBase 的 `atomL` 变成 `Lab₁` 再逐行 (`GSumA`); 其余对尾巴的 `LabG₊` 归纳 (`GSum₊`, `gu` 换 `Sim` 下到下一层, 经 `GSum` 按层号种类分派).

```agda
GSumA : ∀ {ℓ} {a : Ordˢ ℓ} {σ : Simᴵ zero ℓ} {b : Ordˢ zero} {x ys} → LabG₊ ℓ Lg a (x ∷ []) → Lab₁ b ys →
        LabG₊ ℓ Lg (addˢ a σ b) (x ∷ ys)
GSumA {ys = []} la (lz c) = la
GSumA {ys = y ∷ ys} la (lz c) = ⊥-elim (cof-ne y ys c)
GSumA {ys = []} la (ls () l)
GSumA {ys = y ∷ ys} la (ls c l) = gs c (GSumA la l)
GSumA {ys = []} la (ll () h)
GSumA {ys = y ∷ ys} la (ll c h) = gl c (λ n → GSumA la (h n))
GSumA la (lu {r = ()} l)
GSumA la (li {q = ()} c h)
GSumA la (lŝ () c h₀ hg)
GSumA {ys = []} la (lŝ₀ () h₀ hk)
GSumA {ys = y ∷ ys} la (lŝ₀ c h₀ hk) = gĉ c (λ K → GSumA la (h₀ K)) (λ K m → GSumA la (hk K m))
GSumA {ys = []} la (lĉ () h₀ hk)
GSumA {ys = y ∷ ys} la (lĉ c h₀ hk) = gĉ c (λ K → GSumA la (h₀ K)) (λ K m → GSumA la (hk K m))

GSum  : ∀ {k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} {x ys} → LabG₊ ℓ Lg a (x ∷ []) → LabG b ys →
        LabG₊ ℓ Lg (addˢ a σ b) (x ∷ ys)
GSum₊ : ∀ {k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} {x ys} → LabG₊ ℓ Lg a (x ∷ []) → LabG₊ k Lg b ys →
        LabG₊ ℓ Lg (addˢ a σ b) (x ∷ ys)
GSum {k = zero} la at = GSumA la (atomL at)
GSum {k = suc _} la h = GSum₊ la h
GSum {k = lim _ _} la h = GSum₊ la h
GSum₊ {ys = []} la (gz c) = la
GSum₊ {ys = y ∷ ys} la (gz c) = ⊥-elim (cof-ne y ys c)
GSum₊ {ys = []} la (gs () h)
GSum₊ {ys = y ∷ ys} la (gs c h) = gs c (GSum₊ la h)
GSum₊ {ys = []} la (gl () h)
GSum₊ {ys = y ∷ ys} la (gl c h) = gl c (λ n → GSum₊ la (h n))
GSum₊ {σ = σ} la (gu {r = zero} h) = GSum {σ = λ q → σ (suc q)} la h
GSum₊ {σ = σ} la (gu {r = self n} h) = GSum {σ = λ q → σ (lim n q)} la h
GSum₊ {ys = []} la (gi () I ej h)
GSum₊ {a = a} {σ = σ} {x = x} {ys = y ∷ ys} la (gi {q = q} {f = f} c I ej h) =
  gi c I ej (λ η w l → subst (λ v → LabG₊ _ Lg (addˢ a σ (f (intoˢ (<→◃ q) v))) (x ∷ fsT (y ∷ ys) η))
                             (sym (out-intoˢ (<→◃ (σ q)) w))
                             (GSum₊ la (h η w (→Lg (<→◃ q) (Lg→ (<→◃ (σ q)) l)))))
GSum₊ {ys = []} la (gĉ () h₀ hk)
GSum₊ {ys = y ∷ ys} la (gĉ c h₀ hk) = gĉ c (λ K → GSum₊ la (h₀ K)) (λ K m → GSum₊ la (hk K m))

GRep : ∀ {ℓ} {P : Ordˢ ℓ} {x} → LabG₊ ℓ Lg P (x ∷ []) → ∀ n → LabG₊ ℓ Lg (iter (P +ˢ_) Ord₊ˢ.zero n) (replicate n x)
GRep lP zero    = gz refl
GRep lP (suc n) = GSum₊ lP (GRep lP n)
```


## §7 派发

`fold0`/`pen0`: 空栈 $\psi^P$ (`ψ0`) 的 `fold⁺`/`pen⁺`. `giPsi`: $\psi_w(b)$ 的 $\Omega_{\nu+1}$ 行, 两个递归调用作为参数 (`rec`: 目标 $i$; `recC`: 链点, 目标 $j$, 要 $j$ 非零), 派发只由两个 `Idx` 决定:

- `cmpᵀ (ν+1) w` 为 `lt`/`eq`: 由 Bachmann 的 `pen→<` 与 `Ilt` 得 $\mathtt{lvI}\,\nu\prec^\mathsf I\mathtt{lvI}\,w$, 搬到 $j\prec^\mathsf Ii$, `pen0` 给出字面的穿透节点, 新节点层号 $j'\cong^\mathsf Ij$, 分支输入经 `LabG-tr⁻`, 记号侧 `fsT₊-pen′`.
- `gt`: Bachmann 的 `gt→≤` 给 $w<\nu$ 或 $w=\nu$, 由 `Ilt`/`Ieq` 得 $i\prec^\mathsf Ij$ 或 $i\cong^\mathsf Ij$, `fold0` 给出字面的规则 6 树; 链点 `chain0` 的标签逐点: 第 0 点 $\Omega_j$ 由 `LabG-Ω`, 第 $m+1$ 点由 `recC` 在第 $m$ 点处 (这就是 "上一阶段的标签给出下一阶段的下标" 的局部形式); 第 $m$ 个输出由 `rec`, 记号侧 Bachmann 的 `fs-gt`. $j$ 非零: $w\ne0$ (目标层非零, `kdI[]`), 由 `gtν` 得 $\nu\ne0$, 由 `kdI′`.

工程注记: 在 `where` 里对父子句的变量 `pn` 做 `with` 报 `[WithOnFreeVariable] Cannot with on variable pn bound in a module telescope (or patterns of a parent clause)`, 改成引理 `cofP`.

```agda
fold0 : ∀ {i k ℓ j} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
        (i ≺ᴵ j) ⊎ (i ≅ᴵ j) → ψ0 p σ (Ord₊ˢ.limᵢ q f) ≡ Ord₊ˢ.lim (λ m → ψ0 p σ (f (intoˢ (<→◃ q) (chain0 σ q f m))))
fold0 {p = p} {σ = σ} {q = q} h with <ᴵ-dec (σ q) p
... | injᵃ s = ⊥-elim (clash s h)
... | injᵇ _ = refl
... | injᶜ _ = refl

pen0 : ∀ {i k ℓ j N} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
       j ≅ᴵ N → N ≺ᴵ i →
       Σ Ordᴵ λ j′ → Σ (j ≅ᴵ j′) λ e → Σ (j′ <ᴵ i) λ r →
       ψ0 p σ (Ord₊ˢ.limᵢ q f) ≡ Ord₊ˢ.limᵢ r (λ y → ψ0 p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) y)))))
pen0 {p = p} {σ = σ} {q = q} ej νi with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = _ , e , r , refl
... | injᵇ s = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ (≺ᴵ-trans νi s) ej))
... | injᶜ c = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ νi (≅ᴵ-trans (≅ᴵ-sym c) ej)))

kdI[] : (I : Idx []) → kd (lvI I) ≡ true
kdI[] (Ord₊.zero , hY , lY , nY) = refl
kdI[] (Ord₊.suc Y , hY , l0 c () , nY)
kdI[] (Ord₊.suc Y , hY , l1 () e l , nY)
kdI[] (Ord₊.suc Y , hY , lω () e h , nY)
kdI[] (Ord₊.lim F , hY , l0 c () , nY)
kdI[] (Ord₊.lim F , hY , l1 () e l , nY)
kdI[] (Ord₊.lim F , hY , lω () e h , nY)
kdI[] (Ord₊.limᵢ () f , hY , lY , nY)
kdI[] (Ord₊.up () x , hY , lY , nY)

cofP : ∀ {w ν} → Pen (cmpᵀ (sucT ν) w) → E.cofψ₊ w ν (cmpᵀ (sucT ν) w) ≡ cΩ ν
cofP {w} {ν} (inj₁ em) = cong (E.cofψ₊ w ν) em
cofP {w} {ν} (inj₂ em) = cong (E.cofψ₊ w ν) em

-- the Ω_{ν+1}-row of ψ_w, given the two recursive calls as oracles
giPsi : ∀ {k ℓ i w ν j y ys} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
        (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
        (rec : ∀ η (x : Ordˢ j) → LabG x η → LabG₊ i Lg (ψ0 p σ (f (intoˢ (<→◃ q) x))) (ψᵗ w (fsT (y ∷ ys) η) ∷ [])) →
        (recC : kd j ≡ false → ∀ η (x : Ordˢ j) → LabG x η →
                LabG₊ j Lg (ψ0 (σ q) σ (f (intoˢ (<→◃ q) x))) (ψᵗ ν (fsT (y ∷ ys) η) ∷ [])) →
        LabG₊ i Lg (ψ0 p σ (Ord₊ˢ.limᵢ q f)) (ψᵗ w (y ∷ ys) ∷ [])
giPsi {i = i} {w = w} {ν = ν} {j = j} {y = y} {ys = ys} {p = p} {σ = σ} {q = q} {f = f} Iw ei ki c Iν ej rec recC =
  go (cmpᵀ (sucT ν) w) refl
  where
  pen : Pen (cmpᵀ (sucT ν) w) → LabG₊ i Lg (ψ0 p σ (Ord₊ˢ.limᵢ q f)) (ψᵗ w (y ∷ ys) ∷ [])
  pen pn with pen0 {p = p} {σ = σ} {q = q} {f = f} (≅ᴵ-refl j)
                   (≺ᴵ-respʳ (≺ᴵ-respˡ ej (Ilt Iν Iw (pen→< ν w pn))) (≅ᴵ-sym ei))
  ... | j′ , e , r , eqn =
    subst (λ W → LabG₊ i Lg W (ψᵗ w (y ∷ ys) ∷ [])) (sym eqn)
          (gi cofE Iν (≅ᴵ-trans (≅ᴵ-sym e) ej)
              (λ η x l → subst (λ v → LabG₊ i Lg (ψ0 p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e v)))) (fsT (ψᵗ w (y ∷ ys) ∷ []) η))
                               (sym (out-intoˢ (<→◃ r) x))
                               (subst (LabG₊ i Lg _) (sym (fsT₊-pen′ w (y ∷ ys) ν (cof (y ∷ ys)) c pn η))
                                      (rec η (tr⁻ˢ e x) (LabG-tr⁻ e (Lg→ (<→◃ r) l))))))
    where
    cofE : cof (ψᵗ w (y ∷ ys) ∷ []) ≡ cΩ ν
    cofE = trans (cong (E.cofA w) c) (cofP pn)
  ne-w : w ≡ [] → ⊥
  ne-w refl = tf (trans (sym (kdI[] Iw)) (trans (sym (kd-≅ ei)) ki))
  fold : cmpᵀ (sucT ν) w ≡ gt → LabG₊ i Lg (ψ0 p σ (Ord₊ˢ.limᵢ q f)) (ψᵗ w (y ∷ ys) ∷ [])
  fold em =
    subst (λ W → LabG₊ i Lg W (ψᵗ w (y ∷ ys) ∷ [])) (sym (fold0 {p = p} {σ = σ} {q = q} {f = f} ij))
          (gl (trans (cong (E.cofA w) c) (cong (E.cofψ₊ w ν) em))
              (λ m → subst (LabG₊ i Lg _) (sym (fs-gt w y ys ν c em m)) (rec _ _ (chainL m))))
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
    chainL : ∀ m → LabG (chain0 σ q f m) (γT (y ∷ ys) ν m)
    chainL zero    = LabG-Ω (proj₁ Iν) (proj₁ (proj₂ Iν)) (proj₁ (proj₂ (proj₂ Iν))) (proj₂ (proj₂ (proj₂ Iν))) ej
    chainL (suc m) = frG₊ kj (recC kj _ _ (chainL m))
  go : ∀ m → cmpᵀ (sucT ν) w ≡ m → LabG₊ i Lg (ψ0 p σ (Ord₊ˢ.limᵢ q f)) (ψᵗ w (y ∷ ys) ∷ [])
  go lt em = pen (inj₁ em)
  go eq em = pen (inj₂ em)
  go gt em = fold em
```


## §8 不带前缀的 $\psi_w$ 的上下文引理

`PsiG₊ Iw ei ki : LabG₊ k Lg X b → LabG₊ i Lg (ψ0 p σ X) (ψ_w(b))`: 目标层 $i\cong^\mathsf I$ `lvI Iw` 非零, 环境层号与 `Sim` 任意. 对 `LabG₊` 推导递归: `gz` 是 $\Omega_i$ (`LabG-Ω`), `gs` 是规则 4 (`GRep`), `gl`/`gĉ` 逐项, `gu` 下到下一层 (`PsiV` 按层号种类分派, 第 0 层的原子走 `PsiA`), `gi` 交给 `giPsi`, 两个 oracle 都是对分支 `h η x …` 的直接递归调用 (目标分别是 $(i,w)$ 与 $(j,\nu)$). 与 DecoupleBase §4 同样, oracle 写法让每个递归调用都落在模式子项上.

```agda
PsiA : ∀ {ℓ i w} {p : i <ᴵ ℓ} {σ : Simᴵ zero ℓ} {X : Ordˢ zero} {b} (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
       Lab₁ X b → LabG₊ i Lg (ψ0 p σ X) (ψᵗ w b ∷ [])
PsiA {b = []} (Y , hY , lY , nY) ei ki (lz c) = toG₊ ki (LabG-Ω Y hY lY nY ei)
PsiA {b = y ∷ ys} Iw ei ki (lz c) = ⊥-elim (cof-ne y ys c)
PsiA {b = []} Iw ei ki (ls () l)
PsiA {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (ls c l) =
  gl (cong (E.cofA w) c) (λ n → subst (LabG₊ _ Lg _) (sym (fs-rep w y ys c n)) (GRep (PsiA {p = p} {σ = σ} Iw ei ki l) n))
PsiA {b = []} Iw ei ki (ll () h)
PsiA {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (ll c h) =
  gl (cong (E.cofA w) c) (λ n → subst (LabG₊ _ Lg _) (sym (fs-ω w y ys c n)) (PsiA {p = p} {σ = σ} Iw ei ki (h n)))
PsiA Iw ei ki (lu {r = ()} l)
PsiA Iw ei ki (li {q = ()} c h)
PsiA Iw ei ki (lŝ () c h₀ hg)
PsiA {b = []} Iw ei ki (lŝ₀ () h₀ hk)
PsiA {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (lŝ₀ c h₀ hk) =
  gĉ (cong (E.cofA w) c) (λ K → subst (LabG₊ _ Lg _) (sym (fs-ω w y ys c 0)) (PsiA {p = p} {σ = σ} Iw ei ki (h₀ K)))
     (λ K m → subst (LabG₊ _ Lg _) (sym (fs-ω w y ys c (suc m))) (PsiA {p = p} {σ = σ} Iw ei ki (hk K m)))
PsiA {b = []} Iw ei ki (lĉ () h₀ hk)
PsiA {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (lĉ c h₀ hk) =
  gĉ (cong (E.cofA w) c) (λ K → subst (LabG₊ _ Lg _) (sym (fs-ω w y ys c 0)) (PsiA {p = p} {σ = σ} Iw ei ki (h₀ K)))
     (λ K m → subst (LabG₊ _ Lg _) (sym (fs-ω w y ys c (suc m))) (PsiA {p = p} {σ = σ} Iw ei ki (hk K m)))

PsiV  : ∀ {k ℓ i w} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {X : Ordˢ k} {b} (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
        LabG X b → LabG₊ i Lg (ψ0 p σ X) (ψᵗ w b ∷ [])
PsiG₊ : ∀ {k ℓ i w} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {X : Ordˢ k} {b} (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
        LabG₊ k Lg X b → LabG₊ i Lg (ψ0 p σ X) (ψᵗ w b ∷ [])
PsiV {k = zero}    {p = p} {σ = σ} Iw ei ki at = PsiA {p = p} {σ = σ} Iw ei ki (atomL at)
PsiV {k = suc _}   {p = p} {σ = σ} Iw ei ki h  = PsiG₊ {p = p} {σ = σ} Iw ei ki h
PsiV {k = lim _ _} {p = p} {σ = σ} Iw ei ki h  = PsiG₊ {p = p} {σ = σ} Iw ei ki h

PsiG₊ {b = []} (Y , hY , lY , nY) ei ki (gz c) = toG₊ ki (LabG-Ω Y hY lY nY ei)
PsiG₊ {b = y ∷ ys} Iw ei ki (gz c) = ⊥-elim (cof-ne y ys c)
PsiG₊ {b = []} Iw ei ki (gs () l)
PsiG₊ {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gs c l) =
  gl (cong (E.cofA w) c) (λ n → subst (LabG₊ _ Lg _) (sym (fs-rep w y ys c n)) (GRep (PsiG₊ {p = p} {σ = σ} Iw ei ki l) n))
PsiG₊ {b = []} Iw ei ki (gl () h)
PsiG₊ {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gl c h) =
  gl (cong (E.cofA w) c) (λ n → subst (LabG₊ _ Lg _) (sym (fs-ω w y ys c n)) (PsiG₊ {p = p} {σ = σ} Iw ei ki (h n)))
PsiG₊ {p = p} {σ = σ} Iw ei ki (gu {r = zero} h)   = PsiV {p = p} {σ = λ q → σ (suc q)} Iw ei ki h
PsiG₊ {p = p} {σ = σ} Iw ei ki (gu {r = self n} h) = PsiV {p = p} {σ = λ q → σ (lim n q)} Iw ei ki h
PsiG₊ {b = []} Iw ei ki (gi () Iν ej h)
PsiG₊ {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gi {q = q} {f = f} c Iν ej h) =
  giPsi {p = p} {σ = σ} {q = q} {f = f} Iw ei ki c Iν ej
        (λ η x l → PsiG₊ {p = p} {σ = σ} Iw ei ki (h η x (→Lg (<→◃ q) l)))
        (λ kj η x l → PsiG₊ {p = σ q} {σ = σ} Iν ej kj (h η x (→Lg (<→◃ q) l)))
PsiG₊ {b = []} Iw ei ki (gĉ () h₀ hk)
PsiG₊ {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gĉ c h₀ hk) =
  gĉ (cong (E.cofA w) c) (λ K → subst (LabG₊ _ Lg _) (sym (fs-ω w y ys c 0)) (PsiG₊ {p = p} {σ = σ} Iw ei ki (h₀ K)))
     (λ K m → subst (LabG₊ _ Lg _) (sym (fs-ω w y ys c (suc m))) (PsiG₊ {p = p} {σ = σ} Iw ei ki (hk K m)))
```


## §9 两个假设与 $X_2$ 的标签

`conv`: 第 1 层的 `LabG₊` 就是 `Lab₁` (节点层号 $<1$ 只能字面为 `zero`, 由 `kdI` 节点下标是 $0$, `gi` 变成 `li`; 第 0 层的原子经 `atomL`). `Hθ′`: 对任意带标签的 $Y$ (标签 $\theta$, 标准形), $\psi_1(\Omega_{\mathtt{toLevel}\,Y})$ 带 $\psi_1(\Omega_\theta)$ 的 `Lab₁`: 目标下标 $1$ 的 `Idx` 是 `I1`, 参数由 `LabG-Ω`, 主体由 `PsiV`. 不需要 DecoupleBase 里的前提 $\theta>1$. `H₀` 是 $\theta=1$. 代入 DecoupleBase 的 `Pre1M`:

```agda
conv : ∀ {X : Ordˢ one} {t} → LabG₊ one Lg X t → Lab₁ X t
conv (gz c)   = lz c
conv (gs c h) = ls c (conv h)
conv (gl c h) = ll c (λ n → conv (h n))
conv (gu {r = zero} at) = lu (atomL at)
conv (gi {q = zero} c I ej h) = li (trans c (cong cΩ (kdI I (sym (kd-≅ ej))))) (λ θ x at → conv (h θ x at))
conv (gi {q = suc ()} c I ej h)
conv (gĉ c h₀ hk) = lĉ c (λ K → conv (h₀ K)) (λ K m → conv (hk K m))

one⁰ : Ordᶜ zero
one⁰ = suc zero

I1 : Idx (natT 1)
I1 = one⁰ , hs hz , l1 refl (s≅ z≅) (l0 refl z≅) , γ′-NF 0

Hθ′ : ∀ θ (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ →
      ∀ {ℓ} (p : one <ᴵ ℓ) (σ : Simᴵ (toLevel Y hY) ℓ) → Lab₁ (ψ0 p σ (Ωˢ (toLevel Y hY))) (ψ₁Ω θ)
Hθ′ θ Y hY lY nθ p σ = conv (PsiV {p = p} {σ = σ} I1 (≅ᴵ-refl one) refl (LabG-Ω Y hY lY nθ (≅ᴵ-refl _)))

H₀ : ∀ {ℓ} (p : one <ᴵ ℓ) (σ : Simᴵ one ℓ) → Lab₁ (ψ0 p σ (Ωˢ one)) (ψ₁Ω (natT 1))
H₀ p σ = Hθ′ (natT 1) one⁰ (hs hz) (l1 refl (s≅ z≅) (l0 refl z≅)) (γ′-NF 0) p σ

open Pre1M H₀ (λ θ Y hY lY nθ _ → Hθ′ θ Y hY lY nθ) public using (Pre1; X₂-label)
```


**定理 `X₂-label : Lab X₂ᶠ X₂ᵗ`** (上面 `open Pre1M … public` 导出). 类型检查器核对的就是这个陈述:

```agda
_ : Lab X₂ᶠ X₂ᵗ
_ = X₂-label
```


**推论.** `Lab-walk` (Stage2) 把标签沿基本列路径传下去. Stage2Label §9 的两个缺口: $A=X_2[1][0][1]=\psi_0(\Omega_\Omega+\psi_1(\Omega_\Omega))$ (Symbolic 的 `X₂-at-A`) 与 $A[1]=\psi_0(\Omega_\Omega+\psi_1(\Omega_{\eta_1}))$. Symbolic 的 `B0-unlabel` 的路径 (静态前缀的树在终点是 `zero`): 计值树在终点带 $\psi_0(\Omega_\Omega)$ 的标签, 由 `Lab-uniq` 与 Label 的 `BTBO-label`, 终点 $\cong$ `BTBOᴵ`; Stage2Label §6 只编译了 "终点非零", "$\cong$ BTBO" 是纸面的.

```agda
pathB : List _
pathB = 2 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

_ : walkᵀ X₂ᵗ pathB ≡ E.EBOψ 2
_ = refl

B-end : walk X₂ᶠ pathB ≅ N.BTBOᴵ
B-end = Lab-uniq (Lab-walk pathB X₂-label (refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , tt)) BTBO-label

pathA : List _
pathA = 1 ∷ 0 ∷ 1 ∷ []

A-label : Lab (walk X₂ᶠ pathA) Aᵗ
A-label = Lab-walk pathA X₂-label (refl , refl , refl , tt)

A1-label : Lab (walk X₂ᶠ (pathA Data.List.++ (1 ∷ []))) (E.fsn Aᵗ 1)
A1-label = Lab-walk (pathA Data.List.++ (1 ∷ [])) X₂-label (refl , refl , refl , refl , tt)
```


## §10 对比表

| | Stage2Label (§9–§11 的计划) | 本文 |
|---|---|---|
| 证书 | `GX₂` (界 $\le2$) | 不变, 只用 `GX₂` |
| 证书与标签的环 | 预计在 $X_2$ 已出现 | 对 $X_2$ 不存在 (C1); 在 $\psi_0(\Omega_\Omega\cdot2)$ 才出现 (§11) |
| 下标的比较 | 阶段 2 的 `Slt`/`Seq` 来自上一阶段的标签 | 每个 `limᵢ` 行自带 `Idx`, 比较由 `Lab-oc`/`Lab-uniq` 现造 (`Ilt`/`Ieq`) |
| 形状理论 | 带前缀的 `Generic` | 关系式标签 `Lab₁`/`LabG`, 对实际的树递归, 无翻译、无公共上界 |
| 沿链的阶段归纳 | Label 的 `St k` 的阶段 2 版本 | 链点标签逐点前进 (`liBody`, `ŝLab`, `giPsi` 的 `chainL`), 嵌套的链在同一个结构递归里 |
| 原子 (带前缀的可数项进参数) | 未提 | `Atom`, 第 0 层的 `LabG` |
| $X_2$ 的标签 | 第 0 项 `X₂-0` | **`X₂-label : Lab X₂ᶠ X₂ᵗ`** |
| `PB` 终点 | 非零 (`refl`), $\cong$ BTBO 纸面 | `B-end` (定理) |
| R1 | 未评估 | 树的一半不能不经标签 (§1) |
| $\psi_0(\Omega_\Omega\cdot2)$ | 停在链指标 1 | 未做; 障碍精确为 `Dom` 的界与 `Lab₁` 的节点层号 (§11) |

## §11 结论与边界

**字面成立 (`refl`):** `ctx [] ≡ EBOψ 2`; $\psi_1(\Omega_\Omega)[\theta]=\psi_1(\Omega_\theta)$; $X_2$ 的折叠方程 `eqX` (`fold1` 的 `with` 展开); `walkᵀ X₂ᵗ pathB ≡ EBOψ 2`; `Lab-walk` 用到的每个 `cof … ≡ cω`.

**定理 (标签按 Correspond 的 `Lab`, 树只到 $\cong$):**

1. **`X₂-label : Lab X₂ᶠ X₂ᵗ`**, 即 $\psi_0(\Omega_\Omega+\Omega_2)$ 的遗传标签, 树为 Stage2Label 的计值树 (证书 `GX₂`). 推论 `A-label`, `A1-label`, `B-end : walk X₂ᶠ pathB ≅ N.BTBOᴵ`.
2. DecoupleBase: `Pre0` (带前缀的 $\psi_0$, 任意环境层号、`Sim`、证书), `Pre1` (带前缀的 $\psi_1$), `faddᶻ`, `atomL`, `Lab₁-sum`.
3. 本文: `Ilt`/`Ieq` (带标签下标的序的对应), `LabG-tr`/`LabG-tr⁻`/`LabG-back`/`LabG-back⁻`, `LabG-Ω`, `GSum`, `giPsi`, `PsiA`/`PsiV`/`PsiG₊` (不带前缀的 $\psi_w$ 的上下文引理, 目标层非零), `conv`, `Hθ′`, `H₀`.

**标签状态.** $\psi_0(\Omega_\Omega)$, $\psi_0(\Omega_\Omega+1)$, $\psi_0(\Omega_\Omega+\Omega)$: 定理 (此前). **$\psi_0(\Omega_\Omega+\Omega_2)$: 定理 (本文, 符号树族的计值树).** 它的一切基本列后代亦然 (`Lab-walk`). $\psi_0(\Omega_\Omega\cdot2)$: 未得.

**步骤 2 的精确停点.** $t_2=\psi_0(\Omega_\Omega\cdot2)$ 的链点 $\gamma'_2$ 内的 $X_3=\psi_0(\Omega_\Omega+\Omega_3)$ 有界为 3 的闭包 (Stage2Label §11, `refl`). (i) 证书: UniformS 的 `Dom (suc _) c t₀ g = c ⊑ᴵ two` 把非零层闭包的界写死为 $\le2$, 所以 $X_3$ (以及一般的 $\psi^{[\hat\Omega]}_0(\Omega_j)$, $j\prec^\mathsf I\mathtt{lvl}\,\gamma'_k$) 没有 `Good`, 也就没有计值树; 要换成以当前链点为界的支配 (界 $\beta$ 作为参数, 闭包定理 `Good-ψ1` 的前提 $\ell\sqsubseteq^\mathsf I2$ 换成 $\ell\sqsubseteq^\mathsf I\beta$), 是 UniformS §8–§10 与 Stage2Label §3–§5 的一份带参数的拷贝. (ii) 支配的证据 `Strictⱼ` ($\mathtt{lvl}\,\psi^{[\hat\Omega]}_0(\Omega_j)\sqsupseteq^\mathsf Ij+1$): 用本文的工具, 它来自 `Pre0` 给的标签与 `Lab-oc`, 次序是 "第 $k$ 个链点的证书 $\to$ 它与其子层号的标签 ($\mathtt{Pre0}$, `LabG`) $\to$ 第 $k+1$ 个链点里一切界 $\le\mathtt{lvl}\,\gamma'_k+1$ 的闭包的支配 $\to$ 第 $k+1$ 个链点的证书", 是良基的顺序归纳, 不再是环. (iii) 标签: `Lab₁` 的 `li` 行只收节点层号 0 的 `limᵢ` ($\Omega_1$-共尾), `Pre0`/`Pre1` 只处理目标层 0/1 的带前缀节点; $t_2$ 里带前缀的节点下标跑遍 $\mathtt{lvl}\,\gamma'_k$ 的子层号, 需要 `Pre_δ` 对任意带标签的 $\delta$ (同 `PsiG₊` 之于 `PsiA` 的推广). 以上三件都未写; `Strictⱼ`、`Lab T2 t2` 未得, `C2-unlabel` 与 Stage2 的 `Q′` 未解除.

**边界.**

- 关系式标签对树的**字面**构造子归纳, 不对 $\cong^\mathsf s$ 封闭; 需要换层的地方 (穿透的分支) 显式搬运 (§4). 结论 `Lab` 本身模 $\cong$.
- `PsiG₊` 只对非零目标层 (不带前缀的 $\psi_0$ 遇到原子时没有证书一侧的 `Ok`, C3 说 $X_2$ 里不出现).
- §1 的 Python 检验是有界的数值观察, 只用于选择路线, 不作为定理; 定理不依赖它们 (C1 的结论体现为 `GX₂` 的存在, 那是 Stage2Label 的定理).
- 不改 `src/`、`archive/` 与已有的 Align 文件, README 未改.
