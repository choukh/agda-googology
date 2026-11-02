# 树侧的出现不变量 (一): 地板、覆盖与带地板的闭包定理

> 接 [NotFree](NotFree.lagda.md) §6 的判断: $\psi_0(\Omega_\Omega\cdot2)$ 的记号无关证书缺的是**内部闭包的支配**, 现有三种工具都给不出 (全局界 `no-Bound`、值序 `fix-not-strict`、观测前序看不见上下文 `dip`). 缺口被命名为树侧的标准形/出现不变量: "尾巴里出现的层号 $\prec$ 它的 $\psi^{[\hat\Omega]}_0$-折叠的层号" (SystemOmega `occ<` 与 StandardOmega `NF₁` 的 $G$-条件的树版), 逐闭包陈述 (Relative 的 `¬BranchΩ`: 链点会在更低的目标处被重新折叠, 不变量不能按单次计值陈述). 本文 (任务 1–2) 在 Prefix 的符号族 `Ordˢ` 与它的折叠 `ψᴾ` (单 $\hat\Omega$ 栈 `ψ1`, 空栈 `ψ0`) 上定义这个不变量并证明它的保持; [TreeNF](TreeNF.lagda.md) (任务 3–4) 用它得到支配定理与 $t_2$ 的链上的证书.
>
> 结论先说:
>
> 1. **不变量是逐闭包的数据: 覆盖与 (由地板推出的) 支配 (§2–§3).** 非零层闭包 `ŝ c t₀ g` 满足 `Occ≺ᴳ c t₀ g`, 若有层号 $\varphi$ 使得 (i) **覆盖** `CovΛ φ c`: 链点 $\hat\chi_\varphi=\psi^{[\hat\Omega]}_0(\Omega_\varphi)$ 有 Prefix 证书且其层号 $\sqsupseteq^\mathsf Ic$; (ii) **被支配** `ColC c t₀` 与 `∀ η e → ColC c (g η e)`: $c\sqsubseteq^\mathsf I$ 第 0 点 (与各点) 在一切 "目标 0 的单 $\hat\Omega$ 折叠 (外套搬运)" 观测下的计值层号. (ii) 的来源是**地板** `FlΛ φ t` $:=\Omega_\varphi\sqsubseteq^\mathsf o t$: **支配定理 `dom-cov : FlΛ φ t → CovΛ φ c → ColC c t`** (§3), 证明是一次 `ψ1-cong` 加 `toLevel-⊑` (地板在观测前序里把闭包的第 0 点与覆盖它的链点比较). `Dom-of-Occ`: 不变量就是闭包到第 0 层时 `gc` 要的支配. 全部只提到树、`Ordᴵ`、$\sqsubseteq^\mathsf I$、观测前序与 Prefix 证书, 没有记号项; 这是 `Strictᵝ` 被 `no-Bound` 否掉之后需要的 "相对链" 的严格性.
> 2. **保持 (§2–§3).** 地板对弹栈 (`FlΛ-t₀pop`/`FlΛ-gpop`)、空栈与单 $\hat\Omega$ 栈的映射 (`FlΛ-ψ0`/`FlΛ-ψ1`)、带地板前缀的加法 (`FlΛ-add`) 保持, **条件是映射的目标层 $i\sqsupseteq\varphi$**; 地板不从输入继承, 而是由映射者再生 ($\psi_i$ 的一切输出 $\sqsupseteq^\mathsf o\Omega_i$, `B1₀`/`B1₁`). 地板对搬运**不能**陈述 (§2 的编译否定), 所以不变量存地板的推论 `ColC`, 它对搬运定义性地保持. 整体形式 `Occ-pop`/`Occ-ψ1ᴳ`/`Occ-ψ0ᴳ`/`Occ-addᴳ`/`Occ-trᴳ`. 对 $\varphi=1$, 条件对一切非零目标成立 (`one⊑`: 帧证据 $0<^\mathsf I\ell$ 让非零目标 $\sqsupseteq1$), 于是得到无条件的闭包定理 (§4–§5, `Floor β cov`): Omega2Base 的 `Bound β` 把非零层的支配从 "$c\sqsubseteq^\mathsf I\beta$" 换成 `Occ≺ β` ("$c\sqsubseteq^\mathsf I\beta$ 且被 $\beta$ 支配"), 全局假设 `Strictᵝ β` (被 `no-Bound` 否定) 换成覆盖参数 `cov : CovΛ 1 β`. **`Floor.Good-ψ1` 无其他前提.**
> 3. **映射到地板之下是唯一不保持的情形 (§2 末, §3 末).** 目标 $i\prec\varphi$ 的 $\psi_i$ 映射闭包时再生的地板只有 $\Omega_i$, 覆盖不变, 闭包变成 "悬置" 的; 它要等外层分支函数里目标 $\sqsupseteq\varphi$ 的 $\psi_a$ 再次映射才恢复. 这是 `NF₁` 的 `Vis₁` 里 "只看穿下标 $\ge u$ 的节点" (`vs` 规则) 的树侧对应物, 也是 TreeNF 里 $\gamma'_3$ 处的停点.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件. §4–§5 是 Omega2Base §1–§3 (`module Bound`) 的复制, 改动处逐条列在 §4 开头.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeNFBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev; σ1)
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Restrˢ; trˢ; tr⁻ˢ; resˢ; res⁻ˢ;
  Ωˢ; addˢ; _+ˢ_; Goodᶻ; force; force-HS; z<suc)
open Restrˢ
open import OCF.Align.UniformS hiding (Dom; Good₊; Gd; Good; Gd→Good; Good→Gd; Gd-conv; Good→Goodᶻ;
  Dom0-≅; Dom-tr; Dom-tr⁻; Good-tr; Good-tr⁻; Good-back; Good-back⁻; Good-Ω; Good-add; Good-iter;
  bz; bs; bl; bi; bu; bŝ; bĉ)
open import OCF.Align.Stage2Label using (Ok; Ok-Pl; Ok-suc; Ok-lim; Ok-up; Ok-col; Ok-pen; ~ŝ; ~ĉ; Pl-Ω;
  chain0; chain1; chain0-≅; chain1-≅; chain0-step; chain1-step; Strict₀; t₀pop; gpop)
```

## §1 非零目标在 1 之上

`one⊑`: 只要有帧证据 $z:0<^\mathsf I\ell$, 任何非零目标 $i<^\mathsf I\ell$ 都 $\sqsupseteq^\mathsf I1$. 证明是一次有界三歧 (`<ᴵ-dec z p`): $i\prec0$ 不可能, $0\cong^\mathsf Ii$ 迫使 $i$ 字面为 `zero`. 没有公共上界时这不成立: `lim (λ _ → zero)` 是合法的层号, 而 $0\not<^\mathsf I$ 它 (Level 的 $<^\mathsf I$ 是字面子项序). `Mlev⊑`: Symbolic 的公共层号 `Mlev c η e` $=\lim[c,\eta,\eta,\ldots]$ 在 $c,\eta\sqsubseteq\beta$ 时 $\sqsubseteq\beta$; $t_2$ 的链的计值点 $\psi^{[\hat\Omega]}_0(\Omega_\eta)$ 的环境层号就是它.

```agda
NZ : Ordᴵ → Set
NZ zero      = ⊥
NZ (suc _)   = ⊤
NZ (lim _ _) = ⊤

one⊑ : ∀ {i ℓ} → zero <ᴵ ℓ → i <ᴵ ℓ → NZ i → suc zero ⊑ᴵ i
one⊑ z p nz with <ᴵ-dec z p
... | injᵃ r          = s⊑′ r
... | injᵇ (via e ())
... | injᶜ z≅         = ⊥-elim nz

Mlev⊑ : ∀ {c η β} (e : c ⊑ᴵ η) → η ⊑ᴵ β → Mlev c η e ⊑ᴵ β
Mlev⊑ {β = β} e h = l⊑ go
  where
  go : ∀ n → _ ⊑ᴵ β
  go zero    = ⊑ᴵ-trans e h
  go (suc n) = h
```

## §2 地板与它的保持

**定义.** 地板 `FlΛ φ t` $:=\Omega_\varphi\sqsubseteq^\mathsf o t$ (观测前序, UniformS §4: 对一切相似观测与一切证书, 计值后 $\sqsubseteq$). 它是 `Vis₁`/`Bnd₁` 的 "可见" 的树侧形式: 闭包的第 0 点在观测意义上至少是 $\Omega_\varphi$, 所以把它折到第 0 层的任何 $\psi^{[\hat\Omega]}_0$ 都至少是 $\psi^{[\hat\Omega]}_0(\Omega_\varphi)$ (§3). `Fl = FlΛ 1` 是 §4 用的特例.

**保持引理.** 都是 UniformS §7 的 `B1₀`/`B1₁`/`add-r` 的实例, 所以对**任意**输入成立, 只要映射者的目标层 $i\sqsupseteq^\mathsf I\varphi$:

- `FlΛ-ψ0`: $\psi^{[]}_i(y)\sqsupseteq^\mathsf o\Omega_i\sqsupseteq^\mathsf o\Omega_\varphi$ (`B1₀` 以 `Ω-monoᵒ` 为假设).
- `FlΛ-t₀pop`/`FlΛ-gpop`: 弹栈闭包 $\hat s\,(i{+}1)\,\psi^{[]}_i(\Omega_1)\,(\eta\mapsto\psi^{[]}_i(\Omega_\eta))$ 的第 0 点与各点, 是上一条的实例.
- `FlΛ-ψ1`: $\psi^{[\hat\Omega]}_i(y)\sqsupseteq^\mathsf o\psi^{[\hat\Omega]}_i(0)=\hat s\cdots\sqsupseteq^\mathsf o\psi^{[]}_i(\Omega_1)$ (`B1₁` 以 `ŝ-r` 为假设).
- `FlΛ-add`: 前缀 $a$ 有地板则 $a+b$ 有地板. `add-r` 的基本情形是 $a\cong a'$; 这里换成任意 $x\sqsubseteq^\mathsf o a$ (`add-floor`), 其余子句逐字. 注意加法不需要 $b$ 的地板: **前缀提供地板**, 这是 "$\psi_0(\Omega_\Omega+\Omega_{u+1}+\psi_1(\cdots\psi_u\cdots))$ 里前缀 $\Omega_{u+1}$ 把被 $\psi_1$ 压低的 $\psi_u$-闭包重新托起" 的树侧形式 (§6).
- 搬运: **地板不对搬运保持** (见下面的否定), 所以不变量里存的不是地板本身, 而是地板的推论 (§3 的 `ColC`), 后者对搬运定义性地保持.

**`B1₀`/`B1₁` 的隐式参数.** 照 README 的 "折叠引理的隐式 `p`/`σ`/`z` 要写出", 下面全部写出.

```agda
FlΛ : Ordᴵ → ∀ {k} → Ordˢ k → Set
FlΛ φ t = Ωˢ φ ⊑ᵒ t

Fl : ∀ {k} → Ordˢ k → Set
Fl = FlΛ (suc zero)

FlΛ-ψ0 : ∀ {φ i k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} → φ ⊑ᴵ i → (y : Ordˢ k) → y ≅ˢ y → FlΛ φ (ψ0 p σ y)
FlΛ-ψ0 {p = p} {σ = σ} h y ey = B1₀ {q = p} {σ = σ} (Ω-monoᵒ h) y ey

FlΛ-t₀pop : ∀ {φ i ℓ} → φ ⊑ᴵ i → (p : i <ᴵ ℓ) (z : zero <ᴵ ℓ) → FlΛ φ (t₀pop p z)
FlΛ-t₀pop h p z = FlΛ-ψ0 {p = zero} {σ = σ1 (z<suc z p)} h (Ωˢ (suc zero)) (Ωˢ-refl (suc zero))

FlΛ-gpop : ∀ {φ i ℓ} → φ ⊑ᴵ i → (p : i <ᴵ ℓ) (z : zero <ᴵ ℓ) → ∀ η e → FlΛ φ (gpop p z η e)
FlΛ-gpop h p z η e = FlΛ-ψ0 {p = lim 0 zero} {σ = λ q → lim 1 q} h (Ωˢ η) (Ωˢ-refl η)

FlΛ-ψ1 : ∀ {φ i k ℓ} → φ ⊑ᴵ i → (p : i <ᴵ ℓ) (σ : Simᴵ k ℓ) (z : zero <ᴵ ℓ) (y : Ordˢ k) → y ≅ˢ y →
         FlΛ φ (ψ1 p σ z y)
FlΛ-ψ1 h p σ z y ey = B1₁ {q = p} {σ = σ} {z₁ = z} (ŝ-r (FlΛ-t₀pop h p z)) y ey

add-floor : ∀ {k ℓ ℓ₀} {x : Ordˢ ℓ₀} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} (b : Ordˢ k) → x ⊑ᵒ a → b ≅ˢ b → x ⊑ᵒ addˢ a σ b
add-floor Ord₊ˢ.zero h eb = h
add-floor {σ = σ} (Ord₊ˢ.suc b) h eb = suc-r (add-floor {σ = σ} b h (s-invˢ eb))
add-floor {σ = σ} (Ord₊ˢ.lim f) h eb = lim-r 0 (add-floor {σ = σ} (f 0) h (l-invˢ eb 0))
add-floor {x = x} {a = a} {σ = σ} (Ord₊ˢ.limᵢ q g) h eb = limᵢ-r (λ z d →
  subst (λ u → x ⊑ᵒ addˢ a σ (g (intoˢ (<→◃ q) u))) (sym (out-intoˢ (<→◃ (σ q)) z))
        (add-floor {σ = σ} (g (intoˢ (<→◃ q) z)) h (i-respˢ eb (≅ˢ-reflˡ d))))
add-floor {σ = σ} (Ord₊ˢ.up zero y) h eb     = add-floor {σ = λ q → σ (suc q)} y h (u-reflˢ zero eb)
add-floor {σ = σ} (Ord₊ˢ.up (self n) y) h eb = add-floor {σ = λ q → σ (lim n q)} y h (u-reflˢ (self n) eb)
add-floor {k = zero}    {σ = σ} (Ord₊ˢ.ŝ c t₀ g) h eb = ĉ-r (add-floor {σ = σ} t₀ h (ŝ-refl₀ eb))
add-floor {k = suc _}   {σ = σ} (Ord₊ˢ.ŝ c t₀ g) h eb = ŝ-r (add-floor {σ = σ} t₀ h (ŝ-refl₀ eb))
add-floor {k = lim _ _} {σ = σ} (Ord₊ˢ.ŝ c t₀ g) h eb = ŝ-r (add-floor {σ = σ} t₀ h (ŝ-refl₀ eb))
add-floor {σ = σ} (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) h eb = ĉ-r (add-floor {σ = σ} o₀ h (ĉ-refl₀ eb))

FlΛ-add : ∀ {φ k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} (b : Ordˢ k) → FlΛ φ a → b ≅ˢ b → FlΛ φ (addˢ a σ b)
FlΛ-add b h eb = add-floor b h eb

```

**读法.** 每条保持引理的结论都**不读**输入的地板: 一个映射者 ($\psi_i$ 或带地板的前缀) 一旦出现, 它自己就给出地板. 所以地板沿折叠的保持不是 "遗传" 的, 而是 "再生" 的; 唯一要核对的是再生出的地板够不够高 ($i\sqsupseteq\varphi$). 加法读前缀 $a$ 的地板, 不读 $b$ 的.

**否定: 地板对搬运 (编译报错).** 最初的 `FlΛ-tr e et h = ⊑ᵒ-≅ʳ h (≅-trˢ e et)` 报

    [UnequalTerms] b != a of type Ordᴵ
    when checking that the expression ≅-trˢ e et has type t ≅ˢ _y′_516

UniformS 的 `⊑ᵒ-≅ʳ` 只在**同一层**换右端 (中间项的证书要用同一个观测搬过去), 而 $t$ 在层 $a$、`trˢ e t` 在层 $b$. 换成观测的写法也不行: `trˢ e t` 的观测 $O'$ 对应 $t$ 的观测 `tro O′ e`, 而 $\approx^\mathsf o$ 要求两侧同形, 左侧 $\Omega_\varphi$ 的观测不是 `tro`. 所以 "$\Omega_\varphi\sqsubseteq^\mathsf o t\Rightarrow\Omega_\varphi\sqsubseteq^\mathsf o\mathtt{tr}\,e\,t$" 在 $\sqsubseteq^\mathsf o$ 的语言里写不出. §3 的处理: 不变量里只存地板的**推论** "被一切折叠观测支配" (`ColC`), 折叠观测的类 `IsCol` 对搬运观测封闭, 搬运的保持就是定义性的.

**不保持的情形 (纸面, 编译的反面在 TreeNF §3, 路径在 §4).** 目标 $i\prec^\mathsf I\varphi$ 的 $\psi_i$ 映射一个地板为 $\Omega_\varphi$ 的闭包: 再生的地板只有 $\Omega_i$. 在 $\gamma'_3$ 的折叠里这确实发生 (TreeNF §4 的路径): 尾巴 $\Omega_{a+1}$ ($a$ 在 $\mathtt{lvl}\,\gamma'_1$ 与 $\mathtt{lvl}\,\gamma'_2$ 之间) 折叠出链点 $c_1=\psi^{[\hat\Omega]}_a(\Omega_a)$, 其中含界 $a{+}1$ 的弹栈闭包 (地板 $\Omega_a$, 覆盖要 $\varphi=\mathtt{lvl}\,\gamma'_1$); $c_1$ 自己是穿透得到的, 含节点 $d\prec\mathtt{lvl}\,\gamma'_1$ 的 `limᵢ`, 外层 $\psi^{[\hat\Omega]}_0$ 在 $d$ 处折叠出链 $e_{n+1}=\psi^{[\hat\Omega]}_d(\psi^{[\hat\Omega]}_a(e_n))$, 内层闭包被 $\psi_d$ 压到地板 $\Omega_d$, 直到分支函数 $y\mapsto\psi^{[\hat\Omega]}_a(y)$ 再把它托回 $\Omega_a$.

## §3 覆盖、折叠观测与支配定理

**折叠观测.** `IsCol O`: 观测 $O$ 是 "目标 0 的单 $\hat\Omega$ 折叠" (`ψo₁ idO p σ z`, 任意环境、`Sim`、帧证据), 外面套任意多层搬运观测 (`tro`/`tr⁻o`). 闭包在第 0 层被读成链时, `gc` 的支配要的正是它的第 0 点与各点在**这一类**观测下的计值层号; 搬运观测要算进去, 因为闭包可能先被搬运 (穿透分支的 `tr⁻ˢ`) 再被折叠.

**被支配** `ColC c t`: 对一切折叠观测 $O$ 与一切证书, $c\sqsubseteq^\mathsf I\mathtt{lvl}(\mathrm{run}\,O\,t)$. 它对搬运定义性地保持 (`ColC-tr`: `run O (trˢ e t)` 字面就是 `run (tro O e) t`).

**覆盖** `CovΛ φ c`: 链点 $\hat\chi_\varphi=\psi^{[\hat\Omega]}_0(\Omega_\varphi)$ (环境层号 `Mlev 1 φ e`; 与 Omega2 的 `gᵗ φ e` 字面相同) 有一张 Prefix 证书, 且其计值的层号 $\sqsupseteq^\mathsf Ic$.

**支配定理 `dom-cov`.** 地板 $\Omega_\varphi\sqsubseteq^\mathsf ot$ 加覆盖 $\varphi\vdash c$ 推出 `ColC c t`. 证明: 对折叠观测 $O$ 造一个同形的观测 `canΛ φ e` 作用在 $\Omega_\varphi$ 上 (最内层换成 $\hat\chi_\varphi$ 的环境, 搬运层换成 $\varphi$ 上的自反搬运), 它与 $O$ 相似 (`canΛ-≈`), 它在 $\Omega_\varphi$ 上的结果 $\cong\hat\chi_\varphi$ (`canΛ-run`), 所以证书由覆盖的证书经 `Goodᶻ-tr` 搬来; 地板在这一对观测处给出 $\hat\chi_\varphi\sqsubseteq\mathrm{run}\,O\,t$, 再 `toLevel-⊑`. 与 Omega2Base 的 `Dom-ψ1` 对比: 那里 $c\sqsubseteq^\mathsf I\beta\sqsubseteq$ 一切输出 (全局 `Strictᵝ`), 这里 $c\sqsubseteq$ **这一个**链点 $\hat\chi_\varphi\sqsubseteq$ 这一个输出 (相对链).

```agda
χ̂ : (φ : Ordᴵ) → suc zero ⊑ᴵ φ → Ordˢ zero
χ̂ φ e = ψ1 {ℓ = Mlev (suc zero) φ e} (lim 0 zero) (λ q → lim 1 q) (lim 0 zero) (Ωˢ φ)

CovΛ : Ordᴵ → Ordᴵ → Set
CovΛ φ c = Σ (suc zero ⊑ᴵ φ) λ e → Σ (Goodᶻ (toZ (χ̂ φ e))) λ G → c ⊑ᴵ toLevel (force _ G) (force-HS _ G)

data IsCol : ∀ {k} → Obs k → Set where
  col  : ∀ {L k} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} → IsCol (ψo₁ idO p σ z)
  ctr  : ∀ {a b} {O : Obs b} {e : a ≅ᴵ b} → IsCol O → IsCol (tro O e)
  ctr⁻ : ∀ {a b} {O : Obs a} {e : a ≅ᴵ b} → IsCol O → IsCol (tr⁻o O e)

ColC : ∀ {k} → Ordᴵ → Ordˢ k → Set
ColC {k} c t = ∀ {O : Obs k} → IsCol O → (G : Goodᶻ (toZ (run O t))) → c ⊑ᴵ toLevel (force _ G) (force-HS _ G)

ColC-tr : ∀ {c a b} (e : a ≅ᴵ b) {t : Ordˢ a} → ColC c t → ColC c (trˢ e t)
ColC-tr e h k G = h (ctr k) G

ColC-tr⁻ : ∀ {c a b} (e : a ≅ᴵ b) {t : Ordˢ b} → ColC c t → ColC c (tr⁻ˢ e t)
ColC-tr⁻ e h k G = h (ctr⁻ k) G

canΛ : ∀ (φ : Ordᴵ) (e : suc zero ⊑ᴵ φ) {k} {O : Obs k} → IsCol O → Obs φ
canΛ φ e col      = ψo₁ {ℓ = Mlev (suc zero) φ e} idO (lim 0 zero) (λ q → lim 1 q) (lim 0 zero)
canΛ φ e (ctr k)  = tro (canΛ φ e k) (≅ᴵ-refl φ)
canΛ φ e (ctr⁻ k) = tr⁻o (canΛ φ e k) (≅ᴵ-refl φ)

canΛ-≈ : ∀ φ e {k} {O : Obs k} (c : IsCol O) → canΛ φ e c ≈ᵒ O
canΛ-≈ φ e col      = ψo₁ idO
canΛ-≈ φ e (ctr k)  = tro (canΛ-≈ φ e k)
canΛ-≈ φ e (ctr⁻ k) = tr⁻o (canΛ-≈ φ e k)

canΛ-run : ∀ φ e {k} {O : Obs k} (c : IsCol O) {x : Ordˢ φ} → x ≅ˢ Ωˢ φ → run (canΛ φ e c) x ≅ˢ χ̂ φ e
canΛ-run φ e col      ex = ψ1-≅ (≅ᴵ-refl zero) ex
canΛ-run φ e (ctr k)  ex = canΛ-run φ e k (trˢ-≅ (≅ᴵ-refl φ) ex)
canΛ-run φ e (ctr⁻ k) ex = canΛ-run φ e k (tr⁻ˢ-≅ (≅ᴵ-refl φ) ex)

dom-cov : ∀ {φ c k} {t : Ordˢ k} → FlΛ φ t → CovΛ φ c → ColC c t
dom-cov {φ} {t = t} fl (e , G* , d) {O} k G =
  ⊑ᴵ-trans d (toLevel-⊑ (force-HS _ G*) (force-HS _ G)
                        (⊑-trans (≅→⊑ (force-≅ (toZ-≅ (≅ˢ-sym r)) G* G₁)) (fl (canΛ-≈ φ e k) G₁ G)))
  where
  r : run (canΛ φ e k) (Ωˢ φ) ≅ˢ χ̂ φ e
  r = canΛ-run φ e k (Ωˢ-refl φ)
  G₁ : Goodᶻ (toZ (run (canΛ φ e k) (Ωˢ φ)))
  G₁ = Goodᶻ-tr (toZ-≅ (≅ˢ-sym r)) G*
```

**出现不变量** `Occ≺ᴳ c t₀ g` (非零层闭包 `ŝ c t₀ g` 的, 逐闭包): 存在层号 $\varphi$ 覆盖 $c$, 且 $t_0$ 与各 $g\,\eta\,e$ 被 $c$ 支配 (`ColC`). $\varphi$ 是 "在哪个链点之下" 的名字, `ColC` 是它此刻的推论. `Dom-of-Occ`: 不变量**就是**闭包到第 0 层时 `gc` 要的支配 (UniformS 的 `Dom zero` 的两个分量), 只差把折叠观测取成 `col`.

**保持.** 弹栈 (`Occ-pop`: 只要给一个 $\varphi\sqsubseteq i$ 覆盖 $i{+}1$), 映射 (`Occ-ψ1ᴳ`/`Occ-ψ0ᴳ`: 目标 $i\sqsupseteq\varphi$; 支配由映射者再生的地板经 `dom-cov` 重算), 带地板前缀的加法 (`Occ-addᴳ`), 搬运 (`Occ-trᴳ`/`Occ-tr⁻ᴳ`, 定义性). 覆盖是关于层号与一个链点的数据, 与闭包住在哪一层无关, 全程不变.

```agda
Occ≺ᴳ : ∀ {k} (c : Ordᴵ) → Ordˢ k → ((η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k) → Set
Occ≺ᴳ c t₀ g = Σ Ordᴵ λ φ → CovΛ φ c × ColC c t₀ × (∀ η e → ColC c (g η e))

Dom-of-Occ : ∀ {L k c} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} →
             Occ≺ᴳ c t₀ g →
             (∀ G → c ⊑ᴵ toLevel (force (toZ (ψ1 p σ z t₀)) G) (force-HS _ G)) ×
             (∀ η e G → c ⊑ᴵ toLevel (force (toZ (ψ1 p σ z (g η e))) G) (force-HS _ G))
Dom-of-Occ (φ , cv , c₀ , cg) = (λ G → c₀ col G) , (λ η e G → cg η e col G)

Occ-pop : ∀ {φ i ℓ} → φ ⊑ᴵ i → CovΛ φ (suc i) → (p : i <ᴵ ℓ) (z : zero <ᴵ ℓ) → Occ≺ᴳ (suc i) (t₀pop p z) (gpop p z)
Occ-pop {φ} h cv p z = φ , cv , dom-cov (FlΛ-t₀pop h p z) cv , λ η e → dom-cov (FlΛ-gpop h p z η e) cv

Occ-ψ1ᴳ : ∀ {i k ℓ c} {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} (p : i <ᴵ ℓ) (σ : Simᴵ k ℓ) (z : zero <ᴵ ℓ) →
          (o : Occ≺ᴳ c t₀ g) → proj₁ o ⊑ᴵ i → t₀ ≅ˢ t₀ → (∀ η e → g η e ≅ˢ g η e) →
          Occ≺ᴳ c (ψ1 p σ z t₀) (λ η e → ψ1 p σ z (g η e))
Occ-ψ1ᴳ {t₀ = t₀} {g = g} p σ z (φ , cv , _ , _) h et eg =
  φ , cv , dom-cov (FlΛ-ψ1 h p σ z t₀ et) cv , λ η e → dom-cov (FlΛ-ψ1 h p σ z (g η e) (eg η e)) cv

Occ-ψ0ᴳ : ∀ {i k ℓ c} {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} (p : i <ᴵ ℓ) (σ : Simᴵ k ℓ) →
          (o : Occ≺ᴳ c t₀ g) → proj₁ o ⊑ᴵ i → t₀ ≅ˢ t₀ → (∀ η e → g η e ≅ˢ g η e) →
          Occ≺ᴳ c (ψ0 p σ t₀) (λ η e → ψ0 p σ (g η e))
Occ-ψ0ᴳ {t₀ = t₀} {g = g} p σ (φ , cv , _ , _) h et eg =
  φ , cv , dom-cov (FlΛ-ψ0 {p = p} {σ = σ} h t₀ et) cv , λ η e → dom-cov (FlΛ-ψ0 {p = p} {σ = σ} h (g η e) (eg η e)) cv

Occ-addᴳ : ∀ {k ℓ c} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} →
           (o : Occ≺ᴳ c t₀ g) → FlΛ (proj₁ o) a → t₀ ≅ˢ t₀ → (∀ η e → g η e ≅ˢ g η e) →
           Occ≺ᴳ c (addˢ a σ t₀) (λ η e → addˢ a σ (g η e))
Occ-addᴳ {t₀ = t₀} {g = g} (φ , cv , _ , _) fa et eg =
  φ , cv , dom-cov (FlΛ-add t₀ fa et) cv , λ η e → dom-cov (FlΛ-add (g η e) fa (eg η e)) cv

Occ-trᴳ : ∀ {a b c} (e : a ≅ᴵ b) {t₀ : Ordˢ a} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ a} →
          Occ≺ᴳ c t₀ g → Occ≺ᴳ c (trˢ e t₀) (λ η d → trˢ e (g η d))
Occ-trᴳ e (φ , cv , c₀ , cg) = φ , cv , ColC-tr e c₀ , λ η d → ColC-tr e (cg η d)

Occ-tr⁻ᴳ : ∀ {a b c} (e : a ≅ᴵ b) {t₀ : Ordˢ b} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ b} →
           Occ≺ᴳ c t₀ g → Occ≺ᴳ c (tr⁻ˢ e t₀) (λ η d → tr⁻ˢ e (g η d))
Occ-tr⁻ᴳ e (φ , cv , c₀ , cg) = φ , cv , ColC-tr⁻ e c₀ , λ η d → ColC-tr⁻ e (cg η d)
```

**读法.** 五条保持里只有映射有条件 ($\varphi\sqsubseteq i$), 加法要前缀的地板; 其余无条件. 映射到地板之下 ($i\prec\varphi$) 时 `ColC c (ψ_i t₀)` 一般为假 (TreeNF §3), 所以 `Occ≺ᴳ` **不是**对一切折叠封闭的; 这一点与 `NF₁` 相同 (NF₁ 也不对一切 $\psi$-应用封闭, 只对基本列封闭, `NF₁-fsn`), 区别在于树侧的 "基本列" 是折叠本身, 链点里的闭包确实被更低的 $\psi_d$ 映射过 (§2 末).

## §4 `Floor β`: 以地板 $\Omega_1$ 为不变量的遗传好树

**特例 $\varphi=1$.** §2 的保持条件 "目标 $\sqsupseteq\varphi$" 对 $\varphi=1$ 与一切非零目标成立 (`one⊑`: 有帧证据时非零目标 $\sqsupseteq1$), 所以 $\varphi=1$ 的不变量可以直接写进 `Good` 的非零层支配, 不带量词. 覆盖取成模块参数 `cov : CovΛ 1 β` (链点 $\hat\chi_1=\psi^{[\hat\Omega]}_0(\Omega_1)$ 的证书与 $\beta\sqsubseteq^\mathsf I$ 它的层号), 即 "一切闭包都由同一个链点 $\hat\chi_1$ 覆盖". 这是 Omega2Base 的 `Bound β` 只改支配:

| | Omega2Base `Bound β` | 本文 `Floor β cov` |
|---|---|---|
| 非零层 `Dom` | $c\sqsubseteq^\mathsf I\beta$ | `Occ≺ β c t₀ g` $=c\sqsubseteq^\mathsf I\beta$ × `ColC β t₀` × `∀ η e → ColC β (g η e)` |
| 第 0 层支配的来源 (`Dom-ψ1`) | 模块参数 `Strictᵝ β`: **一切**尾巴的输出 $\sqsupseteq\beta$ | 输入的 `Occ≺` 本身 (`ColC` 在观测 `col` 处) |
| 支配从哪里来 | 全局假设 | 再生的地板 $\Omega_1$ + `dom-cov` + `cov` (`Strict⁺`) |
| 可用的 $\beta$ | $\beta\sqsubseteq\mathtt{lvl}\,\mathrm{BTBO}$ (`Sβ-fails⁺`) | $\beta\sqsubseteq\mathtt{lvl}\,\gamma'_1$ (TreeNF `floor-wall`) |

复制时的改动 (其余逐字): (1) 模块多参数 `cov`, `Dom (suc _)`/`Dom (lim _ _)` 换成 `Occ≺ β`; (2) `Dom-tr`/`Dom-tr⁻` 的非零情形用 `Occ-tr`/`Occ-tr⁻` (定义性, `ColC-tr`); (3) `Good-add` 多一个参数 `FlA ℓ a` (非零层的前缀有地板; 包在单字段记录 `Wrap` 里, 否则模式变量在 `ℓ = suc _` 的子句里被插入隐式参数, 报 `[UnequalHiding] … because one is an implicit function type and the other is an explicit function type when checking that the expression fa has type FlA (suc x) a`), 非零层闭包的情形用 `Occ-add`; `Good-iter` 同; (4) `Good-ψ0` 放进以帧证据 `z₀ : zero <ᴵ ℓ` 为参数的匿名模块 (递归中环境层号不变), 非零目标映射非零层闭包时用 `Occ-ψ0` (地板由 `one⊑ z₀ p` 再生), 后继情形的 `Good-iter` 用 `FlA-ψ0`; (5) `popDom` 的非零情形给出三元组 (界 `s⊑′ (sim h p)` 与弹栈闭包的支配); (6) 去掉 `Strictᵝ` 与子模块 `Clos`: `Dom-ψ1` 直接读输入的 `Occ≺`; `Good-ψ1` 的非零目标映射非零层闭包用 `Occ-ψ1`, 后继情形用 `FlA-ψ1`.

```agda
Occ≺ : ∀ {k} (β c : Ordᴵ) → Ordˢ k → ((η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k) → Set
Occ≺ β c t₀ g = c ⊑ᴵ β × ColC β t₀ × (∀ η e → ColC β (g η e))

record Wrap (A : Set) : Set where
  constructor wrap
  field unwrap : A
open Wrap

FlA : (ℓ : Ordᴵ) → Ordˢ ℓ → Set
FlA zero      a = ⊤
FlA (suc _)   a = Wrap (Fl a)
FlA (lim _ _) a = Wrap (Fl a)

FlA-ψ1 : ∀ {i k ℓ} (p : i <ᴵ ℓ) (σ : Simᴵ k ℓ) (z : zero <ᴵ ℓ) (y : Ordˢ k) → y ≅ˢ y → FlA i (ψ1 p σ z y)
FlA-ψ1 {i = zero}    p σ z y ey = tt
FlA-ψ1 {i = suc _}   p σ z y ey = wrap (FlΛ-ψ1 (one⊑ z p tt) p σ z y ey)
FlA-ψ1 {i = lim _ _} p σ z y ey = wrap (FlΛ-ψ1 (one⊑ z p tt) p σ z y ey)

FlA-ψ0 : ∀ {i k ℓ} → zero <ᴵ ℓ → (p : i <ᴵ ℓ) (σ : Simᴵ k ℓ) (y : Ordˢ k) → y ≅ˢ y → FlA i (ψ0 p σ y)
FlA-ψ0 {i = zero}    z₀ p σ y ey = tt
FlA-ψ0 {i = suc _}   z₀ p σ y ey = wrap (FlΛ-ψ0 {p = p} {σ = σ} (one⊑ z₀ p tt) y ey)
FlA-ψ0 {i = lim _ _} z₀ p σ y ey = wrap (FlΛ-ψ0 {p = p} {σ = σ} (one⊑ z₀ p tt) y ey)
```

**`Floor β` 的定义** (Omega2Base §1 逐字, 只改非零层的 `Dom`):

```agda
module Floor (β : Ordᴵ) (cov : CovΛ (suc zero) β) where
  Dom : (ℓ c : Ordᴵ) → Ordˢ ℓ → ((η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ) → Set
  Dom zero      c t₀ g = (∀ G → c ⊑ᴵ toLevel (force (toZ t₀) G) (force-HS _ G)) ×
                         (∀ η e G → c ⊑ᴵ toLevel (force (toZ (g η e)) G) (force-HS _ G))
  Dom (suc _)   c t₀ g = Occ≺ β c t₀ g
  Dom (lim _ _) c t₀ g = Occ≺ β c t₀ g

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

**`Occ≺` 的五条保持** (§3 的 `Occ-…ᴳ` 在 $\varphi=1$ 的实例; 地板由 `one⊑` 再生, 支配由 `dom-cov … cov`):

```agda
  Strict⁺ : ∀ {k} {y : Ordˢ k} → Fl y → ColC β y
  Strict⁺ fl = dom-cov fl cov

  Occ-tr : ∀ {a b c} (e : a ≅ᴵ b) {t₀ : Ordˢ a} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ a} →
           t₀ ≅ˢ t₀ → (∀ η d → g η d ≅ˢ g η d) → Occ≺ β c t₀ g → Occ≺ β c (trˢ e t₀) (λ η d → trˢ e (g η d))
  Occ-tr e et eg (cb , c₀ , cg) = cb , ColC-tr e c₀ , λ η d → ColC-tr e (cg η d)

  Occ-tr⁻ : ∀ {a b c} (e : a ≅ᴵ b) {t₀ : Ordˢ b} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ b} →
            t₀ ≅ˢ t₀ → (∀ η d → g η d ≅ˢ g η d) → Occ≺ β c t₀ g → Occ≺ β c (tr⁻ˢ e t₀) (λ η d → tr⁻ˢ e (g η d))
  Occ-tr⁻ e et eg (cb , c₀ , cg) = cb , ColC-tr⁻ e c₀ , λ η d → ColC-tr⁻ e (cg η d)

  Occ-add : ∀ {k ℓ c} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} →
            Fl a → t₀ ≅ˢ t₀ → (∀ η e → g η e ≅ˢ g η e) → Occ≺ β c t₀ g → Occ≺ β c (addˢ a σ t₀) (λ η e → addˢ a σ (g η e))
  Occ-add {t₀ = t₀} {g = g} fa et eg (cb , _ , _) = cb , Strict⁺ (FlΛ-add t₀ fa et) , λ η e → Strict⁺ (FlΛ-add (g η e) fa (eg η e))

  Occ-ψ0 : ∀ {i k ℓ c} {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} → suc zero ⊑ᴵ i → (p : i <ᴵ ℓ) (σ : Simᴵ k ℓ) →
           Occ≺ β c t₀ g → t₀ ≅ˢ t₀ → (∀ η e → g η e ≅ˢ g η e) → Occ≺ β c (ψ0 p σ t₀) (λ η e → ψ0 p σ (g η e))
  Occ-ψ0 {t₀ = t₀} {g = g} h p σ (cb , _ , _) et eg =
    cb , Strict⁺ (FlΛ-ψ0 {p = p} {σ = σ} h t₀ et) , λ η e → Strict⁺ (FlΛ-ψ0 {p = p} {σ = σ} h (g η e) (eg η e))

  Occ-ψ1 : ∀ {i k ℓ c} {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} → suc zero ⊑ᴵ i →
           (p : i <ᴵ ℓ) (σ : Simᴵ k ℓ) (z : zero <ᴵ ℓ) →
           Occ≺ β c t₀ g → t₀ ≅ˢ t₀ → (∀ η e → g η e ≅ˢ g η e) → Occ≺ β c (ψ1 p σ z t₀) (λ η e → ψ1 p σ z (g η e))
  Occ-ψ1 {t₀ = t₀} {g = g} h p σ z (cb , _ , _) et eg =
    cb , Strict⁺ (FlΛ-ψ1 h p σ z t₀ et) , λ η e → Strict⁺ (FlΛ-ψ1 h p σ z (g η e) (eg η e))
```

**搬运、$\Omega$ 与加法** (Omega2Base §2, 改动 (2)(3)):

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
  Dom-tr e@(s≅ _) g0 gg et eg h = Occ-tr e et eg h
  Dom-tr e@(l≅ _) g0 gg et eg h = Occ-tr e et eg h

  Dom-tr⁻ : ∀ {a b c} (e : a ≅ᴵ b) {t₀ : Ordˢ b} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ b} →
            Good t₀ → (∀ η d → Good (g η d)) → t₀ ≅ˢ t₀ → (∀ η d → g η d ≅ˢ g η d) →
            Dom b c t₀ g → Dom a c (tr⁻ˢ e t₀) (λ η d → tr⁻ˢ e (g η d))
  Dom-tr⁻ z≅     g0 gg et eg h = Dom0-≅ g0 gg (tr⁻ˢ-≅ z≅ et) (λ η d → tr⁻ˢ-≅ z≅ (eg η d)) h
  Dom-tr⁻ e@(s≅ _) g0 gg et eg h = Occ-tr⁻ e et eg h
  Dom-tr⁻ e@(l≅ _) g0 gg et eg h = Occ-tr⁻ e et eg h

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

  Good-add : ∀ {k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} → Lv k ℓ → FlA ℓ a → Good a → a ≅ˢ a → Good b → Good (addˢ a σ b)
  Good-add lv fa ga ea bz          = ga
  Good-add lv fa ga ea (bs g)      = bs (Good-add lv fa ga ea g)
  Good-add lv fa ga ea (bl hg st)  = bl (λ n → Good-add lv fa ga ea (hg n)) (λ n → add-cong refl ea (st n))
  Good-add {a = a} {σ = σ} lv fa ga ea (bi {p = q} {f = f} hb hm) = bi
    (λ z ez g → subst (λ u → Good (addˢ a σ (f (intoˢ (<→◃ q) u)))) (sym (out-intoˢ (<→◃ (σ q)) z))
                      (Good-add lv fa ga ea (hb z ez (Gd-conv (<→◃ (σ q)) (<→◃ q) g))))
    (λ {z} {z′} h → subst₂ (λ u v → addˢ a σ (f (intoˢ (<→◃ q) u)) ⊑ᵒ addˢ a σ (f (intoˢ (<→◃ q) v)))
                           (sym (out-intoˢ (<→◃ (σ q)) z)) (sym (out-intoˢ (<→◃ (σ q)) z′)) (add-cong refl ea (hm h)))
  Good-add lv fa ga ea (bu {r = zero} g)   = Good-add (Lv-up zero lv) fa ga ea g
  Good-add lv fa ga ea (bu {r = self n} g) = Good-add (Lv-up (self n) lv) fa ga ea g
  Good-add {k = zero} lv fa ga ea (bŝ g0 gg et eg m mm dm) =
    bĉ G₀ Gg (proj₁ dm G₀) (λ η e → proj₂ dm η e (Gg η e))
       (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
       (Good-add lv fa ga ea g0) (λ η e → Good-add lv fa ga ea (gg η e))
       (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h))
    where
    G₀ = Good→Goodᶻ g0
    Gg = λ η e → Good→Goodᶻ (gg η e)
  Good-add {k = suc _} {ℓ = zero} lv fa ga ea (bŝ g0 gg et eg m mm dm) = ⊥-elim (tf (sym lv))
  Good-add {k = lim _ _} {ℓ = zero} lv fa ga ea (bŝ g0 gg et eg m mm dm) = ⊥-elim (tf (sym lv))
  Good-add {k = suc _} {ℓ = suc _} {a = a} {σ = σ} lv fa ga ea (bŝ g0 gg et eg m mm dm) =
    bŝ (Good-add lv fa ga ea g0) (λ η e → Good-add lv fa ga ea (gg η e)) (addˢ-≅ refl ea et)
       (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
       (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h)) (Occ-add {a = a} {σ = σ} (unwrap fa) et (λ η e → eg η e η e (≅ᴵ-refl η)) dm)
  Good-add {k = suc _} {ℓ = lim _ _} {a = a} {σ = σ} lv fa ga ea (bŝ g0 gg et eg m mm dm) =
    bŝ (Good-add lv fa ga ea g0) (λ η e → Good-add lv fa ga ea (gg η e)) (addˢ-≅ refl ea et)
       (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
       (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h)) (Occ-add {a = a} {σ = σ} (unwrap fa) et (λ η e → eg η e η e (≅ᴵ-refl η)) dm)
  Good-add {k = lim _ _} {ℓ = suc _} {a = a} {σ = σ} lv fa ga ea (bŝ g0 gg et eg m mm dm) =
    bŝ (Good-add lv fa ga ea g0) (λ η e → Good-add lv fa ga ea (gg η e)) (addˢ-≅ refl ea et)
       (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
       (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h)) (Occ-add {a = a} {σ = σ} (unwrap fa) et (λ η e → eg η e η e (≅ᴵ-refl η)) dm)
  Good-add {k = lim _ _} {ℓ = lim _ _} {a = a} {σ = σ} lv fa ga ea (bŝ g0 gg et eg m mm dm) =
    bŝ (Good-add lv fa ga ea g0) (λ η e → Good-add lv fa ga ea (gg η e)) (addˢ-≅ refl ea et)
       (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
       (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h)) (Occ-add {a = a} {σ = σ} (unwrap fa) et (λ η e → eg η e η e (≅ᴵ-refl η)) dm)
  Good-add lv fa ga ea (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
    bĉ G₀ Gg d₀ dE m₀ mE (Good-add lv fa ga ea go) (λ η e → Good-add lv fa ga ea (gO η e))
       (λ η e → add-cong refl ea (mo η e)) (λ η e η′ e′ h → add-cong refl ea (mO η e η′ e′ h))

  Good-iter : ∀ {ℓ} {c : Ordˢ ℓ} → Good c → c ≅ˢ c → FlA ℓ c → ∀ n → Good (iter (c +ˢ_) Ord₊ˢ.zero n)
  Good-iter {ℓ} gc ec fc zero    = bz
  Good-iter {ℓ} gc ec fc (suc n) = Good-add (Lv-refl ℓ) fc gc ec (Good-iter gc ec fc n)
```

## §5 闭包定理, 以 `Strict⁺` 为参数

`Strict⁺` (上一节, 由 `cov` 与 `dom-cov` 得到, 不是假设): 一切以 $\Omega_1$ 为地板的尾巴被 $\beta$ 支配, 对一切折叠观测与一切证书. 与 Omega2Base 的 `Strictᵝ β` 的区别是多了前提 `Fl y`; 它排除了尾巴 $0$ (输出 BTBO, `Sβ-fails⁺` 的反例), 而不排除任何以 $\Omega_1$ 为地板的闭包的第 0 点. 下面的 `mkĉ`、`Good-ψ0`、`popGood` 是 Omega2Base 的复制 (改动 (4)(5)).

```agda
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

  module _ {ℓ : Ordᴵ} (z₀ : zero <ᴵ ℓ) where
    Good-ψ0 : ∀ {i k} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {x : Ordˢ k} → Good x → x ≅ˢ x → Ok i x → Good (ψ0 p σ x)
    chain0-good : ∀ {j k} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
                  (∀ (z : Ordˢ j) → z ≅ˢ z → Gd j (<→◃ q) (intoˢ (<→◃ q) z) → Good (f (intoˢ (<→◃ q) z))) →
                  Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → (∀ n → Ok j (f (intoˢ (<→◃ q) (chain0 σ q f n)))) →
                  ∀ n → Good (chain0 σ q f n)
    chain0-good {j} hb e ok zero = Good-Ω j
    chain0-good {σ = σ} {q = q} {f = f} hb e ok (suc n) =
      Good-ψ0 (hb (chain0 σ q f n) (chain0-≅ e n) (Good→Gd (<→◃ q) (chain0-good hb e ok n))) (i-respˢ e (chain0-≅ e n)) (ok n)

    Good-ψ0 {i} bz ex ok = Good-Ω i
    Good-ψ0 {i} {p = p} {σ = σ} (bs g) ex ok = bl (Good-iter (Good-ψ0 g ea (Ok-suc i ok)) eψ (FlA-ψ0 z₀ p σ _ ea)) (rule4ᵒ eψ)
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
    Good-ψ0 {i = suc _} {k = suc _} {p = p} {σ = σ} (bŝ g0 gg et eg m mm dm) ex ok =
      bŝ (Good-ψ0 g0 et tt) (λ η e → Good-ψ0 (gg η e) (eg η e η e (≅ᴵ-refl η)) tt)
         (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
         (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h)) (Occ-ψ0 (one⊑ z₀ p tt) p σ dm et (λ η e → eg η e η e (≅ᴵ-refl η)))
    Good-ψ0 {i = suc _} {k = lim _ _} {p = p} {σ = σ} (bŝ g0 gg et eg m mm dm) ex ok =
      bŝ (Good-ψ0 g0 et tt) (λ η e → Good-ψ0 (gg η e) (eg η e η e (≅ᴵ-refl η)) tt)
         (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
         (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h)) (Occ-ψ0 (one⊑ z₀ p tt) p σ dm et (λ η e → eg η e η e (≅ᴵ-refl η)))
    Good-ψ0 {i = lim _ _} {k = suc _} {p = p} {σ = σ} (bŝ g0 gg et eg m mm dm) ex ok =
      bŝ (Good-ψ0 g0 et tt) (λ η e → Good-ψ0 (gg η e) (eg η e η e (≅ᴵ-refl η)) tt)
         (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
         (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h)) (Occ-ψ0 (one⊑ z₀ p tt) p σ dm et (λ η e → eg η e η e (≅ᴵ-refl η)))
    Good-ψ0 {i = lim _ _} {k = lim _ _} {p = p} {σ = σ} (bŝ g0 gg et eg m mm dm) ex ok =
      bŝ (Good-ψ0 g0 et tt) (λ η e → Good-ψ0 (gg η e) (eg η e η e (≅ᴵ-refl η)) tt)
         (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
         (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h)) (Occ-ψ0 (one⊑ z₀ p tt) p σ dm et (λ η e → eg η e η e (≅ᴵ-refl η)))
    Good-ψ0 {i = zero} (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex (_ , _ , d) = ⊥-elim (~ĉ d)
    Good-ψ0 {i = suc _} (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex ok =
      bĉ G₀ Gg d₀ dE m₀ mE (Good-ψ0 go (ĉ-refl₀ ex) tt) (λ η e → Good-ψ0 (gO η e) (ĉ-reflg ex η e) tt)
         (λ η e → ψ0-cong (mo η e)) (λ η e η′ e′ h → ψ0-cong (mO η e η′ e′ h))
    Good-ψ0 {i = lim _ _} (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex ok =
      bĉ G₀ Gg d₀ dE m₀ mE (Good-ψ0 go (ĉ-refl₀ ex) tt) (λ η e → Good-ψ0 (gO η e) (ĉ-reflg ex η e) tt)
         (λ η e → ψ0-cong (mo η e)) (λ η e η′ e′ h → ψ0-cong (mO η e η′ e′ h))

  popGood : ∀ {i k ℓ} (p : i <ᴵ ℓ) (σ : Simᴵ k ℓ) (z : zero <ᴵ ℓ) → Dom i (suc i) (t₀pop p z) (gpop p z) →
            Good (ψ1 p σ z Ord₊ˢ.zero)
  popGood {i} p σ z dm =
    bŝ (Good-ψ0 (z<suc z p) (Good-Ω (suc zero)) (Ωˢ-refl (suc zero)) (Ok-Pl i (Pl-Ω (suc zero))))
       (λ η e → Good-ψ0 (lim 0 (z<suc z p)) (Good-Ω η) (Ωˢ-refl η) (Ok-Pl i (Pl-Ω η)))
       (ψ0-≅ (≅ᴵ-refl i) (Ωˢ-refl (suc zero))) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl i) (Ωˢ-≅ eη))
       (λ η e → ψ0-cong (Ω-monoᵒ (⊑ᴵ-trans (s⊑ z≅ (z<suc z p)) e))) (λ η e η′ e′ h → ψ0-cong (Ω-monoᵒ h)) dm

  popDom₀ : ∀ {ℓ} (p : zero <ᴵ ℓ) (z : zero <ᴵ ℓ) → Dom zero (suc zero) (t₀pop p z) (gpop p z)
  popDom₀ p z = (λ G → Strict₀ (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)) G) , (λ η e G → Strict₀ (Ωˢ η) (Ωˢ-refl η) G)

  popDom : ∀ {i ℓ} (p : i <ᴵ ℓ) (z : zero <ᴵ ℓ) → ℓ ⊑ᴵ β → Dom i (suc i) (t₀pop p z) (gpop p z)
  popDom {i = zero}    p z h = popDom₀ p z
  popDom {i = suc _}   p z h = s⊑′ (sim h p) , Strict⁺ (FlΛ-t₀pop (one⊑ z p tt) p z) , λ η e → Strict⁺ (FlΛ-gpop (one⊑ z p tt) p z η e)
  popDom {i = lim _ _} p z h = s⊑′ (sim h p) , Strict⁺ (FlΛ-t₀pop (one⊑ z p tt) p z) , λ η e → Strict⁺ (FlΛ-gpop (one⊑ z p tt) p z η e)
```

**`Good-ψ1`.** `Dom-ψ1`: 非零层闭包被目标 0 的折叠映到第 0 层; 支配 $c\sqsubseteq^\mathsf I\beta\sqsubseteq^\mathsf I$ 链点的层号, 第二步就是输入的 `Occ≺` 的 `ColC` 分量在观测 `col` 处的实例. 这是全文唯一读输入的支配数据的地方, 也是支配定理 (§3 `dom-cov`) 在 $\varphi=1$ 的使用点.

```agda
  Dom-ψ1 : ∀ {L k c} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} →
           Occ≺ β c t₀ g → t₀ ≅ˢ t₀ → (∀ η e → g η e ≅ˢ g η e) →
           Dom zero c (ψ1 p σ z t₀) (λ η e → ψ1 p σ z (g η e))
  Dom-ψ1 (cb , c₀ , cg) et eg = (λ G → ⊑ᴵ-trans cb (c₀ col G)) , (λ η e G → ⊑ᴵ-trans cb (cg η e col G))

  Good-ψ1 : ∀ {i k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {x : Ordˢ k} → ℓ ⊑ᴵ β → Good x → x ≅ˢ x →
            Good (ψ1 p σ z x)
  chain1-good : ∀ {j k ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} → ℓ ⊑ᴵ β →
                (∀ (y : Ordˢ j) → y ≅ˢ y → Gd j (<→◃ q) (intoˢ (<→◃ q) y) → Good (f (intoˢ (<→◃ q) y))) →
                Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → ∀ n → Good (chain1 σ z q f n)
  chain1-good {j} h hb e zero = Good-Ω j
  chain1-good {σ = σ} {z = z} {q = q} {f = f} h hb e (suc n) =
    Good-ψ1 h (hb (chain1 σ z q f n) (chain1-≅ e n) (Good→Gd (<→◃ q) (chain1-good h hb e n))) (i-respˢ e (chain1-≅ e n))

  Good-ψ1 {p = p} {σ = σ} {z = z} h bz ex = popGood p σ z (popDom p z h)
  Good-ψ1 {i} {p = p} {σ = σ} {z = z} h (bs g) ex = bl (Good-iter (Good-ψ1 h g ea) eψ (FlA-ψ1 p σ z _ ea)) (rule4ᵒ eψ)
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
  Good-ψ1 {i = suc _} {k = suc _} {p = p} {σ = σ} {z = z} h (bŝ g0 gg et eg m mm dm) ex =
    bŝ (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
       (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh)) (Occ-ψ1 (one⊑ z p tt) p σ z dm et (λ η e → eg η e η e (≅ᴵ-refl η)))
  Good-ψ1 {i = suc _} {k = lim _ _} {p = p} {σ = σ} {z = z} h (bŝ g0 gg et eg m mm dm) ex =
    bŝ (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
       (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh)) (Occ-ψ1 (one⊑ z p tt) p σ z dm et (λ η e → eg η e η e (≅ᴵ-refl η)))
  Good-ψ1 {i = lim _ _} {k = suc _} {p = p} {σ = σ} {z = z} h (bŝ g0 gg et eg m mm dm) ex =
    bŝ (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
       (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh)) (Occ-ψ1 (one⊑ z p tt) p σ z dm et (λ η e → eg η e η e (≅ᴵ-refl η)))
  Good-ψ1 {i = lim _ _} {k = lim _ _} {p = p} {σ = σ} {z = z} h (bŝ g0 gg et eg m mm dm) ex =
    bŝ (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
       (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh)) (Occ-ψ1 (one⊑ z p tt) p σ z dm et (λ η e → eg η e η e (≅ᴵ-refl η)))
  Good-ψ1 h (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex =
    bĉ G₀ Gg d₀ dE m₀ mE (Good-ψ1 h go (ĉ-refl₀ ex)) (λ η e → Good-ψ1 h (gO η e) (ĉ-reflg ex η e))
       (λ η e → ψ1-cong (mo η e)) (λ η e η′ e′ hh → ψ1-cong (mO η e η′ e′ hh))
```

**读法.** 前提 $\ell\sqsubseteq^\mathsf I\beta$ 只在弹栈的界 (`popDom`) 用; 地板的再生 (`Occ-ψ1`, `Occ-ψ0`, `FlA-ψ1`, `FlA-ψ0`, `popDom`) 只用 `one⊑` 与帧证据; 覆盖 `cov` 只经 `Strict⁺ = dom-cov · cov` 进入. 与 Omega2Base 相比, 数学全在 `CovΛ 1 β` 对哪些 $\beta$ 有居留: TreeNF §1 对 $\beta=\mathtt{lvl}\,\gamma'_1$ 给出 (覆盖链点 $\hat\chi_1\cong\gamma'_1$), 而 $\beta\sqsupseteq\mathtt{lvl}\,\gamma'_1+1$ 时 `Strict⁺` 为假 (TreeNF `floor-wall`).

## §6 对比表: 记号侧 `NF₁`/`occ<` 与树侧 `Occ≺`

| 记号侧 (StandardOmega §2/§5, SystemOmega) | 树侧 (本文) | 说明 |
|---|---|---|
| 项 $\psi_0(\Omega_\Omega+b)$ 的 $G$-条件: $b$ 里经下标 $\ge u$ 的节点可见的参数 $<^\mathsf T$ 项 (`Bnd₁`, `Vis₁` 的 `vs` 规则) | 非零层闭包 `ŝ c t₀ g` 的 `Occ≺ᴳ`: 有覆盖层号 $\varphi$ 与地板 $\Omega_\varphi\sqsubseteq^\mathsf o t_0$ | 闭包 = 弹栈产生的 $\psi_j(\Omega_\Omega+\cdots)$, 界 $c=j+1$ 就是 "出现的下标 $j$" |
| `occ<`: NF₁ 项里出现的每个可数下标 $<^\mathsf T$ 项 | `ColC c t₀`: $c\sqsubseteq^\mathsf I$ $t_0$ 的一切 $\psi^{[\hat\Omega]}_0$-折叠的层号 (一切折叠观测、一切证书) | 层号是树 (`Ordᴵ`), 比较是 $\sqsubseteq^\mathsf I$/$\prec^\mathsf I$, 没有记号项 |
| 下标 $u$ 由谁 "看见": 外层 $\psi_v$, $v\le u$ 的节点穿透到它 | 地板由映射者再生: $\psi_i$ 的一切输出 $\sqsupseteq^\mathsf o\Omega_i$ (`FlΛ-ψ0`/`FlΛ-ψ1`), 前缀 $a$ 的地板传给 $a+b$ (`FlΛ-add`) | `vs` 规则只看穿下标 $\ge u$ 的节点 ⟷ 再生条件 "目标 $\sqsupseteq\varphi$" |
| `occ<` 的证明经标签 `Lab-oc` 变成树上的 $\prec$ (GoodLBase `domᴸ`) | 覆盖 `CovΛ φ c`: 链点 $\hat\chi_\varphi=\psi^{[\hat\Omega]}_0(\Omega_\varphi)$ 的 Prefix 证书与 $c\sqsubseteq^\mathsf I$ 其层号 | 记号侧的 "项的值" 换成 "链点的计值", 来自同一条链的前一个证书 |
| `SELF`/`SELFΩ` (自界: 在自己的折叠之下的下标, 走一步基本列后仍在其下) | `dom-cov` (支配定理) + `Occ-ψ1ᴳ`: 覆盖不随映射改变, 支配由再生的地板重算 | 树侧没有 "走一步" 的单独引理: 链点的下一点就是映射者 |
| `NF₁-fsn`/`NF₁-γ`: 基本列与 γ-链保持 NF₁ | `Occ-pop`/`Occ-ψ1ᴳ`/`Occ-ψ0ᴳ`/`Occ-addᴳ`/`Occ-trᴳ`; $\varphi=1$ 时合成 `Floor.Good-ψ1` (无前提) | 映射到地板之下 ($i\prec\varphi$) 不保持, 见 TreeNF §4 |
| 上下文 `DESC`/`LIFT` | 观测前序的观测栈 (`IsCol` 只取 "搬运* ∘ 目标 0 折叠" 一类) | `IsCol` 对搬运封闭, 地板本身不对搬运封闭 (§2 否定) |

**为什么记号无关.** 定义 (`FlΛ`, `ColC`, `CovΛ`, `Occ≺ᴳ`, `Occ≺`, `Floor`) 与全部证明只提到 `Ordˢ`/`Z` 的树、`Ordᴵ` 的层号、$\sqsubseteq^\mathsf I$、观测前序 $\sqsubseteq^\mathsf o$ 与 Prefix 证书 `Goodᶻ`; 所导入的 UniformS/Stage2Label 名字 (`B1₀`, `B1₁`, `Strict₀`, `Ok`, `chain0` …) 本身不读记号 (NotFree 的边界注记同). 覆盖用的是**链点的证书**, 不是标签.

## §7 结论与边界

**定义 (编译).** 地板 `FlΛ φ t` ($\Omega_\varphi\sqsubseteq^\mathsf o t$); 折叠观测 `IsCol`; 被支配 `ColC c t`; 覆盖 `CovΛ φ c`; **逐闭包的出现不变量 `Occ≺ᴳ c t₀ g`** (存在 $\varphi$: `CovΛ φ c` 且 $t_0$、各 $g\,\eta\,e$ 满足 `ColC c`); $\varphi=1$ 的特例 `Occ≺ β` 与遗传好树 `Floor β cov`.

**定理 (编译).**

1. 保持: `FlΛ-ψ0`, `FlΛ-t₀pop`, `FlΛ-gpop`, `FlΛ-ψ1` (目标 $\sqsupseteq\varphi$), `add-floor`/`FlΛ-add` (前缀的地板); `ColC-tr`/`ColC-tr⁻` (定义性); 整体形式 `Occ-pop`, `Occ-ψ1ᴳ`, `Occ-ψ0ᴳ`, `Occ-addᴳ`, `Occ-trᴳ`, `Occ-tr⁻ᴳ`.
2. 支配: **`dom-cov : FlΛ φ t → CovΛ φ c → ColC c t`**, `Dom-of-Occ` (不变量给出第 0 层链的 `d₀`/`dE`).
3. `one⊑` (帧证据下非零目标 $\sqsupseteq1$), `Mlev⊑`.
4. **`Floor.Good-ψ1 : ℓ ⊑ᴵ β → Good x → x ≅ˢ x → Good (ψ1 p σ z x)`**, 只以覆盖 `cov : CovΛ 1 β` 为模块参数 (没有 `Strictᵝ` 式的全局假设); `Floor.Good→Goodᶻ`.

**否定 (编译报错, 记在 §2):** 地板对搬运不能在 $\sqsubseteq^\mathsf o$ 的语言里陈述 (`⊑ᵒ-≅ʳ` 只同层, `≈ᵒ` 要求同形), 故不变量存地板的推论 `ColC`. 工程注记: `FlA` 的非零值必须包在 `Wrap` 里 (否则 `[UnequalHiding]`).

**边界.** (i) `Floor` 只用一个覆盖 ($\varphi=1$, 一切闭包由 $\hat\chi_1$ 覆盖); 一般的 `Occ≺ᴳ` 的映射保持带条件 $\varphi\sqsubseteq i$, 不是对一切折叠封闭的 (TreeNF §3). (ii) 只处理 Prefix 的折叠 `ψᴾ` 的栈 `[]` 与 `[Ω̂]` (UniformS 的范围); 统一形 (Uniform2Base 的前缀塔) 上没有这套理论. (iii) 只导入已有模块, 不改任何已有文件; 被改动的定义 (Omega2Base 的 `Bound`) 以新名字 `Floor` 复制在本文.

