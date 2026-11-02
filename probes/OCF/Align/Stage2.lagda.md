# 阶段 2: 不可数下标 $\Omega_\Omega$ 的交替读法

> 接 [NoCumsum](NoCumsum.lagda.md) 与 [Label](Label.lagda.md): 无 cumsum 的闭项 `N.BTBOᴵ` 的遗传标签是 EBO 的 $\psi_0(\Omega_\Omega)$ (`BTBO-label`). 越过它, [EBO](EBO.lagda.md) 的项开始带**不可数下标**: $\psi_0(\Omega_\Omega+1)$, $\psi_0(\Omega_\Omega\cdot2)$, $\psi_0(\Omega_{\Omega+1})$, $\psi_0(\Omega_{\Omega_\Omega})$, …. 树的层号只能可数 ([Barrier](../Barrier.lagda.md)). 已有的代表是层号 `BTBOᴸ` 与它的 $\Omega$ (对角 $\mathbb N$-极限 $\lim_n\Omega_{L_{n+1}}$, [Diagonal](Diagonal.lagda.md) §5). 本文按交替原则 ($\Omega$ 只在对象层作对角 $\mathbb N$-极限; 被比较的下标要在下标层有公共上界) 做下一阶段的第一步: 核对三条事实, 检验三个设计, 实现选中的一个并通过决定性检验, 再把它的第一处失败精确定位.
>
> 结论先说:
>
> 1. **种子步成立, 但不升值 (§1).** `seed : BTBOᴵ ⊑ ψ⁰ (Ω BTBOᴸ)`, 反向的 `seed⁻` 也成立; `ψ⁰ (Ω BTBOᴸ) ≡ lim (γ ∘ suc ∘ suc)` (`refl`): 对角线平移一位, 同一个不动点. EBO 侧 $\psi_0(\Omega_{\psi_0(\Omega_\Omega)})$ 的共尾度是 $\omega$, 第 $n$ 项是 $\gamma^\mathsf E_{n+2}$ (`tb-fs`), 树与它**遗传**一致 (`tb-label`). 另: 含 $\gamma_0$ 的对角层号 `ℓ₀ = toLevel (lim γ) _` 满足 `ψ⁰ (Ω ℓ₀) ≡ BTBOᴵ` (`refl`), 它才是 $\psi_0$ 意义下 $\Omega$ 的精确代表; `BTBOᴸ` 差一位.
> 2. **规则 4 越过不动点不需要新对象, 但要用 `ℓ₀` (§3).** `ts-label : Lab (ψ⁰ (suc (Ω ℓ₀))) ψ₀(Ω_Ω+1)`. 换成 `BTBOᴸ` 则不成立 (`shift-unlabel`, 已编译的否定; 两棵树的第 0 项分别是 $\gamma_2$, $\gamma_1$, 而 `γ12 : ¬ γ₂ ≅ γ₁`); `ψ⁰ (suc (Ω BTBOᴸ))` 的标签是另一个记号 $\psi_0(\Omega_{\psi_0(\Omega_\Omega)}+1)$ (`tbs-label`). 标签机器只**加引理** (和 `Lab-+`, 倍数 `Lab-rep`, 唯一性 `Lab-uniq`, 沿路径反演 `Lab-walk`), `Lab` 本身不改.
> 3. **朴素代表在 $\psi_0(\Omega_\Omega\cdot2)$ 处断 (§4).** `N2 = ψ⁰ (Ω ℓ₀ + Ω ℓ₀)` 的第 0 项正确 (它就是下文的 $\chi_1$, 遗传一致), 第 1 项的下标却是对角线的 $\gamma_1=\varepsilon_0$, 而 EBO 的第 1 项下标是规则 6 链的上一项 $\psi_0(\Omega_\Omega+\Omega)$ (`naive-mismatch : ¬ (γ₁ ≅ χ₁)`); 沿路径 $[1][0][1][0][0]$ 树走到 $0$, EBO 是 $\psi_0(\Omega_\Omega+\Omega_\omega)$ (`naive-unlabel`). 朴素的 $\psi^0(\Omega_{\ell_0+1})$ 第 0 项 `≡ BTBOᴵ` 正确, 但它的 $[1][0][0][2]$ **字面上就是** `N2`, EBO 侧恰是 $\psi_0(\Omega_\Omega\cdot2)$ (两边 `refl`), 故同样无标签 (`naiveO-unlabel`). 根因: 被计值的 $\Omega_\Omega$ 的 $\mathbb N$-序列必须是**上下文**的 $\gamma$-链, 而可数层号上的 $\Omega_\ell$ 只有一条固定的基本列.
> 4. **三个设计 (§5–§7, 对比表 §11).** **D1** (第二层, $\Omega_\Omega$ 节点的分支遍历全部可数树/层号) 否定: $\psi_\delta(\Omega_{a+1})$ 的忠实派发要判定 $a\prec^\mathsf I\delta$, 取 $\delta=\omega+1$ 推出 WLPO (`dec→WLPO`, 已编译). **D2** (下标层的 $\hat\Omega$, 其 $\Omega$ 只遍历 `BTBOᴵ` 之下的带证书树) 否定: `limᵢ` 的分支定义域是整个 `Ordᶜ i`, 限制定义域要新构造子; 而且上界太小: 规则 6 链的第二个点 $\chi_1=\psi_0(\Omega_\Omega+\Omega)$ 已在 `BTBOᴵ` 之上 (`BTBO≺χ1`, `χ1⊀BTBO`). **采用 D3**: 记号驱动的上下文对角线, 外层规则 6 在记号层面执行, 链 $\chi_0=1$, $\chi_{k+1}=\psi^0(\hat\Omega\oplus\Omega_{\mathtt{lvl}\,\chi_k})$; 每一步现场造一个层号 $M_k$ 同时以 `ℓ₀` 与 $\mathtt{lvl}\,\chi_k$ 为结构前驱, 步进证据由链携带的序证据 `ev : lim γ ⊑ χ_k` 给出 (公共上界逐步现造, 交替不变量); 前缀 $\hat\Omega$ 是提升到 $M_k$ 的 $\Omega_{\ell_0}$.
> 5. **决定性检验通过, 且更强 (§8).** 外层规则 6 形状 `refl` (`χ (k+2) ≡ ψ⁰ (K (Γ₂ k))`, `T₂ ≡ lim (χ ∘ suc)`), 记号侧 `diag2-fs : fsn ψ₀(Ω_Ω·2) n ≡ γ′ᴱ (n+1)`, $\gamma'^\mathsf E_{k+1}=\psi_0(\Omega_\Omega+\Omega_{\gamma'^\mathsf E_k})$ (`refl`). 链的前两项: `lab-χ0`, 以及 **`χ1-label : Lab χ₁ γ′ᴱ₁`**, 是遗传标签而不只是一步形状, 来自上下文引理 `Ctx₀` (任意带标签的可数 $Y$, $\psi^0(\Omega_{\ell_0}\oplus Y)$ 带 $\psi_0(\Omega_\Omega+y)$ 的标签). 于是 `T₂-0 : Lab T₂[0] ψ₀(Ω_Ω·2)[0]`; 在朴素树为 $0$ 的路径 $P$ 上, `T₂` 与 EBO 同形且 $P[0]$ 处带遗传标签 (`stage2-P`). `T₂` 有证书 (`T₂-HS`), 可回灌为层号 `T₂ᴸ`.
> 6. **第一处失败 (§9).** $\chi_2$ 无标签 (`χ2-unlabel`, 17 步路径), 故 `T₂` 无完整标签 (`stage2-unlabel`); D3 下最小的失败项是 $\psi_0(\Omega_\Omega+\Omega_2)$ (`X₂-unlabel`, 10 步). 原因都是: 前缀 $\Omega_\Omega$ 在 $\psi_\delta$ ($\delta\ge1$) 之下暴露时, EBO 穿透 ($\psi_\delta(\Omega_\Omega)$ 是 $\Omega_1$-共尾的, 随后由**那个**上下文的链计值), 而静态前缀 $\Omega_{\ell_0}$ 是 $\omega$-共尾的对角线.
> 7. **阶段 2 的遗传标签需要什么 (§10):** 符号化的 $\Omega_\Omega$ 与 $\psi_\delta(\Omega_\Omega)$ (不带分支的构造子), 折叠在每个 $\mu=0$ 的规则 6 处用上下文链计值并沿链携带序证据现造层号 (推广 `ev`/`pre`/`M`), 新族的一致引理, 以及记号侧把 Standard 的 `NF`/`cofin` 推广到唯一的不可数下标 $\Omega$.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件, 没有复制私有定义.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Stage2 where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; replicate; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Uniform using (Good; Good-add; Good-ψ⁰; Good-Ω; Good→HS; l-inv; ψ⁰-cong; add-cong; Ω-monoᵒ; idO)
import OCF.Align.NoCumsum as N
import OCF.Align.EBO as E
open E using (T; cω; cof; cofA; fsn; fsT; γT; Ωt; natT; sucT; dec) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; γᴱ; diag-fs; fs-Ωω; fs-rep; fs-ω; βᴱ)
open import OCF.Align.Label using (γ-label; BTBO-label; Good-lift)
```

## §0 记号与问题

EBO 里 $\Omega=\Omega_1$ 是 `Ωt (natT 1)` (下面记作 `Ωᵗ`), $\Omega_\Omega$ 是 `βᴱ = Ωt Ωᵗ`, 它的共尾度是 $\Omega_1$ (`cΩ []`), $\Omega_\Omega[\eta]=\Omega_\eta$ (`fsT βᴱ η ≡ Ωt η`, Correspond §7). 于是只要某个 $\psi_u(b)$ 的 $b$ 以 $\Omega_\Omega$ 结尾:

- $u=0$: 规则 6, $\mu=0$, 链 $\gamma_0=\Omega_0=1$, $\gamma_{k+1}=\psi_0(b[\gamma_k])$, $\psi_0(b)[n]=\psi_0(b[\gamma_n])$. **链依赖整个 $b$**: $b=\Omega_\Omega$ 时就是对角线 $\gamma$, $b=\Omega_\Omega+\Omega_\Omega$ 时是另一条链 $\gamma'$.
- $u=\delta\ge1$ 可数: 规则 5Ω, 穿透, $\psi_\delta(b)$ 本身是 $\Omega_1$-共尾的, 第 $\eta$ 项 $\psi_\delta(b[\eta])$; 在外层 $\psi_0$ 的规则 6 里再用那一层的链计值.
- $u=\Omega$ (不可数目标层, $\psi_0(\Omega_{\Omega+1})$ 的链里出现): 同样穿透.

树这边层号可数, $\Omega_\Omega$ 只能以某个可数层号 $\ell$ 上的 $\Omega_\ell$ 代表; 若 $\ell$ 是对角层号, $\Omega_\ell$ 是 $\mathbb N$-极限, 其基本列固定. 本文的问题就是: 这种固定的 $\mathbb N$-序列什么时候恰好等于 EBO 的上下文链, 不等时怎么办.

## §1 事实 1: 种子步

两个对角层号. `BTBOᴸ` 是 NoCumsum 的 `toLevel BTBOᴵ _`, 其序列从 $L_1$ 开始; `ℓ₀` 是包含 $\gamma_0=1$ 的整条对角线 `lim γ` 的层号, 证书由 Diagonal 的 `diag-step` 给出.

```agda
lγ-HS : HS (lim N.γ)
lγ-HS = hl N.cert N.D.diag-step

ℓ₀ : Ordᴵ
ℓ₀ = toLevel (lim N.γ) lγ-HS

_ : ψ⁰ (Ω ℓ₀) ≡ N.BTBOᴵ
_ = refl

_ : ψ⁰ (Ω N.BTBOᴸ) ≡ lim (λ n → N.γ (suc (suc n)))
_ = refl
```

第一条: $\psi^0(\Omega_{\ell_0})$ **字面上就是** `BTBOᴵ` ($\Omega_{\ell_0}$ 的第 $n$ 项是 $\Omega_{L_n}$, 折叠后是 $\gamma_{n+1}$). 第二条: $\psi^0(\Omega_{\mathtt{BTBO}^\mathsf L})$ 是对角线平移一位. 种子步与它的逆都成立, 都只用 `diag-step`:

```agda
seed : N.BTBOᴵ ⊑ ψ⁰ (Ω N.BTBOᴸ)
seed (≺l n h) = ≺l n (N.D.diag-step (suc n) h)

seed⁻ : ψ⁰ (Ω N.BTBOᴸ) ⊑ N.BTBOᴵ
seed⁻ (≺l n h) = ≺l (suc n) h
```

所以从 `BTBOᴵ` 重起对角线 (Diagonal §5 第 3 条) 不升值: 新对角线的第一项与旧的极限互为 $\sqsubseteq$. EBO 侧对应的项是 $\psi_0(\Omega_{\psi_0(\Omega_\Omega)})$: 下标 $\psi_0(\Omega_\Omega)$ 的共尾度为 $\omega$, 规则 3 给 $\psi_0(\Omega_{\psi_0(\Omega_\Omega)[n]})=\gamma^\mathsf E_{n+2}$. 树与它遗传一致 (每一项用 Label 的 `γ-label`).

```agda
tb : T
tb = ψᵗ [] (Ωt (E.EBOψ 2)) ∷ []

_ : cof tb ≡ cω
_ = refl

tb-fs : ∀ n → fsn tb n ≡ γᴱ (suc (suc n))
tb-fs n = trans (fs-Ωω (ψᵗ [] βᴱ) [] refl n) (cong (λ z → ψᵗ [] (Ωt z) ∷ []) (diag-fs n))

tb-label : Lab (ψ⁰ (Ω N.BTBOᴸ)) tb
tb-label = lω refl (l≅ (λ n → ≅-refl⁰ _)) (λ n → subst (Lab (N.γ (suc (suc n)))) (sym (tb-fs n)) (γ-label (suc n)))
```

**读法.** 事实 1 证实: 按 EBO 的基本列语义, $\psi_0(\Omega_{\psi_0(\Omega_\Omega)})$ 与 $\psi_0(\Omega_\Omega)$ 只差一位, 是同一个值; 交替原则下"把对角对象回灌成下标再折叠"本身不前进. 前进要靠下标层之外的东西: 规则 4 (§3) 或上下文链 (§7).

## §2 标签工具

Correspond 的 `Lab` 原样使用, 本节只加引理. `Lab-+`: 和的标签 ($X$ 标 $x$, $Y$ 标 $ys$, 则 $X+Y$ 标 $x\mathbin{::}ys$), 对 $Y$ 的标签递归; 记号侧规则 1 的三种情况都是定义性的 (`cof`, `pred`, `fsn` 在 $x\mathbin{::}y\mathbin{::}ys$ 上直接落到 $y\mathbin{::}ys$). `Lab-rep`: 规则 4 的倍数 $X\cdot n$ 标 `replicate n x`. `Lab-uniq`: 同一个项的两个标签树 $\cong$.

```agda
Lab-+ : ∀ {X Y x ys} → Lab X (x ∷ []) → Lab Y ys → Lab (X + Y) (x ∷ ys)
Lab-+ {ys = []}     hX (l0 c e) = Lab-≅ (add-≅ {σ = λ q → q} {σ′ = λ q → q} (≅-refl⁰ _) e) hX
Lab-+ {ys = y ∷ ys} hX (l0 c e) = ⊥-elim (cof-ne y ys c)
Lab-+ {ys = []}     hX (l1 () e l)
Lab-+ {ys = y ∷ ys} hX (l1 c e l) = l1 c (add-≅ (≅-refl⁰ _) e) (Lab-+ hX l)
Lab-+ {ys = []}     hX (lω () e h)
Lab-+ {ys = y ∷ ys} hX (lω c e h) = lω c (add-≅ (≅-refl⁰ _) e) (λ n → Lab-+ hX (h n))

Lab-rep : ∀ {X x} → Lab X (x ∷ []) → ∀ n → Lab (iter (X +_) zero n) (replicate n x)
Lab-rep hX zero    = l0 refl z≅
Lab-rep hX (suc n) = Lab-+ hX (Lab-rep hX n)

Lab-uniq : ∀ {A B t} → Lab A t → Lab B t → A ≅ B
Lab-uniq (l0 c e) (l0 c′ e′) = ≅-trans e (≅-sym e′)
Lab-uniq (l0 c e) (l1 c′ e′ l′) with trans (sym c) c′
... | ()
Lab-uniq (l0 c e) (lω c′ e′ h′) with trans (sym c) c′
... | ()
Lab-uniq (l1 c e l) (l0 c′ e′) with trans (sym c) c′
... | ()
Lab-uniq (l1 c e l) (l1 c′ e′ l′) = ≅-trans e (≅-trans (s≅ (Lab-uniq l l′)) (≅-sym e′))
Lab-uniq (l1 c e l) (lω c′ e′ h′) with trans (sym c) c′
... | ()
Lab-uniq (lω c e h) (l0 c′ e′) with trans (sym c) c′
... | ()
Lab-uniq (lω c e h) (l1 c′ e′ l′) with trans (sym c) c′
... | ()
Lab-uniq (lω c e h) (lω c′ e′ h′) = ≅-trans e (≅-trans (l≅ (λ n → Lab-uniq (h n) (h′ n))) (≅-sym e′))
```

否定结论的工具: 沿基本列路径反演标签. `sq X n` 取第 0 层树的第 $n$ 项 (非 `lim` 返回自身), `walk`/`walkᵀ` 沿一串下标走树与记号. 若 `Lab X t` 且路径上每个记号都是 $\omega$-共尾 (`Allω`, 由 `refl` 填), 则终点仍带标签 (`Lab-walk`); 终点的树若是 `zero` 而记号仍 $\omega$-共尾, 矛盾 (`Lab0`). 这样每个否定都归结为两侧的计算.

```agda
sq : Ordᶜ zero → ℕ → Ordᶜ zero
sq (lim f) n = f n
sq x       n = x

Lab0 : ∀ {t} → Lab zero t → cof t ≡ cω → ⊥
Lab0 (l0 c e) c′ with trans (sym c) c′
... | ()
Lab0 (l1 c () l) c′
Lab0 (lω c () h) c′

Labω : ∀ {G t} → Lab (lim G) t → cof t ≡ cω → ∀ n → Lab (G n) (fsn t n)
Labω (l0 c e) c′ with trans (sym c) c′
... | ()
Labω (l1 c e l) c′ with trans (sym c) c′
... | ()
Labω (lω c e h) c′ n = Lab-≅ (l-inv e n) (h n)

sqLab : ∀ {X t} → Lab X t → cof t ≡ cω → ∀ n → Lab (sq X n) (fsn t n)
sqLab {X = lim G} l c n = Labω l c n
sqLab {X = zero}  l c n = ⊥-elim (Lab0 l c)
sqLab {X = suc Y} (l0 c e) c′ n with trans (sym c) c′
... | ()
sqLab {X = suc Y} (l1 c e l) c′ n with trans (sym c) c′
... | ()
sqLab {X = suc Y} (lω c () h) c′ n
sqLab {X = limᵢ () f} l c n
sqLab {X = up () x} l c n

walk : Ordᶜ zero → List ℕ → Ordᶜ zero
walk X []      = X
walk X (n ∷ p) = walk (sq X n) p

walkᵀ : T → List ℕ → T
walkᵀ t []      = t
walkᵀ t (n ∷ p) = walkᵀ (fsn t n) p

Allω : T → List ℕ → Set
Allω t []      = ⊤
Allω t (n ∷ p) = (cof t ≡ cω) × Allω (fsn t n) p

Lab-walk : ∀ {X t} p → Lab X t → Allω t p → Lab (walk X p) (walkᵀ t p)
Lab-walk []      l _        = l
Lab-walk (n ∷ p) l (c , cs) = Lab-walk p (sqLab l c n) cs
```

两条对角线项不 $\cong$: $\gamma_2[0][1]$ 是 $\psi^0(\Omega_1)$ (一个 `lim`), $\gamma_1[0][1]$ 是 $1$ (一个 `suc`). 覆盖检查器直接看出 `lim ≅ suc` 无构造子.

```agda
γ12 : ¬ (N.γ 2 ≅ N.γ 1)
γ12 e with l-inv (l-inv e 0) 1
... | ()
```

## §3 事实 2: 规则 4 越过不动点

EBO 的 $\psi_0(\Omega_\Omega+1)$: 参数后继, 规则 4, 第 $n$ 项 $\psi_0(\Omega_\Omega)\cdot n$ (`ts-fs`, 由 Correspond 的 `fs-rep`). 树侧 `ψ⁰ (suc (Ω ℓ₀))` 定义性地是 `lim (iter (BTBOᴵ +_) zero)`, 每项由 `Lab-rep` 与 `BTBO-label` 标好.

```agda
ts : T
ts = ψᵗ [] (sucT βᴱ) ∷ []

_ : cof ts ≡ cω
_ = refl

ts-fs : ∀ n → fsn ts n ≡ replicate n (ψᵗ [] βᴱ)
ts-fs n = fs-rep [] _ _ refl n

ts-label : Lab (ψ⁰ (suc (Ω ℓ₀))) ts
ts-label = lω refl (l≅ (λ n → ≅-refl⁰ _)) (λ n → subst (Lab _) (sym (ts-fs n)) (Lab-rep BTBO-label n))
```

用 `BTBOᴸ` 不行: 若 `ψ⁰ (suc (Ω BTBOᴸ))` 带 $\psi_0(\Omega_\Omega+1)$ 的标签, 它的第 1 项 $\psi^0(\Omega_{\mathtt{BTBO}^\mathsf L})$ 就带 $\psi_0(\Omega_\Omega)$ 的标签, 由唯一性 $\cong$ `BTBOᴵ`, 取第 0 项得 $\gamma_2\cong\gamma_1$, 与 `γ12` 矛盾. 它真正的标签是 $\psi_0(\Omega_{\psi_0(\Omega_\Omega)}+1)$.

```agda
shift-unlabel : ¬ Lab (ψ⁰ (suc (Ω N.BTBOᴸ))) ts
shift-unlabel l = γ12 (l-inv (Lab-uniq (subst (Lab _) (ts-fs 1) (Labω l refl 1)) BTBO-label) 0)

tbs : T
tbs = ψᵗ [] (sucT (Ωt (E.EBOψ 2))) ∷ []

tbs-label : Lab (ψ⁰ (suc (Ω N.BTBOᴸ))) tbs
tbs-label = lω refl (l≅ (λ n → ≅-refl⁰ _)) (λ n → subst (Lab _) (sym (fs-rep [] _ _ refl n)) (Lab-rep tb-label n))
```

**读法.** 事实 2 成立, 但取决于代表层号: $\Omega_{\ell_0}$ 是 $\psi_0$ 意义下 $\Omega_\Omega$ 的精确代表, $\Omega_{\mathtt{BTBO}^\mathsf L}$ 精确代表的是另一个 (非标准的) 记号 $\Omega_{\psi_0(\Omega_\Omega)}$. 标签机器的扩充只是 §2 的引理.

## §4 事实 3: 朴素代表在哪里断

EBO 的 $\psi_0(\Omega_\Omega\cdot2)$ (`t2`): 参数的末项 $\Omega_\Omega$ 共尾度 $\Omega_1$, 规则 6, $\mu=0$, 链 $\gamma'_0=1$, $\gamma'_{k+1}=\psi_0(\Omega_\Omega+\Omega_{\gamma'_k})$, 第 $n$ 项 $\psi_0(\Omega_\Omega+\Omega_{\gamma'_n})$. 朴素的树 `N2 = ψ⁰ (Ω ℓ₀ + Ω ℓ₀)`: 第二个 $\Omega_{\ell_0}$ 是 `lim`, 共尾度 $\omega$, 第 $n$ 项 $\psi^0(\Omega_{\ell_0}\oplus\Omega_{L_n})$, 下标是**对角线** $L_n$. 两边都是 $\omega$-共尾; 第 0 项两边都是 $\psi_0(\Omega_\Omega+\Omega_1)$ ($L_0=1=\gamma'_0$), 第 1 项的下标分别是 $\gamma_1=\varepsilon_0$ 与 $\gamma'_1=\psi_0(\Omega_\Omega+\Omega)$.

```agda
Ωᵗ : T
Ωᵗ = Ωt (natT 1)

t2 : T
t2 = ψᵗ [] (βᴱ ++ βᴱ) ∷ []

N2 : Ordᶜ zero
N2 = ψ⁰ (Ω ℓ₀ + Ω ℓ₀)

_ : cof t2 ≡ cω
_ = refl

_ : fsn t2 0 ≡ ψᵗ [] (ψᵗ Ωᵗ [] ∷ ψᵗ (natT 1) [] ∷ []) ∷ []
_ = refl

_ : sq N2 1 ≡ ψ⁰ (add (Ω ℓ₀) (λ q → lim 1 q) (Ω (N.L 1)))
_ = refl
```

决定性的不一致是路径 $P=[1][0][1][0][0]$: EBO 依次是 $\psi_0(\Omega_\Omega+\Omega_{\gamma'_1})$, $\psi_0(\Omega_\Omega+\Omega_{\psi_0(\Omega_\Omega+1)})$, $\psi_0(\Omega_\Omega+\Omega_{\psi_0(\Omega_\Omega)})$, $\psi_0(\Omega_\Omega+\Omega_{\varepsilon_0})$, $\psi_0(\Omega_\Omega+\Omega_\omega)$, 全部 $\omega$-共尾; 树的下标走 $\varepsilon_0\to\omega\to1$ 后成了 $\psi^0(\Omega_{\ell_0}+1)$, 再取第 0 项得 $0$.

```agda
P5 : Ordᶜ zero → Ordᶜ zero
P5 X = sq (sq (sq (sq (sq X 1) 0) 1) 0) 0

_ : P5 N2 ≡ zero
_ = refl

naive-unlabel : ¬ Lab N2 t2
naive-unlabel l = Lab0 (Labω (Labω (Labω (Labω (Labω l refl 1) refl 0) refl 1) refl 0) refl 0) refl
```

$\psi_0(\Omega_{\Omega+1})$ (`tO`): $\Omega_{\Omega+1}$ 正规, 共尾度自身, 规则 6 的链在层 $\Omega$ 上: $\zeta_0=\Omega_\Omega$, $\zeta_{k+1}=\psi_\Omega(\zeta_k)$. 朴素树把层 $\Omega$ 换成 $\ell_0$: `NO = ψ⁰ (Ω (suc ℓ₀))`, 链 $\Omega_{\ell_0}$, $\psi_{\ell_0}(\Omega_{\ell_0})$, …. 第 0 项两边一致 (树 `≡ BTBOᴵ`, 记号 `≡ EBOψ 2`). 但沿 $[1][0][0][2]$ 两边分别**字面地**到达 `N2` 与 `t2`: $\psi_0(\psi_\Omega(\Omega_\Omega))\to\psi_0(\psi_\Omega(\Omega_1))\to\psi_0(\psi_\Omega(1))\to\psi_0(\Omega_\Omega\cdot2)$, 树侧 $\psi_{\ell_0}(0)=\Omega_{\ell_0}$, 于是 $\psi_{\ell_0}(1)$ 的第 2 项正是 $\Omega_{\ell_0}+\Omega_{\ell_0}$.

```agda
tO : T
tO = ψᵗ [] (Ωt (sucT Ωᵗ)) ∷ []

NO : Ordᶜ zero
NO = ψ⁰ (Ω (suc ℓ₀))

_ : cof tO ≡ cω
_ = refl

_ : fsn tO 0 ≡ E.EBOψ 2
_ = refl

_ : sq NO 0 ≡ N.BTBOᴵ
_ = refl

_ : fsn (fsn (fsn (fsn tO 1) 0) 0) 2 ≡ t2
_ = refl

_ : sq (sq (sq (sq NO 1) 0) 0) 2 ≡ N2
_ = refl

naiveO-unlabel : ¬ Lab NO tO
naiveO-unlabel l = naive-unlabel (Labω (Labω (Labω (Labω l refl 1) refl 0) refl 0) refl 2)
```

**读法.** 事实 3 的不一致不在共尾度 (两边都是 $\omega$), 而在第 1 项起的下标: EBO 的规则 6 让第二个 $\Omega_\Omega$ 沿**上下文**链 $\gamma'$ 取值, 朴素树只能沿 $\Omega_{\ell_0}$ 自带的对角线 $L_n$ 取值. 换任何别的可数层号 $\ell$ 也一样: $\psi^0(\Omega_\ell)$ 要 $\cong$ `BTBOᴵ` 就迫使 $\ell$ 的第 $n$ 项给出 $\gamma_{n+1}$, 即 $\ell\cong^\mathsf I\ell_0$ (纸面: 逐项比较), 而上下文链的点 $\gamma'_k$ ($k\ge1$) 都在 `BTBOᴵ` 之上 (§6), 层号 $\ell_0$ 装不下它们. $\psi_0(\Omega_{\Omega+1})$ 的朴素树在 $\psi_0(\Omega_\Omega\cdot2)$ 这个后代处继承了同一个失败.

## §5 设计 D1: 第二层, 分支遍历全部可数下标

D1 设想一个新的树族, 其中 $\Omega_\Omega$ 是真正的 $\Omega_1$-共尾节点: 分支函数 $\eta\mapsto\Omega_\eta$ 定义在全部 (带证书的) 第 0 层树或全部层号上, 第二层节点不挂在固定层号上. 这样 §4 的上下文链自然由折叠的规则 6 产生. 问题出在 §0 的第二种情况: $\psi_\delta(\Omega_\Omega)$ ($\delta\ge1$ 可数) 穿透, 它的分支 $\eta\mapsto\psi_\delta(\Omega_\eta)$ 要对**每个** $\eta$ 决定规则: $\eta=a+1$ 时, $a+1\le\delta$ 穿透 (节点挂在 $\delta$ 的某个结构前驱上), $a+1>\delta$ 折叠. 这就是对任意 $a$ 判定 $a\prec^\mathsf I\delta$ (模 $\cong^\mathsf I$, 与 `<ᴵ-dec` 的派发同一含义), 而 $a$ 与 $\delta$ 在下标层没有公共上界. 取 $\delta=\omega+1$: 对二进制序列 $s$ 造层号 $a_s=\lim_n g_n$, $g_n=n$ 直到 $s$ 出现第一个 $1$, 此后 $g_n=n+1$. 则 $a_s\prec^\mathsf I\omega+1$ 当且仅当 $a_s\cong^\mathsf I\omega$ 当且仅当 $s$ 恒为 `false`.

```agda
any : (ℕ → Bool) → ℕ → Bool
any s zero    = s zero
any s (suc n) = any s n ∨ s (suc n)

g : Bool → ℕ → Ordᴵ
g true  n = natᴵ (suc n)
g false n = natᴵ n

gstep : ∀ b c n → g b n ⊑ᴵ g (b ∨ c) (suc n)
gstep true  c     n = Sim→⊑ᴵ suc
gstep false true  n = Sim→⊑ᴵ (λ q → suc (suc q))
gstep false false n = Sim→⊑ᴵ suc

aₛ : (ℕ → Bool) → Ordᴵ
aₛ s = lim (λ n → g (any s n) n) (λ n → gstep (any s n) (s (suc n)) n)

WLPO : Set
WLPO = ∀ (s : ℕ → Bool) → (∀ n → s n ≡ false) ⊎ ¬ (∀ n → s n ≡ false)

any-false : ∀ {s} → (∀ n → s n ≡ false) → ∀ n → any s n ≡ false
any-false h zero    = h zero
any-false {s} h (suc n) rewrite any-false h n | h (suc n) = refl

any-true : ∀ {s} n → s n ≡ true → any s n ≡ true
any-true zero    e = e
any-true {s} (suc n) e rewrite e with any s n
... | true  = refl
... | false = refl

nat-neq : ∀ n → ¬ (natᴵ (suc n) ≅ᴵ natᴵ n)
nat-neq zero    ()
nat-neq (suc n) (s≅ e) = nat-neq n e

data IsNat : Ordᴵ → Set where
  nz : IsNat zero
  ns : ∀ {a} → IsNat a → IsNat (suc a)

natIs : ∀ n → IsNat (natᴵ n)
natIs zero    = nz
natIs (suc n) = ns (natIs n)

lim≮ : ∀ {b} {f : ℕ → Ordᴵ} {t : ∀ n → f n ⊑ᴵ f (suc n)} → IsNat b → lim f t <ᴵ b → ⊥
lim≮ nz      ()
lim≮ (ns ()) zero
lim≮ (ns i)  (suc q) = lim≮ i q

claim₁ : ∀ s → (∀ n → s n ≡ false) → aₛ s ≺ᴵ suc ωᴵ
claim₁ s h = via (l≅ (λ n → subst (λ b → g b n ≅ᴵ natᴵ n) (sym (any-false h n)) (≅ᴵ-refl _))) zero

claim₂ : ∀ s → aₛ s ≺ᴵ suc ωᴵ → ∀ n → s n ≡ false
claim₂ s (via (l≅ h) zero) n with s n in eq
... | false = refl
... | true  = ⊥-elim (nat-neq n (subst (λ b → g b n ≅ᴵ natᴵ n) (any-true n eq) (h n)))
claim₂ s (via (l≅ h) (suc (lim m q))) n = ⊥-elim (lim≮ (natIs m) q)

dec→WLPO : (∀ a → Dec (a ≺ᴵ suc ωᴵ)) → WLPO
dec→WLPO d s with d (aₛ s)
... | yes p = inj₁ (claim₂ s p)
... | no ¬p = inj₂ (λ h → ¬p (claim₁ s h))
```

`claim₂` 的第二个子句: $a_s$ 是 `lim`, 不能 $\cong^\mathsf I$ 于 $\omega$ 的任何有限前驱 (`lim≮`, 为避开 `natᴵ m` 对变量 $m$ 卡住的合一, 改用谓词 `IsNat`).

**判定: D1 否定.** 在 `--safe --without-K` 下 WLPO 不可证 (与 Barrier 的 LPO 同一个元定理: 闭项会判定停机), 所以 $\psi_\delta(\Omega_\Omega)$ 的分支不能既全又忠实. 这是壁垒在分支层面的形态: 不是"下标类型有 $\Omega$-共尾元", 而是"分支要拿任意可数下标去和一个固定下标比". 证书 (`HS`) 不救它: $a_s$ 模 $\cong^\mathsf I$ 就是一棵带证书的第 0 层树 (自然数树的单调极限) 的 `toLevel` 像 (纸面, 未编译). 只剩两条路: 限制分支的定义域 (D2), 或根本不给 $\Omega_\Omega$ 分支函数 (D3).

## §6 设计 D2: 有界定义域的 $\hat\Omega$

D2 设想下标层的对象 $\hat\Omega$, 其 $\Omega$ 是一个 `limᵢ`, 分支只遍历 `BTBOᴸ` 之下的带证书树, 例如 $\{x : \mathsf{Ord}^\mathsf c\,0\mid\mathsf{HS}\,x,\ x\prec\mathtt{BTBO}^\mathsf I\}$. 两个障碍.

- **类型.** `limᵢ p f` 的 `f : U i (<→◃ p) → Ord₊`, 定义域是整个 `Ordᶜ i`; 带谓词的定义域要新构造子, 例如 `limᴮ : ((x : Ordᶜ zero) → HS x → x ≺ B → Ord₊) → Ord₊`. 它严格正 (`HS`、`≺` 都先于族定义), 但这就离开了现有的族, 而树族、`ψ`、`Good`、`Uniform` 都要随之重做. 用全函数加"截断" (定义域外给垃圾值) 绕开新构造子, 截断本身要判定 $x\prec B$, 回到 §5.
- **上界太小.** 即便有 `limᴮ`, 规则 6 的链在上界之外计值: $\psi_0(\Omega_\Omega\cdot2)$ 的链的第二个点 $\chi_1=\psi_0(\Omega_\Omega+\Omega)$ (下面的 `K₀`, §7 的 $\chi_1$) 已在 `BTBOᴵ` 之上. $\chi_1[0][2][0][0][1]$ 是 $\mathtt{BTBO}^\mathsf I+1$, 所以 $\mathtt{BTBO}^\mathsf I\prec\chi_1$; 反向不成立 (否则经 `≺→⊑` 得 $\mathtt{BTBO}^\mathsf I\prec\mathtt{BTBO}^\mathsf I$).

```agda
K₀ : Ordᶜ ℓ₀
K₀ = add (Ω ℓ₀) (λ q → lim 0 q) (Ω (suc zero))

_ : sq N2 0 ≡ ψ⁰ K₀
_ = refl

≺→⊑ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≺ b → a ⊑ b
≺→⊑ (≺z e)      h = ≺s (≺-respʳ h e)
≺→⊑ (≺s p)      h = ≺s (≺→⊑ p h)
≺→⊑ (≺l n p)    h = ≺l n (≺→⊑ p h)
≺→⊑ (≺i x ex p) h = ≺i x ex (≺→⊑ p h)
≺→⊑ (≺u p)      h = ≺u (≺→⊑ p h)

BTBO≺χ1 : N.BTBOᴵ ≺ ψ⁰ K₀
BTBO≺χ1 = ≺l 0 (≺l 2 (≺l 0 (≺l 0 (≺l 1 (≺z (≅-refl⁰ _))))))

χ1⊀BTBO : ¬ (ψ⁰ K₀ ≺ N.BTBOᴵ)
χ1⊀BTBO p = ≺-irrefl (≺→⊑ p BTBO≺χ1)
```

**判定: D2 否定.** 任何**事先固定**的可数上界 $B$ 都有同样的问题: $\psi_0(b)$ 的规则 6 链只被 $\psi_0(b)$ 自身界住, 而 $B$ 要在定义 $\psi_0(b)$ 的树之前给出. §9 还会看到链点要在比 $\chi_1$ 大得多的地方计值. D2 留下的有用部分是"定义域有界、界由证据给出"; D3 把界改成**逐步现造**.

## §7 设计 D3: 记号驱动的上下文对角线

D3 不造 $\Omega_\Omega$ 这个对象, 而是在记号层面执行它的规则 6: $\psi_0(\Omega_\Omega\cdot2)$ 的树就是链 $\chi_0=1$, $\chi_{k+1}=\psi^0(K_k)$ 的极限, $K_k$ 是 "$\Omega_\Omega+\Omega_{\chi_k}$" 在某个可数层号 $M_k$ 上的树. 这正是交替原则的读法: $\Omega_\Omega$ 只以对角 $\mathbb N$-极限出现, 而这个对角线由折叠它的上下文决定; 每个链点折叠后回灌成下标, 再开一层.

$K_k$ 有两个分量, 都要求 $M_k$ 有相应的结构前驱:

- **前缀** $\hat\Omega=\Omega_{\ell_0}$, 经 `up (self 0)` 提升到 $M_k$: 当它被暴露给 $\psi^0$ 时 (例如 $\psi_0(\Omega_\Omega+0)$), 折叠的结果字面上是 `BTBOᴵ`, 即 §3 的精确代表. 需要 $\ell_0\triangleleft M_k$.
- **末项** $\Omega_{\mathtt{lvl}\,\chi_k}$: 需要 `Sim (lvl χₖ) Mₖ`.

在下标层里, "同时以两个层号为结构前驱"只能是一个 `lim`, 要步进证据 $\ell_0\sqsubseteq^\mathsf I\mathtt{lvl}\,\chi_k$; 没有比较就不能取 max. 所以链除了树与证书还携带**序证据** `ev : lim γ ⊑ χₖ`, 层号是 `toLevel (lim [lim γ, χₖ, χₖ, …])`, 它的第 0 项**定义性地**就是 `ℓ₀`, 第 1 项就是 `lvl χₖ`. 序证据由下面的 `pre` 逐步再生: $\psi^0(P\oplus\Omega_L)\sqsupseteq\psi^0(P)$, 沿 $\Omega_L$ 的第 0 项一路下到 $\psi^0(P+1)$, 其第 1 项就是 $\psi^0(P)$.

```agda
lγ⊑BTBO : lim N.γ ⊑ N.BTBOᴵ
lγ⊑BTBO (≺l n h) = ≺l n (N.D.diag-step n h)

pre : ∀ L {M} (σ : Simᴵ L M) {P : Ordᶜ M} → ψ⁰ P ⊑ ψ⁰ (add P σ (Ω L))
pre zero      σ h = ≺l 1 h
pre (suc L)   σ {P} h = ≺l 0 (subst (λ z → _ ≺ ψ⁰ (add P (λ q → σ (suc q)) z)) (sym (out-into (<→◃ (σ zero)) (Ω L)))
                                     (pre L (λ q → σ (suc q)) h))
pre (lim f s) σ h = ≺l 0 (pre (f 0) (λ q → σ (lim 0 q)) h)
```

`pre` 的后继情况: $\Omega_{L+1}$ 是 `limᵢ zero (up zero)`, 加上前缀后节点的下标证明是抽象的 `σ zero`, 链起点 $\Omega_L$ 经 `into`/`out` 往返, 用 Cumulative 的 `out-into` 化回. 这是全文唯一一处命题等式搬运.

链的状态, 每步的层号与树. `Bseq x` 是序列 $[\lim\gamma, x, x,\ldots]$; `BH`/`Bst` 给它的证书 (第 0 步由 `ev`, 其余自反).

```agda
record St : Set where
  constructor st
  field
    x  : Ordᶜ zero
    hx : HS x
    ev : lim N.γ ⊑ x
open St

Bseq : Ordᶜ zero → ℕ → Ordᶜ zero
Bseq x zero    = lim N.γ
Bseq x (suc _) = x

BH : ∀ {x} → HS x → ∀ n → HS (Bseq x n)
BH h zero    = lγ-HS
BH h (suc _) = h

Bst : ∀ {x} → lim N.γ ⊑ x → ∀ n → Bseq x n ⊑ Bseq x (suc n)
Bst ev zero    = ev
Bst ev (suc n) = λ h → h

M : St → Ordᴵ
M s = toLevel (lim (Bseq (x s))) (hl (BH (hx s)) (Bst (ev s)))

Lv : St → Ordᴵ
Lv s = toLevel (x s) (hx s)

Ω̂ : ∀ s → Ordᶜ (M s)
Ω̂ s = up (self 0) (Ω ℓ₀)

K : ∀ s → Ordᶜ (M s)
K s = add (Ω̂ s) (λ q → lim 1 q) (Ω (Lv s))

_ : ∀ s → ψ⁰ (Ω̂ s) ≡ N.BTBOᴵ
_ = λ s → refl
```

`Ω̂ s` 的类型检查本身就是"第 0 项定义性地是 `ℓ₀`"的证明 (`hl₁` 在 `hl` 上归约, `BH h zero` 归约成 `lγ-HS`); `λ q → lim 1 q` 的类型检查同理是"第 1 项就是 `Lv s`". 最后一行: 前缀被 $\psi^0$ 折叠时字面上是 `BTBOᴵ`.

每一步的证书来自 Uniform 的 `Good` 封闭性 ($K_k$ 是第一层族里的普通对象, `Good-lift` 取自 Label), 序证据来自 `pre`. 第一步 ($\chi_0=1\sqsubseteq\ell_0$ 的方向反过来) 单独处理: $K_0$ 直接放在 $\ell_0$ 上, 末项 $\Omega_1$ 经 `lim 0` 进入 (§6 的 `K₀`, 它也是朴素树 `N2` 的第 0 项).

```agda
Ω̂-refl : ∀ s → Ω̂ s ≅ Ω̂ s
Ω̂-refl s = upˡ (upʳ (Ω-refl ℓ₀))

K-refl : ∀ s → K s ≅ K s
K-refl s = add-≅ {σ = λ q → lim 1 q} {σ′ = λ q → lim 1 q} (Ω̂-refl s) (Ω-refl (Lv s))

K-good : ∀ s → Good (K s)
K-good s = Good-add (Good-lift (self 0) (Good-Ω ℓ₀)) (Ω̂-refl s) (Good-Ω (Lv s))

step : St → St
step s = st (ψ⁰ (K s)) (Good→HS (Good-ψ⁰ (K-good s) (K-refl s))) (λ h → pre (Lv s) (λ q → lim 1 q) (lγ⊑BTBO h))

K₀-refl : K₀ ≅ K₀
K₀-refl = add-≅ {σ = λ q → lim 0 q} {σ′ = λ q → lim 0 q} (Ω-refl ℓ₀) (Ω-refl (suc zero))

s₁ : St
s₁ = st (ψ⁰ K₀) (Good→HS (Good-ψ⁰ (Good-add (Good-Ω ℓ₀) (Ω-refl ℓ₀) (Good-Ω (suc zero))) K₀-refl))
        (λ h → pre (suc zero) (λ q → lim 0 q) (lγ⊑BTBO h))

Γ₂ : ℕ → St
Γ₂ zero    = s₁
Γ₂ (suc k) = step (Γ₂ k)

χ : ℕ → Ordᶜ zero
χ zero    = suc zero
χ (suc k) = x (Γ₂ k)

T₂ : Ordᶜ zero
T₂ = lim (λ k → x (Γ₂ k))
```

**对角对象回灌下标层.** 与 Diagonal 的 `BTBO-HS` 一样, `T₂` 自己遗传步进: 相邻两项经 `ψ⁰-cong`/`add-cong`/`Ω-monoᵒ` (Uniform 的观测前序), 下标的一步由上一步经 `toLevel-⊑` 给出; 第 0 步用 $1\sqsubseteq\psi^0(\cdot)$. 于是 `T₂ᴸ` 是下一阶段可用的层号. FGH 的小值照常可算.

```agda
one⊑ : ∀ {k} {y : Ordᶜ k} → _⊑_ {ℓ₁ = zero} (suc zero) (ψ⁰ y)
one⊑ (≺z e) = ≺-respˡ (≅-sym e) (z≺ψ⁰ _)

χ-step : ∀ k → x (Γ₂ k) ⊑ x (Γ₂ (suc k))
χ-step zero = ψ⁰-cong {x = K₀} {y = K s₁}
  (add-cong (upʳ (Ω-refl ℓ₀)) (Ω-monoᵒ (toLevel-⊑ (hs hz) (hx s₁) (one⊑ {y = K₀})))) idO
χ-step (suc k) = ψ⁰-cong {x = K (Γ₂ k)} {y = K (Γ₂ (suc k))}
  (add-cong (upˡ (upʳ (Ω-refl ℓ₀))) (Ω-monoᵒ (toLevel-⊑ (hx (Γ₂ k)) (hx (Γ₂ (suc k))) (χ-step k)))) idO

T₂-HS : HS T₂
T₂-HS = hl (λ k → hx (Γ₂ k)) χ-step

T₂ᴸ : Ordᴵ
T₂ᴸ = toLevel T₂ T₂-HS

_ : FGH T₂ 1 ≡ 2
_ = refl

_ : FGH (ψ⁰ (Ω T₂ᴸ)) 1 ≡ 2
_ = refl
```

`ψ⁰-cong` 的隐式参数必须显式给出: 期望类型里的 `ψ⁰ K₀` 已归约成 `lim …`, 合一 `ψ⁰ ?y = lim …` 解不出 (`[UnsolvedConstraints]`, 首次编译所见); `one⊑` 同样要指明 `ℓ₁ = zero` (否则 `suc zero` 的层号是未定元, 匹配 `≺z` 时 `[SplitError.UnificationStuck]`).

## §8 决定性检验

**记号侧.** $b_2=\Omega_\Omega+\Omega_\Omega$, $b_2[\eta]=\Omega_\Omega+\Omega_\eta$ (`refl`), 链 `γ′ᴱ = γT b₂ []`. `diag2-fs` 与 Correspond 的 `diag-fs` 同法, 经 EBO 的 `fsT↓-trm`/`γ↓-trm` 化到裸值.

```agda
b₂ : T
b₂ = βᴱ ++ βᴱ

γ′ᴱ : ℕ → T
γ′ᴱ = γT b₂ []

_ : ∀ η → fsT b₂ η ≡ ψᵗ Ωᵗ [] ∷ ψᵗ η [] ∷ []
_ = λ η → refl

_ : γ′ᴱ 0 ≡ natT 1
_ = refl

_ : ∀ k → γ′ᴱ (suc k) ≡ ψᵗ [] (ψᵗ Ωᵗ [] ∷ ψᵗ (γ′ᴱ k) [] ∷ []) ∷ []
_ = λ k → refl

diag2-fs : ∀ n → fsn t2 n ≡ γ′ᴱ (suc n)
diag2-fs n = cong (λ z → ψᵗ [] z ∷ [])
  (trans (E.fsT↓-trm b₂ refl (dec (E.γ↓ b₂ [] refl n))) (cong (fsT b₂) (E.γ↓-trm b₂ [] refl n)))
```

**外层形状, 全部 `refl`.** 两侧都是"第 $n$ 项是链的第 $n+1$ 点, 第 $k+1$ 点是 $\psi_0(\Omega_\Omega+\Omega_{\text{第 }k\text{ 点}})$, 起点 $1$". 第 1 项的下标就是链的第 1 点 $\chi_1$ (对照 §4 朴素树的 $\gamma_1$).

```agda
_ : T₂ ≡ lim (χ ∘ suc)
_ = refl

_ : χ 1 ≡ ψ⁰ K₀
_ = refl

_ : ∀ k → χ (suc (suc k)) ≡ ψ⁰ (K (Γ₂ k))
_ = λ k → refl

_ : χ 2 ≡ ψ⁰ (add (Ω̂ s₁) (λ q → lim 1 q) (Ω (toLevel (χ 1) (hx s₁))))
_ = refl

naive-mismatch : ¬ (N.γ 1 ≅ χ 1)
naive-mismatch e with l-inv (l-inv e 0) 1
... | ()
```

`naive-mismatch`: 朴素树第 1 项的下标 ($\gamma_1$) 与 D3 第 1 项的下标 ($\chi_1$) 不 $\cong$ ($\gamma_1[0][1]=1$, $\chi_1[0][1]=\mathtt{BTBO}^\mathsf I$).

**链的第 0 点与第 1 点.** 第 0 点平凡. 第 1 点 $\chi_1=\psi^0(\Omega_{\ell_0}\oplus\Omega_1)$ 对 $\gamma'^\mathsf E_1=\psi_0(\Omega_\Omega+\Omega)$: 一步形状先逐项写出 (第 0 项 `refl` 是 $\psi^0(\Omega_{\ell_0}+1)$, 记号是 $\psi_0(\Omega_\Omega+1)$; 第 1 项 $\cong\psi^0(\Omega_{\ell_0}\oplus\chi_1[0])$, 记号是 $\psi_0(\Omega_\Omega+\psi_0(\Omega_\Omega+1))$).

```agda
lab-χ0 : Lab (χ 0) (γ′ᴱ 0)
lab-χ0 = l1 refl (s≅ z≅) (l0 refl z≅)

_ : cof (γ′ᴱ 1) ≡ cω
_ = refl

_ : sq (χ 1) 0 ≡ ψ⁰ (suc (Ω ℓ₀))
_ = refl

_ : fsn (γ′ᴱ 1) 0 ≡ ts
_ = refl

_ : fsn (γ′ᴱ 1) 1 ≡ ψᵗ [] (ψᵗ Ωᵗ [] ∷ ts) ∷ []
_ = refl

χ1-1 : sq (χ 1) 1 ≅ ψ⁰ (add (Ω ℓ₀) (λ q → lim 0 q) (up zero (sq (χ 1) 0)))
χ1-1 = ψ⁰-≅ (add-≅ {σ = λ q → lim 0 (suc q)} {σ′ = λ q → lim 0 q} (Ω-refl ℓ₀)
         (upʳ (≅-sym (ψ⁰≅ψ {p = lim 0 zero} {σ = λ q → q} (s≅ (Ω-refl ℓ₀))))))
```

检验要求到这里为止. 实际上能证得更多: **$\chi_1$ 的遗传标签**. 关键是上下文引理 `Ctx₀`: 前缀 $\Omega_{\ell_0}$ 后面接一棵第 0 层的树 $Y$ (任何 `Sim zero ℓ₀` 都行), 只要 $Y$ 带可数记号 $y$ 的标签, $\psi^0(\Omega_{\ell_0}\oplus Y)$ 就带 $\psi_0(\Omega_\Omega+y)$ 的标签. 对 $Y$ 的标签归纳: $y=0$ 时是 `BTBO-label`; 后继时规则 4 (`Lab-rep`); $\omega$ 时规则 5ω. 前缀从不在 $\psi_\delta$ ($\delta\ge1$) 之下暴露, 因为 $Y$ 在第 0 层.

```agda
ctx : T → T
ctx y = ψᵗ [] (ψᵗ Ωᵗ [] ∷ y) ∷ []

Ctx₀ : ∀ {Y y} (σ : Simᴵ zero ℓ₀) → Lab Y y → Lab (ψ⁰ (add (Ω ℓ₀) σ Y)) (ctx y)
Ctx₀ {y = []}     σ (l0 c e) = Lab-≅ (ψ⁰-≅ (add-≅ {σ = σ} {σ′ = σ} (Ω-refl ℓ₀) e)) BTBO-label
Ctx₀ {y = y ∷ ys} σ (l0 c e) = ⊥-elim (cof-ne y ys c)
Ctx₀ {y = []}     σ (l1 () e l)
Ctx₀ {y = y ∷ ys} σ (l1 c e l) =
  lω (cong (cofA []) c) (ψ⁰-≅ (add-≅ {σ = σ} {σ′ = σ} (Ω-refl ℓ₀) e))
     (λ n → subst (Lab _) (sym (fs-rep [] (ψᵗ Ωᵗ []) (y ∷ ys) c n)) (Lab-rep (Ctx₀ σ l) n))
Ctx₀ {y = []}     σ (lω () e h)
Ctx₀ {y = y ∷ ys} σ (lω c e h) =
  lω (cong (cofA []) c) (ψ⁰-≅ (add-≅ {σ = σ} {σ′ = σ} (Ω-refl ℓ₀) e))
     (λ n → subst (Lab _) (sym (fs-ω [] (ψᵗ Ωᵗ []) (y ∷ ys) c n)) (Ctx₀ σ (h n)))
```

$\chi_1$ 内部的链 `ch`: $1$, $\psi_{0}(\Omega_{\ell_0}\oplus\cdot)$ (带证明的折叠, 目标层 $0$), 与记号侧 $\psi_0(\Omega_\Omega+\Omega)$ 的链 $\eta_0=1$, $\eta_{m+1}=\psi_0(\Omega_\Omega+\eta_m)$ (`γT b′ []`) 逐点由 `Ctx₀` 标好 (带证明的折叠经 Level 的 `ψ⁰≅ψ` 换成 `ψ⁰`). `χ 1 ≡ lim (…ch…)` 是 `refl`: 具体证明上的 `coe`/`into`/`out` 都归约掉了.

```agda
σ₁ : Simᴵ zero ℓ₀
σ₁ = λ q → lim 0 (suc q)

ch : ℕ → Ordᶜ zero
ch = iter (λ x → ψ (lim 0 zero) (λ r → r) (add (Ω ℓ₀) σ₁ x)) (suc zero)

_ : χ 1 ≡ lim (λ m → ψ⁰ (add (Ω ℓ₀) σ₁ (ch m)))
_ = refl

b′ : T
b′ = ψᵗ Ωᵗ [] ∷ ψᵗ (natT 1) [] ∷ []

_ : γ′ᴱ 1 ≡ ψᵗ [] b′ ∷ []
_ = refl

_ : ∀ m → γT b′ [] (suc m) ≡ ctx (γT b′ [] m)
_ = λ m → refl

fs-χ1 : ∀ m → fsn (γ′ᴱ 1) m ≡ ctx (γT b′ [] m)
fs-χ1 m = cong (λ z → ψᵗ [] z ∷ [])
  (trans (E.fsT↓-trm b′ refl (dec (E.γ↓ b′ [] refl m))) (cong (fsT b′) (E.γ↓-trm b′ [] refl m)))

lab-ch : ∀ m → Lab (ch m) (γT b′ [] m)
lab-ch zero    = lab-χ0
lab-ch (suc m) = Lab-≅ (≅-sym (ψ⁰≅ψ {p = lim 0 zero} {σ = λ r → r} (add-≅ {σ = σ₁} {σ′ = σ₁} (Ω-refl ℓ₀) (≅-refl⁰ (ch m)))))
                       (Ctx₀ σ₁ (lab-ch m))

χ1-label : Lab (χ 1) (γ′ᴱ 1)
χ1-label = lω refl (l≅ (λ m → ≅-refl⁰ _)) (λ m → subst (Lab _) (sym (fs-χ1 m)) (Ctx₀ σ₁ (lab-ch m)))

T₂-0 : Lab (sq T₂ 0) (fsn t2 0)
T₂-0 = subst (Lab _) (sym (diag2-fs 0)) χ1-label
```

**对照 §4 的路径 $P$.** 朴素树在 $P$ 处是 $0$; D3 的 `T₂` 在 $P$ 处与 EBO 同为 $\psi_0(\Omega_\Omega+\Omega_\omega)$ 形 (下标沿 $\chi_1[0][1]=\mathtt{BTBO}^\mathsf I$ 正确地下降), 再取第 0 项字面上是 `ψ⁰ (suc (Ω ℓ₀))`, 带 $\psi_0(\Omega_\Omega+1)$ 的遗传标签.

```agda
_ : sq (P5 T₂) 0 ≡ ψ⁰ (suc (Ω ℓ₀))
_ = refl

_ : fsn (fsn (fsn (fsn (fsn (fsn t2 1) 0) 1) 0) 0) 0 ≡ ts
_ = refl

stage2-P : Lab (sq (P5 T₂) 0) (fsn (fsn (fsn (fsn (fsn (fsn t2 1) 0) 1) 0) 0) 0)
stage2-P = ts-label
```

**检验结论.** `T₂` 的基本列与 EBO 的 $\psi_0(\Omega_\Omega\cdot2)[n]$ 在第一层逐项同形 (外层规则 6 `refl`, 链的递推 `refl`), 链的第 0、1 点有**遗传**标签 (`lab-χ0`, `χ1-label`), 第 1 项的下标是上下文链而不是对角线 (`naive-mismatch` 对照). 检验通过.

## §9 第一处失败: 前缀在 $\psi_\delta$ 下暴露

`T₂` 的第 1 项 $\chi_2=\psi_0(\Omega_\Omega+\Omega_{\chi_1})$ 没有标签. 路径 $[0][2][0][0][1]$ 把下标 $\chi_1$ 降到 $\mathtt{BTBO}^\mathsf I+1$ (两侧一致), 于是出现层 $\delta=\mathtt{BTBO}^\mathsf I$ 上的规则 6 链, 其点是 $\psi_\delta(\Omega_\Omega+\zeta)$; 再走 $[1][0][0][0][1]$ 到达 $\psi_0(\Omega_\Omega+\psi_\delta(\Omega_\Omega))$. 这里前缀**在 $\psi_\delta$ 之下暴露**: EBO 穿透, $\psi_\delta(\Omega_\Omega)$ 是 $\Omega_1$-共尾, 外层 $\psi_0$ 用规则 6 的链 $\eta_0=1$, $\eta_{m+1}=\psi_0(\Omega_\Omega+\psi_\delta(\Omega_{\eta_m}))$ 计值; 树侧前缀是 $\Omega_{\ell_0}$, $\psi_\delta(\Omega_{\ell_0})$ 是 `lim`, 第 $m$ 项用对角线 $L_m$. 第 1 项起下标分岔 ($\eta_1$ 对 $L_1=\varepsilon_0$), 再走 6 步树到 $0$, 记号是 $\psi_0(\Omega_\Omega)$. 全程 17 步, 两侧都只是计算 (Python 模拟器先找路径, Agda `refl` 核对).

```agda
Q′ : List ℕ
Q′ = 0 ∷ 2 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

_ : walk (χ 2) Q′ ≡ zero
_ = refl

_ : walkᵀ (γ′ᴱ 2) Q′ ≡ E.EBOψ 2
_ = refl

χ2-unlabel : ¬ Lab (χ 2) (γ′ᴱ 2)
χ2-unlabel l = Lab0 (Lab-walk Q′ l (refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl ,
                                     refl , refl , refl , refl , refl , refl , tt)) refl

stage2-unlabel : ¬ Lab T₂ t2
stage2-unlabel l = χ2-unlabel (subst (Lab (χ 2)) (diag2-fs 1) (sqLab l refl 1))
```

同一个机制给出 D3 下**最小**的失败项 $\psi_0(\Omega_\Omega+\Omega_2)$: 规则 6 的链在第 1 层, 链点 $\psi_1(\Omega_\Omega+\zeta)$, 三步后到 $\psi_0(\Omega_\Omega+\psi_1(\Omega_\Omega))$, 再一步下标分岔, 共 10 步. $\Omega_2$ 进入 $\ell_0$ 的路径: $\ell_0$ 的第 1 项是 $\varepsilon_0$ 的层号, 其第 0 项是 $\omega$ 的层号, 其第 3 项字面上是 $3$.

```agda
σ₂ : Simᴵ (suc (suc zero)) ℓ₀
σ₂ q = lim 1 (lim 0 (lim 3 (suc q)))

X₂ : Ordᶜ zero
X₂ = ψ⁰ (add (Ω ℓ₀) σ₂ (Ω (suc (suc zero))))

Rp : List ℕ
Rp = 1 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

_ : walk X₂ Rp ≡ zero
_ = refl

X₂-unlabel : ¬ Lab X₂ (ctx (Ωt (natT 2)))
X₂-unlabel l = Lab0 (Lab-walk Rp l (refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , tt)) refl
```

**读法.** `Ctx₀` 与 `X₂-unlabel` 一起给出 D3 静态前缀的精确边界: $\psi_0(\Omega_\Omega+y)$ 对一切可数 $y$ 都对, $y=\Omega_2$ 就错. 分界恰在 $y$ 是否带 $\ge1$ 层的规则 6 链: 只有那时 $\Omega_\Omega$ 会落进 $\psi_\delta$ ($\delta\ge1$) 的参数, 然后作为 $\Omega_1$-共尾对象被**另一个**上下文的链计值. D3 只把**最外层**的 $\Omega_\Omega$ (§7 的 $K_k$ 的末项) 交给上下文链, 前缀仍是静态的 $\mathbb N$-对角线.

$\psi_0(\Omega_{\Omega+1})$ 在 D3 中只到第 0 项 (§4: `≡ BTBOᴵ`). 它的第 1 项 $\psi_0(\psi_\Omega(\Omega_\Omega))$ 要折叠到不可数目标层 $\Omega$, 且其 $[0][0][2]$ 就是 $\psi_0(\Omega_\Omega\cdot2)$ (§4 `refl`); D3 的 `T₂` 不是第一层族里的对象, 第一层的 `ψ⁰` 只会结构地产生 `N2`. 所以 $\psi_0(\Omega_{\Omega+1})$ 至少需要 §10 的整个族, 外加以 "$\Omega+$可数" 为目标层的折叠.

## §10 阶段 2 的遗传标签需要什么

由 §5 (WLPO)、§6 (上界只被项自身界住)、§9 (静态前缀) 三个否定, 下一个可行的设计必须同时满足:

1. **符号化的 $\Omega_\Omega$.** 它不能是带全分支的节点 (§5), 也不能是固定的 $\mathbb N$-对角线 (§9); 只能是**不带分支的构造子** (以及穿透产物 $\psi_\delta(\Omega_\Omega)$ 的符号形式), 其共尾序列在折叠时由上下文产生: 遇到 $\mu=0$ 的规则 6, 用当前上下文的链 (本文 `Γ₂` 的一般化); 遇到 $\psi_\delta$ 的穿透, 记下 $\delta$, 留待外层的规则 6 计值.
2. **逐步现造的公共上界.** 每次计值 $\Omega_\eta$ 或 $\psi_\delta(\Omega_\eta)$ 都要一个以 $\delta$、$\mathtt{lvl}\,\eta$ 与前缀的层号为结构前驱的层号 (本文的 `M`), 其步进证据由链携带的序证据给出. 本文只需 `ev : lim γ ⊑ χₖ`; 一般情形需要的不变量是 "链从第 1 点起支配上下文里的一切可数下标, 第 0 点 $1\sqsubseteq\delta$", 由 `pre` 型引理在新族上逐步再生. 这正是交替不变量 (被比较的下标在下标层有公共上界) 的构造性版本: 上界不预先存在, 而由链逐步产生.
3. **新族的一致引理.** 本文的每个 $K_k$ 都是第一层族的对象, 证书来自 Uniform 的 `Good`; 符号构造子进入族之后, 需要 `Good` 对它们与对上下文计值封闭 (Uniform §6–§7 的推广), 以及 `pre`/`chain-step` 的对应物.
4. **记号侧.** Standard 的 `NF` 要求 $\psi$-下标 `Ctbl` (全是 $\psi_0$ 项), 所以 $\Omega_\Omega$ 不在其中. 需要把 `NF`、`Bnd`、`cofin` 推广到唯一的不可数下标 $\Omega$ (以及 $\Omega+$可数, 若要 $\psi_0(\Omega_{\Omega+1})$), 并给 Label 的 `System`/`Next` 一个"上界逐步给出"的版本 (目前 `A′ = suc (lvS′ β)` 是一次给定的).
5. **标签的组织.** `Ctx₀` 提示了形式: 遗传标签对"上下文 + 可数尾巴"归纳, 上下文里的符号 $\Omega_\Omega$ 由 BTBO 的标签兜底. 一般情形的归纳对象是带符号的上下文, 而不只是 $\Omega_\Omega+\cdot$.

## §11 对比表

| | D1 第二层 (全分支) | D2 有界 $\hat\Omega$ (界 `BTBOᴸ`) | D3 上下文对角线 (本文) |
|---|---|---|---|
| $\Omega_\Omega$ 的表示 | $\Omega_1$-共尾节点, 分支 $\eta\mapsto\Omega_\eta$ 遍历全部可数下标 | `limᵢ`, 分支只遍历 `BTBOᴵ` 之下的带证书树 | 不表示为对象; 最外层的规则 6 在记号层执行, 前缀为 $\Omega_{\ell_0}$ |
| 类型 | 新族, 节点不挂固定层号 | `limᵢ` 定义域是整个 `Ordᶜ i`, 需新构造子 | 现有族不变, 只加链与逐步层号 `M` |
| 有界三歧性 | 分支要比较任意 $a$ 与固定 $\delta$: `dec→WLPO` | 族内不受影响 | 不受影响: 每次比较都在 `M` 内 |
| 无不可数下标 | 是 | 是 | 是 |
| 否定 (已编译) | `dec→WLPO` | `BTBO≺χ1`, `χ1⊀BTBO` (链点越界) | `χ2-unlabel`, `X₂-unlabel` (前缀暴露) |
| 决定性检验 | 未建 | 未建 | 通过: 外层 `refl`, `lab-χ0`, `χ1-label`, `stage2-P` |
| 回灌下标层 | — | — | `T₂-HS`, `T₂ᴸ` |
| 能推广到哪 | 不能 (WLPO) | 不能 (上界固定) | 需 §10 的符号构造子与逐步上界 |

## §12 结论与边界

**字面成立 (`refl`):** `ψ⁰ (Ω ℓ₀) ≡ BTBOᴵ`; `ψ⁰ (Ω BTBOᴸ) ≡ lim (γ ∘ suc ∘ suc)`; `fsn ψ₀(Ω_{Ω+1}) 0 ≡ EBOψ 2` 与 `sq NO 0 ≡ BTBOᴵ`; 朴素树的 $[1][0][0][2]$ 两侧分别 `≡ N2`、`≡ t2`; `P5 N2 ≡ zero`; D3 的外层形状 (`T₂ ≡ lim (χ ∘ suc)`, `χ (k+2) ≡ ψ⁰ (K (Γ₂ k))`, `χ 2` 的下标是 `lvl χ₁`), `fsT b₂ η`, `γ′ᴱ` 的递推; `sq (P5 T₂) 0 ≡ ψ⁰ (suc (Ω ℓ₀))`; 失败路径两端 (`walk (χ 2) Q′ ≡ zero`, `walk X₂ Rp ≡ zero`); FGH 小值.

**定理 (模 $\cong$, 标签按 Correspond 的 `Lab`):**

1. 事实 1: `seed`, `seed⁻`, `tb-fs`, `tb-label`.
2. 事实 2: `ts-label`; 否定 `shift-unlabel` (经 `Lab-uniq`, `γ12`); `tbs-label`.
3. 事实 3: 否定 `naive-unlabel`, `naiveO-unlabel`, `naive-mismatch`.
4. D1: `dec→WLPO`. D2: `BTBO≺χ1`, `χ1⊀BTBO`.
5. D3: 构造 `Γ₂`/`χ`/`T₂`, 证书 `T₂-HS`, 层号 `T₂ᴸ`; 决定性检验 `diag2-fs`, `lab-χ0`, `χ1-1`, **`χ1-label`**, `T₂-0`, `stage2-P`; 上下文引理 `Ctx₀`; 边界 `χ2-unlabel`, `stage2-unlabel`, `X₂-unlabel`.
6. 标签工具: `Lab-+`, `Lab-rep`, `Lab-uniq`, `sqLab`, `Lab-walk`.

**边界.**

- `T₂` **不是** $\psi_0(\Omega_\Omega\cdot2)$ 的遗传标签树 (`stage2-unlabel`); 已证的是外层一步、链的前两点的遗传标签、以及 "$\Omega_\Omega+$可数" 片段的全部 (`Ctx₀`). 按 probes/README 的认证准则, 本文越过 BTBO 的定理级标签是 `ts-label` ($\psi_0(\Omega_\Omega+1)$)、`Ctx₀` (一切 $\psi_0(\Omega_\Omega+y)$, $y$ 可数且有标签) 与 `χ1-label` ($\psi_0(\Omega_\Omega+\Omega)$, 即这个片段的上确界); $\psi_0(\Omega_\Omega\cdot2)$ 及以上仍无.
- `dec→WLPO` 说的是"忠实派发需要的判定蕴含 WLPO"; "D1 的任何实现都需要这个判定"是对设计的分析 (§5), 不是定理. WLPO 不可证是元定理, 未编译.
- §6 "任何固定上界都失败"、§4 读法里"换任何可数层号也一样"与 §10 的需求清单是纸面论证; 编译的只是 `BTBOᴸ`/`ℓ₀` 这两个具体代表的反例.
- $\psi_0(\Omega_{\Omega+1})$, $\psi_0(\Omega_{\Omega\cdot2})$, $\psi_0(\Omega_{\Omega_\Omega})$ 只做了朴素版的否定 (前者, `naiveO-unlabel`); 后两者的 EBO 链分别在层 $\Omega\cdot2$ 与 $\Omega_\Omega$ 上, 需要不可数目标层的折叠, 本文未涉及.
- 值的语义 (例如 $\psi_0(\Omega_{\psi_0(\Omega_\Omega)})$ 在 Buchholz 的集合论定义下是否等于 $\psi_0(\Omega_\Omega)$) 不在本文: 本文只用 EBO 的基本列语义.
- 不改 `src/`、`archive/` 与已有的 Align 文件, README 未改.
