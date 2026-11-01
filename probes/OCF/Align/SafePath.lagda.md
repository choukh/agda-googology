# 安全路径引理: 观测前序与遗传步进

> 接 [Cumulative](Cumulative.lagda.md) §10、§13 与 [Certified](Certified.lagda.md) §4. 那里留下的唯一数学缺口: 第 $\ge1$ 层规则 6 的 $\gamma$-链是否 $\sqsubseteq$-递增 (Cumulative §10 表的第四行), 以及更一般地, $x_3=\psi_0(\Omega_{\varepsilon_0})$ 乃至整条对角线 $\psi_0(\Omega_a)$ 内部的**每个** `lim` 序列是否步进. Cumulative 已说明它不受内涵性阻挡, 但 $\psi$ 不 $\sqsubseteq$-单调 (`ψ-not-⊑mono`), 所以需要一个只覆盖 "实际出现的输入" 的关系.
>
> 结论先说:
>
> 1. **缺口闭合 (模 $\cong$).** 对任意层号 $a$ : `Ordʷ`, $\psi^0(\Omega_a)$ 遗传步进: 其中每个 `lim` 的相邻两项在 Cumulative 的 $\sqsubseteq$ (叶子为 $\cong$) 下递增 (`HS-diag`, 无附加前提). 特例: $x_3$ (`HS-x₃`); 第四行对**任意** $c$ 成立, $\psi^0(\gamma^c_n)\sqsubseteq\psi^0(\gamma^c_{n+1})$ (`row4`, $c=1$ 为 `row4-c1`).
> 2. **采用的关系: 观测前序 $\sqsubseteq^\mathsf{o}$ (候选 C2 的语义化).** 一个 "观测" 是有限的运算栈: 若干次 $\psi_p\sigma$、$\psi^0$、$a+\_$, 最后落在第 0 层 (恒等). $x\sqsubseteq^\mathsf{o}y$ 指对每一对**相似**的观测 (同形状、同目标层, `Sim` 证据任意, 加数 $\cong$), 两边的观测结果在第 0 层 $\sqsubseteq$. 按定义, $\sqsubseteq^\mathsf{o}$ 对 $\psi_p$、$\psi^0$、加法是同余, 单调性各是一行; 全部数学内容集中在五条 "上界引理" 上 (`lim-r`, `lim-l`, `suc-r`, `limᵢ-r`, `add-r`) 与链起点引理 `B1`, 每条都对观测归纳证明.
> 3. **关键的一条是 `limᵢ-r`**: 在任何观测下, 节点 $\lim_j g$ 都在它的**起点分支** $g(\Omega_j)$ 之上. 理由: 观测中的每一步要么穿透这个节点 (输出仍是 $\lim_j$ 节点, 分支函数变成 $C\circ g$, 链跟着变), 要么折叠它 (输出 $\lim_n C(g(\gamma_n))$); 两种情况下第 0 条链都从 $\Omega_j$ 开始, 与节点无关. 只有第 0 项是一致的: 第 $k>0$ 项在穿透后换成新链的项, 这正是 C1 失败的地方 (§1). 链的步进只需要起点一步 (`B1`: $\Omega_j\sqsubseteq^\mathsf{o}\psi_q z$) 加上同余.
> 4. **三个候选的结局.** C1 (只经链分支的前驱) 不被 $\psi$ 保持, 数学反例在穿透处 (§1, 序数值). C2 (链步的归纳同余闭包) 的可靠性证明在 "$\psi$ 之上再 $\psi$" 处要求对任意深的运算栈归纳; 把栈显式化就得到 $\sqsubseteq^\mathsf{o}$, 归纳闭包随之多余 (§2). C3 (标准性谓词) 不需要: $\sqsubseteq^\mathsf{o}$ 只沿同余与起点分支增长, 非标准输入对进不来 (§3).
> 5. **反例对被拒绝.** `ψ-not-⊑mono` 的 $\mathrm{suc}\,a_1\sqsubseteq\Omega_1$ 不是 $\sqsubseteq^\mathsf{o}$ (`⊑ᵒ-rejects`): $\psi_0$ 本身就是一个观测, 而 $\psi_0(\mathrm{suc}\,a_1)\not\sqsubseteq\psi_0(\Omega_1)$.
> 6. **边界.** 步进是模 $\cong$ 的 (Cumulative §6 的 $\sqsubseteq$), 不是 Cumulative §9 的字面 $\sqsubseteq^0$; 两侧观测的 `Sim` 证据不同 (极限层 $\Omega$ 的 `up (self n)` 与 `up (self (n+1))`), 闭包因而字面不同. 字面版本与 Certified 的证书 `CertDiag` (要求字面 $\sqsubseteq^\mathsf{w}$) 仍是内涵性的缺口, 本文未处理.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 不改动任何已有文件; Cumulative 的全部定义都是公开的, 直接导入, 没有复制.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SafePath where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Cumsum using (module W)
open W using (Ordʷ; zero; suc; lim; _<ʷ_; _⊑ʷ_; z⊑; s⊑; l⊑; <ʷ-dec; Simʷ)
open import OCF.Align.Certified using (ε₀ʷ)
open import OCF.Align.Cumulative
```

## §0 问题的精确形式

记号沿用 Cumulative: 树族 `Ordᶜ ℓ` (构造子 `zero/suc/lim/limᵢ/up`), 带累积 `Sim` 证据的忠实折叠 `ψ p σ`, 目标层 0 的无证明折叠 `ψ⁰`, 跨层结构互模拟 $\cong$, 叶子为 $\cong$ 的结构序 $\prec$ 与前驱包含 $\sqsubseteq$. 节点 $\lim_j f$ (证明 $q:j<^\mathsf{w}k$) 的 $\gamma$-链是它固有的: $\gamma_0=\Omega_j$, $\gamma_{n+1}=\psi_q(f\,\gamma_n)$, 规则 6 与 `ψ⁰` 都只用这条链.

$\Omega_{\mathrm{suc}\,c}=\lim_c\,\mathtt{up}$, 所以 $\psi^0(\Omega_{\mathrm{suc}\,c})=\lim_n\psi^0(\gamma^c_n)$, 其中 $\gamma^c_{n+1}=\psi_{c<c+1}(\mathtt{up}\,\gamma^c_n)$. 第 $c$ 层的树里所有 `limᵢ` 的下标都 $<c$, 所以 $\gamma^c_{n+1}$ 是 $\gamma^c_n$ 的 "穿透拷贝" ($0\mapsto\Omega_c$, $\mathrm{suc}\mapsto\cdot\omega$, `limᵢ` 节点换成 $\psi_c\circ f$ 的节点); 而 $\psi^0$ 在这些节点上再走规则 6, 用的是**新**节点的链. 所以要比较的两棵树 $\psi^0(\gamma^c_n)$、$\psi^0(\gamma^c_{n+1})$ 里, 对应位置上的链各不相同, 单靠 "$\psi$ 单调" 推不出来 (它也不成立).

需要的是一个关系 $\sqsubseteq^?$, 满足: (i) 链 $\sqsubseteq^?$-递增; (ii) 出现的分支函数 (`up`、$\psi_q\circ f$、$a+f$) $\sqsubseteq^?$-单调; (iii) 第 0 层的 $\sqsubseteq^?$ 蕴含 $\sqsubseteq$; (iv) $\psi$ 与各构造保持它. 任务给了三个候选.

## §1 候选 C1: 只经链分支的前驱 (不成立, 数学反例)

C1: $\prec^\mathsf{g}$ 与 $\prec$ 相同, 只是 `≺i` 只能经链分支 $f(\gamma_k)$ 下降; $\sqsubseteq^\mathsf{g}$ 为前驱包含. 它确实消掉了 Cumulative §10 的反例 ($a_1=\uparrow\lim G$ 不在任何 $G\,k$ 之下). 但它不被穿透的折叠保持. 反例 (第 2 层, 目标层 1):

- $\uparrow^2=\mathtt{up}\,0\circ\mathtt{up}\,0$ 把第 0 层的树提升到第 2 层. $x=\lim_0\uparrow^2$ (证明 $0<^\mathsf{w}2$), 即 "第 2 层里的 $\Omega_1$"; $b=\lim_k\uparrow^2(G_k)$, 即第 2 层里的 $\varepsilon_0$, 其中 $G$ 是 Cumulative 的 $\Omega_1$-链 ($G_0=1$, $G_{k+1}=\psi_0(G_k)$).
- $x$ 的节点的链: $\gamma'_0=\Omega_0=1$, $\gamma'_{k+1}=\psi_{0<2}(\uparrow^2\gamma'_k)=\psi_0(\gamma'_k)=G_{k+1}$ ($\psi$ 透过 `up`). 所以 $x$ 的链分支是 $\uparrow^2 G_k$, 每个都在 $b$ 之下: $x\sqsubseteq^\mathsf{g}b$.
- 折叠 $\psi_1$ ($1<2$): 节点下标 $0<1$, 规则 5Ω 穿透, $\psi_1(x)=\lim_0(\psi_1\circ\uparrow^2)$; 它的链换成 $\gamma''_{k+1}=\psi_0(\psi_1(\uparrow^2\gamma''_k))$, $\gamma''_1=\psi_0(\psi_1(1))=\psi_0(\Omega_1\cdot\omega)>\varepsilon_0$, 新链不被旧链控制. 取值: 规则给出 $\psi_1(\uparrow^2 z)=\Omega_1\cdot\omega^z$, 于是 $\psi_1(x)=\Omega_1\cdot\omega^{\Omega_1}$, $\psi_1(b)=\Omega_1\cdot\omega^{\varepsilon_0}$.
- 若 $\psi_1(x)\sqsubseteq^\mathsf{g}\psi_1(b)$, 再用 $\psi_0$ (目标层 0 时 $\sqsubseteq^\mathsf{g}$ 恰是 Certified 的 "安全" $\sqsubseteq_p$, $\psi_0$ 把它送到 $\sqsubseteq$, 同 `ψ-⊑ₚ` 的论证), 得 $\psi_0(\Omega_1\omega^{\Omega_1})\le\psi_0(\Omega_1\omega^{\varepsilon_0})$. 两个参数都是标准的 ($\varepsilon_0=\psi_0(\Omega_1)$ 且 $\Omega_1<\Omega_1\omega^{\varepsilon_0}$), Buchholz 的 $\psi_0$ 在其上严格递增, 矛盾.

根源: $\sqsubseteq^\mathsf{g}$ 对下标 $j$ 的节点只看链, 这只对目标层 $\le j$ 的折叠正确; 目标层 $>j$ 的折叠穿透节点, 需要全部分支, 而且穿透后的节点有另一条链. 把 $\prec^\mathsf{g}$ 改成依赖目标层就是 Certified 的 $\sqsubseteq_p$, 它被 $\psi_p$ 送到**完全的** $\sqsubseteq$, 不再是下一次折叠所需的 $\sqsubseteq_{p'}$; "左边 $\sqsubseteq_p$、右边完全 $\sqsubseteq$" 的互归纳在下一层折叠处遇到 `ψ-not-⊑mono`. 结论: 一个固定的、由结构前驱定义的关系承担不了 "穿透改变链" 这件事.

## §2 候选 C2: 链步的同余闭包, 以及它的语义化

C2: 归纳定义 $\trianglelefteq$, 基本步 $\gamma_k\trianglelefteq\gamma_{k+1}$, 对 `suc/lim/limᵢ/up/+/ψ/Ω` 同余, 再加 $\cong$ 与传递, 然后证可靠性 $x\trianglelefteq y\Rightarrow x\sqsubseteq y$. 归纳在同余规则 $\psi_q$ 处卡住: 由 $x\trianglelefteq y$ 的归纳假设只得到 $x\sqsubseteq y$, 而 $\sqsubseteq$ 不 $\psi$-单调. 把归纳假设加强为 "对一切 $q$, $\psi_q x\sqsubseteq\psi_q y$", 下一层又要 "$\psi_p\psi_q x\sqsubseteq\psi_p\psi_q y$"; 规则 4 与加法还会在中间插入 $a+\_$. 所以可靠性的归纳假设必须是: **对任意有限运算栈 $S$, $S\,x\sqsubseteq S\,y$**. 把这句话直接取作定义, 就是本文的 $\sqsubseteq^\mathsf{o}$; C2 的每条规则变成关于 $\sqsubseteq^\mathsf{o}$ 的引理: 同余是一行 (栈的复合), 基本步归结为链起点 `B1`, 再加同余.

纸面上还试过一个中间方案: 归纳关系里 `limᵢ` 在左边经**全部**分支、在右边只经**链**分支. 它在加法处断掉: $a+\lim_j g=\lim_j(a+g)$ 的链是 $\gamma'_{k+1}=\psi_j(a+g\,\gamma'_k)$, 不是 $g$ 的链, 于是右规则 $y\trianglelefteq g(\gamma_k)\Rightarrow y\trianglelefteq\lim_j g$ 推不出 $a+y\trianglelefteq\lim_j(a+g)$, 除非先证明两条链的比较, 而那又要 $\psi_j$ 的单调性. $\sqsubseteq^\mathsf{o}$ 绕开了这一点: 它只需要起点分支 ($k=0$), 起点对所有节点都是 $\Omega_j$.

## §3 候选 C3: 标准性 (不需要)

C3 要在树上定义 "标准参数" 谓词 (Buchholz 的 $a\in C_\nu(a)$ 的影子), 再对标准输入证 $\psi$ 的 $\sqsubseteq$-单调; 记号侧需要 EBO 的 `cmpᵀ`/`fsT↓` 理论 ("链在标准参数中共尾"). 本文没有走这条路, 因为 $\sqsubseteq^\mathsf{o}$ 已给出全部结论, 且不需要任何标准性前提: $\sqsubseteq^\mathsf{o}$ 只由同余与 "起点分支在节点之下" 生成, 非标准的比较 (如 $\mathrm{suc}\,a_1$ 对 $\Omega_1$, 经非链分支 $(\lim G)+1$) 根本不进入 $\sqsubseteq^\mathsf{o}$. 标准性在这里的角色由遗传谓词 `Good` (§9) 扮演: 它只要求分支函数 $\sqsubseteq^\mathsf{o}$-单调, 这对实际出现的分支函数 (`up`、$\psi\circ f$、$a+f$) 按定义成立.

## §4 观测与观测前序

**$\psi^0$ 的双侧 $\cong$.** Cumulative 的 `ψ⁰-≅` 一边是 `ψ⁰`、一边是带证明的折叠; 这里需要两边都是 `ψ⁰` 的版本, 证明逐字相同.

```agda
ψ⁰≅ : ∀ {k₁ k₂} {a : Ordᶜ k₁} {b : Ordᶜ k₂} → a ≅ b → ψ⁰ a ≅ ψ⁰ b
ψ⁰≅ z≅     = s≅ z≅
ψ⁰≅ (s≅ e) = l≅ (iter-R _≅_ (λ e′ → add-≅ (ψ⁰≅ e) e′) z≅)
ψ⁰≅ (l≅ h) = l≅ (λ n → ψ⁰≅ (h n))
ψ⁰≅ (upˡ {r = zero} e)   = ψ⁰≅ e
ψ⁰≅ (upˡ {r = self n} e) = ψ⁰≅ e
ψ⁰≅ (upʳ {r = zero} e)   = ψ⁰≅ e
ψ⁰≅ (upʳ {r = self n} e) = ψ⁰≅ e
ψ⁰≅ (lᵢ≅ {j = j} {p = q} {q = q′} {f = f} {g = g} h) = l≅ (λ n → ψ⁰≅ (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ e → ψ-≅ (h _ _ (≅→R (<→◃ q) e))) (Ω-refl j)
```

**观测.** `Obs k` 是作用于第 $k$ 层树的运算栈, 最内层的运算是首构造子: `ψo O p σ` 先做 $\psi_p\sigma$ 再做 `O`, `addo O a σ` 先做 `add a σ` (右加数是洞), `ψ⁰o O` 先做 `ψ⁰`; 栈底是第 0 层的恒等 `idO`. `run O x` 执行观测.

**相似.** 两侧的观测必须能不同: 极限层 $\Omega_{\lim g}$ 的相邻两项是 `up (self n) (Ω (g n))` 与 `up (self (n+1)) (Ω (g (n+1)))`, 观测透过提升节点时把 `self n` 并入 `Sim` 证据, 两侧证据不同, 两棵 $\Omega$ 也在不同的层. 所以 $\approx^\mathsf{o}$ 要求同形状、`ψo` 同目标层, `Sim` 证据与外层层号任意, 加数 $\cong$. 它是 PER (`≈ᵒ-reflˡ`/`≈ᵒ-reflʳ`), 相似观测把 $\cong$ 送到 $\cong$ (`run-≅`, 用 `ψ-≅`/`add-≅`/`ψ⁰≅`).

**观测前序.** $x\sqsubseteq^\mathsf{o}y$: 对一切相似的观测对, 第 0 层的结果 $\sqsubseteq$ (Cumulative §6, 叶子 $\cong$). $\cong\subseteq\sqsubseteq^\mathsf{o}$. 传递性需要中间层上的一个观测: 中间项与某一端同层时用 PER 性 (`⊑ᵒ-trans`, `⊑ᵒ-transˡ`); 中间项在右端的结构前驱层时, 把右侧观测沿 $\triangleleft$ 改写 `Sim` (`retarget`, `⊑ᵒ-trans◃`). 三端都不同层的一般传递性没有: 第 0 层以外没有恒等观测, `Sim` 证据也没有公共上界可取; 本文只在 $\Omega$ 的单调性 (§8) 里遇到三层不同的情形, 那里中间层恰是右端的直接前驱.

```agda
data Obs : Ordʷ → Set where
  idO  : Obs zero
  ψ⁰o  : ∀ {k} → Obs zero → Obs k
  ψo   : ∀ {i k ℓ} → Obs i → i <ʷ ℓ → Simʷ k ℓ → Obs k
  addo : ∀ {k ℓ} → Obs ℓ → Ordᶜ ℓ → Simʷ k ℓ → Obs k

run : ∀ {k} → Obs k → Ordᶜ k → Ordᶜ zero
run idO          x = x
run (ψ⁰o O)      x = run O (ψ⁰ x)
run (ψo O p σ)   x = run O (ψ p σ x)
run (addo O a σ) x = run O (add a σ x)

infix 4 _≈ᵒ_ _⊑ᵒ_
data _≈ᵒ_ : ∀ {k k′} → Obs k → Obs k′ → Set where
  idO  : idO ≈ᵒ idO
  ψ⁰o  : ∀ {k k′} {O O′ : Obs zero} → O ≈ᵒ O′ → ψ⁰o {k} O ≈ᵒ ψ⁰o {k′} O′
  ψo   : ∀ {i k k′ ℓ ℓ′} {O O′ : Obs i} {p : i <ʷ ℓ} {p′ : i <ʷ ℓ′} {σ : Simʷ k ℓ} {σ′ : Simʷ k′ ℓ′} →
         O ≈ᵒ O′ → ψo O p σ ≈ᵒ ψo O′ p′ σ′
  addo : ∀ {k k′ ℓ ℓ′} {O : Obs ℓ} {O′ : Obs ℓ′} {a : Ordᶜ ℓ} {a′ : Ordᶜ ℓ′} {σ : Simʷ k ℓ} {σ′ : Simʷ k′ ℓ′} →
         O ≈ᵒ O′ → a ≅ a′ → addo O a σ ≈ᵒ addo O′ a′ σ′

≈ᵒ-reflʳ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → O′ ≈ᵒ O′
≈ᵒ-reflʳ idO        = idO
≈ᵒ-reflʳ (ψ⁰o o)    = ψ⁰o (≈ᵒ-reflʳ o)
≈ᵒ-reflʳ (ψo o)     = ψo (≈ᵒ-reflʳ o)
≈ᵒ-reflʳ (addo o e) = addo (≈ᵒ-reflʳ o) (≅-reflʳ e)

run-≅ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} {x : Ordᶜ k} {x′ : Ordᶜ k′} → O ≈ᵒ O′ → x ≅ x′ → run O x ≅ run O′ x′
run-≅ idO        e = e
run-≅ (ψ⁰o o)    e = run-≅ o (ψ⁰≅ e)
run-≅ (ψo o)     e = run-≅ o (ψ-≅ e)
run-≅ (addo o a) e = run-≅ o (add-≅ a e)

_⊑ᵒ_ : ∀ {k k′} → Ordᶜ k → Ordᶜ k′ → Set
_⊑ᵒ_ {k} {k′} x y = ∀ {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → run O x ⊑ run O′ y

≅→⊑ᵒ : ∀ {k k′} {x : Ordᶜ k} {y : Ordᶜ k′} → x ≅ y → x ⊑ᵒ y
≅→⊑ᵒ e o = ≅→⊑ (run-≅ o e)

≈ᵒ-reflˡ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → O ≈ᵒ O
≈ᵒ-reflˡ idO        = idO
≈ᵒ-reflˡ (ψ⁰o o)    = ψ⁰o (≈ᵒ-reflˡ o)
≈ᵒ-reflˡ (ψo o)     = ψo (≈ᵒ-reflˡ o)
≈ᵒ-reflˡ (addo o e) = addo (≈ᵒ-reflˡ o) (≅-reflˡ e)

-- 中间项与右端同层
⊑ᵒ-trans : ∀ {k₁ k₂} {x : Ordᶜ k₁} {y z : Ordᶜ k₂} → x ⊑ᵒ y → y ⊑ᵒ z → x ⊑ᵒ z
⊑ᵒ-trans h h′ o = ⊑-trans (h o) (h′ (≈ᵒ-reflʳ o))

-- 中间项与左端同层
⊑ᵒ-transˡ : ∀ {k₁ k₂} {x y : Ordᶜ k₁} {z : Ordᶜ k₂} → x ⊑ᵒ y → y ⊑ᵒ z → x ⊑ᵒ z
⊑ᵒ-transˡ h h′ o = ⊑-trans (h (≈ᵒ-reflˡ o)) (h′ o)

-- 中间项在右端的结构前驱层: 观测沿 ◃ 改写 Sim
◃→Sim : ∀ {a b} → a ◃ b → Simʷ a b
◃→Sim zero      q = suc q
◃→Sim (suc r)   q = suc (◃→Sim r q)
◃→Sim (self n)  q = lim n q
◃→Sim (lim n r) q = lim n (◃→Sim r q)

retarget : ∀ {k ℓ} → Obs ℓ → k ◃ ℓ → Obs k
retarget idO          ()
retarget (ψ⁰o O)      r = ψ⁰o O
retarget (ψo O p σ)   r = ψo O p (λ q → σ (◃→Sim r q))
retarget (addo O a σ) r = addo O a (λ q → σ (◃→Sim r q))

ret-≈ : ∀ {k k′ ℓ} {O : Obs k} {O′ : Obs ℓ} (r : k′ ◃ ℓ) → O ≈ᵒ O′ → O ≈ᵒ retarget O′ r
ret-≈ () idO
ret-≈ r (ψ⁰o o)    = ψ⁰o o
ret-≈ r (ψo o)     = ψo o
ret-≈ r (addo o e) = addo o e

ret-≈ˡ : ∀ {k ℓ ℓ′} {O′ : Obs ℓ} {O″ : Obs ℓ′} (r : k ◃ ℓ) → O′ ≈ᵒ O″ → retarget O′ r ≈ᵒ O″
ret-≈ˡ () idO
ret-≈ˡ r (ψ⁰o o)    = ψ⁰o o
ret-≈ˡ r (ψo o)     = ψo o
ret-≈ˡ r (addo o e) = addo o e

⊑ᵒ-trans◃ : ∀ {k₁ k₂ k₃} (r : k₂ ◃ k₃) {x : Ordᶜ k₁} {y : Ordᶜ k₂} {z : Ordᶜ k₃} → x ⊑ᵒ y → y ⊑ᵒ z → x ⊑ᵒ z
⊑ᵒ-trans◃ r h h′ o = ⊑-trans (h (ret-≈ r o)) (h′ (ret-≈ˡ r (≈ᵒ-reflʳ o)))
```

## §5 同余

按定义, $\sqsubseteq^\mathsf{o}$ 对 $\psi_p\sigma$ (任意目标层相同的两侧证明与证据)、`ψ⁰`、`add a σ` ($a\cong a'$) 是同余: 把运算推进观测栈即可. 透过提升节点也是一行: `run O (up r x)` 定义性地等于 "把 $r$ 并入 `O` 的最内层证据后 `run` $x$", 并入后的观测仍与原来的相似. 第 0 层没有提升节点, `idO` 的情况是荒谬的.

```agda
ψ-cong : ∀ {i k k′ ℓ ℓ′} {p : i <ʷ ℓ} {p′ : i <ʷ ℓ′} {σ : Simʷ k ℓ} {σ′ : Simʷ k′ ℓ′} {x : Ordᶜ k} {y : Ordᶜ k′} →
         x ⊑ᵒ y → ψ p σ x ⊑ᵒ ψ p′ σ′ y
ψ-cong h o = h (ψo o)

ψ⁰-cong : ∀ {k k′} {x : Ordᶜ k} {y : Ordᶜ k′} → x ⊑ᵒ y → ψ⁰ x ⊑ᵒ ψ⁰ y
ψ⁰-cong h o = h (ψ⁰o o)

add-cong : ∀ {k k′ ℓ ℓ′} {a : Ordᶜ ℓ} {a′ : Ordᶜ ℓ′} {σ : Simʷ k ℓ} {σ′ : Simʷ k′ ℓ′} {x : Ordᶜ k} {y : Ordᶜ k′} →
           a ≅ a′ → x ⊑ᵒ y → add a σ x ⊑ᵒ add a′ σ′ y
add-cong e h o = h (addo o e)

up-l : ∀ {k ℓ ℓ′} {r : k ◃₁ ℓ} {x : U k (◃₁→◃ r)} {y : Ordᶜ ℓ′} → out (◃₁→◃ r) x ⊑ᵒ y → up r x ⊑ᵒ y
up-l {r = zero}   h (ψ⁰o o)    = h (ψ⁰o o)
up-l {r = zero}   h (ψo o)     = h (ψo o)
up-l {r = zero}   h (addo o e) = h (addo o e)
up-l {r = self n} h (ψ⁰o o)    = h (ψ⁰o o)
up-l {r = self n} h (ψo o)     = h (ψo o)
up-l {r = self n} h (addo o e) = h (addo o e)

up-r : ∀ {k ℓ ℓ′} {r : k ◃₁ ℓ} {y : U k (◃₁→◃ r)} {x : Ordᶜ ℓ′} → x ⊑ᵒ out (◃₁→◃ r) y → x ⊑ᵒ up r y
up-r {r = zero}   h (ψ⁰o o)    = h (ψ⁰o o)
up-r {r = zero}   h (ψo o)     = h (ψo o)
up-r {r = zero}   h (addo o e) = h (addo o e)
up-r {r = self n} h (ψ⁰o o)    = h (ψ⁰o o)
up-r {r = self n} h (ψo o)     = h (ψo o)
up-r {r = self n} h (addo o e) = h (addo o e)
```

这就是 C1/C2 所缺的: 在 $\sqsubseteq^\mathsf{o}$ 下, "$\psi$ 保持步进" 不需要证明.

## §6 上界引理

四条关于极限与后继的引理, 都对观测对归纳. 每一条在 `ψo`/`ψ⁰o`/`addo` 处的论证相同: 这三种运算都**交换** `lim` (规则 5ω 与加法的 `lim` 子句), 所以把运算推进去, 对内层观测用归纳假设. 后继处用规则 4: $\psi(\mathrm{suc}\,y)$ 的第 1 项定义性地是 $\psi(y)+0=\psi(y)$.

- `lim-r`: $x\cong h\,n\Rightarrow x\sqsubseteq^\mathsf{o}\lim h$;
- `lim-l`: $(\forall n.\,h\,n\sqsubseteq^\mathsf{o}y)\Rightarrow\lim h\sqsubseteq^\mathsf{o}y$;
- `suc-r`: $x\cong y\Rightarrow x\sqsubseteq^\mathsf{o}\mathrm{suc}\,y$.

```agda
lim-r : ∀ {k k′} {x : Ordᶜ k} {h : ℕ → Ordᶜ k′} n → x ≅ h n → x ⊑ᵒ lim h
lim-r n e idO        = ⊑-lim n (≅→⊑ e)
lim-r n e (ψ⁰o o)    = lim-r n (ψ⁰≅ e) o
lim-r n e (ψo o)     = lim-r n (ψ-≅ e) o
lim-r n e (addo o a) = lim-r n (add-≅ a e) o

lim-l : ∀ {k k′} {h : ℕ → Ordᶜ k} {y : Ordᶜ k′} → (∀ n → h n ⊑ᵒ y) → lim h ⊑ᵒ y
lim-l k idO        = lim-⊑ (λ n → k n idO)
lim-l k (ψ⁰o o)    = lim-l (λ n o′ → k n (ψ⁰o o′)) o
lim-l k (ψo o)     = lim-l (λ n o′ → k n (ψo o′)) o
lim-l k (addo o a) = lim-l (λ n o′ → k n (addo o′ a)) o

suc-r : ∀ {k k′} {x : Ordᶜ k} {y : Ordᶜ k′} → x ≅ y → x ⊑ᵒ suc y
suc-r e idO        = λ h → ≺s (≺-respʳ h e)
suc-r e (ψ⁰o o)    = lim-r 1 (ψ⁰≅ e) o
suc-r e (ψo o)     = lim-r 1 (ψ-≅ e) o
suc-r e (addo o a) = suc-r (add-≅ a e) o
```

**`limᵢ-r`: 起点分支在节点之下.** $x\cong g(\Omega_j)\Rightarrow x\sqsubseteq^\mathsf{o}\lim_j g$. 对观测归纳: `idO` 荒谬 (没有 $j<^\mathsf{w}0$); `ψ⁰o` 走规则 6, 第 0 项是 $\psi^0(g(\gamma_0))=\psi^0(g(\Omega_j))$; `ψo` 按 `<ʷ-dec` 分两种: 穿透 (`injᵃ`) 时输出是新节点 $\lim_j(\psi\circ g)$, 它的起点分支是 $\psi(g(\Omega_j))$ (经 `out-into` 改写), 对内层观测递归; 折叠时输出的第 0 项是 $\psi(g(\Omega_j))$. `addo` 与穿透相同. 整个证明从不需要第 $k>0$ 项.

```agda
limᵢ-r : ∀ {k k′ j} {x : Ordᶜ k} {q : j <ʷ k′} {g : U j (<→◃ q) → Ordᶜ k′} →
         x ≅ g (into (<→◃ q) (Ω j)) → x ⊑ᵒ limᵢ q g
limᵢ-r {q = ()} e idO
limᵢ-r e (ψ⁰o o) = lim-r 0 (ψ⁰≅ e) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} e (ψo {p = p} {p′ = p′} {σ = σ} {σ′ = σ′} o) with <ʷ-dec (σ′ q) p′
... | injᵃ r = limᵢ-r (subst (λ u → ψ p σ x ≅ ψ p′ σ′ (g (into (<→◃ q) u))) (sym (out-into (<→◃ r) (Ω j))) (ψ-≅ e)) o
... | injᵇ _ = lim-r 0 (ψ-≅ e) o
... | injᶜ _ = lim-r 0 (ψ-≅ e) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} e (addo {a = a} {a′ = a′} {σ = σ} {σ′ = σ′} o ea) =
  limᵢ-r (subst (λ u → add a σ x ≅ add a′ σ′ (g (into (<→◃ q) u))) (sym (out-into (<→◃ (σ′ q)) (Ω j))) (add-≅ ea e)) o
```

## §7 链的起点: $\Omega_j\sqsubseteq^\mathsf{o}\psi_q z$

先是 $\cong$ 的几条反演. `limᵢ` 的反演不能写成 `limᵢ p f ≅ limᵢ p g → …`: 对 `lᵢ≅` 分情况时下标 $j$ 出现两次, 报 `[SplitError.UnificationStuck] … Cannot eliminate reflexive equation j = j of type Ordʷ because K has been disabled`. 改为右边任意 (`limᵢ p f ≅ b`), 只取左边的自反性, 并对 `upʳ` 递归.

```agda
s-inv : ∀ {k k′} {a : Ordᶜ k} {b : Ordᶜ k′} → suc a ≅ suc b → a ≅ b
s-inv (s≅ e) = e

l-inv : ∀ {k k′} {f : ℕ → Ordᶜ k} {g : ℕ → Ordᶜ k′} → lim f ≅ lim g → ∀ n → f n ≅ g n
l-inv (l≅ h) = h

i-inv : ∀ {k k′ j} {p : j <ʷ k} {f : U j (<→◃ p) → Ordᶜ k} {b : Ordᶜ k′} → limᵢ p f ≅ b →
        ∀ (z : Ordᶜ j) → z ≅ z → f (into (<→◃ p) z) ≅ f (into (<→◃ p) z)
i-inv {p = p} (lᵢ≅ h) z ez = ≅-reflˡ (h z z (≅→R (<→◃ p) ez))
i-inv (upʳ {r = zero} e)   = i-inv e
i-inv (upʳ {r = self n} e) = i-inv e

u-inv : ∀ {k ℓ ℓ′} (r : k ◃₁ ℓ) {x : U k (◃₁→◃ r)} {b : Ordᶜ ℓ′} → up r x ≅ b → out (◃₁→◃ r) x ≅ b
u-inv zero     (upˡ e)              = e
u-inv zero     (upʳ {r = zero} e)   = upʳ (u-inv zero e)
u-inv zero     (upʳ {r = self n} e) = upʳ (u-inv zero e)
u-inv (self m) (upˡ e)              = e
u-inv (self m) (upʳ {r = zero} e)   = upʳ (u-inv (self m) e)
u-inv (self m) (upʳ {r = self n} e) = upʳ (u-inv (self m) e)

u-refl : ∀ {k ℓ} (r : k ◃₁ ℓ) {x : U k (◃₁→◃ r)} → up r x ≅ up r x → out (◃₁→◃ r) x ≅ out (◃₁→◃ r) x
u-refl r e = ≅-reflˡ (u-inv r e)
```

**`B1`.** 对任意目标层与证据, $z\cong z\Rightarrow\Omega_j\sqsubseteq^\mathsf{o}\psi_q\sigma z$, 对 $z$ 归纳: $z=0$ 时两边就是 $\Omega_j$; 后继用 `lim-r 1` (规则 4 的第 1 项); `lim` 用第 0 项; `limᵢ` 穿透时用 `limᵢ-r` (起点分支), 折叠时用规则 6 的第 0 项 (链起点 $\Omega_{j'}$); 提升节点并入证据. 这正是 Certified `Ω⊑ψ` 的观测版, 而且它对**任意**观测成立: 它只用到 "第 0 项" 型的上界. `B1⁰` 是目标层 0 的无证明版本.

两个推论: 左加数在和之下 (`add-r`: $a\cong a'\Rightarrow a\sqsubseteq^\mathsf{o}a'+b$, 对 $b$ 归纳), 零在一切 (自反的) 树之下 (`zero-l`, 对观测分情况, 分别化为 `B1`、`B1⁰`、`add-r`). 注意 `zero-l` 在 `addo` 观测下要的是 $a\sqsubseteq^\mathsf{o}a'+y$, 在 `ψo` 观测下要的是 $\Omega_i\sqsubseteq^\mathsf{o}\psi y$: 零的 "最小性" 在观测下就是 `B1`.

```agda
B1 : ∀ {j ℓ k} {q : j <ʷ ℓ} {σ : Simʷ k ℓ} (z : Ordᶜ k) → z ≅ z → Ω j ⊑ᵒ ψ q σ z
B1 zero e = ≅→⊑ᵒ (Ω-refl _)
B1 {q = q} {σ = σ} (suc a) e = ⊑ᵒ-trans (B1 {q = q} {σ = σ} a (s-inv e)) (lim-r 1 (ψ-≅ (s-inv e)))
B1 {q = q} {σ = σ} (lim h) e = ⊑ᵒ-trans (B1 {q = q} {σ = σ} (h 0) (l-inv e 0)) (lim-r 0 (ψ-≅ (l-inv e 0)))
B1 {q = q} {σ = σ} (limᵢ {i = j′} q′ g) e with <ʷ-dec (σ q′) q
... | injᵃ r = ⊑ᵒ-trans (B1 {q = q} {σ = σ} (g (into (<→◃ q′) (Ω j′))) eg)
                 (limᵢ-r (subst (λ u → ψ q σ (g (into (<→◃ q′) (Ω j′))) ≅ ψ q σ (g (into (<→◃ q′) u)))
                                (sym (out-into (<→◃ r) (Ω j′))) (ψ-≅ eg)))
  where eg = i-inv e (Ω j′) (Ω-refl j′)
... | injᵇ _ = ⊑ᵒ-trans (B1 {q = q} {σ = σ} (g (into (<→◃ q′) (Ω j′))) eg) (lim-r 0 (ψ-≅ eg))
  where eg = i-inv e (Ω j′) (Ω-refl j′)
... | injᶜ _ = ⊑ᵒ-trans (B1 {q = q} {σ = σ} (g (into (<→◃ q′) (Ω j′))) eg) (lim-r 0 (ψ-≅ eg))
  where eg = i-inv e (Ω j′) (Ω-refl j′)
B1 (up zero x) e     = B1 x (u-refl zero e)
B1 (up (self n) x) e = B1 x (u-refl (self n) e)

B1⁰ : ∀ {k} (z : Ordᶜ k) → z ≅ z → Ω zero ⊑ᵒ ψ⁰ z
B1⁰ zero e = ≅→⊑ᵒ (Ω-refl zero)
B1⁰ (suc a) e = ⊑ᵒ-trans (B1⁰ a (s-inv e)) (lim-r 1 (ψ⁰≅ (s-inv e)))
B1⁰ (lim h) e = ⊑ᵒ-trans (B1⁰ (h 0) (l-inv e 0)) (lim-r 0 (ψ⁰≅ (l-inv e 0)))
B1⁰ (limᵢ {i = j′} q′ g) e = ⊑ᵒ-trans (B1⁰ (g (into (<→◃ q′) (Ω j′))) eg) (lim-r 0 (ψ⁰≅ eg))
  where eg = i-inv e (Ω j′) (Ω-refl j′)
B1⁰ (up zero x) e     = B1⁰ x (u-refl zero e)
B1⁰ (up (self n) x) e = B1⁰ x (u-refl (self n) e)

add-r : ∀ {k ℓ ℓ′} {a : Ordᶜ ℓ} {a′ : Ordᶜ ℓ′} {σ : Simʷ k ℓ′} (b : Ordᶜ k) → a ≅ a′ → b ≅ b → a ⊑ᵒ add a′ σ b
add-r zero    ea eb = ≅→⊑ᵒ ea
add-r {σ = σ} (suc b) ea eb = ⊑ᵒ-trans (add-r {σ = σ} b ea (s-inv eb)) (suc-r (add-≅ (≅-reflʳ ea) (s-inv eb)))
add-r {σ = σ} (lim h) ea eb = ⊑ᵒ-trans (add-r {σ = σ} (h 0) ea (l-inv eb 0)) (lim-r 0 (add-≅ (≅-reflʳ ea) (l-inv eb 0)))
add-r {a′ = a′} {σ = σ} (limᵢ {i = j} q g) ea eb =
  ⊑ᵒ-trans (add-r {σ = σ} (g (into (<→◃ q) (Ω j))) ea eg)
    (limᵢ-r (subst (λ u → add a′ σ (g (into (<→◃ q) (Ω j))) ≅ add a′ σ (g (into (<→◃ q) u)))
                   (sym (out-into (<→◃ (σ q)) (Ω j))) (add-≅ (≅-reflʳ ea) eg)))
  where eg = i-inv eb (Ω j) (Ω-refl j)
add-r (up zero x)     ea eb = add-r x ea (u-refl zero eb)
add-r (up (self n) x) ea eb = add-r x ea (u-refl (self n) eb)

zero-l : ∀ {k k′} {y : Ordᶜ k′} → y ≅ y → 𝟎 {k} ⊑ᵒ y
zero-l ey idO         = λ ()
zero-l ey (ψ⁰o o)     = B1⁰ _ ey o
zero-l ey (ψo o)      = B1 _ ey o
zero-l ey (addo o ea) = add-r _ ea ey o
```

## §8 $\Omega$ 的单调性 (观测版, 跨层)

$a\sqsubseteq^\mathsf{w}b\Rightarrow\Omega_a\sqsubseteq^\mathsf{o}\Omega_b$, 证明与 Cumulative 的 `Ψ-mono` 同形, 但不再分目标层的情况: 一步 $\Omega_c\sqsubseteq^\mathsf{o}\Omega_{c+1}$ 就是 `limᵢ-r` (起点分支 $\mathtt{up}\,\Omega_c$), 极限层用 `lim-r`/`lim-l` 与透过提升. 三层不同的传递用 `⊑ᵒ-trans◃`, 中间层是右端的直接前驱 (`zero` 或 `self n`).

```agda
Ω-suc : ∀ c → Ω c ⊑ᵒ Ω (suc c)
Ω-suc c = limᵢ-r (upʳ (Ω-refl c))

Ω0 : ∀ b → Ω zero ⊑ᵒ Ω b
Ω0 zero      = ≅→⊑ᵒ (Ω-refl zero)
Ω0 (suc b)   = ⊑ᵒ-trans◃ zero (Ω0 b) (Ω-suc b)
Ω0 (lim g s) = ⊑ᵒ-trans◃ (self 0) (Ω0 (g 0)) (lim-r 0 (upʳ (Ω-refl (g 0))))

Ω< : ∀ {a b} → a <ʷ b → Ω (suc a) ⊑ᵒ Ω b
Ω< zero = ≅→⊑ᵒ (Ω-refl _)
Ω< {b = suc b} (suc q) = ⊑ᵒ-trans◃ zero (Ω< q) (Ω-suc b)
Ω< (lim n q) = ⊑ᵒ-trans◃ (self n) (Ω< q) (lim-r n (upʳ (Ω-refl _)))

Ω-monoᵒ : ∀ {a b} → a ⊑ʷ b → Ω a ⊑ᵒ Ω b
Ω-monoᵒ {b = b} z⊑ = Ω0 b
Ω-monoᵒ (s⊑ q)     = Ω< q
Ω-monoᵒ (l⊑ k)     = lim-l (λ n → up-l (Ω-monoᵒ (k n)))
```

## §9 遗传好树 `Good` 及其封闭性

`Good` 与 Cumulative 的 `R` 同一模式: 较低层的谓词作参数 `G<`, 再对 $\triangleleft$ 的证明递归定义 (`Gd`). 条件: `lim` 的相邻项 $\sqsubseteq^\mathsf{o}$-步进; `limᵢ` 的分支在好的 (且 $\cong$-自反的) 输入上是好的, 且分支函数 $\sqsubseteq^\mathsf{o}$-单调 (对**一切**输入, 不要求好); 提升节点的内容是好的.

```agda
module _ (ℓ : Ordʷ) (G< : (i : Ordʷ) (r : i ◃ ℓ) → U i r → Set) where
  data Good₊ : Ordᶜ ℓ → Set where
    gz : Good₊ zero
    gs : ∀ {a} → Good₊ a → Good₊ (suc a)
    gl : ∀ {h : ℕ → Ordᶜ ℓ} → (∀ n → Good₊ (h n)) → (∀ n → h n ⊑ᵒ h (suc n)) → Good₊ (lim h)
    gi : ∀ {j} {p : j <ʷ ℓ} {f : U j (<→◃ p) → Ordᶜ ℓ} →
         (∀ (z : Ordᶜ j) → z ≅ z → G< j (<→◃ p) (into (<→◃ p) z) → Good₊ (f (into (<→◃ p) z))) →
         (∀ {z z′ : Ordᶜ j} → z ⊑ᵒ z′ → f (into (<→◃ p) z) ⊑ᵒ f (into (<→◃ p) z′)) →
         Good₊ (limᵢ p f)
    gu : ∀ {k} {r : k ◃₁ ℓ} {x : U k (◃₁→◃ r)} → G< k (◃₁→◃ r) x → Good₊ (up r x)

Gd : ∀ {ℓ} (i : Ordʷ) (r : i ◃ ℓ) → U i r → Set
Gd i zero         x = Good₊ i Gd x
Gd i (suc r)      x = Gd i r x
Gd _ (self {f} n) x = Good₊ (f n) Gd x
Gd i (lim n r)    x = Gd i r x

Good : ∀ {ℓ} → Ordᶜ ℓ → Set
Good {ℓ} = Good₊ ℓ Gd

Gd→Good : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordᶜ i} → Gd i r (into r x) → Good x
Gd→Good zero      g = g
Gd→Good (suc r)   g = Gd→Good r g
Gd→Good (self n)  g = g
Gd→Good (lim n r) g = Gd→Good r g

Good→Gd : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordᶜ i} → Good x → Gd i r (into r x)
Good→Gd zero      g = g
Good→Gd (suc r)   g = Good→Gd r g
Good→Gd (self n)  g = g
Good→Gd (lim n r) g = Good→Gd r g

Gd-conv : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) (r′ : i ◃ ℓ′) {x : Ordᶜ i} → Gd i r (into r x) → Gd i r′ (into r′ x)
Gd-conv r r′ g = Good→Gd r′ (Gd→Good r g)
```

**封闭性.** `Good` 对 $\Omega$、加法 (左加数好且自反)、规则 4 的倍数、$\psi_p\sigma$、`ψ⁰` 封闭. 新出现的分支函数是 `up`、$a+f$、$\psi\circ f$, 单调性分别是 `up-l`/`up-r`、`add-cong`、`ψ-cong`, 只需经 `out-into` 改写 `coe`. 规则 4 的步进 $c\cdot n\sqsubseteq^\mathsf{o}c\cdot(n+1)=c+c\cdot n$ 对 $n$ 归纳: 第 0 步是 `zero-l`, 其后是加法对右加数的同余 (不需要左加数的同余, 也不需要 "后继的同余", 后者在观测下是多洞的).

$\Omega_{\lim g}$ 的步进来自 `Ω-monoᵒ`; $\Omega_{\mathrm{suc}\,c}$ 只要求分支函数 `up zero` 单调, 与 $c$ 无关.

```agda
Good-Ω : ∀ a → Good (Ω a)
Good-Ω zero      = gs gz
Good-Ω (suc c)   = gi (λ z ez g → gu g) (λ h → up-l (up-r h))
Good-Ω (lim g s) = gl (λ n → gu (Good-Ω (g n))) (λ n → up-l (up-r (Ω-monoᵒ (s n))))

Good-add : ∀ {k ℓ} {a : Ordᶜ ℓ} {σ : Simʷ k ℓ} {b : Ordᶜ k} → Good a → a ≅ a → Good b → Good (add a σ b)
Good-add ga ea gz          = ga
Good-add ga ea (gs g)      = gs (Good-add ga ea g)
Good-add ga ea (gl hg st)  = gl (λ n → Good-add ga ea (hg n)) (λ n → add-cong ea (st n))
Good-add {a = a} {σ = σ} ga ea (gi {p = q} {f = f} hb hm) = gi
  (λ z ez g → subst (λ u → Good (add a σ (f (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ q)) z))
                    (Good-add ga ea (hb z ez (Gd-conv (<→◃ (σ q)) (<→◃ q) g))))
  (λ {z} {z′} h → subst₂ (λ u v → add a σ (f (into (<→◃ q) u)) ⊑ᵒ add a σ (f (into (<→◃ q) v)))
                         (sym (out-into (<→◃ (σ q)) z)) (sym (out-into (<→◃ (σ q)) z′)) (add-cong ea (hm h)))
Good-add ga ea (gu {r = zero} g)   = Good-add ga ea g
Good-add ga ea (gu {r = self n} g) = Good-add ga ea g

Good-iter : ∀ {ℓ} {c : Ordᶜ ℓ} → Good c → c ≅ c → ∀ n → Good (iter (c +_) zero n)
Good-iter gc ec zero    = gz
Good-iter gc ec (suc n) = Good-add gc ec (Good-iter gc ec n)

rule4ᵒ : ∀ {ℓ} {c : Ordᶜ ℓ} → c ≅ c → ∀ n → iter (c +_) zero n ⊑ᵒ iter (c +_) zero (suc n)
rule4ᵒ ec zero    = zero-l ec
rule4ᵒ ec (suc n) = add-cong ec (rule4ᵒ ec n)
```

**链的步进.** 对节点 $(j,q,f)$, 若 $f$ 单调 (且节点 $\cong$-自反), 则它的链 $\sqsubseteq^\mathsf{o}$-递增 (`chain-step`): 第 0 步 $\Omega_j\sqsubseteq^\mathsf{o}\psi_q(f\,\Omega_j)$ 是 `B1`; 其后 $\gamma_k\sqsubseteq^\mathsf{o}\gamma_{k+1}\Rightarrow f\gamma_k\sqsubseteq^\mathsf{o}f\gamma_{k+1}\Rightarrow\psi_q(f\gamma_k)\sqsubseteq^\mathsf{o}\psi_q(f\gamma_{k+1})$. 这就是安全路径引理的形式: **不是** "$\psi$ 单调", 而是 "链是同一个上下文作用在前一步上".

```agda
chain : ∀ {j k} (q : j <ʷ k) (f : U j (<→◃ q) → Ordᶜ k) → ℕ → Ordᶜ j
chain {j} q f = iter (λ x → ψ q (λ r → r) (f (into (<→◃ q) x))) (Ω j)

chain-≅ : ∀ {j k k′} {q : j <ʷ k} {f : U j (<→◃ q) → Ordᶜ k} {b : Ordᶜ k′} → limᵢ q f ≅ b → ∀ n → chain q f n ≅ chain q f n
chain-≅ {j} e zero    = Ω-refl j
chain-≅ {q = q} e (suc n) = ψ-≅ {p = q} {σ = λ r → r} {p′ = q} {σ′ = λ r → r} (i-inv e _ (chain-≅ e n))

chain-step : ∀ {j k k′} {q : j <ʷ k} {f : U j (<→◃ q) → Ordᶜ k} {b : Ordᶜ k′} → limᵢ q f ≅ b →
             (∀ {z z′ : Ordᶜ j} → z ⊑ᵒ z′ → f (into (<→◃ q) z) ⊑ᵒ f (into (<→◃ q) z′)) →
             ∀ n → chain q f n ⊑ᵒ chain q f (suc n)
chain-step {j} {q = q} {f = f} e hm zero = B1 {q = q} {σ = λ r → r} (f (into (<→◃ q) (Ω j))) (i-inv e (Ω j) (Ω-refl j))
chain-step e hm (suc n) = ψ-cong (hm (chain-step e hm n))
```

**`Good-ψ`.** 对 `Good` 的推导归纳, `limᵢ` 处与 `ψ` 对同一个 `<ʷ-dec` 分情况. 穿透时新节点的分支函数是 $\psi\circ f\circ\mathtt{coe}$; 折叠时输出是 $\lim_n\psi(f\gamma_n)$, 各项好要求链上各点好 (`chain-good`, 与 `Good-ψ` 互递归: 对 `hb` 的应用递归, 停机检查器接受), 步进是 `chain-step` 再加 `ψ-cong`. `Good-ψ⁰` 同理, 只有规则 6.

```agda
Good-ψ : ∀ {i k ℓ} {p : i <ʷ ℓ} {σ : Simʷ k ℓ} {x : Ordᶜ k} → Good x → x ≅ x → Good (ψ p σ x)
chain-good : ∀ {j k} {q : j <ʷ k} {f : U j (<→◃ q) → Ordᶜ k} →
             (∀ (z : Ordᶜ j) → z ≅ z → Gd j (<→◃ q) (into (<→◃ q) z) → Good (f (into (<→◃ q) z))) →
             limᵢ q f ≅ limᵢ q f → ∀ n → Good (chain q f n)
chain-good {j} hb e zero = Good-Ω j
chain-good {q = q} {f = f} hb e (suc n) =
  Good-ψ (hb (chain q f n) (chain-≅ e n) (Good→Gd (<→◃ q) (chain-good hb e n))) (i-inv e _ (chain-≅ e n))

Good-ψ {i} gz ex = Good-Ω i
Good-ψ {p = p} {σ = σ} (gs {a} g) ex = gl (Good-iter (Good-ψ g ea) eψ) (rule4ᵒ eψ)
  where ea = s-inv ex
        eψ = ψ-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} ea
Good-ψ (gl hg st) ex = gl (λ n → Good-ψ (hg n) (l-inv ex n)) (λ n → ψ-cong (st n))
Good-ψ {p = p} {σ = σ} (gi {j = j} {p = q} {f = f} hb hm) ex with <ʷ-dec (σ q) p
... | injᵃ r = gi
  (λ z ez g → subst (λ u → Good (ψ p σ (f (into (<→◃ q) u)))) (sym (out-into (<→◃ r) z))
                    (Good-ψ (hb z ez (Gd-conv (<→◃ r) (<→◃ q) g)) (i-inv ex z ez)))
  (λ {z} {z′} h → subst₂ (λ u v → ψ p σ (f (into (<→◃ q) u)) ⊑ᵒ ψ p σ (f (into (<→◃ q) v)))
                         (sym (out-into (<→◃ r) z)) (sym (out-into (<→◃ r) z′)) (ψ-cong (hm h)))
... | injᵇ _ = gl (λ n → Good-ψ (hb (chain q f n) (chain-≅ ex n) (Good→Gd (<→◃ q) (chain-good hb ex n)))
                                (i-inv ex _ (chain-≅ ex n)))
                  (λ n → ψ-cong (hm (chain-step ex hm n)))
... | injᶜ _ = gl (λ n → Good-ψ (hb (chain q f n) (chain-≅ ex n) (Good→Gd (<→◃ q) (chain-good hb ex n)))
                                (i-inv ex _ (chain-≅ ex n)))
                  (λ n → ψ-cong (hm (chain-step ex hm n)))
Good-ψ (gu {r = zero} g) ex   = Good-ψ g (u-refl zero ex)
Good-ψ (gu {r = self n} g) ex = Good-ψ g (u-refl (self n) ex)

Good-ψ⁰ : ∀ {k} {x : Ordᶜ k} → Good x → x ≅ x → Good (ψ⁰ x)
Good-ψ⁰ gz ex = gs gz
Good-ψ⁰ (gs {a} g) ex = gl (Good-iter (Good-ψ⁰ g ea) (ψ⁰≅ ea)) (rule4ᵒ (ψ⁰≅ ea))
  where ea = s-inv ex
Good-ψ⁰ (gl hg st) ex = gl (λ n → Good-ψ⁰ (hg n) (l-inv ex n)) (λ n → ψ⁰-cong (st n))
Good-ψ⁰ (gi {p = q} {f = f} hb hm) ex =
  gl (λ n → Good-ψ⁰ (hb (chain q f n) (chain-≅ ex n) (Good→Gd (<→◃ q) (chain-good hb ex n))) (i-inv ex _ (chain-≅ ex n)))
     (λ n → ψ⁰-cong (hm (chain-step ex hm n)))
Good-ψ⁰ (gu {r = zero} g) ex   = Good-ψ⁰ g (u-refl zero ex)
Good-ψ⁰ (gu {r = self n} g) ex = Good-ψ⁰ g (u-refl (self n) ex)
```

## §10 决定性检验

**第 0 层的遗传步进 `HS`** 按任务的形状定义, 步进关系是 Cumulative §6 的 $\sqsubseteq$ (叶子 $\cong$). 第 0 层的好树都遗传步进 (`Good→HS`): 用恒等观测 `idO`. 于是对任意层号 $a$, $\psi^0(\Omega_a)$ 遗传步进 (`HS-diag`, **检验 4**), $x_3$ 是特例 (`HS-x₃`, **检验 3**, 其中 `x₃` 就是 Cumulative 的 `ψ⁰ (Ω ε₀ʷ)`).

```agda
data HS : Ordᶜ zero → Set where
  hz : HS zero
  hs : ∀ {a} → HS a → HS (suc a)
  hl : ∀ {f : ℕ → Ordᶜ zero} → (∀ n → HS (f n)) → (∀ n → f n ⊑ f (suc n)) → HS (lim f)

Good→HS : ∀ {x : Ordᶜ zero} → Good x → HS x
Good→HS gz         = hz
Good→HS (gs g)     = hs (Good→HS g)
Good→HS (gl hg st) = hl (λ n → Good→HS (hg n)) (λ n → st n idO)
Good→HS (gi {p = ()} hb hm)
Good→HS (gu {r = ()} g)

HS-diag : ∀ a → HS (ψ⁰ (Ω a))
HS-diag a = Good→HS (Good-ψ⁰ (Good-Ω a) (Ω-refl a))

HS-x₃ : HS x₃
HS-x₃ = HS-diag ε₀ʷ
```

**第四行 (检验 1、2).** $\Omega_{\mathrm{suc}\,c}$ 的 $\psi_c$-链 $\gamma^c$ 与 `ψ⁰` 的展开 `refl` 一致; 链步进 (`γᶜ-step`) 的第 0 步是 `B1` 作用于 $\mathtt{up}\,\Omega_c$, 其后是 `ψ-cong` (注意 $\psi_c(\mathtt{up}\,y)$ 定义性地是 $\psi_c$ 以证据 `suc` 作用于 $y$, 提升节点已被并入). 用观测 `ψ⁰o idO` 得到第 0 层的 $\sqsubseteq$: 对任意 $c$ (包括 $c=0$, 即 Cumulative 的第三行), $\psi^0(\gamma^c_n)\sqsubseteq\psi^0(\gamma^c_{n+1})$.

```agda
γᶜ : ∀ c → ℕ → Ordᶜ c
γᶜ c = iter (λ x → ψ zero (λ r → r) (up zero x)) (Ω c)

_ : ∀ c → ψ⁰ (Ω (suc c)) ≡ lim (λ n → ψ⁰ (γᶜ c n))
_ = λ c → refl

γᶜ-step : ∀ c n → γᶜ c n ⊑ᵒ γᶜ c (suc n)
γᶜ-step c zero    = B1 {q = zero} {σ = λ r → r} (up zero (Ω c)) (upˡ (upʳ (Ω-refl c)))
γᶜ-step c (suc n) = ψ-cong {p = zero} {p′ = zero} {σ = λ r → suc r} {σ′ = λ r → suc r} (γᶜ-step c n)

row4 : ∀ c n → ψ⁰ (γᶜ c n) ⊑ ψ⁰ (γᶜ c (suc n))
row4 c n = γᶜ-step c n (ψ⁰o idO)

row4-c1 : ∀ n → ψ⁰ (γᶜ (suc zero) n) ⊑ ψ⁰ (γᶜ (suc zero) (suc n))
row4-c1 = row4 (suc zero)
```

**反例对被拒绝.** `ψ-not-⊑mono` 说 $\mathrm{suc}\,a_1\sqsubseteq\Omega_1$ 而 $\psi_0(\mathrm{suc}\,a_1)\not\sqsubseteq\psi_0(\Omega_1)$. $\psi_0$ 本身是一个观测 (`ψo idO zero id`), 所以 $\mathrm{suc}\,a_1\not\sqsubseteq^\mathsf{o}\Omega_1$. 换个角度: $\mathrm{suc}\,a_1\sqsubseteq\Omega_1$ 经过的是非链分支 $(\lim G)+1$, 而 $\sqsubseteq^\mathsf{o}$ 进入 `limᵢ` 节点的唯一途径是起点分支 (`limᵢ-r`) 与同余, 都碰不到那个分支. §1 的 C1 反例对 ($\uparrow^2\Omega_1$ 对 $\uparrow^2\varepsilon_0$) 同理不在 $\sqsubseteq^\mathsf{o}$ 中 (观测 $\psi_0\circ\psi_1$ 把它送到一对严格反序的序数; 这一条是纸面论证, 未编译).

```agda
⊑ᵒ-rejects : ¬ (suc a₁ ⊑ᵒ Ω₁)
⊑ᵒ-rejects h = proj₂ ψ-not-⊑mono (h (ψo {p = zero} {p′ = zero} {σ = λ q → q} {σ′ = λ q → q} idO))
```

**接口: 层号的前提.** `HS-diag` 对 `Ordʷ` 的每个元素成立, 没有附加前提. 它实际用到的只是 `Good (Ω a)`, 而这又只依赖 $a$ 的**极限脊**上的步进: $\Omega_{\mathrm{suc}\,c}$ 对任意 $c$ 都好, $\Omega_{\lim g}$ 好当且仅当各 $\Omega_{g\,n}$ 好且 $\Omega_{g\,n}\sqsubseteq^\mathsf{o}\Omega_{g(n+1)}$. 这就是 `ΩStep`; 对 `Ordʷ` 它由字面的 $\sqsubseteq^\mathsf{w}$ 经 `Ω-monoᵒ` 给出 (`ΩStep-all`). 若另一个下标类型的 `lim` 证据只在某种互模拟 $\cong^\mathsf{w}$ 下成立, 它需要提供的恰是 `ΩStep` 的第三个字段, 即观测版的 $\Omega_{g\,n}\sqsubseteq^\mathsf{o}\Omega_{g(n+1)}$.

```agda
data ΩStep : Ordʷ → Set where
  z : ΩStep zero
  s : ∀ {c} → ΩStep (suc c)
  l : ∀ {g : ℕ → Ordʷ} {t : ∀ n → g n ⊑ʷ g (suc n)} →
      (∀ n → ΩStep (g n)) → (∀ n → Ω (g n) ⊑ᵒ Ω (g (suc n))) → ΩStep (lim g t)

Good-Ωˢ : ∀ {a} → ΩStep a → Good (Ω a)
Good-Ωˢ z       = gs gz
Good-Ωˢ (s {c}) = Good-Ω (suc c)
Good-Ωˢ (l h st) = gl (λ n → gu (Good-Ωˢ (h n))) (λ n → up-l (up-r (st n)))

ΩStep-all : ∀ a → ΩStep a
ΩStep-all zero      = z
ΩStep-all (suc c)   = s
ΩStep-all (lim g t) = l (λ n → ΩStep-all (g n)) (λ n → Ω-monoᵒ (t n))

HS-diagˢ : ∀ {a} → ΩStep a → HS (ψ⁰ (Ω a))
HS-diagˢ {a} h = Good→HS (Good-ψ⁰ (Good-Ωˢ h) (Ω-refl a))
```

## §11 对比

| 候选 | 链步进 | $\psi$ 保持 | 拒绝 `ψ-not-⊑mono` 的对 | 第 0 层给出 $\sqsubseteq$ | 结局 |
|---|---|---|---|---|---|
| Cumulative 的 $\sqsubseteq$ (基线) | 未知 | 否 (`ψ-not-⊑mono`) | 否 | 是 | 缺口所在 |
| C1 $\sqsubseteq^\mathsf{g}$ (只经链分支) | — | 否, 穿透处 (§1 数值反例: $\psi_0\psi_1$ 反序) | 是 | 是 | 放弃 |
| Certified $\sqsubseteq_p$ (依目标层) | 是 (`rule6-chain`, 有前提) | 只到完全 $\sqsubseteq$ (`ψ-⊑ₚ`), 不能复合 | 是 | 是 | 不能逐层复合 |
| C2 归纳同余闭包 $\trianglelefteq$ | 是 (定义) | 是 (定义) | 是 | 可靠性证明需对运算栈归纳 | 语义化为 C2′ |
| **C2′ 观测前序 $\sqsubseteq^\mathsf{o}$ (本文)** | **是** (`chain-step`, `γᶜ-step`) | **是** (`ψ-cong`, 一行) | **是** (`⊑ᵒ-rejects`) | **是** (`idO`) | **采用, 检验 1–4 通过** |
| C3 标准性谓词 | — | 预期是 | 是 | — | 不需要, 未做 |

## §12 结论与边界

**已证** (全部 `--safe --without-K`, 无公设、无洞、无编译指示):

1. 观测前序 $\sqsubseteq^\mathsf{o}$ 的基本理论: $\cong\subseteq\sqsubseteq^\mathsf{o}$ (`≅→⊑ᵒ`), 三种传递 (`⊑ᵒ-trans`, `⊑ᵒ-transˡ`, `⊑ᵒ-trans◃`), 同余 (`ψ-cong`, `ψ⁰-cong`, `add-cong`, `up-l`, `up-r`), 上界 (`lim-r`, `lim-l`, `suc-r`, `limᵢ-r`, `add-r`, `zero-l`), 链起点 (`B1`, `B1⁰`), $\Omega$ 的单调性 (`Ω-monoᵒ`).
2. 安全路径引理的形式: 分支函数单调的节点, 其 $\gamma$-链 $\sqsubseteq^\mathsf{o}$-递增 (`chain-step`).
3. 遗传好树 `Good` 对 $\Omega$、加法、$\psi_p\sigma$、`ψ⁰` 封闭 (`Good-Ω`, `Good-add`, `Good-ψ`, `Good-ψ⁰`); 第 0 层的好树遗传步进 (`Good→HS`).
4. 检验 1–4: `row4-c1`、`row4` (任意 $c$)、`HS-x₃`、`HS-diag` (任意 $a$ : `Ordʷ`, 无前提); 带显式前提的版本 `HS-diagˢ : ΩStep a → HS (ψ⁰ (Ω a))`.
5. 反例对被拒绝 (`⊑ᵒ-rejects`).

**未证与边界.**

- **字面版本 (内涵性).** `HS` 的步进是模 $\cong$ 的. 字面的 $\sqsubseteq^0$ (Cumulative §9) 要求闭包定义性相等; 观测两侧的 `Sim` 证据不同 (极限层 $\Omega$ 的两个提升节点、穿透时 `<ʷ-dec` 写进输出的证明), 本文的方法在这里给不出字面结论. 这不是数学缺口.
- **证书 (内涵性).** Certified 的 `CertDiag` 第 1 步要一个 $L_2$ : `Ordʷ`, 其 `lim` 证据是层号之间的**字面** $\sqsubseteq^\mathsf{w}$, 而且建在 `W` 的树族上 (不是 `Ordᶜ`). `HS-x₃` 给出了它需要的数学内容 ($x_3$ 内部的每个序列都步进), 但把模 $\cong$ 的树步进变成字面的层号步进, 需要一个 "证据模 $\cong^\mathsf{w}$" 的下标类型, 或把 `HS` 的步进翻译成那个类型的证据. 本文只给出接口: `HS` 如上定义, 一致定理 `HS-diag : ∀ a → HS (ψ⁰ (Ω a))`, 以及它对层号的精确前提 `ΩStep`.
- **对角线的后续各项.** $x_{n+1}=\psi_0(\Omega_{x_n})$ 要把第 0 层的树 $x_n$ 变成层号; `HS-diag` 对**任意**层号成立, 所以每一步的数学内容都已具备, 剩下的是 "树 → 层号" 的转换, 即上一条.
- §1 的 C1 反例是纸面的 (序数值与 Buchholz $\psi_0$ 在标准参数上的严格单调性), 未编译; C3 未做.
- 本文不改 `src/`、`archive/` 与已有的 Align 文件.
