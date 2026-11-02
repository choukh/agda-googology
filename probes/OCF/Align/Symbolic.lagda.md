# 符号化的 $\Omega_\Omega$: 上下文链计值与逐步现造的公共层号

> 接 [Stage2](Stage2.lagda.md) §10. 那里由三个已编译的否定 (D1 的 `dec→WLPO`, D2 的上界太小, D3 的静态前缀 `X₂-unlabel`/`stage2-unlabel`) 推出下一个设计的五条要求: 符号化的 $\Omega_\Omega$ 与 $\psi_\delta(\Omega_\Omega)$, 由上下文链计值, 逐步现造的公共上界, `Good` 的推广, 记号侧的推广. 本文做树侧, 决定性检验是 $\psi_0(\Omega_\Omega\cdot2)$ 的遗传标签.
>
> 结论先说:
>
> 1. **最小文法不是 $\{\hat\Omega,\hat\psi_\delta\}$ (§1).** 用 Python 模拟器读出 EBO 的基本列闭包, 再用 `refl` 核对: 符号尾 (以 $\Omega_\Omega$ 结尾、共尾度 $\Omega_1$ 的参数) 在每个 $\psi_\delta$ ($\delta\ge1$) 下穿透, 只在 $\psi_0$ 处折叠 (`symb-cof`, `A-fs0`/`A-fs1`); 而在 $\psi_0(\Omega_\Omega\cdot2)$ 的闭包里, 第 1 层的符号对象的参数含第 2 层的符号对象: $\psi_1(\Omega_\Omega+\psi_2(\Omega_\Omega)+\psi_2(\Omega_\Omega))$ (`N3-path`, 从 `t2` 出发 10 步). 所以符号节点必须携带比自身层号更高的数据.
> 2. **两个已编译的否定决定了表示 (§2, §3).** (a) 若 $\hat\Omega$ 是可数层树族的构造子 (不论带不带分支), 它会作为 $\Omega_{\eta+1}$ 的分支输入出现, "计值 + 取分支 + 下降"构成环 (`loop : ¬ Acc▹ (a Ω̂ᴬ)`): 折叠不能对树结构递归. 所以 $\Omega_\Omega$ 本身不能进入可数层, 只能活在参数层 (前缀栈). (b) 层号为 $\delta$ 的树族 `Ordᶜ δ` 只能存放 $\triangleleft\delta$ 的层的数据 (归纳-递归的 `U`), 存不下 §1 的 "更高的前缀"; 唯一的出路是把 $\psi_\delta(\cdots\Omega_\Omega)$ 存成**定义域受支配的闭包** $\hat s\,c\,t_0\,g$, $g:\prod_\eta\,c\sqsubseteq^\mathsf I\eta\to\cdots$. 带这两个构造子 (`ŝ`, `ĉᴸ`) 的树族 `Ordˢ` 严格正 (§3 编译通过). 它有分支函数, 但定义域带公共上界的证据, 所以 D1 的 WLPO 论证不适用 (派发只在 `Mlev c η e` 内进行).
> 3. **逐步现造的公共层号是类型化的 (§4, §5).** `Mlev c η e = lim [c, η, η, …]`, 步进证据就是支配证据 $e:c\sqsubseteq^\mathsf I\eta$. 上下文链 `Ctx` (Stage2 的 `St`/`step`/`Γ₂`/`M` 的一般化): 链点的证书 `HS` 与支配证据 `dx` 随链携带, 链 $T$ 自带证书 `Tᶜ-HS`, 可回灌为层号. 第 0 层的待计值折叠节点 `ĉ` 用**归纳-递归**的 `Goodᶻ`/`force`/`force-HS` 计值: `Goodᶻ` 的 `ĉ` 子句的字段正是 `Ctx` 的字段 (取 `force` 之后), `force (ĉ …) ≡ Tᶜ …`. 这就是 §10 第 2 条的不变量 ("链从第 1 点起支配上下文里的可数下标") 的构造性形式, 编译通过.
> 4. **检验 1 通过 (§6).** `zβ` (= $\psi_0(\Omega_\Omega)$ 的符号节点) 计值后 `≡ Tᶜ Cβ` (`refl`), 且 `Tβ≅ : Tᶜ Cβ ≅ BTBOᴵ`; 于是 `zβ-label : Lab (force zβ Gβ) ψ₀(Ω_Ω)`, `zβ1-label : … ψ₀(Ω_Ω+1)`. $\psi_0(\Omega_\Omega+\Omega)$ 的标签沿用 Stage2 的 `χ1-label` (可数尾巴时静态前缀与符号前缀一致, §6 末).
> 5. **检验 2: Stage2 的失败点修好了, 但失败只是下移一层 (§7).** Stage2 的 `X₂-unlabel` 的 10 步路径在第 3 步到达 $A=\psi_0(\Omega_\Omega+\psi_1(\Omega_\Omega))$ (`X₂-at-A`); 本文为 $A$ 造的上下文链树 `TA` 沿余下 7 步到达 `BTBOᴵ` 而不是 $0$ (`A-repaired`, `refl`), 终点带 $\psi_0(\Omega_\Omega)$ 的标签 (`A-end-label`); 外层一步形状逐项 `refl`. 但只计值最外层的 $\Omega_\Omega$ 仍不够: 深一层的 $B=\psi_0(\Omega_\Omega+\psi_1(\Omega_\Omega+\psi_1(\Omega_\Omega)))$, 第 0 点树沿 9 步到 $0$ 而记号是 $\psi_0(\Omega_\Omega)$ (`B0-unlabel`). **$\psi_0(\Omega_\Omega+\Omega_2)$ 的遗传标签未得**: 它的闭包里符号的嵌套深度无界, 每一层都要上下文链.
> 6. **检验 3 不通过, 精确停在同一处 (§8).** $\psi_0(\Omega_\Omega\cdot2)$ 的外层链作为 `Ctx` 实例 `C2` (证书、支配、单调全部证出), 第 0 项带 `χ1-label`; 但 `C2-unlabel : ¬ Lab (Tᶜ C2) t2`, 路径与 Stage2 的 `Q′` 相同. **检验 4 未做** (§9 说明需要什么).
> 7. **缺的构造 (§10).** (i) 前缀栈折叠 $\psi^{P}$ (对 (前缀栈, 尾树) 字典序递归; 栈帧是 $\hat\Omega$ 或带 `Sim` 的树), 它把每个暴露的 $\Omega_\Omega$ 变成 `ŝ`/`ĉ` 闭包, 停机论证在 §10 给出但**未编译**; (ii) `Goodᶻ` 对 $\psi^P$ 的输出封闭 (Uniform 的推广, 要对 `ŝ`/`ĉ` 证观测单调性), 这是产生 `gc` 的五个字段的唯一途径; (iii) 记号侧: NF/Bnd/cofin 对唯一不可数下标 $\Omega$ 的推广 (并行任务). 有了 (i)(ii), 本文的 `Ctx`/`force` 原样就是计值层.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Symbolic where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Uniform using (Good; Good-add; Good-ψ⁰; Good-ψ; Good-Ω; Good→HS; ψ⁰-cong; ψ-cong; add-cong;
                                     Ω-monoᵒ; idO; zero-l; Uniform)
import OCF.Align.NoCumsum as N
import OCF.Align.EBO as E
open E using (T; cω; cΩ; cof; fsn; natT; Ωt) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; βᴱ)
open import OCF.Align.Label using (BTBO-label; Good-lift)
open import OCF.Align.Stage2 using (ℓ₀; lγ-HS; lγ⊑BTBO; one⊑; sq; walk; walkᵀ; Lab-walk; Lab0; sqLab; Lab-rep;
                                    ts; ts-fs; Ωᵗ; t2; K₀; K₀-refl; χ; χ1-label; Q′; diag2-fs; ctx; X₂; Rp)
```

## §1 EBO 侧: 符号尾与最小文法

记号沿用 Stage2: $\Omega=$ `Ωᵗ`, $\Omega_\Omega=$ `βᴱ`, `ctx y` $=\psi_0(\Omega_\Omega+y)$. 称参数 $b$ 有**符号尾**, 若它的末项是 $\Omega_\Omega$, 或末项是 $\psi_\delta(b')$ ($\delta\ne0$) 而 $b'$ 有符号尾. Stage2 的最小失败项 $\psi_0(\Omega_\Omega+\Omega_2)$ 沿 `Rp` 的前 3 步到达 $A=\psi_0(\Omega_\Omega+\psi_1(\Omega_\Omega))$, 它的参数有符号尾, 共尾度是 $\Omega_1$ (`cΩ []`): $\psi_1$ 穿透, 外层 $\psi_0$ 折叠. 第 $n$ 项是 $\psi_0(\Omega_\Omega+\psi_1(\Omega_{\eta_n}))$, $\eta_0=1$, $\eta_{m+1}=A[m]$: 被计值的是**最内层**那个 $\Omega_\Omega$, 计值用的是**外层** $\psi_0$ 的链.

```agda
ψ₁Ω̂ : T
ψ₁Ω̂ = ψᵗ (natT 1) βᴱ ∷ []

Aᵗ : T
Aᵗ = ctx ψ₁Ω̂

X₂ᵗ : T
X₂ᵗ = ctx (Ωt (natT 2))

X₂-at-A : walkᵀ X₂ᵗ (1 ∷ 0 ∷ 1 ∷ []) ≡ Aᵗ
X₂-at-A = refl

symb-cof : cof (ψᵗ Ωᵗ [] ∷ ψ₁Ω̂) ≡ cΩ []
symb-cof = refl

A-fs0 : fsn Aᵗ 0 ≡ ctx (ψᵗ (natT 1) (Ωt (natT 1)) ∷ [])
A-fs0 = refl

A-fs1 : fsn Aᵗ 1 ≡ ctx (ψᵗ (natT 1) (Ωt (fsn Aᵗ 0)) ∷ [])
A-fs1 = refl
```

`A-fs1` 的下标 `fsn Aᵗ 0` 就是链的上一点: 这是 Stage2 的 D3 在最外层做的事, 但这里发生在 $\psi_1$ 之下.

**嵌套与更高的前缀.** 从 $\psi_0(\Omega_\Omega\cdot2)$ 出发, 路径 $[1][0][1][0][0][3]$ 到 $\psi_0(\Omega_\Omega+\Omega_3)$, 再 $[1][1][0][2]$ 到一个项, 其中第 1 层的符号对象 $\psi_1(\Omega_\Omega+\psi_2(\Omega_\Omega)+\psi_2(\Omega_\Omega))$ 的参数里有第 2 层的符号对象 (模拟器搜索得到, 下面 `refl` 核对).

```agda
ψ₂Ω̂ : T
ψ₂Ω̂ = ψᵗ (natT 2) βᴱ ∷ []

X₃ᵗ : T
X₃ᵗ = ctx (Ωt (natT 3))

t2-to-X₃ : walkᵀ t2 (1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 3 ∷ []) ≡ X₃ᵗ
t2-to-X₃ = refl

N3 : T
N3 = ctx (ψᵗ (natT 2) (ψᵗ Ωᵗ [] ∷ ψᵗ (natT 1) (ψᵗ Ωᵗ [] ∷ ψ₂Ω̂ ++ ψ₂Ω̂) ∷ []) ∷ [])

N3-path : walkᵀ X₃ᵗ (1 ∷ 1 ∷ 0 ∷ 2 ∷ []) ≡ N3
N3-path = refl

N3-cof : cof (ψᵗ Ωᵗ [] ∷ ψ₂Ω̂ ++ ψ₂Ω̂) ≡ cΩ []
N3-cof = refl
```

**读法 (最小文法).** 闭包里出现的符号对象是: 参数层的 "前缀 $+\Omega_\Omega$" (前缀可以再含 $\Omega_\Omega$), 以及可数层 $\delta\ge1$ 上的 $\psi_\delta(\text{前缀}+\text{符号尾})$, 前缀里可以有**层号高于 $\delta$** 的对象 (`N3`: 层 1 的节点含层 2 的 $\psi_2(\Omega_\Omega)$). 只记下 $\delta$ 的无分支 `ψ̂ δ` 丢掉了前缀, 不同的项映到同一个节点, 不可能带遗传标签; 而把前缀存进节点又违反树族的层次 (§3). 第 0 层上还要一种节点: 外层 $\psi_0$ 对符号尾折叠后的 $\omega$-极限, 它的序列要等链算出来 (`ĉ`).

## §2 否定 (a): $\hat\Omega$ 不能是可数层的构造子

设 $\hat\Omega$ 是可数层树族 (每一层) 的构造子. 上下文计值把它变成 $\Omega_\eta$; $\Omega_{\eta'+1}$ 的分支遍历第 $\eta'$ 层的**全部**树, 其中就有 $\hat\Omega$ 本身 (提升进来). 于是 "计值 → 取分支 → 下降" 回到起点. 下面是两层的最小模型: `A` 是下一层 (含 `Ω̂ᴬ`), `B` 的 `Ωᴮ` 是分支遍历 `A` 的节点, `upᴮ` 是提升. 关系 `x ▹ y` 读作 "计算 $x$ 的折叠时要对 $y$ 递归".

```agda
module Toy where
  data A : Set where
    Ω̂ᴬ : A
    zᴬ  : A

  data B : Set where
    Ωᴮ  : (A → B) → B
    upᴮ : A → B

  data Node : Set where
    a : A → Node
    b : B → Node

  data _▹_ : Node → Node → Set where
    eval : a Ω̂ᴬ ▹ b (Ωᴮ upᴮ)
    br   : ∀ {f} x → b (Ωᴮ f) ▹ b (f x)
    dn   : ∀ {x} → b (upᴮ x) ▹ a x

  data Acc▹ (x : Node) : Set where
    acc : (∀ {y} → x ▹ y → Acc▹ y) → Acc▹ x

  loop : ¬ Acc▹ (a Ω̂ᴬ)
  loop (acc h) with h eval
  ... | acc h₁ with h₁ (br Ω̂ᴬ)
  ...   | acc h₂ = loop (h₂ dn)
```

**读法.** 三种步骤各自都是合法的折叠递归 (计值是上下文链的那一步, `br` 是 Level 的 `ψ` 对 `limᵢ` 分支的递归, `dn` 是透过 `up`), 合起来不良基. 语义上 $\Omega_\Omega$ 不是 $\Omega_{\eta'+1}$ 的分支值 (它不 $<\Omega_{\eta'+1}$), 但类型 `Ordᶜ η′` 不知道这一点. 结论: $\Omega_\Omega$ 只能出现在 $\psi$ 的**参数层**, 以前缀栈的形式 (§10), 不进入任何可数层. 可数层里能出现的符号对象只有 $\psi_\delta(\cdots)$ ($<\Omega_{\delta+1}$, 语义上是合法的第 $\delta$ 层元素).

## §3 否定 (b) 与新树族的声明

Level 的树族 `Ord₊ ℓ U` 对层号的结构前驱 (`i ◃ ℓ`) 解码 `U`; 层 $\delta$ 的节点只能存 $\triangleleft\delta$ 的层的树. §1 的 `N3` 要求层 1 的节点记住层 2 的前缀, 存不下. 剩下的唯一办法是不存前缀, 而存 "在 $\eta$ 处计值" 的**闭包**: 闭包捕获前缀, 但它是函数, 不是数据. 为了避开 D1 (对任意 $\eta$ 派发推出 WLPO), 闭包的定义域带公共上界的证据: $\{\eta\mid c\sqsubseteq^\mathsf I\eta\}$, $c$ 是上下文里一切可数下标的公共上界层号. 链的第 0 点 ($\eta=1$, 不受支配) 单独存为子树 $t_0$.

新族在 Level 的五个构造子之外加三个:

- `ŝ c t₀ g`: 层 $\ell$ 上的 $\Omega_1$-共尾符号对象 $\psi_\ell(\cdots)$, 第 0 点 $t_0$, 受支配的计值 $g$;
- `ĉᴸ c t₀ g o₀ o`: 外层 $\psi_0$ 对符号尾折叠后的 $\omega$-极限, 链在第 0 层 (`Z`), 输出在本层 (加法把前缀加到输出上而不碰链);
- `z0 w`: 第 0 层的待计值树 `Z` 嵌入 (只在层 0 有意义).

`Z` 是第 0 层的待计值树: 自然数构造子、旧族第 0 层树 `oldz`, 以及待计值的折叠 `ĉ` (链即输出). 它先于新族定义.

```agda
data Z : Set where
  zero : Z
  suc  : Z → Z
  lim  : (ℕ → Z) → Z
  oldz : Ordᶜ zero → Z
  ĉ    : (c : Ordᴵ) → Z → ((η : Ordᴵ) → c ⊑ᴵ η → Z) → Z

module _ (ℓ : Ordᴵ) (Uˢ : (i : Ordᴵ) → i ◃ ℓ → Set) where
  data Ord₊ˢ : Set where
    zero : Ord₊ˢ
    suc  : Ord₊ˢ → Ord₊ˢ
    lim  : (f : ℕ → Ord₊ˢ) → Ord₊ˢ
    limᵢ : ∀ {i} (p : i <ᴵ ℓ) (f : Uˢ i (<→◃ p) → Ord₊ˢ) → Ord₊ˢ
    up   : ∀ {k} (r : k ◃₁ ℓ) (x : Uˢ k (◃₁→◃ r)) → Ord₊ˢ
    z0   : Z → Ord₊ˢ
    ŝ    : (c : Ordᴵ) → Ord₊ˢ → ((η : Ordᴵ) → c ⊑ᴵ η → Ord₊ˢ) → Ord₊ˢ
    ĉᴸ   : (c : Ordᴵ) → Z → ((η : Ordᴵ) → c ⊑ᴵ η → Z) → Ord₊ˢ → ((η : Ordᴵ) → c ⊑ᴵ η → Ord₊ˢ) → Ord₊ˢ

Uˢ : ∀ {ℓ} (i : Ordᴵ) → i ◃ ℓ → Set
Uˢ i zero         = Ord₊ˢ i Uˢ
Uˢ i (suc r)      = Uˢ i r
Uˢ _ (self {f} n) = Ord₊ˢ (f n) Uˢ
Uˢ i (lim n r)    = Uˢ i r

Ordˢ : Ordᴵ → Set
Ordˢ ℓ = Ord₊ˢ ℓ Uˢ
```

严格正性与 `Uˢ` 的停机都照 Level 通过: 新构造子的分支只以 `Ord₊ˢ` 为值域, 定义域是先于族定义的 `Ordᴵ` 与 $\sqsubseteq^\mathsf I$. 有界三歧性 (`<ᴵ-dec`) 不动: 下标类型仍是 Level 的 `Ordᴵ`. 折叠 $\psi^P$ 在这个族上的定义见 §10 (未编译).

## §4 逐步现造的公共层号与上下文链

公共层号 `Mlev c η e` 以 $c$ 为第 0 项、$\eta$ 为其余各项, 步进证据就是支配证据 $e$. 上下文的可数部分经 `up (self 0)` 进入, 计值点 $\Omega_\eta$ 经 `λ q → lim 1 q` 进入; 二者在 `Mlev` 内被比较时, `<ᴵ-dec` 读的正是 $e$.

```agda
Fs : Ordᴵ → Ordᴵ → ℕ → Ordᴵ
Fs c η zero    = c
Fs c η (suc _) = η

Fst : ∀ {c η} → c ⊑ᴵ η → ∀ n → Fs c η n ⊑ᴵ Fs c η (suc n)
Fst e zero    = e
Fst e (suc n) = ⊑ᴵ-refl

Mlev : (c η : Ordᴵ) → c ⊑ᴵ η → Ordᴵ
Mlev c η e = lim (Fs c η) (Fst e)
```

上下文 `Ctx`: 支配界 $c$, 第 0 点 $t_0$ ($\eta=1$ 的计值), 受支配的计值 $E$, 以及五个证据: 证书 (`h₀`, `hE`), 支配 (`d₀`, `dE`: 计值结果的层号 $\sqsupseteq c$), 单调 (`m₀`, `mE`). 链点 `Pt` 携带树、证书与支配证据 `dx`; 下一点在 `toLevel` 处计值, 支配证据当场交给 `E`. 这是 Stage2 的 `St`/`step`/`Γ₂` 的一般化: 那里的 `ev : lim γ ⊑ χₖ` 就是这里 $c=\ell_0$ 时的 `dx` (经 `toLevel-⊑`).

```agda
record Ctx : Set where
  field
    c  : Ordᴵ
    t₀ : Ordᶜ zero
    E  : (η : Ordᴵ) → c ⊑ᴵ η → Ordᶜ zero
    h₀ : HS t₀
    hE : ∀ η e → HS (E η e)
    d₀ : c ⊑ᴵ toLevel t₀ h₀
    dE : ∀ η e → c ⊑ᴵ toLevel (E η e) (hE η e)
    m₀ : ∀ η e → t₀ ⊑⁰ E η e
    mE : ∀ η e η′ e′ → η ⊑ᴵ η′ → E η e ⊑⁰ E η′ e′

record Pt (C : Ctx) : Set where
  constructor pt
  field
    x  : Ordᶜ zero
    hx : HS x
    dx : Ctx.c C ⊑ᴵ toLevel x hx

module _ (C : Ctx) where
  open Ctx C

  lvP : Pt C → Ordᴵ
  lvP p = toLevel (Pt.x p) (Pt.hx p)

  stepP : Pt C → Pt C
  stepP p = pt (E (lvP p) (Pt.dx p)) (hE _ _) (dE _ _)

  Γᶜ : ℕ → Pt C
  Γᶜ = iter stepP (pt t₀ h₀ d₀)

  χᶜ : ℕ → Ordᶜ zero
  χᶜ n = Pt.x (Γᶜ n)

  Tᶜ : Ordᶜ zero
  Tᶜ = lim χᶜ

  χᶜ-step : ∀ n → χᶜ n ⊑⁰ χᶜ (suc n)
  χᶜ-step zero    = m₀ _ _
  χᶜ-step (suc n) = mE _ _ _ _ (toLevel-⊑ (Pt.hx (Γᶜ n)) (Pt.hx (Γᶜ (suc n))) (χᶜ-step n))

  Tᶜ-HS : HS Tᶜ
  Tᶜ-HS = hl (λ n → Pt.hx (Γᶜ n)) χᶜ-step

  Tᶜᴸ : Ordᴵ
  Tᶜᴸ = toLevel Tᶜ Tᶜ-HS

  Tᶜ-0 : χᶜ 0 ≡ t₀
  Tᶜ-0 = refl

  Tᶜ-suc : ∀ n → χᶜ (suc n) ≡ E (lvP (Γᶜ n)) (Pt.dx (Γᶜ n))
  Tᶜ-suc n = refl
```

**读法.** `Tᶜ-suc` 是 EBO 规则 6 ($\mu=0$) 的树侧: 第 $n+1$ 项是上下文在链的上一点处的计值, 下标是 `toLevel` 现造的层号. 链的证书 `Tᶜ-HS` 只用 `m₀`/`mE` 与 `toLevel-⊑`; 支配证据只在下一次计值时被 `E` 消费 (公共层号 `Mlev c η e` 的步进).

## §5 归纳-递归的证书: `Goodᶻ`, `force`, `force-HS`

待计值的第 0 层树 `Z` 的计值 `force` 需要链点的证书与支配证据, 而它们又是对 `force` 的结果的陈述. 所以 `Goodᶻ` 与 `force`/`force-HS` 归纳-递归地同时定义: `gc` 的字段提到 `force` 与 `force-HS` 在前面字段上的值. `force (ĉ …)` 就是 §4 的 `Tᶜ`, 上下文由字段组装.

```agda
data Goodᶻ : Z → Set
force    : (x : Z) → Goodᶻ x → Ordᶜ zero
force-HS : (x : Z) (G : Goodᶻ x) → HS (force x G)

data Goodᶻ where
  gz : Goodᶻ zero
  gs : ∀ {x} → Goodᶻ x → Goodᶻ (suc x)
  gl : ∀ {f : ℕ → Z} (G : ∀ n → Goodᶻ (f n)) →
       (∀ n → force (f n) (G n) ⊑⁰ force (f (suc n)) (G (suc n))) → Goodᶻ (lim f)
  go : ∀ {x} → HS x → Goodᶻ (oldz x)
  gc : ∀ {c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} (G₀ : Goodᶻ t₀) (Gg : ∀ η e → Goodᶻ (g η e)) →
       c ⊑ᴵ toLevel (force t₀ G₀) (force-HS t₀ G₀) →
       (∀ η e → c ⊑ᴵ toLevel (force (g η e) (Gg η e)) (force-HS (g η e) (Gg η e))) →
       (∀ η e → force t₀ G₀ ⊑⁰ force (g η e) (Gg η e)) →
       (∀ η e η′ e′ → η ⊑ᴵ η′ → force (g η e) (Gg η e) ⊑⁰ force (g η′ e′) (Gg η′ e′)) →
       Goodᶻ (ĉ c t₀ g)

force zero      gz          = zero
force (suc x)   (gs G)      = suc (force x G)
force (lim f)   (gl G st)   = lim (λ n → force (f n) (G n))
force (oldz x)  (go h)      = x
force (ĉ c t₀ g) (gc G₀ Gg d₀ dE m₀ mE) = Tᶜ (record
  { c = c ; t₀ = force t₀ G₀ ; E = λ η e → force (g η e) (Gg η e)
  ; h₀ = force-HS t₀ G₀ ; hE = λ η e → force-HS (g η e) (Gg η e)
  ; d₀ = d₀ ; dE = dE ; m₀ = m₀ ; mE = mE })

force-HS zero      gz        = hz
force-HS (suc x)   (gs G)    = hs (force-HS x G)
force-HS (lim f)   (gl G st) = hl (λ n → force-HS (f n) (G n)) st
force-HS (oldz x)  (go h)    = h
force-HS (ĉ c t₀ g) (gc G₀ Gg d₀ dE m₀ mE) = Tᶜ-HS (record
  { c = c ; t₀ = force t₀ G₀ ; E = λ η e → force (g η e) (Gg η e)
  ; h₀ = force-HS t₀ G₀ ; hE = λ η e → force-HS (g η e) (Gg η e)
  ; d₀ = d₀ ; dE = dE ; m₀ = m₀ ; mE = mE })
```

**读法.** 停机: `force` 对 `Z` 结构递归 (`g η e` 是 `ĉ c t₀ g` 的子项, 在 λ 之下传给 `Tᶜ`), 证书 `Goodᶻ` 只作伴随参数. 这正是 Stage2 §10 第 2、3 条要的形状: 计值时的公共上界 (`dE` 给出的 $c\sqsubseteq^\mathsf I$ 链点层号) 不是事先假定的, 而是由链点的证书逐步产生; `HS` 对计值结果是**定义**出来的 (`force-HS`), `Good→HS` 的推广在这一层是平凡的. 不平凡的部分全部移到了 "构造 `gc` 的五个字段" 上, 即 §10 (ii).

## §6 检验 1: $\psi_0(\Omega_\Omega)$, $\psi_0(\Omega_\Omega+1)$, $\psi_0(\Omega_\Omega+\Omega)$

只有一个 $\Omega_\Omega$ 的上下文 (空前缀): 第 0 点 $\psi^0(\Omega_1)$, 在 $\eta$ 处计值为 $\psi^0(\Omega_\eta)$, 支配界 $c=1$. 证书用 Uniform, 支配用 Stage2 的 `one⊑`, 单调用 Level 的 `Ψ⁰-mono`.

```agda
Cβ : Ctx
Cβ = record
  { c  = suc zero
  ; t₀ = ψ⁰ (Ω (suc zero))
  ; E  = λ η _ → ψ⁰ (Ω η)
  ; h₀ = Uniform (suc zero)
  ; hE = λ η _ → Uniform η
  ; d₀ = toLevel-⊑ (hs hz) (Uniform (suc zero)) (one⊑ {y = Ω (suc zero)})
  ; dE = λ η _ → toLevel-⊑ (hs hz) (Uniform η) (one⊑ {y = Ω η})
  ; m₀ = λ η e → Ψ⁰-mono e
  ; mE = λ η e η′ e′ h → Ψ⁰-mono h }

zβ : Z
zβ = ĉ (suc zero) (oldz (ψ⁰ (Ω (suc zero)))) (λ η _ → oldz (ψ⁰ (Ω η)))

Gβ : Goodᶻ zβ
Gβ = gc (go (Uniform _)) (λ η _ → go (Uniform η)) (Ctx.d₀ Cβ) (Ctx.dE Cβ) (Ctx.m₀ Cβ) (Ctx.mE Cβ)

force-zβ : force zβ Gβ ≡ Tᶜ Cβ
force-zβ = refl
```

链与 NoCumsum 的对角线逐点相同 (连证书都相同, 因为 `N.cert (n+1)` 就是 `Uniform (L n)`), 于是计值结果 $\cong$ `BTBOᴵ`, 遗传标签来自 Label 的 `BTBO-label`.

```agda
β-eq : ∀ n → (Pt.x (Γᶜ Cβ n) , Pt.hx (Γᶜ Cβ n)) ≡ N.D.Γ (suc n)
β-eq zero    = refl
β-eq (suc n) = cong N.D.next (β-eq n)

Tβ≅ : Tᶜ Cβ ≅ N.BTBOᴵ
Tβ≅ = l≅ (λ n → subst (λ p → Pt.x (Γᶜ Cβ n) ≅ proj₁ p) (β-eq n) (≅-refl⁰ _))

zβ-label : Lab (force zβ Gβ) (E.EBOψ 2)
zβ-label = Lab-≅ Tβ≅ BTBO-label

zβ1-label : Lab (lim (iter (force zβ Gβ +_) zero)) ts
zβ1-label = lω refl (l≅ (λ n → ≅-refl⁰ _)) (λ n → subst (Lab _) (sym (ts-fs n)) (Lab-rep zβ-label n))
```

$\psi_0(\Omega_\Omega+\Omega)$: 尾巴 $\Omega$ 是可数的普通节点, 规则 6 的链在第 0 层, 链点 $\psi_0(\Omega_\Omega+y)$ 的 $y$ 全是可数的; 前缀 $\Omega_\Omega$ 只在 $y$ 降到 0 时暴露, 而那时它在 $\psi_0$ 之下, 计值就是上面的 `zβ`. 所以在这个片段上静态前缀 $\Omega_{\ell_0}$ 与符号前缀应给出同一棵树 (模 $\cong$, 经 `Tβ≅` 与 `ψ⁰ (Ω ℓ₀) ≡ BTBOᴵ`; 纸面论证, 符号版的树要 §10 的 $\psi^P$ 才能写出), Stage2 的 `Ctx₀`/`χ1-label` 原样适用:

```agda
χ1-label-reused : Lab (χ 1) _
χ1-label-reused = χ1-label
```

`χ1-label` 是 Stage2 的定理, 不是重新证的; 这里只记录它在符号读法下仍是检验 1 的第三项.

## §7 检验 2: Stage2 的失败点与它的下一层

**$A=\psi_0(\Omega_\Omega+\psi_1(\Omega_\Omega))$ 的上下文链.** 支配界取 $c=\ell_0$ (前缀 $\Omega_{\ell_0}$ 的层号; 它的字面子项里有 $0$ 与 $1$: `z<ℓ₀`, `o<ℓ₀`, 由计算核对). 在 $\eta$ 处的计值: 公共层号 `Mlev ℓ₀ η e`, 前缀 `up (self 0) (Ω ℓ₀)`, 尾巴 $\psi_1(\Omega_\eta)$ (目标证明 `lim 0 o<ℓ₀`, $\Omega_\eta$ 经 `λ q → lim 1 q` 进入). 第 0 点在 $\ell_0$ 上: $\psi_0(\Omega_\Omega+\psi_1(\Omega_1))$. 这里外层前缀仍是静态的 $\Omega_{\ell_0}$: 它在 $A$ 的闭包里只在 $\psi_0$ 之下暴露, 那时静态与符号一致 (§6; 纸面论证, 未编译).

```agda
z<ℓ₀ : zero <ᴵ ℓ₀
z<ℓ₀ = lim 0 zero

o<ℓ₀ : suc zero <ᴵ ℓ₀
o<ℓ₀ = lim 1 (lim 0 (lim 2 zero))

σ1 : ∀ {L} → zero <ᴵ L → Simᴵ (suc zero) L
σ1 z zero    = z
σ1 z (suc ())

1⊑ℓ₀ : suc zero ⊑ᴵ ℓ₀
1⊑ℓ₀ = s⊑ z≅ z<ℓ₀

PA : ∀ η e → Ordᶜ (Mlev ℓ₀ η e)
PA η e = up (self 0) (Ω ℓ₀)

YA : ∀ η e → Ordᶜ (suc zero)
YA η e = ψ {ℓ = Mlev ℓ₀ η e} (lim 0 o<ℓ₀) (λ q → lim 1 q) (Ω η)

argA : ∀ η e → Ordᶜ (Mlev ℓ₀ η e)
argA η e = add (PA η e) (σ1 (lim 0 z<ℓ₀)) (YA η e)

Y₀A : Ordᶜ (suc zero)
Y₀A = ψ {ℓ = ℓ₀} o<ℓ₀ (σ1 z<ℓ₀) (Ω (suc zero))

arg₀A : Ordᶜ ℓ₀
arg₀A = add (Ω ℓ₀) (σ1 z<ℓ₀) Y₀A
```

五个证据. 证书来自 Uniform 的 `Good` 封闭性; 支配 $\ell_0\sqsubseteq^\mathsf I$ 计值的层号, 经 `toLevel-⊑` 归结为树上的 $\lim\gamma\sqsubseteq\mathtt{BTBO}^\mathsf I\sqsubseteq\psi^0(P\oplus Y)$, 后一步是 Stage2 `pre` 的一般形式 `pre⁰` (只用 Uniform 的 `zero-l` 与同余); 单调来自 `Ω-monoᵒ` 与同余.

```agda
pre⁰ : ∀ {k L} {a : Ordᶜ L} {σ : Simᴵ k L} {Y : Ordᶜ k} → a ≅ a → Y ≅ Y → ψ⁰ a ⊑⁰ ψ⁰ (add a σ Y)
pre⁰ {k} {a = a} {σ = σ} {Y = Y} ea eY = ψ⁰-cong {x = add a σ (𝟎 {k})} {y = add a σ Y} (add-cong ea (zero-l eY)) idO

ePA : ∀ η e → PA η e ≅ PA η e
ePA η e = upˡ (upʳ (Ω-refl ℓ₀))

eYA : ∀ η e → YA η e ≅ YA η e
eYA η e = ψ-≅ {p = lim 0 o<ℓ₀} {σ = λ q → lim 1 q} {p′ = lim 0 o<ℓ₀} {σ′ = λ q → lim 1 q} (≅ᴵ-refl _) (Ω-refl η)

eY₀A : Y₀A ≅ Y₀A
eY₀A = ψ-≅ {p = o<ℓ₀} {σ = σ1 z<ℓ₀} {p′ = o<ℓ₀} {σ′ = σ1 z<ℓ₀} (≅ᴵ-refl _) (Ω-refl (suc zero))

hEA : ∀ η e → HS (ψ⁰ (argA η e))
hEA η e = Good→HS (Good-ψ⁰ (Good-add (Good-lift (self 0) (Good-Ω ℓ₀)) (ePA η e) (Good-ψ (Good-Ω η) (Ω-refl η)))
                           (add-≅ {σ = σ1 (lim 0 z<ℓ₀)} {σ′ = σ1 (lim 0 z<ℓ₀)} (ePA η e) (eYA η e)))

h₀A : HS (ψ⁰ arg₀A)
h₀A = Good→HS (Good-ψ⁰ {x = arg₀A}
                 (Good-add {σ = σ1 z<ℓ₀} (Good-Ω ℓ₀) (Ω-refl ℓ₀)
                           (Good-ψ {p = o<ℓ₀} {σ = σ1 z<ℓ₀} (Good-Ω (suc zero)) (Ω-refl (suc zero))))
                 (add-≅ {σ = σ1 z<ℓ₀} {σ′ = σ1 z<ℓ₀} (Ω-refl ℓ₀) eY₀A))

CA : Ctx
CA = record
  { c  = ℓ₀
  ; t₀ = ψ⁰ arg₀A
  ; E  = λ η e → ψ⁰ (argA η e)
  ; h₀ = h₀A
  ; hE = hEA
  ; d₀ = toLevel-⊑ lγ-HS h₀A (⊑-trans lγ⊑BTBO (pre⁰ {σ = σ1 z<ℓ₀} (Ω-refl ℓ₀) eY₀A))
  ; dE = λ η e → toLevel-⊑ lγ-HS (hEA η e) (⊑-trans lγ⊑BTBO (pre⁰ {σ = σ1 (lim 0 z<ℓ₀)} (ePA η e) (eYA η e)))
  ; m₀ = λ η e → ψ⁰-cong {x = arg₀A} {y = argA η e}
                   (add-cong (upʳ (Ω-refl ℓ₀))
                     (ψ-cong {p = o<ℓ₀} {p′ = lim 0 o<ℓ₀} {σ = σ1 z<ℓ₀} {σ′ = λ q → lim 1 q}
                             {x = Ω (suc zero)} {y = Ω η} (Ω-monoᵒ (⊑ᴵ-trans 1⊑ℓ₀ e)))) idO
  ; mE = λ η e η′ e′ h → ψ⁰-cong {x = argA η e} {y = argA η′ e′}
                   (add-cong (upˡ (upʳ (Ω-refl ℓ₀)))
                     (ψ-cong {p = lim 0 o<ℓ₀} {p′ = lim 0 o<ℓ₀} {σ = λ q → lim 1 q} {σ′ = λ q → lim 1 q}
                             {x = Ω η} {y = Ω η′} (Ω-monoᵒ h))) idO }

TA : Ordᶜ zero
TA = Tᶜ CA
```

**Stage2 的失败点修好了.** Stage2 的 $\psi_0(\Omega_\Omega+\Omega_2)$ 树沿 `Rp` 走 10 步到 $0$; 前 3 步到 $A$ (`X₂-at-A`), 余下 7 步 $[1][0][0][0][0][0][0]$. 在 `TA` 上, 同样 7 步到达 `BTBOᴵ` (字面相等), 记号侧到达 $\psi_0(\Omega_\Omega)$; 终点带遗传标签. 外层一步: 第 0 项是 $\psi_0(\Omega_\Omega+\psi_1(\Omega_1))$, 第 1 项的下标是第 0 项现造的层号, 与 `A-fs0`/`A-fs1` 逐项同形.

```agda
RpA : List ℕ
RpA = 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

_ : Rp ≡ (1 ∷ 0 ∷ 1 ∷ []) ++ RpA
_ = refl

_ : walk X₂ Rp ≡ zero
_ = refl

A-repaired : walk TA RpA ≡ N.BTBOᴵ
A-repaired = refl

A-end : walkᵀ Aᵗ RpA ≡ E.EBOψ 2
A-end = refl

A-end-label : Lab (walk TA RpA) (walkᵀ Aᵗ RpA)
A-end-label = BTBO-label

A-shape0 : sq TA 0 ≡ ψ⁰ arg₀A
A-shape0 = refl

A-shape1 : sq TA 1 ≡ ψ⁰ (argA (toLevel (ψ⁰ arg₀A) h₀A) (Ctx.d₀ CA))
A-shape1 = refl
```

**失败下移一层.** 只计值最外层 $\Omega_\Omega$ 的树, 在深一层的 $B=\psi_0(\Omega_\Omega+\psi_1(\Omega_\Omega+\psi_1(\Omega_\Omega)))$ 处重演 Stage2 的失败: 不论外层链怎样造, $B$ 的第 0 项都是 "内层 $\Omega_\Omega$ 静态" 的树 $\psi^0(\Omega_{\ell_0}\oplus\psi_1(\Omega_{\ell_0}\oplus\psi_1(\Omega_1)))$, 它沿 $[0][0]$ 到达 $A$ 的静态版本, 再沿 `RpA` 到 $0$; 记号侧全程 $\omega$-共尾, 终点 $\psi_0(\Omega_\Omega)$.

```agda
Bᵗ : T
Bᵗ = ctx (ψᵗ (natT 1) (ψᵗ Ωᵗ [] ∷ ψ₁Ω̂) ∷ [])

B0t : Ordᶜ zero
B0t = ψ⁰ (add (Ω ℓ₀) (σ1 z<ℓ₀) (ψ {ℓ = ℓ₀} o<ℓ₀ (λ q → q) (add (Ω ℓ₀) (σ1 z<ℓ₀) Y₀A)))

PB : List ℕ
PB = 0 ∷ 0 ∷ RpA

X₂-at-B : walkᵀ X₂ᵗ (2 ∷ 0 ∷ 1 ∷ []) ≡ Bᵗ
X₂-at-B = refl

_ : walkᵀ (fsn Bᵗ 0) (0 ∷ 0 ∷ []) ≡ Aᵗ
_ = refl

_ : walk B0t PB ≡ zero
_ = refl

B0-unlabel : ¬ Lab B0t (fsn Bᵗ 0)
B0-unlabel l = Lab0 (Lab-walk PB l (refl , refl , refl , refl , refl , refl , refl , refl , refl , tt)) refl
```

**读法.** 外层的上下文链 (以及 §5 的 `force`) 计值的只是**一个** $\Omega_\Omega$; 链点 $\psi_0(C[\eta])$ 里其余的 $\Omega_\Omega$ 仍要在它们各自暴露时, 由**那时**的外层链计值. `A-repaired` 与 `B0-unlabel` 一起说明: 每多计值一层, 失败就下移一层; $\psi_0(\Omega_\Omega+\Omega_2)$ 的闭包里嵌套深度无界 ($A$ 与 $B$ 都在 `X₂` 的闭包中: `X₂-at-A`, `X₂-at-B`), 所以它的遗传标签要求计值在折叠**内部**发生, 即 §10 的 $\psi^P$. **检验 2 的结论: 未得 $\psi_0(\Omega_\Omega+\Omega_2)$ 的遗传标签; Stage2 的最小失败点已修复, 新的最小失败点是 $B$ 的第 0 项沿 `PB`.**

## §8 检验 3: $\psi_0(\Omega_\Omega\cdot2)$

外层链作为 `Ctx` 实例: 支配界 $\ell_0$, 第 0 点 Stage2 的 $\chi_1=\psi^0(K_0)$, 在 $\eta$ 处计值 $\psi^0(\Omega_{\ell_0}\oplus\Omega_\eta)$ (层号 `Mlev ℓ₀ η e`). 证据与 §7 同法.

```agda
arg2 : ∀ η e → Ordᶜ (Mlev ℓ₀ η e)
arg2 η e = add (PA η e) (λ q → lim 1 q) (Ω η)

h2 : ∀ η e → HS (ψ⁰ (arg2 η e))
h2 η e = Good→HS (Good-ψ⁰ (Good-add (Good-lift (self 0) (Good-Ω ℓ₀)) (ePA η e) (Good-Ω η))
                          (add-≅ {σ = λ q → lim 1 q} {σ′ = λ q → lim 1 q} (ePA η e) (Ω-refl η)))

h2₀ : HS (ψ⁰ K₀)
h2₀ = Good→HS (Good-ψ⁰ (Good-add (Good-Ω ℓ₀) (Ω-refl ℓ₀) (Good-Ω (suc zero))) K₀-refl)

C2 : Ctx
C2 = record
  { c  = ℓ₀
  ; t₀ = ψ⁰ K₀
  ; E  = λ η e → ψ⁰ (arg2 η e)
  ; h₀ = h2₀
  ; hE = h2
  ; d₀ = toLevel-⊑ lγ-HS h2₀ (⊑-trans lγ⊑BTBO (pre⁰ {σ = λ q → lim 0 q} (Ω-refl ℓ₀) (Ω-refl (suc zero))))
  ; dE = λ η e → toLevel-⊑ lγ-HS (h2 η e) (⊑-trans lγ⊑BTBO (pre⁰ {σ = λ q → lim 1 q} (ePA η e) (Ω-refl η)))
  ; m₀ = λ η e → ψ⁰-cong {x = K₀} {y = arg2 η e} (add-cong (upʳ (Ω-refl ℓ₀)) (Ω-monoᵒ (⊑ᴵ-trans 1⊑ℓ₀ e))) idO
  ; mE = λ η e η′ e′ h → ψ⁰-cong {x = arg2 η e} {y = arg2 η′ e′} (add-cong (upˡ (upʳ (Ω-refl ℓ₀))) (Ω-monoᵒ h)) idO }

T2 : Ordᶜ zero
T2 = Tᶜ C2

T2-0 : Lab (sq T2 0) (fsn t2 0)
T2-0 = subst (Lab _) (sym (diag2-fs 0)) χ1-label

_ : walk (sq T2 1) Q′ ≡ zero
_ = refl

C2-unlabel : ¬ Lab T2 t2
C2-unlabel l = Lab0 (Lab-walk Q′ (subst (Lab _) (diag2-fs 1) (sqLab l refl 1))
                      (refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl ,
                       refl , refl , refl , refl , refl , refl , tt)) refl
```

**读法.** `C2` 就是 Stage2 的 `Γ₂`/`T₂` 写成一般的上下文链 (公共层号由支配证据现造, 不再需要专门的 `Bseq`/`BH`/`Bst`), 结论也相同: 外层一步与第 0 项的遗传标签成立 (`T2-0`), 第 1 项沿 `Q′` 在 17 步后树为 $0$ (`C2-unlabel`). 那条路径经过的项是 $\psi_0(\Omega_\Omega+\psi_\delta(\Omega_\Omega))$ ($\delta$ 是 `BTBOᴵ` 的层号, Stage2 §9), 与 §7 的 $A$ 同一种暴露. **检验 3 不通过**; 缺的是同一件东西 (§10 (i)(ii)).

## §9 检验 4: $\psi_0(\Omega_{\Omega+1})$ 的一步形状与它需要什么

记号侧 (Stage2 §4 的 `tO`): $\Omega_{\Omega+1}$ 正规, 规则 6 的链在**不可数**层 $\Omega$ 上: $\zeta_0=\Omega_\Omega$, $\zeta_{k+1}=\psi_\Omega(\zeta_k)$. 第 1 项 $\psi_0(\psi_\Omega(\Omega_\Omega))$ 的参数又是符号尾 (共尾度 $\Omega_1$: $\psi_\Omega$ 对 $\Omega_\Omega$ 穿透, 因为 $1\le\Omega$).

```agda
tO : T
tO = ψᵗ [] (Ωt (E.sucT Ωᵗ)) ∷ []

tO-fs0 : fsn tO 0 ≡ E.EBOψ 2
tO-fs0 = refl

tO-fs1 : fsn tO 1 ≡ ψᵗ [] (ψᵗ Ωᵗ βᴱ ∷ []) ∷ []
tO-fs1 = refl

tO-fs2 : fsn tO 2 ≡ ψᵗ [] (ψᵗ Ωᵗ (ψᵗ Ωᵗ βᴱ ∷ []) ∷ []) ∷ []
tO-fs2 = refl

ψΩΩ̂-cof : cof (ψᵗ Ωᵗ βᴱ ∷ []) ≡ cΩ []
ψΩΩ̂-cof = refl
```

树侧的第 0 项就是 `zβ` (`tO-fs0`, §6). 从第 1 项起, 链点 $\zeta_k$ 是**参数层**的符号对象 ($\Omega_\Omega\le\zeta_k<\Omega_{\Omega+1}$), 不属于任何可数层 (§2 的论证同样适用). 于是一个符号的 $\psi_0(\Omega_{\Omega+1})$ 需要:

1. 参数层的文法里多一种栈帧 "$\psi_\Omega(\cdot)$" (折叠到不可数目标层 $\Omega$), 它对符号尾总是穿透 (`ψΩΩ̂-cof`: $\mu=0$, $1\le\Omega$), 对可数尾巴按规则 4/5ω/6 计算, 规则 6 的链在尾巴自己的可数层上 (与 $\psi^P$ 相同);
2. 一个以**参数层对象**为链点的 $\omega$-极限: 第 $n$ 项是 $\psi^{P}$ 作用于栈 $\zeta_n$ (空尾巴). 链点 $\zeta_{k+1}=\psi_\Omega(\zeta_k)$ 是越来越大的栈, 不是 $\psi_0(\Omega_{\Omega+1})$ 的结构子项, 所以这个极限不能写成 $\psi^P$ 自己的一个子句 (停机检查会拒绝对 $\zeta_n$ 的递归调用); 它必须是 $\psi^P$ 之后定义的第三层函数 (对 $n$ 递归, 每项调用已定义好的 $\psi^P$), 或者用记号侧的良基性 (`<ᵀ` 在 NF 上的 `Acc`, Standard 未做) 驱动.
3. 链点 $\zeta_k$ 本身不需要层号 (它不被当作下标比较), 所以这一层**不需要**支配证据, 只需要 `Goodᶻ` 式的步进证书 ($\psi_0(\zeta_k)\sqsubseteq^0\psi_0(\zeta_{k+1})$).

本文只给出上面的一步形状 (`tO-fs0/1/2`, 第 0 项与 `zβ` 的对应); 第 1 项起的树侧对象依赖 §10 (i), 未构造.

## §10 缺的构造

**(i) 前缀栈折叠 $\psi^P$ (设计, 未编译).** 栈帧 `Frame ℓ` 两种: `fΩ̂ : zero <ᴵ ℓ → Frame ℓ` (一个 $\Omega_\Omega$ 被加数; 证据 $0<^\mathsf I\ell$ 让第 0 点 $a+\Omega_1$ 留在层 $\ell$), `fT : Ordˢ k → Simᴵ k ℓ → Frame ℓ` (可数层的树前缀). 栈 `Vec (Frame ℓ) n` 以长度 $n$ 为下标. $\psi^P_p\,\sigma\,y$ 表示 $\psi_i(P+y)$:

- 尾巴 $y$ 的 `zero`/`suc`/`lim`/`limᵢ`/`up` 子句照 Level 的 `ψ` (前缀 $P$ 原样携带, `add` 的作用被吸收); 规则 6 的链在节点层 $j$ 上, 链点用空栈的 $\psi^{[]}$;
- 尾巴 `zero`, 栈顶 `fT x σ′`: 弹栈, 对 $x$ 继续 ($n$ 下降, 尾巴任意);
- 尾巴 `zero`, 栈顶 `fΩ̂ z`: 弹栈, 产生闭包. 目标层 $i\ne0$ 时 `ŝ ℓ t₀ g`, $t_0=\psi^{P'}(\Omega_1)$, $g\,\eta\,e=\psi^{P'\uparrow}_{\texttt{lim 0}\,p}(\Omega_\eta)$, 其中 $P'\uparrow$ 是把剩余栈经 `self 0` 提升到 `Mlev ℓ η e` (长度不变); 目标层 $0$ 时 `z0 (ĉ ℓ …)`;
- 尾巴 `ŝ c t₀ g`: 逐点推进 (`ŝ c (ψ^P t₀) (λ η e → ψ^P (g η e))`, 目标层 0 时改为 `ĉ`), 不需要新的公共层号;
- 尾巴 `ĉᴸ`/`z0`: 输出逐点推进, 链不动.

停机度量是 ($n$, 尾巴) 的字典序: 弹栈时 $n$ 下降而尾巴可以是全新的树 ($\Omega_\eta$, $\Omega_1$, 前缀 $x$), 其余调用 $n$ 不变而尾巴是结构子项 (或 `g η e`). 栈用 `List` 时停机检查器看不出 $P'\uparrow$ 不比 $P$ 长 (它是 `map`), 所以要以长度为下标. 这正是 §2 的反面: $\Omega_\Omega$ 在栈里而不在可数层里, "计值" 一步总伴随着栈变短. 还需要: `tr`/`tr⁻`/`res` 对 `ŝ`/`ĉᴸ`/`z0` 的子句 (逐点), `Ω`/`lift`/`into`/`out` 照抄.

**(ii) `Goodᶻ` 对 $\psi^P$ 的输出封闭 (未做).** §5 把一切不平凡的东西集中到 `gc` 的五个字段. 对 $\psi^P$ 产生的 `ĉ`, 它们是:

- `dE`: 上下文里的可数下标 (支配界 $c$) $\sqsubseteq^\mathsf I$ 链点的层号. 树侧对每个实例都经 `pre⁰` 与 `lγ⊑BTBO` 证出 (§7, §8); 一般情形要一条 "$\psi^0(P+y)\sqsupseteq\psi^0(P)\sqsupseteq c$ 的树" 的引理, 前半是 `pre⁰` 在新族上的版本, 后半要求上下文的可数下标都 $\le$ 第 0 点, 即**交替不变量**: 被比较的下标在下标层有公共上界, 而这个上界就是链点.
- `mE`/`m₀`: 计值关于 $\eta$ 单调. 在新族上要把 Uniform 的观测前序 $\sqsubseteq^\mathsf o$ 推广到 `ŝ`/`ĉᴸ`/`z0` (它们对观测逐点交换, 与 `lim` 同类), 以及 `Ω-monoᵒ` 跨不同的 `Mlev ℓ η e` (目标证明 `lim 0 p` 与 `Sim` 不同, Uniform 的 `ψ-cong` 已经允许).
- `hE`/`h₀`: 在 `Goodᶻ` 里由 `force-HS` 定义性地给出, 只要递归地有 `Goodᶻ`.

有了 (i)(ii), $\psi_0(\Omega_\Omega+\Omega_2)$ 的树是 `force (ψ⁰^{[fΩ̂ z]} (Ω 2)) G`, 本文的 `A-repaired` 与 `B0-unlabel` 的路径会在嵌套的每一层都由 `ĉ` 计值.

**(iii) 记号侧 (并行任务) 与合并接口.** 本文用到的记号侧事实全部是 EBO 的 `fsn`/`cof`/`walkᵀ` 在具体项上的 `refl`: `X₂-at-A`, `X₂-at-B`, `symb-cof`, `A-fs0`, `A-fs1`, `t2-to-X₃`, `N3-path`, `N3-cof`, `A-end`, `tO-fs0/1/2`, `ψΩΩ̂-cof`, 以及 Stage2 的 `diag2-fs`, `ts-fs`, `Q′` 路径. 合并时树侧需要记号侧提供 (本文未证, 列为假设):

- (H1) **符号尾的刻画**: NF 项 $b$ 的共尾度为 $\Omega_1$ 且来自 $\Omega_\Omega$ (末项是 $\Omega_\Omega$ 或 $\psi_\delta(b')$, $\delta\ge1$, $b'$ 有符号尾) 时, 对一切 $\delta\ge1$ 穿透, 只在 $\psi_0$ 处折叠 ($\mu=0$, 链 $\gamma_0=1$); `symb-cof`/`N3-cof`/`ψΩΩ̂-cof` 是它的实例.
- (H2) **交替不变量的记号版**: NF 的 $\psi_0(C[\Omega_\Omega])$ (符号尾) 中, $C$ 的每个可数下标 $v$ 满足 $v<\psi_0(C[1])$. 这是 `dE`/`d₀` 的记号侧对应 (链从第 1 点起支配上下文).
- (H3) **共尾性 (Standard 的 `cofin`/`Cof6` 在 $\mu=0$、符号尾时的版本)**: NF 的 $v<\psi_0(C[\Omega_\Omega])$ 推出 $v<\psi_0(C[\zeta_n])$ 对某个链点 $\zeta_n$. 它是 Label 的 `Next` 在新阶段给出 `Slt`/`Seq` 所需.
- (H4) $\psi_0(\Omega_{\Omega+1})$ 需要的 $\psi_\Omega$ 栈帧的 NF 条件 (`Bnd` 对目标层 $\Omega$).

## §11 对比表

| | Stage2 D3 | 本文: 上下文链 `Ctx` + `Goodᶻ`/`force` | 完整设计 ($\psi^P$ + `Goodᶻ` 封闭) |
|---|---|---|---|
| $\Omega_\Omega$ 的表示 | 静态前缀 $\Omega_{\ell_0}$, 只有最外层交给链 | 待计值节点 `ĉ` (第 0 层) / `ŝ` (第 $\delta$ 层) 的闭包, 定义域 $\{\eta\mid c\sqsubseteq^\mathsf I\eta\}$ | 参数层前缀栈的 `fΩ̂` 帧, 暴露时由 $\psi^P$ 变成闭包 |
| 能否作可数层构造子 | — | 否: `loop` (计值+取分支+下降成环) | 否 (同左), 只在栈里 |
| 公共层号 | 专门的 `M s` (`Bseq`/`BH`/`Bst`) | `Mlev c η e`, 步进证据 = 支配证据 | 同左 |
| 有界三歧性 | 不受影响 | 不受影响 (派发只在 `Mlev` 内) | 同左 |
| 证书 | 链外手工 (`St`) | 归纳-递归 `Goodᶻ`/`force`/`force-HS`, `force (ĉ…) ≡ Tᶜ…` | 需 `Goodᶻ` 对 $\psi^P$ 输出封闭 (未做) |
| 检验 1 ($\psi_0(\Omega_\Omega)$, $+1$, $+\Omega$) | `ts-label`, `χ1-label` | `force-zβ` (`refl`), `Tβ≅`, `zβ-label`, `zβ1-label`, `χ1-label` | 同左 |
| 检验 2 ($\psi_0(\Omega_\Omega+\Omega_2)$) | `X₂-unlabel` (10 步) | 失败点 $A$ 修复 (`A-repaired`, `A-end-label`), 下移到 $B$ (`B0-unlabel`, 9 步) | 预期通过, 未构造 |
| 检验 3 ($\psi_0(\Omega_\Omega\cdot2)$) | `stage2-unlabel` | `C2` (证据齐全), `T2-0`, `C2-unlabel` | 预期通过, 未构造 |
| 检验 4 ($\psi_0(\Omega_{\Omega+1})$) | `naiveO-unlabel` | 一步形状 `tO-fs0/1/2`, 第 0 项 = `zβ` | 还需参数层链 (§9) |

## §12 结论与边界

**字面成立 (`refl`):** 记号侧 `X₂-at-A`, `X₂-at-B`, `symb-cof`, `A-fs0`, `A-fs1`, `t2-to-X₃`, `N3-path`, `N3-cof`, `A-end`, `tO-fs0/1/2`, `ψΩΩ̂-cof`; 树侧 `Tᶜ-0`, `Tᶜ-suc` (上下文链的规则 6 形状), `force-zβ` (`force zβ Gβ ≡ Tᶜ Cβ`), `A-repaired` (`walk TA RpA ≡ BTBOᴵ`), `A-shape0`, `A-shape1`, `walk B0t PB ≡ zero`, `walk (sq T2 1) Q′ ≡ zero`, `walk X₂ Rp ≡ zero` (Stage2 的失败, 复核).

**定理 (模 $\cong$, 标签按 Correspond 的 `Lab`):**

1. 否定 (a): `Toy.loop : ¬ Acc▹ (a Ω̂ᴬ)` (可数层里的 $\hat\Omega$ 让折叠的递归不良基).
2. 新族 `Ordˢ` (含 `ŝ`, `ĉᴸ`, `z0`) 与第 0 层待计值树 `Z` 的声明 (严格正, `Uˢ` 停机).
3. 上下文链: `Ctx`, `Mlev`, `Γᶜ`, `Tᶜ`, `χᶜ-step`, `Tᶜ-HS`, `Tᶜᴸ` (可回灌); 一般的 `pre⁰`.
4. 归纳-递归的证书 `Goodᶻ`/`force`/`force-HS`.
5. 检验 1: `Cβ`, `zβ`, `Gβ`, `β-eq`, `Tβ≅ : Tᶜ Cβ ≅ BTBOᴵ`, `zβ-label` ($\psi_0(\Omega_\Omega)$), `zβ1-label` ($\psi_0(\Omega_\Omega+1)$); $\psi_0(\Omega_\Omega+\Omega)$ 沿用 Stage2 `χ1-label`.
6. 检验 2: `CA` (五个证据齐全), `TA`, `A-end-label`; 否定 `B0-unlabel`.
7. 检验 3: `C2`, `T2-0`; 否定 `C2-unlabel : ¬ Lab T2 t2`.

**边界.**

- **$\psi_0(\Omega_\Omega+\Omega_2)$ 与 $\psi_0(\Omega_\Omega\cdot2)$ 的遗传标签都未得.** 精确的停点: 检验 2 是 $B=\psi_0(\Omega_\Omega+\psi_1(\Omega_\Omega+\psi_1(\Omega_\Omega)))$ 的第 0 项沿 `PB` $=[0][0][1][0]^6$ (`X₂` 沿 $[2][0][1]$ 到 $B$); 检验 3 是 `T2` 的第 1 项沿 Stage2 的 `Q′`. 缺的成分: §10 (i) 前缀栈折叠 $\psi^P$ (设计与停机论证在纸面, 未编译) 与 (ii) `Goodᶻ` 对其输出的封闭性 (Uniform 的推广), 以及 (iii) 记号侧的 (H1)–(H3).
- 新族 `Ordˢ` 的折叠没有写 (只有声明); 本文所有树都是**旧族**的树, 由 `Ctx` 在外面组装, `Z` 只用 `oldz` 叶子. `force` 对一般的 `Z` 有定义, 但目前唯一产生 `ĉ` 的是手写的 `zβ`.
- `ŝ`/`ĉ` 有分支函数. 这偏离了 "无分支构造子" 的字面要求; 理由是 §2–§3 的两个否定 (无分支的 $\hat\Omega$ 在可数层里使递归不良基; 无分支的 $\hat\psi_\delta$ 丢失更高层的前缀). D1 的 `dec→WLPO` 不适用, 因为分支的定义域带支配证据, 一切比较都在 `Mlev c η e` 之内; 这是元层的论证, 未编译.
- `Tβ≅` 只到 $\cong$ (链的证书与 NoCumsum 的证书字面相同, 但 `lim` 的逐点相等要函数外延性).
- §1 "最小文法" 的结论来自模拟器搜索 (深度 $\le 10$, 下标 $\le 3$) 加 `refl` 核对具体项, 不是对闭包的完全刻画.
- 不改 `src/`、`archive/` 与已有的 Align 文件, README 未改.
