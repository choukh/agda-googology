# 累积树族: 让层间提升成为定义性的

> 接 [Certified](Certified.lagda.md) §5、§10、§11. 那里的障碍是: BTBO 的树族 (经 Cumsum 的模块 `W` 换成 $\sqsubseteq$-步进的下标 `Ordʷ`) 里, $\Omega$ 在极限层的第 $n$ 项是 $\uparrow_{\mathtt{lim}\,n}\Omega_{f\,n}$, 递归的 `↑` 把证明 `lim n` 写进被提升子树的每个 `limᵢ` 节点; 结构前驱包含 $\sqsubseteq$ 是字面的, 于是相邻两项不 $\sqsubseteq$-相关 (`Ω-not-step`, `Ωε₀-not-step`), 带证书的对角线停在 $x_2=\varepsilon_0$. 本文寻找一个树族, 让**提升是定义性的** (不遍历子树、不把层号证明写进节点), 使这个障碍消失, 层号不借助 `cumsum` 也能认证.
>
> 结论先说:
>
> 1. **内涵性障碍有两层.** (i) 提升把证明写进 `limᵢ` 节点 (Certified §5); (ii) 第 0 层的闭包: 折叠的规则 6 链和提升函数留在 `lim` 的闭包里, 字面 $\sqsubseteq$ 要求两个闭包定义性相等 (Certified §10 第 2 条). 只让提升成为定义性的 (方向 A) 去掉了 (i) 的来源, 但 $\psi$ 的输出仍然带证明 (穿透时 `<ʷ-dec` 算出的 $j<i$, 以及沿提升累积的 `Sim` 证据). 要让两层都不再起作用, 还需要第二个改动: 结构关系的叶子从字面相等换成**跨层结构互模拟** $\cong$ (对证明不敏感、对函数逐点、透过提升节点). $\cong$ 是 [FiniteAll](FiniteAll.lagda.md) §3 的跨层 PER 加两条提升规则, 不是值的外延相等, 所以不触及有界三歧性 (壁垒定理 [Barrier](../Barrier.lagda.md)).
> 2. **方向 C 全部被拒绝 (§1, 记录了确切错误).** 全局树加层号谓词不严格正; 无关的、形状无关的、擦除的证明都不能出现在 `limᵢ` 定义域的类型里; `Prop` 值的 $<$ 不能用来递归定义定义域. 更根本的一点: `<ʷ-dec` 从证明 `lim n p` 里**读出** $n$ 来决定比较的方向, 所以 $<$ 的证明相关性是有界三歧性的原料, 不能擦掉. 能做的只有两件事: 让提升不再复制证明, 让关系忽略证明.
> 3. **方向 B (和类型) 退化为 A (§2).** 后继层上 `old : O₀ → O₁` 就是定义性提升; 但要让表示唯一, 必须判定 "$\lim f$ 的各项是否全是旧树", 这推出 LPO (`canon→LPO`, 已编译). 不要求唯一时, 同一棵树有多个表示, 只能由关系识别, 这正是 A 的做法; 极限层的 $(n,x)$ 表示就是 A 的 `up (self n) x`.
> 4. **候选 A 编译通过 (§3–§6).** 树族 `Ordᶜ` 多一个构造子 `up`, 按层号的**直接结构前驱** (后继层 `suc k` 的 `zero`、极限层 `lim f s` 的 `self n`) 嵌入较低层的树. $\Omega$ 的两处提升各是一个节点; 任意结构距离的提升是 `up` 链, 只对层号证明递归, 从不遍历树 (`lift`). 下标类型、有界三歧性原样沿用 `W`. 折叠 `ψ` 带一个累积的 `Sim` 证据, 遇到 `up` 就把提升并入证据继续, 不需要比较目标层与提升节点的层 (那个比较对 $\sqsubseteq$-步进的层号不可判定, §3). 不同提升路径在 $\cong$ 下双向相关 (`lift-coh`, `lift-comp`); 折叠尊重 $\cong$, 与用哪个证明、经哪条提升路径无关 (`ψ-≅`).
> 5. **决定性检验, 前两步通过.** Certified 的 `Ωε₀-not-step` 在这里翻转为 `Ωε₀-step`; 一般地 $a\sqsubseteq^\mathsf{w}b\Rightarrow\Omega_a\sqsubseteq\Omega_b$ (`Ω-mono`, 任意层号). $x_3=\psi_0(\Omega_{\varepsilon_0})$ 的顶层序列是步进的, 一般定理是 $a\sqsubseteq^\mathsf{w}b\Rightarrow\psi_i(\Omega_a)\sqsubseteq\psi_i(\Omega_b)$ (`Ψ-mono`, 任意目标层、任意折叠证据). 目标层为 0 时折叠不需要任何证明 (没有比 0 小的层可比), 写成 `ψ⁰` 后 $x_3$ 的顶层步进对 Certified 的**字面** $\sqsubseteq$ 也成立 (`x₃-literal-step`). 这一条只有定义性提升才给得出: `ψ⁰ (up r x) = ψ⁰ x`, 而在 `W` 里 $\psi_0(\uparrow x)$ 要遍历 $\uparrow x$, 读到的是改写过的证明.
> 6. **没有做到的.** $x_3$ 的**遗传**步进与它的层号证书. $x_3$ 内部的序列分四类: $\psi(\Omega_a)$ 型 (已证)、规则 4 (已证, `rule4⁰`)、第 0 层的 $\gamma$-链 (已证, `Ω₁-chain-step`)、第 $\ge1$ 层的 $\gamma$-链 (未证). 最后一类就是 Cumsum/Certified 留下的安全路径引理 (规则 6 的链在 $\sqsubseteq$ 下递增). 在 $\cong$ 版本里它已不受内涵性阻挡, 是纯数学的缺口; 但 $\psi$ 在这个族上仍不 $\sqsubseteq$-单调 (`ψ-not-⊑mono`, 与 Certified 同一个反例), 所以 "生成对角线的运算保持步进" 这样的一般定理不成立.
>
> 按任务的四条标准: 1 (`--safe --without-K`、严格正、FGH 结构递归) 成立; 2 (提升定义性且路径一致) 成立; 3 (有界三歧性、忠实折叠的规则 4/5ω/5Ω/6) 成立; 4 部分成立: Certified 第一个失败的情形 (`Ωε₀-not-step`) 与 $x_3$ 的顶层序列已证, 遗传步进与证书未证. 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示; 下标与 $\varepsilon_0^\mathsf{w}$ 从 Cumsum 的 `W` 与 Certified 导入.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Cumulative where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; subst; subst₂; trans)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Barrier using (LPO)
open import OCF.Align.Cumsum using (module W)
open W using (Ordʷ; zero; suc; lim; _<ʷ_; _⊑ʷ_; z⊑; s⊑; l⊑; <ʷ-dec; <ʷ-trans; Simʷ)
open import OCF.Align.Certified using (<ʷ-irrefl; γᴺ; γᴺ-step; ε₀ʷ; z<ε₀ʷ)
```

## §0 问题的精确形式

Certified 证明了两件事. 其一 (§5): 在 `W` 的树族里, $\Omega_\omega$ 的第 2、3 项之间没有 $\sqsubseteq$, 理由是第 $n$ 项的每个 `limᵢ` 前驱都带标签 $n+1$ (`tag-↑`), 而 $\sqsubseteq$ 在后继上要求前驱**字面**相等 (`⊑-literal`). 其二 (§10 第 2 条, 未编译): 即使不看树上的节点, 第 0 层的树 $\psi_p(T'_n)$ 的子树也是闭包, 闭包里存着 `limS n` 与 $\psi_q$ 的证明 $q$; 字面 $\sqsubseteq$ 要求闭包定义性相等, 而它们只是逐点外延相等.

所以一个 "累积树族" 要回答两个问题:

- 层间提升能否不改写子树? 这消去 (i) 的来源;
- 结构关系能否不比较证明与闭包, 同时仍是结构的 (从而不碰有界三歧性)? 这处理 (ii), 也处理折叠在输出里新写入的证明.

任务给出的四条标准:

1. `--safe --without-K`, 严格正, 无公设与编译指示; 第 0 层的 FGH 是结构递归.
2. 提升是定义性的, 或者是单个构造子; 有一个跨层结构关系, 同一棵树经不同提升路径得到的结果在它之下双向相关.
3. 下标类型 (可数层号) 上的有界三歧性仍成立, 忠实折叠 $\psi^\mathsf{E}$ 的规则 4、5ω、5Ω、6 (规则 6 的链经直接折叠到共尾层) 可以定义.
4. 决定性检验: $x_3=\psi_0(\Omega_{\varepsilon_0})$ 的层号不借助 `cumsum` 而得到认证, 即 $x_3$ 内部的序列都是 $\sqsubseteq$-步进的 (Certified 第一个失败的情形); 最好是 "生成对角线的运算保持步进" 的一般定理.

## §1 方向 C: 擦掉证明 (全部被拒)

四个实验写在临时文件里, 只依赖 `W`, 下面给出关键声明与 Agda 2.8 的确切报错.

**C1 全局树加层号谓词.** 只有一个树类型, 层号是谓词, `limᵢ` 的定义域是 "层号为 $j$ 的树":

    data Tree where
      ...
      limᵢ : (j : Lv) → (Σ Tree (λ x → HasLv x j) → Tree) → Tree

报错 `[NotStrictlyPositive] Tree is not strictly positive, because it occurs in the third argument of Σ to the left of an arrow in the type of the constructor limᵢ` (同时 `HasLv` 也不严格正). 这是本质的: 定义域必须是**先于**当前层定义好的类型, 所以只能由某种对层号 (或其证明) 的递归计算出来, 即 BTBO 的归纳-递归写法. 层号作为下标不可避免.

**C2 无关证明.** `limᵢ : ∀ {i} .(p : i <ʷ ℓ) (f : Ord< i p → Ord₊) → Ord₊`: 报错 `[VariableIsIrrelevant] Variable p is declared irrelevant, so it cannot be used here`. 形状无关 `..(p : i <ʷ ℓ)` 需要 `--experimental-irrelevance`, `--safe` 拒绝该选项 (`[SafeFlagPragma]`); 去掉 `--safe` 后仍是同一个 `VariableIsIrrelevant`, 因为 `Ord<` 的参数本身是相关的.

**C3 擦除证明.** `--erasure` 下 `limᵢ : ∀ {i} (@0 p : i <ʷ ℓ) (f : Ord< i p → Ord₊) → Ord₊`: 报错 `[UnusableAtModality] ... is not usable at the required modality @ω`. 即使被接受也无济于事: `@0` 只是运行时擦除, 定义性相等照样比较 $p$.

**C4 `Prop` 值的序.** `_<ᵖ_ : Ordᵖ → Ordᵖ → Prop` 有定义性的证明无关性, 但 `Ord< i zero = …` 这样对证明分情况立即报错 `[SplitInProp] Cannot split on datatype in Prop unless target is in Prop`. 更根本的是有界三歧性本身: `<ʷ-dec` 在 `lim`/`lim` 情况读出两个证明里的 $n,m$ 来比较, 这是从证明里取数据; 证明一旦定义性无关, 三歧性就只能落在 `Prop` 里, 不能再用来派发折叠.

**小结.** 层号证明必须是相关的数据, 并且必须出现在定义域的计算里. 能改的是: (a) 提升不再复制证明; (b) 关系不比较证明.

## §2 方向 B: 和类型累积

把 "第 $n+1$ 层的树要么是第 $n$ 层的树, 要么是新树" 直接写成类型. 第 1 层只需一个新构造子 `old`, 提升就是 `old` 本身, 定义性且唯一. 问题在 `lim`: 旧树的极限可以写成 `old (lim g)`, 也可以写成 `lim (old ∘ g)`, 两者是不同的项 (`two-reps`). 要选出规范代表, 就得判定一个序列是否 "全旧"; 而这个判定推出 LPO (`canon→LPO`: 把 $\alpha\,k$ 编码成第 $k$ 项是否是新树).

```agda
module B where
  data O₀ : Set where
    zero : O₀
    suc  : O₀ → O₀
    lim  : (ℕ → O₀) → O₀

  data O₁ : Set where
    old  : O₀ → O₁
    suc  : O₁ → O₁
    lim  : (ℕ → O₁) → O₁
    limᵢ : (O₀ → O₁) → O₁

  nat₀ : ℕ → O₀
  nat₀ zero    = zero
  nat₀ (suc n) = suc (nat₀ n)

  two-reps : old (lim nat₀) ≢ lim (old ∘ nat₀)
  two-reps ()

  IsOld : O₁ → Set
  IsOld (old _)  = ⊤
  IsOld (suc _)  = ⊥
  IsOld (lim _)  = ⊥
  IsOld (limᵢ _) = ⊥

  Canon : Set
  Canon = (f : ℕ → O₁) → (∀ n → IsOld (f n)) ⊎ (Σ[ n ∈ ℕ ] ¬ IsOld (f n))

  pick : Bool → O₁
  pick true  = limᵢ (λ _ → old zero)
  pick false = old zero

  old→false : ∀ b → IsOld (pick b) → b ≡ false
  old→false false _ = refl
  old→false true  ()

  new→true : ∀ b → ¬ IsOld (pick b) → b ≡ true
  new→true true  _ = refl
  new→true false h = ⊥-elim (h tt)

  canon→LPO : Canon → LPO
  canon→LPO c α with c (pick ∘ α)
  ... | inj₁ all     = inj₂ (λ k → old→false (α k) (all k))
  ... | inj₂ (k , h) = inj₁ (k , new→true (α k) h)
```

推广到全部层: 极限层的和类型是 $(\Sigma n.\,O(f\,n))\uplus\mathrm{New}$, 同样有 $(n,x)$ 与 $(n+1,\mathtt{old}\,x)$ 两个表示. "取最小的 $n$" 对构造子分情况可以判定 ($x$ 是否形如 `old y`), 但它不给出唯一性, 因为 $x$ 可以是 `lim (old ∘ g)` 这种 "实际上是旧的" 新树, 判定它又是 LPO. 而且第 $n+1$ 层的新树要能含第 $j<n$ 层的 `limᵢ` 节点 (加法 $a+\lim_j f=\lim_j(a+f)$ 会造出它们), 所以 New 必须能访问全部较低层, 结构上就回到 BTBO 的归纳-递归族, 再加上一个嵌入构造子. 这正是方向 A. 结论: **B 的可用形式就是 A; B 承诺的唯一表示需要 LPO.**

## §3 方向 A: 提升作为构造子

**为什么嵌入关系不是 `<ʷ`.** 在 `Ordʷ` 上, `lim f s` 的证据只是 $f\,n\sqsubseteq^\mathsf{w}f(n+1)$ (非严格), $f\,n<^\mathsf{w}\lim f$ 一般不成立 (常值列是合法的极限). `W` 的 $\Omega$ 因此用 `Sim` 证据 `lim n` 提升, 而不是一个证明 $f\,n<\ell$. 所以嵌入要用**结构子项**关系 $\triangleleft$: 它比 `<ʷ` 多一个构造子 `self n : f n ◃ lim f s`. `limᵢ` 仍用 `<ʷ` (被折叠的层必须严格在下面), `up` 只用直接前驱 $\triangleleft_1$ (`zero : a ◃₁ suc a` 与 `self n`).

```agda
infix 4 _◃_ _◃₁_

data _◃_ : Ordʷ → Ordʷ → Set where
  zero : ∀ {a} → a ◃ suc a
  suc  : ∀ {a b} → a ◃ b → a ◃ suc b
  self : ∀ {f : ℕ → Ordʷ} {s : ∀ n → f n ⊑ʷ f (suc n)} n → f n ◃ lim f s
  lim  : ∀ {a} {f : ℕ → Ordʷ} {s : ∀ n → f n ⊑ʷ f (suc n)} n → a ◃ f n → a ◃ lim f s

data _◃₁_ : Ordʷ → Ordʷ → Set where
  zero : ∀ {a} → a ◃₁ suc a
  self : ∀ {f : ℕ → Ordʷ} {s : ∀ n → f n ⊑ʷ f (suc n)} n → f n ◃₁ lim f s

<→◃ : ∀ {a b} → a <ʷ b → a ◃ b
<→◃ zero      = zero
<→◃ (suc p)   = suc (<→◃ p)
<→◃ (lim n p) = lim n (<→◃ p)

◃₁→◃ : ∀ {a b} → a ◃₁ b → a ◃ b
◃₁→◃ zero     = zero
◃₁→◃ (self n) = self n

◃₁→Sim : ∀ {a b} → a ◃₁ b → Simʷ a b
◃₁→Sim zero     q = suc q
◃₁→Sim (self n) q = lim n q
```

**树族.** 归纳-递归参数 `U` 按 $\triangleleft$ 的证明索引, `limᵢ` 的定义域是 `U i (<→◃ p)`, `up` 的内容是 `U k (◃₁→◃ r)`. `U` 对证明递归; 停机检查器看到隐式层号从 `suc i` 降到 `i`, 从 `lim f s` 降到 `f n`. `into`/`out` 也对证明递归, 每一步都是恒等, 所以 `out-into` 每步都是 `refl`; 它们取代了 BTBO 基于 `subst` 的 `coe`. 对闭的证明, `into r x` 定义性地就是 `x`.

`lift r` 沿 $r$ 的每个结构步放一个 `up` 节点, 只对 $r$ 递归, 从不碰 $x$.

```agda
module _ (ℓ : Ordʷ) (U : (i : Ordʷ) → i ◃ ℓ → Set) where
  data Ord₊ : Set where
    zero : Ord₊
    suc  : Ord₊ → Ord₊
    lim  : (f : ℕ → Ord₊) → Ord₊
    limᵢ : ∀ {i} (p : i <ʷ ℓ) (f : U i (<→◃ p) → Ord₊) → Ord₊
    up   : ∀ {k} (r : k ◃₁ ℓ) (x : U k (◃₁→◃ r)) → Ord₊

U : ∀ {ℓ} (i : Ordʷ) → i ◃ ℓ → Set
U i zero         = Ord₊ i U
U i (suc r)      = U i r
U _ (self {f} n) = Ord₊ (f n) U
U i (lim n r)    = U i r

Ordᶜ : Ordʷ → Set
Ordᶜ ℓ = Ord₊ ℓ U

out : ∀ {i ℓ} (r : i ◃ ℓ) → U i r → Ordᶜ i
out zero      x = x
out (suc r)   x = out r x
out (self n)  x = x
out (lim n r) x = out r x

into : ∀ {i ℓ} (r : i ◃ ℓ) → Ordᶜ i → U i r
into zero      x = x
into (suc r)   x = into r x
into (self n)  x = x
into (lim n r) x = into r x

out-into : ∀ {i ℓ} (r : i ◃ ℓ) (x : Ordᶜ i) → out r (into r x) ≡ x
out-into zero      x = refl
out-into (suc r)   x = out-into r x
out-into (self n)  x = refl
out-into (lim n r) x = out-into r x

coe : ∀ {i ℓ₁ ℓ₂} (r : i ◃ ℓ₁) (r′ : i ◃ ℓ₂) → U i r → U i r′
coe r r′ x = into r′ (out r x)

lift : ∀ {k ℓ} → k ◃ ℓ → Ordᶜ k → Ordᶜ ℓ
lift zero      x = up zero x
lift (suc r)   x = up zero (lift r x)
lift (self n)  x = up (self n) x
lift (lim n r) x = up (self n) (lift r x)
```

**$\Omega$ 与加法.** $\Omega_{\mathrm{suc}\,\ell}$ 的分支是 `up zero`, $\Omega_{\lim f}$ 的第 $n$ 项是 `up (self n) (Ω (f n))`: 两处提升都是一个节点. 加法的右加数若是提升节点, 必须遍历它 (结果在高层, 不是任何低层树的提升), 所以 `add` 带一个 `Sim` 证据, 把途经的提升记下来.

```agda
Ω : (ℓ : Ordʷ) → Ordᶜ ℓ
Ω zero      = suc zero
Ω (suc ℓ)   = limᵢ zero (up zero)
Ω (lim f s) = lim (λ n → up (self n) (Ω (f n)))

add : ∀ {k ℓ} → Ordᶜ ℓ → Simʷ k ℓ → Ordᶜ k → Ordᶜ ℓ
add a σ zero              = a
add a σ (suc b)           = suc (add a σ b)
add a σ (lim f)           = lim (λ n → add a σ (f n))
add a σ (limᵢ q f)        = limᵢ (σ q) (λ y → add a σ (f (coe (<→◃ (σ q)) (<→◃ q) y)))
add a σ (up zero x)       = add a (λ q → σ (suc q)) x
add a σ (up (self n) x)   = add a (λ q → σ (lim n q)) x

infixl 6 _+_
_+_ : ∀ {ℓ} → Ordᶜ ℓ → Ordᶜ ℓ → Ordᶜ ℓ
a + b = add a (λ q → q) b
```

**折叠.** `ψ p σ x` 的意思是 "把较低层的树 $x$ 经 `σ : Sim k ℓ` 看成第 $\ell$ 层的树, 再用 $p:i<\ell$ 折叠", 即 $\psi_p(\uparrow_\sigma x)$, 但不构造 $\uparrow_\sigma x$. 规则与 `W` 的 `ψʷ` 相同: 规则 4 (`suc`)、5ω (`lim`)、5Ω (`limᵢ`, $j<i$, 穿透)、6 ($i\le j$, $\gamma$-链经直接折叠 `ψ q` 到共尾层 $j$, 起点 $\Omega_j$). `limᵢ` 的派发比较的是 `σ q : j <ʷ ℓ` 与 `p : i <ʷ ℓ`, 两者有共同上界, 有界三歧性 `<ʷ-dec` 直接适用. 遇到 `up` 就把它并入 `σ`.

这样做是必要的, 不只是方便. 另一种写法是在 `up r x` 处比较目标层 $i$ 与 $x$ 的层 $k$, 决定是继续折叠 $x$ (若 $i<k$) 还是整体穿透 (若 $k\le i$). 但 $k=f\,n$ 而 $p=\mathtt{lim}\,m\,p'$、$m>n$ 时, 我们只知道 $i<f\,m$ 与 $f\,n\sqsubseteq^\mathsf{w}f\,m$; 若 $f\,n$ 是极限, 判定 $i<f\,n$ 要在 $f\,n$ 的基本列里无界搜索. 并入 `σ` 后只比较 `limᵢ` 的下标, 而它们都严格在 $\ell$ 之下.

```agda
ψ : ∀ {i k ℓ} → i <ʷ ℓ → Simʷ k ℓ → Ordᶜ k → Ordᶜ i
ψ p σ zero    = Ω _
ψ p σ (suc a) = lim (iter (ψ p σ a +_) zero)
ψ p σ (lim f) = lim (λ n → ψ p σ (f n))
ψ p σ (limᵢ {i = j} q f) with <ʷ-dec (σ q) p
... | injᵃ j<i = limᵢ j<i (λ y → ψ p σ (f (coe (<→◃ j<i) (<→◃ q) y)))
... | injᵇ _   = lim (λ n → ψ p σ (f (into (<→◃ q) (iter (λ x → ψ q (λ r → r) (f (into (<→◃ q) x))) (Ω j) n))))
... | injᶜ _   = lim (λ n → ψ p σ (f (into (<→◃ q) (iter (λ x → ψ q (λ r → r) (f (into (<→◃ q) x))) (Ω j) n))))
ψ p σ (up zero x)     = ψ p (λ q → σ (suc q)) x
ψ p σ (up (self n) x) = ψ p (λ q → σ (lim n q)) x
```

**FGH.** 第 0 层没有 `limᵢ` (没有 $j<^\mathsf{w}0$), 也没有 `up` (没有 $k\triangleleft_1 0$), 两个情况都是荒谬模式, 其余是结构递归. **标准 1 成立.**

```agda
FGH : Ordᶜ zero → ℕ → ℕ
FGH zero        n = suc n
FGH (suc a)     n = iter (FGH a) n n
FGH (lim f)     n = FGH (f n) n
FGH (limᵢ () f) n
FGH (up () x)   n
```

**单节点的任意距离提升.** 也可以让 `up` 接受任意 `r : k ◃ ℓ`, 于是任意距离的提升都是一个节点. 数据类型照样被接受; 但内容的类型 `U k r` 只有在 $r$ 已知时才归约成 `Ordᶜ k`, 朴素的递归 `size (up r x) = size (out r x)` 被拒: `[TerminationIssue] Termination checking failed for the following functions: size. Problematic calls: size (out r x)`. 修复是给每个函数配一个先对 $r$ 递归的辅助函数 (`sizeU zero x = size x`, `sizeU (suc r) x = sizeU r x`, …), 这样编译通过 (临时文件 `A3`). 每个关系也要相应的归纳-递归参数. 本文取直接前驱版: $\Omega$ 只用直接前驱, 每个函数的 `up` 情况只有两条子句, 定义性地展开.

## §4 跨层结构互模拟 $\cong$ 与提升的一致性

$\cong$ 是 FiniteAll §3 的异层 PER, 改动三处: 下标是 `Ordʷ`; `limᵢ` 的强条件用 `into` 取分支; 加上两条提升规则 `upˡ`/`upʳ` ("提升节点与它的内容相关"). 较低层的关系 `R` 对 $\triangleleft$ 的证明递归定义, 停机理由与 `U` 相同. 它对 `limᵢ` 节点里的证明不敏感 (两边只要求同一个下标 $j$), 对 `lim` 逐点 (不需要函数外延性), 对提升透明.

```agda
module _ (ℓ : Ordʷ) (R : (i : Ordʷ) (r : i ◃ ℓ) → U i r → ∀ {ℓ′} → Ordᶜ ℓ′ → Set) where
  data Eq₊ : ∀ {ℓ′} → Ordᶜ ℓ → Ordᶜ ℓ′ → Set where
    z≅  : ∀ {ℓ′} → Eq₊ {ℓ′} zero zero
    s≅  : ∀ {ℓ′} {a : Ordᶜ ℓ} {b : Ordᶜ ℓ′} → Eq₊ a b → Eq₊ (suc a) (suc b)
    l≅  : ∀ {ℓ′} {f : ℕ → Ordᶜ ℓ} {g : ℕ → Ordᶜ ℓ′} → (∀ n → Eq₊ (f n) (g n)) → Eq₊ (lim f) (lim g)
    lᵢ≅ : ∀ {ℓ′ j} {p : j <ʷ ℓ} {q : j <ʷ ℓ′} {f : U j (<→◃ p) → Ordᶜ ℓ} {g : U j (<→◃ q) → Ordᶜ ℓ′} →
          (∀ (x y : Ordᶜ j) → R j (<→◃ p) (into (<→◃ p) x) y → Eq₊ (f (into (<→◃ p) x)) (g (into (<→◃ q) y))) →
          Eq₊ (limᵢ p f) (limᵢ q g)
    upˡ : ∀ {ℓ′ k} {r : k ◃₁ ℓ} {x : U k (◃₁→◃ r)} {b : Ordᶜ ℓ′} → R k (◃₁→◃ r) x b → Eq₊ (up r x) b
    upʳ : ∀ {ℓ′ k} {r : k ◃₁ ℓ′} {y : U k (◃₁→◃ r)} {a : Ordᶜ ℓ} → Eq₊ a (out (◃₁→◃ r) y) → Eq₊ a (up r y)

R : ∀ {ℓ} (i : Ordʷ) (r : i ◃ ℓ) → U i r → ∀ {ℓ′} → Ordᶜ ℓ′ → Set
R i zero         x b = Eq₊ i R x b
R i (suc r)      x b = R i r x b
R _ (self {f} n) x b = Eq₊ (f n) R x b
R i (lim n r)    x b = R i r x b

infix 4 _≅_
_≅_ : ∀ {ℓ₁ ℓ₂} → Ordᶜ ℓ₁ → Ordᶜ ℓ₂ → Set
_≅_ {ℓ₁} = Eq₊ ℓ₁ R
```

对称与传递对**一切**树成立, 与 FiniteAll 一样和对证明递归的 `R-flip`/`R-reflʳ` 互递归. 一个编译中的教训: `R-flip` 若同时对两个证明分情况, `self n` 对 `self m` 的情况报 `[SplitError.UnificationStuck] I'm not sure if there should be a case for the constructor self … f m ≟ f₁ n`; 只对第一个证明递归, 第二个用 `≅→R` 转换, 就避开了这个合一问题.

```agda
R→≅ : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) {x : Ordᶜ i} {b : Ordᶜ ℓ′} → R i r (into r x) b → x ≅ b
R→≅ zero      e = e
R→≅ (suc r)   e = R→≅ r e
R→≅ (self n)  e = e
R→≅ (lim n r) e = R→≅ r e

≅→R : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) {x : Ordᶜ i} {b : Ordᶜ ℓ′} → x ≅ b → R i r (into r x) b
≅→R zero      e = e
≅→R (suc r)   e = ≅→R r e
≅→R (self n)  e = e
≅→R (lim n r) e = ≅→R r e

≅-sym   : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≅ b → b ≅ a
R-flip  : ∀ {j ℓ₁ ℓ₂} (r : j ◃ ℓ₁) (r′ : j ◃ ℓ₂) {x y : Ordᶜ j} → R j r (into r x) y → R j r′ (into r′ y) x
≅-sym z≅      = z≅
≅-sym (s≅ e)  = s≅ (≅-sym e)
≅-sym (l≅ h)  = l≅ (λ n → ≅-sym (h n))
≅-sym (lᵢ≅ {p = p} {q = q} h) = lᵢ≅ (λ y x e → ≅-sym (h x y (R-flip (<→◃ q) (<→◃ p) e)))
≅-sym (upˡ {r = zero} e)    = upʳ (≅-sym e)
≅-sym (upˡ {r = self n} e)  = upʳ (≅-sym e)
≅-sym (upʳ {r = zero} e)    = upˡ (≅-sym e)
≅-sym (upʳ {r = self n} e)  = upˡ (≅-sym e)
R-flip zero      r′ e = ≅→R r′ (≅-sym e)
R-flip (suc r)   r′ e = R-flip r r′ e
R-flip (self n)  r′ e = ≅→R r′ (≅-sym e)
R-flip (lim n r) r′ e = R-flip r r′ e

≅-trans  : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} {c : Ordᶜ ℓ₃} → a ≅ b → b ≅ c → a ≅ c
R-reflʳ  : ∀ {j ℓ₁ ℓ₂} (r : j ◃ ℓ₁) (r′ : j ◃ ℓ₂) {x z : Ordᶜ j} → R j r (into r x) z → R j r′ (into r′ z) z
≅-trans (upˡ {r = zero} e)   d = upˡ (≅-trans e d)
≅-trans (upˡ {r = self n} e) d = upˡ (≅-trans e d)
≅-trans d (upʳ {r = zero} e)   = upʳ (≅-trans d e)
≅-trans d (upʳ {r = self n} e) = upʳ (≅-trans d e)
≅-trans (upʳ {r = zero} e)   (upˡ e′) = ≅-trans e e′
≅-trans (upʳ {r = self n} e) (upˡ e′) = ≅-trans e e′
≅-trans z≅     z≅      = z≅
≅-trans (s≅ e) (s≅ e′) = s≅ (≅-trans e e′)
≅-trans (l≅ h) (l≅ h′) = l≅ (λ n → ≅-trans (h n) (h′ n))
≅-trans (lᵢ≅ {p = p} {q = q} h) (lᵢ≅ h′) =
  lᵢ≅ (λ x z e → ≅-trans (h x z e) (h′ z z (R-reflʳ (<→◃ p) (<→◃ q) e)))
R-reflʳ zero      r′ e = ≅→R r′ (≅-trans (≅-sym e) e)
R-reflʳ (suc r)   r′ e = R-reflʳ r r′ e
R-reflʳ (self n)  r′ e = ≅→R r′ (≅-trans (≅-sym e) e)
R-reflʳ (lim n r) r′ e = R-reflʳ r r′ e

≅-reflˡ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≅ b → a ≅ a
≅-reflˡ e = ≅-trans e (≅-sym e)

≅-reflʳ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≅ b → b ≅ b
≅-reflʳ e = ≅-trans (≅-sym e) e

R-conv : ∀ {j ℓ₁ ℓ₂ ℓ′} (r : j ◃ ℓ₁) (r′ : j ◃ ℓ₂) {x : Ordᶜ j} {b : Ordᶜ ℓ′} → R j r (into r x) b → R j r′ (into r′ x) b
R-conv r r′ e = ≅→R r′ (R→≅ r e)
```

**提升的一致性 (标准 2).** 提升在 $\cong$ 下消失 (`lift-≅`); 于是同一棵树沿两条不同的提升路径得到的结果双向相关 (`lift-coh`, $\cong$ 对称), 先提升再提升与一次提升相关 (`lift-comp`). 这里不需要任何关于 `coe` 的引理: `upˡ`/`upʳ` 就是这条一致性本身. 对比 FiniteAll, 那里的 `↑ˡ` 要对树归纳, 并在每个 `limᵢ` 处用 `coe-coe₀` 改写.

```agda
lift-≅ : ∀ {k ℓ ℓ′} (r : k ◃ ℓ) {x : Ordᶜ k} {b : Ordᶜ ℓ′} → x ≅ b → lift r x ≅ b
lift-≅ zero      e = upˡ e
lift-≅ (suc r)   e = upˡ (lift-≅ r e)
lift-≅ (self n)  e = upˡ e
lift-≅ (lim n r) e = upˡ (lift-≅ r e)

≅-lift : ∀ {k ℓ ℓ′} (r : k ◃ ℓ) {a : Ordᶜ ℓ′} {x : Ordᶜ k} → a ≅ x → a ≅ lift r x
≅-lift r e = ≅-sym (lift-≅ r (≅-sym e))

lift-coh : ∀ {k ℓ₁ ℓ₂} (r : k ◃ ℓ₁) (r′ : k ◃ ℓ₂) {x : Ordᶜ k} → x ≅ x → lift r x ≅ lift r′ x
lift-coh r r′ e = lift-≅ r (≅-lift r′ e)

lift-comp : ∀ {k m ℓ ℓ′} (r : k ◃ m) (r′ : m ◃ ℓ) (r″ : k ◃ ℓ′) {x : Ordᶜ k} → x ≅ x →
            lift r′ (lift r x) ≅ lift r″ x
lift-comp r r′ r″ e = lift-≅ r′ (lift-≅ r (≅-lift r″ e))

Ω-refl : ∀ ℓ → Ω ℓ ≅ Ω ℓ
Ω-refl zero      = s≅ z≅
Ω-refl (suc ℓ)   = lᵢ≅ (λ x y e → upˡ (upʳ e))
Ω-refl (lim f s) = l≅ (λ n → upˡ (upʳ (Ω-refl (f n))))
```

## §5 折叠尊重 $\cong$

$a\cong b\Rightarrow\psi_p\,\sigma\,a\cong\psi_{p'}\,\sigma'\,b$, 只要目标层相同; $p,p',\sigma,\sigma'$ 任意. 证明与 FiniteAll 的 `ψᴱ-≈` 同构: `limᵢ` 处对两边的 `<ʷ-dec` 同时分情况, 一边穿透一边折叠的组合由无自反 (`<ʷ-irrefl`) 排除; 两边都折叠时两条 $\gamma$-链逐项相关 (`iter-R`). 新增的只有提升情况, 每个都是一行. 取 $a=b$ 而 $\sigma\ne\sigma'$, 就是 "经不同提升路径折叠, 结果相关". 这一条在 FiniteAll 里要靠 `↑ˡ` 与 `ψᴱ-≈` 组合才得到.

```agda
iter-R : ∀ {A B : Set} (Rel : A → B → Set) {G : A → A} {G′ : B → B} →
         (∀ {x y} → Rel x y → Rel (G x) (G′ y)) → ∀ {x y} → Rel x y → ∀ n → Rel (iter G x n) (iter G′ y n)
iter-R Rel h e zero    = e
iter-R Rel h e (suc n) = h (iter-R Rel h e n)

add-≅ : ∀ {k₁ ℓ₁ k₂ ℓ₂} {σ : Simʷ k₁ ℓ₁} {σ′ : Simʷ k₂ ℓ₂} {a : Ordᶜ ℓ₁} {a′ : Ordᶜ ℓ₂} {b : Ordᶜ k₁} {b′ : Ordᶜ k₂} →
        a ≅ a′ → b ≅ b′ → add a σ b ≅ add a′ σ′ b′
add-≅ ea z≅     = ea
add-≅ ea (s≅ e) = s≅ (add-≅ ea e)
add-≅ ea (l≅ h) = l≅ (λ n → add-≅ ea (h n))
add-≅ ea (upˡ {r = zero} e)   = add-≅ ea e
add-≅ ea (upˡ {r = self n} e) = add-≅ ea e
add-≅ ea (upʳ {r = zero} e)   = add-≅ ea e
add-≅ ea (upʳ {r = self n} e) = add-≅ ea e
add-≅ {σ = σ} {σ′ = σ′} {a = a} {a′ = a′} ea (lᵢ≅ {p = q} {q = q′} {f = f} {g = g} h) = lᵢ≅ λ x y e →
  subst₂ (λ u v → add a σ (f (into (<→◃ q) u)) ≅ add a′ σ′ (g (into (<→◃ q′) v)))
         (sym (out-into (<→◃ (σ q)) x)) (sym (out-into (<→◃ (σ′ q′)) y))
         (add-≅ ea (h x y (R-conv (<→◃ (σ q)) (<→◃ q) e)))

ψ-≅ : ∀ {i k₁ ℓ₁ k₂ ℓ₂} {p : i <ʷ ℓ₁} {σ : Simʷ k₁ ℓ₁} {p′ : i <ʷ ℓ₂} {σ′ : Simʷ k₂ ℓ₂}
      {a : Ordᶜ k₁} {b : Ordᶜ k₂} → a ≅ b → ψ p σ a ≅ ψ p′ σ′ b
ψ-≅ {i} z≅ = Ω-refl i
ψ-≅ (s≅ e) = l≅ (iter-R _≅_ (λ e′ → add-≅ (ψ-≅ e) e′) z≅)
ψ-≅ (l≅ h) = l≅ (λ n → ψ-≅ (h n))
ψ-≅ (upˡ {r = zero} e)   = ψ-≅ e
ψ-≅ (upˡ {r = self n} e) = ψ-≅ e
ψ-≅ (upʳ {r = zero} e)   = ψ-≅ e
ψ-≅ (upʳ {r = self n} e) = ψ-≅ e
ψ-≅ {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} (lᵢ≅ {j = j} {p = q} {q = q′} {f = f} {g = g} h)
  with <ʷ-dec (σ q) p | <ʷ-dec (σ′ q′) p′
... | injᵃ r | injᵃ r′ = lᵢ≅ λ x y e →
  subst₂ (λ u v → ψ p σ (f (into (<→◃ q) u)) ≅ ψ p′ σ′ (g (into (<→◃ q′) v)))
         (sym (out-into (<→◃ r) x)) (sym (out-into (<→◃ r′) y))
         (ψ-≅ (h x y (R-conv (<→◃ r) (<→◃ q) e)))
... | injᵃ r | injᵇ s  = ⊥-elim (<ʷ-irrefl (<ʷ-trans r s))
... | injᵃ r | injᶜ e  = ⊥-elim (<ʷ-irrefl (subst (j <ʷ_) (sym e) r))
... | injᵇ s | injᵃ r  = ⊥-elim (<ʷ-irrefl (<ʷ-trans r s))
... | injᶜ e | injᵃ r  = ⊥-elim (<ʷ-irrefl (subst (j <ʷ_) (sym e) r))
... | injᵇ _ | injᵇ _  = l≅ (λ n → ψ-≅ (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ e → ψ-≅ (h _ _ (≅→R (<→◃ q) e))) (Ω-refl j)
... | injᵇ _ | injᶜ _  = l≅ (λ n → ψ-≅ (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ e → ψ-≅ (h _ _ (≅→R (<→◃ q) e))) (Ω-refl j)
... | injᶜ _ | injᵇ _  = l≅ (λ n → ψ-≅ (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ e → ψ-≅ (h _ _ (≅→R (<→◃ q) e))) (Ω-refl j)
... | injᶜ _ | injᶜ _  = l≅ (λ n → ψ-≅ (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ e → ψ-≅ (h _ _ (≅→R (<→◃ q) e))) (Ω-refl j)
```

## §6 叶子为 $\cong$ 的结构序

$\prec$ 与 Certified §1 的结构序形状相同, 只改两处: 叶子 `≺z` 要求 $c\cong b$ 而不是 $c=b$; `≺i` 只经 PER 定义域内的分支 ($x\cong x$) 下降. 另加 `≺u` (透过提升). 它是跨层的: 左右两边可以在不同的层. 前驱包含 $a\sqsubseteq b$ 直接定义为 "$a$ 的每个前驱都是 $b$ 的前驱"; 在树这一侧不需要 Certified 那样的归纳版本, 因为它从不进入某个数据类型的构造子. $\prec$ 两侧都尊重 $\cong$ (`≺-respˡ`, `≺-respʳ`), 所以 $\cong\subseteq\sqsubseteq$.

```agda
infix 4 _≺_ _⊑_
data _≺_ : ∀ {ℓ₁ ℓ₂} → Ordᶜ ℓ₁ → Ordᶜ ℓ₂ → Set where
  ≺z : ∀ {ℓ₁ ℓ₂} {c : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → c ≅ b → c ≺ suc b
  ≺s : ∀ {ℓ₁ ℓ₂} {c : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → c ≺ b → c ≺ suc b
  ≺l : ∀ {ℓ₁ ℓ₂} {c : Ordᶜ ℓ₁} {f : ℕ → Ordᶜ ℓ₂} n → c ≺ f n → c ≺ lim f
  ≺i : ∀ {ℓ₁ ℓ₂ j} {c : Ordᶜ ℓ₁} {p : j <ʷ ℓ₂} {f : U j (<→◃ p) → Ordᶜ ℓ₂}
       (x : Ordᶜ j) → x ≅ x → c ≺ f (into (<→◃ p) x) → c ≺ limᵢ p f
  ≺u : ∀ {ℓ₁ ℓ₂ k} {c : Ordᶜ ℓ₁} {r : k ◃₁ ℓ₂} {y : U k (◃₁→◃ r)} → c ≺ out (◃₁→◃ r) y → c ≺ up r y

_⊑_ : ∀ {ℓ₁ ℓ₂} → Ordᶜ ℓ₁ → Ordᶜ ℓ₂ → Set
a ⊑ b = ∀ {ℓ} {c : Ordᶜ ℓ} → c ≺ a → c ≺ b

≺-respˡ : ∀ {ℓ₁ ℓ₁′ ℓ₂} {c : Ordᶜ ℓ₁} {c′ : Ordᶜ ℓ₁′} {b : Ordᶜ ℓ₂} → c ≅ c′ → c ≺ b → c′ ≺ b
≺-respˡ e (≺z e′)      = ≺z (≅-trans (≅-sym e) e′)
≺-respˡ e (≺s h)       = ≺s (≺-respˡ e h)
≺-respˡ e (≺l n h)     = ≺l n (≺-respˡ e h)
≺-respˡ e (≺i x ex h)  = ≺i x ex (≺-respˡ e h)
≺-respˡ e (≺u h)       = ≺u (≺-respˡ e h)

≺-respʳ : ∀ {ℓ₁ ℓ₂ ℓ₃} {c : Ordᶜ ℓ₁} {a : Ordᶜ ℓ₂} {b : Ordᶜ ℓ₃} → c ≺ a → a ≅ b → c ≺ b
≺-respʳ h (upʳ {r = zero} e)   = ≺u (≺-respʳ h e)
≺-respʳ h (upʳ {r = self n} e) = ≺u (≺-respʳ h e)
≺-respʳ (≺u {r = zero} h)   (upˡ e) = ≺-respʳ h e
≺-respʳ (≺u {r = self n} h) (upˡ e) = ≺-respʳ h e
≺-respʳ (≺z e₀)   (s≅ e) = ≺z (≅-trans e₀ e)
≺-respʳ (≺s h)    (s≅ e) = ≺s (≺-respʳ h e)
≺-respʳ (≺l n h)  (l≅ e) = ≺l n (≺-respʳ h (e n))
≺-respʳ (≺i {p = p} x ex h) (lᵢ≅ e) = ≺i x ex (≺-respʳ h (e x x (≅→R (<→◃ p) ex)))

≅→⊑ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≅ b → a ⊑ b
≅→⊑ e h = ≺-respʳ h e

⊑-refl : ∀ {ℓ} {a : Ordᶜ ℓ} → a ⊑ a
⊑-refl h = h

⊑-trans : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} {c : Ordᶜ ℓ₃} → a ⊑ b → b ⊑ c → a ⊑ c
⊑-trans p q h = q (p h)

⊑-lim : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {f : ℕ → Ordᶜ ℓ₂} n → a ⊑ f n → a ⊑ lim f
⊑-lim n p h = ≺l n (p h)

lim-⊑ : ∀ {ℓ₁ ℓ₂} {f : ℕ → Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → (∀ n → f n ⊑ b) → lim f ⊑ b
lim-⊑ k (≺l n h) = k n h

⊑-limᵢ : ∀ {ℓ₁ ℓ₂ j} {a : Ordᶜ ℓ₁} {p : j <ʷ ℓ₂} {f : U j (<→◃ p) → Ordᶜ ℓ₂}
         (x : Ordᶜ j) → x ≅ x → a ⊑ f (into (<→◃ p) x) → a ⊑ limᵢ p f
⊑-limᵢ x ex p h = ≺i x ex (p h)

⊑-up : ∀ {ℓ₁ ℓ₂ k} {a : Ordᶜ ℓ₁} {r : k ◃₁ ℓ₂} {y : U k (◃₁→◃ r)} → a ⊑ out (◃₁→◃ r) y → a ⊑ up r y
⊑-up p h = ≺u (p h)

up-⊑ : ∀ {ℓ₁ ℓ₂ k} {b : Ordᶜ ℓ₁} {r : k ◃₁ ℓ₂} {y : U k (◃₁→◃ r)} → out (◃₁→◃ r) y ⊑ b → up r y ⊑ b
up-⊑ p (≺u h) = p h
```

**不退化.** $\prec$ 是良基的 (`acc≺`), 于是无自反; 对 PER 定义域内的 $a$, $\mathrm{suc}\,a\not\sqsubseteq a$. 所以把叶子换成 $\cong$ 并没有让 $\sqsubseteq$ 变得平凡.

```agda
data Acc≺ {ℓ} (a : Ordᶜ ℓ) : Set where
  acc : (∀ {ℓ′} {b : Ordᶜ ℓ′} → b ≺ a → Acc≺ b) → Acc≺ a

acc≺ : ∀ {ℓ} (a : Ordᶜ ℓ) {ℓ′} {b : Ordᶜ ℓ′} → b ≺ a → Acc≺ b
acc≺ (suc a)          (≺z e)      = acc (λ h → acc≺ a (≺-respʳ h e))
acc≺ (suc a)          (≺s h)      = acc≺ a h
acc≺ (lim f)          (≺l n h)    = acc≺ (f n) h
acc≺ (limᵢ p f)       (≺i x ex h) = acc≺ (f (into (<→◃ p) x)) h
acc≺ (up zero y)      (≺u h)      = acc≺ y h
acc≺ (up (self n) y)  (≺u h)      = acc≺ y h

≺-irrefl : ∀ {ℓ} {a : Ordᶜ ℓ} → ¬ (a ≺ a)
≺-irrefl {a = a} = go (acc (acc≺ a)) where
  go : ∀ {ℓ} {a : Ordᶜ ℓ} → Acc≺ a → ¬ (a ≺ a)
  go (acc h) p = go (h p) p

suc-⋢ : ∀ {ℓ} {a : Ordᶜ ℓ} → a ≅ a → ¬ (suc a ⊑ a)
suc-⋢ e h = ≺-irrefl (h (≺z e))
```

## §7 决定性检验 I: $\Omega$ 的极限分支是步进的

$\Omega_{\mathrm{suc}\,a}$ 的前驱恰是第 $a$ 层各树的前驱 (经 `≺i x (≺u h)`), $\Omega_{\lim f}$ 的前驱是各 $\Omega_{f\,n}$ 的前驱 (经 `≺l n (≺u h)`). 由此 $a<^\mathsf{w}b$ 时第 $a$ 层每棵树都 $\sqsubseteq\Omega_b$ (`below`), 进而对**任意**层号, $a\sqsubseteq^\mathsf{w}b\Rightarrow\Omega_a\sqsubseteq\Omega_b$ (`Ω-mono`). 于是 $\Omega$ 在任意极限层的基本列都是 $\sqsubseteq$-步进的 (`Ω-lim-step`); 对角线实际用到的 $\Omega_{\varepsilon_0}$ 是特例 (`Ωε₀-step`). 对照 Certified 的 `Ωε₀-not-step`: 同样的层号 `ε₀ʷ`、同样的步进证据 `γᴺ-step`, 结论相反.

```agda
𝟎 : ∀ {ℓ} → Ordᶜ ℓ
𝟎 = zero

z≺Ω : ∀ {ℓ₀} b → 𝟎 {ℓ₀} ≺ Ω b
z≺Ω zero      = ≺z z≅
z≺Ω (suc b)   = ≺i (suc zero) (s≅ z≅) (≺u (≺z z≅))
z≺Ω (lim f s) = ≺l 0 (≺u (z≺Ω (f 0)))

below : ∀ {a b} → a <ʷ b → {x : Ordᶜ a} → x ≅ x → x ⊑ Ω b
below zero      ex h = ≺i _ ex (≺u h)
below {b = suc b} (suc q)   ex h = ≺i (Ω b) (Ω-refl b) (≺u (below q ex h))
below (lim n q) ex h = ≺l n (≺u (below q ex h))

Ω-mono : ∀ {a b} → a ⊑ʷ b → Ω a ⊑ Ω b
Ω-mono {b = b} z⊑ (≺z e) = ≺-respˡ (≅-sym e) (z≺Ω b)
Ω-mono (s⊑ q) (≺i x ex (≺u h)) = below q ex h
Ω-mono (l⊑ k) (≺l n (≺u h))    = Ω-mono (k n) h

Ω-lim-step : ∀ {f : ℕ → Ordʷ} {s : ∀ n → f n ⊑ʷ f (suc n)} n →
             _⊑_ {lim f s} {lim f s} (up (self {f = f} {s = s} n) (Ω (f n)))
                                     (up (self {f = f} {s = s} (suc n)) (Ω (f (suc n))))
Ω-lim-step {s = s} n = up-⊑ (⊑-up (Ω-mono (s n)))

Tᶜ : ℕ → Ordᶜ ε₀ʷ
Tᶜ n = up (self n) (Ω (γᴺ (suc n)))

_ : Ω ε₀ʷ ≡ lim Tᶜ
_ = refl

Ωε₀-step : ∀ n → Tᶜ n ⊑ Tᶜ (suc n)
Ωε₀-step = Ω-lim-step {f = γᴺ ∘ suc} {s = γᴺ-step ∘ suc}
```

这里**两个**改动都用到了. `up` 让第 $n$ 项的前驱就是 $\Omega_{f\,n}$ 的前驱, 不带标签; $\cong$ 叶子 (经 `≺-respˡ`) 让 $\Omega_0=1$ 的前驱 $0$ 与 $\Omega_b$ 里的 $0$ 相认. 只有后者而没有 `up` 时, 同一定理在 `W` 上应当也能证 (用 FiniteAll `↑ˡ` 那样的引理把 $\uparrow$ 消掉), 本文未编译; 只有前者而叶子仍是字面相等时, 跨层的 `≺z` 根本无法陈述.

## §8 决定性检验 II: $x_3$ 的顶层序列是步进的

$x_3=\psi_0(\Omega_{\varepsilon_0})$ 的基本列是 $X_n=\psi_0(\Omega_{\gamma(n+1)})$, 其中折叠经 `Sim` 证据 `lim n` (并入的那个提升). 一般定理: 对任意目标层 $i$ 与任意折叠证据, $a\sqsubseteq^\mathsf{w}b\Rightarrow\psi_i(\Omega_a)\sqsubseteq\psi_i(\Omega_b)$ (`Ψ-mono`). 关键一步是 `Ψ-suc`: $\psi_i(\Omega_{\mathrm{suc}\,c})$ 若折叠 ($i\le c$), 它的 $\gamma$-链第 0 项是 $\psi_i(\Omega_c)$ (起点 $\Omega_c$, 经 `up zero`); 若穿透 ($c<i$), 它在分支 $\Omega_c$ 处就是 $\psi_i(\Omega_c)$. 两种情况下 "就是" 都只在 $\cong$ 下成立, 因为两边的 `Sim` 证据不同, 由 `ψ-≅` 补上. 其余情况对 $\sqsubseteq^\mathsf{w}$ 与 $<^\mathsf{w}$ 的推导递归.

```agda
Ψ-suc : ∀ {i c ℓ ℓ′} {p : i <ʷ ℓ} {σ : Simʷ c ℓ} {p′ : i <ʷ ℓ′} {σ′ : Simʷ (suc c) ℓ′} →
        ψ p σ (Ω c) ⊑ ψ p′ σ′ (Ω (suc c))
Ψ-suc {c = c} {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} with <ʷ-dec (σ′ zero) p′
... | injᵃ r = ⊑-limᵢ (Ω c) (Ω-refl c)
                 (subst (λ u → ψ p σ (Ω c) ⊑ ψ p′ σ′ (up zero u)) (sym (out-into (<→◃ r) (Ω c)))
                        (≅→⊑ (ψ-≅ (Ω-refl c))))
... | injᵇ _ = ⊑-lim 0 (≅→⊑ (ψ-≅ (Ω-refl c)))
... | injᶜ _ = ⊑-lim 0 (≅→⊑ (ψ-≅ (Ω-refl c)))

Ψ0 : ∀ {i ℓ ℓ′} b {p : i <ʷ ℓ} {σ : Simʷ zero ℓ} {p′ : i <ʷ ℓ′} {σ′ : Simʷ b ℓ′} →
     ψ p σ (Ω zero) ⊑ ψ p′ σ′ (Ω b)
Ψ0 zero      = ≅→⊑ (ψ-≅ (Ω-refl zero))
Ψ0 (suc b) {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} =
  ⊑-trans (Ψ0 b {p = p} {σ = σ} {p′ = p′} {σ′ = λ q → σ′ (suc q)}) (Ψ-suc {p = p′} {σ = λ q → σ′ (suc q)})
Ψ0 (lim g t) {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} =
  ⊑-lim 0 (Ψ0 (g 0) {p = p} {σ = σ} {p′ = p′} {σ′ = λ q → σ′ (lim 0 q)})

Ψ< : ∀ {i a b ℓ ℓ′} → a <ʷ b → {p : i <ʷ ℓ} {σ : Simʷ (suc a) ℓ} {p′ : i <ʷ ℓ′} {σ′ : Simʷ b ℓ′} →
     ψ p σ (Ω (suc a)) ⊑ ψ p′ σ′ (Ω b)
Ψ< zero = ≅→⊑ (ψ-≅ (Ω-refl _))
Ψ< (suc q) {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} =
  ⊑-trans (Ψ< q {p = p} {σ = σ} {p′ = p′} {σ′ = λ r → σ′ (suc r)}) (Ψ-suc {p = p′} {σ = λ r → σ′ (suc r)})
Ψ< (lim n q) {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} =
  ⊑-lim n (Ψ< q {p = p} {σ = σ} {p′ = p′} {σ′ = λ r → σ′ (lim n r)})

Ψ-mono : ∀ {i a b ℓ ℓ′} → a ⊑ʷ b → {p : i <ʷ ℓ} {σ : Simʷ a ℓ} {p′ : i <ʷ ℓ′} {σ′ : Simʷ b ℓ′} →
         ψ p σ (Ω a) ⊑ ψ p′ σ′ (Ω b)
Ψ-mono {b = b} z⊑ {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} = Ψ0 b {p = p} {σ = σ} {p′ = p′} {σ′ = σ′}
Ψ-mono (s⊑ q) {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} = Ψ< q {p = p} {σ = σ} {p′ = p′} {σ′ = σ′}
Ψ-mono (l⊑ k) {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} =
  lim-⊑ (λ n → Ψ-mono (k n) {p = p} {σ = λ r → σ (lim n r)} {p′ = p′} {σ′ = σ′})

x₃ᶜ : Ordᶜ zero
x₃ᶜ = ψ z<ε₀ʷ (λ q → q) (Ω ε₀ʷ)

X : ℕ → Ordᶜ zero
X n = ψ z<ε₀ʷ (λ q → lim n q) (Ω (γᴺ (suc n)))

_ : x₃ᶜ ≡ lim X
_ = refl

x₃-step : ∀ n → X n ⊑ X (suc n)
x₃-step n = Ψ-mono (γᴺ-step (suc n)) {p = z<ε₀ʷ} {σ = λ q → lim n q} {p′ = z<ε₀ʷ} {σ′ = λ q → lim (suc n) q}
```

`x₃ᶜ` 就是本族的忠实折叠 $\psi_{0<\varepsilon_0}(\Omega_{\varepsilon_0})$, 它的基本列逐项是 $\psi_0(\Omega_{\gamma(n+1)})$ (`refl`), 与 EBO 的 $\Omega_u[n]=\Omega_{u[n]}$ 格式一致.

## §9 目标层 0: 无证明的折叠与字面步进

目标层为 0 时没有 $j<^\mathsf{w}0$, 派发永远落在规则 6, 所以折叠不需要 $p$, 也不需要 `Sim`. 写成 `ψ⁰`, 提升节点直接透过: `ψ⁰ (up r x) = ψ⁰ x`. 它与带证明的折叠在 $\cong$ 下一致 (`ψ⁰-≅`, 穿透分支 `injᵃ ()` 是荒谬的).

```agda
ψ⁰ : ∀ {k} → Ordᶜ k → Ordᶜ zero
ψ⁰ zero    = suc zero
ψ⁰ (suc a) = lim (iter (ψ⁰ a +_) zero)
ψ⁰ (lim f) = lim (λ n → ψ⁰ (f n))
ψ⁰ (limᵢ {i = j} q f) = lim (λ n → ψ⁰ (f (into (<→◃ q) (iter (λ x → ψ q (λ r → r) (f (into (<→◃ q) x))) (Ω j) n))))
ψ⁰ (up zero x)     = ψ⁰ x
ψ⁰ (up (self n) x) = ψ⁰ x

ψ⁰-≅ : ∀ {k₁ k₂ ℓ} {p : zero <ʷ ℓ} {σ : Simʷ k₂ ℓ} {a : Ordᶜ k₁} {b : Ordᶜ k₂} → a ≅ b → ψ⁰ a ≅ ψ p σ b
ψ⁰-≅ z≅     = s≅ z≅
ψ⁰-≅ (s≅ e) = l≅ (iter-R _≅_ (λ e′ → add-≅ (ψ⁰-≅ e) e′) z≅)
ψ⁰-≅ (l≅ h) = l≅ (λ n → ψ⁰-≅ (h n))
ψ⁰-≅ (upˡ {r = zero} e)   = ψ⁰-≅ e
ψ⁰-≅ (upˡ {r = self n} e) = ψ⁰-≅ e
ψ⁰-≅ (upʳ {r = zero} e)   = ψ⁰-≅ e
ψ⁰-≅ (upʳ {r = self n} e) = ψ⁰-≅ e
ψ⁰-≅ {p = p} {σ = σ} (lᵢ≅ {j = j} {p = q} {q = q′} {f = f} {g = g} h) with <ʷ-dec (σ q′) p
... | injᵃ ()
... | injᵇ _ = l≅ (λ n → ψ⁰-≅ (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ e → ψ-≅ (h _ _ (≅→R (<→◃ q) e))) (Ω-refl j)
... | injᶜ _ = l≅ (λ n → ψ⁰-≅ (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ e → ψ-≅ (h _ _ (≅→R (<→◃ q) e))) (Ω-refl j)
```

**字面步进.** 用 Certified 的字面结构序 (第 0 层, 叶子是字面相等; `⊑⁰-literal` 与 Certified 的 `⊑-literal` 同一形式), $a\mapsto\psi^0(\Omega_a)$ 仍是单调的 (`Ψ⁰-mono`), 而且证明比 $\cong$ 版本更短: $\psi^0(\Omega_{\mathrm{suc}\,c})$ 的第 0 项**定义性地**就是 $\psi^0(\Omega_c)$. 于是 $x_3$ 的顶层序列对字面 $\sqsubseteq$ 也是步进的 (`x₃-literal-step`); $x_3$ 的基本列逐项是 $\psi^0(\Omega_{\gamma(n+1)})$, 闭包里没有 `lim n`.

这是定义性提升独有的收益. 在 `W` 里 $\psi_0(\uparrow_s x)$ 要遍历 $\uparrow_s x$, 规则 6 的链调用 $\psi_{s\,q}$, 读到的是被 $s$ 改写过的证明, 闭包因此依赖提升路径 (Certified §10 第 2 条). 在这里, 提升节点根本不被展开.

FGH 在 $\cong$ 下不变 (`FGH-≅`), 所以无证明的 $x_3$ 与忠实折叠的 `x₃ᶜ` 给出同一个增长函数 (`FGH-x₃`); `FGH x₃ 99` 是闭项 (只做类型检查).

```agda
infix 4 _≺⁰_ _⊑⁰_
data _≺⁰_ : Ordᶜ zero → Ordᶜ zero → Set where
  ≺z : ∀ {a} → a ≺⁰ suc a
  ≺s : ∀ {a b} → a ≺⁰ b → a ≺⁰ suc b
  ≺l : ∀ {a} {f : ℕ → Ordᶜ zero} n → a ≺⁰ f n → a ≺⁰ lim f

_⊑⁰_ : Ordᶜ zero → Ordᶜ zero → Set
a ⊑⁰ b = ∀ {c} → c ≺⁰ a → c ≺⁰ b

⊑⁰-literal : ∀ {a b} → suc a ⊑⁰ suc b → a ≡ b ⊎ a ≺⁰ b
⊑⁰-literal h with h ≺z
... | ≺z   = inj₁ refl
... | ≺s q = inj₂ q

Ψ⁰-suc : ∀ c → ψ⁰ (Ω c) ⊑⁰ ψ⁰ (Ω (suc c))
Ψ⁰-suc c h = ≺l 0 h

Ψ⁰0 : ∀ b → ψ⁰ (Ω zero) ⊑⁰ ψ⁰ (Ω b)
Ψ⁰0 zero      h = h
Ψ⁰0 (suc b)   h = Ψ⁰-suc b (Ψ⁰0 b h)
Ψ⁰0 (lim g t) h = ≺l 0 (Ψ⁰0 (g 0) h)

Ψ⁰< : ∀ {a b} → a <ʷ b → ψ⁰ (Ω (suc a)) ⊑⁰ ψ⁰ (Ω b)
Ψ⁰< zero      h = h
Ψ⁰< {b = suc b} (suc q) h = Ψ⁰-suc b (Ψ⁰< q h)
Ψ⁰< (lim n q) h = ≺l n (Ψ⁰< q h)

Ψ⁰-mono : ∀ {a b} → a ⊑ʷ b → ψ⁰ (Ω a) ⊑⁰ ψ⁰ (Ω b)
Ψ⁰-mono {b = b} z⊑ = Ψ⁰0 b
Ψ⁰-mono (s⊑ q)     = Ψ⁰< q
Ψ⁰-mono (l⊑ k) (≺l n h) = Ψ⁰-mono (k n) h

x₃ : Ordᶜ zero
x₃ = ψ⁰ (Ω ε₀ʷ)

_ : x₃ ≡ lim (λ n → ψ⁰ (Ω (γᴺ (suc n))))
_ = refl

x₃-literal-step : ∀ n → ψ⁰ (Ω (γᴺ (suc n))) ⊑⁰ ψ⁰ (Ω (γᴺ (suc (suc n))))
x₃-literal-step n = Ψ⁰-mono (γᴺ-step (suc n))

x₃≅x₃ᶜ : x₃ ≅ x₃ᶜ
x₃≅x₃ᶜ = ψ⁰-≅ (Ω-refl ε₀ʷ)

_ : ℕ
_ = FGH x₃ 99
```

```agda
iter-ext : ∀ {f g : ℕ → ℕ} → (∀ m → f m ≡ g m) → ∀ a n → iter f a n ≡ iter g a n
iter-ext h a zero    = refl
iter-ext {g = g} h a (suc n) = trans (h _) (cong g (iter-ext h a n))

FGH-≅ : ∀ {x y : Ordᶜ zero} → x ≅ y → ∀ n → FGH x n ≡ FGH y n
FGH-≅ z≅     n = refl
FGH-≅ (s≅ e) n = iter-ext (FGH-≅ e) n n
FGH-≅ (l≅ h) n = FGH-≅ (h n) n
FGH-≅ (lᵢ≅ {p = ()} h) n
FGH-≅ (upˡ {r = ()} e) n
FGH-≅ (upʳ {r = ()} e) n

FGH-x₃ : ∀ n → FGH x₃ n ≡ FGH x₃ᶜ n
FGH-x₃ = FGH-≅ x₃≅x₃ᶜ
```

## §10 $x_3$ 内部: 已证与未证

$x_3$ 的遗传步进要求它内部的**每个** `lim` 序列都步进. 层号 $\gamma(n+1)$ 都在 $\psi_0$ 片段 ($\varepsilon_0$ 以下), 由 `zero`/`suc`/`lim` 生成, 所以 $x_3$ 内部的序列只有四类:

| 来源 | 形状 | 状态 |
|---|---|---|
| $\psi^0(\Omega_{\lim g})$ | $\lim_n\psi^0(\Omega_{g\,n})$ | 已证, 字面 (`Ψ⁰-mono`) |
| $\psi^0(\Omega_0)$, 规则 4 | $\lim_n c\cdot n$ | 已证, 字面 (`rule4⁰`) |
| $\psi^0(\Omega_1)$, 第 0 层的链 | $\lim_n\psi^0(G_n)$ | 已证, 字面 (`Ω₁-chain-step`, 用 `G-step`) |
| $\psi^0(\Omega_{\mathrm{suc}\,c})$, $c\ge1$ | $\lim_n\psi^0(\gamma^c_n)$, $\gamma^c$ 是第 $c$ 层的 $\psi_c$-链 | **未证** |

第三行以及 Certified 的 `G-step` 依赖 "$\psi$ 在不含 `limᵢ` 的输入上单调". 第四行要求 $\psi^0$ (以及它在链元素内部遇到的折叠) 在链元素上单调, 而链元素含 `limᵢ`. 这就是 Cumsum §7 第 3 条与 Certified §4 的安全路径引理: 相邻两项的结构路径在每个下标 $\ge$ 目标层的 `limᵢ` 节点处都要经过 $\gamma$-链分支. 它在这里不再受内涵性阻挡 (在 $\cong$ 版本里, 证明与闭包都不被比较), 但仍需要真正的数学内容. 下面的反例说明这条引理绕不开: Certified 的 `ψ-not-⊑mono` 在本族上原样成立. $\mathrm{suc}\,a_1\sqsubseteq\Omega_1$ 经过的是非链分支, 而 $\psi_0(\mathrm{suc}\,a_1)\not\sqsubseteq\psi_0(\Omega_1)$.

```agda
Ω₁ : Ordᶜ (suc zero)
Ω₁ = Ω (suc zero)

ψ₀ : Ordᶜ (suc zero) → Ordᶜ zero
ψ₀ = ψ zero (λ q → q)

G : ℕ → Ordᶜ zero
G = iter (λ x → ψ₀ (up zero x)) (suc zero)

E : Ordᶜ zero
E = lim (G ∘ suc)

_ : ψ₀ Ω₁ ≡ E
_ = refl

a₁ : Ordᶜ (suc zero)
a₁ = up zero (lim G)

_ : ψ₀ a₁ ≡ E
_ = refl

G-refl : ∀ n → G n ≅ G n
G-refl zero    = s≅ z≅
G-refl (suc n) = ψ-≅ {p = zero} {σ = λ q → suc q} {p′ = zero} {σ′ = λ q → suc q} (G-refl n)

lG : lim G ≅ lim G
lG = l≅ G-refl

E≅E : E ≅ E
E≅E = l≅ (λ n → G-refl (suc n))

suca₁⊑Ω₁ : suc a₁ ⊑ Ω₁
suca₁⊑Ω₁ (≺z e)       = ≺i (suc (lim G)) (s≅ lG) (≺u (≺z (≅-trans e (upˡ lG))))
suca₁⊑Ω₁ (≺s (≺u h))  = ≺i (suc (lim G)) (s≅ lG) (≺u (≺s h))

E≺ : E ≺ ψ₀ (suc a₁)
E≺ = ≺l 2 (≺l 0 (≺l 1 (≺z E≅E)))

ψ-not-⊑mono : (suc a₁ ⊑ Ω₁) × ¬ (ψ₀ (suc a₁) ⊑ ψ₀ Ω₁)
ψ-not-⊑mono = suca₁⊑Ω₁ , λ h → ≺-irrefl (h E≺)
```

第 0 层的三条已证序列:

```agda
⊑⁰-trans : ∀ {a b c} → a ⊑⁰ b → b ⊑⁰ c → a ⊑⁰ c
⊑⁰-trans p q h = q (p h)

+-mono≺⁰ : ∀ {a b c : Ordᶜ zero} → b ≺⁰ c → a + b ≺⁰ a + c
+-mono≺⁰ ≺z       = ≺z
+-mono≺⁰ (≺s h)   = ≺s (+-mono≺⁰ h)
+-mono≺⁰ (≺l n h) = ≺l n (+-mono≺⁰ h)

⊑⁰+ : ∀ {a : Ordᶜ zero} b → a ⊑⁰ a + b
⊑⁰+ zero        h = h
⊑⁰+ (suc b)     h = ≺s (⊑⁰+ b h)
⊑⁰+ (lim f)     h = ≺l 0 (⊑⁰+ (f 0) h)
⊑⁰+ (limᵢ () f) h
⊑⁰+ (up () x)   h

≺-trans⁰ : ∀ {x y z} → x ≺⁰ y → y ≺⁰ z → x ≺⁰ z
≺-trans⁰ p ≺z       = ≺s p
≺-trans⁰ p (≺s q)   = ≺s (≺-trans⁰ p q)
≺-trans⁰ p (≺l n q) = ≺l n (≺-trans⁰ p q)

+-mono⊑⁰ : ∀ {a : Ordᶜ zero} b {c} → b ⊑⁰ c → a + b ⊑⁰ a + c
+-mono⊑⁰ zero    {c} k h      = ⊑⁰+ c h
+-mono⊑⁰ (suc b) k ≺z         = +-mono≺⁰ (k ≺z)
+-mono⊑⁰ (suc b) k (≺s h)     = ≺-trans⁰ h (+-mono≺⁰ (k ≺z))
+-mono⊑⁰ (lim f) k (≺l n h)   = +-mono⊑⁰ (f n) (λ h′ → k (≺l n h′)) h
+-mono⊑⁰ (limᵢ () f) k h
+-mono⊑⁰ (up () x) k h

rule4⁰ : ∀ (c : Ordᶜ zero) n → iter (c +_) zero n ⊑⁰ iter (c +_) zero (suc n)
rule4⁰ c zero    ()
rule4⁰ c (suc n) = +-mono⊑⁰ (iter (c +_) zero n) (rule4⁰ c n)
```

```agda
z≺ψ⁰ : ∀ {k} (y : Ordᶜ k) → zero ≺⁰ ψ⁰ y
z≺ψ⁰ zero            = ≺z
z≺ψ⁰ (suc a)         = ≺l 1 (z≺ψ⁰ a)
z≺ψ⁰ (lim f)         = ≺l 0 (z≺ψ⁰ (f 0))
z≺ψ⁰ (limᵢ {i = j} q f) = ≺l 0 (z≺ψ⁰ (f (into (<→◃ q) (Ω j))))
z≺ψ⁰ (up zero x)     = z≺ψ⁰ x
z≺ψ⁰ (up (self n) x) = z≺ψ⁰ x

ψ⁰-≺ : ∀ {a b : Ordᶜ zero} → a ≺⁰ b → ψ⁰ (suc a) ⊑⁰ ψ⁰ b
ψ⁰-≺ ≺z       h = h
ψ⁰-≺ (≺s q)   h = ≺l 1 (ψ⁰-≺ q h)
ψ⁰-≺ (≺l n q) h = ≺l n (ψ⁰-≺ q h)

ψ⁰-mono⁰ : ∀ (x : Ordᶜ zero) {y} → x ⊑⁰ y → ψ⁰ x ⊑⁰ ψ⁰ y
ψ⁰-mono⁰ zero    {y} k ≺z = z≺ψ⁰ y
ψ⁰-mono⁰ (suc a) k h      = ψ⁰-≺ (k ≺z) h
ψ⁰-mono⁰ (lim f) k (≺l n h) = ψ⁰-mono⁰ (f n) (λ h′ → k (≺l n h′)) h
ψ⁰-mono⁰ (limᵢ () f) k h
ψ⁰-mono⁰ (up () x) k h
```

```agda
ψ₀↑ : Ordᶜ zero → Ordᶜ zero
ψ₀↑ x = ψ₀ (up zero x)

z≺ψ₀↑ : ∀ (y : Ordᶜ zero) → zero ≺⁰ ψ₀↑ y
z≺ψ₀↑ zero    = ≺z
z≺ψ₀↑ (suc a) = ≺l 1 (z≺ψ₀↑ a)
z≺ψ₀↑ (lim f) = ≺l 0 (z≺ψ₀↑ (f 0))
z≺ψ₀↑ (limᵢ () f)
z≺ψ₀↑ (up () x)

ψ₀↑-≺ : ∀ {a b : Ordᶜ zero} → a ≺⁰ b → ψ₀↑ (suc a) ⊑⁰ ψ₀↑ b
ψ₀↑-≺ ≺z       h = h
ψ₀↑-≺ (≺s q)   h = ≺l 1 (ψ₀↑-≺ q h)
ψ₀↑-≺ (≺l n q) h = ≺l n (ψ₀↑-≺ q h)

ψ₀↑-mono : ∀ (x : Ordᶜ zero) {y} → x ⊑⁰ y → ψ₀↑ x ⊑⁰ ψ₀↑ y
ψ₀↑-mono zero    {y} k ≺z = z≺ψ₀↑ y
ψ₀↑-mono (suc a) k h      = ψ₀↑-≺ (k ≺z) h
ψ₀↑-mono (lim f) k (≺l n h) = ψ₀↑-mono (f n) (λ h′ → k (≺l n h′)) h
ψ₀↑-mono (limᵢ () f) k h
ψ₀↑-mono (up () x) k h

G-step : ∀ n → G n ⊑⁰ G (suc n)
G-step zero    ≺z = z≺ψ₀↑ (suc zero)
G-step (suc n) = ψ₀↑-mono (G n) (G-step n)

_ : ψ⁰ (Ω (suc zero)) ≡ lim (λ n → ψ⁰ (G n))
_ = refl

Ω₁-chain-step : ∀ n → ψ⁰ (G n) ⊑⁰ ψ⁰ (G (suc n))
Ω₁-chain-step n = ψ⁰-mono⁰ (G n) (G-step n)
```

**字面版本的边界.** 第四行即使证出, 在字面关系下也未必成立: 当目标层 $i\ge\omega$ 时, 穿透把 `<ʷ-dec (σ q) p` 算出的证明写进输出的 `limᵢ`, 而 `σ` 依赖提升路径; $\psi^0$ 的链再经 $\psi_q$ 读这个证明. 在 $\cong$ 版本里这不是问题 (`ψ-≅` 对任意 `σ` 成立).

## §11 与 WellFormed 系列及 QIITOrd 的比较

**[WellFormed](../../../src/WellFormed/Base.lagda.md) 系列 (作者自己的良构树序数, `--cubical`).** `Ord` 的极限要求严格递增 (`wf`), 结构序 `Road`/`<` 与 `Ord` 互归纳, 这与 `W` 的做法同类. [CrossTree](../../../src/WellFormed/CrossTree.lagda.md) 定义跨树的非严格序 $\preccurlyeq$ (`z≼`, `s≼s`, `≼l`, `l≼`), 外延相等 $\approx\;:=\;\preccurlyeq\wedge\succcurlyeq$, 严格序 $a\prec b:=a^+\preccurlyeq b$. 与本文对照:

- CrossTree 的 $\preccurlyeq$ 是**外延**的: `l≼` 让 $\lim f\preccurlyeq a$ 只看各项, 两个共尾的基本列给出 $\approx$ 的极限. 本文的 $\cong$ 是**结构**的: `l≅` 逐项对应, 不同基本列的极限不 $\cong$. 这个差别决定了能否保留有界三歧性. 外延的序上三歧性推出 LPO (Barrier), 只能用于语义陈述; $\cong$ 只是把 "函数逐点" 与 "证明无关" 加到结构相等上, `<ʷ-dec` 照常可判定.
- WellFormed 用 cubical 是为了函数外延性与 `wf` 的命题性 (`limExtPath`: 逐点路径 $\Rightarrow$ 极限的路径, 要 `funExt` 与 `isPropWf`). 本文的 $\cong$ 正是这两件事的 setoid 替身: `l≅` 代替 `funExt`, `limᵢ`/`up` 不比较证明代替 `isPropWf`. 代价是 $\cong$ 不是 `≡`, 每个运算都要另证尊重 $\cong$ (`add-≅`, `ψ-≅`, `FGH-≅`).
- CrossTree 的 "跨树" 指同一类型里表示不同的两棵树; 本文的 "跨层" 指不同类型 `Ordᶜ ℓ₁`、`Ordᶜ ℓ₂`, 需要归纳-递归的关系参数 `R`. CrossTree 的 $\prec:=\mathrm{suc}\,a\preccurlyeq b$ 是本文 $\sqsubseteq$ 的外延版本.

**[QIITOrd](https://github.com/BedrockInstitute/QIITOrd) (`--cubical --safe`, 依赖 cubical 0.9).** `Ord` 是商归纳-归纳类型: 构造子 `zero`/`suc`/`lim` (严格单调列), 路径构造子 `l≡l : fst f ≈ fst g → lim f ≡ lim g` (互相共尾的列给出相等的极限), 集合截断 `isSetOrd`; 序 `_≤_` 与 `Ord` 同时定义, 带 `≤-trans` 与 `isProp≤` 两个构造子; 计算的序 `_≤ᶜ_` 经外部消去子定义, 不用 `TERMINATING`. **它必须用 `--cubical`**: 路径构造子与集合截断是高阶归纳类型, `--without-K` 下没有 (只能公设, 违反 `--safe` 纲领). 逐项看能移植什么:

| QIITOrd 的成分 | 能否在 `--safe --without-K` 下保留 | 说明 |
|---|---|---|
| 类型与序同时定义 (归纳-归纳) | 能, 已在用 | `W` 的 `Ordʷ`/`_<ʷ_`/`_⊑ʷ_` 就是这样 |
| 用递归计算的序 (`_≤ᶜ_`) 代替带传递构造子的归纳序 | 能 | 本文树侧的 $\sqsubseteq$ 是函数定义的 (`a ⊑ b = ∀ c → c ≺ a → c ≺ b`), 传递是 `refl` 级的 |
| `l≡l`: 共尾的极限相等 | 不能 (路径构造子); 即使在 cubical 下也**不应**用 | 它把基本列商掉: `FGH (lim f) n = FGH (f n) n` 不尊重 `l≡l`, FGH 在 QIIT 上根本定义不出来; 作下标时序是外延的, 有界三歧性推出 LPO |
| `isProp≤`、`isSetOrd` | 不能 (截断) | 本文用 "关系不比较证明" 代替 |
| 双模拟 $f\approx g$ 作为极限的等同标准 | 只能作语义陈述 | 结构版本是 $\cong$ 的 `l≅` (逐项而非共尾) |

所以 QIITOrd 的核心技术 (商掉基本列) 与本项目的需求正好相反: 大数函数需要基本列, 有界三歧性需要结构序. 可移植的是它的组织方式 (归纳-归纳、计算的序代替带传递性的归纳序), 本文都已采用.

## §12 对比

| 候选 | 1 安全/正性/FGH | 2 定义性提升 + 一致性 | 3 三歧性 + 忠实 $\psi$ | 4 $x_3$ 的步进 |
|---|---|---|---|---|
| C1 全局树 + 层号谓词 | 否 (不严格正) | — | — | — |
| C2/C3 无关、擦除证明 | 否 (类型检查拒绝) | — | — | — |
| C4 `Prop` 值的 $<$ | 否 (`SplitInProp`) | — | 三歧性只能在 `Prop` 里 | — |
| B 和类型 | 是 (第 1 层) | 是 (`old`), 唯一表示需 LPO | 未做 (退化为 A) | — |
| `W` (Certified), 字面 $\sqsubseteq$ | 是 | 否 (`↑` 遍历并写证明) | 是 | 否 (`Ωε₀-not-step`) |
| `W` + $\cong$ 叶子 (未编译, 预期) | 是 | 一致性要 `↑ˡ` 式引理 | 是 | 顶层预期可证 ($\cong$ 版), 字面不行 |
| **A, 直接前驱 `up` (本文)** | **是** | **是** (`lift`, `lift-coh`, `lift-comp`) | **是** (`<ʷ-dec`, `ψ`, `ψ-≅`) | **顶层**: $\cong$ 版 `x₃-step`, 字面版 `x₃-literal-step`; 遗传: 3/4 类序列 |
| A, 任意距离单节点 `up` | 是 (需辅助递归) | 是 (一个节点) | 预期同上 (未展开) | 同上 |

## §13 结论与边界

**推荐.** 采用候选 A (直接前驱 `up`) 加叶子为 $\cong$ 的跨层结构关系; 对角线的顶层折叠用无证明的 `ψ⁰`. 理由:

1. 它满足标准 1–3, 而且下标类型、有界三歧性、忠实折叠的规则形状都不变 (`W` 原样导入).
2. 它把 Certified 的两条否定翻转: `Ωε₀-not-step` 变为 `Ωε₀-step`; Certified 的 "$x_3$ 的步进被内涵性挡住" 变为 `x₃-step` ($\cong$) 与 `x₃-literal-step` (字面). 后者只有定义性提升才给得出.
3. 内涵性不再是对角线的障碍 (在 $\cong$ 版本里). 剩下的缺口是纯数学的: 第 $\ge1$ 层的规则 6 链 $\sqsubseteq$-递增, 即安全路径引理.

**代价.**

- 每个树上的函数多两条 `up` 子句, 每个关系多透明规则. $\cong$ 是 FiniteAll 规模的 PER 机器 (归纳-递归参数 `R`, `R-flip`/`R-reflʳ` 互递归). 加法遇到提升节点仍要遍历 (结果在高层), 只是不再写入证明.
- 步进是模 $\cong$ 的. Certified 的证书 `Step`/`toLevel` 要求下标 `Ordʷ` 的**字面** $\sqsubseteq^\mathsf{w}$. 字面版本目前只在目标层 0 的顶层得到 (`x₃-literal-step`); 若链的步进只在 $\cong$ 下成立, 证书就需要一个 "证据模 $\cong^\mathsf{w}$" 的下标类型. 那时有界三歧性只能给出 "$a<b$, $b<a$ 或 $a\cong^\mathsf{w}b$", 族的定义域在 $\cong^\mathsf{w}$-相关的层之间要靠结构搬运函数, 不再是 `subst`. 这一步本文没有尝试.
- $\psi$ 仍不 $\sqsubseteq$-单调 (`ψ-not-⊑mono`), 所以没有 "所有生成运算保持步进" 的一般定理, 遗传步进必须沿安全路径证.

**边界与未做.**

- 标准 4 只部分成立: Certified 第一个失败的情形 (`Ωε₀-step`) 与 $x_3$ 的顶层序列 (`x₃-step`, `x₃-literal-step`) 已证; $x_3$ 内部四类序列中三类已证 (§10 的表); 第 $\ge1$ 层的链、$x_3$ 的遗传步进与层号证书 (`CertDiag` 的第 1 步) 未证.
- `Ordᶜ` 与 `W` 的树族之间的翻译 (把 `up` 展开成 `↑ʷ`) 及其与 $\cong$/Certified 的 $\approx$ 的对应未编译; $x_3$ 的序数标签沿用 Certified 的识别, 本文没有对 `ψ` 重做对齐.
- "`W` + $\cong$ 叶子" 一行是基于 FiniteAll `↑ˡ`/`ψᴱ-≈` 的预期, 未编译.
- 方向 C 与单节点 `up` 的实验在临时文件中, 正文只记录了声明与确切报错.
- 本文不改 `src/`、`archive/` 与已有的 Align 文件.
