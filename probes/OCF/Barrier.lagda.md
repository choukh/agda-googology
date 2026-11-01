# 形式化大数数学 (3.1 - 布劳威尔树壁垒定理)

> 交流Q群: 893531731  
> 本文源码: [Barrier.lagda.md](https://github.com/choukh/agda-googology/blob/main/probes/OCF/Barrier.lagda.md)  
> 前篇: [BTBO.lagda.md](../../src/OCF/BTBO.lagda.md)

[前篇](../../src/OCF/BTBO.lagda.md)用布劳威尔树实现了 Buchholz 的 $\psi$, 止步于 $\psi(\Omega_\Omega)$, 并把这个序数命名为布劳威尔树壁垒序数 (BTBO). 此后的一系列探针 (见 `archive/probes/OCF`) 试图把 $\Omega$ 层级的下标推过 $\Omega$, 全部在同一个地方停下: 下标类型一旦含有共尾度为 $\Omega$ 的元素, 它的**有界三歧性**就写不出来. 这些探针记录的都是"没证出来", 而不是"证不出来". 本文把后者形式化.

**定理 (非形式陈述)** 设 $I$ 是任意类型, 带有严格序 $<$, 使得可数序数类型 $\mathsf{Ord}^\mathsf{D}$ 作为**精确的初始段**嵌入 $I$, 且 $I$ 中有一个元素位于整个 $\mathsf{Ord}^\mathsf{D}$ 之上 (即 $I$ 有共尾度 $\Omega$ 的元素). 若 $I$ 具有前篇意义下的有界三歧性, 则有限全知原理 LPO 成立.

LPO 在 Agda `--safe` 下不可证 (见末节的元定理说明), 因此满足上述条件的 $I$ 在本项目纲领内不可定义. 而前篇的 $\psi_<$ 恰好以"下标类型的有界三歧性"为派发机制, 所以 $\Omega$ 层级的下标不可能在该机制下越过 $\Omega$. 这就是壁垒.

与文献的关系: de Jong, Kraus, Nordvall Forsberg, Xu, *Type-Theoretic Approaches to Ordinals* (TCS 2023, [arXiv:2208.03844](https://arxiv.org/abs/2208.03844)) 的 Theorem 53 证明了: 对商归纳类型 Brw (以双模拟商掉的布劳威尔树), 三歧性 $\forall x\,y.\;x<y \lor x=y \lor y<x$ 等价于 LPO; Theorem 48 证明了 $<$, $\le$, $=$ 的可判定性都等价于 LPO. 本文的差别在于: (1) 不商化, 直接在原始归纳类型上工作, 等号是内涵等号; (2) 三歧性只要求**有界**的 (有共同上界的两元素), 这正是前篇真正用到的版本, 也是 BTBO 能成立的原因; (3) $I$ 是任意抽象类型, 定理对所有"把 $\mathsf{Ord}^\mathsf{D}$ 当作初始段再往上加构造子"的设计一次性成立, 而不是针对某个固定的 Brw.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Barrier where
open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import OCF.BTBO using (module Trich; module BoundedTrich; injᵃ; injᵇ; injᶜ)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec)
open BoundedTrich
```

## 有限全知原理

**定义 (LPO)** 对任意二进制序列 $\alpha:\mathbb{N}\to\mathbf{2}$, 要么存在 $k$ 使 $\alpha(k)=\mathsf{true}$, 要么对所有 $k$ 都有 $\alpha(k)=\mathsf{false}$.

```agda
LPO : Set
LPO = (α : ℕ → Bool) → (Σ[ k ∈ ℕ ] α k ≡ true) ⊎ (∀ k → α k ≡ false)
```

LPO 是构造数学中最标准的"禁忌" (taboo) 之一: 它在经典逻辑下平凡成立, 但不能在 Agda `--safe` 中证明 (否则按典范性, 停机问题可判定). 构造反推数学的标准做法, 就是把"命题 $P$ 不可证"精确化为"$P\to\mathsf{LPO}$". 本文遵循这一做法.

把二进制序列翻译成布劳威尔树时, 我们需要"前 $n$ 项中是否出现过 $\mathsf{true}$"这个可判定谓词.

**定义** $\mathsf{any}_\alpha(n) := \alpha(0)\lor\cdots\lor\alpha(n)$.

```agda
any : (ℕ → Bool) → ℕ → Bool
any α zero    = α zero
any α (suc n) = α (suc n) ∨ any α n
```

**引理** (1) $\mathsf{any}_\alpha$ 单调; (2) 若 $\mathsf{any}_\alpha(n)$ 为真, 则存在 $k$ 使 $\alpha(k)$ 为真; (3) 若 $\alpha(k)$ 为真则 $\mathsf{any}_\alpha(k)$ 为真.

```agda
bool-dec : (b : Bool) → b ≡ true ⊎ b ≡ false
bool-dec true  = inj₁ refl
bool-dec false = inj₂ refl

∨-true : ∀ b → b ∨ true ≡ true
∨-true true  = refl
∨-true false = refl

any-up : ∀ {α} n → any α n ≡ true → any α (suc n) ≡ true
any-up {α} n p rewrite p = ∨-true (α (suc n))

any-mono : ∀ {α n m} → n <ᴺ m → any α n ≡ true → any α m ≡ true
any-mono {n = n} zero p = any-up n p
any-mono (suc q) p      = any-up _ (any-mono q p)

any-witness : ∀ {α} n → any α n ≡ true → Σ[ k ∈ ℕ ] α k ≡ true
any-witness zero p = zero , p
any-witness {α} (suc n) p with α (suc n) in eq
... | true  = suc n , eq
... | false = any-witness n p

true→any : ∀ {α} k → α k ≡ true → any α k ≡ true
true→any zero p = p
true→any (suc k) p rewrite p = refl
```

## 抽象壁垒定理

先把定理的核心剥离成一个不涉及布劳威尔树细节的形式. 设 $(I,<)$ 是带传递、非自反的严格序的类型, 并有有界三歧性. 假设 $I$ 中有如下几族元素:

- 有限阶段 $\mathsf{fin}(n)$, 代表自然数 $n$;
- 一个元素 $u$, 是所有有限阶段的**精确**上确界: 任何 $z<u$ 都小于某个 $\mathsf{fin}(n)$;
- 对每个二进制序列 $\alpha$ 一个元素 $v_\alpha$, 它也在所有有限阶段之上, 并且是如下阶段的精确上确界: 任何 $z<v_\alpha$ 都见证"$\mathsf{any}_\alpha(n)$ 为真" 或者小于 $\mathsf{fin}(n)$ (对某个 $n$);
- 只要 $\alpha$ 在某处为真, 就有 $u<v_\alpha$;
- 一个共同上界 $\top$, 位于 $u$ 与所有 $v_\alpha$ 之上.

直观上 $u$ 是 $\omega$, $v_\alpha$ 是"在 $\alpha$ 第一次为真之前像 $\omega$, 之后像 $\omega\cdot 2$"的序数. 经典地, 比较 $u$ 与 $v_\alpha$ 就等于判定 $\alpha$ 是否恒假; 构造地, 这个比较只有在 LPO 下才做得到.

**定理** 以上假设推出 LPO.  
**证明** 给定 $\alpha$, 对 $u<\top$ 和 $v_\alpha<\top$ 应用有界三歧性.

- 若 $u<v_\alpha$: 由 $v_\alpha$ 的精确性得 $n$, 使得 $\mathsf{any}_\alpha(n)$ 为真, 或 $u<\mathsf{fin}(n)$. 前者给出 $\alpha$ 的见证; 后者与 $\mathsf{fin}(n)<u$ 一起由传递性得 $u<u$, 与非自反矛盾.
- 若 $v_\alpha<u$: 由 $u$ 的精确性得 $n$ 使 $v_\alpha<\mathsf{fin}(n)$, 与 $\mathsf{fin}(n)<v_\alpha$ 一起得 $v_\alpha<v_\alpha$, 矛盾.
- 若 $u=v_\alpha$: 对任意 $k$, 若 $\alpha(k)$ 为真, 则 $u<v_\alpha=u$, 矛盾; 故 $\alpha(k)$ 为假. ∎

```agda
module Stages
  (I : Set) (_<ᴵ_ : I → I → Set)
  (trans  : ∀ {a b c} → a <ᴵ b → b <ᴵ c → a <ᴵ c)
  (irrefl : ∀ {a} → ¬ (a <ᴵ a))
  (dec    : ∀ {a b c} → a <ᴵ c → b <ᴵ c → a <ᴵ b ⊎ b <ᴵ a ⊎ a ≡ b)
  (fin : ℕ → I) (u : I) (v : (ℕ → Bool) → I) (top : I)
  (u<top   : u <ᴵ top)
  (v<top   : ∀ α → v α <ᴵ top)
  (fin<u   : ∀ n → fin n <ᴵ u)
  (fin<v   : ∀ α n → fin n <ᴵ v α)
  (u<v     : ∀ α k → α k ≡ true → u <ᴵ v α)
  (u-exact : ∀ {z} → z <ᴵ u → Σ[ n ∈ ℕ ] z <ᴵ fin n)
  (v-exact : ∀ {α z} → z <ᴵ v α → Σ[ n ∈ ℕ ] (any α n ≡ true ⊎ z <ᴵ fin n))
  where

  lpo : LPO
  lpo α with dec u<top (v<top α)
  lpo α | injᵃ u<vα with v-exact u<vα
  lpo α | injᵃ u<vα | n , inj₁ w    = inj₁ (any-witness n w)
  lpo α | injᵃ u<vα | n , inj₂ u<fn = ⊥-elim (irrefl (trans u<fn (fin<u n)))
  lpo α | injᵇ vα<u with u-exact vα<u
  lpo α | injᵇ vα<u | n , vα<fn     = ⊥-elim (irrefl (trans vα<fn (fin<v α n)))
  lpo α | injᶜ u≡vα = inj₂ k-false
    where
    k-false : ∀ k → α k ≡ false
    k-false k with bool-dec (α k)
    ... | inj₁ t = ⊥-elim (irrefl (subst (_<ᴵ v α) u≡vα (u<v α k t)))
    ... | inj₂ f = f
```

注意证明用到有界三歧性的全部三个分支, 也用到 $u$, $v_\alpha$ 两者的精确性: 第一分支从 $v_\alpha$ 的阶段中**提取**见证, 第二分支用 $u$ 的阶段排除, 第三分支用 $u<v_\alpha$ 排除. 任何一条假设去掉, 推不出 LPO 的全部, 这在末节讨论.

## 可数序数源

现在在前篇的 $\mathsf{Ord}^\mathsf{D}$ (单调基本列的可数布劳威尔树) 中具体造出 $\omega$ 与 $\omega^+_\alpha$.

**定义** 自然数的嵌入 $\mathsf{nat}$, 后继的迭代 $a+^{\mathbb{N}}n$, 以及 $\omega:=\mathsf{lim}(\mathsf{nat})$.

```agda
nat : ℕ → Ordᴰ
nat zero    = zero
nat (suc n) = suc (nat n)

nat-mono : monotonic nat
nat-mono zero    = zero
nat-mono (suc p) = suc (nat-mono p)

ω : Ordᴰ
ω = lim nat nat-mono

_+ⁿ_ : Ordᴰ → ℕ → Ordᴰ
a +ⁿ zero  = a
a +ⁿ suc n = suc (a +ⁿ n)

+ⁿ-mono : ∀ {a n m} → n <ᴺ m → a +ⁿ n < a +ⁿ m
+ⁿ-mono zero    = zero
+ⁿ-mono (suc p) = suc (+ⁿ-mono p)

a<a+ⁿ : ∀ {a} n → a < a +ⁿ suc n
a<a+ⁿ zero    = zero
a<a+ⁿ (suc n) = suc (a<a+ⁿ n)

n<ω : ∀ n → nat n < ω
n<ω n = f<l n
```

**定义 (开关序列)** 给定 $\alpha$, 令

$$
\mathsf{sw}_\alpha(n) :=
\begin{cases}
   \omega + (n+1) &\text{if } \mathsf{any}_\alpha(n) \\
   n &\text{otherwise}
\end{cases}
\qquad
\omega^+_\alpha := \mathsf{lim}(\mathsf{sw}_\alpha)
$$

当 $\alpha$ 恒假时 $\mathsf{sw}_\alpha$ 逐点等于 $\mathsf{nat}$, 所以 $\omega^+_\alpha$ 是 $\omega$ 的另一个表示; 当 $\alpha$ 在 $k$ 处为真时, 从第 $k$ 项起 $\mathsf{sw}_\alpha$ 越过 $\omega$, 于是 $\omega^+_\alpha$ 表示 $\omega\cdot2$. 这就是 de Jong 等人 Lemma 47 中 $\mathsf{limit}(s^\uparrow)\le\omega\cdot2$ 的构造在原始归纳类型上的版本.

```agda
switch : Bool → ℕ → Ordᴰ
switch true  n = ω +ⁿ suc n
switch false n = nat n

sw : (ℕ → Bool) → ℕ → Ordᴰ
sw α n = switch (any α n) n
```

**引理** $\mathsf{sw}_\alpha$ 单调.  
**证明** 对 $n<m$, 按 $\mathsf{any}_\alpha(n)$, $\mathsf{any}_\alpha(m)$ 的真值分四种情况. 两真: 后继迭代保序. 两假: $\mathsf{nat}$ 保序. 前假后真: $n<\omega<\omega+(m+1)$. 前真后假: 与 $\mathsf{any}_\alpha$ 的单调性矛盾. ∎

```agda
false≢true : false ≡ true → ⊥
false≢true ()

switch-mono : ∀ {b c n m} → n <ᴺ m → (b ≡ true → c ≡ true) → switch b n < switch c m
switch-mono {b = true}  {c = true}  p _ = +ⁿ-mono (s<s p)
switch-mono {b = false} {c = false} p _ = nat-mono p
switch-mono {b = false} {c = true} {n} {m} p _ = <-trans (n<ω n) (a<a+ⁿ m)
switch-mono {b = true}  {c = false} p h = ⊥-elim (false≢true (h refl))

sw-mono : ∀ α → monotonic (sw α)
sw-mono α p = switch-mono p (any-mono p)

ω⁺ : (ℕ → Bool) → Ordᴰ
ω⁺ α = lim (sw α) (sw-mono α)
```

**引理** (1) 对任意 $n$, $\mathsf{nat}(n)<\omega^+_\alpha$; (2) 若 $\alpha(k)$ 为真, 则 $\omega<\omega^+_\alpha$; (3) 若 $\mathsf{any}_\alpha(n)$ 为假, 则 $\mathsf{sw}_\alpha(n)=\mathsf{nat}(n)$.  
**证明** (1) $\mathsf{nat}(n)<\mathsf{sw}_\alpha(n+1)$: 若开关已开, $\mathsf{nat}(n)<\omega<\omega+(n+2)$; 否则 $\mathsf{nat}(n)<\mathsf{nat}(n+1)$. (2) $\mathsf{any}_\alpha(k)$ 为真, 故 $\mathsf{sw}_\alpha(k)=\omega+(k+1)>\omega$. (3) 按定义. ∎

```agda
n<ω⁺ : ∀ α n → nat n < ω⁺ α
n<ω⁺ α n = lim (suc n) (n<switch (any α (suc n)))
  where
  n<switch : ∀ b → nat n < switch b (suc n)
  n<switch true  = <-trans (n<ω n) (a<a+ⁿ (suc n))
  n<switch false = zero

ω<ω⁺ : ∀ α k → α k ≡ true → ω < ω⁺ α
ω<ω⁺ α k p = lim k (subst (λ b → ω < switch b k) (sym (true→any k p)) (a<a+ⁿ k))

sw-false : ∀ {α n} → any α n ≡ false → sw α n ≡ nat n
sw-false {n = n} p = cong (λ b → switch b n) p
```

## $\Omega$-扩张与壁垒推论

前篇的 `Ord-Ord` 模块对下标类型 $\mathsf{Ord}^\mathsf{D}$ 只用了这些东西: 序 $<$ 及其传递性, 有界三歧性 `<-dec`, 以及 (在 $\Omega$ 与 $\psi_0$ 的定义里) 对构造子 $\mathsf{zero},\mathsf{suc},\mathsf{lim}$ 的递归与 `f<l`. 要把层级推过 $\Omega$, 下标类型 $I$ 必须比 $\mathsf{Ord}^\mathsf{D}$ 多出共尾度为 $\Omega$ 的元素, 同时保留 `<-dec`. 我们把前者写成下面的接口.

**定义 ($\Omega$-扩张)** 一个 $\Omega$-扩张由以下数据组成:

- 类型 $I$ 与严格序 $<_I$ (传递、非自反);
- 嵌入 $\iota:\mathsf{Ord}^\mathsf{D}\to I$, 严格保序;
- **精确性**: 嵌入的极限仍是极限, 即 $z<_I\iota(\mathsf{lim}\,f)$ 蕴含存在 $n$ 使 $z<_I\iota(f(n))$;
- 一个元素 $\top$, 使 $\iota(a)<_I\top$ 对所有 $a$ 成立;
- 有界三歧性.

精确性是说 $\iota$ 把 $\mathsf{Ord}^\mathsf{D}$ 嵌入为 $I$ 的**初始段**而不仅是子序: 凡是 $I$ 中位于某个嵌入极限之下的元素, 都已经位于该极限的某一项之下. 任何"在 $\mathsf{Ord}^\mathsf{D}$ 的构造子之外再加构造子 $\mathsf{lim}_1$, 并把 $<$ 定义为同形的归纳关系"的设计都自动满足它, 因为 $z<\mathsf{lim}(f)$ 的唯一推导规则就是经由某个 $f(n)$. 下一节的实例会展示这一点.

```agda
record Ω-Extension : Set₁ where
  field
    I         : Set
    _<ᴵ_      : I → I → Set
    <ᴵ-trans  : ∀ {a b c} → a <ᴵ b → b <ᴵ c → a <ᴵ c
    <ᴵ-irrefl : ∀ {a} → ¬ (a <ᴵ a)
    ι         : Ordᴰ → I
    ι-mono    : ∀ {a b} → a < b → ι a <ᴵ ι b
    ι-exact   : ∀ {f : ℕ → Ordᴰ} {mono : monotonic f} {z} → z <ᴵ ι (lim f mono) → Σ[ n ∈ ℕ ] z <ᴵ ι (f n)
    top       : I
    ι<top     : ∀ a → ι a <ᴵ top
    <ᴵ-dec    : ∀ {a b c} → a <ᴵ c → b <ᴵ c → a <ᴵ b ⊎ b <ᴵ a ⊎ a ≡ b
```

**定理 (壁垒)** 任何 $\Omega$-扩张都推出 LPO.  
**证明** 取 $\mathsf{fin}:=\iota\circ\mathsf{nat}$, $u:=\iota(\omega)$, $v_\alpha:=\iota(\omega^+_\alpha)$, 共同上界 $\top$. 抽象定理的各条假设: $u,v_\alpha<\top$ 由 $\top$ 的性质; $\mathsf{fin}(n)<u$, $\mathsf{fin}(n)<v_\alpha$, 以及 ($\alpha(k)$ 为真时) $u<v_\alpha$ 由上节引理经 $\iota$ 保序; $u$ 的精确性就是 $\iota$ 在 $\omega=\mathsf{lim}(\mathsf{nat})$ 处的精确性; $v_\alpha$ 的精确性由 $\iota$ 在 $\mathsf{lim}(\mathsf{sw}_\alpha)$ 处的精确性得 $n$ 与 $z<\iota(\mathsf{sw}_\alpha(n))$, 再按 $\mathsf{any}_\alpha(n)$ 分情况: 真则直接得证, 假则 $\mathsf{sw}_\alpha(n)=\mathsf{nat}(n)$. ∎

```agda
barrier : Ω-Extension → LPO
barrier E = lpo
  where
  open Ω-Extension E

  v-exact : ∀ {α z} → z <ᴵ ι (ω⁺ α) → Σ[ n ∈ ℕ ] (any α n ≡ true ⊎ z <ᴵ ι (nat n))
  v-exact {α} p with ι-exact p
  ... | n , q with any α n in eq
  ...   | true  = n , inj₁ eq
  ...   | false = n , inj₂ q

  open Stages I _<ᴵ_ <ᴵ-trans <ᴵ-irrefl <ᴵ-dec
    (ι ∘ nat) (ι ω) (ι ∘ ω⁺) top
    (ι<top ω) (ι<top ∘ ω⁺)
    (ι-mono ∘ n<ω) (λ α n → ι-mono (n<ω⁺ α n)) (λ α k p → ι-mono (ω<ω⁺ α k p))
    ι-exact v-exact
```

于是: 在 Agda `--safe --without-K` 中, 只要不接受 LPO, 就没有任何 $\Omega$-扩张. 换言之, 下标类型"含有 $\Omega$-共尾元"与"有有界三歧性"二者不可兼得. 前篇的 $\mathsf{Ord}^\mathsf{D}$ 选择了后者, 代价是 $\sup\mathsf{Ord}^\mathsf{D}=\Omega$, 于是 $\psi(\Omega_\Omega)$ 成为壁垒.

## 实例: 朴素的 $\mathsf{Ord}_1^\mathsf{D}$

探针 `archive/probes/OCF/Ord1D` 中最直接的设计, 是把 $\mathsf{Ord}^\mathsf{D}$ 的构造子照抄一遍, 再加一个以 $\mathsf{Ord}^\mathsf{D}$ 为下标的极限 $\mathsf{lim}_1$ (要求单调), 期望 $\sup=\Omega_2$:

```agda
module Naive where
  data Ord₁ : Set
  data _<₁_ : Ord₁ → Ord₁ → Set

  monotonic₀ : (ℕ → Ord₁) → Set
  monotonic₀ f = ∀ {n m} → n <ᴺ m → f n <₁ f m

  monotonic₁ : (Ordᴰ → Ord₁) → Set
  monotonic₁ f = ∀ {a b} → a < b → f a <₁ f b

  private variable
    a b c : Ord₁
    f₀ : ℕ → Ord₁
    f₁ : Ordᴰ → Ord₁
    m₀ : monotonic₀ f₀
    m₁ : monotonic₁ f₁

  data Ord₁ where
    zero : Ord₁
    suc  : Ord₁ → Ord₁
    lim₀ : (f : ℕ → Ord₁) → monotonic₀ f → Ord₁
    lim₁ : (f : Ordᴰ → Ord₁) → monotonic₁ f → Ord₁

  infix 10 _<₁_
  data _<₁_ where
    zero : a <₁ suc a
    suc  : a <₁ b → a <₁ suc b
    lim₀ : ∀ n → a <₁ f₀ n → a <₁ lim₀ f₀ m₀
    lim₁ : ∀ x → a <₁ f₁ x → a <₁ lim₁ f₁ m₁
```

探针在这里要写 `<₁-dec`, 卡在 $\mathsf{lim}_1/\mathsf{lim}_1$ 的情况: 两个下标 $x,y:\mathsf{Ord}^\mathsf{D}$ 没有共同上界, 无法派发. 我们现在证明这不是技巧问题. 先补齐接口所需的基本性质.

**引理** $<_1$ 传递, 良基, 从而非自反.

```agda
  <₁-trans : a <₁ b → b <₁ c → a <₁ c
  <₁-trans p zero       = suc p
  <₁-trans p (suc q)    = suc (<₁-trans p q)
  <₁-trans p (lim₀ n q) = lim₀ n (<₁-trans p q)
  <₁-trans p (lim₁ x q) = lim₁ x (<₁-trans p q)

  data Acc (a : Ord₁) : Set where
    acc : (∀ {y} → y <₁ a → Acc y) → Acc a

  acc-below : Acc a → b <₁ a → Acc b
  acc-below (acc h) p = h p

  wf : ∀ a → Acc a
  wf zero        = acc λ ()
  wf (suc a)     = acc below
    where
    below : b <₁ suc a → Acc b
    below zero    = wf a
    below (suc p) = acc-below (wf a) p
  wf (lim₀ f m)  = acc λ { (lim₀ n p) → acc-below (wf (f n)) p }
  wf (lim₁ f m)  = acc λ { (lim₁ x p) → acc-below (wf (f x)) p }

  <₁-irrefl : ¬ (a <₁ a)
  <₁-irrefl {a} p = go (wf a) p
    where
    go : Acc a → a <₁ a → ⊥
    go (acc h) q = go (h q) q
```

**定义 (嵌入)** $\mathsf{Ord}^\mathsf{D}$ 逐构造子嵌入 $\mathsf{Ord}_1$, 单调性证明一并嵌入.

```agda
  embed : Ordᴰ → Ord₁
  embed-mono : ∀ {a b} → a < b → embed a <₁ embed b
  embed zero         = zero
  embed (suc a)      = suc (embed a)
  embed (lim f mono) = lim₀ (embed ∘ f) (embed-mono ∘ mono)
  embed-mono zero      = zero
  embed-mono (suc p)   = suc (embed-mono p)
  embed-mono (lim n p) = lim₀ n (embed-mono p)
```

**引理** (1) 精确性: $z<_1\mathsf{embed}(\mathsf{lim}\,f)$ 的推导只能经由某个 $f(n)$; (2) $\mathsf{lim}_1(\mathsf{embed})$ 位于整个嵌入像之上.

```agda
  embed-exact : ∀ {f : ℕ → Ordᴰ} {mono : monotonic f} {z} → z <₁ embed (lim f mono) → Σ[ n ∈ ℕ ] z <₁ embed (f n)
  embed-exact (lim₀ n p) = n , p

  top : Ord₁
  top = lim₁ embed embed-mono

  embed<top : ∀ a → embed a <₁ top
  embed<top a = lim₁ (suc a) zero
```

**定理** 若朴素 $\mathsf{Ord}_1$ 有有界三歧性, 则 LPO.

```agda
  BoundedTrich₁ : Set
  BoundedTrich₁ = ∀ {a b c} → a <₁ c → b <₁ c → a <₁ b ⊎ b <₁ a ⊎ a ≡ b

  naive-barrier : BoundedTrich₁ → LPO
  naive-barrier dec = barrier record
    { I = Ord₁ ; _<ᴵ_ = _<₁_ ; <ᴵ-trans = <₁-trans ; <ᴵ-irrefl = <₁-irrefl
    ; ι = embed ; ι-mono = embed-mono ; ι-exact = embed-exact
    ; top = top ; ι<top = embed<top ; <ᴵ-dec = dec }
```

对这个具体设计其实可以说得更多: 因为等号是内涵的, 有界三歧性不只是禁忌, 而是**假命题**. 取 $\omega$ 的两个表示 $\mathsf{lim}(\mathsf{nat})$ 与 $\mathsf{lim}(n\mapsto\mathsf{nat}(n+1))$, 它们在 $\top$ 之下, 彼此都不小于对方 (极限不可能小于有限树), 又不相等 (基本列第 $0$ 项不同).

```agda
  data Fin₁ : Ord₁ → Set where
    zero : Fin₁ zero
    suc  : Fin₁ a → Fin₁ (suc a)

  fin-nat : ∀ n → Fin₁ (embed (nat n))
  fin-nat zero    = zero
  fin-nat (suc n) = suc (fin-nat n)

  lim≮fin : Fin₁ b → ¬ (lim₀ f₀ m₀ <₁ b)
  lim≮fin zero    ()
  lim≮fin (suc ()) zero
  lim≮fin (suc h) (suc p) = lim≮fin h p

  lim₀-inj : ∀ {f g : ℕ → Ord₁} {mf : monotonic₀ f} {mg : monotonic₀ g} → _≡_ {A = Ord₁} (lim₀ f mf) (lim₀ g mg) → f ≡ g
  lim₀-inj refl = refl

  zero≢suc : zero ≡ suc a → ⊥
  zero≢suc ()

  ω′ : Ordᴰ
  ω′ = lim (nat ∘ suc) (nat-mono ∘ s<s)

  ¬naive-trich : ¬ BoundedTrich₁
  ¬naive-trich dec with dec (embed<top ω) (embed<top ω′)
  ... | injᵃ (lim₀ n p) = lim≮fin (fin-nat (suc n)) p
  ... | injᵇ (lim₀ n p) = lim≮fin (fin-nat n) p
  ... | injᶜ e          = zero≢suc (cong (λ h → h 0) (lim₀-inj e))
```

这个反驳只对内涵等号成立, 依赖的是"同一序数有不同表示". 壁垒定理不依赖它: 即使把等号换成任何把表示粘合起来的等价 (商类型、setoid、更粗的 $<_I$), 只要精确性与 $\Omega$-共尾元保留, 结论仍是 LPO. 两条结论合起来说的是: 朴素设计在内涵层面直接错, 而任何修补都至少要付出 LPO.

## 结论与边界

**已证明的.** 在 Agda `--safe --without-K`、无公理、无终止检查绕过的条件下:

1. 任何 $\Omega$-扩张 (以 $\mathsf{Ord}^\mathsf{D}$ 为精确初始段、含 $\Omega$-共尾元、有有界三歧性的类型) 推出 LPO.
2. 探针中直接给 $\mathsf{Ord}^\mathsf{D}$ 加 $\mathsf{lim}_1$ 的设计满足该接口, 其 `<₁-dec` 推出 LPO, 且在内涵等号下可直接反驳.

**元定理.** LPO 在上述 Agda 片段中不可证: 该片段有典范性, 一个 LPO 的闭项会给出判定任意可计算二进制序列是否恒假的算法, 从而判定停机问题. 这一步在 Agda 内部不可形式化 (它是关于 Agda 的陈述), 但它是构造类型论的标准事实, 与 de Jong 等人把"$\mathsf{Brw}$ 三歧"刻画为 LPO 时所依赖的是同一个元定理.

**由此得到的壁垒陈述.** 前篇的折叠函数 $\psi_<$ 在 $\mathsf{lim}_i$ 情况以下标类型的有界三歧性派发. 于是在该方案内, 下标类型必须有有界三歧性, 而定理 1 说这样的类型没有 $\Omega$-共尾元, 即 $\sup I\le\Omega$. 所以 $\Omega$-层级的下标到不了 $\Omega$ 之上, 这就是 $\psi(\Omega_\Omega)$ 作为壁垒的精确含义. 探针 `Higher`/`HigherGen` 之所以能在壁垒之上再走几步, 是因为它们把 $\Omega$-共尾的极限全部编码进**单一的 $\mathbb{N}$-单调序列**, 派发落在 $\mathbb{N}$ 的无条件三歧性上, 下标类型本身从未获得 $\Omega$-共尾元; 它们没有违反定理 1, 而是绕开了定理 1 的前提.

**未证明、也不打算在 Agda 内证明的.**

1. "任何可能的折叠算法都必须以下标的有界三歧性派发". 这是对"布劳威尔树范式"的定义, 不是定理. 定理 1 的价值在于把范式的边界精确地落在三条假设上: 精确初始段、$\Omega$-共尾元、有界三歧性. 要越过壁垒就必须放弃其中一条. 放弃第三条的一个方式是改用有限项的表记系统 (可判定的句法 $\prec$), 代价是良基性不再由构造自动保证, 必须另证 (Setzer 1998 的"从下面来"定理说明这一代价不可免). 放弃第三条的另一个方式是让折叠**不派发**: 不比较下标, 而把各分支的候选结果用算律 (max、lub、沿结构递归取的 sup) 合成. 探针 `PastBTBO/SMB/AlgebraicOCF` 给出了这种折叠的可编译原型: 下标用无单调性约束的原始树, 极限构造子不带上界, $\Omega$-索引极限的坍缩沿深度 $0,1,2,\dots$ 的有限树逐步取 max 再用可数极限聚合, 最小不动点换成 $\omega$ 次迭代的极限. 它确实不碰定理 1: 没有三歧就没有 LPO. 但它的 $\Omega$-索引极限坍缩只访问一条固定的、与具体极限无关的 $\mathbb{N}$-序列, 所以它并未越出 `Higher`/`HigherGen` 的编码方式, 反而少了选择序列的自由. 需要更正该探针文档及本项目此前讨论中的措辞: "强度 $\le\psi(\Omega_\Omega)$、与 BTBO 相当"是非形式上界, "判定每次提取 $\log 3$ 比特信息而算律将其抹除"是启发式比喻, 二者都不是定理, "算律折叠强度严格更弱"也不是已证的不等式. 按原型的构造看其实际强度应远低于 BTBO, 但没有人计算过. 本文能负责的陈述只有: 不派发的折叠不超出单一 $\mathbb{N}$-序列编码所能到达的范围, 这是结构性观察.
2. 精确性假设之外的设计 (让 $\iota(\mathsf{lim}\,f)$ 不是其各项的精确上确界的"肥"序) 不被定理 1 覆盖. 元理论上它们也不可定义 (任何可定义的比较函数在基本列上连续, 而把 $\omega$ 塞进第 $k$ 项的序列族 $k\mapsto\mathsf{sw}_{\alpha_k}$ 的比较结果在 $k\to\infty$ 时不连续), 但这个论证不能在 Agda 内部进行, 本文不把它算作结果.
3. 关于序数**强度**的论断 ($\psi(\Omega_{\Omega+\omega})$、$\psi(\Omega_{\Omega^\Omega})$ 等估计) 仍是非形式的. 本文只形式化了结构性的壁垒.

**定理覆盖哪些探针.** 定理 1 的 $\top$ 要位于整个嵌入像 $\iota(\mathsf{Ord}^\mathsf{D})$ 之上. 以 $\mathsf{Ord}^\mathsf{D}$ 为 $\mathsf{lim}_1$ 下标的设计 (`Ord1D/SpikeA2`, 即上节的朴素 $\mathsf{Ord}_1$) 直接提供这样的 $\top$, 被定理覆盖. Kovacs 风格的 IR 宇宙分层 (`Kovacs/Base2`) 以低一层的单调序列树为 `Lim` 的下标, 其 `<ᵁ` 有 `Lim*` 规则, 升层映射精确, 本文的论证可以逐字搬到那里; 该探针记下的 "unbounded trichotomy on U' i" 墙就是定理 1 的结论. 而以原始 $\mathsf{Ord}_0$ (无单调性约束) 为下标的设计 (`Ord1D/SpikeA1`, `AlphaDec/IR`) **不**被覆盖: 那里找不到位于 $\iota(\mathsf{Ord}^\mathsf{D})$ 之上的元素. $\mathsf{lim}_1(f)$ 只在 $f$ 的像之上, 而 $f:\mathsf{Ord}_0\to I$ 无法从原始树重建 $\mathsf{lim}$ 所需的单调性证明; 前篇的单调化 $\mathsf{ord}^\mathsf{D}$ 也不保持原始的 $<_0$, 因为累积和把 $f(n+1)$ 放在加法右侧, 极限不再是子项. 换言之这些设计的 $\mathsf{lim}_1$ 并未在 $\mathsf{Ord}^\mathsf{D}$ 之上提供共尾度 $\Omega$ 的元素, 它们停在定理 1 的上游: 不是"有 $\Omega$-共尾元就不能三歧", 而是"喂不进一个既单调又精确的下标族". 这一点本文没有形式化, 只作为观察记录.

## 参考

- Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu, *Type-Theoretic Approaches to Ordinals*, Theoretical Computer Science 2023. [arXiv:2208.03844](https://arxiv.org/abs/2208.03844). Section 6.6: Theorem 48 ($\mathsf{Brw}$ 上 $<,\le,=$ 可判定 $\iff$ LPO), Theorem 53 ($\mathsf{Brw}$ 三歧 $\iff$ LPO), Lemma 47 (二进制序列到 $\mathsf{Brw}$ 的翻译).
- Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu, *Connecting Constructive Notions of Ordinals in Homotopy Type Theory*, MFCS 2021. [arXiv:2104.02549](https://arxiv.org/abs/2104.02549).
- Tom de Jong, Nicolai Kraus, Aref Mohammadzadeh, Fredrik Nordvall Forsberg, *Generalized Decidability via Brouwer Trees*, LICS 2026. [arXiv:2602.10844](https://arxiv.org/abs/2602.10844). (探针文档中的 "de Jong-Eremondi-Forsberg 2026" 应指此文与上面的 TCS 文章; 该作者组合不存在.)
- Anton Setzer, *An introduction to well-ordering proofs in Martin-Löf's type theory*, 1998.
