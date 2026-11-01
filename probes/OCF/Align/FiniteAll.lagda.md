# EBO 对齐 (三): 全部有限下标

> 交替路线的第三步, 接 [Finite](Finite.lagda.md) 与 [Omega1](Omega1.lagda.md). Omega1 用自定义的两层树把对应定理推到下标 $\le 1$ (Bachmann–Howard 序数). 本篇推到**全部自然数下标** $\psi_\nu$ ($\nu<\omega$, 片段极限 $\psi_0(\Omega_\omega)$, 即 Buchholz 序数), 并且回到 **BTBO 自己的树类型** `Ord (nat n)`, 折叠用 Finite §3 的 `ψᴱ`, 嵌入照抄 Finite §4 的 `emb`.
>
> 结果: 对**每个**镜像项 $t$ (不加任何前提), 嵌入 `emb t` 的形状由句法 `cof t` 决定, 四种共尾度 $0$, 后继, $\omega$, $\Omega_{\mu+1}$ ($\mu$ 任意) 全部证完 (`corr`); 推论是树上的 FGH 满足表记沿 `pred`/`fs` 的递归方程 (`FGH-c1`, `FGH-cω`), 以及在任意层级 $n\ge\mathsf{lv}\,t$ 上的 $\Omega$-基本列对应 (`Ω-corr`). 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示.
>
> 技术核心只有一个: **跨层级的外延相等** $a\approx b$ ($a:\mathsf{Ord}\,\ell_1$, $b:\mathsf{Ord}\,\ell_2$, 层级可以不同). 有了它, 层级提升 `↑`、`↑≤` 在 $\approx$ 下消失, `ψᴱ` 尊重 $\approx$ 与"提升后再折叠等于直接折叠"合成同一条引理, 定理的陈述里不出现任何层级簿记.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FiniteAll where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst; subst₂)

open import OCF.BTBO using (module Trich; module BoundedTrich; module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Barrier using (nat)
open Trich renaming (_<_ to _<ᴺ_) using (zero; suc)
open BoundedTrich using (Ordᴰ; zero; suc; lim; _<_; <-trans; <-dec)
open Ord-Ord using (Ord<; Ord; Ord₀; zero; suc; lim; limᵢ; coe; coe₀; ↑; _+_; iter; FGH)
open import OCF.Align.Finite using (_≤ᴺ_; ≤-refl; ≤-step; ≤⊔ˡ; ≤⊔ʳ; ↑≤; <≤; nat<; Ωᴱ; ψᴱ; iter-ext)
```

## §1 树类型的选择

纲领允许不用 BTBO 的 `Ord ℓ`. 动笔前比较了三种全有限层级的树族 (各写了一个最小文件编译通过):

| 方案 | `limᵢ` 的定义域 | 结论 |
|---|---|---|
| (A) BTBO 的 `Ord (nat n)`: 对证明 $p:i<\ell$ 递归的归纳-递归族 `Ord< i p` | `Ord< j p`, 只在 $p$ 为闭项时定义性地等于 `Ord j` | **采用** |
| (B) 同构造限制到 $\mathbb{N}$: `O₊ n O<`, `O< j p` 对 $p:j<n$ 递归 | 同 (A): 变量证明下卡住 | 与 (A) 同病, 且失去与 BTBO 的同一性 |
| (C) Omega1 结论里的表格式: `Tr k (D : Fin k → Set)`, `Ob n = Tr n (Ds n)`, `Ds (suc n) zero = Ob n` | `Ds n j`, 变量 `j` 下卡在查表 | 同样需要搬运引理, 还多一层 `Fin` 与 $\mathbb{N}$ 层级的换算 |

三者的共同点是: 定理对**变量**层级陈述时, `limᵢ` 的定义域都不会定义性地归约成较低层的树类型. 这不是工程问题而是正性的代价: `data O : ℕ → Set` 带 `limᵢ : (O j → O n) → O n` 不严格正, 任何可接受的写法都要让定义域经由某个对层级 (或其证明) 的递归计算出来, 于是变量层级下必然卡住. 既然搬运 (`coe`) 不可避免, (A) 就没有劣势, 而它多一个好处: 定理认证的就是 BTBO 文件里的树类型 `Ord`, 与 Finite 的 `ψᴱ`/`emb` 原样组合, 以后认证 BTBO 自己的树 (或 BTBOFix 的补丁版) 不需要桥.

采用的树类型 (BTBO 原文, 逐字):

    module _ (ℓ : Ordᴰ) (Ord< : (i : Ordᴰ) (p : i < ℓ) → Set) where
      data Ord₊ : Set where
        zero  : Ord₊
        suc   : Ord₊ → Ord₊
        lim   : (f : ℕ → Ord₊) → Ord₊
        limᵢ  : (p : i < ℓ) (f : Ord< i p → Ord₊) → Ord₊

    Ord< : (i : Ordᴰ) (p : i < ℓ) → Set
    Ord< i zero      = Ord₊ i Ord<
    Ord< i (suc p)   = Ord< i p
    Ord< i (lim n p) = Ord< i p

    Ord : Ordᴰ → Set
    Ord ℓ = Ord< ℓ zero

`coe` 的处理方式: 凡是函数 `f : Ord< j p → _` 都只在 `coe₀ x` ($x:\mathsf{Ord}\,j$) 处取值; 唯一需要的搬运事实是 `coe-coe₀` (两次搬运合成一次), 对证明归纳得到 (无 K, 不用 UIP), 在结论上用 `subst` 改写, 从不在递归调用的参数上改写 (那会破坏结构递降).

## §2 层级的两条基本事实

**无自反.** 层级上的 $<$ 是良基的 (对 $a$ 结构归纳构造 `Acc`), 所以 $a<a$ 不可能. 这条用于排除 `ψᴱ` 的 `<-dec` 派发中互相矛盾的分支 (例如一边 $j<i$, 另一边 $i<j$), 对一切 `Ordᴰ` 成立, 不限于自然数层级.

```agda
data Acc (a : Ordᴰ) : Set where
  acc : (∀ {b} → b < a → Acc b) → Acc a

acc< : ∀ a {b} → b < a → Acc b
acc< (suc a)   zero      = acc (acc< a)
acc< (suc a)   (suc p)   = acc< a p
acc< (lim f m) (lim n p) = acc< (f n) p

<-irrefl : ∀ {a} → a < a → ⊥
<-irrefl {a} = go (acc (acc< a)) where
  go : ∀ {a} → Acc a → a < a → ⊥
  go (acc h) p = go (h p) p
```

**搬运合成.** `coe {p = r} {q = q} (coe₀ {p = r} x) ≡ coe₀ {p = q} x`. 对两个证明逐层剥: 每一步两边都定义性地剥掉同一层 (`Ord<-≡` 的子句顺序保证了这一点).

```agda
coe-coe₀ : ∀ {j ℓ₁ ℓ₂} (r : j < ℓ₁) (q : j < ℓ₂) (x : Ord j) →
           coe {p = r} {q = q} (coe₀ {p = r} x) ≡ coe₀ {p = q} x
coe-coe₀ zero      q         x = refl
coe-coe₀ (suc r)   zero      x = coe-coe₀ r zero x
coe-coe₀ (suc r)   (suc q)   x = coe-coe₀ (suc r) q x
coe-coe₀ (suc r)   (lim n q) x = coe-coe₀ (suc r) q x
coe-coe₀ (lim m r) zero      x = coe-coe₀ r zero x
coe-coe₀ (lim m r) (suc q)   x = coe-coe₀ (lim m r) q x
coe-coe₀ (lim m r) (lim n q) x = coe-coe₀ (lim m r) q x
```

## §3 跨层级外延相等

Omega1 的 $\approx$ 把较低层的关系作为参数 `R` 传入, 只有两层. 推广到全部层级时, 较低层的关系本身就是"较低层的 $\approx$", 不能直接写进构造子 (负出现). 解法与 BTBO 定义 `Ord<` 完全相同: 把较低层关系 `R< i p` 作为参数, 再**对证明 $p:i<\ell$ 递归**地把它定义为第 $i$ 层的 $\approx$. 停机检查器在 `R< i zero = Eq₊ i R<` 处看到隐式层级从 $i^+$ 降到 $i$.

关系是**异层**的: 左边在 $\ell$ 层, 右边在任意 $\ell'$ 层; `limᵢ` 的条件要求两边的指标层级 $i$ 相同 (证明可以不同), 并用强条件 (Omega1 §3): $x\approx y$ 蕴含 $f(x)\approx g(y)$. 它是部分等价关系, 自反元素就是遗传外延的树.

```agda
module _ (ℓ : Ordᴰ) (R< : (i : Ordᴰ) → i < ℓ → Ord i → Ord i → Set) where
  data Eq₊ : ∀ {ℓ′} → Ord ℓ → Ord ℓ′ → Set where
    z≈ : ∀ {ℓ′} → Eq₊ {ℓ′} zero zero
    s≈ : ∀ {ℓ′} {a : Ord ℓ} {b : Ord ℓ′} → Eq₊ a b → Eq₊ (suc a) (suc b)
    l≈ : ∀ {ℓ′} {f : ℕ → Ord ℓ} {g : ℕ → Ord ℓ′} → (∀ n → Eq₊ (f n) (g n)) → Eq₊ (lim f) (lim g)
    lᵢ≈ : ∀ {ℓ′ i} {p : i < ℓ} {q : i < ℓ′} {f : Ord< i p → Ord ℓ} {g : Ord< i q → Ord ℓ′} →
          (∀ x y → R< i p x y → Eq₊ (f (coe₀ x)) (g (coe₀ y))) → Eq₊ (limᵢ p f) (limᵢ q g)

R< : ∀ {ℓ} (i : Ordᴰ) → i < ℓ → Ord i → Ord i → Set
R< i zero      = Eq₊ i R<
R< i (suc p)   = R< i p
R< i (lim n p) = R< i p

infix 4 _≈_
_≈_ : ∀ {ℓ₁ ℓ₂} → Ord ℓ₁ → Ord ℓ₂ → Set
_≈_ {ℓ₁} = Eq₊ ℓ₁ R<
```

`R<` 与 $\approx$ 互相转换 (对证明归纳, 每一步定义性地展开). 对称与传递对**一切**树成立: `limᵢ` 情况要用第 $i$ 层的对称/传递 (传递还要 $y\approx y$, 由 $x\approx y$ 经 PER 得到), 所以 `≈-sym`/`≈-trans` 与对证明递归的 `R<-sym`/`R<-trans` 互递归; 每绕一圈, 隐式层级严格下降, 停机检查器直接接受 (无需燃料参数).

```agda
R<-conv : ∀ {i ℓ₁ ℓ₂} (p : i < ℓ₁) (q : i < ℓ₂) {x y : Ord i} → R< i p x y → R< i q x y
R<-conv zero      zero      r = r
R<-conv zero      (suc q)   r = R<-conv zero q r
R<-conv zero      (lim n q) r = R<-conv zero q r
R<-conv (suc p)   q         r = R<-conv p q r
R<-conv (lim n p) q         r = R<-conv p q r

≈→R< : ∀ {i ℓ} (p : i < ℓ) {x y : Ord i} → x ≈ y → R< i p x y
≈→R< p = R<-conv zero p

R<→≈ : ∀ {i ℓ} (p : i < ℓ) {x y : Ord i} → R< i p x y → x ≈ y
R<→≈ p = R<-conv p zero

≈-sym  : ∀ {ℓ₁ ℓ₂} {a : Ord ℓ₁} {b : Ord ℓ₂} → a ≈ b → b ≈ a
R<-sym : ∀ {i ℓ} (p : i < ℓ) {x y : Ord i} → R< i p x y → R< i p y x
≈-sym z≈      = z≈
≈-sym (s≈ e)  = s≈ (≈-sym e)
≈-sym (l≈ h)  = l≈ (λ n → ≈-sym (h n))
≈-sym (lᵢ≈ {p = p} {q = q} h) = lᵢ≈ (λ y x r → ≈-sym (h x y (R<-conv q p (R<-sym q r))))
R<-sym zero      r = ≈-sym r
R<-sym (suc p)   r = R<-sym p r
R<-sym (lim n p) r = R<-sym p r

≈-trans  : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : Ord ℓ₁} {b : Ord ℓ₂} {c : Ord ℓ₃} → a ≈ b → b ≈ c → a ≈ c
R<-trans : ∀ {i ℓ} (p : i < ℓ) {x y z : Ord i} → R< i p x y → R< i p y z → R< i p x z
≈-trans z≈     z≈      = z≈
≈-trans (s≈ e) (s≈ e′) = s≈ (≈-trans e e′)
≈-trans (l≈ h) (l≈ h′) = l≈ (λ n → ≈-trans (h n) (h′ n))
≈-trans (lᵢ≈ {p = p} {q = q} h) (lᵢ≈ h′) =
  lᵢ≈ (λ x z r → ≈-trans (h x z r) (h′ z z (R<-conv p q (R<-trans p (R<-sym p r) r))))
R<-trans zero      r r′ = ≈-trans r r′
R<-trans (suc p)   r r′ = R<-trans p r r′
R<-trans (lim n p) r r′ = R<-trans p r r′
```

## §4 树上运算尊重 $\approx$

提升 `↑` 在 $\approx$ 下消失 (`↑ˡ`/`↑ʳ`: $a\approx b\Rightarrow{\uparrow}a\approx b$), 于是 Finite 的 `↑≤` 也消失. 这一条替代了 Omega1 的 `↑-emb` 与"提升与加法交换"等全部层级簿记.

```agda
≈-reflˡ : ∀ {ℓ₁ ℓ₂} {a : Ord ℓ₁} {b : Ord ℓ₂} → a ≈ b → a ≈ a
≈-reflˡ e = ≈-trans e (≈-sym e)

≈-reflʳ : ∀ {ℓ₁ ℓ₂} {a : Ord ℓ₁} {b : Ord ℓ₂} → a ≈ b → b ≈ b
≈-reflʳ e = ≈-trans (≈-sym e) e
↑ˡ : ∀ {ℓ₁ ℓ₁′ ℓ₂} {r : ℓ₁ < ℓ₁′} {a : Ord ℓ₁} {b : Ord ℓ₂} → a ≈ b → ↑ r a ≈ b
↑ˡ z≈     = z≈
↑ˡ (s≈ e) = s≈ (↑ˡ e)
↑ˡ (l≈ h) = l≈ (λ n → ↑ˡ (h n))
↑ˡ {r = r} (lᵢ≈ {p = q} {f = f} {g = g} h) = lᵢ≈ λ x y e →
  subst (λ z → ↑ r (f z) ≈ g (coe₀ y)) (sym (coe-coe₀ (<-trans q r) q x))
        (↑ˡ (h x y (R<-conv (<-trans q r) q e)))

↑ʳ : ∀ {ℓ₁ ℓ₂ ℓ₂′} {r : ℓ₂ < ℓ₂′} {a : Ord ℓ₁} {b : Ord ℓ₂} → a ≈ b → a ≈ ↑ r b
↑ʳ e = ≈-sym (↑ˡ (≈-sym e))

↑≤ˡ : ∀ {m n ℓ} (h : m ≤ᴺ n) {a : Ord (nat m)} {b : Ord ℓ} → a ≈ b → ↑≤ h a ≈ b
↑≤ˡ ≤-refl     e = e
↑≤ˡ (≤-step h) e = ↑ˡ (↑≤ˡ h e)

↑≤ʳ : ∀ {m n ℓ} (h : m ≤ᴺ n) {a : Ord ℓ} {b : Ord (nat m)} → a ≈ b → a ≈ ↑≤ h b
↑≤ʳ h e = ≈-sym (↑≤ˡ h (≈-sym e))
```

加法、迭代 (对任意关系)、$\Omega^\mathsf{E}$ 的自反:

```agda
+-≈ : ∀ {ℓ₁ ℓ₂} {a c : Ord ℓ₁} {b d : Ord ℓ₂} → a ≈ b → c ≈ d → a + c ≈ b + d
+-≈ e z≈      = e
+-≈ e (s≈ e′) = s≈ (+-≈ e e′)
+-≈ e (l≈ h)  = l≈ (λ n → +-≈ e (h n))
+-≈ e (lᵢ≈ h) = lᵢ≈ (λ x y r → +-≈ e (h x y r))

iter-R : ∀ {A B : Set} (R : A → B → Set) {G : A → A} {G′ : B → B} →
         (∀ {x y} → R x y → R (G x) (G′ y)) → ∀ {x y} → R x y → ∀ n → R (iter G x n) (iter G′ y n)
iter-R R h e zero    = e
iter-R R h e (suc n) = h (iter-R R h e n)
Ωᴱ-refl : ∀ ℓ → Ωᴱ ℓ ≈ Ωᴱ ℓ
Ωᴱ-refl zero      = s≈ z≈
Ωᴱ-refl (suc ℓ)   = lᵢ≈ (λ x y e → ↑ˡ (↑ʳ e))
Ωᴱ-refl (lim f m) = l≈ (λ n → ↑ˡ (↑ʳ (Ωᴱ-refl (f n))))
```

**`ψᴱ` 尊重 $\approx$ (异层版).** $a\approx b$ ($a$ 在 $\ell_1$ 层, $b$ 在 $\ell_2$ 层) 蕴含 $\psi^\mathsf{E}_p\,a\approx\psi^\mathsf{E}_{p'}\,b$, 只要目标层级 $i$ 相同. 取 $\ell_1=\ell_2$ 是通常的"折叠尊重外延相等"; 取 $a={\uparrow}b$ 是"提升后再折叠等于直接折叠". `limᵢ` 情况对两边的 `<-dec` 同时分情况: 同为穿透 (规则 5Ω) 时逐点用强条件; 同为折叠 (规则 6, `injᵇ`/`injᶜ` 两个分支是同一个表达式) 时两条 $\gamma$-链逐项相关 (`iter-R`); 一穿透一折叠的四种组合由无自反排除.

```agda
ψᴱ-≈ : ∀ {i ℓ₁ ℓ₂} {p : i < ℓ₁} {p′ : i < ℓ₂} {a : Ord ℓ₁} {b : Ord ℓ₂} → a ≈ b → ψᴱ p a ≈ ψᴱ p′ b
ψᴱ-≈ {i} z≈ = Ωᴱ-refl i
ψᴱ-≈ (s≈ e) = l≈ (iter-R _≈_ (λ e′ → +-≈ (ψᴱ-≈ e) e′) z≈)
ψᴱ-≈ (l≈ h) = l≈ (λ n → ψᴱ-≈ (h n))
ψᴱ-≈ {p = p} {p′ = p′} (lᵢ≈ {i = j} {p = q} {q = q′} {f = f} {g = g} h)
  with <-dec q p | <-dec q′ p′
... | injᵃ r | injᵃ r′ = lᵢ≈ λ x y e →
  subst₂ (λ u v → ψᴱ p (f u) ≈ ψᴱ p′ (g v)) (sym (coe-coe₀ r q x)) (sym (coe-coe₀ r′ q′ y))
         (ψᴱ-≈ (h x y (R<-conv r q e)))
... | injᵃ r | injᵇ s  = ⊥-elim (<-irrefl (<-trans r s))
... | injᵃ r | injᶜ e  = ⊥-elim (<-irrefl (subst (j <_) (sym e) r))
... | injᵇ s | injᵃ r  = ⊥-elim (<-irrefl (<-trans r s))
... | injᶜ e | injᵃ r  = ⊥-elim (<-irrefl (subst (j <_) (sym e) r))
... | injᵇ _ | injᵇ _  = l≈ (λ n → ψᴱ-≈ (h _ _ (chain n)))
  where chain = iter-R (R< j q) (λ e → ≈→R< q (ψᴱ-≈ (h _ _ e))) (≈→R< q (Ωᴱ-refl j))
... | injᵇ _ | injᶜ _  = l≈ (λ n → ψᴱ-≈ (h _ _ (chain n)))
  where chain = iter-R (R< j q) (λ e → ≈→R< q (ψᴱ-≈ (h _ _ e))) (≈→R< q (Ωᴱ-refl j))
... | injᶜ _ | injᵇ _  = l≈ (λ n → ψᴱ-≈ (h _ _ (chain n)))
  where chain = iter-R (R< j q) (λ e → ≈→R< q (ψᴱ-≈ (h _ _ e))) (≈→R< q (Ωᴱ-refl j))
... | injᶜ _ | injᶜ _  = l≈ (λ n → ψᴱ-≈ (h _ _ (chain n)))
  where chain = iter-R (R< j q) (λ e → ≈→R< q (ψᴱ-≈ (h _ _ e))) (≈→R< q (Ωᴱ-refl j))
```

## §5 镜像表记与嵌入

表记**导入** Omega1 §4 (全部自然数下标的 `cof`/`pred`/`fsΩ`/`γ`/`fs`, 逐条抄自 EBO). 嵌入 `emb` 与 Finite §4 逐字相同, 只是建立在 Omega1 的项类型上 (Finite 与 Omega1 各自定义了同构的 `T`, Finite 的 `emb` 不能直接复用). 为了在证明里点名, 把 $\psi_u(a)$ 的折叠证明与提升后的参数命名为 `pψ`/`argψ`; 层级 `lv` 只看顶层下标.

```agda
open import OCF.Align.Omega1 using (P; T; ψ; natT; Cmp; lt; eq; gt; cmp; Cof; c0; c1; cω; cΩ;
  cofψ₊; cofA; cof; cofP; pred; fsΩ; fsΩ₊; fsΩc; γ; rep; fs; fsn; fsn₊; fsnc; cof-ne;
  Top₀; t[]; t∷; Top₀-pred; Top₀-fs; agree; allAgree)

lv  : T → ℕ
lvP : P → ℕ
lv []               = zero
lv (x ∷ [])         = lvP x
lv (x ∷ xs@(_ ∷ _)) = lvP x ⊔ lv xs
lvP (ψ u a)         = u

emb  : (t : T) → Ord (nat (lv t))
embP : (x : P) → Ord (nat (lvP x))
pψ   : ∀ u a → nat u < nat (lv a ⊔ suc u)
argψ : ∀ u a → Ord (nat (lv a ⊔ suc u))
emb []               = zero
emb (x ∷ [])         = embP x
emb (x ∷ xs@(_ ∷ _)) = ↑≤ (≤⊔ˡ (lvP x) (lv xs)) (embP x) + ↑≤ (≤⊔ʳ (lvP x) (lv xs)) (emb xs)
embP (ψ u a) = ψᴱ (pψ u a) (argψ u a)

pψ u a   = nat< (<≤ zero (≤⊔ʳ (lv a) (suc u)))
argψ u a = ↑≤ (≤⊔ˡ (lv a) (suc u)) (emb a)
```

每个嵌入的树都在 PER 的定义域里 (对任意项, 无前提):

```agda
emb-refl  : ∀ t → emb t ≈ emb t
embP-refl : ∀ x → embP x ≈ embP x
emb-refl []               = z≈
emb-refl (x ∷ [])         = embP-refl x
emb-refl (x ∷ xs@(_ ∷ _)) = +-≈ (↑≤ˡ _ (↑≤ʳ _ (embP-refl x))) (↑≤ˡ _ (↑≤ʳ _ (emb-refl xs)))
embP-refl (ψ u a) = ψᴱ-≈ (↑≤ˡ _ (↑≤ʳ _ (emb-refl a)))
```

## §6 形状与形状的不变性

**反演.** $Y\approx\mathsf{suc}\,Z$ 时 $Y$ 本身 (在自己的层级上) $\approx$ 某个 $\mathsf{suc}\,Y'$; `lim`、`limᵢ` 同理. 这让形状可以从一个层级搬到另一个层级.

```agda
s-inv : ∀ {ℓ₁ ℓ₂} {Y : Ord ℓ₁} {Z : Ord ℓ₂} → Y ≈ suc Z → Σ (Ord ℓ₁) λ Y′ → (Y ≈ suc Y′) × (Y′ ≈ Z)
s-inv (s≈ e) = _ , s≈ (≈-reflˡ e) , e

l-inv : ∀ {ℓ₁ ℓ₂} {Y : Ord ℓ₁} {G : ℕ → Ord ℓ₂} → Y ≈ lim G →
        Σ (ℕ → Ord ℓ₁) λ F → (Y ≈ lim F) × (∀ n → F n ≈ G n)
l-inv (l≈ h) = _ , l≈ (λ n → ≈-reflˡ (h n)) , h

lᵢ-inv : ∀ {ℓ₁ ℓ₂ i} {Y : Ord ℓ₁} {q : i < ℓ₂} {G : Ord< i q → Ord ℓ₂} → Y ≈ limᵢ q G →
         Σ (i < ℓ₁) λ q′ → Σ (Ord< i q′ → Ord ℓ₁) λ F →
         (Y ≈ limᵢ q′ F) × (∀ x y → x ≈ y → F (coe₀ x) ≈ G (coe₀ y))
lᵢ-inv (lᵢ≈ {p = q′} {f = F} h) = q′ , F ,
  lᵢ≈ (λ x y r → ≈-trans (h x y r) (≈-sym (h y y (R<-trans q′ (R<-sym q′ r) r)))) ,
  λ x y e → h x y (≈→R< q′ e)
```

**形状.** 嵌入 $X$ (在 $\ell$ 层) 的形状由共尾度决定:

| `cof t` | `Sh X …` |
|---|---|
| `c0` | $X\approx 0$ |
| `c1` | $X\approx(\mathsf{emb}(\mathsf{pred}\,t))^+$ |
| `cω` | $\exists F.\ X\approx\lim F$ 且 $\forall n.\ F\,n\approx\mathsf{emb}(t[n])$ |
| `cΩ μ` | $\exists q{:}\mu<\ell,\,F.\ X\approx\lim_i(q,F)$ 且 $\forall\eta\,x.\ x\approx\mathsf{emb}\,\eta\Rightarrow F(x)\approx\mathsf{emb}(t[\eta])$ |

$\omega$ 与 $\Omega$ 两行用存在量词而不是直接写 $\lim(n\mapsto\mathsf{emb}(t[n]))$, 因为 $t[n]$ 的层级随 $n$ 变, 不能放进同一个 `lim`; 而有了异层 $\approx$, 存在的 $F$ 与嵌入逐点相关就是同一回事. $\Omega$ 行对 $\eta$ **不加任何条件**: 只要求喂给 $F$ 的树 $x$ 与 $\mathsf{emb}\,\eta$ 相关; 任务要求的形式 (第 $\mu$ 层的 $\mathsf{emb}\,\eta$, $\mathsf{lv}\,\eta\le\mu$) 是特例 (§9 `Ω-corr`).

```agda
𝟎 : Ord₀
𝟎 = zero

Sh : ∀ {ℓ} → Ord ℓ → Cof → T → (ℕ → T) → (T → T) → Set
Sh     X c0     p s g = X ≈ 𝟎
Sh     X c1     p s g = X ≈ suc (emb p)
Sh {ℓ} X cω     p s g = Σ (ℕ → Ord ℓ) λ F → (X ≈ lim F) × (∀ n → F n ≈ emb (s n))
Sh {ℓ} X (cΩ μ) p s g = Σ (nat μ < ℓ) λ q → Σ (Ord< (nat μ) q → Ord ℓ) λ F →
                        (X ≈ limᵢ q F) × (∀ η x → x ≈ emb η → F (coe₀ x) ≈ emb (g η))
Shape : T → Set
Shape t = Sh (emb t) (cof t) (pred t) (fs t) (fsΩ t)
```

**形状在 $\approx$ 下不变** (对任意两个层级). 这是"层级 $n\ge\mathsf{lv}\,t$ 上的形状"与"参数提升到折叠层级之后的形状"的共同来源.

```agda
Sh-resp : ∀ {ℓ₁ ℓ₂} {X : Ord ℓ₁} {Y : Ord ℓ₂} c {p s g} → X ≈ Y → Sh X c p s g → Sh Y c p s g
Sh-resp c0 e sh = ≈-trans (≈-sym e) sh
Sh-resp c1 e sh = ≈-trans (≈-sym e) sh
Sh-resp cω e (F , eF , hF) with l-inv (≈-trans (≈-sym e) eF)
... | F′ , eF′ , hF′ = F′ , eF′ , λ n → ≈-trans (hF′ n) (hF n)
Sh-resp (cΩ μ) e (q , F , eF , hF) with lᵢ-inv (≈-trans (≈-sym e) eF)
... | q′ , F′ , eF′ , hF′ = q′ , F′ , eF′ , λ η x ex → ≈-trans (hF′ x x (≈-reflˡ ex)) (hF η x ex)
```

## §7 派发引理

自然数比较与层级派发的对应: `cmp (suc ν) u` 为 `lt`/`eq` 时 $\nu<u$, 为 `gt` 时 $u\le\nu$.

```agda
<→≤ : ∀ {u ν} → u <ᴺ ν → u ≤ᴺ ν
<→≤ zero    = ≤-step ≤-refl
<→≤ (suc p) = ≤-step (<→≤ p)

≤nat< : ∀ {u ν ℓ} → u ≤ᴺ ν → nat ν < ℓ → nat u < ℓ
≤nat< ≤-refl     q = q
≤nat< (≤-step h) q = ≤nat< h (<-trans zero q)

s<→< : ∀ {m n} → suc m <ᴺ n → m <ᴺ n
s<→< zero    = suc zero
s<→< (suc p) = suc (s<→< p)

cmp-lt : ∀ m n → cmp m n ≡ lt → m <ᴺ n
cmp-lt zero    (suc n) e = Trich.z<s n
cmp-lt (suc m) (suc n) e = Trich.s<s (cmp-lt m n e)

cmp-eq : ∀ m n → cmp m n ≡ eq → m ≡ n
cmp-eq zero    zero    e = refl
cmp-eq (suc m) (suc n) e = cong suc (cmp-eq m n e)

cmp-gt : ∀ m n → cmp m n ≡ gt → n <ᴺ m
cmp-gt (suc m) zero    e = Trich.z<s m
cmp-gt (suc m) (suc n) e = Trich.s<s (cmp-gt m n e)

<suc→≤ : ∀ {u ν} → u <ᴺ suc ν → u ≤ᴺ ν
<suc→≤ zero    = ≤-refl
<suc→≤ (suc p) = <→≤ p
```

`ψᴱ` 在 `limᵢ` 节点上的两种行为. $\nu<u$ 时必走穿透 (`pen`, 规则 5Ω), $u\le\nu$ 时必走 $\gamma$-链 (`coll`, 规则 6, $\gamma_0=\Omega^\mathsf{E}_\nu$, 每步经到共尾层 $\nu$ 的直接折叠 `ψᴱ q`). 证明对 `<-dec q p` 做 `with`, 同时把 `ψᴱ-≈ ext` 一并抽象, 在正确的分支里它就是所需的结论; 错误分支由无自反排除.

```agda
pen : ∀ {ℓ ν u} (q : nat ν < ℓ) (p : nat u < ℓ) {F : Ord< (nat ν) q → Ord ℓ} →
      limᵢ q F ≈ limᵢ q F → ν <ᴺ u →
      Σ (nat ν < nat u) λ r → ψᴱ p (limᵢ q F) ≈ limᵢ r (ψᴱ p ∘ F ∘ coe)
pen q p ext νu with <-dec q p | ψᴱ-≈ {p = p} {p′ = p} ext
... | injᵃ r | e = r , e
... | injᵇ s | _ = ⊥-elim (<-irrefl (<-trans s (nat< νu)))
... | injᶜ e | _ = ⊥-elim (<-irrefl (subst (_< _) e (nat< νu)))

coll : ∀ {ℓ ν u} (q : nat ν < ℓ) (p : nat u < ℓ) {F : Ord< (nat ν) q → Ord ℓ} →
       limᵢ q F ≈ limᵢ q F → u ≤ᴺ ν →
       ψᴱ p (limᵢ q F) ≈ lim (λ n → ψᴱ p (F (coe₀ (iter (ψᴱ q ∘ F ∘ coe₀) (Ωᴱ (nat ν)) n))))
coll q p ext uν with <-dec q p | ψᴱ-≈ {p = p} {p′ = p} ext
... | injᵃ r | _ = ⊥-elim (<-irrefl (≤nat< uν r))
... | injᵇ _ | e = e
... | injᶜ _ | e = e
```

## §8 对应定理

辅助: 和的嵌入 (`emb-∷`, 处理单元素和的特殊子句), 规则 4 的 `rep`, 以及"参数相关则折叠相关" (`ψ-arg`, 即 `ψᴱ-≈` 加一次 `↑≤`).

```agda
emb-∷ : ∀ x zs {ℓ} {A Z : Ord ℓ} → A ≈ embP x → Z ≈ emb zs → A + Z ≈ emb (x ∷ zs)
emb-∷ x []         eA z≈ = eA
emb-∷ x zs@(_ ∷ _) eA eZ = +-≈ (≈-trans eA (↑≤ʳ _ (embP-refl x))) (≈-trans eZ (↑≤ʳ _ (emb-refl zs)))

rep≈ : ∀ u a {ℓ} {c : Ord ℓ} → c ≈ embP (ψ u a) → ∀ n → iter (c +_) zero n ≈ emb (rep u a n)
rep≈ u a e zero    = z≈
rep≈ u a e (suc n) = emb-∷ (ψ u a) (rep u a n) e (rep≈ u a e n)

-- ψ_u 作用在 "参数嵌入 ≈ 某棵树 Y" 上: 结果 ≈ embP (ψ u a)
ψ-arg : ∀ u a {ℓ} {p : nat u < ℓ} {Y : Ord ℓ} → Y ≈ emb a → ψᴱ p Y ≈ embP (ψ u a)
ψ-arg u a e = ψᴱ-≈ (↑≤ʳ _ e)
```

**规则 6 的链引理.** 若 $F$ 在嵌入的项上就是 $b[\cdot]$, 则树的 $\gamma$-链逐项 $\approx$ 表记 $\gamma$-链的嵌入: $\gamma_0=\Omega^\mathsf{E}_\nu=\psi^\mathsf{E}_q(0)\approx\mathsf{emb}\,\Omega_\nu$; $\gamma_{k+1}=\psi^\mathsf{E}_q(F\,\gamma_k)\approx\psi_\nu(b[\gamma_k])$. 两边的 $\psi_\nu$ 来自不同层级的参数 (树这边是 `limᵢ` 节点所在层, 表记这边是 $\mathsf{lv}(b[\gamma_k])\sqcup(\nu+1)$), 由异层 `ψᴱ-≈` 直接接上.

```agda
chain : ∀ {ℓ ν} (q : nat ν < ℓ) {F : Ord< (nat ν) q → Ord ℓ} b →
        (∀ η x → x ≈ emb η → F (coe₀ x) ≈ emb (fsΩ b η)) →
        ∀ n → iter (ψᴱ q ∘ F ∘ coe₀) (Ωᴱ (nat ν)) n ≈ emb (γ b ν n)
chain {ℓ} {ν} q b hF zero    = ψᴱ-≈ {p = q} {a = Ord∋zero} (↑≤ʳ _ z≈)
  where Ord∋zero : Ord ℓ
        Ord∋zero = zero
chain {ν = ν} q {F} b hF (suc n) = ψ-arg ν (fsΩ b (γ b ν n)) (hF _ _ (chain q {F} b hF n))
```

**主项 $\psi_u(b)$, $b$ 的共尾度为 $\Omega_{\nu+1}$.** 按 `cmp (suc ν) u` 分三支: `lt`/`eq` 穿透, 新的 $F$ 是 $\psi_u\circ F$, 用 `coe-coe₀` 消去穿透分支里多出的一次搬运; `gt` 折叠, 第 $n$ 项是 $\psi_u(b[\gamma_n])$.

```agda
corrΩ : ∀ u b ν m → cmp (suc ν) u ≡ m → ∀ {ℓ} {p : nat u < ℓ} {A : Ord ℓ} →
        Sh A (cΩ ν) (pred b) (fs b) (fsΩ b) →
        Sh (ψᴱ p A) (cofψ₊ u ν m) (pred (ψ u b ∷ [])) (λ n → fsnc u b ν m n) (λ η → fsΩc u b ν m η)
corrΩ u b ν lt em {p = p} (q , F , eF , hF) with pen q p (≈-reflʳ eF) (s<→< (cmp-lt _ _ em))
... | r , e = r , (ψᴱ p ∘ F ∘ coe) , ≈-trans (ψᴱ-≈ eF) e , λ η x ex →
  subst (λ z → ψᴱ p (F z) ≈ _) (sym (coe-coe₀ r q x)) (ψ-arg u (fsΩ b η) (hF η x ex))
corrΩ u b ν eq em {p = p} (q , F , eF , hF) with pen q p (≈-reflʳ eF) (subst (ν <ᴺ_) (cmp-eq _ _ em) zero)
... | r , e = r , (ψᴱ p ∘ F ∘ coe) , ≈-trans (ψᴱ-≈ eF) e , λ η x ex →
  subst (λ z → ψᴱ p (F z) ≈ _) (sym (coe-coe₀ r q x)) (ψ-arg u (fsΩ b η) (hF η x ex))
corrΩ u b ν gt em {p = p} (q , F , eF , hF) =
  _ , ≈-trans (ψᴱ-≈ eF) (coll q p (≈-reflʳ eF) (<suc→≤ (cmp-gt _ _ em))) ,
  λ n → ψ-arg u (fsΩ b (γ b ν n)) (hF _ _ (chain q b hF n))
```

**主项 $\psi_u(b)$** 的其余情况: 先用 `Sh-resp` 把 $b$ 的形状搬到实际被折叠的树 `argψ u b` (提升到 $\mathsf{lv}\,b\sqcup(u+1)$ 层) 上, 使代表元与 `pψ u b` 同层. 后继走 `ψᴱ` 的 `suc` 分支 (规则 4, 与 `rep` 对应); $\omega$ 走 `lim` 分支 (规则 5ω).

```agda
shArg : ∀ u b c → Sh (emb b) c (pred b) (fs b) (fsΩ b) → Sh (argψ u b) c (pred b) (fs b) (fsΩ b)
shArg u b c = Sh-resp c (↑≤ʳ _ (emb-refl b))

corrψ : ∀ u y ys c → cof (y ∷ ys) ≡ c → Sh (emb (y ∷ ys)) c (pred (y ∷ ys)) (fs (y ∷ ys)) (fsΩ (y ∷ ys)) →
        Sh (embP (ψ u (y ∷ ys))) (cofA u c) (pred (ψ u (y ∷ ys) ∷ []))
           (λ n → fsn₊ u (y ∷ ys) c n) (λ η → fsΩ₊ u (y ∷ ys) c η)
corrψ u y ys c0 e sh = ⊥-elim (cof-ne y ys e)
corrψ u y ys c1 e sh with s-inv (shArg u (y ∷ ys) c1 sh)
... | A′ , eA , eA′ = iter (ψᴱ (pψ u (y ∷ ys)) A′ +_) zero ,
  ψᴱ-≈ {p = pψ u (y ∷ ys)} {p′ = pψ u (y ∷ ys)} eA , rep≈ u (pred (y ∷ ys)) (ψ-arg u _ eA′)
corrψ u y ys cω e sh with shArg u (y ∷ ys) cω sh
... | F , eF , hF = ψᴱ (pψ u (y ∷ ys)) ∘ F ,
  ψᴱ-≈ {p = pψ u (y ∷ ys)} {p′ = pψ u (y ∷ ys)} eF , λ n → ψ-arg u (fs (y ∷ ys) n) (hF n)
corrψ u y ys (cΩ ν) e sh =
  corrΩ u (y ∷ ys) ν (cmp (suc ν) u) refl (shArg u (y ∷ ys) (cΩ ν) sh)
```

**和** (规则 1): 树的 `a + suc b`, `a + lim f`, `a + limᵢ f` 与句法的 `pred`, `fs`, `fsΩ` 同步归约.

```agda
sum : ∀ x y ys c → cof (y ∷ ys) ≡ c → Sh (emb (y ∷ ys)) c (pred (y ∷ ys)) (fs (y ∷ ys)) (fsΩ (y ∷ ys)) →
      Sh (emb (x ∷ y ∷ ys)) c (pred (x ∷ y ∷ ys)) (fs (x ∷ y ∷ ys)) (fsΩ (x ∷ y ∷ ys))
sum x y ys c e sh = go c e (Sh-resp c (↑≤ʳ (≤⊔ʳ (lvP x) (lv (y ∷ ys))) (emb-refl (y ∷ ys))) sh) where
  A₁ = ↑≤ (≤⊔ˡ (lvP x) (lv (y ∷ ys))) (embP x)
  eA₁ : A₁ ≈ embP x
  eA₁ = ↑≤ˡ _ (embP-refl x)
  rA₁ = ≈-reflˡ eA₁
  go : ∀ c → cof (y ∷ ys) ≡ c → Sh (↑≤ (≤⊔ʳ (lvP x) (lv (y ∷ ys))) (emb (y ∷ ys))) c (pred (y ∷ ys)) (fs (y ∷ ys)) (fsΩ (y ∷ ys)) →
       Sh (emb (x ∷ y ∷ ys)) c (pred (x ∷ y ∷ ys)) (fs (x ∷ y ∷ ys)) (fsΩ (x ∷ y ∷ ys))
  go c0 e _ = ⊥-elim (cof-ne y ys e)
  go c1 e sh with s-inv sh
  ... | B′ , eB , eB′ = ≈-trans (+-≈ rA₁ eB) (s≈ (emb-∷ x (pred (y ∷ ys)) eA₁ eB′))
  go cω e (F , eF , hF) = (λ n → A₁ + F n) , +-≈ rA₁ eF , λ n → emb-∷ x (fs (y ∷ ys) n) eA₁ (hF n)
  go (cΩ μ) e (q , F , eF , hF) =
    q , (λ z → A₁ + F z) , +-≈ rA₁ eF , λ η z ez → emb-∷ x (fsΩ (y ∷ ys) η) eA₁ (hF η z ez)
```

**定理** 对**每个**项 $t$ (下标为任意自然数, 不要求标准形), `emb t` 的形状由 `cof t` 决定. 对项归纳; $\psi_0(0)=1$ 定义性地是 $0^+$; $\Omega_{\mu+1}=\psi_{\mu+1}(0)$ 取 $q=0_{\mu}:\mu<\mu+1$, $F={\uparrow}$, 其 $\Omega$-基本列 $\eta\mapsto\eta$ 由 `↑ˡ` 兑现.

```agda
corr  : ∀ t → Shape t
corrP : ∀ x → Shape (x ∷ [])
corr []           = z≈
corr (x ∷ [])     = corrP x
corr (x ∷ y ∷ ys) = sum x y ys (cof (y ∷ ys)) refl (corr (y ∷ ys))
corrP (ψ zero [])     = s≈ z≈
corrP (ψ (suc μ) [])  = zero , ↑ zero , ψᴱ-≈ {p = pψ (suc μ) []} {p′ = pψ (suc μ) []} (↑≤ˡ _ z≈) , λ η x ex → ↑ˡ ex
corrP (ψ u (y ∷ ys))  = corrψ u y ys (cof (y ∷ ys)) refl (corr (y ∷ ys))
```

## §9 推论

**任意层级.** 在 $n\ge\mathsf{lv}\,t$ 层看嵌入 (`↑≤ h (emb t)`), 形状不变; $\Omega$ 情况写成任务要求的形式: $q:\mu<n$ (于是 $\mu<n$ 自动成立), 喂给 $F$ 的是 $\eta$ 在第 $\mu$ 层的嵌入.

```agda
corr↑ : ∀ t {n} (h : lv t ≤ᴺ n) → Sh (↑≤ h (emb t)) (cof t) (pred t) (fs t) (fsΩ t)
corr↑ t h = Sh-resp (cof t) (↑≤ʳ h (emb-refl t)) (corr t)

Ω-corr : ∀ t μ → cof t ≡ cΩ μ → ∀ {n} (h : lv t ≤ᴺ n) →
         Σ (nat μ < nat n) λ q → Σ (Ord< (nat μ) q → Ord (nat n)) λ F →
         (↑≤ h (emb t) ≈ limᵢ q F) × (∀ η (hη : lv η ≤ᴺ μ) → F (coe₀ (↑≤ hη (emb η))) ≈ emb (fsΩ t η))
Ω-corr t μ e h with subst (λ c → Sh (↑≤ h (emb t)) c (pred t) (fs t) (fsΩ t)) e (corr↑ t h)
... | q , F , eF , hF = q , F , eF , λ η hη → hF η _ (↑≤ˡ hη (emb-refl η))
```

**树的 FGH 满足表记的递归方程.** FGH 只吃第 0 层的树; 顶层下标全为 0 的项 (Omega1 的 `Top₀`, 即 $t<\Omega_1$) 的层级是 0, 用 `at₀` 把 `Ord (nat (lv t))` 沿 `lv t ≡ 0` 搬到 `Ord₀` (对变量 $m$ 匹配 `refl`, 无 K). `Top₀` 对 `pred`/`fs` 封闭 (Omega1 `Top₀-pred`/`Top₀-fs`), 所以两条方程可以沿递归一路用下去; 表记这边不需要 `Acc` 证书.

```agda
FGH-≈ : ∀ {a b : Ord₀} → a ≈ b → ∀ n → FGH a n ≡ FGH b n
FGH-≈ z≈     n = refl
FGH-≈ (s≈ e) n = iter-ext (FGH-≈ e) n n
FGH-≈ (l≈ h) n = FGH-≈ (h n) n
FGH-≈ (lᵢ≈ {p = ()} h) n
lv-Top₀ : ∀ {t} → Top₀ t → lv t ≡ 0
lv-Top₀ t[]                     = refl
lv-Top₀ (t∷ {xs = []} tp)       = refl
lv-Top₀ (t∷ {xs = x ∷ xs} tp)   = lv-Top₀ {x ∷ xs} tp

at₀ : ∀ {m} → m ≡ 0 → Ord (nat m) → Ord₀
at₀ refl x = x

at₀-≈ : ∀ {m ℓ} (e : m ≡ 0) {x : Ord (nat m)} {y : Ord ℓ} → x ≈ y → at₀ e x ≈ y
at₀-≈ refl h = h

emb₀ : (t : T) → Top₀ t → Ord₀
emb₀ t tp = at₀ (lv-Top₀ tp) (emb t)

emb₀-≈ : ∀ t tp → emb₀ t tp ≈ emb t
emb₀-≈ t tp = at₀-≈ (lv-Top₀ tp) (emb-refl t)
FGH-c1 : ∀ t tp → cof t ≡ c1 → ∀ n → FGH (emb₀ t tp) n ≡ iter (FGH (emb₀ (pred t) (Top₀-pred t tp))) n n
FGH-c1 t tp e n with s-inv (≈-trans (emb₀-≈ t tp) (subst (λ c → Sh (emb t) c (pred t) (fs t) (fsΩ t)) e (corr t)))
... | X′ , eX , eX′ = trans (FGH-≈ eX n)
  (iter-ext (FGH-≈ (≈-trans eX′ (≈-sym (emb₀-≈ (pred t) (Top₀-pred t tp))))) n n)

FGH-cω : ∀ t tp → cof t ≡ cω → ∀ n → FGH (emb₀ t tp) n ≡ FGH (emb₀ (fs t n) (Top₀-fs t n tp)) n
FGH-cω t tp e n with subst (λ c → Sh (emb t) c (pred t) (fs t) (fsΩ t)) e (corr t)
... | F , eF , hF with l-inv (≈-trans (emb₀-≈ t tp) eF)
... | F′ , eF′ , hF′ = trans (FGH-≈ eF′ n)
  (FGH-≈ (≈-trans (hF′ n) (≈-trans (hF n) (≈-sym (emb₀-≈ (fs t n) (Top₀-fs t n tp))))) n)
```

**数值与逐例核对.** $f_\omega(2)=8$, $f_{\varepsilon_0}(1)=2$ (与 Omega1 相同); $\psi_0(\Omega_2)[1]=\psi_0(\psi_1(\Omega_1))$ (规则 6 的链经过 $\psi_1$, 不是 BTBO 原版的 $\varepsilon_0$, 见 BTBOSemantics `ψΩ-flat`); 含 $\psi_2,\psi_3$ 的项上 FGH 方程的 `refl` 实例; 以及用 Omega1 §7.3 的翻译 `agree`, 在含 $\psi_2,\psi_3$ 的样例上核对 `fs` 与归档 EBO 的 `fsn↓` 逐字相同. (较大的 FGH 值, 如 $f_{\psi_0(\Omega_2)}(2)$, 在类型检查器里两分钟内算不完, 未列入.)

```agda
𝟙 ω̂ εₜ Ω₂ψ ψ₀Ω₂ ψ₀ψ₁Ω₂ ψ₀ψ₁ψ₂ψ₃ : T
𝟙        = ψ 0 [] ∷ []
ω̂        = ψ 0 𝟙 ∷ []
εₜ       = ψ 0 (ψ 1 [] ∷ []) ∷ []
Ω₂ψ      = ψ 2 [] ∷ []
ψ₀Ω₂     = ψ 0 Ω₂ψ ∷ []
ψ₀ψ₁Ω₂   = ψ 0 (ψ 1 Ω₂ψ ∷ []) ∷ []
ψ₀ψ₁ψ₂ψ₃ = ψ 0 (ψ 1 (ψ 2 (ψ 3 [] ∷ []) ∷ []) ∷ []) ∷ []

_ : FGH (emb ω̂) 2 ≡ 8
_ = refl

_ : FGH (emb εₜ) 1 ≡ 2
_ = refl

_ : fs ψ₀ψ₁Ω₂ 1 ≡ ψ 0 (ψ 1 (ψ 1 (ψ 1 [] ∷ []) ∷ []) ∷ []) ∷ []
_ = refl

_ : FGH (emb ψ₀Ω₂) 1 ≡ FGH (emb (fs ψ₀Ω₂ 1)) 1
_ = refl

_ : FGH (emb ψ₀ψ₁ψ₂ψ₃) 1 ≡ FGH (emb (fs ψ₀ψ₁ψ₂ψ₃ 1)) 1
_ = refl

_ : fs ψ₀Ω₂ 1 ≡ ψ 0 (ψ 1 (ψ 1 [] ∷ []) ∷ []) ∷ []
_ = refl

samples₂ : List T
samples₂ = ψ₀Ω₂ ∷ ψ₀ψ₁Ω₂ ∷ ψ₀ψ₁ψ₂ψ₃ ∷ (ψ 1 (ψ 3 [] ∷ []) ∷ [])
         ∷ (ψ 2 (ψ 2 (ψ 3 [] ∷ []) ∷ []) ∷ []) ∷ (ψ 0 (ψ 3 [] ∷ ψ 2 (ψ 2 [] ∷ []) ∷ []) ∷ []) ∷ []

_ : allAgree samples₂ 0 ≡ true
_ = refl

_ : allAgree samples₂ 2 ≡ true
_ = refl
```

## §10 结论与边界

**已证** (全部 `--safe --without-K`, 无公设、无洞、无 `TERMINATING`, 无 `--no-positivity-check`):

1. 树类型就是 BTBO 的 `Ord (nat n)` (§1 逐字列出), 折叠就是 Finite §3 的 `ψᴱ`, 嵌入与 Finite §4 的 `emb` 逐字相同 (换成 Omega1 的项类型).
2. 跨层级外延相等 `_≈_ : Ord ℓ₁ → Ord ℓ₂ → Set` (强 `limᵢ` 条件, 较低层关系对 `<`-证明递归定义), 对一切层级是 PER; `↑`, `↑≤`, `+`, `iter`, `Ωᴱ`, `ψᴱ` 尊重它 (`ψᴱ-≈` 同时给出"提升后折叠 = 直接折叠"); 每个嵌入自反 (`emb-refl`).
3. **对应定理** `corr : ∀ t → Shape t`: 对每个镜像项 (任意自然数下标, 无前提), 形状如 §6 表格, 覆盖 `c0`/`c1`/`cω`/`cΩ μ` (一切 $\mu$). 层级版 `corr↑`, $\Omega$ 版 `Ω-corr` (对 $n\ge\mathsf{lv}\,t$, 给出 $q:\mu<n$ 与 $F$, 使 $F(\mathsf{emb}_\mu\,\eta)\approx\mathsf{emb}(t[\eta])$ 对一切 $\mathsf{lv}\,\eta\le\mu$).
4. 推论 `FGH-c1`, `FGH-cω`: 在 $t<\Omega_1$ 的项上, 树的 FGH 满足表记沿 `pred`/`fs` 的递归方程; 前提 `Top₀` 对 `pred`, `fs` 封闭. 主定理本身没有前提, 所以"片段对 `pred`/`fs`/`fsΩ` 封闭"是平凡的.
5. `refl` 核对: $f_\omega(2)=8$, $f_{\varepsilon_0}(1)=2$, $\psi_0(\psi_1(\Omega_2))[1]$, $\psi_0(\Omega_2)[1]=\psi_0(\psi_1(\Omega_1))$, 两个含 $\psi_2/\psi_3$ 的 FGH 方程实例; 6 个含 $\psi_2,\psi_3$ 的样例在 $n=0,2$ 上与 EBO `fsn↓` 逐字相同.

**与 EBO 规则的对应**: 规则 1 (和取末项)、$1[n]=0$、$\Omega_{\mu+1}[\eta]=\eta$、规则 4、规则 5ω、规则 5Ω (穿透, `cmp (suc ν) u` 为 `lt`/`eq`)、规则 6 ($\gamma_0=\Omega_\nu$, $\gamma_{k+1}=\psi_\nu(b[\gamma_k])$, `gt`) 在树上与表记上逐条相同, 由对应定理保证, 对一切自然数下标. 剩余差异只有哑值, 都不进入结论: 表记侧 `fsΩ` 在非 $\Omega$-共尾输入上的哑值, `fs` 在 $\Omega$-共尾项上的 ℕ-截断 (同 EBO; 定理对 $\Omega$-共尾项只断言 `fsΩ`); `pred` 在非后继项上的哑值. 嵌入侧**没有**哑值 (Omega1 中下标 $\ge2$ 的哑值已消失, `W` 前提随之取消). 镜像表记与 EBO 的一致仍只是逐例核对 (另一路工作在做一般翻译定理).

**设计与障碍**:

- 树族: 见 §1. 三种候选在变量层级下都需要搬运; 选 BTBO 的 `Ord` 是因为它不输于其他方案, 且认证的就是 BTBO 的树类型. 得失: 与 BTBO 同一类型、同一 `↑`/`+`/`FGH`, 认证 BTBO 原版或 BTBOFix 的树只需比较折叠函数 (仍需对它们各自的 `ψ<` 做"与 `ψᴱ` 在嵌入上 $\approx$"之类的论证), 不需要类型之间的桥. 代价是 `coe` 与证明索引, 但只出现在 `coe-coe₀` 与 `R<-*` 几条引理里.
- 原计划用燃料参数 (对层级上界递归) 证 PER 的传递性, 并证 `<-unique`、`<-dec` 与 `cmp` 的对应. 实际都不需要: 对证明递归的 `R<` 让停机检查器直接接受互递归; 派发的一致性只用无自反 (对一切 `Ordᴰ` 成立); 证明唯一性完全没用到, 因为 `≈` 本身允许两边证明不同.
- 异层 $\approx$ 是本篇的关键选择. 同层 $\approx$ 加提升引理的方案要处理 `↑≤` 的证明无关、`↑` 与 `+`/`limᵢ` 的交换、提升后再折叠等一串引理; 异层 $\approx$ 下它们都是 `↑ˡ`/`↑ʳ`/`ψᴱ-≈` 的特例.
- `with` 抽象: `pen`/`coll` 把 `ψᴱ-≈ ext` 作为第二个 `with` 参数, Agda 在其类型中也抽象掉 `<-dec q p`, 于是分支里直接得到所需等式, 不必另写 `ψᴱ` 的展开引理.
- `ψᴱ-≈` 中规则 6 的四个分支 (`injᵇ`/`injᶜ` 两两组合) 是同一段证明的四份拷贝, 因为 Finite 的 `ψᴱ` 对 `injᵇ`/`injᶜ` 分别写了相同的右边.

**下一步**:

1. **可数下标 (对角)**: $\Omega$ 的下标为项, 走向 EBO 本身 ($\psi_0(\Lambda)$). 层级空间要与序数空间同一, 树族索引需要是树本身 (Mahlo/路线 C 的问题); 本篇的异层 $\approx$ 与对证明递归的 `R<` 对一切 `Ordᴰ` 层级定义, 可以直接复用于 `lim` 层级, 但 `ψᴱ` 在极限层级的 $\Omega^\mathsf{E}$ 与 BTBO 的对角 (`ψ₀ {lim}`) 需要按 EBO 的 `cofψ0` 规则重写.
2. **交替**: 折叠输出回灌为新下标 (`ordᴰ`), 需要树到 `Ordᴰ` 的嵌入保持 $\approx$, 以及下标层的有界三歧只在公共上界内使用.
3. 用本篇的 `ψᴱ-≈` 比较 BTBOFix 的补丁折叠与 `ψᴱ`, 把 BTBOFix 的估计值 $\psi_0(\Omega_\Omega)$ 的有限下标部分升级为定理.
