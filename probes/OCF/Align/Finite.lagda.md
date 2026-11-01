# EBO 对齐 (一): 有限下标片段的镜像表记

> 交替路线的第一步 (见 [probes/README.md](../../README.md)): 把表记系统嵌进布劳威尔树, 让"这棵树是 $\psi(\ldots)$"从非形式估计变成定理.
> 本文做最底层的一段: **下标为自然数的 Buchholz $\psi_\nu$** ($\nu<\omega$, 极限 $\psi_0(\Omega_\omega)$), 对应 [BTBO](../../../src/OCF/BTBO.lagda.md) 的 `Ord (nat n)` 层级.
>
> 方法不是把 [Notation/EBO](../Notation/EBO.lagda.md) 的基本列规则搬到树上, 而是反过来: 先写出树的 $\psi$ 实际在算什么 (镜像表记 $\mathsf{T}$ 及其句法基本列), 证明嵌入保持基本列, 再逐条记录镜像规则与 EBO 规则的差异. 树那边的良基性是免费的, 所以一旦嵌入保持基本列, 表记那边的 `Acc` 证书也随之免费.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Finite where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import OCF.BTBO using (module Trich; module BoundedTrich; module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Barrier using (nat; nat-mono)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec)
open BoundedTrich hiding (_+_)
open Ord-Ord
```

## §1 有限层级

树的层级是 $\mathsf{Ord}^\mathsf{D}$, 本文只用其中的自然数 $\mathsf{nat}\,n$. 层级之间的提升需要 $\le$ 的证明, 自然数上这是免费的.

```agda
infix 4 _≤ᴺ_
data _≤ᴺ_ : ℕ → ℕ → Set where
  ≤-refl : ∀ {n} → n ≤ᴺ n
  ≤-step : ∀ {n m} → n ≤ᴺ m → n ≤ᴺ suc m

z≤ : ∀ n → zero ≤ᴺ n
z≤ zero    = ≤-refl
z≤ (suc n) = ≤-step (z≤ n)

s≤s : ∀ {n m} → n ≤ᴺ m → suc n ≤ᴺ suc m
s≤s ≤-refl     = ≤-refl
s≤s (≤-step p) = ≤-step (s≤s p)

≤⊔ˡ : ∀ m n → m ≤ᴺ m ⊔ n
≤⊔ˡ zero    n       = z≤ n
≤⊔ˡ (suc m) zero    = ≤-refl
≤⊔ˡ (suc m) (suc n) = s≤s (≤⊔ˡ m n)

≤⊔ʳ : ∀ m n → n ≤ᴺ m ⊔ n
≤⊔ʳ zero    n       = ≤-refl
≤⊔ʳ (suc m) zero    = z≤ (suc m)
≤⊔ʳ (suc m) (suc n) = s≤s (≤⊔ʳ m n)

≤-dec : ∀ m n → m ≤ᴺ n ⊎ n <ᴺ m
≤-dec zero    n       = inj₁ (z≤ n)
≤-dec (suc m) zero    = inj₂ (z<s m)
≤-dec (suc m) (suc n) with ≤-dec m n
... | inj₁ p = inj₁ (s≤s p)
... | inj₂ q = inj₂ (s<s q)

↑≤ : ∀ {m n} → m ≤ᴺ n → Ord (nat m) → Ord (nat n)
↑≤ ≤-refl     a = a
↑≤ (≤-step p) a = ↑ zero (↑≤ p a)
```

**顺序引理** $n<m\le k$ 蕴含 $n<k$; 以及把 $\mathbb{N}$ 上的 $<$ 送到层级上.

```agda
<≤ : ∀ {n m k} → n <ᴺ m → m ≤ᴺ k → n <ᴺ k
<≤ p ≤-refl     = p
<≤ p (≤-step q) = suc (<≤ p q)

nat< : ∀ {n m} → n <ᴺ m → nat n < nat m
nat< = nat-mono
```

## §2 BTBO 的 $\psi$ 不是 Buchholz 的 $\psi$

对齐的第一个发现是负面的. 逐条读 BTBO 的 `ψ<`:

1. `ψ< p zero = Ω i` 而 `Ω zero = ω`: 取 $\Omega_0=\omega$, 于是 $\psi_0(0)=\omega$. Buchholz 与 EBO 取 $\Omega_0=1$.
2. `ψ< p (suc a) = lfp (ψ< p a +_)`: 基本列 $\psi(a)\cdot n$, 与 EBO 规则 4 相同.
3. `limᵢ` 情况 `injᶜ`: `lfp (ψ< p ∘ f ∘ coe₀)`, 链从 $0$ 起; EBO 规则 6 的 $\gamma$-链从 $\Omega_\mu$ 起. 差一个平移.
4. `limᵢ` 情况 `injᵇ` ($i<j$): `lfp (ψ< p ∘ f ∘ coe₀ ∘ ↑ i<j)`, 链上的每一步只经过目标层 $i$ 的 $\psi$; EBO 规则 6 的链经过共尾层 $\mu=j$ 的 $\psi_\mu$. 下面用 `refl` 核实其后果: 树把 $\psi_0(\Omega_2)$ 算成与 $\psi_0(\Omega_1)$ 同一条链 (只差把参数多提升一层), 即 $\varepsilon_0$; 而 Buchholz 的 $\psi_0(\Omega_2)=\psi_0(\varepsilon_{\Omega+1})$ 是 Bachmann–Howard 序数.
5. `ψ₀ {suc ℓ} a = ψ₀ (ψ< zero a)`: 跨层折叠是逐层一步折叠的复合. 逐层复合与 Buchholz 的直接折叠不是同一个函数 (例如 $\psi_0(\psi_1(y))\ne\psi_0(y)$ 对可数 $y$).

```agda
chain₂ chain₁ : ℕ → Ord₀
chain₂ = iter (λ x → ψ< (suc zero) (↑ zero (↑ zero x))) zero
chain₁ = iter (λ x → ψ< zero (↑ zero x)) zero

_ : ψ< (suc zero) (Ω (suc (suc zero))) ≡ lim chain₂
_ = refl

_ : ψ< zero (Ω (suc zero)) ≡ lim chain₁
_ = refl
```

这些差异说明: BTBO 的树序数的"标签"($\psi(\Omega_\omega)$ 之类)不能靠与 EBO 的基本列逐条对照来兑现, 需要序理论的比较. 本文不走那条路, 而是**在 BTBO 的树类型上另定义一个忠实于 Buchholz 规则的折叠** $\psi^\mathsf{E}$, 把 EBO 片段嵌进去. 这样得到的树构造与 EBO 的基本列逐条相同, 树的 FGH 与表记的 FGH 相等就成了可以对项归纳证明的事.

## §3 Buchholz 忠实的折叠 $\psi^\mathsf{E}$

$\Omega^\mathsf{E}_0 = 1$, 其余同 BTBO. 折叠规则逐条照抄 EBO §5:

- $\psi_i(0)=\Omega_i$;
- $\psi_i(a+1)[n]=\psi_i(a)\cdot n$ (规则 4);
- $\psi_i(\lim f)[n]=\psi_i(f\,n)$ (规则 5, $\omega$);
- $a=\lim_j(f)$ 且 $j<i$: $\psi_i(a)[\eta]=\psi_i(f\,\eta)$ (规则 5, $\Omega$: 穿透);
- $a=\lim_j(f)$ 且 $j\ge i$: $\gamma_0=\Omega_j$, $\gamma_{k+1}=\psi_j(f\,\gamma_k)$, $\psi_i(a)[n]=\psi_i(f\,\gamma_n)$ (规则 6). 这里 $\psi_j$ 是到共尾层 $j$ 的**直接**折叠 `ψᴱ q`, 它的下标证明 $q:j<\ell$ 正是 `limᵢ` 节点自带的.

```agda
Ωᴱ : (ℓ : Ordᴰ) → Ord ℓ
Ωᴱ zero      = suc zero
Ωᴱ (suc ℓ)   = limᵢ zero (↑ zero)
Ωᴱ (lim f _) = lim (λ n → ↑ (f<l n) (Ωᴱ (f n)))

ψᴱ : ∀ {i ℓ} → i < ℓ → Ord ℓ → Ord i
ψᴱ p zero     = Ωᴱ _
ψᴱ p (suc a)  = lim (iter (ψᴱ p a +_) zero)
ψᴱ p (lim f)  = lim (ψᴱ p ∘ f)
ψᴱ {i} {ℓ} p (limᵢ {i = j} q f) with <-dec q p
... | injᵃ j<i = limᵢ j<i (ψᴱ p ∘ f ∘ coe)
... | injᵇ _   = lim (λ n → ψᴱ p (f (coe₀ (iter (ψᴱ q ∘ f ∘ coe₀) (Ωᴱ j) n))))
... | injᶜ _   = lim (λ n → ψᴱ p (f (coe₀ (iter (ψᴱ q ∘ f ∘ coe₀) (Ωᴱ j) n))))
```

终止性与 BTBO 的 `ψ<` 同理: 每个递归调用的树参数都是 `f` 的像, 是 `limᵢ q f` 的子项; 第一个参数换成 `q` 不影响度量.

## §4 镜像表记与嵌入

项是主项的和, 主项 `ψ u a` 的下标 $u$ 是自然数. $\mathbf{1}=\psi_0(0)$, 与 EBO 一致.

```agda
data P : Set
T : Set
T = List P

data P where
  ψ : (u : ℕ) (a : T) → P

pattern 𝟏 = ψ 0 []

natT : ℕ → T
natT zero    = []
natT (suc n) = 𝟏 ∷ natT n
```

**层级** $\mathsf{lv}\,t$: 项里出现的最大下标. 单元素和按主项算, 使 `lv (x ∷ [])` 定义性地归约.

```agda
lv  : T → ℕ
lvP : P → ℕ
lv []              = zero
lv (x ∷ [])        = lvP x
lv (x ∷ xs@(_ ∷ _)) = lvP x ⊔ lv xs
lvP (ψ u a)        = u
```

**嵌入**: $\psi_u(a)$ 的参数 $a$ 先提升到层级 $m=\mathsf{lv}\,a\sqcup(u+1)$ (保证 $u<m$), 再用 $\psi^\mathsf{E}$ 直接折叠到第 $u$ 层. 和映到树的加法, 两边提升到公共层级.

```agda
emb  : (t : T) → Ord (nat (lv t))
embP : (x : P) → Ord (nat (lvP x))
emb []               = zero
emb (x ∷ [])         = embP x
emb (x ∷ xs@(_ ∷ _)) = ↑≤ (≤⊔ˡ (lvP x) (lv xs)) (embP x) + ↑≤ (≤⊔ʳ (lvP x) (lv xs)) (emb xs)
embP (ψ u a) = ψᴱ (nat< (<≤ zero (≤⊔ʳ (lv a) (suc u)))) (↑≤ (≤⊔ˡ (lv a) (suc u)) (emb a))
```

定义性计算:

```agda
_ : emb (𝟏 ∷ []) ≡ suc zero                      -- ψ₀(0) = 1
_ = refl

_ : emb (natT 2) ≡ suc (suc zero)
_ = refl

_ : emb (ψ 1 [] ∷ []) ≡ Ωᴱ (suc zero)            -- ψ₁(0) = Ω₁
_ = refl

ω̂ : T                                             -- ω = ψ₀(1)
ω̂ = ψ 0 (natT 1) ∷ []

_ : emb ω̂ ≡ lim (iter (suc zero +_) zero)        -- ω[n] = 1·n
_ = refl
```

## §5 树的外延相等

嵌入保持基本列的陈述要比较两棵树, 而树里有函数, 没有函数外延性就证不出命题相等. 改用结构定义的外延相等 $\approx$: 极限逐项相等. 本文先只处理没有 `limᵢ` 节点的树 (第 0 层的树, 以及它们的提升), $\Omega$-索引极限的外延相等留到下一篇.

```agda
infix 4 _≈_
data _≈_ {ℓ} : Ord ℓ → Ord ℓ → Set where
  z≈ : zero ≈ zero
  s≈ : ∀ {a b} → a ≈ b → suc a ≈ suc b
  l≈ : ∀ {f g} → (∀ n → f n ≈ g n) → lim f ≈ lim g

data NoLᵢ {ℓ} : Ord ℓ → Set where
  nz : NoLᵢ zero
  ns : ∀ {a} → NoLᵢ a → NoLᵢ (suc a)
  nl : ∀ {f} → (∀ n → NoLᵢ (f n)) → NoLᵢ (lim f)

≈-refl : ∀ {ℓ} {a : Ord ℓ} → NoLᵢ a → a ≈ a
≈-refl nz     = z≈
≈-refl (ns h) = s≈ (≈-refl h)
≈-refl (nl h) = l≈ (λ n → ≈-refl (h n))

≈-trans : ∀ {ℓ} {a b c : Ord ℓ} → a ≈ b → b ≈ c → a ≈ c
≈-trans z≈     z≈      = z≈
≈-trans (s≈ e) (s≈ e′) = s≈ (≈-trans e e′)
≈-trans (l≈ e) (l≈ e′) = l≈ (λ n → ≈-trans (e n) (e′ n))
```

树上的运算都尊重 $\approx$ 并保持无 `limᵢ`: 加法、提升、迭代, 以及**折叠到第 0 层**的 $\psi^\mathsf{E}$ (折叠到更高层会产生 `limᵢ`, 留到下一篇).

```agda
+-≈ : ∀ {ℓ} {a a′ b b′ : Ord ℓ} → a ≈ a′ → b ≈ b′ → a + b ≈ a′ + b′
+-≈ e z≈      = e
+-≈ e (s≈ e′) = s≈ (+-≈ e e′)
+-≈ e (l≈ e′) = l≈ (λ n → +-≈ e (e′ n))

↑-≈ : ∀ {ℓ₁ ℓ₂} {p : ℓ₁ < ℓ₂} {a b : Ord ℓ₁} → a ≈ b → ↑ p a ≈ ↑ p b
↑-≈ z≈     = z≈
↑-≈ (s≈ e) = s≈ (↑-≈ e)
↑-≈ (l≈ e) = l≈ (λ n → ↑-≈ (e n))

iter-≈ : ∀ {ℓ} {G G′ : Ord ℓ → Ord ℓ} → (∀ {x y} → x ≈ y → G x ≈ G′ y) →
         ∀ {x y} → x ≈ y → ∀ n → iter G x n ≈ iter G′ y n
iter-≈ h e zero    = e
iter-≈ h e (suc n) = h (iter-≈ h e n)

ψᴱ-≈ : ∀ {ℓ} {p : zero < ℓ} {a b : Ord ℓ} → a ≈ b → ψᴱ p a ≈ ψᴱ p b
ψᴱ-≈ z≈     = s≈ z≈
ψᴱ-≈ (s≈ e) = l≈ (iter-≈ (λ e′ → +-≈ (ψᴱ-≈ e) e′) z≈)
ψᴱ-≈ (l≈ e) = l≈ (λ n → ψᴱ-≈ (e n))

+-noLᵢ : ∀ {ℓ} {a b : Ord ℓ} → NoLᵢ a → NoLᵢ b → NoLᵢ (a + b)
+-noLᵢ ha nz      = ha
+-noLᵢ ha (ns hb) = ns (+-noLᵢ ha hb)
+-noLᵢ ha (nl hb) = nl (λ n → +-noLᵢ ha (hb n))

↑-noLᵢ : ∀ {ℓ₁ ℓ₂} {p : ℓ₁ < ℓ₂} {a : Ord ℓ₁} → NoLᵢ a → NoLᵢ (↑ p a)
↑-noLᵢ nz     = nz
↑-noLᵢ (ns h) = ns (↑-noLᵢ h)
↑-noLᵢ (nl h) = nl (λ n → ↑-noLᵢ (h n))

iter-noLᵢ : ∀ {ℓ} {G : Ord ℓ → Ord ℓ} → (∀ {x} → NoLᵢ x → NoLᵢ (G x)) →
            ∀ {x} → NoLᵢ x → ∀ n → NoLᵢ (iter G x n)
iter-noLᵢ h hx zero    = hx
iter-noLᵢ h hx (suc n) = h (iter-noLᵢ h hx n)

ψᴱ-noLᵢ : ∀ {ℓ} {p : zero < ℓ} {a : Ord ℓ} → NoLᵢ a → NoLᵢ (ψᴱ p a)
ψᴱ-noLᵢ nz     = ns nz
ψᴱ-noLᵢ (ns h) = nl (iter-noLᵢ (+-noLᵢ (ψᴱ-noLᵢ h)) nz)
ψᴱ-noLᵢ (nl h) = nl (λ n → ψᴱ-noLᵢ (h n))
```

快速增长层级只看第 0 层的树, 而且只看极限的各项, 所以它尊重 $\approx$:

```agda
iter-ext : ∀ {f g : ℕ → ℕ} → (∀ n → f n ≡ g n) → ∀ x k → iter f x k ≡ iter g x k
iter-ext e x zero    = refl
iter-ext {g = g} e x (suc k) = trans (e _) (cong g (iter-ext e x k))

FGH-≈ : ∀ {a b : Ord₀} → a ≈ b → ∀ n → FGH a n ≡ FGH b n
FGH-≈ z≈     n = refl
FGH-≈ (s≈ e) n = iter-ext (FGH-≈ e) n n
FGH-≈ (l≈ e) n = FGH-≈ (e n) n
```

## §6 $\varepsilon_0$ 片段: 只有 $\psi_0$ 的项

先做最小的闭合片段: 所有下标都是 0. 这是 Cantor 范式 ($\psi_0(a)=\omega^a$), 极限 $\varepsilon_0$. 规则只剩 EBO 的规则 1 (和取末项)、规则 4 ($\psi_0(b+1)[n]=\psi_0(b)\cdot n$) 和规则 5 的 $\omega$ 情况 ($\psi_0(b)[n]=\psi_0(b[n])$). 为了让层级定义性地归约, 片段用自己的项类型, 嵌入直接落在 `Ord₀`.

```agda
data P₀ : Set
T₀ : Set
T₀ = List P₀

data P₀ where
  ψ⁰ : (a : T₀) → P₀

emb₀  : T₀ → Ord₀
embP₀ : P₀ → Ord₀
emb₀ []       = zero
emb₀ (x ∷ xs) = embP₀ x + emb₀ xs
embP₀ (ψ⁰ a)  = ψᴱ zero (↑ zero (emb₀ a))
```

共尾度、前驱、基本列, 逐条照抄 EBO:

```agda
data Cof₀ : Set where
  c0 c1 cω : Cof₀

cof₀  : T₀ → Cof₀
cofP₀ : P₀ → Cof₀
cof₀ []               = c0
cof₀ (x ∷ [])         = cofP₀ x
cof₀ (x ∷ xs@(_ ∷ _)) = cof₀ xs
cofP₀ (ψ⁰ [])         = c1
cofP₀ (ψ⁰ (_ ∷ _))    = cω

pred₀ : T₀ → T₀
pred₀ []                 = []
pred₀ (x ∷ xs@(_ ∷ _))   = x ∷ pred₀ xs
pred₀ (ψ⁰ [] ∷ [])       = []
pred₀ (ψ⁰ (y ∷ ys) ∷ []) = ψ⁰ (y ∷ ys) ∷ []      -- 哑值 (不是后继)

rep₀ : T₀ → ℕ → T₀                                -- ψ⁰(b)·n
rep₀ b zero    = []
rep₀ b (suc n) = ψ⁰ b ∷ rep₀ b n

fs₀  : T₀ → ℕ → T₀
fs₀ᵃ : T₀ → Cof₀ → ℕ → T₀
fs₀ []                 n = []
fs₀ (x ∷ xs@(_ ∷ _))   n = x ∷ fs₀ xs n                       -- 规则 1
fs₀ (ψ⁰ [] ∷ [])       n = []                                 -- 哑值 (1 是后继)
fs₀ (ψ⁰ (y ∷ ys) ∷ []) n = fs₀ᵃ (y ∷ ys) (cof₀ (y ∷ ys)) n
fs₀ᵃ b c0 n = []                                              -- 不可达
fs₀ᵃ b c1 n = rep₀ (pred₀ b) n                                -- 规则 4
fs₀ᵃ b cω n = ψ⁰ (fs₀ b n) ∷ []                               -- 规则 5 (ω)
```

## §7 对应定理

**定理** 对每个项 $t$, 嵌入 $\mathsf{emb}_0\,t$ 的形状由 $\mathsf{cof}_0\,t$ 决定, 且各分量恰是句法前驱或句法基本列的嵌入:

- $\mathsf{cof}_0\,t=0$: $\mathsf{emb}_0\,t\approx 0$;
- $\mathsf{cof}_0\,t=1$: $\mathsf{emb}_0\,t\approx(\mathsf{emb}_0(\mathsf{pred}_0\,t))^+$;
- $\mathsf{cof}_0\,t=\omega$: $\mathsf{emb}_0\,t\approx\lim(n\mapsto\mathsf{emb}_0(t[n]))$.

```agda
Shape : T₀ → Cof₀ → Set
Shape t c0 = emb₀ t ≈ zero
Shape t c1 = emb₀ t ≈ suc (emb₀ (pred₀ t))
Shape t cω = emb₀ t ≈ lim (λ n → emb₀ (fs₀ t n))
```

两条辅助引理: 非空和的共尾度不是 0; $\psi_0(b)\cdot n$ 的嵌入就是树上的迭代加法 (定义性成立).

```agda
cof₀-ne : ∀ y ys → cof₀ (y ∷ ys) ≡ c0 → ⊥
cof₀-ne (ψ⁰ [])      []       ()
cof₀-ne (ψ⁰ (_ ∷ _)) []       ()
cof₀-ne y            (z ∷ zs) e = cof₀-ne z zs e

rep-iter : ∀ b n → emb₀ (rep₀ b n) ≡ iter (embP₀ (ψ⁰ b) +_) zero n
rep-iter b zero    = refl
rep-iter b (suc n) = cong (embP₀ (ψ⁰ b) +_) (rep-iter b n)

emb₀-noLᵢ  : ∀ t → NoLᵢ (emb₀ t)
embP₀-noLᵢ : ∀ x → NoLᵢ (embP₀ x)
emb₀-noLᵢ []        = nz
emb₀-noLᵢ (x ∷ xs)  = +-noLᵢ (embP₀-noLᵢ x) (emb₀-noLᵢ xs)
embP₀-noLᵢ (ψ⁰ a)   = ψᴱ-noLᵢ (↑-noLᵢ (emb₀-noLᵢ a))
```

**证明** 对项归纳. 和的情况由加法尊重 $\approx$ 直接得到 (树的 `a + suc b`, `a + lim f` 与句法的 `pred`, `fs` 同步归约). 主项 $\psi_0(b)$ 的情况按 $\mathsf{cof}_0\,b$ 分: 后继时 $\psi^\mathsf{E}$ 的 `suc` 分支给出迭代加法, 与 `rep₀` 定义性一致; $\omega$ 时 `lim` 分支逐项递归. 两种情况都只用到 $\psi^\mathsf{E}$ 尊重 $\approx$.

```agda
corr  : ∀ t → Shape t (cof₀ t)
corrP : ∀ x → Shape (x ∷ []) (cofP₀ x)
corrψ : ∀ y ys c → cof₀ (y ∷ ys) ≡ c → Shape (y ∷ ys) c →
        ψᴱ zero (↑ zero (emb₀ (y ∷ ys))) ≈ lim (λ n → emb₀ (fs₀ᵃ (y ∷ ys) c n))

corr []               = z≈
corr (x ∷ [])         = corrP x
corr (x ∷ xs@(_ ∷ _)) = go (cof₀ xs) refl (corr xs) where
  go : ∀ c → cof₀ xs ≡ c → Shape xs c → Shape (x ∷ xs) c
  go c0 e _  = ⊥-elim (cof₀-ne _ _ e)
  go c1 _ sh = +-≈ (≈-refl (embP₀-noLᵢ x)) sh
  go cω _ sh = +-≈ (≈-refl (embP₀-noLᵢ x)) sh

corrP (ψ⁰ [])       = s≈ z≈
corrP (ψ⁰ (y ∷ ys)) = corrψ y ys (cof₀ (y ∷ ys)) refl (corr (y ∷ ys))

corrψ y ys c0 e _  = ⊥-elim (cof₀-ne y ys e)
corrψ y ys c1 _ sh = ≈-trans (ψᴱ-≈ (↑-≈ sh))
  (l≈ (λ n → subst (iter _ zero n ≈_) (sym (rep-iter _ n))
                   (≈-refl (iter-noLᵢ (+-noLᵢ (embP₀-noLᵢ (ψ⁰ (pred₀ (y ∷ ys))))) nz n))))
corrψ y ys cω _ sh = ψᴱ-≈ (↑-≈ sh)
```

## §8 推论: 树的 FGH 就是表记的 FGH

于是在这个片段上, 对 `emb₀ t` 做的快速增长层级恰好满足表记上沿 `pred₀`/`fs₀` 的递归方程. 表记这边不需要任何 `Acc` 证书, 树的结构递归就是证书.

```agda
FGH-c1 : ∀ t → cof₀ t ≡ c1 → ∀ n → FGH (emb₀ t) n ≡ iter (FGH (emb₀ (pred₀ t))) n n
FGH-c1 t e n = FGH-≈ (subst (Shape t) e (corr t)) n

FGH-cω : ∀ t → cof₀ t ≡ cω → ∀ n → FGH (emb₀ t) n ≡ FGH (emb₀ (fs₀ t n)) n
FGH-cω t e n = FGH-≈ (subst (Shape t) e (corr t)) n
```

数值核对 ($\omega$-塔的项与 Fusion §5 的数值一致):

```agda
ωTow₀ : ℕ → T₀                                    -- ω↑↑k
ωTow₀ zero    = ψ⁰ [] ∷ []
ωTow₀ (suc k) = ψ⁰ (ωTow₀ k) ∷ []

_ : FGH (emb₀ (ωTow₀ 1)) 2 ≡ 8                    -- f_ω(2) = f₂(2) = 8
_ = refl

_ : FGH (emb₀ (ωTow₀ 2)) 1 ≡ 2                    -- f_{ω^ω}(1)
_ = refl
```

## §9 小结与下一步

本篇建立的是方法, 不是强度: $\varepsilon_0$ 片段的嵌入保持基本列, 树的 FGH 与表记的 FGH 逐项相等. 得到的新事实有两条:

1. BTBO 的 `ψ<` 与 Buchholz 的 $\psi$ 不是同一个函数 (§2 的五条差异, 其中 $\psi_0(\Omega_2)$ 的链用 `refl` 核实), 所以 BTBO 的强度标签不能靠逐条对照基本列兑现; 本篇改在同一树类型上定义了忠实的 $\psi^\mathsf{E}$.
2. 对齐的证明形态: 外延相等 $\approx$ + "运算尊重 $\approx$" + 对项归纳的形状定理. 每条规则一段, 没有良基性义务.

下一篇加入下标 1 (即 $\Omega_1$-索引的 `limᵢ` 节点, 规则 5 的 $\Omega$ 情况与规则 6 的 $\gamma$-链), 把片段推到 Bachmann–Howard 序数. 那里 $\approx$ 需要 `limᵢ` 情况, 而 $\psi^\mathsf{E}$ 尊重 $\approx$ 要求极限函数自身尊重 $\approx$, 需要一个"遗传外延"谓词.
