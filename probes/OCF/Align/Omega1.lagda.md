# EBO 对齐 (二): 下标 ≤ 1 的片段

> 交替路线的第二步, 接 [Finite](Finite.lagda.md). 上一篇只处理了 $\psi_0$ (极限 $\varepsilon_0$), 树里没有 $\Omega$-索引极限. 本篇加入 $\psi_1$: 项由 $\psi_0,\psi_1$ 生成, 极限是 Bachmann–Howard 序数 $\psi_0(\varepsilon_{\Omega+1})$. 新出现的规则是 [EBO](EBO.lagda.md) §5 的规则 5 ($\Omega$ 情况, 穿透) 与规则 6 ($\gamma$-链折叠), 以及 $\Omega_1[\eta]=\eta$.
>
> 结果: 嵌入的形状由句法 `cof` 决定, 四种共尾度 (0, 后继, $\omega$, $\Omega_1$) 全部证完; 推论是树上的 FGH 满足表记沿 `pred`/`fs` 的递归方程, 片段对 `pred`/`fs`/`fsΩ` 封闭. 全文 `--safe --without-K`, 无公设、无洞、无停机编译指示.
>
> 与上一篇不同, 本篇**不用** BTBO 的 `Ord ℓ`, 而是自定义两层树类型. 理由见 §1.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Omega1 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
import OCF.Align.EBO as E
```

## §1 两层树

自然的写法是一个 $\mathbb{N}$-索引族, `limᵢ` 节点取较低层的树作参数:

    data O : ℕ → Set where ... limᵢ : (j : ℕ) → j < n → (O j → O n) → O n

Agda 不接受它: 正性检查把整个族 `O` 当作一个整体, `O j` 出现在构造子参数的箭头左边就是负出现, 不管 $j<n$. BTBO 的解法是归纳-递归: `Ord< i p` 对证明 $p:i<\ell$ 递归定义, 于是 `limᵢ` 的定义域是 `Ord< i p` 而不是 `Ord i`, 两者只在 $p$ 归约到规范形后才定义性相等, 中间要靠 `coe` 过渡.

本篇只需要两层, 可以把较低层作为**参数**传进来: `Tr L b` 是以 `L` 为 `limᵢ` 定义域的树, 布尔索引 `b` 控制 `limᵢ` 是否可用. 第 0 层取 `Tr ⊥ false` (索引排除了 `limᵢ`, 不留垃圾节点), 第 1 层取 `Tr O₀ true`. 于是 `limᵢ` 的定义域**定义性地**就是 $O_0$, 不需要任何 `coe`. 加法、外延相等等通用运算对 `Tr L b` 写一次, 两层共用.

```agda
data Tr (L : Set) : Bool → Set where
  zero : ∀ {b} → Tr L b
  suc  : ∀ {b} → Tr L b → Tr L b
  lim  : ∀ {b} → (ℕ → Tr L b) → Tr L b
  limᵢ : (L → Tr L true) → Tr L true

O₀ : Set
O₀ = Tr ⊥ false

O₁ : Set
O₁ = Tr O₀ true

iter : {A : Set} → (A → A) → A → ℕ → A
iter f x zero    = x
iter f x (suc k) = f (iter f x k)
```

加法对第二个参数递归 (与 BTBO 相同, `a + limᵢ f` 逐点加), 提升 $\uparrow:O_0\to O_1$ 保持形状. $\Omega^\mathsf{E}_0=1$ (Buchholz 约定, 见 Finite §2 第 1 条), $\Omega^\mathsf{E}_1=\lim_i(\uparrow)$, 即 $\Omega_1[\eta]=\eta$.

```agda
module _ {L : Set} where
  infixl 6 _+_
  _+_ : ∀ {b} → Tr L b → Tr L b → Tr L b
  a + zero   = a
  a + suc c  = suc (a + c)
  a + lim f  = lim (λ n → a + f n)
  a + limᵢ f = limᵢ (λ x → a + f x)

↑ : O₀ → O₁
↑ zero    = zero
↑ (suc a) = suc (↑ a)
↑ (lim f) = lim (λ n → ↑ (f n))

Ωᴱ₀ : O₀
Ωᴱ₀ = suc zero

Ωᴱ₁ : O₁
Ωᴱ₁ = limᵢ ↑
```

## §2 Buchholz 忠实的折叠

需要两个折叠: $\psi_0$ 与 $\psi_1$, 参数都在第 1 层.

- `ψ₁₀ : O₁ → O₀` 是 Finite §3 的 `ψᴱ` 在 $i=0,\ell=1$ 处的实例. `limᵢ` 节点的共尾层 $j=0\ge i=0$, 走**规则 6**: $\gamma_0=\Omega_0=1$, $\gamma_{k+1}=\psi_0(f\,\gamma_k)$, $\psi_0(\lim_i f)[n]=\psi_0(f\,\gamma_n)$. 这里到共尾层 $j=0$ 的直接折叠恰好就是 `ψ₁₀` 自己.
- `ψ₁₁ : O₁ → O₁` 是同层折叠. Finite §4 的嵌入把 $\psi_u(a)$ 的参数提升到 $\max(\mathsf{lv}\,a,u+1)$ 层再折叠, 对 $\psi_1$ 就要第 2 层. 但折叠 $O_2\to O_1$ 作用在提升上来的树上时, 遇到的 `limᵢ` 都是共尾层 $j=0<i=1$, 只走**规则 5 ($\Omega$, 穿透)**, 规则 6 不会触发; 结果与直接在第 1 层逐构造子穿透的 `ψ₁₁` 逐节点相同. 所以本篇省掉第 2 层, 让 $\psi_u$ 的参数层不超过 $u$ 时直接同层折叠. 对应 EBO 的判定: `cmp (suc μ) u` 为 `lt`/`eq` 时穿透.

其余三条对两个折叠相同: $\psi_i(0)=\Omega_i$; $\psi_i(a+1)[n]=\psi_i(a)\cdot n$ (规则 4); $\psi_i(\lim f)[n]=\psi_i(f\,n)$ (规则 5, $\omega$).

```agda
ψ₁₀ : O₁ → O₀
ψ₁₀ zero     = Ωᴱ₀
ψ₁₀ (suc a)  = lim (iter (ψ₁₀ a +_) zero)
ψ₁₀ (lim f)  = lim (λ n → ψ₁₀ (f n))
ψ₁₀ (limᵢ f) = lim (λ n → ψ₁₀ (f (iter (λ x → ψ₁₀ (f x)) Ωᴱ₀ n)))

ψ₁₁ : O₁ → O₁
ψ₁₁ zero     = Ωᴱ₁
ψ₁₁ (suc a)  = lim (iter (ψ₁₁ a +_) zero)
ψ₁₁ (lim f)  = lim (λ n → ψ₁₁ (f n))
ψ₁₁ (limᵢ f) = limᵢ (λ x → ψ₁₁ (f x))
```

终止性: 每个递归调用的参数都是 `f n` 或 `f x` 的形式, 是 `lim f`/`limᵢ f` 的结构子项; `ψ₁₀` 的 $\gamma$-链写成传给 `iter` 的 λ, 停机检查器照样看到 `ψ₁₀ (f x)` 的结构递降. 快速增长层级对第 0 层的树结构递归, 与 BTBO 的 `FGH` 逐字相同:

```agda
FGH : O₀ → ℕ → ℕ
FGH zero    n = suc n
FGH (suc a) n = iter (FGH a) n n
FGH (lim f) n = FGH (f n) n
```

## §3 外延相等: 一个部分等价关系

Finite §5 的 $\approx$ 只有 `zero`/`suc`/`lim` 三种情况. 加入 `limᵢ` 时, 逐点的条件 $\forall x.\,f\,x\approx g\,x$ 不够用: 要证 $\psi_0$ 尊重 $\approx$, 规则 6 的链在两边分别是 $\gamma_k(f)$ 与 $\gamma_k(g)$, 它们只是 $\approx$-相关而不是同一个输入, 逐点条件无法把 $f\,\gamma_k(f)$ 与 $g\,\gamma_k(g)$ 联系起来.

所以用**强**条件: $\lim_i f\approx\lim_i g$ 当且仅当 $x\approx y$ 蕴含 $f\,x\approx g\,y$. 定义域上的关系作为参数 `R` 传入, 第 1 层取 `R` 为第 0 层的 $\approx_0$ (第 0 层没有 `limᵢ`, 它的 `R` 无关紧要, 取空关系).

代价是自反性不再自动成立: $\lim_i f\approx\lim_i f$ 正好说 $f$ 尊重 $\approx_0$. 这样 $\approx_1$ 是部分等价关系 (PER), 其定义域 $\{a\mid a\approx a\}$ 就是"遗传外延的树". 这比另设一个谓词 `Good` 省事: 对称、传递对所有树成立 (传递性在 `limᵢ` 情况需要中间输入 $y\approx_0 y$, 由第 0 层的自反性给出, 这正是"内层输入在更低层"的作用), 只有自反性需要对具体的树单独证明 (§5 的 `emb₁-refl`).

```agda
module _ {L : Set} (R : L → L → Set) where
  data Eq : ∀ {b} → Tr L b → Tr L b → Set where
    z≈ : ∀ {b} → Eq {b} zero zero
    s≈ : ∀ {b} {a c : Tr L b} → Eq a c → Eq (suc a) (suc c)
    l≈ : ∀ {b} {f g : ℕ → Tr L b} → (∀ n → Eq (f n) (g n)) → Eq (lim f) (lim g)
    i≈ : {f g : L → Tr L true} → (∀ x y → R x y → Eq (f x) (g y)) → Eq (limᵢ f) (limᵢ g)

infix 4 _≈₀_ _≈₁_
_≈₀_ : O₀ → O₀ → Set
_≈₀_ = Eq (λ _ _ → ⊥)

_≈₁_ : O₁ → O₁ → Set
_≈₁_ = Eq _≈₀_
```

通用引理: 对称、传递 (各带一个关于 `R` 的前提), 加法与迭代尊重 $\approx$.

```agda
module _ {L : Set} {R : L → L → Set} where
  ≈-sym : (∀ {x y} → R x y → R y x) → ∀ {b} {a c : Tr L b} → Eq R a c → Eq R c a
  ≈-sym s z≈     = z≈
  ≈-sym s (s≈ e) = s≈ (≈-sym s e)
  ≈-sym s (l≈ h) = l≈ (λ n → ≈-sym s (h n))
  ≈-sym s (i≈ h) = i≈ (λ x y r → ≈-sym s (h y x (s r)))

  ≈-trans : (∀ x → R x x) → ∀ {b} {a c d : Tr L b} → Eq R a c → Eq R c d → Eq R a d
  ≈-trans rf z≈     z≈      = z≈
  ≈-trans rf (s≈ e) (s≈ e′) = s≈ (≈-trans rf e e′)
  ≈-trans rf (l≈ h) (l≈ h′) = l≈ (λ n → ≈-trans rf (h n) (h′ n))
  ≈-trans rf (i≈ h) (i≈ h′) = i≈ (λ x y r → ≈-trans rf (h x y r) (h′ y y (rf y)))

  +-≈ : ∀ {b} {a a′ c c′ : Tr L b} → Eq R a a′ → Eq R c c′ → Eq R (a + c) (a′ + c′)
  +-≈ e z≈      = e
  +-≈ e (s≈ e′) = s≈ (+-≈ e e′)
  +-≈ e (l≈ h)  = l≈ (λ n → +-≈ e (h n))
  +-≈ e (i≈ h)  = i≈ (λ x y r → +-≈ e (h x y r))

  iter-≈ : ∀ {b} {G G′ : Tr L b → Tr L b} → (∀ {x y} → Eq R x y → Eq R (G x) (G′ y)) →
           ∀ {x y} → Eq R x y → ∀ n → Eq R (iter G x n) (iter G′ y n)
  iter-≈ h e zero    = e
  iter-≈ h e (suc n) = h (iter-≈ h e n)
```

第 0 层是真正的等价关系; 第 1 层是 PER. `i≈-inv` 把 `limᵢ` 之间的 $\approx$ 拆回定义域上的条件.

```agda
≈₀-refl : (a : O₀) → a ≈₀ a
≈₀-refl zero    = z≈
≈₀-refl (suc a) = s≈ (≈₀-refl a)
≈₀-refl (lim f) = l≈ (λ n → ≈₀-refl (f n))

≈₀-sym : ∀ {a c : O₀} → a ≈₀ c → c ≈₀ a
≈₀-sym = ≈-sym (λ ())

≈₀-trans : ∀ {a c d : O₀} → a ≈₀ c → c ≈₀ d → a ≈₀ d
≈₀-trans = ≈-trans (λ ())

≈₁-sym : ∀ {a c : O₁} → a ≈₁ c → c ≈₁ a
≈₁-sym = ≈-sym ≈₀-sym

≈₁-trans : ∀ {a c d : O₁} → a ≈₁ c → c ≈₁ d → a ≈₁ d
≈₁-trans = ≈-trans ≈₀-refl

i≈-inv : ∀ {f g : O₀ → O₁} → limᵢ f ≈₁ limᵢ g → ∀ x y → x ≈₀ y → f x ≈₁ g y
i≈-inv (i≈ h) = h
```

树上运算尊重 $\approx$. 关键是 `ψ₁₀-≈` 的 `limᵢ` 情况: 两条 $\gamma$-链逐项 $\approx_0$-相关 (`iter-≈`, 每一步用强条件 `h` 把相关输入送到相关输出, 再递归地用 `ψ₁₀-≈`), 然后第 $n$ 项再用一次 `h`. 递归调用的参数 `h _ _ e` 是 `i≈ h` 的结构子项, 无需辅助函数. `↑` 对加法的分配只在 $\approx$ 意义下成立 (`lim` 情况需要外延性).

```agda
↑-≈ : ∀ {a c : O₀} → a ≈₀ c → ↑ a ≈₁ ↑ c
↑-≈ z≈     = z≈
↑-≈ (s≈ e) = s≈ (↑-≈ e)
↑-≈ (l≈ h) = l≈ (λ n → ↑-≈ (h n))

↑-+ : ∀ (a c : O₀) → ↑ (a + c) ≈₁ ↑ a + ↑ c
↑-+ a zero    = ↑-≈ (≈₀-refl a)
↑-+ a (suc c) = s≈ (↑-+ a c)
↑-+ a (lim f) = l≈ (λ n → ↑-+ a (f n))

ψ₁₀-≈ : ∀ {a c : O₁} → a ≈₁ c → ψ₁₀ a ≈₀ ψ₁₀ c
ψ₁₀-≈ z≈     = s≈ z≈
ψ₁₀-≈ (s≈ e) = l≈ (iter-≈ (λ e′ → +-≈ (ψ₁₀-≈ e) e′) z≈)
ψ₁₀-≈ (l≈ h) = l≈ (λ n → ψ₁₀-≈ (h n))
ψ₁₀-≈ (i≈ h) = l≈ (λ n → ψ₁₀-≈ (h _ _ (iter-≈ (λ e → ψ₁₀-≈ (h _ _ e)) (s≈ z≈) n)))

ψ₁₁-≈ : ∀ {a c : O₁} → a ≈₁ c → ψ₁₁ a ≈₁ ψ₁₁ c
ψ₁₁-≈ z≈     = i≈ (λ x y r → ↑-≈ r)
ψ₁₁-≈ (s≈ e) = l≈ (iter-≈ (λ e′ → +-≈ (ψ₁₁-≈ e) e′) z≈)
ψ₁₁-≈ (l≈ h) = l≈ (λ n → ψ₁₁-≈ (h n))
ψ₁₁-≈ (i≈ h) = i≈ (λ x y r → ψ₁₁-≈ (h x y r))
```

FGH 只看第 0 层, 它尊重 $\approx_0$:

```agda
iter-ext : ∀ {f g : ℕ → ℕ} → (∀ n → f n ≡ g n) → ∀ x k → iter f x k ≡ iter g x k
iter-ext e x zero    = refl
iter-ext {g = g} e x (suc k) = Relation.Binary.PropositionalEquality.trans (e _) (cong g (iter-ext e x k))

FGH-≈ : ∀ {a c : O₀} → a ≈₀ c → ∀ n → FGH a n ≡ FGH c n
FGH-≈ z≈     n = refl
FGH-≈ (s≈ e) n = iter-ext (FGH-≈ e) n n
FGH-≈ (l≈ h) n = FGH-≈ (h n) n
```

## §4 镜像表记

项的设计同 Finite §4: 主项 `ψ u a` 的下标是自然数, 和是主项列表. 共尾度、前驱、$\Omega$-基本列 `fsΩ` ($a[\eta]$)、$\gamma$-链、$\omega$-基本列 `fs`, **逐条照抄 EBO §3, §5**, 只做两处机械替换: 项下标换成自然数, `cmpᵀ (sucT μ) u` 换成 `cmp (suc μ) u`. 自然数下标永远不是极限, 所以 EBO 的 `cofψ0` 只剩两种情况: $\psi_0(0)=1$ 是后继, $\psi_{\mu+1}(0)=\Omega_{\mu+1}$ 的共尾度是 $\Omega_{\mu+1}$.

这里的表记对**全部**自然数下标定义, 不限于 $\le 1$; 限制只出现在嵌入与定理的前提里 (§5).

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

data Cmp : Set where lt eq gt : Cmp

cmp : ℕ → ℕ → Cmp
cmp zero    zero    = eq
cmp zero    (suc _) = lt
cmp (suc _) zero    = gt
cmp (suc m) (suc n) = cmp m n

data Cof : Set where
  c0 c1 cω : Cof
  cΩ : (μ : ℕ) → Cof              -- 共尾度 Ω_{μ+1}

cofψ₊ : ℕ → ℕ → Cmp → Cof         -- 第三参数 = cmp (μ+1) u
cofψ₊ u μ lt = cΩ μ               -- 规则 5 (Ω): 穿透
cofψ₊ u μ eq = cΩ μ
cofψ₊ u μ gt = cω                 -- 规则 6: 折叠

cofA : ℕ → Cof → Cof              -- ψ_u(b), b ≠ 0, 第二参数 = cof b
cofA u c0     = cω                -- 不可达; 哑值 (同 EBO)
cofA u c1     = cω                -- 规则 4
cofA u cω     = cω                -- 规则 5 (ω)
cofA u (cΩ μ) = cofψ₊ u μ (cmp (suc μ) u)

cof  : T → Cof
cofP : P → Cof
cof []               = c0
cof (x ∷ [])         = cofP x
cof (x ∷ xs@(_ ∷ _)) = cof xs     -- 和的共尾度 = 末项的共尾度
cofP (ψ u b@(_ ∷ _)) = cofA u (cof b)
cofP (ψ zero [])     = c1
cofP (ψ (suc μ) [])  = cΩ μ
```

`pred` 的语义同 EBO (剥一个尾部 $\mathbf{1}$, 其余为哑值). EBO 用一条通配子句兜底, 这里拆成互不重叠的子句, 使 `pred (ψ u (y ∷ ys) ∷ [])` 对变量 `u` 也能归约.

```agda
pred : T → T
pred []                     = []
pred (x ∷ xs@(_ ∷ _))       = x ∷ pred xs
pred (ψ u b@(_ ∷ _) ∷ [])   = ψ u b ∷ []
pred (ψ zero [] ∷ [])       = []
pred (ψ (suc μ) [] ∷ [])    = ψ (suc μ) [] ∷ []
```

$\Omega$-基本列 `fsΩ t η` $=t[\eta]$, 照抄 EBO 的 `fsT↓` (去掉证书). EBO 在前提 `cof a ≡ cΩ μ` 不成立的分支用 `()` 排除; 这里没有前提, 那些分支给哑值 (`fsΩ (𝟏 ∷ []) = []`, 其余返回原主项). 定理只在 `cof t ≡ cΩ 0` 时用到 `fsΩ t`, 哑值不进入任何结论.

```agda
fsΩ  : T → T → T
fsΩ₊ : ℕ → T → Cof → T → T
fsΩc : ℕ → T → ℕ → Cmp → T → T

fsΩ []                     η = []
fsΩ (x ∷ xs@(_ ∷ _))       η = x ∷ fsΩ xs η
fsΩ (ψ u b@(_ ∷ _) ∷ [])   η = fsΩ₊ u b (cof b) η
fsΩ (ψ zero [] ∷ [])       η = []                 -- 哑值 (EBO: 不可达)
fsΩ (ψ (suc μ) [] ∷ [])    η = η                  -- Ω_{μ+1}[η] = η

fsΩ₊ u b c0     η = ψ u b ∷ []                    -- 哑值 (EBO: 不可达)
fsΩ₊ u b c1     η = ψ u b ∷ []                    -- 哑值
fsΩ₊ u b cω     η = ψ u b ∷ []                    -- 哑值
fsΩ₊ u b (cΩ ν) η = fsΩc u b ν (cmp (suc ν) u) η

fsΩc u b ν lt η = ψ u (fsΩ b η) ∷ []              -- 规则 5 (Ω): 穿透
fsΩc u b ν eq η = ψ u (fsΩ b η) ∷ []
fsΩc u b ν gt η = ψ u b ∷ []                      -- 哑值 (EBO: 不可达)
```

$\gamma$-链 (EBO `γ↓`): $\gamma_0=\Omega_\nu$, $\gamma_{k+1}=\psi_\nu(b[\gamma_k])$. $\omega$-基本列 (EBO `fsn↓`): 按 EBO 的工程注记, 辅助函数全部提升为顶层互递归, 子项整体作参数.

```agda
γ : T → ℕ → ℕ → T
γ b ν zero    = ψ ν [] ∷ []
γ b ν (suc k) = ψ ν (fsΩ b (γ b ν k)) ∷ []

rep : ℕ → T → ℕ → T                               -- ψ_u(a)·n
rep u a zero    = []
rep u a (suc n) = ψ u a ∷ rep u a n

fs   : T → ℕ → T
fsn  : P → T → ℕ → T
fsn₊ : ℕ → T → Cof → ℕ → T
fsnc : ℕ → T → ℕ → Cmp → ℕ → T

fs []       n = []
fs (x ∷ xs) n = fsn x xs n

fsn x (y ∷ ys)          n = x ∷ fsn y ys n        -- 规则 1: 和 ⇒ 末项
fsn (ψ u b@(_ ∷ _)) []  n = fsn₊ u b (cof b) n
fsn (ψ zero [])     []  n = []                    -- 1[n] = 0
fsn (ψ (suc μ) [])  []  n = natT n                -- 正规 Ω: 哑值 (同 EBO)

fsn₊ u b c0     n = []                            -- 不可达哑值 (同 EBO)
fsn₊ u b c1     n = rep u (pred b) n              -- 规则 4
fsn₊ u b cω     n = ψ u (fs b n) ∷ []             -- 规则 5 (ω)
fsn₊ u b (cΩ ν) n = fsnc u b ν (cmp (suc ν) u) n

fsnc u b ν gt n = ψ u (fsΩ b (γ b ν n)) ∷ []      -- 规则 6: γ-链折叠
fsnc u b ν lt n = ψ u (fsΩ b (natT n)) ∷ []       -- 规则 5 (Ω) 的 ℕ-截断 (同 EBO)
fsnc u b ν eq n = ψ u (fsΩ b (natT n)) ∷ []
```

## §5 嵌入

**层级下落.** Finite 的嵌入是 `emb : (t : T) → Ord (nat (lv t))`, 层级随项变化. 在本片段这会出问题: 对应定理要比较 `emb t` 与 `emb (pred t)`、`emb (fs t n)`、`emb (fsΩ t η)`, 而它们的层级可以不同. 最典型的是 $\Omega_1[\eta]=\eta$: 左边在第 1 层, 右边在第 0 层; 和 $x+\Omega_1$ 的基本列 $x+\eta$ 也一样. 若坚持 `lv`-索引, 每个陈述都得插入依赖于层级证明的提升.

这里改成**两个嵌入**: `emb₀ t : O₀` 与 `emb₁ t : O₁` 分别把项放在第 0 层与第 1 层, 不看 `lv`. 参数总是用 `emb₁` 嵌入 (参数小于 $\Omega_2$), $\psi_0(a)$ 由 `ψ₁₀` 落到第 0 层, 在第 1 层再提升. 两个嵌入的一致性是一条引理 (`↑-emb`: 顶层下标全为 0 的项, 提升后的 `emb₀` 与 `emb₁` $\approx_1$-相等). 层级下落于是只在 $\Omega$-基本列的陈述里出现一次: 树的 $F$ 吃 $O_0$, 喂给它的是 `emb₀ η`.

下标 $\ge 2$ 的主项在嵌入里是**哑值** (`emb₀` 给 0, `emb₁` 当作 $\psi_1$), 由定理前提排除:

- `W t`: $t$ 中**所有**下标 (遗传地) $\le 1$;
- `Top₀ t`: $t$ 的**顶层**下标全为 0 (即 $t<\Omega_1$; 参数可以含 $\psi_1$).

```agda
emb₀  : T → O₀
embP₀ : P → O₀
emb₁  : T → O₁
embP₁ : P → O₁

emb₀ []       = zero
emb₀ (x ∷ xs) = embP₀ x + emb₀ xs
embP₀ (ψ zero a)    = ψ₁₀ (emb₁ a)
embP₀ (ψ (suc _) a) = zero                        -- 哑值: 不可数主项不在第 0 层

emb₁ []       = zero
emb₁ (x ∷ xs) = embP₁ x + emb₁ xs
embP₁ (ψ zero a)    = ↑ (ψ₁₀ (emb₁ a))
embP₁ (ψ (suc _) a) = ψ₁₁ (emb₁ a)                -- 下标 ≥ 2 时为哑值

data W  : T → Set
data WP : P → Set
data W where
  w[] : W []
  w∷  : ∀ {x xs} → WP x → W xs → W (x ∷ xs)
data WP where
  w0 : ∀ {a} → W a → WP (ψ 0 a)
  w1 : ∀ {a} → W a → WP (ψ 1 a)

data Top₀ : T → Set where
  t[] : Top₀ []
  t∷  : ∀ {a xs} → Top₀ xs → Top₀ (ψ 0 a ∷ xs)
```

和用 `embP x + emb xs` 嵌入, 单元素和 `emb (x ∷ [])` 定义性地等于 `embP x + zero`, 即 `embP x`, 所以不需要 Finite 的 `lv (x ∷ [])` 特殊子句. 定义性核对:

```agda
_ : emb₁ (ψ 1 [] ∷ []) ≡ Ωᴱ₁                      -- ψ₁(0) = Ω₁
_ = refl

_ : emb₀ (ψ 0 (𝟏 ∷ []) ∷ []) ≡ lim (iter (suc zero +_) zero)   -- ω[n] = 1·n
_ = refl
```

**每个嵌入的树都在 PER 的定义域里** (遗传外延). 这条对任意项成立, 不需要 `W`: 哑值 `zero` 也是外延的.

```agda
emb₁-refl  : ∀ t → emb₁ t ≈₁ emb₁ t
embP₁-refl : ∀ x → embP₁ x ≈₁ embP₁ x
emb₁-refl []       = z≈
emb₁-refl (x ∷ xs) = +-≈ (embP₁-refl x) (emb₁-refl xs)
embP₁-refl (ψ zero a)    = ↑-≈ (≈₀-refl _)
embP₁-refl (ψ (suc _) a) = ψ₁₁-≈ (emb₁-refl a)
```

两个嵌入的一致性:

```agda
↑-emb : ∀ t → Top₀ t → ↑ (emb₀ t) ≈₁ emb₁ t
↑-emb []             t[]      = z≈
↑-emb (ψ zero a ∷ xs) (t∷ tp) =
  ≈₁-trans (↑-+ (ψ₁₀ (emb₁ a)) (emb₀ xs)) (+-≈ (↑-≈ (≈₀-refl _)) (↑-emb xs tp))
```

杂项: $\psi_0$ 的基本列各项顶层仍是 $\psi_0$; `rep` 的嵌入就是树上的迭代加法; 非空和的共尾度不是 0.

```agda
Top₀-rep : ∀ b n → Top₀ (rep 0 b n)
Top₀-rep b zero    = t[]
Top₀-rep b (suc n) = t∷ (Top₀-rep b n)

Top₀-fsn₊ : ∀ b c n → Top₀ (fsn₊ 0 b c n)
Top₀-fsn₊ b c0     n = t[]
Top₀-fsn₊ b c1     n = Top₀-rep _ n
Top₀-fsn₊ b cω     n = t∷ t[]
Top₀-fsn₊ b (cΩ ν) n = t∷ t[]

Top₀-γ : ∀ b n → Top₀ (γ b 0 n)
Top₀-γ b zero    = t∷ t[]
Top₀-γ b (suc n) = t∷ t[]

rep₀ : ∀ b n → iter (embP₀ (ψ 0 b) +_) zero n ≈₀ emb₀ (rep 0 b n)
rep₀ b zero    = z≈
rep₀ b (suc n) = +-≈ (≈₀-refl _) (rep₀ b n)

rep₁ : ∀ b n → iter (embP₁ (ψ 1 b) +_) zero n ≈₁ emb₁ (rep 1 b n)
rep₁ b zero    = z≈
rep₁ b (suc n) = +-≈ (embP₁-refl (ψ 1 b)) (rep₁ b n)

cofψ₊-ne : ∀ u μ m → cofψ₊ u μ m ≡ c0 → ⊥
cofψ₊-ne u μ lt ()
cofψ₊-ne u μ eq ()
cofψ₊-ne u μ gt ()

cofA-ne : ∀ u c → cofA u c ≡ c0 → ⊥
cofA-ne u c0 ()
cofA-ne u c1 ()
cofA-ne u cω ()
cofA-ne u (cΩ μ) e = cofψ₊-ne u μ _ e

cof-ne : ∀ y ys → cof (y ∷ ys) ≡ c0 → ⊥
cof-ne (ψ u (_ ∷ _)) []       e = cofA-ne u _ e
cof-ne (ψ zero [])   []       ()
cof-ne (ψ (suc μ) []) []      ()
cof-ne y             (z ∷ zs) e = cof-ne z zs e
```

## §6 对应定理

**形状.** 对第 0 层与第 1 层分别规定"嵌入的形状由共尾度决定":

| `cof t` | 第 0 层 (`emb₀`) | 第 1 层 (`emb₁`) |
|---|---|---|
| `c0` | $\approx 0$ | $\approx 0$ |
| `c1` | $\approx (\mathsf{emb}_0(\mathsf{pred}\,t))^+$ | $\approx (\mathsf{emb}_1(\mathsf{pred}\,t))^+$ |
| `cω` | $\approx \lim_n \mathsf{emb}_0(t[n])$ | $\approx \lim_n \mathsf{emb}_1(t[n])$ |
| `cΩ 0` | 不可能 ($\bot$) | $\exists F.\ \approx\lim_i F$ 且 $\forall\eta\,(\mathsf{Top}_0\,\eta).\ F(\mathsf{emb}_0\,\eta)\approx\mathsf{emb}_1(t[\eta])$ |
| `cΩ (μ+1)` | $\bot$ | $\bot$ |

$\Omega$-情况的 $\eta$ 取遍**项** (顶层下标为 0 的), 而不是任意树: $F$ 吃树, 但对齐只关心嵌入出来的树, 而规则 6 的 $\gamma_k$ 正是嵌入的项. 前提只要 `Top₀ η`, 不要 `W η`, 因为 `↑-emb` 只看顶层. `cΩ (μ+1)` 一行写成 $\bot$, 于是定理本身就推出 "下标 $\le1$ 的项的共尾度不会是 $\Omega_2$ 及以上" (§7 `Ω-excl`).

`Sh₀`/`Sh₁` 把形状对各分量参数化, 使单个主项的辅助引理可以用显式的 `c` 陈述 (而不是卡住的 `cof b`), 在调用处取 `c := cof b` 时与 `Shape` 定义性一致 — 这是 Finite `corrψ` 的同一手法.

```agda
Sh₀ : O₀ → Cof → T → (ℕ → T) → Set
Sh₀ X c0     p s = X ≈₀ zero
Sh₀ X c1     p s = X ≈₀ suc (emb₀ p)
Sh₀ X cω     p s = X ≈₀ lim (λ n → emb₀ (s n))
Sh₀ X (cΩ _) p s = ⊥

Sh₁ : O₁ → Cof → T → (ℕ → T) → (T → T) → Set
Sh₁ X c0           p s g = X ≈₁ zero
Sh₁ X c1           p s g = X ≈₁ suc (emb₁ p)
Sh₁ X cω           p s g = X ≈₁ lim (λ n → emb₁ (s n))
Sh₁ X (cΩ zero)    p s g = Σ (O₀ → O₁) λ F →
                           X ≈₁ limᵢ F × (∀ η → Top₀ η → F (emb₀ η) ≈₁ emb₁ (g η))
Sh₁ X (cΩ (suc _)) p s g = ⊥

Shape₀ : T → Cof → Set
Shape₀ t c = Sh₀ (emb₀ t) c (pred t) (fs t)

Shape₁ : T → Cof → Set
Shape₁ t c = Sh₁ (emb₁ t) c (pred t) (fs t) (fsΩ t)
```

**规则 6 的链引理.** 若 $\mathsf{emb}_1\,b\approx\lim_i F$ 且 $F$ 在嵌入的项上就是 $b[\cdot]$, 则树的 $\gamma$-链逐项 $\approx_0$ 于表记的 $\gamma$-链的嵌入. 归纳步: $\gamma_{k+1}^\text{树}=\psi_0(F\,\gamma_k^\text{树})\approx\psi_0(F(\mathsf{emb}_0\,\gamma_k))\approx\psi_0(\mathsf{emb}_1(b[\gamma_k]))=\mathsf{emb}_0\,\gamma_{k+1}$. 第一步要 $F$ 自身尊重 $\approx_0$ (`ext`), 第二步要 $\gamma_k$ 顶层下标为 0. 注意 $\psi_0(b)[n]=\psi_0(b[\gamma_n])$ 恰是 $\gamma_{n+1}$, 所以主定理直接取链引理的第 $n+1$ 项.

```agda
rule6 : ∀ b (F : O₀ → O₁) → (∀ x y → x ≈₀ y → F x ≈₁ F y) →
        (∀ η → Top₀ η → F (emb₀ η) ≈₁ emb₁ (fsΩ b η)) →
        ∀ n → iter (λ x → ψ₁₀ (F x)) Ωᴱ₀ n ≈₀ emb₀ (γ b 0 n)
rule6 b F ext h zero    = s≈ z≈
rule6 b F ext h (suc n) =
  ≈₀-trans (ψ₁₀-≈ (ext _ _ (rule6 b F ext h n))) (ψ₁₀-≈ (h _ (Top₀-γ b n)))
```

**主项 $\psi_0(b)$, 第 0 层.** 按 $c=\mathsf{cof}\,b$ 分: 后继走 `ψ₁₀` 的 `suc` 分支 (规则 4); $\omega$ 走 `lim` 分支 (规则 5ω); $\Omega_1$ 走 `limᵢ` 分支 (规则 6). 目标的共尾度 `cofA 0 c` 在三种情况都定义性地归约为 `cω` (`cmp (suc ν) 0` 恒为 `gt`). $F$ 的外延性从 $\mathsf{emb}_1\,b\approx\lim_i F$ 用 PER 的对称+传递得到 $\lim_i F\approx\lim_i F$, 再拆开.

```agda
corrψ₀ : ∀ y ys c → cof (y ∷ ys) ≡ c → Shape₁ (y ∷ ys) c →
         Sh₀ (ψ₁₀ (emb₁ (y ∷ ys))) (cofA 0 c) (pred (ψ 0 (y ∷ ys) ∷ [])) (λ n → fsn₊ 0 (y ∷ ys) c n)
corrψ₀ y ys c0 e sh = ⊥-elim (cof-ne y ys e)
corrψ₀ y ys c1 e sh = ≈₀-trans (ψ₁₀-≈ sh) (l≈ (rep₀ (pred (y ∷ ys))))
corrψ₀ y ys cω e sh = ψ₁₀-≈ sh
corrψ₀ y ys (cΩ zero) e (F , eF , h) =
  ≈₀-trans (ψ₁₀-≈ eF) (l≈ (λ n → rule6 (y ∷ ys) F ext h (suc n)))
  where ext = i≈-inv (≈₁-trans (≈₁-sym eF) eF)
corrψ₀ y ys (cΩ (suc ν)) e ()
```

**主项 $\psi_0(b)$, 第 1 层**: 把第 0 层的结论提升, 各分量用 `↑-emb` 换成 `emb₁` (要求分量顶层下标为 0, 即 `Top₀-fsn₊`).

```agda
lift-cω : ∀ {X : O₀} (s : ℕ → T) → X ≈₀ lim (λ n → emb₀ (s n)) → (∀ n → Top₀ (s n)) →
          ↑ X ≈₁ lim (λ n → emb₁ (s n))
lift-cω s e tp = ≈₁-trans (↑-≈ e) (l≈ (λ n → ↑-emb (s n) (tp n)))

corrψ₀↑ : ∀ y ys c → cof (y ∷ ys) ≡ c → Shape₁ (y ∷ ys) c →
          Sh₁ (↑ (ψ₁₀ (emb₁ (y ∷ ys)))) (cofA 0 c) (pred (ψ 0 (y ∷ ys) ∷ []))
              (λ n → fsn₊ 0 (y ∷ ys) c n) (λ η → fsΩ₊ 0 (y ∷ ys) c η)
corrψ₀↑ y ys c0     e sh = ⊥-elim (cof-ne y ys e)
corrψ₀↑ y ys c1     e sh = lift-cω _ (corrψ₀ y ys c1 e sh) (Top₀-fsn₊ (y ∷ ys) c1)
corrψ₀↑ y ys cω     e sh = lift-cω _ (corrψ₀ y ys cω e sh) (Top₀-fsn₊ (y ∷ ys) cω)
corrψ₀↑ y ys (cΩ ν) e sh = lift-cω _ (corrψ₀ y ys (cΩ ν) e sh) (Top₀-fsn₊ (y ∷ ys) (cΩ ν))
```

**主项 $\psi_1(b)$.** 后继、$\omega$ 同上 (用 `ψ₁₁`). $\Omega_1$ 情况 `cmp 1 1 = eq`, 共尾度穿透 (规则 5Ω): 新的 $F$ 是 $\psi_1\circ F$, 而 $\psi_1(b)[\eta]=\psi_1(b[\eta])$ 的嵌入定义性地是 `ψ₁₁ (emb₁ (fsΩ b η))`.

```agda
corrψ₁ : ∀ y ys c → cof (y ∷ ys) ≡ c → Shape₁ (y ∷ ys) c →
         Sh₁ (ψ₁₁ (emb₁ (y ∷ ys))) (cofA 1 c) (pred (ψ 1 (y ∷ ys) ∷ []))
             (λ n → fsn₊ 1 (y ∷ ys) c n) (λ η → fsΩ₊ 1 (y ∷ ys) c η)
corrψ₁ y ys c0 e sh = ⊥-elim (cof-ne y ys e)
corrψ₁ y ys c1 e sh = ≈₁-trans (ψ₁₁-≈ sh) (l≈ (rep₁ (pred (y ∷ ys))))
corrψ₁ y ys cω e sh = ψ₁₁-≈ sh
corrψ₁ y ys (cΩ zero) e (F , eF , h) = (λ x → ψ₁₁ (F x)) , ψ₁₁-≈ eF , λ η tp → ψ₁₁-≈ (h η tp)
corrψ₁ y ys (cΩ (suc ν)) e ()
```

**和** (规则 1): 树的 `a + suc b`, `a + lim f`, `a + limᵢ f` 与句法的 `pred`, `fs`, `fsΩ` 同步归约; 唯一需要的是首项自反 (`embP₁-refl`), 这就是为什么 PER 的自反性要对嵌入单独证.

```agda
sum₁ : ∀ x y ys c → cof (y ∷ ys) ≡ c → Shape₁ (y ∷ ys) c → Shape₁ (x ∷ y ∷ ys) c
sum₁ x y ys c0 e sh = ⊥-elim (cof-ne y ys e)
sum₁ x y ys c1 e sh = +-≈ (embP₁-refl x) sh
sum₁ x y ys cω e sh = +-≈ (embP₁-refl x) sh
sum₁ x y ys (cΩ zero) e (F , eF , h) =
  (λ z → embP₁ x + F z) , +-≈ (embP₁-refl x) eF , λ η tp → +-≈ (embP₁-refl x) (h η tp)
sum₁ x y ys (cΩ (suc ν)) e ()
```

**定理 (第 1 层)** 对每个下标 $\le 1$ 的项 $t$, `emb₁ t` 的形状由 `cof t` 决定. 对项归纳; $\Omega_1=\psi_1(0)$ 本身取 $F=\uparrow$, 它的 $\Omega$-基本列 $\eta\mapsto\eta$ 由 `↑-emb` 兑现.

```agda
corr₁  : ∀ t → W t → Shape₁ t (cof t)
corrP₁ : ∀ x → WP x → Shape₁ (x ∷ []) (cofP x)
corr₁ []             w            = z≈
corr₁ (x ∷ [])       (w∷ wx _)    = corrP₁ x wx
corr₁ (x ∷ y ∷ ys)   (w∷ _ w)     = sum₁ x y ys (cof (y ∷ ys)) refl (corr₁ (y ∷ ys) w)
corrP₁ (ψ zero [])       (w0 _)  = s≈ z≈
corrP₁ (ψ zero (y ∷ ys)) (w0 wa) = corrψ₀↑ y ys (cof (y ∷ ys)) refl (corr₁ (y ∷ ys) wa)
corrP₁ (ψ 1 [])          (w1 _)  = ↑ , i≈ (λ x y r → ↑-≈ r) , λ η tp → ↑-emb η tp
corrP₁ (ψ 1 (y ∷ ys))    (w1 wa) = corrψ₁ y ys (cof (y ∷ ys)) refl (corr₁ (y ∷ ys) wa)
```

**定理 (第 0 层)** 对每个下标 $\le 1$ 且顶层下标为 0 的项 (即 $<\Omega_1$ 的项), `emb₀ t` 的形状由 `cof t` 决定. 参数的形状取自第 1 层定理.

```agda
sum₀ : ∀ x y ys c → cof (y ∷ ys) ≡ c → Shape₀ (y ∷ ys) c → Shape₀ (x ∷ y ∷ ys) c
sum₀ x y ys c0     e sh = ⊥-elim (cof-ne y ys e)
sum₀ x y ys c1     e sh = +-≈ (≈₀-refl _) sh
sum₀ x y ys cω     e sh = +-≈ (≈₀-refl _) sh
sum₀ x y ys (cΩ _) e ()

corr₀ : ∀ t → W t → Top₀ t → Shape₀ t (cof t)
corr₀ []                  w                 tp       = z≈
corr₀ (ψ zero [] ∷ [])    w                 tp       = s≈ z≈
corr₀ (ψ zero (y ∷ ys) ∷ []) (w∷ (w0 wa) _) tp     =
  corrψ₀ y ys (cof (y ∷ ys)) refl (corr₁ (y ∷ ys) wa)
corr₀ (x ∷ y ∷ ys)        (w∷ _ w)          (t∷ tp)  = sum₀ x y ys (cof (y ∷ ys)) refl (corr₀ (y ∷ ys) w tp)
```

## §7 推论

### 7.1 树的 FGH 满足表记的递归方程

```agda
FGH-c1 : ∀ t → W t → Top₀ t → cof t ≡ c1 → ∀ n → FGH (emb₀ t) n ≡ iter (FGH (emb₀ (pred t))) n n
FGH-c1 t w tp e n = FGH-≈ (subst (Shape₀ t) e (corr₀ t w tp)) n

FGH-cω : ∀ t → W t → Top₀ t → cof t ≡ cω → ∀ n → FGH (emb₀ t) n ≡ FGH (emb₀ (fs t n)) n
FGH-cω t w tp e n = FGH-≈ (subst (Shape₀ t) e (corr₀ t w tp)) n
```

$\Omega_1$-共尾的项 (第 1 层) 的 $\Omega$-基本列由树的 `limᵢ` 兑现; 同一定理还排除了更高的共尾度:

```agda
Ω-corr : ∀ t → W t → cof t ≡ cΩ 0 → Σ (O₀ → O₁) λ F →
         emb₁ t ≈₁ limᵢ F × (∀ η → Top₀ η → F (emb₀ η) ≈₁ emb₁ (fsΩ t η))
Ω-corr t w e = subst (Shape₁ t) e (corr₁ t w)

Ω-excl : ∀ t {ν} → W t → cof t ≡ cΩ (suc ν) → ⊥
Ω-excl t w e = subst (Shape₁ t) e (corr₁ t w)
```

### 7.2 片段的封闭性

为了让 `FGH-c1`/`FGH-cω` 能沿递归一路用下去, 前提 `W`、`Top₀` 必须在 `pred`、`fs` 下保持. 下面逐条证明 (`fsΩ` 在 `W` 输入下也保持 `W`). `W-fsnc` 的规则 6 分支需要 $\nu=0$, 正是由 `Ω-excl` 提供 — 对应定理在这里反过来服务于句法性质.

```agda
argW : ∀ {u a} → WP (ψ u a) → W a
argW (w0 w) = w
argW (w1 w) = w

swapW : ∀ {u a a′} → WP (ψ u a) → W a′ → WP (ψ u a′)
swapW (w0 _) w = w0 w
swapW (w1 _) w = w1 w

W-natT : ∀ n → W (natT n)
W-natT zero    = w[]
W-natT (suc n) = w∷ (w0 w[]) (W-natT n)

W-rep : ∀ {u a} → WP (ψ u a) → ∀ n → W (rep u a n)
W-rep wp zero    = w[]
W-rep wp (suc n) = w∷ wp (W-rep wp n)

W-pred : ∀ t → W t → W (pred t)
W-pred []                   w           = w[]
W-pred (x ∷ y ∷ ys)         (w∷ wx w)   = w∷ wx (W-pred (y ∷ ys) w)
W-pred (ψ u (_ ∷ _) ∷ [])   w           = w
W-pred (ψ zero [] ∷ [])     w           = w[]
W-pred (ψ (suc μ) [] ∷ [])  w           = w

W-fsΩ  : ∀ t η → W t → W η → W (fsΩ t η)
W-fsΩ₊ : ∀ u b c η → WP (ψ u b) → W η → W (fsΩ₊ u b c η)
W-fsΩc : ∀ u b ν m η → WP (ψ u b) → W η → W (fsΩc u b ν m η)
W-fsΩ []                  η w          wη = w[]
W-fsΩ (x ∷ y ∷ ys)        η (w∷ wx w)  wη = w∷ wx (W-fsΩ (y ∷ ys) η w wη)
W-fsΩ (ψ u b@(_ ∷ _) ∷ []) η (w∷ wp _) wη = W-fsΩ₊ u b (cof b) η wp wη
W-fsΩ (ψ zero [] ∷ [])    η w          wη = w[]
W-fsΩ (ψ (suc μ) [] ∷ []) η w          wη = wη
W-fsΩ₊ u b c0     η wp wη = w∷ wp w[]
W-fsΩ₊ u b c1     η wp wη = w∷ wp w[]
W-fsΩ₊ u b cω     η wp wη = w∷ wp w[]
W-fsΩ₊ u b (cΩ ν) η wp wη = W-fsΩc u b ν (cmp (suc ν) u) η wp wη
W-fsΩc u b ν lt η wp wη = w∷ (swapW wp (W-fsΩ b η (argW wp) wη)) w[]
W-fsΩc u b ν eq η wp wη = w∷ (swapW wp (W-fsΩ b η (argW wp) wη)) w[]
W-fsΩc u b ν gt η wp wη = w∷ wp w[]

W-γ : ∀ b → W b → ∀ n → W (γ b 0 n)
W-γ b w zero    = w∷ (w0 w[]) w[]
W-γ b w (suc n) = w∷ (w0 (W-fsΩ b _ w (W-γ b w n))) w[]

W-fs   : ∀ t n → W t → W (fs t n)
W-fsn  : ∀ x xs n → W (x ∷ xs) → W (fsn x xs n)
W-fsn₊ : ∀ u b c → cof b ≡ c → ∀ n → WP (ψ u b) → W (fsn₊ u b c n)
W-fsnc : ∀ u b ν → cof b ≡ cΩ ν → ∀ m n → WP (ψ u b) → W (fsnc u b ν m n)
W-fs []       n w = w[]
W-fs (x ∷ xs) n w = W-fsn x xs n w
W-fsn x (y ∷ ys)          n (w∷ wx w) = w∷ wx (W-fsn y ys n w)
W-fsn (ψ u b@(_ ∷ _)) []  n (w∷ wp _) = W-fsn₊ u b (cof b) refl n wp
W-fsn (ψ zero [])     []  n w         = w[]
W-fsn (ψ (suc μ) [])  []  n w         = W-natT n
W-fsn₊ u b c0     e n wp = w[]
W-fsn₊ u b c1     e n wp = W-rep (swapW wp (W-pred b (argW wp))) n
W-fsn₊ u b cω     e n wp = w∷ (swapW wp (W-fs b n (argW wp))) w[]
W-fsn₊ u b (cΩ ν) e n wp = W-fsnc u b ν e (cmp (suc ν) u) n wp
W-fsnc u b zero    e gt n wp = w∷ (swapW wp (W-fsΩ b _ (argW wp) (W-γ b (argW wp) n))) w[]
W-fsnc u b (suc ν) e gt n wp = ⊥-elim (Ω-excl b (argW wp) e)
W-fsnc u b ν       e lt n wp = w∷ (swapW wp (W-fsΩ b _ (argW wp) (W-natT n))) w[]
W-fsnc u b ν       e eq n wp = w∷ (swapW wp (W-fsΩ b _ (argW wp) (W-natT n))) w[]

Top₀-pred : ∀ t → Top₀ t → Top₀ (pred t)
Top₀-pred []                    tp      = t[]
Top₀-pred (ψ zero a ∷ y ∷ ys)   (t∷ tp) = t∷ (Top₀-pred (y ∷ ys) tp)
Top₀-pred (ψ zero (_ ∷ _) ∷ []) tp      = tp
Top₀-pred (ψ zero [] ∷ [])      tp      = t[]

Top₀-fs : ∀ t n → Top₀ t → Top₀ (fs t n)
Top₀-fs []                       n tp      = t[]
Top₀-fs (ψ zero a ∷ y ∷ ys)      n (t∷ tp) = t∷ (Top₀-fs (y ∷ ys) n tp)
Top₀-fs (ψ zero b@(_ ∷ _) ∷ [])  n tp      = Top₀-fsn₊ b (cof b) n
Top₀-fs (ψ zero [] ∷ [])         n tp      = t[]
```

于是 $\{t\mid \mathsf{W}\,t\wedge\mathsf{Top}_0\,t\}$ (即 $\psi_0(\varepsilon_{\Omega+1})$ 以下的项) 对 `pred` 和 `fs` 封闭, 在其上 `FGH ∘ emb₀` 满足表记 FGH 的全部递归方程. 表记这边不需要 `Acc` 证书.

### 7.3 与 EBO 的逐例核对

镜像表记的规则是从 EBO 抄来的; 下面把镜像项翻译成 EBO 的项 (下标 $u\mapsto$ `natT u`), 在一批样例上用 `refl` 核对 $\omega$-基本列与 EBO 的 `fsn↓` 逐字相同 (用 EBO 的可判定比较 `cmpᵀ` 判等). 样例覆盖规则 1, 4, 5ω, 5Ω (ℕ-截断), 6, 以及含 $\psi_2$ 的项 (镜像表记对全部自然数下标定义). 这是逐例检查, 不是一般定理.

```agda
toE  : T → E.T
toEP : P → E.PT
toE []       = []
toE (x ∷ xs) = toEP x ∷ toE xs
toEP (ψ u a) = E.ψ (E.natT u) (toE a)

fsE : T → ℕ → E.T
fsE []       n = []
fsE (x ∷ xs) n = E.trm (E.fsn↓ (toEP x) (toE xs) n)

isEq : E.Cmp → Bool
isEq E.eq = true
isEq _    = false

agree : T → ℕ → Bool
agree t n = isEq (E.cmpᵀ (toE (fs t n)) (fsE t n))

Ω₁ Ω₂ ω : T
Ω₁ = ψ 1 [] ∷ []
Ω₂ = ψ 2 [] ∷ []
ω  = ψ 0 (𝟏 ∷ []) ∷ []

εₜ : T                                            -- ε₀ = ψ₀(Ω₁)
εₜ = ψ 0 Ω₁ ∷ []

samples : List T
samples =
  εₜ ∷ (ψ 0 (ψ 1 Ω₁ ∷ []) ∷ []) ∷ (ψ 0 (ψ 1 (ψ 1 Ω₁ ∷ []) ∷ []) ∷ [])
  ∷ (ψ 0 (ψ 1 (𝟏 ∷ []) ∷ []) ∷ []) ∷ (ψ 0 (ψ 1 [] ∷ 𝟏 ∷ []) ∷ [])
  ∷ (ψ 0 (ψ 1 [] ∷ ω) ∷ []) ∷ (ψ 1 (ψ 1 [] ∷ 𝟏 ∷ []) ∷ []) ∷ (ψ 1 ω ∷ [])
  ∷ (ψ 0 (ψ 1 [] ∷ []) ∷ ψ 0 (ψ 1 [] ∷ ψ 0 (ψ 1 [] ∷ []) ∷ []) ∷ [])
  ∷ (ψ 0 Ω₂ ∷ []) ∷ (ψ 0 (ψ 2 Ω₂ ∷ []) ∷ []) ∷ (ψ 1 Ω₂ ∷ []) ∷ []

allAgree : List T → ℕ → Bool
allAgree []       n = true
allAgree (t ∷ ts) n with agree t n
... | true  = allAgree ts n
... | false = false

_ : allAgree samples 0 ≡ true
_ = refl

_ : allAgree samples 3 ≡ true
_ = refl

_ : agree ω 2 ≡ true
_ = refl

_ : isEq (E.cmpᵀ (toE ω) (toE εₜ)) ≡ false      -- 判等不是平凡的
_ = refl
```

$\Omega$-基本列与 EBO 的 `fsT↓` (证书取 `refl` 与具体的 `<ᵀ` 证明):

```agda
ΩΩ : T                                            -- ψ₁(Ω₁)
ΩΩ = ψ 1 Ω₁ ∷ []

_ : toE (fsΩ ΩΩ (natT 2)) ≡ E.trm (E.fsT↓ (toE ΩΩ) refl (E.natT<Ωs 2 []))
_ = refl

_ : toE (fsΩ (ψ 1 [] ∷ ΩΩ) ω) ≡ E.trm (E.fsT↓ (toE (ψ 1 [] ∷ ΩΩ)) refl (E.hd< (E.lv< E.[]<)))
_ = refl
```

### 7.4 数值核对

$\varepsilon_0=\psi_0(\Omega_1)$: $\varepsilon_0[2]=\psi_0(\psi_0(\psi_0(1)))$, 与 EBO §7.2 相同; $f_{\varepsilon_0}(1)=2$, 与 Fusion §5 相同. 树这边直接算, 没有 `Acc`.

```agda
_ : fs εₜ 2 ≡ ψ 0 (ψ 0 (ψ 0 (𝟏 ∷ []) ∷ []) ∷ []) ∷ []
_ = refl

_ : FGH (emb₀ εₜ) 1 ≡ 2
_ = refl

_ : FGH (emb₀ ω) 2 ≡ 8                            -- f_ω(2) = f₂(2)
_ = refl

bh₂ : T                                           -- ψ₀(ψ₁(Ω₁)): 规则 6 套规则 5Ω
bh₂ = ψ 0 (ψ 1 Ω₁ ∷ []) ∷ []

_ : FGH (emb₀ bh₂) 1 ≡ 2
_ = refl
```

## §8 结论与边界

**已证** (全部 `--safe --without-K`, 无公设、无洞、无 `TERMINATING`, 无 `--no-positivity-check`):

1. 两层树 `O₀ = Tr ⊥ false`, `O₁ = Tr O₀ true` (严格正, `limᵢ` 定义域定义性地是 $O_0$, 无 `coe`); Buchholz 忠实的折叠 `ψ₁₀ : O₁ → O₀` (含规则 6, $\gamma_0=\Omega_0=1$, 链经由到共尾层的直接折叠) 与 `ψ₁₁ : O₁ → O₁` (规则 5Ω 穿透); FGH 对树结构递归.
2. 第 1 层的外延相等是 PER (强 `limᵢ` 条件), 第 0 层是等价关系; `+`, `↑`, `iter`, `ψ₁₀`, `ψ₁₁` 尊重 $\approx$; 每个嵌入的树都自反 (`emb₁-refl`).
3. 镜像表记 (全部自然数下标) 的 `cof`/`pred`/`fsΩ`/`γ`/`fs` 逐条抄自 EBO.
4. **对应定理** `corr₁ : ∀ t → W t → Shape₁ t (cof t)` 与 `corr₀ : ∀ t → W t → Top₀ t → Shape₀ t (cof t)`: 四种共尾度 (0, 后继, $\omega$, $\Omega_1$) 的形状如 §6 表格; 共尾度 $\Omega_{\mu+2}$ 被排除.
5. 推论: `FGH-c1`, `FGH-cω` (树的 FGH 满足表记沿 `pred`/`fs` 的递归方程), `Ω-corr`, `Ω-excl`; 片段 `W ∧ Top₀` 对 `pred`, `fs` 封闭, `W` 对 `fsΩ` 封闭.
6. `refl` 核对: 12 个样例在 $n=0,3$ 上 `fs` 与 EBO `fsn↓` 逐字相同, 两个 `fsΩ` 与 EBO `fsT↓` 相同; $\varepsilon_0[2]$, $f_{\varepsilon_0}(1)=2$, $f_\omega(2)=8$, $f_{\psi_0(\psi_1(\Omega_1))}(1)=2$.

**与 EBO 规则的对应**: 规则 1 (和取末项)、$1[n]=0$、$\Omega_1[\eta]=\eta$、规则 4、规则 5ω、规则 5Ω (穿透)、规则 6 ($\gamma$-链) 在树上与表记上逐条相同, 由对应定理保证. 剩余差异只有哑值, 都不进入定理的结论:

- 表记侧: `fsΩ` 在非 $\Omega$-共尾的输入上 (EBO 用 `()` 排除) 给哑值; `fs` 在 $\Omega$-共尾项上的 ℕ-截断 (`fsnc` 的 `lt`/`eq` 分支, 正规 $\Omega$ 给 `natT n`) 与 EBO 相同, 定理对 $\Omega$-共尾项只断言 `fsΩ`, 不断言 `fs`.
- 嵌入侧: 下标 $\ge 2$ 的主项是哑值 (`emb₀` 给 0, `emb₁` 当作 $\psi_1$), 由前提 `W` 排除; `emb₀` 对不可数主项给 0, 由前提 `Top₀` 排除.
- 镜像表记与 EBO 的一致: 本篇只在样例上用 `refl` 核对; 翻译 `toE` 与 `cof`/`pred`/`fs`/`fsΩ`/`γ` 交换的一般定理 (对全部 ℕ 下标, 无附加条件) 已在 [Translate](Translate.lagda.md) 中证明 (2026-11-01 后补).

**设计上的取舍与遇到的障碍**:

- 任务建议的 `data O : ℕ → Set` (`limᵢ : j < n → (O j → O n) → O n`) 不严格正, Agda 拒绝. BTBO 的 IR 解法带来证明索引的定义域与 `coe`. 本篇用"较低层作参数 + 布尔索引"绕开, 代价是只有两层.
- 逐点 $\approx$ 不足以证 `ψ₁₀` 尊重 $\approx$ (规则 6 的链在两边喂不同的输入). 强 `limᵢ` 条件使 $\approx_1$ 成为 PER; 对称、传递无条件成立 (传递要第 0 层自反), 自反性即遗传外延性, 只需对嵌入证一次. 比 `Good` 谓词少一套保持引理.
- 层级下落 ($\Omega_1[\eta]=\eta$ 从第 1 层落到第 0 层): 用两个嵌入 `emb₀`/`emb₁` 加一致性引理 `↑-emb` 代替 `lv`-索引的嵌入, 下落只在 $\Omega$-情况的陈述里出现一次 ($F$ 吃 `emb₀ η`).
- $\psi_1$ 的参数不提升到第 2 层: 同层折叠 `ψ₁₁` 与"提升后再折叠"逐节点相同 (§2), 因为此时规则 6 不会触发.

**下一步**:

1. **一般有限下标** ($\psi_0(\Omega_\omega)$). 需要对所有 $n$ 的树族 $O_n$, `limᵢ` 的定义域对变量层级也最好定义性地是 $O_j$. 候选: 以较低各层的类型列表为参数 `Tr (Ls : List Set)`, `limᵢ` 的索引用倒序的 `Fin` (`fzero` = 最高的下层); 此时一步提升 $O_n\to O_{n+1}$ 对变量 $n$ 定义性地无 `coe`, 但折叠到变量层 $i$ 的穿透分支仍会卡在 `lookup`. 另一条路是接受 BTBO 式的证明索引, 把 `coe` 的计算行为做成 $\approx$-引理. $\approx$ 的强条件也要推广: 第 $n$ 层的 `limᵢ j` 条件用第 $j$ 层的 $\approx_j$, PER 的传递性对层级归纳.
2. **对角** ($\Omega$-下标为项, 走向 EBO 本身): 层级空间与序数空间同一, 树族的索引需要是树本身, 这是 Mahlo/路线 C 的问题.
3. 可选: 证明 `toE` 与 `cof`/`pred`/`fs`/`fsΩ` 交换, 把 7.3 的逐例核对升级为定理.
