# EBO: 扩展 Buchholz 表记 (对齐纲领的参照表记)

> 交替路线的分支 2 要做"与原版 EBO 基本列逐条一致的树序数" (见 [probes/README.md](../../README.md)). "原版 EBO" 指的就是本文件: Maksudov 的扩展 Buchholz 表记, $\psi_u(a)$ 的下标 $u$ 本身是项, 系统极限 $\mathrm{EBO}=\psi_0(\Lambda)$, $\Lambda$ 为最小的 $\Omega$-不动点 ($\Lambda=\Omega_\Lambda$).
>
> **来源.** 代码逐字取自已归档的 [Notation/EBO](../../../archive/probes/OCF/Notation/EBO.lagda.md) (`OCF.Notation.EBO`): 项、序、`cmpᵀ`、`cof`、`pred`、`Below`、`fsT↓`、`γ↓`、`fsn↓`、`Acc`-FGH 与样例, 定义一字不改; 裸值包装 `fsn` 与 `cof-natT`/`pred-natT`/`fsn₊-eq`/`rep-trm` 取自归档的 [Notation/Fusion](../../../archive/probes/OCF/Notation/Fusion.lagda.md) §1–2. 本文新增的只有 §6: Ω-基本列的裸值 `fsT`、γ-链的裸值 `γT`, 以及"带证书的版本只是裸值加证书"的三条引理 (`fsT↓-trm`, `γ↓-trm`, `fsn0-eq`). 归档冻结, 本文件取代它成为对齐纲领的参照表记; [Omega1](Omega1.lagda.md) 的样例核对与 [Translate](Translate.lagda.md) 的翻译定理都以本文件为准.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机编译指示. 边界 (哑值的清单, `_<ᵀ_` 在非标准形上不良基) 见 §9.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EBO where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
```

## §1 项

每个序数写成主项 (加法不可分解的序数) 的和. 主项只有一种, `ψ u a` $=\psi_u(a)$, 下标 $u$ 与参数 $a$ **都是项**. 和用 `List` 表示, `[]` $=0$; 意图是降序和, 但类型不强制 (见 §9).

下标空间与序数空间是同一个类型, 所以 $\Omega$-下标可以任意嵌套, 系统的极限是 $\Omega$-不动点 $\Lambda$ 之下的 $\psi_0$. 与此对照: 树这边的下标层必须有有界三歧性, 而以精确初始段为下标、含 $\Omega$-共尾元又有有界三歧性的下标类型推出 LPO ([Barrier](../Barrier.lagda.md)). 表记没有这个问题, 因为项是有限语法树, 比较是结构递归 (§2).

```agda
data PT : Set          -- 主项 (principal term)
T : Set                -- 项 = 主项的 (意图降序的) 列表
T = List PT

data PT where
  ψ : (u a : T) → PT   -- ψ_u(a)

pattern 𝟏 = ψ [] []    -- 1 = ψ₀(0)

private variable
  u v a b : T
  x y : PT
  xs ys : T
  n : ℕ
  μ ν : T
```

自然数、后继与 $\Omega$ 数的项. `Ωt μ` $=\Omega_\mu=\psi_\mu(0)$ ($\Omega_0=1$; $\mu$ 为极限时是奇异的 $\Omega_\mu$), `Ωs μ` $=\Omega_{\mu+1}$ (正规基数).

```agda
natT : ℕ → T
natT zero    = []
natT (suc n) = 𝟏 ∷ natT n

sucT : T → T           -- a + 1
sucT a = a ++ (𝟏 ∷ [])

Ωt : T → T             -- Ω_μ := ψ_μ(0)  (Ω₀ = 1; 极限 μ 时为奇异 Ω_μ, 均为合法项)
Ωt μ = ψ μ [] ∷ []

Ωs : T → T             -- Ω_{μ+1} := ψ_{μ+1}(0)  (正规基数刻度)
Ωs μ = ψ (sucT μ) [] ∷ []
```

## §2 序与可判定比较

序是纯语法的字典序: 和 (列表) 逐项比较, 主项先比下标再比参数. 在标准形 (降序且满足 Buchholz 的 $a\in C_u(a)$ 条件) 上这就是序数的序; 在一般的项上它不是良序 (§9).

```agda
infix 4 _<ᵀ_ _<ᴾ_

data _<ᵀ_ : T → T → Set
data _<ᴾ_ : PT → PT → Set

data _<ᵀ_ where
  []< : [] <ᵀ (x ∷ xs)
  hd< : x <ᴾ y → (x ∷ xs) <ᵀ (y ∷ ys)
  tl< : xs <ᵀ ys → (x ∷ xs) <ᵀ (x ∷ ys)

data _<ᴾ_ where
  lv< : u <ᵀ v → ψ u a <ᴾ ψ v b
  ar< : a <ᵀ b → ψ u a <ᴾ ψ u b
```

比较 `cmpᵀ` 对两个项同时结构递归, 是全函数, 不需要任何前提. 下面的共尾度分类 (规则 5/6 的分界 $\mu+1$ 与 $u$ 的比较) 就靠它.

```agda
data Cmp : Set where lt eq gt : Cmp

cmpᵀ : T → T → Cmp
cmpᴾ : PT → PT → Cmp

cmpᵀ [] [] = eq
cmpᵀ [] (y ∷ ys) = lt
cmpᵀ (x ∷ xs) [] = gt
cmpᵀ (x ∷ xs) (y ∷ ys) with cmpᴾ x y
... | lt = lt
... | gt = gt
... | eq = cmpᵀ xs ys

cmpᴾ (ψ u a) (ψ v b) with cmpᵀ u v
... | lt = lt
... | gt = gt
... | eq = cmpᵀ a b
```

## §3 前驱与共尾度

`cof` 把每个项分到四类之一: $0$ (`c0`), 后继 (`c1`), 共尾度 $\omega$ (`cω`), 共尾度 $\Omega_{\mu+1}$ (`cΩ μ`). 它是基本列的路由器. 各条规则:

- 和的共尾度是末项的共尾度.
- $\psi_0(0)=1$ 是后继.
- $\psi_u(0)=\Omega_u$ ($u\ne0$, `cofψ0`, 第二参数是 `cof u`): $u$ 后继时 $\Omega_u$ 正规, 共尾度 $\Omega_u$ 自身, 记作 `cΩ (pred u)`; $u$ 的共尾度为 $\omega$ 或 $\Omega_{\mu+1}$ 时 $\Omega_u$ 奇异, 共尾度随 $u$. `c0` 一行不可达 (调用处 $u$ 非空), 是哑值.
- $\psi_u(b)$, $b\ne0$ (`cofA`, 第二参数是 `cof b`): $b$ 后继 (规则 4) 或共尾度 $\omega$ (规则 5ω) 时为 $\omega$; $b$ 的共尾度为 $\Omega_{\mu+1}$ 时比较 $\mu+1$ 与 $u$ (`cofψ₊`): $\mu+1\le u$ 时共尾度穿透 (规则 5Ω), $\mu+1>u$ 时折叠, 共尾度坍缩为 $\omega$ (规则 6). `c0` 一行不可达, 是哑值.

`pred` 剥掉末尾的一个 $\mathbf 1$; 只对后继项有意义, 其余分支返回原项 (哑值).

`cof` 不用 `with`, 而用一等辅助函数 `cofψ0`/`cofA`/`cofψ₊` 组合. `with` 生成的辅助函数是不透明的, 证明里会卡住归约; 辅助函数则可以在证明侧用显式的等式参数逐情况处理 (§4 `pred-suc`, §6 的 J-对齐).

```agda
data Cof : Set where
  c0 : Cof              -- 零
  c1 : Cof              -- 后继
  cω : Cof              -- 共尾度 ω
  cΩ : (μ : T) → Cof    -- 共尾度 Ω_{μ+1}

pred : T → T            -- 仅对后继项有意义 (剥一个尾部 𝟏); 其余分支为无害哑值
pred [] = []
pred (x ∷ y ∷ ys) = x ∷ pred (y ∷ ys)
pred (𝟏 ∷ []) = []
pred (x ∷ []) = x ∷ []

-- ψ_u(0) = Ω_u 的共尾度, 第二参数 = cof u
cofψ0 : T → Cof → Cof
cofψ0 u c0     = c0                -- 不可达 (调用处 u 非空); 哑值
cofψ0 u c1     = cΩ (pred u)       -- u 后继: Ω_u 正规
cofψ0 u cω     = cω                -- u 极限: Ω_u 奇异, 随 u 的共尾度
cofψ0 u (cΩ μ) = cΩ μ

-- ψ_u(b) (b ≠ 0, cof b = Ω_{μ+1}) 的共尾度, 第三参数 = cmpᵀ (μ+1) u
cofψ₊ : T → T → Cmp → Cof
cofψ₊ u μ lt = cΩ μ                -- 规则 5 (Ω): μ+1 < u, 共尾度穿透
cofψ₊ u μ eq = cΩ μ                -- 规则 5 (Ω): μ+1 = u
cofψ₊ u μ gt = cω                  -- 规则 6: μ+1 > u, 折叠, 共尾度坍缩为 ω

-- ψ_u(b) (b ≠ 0) 的共尾度, 第二参数 = cof b
cofA : T → Cof → Cof
cofA u c0     = cω                 -- 不可达; 哑值
cofA u c1     = cω                 -- 规则 4: ψ_u(b'+1)[n] = ψ_u(b')·n
cofA u cω     = cω                 -- 规则 5 (ω)
cofA u (cΩ μ) = cofψ₊ u μ (cmpᵀ (sucT μ) u)

cof  : T → Cof
cofP : PT → Cof

cof [] = c0
cof (x ∷ []) = cofP x
cof (x ∷ xs@(_ ∷ _)) = cof xs      -- 和的共尾度 = 末项的共尾度

cofP (ψ u (y ∷ ys))  = cofA u (cof (y ∷ ys))
cofP (ψ (w ∷ ws) []) = cofψ0 (w ∷ ws) (cof (w ∷ ws))
cofP 𝟏 = c1
```

## §4 基础引理

```agda
<-sucT : ∀ a → a <ᵀ sucT a               -- a < a+1
<-sucT [] = []<
<-sucT (x ∷ xs) = tl< (<-sucT xs)

[]<sucT : ∀ a → [] <ᵀ sucT a             -- 0 < a+1
[]<sucT [] = []<
[]<sucT (x ∷ xs) = []<

natT<Ωs : ∀ n μ → natT n <ᵀ Ωs μ         -- n < Ω_{μ+1}
natT<Ωs zero    μ = []<
natT<Ωs (suc n) μ = hd< (lv< ([]<sucT μ))
```

后继项的重构: `cof a ≡ c1` 蕴含 `a = pred a + 1`. 证明按 `cof` 的辅助函数逐层拆开等式参数.

```agda
pred-suc : ∀ a → cof a ≡ c1 → sucT (pred a) ≡ a
pred-suc [] ()
pred-suc (x ∷ y ∷ ys) e = cong (x ∷_) (pred-suc (y ∷ ys) e)
pred-suc (𝟏 ∷ []) e = refl
pred-suc (ψ (w ∷ ws) [] ∷ []) e = go (cof (w ∷ ws)) e where
  go : ∀ c → cofψ0 (w ∷ ws) c ≡ c1 → sucT (pred (ψ (w ∷ ws) [] ∷ [])) ≡ ψ (w ∷ ws) [] ∷ []
  go c0 ()
  go c1 ()
  go cω ()
  go (cΩ μ) ()
pred-suc (ψ u (y ∷ ys) ∷ []) e = go (cof (y ∷ ys)) e where
  go : ∀ c → cofA u c ≡ c1 → sucT (pred (ψ u (y ∷ ys) ∷ [])) ≡ ψ u (y ∷ ys) ∷ []
  go c0 ()
  go c1 ()
  go cω ()
  go (cΩ μ) e′ = go′ (cmpᵀ (sucT μ) u) e′ where
    go′ : ∀ m → cofψ₊ u μ m ≡ c1 → sucT (pred (ψ u (y ∷ ys) ∷ [])) ≡ ψ u (y ∷ ys) ∷ []
    go′ lt ()
    go′ eq ()
    go′ gt ()

pred-< : ∀ a → cof a ≡ c1 → pred a <ᵀ a
pred-< a e = subst (pred a <ᵀ_) (pred-suc a e) (<-sucT (pred a))
```

## §5 基本列: 值带递减证书

基本列直接返回 `Below a`: 一个项连同它 $<a$ 的证书. 每个证书都是一两个构造子. FGH (§7) 沿 `Acc` 递归时要的正是这个证书.

```agda
record Below (a : T) : Set where
  constructor _⟨_⟩
  field
    trm : T
    dec : trm <ᵀ a
open Below public

cΩ-inj : cΩ μ ≡ cΩ ν → μ ≡ ν
cΩ-inj refl = refl
```

### 5.1 Ω-基本列 $a[\eta]$

`fsT↓ a e η<` $=a[\eta]$, 前提是 `e : cof a ≡ cΩ μ` 与 `η< : η <ᵀ Ωs μ`. 规则:

- 和: $(x+a)[\eta]=x+a[\eta]$.
- 正规叶 $\Omega_u$, $u=\mu+1$ 后继 (`fsT↓0` 的 `c1` 行): $\Omega_u[\eta]=\eta$. 前提 $\eta<\Omega_{\mu+1}$ 恰好就是递减证书 (经 `pred-suc` 换写).
- 奇异叶 $\Omega_u$, $u$ 的共尾度为 $\Omega_{\mu+1}$ (`cΩ` 行): $\Omega_u[\eta]=\Omega_{u[\eta]}$.
- $\psi_u(b)$, $b$ 的共尾度为 $\Omega_{\nu+1}$ 且 $\nu+1\le u$ (`fsT↓c` 的 `lt`/`eq` 行, 规则 5Ω): $\psi_u(b)[\eta]=\psi_u(b[\eta])$.
- 其余情况 (`cof a` 不是 `cΩ`) 被前提 `e` 用 `()` 排除.

工程注记 (归档原文): 递归经由 where-helper 会让停机检查器丢失 size-change 信息, 所以辅助函数都提升为顶层互递归, 且子项整体作参数传递.

```agda
fsT↓  : ∀ a {μ} → cof a ≡ cΩ μ → ∀ {η} → η <ᵀ Ωs μ → Below a
fsT↓0 : ∀ u c → cof u ≡ c → ∀ {μ} → cofψ0 u c ≡ cΩ μ →
        ∀ {η} → η <ᵀ Ωs μ → Below (ψ u [] ∷ [])
fsT↓₊ : ∀ u b c → cof b ≡ c → ∀ {μ} → cofA u c ≡ cΩ μ →
        ∀ {η} → η <ᵀ Ωs μ → Below (ψ u b ∷ [])
fsT↓c : ∀ u b ν → cof b ≡ cΩ ν → ∀ m {μ} → cofψ₊ u ν m ≡ cΩ μ →
        ∀ {η} → η <ᵀ Ωs μ → Below (ψ u b ∷ [])

fsT↓ [] () η<
fsT↓ (x ∷ xs@(_ ∷ _)) e η< =
  let r = fsT↓ xs e η< in (x ∷ trm r) ⟨ tl< (dec r) ⟩
fsT↓ (ψ u (y ∷ ys) ∷ []) e η< = fsT↓₊ u (y ∷ ys) (cof (y ∷ ys)) refl e η<
fsT↓ (ψ (w ∷ ws) [] ∷ []) e η< = fsT↓0 (w ∷ ws) (cof (w ∷ ws)) refl e η<
fsT↓ (𝟏 ∷ []) () η<

fsT↓0 u c0 ue ()
fsT↓0 u c1 ue e′ {η} η< =          -- 正规叶 Ω_u (u = μ+1): a[η] = η
  η ⟨ subst (λ z → η <ᵀ (ψ z [] ∷ []))
            (trans (cong sucT (sym (cΩ-inj e′))) (pred-suc u ue)) η< ⟩
fsT↓0 u cω ue ()
fsT↓0 u (cΩ ν) ue e′ η< =          -- u 极限: Ω_{u[η]}
  let r = fsT↓ u (trans ue (cong cΩ (cΩ-inj e′))) η<
  in (ψ (trm r) [] ∷ []) ⟨ hd< (lv< (dec r)) ⟩

fsT↓₊ u b c0 be ()
fsT↓₊ u b c1 be ()
fsT↓₊ u b cω be ()
fsT↓₊ u b (cΩ ν) be e′ η< = fsT↓c u b ν be (cmpᵀ (sucT ν) u) e′ η<

fsT↓c u b ν be lt e″ η< =          -- 规则 5 (Ω): 穿透
  let r = fsT↓ b (trans be (cong cΩ (cΩ-inj e″))) η<
  in (ψ u (trm r) ∷ []) ⟨ hd< (ar< (dec r)) ⟩
fsT↓c u b ν be eq e″ η< =
  let r = fsT↓ b (trans be (cong cΩ (cΩ-inj e″))) η<
  in (ψ u (trm r) ∷ []) ⟨ hd< (ar< (dec r)) ⟩
fsT↓c u b ν be gt ()
```

### 5.2 规则 6 的 γ-链

Buchholz 的规则 6: 当 $b$ 的共尾度为 $\Omega_{\mu+1}$ 而 $\mu+1>u$ 时, $\gamma_0=\Omega_\mu$, $\gamma_{k+1}=\psi_\mu(b[\gamma_k])$, $\psi_u(b)[n]=\psi_u(b[\gamma_n])$. 每个 $\gamma_k$ 自带 $<\Omega_{\mu+1}$ 的证书 (两行都是 $\psi_\mu(\cdot)<\psi_{\mu+1}(0)$ 的 `lv<`), 正好喂给下一步的 `fsT↓`.

```agda
γ↓ : ∀ β μ → cof β ≡ cΩ μ → ℕ → Below (Ωs μ)
γ↓ β μ e zero    = Ωt μ ⟨ hd< (lv< (<-sucT μ)) ⟩
γ↓ β μ e (suc k) =
  let g = γ↓ β μ e k
      r = fsT↓ β e (dec g)
  in (ψ μ (trm r) ∷ []) ⟨ hd< (lv< (<-sucT μ)) ⟩
```

### 5.3 ω-基本列 $t[n]$

`fsn↓ x xs n` $=(x\mathbin{::}xs)[n]$. 规则:

1. 和: $(x+a)[n]=x+a[n]$.
2. $1[n]=0$.
3. 奇异叶 $\Omega_u$: $u$ 的共尾度为 $\omega$ 时 $\Omega_u[n]=\Omega_{u[n]}$; 为 $\Omega_{\nu+1}$ 时 $\Omega_u[n]=\Omega_{u[n]}$, 其中 $u[n]$ 取 Ω-基本列在 $\eta=n$ 处的值.
4. $\psi_u(b+1)[n]=\psi_u(b)\cdot n$ (`rep↓`).
5. (ω) $b$ 的共尾度为 $\omega$: $\psi_u(b)[n]=\psi_u(b[n])$.
6. $b$ 的共尾度为 $\Omega_{\nu+1}$ 且 $\nu+1>u$: γ-链, $\psi_u(b)[n]=\psi_u(b[\gamma_n])$.

再加两类只为全函数性存在的分支 (哑值, 见 §9): 正规叶 $\Omega_{\mu+1}$ 给 `natT n`; 规则 5Ω 的情况 ($\nu+1\le u$, 真正的基本列是 $\Omega_{\nu+1}$-索引的) 截断为 $b[n]$. `c0` 两行不可达.

```agda
rep↓ : ∀ u {a a′} → a′ <ᵀ a → (n : ℕ) → Below (ψ u a ∷ [])
rep↓ u a′< zero    = [] ⟨ []< ⟩
rep↓ u a′< (suc n) =
  let r = rep↓ u a′< n
  in (ψ u _ ∷ trm r) ⟨ hd< (ar< a′<) ⟩

fsn↓  : ∀ x xs → ℕ → Below (x ∷ xs)
fsn↓0 : ∀ w ws c → cof (w ∷ ws) ≡ c → ℕ → Below (ψ (w ∷ ws) [] ∷ [])
fsn↓₊ : ∀ u y ys c → cof (y ∷ ys) ≡ c → ℕ → Below (ψ u (y ∷ ys) ∷ [])
fsn↓c : ∀ u y ys ν → cof (y ∷ ys) ≡ cΩ ν → Cmp → ℕ → Below (ψ u (y ∷ ys) ∷ [])

fsn↓ x (y ∷ ys) n =                              -- 规则 1: 和 ⇒ 末项
  let r = fsn↓ y ys n in (x ∷ trm r) ⟨ tl< (dec r) ⟩
fsn↓ (ψ u (y ∷ ys)) [] n = fsn↓₊ u y ys (cof (y ∷ ys)) refl n
fsn↓ (ψ (w ∷ ws) []) [] n = fsn↓0 w ws (cof (w ∷ ws)) refl n
fsn↓ 𝟏 [] n = [] ⟨ []< ⟩                          -- 1[n] = 0

fsn↓0 w ws c0 ue n = [] ⟨ []< ⟩                   -- 不可达哑值
fsn↓0 w ws c1 ue n =                              -- 正规 Ω_u: FGH 用不到, 给 natT n (仍递减)
  natT n ⟨ subst (λ z → natT n <ᵀ (ψ z [] ∷ [])) (pred-suc (w ∷ ws) ue)
                 (natT<Ωs n (pred (w ∷ ws))) ⟩
fsn↓0 w ws cω ue n =                              -- u 极限: Ω_{u[n]}
  let r = fsn↓ w ws n in (ψ (trm r) [] ∷ []) ⟨ hd< (lv< (dec r)) ⟩
fsn↓0 w ws (cΩ ν) ue n =
  let r = fsT↓ (w ∷ ws) ue (natT<Ωs n ν)
  in (ψ (trm r) [] ∷ []) ⟨ hd< (lv< (dec r)) ⟩

fsn↓₊ u y ys c0 be n = [] ⟨ []< ⟩                 -- 不可达哑值
fsn↓₊ u y ys c1 be n = rep↓ u (pred-< (y ∷ ys) be) n  -- 规则 4: ψ_u(b+1)[n] = ψ_u(b)·n
fsn↓₊ u y ys cω be n =                            -- 规则 5 (ω)
  let r = fsn↓ y ys n in (ψ u (trm r) ∷ []) ⟨ hd< (ar< (dec r)) ⟩
fsn↓₊ u y ys (cΩ ν) be n = fsn↓c u y ys ν be (cmpᵀ (sucT ν) u) n

fsn↓c u y ys ν be gt n =                          -- 规则 6: γ-链折叠
  let g = γ↓ (y ∷ ys) ν be n
      r = fsT↓ (y ∷ ys) be (dec g)
  in (ψ u (trm r) ∷ []) ⟨ hd< (ar< (dec r)) ⟩
fsn↓c u y ys ν be lt n =                          -- 规则 5 (Ω) 的 ℕ-截断 (见注记)
  let r = fsT↓ (y ∷ ys) be (natT<Ωs n ν)
  in (ψ u (trm r) ∷ []) ⟨ hd< (ar< (dec r)) ⟩
fsn↓c u y ys ν be eq n =
  let r = fsT↓ (y ∷ ys) be (natT<Ωs n ν)
  in (ψ u (trm r) ∷ []) ⟨ hd< (ar< (dec r)) ⟩
```

注记: 规则 5Ω 的真基本列是 $\Omega_{\nu+1}$-索引的; FGH 只喂自然数, 而可数项的共尾度只会是 `c0`/`c1`/`cω`, 所以 `fsn↓c` 的 `lt`/`eq` 行与 `fsn↓0` 的 `c1` 行 (正规叶) 只为全函数性存在. 它们仍带递减证书, 只是值无序数意义.

## §6 裸值

翻译定理 ([Translate](Translate.lagda.md)) 在裸值上陈述. `fsn` 是 `fsn↓` 去掉证书 (取自 Fusion §1); `fsT`, `γT` 是 `fsT↓`, `γ↓` 的裸值版本, 子句结构逐条照抄, 在 `fsT↓` 用 `()` 排除的分支给出哑值. 这些哑值可以任意选 (带证书的版本在那里没有定义); 这里选成与 [Omega1](Omega1.lagda.md) 镜像表记 `fsΩ` 的哑值相同 (`𝟏 ∷ []` 与 `[]` 给 `[]`, 非 Ω-共尾的主项返回自身), 于是翻译定理对 Ω-基本列也无需前提.

```agda
fsn : T → ℕ → T
fsn [] n = []
fsn (x ∷ xs) n = trm (fsn↓ x xs n)

fsT  : T → T → T
fsT0 : T → Cof → T → T              -- 第二参数 = cof u
fsT₊ : T → T → Cof → T → T          -- 第三参数 = cof b
fsTc : T → T → T → Cmp → T → T      -- 第四参数 = cmpᵀ (ν+1) u

fsT []                   η = []      -- 哑值 (fsT↓: 不可达)
fsT (x ∷ xs@(_ ∷ _))     η = x ∷ fsT xs η
fsT (ψ u (y ∷ ys) ∷ [])  η = fsT₊ u (y ∷ ys) (cof (y ∷ ys)) η
fsT (ψ (w ∷ ws) [] ∷ []) η = fsT0 (w ∷ ws) (cof (w ∷ ws)) η
fsT (𝟏 ∷ [])             η = []      -- 哑值 (fsT↓: 不可达)

fsT0 u c0     η = ψ u [] ∷ []        -- 哑值
fsT0 u c1     η = η                  -- 正规叶: Ω_{μ+1}[η] = η
fsT0 u cω     η = ψ u [] ∷ []        -- 哑值
fsT0 u (cΩ ν) η = ψ (fsT u η) [] ∷ []

fsT₊ u b c0     η = ψ u b ∷ []       -- 哑值
fsT₊ u b c1     η = ψ u b ∷ []       -- 哑值
fsT₊ u b cω     η = ψ u b ∷ []       -- 哑值
fsT₊ u b (cΩ ν) η = fsTc u b ν (cmpᵀ (sucT ν) u) η

fsTc u b ν lt η = ψ u (fsT b η) ∷ [] -- 规则 5 (Ω): 穿透
fsTc u b ν eq η = ψ u (fsT b η) ∷ []
fsTc u b ν gt η = ψ u b ∷ []         -- 哑值 (fsT↓: 不可达)

γT : T → T → ℕ → T
γT β μ zero    = Ωt μ
γT β μ (suc k) = ψ μ (fsT β (γT β μ k)) ∷ []
```

**带证书的版本只是裸值加证书.** 对每个合法输入 (`fsT↓` 的前提成立), `trm (fsT↓ a e η<)` 就是 `fsT a η`. 证明按 `fsT↓` 的子句逐条走; 辅助函数的 `cof`/`cmpᵀ` 参数是普通值, 调用处取 `refl` 即与 `fsT` 内部的分派对齐.

```agda
fsT↓-trm  : ∀ a {μ} (e : cof a ≡ cΩ μ) {η} (η< : η <ᵀ Ωs μ) → trm (fsT↓ a e η<) ≡ fsT a η
fsT↓0-trm : ∀ u c (ue : cof u ≡ c) {μ} (e′ : cofψ0 u c ≡ cΩ μ) {η} (η< : η <ᵀ Ωs μ) →
            trm (fsT↓0 u c ue e′ η<) ≡ fsT0 u c η
fsT↓₊-trm : ∀ u b c (be : cof b ≡ c) {μ} (e′ : cofA u c ≡ cΩ μ) {η} (η< : η <ᵀ Ωs μ) →
            trm (fsT↓₊ u b c be e′ η<) ≡ fsT₊ u b c η
fsT↓c-trm : ∀ u b ν (be : cof b ≡ cΩ ν) m {μ} (e″ : cofψ₊ u ν m ≡ cΩ μ) {η} (η< : η <ᵀ Ωs μ) →
            trm (fsT↓c u b ν be m e″ η<) ≡ fsTc u b ν m η

fsT↓-trm [] () η<
fsT↓-trm (x ∷ xs@(_ ∷ _)) e η< = cong (x ∷_) (fsT↓-trm xs e η<)
fsT↓-trm (ψ u (y ∷ ys) ∷ []) e η< = fsT↓₊-trm u (y ∷ ys) (cof (y ∷ ys)) refl e η<
fsT↓-trm (ψ (w ∷ ws) [] ∷ []) e η< = fsT↓0-trm (w ∷ ws) (cof (w ∷ ws)) refl e η<
fsT↓-trm (𝟏 ∷ []) () η<

fsT↓0-trm u c0 ue () η<
fsT↓0-trm u c1 ue e′ η< = refl
fsT↓0-trm u cω ue () η<
fsT↓0-trm u (cΩ ν) ue e′ η< =
  cong (λ z → ψ z [] ∷ []) (fsT↓-trm u (trans ue (cong cΩ (cΩ-inj e′))) η<)

fsT↓₊-trm u b c0 be () η<
fsT↓₊-trm u b c1 be () η<
fsT↓₊-trm u b cω be () η<
fsT↓₊-trm u b (cΩ ν) be e′ η< = fsT↓c-trm u b ν be (cmpᵀ (sucT ν) u) e′ η<

fsT↓c-trm u b ν be lt e″ η< =
  cong (λ z → ψ u z ∷ []) (fsT↓-trm b (trans be (cong cΩ (cΩ-inj e″))) η<)
fsT↓c-trm u b ν be eq e″ η< =
  cong (λ z → ψ u z ∷ []) (fsT↓-trm b (trans be (cong cΩ (cΩ-inj e″))) η<)
fsT↓c-trm u b ν be gt () η<

γ↓-trm : ∀ β μ (e : cof β ≡ cΩ μ) k → trm (γ↓ β μ e k) ≡ γT β μ k
γ↓-trm β μ e zero    = refl
γ↓-trm β μ e (suc k) =
  cong (λ z → ψ μ z ∷ [])
       (trans (fsT↓-trm β e (dec (γ↓ β μ e k))) (cong (fsT β) (γ↓-trm β μ e k)))
```

**自然数的项与 J-对齐** (取自 Fusion §2). `fsn` 内部按 `cof b` 的**计算值**分派, 证明侧手里只有**命题等式** `be : cof b ≡ k`; 对 `be` 匹配 `refl` 即让两者对齐 (`fsn₊-eq`, `fsn0-eq`), 不需要任何 `with` 重放. `fsn0-eq` 是新增的同型引理, 处理 $\Omega_u$ 叶.

```agda
cof-natT : ∀ k → cof (natT (suc k)) ≡ c1
cof-natT zero    = refl
cof-natT (suc k) = cof-natT k

pred-natT : ∀ k → pred (natT (suc k)) ≡ natT k
pred-natT zero    = refl
pred-natT (suc k) = cong (𝟏 ∷_) (pred-natT k)

fsn₊-eq : ∀ u y ys n {k} (be : cof (y ∷ ys) ≡ k) →
          fsn (ψ u (y ∷ ys) ∷ []) n ≡ trm (fsn↓₊ u y ys k be n)
fsn₊-eq u y ys n refl = refl

fsn0-eq : ∀ w ws n {k} (ue : cof (w ∷ ws) ≡ k) →
          fsn (ψ (w ∷ ws) [] ∷ []) n ≡ trm (fsn↓0 w ws k ue n)
fsn0-eq w ws n refl = refl

rep-trm : ∀ u {b b′} (p : b′ <ᵀ b) n → trm (rep↓ u {b} {b′} p n) ≡ replicate n (ψ u b′)
rep-trm u p zero    = refl
rep-trm u p (suc n) = cong (ψ u _ ∷_) (rep-trm u p n)
```

## §7 FGH: 沿 Acc 递归

`Acc` 是停机检查器认可的超限递归: 构造子 `acc` 的字段在结构上变小, FGH 对 `Acc` 参数结构递归, 无公理. 代价是每个具体的项都要给出 `Acc` 证书 (§9).

```agda
data Acc (a : T) : Set where
  acc : (∀ {b} → b <ᵀ a → Acc b) → Acc a

iter : (ℕ → ℕ) → ℕ → ℕ → ℕ
iter f x zero    = x
iter f x (suc k) = f (iter f x k)

FGH : ∀ a → Acc a → ℕ → ℕ
FGH [] _ n = suc n
FGH (x ∷ xs) (acc rs) n = go (cof (x ∷ xs)) refl where
  go : ∀ c → cof (x ∷ xs) ≡ c → ℕ
  go c0 ce = suc n                                -- 不可达哑值
  go c1 ce = iter (FGH (pred (x ∷ xs)) (rs (pred-< (x ∷ xs) ce))) n n
  go cω ce = let r = fsn↓ x xs n in FGH (trm r) (rs (dec r)) n
  go (cΩ μ) ce = let r = fsn↓ x xs n in FGH (trm r) (rs (dec r)) n
```

`cΩ` 一行是哑值: 它对不可数共尾的项用 ℕ-截断的基本列继续递归; FGH 的输入是可数项, 不会走到这里.

## §8 样例

### 8.1 Ω-塔与比较

$\psi_0(\Omega_{\Omega_\Omega})$ 是一个具体的项, 与 Ω-塔的下一项可判定地比较, `refl` 直接算出.

```agda
ΩTower : ℕ → T          -- 1, Ω, Ω_Ω, Ω_Ω_Ω, ...
ΩTower zero    = natT 1
ΩTower (suc k) = Ωt (ΩTower k)

ψΩΩΩ : T                -- ψ₀(Ω_{Ω_Ω})
ψΩΩΩ = ψ [] (ΩTower 3) ∷ []

EBOψ : ℕ → T            -- ψ₀(Ω-塔_n), n → ∞ 趋于 EBO = ψ₀(Λ)
EBOψ n = ψ [] (ΩTower n) ∷ []

_ : cmpᵀ ψΩΩΩ (EBOψ 4) ≡ lt
_ = refl

_ : cmpᵀ (EBOψ 4) ψΩΩΩ ≡ gt
_ = refl

_ : cmpᵀ ψΩΩΩ ψΩΩΩ ≡ eq
_ = refl
```

### 8.2 ε₀ = ψ₀(Ω) 的 γ-链

$\psi_0(\Omega)[2]=\psi_0(\psi_0(\psi_0(1)))=\omega^{\omega^\omega}$ ($\gamma_0=\Omega_0=1$, $\gamma_1=\psi_0(\Omega[\gamma_0])=\omega$, $\gamma_2=\psi_0(\omega)=\omega^\omega$):

```agda
εₒ : T
εₒ = ψ [] (Ωt (natT 1)) ∷ []

_ : trm (fsn↓ (ψ [] (Ωt (natT 1))) [] 2)
  ≡ ψ [] (ψ [] (ψ [] (𝟏 ∷ []) ∷ []) ∷ []) ∷ []
_ = refl
```

### 8.3 FGH 的底段

```agda
acc[] : Acc []
acc[] = acc λ ()

acc-1∷ : ∀ {xs} → Acc xs → Acc (𝟏 ∷ xs)
acc-1∷ (acc rs) = acc go where
  go : ∀ {b} → b <ᵀ (𝟏 ∷ _) → Acc b
  go []<             = acc[]
  go (hd< (lv< ()))
  go (hd< (ar< ()))
  go (tl< q)         = acc-1∷ (rs q)

accNat : ∀ n → Acc (natT n)
accNat zero    = acc[]
accNat (suc n) = acc-1∷ (accNat n)

_ : FGH (natT 2) (accNat 2) 2 ≡ 8        -- f₂(2) = 2²·2 = 8
_ = refl

_ : FGH (natT 3) (accNat 3) 2 ≡ 2048     -- f₃(2) = f₂(f₂(2)) = f₂(8) = 2⁸·8 = 2048
_ = refl
```

大数只差 `Acc` 证书:

```agda
EBO-number : (∀ n → Acc (EBOψ n)) → ℕ → ℕ
EBO-number wf n = FGH (EBOψ n) (wf n) n
```

## §9 边界

**哑值清单.** 下列分支只为全函数性存在, 值无序数意义:

| 位置 | 情况 | 值 |
|---|---|---|
| `pred` | 非后继项 | 原项 |
| `cofψ0` `c0`, `cofA` `c0` | 不可达 (参数非空) | `c0`, `cω` |
| `fsn↓0` `c0`, `fsn↓₊` `c0` | 不可达 | `[]` |
| `fsn↓0` `c1` | 正规叶 $\Omega_{\mu+1}$ 的 ω-基本列 | `natT n` |
| `fsn↓c` `lt`/`eq` | 规则 5Ω 的 ℕ-截断 | $\psi_u(b[n])$ |
| `FGH` `go c0`, `go (cΩ μ)` | 零 (不可达) / 不可数共尾 | `suc n` / 沿截断基本列 |
| `fsT`, `fsT0`, `fsT₊`, `fsTc` (§6) | `fsT↓` 用 `()` 排除的输入 | `[]` 或原主项 |

带证书的 `fsT↓` 没有哑值 (不合法的输入被类型排除); 它的裸值 `fsT` 的哑值是自由选择, §6 的 `fsT↓-trm` 只在合法输入上断言两者一致.

**`_<ᵀ_` 在全部项上不良基.** 纯语法的无穷降链

    ω  >  1 + ω  >  1 + 1 + ω  >  1 + 1 + 1 + ω  >  ...

即 `ψ [] (𝟏 ∷ []) ∷ []` $>$ `𝟏 ∷ ψ [] (𝟏 ∷ []) ∷ []` $>$ ..., 每步由 `hd<`/`tl<` 导出 (首项 $1<\omega$). 这些项不是标准形 (非降序), 指称相同, 但语法序严格下降. 所以 `Acc` 证书只能在标准形 (降序 + ψ-standardness) 上指望, 需要: 标准形谓词; `fsn↓` 与 `pred` 保持标准形; `_<ᵀ_` 在标准形上良基. 这三条本文都没有做. 对齐纲领的设想是绕开它: 树这边的良基性是免费的, 只要树的基本列与表记逐条一致, 表记的 FGH 递归方程就在树上成立 ([Finite](Finite.lagda.md), [Omega1](Omega1.lagda.md)).

**下标为自然数的片段.** [Translate](Translate.lagda.md) 证明: 下标全是 `natT k` 的 EBO 项恰好是 Omega1 镜像表记的像, 在这个子集上 `cof`, `pred`, `fsn`, `fsT`, `γT` 与镜像表记逐字对应 (无前提). 下标是一般项 (极限下标 $\Omega_\omega$、$\Omega_{\Omega}$ 等) 的部分尚无树侧对应.

## 参考

- W. Buchholz, *A new system of proof-theoretic ordinal functions*, APAL 32 (1986).
- D. Maksudov, extended Buchholz function 及其基本列 (googology wiki).
- 归档原文: [Notation/EBO](../../../archive/probes/OCF/Notation/EBO.lagda.md), [Notation/Fusion](../../../archive/probes/OCF/Notation/Fusion.lagda.md).
