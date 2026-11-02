# EBOᴵ: EBO 的不可达层保守扩张 (规则基本列)

> 项系统 Tᴵ = EBO 的项 + `I` + `ψI a`, 只到一个 $I$ (无 $I_\nu$, 无 χ, 无 M). 下标空间仍等于项空间. 本文件只导入 [EBO](EBO.lagda.md) 与标准库, 是独立于树的标尺.
>
> **定理 (无前提, 对全部项).**
>
> 1. **保守性 (§7).** 嵌入 `ιT : E.T → T` 满足 `cmpᵀ (ιT s) (ιT t) ≡ E.cmpᵀ s t`, `cof (ιT t) ≡ ιc (E.cof t)`, `fsT`, `γT`, `pred` 同理, 以及关键的 **`fsn (ιT t) n ≡ ιT (E.fsn t n)`**. 没有例外项, 连 EBO 的哑值也相同. 标准形同样保守: `isNF (ιT t) ≡ isOTᵉ t`, 后者是 p進大好きbot 的 EBO 谓词的原样转写 (§9).
> 2. **$\psi_0(\Lambda)[n]$ 就是 EBO 的 `EBOψ n`, 对一切 $n$** (`ψ₀Λ-tower`, §8). $\mathrm{EBO}=\psi_0(\Lambda)$ 在这里是一个项.
> 3. **总函数与递减 (§5–§6).** `cmpᵀ`, `cof`, `fsT`, `γT`, `fsn` 在 `--safe` 下全部总函数; `fsn-dec`, `fsT-dec` 给出递减证书, `fsn-lt` 说它在判定序下也递减 (§9.2).
> 4. **片段封闭性 (§9.1).** $\Lambda[n]$, $\psi_0(\Lambda)[n]$, $\psi_I(b+1)[n]$ (前提 $\psi_I(b)\in$ NF), $\psi_I(\omega)[n]$, $I[\eta]$ 留在 `NFᴵ` 内.
>
> **约定.** $\psi_I(0)=\Lambda$, 由 EBO 的 $\Omega_0=1$ 逼出, 与 Setzer 的 $\psi_I 0$ 一致, 与 $T_W$ 差一个下标. $\Omega_f=f$ 对不动点 $f$, 同 Setzer. 序把 $f$ 当作 $\psi_f(0)$ 比较. 共尾度 $I$ 与 $\Omega_{\mu+1}$ 共用一条分派: 比较下标, 只在目标为 $\psi_I$ 时把 $\le$ 换成 $<$.
>
> **只有测试, 没有证明 (§10).** 新规则的正确性. 用归档的 Setzer 定义本身跑: 1489 个小项上 `isNF` 等于 `isOT ∘ τ`, 1000 项的全部 $10^6$ 对比较无一例不一致, 3480 步展开不离开 OT 且递减单调. Python 转写上 66650 步、20000 项同样无例外. 这不是良基性, 也不是封闭性.
>
> **没有证明.** 全系统的 NF 封闭性、良基性、τ 保序、项的值语义. **失败项.** 到 I 层**不**与 $T_W$ 逐项一致, 只有 EBO 这一段一致 (§10); 差异是 $1+a$ 吸收的错位. `cmpᵀ` 的 `lt` 不蕴含 `_<ᵀ_`, 反例是别名, 只在 NF 外 (§9.2).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EBOI where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

import OCF.Align.EBO as E
open E using (Cmp; lt; eq; gt) public
```

## §1 项

EBO 的项 (`ψ u a`, 下标 $u$ 与参数 $a$ 都是项) 加两个新的主项: `I` 是最小的弱不可达基数, `ψI a` $=\psi_I(a)$ 是 $I$ 之下的第 $a$ 个 $\psi_I$-值.

**下标约定.** $\Lambda$ 取作 `ψI []`, 即 $\psi_I(0)=\Lambda$. 这不是从社区系统 $T_W$ 照抄 (那里 $\psi_I(0)=1$, $\psi_I(1)=\Lambda$), 而是 EBO 的约定 $\Omega_0=1$ 的直接后果: $\psi_I(0)$ 是空集在 $+,\Omega$ 下的闭包; $T_W$ 里 $\Omega_0=0$, 所以这个闭包是 $\{0\}$, 值为 $1$; EBO 里 $\Omega_0=1$, 闭包马上含 $1,\Omega_1,\Omega_{\Omega_1},\dots$, 值就是 $\Lambda$. Setzer 的 $\psi_I 0$ 同样是第一个 Ω-不动点 ([Order](../../../archive/src/Mahlo/Inacc/Order.lagda.md) §3). 所以这个约定同时满足"$\Lambda$ 是项"与"与 OT_I 不错位". 对应是 `ψI a` $=\psi^{T_W}_I(1+a)$.

```agda
data PT : Set
T : Set
T = List PT

data PT where
  ψ  : (u a : T) → PT    -- ψ_u(a), 与 EBO 相同
  ψI : (a : T) → PT      -- ψ_I(a)
  I  : PT                -- I

pattern 𝟏 = ψ [] []

private variable
  u v a b : T
  x y f : PT
  xs ys : T
  n : ℕ
  μ ν : T

Λ : T                    -- 最小的 Ω-不动点
Λ = ψI [] ∷ []

𝐈 : T
𝐈 = I ∷ []

natT : ℕ → T
natT zero    = []
natT (suc n) = 𝟏 ∷ natT n

sucT : T → T
sucT a = a ++ (𝟏 ∷ [])

Ωs : T → T               -- Ω_{μ+1}: μ+1 是后继, 不会是不动点, 无需特判
Ωs μ = ψ (sucT μ) [] ∷ []
```

**不动点 $Fi$.** `Fi f` 说 $f$ 是 `I` 或 `ψI a`. 这些值满足 $\Omega_f=f$, 与 Setzer 的 Def 2.10 `Ω a = if isFiT a then a else Ω′ a` 相同; 所以 `ψ (f ∷ []) []` 是 $f$ 的语法别名, 被标准形排除 (§9), 而基本列的输出一律走下面的灵巧构造子 `Ω̂`/`ψ̂`, 不产生别名.

这是相对 EBO 规则的**唯一**形状改动: EBO 写 $\Omega_{u[\eta]}$ 与 $\psi_u(b[\eta])$ 的地方, 这里写 `Ω̂`/`ψ̂`. 在 EBO 的项上它们就是原来的构造子 (§7.3 `Ω̂-ι`, `ψ̂-ι`), 所以这不改变 EBO 的任何一条规则. 不走灵巧构造子则有实例: $\psi_0(\Omega_{I+\omega})[0]$ 会是 $\psi_0(\Omega_I)$, 而 $\psi_\Lambda(\omega)[0]$ 会是 $\psi_\Lambda(0)$, 都是别名, 不在标准形里.

```agda
data Fi : PT → Set where
  Fi-I : Fi I
  Fi-ψ : Fi (ψI a)

Ω̂ : T → PT               -- Ω_u, 在 Fi 上是恒等 (Setzer: Ω a = a)
Ω̂ (ψI a ∷ []) = ψI a
Ω̂ (I ∷ [])    = I
Ω̂ u           = ψ u []

ψ̂ : T → T → PT           -- ψ_u(a), a = 0 时走 Ω̂
ψ̂ u []       = Ω̂ u
ψ̂ u (y ∷ ys) = ψ u (y ∷ ys)
```

## §2 序与可判定比较

**唯一的新思想: 把不动点 $f$ 当成 $\psi_{f}(0)$.** 因为 $\Omega_f=f$, 按 EBO 的字典序就该比较下标:

- $\psi_u(a)$ 对 $f$: 先比 $u$ 与 $f$. $u<f$ 时 $\psi_u(a)<\Omega_{u+1}\le f$; $u>f$ 时 $\psi_u(a)\ge\Omega_u>u>f$; $u=f$ 时 $a=0$ 是别名 (`eq`), 否则 $\psi_f(a)>f$.
- `ψI a` 之间比参数, `ψI a` $<$ `I`.

这与 Setzer 的 (≺′5)–(≺′11) 在我试过的样本上一致 (§10); 没有证明.

```agda
infix 4 _<ᵀ_ _<ᴾ_

data _<ᵀ_ : T → T → Set
data _<ᴾ_ : PT → PT → Set

data _<ᵀ_ where
  []< : [] <ᵀ (x ∷ xs)
  hd< : x <ᴾ y → (x ∷ xs) <ᵀ (y ∷ ys)
  tl< : xs <ᵀ ys → (x ∷ xs) <ᵀ (x ∷ ys)

data _<ᴾ_ where
  lv<   : u <ᵀ v → ψ u a <ᴾ ψ v b
  ar<   : a <ᵀ b → ψ u a <ᴾ ψ u b
  ψ<Fi  : Fi f → u <ᵀ (f ∷ []) → ψ u a <ᴾ f
  Fi<ψ  : Fi f → (f ∷ []) <ᵀ u → f <ᴾ ψ u a
  Fi<ar : Fi f → f <ᴾ ψ (f ∷ []) (y ∷ ys)
  ψI<ψI : a <ᵀ b → ψI a <ᴾ ψI b
  ψI<I  : ψI a <ᴾ I
```

比较 `cmpᵀ` 不能直接把单元素表 `f ∷ []` 传给自身: 那会在实参上**新造**构造子, 停机检查器在 $\psi$ 对 $f$ 与 $f$ 对 $\psi$ 的交替链上丢掉下降. 所以把"项对单元素表"写成两个专用函数 `cmpᵀ¹`/`cmp¹ᵀ`, 让 $f$ 原样传递. `thenC` 是字典序的一等写法, 不用 `with`, 证明里不会卡住.

```agda
thenC : Cmp → Cmp → Cmp
thenC lt _ = lt
thenC eq c = c
thenC gt _ = gt

pos0 neg0 : T → Cmp      -- 参数是否为 0
pos0 []      = eq
pos0 (_ ∷ _) = gt
neg0 []      = eq
neg0 (_ ∷ _) = lt

cmpᵀ  : T → T → Cmp
cmpᴾ  : PT → PT → Cmp
cmpᵀ¹ : T → PT → Cmp     -- u 对 f ∷ []
cmp¹ᵀ : PT → T → Cmp     -- f ∷ [] 对 v

cmpᵀ [] [] = eq
cmpᵀ [] (y ∷ ys) = lt
cmpᵀ (x ∷ xs) [] = gt
cmpᵀ (x ∷ xs) (y ∷ ys) = thenC (cmpᴾ x y) (cmpᵀ xs ys)

cmpᵀ¹ [] f = lt
cmpᵀ¹ (x ∷ xs) f = thenC (cmpᴾ x f) (pos0 xs)
cmp¹ᵀ f [] = gt
cmp¹ᵀ f (y ∷ ys) = thenC (cmpᴾ f y) (neg0 ys)

cmpᴾ (ψ u a) (ψ v b)  = thenC (cmpᵀ u v) (cmpᵀ a b)
cmpᴾ (ψ u a) (ψI b)   = thenC (cmpᵀ¹ u (ψI b)) (pos0 a)
cmpᴾ (ψ u a) I        = thenC (cmpᵀ¹ u I) (pos0 a)
cmpᴾ (ψI a) (ψ v b)   = thenC (cmp¹ᵀ (ψI a) v) (neg0 b)
cmpᴾ I (ψ v b)        = thenC (cmp¹ᵀ I v) (neg0 b)
cmpᴾ (ψI a) (ψI b)    = cmpᵀ a b
cmpᴾ (ψI a) I         = lt
cmpᴾ I (ψI b)         = gt
cmpᴾ I I              = eq
```

## §3 前驱与共尾度

**一个分派代替两个.** 规则共尾度只有两种: $\Omega_{\mu+1}$ 与 $I$. 把它们并成 `Rg`, 下标 `idx r` 满足 $\Omega_{\mathrm{idx}\,r}=$ 那个基数 ($I$ 是不动点, 所以 `idx Ir = I`). EBO 的分界"比较 $\mu+1$ 与 $u$"于是原样覆盖 $I$: 比较 `idx r` 与 $u$, $\le$ 时穿透, $>$ 时折叠. 目标是 $\psi_I$ 时比较 `idx r` 与 $I$: **严格** $<$ 时穿透, 否则折叠. 这是与 $\psi_u$ 唯一的不对称, 来自 $\psi_u$ 的值域上界是 $\Omega_{u+1}$ 而 $\psi_I$ 的上界是 $I$ 自身 (对应 $T_W$ 规则 10/11 的 $\mathrm{cof}(\beta)<\pi$ 与 $\mathrm{cof}(\beta)\ge\pi$).

```agda
data Rg : Set where
  Ωr : (μ : T) → Rg      -- Ω_{μ+1}
  Ir : Rg                -- I

⟦_⟧ : Rg → T             -- 基数本身
⟦ Ωr μ ⟧ = Ωs μ
⟦ Ir ⟧   = 𝐈

idx : Rg → T             -- Ω_{idx r} = ⟦ r ⟧
idx (Ωr μ) = sucT μ
idx Ir     = 𝐈

data Cof : Set where
  c0 c1 cω : Cof
  cR : Rg → Cof

pattern cΩ μ = cR (Ωr μ)
pattern cI   = cR Ir

pred : T → T             -- 与 EBO 同形: 剥一个尾部 𝟏
pred [] = []
pred (x ∷ y ∷ ys) = x ∷ pred (y ∷ ys)
pred (𝟏 ∷ []) = []
pred (x ∷ []) = x ∷ []

cofψ0 : T → Cof → Cof    -- ψ_u(0) = Ω_u, 第二参数 = cof u
cofψ0 u c0     = c0
cofψ0 u c1     = cΩ (pred u)
cofψ0 u cω     = cω
cofψ0 u (cR r) = cR r

cofψ₊ : Rg → Cmp → Cof   -- 第二参数 = cmpᵀ (idx r) u
cofψ₊ r lt = cR r        -- ρ ≤ u: 穿透
cofψ₊ r eq = cR r
cofψ₊ r gt = cω          -- ρ > u: 折叠

cofA : T → Cof → Cof     -- ψ_u(b), b ≠ 0, 第二参数 = cof b
cofA u c0     = cω
cofA u c1     = cω
cofA u cω     = cω
cofA u (cR r) = cofψ₊ r (cmpᵀ (idx r) u)

cofIc : Rg → Cmp → Cof   -- 第二参数 = cmpᵀ (idx r) 𝐈
cofIc r lt = cR r        -- ρ < I: 穿透
cofIc r eq = cω          -- ρ = I: 折叠
cofIc r gt = cω          -- ρ > I: 折叠

cofI : Cof → Cof         -- ψ_I(b), b ≠ 0
cofI c0     = cω
cofI c1     = cω
cofI cω     = cω
cofI (cR r) = cofIc r (cmpᵀ (idx r) 𝐈)

cof  : T → Cof
cofP : PT → Cof

cof [] = c0
cof (x ∷ []) = cofP x
cof (x ∷ xs@(_ ∷ _)) = cof xs

cofP (ψ u (y ∷ ys))  = cofA u (cof (y ∷ ys))
cofP (ψ (w ∷ ws) []) = cofψ0 (w ∷ ws) (cof (w ∷ ws))
cofP 𝟏 = c1
cofP (ψI [])       = cω
cofP (ψI (y ∷ ys)) = cofI (cof (y ∷ ys))
cofP I = cI
```

## §4 基础引理

```agda
<-sucT : ∀ a → a <ᵀ sucT a
<-sucT [] = []<
<-sucT (x ∷ xs) = tl< (<-sucT xs)

[]<sucT : ∀ a → [] <ᵀ sucT a
[]<sucT [] = []<
[]<sucT (x ∷ xs) = []<

natT<⟦⟧ : ∀ n r → natT n <ᵀ ⟦ r ⟧
natT<⟦⟧ zero    (Ωr μ) = []<
natT<⟦⟧ (suc n) (Ωr μ) = hd< (lv< ([]<sucT μ))
natT<⟦⟧ zero    Ir     = []<
natT<⟦⟧ (suc n) Ir     = hd< (ψ<Fi Fi-I []<)

pred-suc : ∀ a → cof a ≡ c1 → sucT (pred a) ≡ a
pred-suc [] ()
pred-suc (x ∷ y ∷ ys) e = cong (x ∷_) (pred-suc (y ∷ ys) e)
pred-suc (𝟏 ∷ []) e = refl
pred-suc (ψ (w ∷ ws) [] ∷ []) e = go (cof (w ∷ ws)) e where
  go : ∀ c → cofψ0 (w ∷ ws) c ≡ c1 → sucT (pred (ψ (w ∷ ws) [] ∷ [])) ≡ ψ (w ∷ ws) [] ∷ []
  go c0 ()
  go c1 ()
  go cω ()
  go (cR r) ()
pred-suc (ψ u (y ∷ ys) ∷ []) e = go (cof (y ∷ ys)) e where
  go : ∀ c → cofA u c ≡ c1 → sucT (pred (ψ u (y ∷ ys) ∷ [])) ≡ ψ u (y ∷ ys) ∷ []
  go c0 ()
  go c1 ()
  go cω ()
  go (cR r) e′ = go′ (cmpᵀ (idx r) u) e′ where
    go′ : ∀ m → cofψ₊ r m ≡ c1 → sucT (pred (ψ u (y ∷ ys) ∷ [])) ≡ ψ u (y ∷ ys) ∷ []
    go′ lt ()
    go′ eq ()
    go′ gt ()
pred-suc (ψI [] ∷ []) ()
pred-suc (ψI (y ∷ ys) ∷ []) e = go (cof (y ∷ ys)) e where
  go : ∀ c → cofI c ≡ c1 → sucT (pred (ψI (y ∷ ys) ∷ [])) ≡ ψI (y ∷ ys) ∷ []
  go c0 ()
  go c1 ()
  go cω ()
  go (cR r) e′ = go′ (cmpᵀ (idx r) 𝐈) e′ where
    go′ : ∀ m → cofIc r m ≡ c1 → sucT (pred (ψI (y ∷ ys) ∷ [])) ≡ ψI (y ∷ ys) ∷ []
    go′ lt ()
    go′ eq ()
    go′ gt ()
pred-suc (I ∷ []) ()

pred-< : ∀ a → cof a ≡ c1 → pred a <ᵀ a
pred-< a e = subst (pred a <ᵀ_) (pred-suc a e) (<-sucT (pred a))
```

灵巧构造子的递减引理: `Ω̂ v` 与 `ψ̂ u x` 都不超过原构造子的位置. 这是 Fi 的新构造子用到的唯一地方.

```agda
Ω̂-lv< : ∀ v → v <ᵀ u → Ω̂ v <ᴾ ψ u a
Ω̂-lv< [] v< = lv< v<
Ω̂-lv< (ψ w c ∷ []) v< = lv< v<
Ω̂-lv< (ψI c ∷ []) v< = Fi<ψ Fi-ψ v<
Ω̂-lv< (I ∷ []) v< = Fi<ψ Fi-I v<
Ω̂-lv< (ψ w c ∷ _ ∷ _) v< = lv< v<
Ω̂-lv< (ψI c ∷ _ ∷ _) v< = lv< v<
Ω̂-lv< (I ∷ _ ∷ _) v< = lv< v<

ψ̂-ar< : ∀ u x (y : PT) (ys : T) → x <ᵀ (y ∷ ys) → ψ̂ u x <ᴾ ψ u (y ∷ ys)
ψ̂-ar< [] [] y ys x< = ar< x<
ψ̂-ar< (ψ w c ∷ []) [] y ys x< = ar< x<
ψ̂-ar< (ψI c ∷ []) [] y ys x< = Fi<ar Fi-ψ
ψ̂-ar< (I ∷ []) [] y ys x< = Fi<ar Fi-I
ψ̂-ar< (ψ w c ∷ _ ∷ _) [] y ys x< = ar< x<
ψ̂-ar< (ψI c ∷ _ ∷ _) [] y ys x< = ar< x<
ψ̂-ar< (I ∷ _ ∷ _) [] y ys x< = ar< x<
ψ̂-ar< u (_ ∷ _) y ys x< = ar< x<

```

## §5 基本列: 裸值

EBO 先写带证书的 `fsT↓`, 再抄一份裸值 `fsT`. 这里反过来: 裸值是定义, 证书是定理 (§6). 子句结构与 EBO §5–6 逐条对应, 哑值也相同, 这样 §7 的保守性可以无前提陈述.

### 5.1 规则基数索引的基本列 $a[\eta]$

新增的三行:

- $I[\eta]=\eta$, 前提 $\eta<I$.
- $\psi_I(b)[\eta]=\psi_I(b[\eta])$, 当 $\mathrm{cof}\,b=\rho<I$.
- $\psi_u(b)[\eta]=\psi_u(b[\eta])$ 当 $\mathrm{cof}\,b=I\le u$. 这条不是新子句: 它就是规则 5Ω 在 `Ir` 上的实例.

```agda
fsT  : T → T → T
fsT0 : T → Cof → T → T
fsT₊ : T → T → Cof → T → T
fsTc : T → T → Cmp → T → T
fsTI : T → Cof → T → T
fsTIc : T → Cmp → T → T

fsT []                   η = []
fsT (x ∷ xs@(_ ∷ _))     η = x ∷ fsT xs η
fsT (ψ u (y ∷ ys) ∷ [])  η = fsT₊ u (y ∷ ys) (cof (y ∷ ys)) η
fsT (ψ (w ∷ ws) [] ∷ []) η = fsT0 (w ∷ ws) (cof (w ∷ ws)) η
fsT (𝟏 ∷ [])             η = []
fsT (ψI [] ∷ [])         η = ψI [] ∷ []     -- 哑值: Λ 的共尾度是 ω
fsT (ψI (y ∷ ys) ∷ [])   η = fsTI (y ∷ ys) (cof (y ∷ ys)) η
fsT (I ∷ [])             η = η              -- I[η] = η

fsT0 u c0     η = ψ u [] ∷ []        -- 哑值
fsT0 u c1     η = η                  -- 正规叶: Ω_{μ+1}[η] = η
fsT0 u cω     η = ψ u [] ∷ []        -- 哑值
fsT0 u (cR r) η = Ω̂ (fsT u η) ∷ []   -- 奇异叶, 含 cof u = I

fsT₊ u b c0     η = ψ u b ∷ []       -- 哑值
fsT₊ u b c1     η = ψ u b ∷ []       -- 哑值
fsT₊ u b cω     η = ψ u b ∷ []       -- 哑值
fsT₊ u b (cR r) η = fsTc u b (cmpᵀ (idx r) u) η

fsTc u b lt η = ψ̂ u (fsT b η) ∷ []   -- 规则 5: 穿透
fsTc u b eq η = ψ̂ u (fsT b η) ∷ []
fsTc u b gt η = ψ u b ∷ []           -- 哑值

fsTI b c0     η = ψI b ∷ []          -- 哑值
fsTI b c1     η = ψI b ∷ []          -- 哑值
fsTI b cω     η = ψI b ∷ []          -- 哑值
fsTI b (cR r) η = fsTIc b (cmpᵀ (idx r) 𝐈) η

fsTIc b lt η = ψI (fsT b η) ∷ []     -- ρ < I: 穿透
fsTIc b eq η = ψI b ∷ []             -- 哑值
fsTIc b gt η = ψI b ∷ []             -- 哑值
```

### 5.2 γ-链

EBO 的 $\gamma_0=\Omega_\mu=\psi_\mu(0)$, $\gamma_{k+1}=\psi_\mu(b[\gamma_k])$. 统一的读法是 $\gamma_0=\psi_\rho(0)$, $\gamma_{k+1}=\psi_\rho(b[\gamma_k])$, 其中 $\psi_\rho$ 是取值在 $\rho$ 之下的那个 ψ. 对 $\rho=\Omega_{\mu+1}$ 这是 $\psi_\mu$, 对 $\rho=I$ 这是 $\psi_I$, 所以 **$\rho=I$ 时 $\gamma_0=\Lambda$**. $T_W$ 写 $\gamma_0=1$; 在 $T_W$ 里 $\psi_I(0)=1$, 所以两边遵循同一原则, 只是 $\psi_I(0)$ 的值不同 (§11 未决选择 1).

```agda
γT : T → Rg → ℕ → T
γT β (Ωr μ) zero    = Ω̂ μ ∷ []
γT β (Ωr μ) (suc k) = ψ̂ μ (fsT β (γT β (Ωr μ) k)) ∷ []
γT β Ir     zero    = Λ
γT β Ir     (suc k) = ψI (fsT β (γT β Ir k)) ∷ []
```

### 5.3 ω-基本列 $t[n]$

EBO 的规则 1–6 不变. 新增的是 $\psi_I$ 的后继与 $\Lambda$, 都是 Ω-塔:

- $\Lambda[n]$: $1,\Omega_1,\Omega_{\Omega_1},\dots$, 与 EBO 的 `ΩTower` 逐项相同 (§8).
- $\psi_I(b+1)[n]$: $\psi_I(b)+1,\ \Omega_{\psi_I(b)+1},\ \dots$ ($T_W$ 规则 5, 6, 差一个下标).
- $\psi_I(b)[n]$, $\mathrm{cof}\,b=\rho\ge I$: 折叠, $\psi_I(b[\gamma_n])$; $\mathrm{cof}\,b=\omega$: $\psi_I(b[n])$.
- $I[n]=n$ 是与正规叶相同的哑值; $\rho<I$ 的 $\psi_I(b)[n]$ 是与规则 5Ω 相同的 ℕ-截断.

```agda
tower : T → ℕ → T        -- t, Ω_t, Ω_{Ω_t}, ...
tower t zero    = t
tower t (suc k) = ψ (tower t k) [] ∷ []

fsn   : T → ℕ → T
fsn0  : T → Cof → ℕ → T
fsn₊  : T → T → Cof → ℕ → T
fsnc  : T → T → Rg → Cmp → ℕ → T
fsnI  : T → Cof → ℕ → T
fsnIc : T → Rg → Cmp → ℕ → T

fsn [] n = []
fsn (x ∷ xs@(_ ∷ _)) n = x ∷ fsn xs n
fsn (ψ u (y ∷ ys) ∷ []) n = fsn₊ u (y ∷ ys) (cof (y ∷ ys)) n
fsn (ψ (w ∷ ws) [] ∷ []) n = fsn0 (w ∷ ws) (cof (w ∷ ws)) n
fsn (𝟏 ∷ []) n = []
fsn (ψI [] ∷ []) n = tower (𝟏 ∷ []) n
fsn (ψI (y ∷ ys) ∷ []) n = fsnI (y ∷ ys) (cof (y ∷ ys)) n
fsn (I ∷ []) n = natT n

fsn0 u c0     n = []                            -- 不可达哑值
fsn0 u c1     n = natT n                        -- 正规叶: 哑值
fsn0 u cω     n = Ω̂ (fsn u n) ∷ []
fsn0 u (cR r) n = Ω̂ (fsT u (natT n)) ∷ []

fsn₊ u b c0     n = []                          -- 不可达哑值
fsn₊ u b c1     n = replicate n (ψ̂ u (pred b))  -- 规则 4
fsn₊ u b cω     n = ψ̂ u (fsn b n) ∷ []          -- 规则 5 (ω)
fsn₊ u b (cR r) n = fsnc u b r (cmpᵀ (idx r) u) n

fsnc u b r gt n = ψ̂ u (fsT b (γT b r n)) ∷ []   -- 规则 6: 折叠
fsnc u b r lt n = ψ̂ u (fsT b (natT n)) ∷ []     -- 规则 5Ω 的 ℕ-截断
fsnc u b r eq n = ψ̂ u (fsT b (natT n)) ∷ []

fsnI b c0     n = []                            -- 不可达哑值
fsnI b c1     n = tower (ψI (pred b) ∷ 𝟏 ∷ []) n
fsnI b cω     n = ψI (fsn b n) ∷ []
fsnI b (cR r) n = fsnIc b r (cmpᵀ (idx r) 𝐈) n

fsnIc b r lt n = ψI (fsT b (natT n)) ∷ []       -- ρ < I: ℕ-截断
fsnIc b r eq n = ψI (fsT b (γT b r n)) ∷ []     -- ρ = I: 折叠
fsnIc b r gt n = ψI (fsT b (γT b r n)) ∷ []     -- ρ > I: 折叠
```

## §6 递减证书

```agda
ψ̂-ar<′ : ∀ u x b → x <ᵀ b → ψ̂ u x <ᴾ ψ u b
ψ̂-ar<′ u x (y ∷ ys) x< = ψ̂-ar< u x y ys x<

ψ̂-<Ωs : ∀ μ x → ψ̂ μ x ∷ [] <ᵀ Ωs μ
ψ̂-<Ωs μ []       = hd< (Ω̂-lv< μ (<-sucT μ))
ψ̂-<Ωs μ (y ∷ ys) = hd< (lv< (<-sucT μ))

γT-< : ∀ β r k → γT β r k <ᵀ ⟦ r ⟧       -- 无需 cof 前提
γT-< β (Ωr μ) zero    = ψ̂-<Ωs μ []
γT-< β (Ωr μ) (suc k) = ψ̂-<Ωs μ (fsT β (γT β (Ωr μ) k))
γT-< β Ir     zero    = hd< ψI<I
γT-< β Ir     (suc k) = hd< ψI<I

fsT-dec  : ∀ a {r} → cof a ≡ cR r → ∀ {η} → η <ᵀ ⟦ r ⟧ → fsT a η <ᵀ a
fsT0-dec : ∀ u c → cof u ≡ c → ∀ {r} → cofψ0 u c ≡ cR r → ∀ {η} → η <ᵀ ⟦ r ⟧ →
           fsT0 u c η <ᵀ ψ u [] ∷ []
fsT₊-dec : ∀ u b c → cof b ≡ c → ∀ {r} → cofA u c ≡ cR r → ∀ {η} → η <ᵀ ⟦ r ⟧ →
           fsT₊ u b c η <ᵀ ψ u b ∷ []
fsTc-dec : ∀ u b r₀ → cof b ≡ cR r₀ → ∀ m {r} → cofψ₊ r₀ m ≡ cR r → ∀ {η} → η <ᵀ ⟦ r ⟧ →
           fsTc u b m η <ᵀ ψ u b ∷ []
fsTI-dec : ∀ b c → cof b ≡ c → ∀ {r} → cofI c ≡ cR r → ∀ {η} → η <ᵀ ⟦ r ⟧ →
           fsTI b c η <ᵀ ψI b ∷ []
fsTIc-dec : ∀ b r₀ → cof b ≡ cR r₀ → ∀ m {r} → cofIc r₀ m ≡ cR r → ∀ {η} → η <ᵀ ⟦ r ⟧ →
            fsTIc b m η <ᵀ ψI b ∷ []

fsT-dec [] () η<
fsT-dec (x ∷ xs@(_ ∷ _)) e η< = tl< (fsT-dec xs e η<)
fsT-dec (ψ u (y ∷ ys) ∷ []) e η< = fsT₊-dec u (y ∷ ys) (cof (y ∷ ys)) refl e η<
fsT-dec (ψ (w ∷ ws) [] ∷ []) e η< = fsT0-dec (w ∷ ws) (cof (w ∷ ws)) refl e η<
fsT-dec (𝟏 ∷ []) () η<
fsT-dec (ψI [] ∷ []) () η<
fsT-dec (ψI (y ∷ ys) ∷ []) e η< = fsTI-dec (y ∷ ys) (cof (y ∷ ys)) refl e η<
fsT-dec (I ∷ []) refl η< = η<

fsT0-dec u c0 ue () η<
fsT0-dec u c1 ue refl {η} η< =
  subst (λ z → η <ᵀ ψ z [] ∷ []) (pred-suc u ue) η<
fsT0-dec u cω ue () η<
fsT0-dec u (cR r) ue refl η< = hd< (Ω̂-lv< _ (fsT-dec u ue η<))

fsT₊-dec u b c0 be () η<
fsT₊-dec u b c1 be () η<
fsT₊-dec u b cω be () η<
fsT₊-dec u b (cR r) be e η< = fsTc-dec u b r be (cmpᵀ (idx r) u) e η<

fsTc-dec u b r₀ be lt refl η< = hd< (ψ̂-ar<′ u _ b (fsT-dec b be η<))
fsTc-dec u b r₀ be eq refl η< = hd< (ψ̂-ar<′ u _ b (fsT-dec b be η<))
fsTc-dec u b r₀ be gt () η<

fsTI-dec b c0 be () η<
fsTI-dec b c1 be () η<
fsTI-dec b cω be () η<
fsTI-dec b (cR r) be e η< = fsTIc-dec b r be (cmpᵀ (idx r) 𝐈) e η<

fsTIc-dec b r₀ be lt refl η< = hd< (ψI<ψI (fsT-dec b be η<))
fsTIc-dec b r₀ be eq () η<
fsTIc-dec b r₀ be gt () η<
```

ω-基本列的递减. 塔的证书靠 `ψ<Fi`: 只要 $t<f$ 且 $f$ 是不动点, $\Omega_t<f$. 这正是"不动点对 Ω 封闭"在语法序上的影子.

```agda
tower-< : ∀ {f} t k → Fi f → t <ᵀ f ∷ [] → tower t k <ᵀ f ∷ []
tower-< t zero    fi t< = t<
tower-< t (suc k) fi t< = hd< (ψ<Fi fi (tower-< t k fi t<))

rep-dec : ∀ u {b b′} → b′ <ᵀ b → ∀ n → replicate n (ψ̂ u b′) <ᵀ ψ u b ∷ []
rep-dec u b′< zero    = []<
rep-dec u {b} {b′} b′< (suc n) = hd< (ψ̂-ar<′ u b′ b b′<)

fsn-dec  : ∀ x xs n → fsn (x ∷ xs) n <ᵀ x ∷ xs
fsn0-dec : ∀ w ws c → cof (w ∷ ws) ≡ c → ∀ n → fsn0 (w ∷ ws) c n <ᵀ ψ (w ∷ ws) [] ∷ []
fsn₊-dec : ∀ u y ys c → cof (y ∷ ys) ≡ c → ∀ n → fsn₊ u (y ∷ ys) c n <ᵀ ψ u (y ∷ ys) ∷ []
fsnc-dec : ∀ u y ys r → cof (y ∷ ys) ≡ cR r → ∀ m n → fsnc u (y ∷ ys) r m n <ᵀ ψ u (y ∷ ys) ∷ []
fsnI-dec : ∀ y ys c → cof (y ∷ ys) ≡ c → ∀ n → fsnI (y ∷ ys) c n <ᵀ ψI (y ∷ ys) ∷ []
fsnIc-dec : ∀ y ys r → cof (y ∷ ys) ≡ cR r → ∀ m n → fsnIc (y ∷ ys) r m n <ᵀ ψI (y ∷ ys) ∷ []

fsn-dec x (y ∷ ys) n = tl< (fsn-dec y ys n)
fsn-dec (ψ u (y ∷ ys)) [] n = fsn₊-dec u y ys (cof (y ∷ ys)) refl n
fsn-dec (ψ (w ∷ ws) []) [] n = fsn0-dec w ws (cof (w ∷ ws)) refl n
fsn-dec 𝟏 [] n = []<
fsn-dec (ψI []) [] n = tower-< (𝟏 ∷ []) n Fi-ψ (hd< (ψ<Fi Fi-ψ []<))
fsn-dec (ψI (y ∷ ys)) [] n = fsnI-dec y ys (cof (y ∷ ys)) refl n
fsn-dec I [] n = natT<⟦⟧ n Ir

fsn0-dec w ws c0 ue n = []<
fsn0-dec w ws c1 ue n =
  subst (λ z → natT n <ᵀ ψ z [] ∷ []) (pred-suc (w ∷ ws) ue) (natT<⟦⟧ n (Ωr (pred (w ∷ ws))))
fsn0-dec w ws cω ue n = hd< (Ω̂-lv< _ (fsn-dec w ws n))
fsn0-dec w ws (cR r) ue n = hd< (Ω̂-lv< _ (fsT-dec (w ∷ ws) ue (natT<⟦⟧ n r)))

fsn₊-dec u y ys c0 be n = []<
fsn₊-dec u y ys c1 be n = rep-dec u (pred-< (y ∷ ys) be) n
fsn₊-dec u y ys cω be n = hd< (ψ̂-ar<′ u _ (y ∷ ys) (fsn-dec y ys n))
fsn₊-dec u y ys (cR r) be n = fsnc-dec u y ys r be (cmpᵀ (idx r) u) n

fsnc-dec u y ys r be gt n = hd< (ψ̂-ar<′ u _ (y ∷ ys) (fsT-dec (y ∷ ys) be (γT-< (y ∷ ys) r n)))
fsnc-dec u y ys r be lt n = hd< (ψ̂-ar<′ u _ (y ∷ ys) (fsT-dec (y ∷ ys) be (natT<⟦⟧ n r)))
fsnc-dec u y ys r be eq n = hd< (ψ̂-ar<′ u _ (y ∷ ys) (fsT-dec (y ∷ ys) be (natT<⟦⟧ n r)))

fsnI-dec y ys c0 be n = []<
fsnI-dec y ys c1 be n =
  tower-< (ψI (pred (y ∷ ys)) ∷ 𝟏 ∷ []) n Fi-ψ (hd< (ψI<ψI (pred-< (y ∷ ys) be)))
fsnI-dec y ys cω be n = hd< (ψI<ψI (fsn-dec y ys n))
fsnI-dec y ys (cR r) be n = fsnIc-dec y ys r be (cmpᵀ (idx r) 𝐈) n

fsnIc-dec y ys r be lt n = hd< (ψI<ψI (fsT-dec (y ∷ ys) be (natT<⟦⟧ n r)))
fsnIc-dec y ys r be eq n = hd< (ψI<ψI (fsT-dec (y ∷ ys) be (γT-< (y ∷ ys) r n)))
fsnIc-dec y ys r be gt n = hd< (ψI<ψI (fsT-dec (y ∷ ys) be (γT-< (y ∷ ys) r n)))
```

打包成 EBO 的形状, 以及沿 `Acc` 的 FGH (与 EBO §7 同文, 只多 `cR` 的共尾分支).

```agda
record Below (a : T) : Set where
  constructor _⟨_⟩
  field
    trm : T
    dec : trm <ᵀ a
open Below public

fsn↓ : ∀ x xs → ℕ → Below (x ∷ xs)
fsn↓ x xs n = fsn (x ∷ xs) n ⟨ fsn-dec x xs n ⟩

fsT↓ : ∀ a {r} → cof a ≡ cR r → ∀ {η} → η <ᵀ ⟦ r ⟧ → Below a
fsT↓ a e {η} η< = fsT a η ⟨ fsT-dec a e η< ⟩

data Acc (a : T) : Set where
  acc : (∀ {b} → b <ᵀ a → Acc b) → Acc a

iter : (ℕ → ℕ) → ℕ → ℕ → ℕ
iter f x zero    = x
iter f x (suc k) = f (iter f x k)

FGH : ∀ a → Acc a → ℕ → ℕ
FGH [] _ n = suc n
FGH (x ∷ xs) (acc rs) n = go (cof (x ∷ xs)) refl where
  go : ∀ c → cof (x ∷ xs) ≡ c → ℕ
  go c0 ce = suc n
  go c1 ce = iter (FGH (pred (x ∷ xs)) (rs (pred-< (x ∷ xs) ce))) n n
  go cω ce = FGH (fsn (x ∷ xs) n) (rs (fsn-dec x xs n)) n
  go (cR r) ce = FGH (fsn (x ∷ xs) n) (rs (fsn-dec x xs n)) n
```

## §7 保守性: EBO 嵌入 Tᴵ

这一节是本文的主要交付物. 嵌入 `ιT` 是恒等式的语法包含. 下面的等式**对全部项**成立 (不限于标准形, 也不限于可数项), 包括 EBO 的每一个哑值分支.

```agda
ιT : E.T → T
ιP : E.PT → PT
ιT [] = []
ιT (x ∷ xs) = ιP x ∷ ιT xs
ιP (E.ψ u a) = ψ (ιT u) (ιT a)

ιc : E.Cof → Cof
ιc E.c0 = c0
ιc E.c1 = c1
ιc E.cω = cω
ιc (E.cΩ μ) = cΩ (ιT μ)

natT-ι : ∀ n → natT n ≡ ιT (E.natT n)
natT-ι zero    = refl
natT-ι (suc n) = cong (𝟏 ∷_) (natT-ι n)

sucT-ι : ∀ a → sucT (ιT a) ≡ ιT (E.sucT a)
sucT-ι [] = refl
sucT-ι (x ∷ xs) = cong (ιP x ∷_) (sucT-ι xs)

pred-ι : ∀ a → pred (ιT a) ≡ ιT (E.pred a)
pred-ι [] = refl
pred-ι (x ∷ y ∷ ys) = cong (ιP x ∷_) (pred-ι (y ∷ ys))
pred-ι (E.ψ [] [] ∷ []) = refl
pred-ι (E.ψ (w ∷ ws) [] ∷ []) = refl
pred-ι (E.ψ [] (y ∷ ys) ∷ []) = refl
pred-ι (E.ψ (w ∷ ws) (y ∷ ys) ∷ []) = refl
```

### 7.1 序

EBO 的 `cmpᵀ` 用 `with` 写成, 先把它改写成 `thenC` 的形状, 然后对两个项同时归纳. 因为 `ι` 的像里没有 `I`, `ψI`, 新增的子句一条都不会被走到, 这在证明里表现为: 分情况时根本不出现它们.

```agda
E-cmpᵀ : ∀ x xs y ys → E.cmpᵀ (x ∷ xs) (y ∷ ys) ≡ thenC (E.cmpᴾ x y) (E.cmpᵀ xs ys)
E-cmpᵀ x xs y ys with E.cmpᴾ x y
... | lt = refl
... | eq = refl
... | gt = refl

E-cmpᴾ : ∀ u a v b → E.cmpᴾ (E.ψ u a) (E.ψ v b) ≡ thenC (E.cmpᵀ u v) (E.cmpᵀ a b)
E-cmpᴾ u a v b with E.cmpᵀ u v
... | lt = refl
... | eq = refl
... | gt = refl

cmpᵀ-ι : ∀ s t → cmpᵀ (ιT s) (ιT t) ≡ E.cmpᵀ s t
cmpᴾ-ι : ∀ x y → cmpᴾ (ιP x) (ιP y) ≡ E.cmpᴾ x y

cmpᵀ-ι [] [] = refl
cmpᵀ-ι [] (y ∷ ys) = refl
cmpᵀ-ι (x ∷ xs) [] = refl
cmpᵀ-ι (x ∷ xs) (y ∷ ys) =
  trans (cong₂ thenC (cmpᴾ-ι x y) (cmpᵀ-ι xs ys)) (sym (E-cmpᵀ x xs y ys))

cmpᴾ-ι (E.ψ u a) (E.ψ v b) =
  trans (cong₂ thenC (cmpᵀ-ι u v) (cmpᵀ-ι a b)) (sym (E-cmpᴾ u a v b))

cmpS-ι : ∀ μ u → cmpᵀ (sucT (ιT μ)) (ιT u) ≡ E.cmpᵀ (E.sucT μ) u
cmpS-ι μ u = trans (cong (λ z → cmpᵀ z (ιT u)) (sucT-ι μ)) (cmpᵀ-ι (E.sucT μ) u)

ι-<ᵀ : ∀ {s t} → s E.<ᵀ t → ιT s <ᵀ ιT t
ι-<ᴾ : ∀ {x y} → x E.<ᴾ y → ιP x <ᴾ ιP y
ι-<ᵀ E.[]< = []<
ι-<ᵀ (E.hd< p) = hd< (ι-<ᴾ p)
ι-<ᵀ (E.tl< q) = tl< (ι-<ᵀ q)
ι-<ᴾ (E.lv< q) = lv< (ι-<ᵀ q)
ι-<ᴾ (E.ar< q) = ar< (ι-<ᵀ q)
```

### 7.2 共尾度

```agda
cofψ₊-ι : ∀ u μ m → cofψ₊ (Ωr (ιT μ)) m ≡ ιc (E.cofψ₊ u μ m)
cofψ₊-ι u μ lt = refl
cofψ₊-ι u μ eq = refl
cofψ₊-ι u μ gt = refl

cofA-ι : ∀ u c → cofA (ιT u) (ιc c) ≡ ιc (E.cofA u c)
cofA-ι u E.c0 = refl
cofA-ι u E.c1 = refl
cofA-ι u E.cω = refl
cofA-ι u (E.cΩ μ) =
  trans (cong (cofψ₊ (Ωr (ιT μ))) (cmpS-ι μ u)) (cofψ₊-ι u μ (E.cmpᵀ (E.sucT μ) u))

cofψ0-ι : ∀ u c → cofψ0 (ιT u) (ιc c) ≡ ιc (E.cofψ0 u c)
cofψ0-ι u E.c0 = refl
cofψ0-ι u E.c1 = cong cΩ (pred-ι u)
cofψ0-ι u E.cω = refl
cofψ0-ι u (E.cΩ μ) = refl

cof-ι  : ∀ t → cof (ιT t) ≡ ιc (E.cof t)
cofP-ι : ∀ x → cofP (ιP x) ≡ ιc (E.cofP x)

cof-ι [] = refl
cof-ι (x ∷ []) = cofP-ι x
cof-ι (x ∷ y ∷ ys) = cof-ι (y ∷ ys)

cofP-ι (E.ψ u (y ∷ ys)) =
  trans (cong (cofA (ιT u)) (cof-ι (y ∷ ys))) (cofA-ι u (E.cof (y ∷ ys)))
cofP-ι (E.ψ (w ∷ ws) []) =
  trans (cong (cofψ0 (ιT (w ∷ ws))) (cof-ι (w ∷ ws))) (cofψ0-ι (w ∷ ws) (E.cof (w ∷ ws)))
cofP-ι (E.ψ [] []) = refl
```

### 7.3 Ω-基本列与 γ-链

灵巧构造子在像上退化为原构造子. 这是 Fi 的改动不影响 EBO 的全部原因.

```agda
Ω̂-ι : ∀ u → Ω̂ (ιT u) ≡ ψ (ιT u) []
Ω̂-ι [] = refl
Ω̂-ι (E.ψ w c ∷ []) = refl
Ω̂-ι (E.ψ w c ∷ y ∷ ys) = refl

ψ̂-ι : ∀ u a → ψ̂ (ιT u) (ιT a) ≡ ψ (ιT u) (ιT a)
ψ̂-ι u [] = Ω̂-ι u
ψ̂-ι u (y ∷ ys) = refl

Ω̂₁ : ∀ {v} {w} → v ≡ ιT w → Ω̂ v ∷ [] ≡ ιT (E.ψ w [] ∷ [])
Ω̂₁ {w = w} refl = cong (_∷ []) (Ω̂-ι w)

ψ̂₁ : ∀ u {v} {w} → v ≡ ιT w → ψ̂ (ιT u) v ∷ [] ≡ ιT (E.ψ u w ∷ [])
ψ̂₁ u {w = w} refl = cong (_∷ []) (ψ̂-ι u w)

fsT-ι  : ∀ a η → fsT (ιT a) (ιT η) ≡ ιT (E.fsT a η)
fsT0-ι : ∀ u c η → fsT0 (ιT u) (ιc c) (ιT η) ≡ ιT (E.fsT0 u c η)
fsT₊-ι : ∀ u b c η → fsT₊ (ιT u) (ιT b) (ιc c) (ιT η) ≡ ιT (E.fsT₊ u b c η)
fsTc-ι : ∀ u b ν m η → fsTc (ιT u) (ιT b) m (ιT η) ≡ ιT (E.fsTc u b ν m η)

fsT-ι [] η = refl
fsT-ι (x ∷ y ∷ ys) η = cong (ιP x ∷_) (fsT-ι (y ∷ ys) η)
fsT-ι (E.ψ u (y ∷ ys) ∷ []) η =
  trans (cong (λ c → fsT₊ (ιT u) (ιT (y ∷ ys)) c (ιT η)) (cof-ι (y ∷ ys)))
        (fsT₊-ι u (y ∷ ys) (E.cof (y ∷ ys)) η)
fsT-ι (E.ψ (w ∷ ws) [] ∷ []) η =
  trans (cong (λ c → fsT0 (ιT (w ∷ ws)) c (ιT η)) (cof-ι (w ∷ ws)))
        (fsT0-ι (w ∷ ws) (E.cof (w ∷ ws)) η)
fsT-ι (E.ψ [] [] ∷ []) η = refl

fsT0-ι u E.c0 η = refl
fsT0-ι u E.c1 η = refl
fsT0-ι u E.cω η = refl
fsT0-ι u (E.cΩ ν) η = Ω̂₁ (fsT-ι u η)

fsT₊-ι u b E.c0 η = refl
fsT₊-ι u b E.c1 η = refl
fsT₊-ι u b E.cω η = refl
fsT₊-ι u b (E.cΩ ν) η =
  trans (cong (λ m → fsTc (ιT u) (ιT b) m (ιT η)) (cmpS-ι ν u))
        (fsTc-ι u b ν (E.cmpᵀ (E.sucT ν) u) η)

fsTc-ι u b ν lt η = ψ̂₁ u (fsT-ι b η)
fsTc-ι u b ν eq η = ψ̂₁ u (fsT-ι b η)
fsTc-ι u b ν gt η = refl

γT-ι : ∀ β μ k → γT (ιT β) (Ωr (ιT μ)) k ≡ ιT (E.γT β μ k)
γT-ι β μ zero    = cong (_∷ []) (Ω̂-ι μ)
γT-ι β μ (suc k) =
  ψ̂₁ μ (trans (cong (fsT (ιT β)) (γT-ι β μ k)) (fsT-ι β (E.γT β μ k)))
```

### 7.4 ω-基本列: 关键定理

EBO 的 `fsn` 是 `fsn↓` 的第一分量, 内部带证书; 这里的辅助函数对 EBO 的 `cof` 值一般化 (`c`, `be`), 调用处取 `refl`. Ω-基本列与 γ-链的证书由 EBO 自己的 `fsT↓-trm`, `γ↓-trm` 消去.

```agda
replicate-ι : ∀ n x → replicate n (ιP x) ≡ ιT (replicate n x)
replicate-ι zero    x = refl
replicate-ι (suc n) x = cong (ιP x ∷_) (replicate-ι n x)

fsn-ι  : ∀ x xs n → fsn (ιT (x ∷ xs)) n ≡ ιT (E.trm (E.fsn↓ x xs n))
fsn0-ι : ∀ w ws c (ue : E.cof (w ∷ ws) ≡ c) n →
         fsn0 (ιT (w ∷ ws)) (ιc c) n ≡ ιT (E.trm (E.fsn↓0 w ws c ue n))
fsn₊-ι : ∀ u y ys c (be : E.cof (y ∷ ys) ≡ c) n →
         fsn₊ (ιT u) (ιT (y ∷ ys)) (ιc c) n ≡ ιT (E.trm (E.fsn↓₊ u y ys c be n))
fsnc-ι : ∀ u y ys ν (be : E.cof (y ∷ ys) ≡ E.cΩ ν) m n →
         fsnc (ιT u) (ιT (y ∷ ys)) (Ωr (ιT ν)) m n ≡ ιT (E.trm (E.fsn↓c u y ys ν be m n))

fsn-ι x (y ∷ ys) n = cong (ιP x ∷_) (fsn-ι y ys n)
fsn-ι (E.ψ u (y ∷ ys)) [] n =
  trans (cong (λ c → fsn₊ (ιT u) (ιT (y ∷ ys)) c n) (cof-ι (y ∷ ys)))
        (fsn₊-ι u y ys (E.cof (y ∷ ys)) refl n)
fsn-ι (E.ψ (w ∷ ws) []) [] n =
  trans (cong (λ c → fsn0 (ιT (w ∷ ws)) c n) (cof-ι (w ∷ ws)))
        (fsn0-ι w ws (E.cof (w ∷ ws)) refl n)
fsn-ι (E.ψ [] []) [] n = refl

fsn0-ι w ws E.c0 ue n = refl
fsn0-ι w ws E.c1 ue n = natT-ι n
fsn0-ι w ws E.cω ue n = Ω̂₁ (fsn-ι w ws n)
fsn0-ι w ws (E.cΩ ν) ue n =
  Ω̂₁ (trans (cong (fsT (ιT (w ∷ ws))) (natT-ι n))
     (trans (fsT-ι (w ∷ ws) (E.natT n))
            (cong ιT (sym (E.fsT↓-trm (w ∷ ws) ue (E.natT<Ωs n ν))))))

fsn₊-ι u y ys E.c0 be n = refl
fsn₊-ι u y ys E.c1 be n =
  trans (cong (λ z → replicate n (ψ̂ (ιT u) z)) (pred-ι (y ∷ ys)))
  (trans (cong (replicate n) (ψ̂-ι u (E.pred (y ∷ ys))))
  (trans (replicate-ι n (E.ψ u (E.pred (y ∷ ys))))
         (cong ιT (sym (E.rep-trm u (E.pred-< (y ∷ ys) be) n)))))
fsn₊-ι u y ys E.cω be n = ψ̂₁ u (fsn-ι y ys n)
fsn₊-ι u y ys (E.cΩ ν) be n =
  trans (cong (λ m → fsnc (ιT u) (ιT (y ∷ ys)) (Ωr (ιT ν)) m n) (cmpS-ι ν u))
        (fsnc-ι u y ys ν be (E.cmpᵀ (E.sucT ν) u) n)

fsnc-ι u y ys ν be gt n =
  let b = y ∷ ys
      g = E.γ↓ b ν be n
  in ψ̂₁ u (trans (cong (fsT (ιT b)) (γT-ι b ν n))
          (trans (fsT-ι b (E.γT b ν n))
                 (cong ιT (sym (trans (E.fsT↓-trm b be (E.dec g))
                                      (cong (E.fsT b) (E.γ↓-trm b ν be n)))))))
fsnc-ι u y ys ν be lt n =
  ψ̂₁ u (trans (cong (fsT (ιT (y ∷ ys))) (natT-ι n))
       (trans (fsT-ι (y ∷ ys) (E.natT n))
              (cong ιT (sym (E.fsT↓-trm (y ∷ ys) be (E.natT<Ωs n ν))))))
fsnc-ι u y ys ν be eq n =
  ψ̂₁ u (trans (cong (fsT (ιT (y ∷ ys))) (natT-ι n))
       (trans (fsT-ι (y ∷ ys) (E.natT n))
              (cong ιT (sym (E.fsT↓-trm (y ∷ ys) be (E.natT<Ωs n ν))))))

conservative-fsn : ∀ t n → fsn (ιT t) n ≡ ιT (E.fsn t n)
conservative-fsn [] n = refl
conservative-fsn (x ∷ xs) n = fsn-ι x xs n

record Conservative : Set where
  field
    cmp : ∀ s t → cmpᵀ (ιT s) (ιT t) ≡ E.cmpᵀ s t
    cof′ : ∀ t → cof (ιT t) ≡ ιc (E.cof t)
    fsΩ : ∀ a η → fsT (ιT a) (ιT η) ≡ ιT (E.fsT a η)
    γ′ : ∀ β μ k → γT (ιT β) (Ωr (ιT μ)) k ≡ ιT (E.γT β μ k)
    fsω : ∀ t n → fsn (ιT t) n ≡ ιT (E.fsn t n)
    pred′ : ∀ a → pred (ιT a) ≡ ιT (E.pred a)

conservative : Conservative
conservative = record
  { cmp = cmpᵀ-ι ; cof′ = cof-ι ; fsΩ = fsT-ι ; γ′ = γT-ι
  ; fsω = conservative-fsn ; pred′ = pred-ι }
```

## §8 样例 (`refl` 测试, 不是证明)

这一节除了第一组 (`tower-ι`, `ψ₀Λ-tower`, 对所有 $n$ 成立的定理) 都是有限个 $n$ 上的计算核对.

**$\Lambda$ 回到 EBO 的极限.** $\psi_0(\Lambda)[n]$ 恰好是 EBO 的 `EBOψ n`: 这个系统里 $\mathrm{EBO}=\psi_0(\Lambda)$ 是一个项, 而 EBO 自己用来逼近极限的那条序列就是它的基本列.

```agda
tower-ι : ∀ n → tower (𝟏 ∷ []) n ≡ ιT (E.ΩTower n)
tower-ι zero    = refl
tower-ι (suc n) = cong (λ z → ψ z [] ∷ []) (tower-ι n)

ψ₀Λ-tower : ∀ n → fsn (ψ [] Λ ∷ []) n ≡ ιT (E.EBOψ n)
ψ₀Λ-tower n = ψ̂₁ [] (tower-ι n)

_ : cof (ψ [] Λ ∷ []) ≡ cω
_ = refl

ψ₀ : T → T
ψ₀ a = ψ [] a ∷ []

ωT Ω₁ ΛS 𝐈S : T
ωT = ψ₀ (natT 1)
Ω₁ = ψ (natT 1) [] ∷ []
ΛS = ψI [] ∷ 𝟏 ∷ []       -- Λ + 1
𝐈S = I ∷ 𝟏 ∷ []           -- I + 1

Ω′ : T → T
Ω′ u = ψ u [] ∷ []

ψΛ ψ𝐈 : T → T             -- ψ_Λ(·), ψ_{u=I}(·): 值域在 [Λ, Ω_{Λ+1}), [I, Ω_{I+1})
ψΛ a = ψ Λ a ∷ []
ψ𝐈 a = ψ 𝐈 a ∷ []

ψI′ : T → T
ψI′ a = ψI a ∷ []

-- ψ₀(Λ+1)[n] = ψ₀(Λ)·n
_ : fsn (ψ₀ ΛS) 2 ≡ ψ [] Λ ∷ ψ [] Λ ∷ []
_ = refl

-- ψ₀(Ω_{Λ+1}): γ₀ = Ω_Λ = Λ, 走 Ω̂ 而不是别名
_ : fsn (ψ₀ (Ω′ ΛS)) 0 ≡ ψ₀ Λ
_ = refl
_ : fsn (ψ₀ (Ω′ ΛS)) 1 ≡ ψ₀ (ψΛ Λ)
_ = refl
_ : fsn (ψ₀ (Ω′ ΛS)) 2 ≡ ψ₀ (ψΛ (ψΛ Λ))
_ = refl

-- ψ₀(I): 目标 I 的折叠, γ₀ = Λ, γ_{k+1} = ψ_I(I[γ_k]) = ψ_I(γ_k)
_ : cof (ψ₀ 𝐈) ≡ cω
_ = refl
_ : fsn (ψ₀ 𝐈) 0 ≡ ψ₀ Λ
_ = refl
_ : fsn (ψ₀ 𝐈) 1 ≡ ψ₀ (ψI′ Λ)
_ = refl
_ : fsn (ψ₀ 𝐈) 2 ≡ ψ₀ (ψI′ (ψI′ Λ))
_ = refl

-- ψ₀(I+1)[n] = ψ₀(I)·n
_ : fsn (ψ₀ 𝐈S) 2 ≡ ψ [] 𝐈 ∷ ψ [] 𝐈 ∷ []
_ = refl

-- ψ₀(Ω_{I+1}): γ₀ = Ω_I = I
_ : fsn (ψ₀ (Ω′ 𝐈S)) 0 ≡ ψ₀ 𝐈
_ = refl
_ : fsn (ψ₀ (Ω′ 𝐈S)) 1 ≡ ψ₀ (ψ𝐈 𝐈)
_ = refl
_ : fsn (ψ₀ (Ω′ 𝐈S)) 2 ≡ ψ₀ (ψ𝐈 (ψ𝐈 𝐈))
_ = refl

-- ψ₀(Ω_{I+ω})[n] = ψ₀(Ω_{I+n}); n = 0 时 Ω_I = I (Setzer 的端点 ψ_{Ω₁}Ω_{I+ω})
_ : fsn (ψ₀ (Ω′ (I ∷ ωT))) 0 ≡ ψ₀ 𝐈
_ = refl
_ : fsn (ψ₀ (Ω′ (I ∷ ωT))) 1 ≡ ψ₀ (Ω′ 𝐈S)
_ = refl
_ : fsn (ψ₀ (Ω′ (I ∷ ωT))) 2 ≡ ψ₀ (Ω′ (I ∷ 𝟏 ∷ 𝟏 ∷ []))
_ = refl

-- ψ_I(1): 下一个不动点, Λ+1, Ω_{Λ+1}, Ω_{Ω_{Λ+1}}, ...
_ : fsn (ψI′ (natT 1)) 0 ≡ ΛS
_ = refl
_ : fsn (ψI′ (natT 1)) 1 ≡ Ω′ ΛS
_ = refl
_ : fsn (ψI′ (natT 1)) 2 ≡ Ω′ (Ω′ ΛS)
_ = refl

-- ψ_I(ω)[n] = ψ_I(n)
_ : fsn (ψI′ ωT) 0 ≡ Λ
_ = refl
_ : fsn (ψI′ ωT) 3 ≡ ψI′ (natT 3)
_ = refl

-- ψ_I(Ω₁): 共尾度 Ω₁ (穿透), ψ_I(Ω₁)[η] = ψ_I(η); ω-基本列是 ℕ-截断
_ : cof (ψI′ Ω₁) ≡ cΩ []
_ = refl
_ : fsT (ψI′ Ω₁) ωT ≡ ψI′ ωT
_ = refl
_ : fsn (ψI′ Ω₁) 2 ≡ ψI′ (natT 2)
_ = refl

-- ψ_I(I): ρ = π = I, 折叠
_ : cof (ψI′ 𝐈) ≡ cω
_ = refl
_ : fsn (ψI′ 𝐈) 1 ≡ ψI′ (ψI′ Λ)
_ = refl

-- ψ_I(Ω_{I+1}): ρ > I, 折叠, γ₀ = I
_ : cof (ψI′ (Ω′ 𝐈S)) ≡ cω
_ = refl
_ : fsn (ψI′ (Ω′ 𝐈S)) 0 ≡ ψI′ 𝐈
_ = refl
_ : fsn (ψI′ (Ω′ 𝐈S)) 1 ≡ ψI′ (ψ𝐈 𝐈)
_ = refl

-- I 与下标 ≥ I 的穿透
_ : cof 𝐈 ≡ cI
_ = refl
_ : fsT 𝐈 ωT ≡ ωT
_ = refl
_ : cof (ψ𝐈 𝐈) ≡ cI
_ = refl
_ : fsT (ψ𝐈 𝐈) ωT ≡ ψ𝐈 ωT
_ = refl

-- 灵巧构造子: ψ_Λ(ω)[0] = Λ, 不产生别名
_ : fsn (ψΛ ωT) 0 ≡ Λ
_ = refl
_ : fsn (ψΛ (natT 1)) 2 ≡ ψI [] ∷ ψI [] ∷ []    -- ψ_Λ(1)[n] = Λ·n
_ = refl

-- 序
_ : cmpᵀ (ιT (E.ΩTower 5)) Λ ≡ lt
_ = refl
_ : cmpᵀ Λ (ψI′ (natT 1)) ≡ lt
_ = refl
_ : cmpᵀ (ψI′ (natT 1)) 𝐈 ≡ lt
_ = refl
_ : cmpᵀ 𝐈 (Ω′ 𝐈S) ≡ lt
_ = refl
_ : cmpᵀ (ιT (E.EBOψ 7)) (ψ₀ Λ) ≡ lt
_ = refl
_ : cmpᵀ (ψ₀ Λ) (ψ₀ ΛS) ≡ lt
_ = refl
_ : cmpᵀ (ψΛ (natT 1)) Λ ≡ gt          -- ψ_Λ(1) > Λ
_ = refl
_ : cmpᵀ (Ω′ Λ) Λ ≡ eq                  -- 别名: cmp 在标准形外不判别语法相等
_ = refl
```

## §9 标准形 `NFᴵ`

基础是 p進大好きbot 给 EBO 记号的显式谓词 ([*Ordinal Notation Associated to Extended Buchholz's OCF*](https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/Ordinal_Notation_Associated_to_Extended_Buchholz%27s_OCF), 转述见 [调研](../../Survey/OrdinalNotationsFS.md) §11): $G(X,Y)\triangleleft Z$, 对 $Y=\langle W_1,W_2\rangle$: $X\le W_1$ 时要 $W_2<Z$ 且递归到 $W_1,W_2$, 否则平凡真; 和逐项; $\langle X_1,X_2\rangle$ 标准当且仅当 $G(X_1,X_2)\triangleleft X_2$. 这就是 Buchholz 的 $G_u(a)<a$. 它在 EBO 这一段的写法在 `G◃`/`G◃ᴾ` 的 `ψ` 子句里一字未改.

扩张到 I 的部分取自 Setzer Def 2.7 (G4)–(G6) 经 §10 的翻译 τ (见 [Closure](../../../archive/src/Mahlo/Inacc/Closure.lagda.md) §2), 我的转写:

- $G_u(I)=\emptyset$; $G_u(\psi_I b)$: $u<\psi_I b$ 时要 $b<Z$ 且递归到 $b$, 否则平凡真. 注意 $u=\psi_I b$ 时平凡真, 不是"$\le$": $\psi_\Lambda(\Lambda)$ 是标准的.
- 目标 $I$ 单独写 `GI◃`: $\psi_I b$ 总要 $b<Z$ 并递归; $\psi_w(c)$ 在 $I\le w$ 时同 EBO 的子句, 而 $w<I$ 时**不是平凡真**, 要递归进下标 $w$. 这与 Setzer (G4) 第二支相同, 是 EBO 的 `else true` 在目标 $I$ 上不再成立的地方. 例如 $\psi_I(\psi_{\psi_I(I)}(1))$: $\psi_I(I)$ 在下标里, 参数 $I$ 不小于 $Z$, 应当被拒绝, 而下标 $<I$.
- $\Omega_f$ ($f\in Fi$) 不标准 (OT5); 其它语法别名只有这一种.

```agda
open import Data.Bool using (Bool; true; false; _∧_; not; if_then_else_)

ltᵇ leᵇ : Cmp → Bool
ltᵇ lt = true
ltᵇ eq = false
ltᵇ gt = false
leᵇ lt = true
leᵇ eq = true
leᵇ gt = false

_<?_ _≤?_ : T → T → Bool
a <? b = ltᵇ (cmpᵀ a b)
a ≤? b = leᵇ (cmpᵀ a b)

isFiT : T → Bool
isFiT (ψI a ∷ []) = true
isFiT (I ∷ [])    = true
isFiT _           = false

G◃  : T → T → T → Bool      -- G(X,Y) ◃ Z
G◃ᴾ : T → PT → T → Bool
G◃ X [] Z = true
G◃ X (y ∷ ys) Z = G◃ᴾ X y Z ∧ G◃ X ys Z
G◃ᴾ X (ψ w c) Z = if X ≤? w then (c <? Z) ∧ G◃ X w Z ∧ G◃ X c Z else true
G◃ᴾ X (ψI b) Z = if X <? (ψI b ∷ []) then (b <? Z) ∧ G◃ X b Z else true
G◃ᴾ X I Z = true

GI◃  : T → T → Bool         -- G_I(Y) ◃ Z
GI◃ᴾ : PT → T → Bool
GI◃ [] Z = true
GI◃ (y ∷ ys) Z = GI◃ᴾ y Z ∧ GI◃ ys Z
GI◃ᴾ (ψ w c) Z = if 𝐈 ≤? w then (c <? Z) ∧ GI◃ w Z ∧ GI◃ c Z else GI◃ w Z
GI◃ᴾ (ψI b) Z = (b <? Z) ∧ GI◃ b Z
GI◃ᴾ I Z = true

descᵇ : PT → T → Bool       -- 和弱递减: 下一项不大于 x
descᵇ x [] = true
descᵇ x (y ∷ ys) = leᵇ (cmpᴾ y x)

isNF  : T → Bool
isNFᴾ : PT → Bool
isNF [] = true
isNF (x ∷ xs) = isNFᴾ x ∧ descᵇ x xs ∧ isNF xs
isNFᴾ (ψ u []) = isNF u ∧ not (isFiT u)
isNFᴾ (ψ u (y ∷ ys)) = isNF u ∧ isNF (y ∷ ys) ∧ G◃ u (y ∷ ys) (y ∷ ys)
isNFᴾ (ψI a) = isNF a ∧ GI◃ a a
isNFᴾ I = true

NFᴵ : T → Set
NFᴵ t = isNF t ≡ true
```

**EBO 段的标准形就是 bot 的原版.** 这条也是保守性: 把谓词在 EBO 的项上按原文写一遍 (`isOTᵉ`), 它等于 `isNF ∘ ι`.

```agda
leEᵇ ltEᵇ : E.T → E.T → Bool
leEᵇ a b = leᵇ (E.cmpᵀ a b)
ltEᵇ a b = ltᵇ (E.cmpᵀ a b)

Gᵉ  : E.T → E.T → E.T → Bool
Gᵉᴾ : E.T → E.PT → E.T → Bool
Gᵉ X [] Z = true
Gᵉ X (y ∷ ys) Z = Gᵉᴾ X y Z ∧ Gᵉ X ys Z
Gᵉᴾ X (E.ψ w c) Z = if leEᵇ X w then ltEᵇ c Z ∧ Gᵉ X w Z ∧ Gᵉ X c Z else true

isOTᵉ  : E.T → Bool
isOTᵉᴾ : E.PT → Bool
descᵉ  : E.PT → E.T → Bool
descᵉ x [] = true
descᵉ x (y ∷ ys) = leᵇ (E.cmpᴾ y x)
isOTᵉ [] = true
isOTᵉ (x ∷ xs) = isOTᵉᴾ x ∧ descᵉ x xs ∧ isOTᵉ xs
isOTᵉᴾ (E.ψ u []) = isOTᵉ u
isOTᵉᴾ (E.ψ u (y ∷ ys)) = isOTᵉ u ∧ isOTᵉ (y ∷ ys) ∧ Gᵉ u (y ∷ ys) (y ∷ ys)

≤?-ι : ∀ a b → (ιT a ≤? ιT b) ≡ leEᵇ a b
≤?-ι a b = cong leᵇ (cmpᵀ-ι a b)

<?-ι : ∀ a b → (ιT a <? ιT b) ≡ ltEᵇ a b
<?-ι a b = cong ltᵇ (cmpᵀ-ι a b)

G◃-ι  : ∀ X Y Z → G◃ (ιT X) (ιT Y) (ιT Z) ≡ Gᵉ X Y Z
G◃ᴾ-ι : ∀ X y Z → G◃ᴾ (ιT X) (ιP y) (ιT Z) ≡ Gᵉᴾ X y Z
G◃-ι X [] Z = refl
G◃-ι X (y ∷ ys) Z = cong₂ _∧_ (G◃ᴾ-ι X y Z) (G◃-ι X ys Z)
G◃ᴾ-ι X (E.ψ w c) Z =
  trans (cong (λ q → if q then (ιT c <? ιT Z) ∧ G◃ (ιT X) (ιT w) (ιT Z) ∧ G◃ (ιT X) (ιT c) (ιT Z) else true) (≤?-ι X w))
        (cong (λ q → if leEᵇ X w then q else true)
              (cong₂ _∧_ (<?-ι c Z) (cong₂ _∧_ (G◃-ι X w Z) (G◃-ι X c Z))))

notFi-ι : ∀ u → not (isFiT (ιT u)) ≡ true
notFi-ι [] = refl
notFi-ι (E.ψ w c ∷ []) = refl
notFi-ι (E.ψ w c ∷ y ∷ ys) = refl

desc-ι : ∀ x xs → descᵇ (ιP x) (ιT xs) ≡ descᵉ x xs
desc-ι x [] = refl
desc-ι x (y ∷ ys) = cong leᵇ (cmpᴾ-ι y x)

∧true : ∀ b → (b ∧ true) ≡ b
∧true false = refl
∧true true  = refl

NF-ι  : ∀ t → isNF (ιT t) ≡ isOTᵉ t
NFᴾ-ι : ∀ x → isNFᴾ (ιP x) ≡ isOTᵉᴾ x
NF-ι [] = refl
NF-ι (x ∷ xs) = cong₂ _∧_ (NFᴾ-ι x) (cong₂ _∧_ (desc-ι x xs) (NF-ι xs))
NFᴾ-ι (E.ψ u []) =
  trans (cong₂ _∧_ (NF-ι u) (notFi-ι u)) (∧true (isOTᵉ u))
NFᴾ-ι (E.ψ u (y ∷ ys)) =
  cong₂ _∧_ (NF-ι u) (cong₂ _∧_ (NF-ι (y ∷ ys)) (G◃-ι u (y ∷ ys) (y ∷ ys)))
```

### 9.1 片段上的封闭性 (定理, 只到便宜的部分)

全系统的封闭性 "标准形对基本列封闭" **没有证明**, bot 的原文也只是声称. 这里只证 Ω-塔这一段: $\Lambda[n]$, $\psi_0(\Lambda)[n]$, $\psi_I(b+1)[n]$ (前提 $\psi_I(b)\in$ NF), $\psi_I(\omega)[n]$, $I[\eta]$.

```agda
Ω′-NF : ∀ u → isNF u ≡ true → isFiT u ≡ false → isNF (ψ u [] ∷ []) ≡ true
Ω′-NF u p q rewrite p | q = refl

tower-NF : ∀ t → isNF t ≡ true → isFiT t ≡ false → ∀ n → NFᴵ (tower t n)
tower-Fi : ∀ t → isFiT t ≡ false → ∀ n → isFiT (tower t n) ≡ false
tower-Fi t q zero    = q
tower-Fi t q (suc n) = refl
tower-NF t p q zero    = p
tower-NF t p q (suc n) = Ω′-NF (tower t n) (tower-NF t p q n) (tower-Fi t q n)

Λ[n]-NF : ∀ n → NFᴵ (fsn Λ n)
Λ[n]-NF = tower-NF (𝟏 ∷ []) refl refl

ψI-suc-base : ∀ b → NFᴵ (ψI b ∷ []) → NFᴵ (ψI b ∷ 𝟏 ∷ [])
ψI-suc-base b p with isNF b ∧ GI◃ b b | p
... | true | _ = refl

ψI-suc-NF : ∀ b → NFᴵ (ψI b ∷ []) → ∀ n → NFᴵ (tower (ψI b ∷ 𝟏 ∷ []) n)
ψI-suc-NF b p = tower-NF (ψI b ∷ 𝟏 ∷ []) (ψI-suc-base b p) refl

[]≤? : ∀ t → ([] ≤? t) ≡ true
[]≤? [] = refl
[]≤? (y ∷ ys) = refl

G◃-tower : ∀ n Z → ([] <? Z) ≡ true → G◃ [] (tower (𝟏 ∷ []) n) Z ≡ true
G◃-tower zero Z p rewrite p = refl
G◃-tower (suc n) Z p rewrite []≤? (tower (𝟏 ∷ []) n) | p | G◃-tower n Z p = refl

ψ₀-tower-NF : ∀ n → NFᴵ (ψ₀ (tower (𝟏 ∷ []) n))
ψ₀-tower-NF zero = refl
ψ₀-tower-NF (suc n)
  rewrite Ω′-NF (tower (𝟏 ∷ []) n) (tower-NF (𝟏 ∷ []) refl refl n) (tower-Fi (𝟏 ∷ []) refl n)
        | G◃-tower (suc n) (ψ (tower (𝟏 ∷ []) n) [] ∷ []) refl = refl

ψ₀Λ[n]-eq : ∀ n → fsn (ψ₀ Λ) n ≡ ψ₀ (tower (𝟏 ∷ []) n)
ψ₀Λ[n]-eq zero    = refl
ψ₀Λ[n]-eq (suc n) = refl

ψ₀Λ[n]-NF : ∀ n → NFᴵ (fsn (ψ₀ Λ) n)
ψ₀Λ[n]-NF n = subst NFᴵ (sym (ψ₀Λ[n]-eq n)) (ψ₀-tower-NF n)

natT-NF : ∀ n → NFᴵ (natT n)
natT-NF zero = refl
natT-NF (suc zero) = refl
natT-NF (suc (suc n)) = natT-NF (suc n)

GI-nat : ∀ n Z → GI◃ (natT n) Z ≡ true
GI-nat zero Z = refl
GI-nat (suc n) Z = GI-nat n Z

rep𝟏 : ∀ n → replicate n 𝟏 ≡ natT n
rep𝟏 zero    = refl
rep𝟏 (suc n) = cong (𝟏 ∷_) (rep𝟏 n)

ψI[nat]-NF : ∀ n → NFᴵ (fsn (ψI′ ωT) n)
ψI[nat]-NF n rewrite rep𝟏 n | natT-NF n | GI-nat n (natT n) = refl

I[η]-NF : ∀ η → NFᴵ η → NFᴵ (fsT 𝐈 η)
I[η]-NF η p = p
```

**样本** (`refl` 测试). 接受的都是 §8 出现过的项; 拒绝的是三种原因各一例: 别名、$\psi_0(\psi_I(I))$ (与 $\psi_0(\psi_1(\Omega_2))$ 同类), 目标 $I$ 的 `else` 分支.

```agda
_ : isNF (ψ₀ Λ) ≡ true
_ = refl
_ : isNF (ψ₀ (Ω′ ΛS)) ≡ true
_ = refl
_ : isNF (ψ₀ 𝐈) ≡ true
_ = refl
_ : isNF (ψ₀ (Ω′ 𝐈S)) ≡ true
_ = refl
_ : isNF (ψ₀ (Ω′ (I ∷ ωT))) ≡ true
_ = refl
_ : isNF (ψI′ Ω₁) ≡ true
_ = refl
_ : isNF (ψI′ 𝐈) ≡ true
_ = refl
_ : isNF (ψI′ (Ω′ 𝐈S)) ≡ true
_ = refl
_ : isNF (ψΛ Λ) ≡ true
_ = refl

_ : isNF (Ω′ Λ) ≡ false              -- Ω_Λ 是 Λ 的别名
_ = refl
_ : isNF (Ω′ 𝐈) ≡ false              -- Ω_I 是 I 的别名
_ = refl
_ : isNF (ψ₀ (ψI′ 𝐈)) ≡ false        -- G₀ 含 I, I ≮ ψ_I(I)
_ = refl
_ : isNF (ψI′ (ψ (ψI′ 𝐈) (natT 1) ∷ [])) ≡ false   -- 目标 I, 下标里的 ψ_I(I)
_ = refl
```

### 9.2 归纳序与判定序的一致性

`_<ᵀ_` 蕴含 `cmpᵀ` 给 `lt`, 对全部项成立. 所以证书 `fsn-dec` 也是判定序下的递减 (`fsn-lt`), 而且 `_<ᵀ_` 非自反. 反方向 (`lt` 蕴含 `_<ᵀ_`) 在全部项上**是假的**: `cmp` 把别名 `ψ (f ∷ []) []` 与 `f` 判作 `eq`, 而 `tl<` 要求语法相等, 所以 `f ∷ [] <ᵀ ψ (f ∷ []) [] ∷ 𝟏 ∷ []` 推不出来, `cmpᵀ` 却给 `lt`. 这只发生在标准形之外.

```agda
cmpᵀ-refl : ∀ t → cmpᵀ t t ≡ eq
cmpᴾ-refl : ∀ x → cmpᴾ x x ≡ eq
cmpᵀ-refl [] = refl
cmpᵀ-refl (x ∷ xs) rewrite cmpᴾ-refl x = cmpᵀ-refl xs
cmpᴾ-refl (ψ u a) rewrite cmpᵀ-refl u = cmpᵀ-refl a
cmpᴾ-refl (ψI a) = cmpᵀ-refl a
cmpᴾ-refl I = refl

<⇒cmpᵀ : ∀ {a b} → a <ᵀ b → cmpᵀ a b ≡ lt
<⇒cmpᴾ : ∀ {x y} → x <ᴾ y → cmpᴾ x y ≡ lt
<⇒cmpᵀ¹ : ∀ {u f} → u <ᵀ f ∷ [] → cmpᵀ¹ u f ≡ lt
<⇒cmp¹ᵀ : ∀ {f v} → f ∷ [] <ᵀ v → cmp¹ᵀ f v ≡ lt

<⇒cmpᵀ []< = refl
<⇒cmpᵀ (hd< p) rewrite <⇒cmpᴾ p = refl
<⇒cmpᵀ (tl< {x = x} q) rewrite cmpᴾ-refl x = <⇒cmpᵀ q

<⇒cmpᵀ¹ []< = refl
<⇒cmpᵀ¹ (hd< p) rewrite <⇒cmpᴾ p = refl
<⇒cmpᵀ¹ (tl< ())

<⇒cmp¹ᵀ (hd< p) rewrite <⇒cmpᴾ p = refl
<⇒cmp¹ᵀ (tl< {x = f} []<) rewrite cmpᴾ-refl f = refl

<⇒cmpᴾ (lv< q) rewrite <⇒cmpᵀ q = refl
<⇒cmpᴾ (ar< {u = u} q) rewrite cmpᵀ-refl u | <⇒cmpᵀ q = refl
<⇒cmpᴾ (ψ<Fi Fi-I q) rewrite <⇒cmpᵀ¹ q = refl
<⇒cmpᴾ (ψ<Fi Fi-ψ q) rewrite <⇒cmpᵀ¹ q = refl
<⇒cmpᴾ (Fi<ψ Fi-I q) rewrite <⇒cmp¹ᵀ q = refl
<⇒cmpᴾ (Fi<ψ Fi-ψ q) rewrite <⇒cmp¹ᵀ q = refl
<⇒cmpᴾ (Fi<ar Fi-I) = refl
<⇒cmpᴾ (Fi<ar (Fi-ψ {a = a})) rewrite cmpᵀ-refl a = refl
<⇒cmpᴾ (ψI<ψI q) = <⇒cmpᵀ q
<⇒cmpᴾ ψI<I = refl

fsn-lt : ∀ x xs n → cmpᵀ (fsn (x ∷ xs) n) (x ∷ xs) ≡ lt
fsn-lt x xs n = <⇒cmpᵀ (fsn-dec x xs n)

<-irrefl : ∀ a → a <ᵀ a → lt ≡ eq
<-irrefl a p = trans (sym (<⇒cmpᵀ p)) (cmpᵀ-refl a)

_ : cmpᵀ (I ∷ []) (ψ (I ∷ []) [] ∷ 𝟏 ∷ []) ≡ lt   -- 上面说的别名反例
_ = refl
```

## §10 测试 (不是证明)

> 测试脚本已入库: `probes/Survey/scripts/eboi/`, 复现方法见 [查阅手册](../../Survey/OrdinalNotationsGuide.md) §8. 下文若说脚本不在仓库, 以此为准.

以下数字来自我写的转写脚本与 `SetzerTest`, 都不在仓库里 (目录规则只允许本文件). 映射写在这里以便重做:

$$\tau(\mathbf 1)=\varphi'_0 0,\quad \tau(\psi_u(0))=\Omega'_{\tau u},\quad \tau(\psi_u(a))=\psi_{\Omega'_{\tau u+1}}(\tau a)\ (a\ne 0),\quad \tau(\psi_I a)=\psi_I(\tau a),\quad \tau(I)=I.$$

它把调研 §8 的 τ 扩张到 $\psi_I$ 与 $I$, 没有下标错位: 我方的 `ψI a` 就映到 Setzer 的 $\psi_I a$.

**真定义上的测试.** 把归档的 `Syntax`, `Order`, `Closure`, `Arith` 复制到暂存目录, 用 Agda 跑 Setzer 的 `lt`, `isOT` 本身, 不是转写:

| 测试 | 样本 | 结果 |
|---|---|---|
| `isNF t` 等于 `isOT (τ t)` | 大小 $\le 4$ 的全部 1489 个原始项 | 全部一致 |
| 闭包样本全在 `isNF` 与 OT 内 | 从 70 个种子的闭包 (4000 项) 随机取 1000 项 | 全部成立 |
| `<?` 等于 Setzer 的 `lt` | 这 1000 项的全部 $10^6$ 对 | 全部一致 |
| $t[n]$ 在 OT 与 NF 内; $t[n]\prec t$; $t[n]\prec t[n+1]$ (都用 Setzer 的序) | 其中 870 个 ω-共尾项, $n\le 3$ | 全部成立 |

**Python 转写上的测试** (核对过: 转写与 Agda 的 `fsn` 在 148 个值上逐字相同, 用 `refl`):

| 测试 | 样本 | 结果 |
|---|---|---|
| 闭包: 留在 NF, 留在 OT, 严格递减 | 20000 项, 66650 步 (含规则基数索引的步) | 无一例外 |
| 单调: $t[n]<t[n+1]$ | 18437 个 ω-共尾项, $n\le 4$ | 无一例外 |
| 与 Setzer 序一致 | 300000 个随机对 | 无一例外 |
| 全序公理: 传递、反对称 | 300000 个三元组 | 无一例外 |
| `isNF` 对 `isOT ∘ τ` | 大小 $\le 5$ 的全部 14665 个原始项, 其中 3688 个 NF | 全部一致 |

闭包样本走到了所有分派分支: $\psi_I$ 的 $\rho<I$ (5986 次出现)、$\rho=I$ (789)、$\rho>I$ (46), $\psi_u$ 的 $\rho=I$ 穿透 (1228) 与折叠 (1059), $\Omega_u$ 的 $\mathrm{cof}\,u=I$ (10). 这是子项出现次数, 最稀的 46 与 10 两类样本偏薄.

**已知不一致.** $\psi_f(0)$ 这个别名上: Setzer 给 $\Lambda\prec\Omega'_\Lambda$, `cmpᵀ` 给 `eq`. 这个项不在 OT 也不在 NF, 所以不算冲突; 也正因如此 NF 外的序不要当真.

**与 $T_W$ 的逐项比较.** 按 Wiki 规则转写, 加调研 §4 的 A, B, C 三条修正, 翻译 `ψI a` $\mapsto\psi^{T_W}_I(1+a)$, 6000 项上每项取 $n\le 2$:

| $\gamma_0$ 在 $\rho=I$ | 一致 / 不一致 | 只含 EBO 文法的项上的不一致 |
|---|---|---|
| $1$ (字面) | 13404 / 2463 | 0 |
| $\Lambda$ (本文) | 14295 / 1572 | 0 |

余下的不一致来自 $1+a$ 吸收. 核对方法: 把 $T_W$ 脚本的 $\psi_I$ 下标换成本文的 $a$ (不加 $1+$), 其它不动, 同一样本上是 15867 / 0. 这个比较有一半是同构造 (脚本的 ψ_I 子句本来就只差下标), 它只说明偏移之外没有别的差异. 例如 $\psi_I(\omega)[n]$ 在这里是 $\psi_I(n)$, 在 $T_W$ 是 $\psi^{T_W}_I(n)$, 即本文的 $\psi_I(n-1)$. 这是下标约定的代价, 不是规则错误; 每个不一致处都是本文的项更大. 所以**到 I 层, 本文不与 $T_W$ 逐项一致**, 只有 EBO 这一段一致.

## §11 对纲领的意义

**被 "EBO 不动" 逼出来的东西.**

1. $\psi_I(0)=\Lambda$: 由 $\Omega_0=1$ 逼出 (§1). 选 $T_W$ 的下标反而要在 EBO 的 $\psi_0(0)=1$ 旁边再放一个同值的 $\psi_I(0)=1$.
2. 灵巧构造子 `Ω̂`, `ψ̂`: 下标空间等于项空间, 所以 $\Omega_f$ 必然是合法的项, 必须当别名处理. 这是唯一对 EBO 规则的形状改动, 由 §7.3 证明在 EBO 项上是恒等的.
3. $\gamma_0=\psi_\rho(0)$: EBO 的 $\Omega_\mu$ 的统一读法, 在 $\rho=I$ 处给出 $\Lambda$.

**保守性为什么是对的, 又为什么不深.** 它对全部项成立, 没有例外项, 连 EBO 的哑值也相同. 但这不是深刻的事实: `ι` 的像对子项与 `cof` 封闭, 新子句一条也走不到, 所以证明只是在核实我没有手滑. 真正的内容在 §10: 新规则在 $I$ 层的行为是否正确, 那边只有测试.

**树侧要匹配什么.** 对照 [InaccTree](InaccTree.lagda.md) §3 的 `OrdI` (本文不依赖它), 下列规则是树要实现的:

- **容易.** $\Lambda[n]$ 与 $\psi_I(b+1)[n]$ 是 ℕ-索引的 Ω-塔; $\psi_I(b)[n]$ 在 $\mathrm{cof}\,b=\omega$ 时逐点进参数.
- **目标 $I$ 的派发, 折叠输出层号.** $\psi_0(I)[n]=\psi_0(\gamma_n)$ 中 $\gamma_{k+1}=\psi_I(I[\gamma_k])$. 这里 $I[\eta]=\eta$ 把一个**层号**当作树的前驱喂给 `limᴵ`, 折叠的输出又回到层号. 树侧要有 "$\psi_I$ 的值是一个层号" 且 $\gamma_k$ 可以再当 `limᴵ` 的索引: 这正是 InaccTree 判决问题的所在, 记号这边的 `cmpᵀ (idx r) u` 是语法比较, 树上没有对应物.
- **`Ω̂` 的不动点判别.** 记号按项的形状判断 $u\in Fi$. 树上"这个层号是不动点吗"没有现成的判别, 所以我预计树要么带标签 (沿用替身), 要么让 $\Omega$ 在 $\psi_I$ 的像上定义性地返回自身. $\psi_0(\Omega_{I+\omega})[0]=\psi_0(I)$ 与 $\psi_\Lambda(\omega)[0]=\Lambda$ 是最小的验收样例.
- **$\rho>I$ 折叠进 $\psi_I$.** $\psi_I(\Omega_{I+1})$ 的 $\gamma_0=I$, $\gamma_1=\psi_{u=I}(I)$: 折叠链穿过 $I$ 本身, 在 $[I,\Omega_{I+1})$ 上算完再落回 $I$ 之下. 下标 $\ge I$ 的 ψ 要与 $I$ 之下的 ψ 用同一条规则. 我认为这是最难的一条, 这是判断, 未试过.
- **$\rho<I$ 穿透 $\psi_I$.** $\psi_I(\Omega_1)$ 的共尾度是 $\Omega_1$, 而 $\psi_I$ 的值在 $I$ 之下: 树节点要在 $\psi_I$ 的值里保留 $\Omega_1$-分支. 这在 Ω-不动点之上不是 ω-极限.

**全 EBO 的 NF 谓词现在有了.** `isOTᵉ` 与 `isNF` (§9) 是递归可判定的, `NF-ι` 证明二者在 EBO 上相同. InaccTree 文首第 5 点说的 "全 EBO 的 NF 谓词尚不存在" 可以换成: 谓词存在, 封闭性 (Buchholz Lemma 3.3 的 EBO 版) 与良基性不存在.

**良基性的方向.** 嵌入 OT_I 这条路现在有样本支持 (§10): 下标不错位, 序一致, 闭包不离开 OT. Setzer 的 `wellfounded` 只到 $\psi_{\Omega_1}\Omega_{I+n}$, 所以即使 τ 的义务都完成, 它也只覆盖 $\psi_0(\Omega_{I+n})$ 以下, 不覆盖全部 Tᴵ: Tᴵ 的项还能写 $\psi_0(\Omega_{\Omega_{I+1}})$, 其极限应当是 $I$ 之上第一个 Ω-不动点之下的 $\psi_0$ (推断). 这一段的项也通过了样本测试, 但没有已证的良基性可以拉回. 第 3 层义务 (τ 严格保序、保 NF、NF 对 `fsn` 封闭) 都没有做.

**未决的规则选择.**

1. $\rho=I$ 时 $\gamma_0$ 取 $\Lambda$ 还是 $1$. 我选 $\Lambda$, 理由是 $\gamma_0=\psi_\rho(0)$ 这个统一原则, 与 $T_W$ 的逐项不一致因此少 891 处 (§10). 两者极限相同. 若树侧的 $\psi_I$ 在 $0$ 处更自然地取别的值, 可以改, 只动 `γT` 一行, 不影响保守性.
2. $\psi_I(\text{极限})$ 与 $T_W$ 的错位 (§10) 是约定的结果, 不打算修. 如果将来要对照 $T_W$ 或 Maksudov 的 Mahlo 系统, 要在那边加上这个偏移.
3. $I[n]$ 与 $\rho<I$ 的 $\psi_I(b)[n]$ 是哑值 (ℕ-截断), 与 EBO 处理不可数共尾的办法相同. 它们不影响可数项.
4. 别名在 `cmpᵀ` 上给 `eq`. 也可以令其严格比 $f$ 大或小, 只影响 NF 外.

**没有做的.** 全系统的 NF 封闭性、`_<ᵀ_` 在 NF 上的良基性、τ 的保序保 NF, `lt` 蕴含 `_<ᵀ_` 在 NF 上的版本, FGH 的保守性 (规则层面已由 `fsn`, `cof`, `pred` 的等式给出, 但 `FGH` 对 `Acc` 证书不依赖的等式没有写). `Fi` 的值语义, 也就是这些项确实指称所称的序数, 这里没有形式化.

## 参考

- D. Maksudov, *FS for Hypcos's notation (with weakly inaccessibles cardinals)* (博客, 转述见调研 §11: $\psi_{I_{\nu+1}}(1)$, $\psi_{I_{\nu+1}}(\beta+1)$ 的塔起点是 $I_\nu+1$, $\psi_{I_{\nu+1}}(\beta)+1$, 下标有歧义, 与 Wiki 表相同的读法下与 §5.3 同形; 其标准形是语义的, 本文没有采用); Wiki 表 [List of systems of fundamental sequences](https://googology.miraheze.org/wiki/List_of_systems_of_fundamental_sequences) ($T_W$ 规则取自这里, 社区, 无证明). 作者的 Google Sites 页面我抓取时只返回导航, 没有读到规则.
- p進大好きbot, *Ordinal Notation Associated to Extended Buchholz's OCF* (EBO 的 $G$ 谓词; 我读的是调研 §11 的转述, 自己没有读到原页面).
- A. Setzer, *Well-ordering proofs for Martin-Löf type theory*, APAL 1998; 转写见 `archive/src/Mahlo/Inacc/`.
- 调研 [OrdinalNotationsFS](../../Survey/OrdinalNotationsFS.md) §3.1, §4, §8, §9, §11.
