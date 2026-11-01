# 范式 B: 真 Mahlo 级项系统 — I-度数层级 + M 对角 (Phase N-2)

> 前置: [EBO.lagda.md](EBO.lagda.md) (范式 B 基础设施: 项/序/cmp/cof/基本列/Acc-FGH 的 extended Buchholz 版).
> 本文件把同一套管线推到 **Mahlo 级**: 层级空间加入
>
> - `I d b` — **度数-d 弱不可达层级的第 b 个** (层级映射 ν ↦ Ω_ν 的度数-d 不动点枚举; Rathjen χ_d(b) 的层级化),
>   其中 **d, b 是任意项 — 度数可以包含 M 本身** (χ_{M}(0), χ_{M+1}(...) 等真 Mahlo 度数是合法语法);
> - `M` — Mahlo 层级: 全体 I-度数层级的正规极限.
>
> **Mahlo 对角在哪**: M-共尾参数的折叠 γ-链走 `γ_{k+1} = I (a[γ_k]) (a[γ_k])` —
> **度数由被折叠参数的前段近似驱动**. 这是 Rathjen "M-共尾 ⇒ 经 χ_下标 反射到正规层级"
> 的基本列形态 (Hyp_cos / Maksudov 系统同款机制).
>
> **实测结论 (TL;DR)**:
> - ✅ Mahlo 级项语法 + **全部跨构造子序规则 + 无条件可判定比较** 编译通过 —
>   范式 A 在 `<ᴹ-dec` 上撞死的正是这一层 ([../PastBTBO/Mahlo/FINDINGS.md](../PastBTBO/Mahlo/FINDINGS.md) §3-5:
>   770 LOC 无解), 这里是 ~60 行结构递归.
> - ✅ `χ_M(0) < M`, `ψ_M(0) ≡ M` (别名) 等真 Mahlo 度数比较可 `refl` 直接计算 (§7).
> - ✅ 基本列全函数 + 每值自带 `<ᵀ` 证书; I/M 情形的 γ-链落地 (含 M 对角). Acc-FGH 管线同 EBO.
> - ⚠️ 诚实边界 (§8): (1) WF 义务同 EBO (NF-限制良基性, 未证);
>   (2) I/M 层级的基本列取的是 **sound-but-not-cofinal** 的简化链 (每值确凿递减, 但高层链
>   未必在项序中共尾 — FGH 停机性与合法性不受影响, 顶层增长率被低估);
>   (3) I-枚举的比较约定 (枚举偏移 eq→gt/lt) 与 M-含度数的基本列覆盖为 Phase 2 待核对项.
>
> 表记级强度主张 (语法+序层面): 系统含 ψ₀(M) 与全部 M-构建度数的 χ-项,
> 对标 Rathjen T(M) 的骨架段位; 基本列当前实际驱动到的段位见 §8 讨论.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Notation.Mahlo where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
```

## §1 项系统

```agda
data PT : Set
T : Set
T = List PT

data PT where
  ψ : (u a : T) → PT     -- ψ_u(a): 层级-u 折叠 (u 是项)
  I : (d b : T) → PT     -- I_d(b): 度数-d 不可达层级第 b 个 (Ω-不动点层级; d 可含 M)
  M : PT                 -- Mahlo 层级

pattern 𝟏 = ψ [] []

private variable
  u v a b c d : T
  d′ b′ : T
  x y : PT
  xs ys : T
  n : ℕ
  μ ν : T
```

```agda
natT : ℕ → T
natT zero    = []
natT (suc n) = 𝟏 ∷ natT n

sucT : T → T
sucT a = a ++ (𝟏 ∷ [])

Ωt : T → T             -- Ω_μ = ψ_μ(0)
Ωt μ = ψ μ [] ∷ []

Ωs : T → T             -- Ω_{μ+1}
Ωs μ = ψ (sucT μ) [] ∷ []

vI : T → T → T         -- 层级项 [I d b]
vI d b = I d b ∷ []

vM : T                 -- 层级项 [M]
vM = M ∷ []
```

## §2 序: 跨构造子规则 + 无条件可判定比较

语义依据 (每条构造子一行):
`ψ_u(a) < Ω_{u+1}`; `Ω_v = v` 对 I/M 层级; 枚举值 ≥ 索引; χ-值 < M (一切 I-项 < M).

```agda
infix 4 _<ᵀ_ _<ᴾ_

data _<ᵀ_ : T → T → Set
data _<ᴾ_ : PT → PT → Set

data _<ᵀ_ where
  []< : [] <ᵀ (x ∷ xs)
  hd< : x <ᴾ y → (x ∷ xs) <ᵀ (y ∷ ys)
  tl< : xs <ᵀ ys → (x ∷ xs) <ᵀ (x ∷ ys)

data _<ᴾ_ where
  lv<  : u <ᵀ v → ψ u a <ᴾ ψ v b                 -- 先比层级
  ar<  : a <ᵀ b → ψ u a <ᴾ ψ u b                 -- 同层级比参数
  ψI<  : u <ᵀ vI d b → ψ u a <ᴾ I d b            -- ψ_u(·) < Ω_{u+1} ≤ I_d(b) 当 u < I_d(b)
  Iψ<  : vI d b <ᵀ v → I d b <ᴾ ψ v c            -- I_d(b) = Ω_{I_d(b)} < Ω_v ≤ ψ_v(·)
  Iψₑ< : I d b <ᴾ ψ (vI d b) (y ∷ ys)            -- 同层级, 参数非零: v < ψ_v(a)
  ψM<  : u <ᵀ vM → ψ u a <ᴾ M
  Mψ<  : vM <ᵀ v → M <ᴾ ψ v c
  Mψₑ< : M <ᴾ ψ vM (y ∷ ys)
  Id<  : d <ᵀ d′ → b <ᵀ vI d′ b′ → I d b <ᴾ I d′ b′   -- 低度数: 与不动点比较归结到索引
  Ib<  : b <ᵀ b′ → I d b <ᴾ I d b′                     -- 同度数: 枚举单调
  Ix<  : vI d b <ᵀ b′ → I d b <ᴾ I d′ b′               -- 值 < 对方索引 ⇒ < (覆盖 d > d′)
  IM<  : I d b <ᴾ M                                    -- 一切 χ-层级 < M (真 Mahlo 度数含内)
```

**范式 A 的 770-LOC 死墙, 此处 ~60 行** — Mahlo 级无条件三歧比较:

```agda
data Cmp : Set where lt eq gt : Cmp

flipC : Cmp → Cmp
flipC lt = gt
flipC eq = eq
flipC gt = lt

-- 工程注记 (实测三连):
-- (1) 与单主项 p 比较用专门函数 cmpT1/cmp1T, 避免 `cmpᵀ u (p ∷ [])` 重新包装;
-- (2) 整参数用 @-模式绑定 (重建的构造子应用在终止检查器中是 unknown);
-- (3) 分派一律用急切组合子, 不用 with — 嵌套 with-lifting 会摧毁 size-change 分析.

-- 字典序组合: 首位相等看次位
lexc : Cmp → Cmp → Cmp
lexc lt _ = lt
lexc gt _ = gt
lexc eq r = r

-- 头比较结果 + 尾是否为空 ⇒ 列表 vs 单主项
t1c : Cmp → T → Cmp
t1c lt _ = lt
t1c gt _ = gt
t1c eq [] = eq
t1c eq (_ ∷ _) = gt

-- ψ vs 不动点层级 v: 层级相同时 ψ_v(0) = Ω_v = v 为别名 (eq), 参数非零则 gt
cmpψv : T → Cmp → Cmp
cmpψv []      eq = eq
cmpψv (_ ∷ _) eq = gt
cmpψv _       lt = lt
cmpψv _       gt = gt

-- 不动点层级 v vs ψ: 镜像 (参数非零时 v < ψ_v(c))
cmpvψ : T → Cmp → Cmp
cmpvψ []      eq = eq
cmpvψ (_ ∷ _) eq = lt
cmpvψ _       lt = lt
cmpvψ _       gt = gt

-- I vs I 的低度数侧: 索引 vs 对方整体 (不动点吸收); eq 为枚举偏移约定 (§8)
absorb : Cmp → Cmp
absorb lt = lt
absorb eq = gt
absorb gt = gt

absorbGt : Cmp → Cmp        -- 高度数侧镜像: 值 vs 对方索引
absorbGt lt = lt
absorbGt eq = lt
absorbGt gt = gt

-- I-I 分派: 度数比较 ⇒ 选取三支之一
iic : Cmp → Cmp → Cmp → Cmp → Cmp
iic eq r _ _ = r
iic lt _ r _ = r
iic gt _ _ r = r

cmpᵀ : T → T → Cmp
cmpᴾ : PT → PT → Cmp
cmpT1 : T → PT → Cmp        -- cmpT1 t p ≙ cmpᵀ t (p ∷ [])
cmp1T : PT → T → Cmp        -- cmp1T p t ≙ cmpᵀ (p ∷ []) t

cmpᵀ [] [] = eq
cmpᵀ [] (y ∷ ys) = lt
cmpᵀ (x ∷ xs) [] = gt
cmpᵀ (x ∷ xs) (y ∷ ys) = lexc (cmpᴾ x y) (cmpᵀ xs ys)

cmpT1 [] p = lt
cmpT1 (x ∷ xs) p = t1c (cmpᴾ x p) xs

cmp1T p [] = gt
cmp1T p (x ∷ xs) = flipC (t1c (flipC (cmpᴾ p x)) xs)

cmpᴾ (ψ u a) (ψ v b) = lexc (cmpᵀ u v) (cmpᵀ a b)
cmpᴾ (ψ u a) q@(I d b) = cmpψv a (cmpT1 u q)
cmpᴾ p@(I d b) (ψ v c) = cmpvψ c (cmp1T p v)
cmpᴾ (ψ u a) q@M = cmpψv a (cmpT1 u q)
cmpᴾ p@M (ψ v c) = cmpvψ c (cmp1T p v)
cmpᴾ p@(I d b) q@(I d′ b′) =
  iic (cmpᵀ d d′) (cmpᵀ b b′)
      (absorb (cmpT1 b q))          -- d < d′: I_d(b) vs 不动点, 归结到索引
      (absorbGt (cmp1T p b′))       -- d > d′: 对称, 值 vs 对方索引
cmpᴾ (I d b) M = lt
cmpᴾ M (I d b) = gt
cmpᴾ M M = eq
```

## §3 前驱与共尾度

共尾度分类新增两类正规层级: `cI d b` (共尾度 I_d(b)) 与 `cM` (共尾度 M).

```agda
data Cof : Set where
  c0 : Cof
  c1 : Cof
  cω : Cof
  cΩ : (μ : T) → Cof        -- 共尾度 Ω_{μ+1}
  cI : (d b : T) → Cof      -- 共尾度 I_d(b)
  cM : Cof                  -- 共尾度 M

pred : T → T
pred [] = []
pred (x ∷ y ∷ ys) = x ∷ pred (y ∷ ys)
pred (𝟏 ∷ []) = []
pred (x ∷ []) = x ∷ []

-- ψ_u(0) = Ω_u 的共尾度 (第二参数 = cof u); I/M-共尾穿透 (Ω 在不动点层级连续)
cofψ0 : T → Cof → Cof
cofψ0 u c0       = c0
cofψ0 u c1       = cΩ (pred u)
cofψ0 u cω       = cω
cofψ0 u (cΩ μ)   = cΩ μ
cofψ0 u (cI d b) = cI d b
cofψ0 u cM       = cM

-- 折叠路由: 参数共尾度 ρ vs 本层级 u — ρ ≤ Ω_u 穿透, ρ > Ω_u 坍缩为 ω (规则 6 类)
route : Cof → Cmp → Cof
route ρ lt = ρ
route ρ eq = ρ
route ρ gt = cω

cofA : T → Cof → Cof
cofA u c0       = cω
cofA u c1       = cω
cofA u cω       = cω
cofA u (cΩ μ)   = route (cΩ μ)   (cmpᵀ (sucT μ) u)
cofA u (cI d b) = route (cI d b) (cmpᵀ (vI d b) u)
cofA u cM       = route cM       (cmpᵀ vM u)

cof  : T → Cof
cofP : PT → Cof

cof [] = c0
cof (x ∷ []) = cofP x
cof (x ∷ xs@(_ ∷ _)) = cof xs

cofP (ψ u (y ∷ ys))  = cofA u (cof (y ∷ ys))
cofP (ψ (w ∷ ws) []) = cofψ0 (w ∷ ws) (cof (w ∷ ws))
cofP 𝟏 = c1
cofP (I d b) = cI d b
cofP M = cM
```

## §4 基础引理

```agda
<-sucT : ∀ a → a <ᵀ sucT a
<-sucT [] = []<
<-sucT (x ∷ xs) = tl< (<-sucT xs)

[]<sucT : ∀ a → [] <ᵀ sucT a
[]<sucT [] = []<
[]<sucT (x ∷ xs) = []<

natT<Ωs : ∀ n μ → natT n <ᵀ Ωs μ
natT<Ωs zero    μ = []<
natT<Ωs (suc n) μ = hd< (lv< ([]<sucT μ))

natT<I : ∀ n d b → natT n <ᵀ vI d b
natT<I zero    d b = []<
natT<I (suc n) d b = hd< (ψI< []<)

natT<M : ∀ n → natT n <ᵀ vM
natT<M zero    = []<
natT<M (suc n) = hd< (ψM< []<)
```

后继重构 (与 EBO 同构, 新增 cI/cM 分支的排除):

```agda
pred-suc : ∀ a → cof a ≡ c1 → sucT (pred a) ≡ a
pred-suc [] ()
pred-suc (x ∷ y ∷ ys) e = cong (x ∷_) (pred-suc (y ∷ ys) e)
pred-suc (𝟏 ∷ []) e = refl
pred-suc (ψ (w ∷ ws) [] ∷ []) e = go (cof (w ∷ ws)) e where
  go : ∀ k → cofψ0 (w ∷ ws) k ≡ c1 → sucT (pred (ψ (w ∷ ws) [] ∷ [])) ≡ ψ (w ∷ ws) [] ∷ []
  go c0 ()
  go c1 ()
  go cω ()
  go (cΩ μ) ()
  go (cI d b) ()
  go cM ()
pred-suc (ψ u (y ∷ ys) ∷ []) e = go (cof (y ∷ ys)) e where
  goΩ : ∀ μ m → route (cΩ μ) m ≡ c1 → sucT (pred (ψ u (y ∷ ys) ∷ [])) ≡ ψ u (y ∷ ys) ∷ []
  goΩ μ lt () ; goΩ μ eq () ; goΩ μ gt ()
  goI : ∀ d b m → route (cI d b) m ≡ c1 → sucT (pred (ψ u (y ∷ ys) ∷ [])) ≡ ψ u (y ∷ ys) ∷ []
  goI d b lt () ; goI d b eq () ; goI d b gt ()
  goM : ∀ m → route cM m ≡ c1 → sucT (pred (ψ u (y ∷ ys) ∷ [])) ≡ ψ u (y ∷ ys) ∷ []
  goM lt () ; goM eq () ; goM gt ()
  go : ∀ k → cofA u k ≡ c1 → sucT (pred (ψ u (y ∷ ys) ∷ [])) ≡ ψ u (y ∷ ys) ∷ []
  go c0 ()
  go c1 ()
  go cω ()
  go (cΩ μ)   e′ = goΩ μ   (cmpᵀ (sucT μ) u)  e′
  go (cI d b) e′ = goI d b (cmpᵀ (vI d b) u)  e′
  go cM       e′ = goM     (cmpᵀ vM u)        e′
pred-suc (I d b ∷ []) ()
pred-suc (M ∷ []) ()

pred-< : ∀ a → cof a ≡ c1 → pred a <ᵀ a
pred-< a e = subst (pred a <ᵀ_) (pred-suc a e) (<-sucT (pred a))
```

## §5 基本列: 三族代换 + 三种 γ-链

与 EBO 同款"构造即证明"; 代换按共尾刻度分三族 (Ω_{μ+1} / I_d(b) / M),
全部顶层互递归 + 子项整体传参 (终止检查要求, 见 EBO §5 工程注记).

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

### 5.1 Ω-族代换 (与 EBO 同构)

```agda
fsT↓  : ∀ a {μ} → cof a ≡ cΩ μ → ∀ {η} → η <ᵀ Ωs μ → Below a
fsT↓0 : ∀ u k → cof u ≡ k → ∀ {μ} → cofψ0 u k ≡ cΩ μ →
        ∀ {η} → η <ᵀ Ωs μ → Below (ψ u [] ∷ [])
fsT↓₊ : ∀ u b k → cof b ≡ k → ∀ {μ} → cofA u k ≡ cΩ μ →
        ∀ {η} → η <ᵀ Ωs μ → Below (ψ u b ∷ [])

fsT↓ [] () η<
fsT↓ (x ∷ xs@(_ ∷ _)) e η< =
  let r = fsT↓ xs e η< in (x ∷ trm r) ⟨ tl< (dec r) ⟩
fsT↓ (ψ u (y ∷ ys) ∷ []) e η< = fsT↓₊ u (y ∷ ys) (cof (y ∷ ys)) refl e η<
fsT↓ (ψ (w ∷ ws) [] ∷ []) e η< = fsT↓0 (w ∷ ws) (cof (w ∷ ws)) refl e η<
fsT↓ (𝟏 ∷ []) () η<
fsT↓ (I d b ∷ []) () η<
fsT↓ (M ∷ []) () η<

fsT↓0 u c0 ue ()
fsT↓0 u c1 ue e′ {η} η< =
  η ⟨ subst (λ z → η <ᵀ (ψ z [] ∷ []))
            (trans (cong sucT (sym (cΩ-inj e′))) (pred-suc u ue)) η< ⟩
fsT↓0 u cω ue ()
fsT↓0 u (cΩ ν) ue e′ η< =
  let r = fsT↓ u (trans ue (cong cΩ (cΩ-inj e′))) η<
  in (ψ (trm r) [] ∷ []) ⟨ hd< (lv< (dec r)) ⟩
fsT↓0 u (cI d b) ue ()
fsT↓0 u cM ue ()

private
  routeΩ : ∀ b {ν} → cof b ≡ cΩ ν → ∀ u m {μ} → route (cΩ ν) m ≡ cΩ μ →
           ∀ {η} → η <ᵀ Ωs μ → Below (ψ u b ∷ [])
  routeΩ b be u lt e″ η< =
    let r = fsT↓ b (trans be (cong cΩ (cΩ-inj e″))) η<
    in (ψ u (trm r) ∷ []) ⟨ hd< (ar< (dec r)) ⟩
  routeΩ b be u eq e″ η< =
    let r = fsT↓ b (trans be (cong cΩ (cΩ-inj e″))) η<
    in (ψ u (trm r) ∷ []) ⟨ hd< (ar< (dec r)) ⟩
  routeΩ b be u gt ()

fsT↓₊ u b c0 be ()
fsT↓₊ u b c1 be ()
fsT↓₊ u b cω be ()
fsT↓₊ u b (cΩ ν) be e″ η< = routeΩ b be u (cmpᵀ (sucT ν) u) e″ η<
fsT↓₊ u b (cI d′ b′) be {μ} e″ η< = goI (cmpᵀ (vI d′ b′) u) e″ where
  goI : ∀ m → route (cI d′ b′) m ≡ cΩ μ → Below (ψ u b ∷ [])
  goI lt () ; goI eq () ; goI gt ()
fsT↓₊ u b cM be {μ} e″ η< = goM (cmpᵀ vM u) e″ where
  goM : ∀ m → route cM m ≡ cΩ μ → Below (ψ u b ∷ [])
  goM lt () ; goM eq () ; goM gt ()
```

### 5.2 I-族与 M-族代换

正规叶: `[I d b]` 处代换即恒等 (η), `[M]` 同理; 其余结构穿透.

```agda
cI-inj₁ : ∀ {d b d′ b′} → cI d b ≡ cI d′ b′ → d ≡ d′
cI-inj₁ refl = refl
cI-inj₂ : ∀ {d b d′ b′} → cI d b ≡ cI d′ b′ → b ≡ b′
cI-inj₂ refl = refl

cI-subst : ∀ {d b d′ b′} → cI d b ≡ cI d′ b′ → ∀ {η} → η <ᵀ vI d′ b′ → η <ᵀ vI d b
cI-subst refl η< = η<

fsI↓  : ∀ a {d b} → cof a ≡ cI d b → ∀ {η} → η <ᵀ vI d b → Below a
fsI↓0 : ∀ u k → cof u ≡ k → ∀ {d b} → cofψ0 u k ≡ cI d b →
        ∀ {η} → η <ᵀ vI d b → Below (ψ u [] ∷ [])
fsI↓₊ : ∀ u b k → cof b ≡ k → ∀ {d′ b′} → cofA u k ≡ cI d′ b′ →
        ∀ {η} → η <ᵀ vI d′ b′ → Below (ψ u b ∷ [])

fsI↓ [] () η<
fsI↓ (x ∷ xs@(_ ∷ _)) e η< =
  let r = fsI↓ xs e η< in (x ∷ trm r) ⟨ tl< (dec r) ⟩
fsI↓ (ψ u (y ∷ ys) ∷ []) e η< = fsI↓₊ u (y ∷ ys) (cof (y ∷ ys)) refl e η<
fsI↓ (ψ (w ∷ ws) [] ∷ []) e η< = fsI↓0 (w ∷ ws) (cof (w ∷ ws)) refl e η<
fsI↓ (𝟏 ∷ []) () η<
fsI↓ (I d′ b′ ∷ []) e {η} η< = η ⟨ cI-subst e η< ⟩   -- 正规叶: a[η] = η
fsI↓ (M ∷ []) () η<

fsI↓0 u c0 ue ()
fsI↓0 u c1 ue ()
fsI↓0 u cω ue ()
fsI↓0 u (cΩ ν) ue ()
fsI↓0 u (cI d b) ue e′ η< =
  let r = fsI↓ u ue (cI-subst e′ η<)
  in (ψ (trm r) [] ∷ []) ⟨ hd< (lv< (dec r)) ⟩
fsI↓0 u cM ue ()

fsI↓₊ u b c0 be ()
fsI↓₊ u b c1 be ()
fsI↓₊ u b cω be ()
fsI↓₊ u b (cΩ ν) be {d′} {b′} e″ η< = go (cmpᵀ (sucT ν) u) e″ where
  go : ∀ m → route (cΩ ν) m ≡ cI d′ b′ → Below (ψ u b ∷ [])
  go lt () ; go eq () ; go gt ()
fsI↓₊ u b (cI d₀ b₀) be {d′} {b′} e″ η< = go (cmpᵀ (vI d₀ b₀) u) e″ where
  go : ∀ m → route (cI d₀ b₀) m ≡ cI d′ b′ → Below (ψ u b ∷ [])
  go lt e‴ = let r = fsI↓ b be (cI-subst e‴ η<)
             in (ψ u (trm r) ∷ []) ⟨ hd< (ar< (dec r)) ⟩
  go eq e‴ = let r = fsI↓ b be (cI-subst e‴ η<)
             in (ψ u (trm r) ∷ []) ⟨ hd< (ar< (dec r)) ⟩
  go gt ()
fsI↓₊ u b cM be {d′} {b′} e″ η< = go (cmpᵀ vM u) e″ where
  go : ∀ m → route cM m ≡ cI d′ b′ → Below (ψ u b ∷ [])
  go lt () ; go eq () ; go gt ()

fsM↓  : ∀ a → cof a ≡ cM → ∀ {η} → η <ᵀ vM → Below a
fsM↓0 : ∀ u k → cof u ≡ k → cofψ0 u k ≡ cM → ∀ {η} → η <ᵀ vM → Below (ψ u [] ∷ [])
fsM↓₊ : ∀ u b k → cof b ≡ k → cofA u k ≡ cM → ∀ {η} → η <ᵀ vM → Below (ψ u b ∷ [])

fsM↓ [] () η<
fsM↓ (x ∷ xs@(_ ∷ _)) e η< =
  let r = fsM↓ xs e η< in (x ∷ trm r) ⟨ tl< (dec r) ⟩
fsM↓ (ψ u (y ∷ ys) ∷ []) e η< = fsM↓₊ u (y ∷ ys) (cof (y ∷ ys)) refl e η<
fsM↓ (ψ (w ∷ ws) [] ∷ []) e η< = fsM↓0 (w ∷ ws) (cof (w ∷ ws)) refl e η<
fsM↓ (𝟏 ∷ []) () η<
fsM↓ (I d b ∷ []) () η<
fsM↓ (M ∷ []) e {η} η< = η ⟨ η< ⟩                 -- 正规叶: M[η] = η

fsM↓0 u c0 ue ()
fsM↓0 u c1 ue ()
fsM↓0 u cω ue ()
fsM↓0 u (cΩ ν) ue ()
fsM↓0 u (cI d b) ue ()
fsM↓0 u cM ue e′ η< =
  let r = fsM↓ u ue η<
  in (ψ (trm r) [] ∷ []) ⟨ hd< (lv< (dec r)) ⟩

fsM↓₊ u b c0 be ()
fsM↓₊ u b c1 be ()
fsM↓₊ u b cω be ()
fsM↓₊ u b (cΩ ν) be e″ η< = go (cmpᵀ (sucT ν) u) e″ where
  go : ∀ m → route (cΩ ν) m ≡ cM → Below (ψ u b ∷ [])
  go lt () ; go eq () ; go gt ()
fsM↓₊ u b (cI d₀ b₀) be e″ η< = go (cmpᵀ (vI d₀ b₀) u) e″ where
  go : ∀ m → route (cI d₀ b₀) m ≡ cM → Below (ψ u b ∷ [])
  go lt () ; go eq () ; go gt ()
fsM↓₊ u b cM be e″ η< = go (cmpᵀ vM u) e″ where
  go : ∀ m → route cM m ≡ cM → Below (ψ u b ∷ [])
  go lt e‴ = let r = fsM↓ b be η< in (ψ u (trm r) ∷ []) ⟨ hd< (ar< (dec r)) ⟩
  go eq e‴ = let r = fsM↓ b be η< in (ψ u (trm r) ∷ []) ⟨ hd< (ar< (dec r)) ⟩
  go gt ()
```

### 5.3 三种 γ-链

Ω-链 = Buchholz 规则 6 (同 EBO). **I-链**: 层级取前一 γ 值 (`ψ_{γ_k}(a[γ_k])`),
向不可达层级爬升. **M-链 (Mahlo 对角)**: `γ_{k+1} = I (a[γ_k]) (a[γ_k])` —
度数由被折叠参数驱动, 这就是 "M-共尾经 χ-度数反射" 的表记形态.

```agda
γΩ↓ : ∀ a μ → cof a ≡ cΩ μ → ℕ → Below (Ωs μ)
γΩ↓ a μ e zero    = Ωt μ ⟨ hd< (lv< (<-sucT μ)) ⟩
γΩ↓ a μ e (suc k) =
  let g = γΩ↓ a μ e k
      r = fsT↓ a e (dec g)
  in (ψ μ (trm r) ∷ []) ⟨ hd< (lv< (<-sucT μ)) ⟩

γI↓ : ∀ a d b → cof a ≡ cI d b → ℕ → Below (vI d b)
γI↓ a d b e zero    = [] ⟨ []< ⟩
γI↓ a d b e (suc k) =
  let g = γI↓ a d b e k
      r = fsI↓ a e (dec g)
  in (ψ (trm g) (trm r) ∷ []) ⟨ hd< (ψI< (dec g)) ⟩

γM↓ : ∀ a → cof a ≡ cM → ℕ → Below vM
γM↓ a e zero    = [] ⟨ []< ⟩
γM↓ a e (suc k) =
  let g = γM↓ a e k
      r = fsM↓ a e (dec g)
  in (I (trm r) (trm r) ∷ []) ⟨ hd< IM< ⟩        -- Mahlo 对角: 度数 = a 的前段近似
```

### 5.4 主基本列

```agda
rep↓ : ∀ u {a a′} → a′ <ᵀ a → (n : ℕ) → Below (ψ u a ∷ [])
rep↓ u a′< zero    = [] ⟨ []< ⟩
rep↓ u a′< (suc n) =
  let r = rep↓ u a′< n
  in (ψ u _ ∷ trm r) ⟨ hd< (ar< a′<) ⟩

fsn↓  : ∀ x xs → ℕ → Below (x ∷ xs)
fsn↓0 : ∀ w ws k → cof (w ∷ ws) ≡ k → ℕ → Below (ψ (w ∷ ws) [] ∷ [])
fsn↓₊ : ∀ u y ys k → cof (y ∷ ys) ≡ k → ℕ → Below (ψ u (y ∷ ys) ∷ [])

fsn↓ x (y ∷ ys) n =
  let r = fsn↓ y ys n in (x ∷ trm r) ⟨ tl< (dec r) ⟩
fsn↓ 𝟏 [] n = [] ⟨ []< ⟩
fsn↓ (ψ (w ∷ ws) []) [] n = fsn↓0 w ws (cof (w ∷ ws)) refl n
fsn↓ (ψ u (y ∷ ys)) [] n = fsn↓₊ u y ys (cof (y ∷ ys)) refl n
fsn↓ (I d b) [] n = natT n ⟨ natT<I n d b ⟩       -- 正规层级: FGH 哑分支 (§8)
fsn↓ M [] n = natT n ⟨ natT<M n ⟩                 -- 同上

fsn↓0 w ws c0 ue n = [] ⟨ []< ⟩
fsn↓0 w ws c1 ue n =
  natT n ⟨ subst (λ z → natT n <ᵀ (ψ z [] ∷ [])) (pred-suc (w ∷ ws) ue)
                 (natT<Ωs n (pred (w ∷ ws))) ⟩
fsn↓0 w ws cω ue n =
  let r = fsn↓ w ws n in (ψ (trm r) [] ∷ []) ⟨ hd< (lv< (dec r)) ⟩
fsn↓0 w ws (cΩ ν) ue n =
  let r = fsT↓ (w ∷ ws) ue (natT<Ωs n ν)
  in (ψ (trm r) [] ∷ []) ⟨ hd< (lv< (dec r)) ⟩
fsn↓0 w ws (cI d b) ue n =
  let r = fsI↓ (w ∷ ws) ue (natT<I n d b)
  in (ψ (trm r) [] ∷ []) ⟨ hd< (lv< (dec r)) ⟩
fsn↓0 w ws cM ue n =
  let r = fsM↓ (w ∷ ws) ue (natT<M n)
  in (ψ (trm r) [] ∷ []) ⟨ hd< (lv< (dec r)) ⟩

fsn↓₊ u y ys c0 be n = [] ⟨ []< ⟩
fsn↓₊ u y ys c1 be n = rep↓ u (pred-< (y ∷ ys) be) n
fsn↓₊ u y ys cω be n =
  let r = fsn↓ y ys n in (ψ u (trm r) ∷ []) ⟨ hd< (ar< (dec r)) ⟩
fsn↓₊ u y ys (cΩ ν) be n = goΩ (cmpᵀ (sucT ν) u) where
  goΩ : Cmp → Below (ψ u (y ∷ ys) ∷ [])
  goΩ gt = let g = γΩ↓ (y ∷ ys) ν be n
               r = fsT↓ (y ∷ ys) be (dec g)
           in (ψ u (trm r) ∷ []) ⟨ hd< (ar< (dec r)) ⟩
  goΩ lt = let r = fsT↓ (y ∷ ys) be (natT<Ωs n ν)
           in (ψ u (trm r) ∷ []) ⟨ hd< (ar< (dec r)) ⟩
  goΩ eq = let r = fsT↓ (y ∷ ys) be (natT<Ωs n ν)
           in (ψ u (trm r) ∷ []) ⟨ hd< (ar< (dec r)) ⟩
fsn↓₊ u y ys (cI d b) be n = goI (cmpᵀ (vI d b) u) where
  goI : Cmp → Below (ψ u (y ∷ ys) ∷ [])
  goI gt = let g = γI↓ (y ∷ ys) d b be n            -- I-链折叠
               r = fsI↓ (y ∷ ys) be (dec g)
           in (ψ u (trm r) ∷ []) ⟨ hd< (ar< (dec r)) ⟩
  goI lt = let r = fsI↓ (y ∷ ys) be (natT<I n d b)
           in (ψ u (trm r) ∷ []) ⟨ hd< (ar< (dec r)) ⟩
  goI eq = let r = fsI↓ (y ∷ ys) be (natT<I n d b)
           in (ψ u (trm r) ∷ []) ⟨ hd< (ar< (dec r)) ⟩
fsn↓₊ u y ys cM be n = goM (cmpᵀ vM u) where
  goM : Cmp → Below (ψ u (y ∷ ys) ∷ [])
  goM gt = let g = γM↓ (y ∷ ys) be n                -- M-链折叠 (Mahlo 对角)
               r = fsM↓ (y ∷ ys) be (dec g)
           in (ψ u (trm r) ∷ []) ⟨ hd< (ar< (dec r)) ⟩
  goM lt = let r = fsM↓ (y ∷ ys) be (natT<M n)
           in (ψ u (trm r) ∷ []) ⟨ hd< (ar< (dec r)) ⟩
  goM eq = let r = fsM↓ (y ∷ ys) be (natT<M n)
           in (ψ u (trm r) ∷ []) ⟨ hd< (ar< (dec r)) ⟩
```

## §6 FGH

```agda
data Acc (a : T) : Set where
  acc : (∀ {b} → b <ᵀ a → Acc b) → Acc a

iter : (ℕ → ℕ) → ℕ → ℕ → ℕ
iter f x zero    = x
iter f x (suc k) = f (iter f x k)

FGH : ∀ a → Acc a → ℕ → ℕ
FGH [] _ n = suc n
FGH (x ∷ xs) (acc rs) n = go (cof (x ∷ xs)) refl where
  go : ∀ k → cof (x ∷ xs) ≡ k → ℕ
  go c0 ce = suc n
  go c1 ce = iter (FGH (pred (x ∷ xs)) (rs (pred-< (x ∷ xs) ce))) n n
  go cω ce = let r = fsn↓ x xs n in FGH (trm r) (rs (dec r)) n
  go (cΩ μ)   ce = let r = fsn↓ x xs n in FGH (trm r) (rs (dec r)) n
  go (cI d b) ce = let r = fsn↓ x xs n in FGH (trm r) (rs (dec r)) n
  go cM       ce = let r = fsn↓ x xs n in FGH (trm r) (rs (dec r)) n
```

## §7 实测 demo

### 7.1 Mahlo 级可判定比较 — 范式 A 的死墙在此为 refl

```agda
I₀ : T                  -- I_0(0): 最小弱不可达层级
I₀ = vI [] []

I₁ : T                  -- I_1(0): 度数 1
I₁ = vI (natT 1) []

χM0 : T                 -- I_M(0) = χ_M(0): 真 Mahlo 度数 (度数为 M 本身!)
χM0 = vI vM []

_ : cmpᵀ I₀ I₁ ≡ lt              -- I_0(0) < I_1(0)
_ = refl

_ : cmpᵀ I₁ χM0 ≡ lt             -- I_1(0) < χ_M(0): M-含度数参与判定
_ = refl

_ : cmpᵀ χM0 vM ≡ lt             -- χ_M(0) < M
_ = refl

_ : cmpᵀ (Ωt vM) vM ≡ eq         -- ψ_M(0) = Ω_M = M: 不动点别名, 判定器直接算出
_ = refl

_ : cmpᵀ (ψ vM (natT 1) ∷ []) vM ≡ gt    -- ψ_M(1) > M
_ = refl

-- 度数塔: I_{I_0(0)}(0), I_{I_{I_0(0)}(0)}(0), ... (对角线爬升)
ITower : ℕ → T
ITower zero    = I₀
ITower (suc k) = vI (ITower k) []

_ : cmpᵀ (ITower 3) (ITower 4) ≡ lt
_ = refl

_ : cmpᵀ (ITower 4) χM0 ≡ lt     -- 一切 M-free 度数塔 < χ_M(0)
_ = refl
```

### 7.2 基本列实测: ψ₀(I₀) 的 I-链

γ₀ = 0, γ₁ = ψ_{γ₀}(I₀[γ₀]) = ψ₀(0) = 1, γ₂ = ψ_{γ₁}(I₀[γ₁]) = ψ_1(1);
故 ψ₀(I₀)[2] = ψ₀(ψ_1(1)) — 层级爬进 Ω-territory, 向不可达对角逼近:

```agda
_ : trm (fsn↓ (ψ [] I₀) [] 2)
  ≡ ψ [] (ψ (𝟏 ∷ []) (𝟏 ∷ []) ∷ []) ∷ []
_ = refl
```

ψ₀(M) 的 M-链 (Mahlo 对角): γ₁ = I(M[γ₀])(M[γ₀]) = I_0(0) = I₀-主项,
γ₂ = I_{I₀}(I₀); 故 ψ₀(M)[2] = ψ₀(I_{I₀}(I₀)) — **度数对角机制实际运转**:

```agda
ψ₀M : T
ψ₀M = ψ [] vM ∷ []

_ : trm (fsn↓ (ψ [] vM) [] 2)
  ≡ ψ [] (I (I [] [] ∷ []) (I [] [] ∷ []) ∷ []) ∷ []
_ = refl
```

### 7.3 FGH 数值 + 大数 (modulo WF 证书)

```agda
acc[] : Acc []
acc[] = acc λ ()

acc-1∷ : ∀ {xs} → Acc xs → Acc (𝟏 ∷ xs)
acc-1∷ (acc rs) = acc go where
  go : ∀ {b} → b <ᵀ (𝟏 ∷ _) → Acc b
  go []<             = acc[]
  go (hd< (lv< ()))
  go (hd< (ar< ()))
  go (hd< (Iψ< ()))
  go (hd< (Mψ< ()))
  go (tl< q)         = acc-1∷ (rs q)

accNat : ∀ n → Acc (natT n)
accNat zero    = acc[]
accNat (suc n) = acc-1∷ (accNat n)

_ : FGH (natT 3) (accNat 3) 2 ≡ 2048
_ = refl

-- 旗舰大数: f_{ψ₀(M)}(n), 唯一缺口 = ψ₀(M) 的 Acc 证书 (WF 义务)
Mahlo-number : Acc ψ₀M → ℕ → ℕ
Mahlo-number wf n = FGH ψ₀M wf n
```

## §8 诚实评估

**已验证** (--safe, 无公理, 编译通过): Mahlo 级项语法 (含 M-构建度数) / 全部跨构造子序规则 /
无条件可判定比较 (χ_M(0) < M 等为 refl) / 三族基本列全函数 + 逐值 `<ᵀ` 证书
(含 M-对角 γ-链) / Acc-FGH 管线 / 数值 demo.

**边界与 Phase 2 义务** (按重要性排序):

1. **WF 义务** (与 EBO 相同形状): `_<ᵀ_` 全项集非良基 (EBO §8 反例在此同样成立),
   需 NF 谓词 + NF 保持 + WF(NF). Mahlo 级的 WF(NF) 是**真正的研究前沿** —
   其证明论强度就是 KPM. 候选路线: 语义化到 Takahashi-MLQ Mahlo universe
   ([../PastBTBO/Mahlo/Phase1.lagda.md](../PastBTBO/Mahlo/Phase1.lagda.md) 已编译, 结构上真 Mahlo) —
   范式 A 的"失败"资产在范式 B 中恰好是 WF 证明所需的语义靶.
2. **基本列的共尾性**: I/M-链每值确凿递减 (证书内建), 但**未证在项序中共尾**.
   已知不共尾的段位: I_d(b) 的 b-后继情形 (链经 ψ-塔, 达不到前一枚举点之后的正规区间);
   M-链只对角 M-free 度数塔, 未爬 M-含度数 (I_{χ_M(0)+1} 等). 后果: FGH 在最高层的
   增长率低于表记序型的理论值 — **停机性与合法性不受影响**, 只影响"数有多大"的下界主张.
   修复 = 移植 Maksudov "collapsing α-weakly inaccessible / weakly Mahlo" 的完整 fs 规则
   (本次网络获取被挡, 见 FINDINGS).
3. **枚举偏移约定**: `cmpII` 的 eq→gt/lt 分支 (I_d 在不动点索引处的取值) 是本仓库约定,
   与 Rathjen χ 的枚举语义的精确对齐待核.
4. `ψ_r(0)` 系列的语义规范化 (本模块沿用 Buchholz 层级式 ψ_u, u 为层级项,
   避开了 Rathjen 正规下标式 ψ_π 的 π⁻ 基底问题 — 这是有意的设计选择, 见 FINDINGS §设计).

**与范式 A 的正面对照**: PastBTBO/Mahlo Phase 2 的 `<ᴹ-dec` 4-子case 死墙
(跨家族 witness 无共同上界) 在本模块对应 `cmpᴾ (I d b) (I d′ b′)` 与 `cmpᴾ (ψ u a) (I d b)` —
**这里是全函数, 60 行, refl 可算**. 撞墙的不是 Mahlo, 是范式.
