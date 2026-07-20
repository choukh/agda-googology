# 范式 B: 有限项表记系统 — Extended Buchholz (Phase N-1)

> 本文件开启 **范式 B (notation 范式)** 探索: 放弃 Brouwer 树的语义序数, 改用**有限项语法**.
> 动机与全局论证见 [FINDINGS.md](FINDINGS.md), 与 Brouwer 范式 (范式 A) 的对照见 [../ROADMAP.md](../ROADMAP.md).
>
> **一句话**: Brouwer 范式的 Mahlo 墙 (BoundedTrich, [../PastBTBO/Mahlo/FINDINGS.md](../PastBTBO/Mahlo/FINDINGS.md)) 是
> constructive taboo ([de Jong et al. 2026](https://arxiv.org/abs/2602.10844)) —— 语义树上的无条件三歧性不可得.
> 但**有限项系统免疫此 taboo**: 项是有限语法树, 比较是结构递归全函数, 无条件三歧性免费.
> 这正是 Rathjen 对 KPM 做序数分析时用的真实数学结构 (notation system T(M)).
>
> **本文件实测结论 (TL;DR)**:
> - ✅ Extended Buchholz 项系统 (Maksudov, ψ_ν 下标为任意项) 落地, 全部结构递归.
> - ✅ 无条件可判定比较 `cmpᵀ` — **范式 A 卡死的三歧性在这里是 10 行函数**.
> - ✅ ROADMAP §3.3 "终极目标" ψ(Ω_Ω_Ω) 在此范式中是一个**具体的项** (`ψΩΩΩ`), 且可判定地参与比较.
> - ✅ 基本列 (Buchholz 6 规则 + Maksudov 扩展) 以"**构造即证明**"风格落地: 每个 `fsn↓` 值自带 `<ᵀ`-证书.
> - ✅ FGH 沿 `Acc`-递归定义, 通过停机检查器 (`--safe`, 无公理) — 符合纲领第 2, 3 条.
> - ⚠️ **新墙被隔离为单一义务**: 原始 `_<ᵀ_` 在全项集上**非良基** (§8 给出无穷降链反例),
>   良基性必须限制在标准形 (NF) 子集上证明. 这是已知可证 (--safe Agda 的证明论强度 ≫ EBO),
>   但工程量为研究级 (对照: ccz181078 在 Coq 中证明了 Buchholz 系统的 WF). 详 §8.
>
> 强度: 本表记系统的极限 = **EBO (Extended Buchholz Ordinal) = ψ₀(Λ), Λ = 最小的 Ω-不动点**,
> 远超范式 A 的结构天花板 ψ(Ω_(Ω^Ω)) (ROADMAP §5.4).
>
> 工程注记: `cof` 全程避免 `with` 而用一等辅助函数 (`cofψ0`/`cofA`/`cofψ₊`) 组合定义,
> 证明侧以显式等式参数的 helper 风格 case — 否则 `with` 的不透明辅助函数会卡死归约 (实测).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Notation.EBO where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
```

## §1 项系统

Maksudov 的 extended Buchholz: 每个序数是主项 (additively indecomposable) 的降序和.
主项只有一种: `ψ u a` (= ψ_u(a), 其中 u 是层级, a 是参数, **两者都是项**).
和用 `List` 表示, `[]` = 0.

关键对照: 范式 A 中"层级"必须是带 BoundedTrich 的 `Ordᴰ` (序型 ≤ Ω, 这是 ψ(Ω_Ω) 天花板的根源);
这里层级就是项本身 — **层级空间与序数空间同一**, Ω-下标可以无穷嵌套, Λ = Ω-不动点成为系统极限.

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

自然数与 Ω 数的项:

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

## §2 项上的序: 归纳定义 + 可判定比较

序是**纯语法的字典序**: 和 (列表) 按字典序; 主项先比层级 u, 再比参数 a.
对标准形 (降序 + ψ-standardness) 而言这就是序数序 — Buchholz 系统的经典事实.

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

**范式 A 撞不穿的墙, 在这里是 10 行结构递归** — 无条件三歧比较:

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

taboo 为什么消失: `_<_` (范式 A) 的 lim-case 需要判定两个**任意 ℕ→树 函数**的像的关系,
这泄露 WLPO. 这里没有函数 — `ψ u a` 的"不可数宽度"只存在于**指称语义**中,
语法上它是两个有限子项. 判定性随归纳结构免费而来.

## §3 前驱与共尾度

`cof` 把每个项分类: 0 / 后继 / ω-共尾 / Ω_{μ+1}-共尾 (正规不可数共尾).
这是基本列系统的路由器, 对应 Buchholz–Maksudov 的 cof 分类.

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

后继项的重构: `cof a ≡ c1` 蕴含 `a = pred a + 1`:

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

## §5 基本列: 构造即证明

风格要点: 不先定义 `fs : T → ℕ → T` 再补证递减性 (那需要与定义的 case 结构完全同步的重放),
而是让基本列**直接返回携带 `<ᵀ`-证书的值**. 每个证书都是一行构造子.

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

`fsT↓ a η` 实现 Ω-共尾项的 η-段代换 a[η] (Buchholz 规则 2/5 的 T-索引形式).
前提: `cof a ≡ cΩ μ` 且 `η <ᵀ Ω_{μ+1}`. 正规叶 (`a = Ω_{μ+1}`) 处 a[η] = η — 前提恰好保证递减.

工程注记: 递归经由 where-helper 会让终止检查器丢失 size-change 信息 (实测),
故所有 helper 提升为顶层互递归函数, 且**子项整体作参数传递** (严格递降 ∘ 相等 = 严格递降).

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

规则 6 的 γ-链 (Buchholz: γ₀ = Ω_μ, γ_{k+1} = ψ_μ(β[γ_k])), 每个 γ_k 自带 `< Ω_{μ+1}` 证书 —
两个分支的证书都是 `ψ_μ(·) < ψ_{μ+1}(0)` 的一行 `lv<`:

```agda
γ↓ : ∀ β μ → cof β ≡ cΩ μ → ℕ → Below (Ωs μ)
γ↓ β μ e zero    = Ωt μ ⟨ hd< (lv< (<-sucT μ)) ⟩
γ↓ β μ e (suc k) =
  let g = γ↓ β μ e k
      r = fsT↓ β e (dec g)
  in (ψ μ (trm r) ∷ []) ⟨ hd< (lv< (<-sucT μ)) ⟩
```

主基本列 `fsn↓ x xs n` = (x ∷ xs)[n], 覆盖全部 6 条规则:

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

注记 (诚实): 规则 5 (Ω) 分支的真基本列是 Ω_{μ+1}-索引的; FGH 只会喂 ℕ, 而可数项的共尾度
永远不落在此分支 (可数项的 cof ∈ {c0, c1, cω}), 所以这里用 `natT n` 截断是无害哑值.
同理 "正规 Ω_u" 分支. 这两个分支只为全函数性存在.

## §6 FGH: 沿 Acc 递归

`Acc` 就是"停机检查器认可的超限递归": 构造子 `acc` 的字段在结构上变小,
FGH 对 Acc-参数做结构递归 — **与纲领第 3 条 (自动停机检查) 完全相容, 无公理**.

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

## §7 实测 demo

### 7.1 表记级: ψ(Ω_Ω_Ω) 是一个项, 且参与可判定比较

```agda
ΩTower : ℕ → T          -- 1, Ω, Ω_Ω, Ω_Ω_Ω, ...
ΩTower zero    = natT 1
ΩTower (suc k) = Ωt (ΩTower k)

ψΩΩΩ : T                -- ROADMAP §3.3 的 "终极目标" ψ(Ω_Ω_Ω): 此范式中的一个具体项
ψΩΩΩ = ψ [] (ΩTower 3) ∷ []

EBOψ : ℕ → T            -- 全系统对角化: ψ₀(Ω-塔_n), n → ∞ 趋于 EBO = ψ₀(Λ)
EBOψ n = ψ [] (ΩTower n) ∷ []

_ : cmpᵀ ψΩΩΩ (EBOψ 4) ≡ lt      -- ψ(Ω_Ω_Ω) < ψ(Ω_Ω_Ω_Ω): 无条件判定, refl 直接算出
_ = refl

_ : cmpᵀ (EBOψ 4) ψΩΩΩ ≡ gt
_ = refl

_ : cmpᵀ ψΩΩΩ ψΩΩΩ ≡ eq
_ = refl
```

### 7.2 基本列实测: ε₀ = ψ₀(Ω) 的 γ-链

ψ₀(Ω)[2] 应为 ψ₀(ψ₀(ψ₀(1))) = ω^(ω^ω) (γ₀ = Ω₀ = 1, γ₁ = ψ₀(Ω[γ₀]) = ω, γ₂ = ψ₀(ω) = ω^ω):

```agda
εₒ : T
εₒ = ψ [] (Ωt (natT 1)) ∷ []

_ : trm (fsn↓ (ψ [] (Ωt (natT 1))) [] 2)
  ≡ ψ [] (ψ [] (ψ [] (𝟏 ∷ []) ∷ []) ∷ []) ∷ []
_ = refl
```

### 7.3 FGH 实测: 底段 Acc + 数值

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

### 7.4 大数 (modulo 单一 WF 证书)

范式 B 的大数 = FGH 应用于 EBO-对角项. 唯一缺口是 Acc 证书 — 这就是被隔离出的新墙:

```agda
EBO-number : (∀ n → Acc (EBOψ n)) → ℕ → ℕ
EBO-number wf n = FGH (EBOψ n) (wf n) n
```

若提供 `wf` (§8 的 WF 义务), `EBO-number wf 99` 就是超过 f_{ψ(Ω_Ω_Ω)}(99) 的合法大数 —
以 BTBO 的尺度看, 它把 ROADMAP 整个路线图 (Phase 7-12) 一次性越过.

## §8 诚实评估: 新墙的精确形状

**`_<ᵀ_` 在全项集上非良基.** 反例 (纯语法的无穷降链):

    ω  >  1 + ω  >  1 + 1 + ω  >  1 + 1 + 1 + ω  >  ...

即 `ψ₀(1) ∷ []  >ᵀ  𝟏 ∷ ψ₀(1) ∷ []  >ᵀ  𝟏 ∷ 𝟏 ∷ ψ₀(1) ∷ [] >ᵀ ...` — 每步都由 `hd<`/`tl<` 合法导出
(首项 𝟏 <ᴾ ψ₀(1)). 这些项**不是标准形** (非降序), 序数指称相同 (都是 ω), 但语法序严格下降.

因此 WF 义务的精确形状是:

1. **NF 谓词**: 降序条件 + ψ-standardness (Buchholz 的 `a ∈ C_u(a)` 条件的语法化).
2. **NF 保持**: `fsn↓` 与 `pred` 保持 NF (对 NF 输入).
3. **WF(NF)**: `_<ᵀ_` 限制在 NF 子集上良基.

三者合取 ⇒ `∀ n → Acc (EBOψ n)` ⇒ §7.4 的大数无条件成立.

**为什么这堵墙与范式 A 的墙本质不同**:

| | 范式 A 的墙 (BoundedTrich) | 范式 B 的墙 (WF-NF) |
|---|---|---|
| 性质 | constructive taboo (定理级不可能) | 可证明性问题 (证明论强度足够) |
| 证据 | de Jong et al. 2026; Phase 1-7 实测 | --safe Agda (含 IR) 强度 ≫ EBO; Coq 先例 (ccz181078 证 Buchholz WF) |
| 出路 | 无 (须换范式) | 纯工程 (研究级, 数千行) |

**已验证部分** (本文件, 全部通过 `--safe --without-K` 编译, 无公理):
项系统 / 无条件比较 / cof / 基本列 (6 规则) / 递减证书 / Acc-FGH / 底段 Acc / 数值 demo.

**下一步** (见 [FINDINGS.md](FINDINGS.md)):
Phase N-2 Mahlo 项系统 ([Mahlo.lagda.md](Mahlo.lagda.md)) — 真 Mahlo 级表记;
Phase N-3 WF 义务 — 候选路线: (a) 直接归纳 (Buchholz/Rathjen 式分层 TI), (b) 语义化到
Takahashi-MLQ Mahlo universe ([../PastBTBO/Mahlo/Phase1.lagda.md](../PastBTBO/Mahlo/Phase1.lagda.md), 已编译) 做 WF 反射.

## 参考

- Buchholz 1986, *A new system of proof-theoretic ordinal functions*
- D. Maksudov, *The extension of Buchholz's function* + fundamental sequences (googology)
- Rathjen 1990, *Ordinal notations based on a weakly Mahlo cardinal*
- de Jong–Kraus–Forsberg–Xu 2026, *Generalized Decidability via Brouwer Trees* (taboo)
- ccz181078, Coq WF 证明先例: [googology repo](https://github.com/ccz181078/googology)
