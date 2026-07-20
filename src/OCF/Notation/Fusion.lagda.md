# 范式融合: 语法索引的 Brouwer 树 (Phase N-2.5 spike)

> **问题** (作者提出): 能否融合范式 A 与范式 B — 保留 Brouwer 树骨架, 把"有限项语法"
> 作为新结构加进去, 使其满足无条件三歧性? 把 "WF 反射" 做成必须义务?
>
> **答案: 可以, 融合体是 `V : T → Set` — 语法索引的 Brouwer 树.** 本文件是编译通过的证明.
>
> 三个诉求逐一兑现:
> - **Brouwer 树骨架**: `V` 的极限构造子 `vω : (∀ n → V (t [ n ])) → V t` 就是 ℕ-索引分支树 —
>   与 [../BTBO.lagda.md](../BTBO.lagda.md) 的 `lim : (ℕ → Ord) → Ord` 同款骨架, 因此
>   **FGH 对 V 直接结构递归, 停机免费** (连 Acc 都不需要, 比 EBO §6 更强).
> - **无条件三歧性**: 每棵 V-树被有限项 t 索引, 比较两个 V-序数 = 比较索引语法 `cmpᵀ` —
>   范式 A 的 taboo 消失, 因为比较根本不触碰树本身 (树上的函数极限只承担停机职责).
> - **WF 反射 = 必须义务**: `V t` 的居民**就是** t 的基本列展开证书 — 不携带证书就没有这个序数.
>   原来外置的整体 WF(NF) 大墙, 在此分解为**逐算子的 V-提升引理** (`V-++`, `V-ψ0`, ...),
>   每条都是有限工程, 已实测提升到 ε₀ 段 (§4-5).
>
> 结构对照 (本质: 把 "构造即证明" 从基本列推到序数本身):
>
> | | 范式 A (Ord₀) | 范式 B (T + Acc) | 融合 (V : T → Set) |
> |---|---|---|---|
> | 停机 | 结构递归 ✓ | Acc, 需外部 WF 证明 | 结构递归 ✓ |
> | 三歧性 | taboo ✗ | cmpᵀ ✓ | cmpᵀ (在索引上) ✓ |
> | 大序数怎么来 | ψ-折叠塔 | 项 + 未证的 Acc | **V-提升引理逐段解锁** |
>
> 已知联系: `V t` 即 "t 属于可达部分" 的构造化, V-提升引理族 = Schütte/Buchholz 风格
> 分层 TI 证明的类型论形态; ccz181078 的 Coq Buchholz-WF 同构于把本文件的 V-提升做到 BO 段.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Notation.Fusion where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst)

open import OCF.Notation.EBO
```

## §1 融合类型 V 与结构递归 FGH

`fsn` 是 EBO 基本列的裸值包装 (证书部分由 V 自己接管):

```agda
fsn : T → ℕ → T
fsn [] n = []
fsn (x ∷ xs) n = trm (fsn↓ x xs n)
```

**融合类型**: 项 t 的"基本列展开树". 可数标准项的共尾度 ∈ {c0, c1, cω},
三个构造子恰好覆盖 (不可数共尾的证书设计见 §6 讨论):

```agda
data V : T → Set where
  v0 : V []
  v1 : ∀ {t} → cof t ≡ c1 → V (pred t)         → V t
  vω : ∀ {t} → cof t ≡ cω → (∀ n → V (fsn t n)) → V t
```

`vω` 的字段 `∀ n → V (fsn t n)` 就是 Brouwer 树的 `lim : (ℕ → _) → _` — 骨架保留.
FGH 对证书结构递归, **停机检查器直接放行, 无 Acc**:

```agda
FGHᵛ : ∀ {t} → V t → ℕ → ℕ
FGHᵛ v0        n = suc n
FGHᵛ (v1 _ c)  n = iter (FGHᵛ c) n n
FGHᵛ (vω _ cs) n = FGHᵛ (cs n) n
```

无条件三歧性: 比较证书 = 比较索引 (树本身不参与, taboo 无从谈起):

```agda
cmpⱽ : ∀ {s t} → V s → V t → Cmp
cmpⱽ {s} {t} _ _ = cmpᵀ s t
```

## §2 语法引理 (索引层的可判定世界)

```agda
cof-natT : ∀ k → cof (natT (suc k)) ≡ c1
cof-natT zero    = refl
cof-natT (suc k) = cof-natT k

pred-natT : ∀ k → pred (natT (suc k)) ≡ natT k
pred-natT zero    = refl
pred-natT (suc k) = cong (𝟏 ∷_) (pred-natT k)

cof-++ : ∀ a {y ys} → cof (a ++ (y ∷ ys)) ≡ cof (y ∷ ys)
cof-++ []           = refl
cof-++ (x ∷ [])     = refl
cof-++ (x ∷ z ∷ a″) = cof-++ (z ∷ a″)

pred-++ : ∀ a {y ys} → pred (a ++ (y ∷ ys)) ≡ a ++ pred (y ∷ ys)
pred-++ []           = refl
pred-++ (x ∷ [])     = refl
pred-++ (x ∷ z ∷ a″) = cong (x ∷_) (pred-++ (z ∷ a″))

fsn-++ : ∀ a {y ys} n → fsn (a ++ (y ∷ ys)) n ≡ a ++ fsn (y ∷ ys) n
fsn-++ []           n = refl
fsn-++ (x ∷ [])     n = refl
fsn-++ (x ∷ z ∷ a″) n = cong (x ∷_) (fsn-++ (z ∷ a″) n)
```

基本列计算的 J-对齐 (把 `fsn` 内部的 `cof`-分派换成手头的等式证据):

```agda
fsn₊-eq : ∀ u y ys n {k} (be : cof (y ∷ ys) ≡ k) →
          fsn (ψ u (y ∷ ys) ∷ []) n ≡ trm (fsn↓₊ u y ys k be n)
fsn₊-eq u y ys n refl = refl

rep-trm : ∀ u {b b′} (p : b′ <ᵀ b) n → trm (rep↓ u {b} {b′} p n) ≡ replicate n (ψ u b′)
rep-trm u p zero    = refl
rep-trm u p (suc n) = cong (ψ u _ ∷_) (rep-trm u p n)
```

## §3 V-提升引理: WF 反射的"逐算子义务"形态

原来的整体 WF(NF) 义务, 现在变成: 每引入一个序数算子, 就证一条 "该算子保 V" 的引理.
每条引理都是对证书的结构递归 + §2 语法引理 — **有限工程, 逐段解锁**.

加法 (列表拼接) 保 V:

```agda
V-++ : ∀ {a b} → V a → V b → V (a ++ b)
V-++ {a} va v0 = subst V (sym (++-identityʳ a)) va
V-++ {a} va (v1 {t = []} () c)
V-++ {a} va (v1 {t = y ∷ ys} e c) =
  v1 (trans (cof-++ a) e)
     (subst V (sym (pred-++ a)) (V-++ va c))
V-++ {a} va (vω {t = []} () cs)
V-++ {a} va (vω {t = y ∷ ys} e cs) =
  vω (trans (cof-++ a) e)
     (λ n → subst V (sym (fsn-++ a n)) (V-++ va (cs n)))

V-rep : ∀ {p} → V (p ∷ []) → ∀ n → V (replicate n p)
V-rep vp zero    = v0
V-rep vp (suc n) = V-++ vp (V-rep vp n)
```

**ψ₀-提升** (核心): 有证书的可数参数 b ↦ 有证书的 ψ₀(b) = ω^b.
对证书结构递归, 三个分支分别对应基本列规则 4 / 5(ω) / 底:

```agda
V-ψ0 : ∀ {b} → V b → V (ψ [] b ∷ [])
V-ψ0 v0 = v1 refl v0                             -- ψ₀(0) = 1
V-ψ0 (v1 {t = []} () c)
V-ψ0 (v1 {t = y ∷ ys} e c) =                          -- 规则 4: ψ₀(b'+1)[n] = ψ₀(b')·n
  vω (cong (cofA []) e)
     (λ n → subst V
        (sym (trans (fsn₊-eq [] y ys n e)
                    (rep-trm [] (pred-< (y ∷ ys) e) n)))
        (V-rep (V-ψ0 c) n))
V-ψ0 (vω {t = []} () cs)
V-ψ0 (vω {t = y ∷ ys} e cs) =                         -- 规则 5(ω): ψ₀(b)[n] = ψ₀(b[n])
  vω (cong (cofA []) e)
     (λ n → subst V (sym (fsn₊-eq [] y ys n e)) (V-ψ0 (cs n)))
```

## §4 证书实例: 从 n 到 ω↑↑k 到 ε₀

```agda
vNat : ∀ k → V (natT k)
vNat zero    = v0
vNat (suc k) = v1 (cof-natT k) (subst V (sym (pred-natT k)) (vNat k))

-- ω-塔: ω↑↑k, 证书 = V-ψ0 的迭代 (范式 A 的 "ψ-塔" 手法原样回归!)
ωTow : ℕ → T
ωTow zero    = natT 1
ωTow (suc k) = ψ [] (ωTow k) ∷ []

vTow : ∀ k → V (ωTow k)
vTow zero    = vNat 1
vTow (suc k) = V-ψ0 (vTow k)
```

**ε₀ = ψ₀(Ω)**: 参数不可数 (cof Ω = cΩ), 超出 V-ψ0 覆盖 — 但 EBO 规则 6 的 γ-链
在具体项 Ω 上**定义性计算**: ε₀[n] = ψ₀(γₙ), γₙ = ψ₀-塔. 于是直接构造:

```agda
-- γ-链的裸值: chain k = ψ₀(ψ₀(...ψ₀(1)))
chain : ℕ → T
chain zero    = 𝟏 ∷ []
chain (suc k) = ψ [] (chain k) ∷ []

vChain : ∀ k → V (chain k)
vChain zero    = vNat 1
vChain (suc k) = V-ψ0 (vChain k)

-- ε₀ 的基本列在具体 Ω 上按定义归约到 chain
chain-eq : ∀ k → trm (γ↓ (Ωt (natT 1)) [] refl k) ≡ chain k
chain-eq zero    = refl
chain-eq (suc k) = cong (λ z → ψ [] z ∷ []) (chain-eq k)

fsnεₒ-eq : ∀ n → fsn εₒ n ≡ ψ [] (chain n) ∷ []
fsnεₒ-eq n = cong (λ z → ψ [] z ∷ []) (chain-eq n)

vεₒ : V εₒ
vεₒ = vω refl (λ n → subst V (sym (fsnεₒ-eq n)) (V-ψ0 (vChain n)))
```

(注: `vεₒ` 的 `cof εₒ ≡ cω` 直接 `refl` — 规则 6 的共尾坍缩在具体项上由计算给出;
γ-链证书 `V-ψ0 (vChain n)` 正是范式 A 中 `ψⁿ`-塔的融合版.)

## §5 实测 demo

```agda
-- 三歧性: 证书间比较 = 索引语法比较, refl 直接算
_ : cmpⱽ (vTow 3) vεₒ ≡ lt          -- ω↑↑3 < ε₀
_ = refl

_ : cmpⱽ vεₒ (vTow 3) ≡ gt
_ = refl

-- FGH 结构递归 (无 Acc!) 的数值实测
_ : FGHᵛ (vNat 3) 2 ≡ 2048           -- f₃(2), 与 EBO §7.3 的 Acc 版一致
_ = refl

_ : FGHᵛ (vTow 1) 2 ≡ 8              -- f_ω(2) = f₂(2) = 8
_ = refl

_ : FGHᵛ (vTow 2) 1 ≡ 2              -- f_{ω^ω}(1)
_ = refl

_ : FGHᵛ vεₒ 1 ≡ 2                   -- f_{ε₀}(1): ε₀[1] = ψ₀(ω) = ω^ω, 再降至 f₁(1)=2
_ = refl

-- 一个真正的大数 (停机由结构保证, 无任何未证义务):
fusion-number : ℕ
fusion-number = FGHᵛ vεₒ 99          -- f_{ε₀}(99), 合法闭项, 纲领三条全满足
```

`fusion-number` 是本仓库第一个**同时满足**"无条件三歧序数 + 停机检查器直接放行 +
零未证义务"的超 Γ₀ 级… 不, ε₀ 级大数. 强度虽低于 BTBO, 但它验证的是**框架**:
沿 V-提升阶梯往上爬, 每一段都是同样形态的有限工程.

## §6 评估与路线

**兑现情况**: 融合成立. WF 反射从"外置大墙"变成"内置逐算子义务" — 这正是把
[FINDINGS.md](FINDINGS.md) §3 路线 W-a/W-c 结构化: 每条 V-提升 = 一段 TI 证明.

**接下来的阶梯** (每级 = 一条新 V-提升引理, 难度递增):

1. `V-ψℓ` at Ω-混合参数 (ψ₀(Ω·2), ψ₀(Ω²), ...): 需要 γ-链在半具体项上的计算引理族
   → 解锁 Γ₀ / BO 段.
2. 一般 `V-ψ` 提升 (对任意已证书化的层级): 对应 Buchholz 的主 TI 定理 → 解锁 BTBO ~ EBO 段.
   此时**范式 B 表记 + 融合证书全面超越范式 A 主线**.
3. 不可数共尾证书 (vΩ-构造子, 孩子 = γ-链值族 `∀ k → V (fsT b (γ k))`) → 系统化 1-2.
4. Mahlo 段 ([Mahlo.lagda.md](Mahlo.lagda.md) 的 T): V-提升 I/M-对角链所需的归纳强度
   即 Mahlo universe — 接入 Takahashi-MLQ 𝕄 ([../PastBTBO/Mahlo/Phase1.lagda.md](../PastBTBO/Mahlo/Phase1.lagda.md))
   作为提升引擎: **范式 A 的全部遗产 (ψ-塔手法 + 𝕄) 在融合框架中各就各位**.

**天花板的诚实陈述**: V-提升阶梯没有有限终点 (Gödel: Agda 证不出自身 PTO 的 TI),
但每一段都是可完成的有限工程 — 这与范式 A 的 taboo 墙 (定理级不可能) 有本质区别.
融合框架把"能走多远"从结构问题变回了纯粹的证明工程问题.

## 附: 本 spike 的工程要点

- `fsn₊-eq` 的 J-技巧: `fsn` 内部按 `cof b` 的**计算值**分派, 证明侧手持的是**命题等式**
  `e : cof b ≡ c1`; 对 `be = refl` 打点即让两者对齐, 一行搞定, 不需要任何 with-重放.
- 具体项上的定义性计算 (`vεₒ` 的 `refl` 共尾度 / `chain-eq`) 是低段证书的主要来源;
  抽象参数上的证书全部走 V-提升引理. 两者的分工线就是"具体 vs 一般 TI"的经典分界.
