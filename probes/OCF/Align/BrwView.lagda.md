# 中间层的布劳威尔树 View

> 入口. 第二次审查的 P9 ([RouteReview2](../../Survey/RouteReview2.md) §4.1). 作者 2026-11-05 对纲领 1 的解释: 中间层若不直接用布劳威尔树, 就要有布劳威尔树的 View (最终定义的验收标准); 可以比布劳威尔树多, 不能少. 这里把 View 写成**一个**记录, 在第 0 层差树、高度树、第 1 层差树上实例化. 不读记号, 不用 `Funext`. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.
>
> **判决: PARTIAL.** 第 0 层与高度树: 无条件定理. 第 1 层: 条件定理, `ni` 段与 `nκ` 段在**同一个**条件 `HW` (世界稳定) 下都成立, 条件可满足 ($\Omega_1$), 条件用到的那条引理 (前缀抬升) 不是无条件的 (编译过的反例). 记录要求 "$\mathbb N$-极限值上严格递增" 推出 LPO (编译过), 所以步进取目标树自己合法性里的那一条 (第一位置, 不严格). 未做: 条件 `HW` 是否必要; 折叠的输出是否满足 `HW`; 部分的良基; 第 2 层以上.

## 1 记录 ([BrwViewDef](BrwViewDef.lagda.md))

```text
record Sig : Set₁ where          -- 目标布劳威尔树
  Ix  : Set                      -- 下标 (第 1 层: 带合法性的世界)
  B   : Ix → Set                 -- 值
  _≼_ : ∀ {i j} → B i → B j → Set
  Stp : ∀ {i} → B i → B i → Set  -- ℕ-极限相邻项 (目标树合法性里的那条)
  Kd  : Ix → Set                 -- Ω-极限的种类
  Cd  : ∀ {i} → Kd i → Set       -- 坐标
  LgC : ∀ {i} {k : Kd i} → Cd k → Set   -- 坐标合法
  tg  : ∀ {i} {k : Kd i} → Cd k → Ix    -- 分支所在的下标
  bz bs bl bΩ                    -- 四种构造子

data View (i : Ix) (v : B i) : Set where   -- 参数: Sig, 载体 X : Ix → Set, val, 合法性 Lgl
  vz : v ≈ bz → View i v
  vs : (y : X i) → Lgl y → v ≈ bs (val y) → View i v
  vl : (f : ℕ → X i) → (∀ n → Lgl (f n)) → (∀ n → Stp (val (f n)) (val (f (suc n)))) → v ≈ bl (λ n → val (f n)) → View i v
  vΩ : (k : Kd i) (g : (c : Cd k) → X (tg c)) → (∀ c → LgC c → Lgl (g c)) → v ≈ bΩ k (λ c → val (g c)) → View i v

record BrwView : Set where
  view : ∀ {i} (x : X i) → Lgl x → View i (val x)
```

$\approx$ 是互相 $\preccurlyeq$. `View` 按值加下标, 两个对象值字面相同时一个 View 两处都能用. 比作者的四条多出的件, 都由实例逼出: **种类 `Kd`** (第 1 层有两种 $\Omega$-极限, `bi` 按坐标、`bκ` 按世界, 两种的坐标都是合法的第 0 层布劳威尔树), **下标 `Ix` 与 `tg`** (第 1 层的分支在更大的世界里), **`LgC`** (高度树的分支取遍不合法坐标).

## 2 实例与定理

| 定理 | 文件 | 内容 | 档 |
|---|---|---|---|
| `view₀` | BrwViewZero | 第 0 层差树 `D azero W`, 值 `sum azero`, 目标 `A`, `≤`, 步进 `_⊲_` | **定理, 无条件** |
| `viewᴴ` | BrwViewHt | 高度树 `H`, View 是恒等, 值 `≤ᴴ` (取遍一切坐标) | 定理, 无条件 |
| `view₁` | BrwViewKappa | 第 1 层差树 `D one W`, 值 `toB`, 目标 `B₁`, `≼`, 步进 `_⊲⟨ yes ⟩_`; 合法性 `HW` | **条件定理** (`HW`) |
| `WithKappa.view₁` | BrwViewOne | 同上, `nκ` 段作参数 `KSeg` | 条件定理 (`HW` + 参数) |
| `JI` | BrwViewOne | 部分积分的差树 `J` 的值就是 `LayerTrOne.I` 积出的值 | 定理 |
| `hw→ws`, `lift` | BrwViewOne | `HW` ⇒ 整棵树世界稳定 ⇒ 前缀抬升值不变 | 条件定理 |
| `HW-Ωx` | BrwViewOne | $\Omega_1$ 的差树满足 `HW` | 定理 (前提可满足) |
| `CK` | BrwViewKappa | 分支世界稳定 ⇒ `K` (逐段在自己的世界求值) 与 `Cut` (抬到顶再求值) 值相同 | 条件定理 |
| **`strict→LPO`**, `strict-D`, `strict-A` | BrwViewNeg | 第 0 层 View 若要 $\mathbb N$-极限值上严格递增, 推出 LPO; 对差树和 `A` 本身都如此 | 否定, 定理 |
| **`lift-fails`**, `not-HW` | BrwViewLift | 一棵没有 `nκ` 的差树, 抬升后值降为 0; 它不满足 `HW` | 否定, 定理 |

**第 0 层 (无条件).** 读法对差树的结构递归, 不经 `toA`: `vw x vx q y` 走过前缀 $x$ 再走 $y$; `n0` 用前缀的读法, `n1` 是后继 (部分是 $x$), `y₁ ⨾ y₂` 把前缀推进到 $x ⨾ y_1$, `nl d` 是 $\mathbb N$-极限 (部分是部分和 $x ⨾ (d_0⨾\dots⨾d_{n-1})$, 步进 `sum-fst`), `nw` 接路径. 值一致除 `nl` 一条 $\equiv$ (`ps-pt`) 外都是字面的.

**第 1 层 (条件).** 同样的 `vw`, `n0`/`n1`/`⨾`/`nl`/`nw` 逐字同形 (步进 `S-fst`). `ni R u` 是 `ki` 种 $\Omega$-极限: 坐标 $(W',p,l',y)$ 上的分支是 `nw p x ⨾ J u (dif y) self n0` (前缀抬到 $W'$ 接上沿 `dif y` 的部分积分, 即 `LayerTrOne.I` 的差树版). `nκ` 是 `kκ` 种: 层 $c$ 上的分支是 `nw p x ⨾ (Cut u c p q lc self ⨾ u c)`. **不需要 `Cv`**: `LayerTrRound` 的 `Cv` 是往返 `toB → difT → toB` 要的, 这里的读法直接用 `toB` 自己的规范坐标 `dif y`, 不读回.

**条件 `HW` 是什么.** `S` 求值时, 差树的抬升 `nw p x` 在大世界里**重新求值** ($x$ 里的 `ni` 只取更大世界上的分支); 布劳威尔树的抬升 `bw` 是透明的. View 的部分在大世界里 (分支的类型逼的), 前缀要抬上去, 两者之差就要 `WSq`:

```text
WSq y = ∀ {W W′} (q : W₀ ⊲ W) (p : W ⊲ W′) (l : Lg W) (l′ : Lg W′) {b : B₁ W} {b′ : B₁ W′} →
        b ≈ b′ → S q l b y ≈ S (⊲-tr q p) l′ b′ y
```

`HW`: 每个 `ni`, `nκ` 节点 `WSq`, 分支遗传地 `HW`. `hw→ws` 把节点上的 `WSq` 合成整棵树的 (对 `⨾`, `nl`, `nw` 是一步的结构定理, 用 `⊲-assoc`). `HW` 是 View 的合法性谓词, 部分都满足它 (`HW-J`, `HW-ps`, `HW-Cut`).

## 3 `nκ` 段: 参数的确切类型与它要的引理

参数 ([BrwViewOne](BrwViewOne.lagda.md) §5):

```text
KSeg = ∀ {W₀ W} (l : Lg W) (x : D one W) → HW x → (q : W₀ ⊲ W) (zz : ⊤) (u : ∀ {c} → W₀ ⊲ c → Lg c → D one c) →
       HW (nκ zz u) → V₁ (W , l) (S q l (toB l x) (nκ zz u))
```

[BrwViewKappa](BrwViewKappa.lagda.md) 给出 `κseg : KSeg` (编译过). 它要的引理 (编译过, 前提是分支世界稳定):

```text
CK : ∀ {W₀} (u : ∀ {c} → W₀ ⊲ c → Lg c → D one c) → (∀ {c} p l → WSq (u {c} p l)) →
     ∀ b {a} (p : a ⊲ b) (aW : W₀ ⊲ a) (lb : Lg b) {Wt} (bW : b ⊲ Wt) (lt : Lg Wt) {x₀ : B₁ a} {c₀ : B₁ Wt} →
     x₀ ≈ c₀ → K u b p aW lb x₀ ≈ S C.self lt c₀ (Cut u b p aW lb bW)
```

加上前缀的 `lift` (同 `ni` 段). **`nκ` 节点自己的 `WSq` 不用** (只在它出现在别的 $\Omega$-极限的前缀里时, 经 `hw→ws` 用到). 所以 `nκ` 段与 `ni` 段要的是同一件事: **第 1 层差树在更大世界里求值, 值不变.** 第 1 层 View 的全部条件就是这一条 (逐节点).

**与 KVal 正在做的共享单调引理是否重合 (判断, 未编译).** 不重合, 是同一族的另一个实例.

- KVal (`KValSound.snd`) 与 HtCross 的 `MonoStep` 讲的是**折叠的输出**对 (状态, 世界, 输入) 单调, 关系 `_⊑[_]_` 比两棵树. 这里的 `WSq` 讲的是**同一棵树作为布劳威尔树的值** (`toB`, 不折叠) 在抬升下不变. 对象不同 (`toB` 对折叠输出), 方向不同 (一棵树的不变性对两棵树的单调).
- 联系: KVal 的 `ni⊑` 用于自比 (`Rfᵏ lo (ni u)`) 时说分支跨一切世界、坐标按值对齐可比. 如果 `⊑[ lo ]` 对 `toB` 也可靠 (跨世界 $x\sqsubseteq x'\Rightarrow$ `toB x ≼ toB x′`, KVal 没有这条, 只有对折叠第 0 层输出的), 那么 `Rfᵏ lo (ni u)` 推出 `ni` 节点的 `WSq` (左边每支在右边取同一坐标、世界 $W'$ 本身, 不要公共上界; 同 `WSq-Ω` 的证明形状). 对 `nκ` 节点, `KMono` (分支对层的值单调) 不够推出节点的 `WSq`: 从更大的世界 $W'$ 起步, 走过的区间 $[W',c]$ 比 $[W,c]$ 短, 还要一个共尾论证 (找 $c'$ 使 $[W',c']$ 不短于 $[W,c]$). 但上面说了, View 的 `nκ` 段不需要节点自己的 `WSq`.
- 所以 HtCross 的第一个障碍里 "回灌的世界变大, 还要对世界单调 (`CvLayer` §3)" 那一半, 在值层 (`toB`) 上的形状就是 `WSq`; 折叠层的 `MonoStep` 是另一半 (对状态与输入单调). R2 那条汇聚引理若做成, 应同时给出两半 (判断).

## 4 否定的范围

- `strict→LPO`: 否定的是 "第 0 层 View 的 $\mathbb N$-极限值上严格递增" 这一个字段形状 (任意载体与值映射, 只要能编码 0/1 序列的部分和; `A` 本身就能). 作者解释里的 "严格递增" 按目标树自己的合法性读 (第一位置 `⊲`, 不严格). `BTBO` 与 `OCF.Free.Level` 的极限也不要严格.
- `lift-fails`: 否定的是 "前缀抬升值不变" 无条件成立. 反例的分支读世界的**路径** (`self` 对 `suc _`). 不否定第 1 层 View 无条件存在: 部分的世界可以另选 (`ki` 种坐标含世界 $W$ 自己, 那一支前缀不用抬), $x ⨾ y$ 的值一致也许在更弱的条件下成立. 未判定, 记作未走通.

## 5 有限测试

没有. 全部是定理.

## 6 翻译账

| 模块 | 记号读来的字段或形状 | 树逼出的 | 类 |
|---|---|---|---|
| `BrwViewDef` | 无. 四种读法与值一致来自作者对纲领 1 的解释 | `Kd` (第 1 层两种 $\Omega$-极限), `Ix`/`tg` (分支在更大世界), `LgC` (`H` 的分支含不合法坐标), `Stp` 取目标的第一位置 (`strict→LPO`) | 提供信息 |
| `BrwViewZero` | 无 | 读法对差树结构递归; 步进是 `sum-fst` | 提供信息 |
| `BrwViewHt` | 无 | 恒等 | 提供信息 |
| `BrwViewOne` | 无. `J` 照 `LayerTrOne.I` 的坐标记法 | 条件 `HW` 由 `nw` 在 `S` 里重新求值逼出 (`lift-fails`) | 提供信息 |
| `BrwViewKappa` | 无. 部分照 `SumOneTree.Cut`, 值照 `LayerTrOne.K` | `CK` 只要分支 `WSq` | 提供信息 |
| `BrwViewNeg`, `BrwViewLift` | 无 | 否定定理划出不能有的字段 (严格步进) 与不能去的条件 (抬升) | 提供信息 |

**按 `AGENTS.md` 归类: 提供信息.** 没有新构造子, 没有改树或折叠, 没有 `Lab`. 新增的前提 `HW` 是对每个节点的一步陈述 (`ni`, `nκ` 各一条 `WSq`), 合成是对结构参数的一步定理 (`hw→ws`); 新用到的字段: `nw` 的路径 (抬升), `ni` 的分支在更大世界上的值, `nκ` 的 `K`/`Cut`. 没有序数值验收 (这里不爬站).

## 7 审计

`importclosure.py --only OCF.Free.Level --only OCF.BTBO --only OCF.Align.CumReadCF --only OCF.Align.TLRuleSpec --only OCF.Align.TLRuleSum --only OCF.Align.TLRule --only OCF.Align.SumOne --only OCF.Align.BrwMid --only OCF.Align.LayerTr --only OCF.Align.NoCumLit --only OCF.Align.HtFeed --only OCF.Align.BrwView OCF.Align.BrwView`: 闭包 32 个模块 (本地 22, 库 10), 禁用表 0, `--only` 之外 0, OK.

`depslice.py` (到达块 / 记号模块块 / 别处记号词): `BrwViewZero:view₀` 42/0/0, `BrwViewHt:viewᴴ` 19/0/0, `BrwViewOne:view₁` (`κseg` 作参数) 91/0/0, `BrwViewKappa:κseg` 101/0/0, `BrwViewOne:HW-Ωx` 90/0/0, `BrwViewNeg:strict-D` 44/0/0, `BrwViewLift:not-HW` 62/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用, 不说明没有受记号启发.

代码行 (agda 块里非空非注释): `BrwViewDef` 33, `BrwViewZero` 59, `BrwViewNeg` 65, `BrwViewHt` 33, `BrwViewOne` 199, `BrwViewKappa` 56, `BrwViewLift` 46, 入口 9; 合计 500.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwView where

open import OCF.Align.BrwViewDef using (Sig; View; vz; vs; vl; vΩ; BrwView) public
open import OCF.Align.BrwViewZero using (Sig₀; view₀; vw) public
open import OCF.Align.BrwViewHt using (Sigᴴ; viewᴴ) public
open import OCF.Align.BrwViewOne using (Sig₁; K1; ki; kκ; X₁; val₁; Lgl₁; V₁; WSq; HW; hw→ws; lift; J; JI; KSeg; module WithKappa; Ωx; HW-Ωx) public
open import OCF.Align.BrwViewKappa using (CK; κseg; view₁) public
open import OCF.Align.BrwViewNeg using (LPO; strict→LPO; strict-D; strict-A) public
open import OCF.Align.BrwViewLift using (xᵖ; lift-fails; not-HW) public
```
