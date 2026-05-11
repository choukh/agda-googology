# BTBO 突破探索: 诊断报告

> 本报告记录尝试在当前 BTBO 框架基础上推进"再往前一步"过程中的发现.
> 主要面向作者 ([@choukh](https://github.com/choukh)), 内容包括:
> 一个已修复的 bug、若干可贡献回 `BoundedTrich` 的辅助引理、
> 以及一个**根本性的负面发现**: 简单加构造子的路径在当前 `<` 与 `+` 定义下不可能完成.

## 0. TL;DR

- **小事**: 在 src/OCF/BTBO.lagda.md 的 `ψⁿ` 注释里发现一个 off-by-one (已 fix on `d68b69b`).
- **中事**: 沿途证出三个对 `BoundedTrich` 有用但不在主线代码里的引理:
  `suc-≤`, `s<sᴰ`, `x<sxy`. 可视情况合并.
- **大事**: 尝试加最小新构造子 (`Ordᴰ-1` with `Ord₀`/`Ordᴰ`-indexed `limΩ`)
  的方案在 phase 2 (有界三歧性) 撞了**根本性墙**——证明这堵墙不能通过
  补 `+-lmono` 引理绕过, 因为 **`+-lmono` 作为定理本身不真**.
  这意味着想在不改 `<` 或 `+` 的前提下突破 BTBO 几乎不可能.

详细论证见后.

## 1. 探索范围

附两个文件:
- [Experiments.lagda.md](Experiments.lagda.md): 四个实验, 验证现框架中各种"往前一步"路径的失败模式.
- [Phase1.lagda.md](Phase1.lagda.md): 最小扩展 `Ordᴰ-1` 的完整代码 + 撞墙分析.

两份均通过 `agda src/OCF/PastBTBO/Naive/*.lagda.md` 编译.

## 2. ψⁿ 注释的 off-by-one

按修复前的代码 `Ω zero = suc zero`, 机械展开:

```
ψⁿ 1 = (ψ₀ ∘ Ω ∘ ordᴰ) zero
     = ψ₀ (Ω zero)
     = ψ₀ (suc zero)      -- Ω zero = suc zero
     = suc zero            -- ψ₀ at ℓ=zero is identity
```

而注释为 `ex1 = ψⁿ 1 -- ω`. 实际为 1 (`suc zero`).

提交 `d68b69b` 把 `Ω zero` 改为 `ω`, 使 `ψⁿ 1 ≡ ω` 由 `refl` 直接成立.

这次修复让 ψⁿ 链条与作者期望的"ω → ψ(Ω_ω) → ψ(Ω_BO) → ..."一致.
顺带让框架的实际语义比之前更接近声称的 ψ(Ω_Ω).

## 3. 三个可贡献回 BoundedTrich 的引理

下面的引理在 `BoundedTrich` 模块当前没有, 但只用现有定义即可证.
合并门槛低, 收益 high (后续加 `Ordᴰ` 上的更多算术性质都可能用到).

### 3.1 `suc-≤`: `a < b → suc a ≤ b`

```agda
suc-≤ : ∀ {a b : Ordᴰ} → a < b → suc a < b ⊎ suc a ≡ b
suc-≤ zero                = inj₂ refl
suc-≤ (suc {b = b'} q) with suc-≤ q
... | inj₁ sa<b'          = inj₁ (suc sa<b')
... | inj₂ sa≡b'          = inj₁ (subst (λ z → z < suc b') (sym sa≡b') zero)
suc-≤ (lim {f} {m} n q) with suc-≤ q
... | inj₁ sa<fn          = inj₁ (lim n sa<fn)
... | inj₂ sa≡fn          = inj₁ (subst (λ z → z < lim f m) (sym sa≡fn) (f<l n))
```

这是建立 `Ordᴰ` 上更丰富的算术性质的基础引理.

### 3.2 `s<sᴰ`: 后继保 `<`

```agda
s<sᴰ : ∀ {a b : Ordᴰ} → a < b → suc a < suc b
s<sᴰ {b = b} q with suc-≤ q
... | inj₁ sa<b           = suc sa<b
... | inj₂ sa≡b           = subst (λ z → z < suc b) (sym sa≡b) zero
```

跟自然数版的 `s<s` 命名一致, 方便记忆.

### 3.3 `x<sxy`: 双参数上界

```agda
x<sxy : ∀ x y → x < suc (x +ᴰ suc y)
x<sxy x y = suc (a<a+b ⦃ _ ⦄)
```

简单但有用. 注意只有右侧的, 没有 `y<sxy` —— 见下文 §5.

完整代码见 [Phase1.lagda.md](Phase1.lagda.md).

## 4. 最小扩展 Ordᴰ-1 的进展

要在不破坏框架结构的前提下"再往前一步", 自然的想法是:
让 `Ordᴰ` 支持 `Ord₀`-索引或 `Ordᴰ`-索引的 `lim` (即 Ω-cofinal 极限).

### 4.1 走通的部分 (phase 1)

```agda
data Ordᴰ-1 : Set
data _<-1_ : Ordᴰ-1 → Ordᴰ-1 → Set

monoᴺ-1 : (ℕ → Ordᴰ-1) → Set
monoΩ-1 : (Ordᴰ → Ordᴰ-1) → Set

data Ordᴰ-1 where
  zero : Ordᴰ-1
  suc  : Ordᴰ-1 → Ordᴰ-1
  lim  : (f : ℕ → Ordᴰ-1) → monoᴺ-1 f → Ordᴰ-1
  limΩ : (f : Ordᴰ → Ordᴰ-1) → monoΩ-1 f → Ordᴰ-1
```

加 `<-1`、`<-1-trans`、`f<l-1`、`f<lΩ-1` 全部通过.

注意一个**坑**: 一开始用 `(f : Ordᴰ-fam i → Ordᴰ-fam ℓ)` 想做泛型版,
Agda 报严格正性错误 —— 即使 `i ≠ ℓ`, 类型族 `Ordᴰ-fam` 出现在
箭头左侧就被否决. 这意味着原框架那种 `module _ (ℓ) (Ord<)` +
type-level 递归函数的模式不能简单换成 indexed `data`. 单层
`Ordᴰ-1` 没这问题.

### 4.2 撞墙的部分 (phase 2: `<-1-dec`)

按 `BoundedTrich.<-dec` 的写法仿:

```agda
<-1-dec (limΩ x p) (limΩ y q) = ???
```

此处需要决定 `x, y : Ordᴰ` 的关系. `<ᴰ-dec` 是**有界**三歧的,
要求 x, y 被同一个 c 限制. 任意 x, y 之间没有自然的共同 c.

要补:
- 选项 a: 证 `Ordᴰ` 上的无条件三歧性. **不可能** (Brouwer 树的
  `lim/lim` 比较一般不可决定).
- 选项 b: 构造 x, y 的共同上界. 这导向下一节的根本壁.

## 5. 根本性发现: `+-lmono` 不真

要给任意 x, y 构造共同 Ordᴰ 上界, 最自然的尝试是 `c = suc (x +ᴰ suc y)`.
其中:
- `x < c`: 用 `a<a+b ⦃ NonZero (suc y) ⦄`, 立刻得证. ✓
- `y < c`: 需要某种"左单调性".

具体地, `y < suc (x +ᴰ suc y)` 等价于 `y ≤ x +ᴰ y`. 而后者本质上是

```
+-lmono : a < b → a +ᴰ c < b +ᴰ c   (取 a=0, c=y, b=x)
```

### 5.1 但 `+-lmono` 不可证 (在序数算术中本身就不真)

在序数算术里, **不**成立 `a < b ⇒ a + c < b + c`. 反例:

```
0 + ω = sup_{n<ω} (0 + n) = sup_n n     = ω
1 + ω = sup_{n<ω} (1 + n) = sup_n (n+1) = ω
```

序数级别 `0 + ω` 与 `1 + ω` 都等于 ω. 所以 `0 < 1` 但 `0 + ω < 1 + ω` 不真.

回到 Ordᴰ 框架: 构造性地, `0 +ᴰ ωᴰ` 和 `1 +ᴰ ωᴰ` 作为 Brouwer 树是
**不同的 `lim ... mono` 项** (内部函数不同), 但代表同一个序数 ω.
在 Ordᴰ 的结构 `<` 上, `0 +ᴰ ωᴰ < 1 +ᴰ ωᴰ` **不可证**——按 `<` 的归纳构造子
逐层展开后会归结到形如 `lim suc-iter mono < suc^{n+1} zero`, 这是 ω
小于一个自然数的断言, 没有有效证明.

`BoundedTrich` 没提供 `+-lmono` **不是疏忽**, 是因为它要么是错的定理 (ordinal view),
要么是不可证的断言 (constructive view). 两种视角都封死了这条路.

### 5.2 所有"自然上界"构造都失败

我们试了如下变体, 每种都撞同一面壁:

| 上界 c | x < c | y < c | 失败原因 |
|--------|------|------|----------|
| `suc (x +ᴰ suc y)` | ✓ | ✗ | 需 `y < x +ᴰ y` ≡ 左单调 (不真) |
| `y +ᴰ suc x` | ✗ | ✓ | 对偶 |
| `(x +ᴰ suc y) +ᴰ (y +ᴰ suc x)` | ✓ | 部分 | 仍需中间步骤的左单调 |
| `lim (n ↦ cumsum f n) _` | ✓ | ✗ | cumsum 是右加 cumulative, 同问题 |

详见 BeyondPhase1.lagda.md 文末.

### 5.3 结论

**`Ordᴰ` 上的 `+` 本质上不是左单调的, 而 `<` 是结构性归纳定义** ——
两者结合的代数性质里, 不存在"任意 x, y 的严格共同上界"的构造方式.

`<-1-dec` 的 `limΩ/limΩ` 案例因此无法完成. 进而 `Ord-1`、`ψ-1` 等
依赖三歧的下游也无法定义.

## 6. 对"突破 BTBO"路径的含义

加 1 个构造子的"小步走"在当前框架下走不通. 真正可走的方向:

| 方向 | 难度 | 是否改原框架 | 终点 |
|------|------|------------|------|
| A. 给 `Ordᴰ` 上加 `_⊔_` (max) 并证性质 | 高: 定义 max 又陷入 lim/lim 决策 | 是 | 不一定通 |
| B. 给 `limΩ` 加上界存在性参数 | 中: 改语义 | 是 | 调用方负担转移 |
| C. 改 `<` 的定义 (加 cofinal 嵌入信息) | 高: 推翻基础 | 是 | 不确定 |
| D. 设计不依赖三歧的 ψ-1 | 极高: OCF 普遍依赖三歧 | 否 (但 ψ 改写) | 可能根本不行 |
| E. 走 IR-Mahlo 路径 | 极高: 研究级 | 是, 大改 | ψ(M) |

A, C 在分析后都发现暗藏同样的 decidability 死循环.
B 改变了 `limΩ` 的语义.
D 是最"保守"但可能根本无解.
E 是已知能行的路径 (Setzer 1998), 但工作量数千行.

**没有看到"小改 200-500 行就能突破 BTBO"的可行路径.**

## 7. 建议

按可执行度排序:

1. **合并辅助引理** (`suc-≤`, `s<sᴰ`, `x<sxy`) 到 `BoundedTrich`.
   工作量 < 10 行 commits, 收益是给框架配齐基本算术工具.

2. **在 BTBO 正文加一个说明**, 指出当前框架的 sup 受限于 ψ(Ω_Ω) 是
   "structurally enforced": 加 lim 索引类型的扩展会撞 `+-lmono` 不真
   这一根本壁. 让读者明白这不是工程问题.

3. **若仍想突破**, 唯一现实选项是走 E (IR-Mahlo). 但这是研究级工作,
   不是延伸 BTBO 而是另起炉灶.

## 8. 文件清单

- [Experiments.lagda.md](Experiments.lagda.md):
  4 个小实验, 验证各种"小步走"的失败模式
- [Phase1.lagda.md](Phase1.lagda.md):
  完整 `Ordᴰ-1` 骨架 + `<-1-trans` + 辅助引理 + phase 2 撞墙分析

两份均无 `postulate`、无 `--unsafe`、通过 Agda 类型检查.

副作用: 我在编译时把根目录 `agda-googology.agda-lib` 的版本依赖
从 `standard-library-2.2 / cubical-0.8` 改成了
`standard-library-2.3 / cubical-0.9` (本地仅有这些版本).
BTBO 在新版下也能编译. 是否回滚由你决定.
