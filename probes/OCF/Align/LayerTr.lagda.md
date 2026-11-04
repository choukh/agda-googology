# 差树按层互译

> 入口. **判决: PARTIAL.** 第 0 层到第 1 层这一步: 两个方向的翻译都定义了, 输出都合法, 合法性由形状给 (编译过). 值上互逆**不**成立: `ni` 处有编译过的反例 (`no-round`); 加上一个条件 (`Cv`: 分支对规范坐标不变) 就成立 (`round-Cv`, 条件定理), 而且条件去不掉 (`xᶜ-not-Cv`). 世界分支 `bκ` 读不回差 (没有编译的否定, 判断). 第 2 层及以上没有做. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示; 不读记号.

## 1 定义

**树** ([LayerTrBase](LayerTrBase.lagda.md)). 第 1 层的布劳威尔树 `B₁ W`:

    bz | bs b | bl f | bi f | bκ g | bw p b
    bi : (∀ {W′} → W ⊲ W′ → Lg W′ → (y : A) → Lg y → B₁ W′) → B₁ W
    bκ : (∀ {c} → W ⊲ c → Lg c → B₁ c) → B₁ W

`bi` 是 $\Omega_1$-分支极限, 分支对**合法的第 0 层布劳威尔树** $y$ 给出 (第 0 层就是 `A` 带 `Lg`, 即 [BrwMidZero](BrwMidZero.lagda.md) 的 `L₀`). `bκ` 按世界分支. 分支只在更大的世界上有, 同差树: 这是壁垒要的字面公共上界, 树里没有比较.

**合法性** `LgB fl` (判断后选定, 全部是字面的第一位置 `⊲⟨ fl ⟩`, 不提值):

| 节点 | 条件 |
|---|---|
| `bl f` | $f\,n\lhd f(n+1)$ |
| `bi f` | 后继坐标: $f\,y\lhd f(y+1)$ |
| `bκ g` | 后继世界: $g\,c\lhd g(c+1)$ |
| 全部 | 遗传到一切分支 |

第一位置进 `bi` 只经世界自身上坐标 $0$ 那一支, 进 `bκ` 只经世界自身那一支; `bw` 两边透明. **不要求**分支在极限坐标、极限世界上连续, 也不要求分支对值单调. 理由: 差树的 `ni`, `nκ` 译过来只自动满足后继步进 (下面 `Lg-S`); 连续与对值单调是值层的性质, 差树里没有.

**值** `_≼_`: 同 `Value` 的 $\preccurlyeq$ (`CrossTree` 四条, 每种分支极限各两条, 抬升透明), 跨世界. `bi` 的值是一切更大世界、一切合法坐标上分支的上确界. 高层只有这一个关系; 差树一侧没有独立的值, 差树的值就定义成 `toB` 的值.

**翻译** ([LayerTrOne](LayerTrOne.lagda.md)):

| | 差树 → 树 (`toB`, 经 `S b x` $=b+x$) | 树 → 差树 (`dif₁`, 沿一条第一位置路径) |
|---|---|---|
| `n0`, `n1`, `⨾`, `nl`, `nw` | 同第 0 层 (`toA`) | 同第 0 层 (`dif`), 多 `bw` |
| `ni R u` / `bi f` | 坐标 $y$ 上: $b+\sum_{w<\mathrm{dif}\,y}u(w)$, 沿 `BrwMidZero.dif y` 积分 (`I`) | 坐标 $z$ 上放 $f(\mathrm{toA}\,z)\to f(\mathrm{toA}\,z+1)$ 那一段, 路径是合法性里的后继步进 |
| `nκ _ u` / `bκ g` | 世界 $c$ 上: $b+\sum_{W\le c'\le c}u(c')$, 沿路径 $W\lhd c$ (`K`) | **没有** |

按层归纳的结构: 第 1 层的翻译用第 0 层的翻译做坐标 (`dif` 喂分支, `toA` 读回), 这就是归纳假设用的地方. 第 0 层的值互译 (`round₁`, `round₂`) 在这一步里够用到坐标的值, 不够用到分支 (见 §3).

## 2 定理表

| 定理 | 文件 | 内容 | 档 |
|---|---|---|---|
| `B₁`, `LgB`, `_≼_`, `≼-refl`, `≼-trans` | LayerTrBase | 第 1 层布劳威尔树, 合法性, 值前序 | 定义, 定理 |
| `toB`, `S-fst`, `Lg-S`, `Lg-toB` | LayerTrOne | 一切第 1 层差树译成合法树, 无前提 (`LgB yes`); 没有 `nκ` 的译成 `LgB no` | 定义, 定理 |
| `dif₁`, `difT` | LayerTrOne | `no` 的第一位置路径读回差树 | 定义 |
| `Ω≈` | LayerTrOmega | $\Omega_1$ 的差树译过来与标准树 `Ωᴮ` (分支即坐标) 互相 $\preccurlyeq$ | 定理, 验收 |
| `Ω-round`, `Ω-dif` | LayerTrOmega | $\Omega_1$: 差→树→差→树字面不变 (`refl`); 读回的差树字面不同 | 定理 |
| **`no-round`** | LayerTrNeg | 反例: $t=\mathrm{toB}\,x\succcurlyeq1$, $t'=\mathrm{toB}(\mathrm{difT}\,x)$ 值为 $0$, `¬ (t ≼ t′)` | 定理 (否定) |
| `S-mono` | LayerTrRound | $b\preccurlyeq b'\Rightarrow b+x\preccurlyeq b'+x$, 一切差树 | 定理 |
| **`round-Cv`** | LayerTrRound | 没有 `nκ` 且 `Cv x`: `toB (difT x) ≈ toB x` | 条件定理 |
| `Ω-Cv`, `Ω-round≈` | LayerTrRound | 前提可满足: $\Omega_1$ 的差树满足 `Cv` | 定理 |
| `xᶜ-not-Cv` | LayerTrRound | 反例不满足 `Cv` | 定理 |
| `Lg-mid`, `mid-κ` | LayerTrFold | 折叠 $\psi_0(\Omega_\Omega)$ 一步在第 1 层的输出译成合法树; 它含 `nκ`, `difT` 用不上 | 定理 |

## 3 哪个构造子翻不过去, 缺什么

**`ni` / `bi` (按低层树分支): 两个方向都能写, 值上不互逆.** 差树的分支 $u$ 拿到的是第 0 层的**差树坐标** $w$, 可以读 $w$ 的字面形状; 树的分支拿到的是**布劳威尔树坐标** $y$. 去程只在 `dif y` 的各个位置调用 $u$; 回程在坐标 $z$ 上读 $f(\mathrm{toA}\,z)$ 到 $f(\mathrm{toA}\,z+1)$, 那一段只在规范坐标 `cw z = n0 ⨾ nw self (dif (toA z))` 上调用 $u$. 所以往返把 $u(w)$ 换成了 $u(\mathrm{cw}\,w)$.

- 反例 (`no-round`): $u(w)=1$ 当 $w$ 形如 `((_ ⨾ _) ⨾ n0) ⨾ _`, 否则 $0$. 坐标 $\omega$ 那一支走到这种位置, 所以 $t\succcurlyeq1$; 规范坐标都是 `n0 ⨾ _`, 所以 $t'$ 的每一格都是 $0$.
- 缺的条件 (`Cv`): 对一切 $w$ 与底 $b$, $b+u(\mathrm{cw}\,w)\approx b+u(w)$, 遗传. 有了它往返保值 (`round-Cv`). $\Omega_1$ 这种分支不读坐标的树满足它, 而且往返字面不变 (`Ω-round`).
- `Cv` 不是第 0 层归纳假设的推论: `round₁` 给的是坐标的值相等 ($\mathrm{toA}(\mathrm{cw}\,w)\approx\mathrm{toA}\,w$), 但 $u$ 不尊重坐标的值. 这与 `Value.ψ⁰-not-cong` 同类 (判断): 折叠的分支读坐标的字面结构 (`Int`, `Run` 按 `⨾`, `nl` 分情况), 所以折叠的输出一般不满足 `Cv` (没有证明, 也没有反例).

**`nκ` / `bκ` (按世界分支): 去程能写, 回程没有.** 回程要在每个世界 $c$ 上放一段 $u'(c)$ (世界 $c$ 上的差树). 后继世界可以: $u'(c+1)$ 是 `bw (g c)` 到 $g(c+1)$ 那一段, 两边都在世界 $c+1$, 路径是合法性里的后继步进. 极限世界 $c=\lim f$ 不行: 那一段要从 "前面各支的极限" 读到 $g(c)$, 需要一条从 $\lim_m g(f\,m)$ 到 $g(c)$ 的字面第一位置路径, 或者 $g$ 在 $c$ 处连续 (值); 合法性只有后继步进. 去程的输出满足的也只是 "$g(c)$ 有字面的第一位置 $K(c)$", 而 $K(c)$ 是用原来的 $u$ 算的, 回程的部分和是用 $u'$ 算的, 两者只值相等. 所以标记 `no` 的路径没有 `inκ`, `dif₁` 不处理 `bκ`. 这是判断, 没有编译的否定定理; 状态写作未走通.

**`bi` 的另一个方向 (树 → 差树 → 树, 对一切合法树).** 没有做. 判断: 要分支在极限坐标上连续 (值) 并且对坐标的值单调, 两者都不在 `LgB` 里. 去程的输出一般也不满足后者 (判断, 没有单独编译).

## 4 判断

- "差树是布劳威尔树的一种写法": 在第 1 层, **去程**有定理依据 (`Lg-toB`: 一切差树都写出合法的布劳威尔树, 合法性由形状给, 不另证). **回程**只对一部分差树成立: 没有 `nκ`, 且分支对规范坐标不变. 不能说两者是同一类对象的两种写法.
- 往返失败不在归纳假设不够强: 第 0 层的互译到值已经最好 (`round₁`, `round₂`), 第 0 层字面不互逆 (`dif-not-id`) 也无法改进 (`sum-dif-not-≈ᴬ`). 失败在第 1 层的分支函数: 它的定义域是差树坐标, 比布劳威尔树坐标细.
- 第 2 层以上: 没有做. 判断: 同样的反例搬上去 (第 1 层坐标里放 `ni`), 而且坐标的翻译自己就要 `Cv` (第 1 层坐标的往返只在 `Cv` 下保值), 条件会逐层叠加. `bκ` 的回程问题在每一层都在.

## 5 有限测试

没有单独的有限测试. `Ω-round`, `Ω-dif`, `big` (反例里 $t\succcurlyeq1$) 是对具体项的 `refl` 级计算, 由检查器归约, 算作定理. 比较器只有 `≼`; `Zv` (没有后继) 只用来证 $t'$ 值为 $0$.

## 6 翻译账

| 模块 | 记号读来的字段或形状 | 类 |
|---|---|---|
| `LayerTrBase` | 无. `B₁` 的形状照差树 `D₊` (世界, `nκ`), `≼` 照 `Value` / `CrossTree` | 提供信息 |
| `LayerTrOne` | 无. 积分的坐标记法照 `SumOneTree.Int`, `K` 照 `Cut` | 提供信息 |
| `LayerTrNeg`, `LayerTrOmega`, `LayerTrRound` | 无 | 提供信息 |
| `LayerTrFold` | 用 `SumOneClosed` 的闭项 (那里 $S=\cdot\omega$ 抄自旧折叠) | 提供信息, 形状受旧树影响 |

## 审计

见报告. `importclosure.py`: 七个模块. `depslice.py`: `LayerTrRound:round-Cv`, `LayerTrNeg:no-round`, `LayerTrFold:Lg-mid`, 正对照 `Om1HnAccept:label-term₀`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LayerTr where

open import OCF.Align.LayerTrBase using (B₁; LgB; _⊲⟨_⟩_; _≼_; _≈_; ≼-refl; ≼-trans; Ωᴮ; emb) public
open import OCF.Align.LayerTrOne using (S; toB; S-fst; S-fstᵃ; Lg-S; Lg-toB; dif₁; difT; Ok; ok-yes) public
open import OCF.Align.LayerTrOmega using (Ω≈; Ω-round; Ω-dif) public
open import OCF.Align.LayerTrNeg using (no-round) public
open import OCF.Align.LayerTrRound using (S-mono; Cv; round-Cv; Ω-Cv; Ω-round≈; xᶜ-not-Cv) public
open import OCF.Align.LayerTrFold using (Lg-mid; mid-κ) public
```
