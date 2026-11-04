# 高层的布劳威尔树: 正规节点

> 入口. **判决: PARTIAL.** 数类第 1 层写成了布劳威尔树, $\Omega$-极限的分支按坐标的结构递归给出 (正规), 合法性无前提 (`Lg-br`), 第 1 层的差树都读成这种树 (`out-legal`). 编译过的否定 `incr-blind` 说明: 只合法 (沿前缀单调) 的布劳威尔节点不被它的增量决定, 所以数据里要存增量, 布劳威尔树是它的读法. 折叠没有改写成直接输出第 1 层的布劳威尔树, $\psi_0(\Omega_\Omega)$ 要一切层, 只做了第 1 层; 序数值验收没有做. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不读记号.

## 1 第 1 层 ([BrwHighOne](BrwHighOne.lagda.md))

| 定理 | 内容 | 档 |
|---|---|---|
| `B₁`, `_⊞₁_`, `⊞₁-fst`, `⊞₁-⊲`, `Lg-⊞₁` | 第 1 层的布劳威尔树与加法; $a\lhd_1 a\boxplus_1 b$ 无前提 | 定理 |
| `Ig`, `Ig-pre` | 正规分支 $g(0)=0$, $g(z+1)=g(z)\boxplus\Delta(z)$, $g(\lim)$ 是部分和; 沿坐标前缀单调, **无前提** | 定理 |
| `Lg-node` | 正规节点合法, 前提只在增量上 | 定理 |
| `N₁`, `br`, `Lg-br` | 正规的树与它的读法; **读出来一律合法, 无前提** | 定理 |
| `nrm`, `out-legal` | 第 1 层的差树 (`D (asuc azero) W`, 即 `SumOne`, `BrwMid` 第 1 层的状态与输出) 读成正规的树, 合法, 无前提 | 定理 |
| `incr-blind` | 分支 `gL` 与正规分支 `Ig (const 0)`: 起点相同, 每个后继增量相同, 两个节点都 `Lg₁`; 在坐标 $\omega$ 处一个是 $1$, 一个值为 $0$ | 否定, 定理 |

**主审的判断对了一半.** 对的: 分支按 $z$ 的结构递归给出时, 沿第一位置的单调由 `⊞₁-fst` 白送, 不要 `WF` (`Ig-pre`, `Lg-node`). 要改的两处:

1. **坐标要用差的写法.** 分支对坐标 $z$ 递归, $z$ 是第 0 层的树. 若 $z$ 是 `Σ A Lg`, 极限 $z=\lim f$ 的相邻项 $f_n\lhd f_{n+1}$ 只是证明, 不是 $f_{n+1}=f_n\boxplus y$, 所以 $g(f_n)\lhd_1 g(f_{n+1})$ 推不出来 (判断, 没有编译). 坐标取差树 `D₀` (与 `Σ A Lg` 互译到值, `BrwMidZero`), 单调就是沿前缀 $z\mapsto z⨾y$, 一行.
2. **读回差不是被构造消掉, 是被构造给出.** 布劳威尔节点 `bN g` 只带 $g$ 的话, 增量读不回来: `incr-blind`. 原因是极限坐标处的连续: 合法性只管沿前缀单调, 不管 $g(\lim)=\lim g$. 正规节点把增量 $\Delta$ 存在数据里 (`mN Δ`), $g$ 由它算出, 读回就是取 $\Delta$, 不要 `dif`, 也不要 `WF`. 第 0 层没有这个问题, 因为第 0 层只有 $\mathbb N$-极限 (`dif-ok`).

## 2 折叠

增量就是折叠算出的差: `SumOne` / `BrwMid` 的折叠在保留节点时输出 `ni s (λ y → Run …)`, 分支是 "在坐标 $z$ 的状态上走 $u(z)$" 的差, 即 $\Delta(z)$. 它由折叠直接算出, 不要折叠对自身单调; `nrm` 把它读成正规节点, `out-legal` 给合法. 这与 `TLPrefix` 的互递归不同: 那里输出带 `lim g` 与 $g$ 的单调证据, 单调证据只能递归调用折叠的单调性.

**没有做的:** 把 `BrwMidFold` 的第 1 层状态换成 `N₁` 直接输出 (状态在第 1 层要再当输入走时, 读回 `D` 就是 `mN Δ ↦ ni (λ z → Δ z)`, `mK` 的分支在层 $c$ 上要坐标, 用 `dif` 从 $W$ 到 $c$). 判断是机械的, 不改变结论. $\psi_0(\Omega_\Omega)$ 的顶层 `D̂` 有一切层 $k<W$ 的节点, 要每一层的 `B_k`; 构造同形, 按层的族写 (同 `CumReadCF` 的 `O`), 没有做.

## 3 回灌闭包

`nκ` 写成同一种节点 `bK W g` / `mK W Δ`: 分支在层 $c=W\boxplus z$ 上, $z$ 是差的坐标. 这就是 `SumOne` 的 `Cut`, `Walk` 已经做的事 (沿 $W\lhd c$ 的路径走层). 合法性同 `bN` (`Lg-br`). `nrm` 把 `nκ` 读进来, 只在 $c=\mathrm{sum}\,W\,z$ 这种层上取值; 任意合法层 $c$ 由 `dif` 化成这种层, 值相同, 字面不同 (`BrwMidZero.sum-dif-not-≈ᴬ`). 所以 `nκ` 能写成正规节点, 坐标是世界之上的差 (定理: `Lg-br` 的 `mK` 情形); 与 `nN` 只差坐标读作 "低层的树" 还是 "层".

## 4 序数值

没有做. `out-legal` 只给合法, 不给值. 第 0 层的值与 `BrwMid` 相同 (同一个折叠). 未走通, 没有否定.

## 5 结论: 中间层能否整个是布劳威尔树

- **作为读法: 能, 第 0 层与第 1 层是定理** (`toA`, `Lg-br`, `out-legal`), 无前提, 不要 `HS`, `Goodᴺ`, `WF`, `ψW`. 更高层同形, 判断.
- **作为数据: 不能只存布劳威尔树.** 卡在 $\Omega$-极限节点 (第 $\ge1$ 层的 `lim g`, 以及 `nκ`): 只存 $g$ 时增量读不回来, 依据是编译过的 `incr-blind` (前提可满足: `Lg-gL`, `Lg-node` 都给出). 折叠要再走自己的输出 (链 $\gamma$ 的起点是状态在第 $k$ 层的差), 所以数据要存增量. 存增量的布劳威尔树就是正规节点 `mN Δ`, 它与差树的 `ni` 是同一件东西换个记法.
- `incr-blind` 只否定 "只靠沿前缀单调读回增量". 不否定带连续性证据的布劳威尔节点 (那要对折叠的输出证连续; 正规节点的连续是定义性的).

## 账

`BrwHighOne` 代码 196 行, 其中合法性 (`⊲₁-tr`, `⊞₁-fst`, `⊞₁-⊲`, `Lg-⊞₁`, `Ig-pre`, `Lg-Ig`, `Lg-Ips`, `Lg-node`, `Lg-br`) 50 行, 无前提或前提只在加数上. 对照: `BrwMidZero` 的第 0 层合法性 28 行切片, `SumOne` 71 行.

## 翻译账

| 模块 | 记号读来的字段或形状 | 类 |
|---|---|---|
| `BrwHighOne` | 无. 正规分支是布劳威尔树加法的递归; `nκ` 的形状同 `SumOneTree` | 提供信息 |

## 审计

`importclosure.py`: `BrwHigh`, `BrwHighOne` OK. `depslice.py` (到达/记号块/词命中): `Lg-br` 31/0/0, `out-legal` 40/0/0, `incr-blind` 41/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwHigh where

open import OCF.Align.BrwHighOne using (B₁; _⊞₁_; ⊞₁-fst; Lg-⊞₁; Lg₁; Ig; Ig-pre; Lg-node; N₁; br; Lg-br; nrm; out-legal; incr-blind) public
```
