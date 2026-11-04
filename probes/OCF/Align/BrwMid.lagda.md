# 中间层是布劳威尔树

> 入口. **判决: PARTIAL.** 第 0 层改回布劳威尔树, 合法性由加法的第一位置给出, 定义编译过, 停机直接过. 高层的中间层仍是差树. 序数值验收未走通, 没有否定定理. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示; 不读记号.

## 1 第 0 层的互译 ([BrwMidZero](BrwMidZero.lagda.md))

| 定理 | 内容 | 档 |
|---|---|---|
| `⊞-fst`, `Lg-⊞` | $a\lhd a\boxplus b$ 无前提; $a\boxplus b$ 合法只要 $a$, $b$ 合法 | 定理 |
| `Σlim` | 部分和的极限, 步进就是 `⊞-fst` | 定义 |
| `toA : D azero W → Σ A Lg` | 差树到带合法性的布劳威尔树 | 定义 |
| `sum-toA`, `sum₀` | $\mathrm{sum}\,b\,x\approx b\boxplus\mathrm{toA}\,x$ | 定理 (值) |
| `dif`, `dif-ok` | 一条第一位置路径到差树, $a\boxplus\mathrm{toA}(\mathrm{dif}\,p)\approx b$ | 定理 (值) |
| `round₁`, `round₂` | 两个方向的往返, 值不变 | 定理 (值) |
| `dif-not-id` | 差树一侧字面不互逆: `dif (sum-fst 0 n1) ≢ n1` | 反例, 定理 |
| `sum-dif-not-≈ᴬ` | 树一侧连 `≈ᴬ` 都不互逆: 从 $1$ 到 $\omega$ 的差加回去, 第 0 项是 $1$ | 反例, 定理 |

**主审的判断对了一半.** 互译成立, 但只到值: `sum` 与 `dif` 互逆到 $\approx$ (互相 $\le$), 不到 `≡`, 树一侧不到 `≈ᴬ`. 起作用的确是那条纪律: 输出写成 "前一个输出再接一段", `⊞` 对右边递归所以 $a\lhd a\boxplus b$ 字面成立.

## 2 折叠 ([BrwMidFold](BrwMidFold.lagda.md))

由 `SumOneFold` 改写, **只改第 0 层**: 状态在目标 $0$ 上是 `Σ A Lg` (`Out azero W = L₀`), `⨾` 换成 `+ᴸ`, `nl` 换成 `Σlim`, `S` 换成 `Σlim 𝟎 (const c)`, 回灌的层是 $W\boxplus z$, 第一位置 `⊞-fst`. 第 0 层的输出再当输入走时 (链 $\gamma$ 在第 0 层的起点, 即 $\Omega_1$ 的分支) 用 `toD = dif`, 它要的 `Lg` 就是输出自带的那一个. 闭项 `T₀`, `T₁`, `Lg-T₀`, `Lg-T₁`, 没有证书参数.

**高层没有改.** 第 $t>0$ 层的差仍是 `D t`. 原因 (判断, 没有编译的否定): 折叠要走输入, 走输入要差. 第 0 层的布劳威尔树能读回差, 靠的是字面的 `Lg` (`dif`); 高层要读回差, 要的是第 $k$ 层树的字面单调 (分支对 $z$ 的单调), 那就是 `WF`, 而高层的输出又被链再走 (`Chn` 的 $\delta_0$ 是状态在第 $k$ 层的差), 所以要对折叠的输出证 `WF`: 回到 `ψW`. 差树把这一步省掉, 因为差就是输出本身.

## 3 停机

直接通过. 对照 `TLPrefix` 的报错 (`Skel.ψ, Skel.ψL`, 问题调用 `ψL T T (st n)`): 那里 `ol` 带证据, 折叠 `ol F` 要输出的证据 $\psi(F\,n)\trianglelefteq\psi(F(n+1))$, 只能递归调用折叠的单调性 `ψL`, 两者互递归. 这里输入的极限是差 (`nl d`), 折叠从不比较 $\psi(F\,n)$ 与 $\psi(F(n+1))$; 输出的步进是 `⊞-fst` 作用在已经算出的部分和上, 不调用折叠. 读回输入的 `dif` 对已经算出的树结构递归, 也不调用折叠.

## 4 序数值验收: 未走通

没有 `BrwMid.T₀ ≈ SumOne.T₀`. 卡点: 第 0 层的输出读回输入时是 `dif (toA δ)`, 与原来的差 $\delta$ 字面不同 (`dif-not-id`), 值相同 (`round₂`). 后面的折叠走的是不同的输入, 所以两次折叠的树对不上, `SumOneRel` 的结构关系用不了. 要接上, 必须补: 旧折叠对第 0 层输入值同余 (第 0 层的分支在值相等的输入上给值相等的输出). `Value.ψ⁰-mono⁰` 是它在目标 0 上的一个片段; 一般目标没有. 这是未走通, 不是否定 (`ψ⁰-not-cong` 只管第 $\ge1$ 层的参数).

有限测试 (慢增长 `G 0`, 单路径): `BrwMid.T₀`, `SumOne.T₀`, `BrwMid.T₁`, 两边第 1 项, 都是 1. 比较器太弱, 不说明什么.

## 5 账

实测, 定义级切片, 口径同 `locslice_tlrule.py` (`probes/Survey/scripts/brwmid/locslice_brwmid.py`).

| | BrwMid | SumOne |
|---|---|---|
| 定义 (`T₀`, `T₁` 的闭包) | 501 | 471 |
| 加 `Lg-T₁` | 503 | 471 |
| 单独的合法性证明 | `⊞-fst`, `Lg-⊞`: 28 (本文件 12) | `Lg-sum`: 71 (`SumOneTree` 52) |
| 读回输入 | `dif`: 41 | 不要 |

合法性的行数降到四成, 代价是 `dif` 进了定义. 证书 (`HS`, `Goodᴺ`, `WF`, `ψW`) 两边都没有.

## 6 回灌闭包在布劳威尔树里怎么写 (判断)

- **第 0 层输出:** 就是 `Σlim`: 层的链 $v_{n+1}=v_n\boxplus\Delta_n$, 输出 $\sum\Delta_n$. 这是一个 $\mathbb N$-极限, 布劳威尔树里的普通 `lim`, 合法性是 `⊞-fst`. 这一点 `BrwMidFold` 已经是这样写的.
- **高层与输入:** `nκ _ u` 是以层为分支的极限节点, 分支 $u(c)$ 对 $c\ge W$ (带 `Lg c`) 给出. 当作布劳威尔树, 它是分支类型为 "世界之上的合法层" 的极限, 与 `Ordᶜ` 的 `limᵢ` (分支是低一层的树) 不同类: 层不是低层的树, 是第 0 层的布劳威尔树. 这就是 `WorldTH` 的 `Hg` (`tφ : (A → Hg) → Hg`) 在数据里的同形, 只是 `Hg` 放在高度上, `nκ` 放在树里. 两者都不要第一支, 也都不要分支单调: 折叠走它时只沿第一位置的路径 (`Cut`, `Walk`), 用到的是差.
- 所以作者问的 "中间层也是布劳威尔树" 在第 0 层是, 在 `nκ` 这一层也是 (以层为分支的极限), 只是这个节点的分支要当差来读, 不当上确界来读. 把它改成上确界来读 (分支单调的布劳威尔极限) 就要分支单调的证据, 回到 `TLPrefix` 的互递归.

## 翻译账

| 模块 | 记号读来的字段或形状 | 类 |
|---|---|---|
| `BrwMidZero` | 无. `⊞` 是布劳威尔树的加法 | 提供信息 |
| `BrwMidFold` | 同 `SumOneFold` (`S = ·ω` 抄自旧折叠); 第 0 层改写不读记号 | 提供信息, 形状受旧树影响 |

## 审计

`importclosure.py`: `BrwMid`, `BrwMidZero`, `BrwMidFold` 全部 OK. `depslice.py` (到达/记号块/词命中): `BrwMidFold:T₀` 135/0/0, `BrwMidFold:Lg-T₁` 136/0/0, `BrwMidZero:dif-ok` 41/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwMid where

open import OCF.Align.BrwMidZero using (⊞-fst; Lg-⊞; Σlim; toA; sum-toA; sum₀; dif; dif-ok; round₁; round₂; dif-not-id; sum-dif-not-≈ᴬ) public
open import OCF.Align.BrwMidFold using (T₀; T₁; Lg-T₀; Lg-T₁; Out; toD) public
```
