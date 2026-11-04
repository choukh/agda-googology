# `Hn` 在 Ω+1: 暂停

> **判决: PARTIAL.** `Hn (Tᴰ 1 one one g₀ C.self)` **未证, 暂停, 未走通**, 没有否定定理. 全文 `--safe --without-K --lossy-unification`. 这里不含记号, 验收在 [NoCumHnAccept](NoCumHnAccept.lagda.md).
>
> ## 这一轮拿到的
>
> | 结果 | 档 |
> |---|---|
> | `TΩᴺ≈ : fr TΩᴺ ≈ᵛ BTBOᴵ`, `TΩᴺ≅`, `TΩᴺ≅T⁰`, `any-cert` | **序数值验收 (主档), 定理.** 过 (p, a) 世界, 不累加, 无前缀的 $\psi_0(\Omega_\Omega)$ |
> | `no-Hn-b : Hn t₂ → ⊥` | 编译过的否定, 范围见 [NoCumHnNeg](NoCumHnNeg.lagda.md) |
> | `Bach`, `Vis-lift`, `mono₂`, `≪→Fp` | 一步的定理, [NoCumHnCore](NoCumHnCore.lagda.md) |
> | `Q-ψ`, `force-Y` | 高度 0 的世界折叠与 `CumReadCF` 同形, [NoCumHnBridge](NoCumHnBridge.lagda.md) |
>
> ## `Hn` 与 `Vis`, `Hon`, `Above` 是不是同一件事
>
> **内容相同, 位置不同.** 逐条对照 (读源码, 判断):
>
> | `OCF.Free` | 这里 | 关系 |
> |---|---|---|
> | `CvP C b`: $t\sqsupseteq\Omega_b$, $G$ 是 `run C t` 的证书, 则 $b+1\sqsubseteq^I$ `lvG G` | `Vis-lift`, `Bach` 的前提里的 "压过 $\Omega_c$ 则 `Fp c`" | **同一条陈述**, 只差: 那边模 $\cong^I$ 的 $\sqsubseteq^I$, 这边字面的 `Fp` |
> | `Above`: 输出压过 $\Omega_j$ | `Ωfst` 加 `Vis-lift` | 同一件事 |
> | `Hon ℓ a C`: `suc a` 行的 $\ell\sqsubseteq^I$ `lvG` | 加法 $W\oplus$ 闭包时世界含 $W$ 的世界, 那一支的守卫 | 同一件事 |
> | `Good` 的 `bi`, `bs`, `bŝ` 行 | 还没有写 | 缺的就是这个 |
> | 没有对应 | `Hn` | `Hn` 只是最外层 (上下文是恒等) 的结论. `Vis` 是证 `Hn` 时必须加强成的归纳假设 |
>
> **能不能写成结构字段. 分两半.**
>
> - **闭包这一行可以.** `Bach` 是对结构参数的一步定理, 用到的字段只有: `tie` (链点是读出), 链点的第一位置, `cmpN`. 不看折叠的规则, 不按阶段分.
> - **传过上下文的部分, 没有走通, 也没有否定.** 编译过的证据: 同一个源 `Ω̇ 1 0`, 直接折叠到第 0 层时 `Hn` 成立 (`Hn-Ω`), 先过目标 $w$ 的折叠再到第 0 层时 `Hn` 是假的 (`no-Hn-b`). 所以 `Hn` **不是源的 $(p,a)$ 形状的函数**, 它依赖折叠的目标是什么下标. 目标 $t=0$ 经过 `ψ 1 0` 的那一棵正是 Ω+1 要证的, 未证. 要成为字段, 字段得挂在世界或下标上 (下标带 "我是读出" 的证据), 不能只挂在 $(p,a)$ 上. 我试着把上下文的类定成只由 $(p,a,u)$ 决定的 $\mathcal V(a,u)$, 纸面上卡在: $a>t$ 时 $C\circ\psi_{q,t}\notin\mathcal V(a,u)$, 而这正是 `oi` 上升的情况. 所以判断是 `Good` 的 `bi` 那种对子类全称的写法省不掉. 这是判断, 没有编译.
>
> ## 第一个障碍
>
> 没有报错原文: 上下文类没有写成代码. 没写的理由是下面这个纸面分析, 不是定理.
>
> 对项递归证 "折叠保 `Hn` 的上下文版" (`ψW` 的样子), 要一个 $\mathcal G\,\mathcal C\,x$ 对项递归, $\mathcal C$ 是上下文的类. 上下文要有帧 (`ψ q t`, `add W R`), `run C x`, 公共世界界. 卡点在 `os`: $\psi(\mathrm{os}\,x)=\lim \mathrm{rep}(\psi x)$, 所以 $x$ 要在 $C\circ(W\oplus)\circ\psi$ 上也好, $W$ 取遍 `rep` 的项. 这个类要对 "第一位置压过 $W$" 封闭, 就是 `Good` 的 `bs` 行的 $\mathcal K$ 和 `FlOver`. `os W` 确实出现 ($W\oplus\mathrm{os}\,o_0$, $W=\Omega_\Omega$). 在 `OCF.Free` 里这一族是 `Class`, `Good`, `ClassF`, `Rules` (合计 1675 行). 这里世界去掉了 `tr`, 其余形状看不出能省.
>
> 另外试过按源项和帧递归, 不走类: `Ω̇ 0 0` 经帧 `ψ q t` 回到 `Ω̇ q t`, 高度和层都可以变高, 没有结构递归可用. 所以这条不通 (判断, 不是定理).
>
> `no-Hn-b` 路径上的报错原文 (直接对 `Tᴰ 1 (w+1)` 走, 不是对 Ω+1):
>
>     agda: Heap exhausted;
>     agda: Current maximum heap size is 12884901888 bytes (12288 MB).
>
> ## `mx` 是否多余
>
> **判断, 未编译:** 同高度的目标 $t$ 放进世界是多余的. [CumReadCF](CumReadCF.lagda.md) 的折叠完全没有世界, 同高度比较靠 `Tg t L` (层字面可比) 就够了. 世界只在跨高度时要: 目标低于项 ($q<p$) 要 $t$, 因为 `od` 的 $k\ll$ 世界要和 $t$ 比; 目标高于项 ($q>p$) 要 $a$, 因为 `oi` 变 `od` 时 $k\ll a$ 要落到世界. $q=p$ 时两个都不要. 改掉要动 `ψ` 的全部世界参数, 没做.
>
> **编译的部分:** `no-Hn-b`: 对字面任意的目标, 当前写法的 `Hn` 是假的. 这与上面一致, 但**没有证明**改掉 `mx` 后 `Hn` 就成立. Ω+1 的目标是 $0$ 或链点的前驱 (链点是输出的读出). `no-Hn-b` 的 $w$ 不是这样来的, 所以它不否定 Ω+1. 这一句是判断.
>
> ## 翻译账
>
> 这一轮**定义没有新增**: 没有新构造子, 新节点, 新字段. 新文件全是定理和验收.
>
> | 东西 | 来源 |
> |---|---|
> | $(p,a)$ 层的形状 | 读自记号 $\Omega\cdot p+a$. 上一轮已有 |
> | `oc` 的守卫 `Hn`, `Fp` | 树逼的: 比较要字面公共上界, 闭包的世界要在链点之下 |
> | `tie`, `lit`, `graft₀` | 树逼的: 下标要字面合法 |
> | `od`, `oL` | 高度带来的. 高度的形状读自记号, 字段是树逼的 |
> | `mx` 里的同高度目标 | 世界写法带的 (判断), 不是序数值需要的 |
> | `Vis`, 上下文类 (未写) | 序数值需要的那部分是 `Bach` 那一步; 帧和 `os` 的类是翻译带来的还是必需的, **未定** |
>
> `Lab` 只作探路: `label-TΩᴺ`. 主档是 `TΩᴺ≈`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoCumHn where

open import OCF.Align.NoCumHnCore using (module Chain; ≪→Fp; Vis-lift; mono₂)
open import OCF.Align.NoCumHnBridge using (Q-ψ; force-Y)
open import OCF.Align.NoCumHnNeg using (no-Hn-b; t₂; Pψ; J)
```
