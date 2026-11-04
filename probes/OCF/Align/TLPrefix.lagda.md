# 前缀: 能否只放在证据里, 不改值

> **判决: PARTIAL.** 编译过的结果全部 `--safe --without-K --lossy-unification`, 无公设, 无洞.
>
> | 目标 | 结果 |
> | --- | --- |
> | 1 不改值的前缀 | **HOLDS.** `VP` 是定义. (iii) 差分的和逐项不改值 (`col-exact`), (i) 绝对的和改值 (`abs-overshoot`), (ii) $u+y$ 只在 $u=1$ 这样的情形有界 (`no-⊕≼`, `1⊕≼`). 字面的切点不能从值的证据得到 (`graftV→LPO`) |
> | 2 替代世界前缀 | **第一站 HOLDS, (iii) 替代不了 (ii).** (ii) 本身在 $\psi_0(\Omega_\Omega)$ 不改序数值 (`TᵖΩ≈`, `TᵖΩ≈T⁰`). 第二站 `HS-Tᵖ` 无条件 (已有), 序数值未比较. (iii) 要字面证据, 就是 `Hn`, 没有去掉 |
> | 3 替代 `padO` | **在 `HtB` 世界未走通.** `T⊤ˣ` 仍是条件定理. 在 $A$ 世界 `TLOpsClo.Feed.T` 无条件, 没有 `⌈_⌉`, 与 `T⊤` 没有定理 |
> | 4 毛刺与代价 | 第 1 项深度 4 起形状不同 (有限测试, 值相同是定理). 第 4 层代价比 `T⁰` 高, 见下 |
> | 理想形态 | **PARTIAL.** 证据进 `lim` 的数据树过了正性和停机, $\Omega$ 带证据造出来了, 第 0 层 `HS` 不要 `WF`; 折叠没有写完, 骨架有停机报错. 未走通, 不是否定 |

## 三种前缀

| 前缀 | 定义里有什么 | 改值吗 | 依据 |
| --- | --- | --- | --- |
| (i) `ordᴰ`, `cumA`, `padO` | 绝对的和, $\lceil\cdot\rceil$ | 改 | `abs-overshoot`, `overshoot` |
| (ii) `TLOpsPre`, `NoCumPre` 的 $u+\mathrm{rd}\,y$ | 算术, 不要证据 | 第一站不改序数值, 改基本列; 第二站未知 | `TᵖΩ≈`, [TLPrefixTest](TLPrefixTest.lagda.md) |
| (iii) `Lit`, `lit`, `graft₀` | 字面含前项 | 不改 (逐项) | `col-exact`, `NoCumLit.eq` |

(iii) 与 (ii) 不是一回事. (iii) 只是把已有的字面切点写出来, 所以要切点: `graft₀` 读 `⊴₀`, 世界上的就是 `Fp`, 也就是 `Hn`. (ii) 不要切点, 代价是 $u+y$ 与 $y$ 的等式要事后证. `graftV→LPO` 说这个差别不是工程量: 只有 "$u$ 的值低于 $y$" 时造不出 (iii).

**第三条路 (判断, 依据是 `TᵖΩ≈`).** 定义里放 (ii), 合法性由构造得到; 值的等式放到第 4 层. 第一站的价钱是一条 `Cross` 加三条关于 $1+$ 的引理. 再往上 $u$ 变大, `no-⊕≼` 说没有 $u+y\preccurlyeq y+1$ 这样的通用界, 要 $u\cdot\omega\preccurlyeq y$ 这样的输出下界. 这不是 `Hn` (字面), 是值上的下界, 判断比 `Hn` 弱, 没有编译.

## 目标 3

`padO` 的放大来自 $\lceil\cdot\rceil$, 来自 `HtB` 要规范位置, 规范位置要严格. 所以 `T⊤ˣ` 要输出 `Str` 或 `Lit`, 而 `no-Good→Str`, `no-Str-out` 说这不能只从 `Goodᴺ` 读. 前缀不解决这件事, 换前缀也没有用.

$A$ 世界不要规范位置: 比较是 `cmpN`, `Lg` 允许相等的相邻项, `Lit-force` 对一切证书成立. 所以 `TLOpsClo.Feed.T` ($\eta\mapsto\psi_0(\Omega_{\Omega\cdot\eta})$ 的回灌) 无条件, 只有 $\oplus$ 型的世界前缀, 没有 $\lceil\cdot\rceil$. 它与 `CrossMClosed.T⊤` 之间没有定理: 两个世界高于第一站没有比较. 判断是同类, 不写成 `T⊤ˣ`.

`exact→LPO` 不挡: `Feed` 只读输出. `no-Str-out` 不挡: `Lit₀` 比 `Str` 弱, 允许相等的相邻项, 退化的 $\alpha$ 在这里合法.

## 理想形态

尺子: 有没有单独的合法性证明要补? 定义是否依赖事后的证书?

| 东西 | 单独的证明 | 定义依赖证书 |
| --- | --- | --- |
| `T⁰`, `TΩᴺ`, `Tᴺ` | 有 (`ψW`, `Hn`) | 是 (`force`, `cell` 读 `Y-lit`) |
| `Tᵖ` | 有 (`ψW`) | 是 (`force` 读 `G`) |
| `Tᶜ` | 有 (`HS-Y`) | 否, 但累加 |
| [TLPrefixNative](TLPrefixNative.lagda.md) 的 `Ω̇`, `ord`, `HS-ord` | **没有** | **否** |
| 那里的折叠 `ψ` | 没写 | 没写 |

**旧结果的前提.**

| 旧结果 | 否定的形状 | 这里在不在前提里 |
| --- | --- | --- |
| `Cumsum.ψᴱ-not-mono` | $\psi$ 对结构序 $\prec$ 单调 | 不在. 证据是 `⊴`, 不是 $\prec$. `ψL` 对 `⊴` 无条件成立 (已有, 不问 `WF`) |
| `Certified.ψ-not-⊑mono`, `mono⇒strict` | $\psi$ 对 $\sqsubseteq$ 单调 | 不在. 反例走非链分支 $(\lim G)+1$, `⊴` 只走第一位置 `nd` |
| `Certified.Ω-not-step` | $\Omega_\omega$ 相邻项 $\sqsubseteq$, 因为 `limᵢ` 里写着证明 | 不在. `Ω⊴` 编译过: 懒嵌入 `oe` 没有把证明写进节点 |
| `Cumsum` 候选 A | 到 $\varepsilon_0$ 成立, 卡在 $\psi^{\mathsf E}$ | 同一个想法, 换了关系. 判断: 卡点由 `⊴` 消去, 没有编译到折叠 |
| `LevelFixVal.Legal` | 不是否定, 块外谓词, 只管层号 | 这里进了定义, 也管第 0 层 |

**能否用归纳-递归把步进证据放进第 0 层树的 `lim`.** 第 0 层是 `O azero`: `ol F st`, `st n : F n ⊴ F (suc n)`. 朴素的全局写法过不了正性 (报错原文):

```text
_⊴_ is not strictly positive, because it occurs
in the type of the constructor ol
in the definition of O, which occurs
                      to the left of an arrow
                      in the type of the constructor oi
                      in the definition of O, which occurs
                                            in the type of the constructor self
                                            in the definition of _⊴_.
```

分层过得了: 关系作参数 (`Str`), 对层递归 (`LeR`, `LeC`). 这是编译过的 `TLPrefixNative`.

**第一个障碍.** 折叠与 `⊴` 的互递归. 一次性的骨架 (其余引理作占位, 只测停机, 不进仓库) 的报错原文:

```text
Termination checking failed for the following functions:
  Skel.ψ, Skel.ψL
Problematic calls:
  ψ t (tgS R T) (outS R x₁)
  ψL T T (st n)
  N1.Skel.zS n
  ψL (self-tg r) (self-tg r) (m (inS (≪S r) (chain n)) (inS (≪S r) (chain (suc n))) (zS n))
```

判断: 骨架里 `ee` 行用了 `outS R x₁`, 不是结构子项; 占位函数也隐去了结构. 真正的问题是证明的类型里 $\psi$ 作用在 `upP P x` 这样的非结构项上, 检查器连隐式参数一起查. 按路径显式匹配可能绕开一部分 (`ψC`, `eC`), 没有走通. 其余约 600 行 (`add`, `rep`, `ψQ`) 没有移植. **这不是否定.**

**与壁垒相容吗 (判断, 依据是定理).** 相容, 只要证据的来源留在折叠里. 下标类型没有 Ω-共尾元, 比较都在字面上界之下 (`cmpN`, `cmpF`), 没有全局三歧; `oi` 的分支对低层绑定, 与现有的树一样. 壁垒的前提不被要求. 不相容的是把任意的树读进来: `exact→LPO`, `graftV→LPO` 说这种转换要 LPO. 所以合法性只能 "按来历", 这与 `Cumsum` §4 的结论一致.

## 第 4 层的代价

口径 `Survey/scripts/locslice_station.py` (块级近似, 含参照树与标签约 2140), 多加两条路线, 脚本不改. 到 $\psi_0(\Omega_\Omega)$ 这一站:

| 路线 | 定义 | 加证书 | 加序数值验收 | 第 4 层新增 (减共用参照) |
| --- | --- | --- | --- | --- |
| `T⁰` | 829 | 997 | 4059 | 约 920 |
| `Tᶜ` | 908 (含定义) | 908 | 4832 | 约 1780 |
| `TΩᴺ` | 1777 | 1777 | 5498 | 约 1580 |
| `TᵖΩ` | 1661 | 1826 | 6406 | 约 2440 |

`TᵖΩ` 的定义和证书对一切 $(p,a)$, 不只这一站, 所以前两列不可比. 第 4 层它最贵, 主要是 `Cross` 经 `BTBOFull` 的机器, 再加桥. 手写只有 `TLPrefixStation` 这一个文件. **所以这一站前缀确实增加第 4 层**, 约是 `T⁰` 的两倍半. 只有一站, 不能外推.

## 审计

- **导入闭包 `importclosure.py`:** `TLPrefixVal`, `TLPrefixBridge`, `TLPrefixNative`, `TLPrefixTest` 退出码 0, 禁用表 0. `TLPrefixStation`, 入口 `TLPrefix` 退出码 1: 经 `NoCumAcceptOmega`, `BTBOValNeg` 到 `EBO`, `Stage2`, 这是验收文件 (正对照也在这里).
- **定义级切片 `depslice.py` (块数, 记号块, 词命中):** `graftV→LPO` 51, 0, 0; `abs-overshoot` 45, 0, 0; `no-⊕≼` 19, 0, 0; `TᵖΩ≈` 908, 0, 0; `Cross` 365, 0, 0; `force-Y` 162, 0, 0; `HS-ord` 82, 0, 0; `Ω̇` 32, 0, 0. 正对照 `NoCumAcceptOmega:label-T⁰` 873, 92, 58. 切片是语法级的; `TᵖΩ≈` 的陈述读 `BTBOᴵ`, 它的标签在 `Label`, 这里没有读.
- **禁用构造:** 全部 `TLPrefix*` 没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, `--cubical`. 骨架里的占位只在个人临时目录.

## 导航

| 文件 | 内容 | 记号 |
| --- | --- | --- |
| [TLPrefixVal](TLPrefixVal.lagda.md) | `VP`, `col-exact`, `abs-overshoot`, `no-⊕≼`, `graftV→LPO` | 否 |
| [TLPrefixBridge](TLPrefixBridge.lagda.md) | `force-Y` 过 `NoCumPre` | 否 |
| [TLPrefixStation](TLPrefixStation.lagda.md) | `Cross`, `TᵖΩ≈`, `TᵖΩ≈T⁰` | 导入闭包经 `BTBOFull` 含 `EBO`, 验收文件 |
| [TLPrefixTest](TLPrefixTest.lagda.md) | 毛刺, 有限测试 | 否 |
| [TLPrefixNative](TLPrefixNative.lagda.md) | 证据在树里 | 否 |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLPrefix where

open import OCF.Align.TLPrefixVal public using (VP; VP-Lit; module Col; abs-overshoot; ω·2-delta; ≼⊕′; no-⊕≼; 1⊕≼; 1⊕≼lim; GraftV; graftV→LPO)
open import OCF.Align.TLPrefixStation public using (Cross; TᵖΩ; TᵖΩ≈; TᵖΩ≈T⁰; any-certᵖ; module Run)
open import OCF.Align.TLPrefixTest using ()
open import OCF.Align.TLPrefixNative public using (module Str; O; Ω̇; Ω⊴; Ω≈; ord; HS-ord; from; Lg-from)
open import OCF.Align.NoCumPre public using (Tᵖ; HS-Tᵖ)
open import OCF.Align.TLOpsClo public using (module Feed)
```
