# 跨段, 下一步: $\psi_0(\Omega_{\psi_1(\Omega)+1})$ 这个硬点, 第 0 行的证书

> **判决: PARTIAL.** [CrossM](CrossM.lagda.md) 报告的障碍 (a), (b) **都解决了, 编译过, 无条件**: 数据树 `T₊` 的第 0 行有三个带证书的折叠. 其中一个与 `T⊤` 字面同值 (`T⊤≅T̂ᵀ`). 字面的 `Tᵀ cz 0` 本身没有证书, 差的只是 `ĉᴸ` 的链生成器. $\alpha\ge1$ **没有做**; 下一个障碍在那里, 判断: `Clo` 绕不开, 见下.
>
> | 定理 | 陈述 | 文件 |
> | --- | --- | --- |
> | `branch≈ e` | `Tᵠ end 0 ≈ᴿ ψ̄ᵀ ok′ e′ (stepT e)`, 对一切 `e`, 一切证据 | [CrossNextDn](CrossNextDn.lagda.md) |
> | `D→≈ᵠ`, `D-Ψ`, `D-self` | 关系 `Dn` 蕴含计值同值; `Ψ` 与 `ΨT` 同值; 第 0 行有 `Dn` | 同上 |
> | `≋-T d` | `A ≋ B` 时两个世界顶上的第 0 行 $\cong$ | [CrossNextInst](CrossNextInst.lagda.md), 对齐在 [CrossNextEq](CrossNextEq.lagda.md) |
> | `Along.Ĝ`, `Along.T̂≅` | 对任何节点 `𝒩` 与同值的分支族: 沿累加链有 `Goodᴺ`, 与 `νT 𝒩` $\cong$ | [CrossNextSum](CrossNextSum.lagda.md) |
> | `Sum.ĜS` | 对 **任何** 带证书的分支族: `ĉᴸ zero t₀ S t₀ S` 有 `Goodᴺ`, 不要单调性 | 同上 |
> | `Sum.Out.ĜO`, `T̄≼T̃`, `T̃≼T̄` | 链带前缀, 输出是另一族: `step` 给出 `Goodᴺ`; 带不带前缀值互相 `≼` | 同上 |
> | `lvG-path`, `lvG-≼`, `ofZ-≋`, `pre≺` | 前缀的码是字面初始段; 右加数层号不超过和; 码转一圈逐点相同; 上一个输出 $\prec$ 下一支 | 同上 |
> | `G-E e`, `E≅ e` | `brE e` 有 `Goodᴺ`; 值 $\cong$ `Gᵖ M′ end 0` | [CrossNextInst](CrossNextInst.lagda.md) |
> | `T̂ᵀ`, `HS-T̂ᵀ`, `fgĥ`, `T⊤≅T̂ᵀ`, `fgh⊤≡` | 修法一: 闭项, `HS`, FGH; 与 `T⊤` $\cong$, FGH 逐点相等 | 同上 |
> | `T̃ᵀ`, `HS-T̃ᵀ`, `fgh̃` | 修法二: 闭项 | 同上 |
> | `T̄ᵀ`, `HS-T̄ᵀ`, `fgh̄`, `T̄-shape`, `stepᵀ`, `domᵀ` | 修法三: 闭项, 输出是 `Tᵀ cz 0` 的字面输出 | 同上 |
> | `T̄≼T̃ᵀ`, `T̃≼T̄ᵀ` | 修法二, 三的层号互相 `≼` | 同上 |
> | `Tᵀ-shape` | `toZ (Tᵀ cz 0)` 就是不带前缀的 `ĉᴸ`, 分支是 `brE`, 起点 `t₀ᵀ` | 同上 |
>
> **条件定理.** `Along`, `Sum`, `Sum.Out`, 带结构参数, 上面的实例都闭合. 没有别的条件定理.
>
> **有限测试 (不是证明).** [CrossNextTest](CrossNextTest.lagda.md): 三个闭项头部是极限, `fgĥ 0 = fgh̃ 0 = fgh̄ 0 = 1`, `fgh̃ 1 = fgh̄ 1 = 2`, `T̃ᵀ`, `T̄ᵀ` 的第 0, 1 项头部是极限; 毛刺在形状上看得见: 第 1 项的第 0 项的第 0 项, `T̄ᵀ` 是 0, `T̃ᵀ` 是后继. 比较器 `refl`, 盲区: 小值和头部不区分强度. 没有结果的: 上一轮 `fgh⊤ 1` 的 `refl` 400 秒没有结果, `fgĥ 1` 与它相等 (`fgh⊤≡`), 这一轮没有再试. [CrossNextAccept](CrossNextAccept.lagda.md) 的 `fs-2` 是只关于记号的定理.
>
> **判断 (单列).** 读法: 三棵树都到 $\psi_0(\Omega_{\psi_1(\Omega)})$; 只有 `T̂ᵀ` 与 `T⊤` 之间是定理, 而 `T⊤` 的读法本身也是判断, 没有标签 (`no-val-T⊤`). 下面 "代价" 和 "(c)" 两节里没有定理名的话都是判断.

## 三个证书

`Tᵀ cz 0` 的第 0 行是 `tH 𝟏ᵀ stepT`. 它的分支 (a) 已经与世界里的第 0 行同值 (`branch≈`). 卡的是链: `ĉᴸ` 的链点只记得 $\eta$, 相邻两支 `cz ᶜ+ ⌈η⌉` 没有 `⊂` (`no-⊂⌈⌉`, 只否定那个证明办法). 三条路:

| | 修法一 `T̂ᵀ` (带码) | 修法二 `T̃ᵀ` (分支带前缀) | 修法三 `T̄ᵀ` (只有链带前缀) |
|---|---|---|---|
| 形状 | `Z.lim (brE ∘ C)`, `C` 是 `T⊤` 的码链 | `ĉᴸ zero t₀ S t₀ S` | `ĉᴸ zero t₀ S t₀ oᵀ` |
| 新构造子 | 没有, 但不是 `ĉᴸ` | 没有 | 没有 |
| 单调性 | `↑br`: 跨段, `up≺` | `pre≺`, 对任何 `b`, 不看 `b` | `stepᵀ`: 跨段, `up≺`, 加 `≋-T` |
| 基本列 | 与 `T⊤` 逐项 $\cong$ | **每项顶着 $\hat\eta_k+1$** | 输出没有前缀; 高度带着前缀 |
| 与 `T⊤` | **$\cong$ (定理)** | 没有定理 | 没有定理 |
| 与字面 `Tᵀ cz 0` | 分支相同, 外形不同 | 外形相同, 分支多前缀 | 只差链生成器 (`T̄-shape`) |
| 能否放进折叠 | 不能: 链要闭合的证书, 只在头部 | `ŝ` 可以, 见 (c) | `ĉᴸ` 的链要闭合的 `Z`, 见 (c) |

**修法一的代价.** 这里的 "带码" 只在头部: 链用 `𝒯` 的证书预先算好. 要它成为折叠里的节点 (`tH` 在 `tΩ` 下面, 链依赖上下文), `Ordˢ`, `Z`, `Goodᴺ` 都要加一个带码的构造子. `Ord₊ˢ` 的每个消去 (`trˢ`, `tr⁻ˢ`, `toZ`, `addˢ`, `Eq₊ˢ`, `tl`, `ι↓`) 和整条闭包定理都要改. 判断: 与 (c) 同量级, 没有做. 好处是基本列没有毛刺.

**修法二的代价, 作者说的毛刺.** `Sum.ĜS` 对任何 `b` 成立, 取 `b` 为常数也有证书. 所以这个 `Goodᴺ` 不含关于 `b` 的单调信息. 基本列的第 $k+1$ 项是 $(\hat\eta_k+1)\oplus b(\eta_k)$, 每项顶着上一个输出 (形状的测试在 [CrossNextTest](CrossNextTest.lagda.md)), FGH 的值因此不同于不加前缀的树 (判断; 算出来的 $n=0,1$ 上相同, 这两个值不区分). 值不变: `T̄≼T̃ᵀ`, `T̃≼T̄ᵀ` 说它与修法三互相 `≼`. 结构值验收 (互相 $\sqsubseteq^0$) 没有证, 判断是假的: $b\sqsubseteq^0 a\oplus b$ 一般不成立, `CumRead` 的 `absorb-fails` 同形.

**修法三的代价.** 毛刺从输出搬到了高度: $\lceil\eta_{k+1}\rceil$ 里每一块都带着 $\hat\eta_k$, 高度增长比 `T⊤` 的累加链快 (判断, 同 `overshootᴬ` 的形状). 多了一个函数外延的坑: $\lceil\hat\eta\rceil$ 读回只逐点相同, 要 `≋` 和 [CrossNextEq](CrossNextEq.lagda.md).

**我的选择.** 要说清与 `T⊤` 的关系, 用修法一: `T⊤ ≅ T̂ᵀ`, 目标的最强形式. 要证书落在字面的 `ĉᴸ` 上且输出不带前缀, 用修法三. 修法二最便宜 (不要 `up≺`), 不推荐作定义.

## 与 `T⊤` 的关系

- `T⊤≅T̂ᵀ`: 定理. 所以 `T⊤ ≼ T̂ᵀ` 且同值, 在结构值验收的意义下也互相 $\sqsubseteq^0$ (都由 $\cong$).
- `T̃ᵀ`, `T̄ᵀ` 与 `T⊤`: **没有定理, 未走通.** 要的是跨码的值单调: `T(C_n)` 与 `T(cz ᶜ+ ⌈η_k⌉)` 比较, 而 $C_{n+1}=C_n$ `ᶜ+ cs` $\lceil w\rceil$ 的后面几块是 $\lceil w_j\rceil$, 对面是 $\lceil a\oplus w_j\rceil$, 不是初始段, 第 0 行的写法不对齐. 这要折叠对值 `≼` 单调, `ψ⁰-not-cong` 一带已知这条不便宜. 判断: 同值. 这是我认为现在最值得回答的一个问题之一, 但不是这一轮的目标.
- 字面 `Tᵀ cz 0` 有没有证书: **未走通.** 判断: $y_1\sqsubseteq^0y_2$ 大概成立 (有限高度的行字面出现), $y_2\sqsubseteq^0y_3$ 大概不成立 (极限高度的行依赖块的结构), 没有编译否定, 不写成否定.

## (c) $\alpha\ge1$: `Clo` 能否绕开 (判断, 没有编译)

**绕不开, 但 `Sum` 去掉了一半.** 把一个 `tH` 的证书化到它的分支, `Sum.ĜS` 已经做到了, 与 $\alpha$ 无关: 分支有证书就够. 所以 `tH` 本身不再要 `gŝ` 的 `𝓑`. 这是 `Clo` 的 "计值是全函数" 那一半.

剩下的在 `tΩ`, `tΩ↓`: `lim_i ψ̄ (h z_i)` 要相邻两项 $\sqsubseteq^0$, 这是 Bachmann 型单调 (`CumRead` 的 `ψL`). `z_{i+1}=ψᵀ(h z_i)` 的叶子是 `Ω̇ᵀ`, 又是一个 `tH`. 比较两个项时, 相同位置上的两个 `tH` 各有各的链. `CumRead` 已经报告了同一个点: "同一个闭包在两个世界算出的两条链字面不可比". 它只有定义, 没有证书. 这里两个世界是字面的 $M\subset M'$, 比那边好一点 (`↑T`, `↓ᴾ` 都有), 但 `no-⊞-left` 的形状还在: $\eta\lhd\eta'$ 推不出 $\lceil\eta\oplus x\rceil\lhd\lceil\eta'\oplus x\rceil$.

另外 **闭合的链不够**: 所有 `tH` 共用一条闭合的链 (规则 `gĉ` 的形状) 值是错的. 记号里 $\psi_0(\Omega_u+\Omega_u)$ 的链是 $y\mapsto\psi_0(\Omega_u+\Omega_{\psi_1(y)})$ 的闭包 (`fs-2`, 定理, 只关于记号), 比第 0 行的闭包点高 (判断), 闭合的链到不了. 所以链必须依赖上下文. 修法二, 三的前缀可以按上下文算, 因为 `ĉᴸ` 的 `g` 只是一个 `Z`, 但这要在 `Ordˢ` 层把前缀和分支一起算, 没有试.

下一步最小的试探: $\alpha=1$ 的第 1 项 `ψ̄ᵀ (ψᵀ zero (ιT zero (Ω̇ᵀ cz 0)))`, 分支有嵌套的 `tH`, `Dn` 的右边没有 `tH` 这一行, 这是第一处要加的东西.

## 第一个障碍

$\alpha\ge1$ 的闭包定理, 这一轮不做. 最小的可见处: `Dn` 的右边没有 `tH`, 而 `ψᵀ` 的叶子就是 `Ω̇ᵀ` (试 `first : Dn zero zero q0 (Ω̇ᵀ cz zero); first = dz`):

```text
error: [UnequalTerms]
t0 != tH 𝟏ᵀ stepT of type T₊ zero UT cz Fl (κ′ Fl)
when checking that the expression dz has type
Dn zero zero q0 (Ω̇ᵀ cz zero)
```

这一行本身只说明要加东西. 真正的难处是上面 (c) 的 Bachmann 单调, 那是读定义的判断. **未走通, 不是否定.**

这一轮解决的障碍, 上一轮的报错 (`Gbranch`) 现在是定理: `G-E`.

## 受记号影响的形状

与 [CrossM](CrossM.lagda.md) 相同: 第 0 行, $\Omega_{\psi_1(\Omega)}$ 是高度上的闭包, 回灌链, 读自记号. 没看记号的: `Dn` (机械改写), `≋`, `⊕`, 前缀, `lvG-path`. 不算树自足.

## 壁垒

没有新的下标类型. `Sum` 的 $\hat\eta$ 是第 0 层的树, 不是下标. 比较都在字面的 `Pos (cs M′)` 里: `stepᵀ` 的 `up≺` 在 $\lceil\eta_{k+1}\rceil$ 里比.

## 审计

记号只在 [CrossNextAccept](CrossNextAccept.lagda.md), [CrossMAccept](CrossMAccept.lagda.md), 入口不导入.

- **导入闭包:** `importclosure.py --only OCF.Free. --only OCF.BTBO --only OCF.Align.LadderNF --only OCF.Align.LadderMono --only OCF.Align.LadderInf --only OCF.Align.LadderOrd --only OCF.Align.CrossM --only OCF.Align.CrossNext OCF.Align.CrossNext`: 退出码 0, 禁用表 0, `--only` 之外 0, 61 个本地模块; 没有 `*Accept`, `EBO`, `*W*` 克隆. 正对照 `OCF.Align.CrossMAccept`: 禁用表命中 `EBO`, 退出码 1.
- **定义级切片 `depslice.py` (块数, 记号块, 词命中):** `branch≈` 515, 0, 0; `D-Ψ` 476, 0, 0; `map≋` 6, 0, 0; `lvG-path` 88, 0, 0; `G-E` 1222, 0, 0; `T⊤≅T̂ᵀ` 1202, 0, 0; `stepᵀ` 1352, 0, 0; `T̃≼T̄ᵀ` 1317, 0, 0. `T̂ᵀ` 64, `T̃ᵀ` 103, `T̄ᵀ` 101 也都是 0, 0, **但这三个数偏小: 它们经模块别名 (`A.T̂`, `B.T̃`, `O.T̄`), 切片看不见别名的实参, 这是脚本已知的盲点, 看闭包和 `G-E`.** 正对照 `CrossMAccept:fs-ψΩ`: 51, 43, 3.
- **禁用构造:** 全部 `CrossNext*` 没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, `--cubical`; 全部带 `--safe --without-K`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CrossNext where

open import OCF.Align.CrossNextEq public using (_≋_; cz+≋; ≋-refl; ≋-sym; module World)
open import OCF.Align.CrossNextSum public using (module Along; module Sum; _⊕_; addZ; addG; addG≅; ofL; ofZ; G-ofZ; ofL-lvl; lvG-path; lvG-≼; ofZ-≋)
open import OCF.Align.CrossNextDn using ()
open import OCF.Align.CrossNextInst public using (cz⊂; brE; G-E; E≅; T̂ᵀ; HS-T̂ᵀ; fgĥ; T⊤≅T̂ᵀ; fgh⊤≡; T̃ᵀ; HS-T̃ᵀ; fgh̃; T̄ᵀ; HS-T̄ᵀ; fgh̄; T̄-shape; Tᵀ-shape; stepᵀ; domᵀ; ≋-T; T̄≼T̃ᵀ; T̃≼T̄ᵀ)
open import OCF.Align.CrossNextTest using ()
```

## 导航

| 文件 | 内容 |
| --- | --- |
| [CrossNextDn](CrossNextDn.lagda.md) | 障碍 (a): `ψ̄ᵀ ∘ ι↓T` 与 `ψ̄ᵠ` 同值, 由 `LadderOrdDn`, `LadderOrdDnSelf` 机械改写 |
| [CrossNextEq](CrossNextEq.lagda.md) | `≋`, 第 0 行对齐 |
| [CrossNextSum](CrossNextSum.lagda.md) | 障碍 (b): 三条修法的通用形式 |
| [CrossNextInst](CrossNextInst.lagda.md) | 三个闭项, 与 `T⊤` 的关系 |
| [CrossNextTest](CrossNextTest.lagda.md) | 有限测试 |
| [CrossNextAccept](CrossNextAccept.lagda.md) | 记号一侧 (闭包不干净, 不进入口) |
