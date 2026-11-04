# 换一步: $\psi(a+1)=\psi(a)\cdot\omega$ 是值逼的, 树逼的, 还是约定

> 入口. **判决: PARTIAL.** 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 定义与否定 ([AddCloRel](AddCloRel.lagda.md), [AddCloStr](AddCloStr.lagda.md), [AddCloEmb](AddCloEmb.lagda.md), [AddCloLeaf](AddCloLeaf.lagda.md), [AddCloInit](AddCloInit.lagda.md), [AddCloNeg](AddCloNeg.lagda.md)) 不读记号, 不读旧树; 值的验收只在 [AddCloAccept](AddCloAccept.lagda.md), 读旧树 (`BTBOFull`, `NoCumsum`), 不读标签.
>
> 一句话: **这一行不是树逼的** (编译过的反例: $S=\cdot2$, $S=+1$ 满足这一路能写出的全部树侧要求, 输出不对加法封闭); **在 $\psi_0(\Omega_\Omega)$ 这一站, 值只认一个带**: 结构上被 $\cdot\omega$ 盖住的 $S$ 值不超过 $\psi_0(\Omega_\Omega)$, 盖住 $\cdot\omega$ 的 $S$ 值不低于它, 两边都满足的 $S$ (不只 $\cdot\omega$ 本身) 值相等. $S=\cdot2$ 的下界和 $S=+1$ 在这一站的严格差**未走通**.

## 做法

旧的比较只有 "同一个层上和形式对上旧折叠". 这里加了一个对**任何** $S$ 都成立的工具: 和上的关系 `Rel` ($x\trianglelefteq y$), 折叠对它单调 (`AddCloRel.main`), 跨世界 (世界 $W_1\lhd W_2$ 字面相连, 比较结果不随世界变: `cmp-tr`). `Rel` 没有 "低层的东西 $\trianglelefteq$ 高层节点" 这一条, 所以不撞 `no-full`, `ψᴱ-not-mono`. 然后:

- 同一个世界: $S_1\trianglelefteq S_2$ 推出 $\psi^{S_1}_0(\Omega_y)\le\psi^{S_2}_0(\Omega_y)$ (`Step.Ψ≤`).
- 跨对角线要层的单调. 这里只有 $\cdot\omega$ 有 (旧树的 `Bump`, `Ψ-emb`). 所以比较总是 "$\psi^S$ 对 $\psi^\omega$, 同一个层; 再用 $\psi^\omega$ 换层". 下界还要把 $\psi^\omega$ 的层嵌进 $\psi^S$ 的层: 第 0 层的 `Rel` 给前驱的保序对应 (`AddCloEmb.emb`), 再搬成 `PEmb` (`AddCloAccept.GrE.pe`).
- 跨层比较要层严格. 一切把正的严格和送到正的严格和的 $S$, cell 都严格 (`SA-cell`), 字面的, 不要证书.

## 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `Main.main` | AddCloRel | 两个折叠 (任意原子), 世界 $W_1\lhd W_2$, 输入与状态 $\trianglelefteq$ 则输出 $\trianglelefteq$ | 定理 |
| `cmp-tr` | AddCloRel | 字面相连的世界里比较结果相同 | 定理 |
| `sum-mono`, `Step.Ψ≤` | AddCloRel | $\trianglelefteq$ 给值的 $\le$; $S_1\trianglelefteq S_2$ 则同一个世界里 $\psi^{S_1}\le\psi^{S_2}$ | 定理 |
| `SA-cell`, `SSt-ω`, `SSt-·2`, `SSt-+1` | AddCloStr | 对角线的层严格 | 定理 |
| `ext`, `emb` | AddCloEmb | 第 0 层的 $x\trianglelefteq x'$ 给 `sum 0 x` 到 `sum 0 x'` 前驱的保序对应 | 定理 |
| `upLeaf` | AddCloLeaf | 节点 $\sum_{z:j}1$ 对 $j$ 以下的目标盖住世界 $j$ 里一切 $\trianglelefteq$ 状态的折叠 | 定理 |
| `Up.T≼` | AddCloAccept | `SubS S ω⋅`, `SSt S` ⇒ `trA (Gen S).Top ≼ BTBOᴵ` | 定理, 序数值验收 |
| `Dn.T≽`, `DnG.T≽` | AddCloAccept | `SubS ω⋅ S`, `SSt S` ⇒ `BTBOᴵ ≼ trA (Gen S).Top`; 一般对角线同 | 定理, 序数值验收 |
| `T⁺≼`, `T²≼`, `T³≼`, `T-c+ω≼` | AddCloAccept | $+1$, $\cdot2$, $\cdot3$, $c+\omega$: 不超过 $\psi_0(\Omega_\Omega)$ | 定理 |
| `Tω²≽` | AddCloAccept | $c\cdot\omega^2$: 不低于 | 定理 |
| `T-1+cω`, `T-c+cω` | AddCloAccept | $1+c\cdot\omega$, $c+c\cdot\omega$: $\approx^v$ `BTBOᴵ` | 定理 |
| `Tʷ≼`, `Tʷ≽` | AddCloAccept | 对 $S=\cdot\omega$ 重证 `T≈` 的两半 (对照) | 定理 |
| `req-·2`, `req-+1`, `no-clo-·2`, `no-clo-+1` | AddCloNeg | 满足树侧要求, 输出不对加法封闭 | 定理 (否定) |
| `succ-spec`, `ω+ω<ω·ω` | AddCloNeg | 换封闭对象, 最小点换值 | 定理 |
| `RψI`, `ΨI≥`, `upI`, `ΨI≤` | AddCloInit | 初态 $\Omega_t+1$: 同一世界不变小; 被下一个层上的原折叠盖住 | 定理 |
| `TI≽` | AddCloAccept | 初态 $\Omega_t+1$ 的对角线不低于 $\psi_0(\Omega_\Omega)$ | 定理 |
| `runZ`, `TopD≤1` | AddCloInit | 去掉地板 ($\psi_t(0)=0$): 一切值为 $0$, 对角线 $\le1$ | 定理 |
| `TD≺`, `TD≇` | AddCloAccept | 去掉地板的对角线严格低于 $\psi_0(\Omega_\Omega)$ | 定理 (否定) |

## 分界线

`SubS S₁ S₂` 是结构的: 输入 $c$ 以 $1$ 开头, $c\trianglelefteq c'$ 推出 $S_1c\trianglelefteq S_2c'$.

| $S$ | 上界 | 下界 | 值 |
|---|---|---|---|
| $\trianglelefteq\cdot\omega$ 且 $\trianglerighteq\cdot\omega$ ($\cdot\omega$, $1+c\cdot\omega$, $c+c\cdot\omega$) | 定理 | 定理 | $=\psi_0(\Omega_\Omega)$, 定理 |
| $\trianglelefteq\cdot\omega$ ($+1$, $\cdot2$, $\cdot3$, $c+\omega$) | 定理 | 未走通 | $\le$ |
| $\trianglerighteq\cdot\omega$ ($c\cdot\omega^2$) | 未走通 | 定理 | $\ge$ |

**如实说:** 第一行的 $S$ 一步的值都恰是 $c\cdot\omega$ (`Rel` 推出值的 $\le$, 两边夹), 所以这一行证明的是 "值不认 $\cdot\omega$ 的写法", **不是** "值不认加法封闭". 分界线真正要问的是第二行的 $\cdot2$: 它满足全部树侧要求, 不加法封闭; 它的值是不是 $\psi_0(\Omega_\Omega)$, 没有定理.

## 约定的地位

| 规则 | 结论 | 依据 | 档 |
|---|---|---|---|
| 输出对加法封闭 | **不是树逼的.** `Req` 里的要求 (回灌, 层严格, 单调, 一步保持严格; 链和和的行对一切 $S$ 相同) 都被 $\cdot2$, $+1$ 满足, 它们的 $\psi_0(1)=2$ 不封闭 | `req-·2`, `no-clo-·2` | 定理 |
| "最小的闭包点" 原则 | **不定下 $S$.** 封闭对象换成后继, 最小点是 $c+\omega$, 值与 $c\cdot\omega$ 不同 | `succ-spec`, `ω+ω<ω·ω` | 定理 |
| $\psi(a+1)$ 的写法 | **值不认写法**, 认的是一个带 | `T-1+cω`, `T-c+cω` | 定理 |
| $\psi(a+1)=\psi(a)\cdot\omega$ 对 $\cdot2$ | **未决.** 上界是定理, 下界未走通 | `T²≼` | 定理 (上界); 判断 (相等) |
| 对 $+1$ | $\Omega_1$ 上值不同 (`gap-Ω₁`, 旧文件); 这一站严格差未走通 | `T⁺≼` | 定理 (上界); 判断 (约 $\zeta_0$) |
| $\psi(0)=\Omega_\tau$, 地板 | **值逼的 (对 "去掉地板"):** 去掉就塌到 $\le1$ | `TD≺` | 定理 |
| $\psi(0)=\Omega_\tau$, 取最小 | 抬到 $\Omega_\tau+1$ 值不变小; 同一层上被 $\psi_0(\Omega_{y+1})$ 盖住. 对角线相等未走通 | `TI≽`, `ΨI≤` | 定理 (下界, 单层上界); 判断 (相等) |

所以: **这一行规则是约定**, 树不逼它; 在这一站值把它逼进一个带 (定理), 带有多宽 (是否含 $\cdot2$) 未决.

## 条件定理

没有. 上面的定理都无前提; `Up`, `Dn`, `DnG` 的模块参数是对 $S$ 的结构条件, 实例都给了.

## 有限测试

这一轮没有新增. 旧的慢增长测试在 [TLRuleTest](TLRuleTest.lagda.md), 不能推序数值.

## 判断 (纸面, 没有编译)

- $S=\cdot2$ 在这一站值相等: 第 $k$ 层的一步 $\cdot2$, 由第 $k+1$ 层的一个节点的链补成 $\cdot\omega$ 以上, 所以 $\psi^{\cdot2}_k$ 只比 $\psi^\omega_k$ 慢一个 $\Omega$; 对角线是层的极限, 吸收得掉. 依据是 `TLRule` 的纸面算例和 `upLeaf` 的形状, 不是定理.
- $S=+1$ 在这一站约 $\zeta_0$, 严格小 (`TLRule` 的纸面算例).
- 初态 $\Omega_\tau+1$ 值相等: 上界 `ΨI≤` 只差一个后继的层, 换层要 $\psi^0$ 的膨胀 ($x+1\preccurlyeq\psi^0(\Omega_x)$), 没有找到现成的.
- **更高的站 (目标 3).** 带的形状大概不变: 上下界的论证只用 "同一个世界里比 $S$" 加 "参照折叠能换层", 不按阶段. 但 (i) 参照折叠换层的定理目前只有 $\psi_0(\Omega_\Omega)$ 以下的旧树 (`Bump`); (ii) 到了层要回灌闭包的站 ($\Omega_{\Omega+1}$ 起, `TLOpsW` 的 `oc`), "一步" 不只作用在第 0 层的和上, $\cdot2$ 少掉的 $\omega$ 要由上一层的链补, 而上一层本身是回灌出来的, 能不能补上没有依据. 我的判断: $+1$ 处处严格小; $\cdot2$ 在每个 "层的极限" 的站与 $\cdot\omega$ 同值, 在 $\psi_0(\Omega_{x+1})$ 这种后继层的站可能差一个层, 极限处吸收. 这是判断, 不是定理, 也不是否定.

## 第一个障碍

**$\cdot2$ 的下界.** 要 $\psi^\omega_0(\Omega_y)\le\psi^{\cdot2}_0(\Omega_{y'})$, $y'$ 是 $\cdot2$ 对角线上的层. 同一个世界里 $\cdot\omega\trianglelefteq\cdot2$ 不成立, 所以 `Step.Ψ≤` 用不上; `upLeaf` 也要 `SubS S₁ S₂`. 要的是 "一步 $\cdot\omega$ 由后面一个高层节点的链模拟", 链在整个输入的后面, 不在每一格后面, 现成的 `Rel` 写不出. 具体地, 把 `Dn` 用在 $\cdot2$ 上要一个项

    hS : SubS ω⋅ (λ c → c)     -- 要 Rel t (nl (λ _ → c)) c′

`Rel` 里没有构造子给它 (值上它就是假的: $c\cdot\omega>c$). 这不是报错原文, 是缺的那一项; 没有编译出否定, 只是这条路不通.

**$+1$ 的严格差.** 要把大世界里的 $\psi^+$ 压到小世界里的 $\psi^\omega$ 之下. `Main` 只能从小世界比到大世界 ($W_1\lhd W_2$), 反方向没有工具.

**初态的上界.** 缺 $x+1\preccurlyeq\psi^0(\Omega_x)$ (对 `SV` 的 $x$).

定义时的报错只有写法一类, 都解决了: 证明 `main` 时把 `acc f` 拆开后再交给 `mainK`, 停机检查失败:

    Termination checking failed for the following functions:
      Main.main, Main.mainK
    Problematic calls:
      mainK f r kp A₁ A₂ hA q h hY τ (cmpN (≪∘ r kp) τ lW)

解法同 `RunK`: 把 `AccL` 的两个证明作参数传下去.

## 翻译账

| 模块 | 记号读来的字段或形状 | 类 |
|---|---|---|
| `AddCloRel`, `AddCloStr`, `AddCloEmb`, `AddCloLeaf` | 没有新的树字段, 没有证书. `Rel` 的规则照折叠的形状写 (`rt` 是被 `c⨾c ⊴ ω⋅c` 逼出来的) | 树侧 |
| `AddCloInit` | 初态 $\Omega_t+1$, `drop` 是我选的两种变体 | 树侧, 选择 |
| `AddCloNeg` | $\cdot2$, $+1$ 来自 `TLRuleVar` | 树侧 |
| `AddCloAccept` | 读旧树 `BTBOFull`, `NoCumsum` 作尺, 不读标签 | 验收 |

**时间线.** 动手前读过: `AGENTS.md`, `probes/README.md` 的翻译账, `TLRule`, `TLRuleSum`, `TLRuleSpec`, `TLRuleVar`, `TLRuleAccept`, `TLRuleDiag`, `TLRuleMain`, `TLRuleTest`, `TLEnd`, `BTBOFull`, `BTBOFullEmb`, `BTBOFullEb`, `BTBOFullV1`, `BTBOFullV3`, `CumReadCF` 开头, `Level` 的 `toLevel`. 没有打开 `EBO`, `Correspond`, `Label`, 也没有读记号的基本列. `AddCloEmb` 的分块思路受 `BTBOFullEb` 影响. 不算 "树自足": 带的尺是旧树.

## 审计

- **导入闭包** (`importclosure.py`): `OCF.Align.AddClo` 退出码 0, 禁用表 0; 加 `--only OCF.Free. --only OCF.BTBO --only OCF.Align.CumReadCF --only OCF.Align.TLRule --only OCF.Align.AddClo` 也是 0, 闭包里本地模块 12 个. `AddCloRel`, `AddCloStr`, `AddCloEmb`, `AddCloLeaf`, `AddCloInit`, `AddCloNeg` 各自 OK. 正对照 `AddCloAccept`: 退出码 1 (经 `Value`, `BTBOValNeg` 碰到 `Omega2Base`, `Stage2`), 与 `TLRuleAccept` 同.
- **定义级切片** (`depslice.py`, 块数 / 记号块 / 词命中): `AddCloRel:main` 84/0/0, `AddCloRel:Ψ≤` 114/0/0, `AddCloStr:SA-cell` 130/0/0, `AddCloEmb:emb` 57/0/0, `AddCloLeaf:upLeaf` 103/0/0, `AddCloInit:ΨI≤` 124/0/0, `AddCloInit:TopD≤1` 93/0/0, `AddCloNeg:no-clo-·2` 76/0/0, `AddCloNeg:req-·2` 142/0/0, `AddCloAccept:T-c+cω` 953/0/0, `AddCloAccept:TI≽` 871/0/0, `AddCloAccept:TD≺` 719/0/0 (验收读旧树, 不读标签). 正对照 `TLOpsAccept:label-TΩ` 1019/92/58.
- **禁用构造:** 全部 `AddClo*` 没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, `--cubical`; 全部带 `--safe --without-K --lossy-unification`.
- 闭包只保证不引用, 不说明没受记号启发; 见时间线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AddClo where

open import OCF.Align.AddCloRel public using (Rel; module Main; module Step; sum-mono; cmp-tr; SubS)
open import OCF.Align.AddCloStr public using (SA; SSt; module Cell; SSt-ω; SSt-·2; SSt-+1)
open import OCF.Align.AddCloEmb public using (Gr; emb)
open import OCF.Align.AddCloLeaf public using (module Leaf)
open import OCF.Align.AddCloInit public using (module GenI; drop; TopD≤1)
open import OCF.Align.AddCloNeg public using (Req; req-·2; req-+1; no-clo-·2; no-clo-+1; succ-spec; ω+ω<ω·ω)
```
