# TK 的值 (入口与判决): `TK` 与 `TN`, `TK` 与有损对照 `TK₀` 的 `ord` 比较

> 不含记号. 作者选定原话: "值: TK 与 TN 的 ord 比较". 本路 (前缀 `ValTK`, 单路) 是 [KindLv](KindLv.lagda.md) 接手清单第 2 条. 第 4 层: 只新增关系, 定理与一个对照闭项, 不改树, 折叠, 合法性, 不改已有文件. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延 (连前提也没有), 不用 UIP 作前提.
>
> **判决: PARTIAL. 没有无条件的 `ord` 比较.**
>
> - **`TK` 对 `TN`: 没有定理, 也没有条件定理.** 两者在三处不同: 每站求值是两份折叠 (`KindLvEv.evK` 走 `KindLvRun`, `NewTwrEv.evN` 走 `GenFoldRun`), 最终坍缩是两份折叠, 最终层差一个 $1\boxplus$ (`TN` 的层是 `one⊞ (up ΛB)`). 第 0 站的对角定义相等, 第 1 站起两个塔就不定义相等 (实验, 报错原文见下). 两份折叠 "逐行相同" 仍是判断; 层 `up ΛB` 与 `1 ⊞ up ΛB` 之间没有字面证据.
> - **`TK` 对有损对照 `TK₀` (同一坍缩, 同一塔, 只把 $\kappa_1$ 换成有损): 条件定理** `ValTKVal.TK₀≤TK : Dom lv₀ lvΛ → TK₀ ≤ᴬ TK`. 前提 `Dom l₁ l₂` 说: 两份折叠在同一个世界, 同一组输入上, 第 0 层输出被加法支配 (对一切底 $b$, $\mathrm{sum}\,b$ 的值 $\le$). `Dom` 的形状可满足 (`Dom-refl`), `Dom lv₀ lvΛ` 没有证, 没有否定. 严格 (`<`) 没有做.
> - **$\kappa_1$ 结点 (第 1 站的结点): 两种输出写成定理, 比较是条件定理.** `ValTKBase.node₀`, `nodeK` (`refl`): 有损一边是当前世界里分支输出 $c$ 的 $\omega$ 份, 按级一边是 $\sum_n\Delta_n$, $\Delta_n$ 是分支在升高的世界 $w_{n+1}$ 里的输出. `ValTKVal.node≤ : BrMono → (有损结点) ⊑ (按级结点)`, 前提 `BrMono` 是 "$c\sqsubseteq\Delta_n$ 对每个 $n$". 世界确实升高, 坐标沿第一位置攀升 (`up-w`, `climb₀`, `climb`, 定理).
>
> **对纲领与目标.** 纲领 1: 一切比较都是 `A` (布劳威尔树) 上通常的 `≤` (`TLRuleSpec._≤_`); `ordK` 按构造子把 `A` 搬到 `Ordᶜ`, 所以这就是 `ord` 的比较. 纲领 2: 无公理, 停机由检查器 (对数据结构与 ℕ 结构递归). 纲领 3: 本路的律 `Dom`, `BrMono` 比较的一对东西都带字面关系: 同一个世界, 或者 $W\le w_{n+1}$ (`qA`, 由 `rs≤` 给) 加上顶坐标的第一位置链 (`climb`); 不比较两个裸下标, 不要求判等 (判断: 不碰壁垒). 纲领 4: 导入闭包干净 (审计). 目标 "让树自足": 本路说明了 "按级回灌是否提高序数值" 卡在哪一条树侧的单调性 (折叠对世界与对级回灌的单调), 没有看记号; 但没有证出来, 所以对 "下一步的定义是否正确" 还不能用值来判断.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValTK where

import OCF.Align.ValTKBase
import OCF.Align.ValTKVal
```

## 定理表

| 名字 | 文件 | 陈述 (读法) | 档 |
|---|---|---|---|
| `lv₀`, **`TK₀`**, `Lg-TK₀`, `fghK₀` | Base §1 | 对照闭项: `ColL GΛ LdΛ flΛ Λ lΛ one⊲ lv₀`, `lv₀ = λ _ → inj₂ tt` | 构造; 合法是定理; 无条件 |
| **`lv-off`**, `lv-on₀`, `lv-onK`, `fb-κ₁` | Base §1 | `∀ κ → ¬ κ ≡ κ₁ → lvΛ κ ≡ lv₀ κ`; 在 $\kappa_1$ 处 `inj₂ tt` 对 `inj₁ K1`; 退回的 `fbA GΛ κ₁ ≡ inj₂ tt` | 定理 (`only-κ₁` 来自 `NegKindLvInst`) |
| **`Node.node₀`** | Base §2 | `N0.RKc ac (inj₁ κ₁) u q₀ lW ll A₀ w Y hz Tq ≡ N0.ω⋅ (drp (yc (N0.Run ac (u q₀ lW) ≤rf lW ll A₀ w Y) (N0.τ₀ lW)))` | 定理 (`refl`) |
| **`Node.nodeK`** | Base §2 | `NK.RKc … hz Tq ≡ nl (λ n → drp (yc (NK.κΔA ac u q₀ lW ll A₀ (c n)) (NK.τ₀ (NK.lwA (c n) , proj₂ lW))))`, `c n = NK.κcL ac K1 … n` | 定理 (`refl`) |
| `Node.top-rd₀`, `Node.top-rd` | Base §3 | 第 $n$ 格世界里 $\kappa_1$ 的顶 $\equiv$ `rd K1` 读出的值 $v_n$ | 定理 (`refl`) |
| **`Node.climb₀`**, **`Node.climb`**, `Node.up-w` | Base §3 | $\mathrm{top}_W\lhd v_0$, $v_n\lhd v_{n+1}$ (`Pr KΛc κ₁`, 在当时的世界里); $W\le w_{n+1}$ | 定理 (第一位置, 不严格) |
| `sum-mono`, `pt-mono` | Val §1 | $b\le b'\Rightarrow \mathrm{sum}\,b\,x\le\mathrm{sum}\,b'\,x$ | 定理 |
| `_⊑_`, `⊑-rf`, `⊑-tr`, `⨾⊑`, `nl⊑`, **`ω⊑nl`**, `drp⊑`, `⊑drp` | Val §1 | 加法支配; 对 `⨾`, `nl` 封闭; $(\forall n.\ c\sqsubseteq e_n)\Rightarrow \omega\cdot c\sqsubseteq\mathrm{nl}\,e$; `drp` 两向支配 | 定理 |
| `NodeCmp.BrMono`, **`NodeCmp.node≤`** | Val §2 | `BrMono → ∀ Tq → N0.RKc … hz Tq ⊑ NK.RKc … hz Tq` | **条件定理** (前提 `BrMono`) |
| `Dom`, `Dom-refl` | Val §3 | 两份折叠同一世界同一输入, 第 0 层输出被支配; 自反 | 定义; 定理 (形状可满足) |
| **`TK₀≤TK`** | Val §3 | `Dom lv₀ lvΛ → TK₀ ≤ᴬ TK` | **条件定理** (前提 `Dom lv₀ lvΛ`) |

## 前提与实例

- `TK₀≤TK` 的前提 `Dom lv₀ lvΛ`: **没有实例.** 形状可满足: `Dom-refl l : Dom l l` (两边同一个级回灌, 输出字面相同). 这只说明条件定理不是空真的形状, 不说明 `Dom lv₀ lvΛ` 成立.
- `node≤` 的前提 `BrMono`: 对实际的两份折叠没有实例. 形状可满足: 若第 $n$ 格的输出就是 $c$, `⊑-rf` (见 Val §2 末).
- `Node` 模块的参数 (`ac u q₀ lW ll A₀ w Y`): 任意; 坍缩里第一次碰到 $\kappa_1$ 结点时的实际参数由 `ColL` 的折叠给出 (起始世界里 $\kappa_1$ 的顶是 $0$, `NegKindLvInst.start-κ₁`).

## 第一个障碍

**[实验, 编译失败, 不是否定] `Dom` 不能对数据结构直接归纳.** 归纳到 $\kappa_1$ 结点 (`RKc (inj₁ κ₁) … hz`) 时, 两边的输出是 `node₀` 与 `nodeK` 的右边; 由 `ω⊑nl` 要的是 `BrMono`, 即有损一边在世界 $W$ (状态 $Y$, 前缀 $w$) 里的分支输出被按级一边在世界 `wA (c n)` (状态 `SA (c n)`, 前缀 `coA (c n)`) 里的分支输出支配. 归纳假设 `Dom` 只给同一世界, 同一状态. 实验 (scratch `valtk/ValTKTry1.agda`, 日志 `valtk/try1.log`) 把 `Dom` 直接用作 `BrMono`, 报错原文:

```text
ValTKTry1.agda:18.34-67: error: [UnequalTerms]
proj₁ W i !=
OCF.Align.KindLvRun.ClA.wA
(NK.κcL ac OCF.Align.KindLvTw.K1 u q₀ lW ll A₀ w Y n) i
of type Wd (OCF.Align.LvKtIf.Kc i)
when checking that the expression dom ac (u q₀ lW) ≤rf lW ll A₀ w Y
has type ... ⊑ FoldTy.Df.yc (NK.κΔA ac u q₀ lW ll A₀ (Node.c ac u q₀ lW ll A₀ w Y n)) ...
```

**缺的单调性 (判断, 未写成接口).** 要把 `Dom` 加强成可归纳的形状 `DomW`: 两份折叠 (`lv₀` 与 `lvΛ`), **两个世界** $W\le W'$ (只在 $\kappa_1$ 的分量上升高, 由 `rs≤` 给字面证据), **两个状态** (后者支配前者: `cv` 搬过来再接上前面各格的输出), 同一份数据族在两个世界里取值 (Ωd 的闭包分支在 $W'$ 里过的是 $g(\mathrm{top}_{W'})$, 层也变了, 所以同时要 "对层沿第一位置单调", 即 `TpMonoIf` 的 (b) 在 `KindLvRun` 上的对应). 输出在第 0 层用 `⊑`; 在第 $\ge1$ 层的目标上, 输出是带 `ni`/`nc` 结点的数据, 关系要能被以后的 `Run` 保持, 并且结点的分支对一切路径 $W\lhd V$ 比较 (`MonoPort9` §3 对 `GoodUp` 与路线 (a) 的判断: 只改输出关系不够, 输入关系也要对一切路径比分支). 这就是此前各路在单种类与两种种类折叠上都没有走通的 "跨世界的值单调" (`GoodUp`, `HtCrossV` 的异质世界), 现在多了一维: 两份折叠的级回灌不同. 没有否定定理, 写 "未走通".

**[实验, 编译失败] `TK` 的塔与 `TN` 的塔从第 1 站起不定义相等.** scratch `valtk/ValTKTry2.agda`: `KT.Bᴧ 0 ≡ NK.NT.Bᴧ 0` 用 `refl` 通过; `KT.Bᴧ 1 ≡ NK.NT.Bᴧ 1` 用 `refl` 被拒, 报错 (日志 `valtk/try2.log`, 1028 行, 摘要): `[UnequalTerms] … OCF.Align.KindLvRun.Run (Lev (hs hz)) (genLev (hs hz)) … (λ _ → inj₂ tt) … (… KindLvRun.Chn …) != … OCF.Align.GenFoldRun.Run (Lev (hs hz)) … (… GenFoldRun.Chn …) … when checking that the expression refl has type KT.Bᴧ 1 ≡ NK.NT.Bᴧ 1`. 两份折叠在链的下标 $n$ 之下卡住, 是两个不同的函数符号. 要比较 `TK` 与 `TN`, 先要 "`KindLvRun` (平凡级回灌) 与 `GenFoldRun` 计算同一个值" 这条跨实例模拟; 回灌出的世界 (`κc₁` 读 `rd₁`, `κcA` 读 `sum`) 在两份里只互模拟不相等, 所以它也撞上面的异质世界 (判断; `KindLv` 接手清单第 4 条).

## 界与读法 (全部是判断)

| 对象 | 界 (判断) | 依据, 测到哪里 |
|---|---|---|
| `TK₀` 对 `TK` | `TK₀` $\le$ `TK` (**条件定理**, 前提 `Dom lv₀ lvΛ`); 严格: 判断成立, 没有定理 | `TK₀≤TK`; 严格的判断来自 `climb` (按级一边的坐标在攀升) 与 `node₀`/`nodeK` 的形状 |
| `TK₀` 与 `TN` | 同一读法 (判断): 两者的最终坍缩里一切闭包结点都有损 (`lv-off`, `fb-κ₁`, `NewTwrK.lossy-rd`), 塔的式子相同, 差在折叠的两份拷贝与层的 $1\boxplus$; 没有定理 | 上一节第二条实验; NewTwr 的读法表 |
| 下界 (三者) | 不低于第 0 站的层 $2$ 的坍缩, 读 $\psi_0(\Omega_2)$ (判断) | 第 0 站的对角定义相等 (`st0` 实验通过); $\psi_0(\Omega_2)$ 是层号的读法, 没有序数值验收 |
| 上界 (三者) | 低于 $\psi_0(\Omega_\Omega)$ (判断) | 第 0 层目标下, 除 $\kappa_1$ 外的闭包结点都在当前世界的顶上取分支, `TK₀` 的折叠不升世界 (判断, 对折叠全程的不变式没写), 顶都是底坐标 (`NewTwrK.base-bot`, `NegKindLvInst.start-κ₁`); $\kappa_1$ 在攀升的 $v_n$ 上取分支, 而 $v_n$ 嵌进层后它自己的 $\Omega$-结点又都有损. 所以有效的层是一个可数的树, 读 $\psi_0(\Omega_\alpha)$, $\alpha<\Omega$. 这一条只是上界, 不是精确值; NewTwr 对 `TN` 的更细的读法 ($\alpha$ 是 $\omega^k$ 量级) 是那一路的判断, 本路没有复核 |
| `TK` 比 `TK₀` 多出的量 | 只在 $\kappa_1$ 的结点: 有效层里 $g(\mathrm{top})$ 换成 $g(v_\omega)$ 的可数影子 (判断); 不改上界的档 | 同上; `KindLv` 的读法 "`TK` 与 `TN` 同量级" 与此一致 |

## 翻译账

本路不读记号.

| 新增 | 来源 | 读自记号 / 树逼出 / 脚手架 |
|---|---|---|
| `lv₀`, `TK₀` | 任务: "把 $\kappa_1$ 换成有损的同一折叠" | 验收用的对照闭项 (第 4 层), 不进成品 |
| `_⊑_` (加法支配) | 第 0 层数据经 `sum` 读成 `A`, 输出接在底的右边 (`sum` 的字面) | 树逼出 |
| `ω⊑nl` | 有损行 `ω⋅` 与按级行 `nl` 的字面 (`node₀`, `nodeK`) | 树逼出 |
| `Dom`, `BrMono` | 两份折叠只在 `lv` 不同; 结点那一行的字面 | 树逼出 (律的定义域: 同一世界, 或带 `qA`/`climb` 证据的一对世界) |

归类 (判断): 提供信息. 没有新构造子或节点字段, 不改树、折叠、合法性, 不用 `Lab`, 没有记号. 这一站新用到的字段: `KLv.rd-fst` (攀升), `KLv.rs≤` (世界升高), `KindLvRun.RKv` 的两支. 信息是: "按级回灌提高 `ord`" 归结为两份折叠之间的跨世界值单调; 局部 (一个结点) 的比较由第 0 层的加法支配给出, 整体卡在同一个障碍上. 第 4 层没有逼出改前 3 层.

## 审计

- **编译.** 三个模块 `OCF.Align.ValTKBase`, `ValTKVal`, `ValTK`: 删自己的 `.agdai` (逐个写精确路径) 后从入口编译, 依赖用共享接口: `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/ValTK.lagda.md +RTS -M6G -RTS`, 退出码 0, 约 4.1 秒, 峰值常驻约 0.76G.
- **实验** (scratch, 不在仓库): `valtk/ValTKTry1.agda` 退出码 42 (预期的 `UnequalTerms`), `valtk/ValTKTry2.agda` 退出码 42 (`st1` 被拒; `st0` 在同一文件里先于 `st1`, 单独没有出错).
- **导入闭包**: `importclosure.py OCF.Align.ValTK` (不加 `--only`): 退出码 0, 闭包 115 个模块 (本地 101, 库 14), 禁用表命中 0. 闭包经 `NegKindLvInst` (`only-κ₁`) 带进否定一路的若干模块, 只导入一个引理.
- **禁用构造**: 三个文件的代码块里没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, 函数外延, UIP 前提.

## 文件

| 文件 | 内容 |
|---|---|
| `ValTKBase` | 对照闭项 `TK₀`; `lv-off`; $\kappa_1$ 结点的两种输出 (`node₀`, `nodeK`); 坐标攀升 (`climb₀`, `climb`, `top-rd`, `up-w`) |
| `ValTKVal` | 加法支配 `⊑` 与它的封闭性; `ω⊑nl`; `node≤` (条件); `Dom`, `Dom-refl`, `TK₀≤TK` (条件) |
| `ValTK` | 入口 (本文件) |

## 接手清单

1. **`DomW`: 两份折叠的跨世界值单调.** 先把接口写成记录 (只增不改): 两个世界带 `_≤w_` 证据, 两个状态带支配证据, 数据族在两个世界里取值; 律的定义域逐条写. 先只对 "闭包结点只有 $\kappa_1$ 与有损种类" 的数据 (`ColL` 的实际数据, 由 `lv-off` 与 `NewTwrK.lossy-rd`) 做, 第 0 层输出用 `⊑`. 配对派否定一路, 对准 "第 $\ge1$ 层目标上的输出关系" (那是 `GoodUp` 卡住的地方). 有了 `DomW`, `Dom lv₀ lvΛ` 是它在 $W'=W$ 的特例, `TK₀≤TK` 无条件.
2. **严格.** `TK₀ < TK` 要在某一个 $\kappa_1$ 结点上严格: 先在最外层第一次碰到 $\kappa_1$ 的结点上, 证 $\Delta_0$ 严格支配 $c$ (起始世界里顶是 $0$, $v_0$ 是 `readL 1` 读出的高度; 需要 "层沿第一位置严格单调", `TpMonoIf` (b) 的严格版在 `KindLvRun` 上的对应).
3. **`TK` 对 `TN`.** 先要 "`KindLvRun` (平凡级回灌) 与 `GenFoldRun` 算同一个值" (跨实例模拟; `KindLv` 接手清单第 4 条), 再要层 `up ΛB` 对 `1 ⊞ up ΛB` 的值比较 (两者之间没有字面第一位置, 不在任何已有律的定义域里). 两步都没做.
4. **上界的不变式.** "`TK₀` 的折叠不升世界, 一切闭包结点在底坐标上取分支" 现在是判断; 可以写成对折叠全程的不变式 (只用 `lv-off`, `lossy-rd`), 这是上界判断的第一环.
