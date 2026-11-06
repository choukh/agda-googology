# 层号换类型: 否定一路的入口

> 不含记号. 作者此前选定的方向原话: "A3: 读回包 + 第 ω+1 级折叠"; 本路是续作 "层号换类型" 的**否定**一路, 与构造一路 `LvKt*` 配对 (手册 §5.2). 对着接口 [LvKtIf](LvKtIf.lagda.md) ("接口定稿 2026-11-05 15:21 (首次编译通过)", 变更记录: 无) 写, 导入它 (与它依赖的 [LvKtCode](LvKtCode.lagda.md)), 不另造接口. 分篇: [NegLvKtTrap](NegLvKtTrap.lagda.md) (分量的陷阱, 对角, 新站的层号, 出口, 前提实例), [NegLvKtCopy](NegLvKtCopy.lagda.md) (拷贝的界, 基世界只见底支, 不封口). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> **判决: 接口没有被否定.** `FoldAtK`, `FoldTower`, `FoldLimK` 有依赖输入的实例 (`foldSlot`, `towerSlot`, `limSlot`); 嵌入与读回注入是分量注入, 不要判定; 没有找到要求三歧或裸判定的律 (不撞壁垒). 编译过的否定都落在接口之外的**写法**上, 各自写明只否定什么. 对构造一路最有用的三条:
>
> 1. **对角不能是各站层号的注入列 (定理, `diag-trap`).** 极限站的层号列若取 `ιΛ s (B s)`, ℕ-极限合法就推出**每一站的层号都没有 $\Omega$-结点** (读法: 都是可数的小层号, 判断). 出口: 部分和 (`LvTop.cum` 的形状) 合法, 且不纯于任何一站 (`Lg-ΛΛ`, `mixed`): 对角在类型上**没有**被困在某一站. 代价 (玩具实例上的定理): 第 $s+1$ 站的增量不是对角的字面第一位置 (`stage-not-below`); "对角越过每一站" 只能是值的定理, 不能由字面第一位置给出.
> 2. **新站与 $\Omega$-结点层号上的 "两个第一位置" (定理, `no-two-nxt`, `no-two-Ω`).** 一切并里, 一个合法高度在一个合法世界里不能同时以两个不同分量注入的、都含 $\Omega$-结点的高度为第一位置 (`Trap.no-two`). 所以新层号不能同时以 `emb (B s)` 与 `injL c r` 为字面第一位置 (只能 `emb (B s) ⊞ injL c r` 那样接在后面); $\Omega$-结点码目标上的读回不能同时以两个坐标的分支读回 (各自注入) 为字面第一位置.
> 3. **拷贝与基世界 (定理).** 嵌入的种类与原件在 `KΛc` 的合法世界里界互不相干 (`no-emb→`, `no-emb←`, `no-routeΛ`); 站内 `emb` 的拷贝与 `Lev hz` 的拷贝也是 (`no-copy→`, `no-copy←`). 外层世界取码的基世界 `w0` 时, 码只走每个 $\Omega$-结点的底支 (`code-botK`, `code-botΛ`, `LvOmNeg.only0` 推广到一切站与极限).
>
> **对纲领与目标.** 纲领 3 (壁垒): 本路没有推出 LPO/WLPO 的定理; 接口只有码 (数据) 的判等, 本路找到的墙都是 "构造子与分量" 的形状 (陷阱, 拷贝), 不是三歧. 纲领 1: 闭项仍是 `A` 的元素. 目标 "让树自足": 否定都写成对一切并 (`Trap`) 或对一切站 (`only-botK`) 的一条定理, 说出了 "层号换类型" 的一条树侧判据: **跨站与跨坐标的增长只能由 ⊞ 接在后面, 不能由分量注入的字面第一位置给出; 由此得到的 "越过每一站" 是值的命题.**

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegLvKt where

open import OCF.Align.NegLvKtTrap public
open import OCF.Align.NegLvKtCopy public
```

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `OmFree`, `Trap.Pure`, `pure-ι`, `pure⊲`, `two-pure`, `free-ι` | Trap §1 | 无 $\Omega$-结点; 纯于一个分量; 注入纯, 第一位置保纯 | 定义; 定理 |
| **`Trap.trap`** | Trap §1 | 一切并: 分量 $i$ 的注入是分量 $j\ne i$ 的注入的第一位置 ⇒ 前者无 $\Omega$-结点 | 定理 (否定) |
| **`Trap.no-two`** | Trap §1 | 合法高度在合法世界里不以两个不同分量的含 $\Omega$-结点的注入同时为第一位置 | 定理 (否定) |
| **`diag-trap`**, `diag-illegal` | Trap §2 | 各站层号的注入列合法 ⇒ 每站层号无 $\Omega$-结点; `ωK` 的注入列不合法 | 定理 (否定) |
| `Lg-finDiag` | Trap §2 | 有限层号的注入列合法 | 定理 (前提实例) |
| **`no-two-nxt`**, `satEmb`, `lg-satEmb` | Trap §3 | `nxt` 里 `emb x` 与 `injL c r` 不同为第一位置 (除非一个无 $\Omega$-结点); 一半可满足 | 定理 (否定; 前提实例) |
| **`no-two-Ω`** | Trap §4 | $\Omega$-结点层号的级里两个坐标的分支读回不同为第一位置 | 定理 (否定) |
| `cumΛ`, **`Lg-ΛΛ`**, **`mixed`**, **`stage-not-below`**, `stage0-below` | Trap §5 | 部分和对角合法, 不纯于任一站; 第 $s+1$ 站增量不是它的第一位置 (玩具实例) | 定理 (出口 + 否定) |
| **`foldSlot`**, `towerSlot`, `limSlot` | Trap §6 | 接口记录有依赖输入的实例 | 定理 (前提实例) |
| **`no-emb→`**, `no-emb←`, **`no-routeΛ`**, `no-routeΛ←` | Copy §1 | `KΛc` 里种类与它的嵌入拷贝的界互不相干; 经任何种类读不通 | 定理 (否定) |
| **`no-copy→`**, `no-copy←` | Copy §1 | `Kc 1` 里 `emb` 拷贝与 `Lev hz` 拷贝的界互不相干 | 定理 (否定) |
| `sat0`, `sat1`, `satE`, `satL` | Copy §1 | 各半可满足 | 定理 (前提实例) |
| `only-botLev`, **`only-botK`**, **`only-botΛ`**, **`code-botK`**, **`code-botΛ`**, `sees1` | Copy §2 | 基世界 `w0` 里只有最小坐标; 码只走底支; 世界变大看得见别的坐标 | 定理 (否定; 对照) |
| `no-closeΛ`, `no-closeNxt`, `no-faithfulK` | Copy §3 | 不封口; 读法无左逆 (一切 `S`) | 定理 (否定, `no-retract` 的实例) |

## 每条律为什么是构造一路需要的

- **`diag-trap`**: 接口文件头 "对角在 `KΛc` 里另写一列 (`Bᴧ`), 相邻项同在 `HB KΛc` 里". 各站的层号 `B s : HB (Kc s)` 只能经 `ιΛ s` 进 `KΛc`; 直接取 `Bᴧ s = ιΛ s (B s)` 是最直接的一列. 判断: 构造一路若照 `LvTop` 用部分和, 不撞 (`Lg-ΛΛ`); 但那时对角的部分和不是各站层号的拷贝, 两者之间的关系只能用值说 (`stage-not-below`).
- **`no-two-nxt`**: 接口 "读回进新站: `injL c` ... 原样成为第 $s+1$ 站层号所在类型里的高度" 与 "塔只说 `emb (B s) ⊲[ w ] B (s+1)`". 新层号若要同时 "装着" 旧层号与读回 (各自作字面第一位置), 就撞这一条.
- **`no-two-Ω`**: 码目标是 $\Omega$-结点时槽类型 `HB (Lev (tgt c))` 是对坐标的并; "读回汇集各坐标分支的读回" 的写法撞这一条 (主审转告的嫌疑: 槽类型不带外层世界; 见下 "判断").
- **`no-emb`, `no-copy`, `no-routeΛ`**: 极限站在 `KΛc` 的世界里折叠 (`FoldLimK`), 各站在 `Kc s` 的世界里折叠; 若极限站的世界要逐站限制回各站的世界并与 `emb` 相干 (第 $s$ 站的种类与第 $s+1$ 站里它的嵌入拷贝同界), 对一切合法世界不成立. 站内: 读回 `injL c r` 里的底种类与 `emb` 那边的底种类是两份拷贝.
- **`code-botK`, `code-botΛ`**: 接口把外层世界 $a$ 作 `FoldAtK` 的输入 (`LvTopIf` 固定为 `A` 的 $0$). 若塔照 `LvTop` 取码的基世界 `w0`, 码看不见任何 $\Omega$-结点的非底支 (主审转告的 `LvOm` 嫌疑: 外层世界须随折叠长高). [只读观察, 不是接口] 构造一路的 [LvKtTower](LvKtTower.lagda.md) `rtTop`, `HTop` 确实取 `a = w0 ck`, 世界取全 $0$ (`w₀K`); 所以塔里每一次折叠调用都落在 `code-botK` (各站) 或 `code-botΛ` (极限站 `Lim`) 的前提上: 码只走底支, 层号的 $\Omega$-结构只能经顶码的目标 (界本身) 进入折叠.
- **`no-closeΛ`, `no-closeNxt`, `no-faithfulK`**: 嫌疑 (i) 的检查: 回灌输出作新层号若要忠实 (可读回), 或下一站要以本站自身为坐标, 撞 `no-retract`. 接口不要求这些 (文件头 "`no-retract` 与壁垒 (检查)"), 所以只是确认.

## 前提实例

- `Trap.trap`: 前提 (不同分量的注入是第一位置) 有实例 `step-fin` (无 $\Omega$-结点的有限高度, 与结论相容). `no-two`: 前提的每一半有实例 (`satEmb`, `lg-satEmb`).
- `diag-trap`: `Lg-finDiag` 满足前提; `ωK` 的列不满足 (`diag-illegal`).
- `no-two-nxt`: 一半 `satEmb`, `lg-satEmb` (合法, 含 $\Omega$-结点).
- `no-emb`, `no-copy`: 各半 `sat0`, `sat1`, `satE`, `satL`, 世界 `wX`, `wY`, `wE1`, `wL1` 合法 (`lgX`, `lgY`, `lgE1`, `lgL1`).
- `code-botK`: 每站的 `w0 (ckc s)` 合法 (`lw0`); 码有居留 (顶码 `Codes.top`).
- 接口前提 `FoldTower`, `FoldLimK`: `towerSlot`, `limSlot` (所以构造一路的条件定理不空真; 但实例不说明值).

## 只否定什么, 不否定什么

- **否定** (编译的): 注入列作对角而层号含 $\Omega$-结点; 两个不同分量的含 $\Omega$-结点的注入同为一个合法高度的第一位置 (一切并; 特例: 新站的 `emb`/`injL`, $\Omega$-结点层号的两个坐标, 极限的两站); 玩具部分和对角以后站增量为字面第一位置; 一切合法 `KΛc` 世界里种类与嵌入拷贝同界; `Kc 1` 里两份底种类拷贝同界; 基世界 `w0` 里码走非底支; 不封口与读法忠实.
- **不否定**: 接口的任何记录与定义; 部分和写法的对角 (合法, 跨站, `mixed`); 新层号 `emb (B s) ⊞ injL c r`; 由塔构造的相干世界 (对特定世界, 不是对一切合法世界); 变大的外层世界; 值的比较 (对角的值不低于每站的值). 路线状态: 本路**没有关闭任何路线**.

## 判断 (单列)

- **主审转告的嫌疑 (槽类型 `Lev (tgt c)` 不带外层世界, 撞 `no-unifΩ`/`no-unif-ΩA`).** 没有推出 "`FoldTower` 只有平凡实例" 的定理, 也不认为推得出: 接口的律只要求输出合法 (`LgB` 对 `Lev (tgt c)` 自己的一切世界), 外层世界 $a$ 是 `FoldAtK` 的输入, 实例可以读它 (`foldSlot` 读输入世界的槽). `no-unifΩ` 落在折叠内部把层的结点翻译回低层时的层证据 (实现), 不在接口的类型上. 编译的相关结论只有三条: 外层世界取 `w0` 时码只走底支 (`code-botK`); 读回不能以两个坐标的分支读回同为字面第一位置 (`no-two-Ω`); 对裸坐标判定可入推出分离子/WLPO (已有, `NegLvRdLay.decAcc-sep`, `decAcc→WLPO`). `LvOm` 的带世界的层结构 `Lv a c` 的读回能否搬进 `HB (Lev c)` (种类 $(x,e)\mapsto x$, 但 `Lv` 在极限处多一层 `step`) 没有写; 那是这条嫌疑的决定性实验.
- **嫌疑 (iii) `HtTowerU` 停在哪里.** `HtTowerU` 停在 "没有折叠" (`HtTower` 第一个障碍 1 (iv): `Lev` 内部生成的种类没有指定读回层, 与 `U` 的低分量种类不是字面相同的). 这次 `nxt` 的 `Lev c` 分量同样含内部拷贝 (`no-copy`), 接口把这件事交给前提 `FoldTower`; 所以同一个问题从 "类型" 移到了 "实例". 对角这次没有重蹈 `no-naive-diag` 的条件是用部分和 (`diag-trap` 是它的一般化).
- **构造一路的塔 (只读观察).** `LvKtTower` 的写法正是本路的出口: 新层号 `B (s+1) = emb (B s) ⊞ injL (B s) (…)` (不撞 `no-two-nxt`), 对角 `Bᴧ (s+1) = Bᴧ s ⊞ ιΛ (s+1) (inc s)` (部分和, 不撞 `diag-trap`). 本路的玩具 `cumΛ` 就是 `Bᴧ` 的形状 (起点 `δ 0`, 增量 `δ (s+1)`), 所以 `stage-not-below` 说: 在这种形状下, 后站的增量一般不是 `ΛB` 的字面第一位置.
- **嫌疑 (iv) 对角的层号是否越过每一站.** 类型上没有被困 (`mixed`: 部分和用到每一站的种类). 字面上不越过 (`stage-not-below`, 玩具实例). 所以 "越过" 只能是值的定理, 本路没有值的结论.
- 读法 (判断): `diag-trap` 的结论 "每站层号无 $\Omega$-结点" 读作各站层号都是可数序数, 注入列的对角作下标仍可数, 闭项读法 $<\psi_0(\Omega_\Omega)$, 远低于 ψ₀Λ. 只是读法.

## 审计

- **编译.** 删本路 3 个模块的 `.agdai` (精确模块名 `OCF.Align.NegLvKt`, `OCF.Align.NegLvKtTrap`, `OCF.Align.NegLvKtCopy`), 依赖用共享接口, `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/NegLvKt.lagda.md +RTS -M6G -RTS`; 退出码见交回报告.
- **导入闭包与定义级切片**: 见交回报告.
- **禁用构造**: 三个文件没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, 函数外延, UIP 前提.
