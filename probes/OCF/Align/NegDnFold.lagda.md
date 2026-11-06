# 有内容的下降: 否定一路的入口

> 不含记号. 本路是 `DnFold` (构造一路) 的配对**否定**一路 (手册 §5.2), 前缀 `NegDnFold`. 对着接口 [DnFoldIf](DnFoldIf.lagda.md) ("接口定稿 2026-11-05 16:13 (首次编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 分篇: [NegDnFoldRet](NegDnFoldRet.lagda.md) (可取回的下降, 嫌疑 iv), [NegDnFoldBlind](NegDnFoldBlind.lagda.md) (忠实的盲区, 嫌疑 ii, iii), [NegDnFoldAdm](NegDnFoldAdm.lagda.md) (裸可入判定与桥), [NegDnFoldCopy](NegDnFoldCopy.lagda.md) (同一种类的两份拷贝, 嫌疑 i). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延 `FEA` 只在 `NegDnFoldAdm` 的两条条件定理里作前提.
>
> **判决: 接口没有被否定; 接口的忠实律被一个常数输出的下降满足 (反模型, 定理).** 四个嫌疑:
>
> 1. **嫌疑 (iv) 成立于强读法, 不成立于接口的读法 (定理).** "从下降后的 `Ht` 取回读回" (下降有左逆) 在第 $s+1$ 站 ($s\ge0$) 的级上不可能, 对一切下降 (`NegDnFoldRet.TwB.no-faithfulB`, 由 `no-retract`: 这些级里有坐标为 `Ht` 的种类). 第 0 站可以 (`ret0`). 可取回推出接口的 `FaithRd` (`ret→faith`), 反方向不成立 (下一条).
> 2. **嫌疑 (ii) 后半被推翻 (定理, 反模型).** 有损下降 `DnSq T` 对一切 `T` 有满足 `FaithRd` 的实例 `dsqC`, 它把一切压成有限高度 (`sqC-fin`). 所以 "D2 使忠实不可能" 不成立; 前半 "压回统一形状" 在接口的律内只能说到 `sq-new` 本身 (判断).
> 3. **嫌疑 (iii): 接口不排除, 也不强迫 (定理 + 判断).** 塔上的下降 `dnC` 满足 `Faith0`, `FaithTower`, `DiffTkc`, 而**每一站的回灌输出都是 $2$** (`HsC`). 所以 "第 2 站起为常数" 与接口的全部忠实律相容. 没有编译出 "求值下降必为常数" 的否定 (`DnEv` 是任意函数, 不读世界的结点证据, `no-unifΩ`, `code-botK` 落不到它的律上; 判断).
> 4. **嫌疑 (i) 不落在接口上, 落在逐种类搬合法性的写法上 (定理 + 判断).** 第 1 站读回所在的级 `Lev X₀` 里, `Ht` 的底种类有两份拷贝, 没有世界映射同时保两份的界 (`NegDnFoldCopy.no-wmatch₀`, 两半各自可满足). 接口的 `DnEv` 翻译是任意函数, 不搬世界, 不需要它; `EvSys` 没有对一切种类结构的比较律.
> 5. **接口 §6 的裸判定 (定理; 条件到 WLPO).** `ExactAdm` 在底分量为 $\omega$ 的世界里推出分离子, 对一切站 (`exactKc-sep`; `FEA` 下 `exactKc→WLPO`). "保留可入分支且种类下标不变" 的桥 `RestrK` 与裸判定等价 (`Keep.keep→dec`, `Keep.dec→keep`), 所以在层号在 `Ht` 的层上撞分离子 (`keepS₁-sep`).
>
> **对纲领与目标.** 纲领 3 (壁垒): 本路推出 WLPO 的只有裸判定 (`ExactAdm`, 带等价的桥), 都是条件定理, 条件 `FEA`; 带公共上界的判定 (`BDecK`) 不受影响. 纲领 1: 本路的定理对 `HB`/`Lev`/`Ht`, 反模型 `dnC` 代入 `KD` 得到一棵合法的闭项 (`KC.TΛ∞ω`), 但它的回灌输出是常数, 没有值的意义. 目标 "让树自足": 第 1 条给出一条树侧判据 (级里有坐标为 `Ht` 的种类 ⇒ 到 `Ht` 的下降不可取回; `Tw` 是沿构造子的一条路, 对一切站一条定理); 第 3 条说明接口的忠实不是判据 (手册 §3.3).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegDnFold where

import OCF.Align.NegDnFoldRet
import OCF.Align.NegDnFoldBlind
import OCF.Align.NegDnFoldAdm
import OCF.Align.NegDnFoldCopy
```

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| **`no-faithful`** | Ret §1 | 级有坐标类型为 `Ht` 的种类 ⇒ 任何 `HB S → Ht` 无左逆 | 定理 (否定) |
| `Tw`, `hasTw`, `tw⊞`, `twι`, `TwB.twB`, `TwB.hasB` | Ret §2 | 一切下降的塔, 一切 $s$: `Lev (B (s+1))` 有这样的种类 | 定理 |
| **`TwB.no-faithfulB`** | Ret §2 | 第 $s+1$ 站的下降 (`FaithTower` 说的那个) 无左逆, 一切 `DnTower`, `DnLim`, $s$ | 定理 (否定) |
| `top≢cut`, **`ret→faith`** | Ret §3 | 可取回 ⇒ `FaithRd` | 定理 |
| `ret0` | Ret §4 | 第 0 站可取回 (对照) | 定理 |
| `sqC`, `sqC-fin`, `lgC`, **`dsqC`** | Blind §1 | 一切 `T` 的 `DnSq` 实例, 输出只有有限高度 | 定理 (构造) |
| **`cheapFaith`**, `top↦2`, `cut↦1` | Blind §1 | 它满足 `FaithRd` | 定理 (反模型) |
| `dC`, `dnC`, `dnLC`, **`faith0C`**, **`faithTC`**, **`HsC`**, **`diffC`** | Blind §2 | 塔上: `Faith0`, `FaithTower`, `DiffTkc` 都成立, 每站回灌输出都是 $2$ | 定理 (反模型) |
| `evC`, `evTC` | Blind §3 | `DnEv`, `DnEvTower` 的常数实例 (接口自述) | 定理 (前提实例) |
| **`exact-sep`**, `exactS₁-sep`, **`exactKc-sep`** | Adm §1 | 裸判定 ⇒ 分离子 (底, `Ht` 的层, 一切站) | 定理 (否定) |
| `exact→WLPO`, **`exactKc→WLPO`** | Adm §1 | 同上 ⇒ WLPO | 条件 (`FEA`) |
| `exStep`, `exSup`, `exKc`, `wω`, `lwω`, `wtωN`, `baseω` | Adm §1 | 传递; 前提的世界塔合法 | 定理 |
| **`Keep.keep→dec`**, **`Keep.dec→keep`**, `restr→dec` | Adm §2 | 保留可入分支且下标不变的桥 ⇔ 裸判定 | 定理 |
| **`keepS₁-sep`** / `keepS₁→WLPO` | Adm §2 | 层号在 `Ht` 的层上, 外层 $\omega$: 这样的桥 ⇒ 分离子 / WLPO | 定理 (否定) / 条件 (`FEA`) |
| `dec0`, `keep0`, `lgω₁` | Adm §2 | 前提实例 (外层世界 $0$; $(\omega,0)$ 合法) | 定理 |
| `X₀-is`, `k1`, `k2`, **`no-wmatch₀`**, `sat1`, `sat2` | Copy | 第 1 站读回级里底种类的两份拷贝不能同时保界; 两半可满足 | 定理 (否定) |

## 每条律为什么是构造一路需要的

- **`FaithRd`, `FaithTower`, `Faith0`, `DiffTkc`** (接口 §5 原文): 构造一路要用它们说 "读回进了闭项" (`KcFold` 第一个障碍: 无条件闭项的下降是常数). 本路的反模型 `dnC` 满足全部四条而每站输出是常数 $2$, 所以这些律不能承担这个说法.
- **可取回** (左逆): 不在接口里; 嫌疑 (iv) 原话 "从下降后的 Ht 取回读回". 若把 "忠实" 读成可取回, 就是这一条, 它在第 1 站起不可能.
- **`DnSq`** (接口 §4 原文, D2): 嫌疑 (ii) "D2 使忠实不可能" 对着它; 反模型 `dsqC` 是它的实例.
- **`ExactAdm`, `RestrK`** (接口 §6 原文): `KcFold` 接手清单第 1 条要把 `LvOm` 推广到 `LvH` (接口 §1), 读回从 `Lev c` 进 `LvW a c` 就是 `RestrK`; 逐结点保留可入分支要 `ExactAdm`.
- **世界映射保两份拷贝的界** (`no-wmatch₀`): 不在接口里; 逐种类把第 1 站读回级的高度翻译进 `Ht` 的数据树并搬运合法性时要它 (`LvRdEmb.Emb` 的 `π`, `bd→`, `bd←` 的形状).

## 前提实例

- `no-faithful`: `HasHt` 有实例 `TwB.hasB s` (一切站), `has 2` 的情形就是 `t2`. 对照 `ret0`: 第 0 站可取回.
- `exact-sep` 等: 前提经典地可满足 (判断); 世界 `wω s` 合法 (`lwω`) 且是 `WTower` (`wtωN`). `KeepIdx` 有实例 `keep0` (外层世界 $0$). `FEA` 在 Agda 里证不出也否证不了.
- `no-wmatch₀`: 两半 `sat1`, `sat2`.
- 接口记录: `DnSq` (`dsqC`), `DnEv`/`DnEvTower` (`evC`, `evTC`), `FaithTower`, `Faith0`, `DiffTkc` (`faithTC`, `faith0C`, `diffC`). 所以接口的条件不空.

## 只否定什么, 不否定什么

- **否定** (编译的): 第 $s+1$ 站 (一切 $s$) 的下降有左逆; 一切含坐标为 `Ht` 的种类的级上的下降有左逆; 裸可入判定 `ExactAdm` 在底分量为 $\omega$ 的世界里 (分离子; `FEA` 下 WLPO); 保留可入分支且种类下标不变的 `RestrK` 分量 (同上); 第 1 站读回级的世界折进 `Ht` 的一个世界而两份底种类拷贝同时保界. 反模型否定的推断: "满足 `FaithRd`/`FaithTower`/`DiffTkc` 就说明读回有内容地进了闭项".
- **不否定**: 接口的任何记录或定义 (都有实例); 有损下降与求值下降能有内容 (值的问题, 本路没有值定理); 带公共上界的判定 (`BDecK`); 只走底支或常数的 `RestrK`; 对角方向的世界 `Wd₂ → Wd (Lev X₀)`. 路线状态: 本路**没有关闭任何路线**.

## 判断 (单列)

- **D1 (`DnEv`) 的值.** 翻译是任意函数, 数据树不带合法性, 所以接口不约束求值下降看见多少分支. 要说它有内容, 须有值的陈述; 本路没找到 D1 必为常数的否定. `no-unifΩ`/`code-botK` 约束的是**结点位置**的证据与基世界里的码, `DnEv` 的 `tr` 若把高度坐标的 $\Omega$-结点翻成闭包 (`nκ`, `nμ`) 则不经过它们; 但 `D` 的闭包只有 `A` 与 `H₀` 两种坐标, 坐标为 `HB (Lev X s)` 的结点只能压成可数的组合 (判断: 这时 D1 在这一处退化为 D2 的形状).
- **更强的忠实.** "下降对新种类结点的每个坐标的分支有反应" 对 D2 不可能 (`sq-new` 只看 `cs`, 这是定义); 对 D1 开放. 要排除 `dnC` 这类实例, 建议把忠实写成值的陈述 (`Hs s` 在 `ord` 下的界), 这是构造一路的事.

## 审计


- **编译.** 五个模块 `OCF.Align.NegDnFoldRet`, `OCF.Align.NegDnFoldBlind`, `OCF.Align.NegDnFoldAdm`, `OCF.Align.NegDnFoldCopy`, `OCF.Align.NegDnFold` 首次编译 (依赖用共享接口), `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/<文件> +RTS -M6G -RTS`, 退出码 0, 峰值常驻约 0.65G.
- **导入闭包** (`importclosure.py`, 不加 `--only`): 五个模块都退出码 0, 禁用表命中 0.
- **定义级切片** (`depslice.py`, 到达块 / 记号模块块 / 别处记号词; `--html` 由导入本入口与 `Om1HnAccept` 的 scratch 模块生成, 退出码 0): `no-faithful` 67/0/0, `no-faithfulB` 213/0/0, `ret→faith` 67/0/0, `dsqC` 61/0/0, `cheapFaith` 69/0/0, `faithTC` 208/0/0, `HsC` 145/0/0, `diffC` 157/0/0, `exactKc-sep` 136/0/0, `exactKc→WLPO` 140/0/0, `keepS₁-sep` 100/0/0, `no-wmatch₀` 200/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 切片看不见模块应用的实参: `HsC`, `diffC` 经 `KC = KD dnC dnLC`, 实参 `dnC`, `dnLC` 在本文件里, 已在 `faithTC` 的切片里到达.
- **禁用构造**: 五个文件没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`; 函数外延 `FEA` 只作 `exact→WLPO`, `exactKc→WLPO`, `keepS₁→WLPO` 的前提; 没有 UIP 前提.

## 文件与行数

| 文件 | 代码行 / 总行 | 内容 |
|---|---|---|
| `NegDnFoldRet` | 71 / 132 | 可取回的下降不存在; 可取回 ⇒ `FaithRd`; 第 0 站对照 |
| `NegDnFoldBlind` | 72 / 129 | 常数输出的反模型满足全部忠实律 |
| `NegDnFoldAdm` | 114 / 184 | 裸判定的分离子; 桥 ⇔ 裸判定 |
| `NegDnFoldCopy` | 45 / 83 | 第 1 站读回级里两份拷贝的界 |
| `NegDnFold` | 6 / 本文件 | 入口 |
