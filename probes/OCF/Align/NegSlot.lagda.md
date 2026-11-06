# 高度坐标的共享槽, 否定一路: 入口与判决

> 不含记号. 本路 (前缀 `NegSlot`) 是否定一路, 与构造一路 `Slot` 配对, 共用接口 [SlotIf](SlotIf.lagda.md) ("接口定稿 2026-11-05 20:03 (首次编译通过)", 变更记录: 无). 作者本轮选定 (原话): "高度坐标的共享槽小实验". 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延 (本路没有条件定理).
>
> **判决.**
>
> 1. **坐标类型随级变的一族 `κHc` 没有共享槽 (定理).** `NegSlotWall.no-slot-κHc : ¬ Slot K₁ tp₁ H₀ κHc Q tq κ₀`, 对任意 $Q$, `tq`, $\kappa_0$, 无别的前提. 原因 (`SL.slot-ret`, 对一切 `T`): 一个 `Slot` 让每个可达成员的坐标类型成为每个别的成员的坐标类型的收缩; 相邻两级 (`HB (Lev (hs c))` 与 `HB (Lev c)`) 撞 `no-retract`. 只含原卡点的 `κH f = κHc (jx f)` 一族时, 加上高一级成员 $f^+$ 的 `RsK` 与一个世界 (给可达性) 同样矛盾 (`no-slot-κH`); 任一族含 `κHc c`, `κHc (hs c)` 同理 (`no-slot-pair`).
> 2. **不经接口的两条 (接口定稿前, 定理).** `NegSlotPre.slot-wall`/`slot-coordK₁`: 若槽是 `K₁` 某个坐标类型的收缩, 就有一份 `κc c′` ($c'$ 显式) 不能经它膨胀地来回. `NegSlotPre.no-forget`/`K1.no-forgetK₁`/`K1.no-forget-jx`: 相邻两级的拷贝, 高的那份能精确置值, 低的那份 `rs≤`, 且升低的那份后高的那份的顶只依赖 $v$ ("忘"), 则矛盾; 对任意世界证据 $P$. 关键引理 `no-inflate` 加强 `no-retract` ($x\lhd u(d\,x)$ 也不行).
> 3. **构造一路的实例 (检查, 定理).** `SlotCp.CpNew.famNew`, `SlotTw.famU s` 的成员是同一种类沿路径的拷贝, 坐标类型都是 `HB (Lev a′)` (`coord-same`): 读回无损, 升界精确, 不是 "有损地经共享槽". 代价: 带证据的世界里一切拷贝的顶经搬运相等 (`sh-same`, `tw-same`, `κd-same`), 两份不能不同 (`tw-no-split`). 覆盖面的边界: `step (step T′)` 的两个新种类不能同在一个 `Slot` (`no-slot-step2`, 实例 `no-slot-steps`: `Lev (a ⊞ hs (hs y))`).
>
> **对纲领与目标.** 纲领 1, 2: 本路不交闭项 (否定一路); 一切结论是 `--safe` 下编译过的定理. 纲领 3: 本路的否定都是 `no-retract` (良基) 的推论, 不是壁垒 (`Barrier`) 的推论, 也不用 LPO/WLPO/分离子; 它说的是 "一个槽装下随级严格变大的坐标" 这一形状与良基冲突. 纲领 4: 不读记号. 目标 "让树自足": 给出一条树侧判据 (定理): **共享槽 = 成员坐标两两互为收缩** (`slot-ret`); 所以能共享槽的只是 "坐标类型可无损互搬" 的成员 (同一种类的拷贝), 相邻两级永远不能. 这把构造一路的推进精确地划在 "拷贝" 一类上.
>
> **只否定什么, 不否定什么.**
>
> - 否定: `Slot` 记录 (接口 §2) 的成员含相邻两级且高的那份可达 (`no-slot-adj`), 特别是整族 `κHc`; "忘" 的一起升 (不经接口, `no-forget`); 槽是 `K₁` 坐标类型的收缩并服务一切 `κc c` (`slot-coordK₁`).
> - 不否定: 构造一路的 `famNew`, `famU` (同一坐标类型的拷贝; 只给代价); 不经 `Slot` 的升界, 包括 "不忘" 且不经共享槽的形状 (例如 `RsOwnIf.PW.OwnFam`; `NegRsOwnPre` 已说 "`KLv` 形状的精确置 ⇒ ⊥" 不可证); 接口 §1 的 `Dg` (非对角无律; 本路没有关于它的否定); 每级一个槽, 组之间另行升界 (判断, 未写). 本路没有关闭任何路线: `κHc` 上的升界问题仍开着, 被关的只是 "经接口形状的共享槽" 这一种.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSlot where

import OCF.Align.NegSlotPre
import OCF.Align.NegSlotWall
import OCF.Align.NegSlotInst
```

## 定理表

| 名字 | 文件 | 陈述 (白话) | 档 |
|---|---|---|---|
| `no-up`, **`no-inflate-at`**, **`no-inflate`** | Pre §1 | 一切 `S`, 种类 $\kappa$: 没有 $d,u$ 使 $x\lhd u(d\,x)$ 对一切 $x$ (加强 `no-retract`) | 定理 |
| **`slot-wall`**, `slot-wall≡` | Pre §2 | `HB S` 经 $X$ 膨胀地来回, 且 $X$ 是 `S` 的某坐标的收缩 ⇒ ⊥ | 定理 (否定) |
| `coordK₁`, **`slot-coordK₁`** | Pre §2 | `K₁` 的每个种类 $\kappa_0$ 给出 $c'$, 使以 `E K₁ κ₀` 为收缩的槽不能膨胀地服务 `κc c′` | 定理 (否定) |
| **`no-forget`** | Pre §3 | `TopH`, `Self≤`, `Forgets` 三者不能同时成立 | 定理 (否定) |
| **`K1.no-forgetK₁`**, **`K1.no-forget-jx`** | Pre §4 | 任意证据 $P$; `RsK` 对 (`κc c`, `κc (hs c)`) 或 (`κH f`, `κH (f⁺ f)`), 升低的那份后高的那份的顶不依赖旧世界 ⇒ ⊥ | 定理 (否定) |
| `satTS`, `satTF`, `satSF`; `RLz`, `RHz`, `w0⊤`, `RLz-keeps` | Pre §3, §4 | 三前提两两可满足; `K₁` 上相邻两级同时有 `RsK` (点更新, 不忘) | 定理 (实例) |
| `SL.sh-read`, `SL.sh-wset`, `SL.img` | Wall §1 | 盲: 带证据世界上成员的顶互相决定; `wset` 给证据; 一个成员的顶在别的成员的像里 | 定理 |
| **`SL.slot-ret`** | Wall §1 | 可达成员的坐标是任一别的成员的坐标的收缩 | 定理 |
| **`SL.no-slot-adj`** | Wall §1 | 相邻两级成员 (高的可达) ⇒ ⊥ | 定理 (否定) |
| **`no-slot-κHc`** | Wall §3 | `¬ Slot K₁ tp₁ H₀ κHc Q tq κ₀` | 定理 (否定) |
| **`no-slot-pair`**, **`no-slot-κH`** | Wall §3 | 含相邻两级 (高的那份有 `RsK` 与一个世界) 的族没有 `Slot` | 定理 (否定) |
| `slot-copies`, `slot-one`, `slot-κHc-one`, `reach-hz1`, `reach-rs` | Wall §2, §3 | `Slot` 可满足 (单成员, 同种类的拷贝); 可达性的来源 | 定理 (实例) |
| **`sh-same`**, `no-split`, `cp-same`, **`tw-same`**, **`tw-no-split`**, **`κd-same`**, `coord-same` | Inst §1, §2 | 构造实例的代价: 带证据的世界里拷贝的顶经搬运相等 | 定理 (盲) |
| **`no-slot-step2`**, **`no-slot-steps`**; `reach-out`, `inst-in`, `inst-out` | Inst §3 | `step (step T′)` 的两个新种类不同槽; 各自单独可成槽 | 定理 (否定; 实例) |

## 前提实例

- `no-inflate`: 前提是 "对一切 $x$" 的膨胀; 去掉 "对一切" 只要一个 $x$ 时可满足 (例 $d,u$ 任意, $x=$ `hz` 时 `z⊲ᴮ`); 本路没有写成定理 (判断: 平凡).
- `slot-wall`: $X$ 是坐标的收缩: `◁-rf`; 膨胀的来回: 取 $X=$ `HB S` 自己, $d=u=\mathrm{id}$ (`hself`); 两者同时就是被否定的.
- `no-forget`: `satTS`, `satTF`, `satSF`. `K1.no-forgetK₁` 的 `RsK` 前提: `RLz`, `RHz` (在 $c=$ `hz`), 世界 `w0⊤`.
- `no-slot-κHc`: 唯一的前提是 `Slot` 本身; `Slot` 对单成员 (`slot-κHc-one`, 一切 $c$) 与同种类拷贝 (`slot-copies`) 可满足, 被否定的是 "含相邻两级的整族".
- `no-slot-pair`, `no-slot-κH`: `RsK` 与世界单独可满足 (`RLz`, `RHz`, `w0⊤`, 在闭的下标上); `Slot` 单独对单成员可满足. 对 `κH f` 一族本身的 `Slot` (没有 `RsK`) 是否存在, 本路**没有**结论 (那一族里没有能按构造子判定的下标, 可达性要 `RsK` 给).
- `no-slot-step2`: `inst-in`, `inst-out`, 世界 `w₀ (genLev _)`.

## 判断 (单列)

1. **穷尽是判断.** 共享槽经接口的形状, 能活的只有 "成员坐标两两互为收缩" 的族 (`slot-ret` 是定理, "只有拷贝一类" 是判断: 例如两个不同级但坐标类型同构的种类也可能共槽, 未检查).
2. **对 `κHc` 的含义.** 若要按级回灌, 槽只能按坐标类型的 "收缩类" 分组, 组之间仍要别的升界; 这把原问题 (相邻级之间) 原样留下 (判断).
3. **`Dg`.** 接口 §1 的对角解码对 `κHc` 一族是否可构造: 有一个判定 (经典) 时有; 无判定时我判断要函数外延 (逐结点重建树后对角恒等), 没有编译成定理, 也不能编译成否定 (函数外延与本仓库的设定相容).
4. **`no-forget` 与 `no-slot-adj` 的关系.** 后者 (静态, 只用 `wset`) 比前者 (动态, 用升界) 对 `Slot` 形状更强; 前者覆盖不经接口的 "忘" 的一起升.

## 翻译账

本路不读记号. 新增的都是对构造一路接口与已有树侧定义的否定, 没有新构造子或节点; 依据是 `no-retract` (高度的良基) 与 `HtTowerTy` 的 `step`/`Lev` 的定义相等. 归类 (判断): 提供信息 (否定定理划出 "不能有的字段": 共享槽里不能有相邻两级).

## 审计

- **编译.** 从仓库根: `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/NegSlot.lagda.md +RTS -M6G -RTS`, 删本路四个模块自己的 `.agdai` (字面路径) 后冷编译, 依赖用共享接口: 退出码 0, 约 4.4 秒, 峰值常驻约 0.77G.
- **禁用构造.** `python3 probes/Survey/scripts/negslot/forbid.py` (只扫 ```agda 代码块; `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, `--cubical`, `--with-K`, `Funext`/`FE₀`): 四个文件命中 0, 选项行都正确, 退出码 0.

## 文件

| 文件 | 内容 |
|---|---|
| `NegSlot` | 入口 |
| `NegSlotPre` | 接口定稿前: `no-inflate`, `slot-wall`, `slot-coordK₁`, `no-forget`, `K₁` 推论与实例 |
| `NegSlotWall` | 对接口: `sh-read`, `slot-ret`, `no-slot-adj`, `no-slot-κHc`, `no-slot-pair`, `no-slot-κH`, `slot-copies` |
| `NegSlotInst` | 对构造实例: `sh-same`, `tw-same`, `κd-same`, `no-slot-step2`, `no-slot-steps` |
| `probes/Survey/scripts/negslot/forbid.py` | 禁用构造扫描 |
