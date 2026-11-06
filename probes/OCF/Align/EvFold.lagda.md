# 事件世界上的真折叠: 入口与判决

> 不含记号. 作者选定原话: "事件世界上写真折叠". 接 [AdmEv](AdmEv.lagda.md) 的接手清单 (真折叠; 塔的 ℕ-极限; `A`-世界长高版的改贴) 与 [Survey/StallDiagnosis.md](../../Survey/StallDiagnosis.md) §5.2 (方向 B). 不改任何已有文件; `evKS₀`, `rp`, `new-gen₀` 从 `AdmEvBase` 原样导入.
>
> **判决: PARTIAL.**
>
> 1. **真折叠: 写出来了 (定理/构造, 无条件, 对外层界 $b_1=1$).** 层的种类是 `A` 的种类加 `evKS₀` 的两个带证据种类 (κ₀ 坐标 $H_0$, κ₁ 坐标 `HB S₁`); 世界是 `A × 事件表`. 事件种类的闭包 `nε κ` 回灌时, **增量是折叠自己的输出的读回** (κ₀ 读第 1 层, κ₁ 读第 2 层), 作为事件接到世界上, 界字面地接上增量 (`new-gen₀`). 闭项 `T-Ω₃`, …, `T-Ω₃²` 与 `fgh` 无参数, 合法性由形状给出. **不被压回 $\Omega_2$** (形状定理, `EvFoldNew`): 输入与两种种类的层的任何像不互模拟; 折叠把 κ₁ 的结点交给 κ₁ 的闭包; κ₁ 的第一次回灌的增量与格世界里 κ₁ 的界都含 $H_0$ 坐标的 $\Omega$-结点, 不与任何 `up h` 互模拟; `top-bd` 的同形物不成立.
> 2. **塔的 ℕ-极限: 未走通, 有编译过的否定 (`EvFoldLim.no-coh-ev`).** 挑战 "只有两条" 的结果: 两条都只管改贴的合法性, 前面还有一道墙: 外层界的 ℕ-极限之下, 各站种类的证据要相干 ($Z_n = \mathrm{wk}_n⨾Z_{n+1}$), 而对 `AdmEvFeed.Inst` 的塔这样的证据族不存在 (相干的证据都走极限界的同一支). 这是拷贝墙在塔的极限上的重现. 另有具体项的否定 `no-lim-n` (`AdmEv` 建议的 "第 $n$ 站沿第 $n$ 支").
> 3. **`A`-世界长高版的改贴: 折叠不需要** (定理 `bd-indepA`, 定义相等): 折叠的 `A`-世界与 `evKS₀` 的外层 `A`-世界 ($a_0=0$) 分开, 事件种类的界不看折叠的 `A` 分量; 外层界 $1$ 不含 $\Omega$-结点, 证据不含 `A` 坐标.
> 4. **值: 没有值定理.** 没有严格增长以外的序数值结论, 没有与 `Tᵁ`, `Tdg₂`, `Tᴰ₊` 的比较, 没有粗界. 有限测试见 §4 (一条重要的盲点: `T-Ω₂` 与 `T-Ω₃` 在测到的范围内形状相同).
>
> **对纲领与目标.** 纲领: 树是布劳威尔树 (`A`), 折叠由检查器保证停机, 无公理, 不碰壁垒 (比较都在字面公共上界之下: 层的比较在 $\Lambda$ 之下, 事件种类的坐标比较在重放的界之下); 闭项与证书的导入闭包不含记号 (§6). 目标 (树自足): 这一步的新定义 (离散走法, 移植, 按读回层的允许层) 都由事件世界的结构逼出 (§5); **一条有用的信息** (判断): 事件世界里闭包的走法与种类无关 (`WalkE` 不进坐标内部), 每多一个事件种类, 折叠里按种类不同的只剩读回 (`RB`) 与回灌的目标层; `HtTowerF` 的 `Walk₁` 要对坐标的每一种 $\Omega$-结点各接一种闭包, 这里不要. 一切级一个折叠的剩余义务因此收窄到 "对一切级的读回" (没有写).

## §1 设计

| 件 | 定义 | 文件 |
|---|---|---|
| 种类结构 | `plus S S′` (种类取和, 世界取积); `T = plus S₀ evK`, `evK = EvKS₀.evKS₀ 0 1 … wz …`; 种类 `κa`, κ₀ = $(0,\mathrm{hsuc\,hself})$, κ₁ = $(1,\mathrm{hself})$ | [EvFoldTree](EvFoldTree.lagda.md) |
| 世界 | `Wε = A × Hist`; 序: `A` 分量第一位置, 事件表后缀 | 同上 |
| 数据树 | `D₊`: `HtTowerFTree` 的七个, `nμ` 换成 `nε κ`; 允许层 `ZE κ` (κ₀: $\ge2$, κ₁: $\ge3$) | 同上 |
| 走法 | `Cut₀` (沿 `A`, 原样); **`CutE`** (沿新事件逐个走); `Int`, `IWε` | 同上 |
| 读回 | `rd₁` (第 1 层 → $H_0$), `rd₂` (第 2 层 → `HB S₁`, κ₀ 闭包读成 `σH` 分支, 世界加 κ₀ 事件); `RB κ`, `evRB`; `drp₁`, `drp₂` (移植 `tp`) | [EvFoldRead](EvFoldRead.lagda.md) |
| 折叠 | `KG` 原样; **`RunE`**/`RKε`/`κcε`/`κΔε`/`Kpε`/`Kbε`; **`WalkE`** (离散); 状态多 `z₂` | [EvFoldFold](EvFoldFold.lagda.md) |
| 闭项 | `TΛ`, `T⁺ h = TΛ (3 ⊞ h)`; `nbᴱ` (κ₁ 上连续的分支), `Ω₃ᴱ`, `Ω₃²`; 对照 `Ω₂ᴱ` | [EvFoldClosed](EvFoldClosed.lagda.md) |
| 不压回 | `¬two-kind`, `Ωd-top`, `run-top`, `first-new`, `Cell.*` | [EvFoldNew](EvFoldNew.lagda.md) |
| 离散与耦合 | `between`, `rp-κ₀-skip`, `skip*`, `rp-κ₁-up` | [EvFoldNeg](EvFoldNeg.lagda.md) |
| 塔的极限 | `idx`, `idx-0`, **`no-coh-ev`**, `ρX`, **`no-lim-n`** | [EvFoldLim](EvFoldLim.lagda.md) |
| 测试 | `same`, `diff`, `diffL` (有限测试) | [EvFoldTest](EvFoldTest.lagda.md) |

**事件种类的闭包怎样折叠** (`EvFoldFold` 文件头). 目标层在读回层及以下: 回灌, 格 $n$ 的世界 $H_n = e_n∷H_{n-1}$ ($H_{-1}$ 是当前世界的表), 事件 $e_0$ 的增量读状态里读回层的累积, $e_{n+1}$ 读第 $n$ 格在读回层上的输出; 格的输出经 `drp`/`drp₁`/`drp₂` 落回目标世界. 目标更高: 沿新事件走到目标世界 (`Kpε`), 再接 `nε κ`. 与 `HtTowerFFold.RunM` 的三处不同: (i) 界由事件给出, 新界字面是 旧界 ⊞ 增量 (`RunM`: $x_{n+1}=\mathrm{rd}(x_n,\Delta_n)$ 读在旧界上); (ii) 格 $n+1$ 的区间只有一个世界 (序是离散的, `between`), `RunM` 的格沿高度路径走过 $[x_n, x_{n+1})$ 的全部坐标; (iii) 有两个读回层, 第 2 层的回灌要丢掉 κ₁ 的事件而保留 κ₀ 的 (`drp₂`).

## §2 定理表

| 名字 | 文件 | 陈述 (白话) | 档 |
|---|---|---|---|
| `plus`, `T`, `Ht`, `D₊`, `Ωd`, `CutE`, `Int` | EvFoldTree | 层, 世界, 数据树, 走法 | 定义 |
| `bd-indepA` | EvFoldTree | 事件种类的界不看世界的 `A` 分量 | 定理 (`refl`) |
| `accL`, `accᴸ` | EvFoldTree | 层良基 | 定理 |
| `sum-fst`, `Lg-sum` | EvFoldTree | 第 0 层的和合法 | 定理 |
| `rd₁-fst`, **`Lg-rd₁`**, `rd₂-fst`, **`Lg-rd₂`** | EvFoldRead | 读回保第一位置, 底合法则读出合法 | 定理 |
| `RB`, `evRB`, `drp₁`, `drp₂`, `tp`, `tp-suf` | EvFoldRead | 增量, 移植 | 定义 / 定理 |
| `Run` 一族, `RunE`, `WalkE`, `κcε` | EvFoldFold | 折叠, 对一切合法且以第 1, 2 层为第一位置的 $\Lambda$ | 定义 (停机检查通过) |
| `NbE.mono`, `Lg-nbᴱ`, `Lg-topᴱ`, `Lg-Ω₃ᴱ`, `Lg-Ω₃²`, `Lg-Ω₂ᴱ` | EvFoldClosed | κ₁ (κ₀) 上的连续分支合法 | 定理 |
| **`T-Ω₃`**, `T-Ω₃+1`, `T-Ω₃·2`, `T-Ω₃ω`, **`T-Ω₃²`**, `T-Ω₂`, `Lg-T-Ω₃²`, **`fgh`**, `fgh₃` | EvFoldClosed | 闭项, 合法, FGH | 定义; 合法是定理 |
| `E-κ₁`, `Λ₃-top` | EvFoldNew | 输入的最外是 κ₁ 的结点, 坐标类型 `HB S₁` | 定理 (`refl`) |
| **`¬two-kind`** | EvFoldNew | 输入与两种种类的层的任何像不互模拟 | 定理 |
| `Ωd-top`, `run-top` | EvFoldNew | $\Omega_\Lambda$ 的数据树是 `n1 ⨾ nε κ₁ …`; 折叠它就是 `RunE κ₁`, 状态 $Y\oplus\mathrm{Stp}\,Y$ | 定理 (`refl`) |
| `HasH`, `has⊲`, `has-⊞`, `up-noH`, `≈-has`, `has→¬up` | EvFoldNew | 含 `σH` 结点: 第一位置之上保持, `up` 的像没有, 互模拟保持 | 定理 |
| **`first-new`**, `Cell.cell₀-new`, `Cell.δ₀-¬up` | EvFoldNew | κ₁ 第 0 格的增量含 `σH` 结点, 不与任何 `up h` 互模拟; 对一切 $\Lambda$, 世界, 状态, 闭包 | 定理 |
| `Cell.cell₀-ev`, `Cell.β₁≡`, **`Cell.bd₁-new`**, `Cell.bd₁-¬up`, `Cell.bd₁-strict` | EvFoldNew | 格世界里 κ₁ 的界 = 旧界 ⊞ δ₀, 含 `σH`, 不是 `up h`, 严格高于旧界 | 定理 (最后一条是严格增长档) |
| **`Cell.¬top-bd-ε`** | EvFoldNew | κ₁ 有界的坐标不都是 $H_0$ 的嵌入 (`TdPlusVal.top-bd` 的同形物不成立) | 定理 |
| **`between`**, `suf-anti` | EvFoldNeg | 后缀序上 $H$ 与 $e∷H$ 之间没有第三张表 | 定理 |
| `rp-κ₀-skip`, `skip*`, `rp-κ₁-up` | EvFoldNeg | κ₁ 事件不进 κ₀ 的界; κ₀ 事件以 `up δ` 进 κ₁ 的界 | 定理 |
| **`no-coh-ev`** | EvFoldLim | `Inst` 塔: 极限界之下没有相干的证据族 | 否定 |
| **`no-lim-n`** | EvFoldLim | `Inst` 塔: 第 1, 2 站沿第 1, 2 支改贴后, 前者不是后者的第一位置 | 否定 |

## §3 闭项与 FGH 的类型原文

```text
EvFoldClosed.T⁺      : (h : Ht) → LgB h → A          -- = TΛ (three ⊞ h) …
EvFoldClosed.Ω₃ᴱ     : Ht                           -- = hΩ (inj₂ κ₁) (nbᴱ hz (λ _ h → hs h))
EvFoldClosed.Ω₃²     : Ht                           -- = hΩ (inj₂ κ₁) (nbᴱ hz (λ _ h → h ⊞ Ω₃ᴱ))
EvFoldClosed.T-Ω₃    : A                            -- = T⁺ Ω₃ᴱ Lg-Ω₃ᴱ
EvFoldClosed.T-Ω₃²   : A                            -- = T⁺ Ω₃² Lg-Ω₃²
EvFoldClosed.Lg-T-Ω₃² : Lg T-Ω₃²
EvFoldClosed.fgh     : ℕ → ℕ                        -- = FL.FGH (ord T-Ω₃²)
EvFoldClosed.fgh₃    : ℕ → ℕ                        -- = FL.FGH (ord T-Ω₃)
```

无模块参数, 无前提. `Ht = HB T`, `T = plus S₀ evK` (`EvFoldTree`).

**前提实例.** 折叠的模块参数 (`Λ`, `lΛ`, `one⊲`, `two⊲`) 在闭项里由 `top₃ h = 3 ⊞ h`, `Lg-top₃`, `o₁⁺`, `o₂⁺` 给出, 对一切合法 $h$. `first-new` 对一切世界与状态; `Cell` 对一切闭包参数 (实例: `run-top` 给出的就是闭项 $\Omega_{\Lambda}$ 的顶层闭包). 两条否定的前提是 `AdmEvFeed.Inst` 的闭项塔 (存在, 无参数). `between` 无前提.

## §4 读法 (判断) 与有限测试

**读法 (判断, 纸面).** 按 `HtTowerF` 的读法: `TΛ Λ` 读 $\psi_0(\Omega_\Lambda)$, $3\boxplus h$ 作下标时读 $h$. κ₁ 的结点 `Ω₃ᴱ` 是 κ₁ 上的恒等分支 (`HtTowerCont.Ωtop` 的同形物, 高一级), 读 $\Omega_3$. 所以 `T-Ω₂` 读 $\psi_0(\Omega_{\Omega_2})$, `T-Ω₃` 读 $\psi_0(\Omega_{\Omega_3})$, `T-Ω₃+1` 读 $\psi_0(\Omega_{\Omega_3+1})$, `T-Ω₃·2`, `T-Ω₃ω` 读 $\psi_0(\Omega_{\Omega_3\cdot2})$, $\psi_0(\Omega_{\Omega_3\cdot\omega})$, 最高的 **`T-Ω₃²` 读 $\psi_0(\Omega_{\Omega_3^2})$**. 对照: `Tᵁ`, `Tdg₂` 读 $\psi_0(\Omega_{\Omega_3})$; `Tᴰ₊` 读 $\psi_0(\Omega_{\Omega_2})\cdot\omega$; `HtTowerFClosed.T-Ω₂²` 读 $\psi_0(\Omega_{\Omega_2^2})$. 按读法 `T-Ω₃+1` 起高于这些; **都没有定理.** 读法的两处额外假设 (判断): (a) 离散走法 (格 $n+1$ 只折叠一个世界的分支) 与 `RunM` 的连续走法给出同一个上确界; (b) `evKS₀` 的内层世界固定为全 0 (坐标的比较在内层世界里), 不改折叠的输出 (折叠里坐标只以界的身份进入节点).

**有限测试** ([EvFoldTest](EvFoldTest.lagda.md), 是测试, 不是证明). `same d w`: 到深度 $d$, 每个极限取前 $w$ 支; `diff`: 同上, 给出第一个不同处的路径; `diffL`: 只数极限的深度.

| 比较 | 结果 |
|---|---|
| `T-Ω₃` 对 `T-Ω₃+1` | `same 4 2` 同, `same 5 2` 不同 |
| 本折叠的 `T-Ω₂` 对 `HtTowerFClosed.T-Ω₂` | `same 4 2` 同, `same 5 2` 不同 |
| 本折叠的 `A`-种类层 (`T-Ω₁`) 对 `T-Ω₂` | `diff 10 3` 在 `[1,0,0]` 不同 (`HtTowerF` 里的同一对也在 `[1,0,0]`) |
| **`T-Ω₂` 对 `T-Ω₃`** | **`same 26 2`, `diff 14 3`, `diffL 12 3`, `diffL 9 4`, 只沿第 $k$ 支到深度 40 ($k=1,2,3,5$): 都没有找到不同; `diffL 15 3` 跑满 25 分钟被 `timeout` 杀掉 (退出码 124, 未完成)** |

**盲点 (判断).** `T-Ω₂` 与 `T-Ω₃` 的两个顶层闭包都是事件闭包, 格 0 的节点层都是 $3$ (界在空表里都是 $0$), 第一处不同在格 1 的节点层里 ($3\boxplus$ 含 `κa` 结点 对 $3\boxplus$ 含 κ₀ 结点), 那里再往里两层才分出 `A`-闭包与事件闭包 (后者在顶层就在 `[1,0,0]` 分开). 测到的范围没有走到那里; 形状是否最终不同, 没有测出来, 也没有定理. **所以 "不被压回" 只到形状定理一档** (`EvFoldNew`: 折叠里 κ₁ 的界长出了不在 $H_0$ 嵌入里的高度), 输出的 `A` 树与 `T-Ω₂` 的不同没有证据.

## §5 第一个障碍

1. **塔的 ℕ-极限** (`no-coh-ev`, 定理): 种类带证据, 外层界取 ℕ-极限时同一个坐标在极限界的不同支下各有一份证据, 塔要求它们相干, 不可能. 下一步的候选 (判断, 没有写): (a) 极限站的高度不取各站高度的 ℕ-极限, 而在极限界之下重新由回灌生成 (只用极限界自己的种类); (b) 外层界只取不含 ℕ-极限的增长 (后继与 $\Omega$-结点), 极限放到别处; (c) 把外层界本身也放进事件世界 (外层事件), 种类的证据对外层事件表相对化. 三条都没有否定定理.
2. **一切级一个折叠**: 本折叠对外层界 $1$ 手写两个事件种类的读回 (`rd₁`, `rd₂`) 与回灌的目标层. 外层界更大时, 要对 $c\lhd b$ 的每一级读回成 `HB (Lev c)` (对 `Lev` 的构造递归), 允许层 `ZE` 与 `drp` 也要按级给出. 走法已经与种类无关 (`WalkE`), 这是剩下的全部按级部分 (判断).
3. **值**: 同 `HtFeed`, `HtTowerF`: 没有树侧的值判据; 本篇的有限测试连 `T-Ω₂` 与 `T-Ω₃` 的输出都没有分开.

## §6 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| 种类 = `A` 的种类 + `evKS₀` 的种类 (`plus`) | 方向 B 的种类带证据; `A` 的种类给第 0 层 | 树侧 (沿用 `AdmEv`) |
| 世界 `A × Hist`, 序取积 | 两部分的界各自只看自己的分量 (`bd-indepA`) | 树逼的 (判断) |
| **`CutE`/`WalkE` 离散走法** | 事件表的序离散 (`between`) | **树逼的** (定理) |
| 格 $n+1$ 的区间只有一个世界 | 同上 | 树逼的 |
| `ZE` (κ₀: $\ge2$, κ₁: $\ge3$) | 读回层的树要能读回 (`rd₁` 没有 `nε`, `rd₂` 没有 `nε κ₁`) | **树逼的** |
| `rd₂` 的 `nε κ₀` 行: 世界加 κ₀ 事件, 增量 $\mathrm{rd}_1(0,\mathrm{toD}_1x)$ | 事件世界只能接增量; 增量要合法 | 树逼的; 形状沿用 `HtTowerNRead` 的 `nμ` 行 |
| `drp₂` 与移植 `tp` | 第 2 层的回灌输出要落回目标世界, 没有并 (同 `drp₁` 的理由) | 树逼的 (判断) |
| 增量从 0 读起, 新界 = 旧界 ⊞ 增量 | `new-gen₀`: 事件世界里界只能这样长 | 树逼的 |
| 回灌/保留的分界按读回层 | 同 `RunM` | 形状沿用 `HtFeedFold`/`RunM` (此前已记账的翻译痕迹) |
| `nbᴱ` (κ₁ 上连续的分支) | `HtTowerCont.nbᴮ` 的同形物 | 沿用 |
| 内层世界全 0 | `evKS₀` 的参数 | 选择 (`AdmEv` 的实例取法) |

归类: **攀爬, 提供信息.** 加深的三个标志: 新构造子或字段读自基本列规则: 没有 (`nε` 是 `nμ` 的同形物; 离散走法由序逼出); 闭包定理新增专属前提: 没有闭包定理; 只能用 `Lab` 验收: 不是. 提供信息的标志: 否定定理划出不能有的形状: 有 (`no-coh-ev`: 塔的极限上不能有相干证据; `between`: 不能有连续走法的中间世界); 一步定理: `first-new` 对一切世界与状态. 序数值验收: 没有. 这一步让缺陷变浅还是变深 (判断): 变浅的一处是走法与种类无关 (每加一种事件种类不再加一份 `Walk`); 变深的一处是读回仍按级手写 (两个).

## §7 审计

本轮的数字 (复核时以重跑为准):

- **编译** (删本组九个 `.agdai`, 写精确模块名; 依赖用共享接口; 堆上限 6G): 入口退出码 0, 7.6 秒, 峰值常驻 0.85G; `EvFoldTest` 退出码 0, 7.5 秒, 0.61G.
- **导入闭包** (`importclosure.py`, `--only` 表: `OCF.Free.Level`, `OCF.BTBO`, `OCF.Align.` 下的 `CumReadCF`, `TLRule`, `HtFeed`, `HtTower`, `DiagK`, `ChainZ`, `StallDx`, `UniTr`, `AdmW`, `AdmEv`, `EvW`, `EvFold`): 入口 58 个模块 (本地 46), `EvFoldTree` 48, `EvFoldRead` 50, `EvFoldFold` 51, `EvFoldClosed` 52, `EvFoldNew` 55, `EvFoldNeg` 49, `EvFoldLim` 50; 都是退出码 0, 禁用表 0, `--only` 之外 0.
- **定义级切片** (`depslice.py`, 到达块 / 记号块 / 别处记号词): `EvFoldClosed:fgh` 362/0/0, `fgh₃` 362/0/0, `Lg-T-Ω₃²` 348/0/0, `T⁺` 320/0/0, `EvFoldFold:RunE` 294/0/0, `EvFoldRead:Lg-rd₂` 205/0/0, `EvFoldNew:¬two-kind` 149/0/0, `first-new` 231/0/0, `EvFoldNeg:between` 72/0/0, `EvFoldLim:no-coh-ev` 201/0/0, `no-lim-n` 181/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 切片看不见模块应用 (`module E₁ = NbE …`, `module RI = TI.Run …`), 导入闭包覆盖这一处. 只保证不引用, 不说明定义没有受记号启发.
- **禁用构造**: 九个文件无 `postulate`, 洞, 停机或正性编译指示, `trustMe`, 函数外延; 选项都是 `--safe --without-K --lossy-unification`.
- **代码行** (agda 块里非空非注释): Tree 345, Read 166, Fold 295, Closed 145, New 96, Neg 46, Lim 70, Test 78, 入口 8; 合计 1249. 文件行合计 1951.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EvFold where

open import OCF.Align.EvFoldTree using (plus; T; Ht; Wε; evK; κa; κ₀; κ₁; D₊; D; Ωd; CutE; Int; bd-indepA) public
open import OCF.Align.EvFoldRead using (rd₁; Lg-rd₁; rd₂; Lg-rd₂; RB; evRB; drp₁; drp₂) public
open import OCF.Align.EvFoldClosed using (TΛ; T⁺; Lg-T⁺; Ω₂ᴱ; Ω₃ᴱ; Ω₃²; T-Ω₂; T-Ω₃; T-Ω₃+1; T-Ω₃·2; T-Ω₃ω; T-Ω₃²; Lg-T-Ω₃²; fgh; fgh₃) public
open import OCF.Align.EvFoldNew using (¬two-kind; Ωd-top; HasH; module Top) public
open import OCF.Align.EvFoldNeg using (between; rp-κ₀-skip; rp-κ₁-up; skip*) public
open import OCF.Align.EvFoldLim using (no-coh-ev; no-lim-n) public
```
