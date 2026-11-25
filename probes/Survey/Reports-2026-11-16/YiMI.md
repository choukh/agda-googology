# 合并同类接口（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-17 07:15 至 07:48 |
| 工具调用 / agda 编译 (粗数) | 117 / 23 |
| token (usage 字段，按消息去重) | 输出 158992；新写入缓存的输入 345901；读缓存的输入 24341668；其余输入 218 |
| 写过的仓库文件 | `YiMIConv.lagda.md`, `YiMIGraded.lagda.md`, `YiMIIface.lagda.md`, `YiMIRead.lagda.md`, `YiMISelf.lagda.md` |
| 文件前缀 | `YiMI` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 5 件全部退出 0，禁用构造 0，两件不读记号的导入闭包干净；九个朝低层保持的名字都换算到一条带五个参数的接口（Hold、LowAt、Low，逐条换算定理）；五份分级实例是同一份的取值（refl）；生成原理与自身折叠保持各合成一份；主线的 LowKeep 只含到第 0 层的路径（wl-inc） |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b81/YiMI.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。在仓库根目录 `<仓库>` 下工作。只新建你前缀的文件，不改任何已有文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

#### 1. 判决

**对纲领与目标意味着什么.** 本路只做接口层的合并, 不改树、折叠、合法性, 也不加强度. 合并后的接口 `Hold`/`LowAt`/`Low` 在不读记号的文件 `YiMIIface` 里, 导入闭包干净. 换算定理逐条编译通过 (编译定理), 结果是: 现有九个 "朝低层保持" 的名字, 结论形状都一样, 不同之处全在五个参数 (目标、路径、上下文头 ψ_ν 与前缀、量化域、不变式) 的取值上. 所以以后的新义务可以写成 "参数取什么值", 不必再起新名字. 这一步不让树更自足: 上下文头 ψ_ν 只在读记号的分级实例里有具体值, 不读记号一侧只是抽象的 `app K`.

**各步进度.** 第 0 到 3 步都做完了. 临时文件 `<实验目录>/YiMIStep0.agda` 第一次编译就通过 (退出 0).
- 第 1 步: 七组旧陈述都换算到新接口, 另加三项: `lowᴷ`、`YiSOUp.UpQ`/`upAll`、抽象的 `SelfKeep`/`UpKeep`.
- 第 2 步: 五份分级实例都是 `gradedᴹ` 的取值 (`refl`). 两份自身折叠的保持都由 `SelfF.LF` 推出. 另外三份生成原理 (连同三组 `Weak`/`Lim`/`Node`) 也合并成了一份.

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 九个保持名字的结论都是 `Hold Φ ap D`, 只有五个参数不同 | YiMIConv, YiMIRead, YiMIIface | 编译定理 (逐条换算) |
| 三份 `sys→low` 的推导相同, 都是 `sys→LowAt` 接在各自的 `keepAll` 上 | FI.Suff, BL.SuffR, QD.SuffRD | 编译定理 (`fi-low′` 等) |
| 不读记号一侧有两套上下文: 系统自己的 `Cxt/ap` 和 `Graded` 的 `Cx/app`. 每条根状态定理都要带一个桥 `ec : ∀ t → apᴮ K₀ t ≡ app Kc t` | Pack, QDPack, XReb, Tree, Zero | 判断 (读定义得出) |
| `lowΩ` 不取 `R ℓ a x`. 它的条件随参照 a 变 (`CondΩ`), 不是逐点的不变式 | YiSDIface.AtΩ | 编译定理 (`lowΩ→` 的形状) |
| 主线分级实例 (`gradedᴮ`/`domsᴮ`) 的 `LowKeep` 只含目标第 0 层、路径 `z≤`. 换基根状态一族 (路径 `inc c′ v`) 不是它的实例 | YiWREnd, YiGIInst.Wlᵍ | 编译定理 (`wl-inc`, `zero→lowKeep`) |
| 底值界有两种写法: ψ_ν(K) (`Keepᵗ`, `Bdᵍ`) 和 ψ_ν(K ++ []) (`Bdᴱ`) | YiSOLow, YiBAEbo | 编译定理 (`bnd⇔` 互推) |
| 生成原理和 `Weak`/`Lim`/`Node` 各有三份逐字相同的副本 | YiFIGen, YiWREnd, YiBAEbo | 编译定理 (`genᴹ` 等, 旧的是取值) |
| 剩下的义务分到不同参数上. `NodeMis`、`UpMis`: 陈述由 "路径的保留判定 `kp … w`" × "头的比较 `cmpᵀ (ν+1) κ`" 索引, 域 `Dm` 只作前提出现. `RebRow`: 量化域. `RootBd`: 不变式. `StepW`: 上下文前缀. 简报说这几条 "都出自量化域太宽", 这一点读作只对其中一部分成立 | YiSOLow, YiSOUp, YiSOEnd, YiWCWire | 判断 (依据 `NodeMis`/`UpMis` 的定义体; `StepW` 只读了文首) |
| `LowSlot` 推不出 `lowAll`, 因为它只给槽位点上的结论 | YiWREnd, YiSOLow | 判断, 没有编译的否定 |

**对应表 (名字 × 五个参数)**

| 名字 | 目标 | 路径 | 上下文 (头/前缀) | 量化域 | 不变式 |
|---|---|---|---|---|---|
| `YiAbsGIface.LowKeep` | ∀ j | ∀ w, `Wl w` | ∀ K, 抽象 `app` | `Gx` | `Gb × Wl × Bd` |
| 主线 `LowKeep` (`gradedᴮ`/`domsᴮ`) | 0 | 只有 `z≤` | ψ₀(K ++ ·) | {Ω 树} | `Bdᴮ` (= `Inv₀`) |
| `YiBLFold.lowᴮ` / `lowᵗ` | 固定 j, 经 c′, `route` 为 `inj₂` | `inc c′ v` | Kc, 经 `ec` 接上 | 全体 | `Bdᴮ (rt β) K₀` |
| `YiFIFold.lowᴷ` | 同上 | `inc c′ v`, 表为空 | Kc, 经 `ec` | 全体 | `Bdᴷ (rt β) K₀` |
| `YiQDFold.lowᴰ` / `low-tw1` | 同上 / `h₁ d` | 同上 / `inc d self` | Kc | `KD` / {Ω 树} | `Bdᴮ (rt β) K₀` |
| `YiXTReb.lowˣ` | 同上 | 同上 | Kc | `KD` | 同上 (另带 `Below`, `AboveL`) |
| `YiSDIface.lowΩ` | 同上 | 同上 | `apᴮ K` (没接到 `app`) | {Ω 树} | `Kept` 顶槽位 + 每个 a 的 `CondΩ` |
| `YiWRZero.lowᶻ` | 0 | `z≤` | `apᶻ K` | 全体 | `Bdᶻ`, 对一切状态 |
| `YiWREnd.Wire.LowSlot` | 槽位层 `at a p` | `posW a p` | 头 κ (`Nu a p κ`), 前缀 K | 全体 | `Inv s K` |
| `YiSOLow.Keepᵗ`/`lowAll`/`core` | ∀ j | ∀ w | ∀ κ (`Rd j κ`), 前缀 K | `Dm` | `Good × SlotBd` + 底值 ≥ ψ_κ(K) |
| `YiSOUp.UpQ`/`upAll` | 上折 j′ → ℓ | 下行链 d | ∀ κ, 前缀 K′ | 全体 | `Rd ℓ κ` + 底值界 |
| `SelfKeep` / `UpKeep` (抽象) | = ℓ / 上折 | `self` / d | `cl ℓ (P ⊕ ·)`, 头固定为 0 | 全体 | `Gb`, 底值界 |
| `YiGTSelf.Self.LF` / `YiWCTw1.Self₁.LF` | = ℓ / = j₁ | `self` | ν / 1, 前缀 t | 全体 | 底值界 (+ `NodeFrame` / `pen₁`) |

**新接口 (不读记号, `YiMIIface.MI`)**
```agda
Hold : ∀ {ℓ j} → (Tr ℓ → Tr j) → (T → T) → (Tr ℓ → Set) → Set
Hold {ℓ} {j} Φ ap D = ∀ {a x} → D x → R ℓ a x → R j (ap a) (Φ x)
LowAt b w β K D = Hold (ψ ℓ b j w β) (app K) D
Low I D = ∀ π → I π → LowAt (bs π) (pth π) (bv π) (cx π) (D π)   -- π : Pt = (源层, 目标, 底, 路径, 底值, 上下文)
KeepSys D = ∀ {a} (s : St a) K → Bdˢ s K → Hold (Φ s) (ap K) (D s)  -- FI.Sys 的状态形式
```

**今后应停用的旧名字 (只记, 没改旧文件; 判断)**
- `FI.Suff.sys→low`、`BL.SuffR.sys→low`、`QD.SuffRD.sys→lowᴰ` 改用 `MI.sys→LowAt`.
- 根状态一族 (`lowᴮ`/`lowᵗ`/`lowᴰ`/`lowˣ`/`low-tw1`/`lowᴷ`/`lowᶻ`/`lowΩ`) 定理名可以保留, 但结论类型以后写成 `LowAt`/`Hold`.
- `Keepᵗ` 改用 `RC.KeepLow`, `LowSlot` 改用 `RC.Slot.SlotLow` (或 `KeepLow` 在槽位点上的取值 `core′`), `UpQ` 改用 `RC.UpHold`.
- 五份分级实例改用 `gradedᴹ`. 底的条件: `Bdᵍ`、`Bdˢ`、`Bdᴱ` 改用 `BdΩ`, `Bdᴮ` 改用 `BdR`. `rowsᵍ`、`rowsᴮ`、`rowsᴷ` 改用 `rowsᴹ`.
- `genᴷ/ᴮ/ᴱ` 与同组的 `weak`/`lim`/`node` 改用 `Gen.genᴹ` 等. `YiSDRead` 的 `weakˢ`/`nodeˢ` 和别处可能还有的副本没有核.
- `Self.LF`、`Self₁.LF` 改用 `SelfF.LF`.

#### 2. 文件表 (都在 `<仓库>/probes/OCF/Lean/`)

| 文件 | 代码行 / 总行 | 冷编退出码 | 峰值内存 | 读记号 |
|---|---|---|---|---|
| YiMIIface.lagda.md | 115 / 183 | 0 | 0.22G | 否 (导入闭包 21 个模块, 禁用命中 0) |
| YiMIConv.lagda.md | 163 / 225 | 0 | 0.33G | 否 (闭包 46 个模块, 禁用命中 0) |
| YiMIGraded.lagda.md | 143 / 202 | 0 | 1.58G | 是 |
| YiMIRead.lagda.md | 92 / 156 | 0 | 1.59G | 是 |
| YiMISelf.lagda.md | 81 / 115 | 0 | 1.50G | 是 |

冷编前删了这五个模块自己的 `.agdai`, 每份日志里只有自己模块的 `Checking` 行. 检索禁用构造和本机路径, 命中都是 0.

#### 3. 定理表 (全部是编译定理)

**YiMIIface (不读记号)**
- `lowKeep→ : LowKeep → Low Iᴷ Dᴷ`, `→lowKeep : Low Iᴷ Dᴷ → LowKeep`. 白话: `LowKeep` 就是不变式取 `Gb×Wl×Bd`、域取 `Gx` 的 `Low`.
- `selfKeep→ : SelfKeep → SelfP` 与 `→selfKeep`; `upKeep→ : UpKeep → UpP` 与 `→upKeep`. 白话: 抽象的自身保持和上折保持都是 `Hold`.
- `sys→LowAt : {D : ∀ {a} → St a → Tr a → Set} → KeepSys D → ∀ {ℓ} (s : St ℓ) (K : Cxt) → Bdˢ s K → (b : Bs ℓ) (w : j ⊑ ℓ) (β : Bt j) (Kc : Cx ℓ j) → (∀ x → Φ s x ≡ ψ ℓ b j w β x) → (∀ t → ap K t ≡ app Kc t) → LowAt b w β Kc (D s)`. 白话: 状态形式的保持落到一点.
- `hold-dom : … (∀ {x} → D′ x → D x) → Hold Φ ap D → Hold Φ ap D′`, `low-mono`. 白话: 域与不变式上反变.
- `fi-keep : KeepSys 𝒮 (λ _ → ⊤ᴰ)`; `fi-low`/`fi-low′`, `bl-low`/`bl-low′`, `rd-low`/`rd-low′` (各对两个同类型, 结论都是 `LowAt b w β Kc …`); `qd-keep : KeepSys 𝒮 (Dom.D 𝒟)`. 白话: 三份旧 `sys→low` 与新推导给出同一结论.

**YiMIConv (不读记号)**
- `lowᴮ→ : OutR sysᴮ sysᴬ keepᴬ embᴮ Le keepᴮ → Sys.Out sysᴬ Le keepᴬ fallᴬ → (β : Tr⁺ j) (K₀ : Cxtᴮ) → Bdᴮ (rt β) K₀ → (Kc : Cx ℓ j) → (∀ t → apᴮ K₀ t ≡ Laws.app 𝔾 𝔻 Kc t) → LowAt (o , r , B) w β Kc ⊤ᴰ`
- `lowᴰ→`, `lowˣ→`: 前提同各自旧定理, 结论 `LowAt (o , r , B) w β Kc KD`.
- `lowᵗ→ … → LowAt (Ok-tw (suc n) , rb-tw (suc n) , B) (inc c′ v) β Kc ⊤ᴰ`.
- `low-tw1→`, `low-tw1′ … → LowAt (Ok-tw 1 , rb-tw 1 , B) (inc d self) β Kc Ωᴰ`. 后者由 `lowᴰ` 经 `hold-dom` 重新得到.
- `lowᶻ→ : OutDN sysᶻ Le fallᶻ → AboveL sysᶻ keepᶻ Dᶻ xtᶻ → KeepSys sysᶻ (λ _ → ⊤ᴰ)`; `lowᶻ-pt … → LowAt (o , r , B) (z≤ ℓ) β Kc ⊤ᴰ`.
- `lowΩ→ : (β : Tr⁺ j) (K : Cxtᴮ) (ev : Kept (inj₁ (inj₁ tt))) → (∀ {a} → Rᵍ ℓ a (proj₁ (Ωt ℓ)) → CondΩ β K ev a) → Hold (λ x → proj₁ (Φᴮ (rt β) x)) (apᴮ K) Ωᴰ`; `lowΩ-pt` 接到 `LowAt`.
- `lowᴷ→ … → LowAt (o , ((λ _ _ → nothing) , rc) , B) (inc c′ v) β Kc ⊤ᴰ`.

**YiMIGraded (读记号)**
- `ᵍ≡ : gradedᵍ ≡ gradedᴹ foldᵍ rowsᵍ proj₁ GR.Nu GR.Rd E.T zeroT idT Bdᵍ`, 以及 `ᴷ≡`、`ᴮ≡` (`Rd = Dom`)、`ᴱ≡` (`X = E.T × E.T`, `proj₁`, `proj₂`, `Bdᴱ`)、`ˢ≡`, 都是 `refl`. 白话: 五份实例是一份实例的取值.
- `ᵍBd : ∀ {ℓ j} → Bdᵍ {ℓ} {j} ≡ BdΩ {Rb = TB.Rb} E.T ψ₀`, 以及 `ˢBd`、`ᴱBd`、`ᴮBd` (`BdR`).
- `bnd⇔`: `R j (E.ψ ν K ∷ []) β` 与 `R j (apE (ν , K) []) β` 互推.
- `rows≡ᵍ : rowsᵍ ≡ rowsᴹ foldᵍ idβ`, `rows≡ᴮ`, `rows≡ᴷ`.
- `Gen.genᴹ : ∀ ℓ → Gen⁺ _≤ᵀ_ ℓ`, `weakᴹ`, `limᴹ`, `nodeᴹ`. 旧的取值: `genᴷ′ : ∀ ℓ → FI.Gen⁺ (gradedᴷ K lifted) (domsᴷ K lifted) _≤ᵀ_ ℓ`, `genᴮ′`, `genᴱ′`, 以及同组的 `weak`/`lim`/`node`. 证明照抄 `YiFIGen.genᴷ`.

**YiMIRead (读记号)**
- `slot→ : LowSlot → SlotLow`, `→slot : SlotLow → LowSlot`.
- `keepᵗ→ : … → (∀ {t x} → GR.R a t x → D x → Keepᵗ st K t x) → KeepLow st K D` 与 `→keepᵗ`.
- `lowAll→ : Low Iˢ Dˢ`; `core→`, `core′ : … → LowAt (o , r , B) (posW a p) (B (at a p) (posW a p)) (κ , K) (Dm (o , r , B))`.
- `upQ→`/`→upQ`, `upAll→ : UpMis → ∀ {ℓ} (j′ : L) (d : O.Dn ℓ j′) → UpHold d`.
- `zero→lowKeep : KeepSys sysᶻ (λ _ → ⊤ᴰ) → LowKeep`, `chain→lowKeep : W₀.ChainRel → LowKeep` (都在 `gradedᴮ`/`domsᴮ` 上).
- `wl-inc : ∀ {j s h} (c : Ch s) (v : j ≤ h c) → Wlᵍ (inc {h = h} c v) → ⊥`. 白话: 经孩子的路径不在主线的 `Wl` 里.

**YiMISelf (读记号)**
- `SelfF.LF : ∀ {a x} → GR.R (nd s h) a x → GR.R (nd s h) (E.ψ ν (t ++ a) ∷ []) (proj₁ (F x))`. 前提是像 F 的五条律 (单调, 后继 `⊴`, 结点 `⊴`, `pen`, 嵌入行 `upF`) 加底值界.
- `InMI.self-hold : Hold (λ x → proj₁ (F x)) (λ a → E.ψ ν (t ++ a) ∷ []) ⊤ᴰ`.
- `gt-self`, 类型与 `GT.Self.LF` 相同: `∀ {a x} → GR.R (nd s h) a x → GR.R (nd s h) (E.ψ ν (t ++ a) ∷ []) (proj₁ (GT.Self.F s h o r B ν t fr β mb x))`.
- `gt-low : LowAt (o , r , B) self β (ν , t) ⊤ᴰ`, 在 `foldᵍ` 上.
- `wc-self`, 类型与 `WC.Self₁.LF` 相同: `∀ {a x} → GR.R j₁ a x → GR.R j₁ (E.ψ WC.𝟙 (t ++ a) ∷ []) (proj₁ (WC.Self₁.F o r B t β mb x))`.

#### 4. 第一个障碍

没有数学上的障碍. 几处工程上的限制:
- 自身折叠只对像 F 参数化, 没有直接套 `FI.Sys`/`KeepLaw` 记录. 原因: 那里的 `⊴` 是 `Laws._⊴_`, 而 `GR` 一侧用的是 `YiKVRel._⊴_`; 嵌入一行要孩子层上折的保持, 只能作前提 `upF`.
- 第 0 层 (`zero-self`) 不在 `SelfF` 里.
- `YiRBSib.ψ` 不是某个 `Fold` 记录的 ψ, 所以 `wc-self` 只落到 `Hold`, 落不到 `LowAt`.

#### 5. 偏离与事故

**偏离 (都只加新内容, 没改旧文件)**
- 超出简报列表另做了: `lowᴷ`、`UpQ`/`upAll`、`SelfKeep`/`UpKeep`、生成原理的合并、`zero→lowKeep`/`chain→lowKeep`、`wl-inc`.
- 接口取名 `Hold`, 因为 `Pres` 和 `YiAbsFrame.Pres` 重名.
- `gradedᴹ` 除了上下文头和读法域, 还要对折叠、`bt`、`Nu`、`Bd` 参数化, 否则五份旧实例不能逐字 `refl`.
- 换算定理大多是定义展开, 证明很浅. 内容主要在参数表.

**事故**
- 第一次编译套了 `/usr/bin/time`, 被沙箱的 sysctl 拦下, 退出 1; 这不是 agda 的退出码.
- 之后修了几处类型错误 (未标类型的 ∀ 绑定、重名、`SuffD` 没有 `sys→lowᴰ`、隐式参数 `Rb`). 没有出现 251.

**没读、只凭转述的**
- `AuditF.md` 及附件, `YiXTIface.stuck`, `YiSDRead.CellRaise`, `YiLLLeafNeg.noLeafOk`, `YiHCRel.Exᴴ` 与 G5: 没读.
- `YiWCWire.StepW`: 只读了文首.
- `YiSOEnd`: 只读了文首与 `Full.lowslot₂`.
- 没有遇到性能问题, 所以 `EBOHandbook` §4.2/§4.6 和 Bedrock 性能手册没读.

临时文件: `<实验目录>/work/YiMI/YiMIStep0.agda`, 编译日志在同一目录.

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：合并同类接口（不读记号）（前缀 YiMI，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Opus 5.5。同批另三路与你互不导入。AGENTS："同类引理以不同名字第二次出现时, 合并成一条并写进接口"。不改任何已有文件，只新建。

#### 作者的决定与背景（2026-11-17）
- 作者要求（原文）："更加结构化地高屋建瓴地分析，而不是盲目地一站一站深入"。作者选项原文："统一收量化域的检验 (Recommended), 合并同类接口 (Recommended), 出口条件与核心证明的耦合, 辅助系统的底取目标层起点（改候选定义）"。前缀 `YiQV`（Fable 5.2）、`YiMI`（Opus 5.5）、`YiXC`（Opus 5.5）、`YiAB`（Fable 5.2），互不导入。**主线定义不动**；换基折叠 `YiBSFold` 是候选。
- **现状（主审复核过，都在 `probes/OCF/Lean/`）**：换基候选上的终点条件定理有两版：`YiWREnd.Wire.ebo-endˢ`（前提 `LowSlot` 与出口条件；两个具体不变式下 `LowSlot` 被审查 F 路编译否定，加强不变式后接线合上，见留档 `probes/Survey/Reports-2026-11-16/AuditF.md` 与附件 `attachments/AuditF-*.txt`），以及不经原接线、带域的 `YiSOEnd.End.ebo-endᴬ`、`YiSOTw1.EndU.ebo-endᵁ`（前提：域 `Domˢ`、`NodeMis`、`RebRow`、`RootBd`、`RootIn`、`UpMis`，加出口条件）。`YiSOLow.Sys.Main.lowAll`、`YiSOUp.UpAll.upAll`：多目标系统里保留判定与参照一致的格对一切层号一次归纳证出。
- **剩下的义务（判断：都出自量化域太宽，第四、五次同形出现）**：`YiSOLow.Sys.NodeMis`（树走链而参照保持 Ω 余尾：审查 F 路 FCross 那一格、`YiXTIface.stuck` 的情形；树保留而参照坍缩：读法允许取空时出现）、`YiSOUp.UpMis`（上折同类一格）、`YiSOLow.Sys.RebRow`（换基行：路由落在地板之上时替身加第 0 层尾项，域取全体时判断为假；`YiSDRead.CellRaise` 未走通）、`YiSOEnd.RootBd`（塔第 2 项起根状态每个槽位每个读法上的 Leaf；全域 Leaf 在 Ω 形状上有否定 `YiLLLeafNeg.noLeafOk`）、`YiWCWire` 的 `StepW`（链的步：上下文前缀可以超出链的上确界）。出口条件 `YiHCRel.Exᴴ` 要求推导里每个向下封闭步 `mc` 两边是标准形、较大一边可数，与核心证明里 `mc` 的用法耦合（审查 F 路 G5）。
- 可用的读回域工具：`YiGLDom`（`Dom`、`dom-top`、`leafᴰ`、`liftᴰ`、`dom-keel`；`rd-not-dom`）、`YiQDFold`（树的域 `KD`、`kd-dw`、`Ωt-in`/`Ωt-out`）、`YiUFDom.QDTw.Ωt-tw`、`YiBCCover`（证据在读回域上处处满）、`YiSDRead.sub-read`/`top-read`（读回形式）、`YiBAEbo.BelowE`（参照取 ψ_ν、条件 `KeepAt`）、`YiSOTw1.root-bd1`（塔第 1 项根状态无前提）。

#### 本路的问题
同一条 "朝低层保持" 至少七个名字：`YiAbsGIface` 的 `LowKeep`、`YiBLFold` 的 `lowᴮ`/`lowᵗ`、`YiXTReb.lowˣ`、`YiQDFold` 的 `lowᴰ`、`YiSDIface` 的 `lowΩ`、`YiWRZero` 的 `lowᶻ`、`YiWREnd` 的 `LowSlot`、`YiSOLow` 的 `Keepᵗ`/`lowAll`。区别在五个参数：目标、路径、上下文的头 ψ_ν、量化域、不变式。分级结构实例至少五份（`YiGIInst.gradedᵍ`、`YiFIGen.gradedᴷ`、`YiWREnd.gradedᴮ`、`YiBAEbo.gradedᴱ`、`YiSDRead.gradedˢ`），生成原理两份以上；自身折叠的保持两份（`YiGTSelf.Self.LF` 对 `YiTBRow.ψ`，`YiWCTw1.Self₁.LF` 对换基核）。

#### 要做的（按序）
0. 读这些定义的签名与定义体，写一张对应表（名字 × 五个参数的取值）。写出一条带五个参数的接口陈述（不读记号的那部分放不读记号的文件），临时文件编译类型。
1. 证每个旧陈述是新接口的实例（编译的换算定理，新 → 旧，或旧 → 新，看哪个方向有意义）；做不到的写清为什么（例如量化域不同而不可比）。
2. 分级结构：写一份对上下文头与读法域参数化的实例，证五份旧实例是它的取值。自身折叠的保持：对折叠参数化（复用 `YiAbsGIface`/`YiFIIface` 的折叠接口），证两份旧引理由它推出。
3. 交：对应表、新接口、换算定理清单；指出哪些旧名字今后应停用（只记，不改旧文件）。

#### 规则（主审写给内部子智能体，必须照做）
- **先读** `AGENTS.md` 全文；性能问题先查 `probes/Survey/EBOHandbook.md` 4.2、4.6 节与 Bedrock 性能手册 `<Bedrock>/dev/cubical-agda-performance.md` 的 C-9（在变量上陈述、定义等式作假设、在唯一调用点实例化）、C-10（具体的站作 opaque 原子或模块参数）、S-1/S-3（重的构造在出生处封进 opaque，并在同一块里导出规格等式）、C-24、Q-1（`--profile=definitions`）、Q-23（量底价、二分）、H-6（251 之后不原样重跑）。
- **只新建文件**，放 `probes/OCF/Lean/`，用你的前缀（见上）。不改任何已有文件，不碰 `src/`、`archive/`，不碰别的前缀。中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行（判决与档位、做了什么、不否定什么、入口）；代码之间只写范围与不显然的理由。一次性的试验放你的临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要把前三个也写上，否则报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（写 `<实验目录>`、`<仓库>`）。
- **编译**（仓库根目录）：`agda +RTS -M6G -RTS --library-file=<库文件> -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`；临时目录的纯 `.agda` 另加 `-i <你的临时目录>`。退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时；154 Agda 内部错误。报退出码不经过管道。同时只跑一个 agda，堆上限 6G（同批另有四路，外部广撒网也可能在编，机器共 64G；峰值超过 4G 先改形状）。不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下，写字面路径）。大的 `refl` 前加 `timeout 600`。
- **停下的条件**：退出 251 时不原样重跑，先按 C-9、C-10、S-1 改形状并定位（附 profile 或二分数据）；改过形状后同一上限仍撞墙才停。同一处两次重新设计仍过不了检查器也停。若某一步要改树、折叠或合法性的定义，停下回报。没有编译的否定时只写 "未走通"。
- **过程**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译。动手证一般形式之前先用临时文件检查前提可满足；已有引理先检索（`grep`）再写，不重证，搬来的证明在文首写明来源。查签名用检索，不整篇读大文件。
- 不在你的临时目录与你前缀的新文件之外写、删、移任何东西；不 `pkill`，不写 `/tmp`，不装包，不提交，不改 `probes/README.md`、`probes/LOG.md`、台账与留档。
- **两条已更正的事实**（不要再照旧说法写）：`YiMXNote.¬Mono` 否定的是记号一侧非标准形项的项序单调，**不是**树侧折叠的跨层单调（树侧跨层单调目前没有编译的否定）；`YiKWObjects.kept` 是新封装的对象，与 `YiC1Slot` 不透明块里的 `kept` 不是同一个。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造与本机路径为 0；文首标 "不读记号" 的文件用 `python3 probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 查导入闭包。

#### 回报（最后一条消息就是回报，主审会原样留档）
1. 判决：先说对纲领与目标意味着什么；各步到哪一步；问题表（问题、位置、档）。档分三种：编译定理、有限测试、判断。
2. 文件表：代码行、冷编退出码。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理；是数学上挡住还是工程上挡住。
5. 偏离与事故；没有读、只凭转述引用的东西。
不用 "只差"、"自然" 一类形容；判断与定理分开写。

