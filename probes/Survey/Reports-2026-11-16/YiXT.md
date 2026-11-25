# 把缺陷都在分叉出口写成定理（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-17 04:52 至 05:35 |
| 工具调用 / agda 编译 (粗数) | 90 / 27 |
| token (usage 字段，按消息去重) | 输出 262690；新写入缓存的输入 485950；读缓存的输入 25742002；其余输入 150 |
| 写过的仓库文件 | `YiXTCur.lagda.md`, `YiXTIface.lagda.md`, `YiXTKp.lagda.md`, `YiXTReb.lagda.md` |
| 文件前缀 | `YiXT` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 4 件全部退出 0，禁用构造 0，导入闭包干净；结点出口的参照义务在两条参照前提 Below、AboveL 之下恰为分叉一份（split、need、exact）；无证据而目标有同层真槽位处结点出口无解（stuck）；现行折叠对角点与 R80 实例点落入（diag-stuck、r80-stuck）；换基在读回域里没有分叉出口，只要 Below 与 AboveL（nodeᴮ、nodeᴬ、lowˣ）；两条前提对记号参照是否成立未查 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b78/YiXT.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。在仓库根目录 `<仓库>` 下工作。只新建你前缀的文件，不改任何已有文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

### YiXT 回报："缺陷都在分叉出口"升为编译定理（不读记号）

#### 1. 判决

**对纲领与目标意味着什么.** 纲领四条都没有触碰. 树、折叠、合法性都没改. 新建的 4 个文件没有公设、洞, 也没有停机或正性编译指示. 导入闭包对禁用表 0 命中, 闭包里 `OCF.Align` 模块数为 0.

对 "让树自足" 的进展:
- 出口分类按树自己的字面数据陈述, 用到层号路径与 "目标有没有同层的真槽位".
- 两条参照前提也按同样的字面数据陈述.
- 定理对一切层号、一切状态成立, 不按站定制, 合于 "闭包定理与阶段无关".

CompareTable 的主结论 "结点上的缺陷都在分叉出口" 在结点出口这一半已是编译定理 (条件档). 它不涉及值. 两条参照前提 `Below`, `AboveL` 对记号参照是否成立, 是判断, 未查.

**简报的说法要收紧一处.** 树一侧的义务 (`NodeTree`) 在三个出口上都直接造出来了, 分叉出口也不例外 (树在那里走链). 所以 "剩下的恰是分叉一份" 剩下的是参照一侧的义务: 参照在分叉出口也必须走链. 在 "无证据, 而目标有同层真槽位" 的点上, 这和 `Below` 矛盾. 对角分叉与 R80 的分叉都属于这种点.

**各步到哪.**
- 第 0 步: 陈述在临时文件编译通过 (退出 0), 按上面收紧后的读法成立.
- 第 1 步: 现行折叠 (`YiTBRow.ψ` 的全部状态) 与换基折叠 (复用 `YiBLFold.Pack`/`YiQDFold.QDPack` 的两个系统) 各给一次, 并接进 `lowᴰ` 的流程, 得到 `lowˣ`.
- 第 2 步: R80 与 R94 都给了编译事实.
- 第 3 步: 即本报告.

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 树一侧取由出口给出的 `nt` 时, 在 `Below`, `AboveL` 之下, 参照义务 `NodeRef` 当且仅当分叉一份 | `YiXTIface` `XT.split`, `need`, `exact`, `out` | 编译定理 (条件) |
| 不管树一侧怎么选: 无证据处结点出口只能走链; 再加 "目标有同层真槽位", 则 `Below` 与 "余尾 ω 不是余尾 Ω" 推出结点出口不成立 | `XT.noev→ω`, `stuck`, `out-stuck` | 编译定理 (条件) |
| `Below` 与 `AboveL` 的作用点互不相交 (目标到自己真槽位的层号没有字面路径) | `YiXTKp` `no-cyc`, `apart` | 编译定理, 无前提 |
| 现行折叠: 对一切 Ω 形状层号, 对角点 (孩子 c 里的槽位字面就是目标 `h c` 的槽位) 的出口是分叉, 且与 `Below` 冲突 | `YiXTCur` `diag-cross`, `diag-stuck`, `diag-¬out` | 编译定理 (条件) |
| 上一行的前提可满足: 平凡模型里全部前提成立, 给出结点出口; 二值模型里 `Below` 与不相交成立, 结点出口不成立 | `modelA-out`, `modelB-¬out` | 编译定理 |
| 换基主系统: 域 `KD` 里只有保留出口, 结点出口只要 `Below`; 对现有树一侧 `ntᴮ` 同样成立 | `YiXTReb` `nodeᴮ`, `nodeRᴮ` | 编译定理 (条件) |
| 换基辅助系统: 目标路径 `lift` 一致, 没有分叉出口, 只要 `Below` 与 `AboveL` | `YiXTKp` `kp-uni`, `uni-notX`; `YiXTReb` `nodeᴬ` | 编译定理 (条件) |
| 换基的 `lowᴰ` 结论只要非结点的各条出口加 `Below`×2 与 `AboveL`, 分叉一份不出现; 平凡模型里前提全部成立 | `lowˣ`, `modelA-low` | 编译定理 (条件); 实例: 编译 |
| R80 在塔各项上就是下标层上的判定 | `r80-tw` | 编译 (refl) |
| R80 一般会分叉: 有对一切 Ω 形状层号的落 `nothing` 引理; 读回域里的实例在塔第 3 项的孩子层号 `L′` 上, 出口是分叉, 且与 `Below` 冲突 | `drop-r80`, `r80-cross`, `r80-lit`, `r80-stuck` | 编译; 实例路径是手写的, 实际折叠是否走到: 未查 |
| R94 本身是进孩子的行. 塔第 2 项上材料经孩子 0 进入, 目标在非零孩子里时, 现行折叠落到回退 "x 的折叠 ⊞ ψ₀(y)" | `r94-fallᶻ` | 编译 (形状档) |
| R94 在 EBOᶻ 闭项计算里确实走到上一行 (Λ 的孩子 m ≥ 2, 基的请求路径 `inc m (inc c (ink self))`) | 纸面追踪 | 判断 |
| R94 在换基折叠上: 目标在地板之下时经 `back` 在孩子 0 上朝原目标折; 目标是孩子层号自身时, 材料只进第 0 层尾项 | `r94-backᴮ`, `r94-seenᴮ` | 编译 (形状档) |
| `Below`, `AboveL` 对记号参照成立 | — | 判断, 未查 (要验收文件) |
| 带不相交的非平凡模型里 `Below` 与 `AboveL` 同时成立 | — | 未做 |
| 嵌入行 (R95) 的 "缺陷在分叉" | 本路只编译了结点出口 | 仍是形状档 (`fallᶻ`, `r94-fallᶻ`) |

#### 2. 文件表

| 文件 | 代码行 / 总行 | 冷编退出码 | 峰值内存 (RTS 驻留) |
|---|---|---|---|
| `probes/OCF/Lean/YiXTIface.lagda.md` | 124 / 200 | 0 | 205MB |
| `probes/OCF/Lean/YiXTKp.lagda.md` | 154 / 240 | 0 | 213MB |
| `probes/OCF/Lean/YiXTCur.lagda.md` | 223 / 327 | 0 | 210MB |
| `probes/OCF/Lean/YiXTReb.lagda.md` | 165 / 235 | 0 | 336MB |

冷编方式: 删掉这 4 个自己的 `.agdai` 后按依赖顺序逐个编译, 6G 上限, 每个 2 到 4 秒. 每份日志都只有自己模块的 `Checking` 行.

自查:
- 禁用构造与本机路径检索: 0.
- `importclosure.py`: 4 个都 OK, 禁用表命中 0.

临时文件 (纯 `.agda`, 不进仓库):
- 第 0 步的陈述文件 `<实验目录>/work/YiXT/XTStmt.agda` (退出 0).
- R80 读回域实例的试验 `<实验目录>/work/YiXT/R80Can.agda` (退出 0), 结果已搬进 `YiXTKp`.

#### 3. 定理表

##### 3.1 抽象接口 (`YiXTIface`, 模块 `XT 𝔾 𝔻`)

参数: 任意系统 𝒮, 保留律 𝓀, 域 D, 以及 `xt : XTree`.

**`XPick s p`** (出口):
- `kept` 带保留证据;
- `high` 带无证据与 `j ⊑ slL a p`;
- `cross` 带无证据, 以及某个结点的孩子 c, c′, 满足 `slL a p ⊑ h′ c` 且 `j ⊑ h′ c′`.

**`XTree`** 的字段: `xp` (出口), `ch` (无证据时树自己的链与支配), `lvl` (保留时层号不变), `mvR` (换型下关系照搬). `nt` 由出口给出.

**`Below`**:
```
Below = ∀ {a} (s : S.St a) K → S.Bdˢ s K → (p : Sl a) → ∀ {t κ} → CΩ t κ → Nu a p κ
  → (q : Sl j) → slL j q ≡ slL a p → RefKeepAt s K q t κ
```
白话: 目标有一个与槽位同层的真槽位时, 参照保留余尾 Ω. 只看字面层号, 不看树是否保留.

**`AboveL`**:
```
∀ … (ne : S.Ev s p → ⊥) → j ⊑ slL a p → RefChain s K p g t (ch s p g d ne)
```
白话: 没有证据, 且目标到槽位层号有字面路径时, 参照沿树的链走.

**`PartX`**: 只在 `cross` 出口上取 `RefChain s K p g t (ch s p g d ne)`, 另两个出口上是 `⊤`.

**`split`**:
```
split : Below → AboveL → At PartX → NodeRef 𝒮 𝓀 D nt
```
白话: 保留一份由 `Below` 与 `lvl` 给出, 同层或高于一份由 `AboveL` 给出, 剩下只要分叉一份.

**`need`**:
```
need : NodeRef 𝒮 𝓀 D nt → At PartX
```
白话: 分叉一份是必要的.

**`exact`** 与 **`out`**:
```
exact : Below → AboveL → (NodeRef 𝒮 𝓀 D nt → At PartX) × (At PartX → NodeRef 𝒮 𝓀 D nt)
out : Below → AboveL → At PartX → NodeOut 𝒮 𝓀 D
```

**`stuck`**:
```
stuck : Below → ∀ {κ} → (∀ {u} → Cω u → CΩ u κ → ⊥) → ∀ {𝓀 : S.KeepLaw} {a} (s : S.St a) K → S.Bdˢ s K
  → (p : Sl a) {t : T} (g : SlT a p → Tr a) → CΩ t κ → Nu a p κ → (S.Ev s p → ⊥)
  → (q : Sl j) → slL j q ≡ slL a p → NodeRes 𝒮 𝓀 s K p g t κ → ⊥
```
白话: 对任何保留律都成立. 无证据而目标有同层真槽位的点上, 结点出口没有解. `out-stuck` 是它的 `NodeOut` 版本.

**`OutDN`, `OutRDN`, `withN`, `withRN`**: `OutD`/`OutRD` 去掉结点一条, 再补回.

全部是编译定理.

##### 3.2 证据形式的出口与 R80 (`YiXTKp`)

- **`kexit`**: `∀ {j} a o p (w : j ≤ a) → KExit j a o p w`. 把 `kp-exit` 换成以 "kp 返回保留" 为证据的三种出口.
- **`kp-lvl`**: 保留时 `at j q ≡ at a p`, 由 `kp-good` 给出.
- **`kp-uni`**: `(ℓ : L) (o : Ok ℓ) (p : Pos ℓ) {j : L} (w : j ≤ ℓ) → Uni w → Exit₂ (at ℓ p) (kp ℓ o p w)`. 路径只由 `self`/`inu` 组成时, 出口只有保留与同层或高于.
- **`uni-notX`**: 由 `kexit-uni` 得到的出口不是分叉.
- **`no-cyc`**: `(j : L) (q : Pos j) → j ≤ at j q → ⊥`. 证明用层号严格后代关系的良基 (`wfᴸ`).
- **`apart`**: `∀ {j a} (p : Pos a) (q : Pos j) → at j q ≡ at a p → j ≤ at a p → ⊥`. 白话: `Below` 与 `AboveL` 不会在同一点同时被要求.
- **`r80-tw`**:
  ```
  kp (tw (suc n)) (Ok-tw (suc n)) (inj₁ t) (inu vs) ≡ mapK (λ z → z) refl (kp⁼ (tw n) (Ok-tw n) t (vs zero))
  ```
  由 refl 得到.
- **`drop-r80`**:
  ```
  Cross (h zero) (proj₂ (proj₁ o) zero) (vs zero) → kp (nd (sΩ k) h) o (inj₁ t) (inu vs) ≡ nothing
  ```
  对一切 Ω 形状层号.
- **`r80-cross`**: `IsCrossK (kexit L′ o′ (inj₁ (inj₁ tt)) (inu vs′))`. 其中 `L′ = tw 2 ⊕ ↑(Ωt (tw 2))` 是塔第 3 项的一个孩子层号, 证据 `o′` 取自 `Ok-tw 3`.
- **`r80-lit`**: `at (tw 2) (inj₁ (inj₁ tt)) ≡ at L′ (inj₁ (inj₁ tt))`.

##### 3.3 现行折叠 (`YiXTCur`)

系统 `sysᵀ`: 状态是 `YiTBRow.ψ` 的全部参数 (任意比较表 `Rb`), 域取全体.

- **`exactᵀ`, `outᵀ`**: §3.1 的 `exact`, `out` 在 `xtᵀ` 上的实例. 前提: 第 j 层关系的生成规则 (链要用).
- **`diag-cross`**: `IsX (xpᵀ (sᵈ o r B β) (pᵈ p′))`. 路径 `inc c self`, 槽位 `inj₂ (c , inj₂ p′)`.
- **`diag-stuck`**:
  ```
  Below sysᵀ → ∀ {κ} → (∀ {u} → Cω u → CΩ u κ → ⊥) → ∀ o r B β (p′ : Pos (h c)) K → Bd (sᵈ o r B β) K
    → {t} (g) → CΩ t κ → Nu (nd (sΩ k) h) (pᵈ p′) κ → NodeRes sysᵀ keepᵀ (sᵈ o r B β) K (pᵈ p′) g t κ → ⊥
  ```
  对一切 k, h, c 成立. `diag-¬out` 是 `NodeOut` 版本.
- **`r80-stuck`**: 上述 R80 实例点上的同一结论.
- **`modelA-out`**: `NodeOut sysᵀ keepᵀ D⊤`, 在平凡模型里 (含生成原理 `genA`).
- **`modelB-¬out`**: `NodeOut sysᵀ keepᵀ D⊤ → ⊥`, 在二值模型里 (`Below` 与不相交成立).
- **`r94-fallᶻ`**:
  ```
  NZ c → TB.ψ Λ Ok-Λ (rbᶻ Λ) B i (inc 2 (inc c v)) β (up x 1 y e)
    ≡ TB.ψ Λ Ok-Λ (rbᶻ Λ) B i (inc 2 (inc c v)) β x ⊞ ψ₀ᶻ (tw 1) (Ok-tw 1) y
  ```

##### 3.4 换基折叠 (`YiXTReb`)

- **`nodeᴮ`**: `Below sysᴮ → NodeOut sysᴮ keepᴮ Dᴮ`.
- **`nodeRᴮ`**: `Below sysᴮ → NodeRef sysᴮ keepᴮ Dᴮ ntᴮ`. 可以直接填进 `lowᴰ` 的 `OutRDT.nodeR`.
- **`nodeᴬ`**: `Below sysᴬ → AboveL sysᴬ keepᴬ Dᴬ xtᴬ → NodeOut sysᴬ keepᴬ Dᴬ`.
- **`lowˣ`**:
  ```
  OutRDN sysᴮ sysᴬ keepᴬ embᴮ Le Dᴮ → OutDN sysᴬ Le fallᴬ → Below sysᴮ → Below sysᴬ → AboveL sysᴬ keepᴬ Dᴬ xtᴬ
    → (β) (K₀) → Bdᴮ (rt β) K₀ → (Kc) → (∀ t → apᴮ K₀ t ≡ app Kc t)
    → ∀ {a x} → KD x → Rᵍ ℓ a x → Rᵍ j (app Kc a) (proj₁ (BS.ψ ℓ o r B j w β x))
  ```
- **`modelA-low`**: `lowˣ` 的平凡模型实例, 在塔第 1 项上.
- **`r94-backᴮ`**: 左边 (路径 `ink v′`) 等于 `BS.ψ (tw 1) (Ok-tw 1) (rb-tw 1) B″ i (v′ ∙ posW (tw 1) p) β″ y`, 对某个 B″, β″ 成立.
- **`r94-seenᴮ`**: 路径 `self` 时, 左边等于 `β″ ⊞ BS.ψ (tw 1) … zero (z≤ (tw 1)) (Ωt zero) y`.

后两条是形状档.

##### 3.5 前提逐条与可满足性

| 前提 | 用在哪 | 实例 |
|---|---|---|
| `XTree` | §3.1 | `xtᵀ`, `xtᴮ`, `xtᴬ` |
| 第 j 层关系的六条规则 + 向下封闭 + 生成 | `xtᵀ`, `xtᴬ` 的链 | 平凡模型: `genA`, `genAᴮ` |
| `Below` | 各处 | `belowA`, `belowᴮ`/`belowᴬ` (平凡模型); `belowB` (二值模型, 带不相交) |
| `AboveL` | `split`, `nodeᴬ`, `lowˣ` | 只有平凡模型的 `aboveA`, `aboveᴬ` |
| 余尾不相交 | `stuck` 一族 | 二值模型 `dωB` |
| `OutRDN`, `OutDN`, `Bdᴮ`, `ec` | `lowˣ` | `modelA-low` |

**它没有说什么.**
- 没有值的定理, 不说哪一格 "掉值".
- 不说 `Below`, `AboveL` 对记号参照成立.
- 对任意树一侧, 只给了无证据处的必要性, 不给分解.
- 不处理嵌入行 (R95) 的出口.
- 现行折叠没有 `FallLaw`, 所以没有 LowKeep 的结论, 只有结点出口.

#### 4. 第一个障碍

本路没有被挡住. 第一个未解决的点是: 在带余尾不相交的非平凡模型里, 让 `XT.Below` 与 `XT.AboveL` 同时成立.
- 已编译的只有两者作用点互不相交 (`apart`).
- 判断: 这需要一个能读出层号关系的参照 (`ap` 要按 "目标有没有同层真槽位" 分别取值, 树侧不可判定). 这属于验收文件的工作, 是工程上没做, 不是数学上被挡.
- `AboveL` 里的 "参照链对着树的链", 记号参照能否满足也是判断. 树链从第一分支 `zero` 起步, CompareTable 已记过这一差别.

#### 5. 偏离与事故; 没有读的

**搬来的副本 (文首已注明).**
- `YiXTCur.AddRᵍ` 搬自 `YiQDFold.AddR`, `MoveG.byGood` 搬自 `Move.byGood`, 都只换成 `foldᵍ`.
- `YiXTReb.genAᴮ` 抄自 `YiXTCur.genA`, 换成 `foldᴮ`.
- 原因: `AddR` 绑定在 `foldᴮ` 上, 不改已有文件就合并不了. 按 AGENTS 的合并规则, 这是待合并项.
- 无证据时的链 `chainK` 已在 `YiXTKp` 里写成对任意关系通用的一份.

**事故.** 有一次用 `/usr/bin/time` 包住 agda, 沙箱拒绝 sysctl, 退出码 1 来自 time 而不是 agda. 去掉包装后重跑, 退出 0. 其余报错都是作用域与隐式参数问题, 当场改掉. 没有 251, 也没有超时.

**解释上的选择.** "现行折叠" 取 `YiTBRow.ψ` 的一切状态 (任意 `Rb`, 包括 `rbᶻ`), 域取全体, 不是 `YiFIFold` 的上折回退系统.

**没有读或只读了一部分的.**
- `YiAbsGRow` 只检索了 `Rules`, `wk⊴`; `YiRBSib` 只看了签名; `YiFINeg` 读了一部分; `YiDXFold` 只读文首; `YiTBRow` 读了第 9–120 行与第 183–191 行.
- Bedrock 性能手册没有打开 (没遇到性能问题), 只读了 EBOHandbook 4.2 与 4.6.
- "R77 的缺陷在第 3 站被问到" 与 V287 是引用 CompareTable 的转述, 没有核实.
- R94 在 EBOᶻ 里被走到是我的纸面追踪, 没有编译.
- 简报里两条已更正的事实本路没有用到.

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：把 "缺陷都在分叉出口" 写成定理（不读记号）（前缀 YiXT，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Opus 5.5。本路不读记号（验收文件除外）。同批另一路（前缀 `YiUF`）与你互不导入。

#### 作者的话与决定（2026-11-17）
- 作者对方法的担心（原文）："真的只有这样一站一站吗？能否借助记号搞清楚内在结构，然后对比树的定义（包括整个归纳类型的规则）在树的生成上，和记号+基本列定义加终止证明生成的树，在什么节点和站上有区别。我的意思是更加结构化地高屋建瓴地分析，而不是盲目地一站一站深入"。
- 对照表一路（YiCM）的结论：`probes/Survey/CompareTable.md`。保留判定 `kp` 对一切层号、证据、槽位、目标只有三个出口：保留（槽位层号有到目标的字面路径，`YiCMExit.kept-below`）、同层或高于（走链）、分叉（Ω 形状结点上，材料在孩子 c 之下，目标在孩子 c′ 之下）（`YiCMExit.kp-exit`）。表里所有值上低与未知的格都在分叉出口（判断，逐格填表；R94 的 `emb` 经孩子 0、R80 的推进经孩子 `zero` 两处未查）。分叉出口上的缺陷对参数一般地成立（形状档）：`YiCMExit.diag-slot`、`diag-same`、`tb-nz`、`fallᶻ`、`YiCMCross.drop-idx`、`drop-tw`（实例 `c′-inst`）、`chainᴿ`、`chainᵀ`、`chainᴮ`、`chain-twᴮ`；换基证据给的保留 `YiCMCross.keepS`、`keepS-lift`（未接进折叠）。
- 作者选项原文："合成一个完整候选折叠并按表核一遍 (Recommended), 把 \"缺陷都在分叉出口\" 写成定理 (Recommended)"。前缀 `YiUF`（Fable 5.2）、`YiXT`（Opus 5.5），互不导入。**主线定义不动**；候选只在新文件，进主线由作者定（AGENTS "第 4 层不反过来改前 3 层"，改动理由来自树侧，翻译账单列 "第 4 层逼出"）。
- **分叉出口的三类格与已在手的手段（主审读表的判断，未编译，要判定的就是它）**：嵌入行 → 换基（`YiBSFold`；替身不再问原材料的槽位，`YiBLIface`/`YiBLFold`）；下标侧槽位推进后分叉 → 换基证据给的路径（`keepS`）；主系统孩子侧槽位 → 读回域里不出现（`YiQDFold` 的域 `KD`：本层结点都在有保留证据的槽位上，嵌入的原材料 `⊴` 孩子层号的 Ω 树）。另：替身内部 `YiBSBase.seen` 用无表证据 `rb-no`（审查 E 路，台账 V299；`YiBCCover.rb-row` 给了替身重建层的证据，接进去要过停机检查，V149 记过一种写法不过）。
- 第七十七批（主审 8G 冷编 13 件全部退出 0，已复核）：`YiQD*`（按读回域的充分性 `SuffD.keepAllᴰ`、`SuffRD.sys→lowᴰ`；换基上的 `WithRules.lowᴰ`、`QDTw1.low-tw1`，前提全在参照一侧；`kp-good`；链一支改成按关系支配 `AddR.chain-dom`，原形状被 `YiQDNeg.Min.no-chain₁` 否定；`SubstDom.raise→SubDom`），`YiZS*`（`StepS` 在 η = ω+n+1 成立 `YiZSLit.Seg.StepS-ωn`；ω·2+1 起要 ℕ 极限层号接口，`YiZSLim.Lim₊` 四条已编译；合并 `YiZSUni.Lift.genS`、`genL`），`YiEM*`（替身码加嵌入码 `YiEMRead.Read⁺`；同步对象各来源的块在码域里；现行 `seen` 不按块的码换基 `YiEMChain.seen≠code`，要按码换基须改定义）。审查 E 路：`Reports-2026-11-16/AuditE.md`，判定件附件 `attachments/AuditE-AuditEKeep.agda.txt`（`drop₂`、`chain₂`）、`AuditE-AuditEKeepFix.agda.txt`（`keepS`、`kp₂-kept`）。
- 主线现状：第一档成品已完成；终点无条件值 ψ₀(Ω_Ω+ψ₁(Ω_ω)+ω)（`YiFYRef.target-low`）；里程碑 ψ₀(Ω_{Ω₂}) 未达到；现行折叠上同步对象那一格已关闭（V287）。

#### 本路的问题
对照表的主结论 "所有值上低与未知的格都在分叉出口" 现在是判断。把它升为编译定理：把 `YiCMExit.kp-exit` 接到保留律的证据域上，证明在 `kept` 与 `high` 两个出口上保留律（及结点出口里树一侧的义务）已经被满足或不需要，义务只剩 `cross` 出口上的格。

#### 要做的（按序）
0. **陈述**：先读 `YiFIIface`（`KeepLaw`、`Ev`、`Out`）、`YiBLIface`（`OutR`）、`YiQDIface`（`OutD`、`NodeTree`、`NodeRef`、`assemble`）与 `YiQDFold`（`kp-good`、`ntᴮ`、`ntᴬ`）的定义体。写出 "出口分解" 的陈述：对任意基于 `kp` 的系统，结点出口的树一侧义务按 `kp-exit` 分成三份，`kept` 一份由 `kp-good` 一类给出，`high` 一份由走链一支给出（对应参照一侧 "同层或高于" 的情形；参照一侧的那一半如需读记号，放验收文件或写成参照接口的前提），剩下的恰是 `cross` 一份。在临时文件里编译类型。不成立就停下回报。
1. **证明**：对现行折叠与换基折叠（`YiBSFold`，复用 `YiBLFold`、`YiQDFold` 的系统）各给一次。
2. **补查两处**：对照表没查的 R94（`emb` 经孩子 0）与 R80（推进经孩子 `zero`）落在哪个出口，效果对不对；给编译事实。
3. 交：定理的陈述与白话；它在什么前提下成立（逐个列出，给实例说明可满足）；它没有说什么（例如不涉及值）。

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

