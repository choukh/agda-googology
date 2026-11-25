# 证或否定那条单调性 (YiMono)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | high |
| 起止 (转录的时间戳，UTC) | 2026-11-11 08:02 至 08:38 |
| 工具调用 / agda 编译 (粗数) | 60 / 17 |
| token (usage 字段，按消息去重) | 输出 207814；新写入缓存的输入 366032；读缓存的输入 14348182；其余输入 114 |
| 写过的仓库文件 | `YiMonoBreak.lagda.md`, `YiMonoEmb.lagda.md`, `YiMonoOne.lagda.md`, `YiMonoVM.lagda.md` |
| 文件前缀 | `YiMono` (在 `probes/OCF/Align/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: 单调性一路返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 没有闭合：结构可比的证法有编译否定；新的无条件下界 ψ₀(Ω_{ω+1})；BTBO 下界归约到三个未证的命题；四件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 任务是 **证或否定一条单调性 `MonoT`**: 乙线的值与 BTBO 持平只缺它. 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 0 先读什么

1. `AGENTS.md` 全篇. 特别是 "量化域先取带证据的读回域" (封闭定理先对规范构造的读回域陈述; 反例对象不在读回域内的否定读作 "谓词太宽"), "用记号验收强度", Agda 一节 (选项, 文字预算, 退出码, 堆; 函数外延只准作前提), "结论的写法" (否定要有编译定理; 前提要可满足).
2. `probes/Survey/EBOHandbook.md` 只读 §4.1 到 §4.5 与 §5.4.
3. **上一路的回报原文, 全读**: `probes/Survey/Reports-2026-11-11/YiBtVal.md` (§5 写了障碍在哪). 同目录 `README.md` 里 "把值做到与 BTBO 持平" 一段.
4. 代码 (都在 `probes/OCF/Align/`, 模块名 `OCF.Align.<名>`; 都已定稿, 可以导入, 不许编辑):
   - **陈述所在**: `YiBtValBT`. 逐字:
     ```agda
     MonoT : Set
     MonoT = ∀ (x : L.Ordᶜ L.zero) (h : L.HS x) (a : R) (l : Lgl B.zero a) → x ≼ read a →
       L.ψ⁰ (L.Ω (L.toLevel x h)) ≼ read (foldᵐ₃ a l)
     module FromMono (mono : MonoT) where
       chain : ∀ n → D.γ n ≼ read (coordᵐ (pointsᵐ n))
       btbo : D.BTBOᴵ ≼ read T₃ᵐ
     mono-⊑ : ∀ x h a l → L.toLevel x h L.⊑ᴵ toIL (read0 a) (rplain a) (read0-legal a l) → ZsL (read0 a) →
       L.ψ⁰ (L.Ω (L.toLevel x h)) ≼ read (foldᵐ₃ a l)
     mono₀ : L.ψ⁰ (L.Ω (L.toLevel (D.γ 0) (D.cert 0))) ≼ read (obsᵐ (pointsᵐ 0))
     T₃ᵐ-own : ∀ n → L.ψ⁰ (L.Ω (κ n)) ≼ read T₃ᵐ     -- κ n: 第 n 个链点读成层号后的参照层号
     ```
     `FromMono.btbo` 只在链点上用 `mono`: x 取 `D.γ n`, a 取 `coordᵐ (pointsᵐ n)`.
   - 被验收一侧: `YiRawFoldTw3` (`T₃ᵐ`, `pointsᵐ`, `coordᵐ`, `obsᵐ`, `foldᵐ₃ η l = Φᵐ (read0 η) … base G.top tt tt`, `T₃ᵐ-feedback`: 链点 ηₙ₊₁ = ηₙ + 这一点上的折叠值), `YiRawFoldInst` (`closedᵐ`), `YiIrrFoldValue` (`read : R → L.Ordᶜ L.zero`).
   - 值定理的工具: `YiBtValFin` (`lower-any : ∀ K pl Lg {κ} → Corr κ K → Zs κ → L.ψ⁰ (L.Ω κ) ≼ read (closedᵐ K pl Lg)`, `lower-toIL`), `YiBtValAdm` (`toIL : ∀ K → Plain K → Legal K → L.Ordᴵ`, `toIL-c`, `Corr`), `YiBtValRel`, `YiBtValFold` (`FOLD`), `YiBtValTw3`.
   - 参照一侧: `OCF.Align.Level` (`Ordᶜ`, `Ordᴵ`, `ψ⁰`, `Ω`, `HS`, `toLevel`, `toLevel-⊑`, `_⊑ᴵ_`, `Ψ⁰-mono : a ⊑ᴵ b → ψ⁰ (Ω a) ⊑ ψ⁰ (Ω b)`), `OCF.Align.Diagonal` (模块 `Diagonal`: `γ`, `cert`, `BTBOᴵ`; 这是 Level 框架里不累加的对角线), `OCF.Align.Uniform`, `OCF.Align.Value` (`≼`, `ψ⁰-mono⁰`, `⊑-not-suc`).
   - 已有的单调与否定: `K4MonoFold`, `K4MonoValue`, `K4MonoNeg` (`ψ-⊑`, `ψ⁰-monoᵖ`: Level 族上折叠保持一个单向的逐点关系; `incomplete`, `no-cross-level`), `RR4MonoFragment` (`mono-fragment-not-cong`: ψ⁰ 对一般的第 1 层树不是值单调的; `≼-+ˡ`).
   - 累加的 BTBO: `src/OCF/BTBO.lagda.md` (只读; `ordᴰ`, `cumsum`, `ψⁿ`, `BTBO`), `OCF.Align.BTBOFull` (`BTBO≈ : tr₀ BTBO ≈ᵛ BTBOᴵ`: 累加的 BTBO 与 Level 框架的对角线同值), `OCF.Align.NoCumsum`.
   查签名用检索, 大文件不要整篇读.

#### 1 问题是什么

乙线塔的第 3 项的闭项 `T₃ᵐ` 读法是 ψ₀(Ω_Ω) (BTBO). 值定理现在到: `T₃ᵐ` 不低于参照的 ψ₀(Ω_ω); `T₃ᵐ` 的第 n 项不低于它自己层号上的参照 (`T₃ᵐ-own`). "BTBO 的参照 ≼ 读回的 `T₃ᵐ`" 只是条件定理, 前提 `MonoT`.

`MonoT` 说: 参照一侧的可数序数 x 的值不超过树一侧坐标 a 的值时, 以 x 为层号的参照 ψ₀(Ω_x) 不超过以 a 读成的层号做的折叠. 也就是 "层号按**值**变大, ψ₀(Ω_层号) 的值不降". 现成的单调性 (`Ψ⁰-mono`) 只对层号**结构**可比 (`⊑ᴵ`) 成立. 上一路的判断 (未编译): 第 1 步之后结构可比不成立, 因为树的链是累加的 (ηₙ₊₁ = ηₙ + 闭项), 后继的基本列与参照的错位, 树的层号里出现 `lim (natᴵ (k+2))` 而参照一侧是 `ωᴵ`, 两者值相同但 `⊑ᴵ` 不能经 `suc` 保持.

#### 2 目标

**最终要的是无条件的 `D.BTBOᴵ ≼ read T₃ᵐ`** (乙线第一个与 BTBO 持平的值定理; 只要下界). 证出一般的 `MonoT` 是一条路, 不是唯一的路. 每做成一步先交.

按 "量化域先取读回域" 的规则, 先对规范的链陈述, 不先对一切合法的 a:

1. **链点上的实例.** 对一切 n: `L.ψ⁰ (L.Ω (L.toLevel (D.γ n) (D.cert n))) ≼ read (foldᵐ₃ (coordᵐ (pointsᵐ n)) …)`. 可以换一个更强的归纳不变量 (不只是 `D.γ n ≼ read (coordᵐ (pointsᵐ n))`), 只要它在第 0 步成立并且被一步保持. n = 1, 2 先作为闭实例试 (看结构可比到底在哪一步, 因为什么断开; 这本身要写成编译事实, 不要只转述上一路的判断).
2. **一般的 `MonoT`**, 或它在一个带证据的定义域上的版本 (例如 a 取 `T₃ᵐ` 的链点或读回域里的坐标).
3. **否定.** 若 `MonoT` 不成立: 给编译过的反例 (具体的 x, h, a, l 与 `x ≼ read a`, 并证结论的否定), 并说明反例的 a 在不在链点的读回域里. 不在的话, 它只说明 `MonoT` 的量化域太宽, 第 1 条仍要回答.

**可以试的办法 (都是主审的判断, 没有验证; 先挑战它们再用).**
- (甲) 拆成两半. 参照一侧的纯陈述: 对 `HS` 的 x, y, `x ≼ y → L.ψ⁰ (L.Ω (L.toLevel x hx)) ≼ L.ψ⁰ (L.Ω (L.toLevel y hy))` ("ψ⁰∘Ω∘toLevel 对值单调", 只涉及 Level 族的规范树 Ω). 树一侧: `read a` 是否 `HS`, `toLevel (read a) _` 与 `toIL (read0 a) …` 是否结构对应 (`≅ᴵ` 或 `⊑ᴵ`); 若是, 由 `lower-toIL` 加前一半得 `MonoT`. 前一半可以用 `K4Mono*` 的逐点关系试: 找一个被 ψ 保持, 且由层号的值序推出的关系.
- (乙) 换参照. 树的链是累加的, 已发布的 BTBO (`src/OCF/BTBO`) 的层号也用累加. 先证累加的参照 (`tr₀ BTBO` 或它的链) ≼ 读回的 `T₃ᵐ` (两边都累加, 结构上可能对得上), 再用 `BTBO≈` 换到 `D.BTBOᴵ`. 注意 `BTBO≈` 用的 `BTBOᴵ` 是哪个模块的, 与 `YiBtValBT` 的 `D.BTBOᴵ` 是否同一个或可互换, 要核对.
- (丙) 不要单调性, 直接对链证更强的不变量: 例如参照的第 n 项对应的层号与树的第 m(n) 个链点的层号结构可比 (允许错开下标), 用 `mono-⊑`.
已知的反面证据: `mono-fragment-not-cong` (一般的第 1 层树上 ψ⁰ 不是值单调的; 但那里的树不是规范的 Ω).

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K (可交显式前提的条件定理, 另给不带它的最强结果); 堆到 6G 仍耗尽. 约化: 把缺的引理写成带确切类型的模块参数, 其余条件地证出来并编译; 说明前提在哪些实例上是定理. 没有编译的否定定理时, 只能写 "未走通", 不能写成 `MonoT` 不成立.

不要为了好证而改折叠或改参照的定义: 被验收的对象就是 `YiRawFoldTw3.T₃ᵐ`.

#### 3 规则

- **只新建文件**, 前缀 `YiMono`, 放 `probes/OCF/Align/`, 中文 literate Agda (`.lagda.md`). 都是验收文件, 文首标 "验收文件"; 允许导入带记号闭包的 `Value`, `Level` 与旧验收文件. 不改任何已有文件 (含 README, LOG, RESULTS, AGENTS), 不碰 `src/`, `archive/`. 同时在跑的另几路用前缀 `YiLean` (在 `probes/OCF/Lean/`), `YiTail`, `YiBaseVal`, 不要动也不要依赖它们的文件.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 函数外延只准作显式前提, 用到它的定理在文首标 "条件".
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Align/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Align/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块. 比较具体闭项的地方容易撞堆墙: 陈述逐字写, 大的参照树放 `opaque`, 隐式参数显式写出 (手册 §4).
- 你的临时目录: `<实验目录>/agents/mono`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 4 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 一段话说对纲领与目标意味着什么 (`D.BTBOᴵ ≼ read T₃ᵐ` 是不是定理了; `MonoT` 是证了, 否定了, 还是归约到了什么).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 条件定理写出前提的 Agda 类型与它的可满足性.
4. 办法: 走的是哪条路; 结构可比在哪一步因为什么断开 (编译事实); 试过而放下的办法与原因.
5. 第一个障碍: 精确到引理, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
6. 偏离与事故.
强度写 ψ₀(Ω_x), 标明是定理还是读法; 下界不写成同值; 不用 "只差", "自然" 一类形容.

## 回报原文

#### YiMono 一路回报：`MonoT`

##### 1 判决

**`D.BTBOᴵ ≼ read T₃ᵐ` 仍不是定理，`MonoT` 没有证，也没有否定。** 这一路做成三件事。

- **结构路线有了编译否定。** 链点上的 `MonoT` 不能经 `⊑ᴵ` 加 `Ψ⁰-mono` 证出 (`no-L`, `no-mono-⊑`)：对一切 n ≥ 1、一切下标 m 都不行，错开下标也不行。
  - 断点在第 1 步。参照层号 `D.L 1` 含字面的 ω+1。树的一切链点层号里，没有一个字面前驱 ≅ᴵ ω：链从 1 起步，`+ʳ` 加在左边，每个 ℕ 极限的第 0 项都非零。
  - 这只否定这条路，不否定 `MonoT`。
- **换了工具：前驱嵌入。** 工具是 `BTBOFullEmb` 已有的 `PEmb` 与 `Ψ-emb`。`PEmb` 指从一个层号的前驱到另一个层号的前驱的保序映射，有了它就有 ψ⁰(Ω_a) ≼ ψ⁰(Ω_b)。
  - 编译了它对后继同余 (`PEmb-suc`)，而 `⊑ᴵ` 不是 (`ω-not`)。
  - 左极限的拼接归约到各项嵌入在公共前驱上一致 (`PEmb-limˡ`)。
  - 用它在真实链点上越过了断点，得到**新的无条件下界：ψ₀(Ω_{ω+1}) ≼ 读回的 `T₃ᵐ` (`T₃ᵐ-Ωω+1`)**。原来只到 ψ₀(Ω_ω)。这是下界，不是同值。
- **BTBO 下界归约到不提 `MonoT` 的命题，都是条件定理。**
  - `DomT`：在 Level 族里比较参照层号与链点读成的具体层号 κ m。`DomT` 推出 `D.BTBOᴵ ≼ read T₃ᵐ`，不需要沿链归纳。
  - `EmbT`：前驱嵌入版，推出 `DomT`。
  - `VMᴸ`：只谈 Level 族的值单调。它推出带 `ZsL` 证据的 `MonoTᶻ`，再推出 BTBO 下界。
  - `VMᴸ` 又归约到它的后继情形 `Crux`，或归约到 `EmbV`。
  - 这五个前提都未证。

读法：`T₃ᵐ` 的 ψ₀(Ω_Ω) 仍是读法。ψ₀(Ω_{ω+1}) 现在是定理。

##### 2 文件表

都在 `probes/OCF/Align/`，都是验收文件。冷编译都是只删自己的 `.agdai` 后跑的，每份日志只有本模块一行 `Checking`，堆上限 6G。

| 文件 | 代码行 / 总行 | 冷编译退出码 | 常驻峰值 |
|---|---|---|---|
| `YiMonoBreak.lagda.md` | 94 / 141 | 0 | 1.35G |
| `YiMonoEmb.lagda.md` | 83 / 127 | 0 | 1.38G |
| `YiMonoVM.lagda.md` | 81 / 116 | 0 | 1.40G |
| `YiMonoOne.lagda.md` | 40 / 66 | 0 | 1.34G |

检索 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、`--irrelevant-projections`、`--cubical`、`Funext`、本机路径：都是 0 处。选项行全是 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。

##### 3 定理表

**YiMonoBreak (结构路线的否定)**

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| `noω` | `∀ K pK lK → NZ K → ∀ {c} → c <ᴵ toIL K pK lK → ¬ (L.ωᴵ ≅ᴵ c)` | 每个极限第 0 项非零的层号 (`NZ`)，它的字面前驱都不 ≅ ω | 编译定理 |
| `inv-nz` | `∀ n → NZ0 (read0 (coordᵐ (pointsᵐ n))) × NZ (read0 (coordᵐ (pointsᵐ n)))` | 一切链点满足 `NZ`；与折叠的内容无关 | 编译定理 |
| `no-sω-κ` | `∀ m → ¬ (L.suc L.ωᴵ ⊑ᴵ κ m)` | ω+1 结构上放不进任何链点层号 | 编译定理 |
| `sω-L1` | `L.suc L.ωᴵ ⊑ᴵ D.L 1` | 参照第 1 项的层号含字面的 ω+1 (路径：ψ⁰ 2 里的 W+W 的第 1 项) | 编译定理 |
| `no-L` | `∀ n m → ¬ (D.L (suc n) ⊑ᴵ κ m)` | n ≥ 1 时，结构可比对一切下标都不成立 | 编译定理 |
| `no-mono-⊑` | `∀ n (a : R) (l : Lgl B.zero a) → NZ (read0 a) → ¬ (L.toLevel (D.γ (suc n)) (D.cert (suc n)) ⊑ᴵ toIL (read0 a) (rplain a) (read0-legal a l))` | `mono-⊑` 的前提在 n ≥ 1、一切 `NZ` 坐标上不成立 | 编译定理 |

**YiMonoEmb (前驱嵌入与约化)**

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| `PEmb-⊑`, `PEmb-∘`, `PEmb-limʳ` | `PEmb-⊑ : ∀ {a b} → a ⊑ᴵ b → PEmb a b` 等 | 结构可比、复合、右极限都给出嵌入 | 编译定理 |
| `PEmb-suc` | `∀ {a b} → PEmb a b → PEmb (L.suc a) (L.suc b)` | 嵌入对后继同余 | 编译定理 |
| `PEmb-limˡ` | `∀ {f s b} (P : ∀ n → PEmb (f n) b) → (∀ n m {c} (r : c ≺ᴵ f n) (t : c ≺ᴵ f m) → map (P n) r ≅ᴵ map (P m) t) → PEmb (L.lim f s) b` | 左极限：各项嵌入在公共前驱上一致即可拼起来 | 编译定理 |
| `ω-not` | `¬ (L.suc L.ωᴵ ⊑ᴵ L.suc ω⁺ᴵ)` | ω⁺ᴵ 指层号 lim (n+1)；ω+1 对 ω⁺+1 不是结构可比 | 编译定理 |
| `ω-inst` | `L.ψ⁰ (L.Ω (L.suc L.ωᴵ)) ≼ L.ψ⁰ (L.Ω (L.suc ω⁺ᴵ))` | 但值上单调，经 `PEmb-suc` | 编译定理 |
| `btbo-dom` | `DomT → D.BTBOᴵ ≼ read T₃ᵐ` | 见下 | 条件定理 |
| `emb→dom` | `EmbT → DomT` | 嵌入推出 `DomT` | 编译定理 |
| `emb₀` | `Σ ℕ λ m → PEmb (D.L 0) (κ m)` | `EmbT` 在 n = 0 成立 | 编译定理 |

两个前提的类型：

```
DomT = ∀ n → Σ ℕ λ m → L.ψ⁰ (L.Ω (D.L n)) ≼ L.ψ⁰ (L.Ω (κ m))
EmbT = ∀ n → Σ ℕ λ m → PEmb (D.L n) (κ m)
```

**YiMonoVM (归约到值单调)**

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| `HS-read` | `∀ a → Lgl B.zero a → L.HS (read a)` | 合法坐标的读回有证书 | 编译定理 |
| `lvl≅` | `∀ a h pl lg → L.toLevel (read a) h L.≅ᴵ toIL (read0 a) pl lg` | 读回的层号与折叠用的层号结构互模拟 | 编译定理 |
| `vm→monoᶻ` | `VMᴸ → MonoTᶻ` | 值单调推出带证据的 `MonoT` | 条件定理 |
| `FromMonoᶻ.btbo` | `D.BTBOᴵ ≼ read T₃ᵐ`，模块参数 `mono : MonoTᶻ` | 沿链归纳 | 条件定理 |
| `btbo-vm` | `VMᴸ → D.BTBOᴵ ≼ read T₃ᵐ` | 值单调推出 BTBO 下界 | 条件定理 |
| `crux→vm` | `Crux → VMᴸ` | 对 `x ≼ y` 的推导归纳；零与两条极限是现成的，只剩 `s≼s` | 编译定理 |
| `embV→vm` | `EmbV → VMᴸ` | 经 `Ψ-emb` 一行 | 编译定理 |

前提的类型：

```
VMᴸ  = ∀ (x : L.Ordᶜ L.zero) (hx : L.HS x) (y : L.Ordᶜ L.zero) (hy : L.HS y) → x ≼ y →
         L.ψ⁰ (L.Ω (L.toLevel x hx)) ≼ L.ψ⁰ (L.Ω (L.toLevel y hy))
MonoTᶻ = ∀ x h a l → ZsL (read0 a) → x ≼ read a → L.ψ⁰ (L.Ω (L.toLevel x h)) ≼ read (foldᵐ₃ a l)
Crux = 与 VMᴸ 同形，结论两边的层号各套一个 L.suc
EmbV = ∀ x hx y hy → x ≼ y → PEmb (L.toLevel x hx) (L.toLevel y hy)
```

`MonoTᶻ` 是 `MonoT` 加前提 `ZsL (read0 a)`；`MonoT` 推出它是平凡的，没有另写成定理。

**YiMonoOne (新的下界)**

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| `ωX` | `∀ pl lg → L.ωᴵ ⊑ᴵ toIL (read0 (one +ʳ G.lim (copies B.zero one))) pl lg` | 1+ω⁺ 的层号 X 结构上 ⊒ ω | 编译定理 |
| `qX` | `_ <ᴵ κ 1` (`L.lim 1 (L.lim 0 (L.lim 1 (L.lim 0 L.zero)))`) | X 是 κ₁ 的字面前驱 | 编译定理 |
| `emb₁` | `PEmb (L.suc L.ωᴵ) (κ 1)` | ω+1 的前驱嵌进 κ₁ | 编译定理 |
| `T₃ᵐ-Ωω+1` | `L.ψ⁰ (L.Ω (L.suc L.ωᴵ)) ≼ read T₃ᵐ` | `T₃ᵐ` 不低于 ψ₀(Ω_{ω+1}) | 编译定理 (下界) |

**前提的可满足性。**
- `EmbT`：n = 0 是定理 (`emb₀`)；n = 1 只做到 ω+1 嵌进 κ₁ (`emb₁`)，不是 `D.L 1` 整个嵌进去。
- `VMᴸ` 与 `Crux`：在结构可比的实例上是定理 (`toLevel-⊑` 加 `Ψ⁰-mono`)，在 ω 对 ω⁺ 上是定理 (`ω-inst`)。
- 判断 (纸面)：`VMᴸ` 与 `EmbV` 在经典集合模型里成立。理由：
  - `toLevel y` 的字面前驱模 `≅ᴵ` 是三歧的 (`<ᴵ-dec`)，字面前驱在值上严格更小，而且 |y| 以下每个值都取得到。所以它是序型 |y| 的良序。
  - 于是经典地有保序嵌入，再接 `Ψ-emb`。
  - 由此推断：`VMᴸ` 与 `MonoTᶻ` 不会有编译的反例。这是判断，不是定理。

##### 4 办法

- **(丙) 带错开下标的结构可比：编译否定。**
  - 结构可比在第 1 步断开，是编译事实。
  - 原因：`D.L 1` 的前驱里有字面的 ω+1 (`sω-L1`)，而链点层号里 ≅ᴵ ω 的结点一个也没有 (`noω`, `inv-nz`)。
  - 所以上一路说的 "lim (natᴵ (k+2)) 对 ωᴵ" 不只出现在 κ₁：它对一切 m 都成立，n = 1、2 都包含在 `no-L` 里。
- **(甲) 拆两半：树一侧已证，参照一侧归约到 `Crux`/`EmbV`，未证。**
  - 树一侧是定理：`HS-read` 与 `lvl≅`。
  - 参照一侧就是 `VMᴸ`，它等价于 `Crux`。
  - 想用 `EmbV` (对 `x ≼ y` 的推导造嵌入) 来证，零、后继 (`PEmb-suc`)、右极限三种情形都有了。左极限要各项嵌入互相一致 (`PEmb-limˡ` 的前提)，而归纳假设给的各个嵌入互不相关。
  - 试过的改法：要求嵌入是 "保初始段" 的，这样唯一性会自动给出一致。但后继情形要定位 "第 |x| 个前驱"，判断：这会推出 LPO 一类的判定。例子：y = suc (lim g)，g 是 0/1 序列。所以放下了。
- **(乙) 换成累加参照：没有走。**
  - 读了 `BTBOFull` 的机制。V2 要求目标在每个极限处都累加 (`ordᴰ`)，树的层号只在根上的链累加。V3 的对应物要新折叠输出的前驱结构。
  - 从这里只拿了 `Ψ-emb`。
  - 没有核对 `BTBOFull` 用的 `NoCumsum.BTBOᴵ` 与这里的 `D.BTBOᴵ` (`Diagonal Uniform`) 是否同一个，因为没有用到。
- **新的下界 ψ₀(Ω_{ω+1}) 是怎么拿到的。** 用临时目录里的纯 `.agda` 按项规范化，看清 `T₃ᵐ` 第 0 项的形状 (有限测试，不是定理)：第 0 支是 ω⁺ = lim (1, 2, 3, …)，第 1 支的第 0 支里出现 ω⁺ + ω。由此写出字面路径 `qX`，由检查器验证。

##### 5 第一个障碍

**`EmbT` 在 n = 1，即 `Σ ℕ λ m → PEmb (D.L 1) (κ m)`。**
- 没有检查器报错，缺的是引理本身。
- 根源：上一路的关系族 `RelF` 在第 0 层的底是值 (`R0 y a = y ≼ read a`)，所以 `lower-any` 只给值，不带任何前驱结构。而每一种单调工具 (`Ψ⁰-mono`, `Ψ-emb`) 都要目标层号 κ m 的前驱结构。
- n = 1 要把 Level 的 ψ₀(Ω₁) 的前驱 (ψ⁰ 迭代的塔) 保序嵌进新折叠的 ψ₀(Ω₁) 输出。按规范化看到的形状，后者是累加链 (判断)。缺下面几条：
  1. 第 0 层 ψ⁰ 对嵌入的函子性：`PEmb (toLevel X) (toLevel Y) → PEmb (toLevel (ψ⁰ X)) (toLevel (ψ⁰ Y))`；
  2. 平移嵌入 `PEmb X (P + X)`；
  3. 各块嵌入的一致性，喂给 `PEmb-limˡ`；
  4. `closedᵐ (fin 1)` 的结构刻画。
- 一般的 n 要的是 `lower-any` 的结构版：新折叠的输出要带前驱嵌入，而不只是值下界。
- 判断：这需要把 `RelF`/`FOLD` 的底关系从值换成嵌入，再做一遍，规模与上一路的 Rel/Fold 相当。没有试。

##### 6 偏离与事故

- 没有改任何已有文件，没碰 `src/`、`archive/`，没有提交，不依赖 `YiLean`/`YiTail`/`YiBaseVal`。
- 一次性试验 `Shape.agda` (纯 `.agda`，只做规范化看形状) 放在 `<实验目录>/agents/mono/scr/`，它的 `.agdai` 也在那里。
  - 其中一项是退化层号 `suc (lim (λ _ → zero))` 上的折叠，用来找 `MonoT` 的反例。规范化出来的形状没有停滞，像 ψ₀(Ω₁) 那样增长 (有限测试，不是定理)，所以没有找到反例。
- 编译中途的错误都是自己的，各改一次就过：
  - `W = L.ψ⁰ (L.suc L.zero)` 的隐式层号没定，改成 `L.ψ⁰ {L.zero}`；
  - `crux→vm` 的点模式改成 `_`。
- 只删过自己四个模块的 `.agdai`，写的是字面路径。
- 编译日志在 `<实验目录>/agents/mono/cold-*.log`。
