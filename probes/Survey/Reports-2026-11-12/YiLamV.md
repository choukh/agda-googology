# TΛ 的值：先 BTBO，再往上 (YiLamV)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-12 01:41 至 02:12 |
| 工具调用 / agda 编译 (粗数) | 57 / 11 |
| token (usage 字段，按消息去重) | 输出 177542；新写入缓存的输入 347317；读缓存的输入 8859915；其余输入 86 |
| 写过的仓库文件 | `YiLamVBtbo.lagda.md`, `YiLamVLost.lagda.md`, `YiLamVOne.lagda.md`, `YiLamVRel.lagda.md`, `YiLamVStep.lagda.md` |
| 文件前缀 | `YiLamV` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-12: 一致折叠闭项的值返回并复核; 主审定的目标完成; 行数表改一格 (主审)” 一节 |
| 主审复核后的一句结论 | TΛ 不低于 BTBO，无前提；T⁺ʷ 到 ψ₀(Ω_Ω+Ω₁)；ψ₀(Ω_Ω·2) 只有条件定理；五件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 作者的指示是 "朝着最终目标的关键路径走" (最终目标: 布劳威尔树上 ψ₀(Λ) 的合法闭项, 值不低于 EBO). 主审定的当前目标: 主线块上读法为 ψ₀(Λ) 的合法闭项, 一致折叠, 前三层 1000 行以下, **值至少不低于 BTBO**. 闭项已有: `probes/OCF/Lean/YiLamFold.lagda.md` 的 `TΛ` (合法无前提, 切片 568 行). **你这一路的任务是它的值: 先闭合 "BTBO 不高于 `read TΛ`", 再从这个锚点往上.** 主审会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 0 先读什么

1. `AGENTS.md` 全篇. 特别是 Agda 一节 (选项, 文字预算, 退出码, 堆; 函数外延只准作前提), "用记号验收强度", "中间站给界", "结论的写法".
2. `probes/Survey/EBOHandbook.md` 只读 §4.1 到 §4.5 与 §5.4.
3. 被验收的对象: `probes/OCF/Lean/YiLamFold.lagda.md` 全读 (`Lw`, `Wit`, `dfin`, `cmpw`, `rootW`, `Ψ`, `ptsΩ`, `Lw-tw`, `VΛ`, `TΛ`, `Tw`, `T⁺ʷ`, `TΛ-form : TΛ ≡ G.lim (psum zero Tw)`); 有限测试 `YiLamTest.lagda.md` (`kept`: 下一站丢掉的那一对现在保留). 部件在 `YiNextCore.lagda.md`, `YiNextBase.lagda.md`, `YiNextTower.lagda.md`. 读回: `YiNextAcc.lagda.md` 的 `read` (它对 `YiNextCore` 的 `R` 定义, 可以直接用在 `TΛ` 上), `plus≽`, `suc-lower`.
4. **已闭合的锚点 (都无前提, 都是对另外两个折叠的)**:
   - `YiBtboLower.lagda.md`: `btbo : D.BTBOᴵ ≼ read T₃` (主线 `YiLeanFold` 的 `T₃`), `btbo⁺ : D.BTBOᴵ ≼ NA.read NT.T⁺` (下一站 `YiNextFold`). 办法: 链上只带值序, 每步经累加规范化层号 (`YiBtboV2.V2′`) 与主线一侧的 `V3m` 造前驱嵌入. 说明在 `probes/Survey/RR7-BtboLower.md`.
   - `YiAboveOne`, `YiAboveCtx`: 下一站 `T⁺` 严格高过 BTBO, 不低于 ψ₀(Ω_Ω+Ω₁) 的带标签参照 (`above`, `χ₁≼`; 上下文引理 `ctx`). `YiAboveStep`: ψ₀(Ω_Ω·2) 的条件定理 `T2≼ᴳ : Stepᴳ → …`, 前提是层号 ≥ 1 的链上的单步比较 (下一站的派发在那里一律折叠). `YiAboveLost`: 下一站丢掉的那一对被问到.
   - 转运的先例: `YiNextValFin.lagda.md` (`co≅`, `T₃≅`: 两套折叠的链点读回互模拟).
查签名用检索, 大文件不要整篇读.

#### 1 要交的, 分步; 每做成一步先交

1. **`D.BTBOᴵ ≼ read TΛ`** (`read` 取 `YiNextAcc` 的), 以及 `D.BTBOᴵ ≼ read (Tw 3)`. 办法自选: 把 `YiBtboLower` 的证法搬到 `YiLamFold` 上 (V3m 要的是第 0 层链点上折叠值的结构), 或者证 `YiLamFold` 的 `Tw 3` 与主线 `T₃` 的读回互模拟 (仿 `T₃≅`), 或者别的. `TΛ` 不低于 `Tw n` 由部分和 (`plus≽` 一类) 给出.
2. **往上**: 照 `YiAbove` 的办法, `T⁺ʷ` (或 `TΛ`) 不低于 ψ₀(Ω_Ω+1), ψ₀(Ω_Ω+Ω₁) 的带标签参照 (`S2.ts-label`, `S2.χ1-label`).
3. **决定性的一步**: ψ₀(Ω_Ω·2) 的带标签参照 (`GoodL` 的 `T2ᴸ`, `T2-label`) 不高于 `read T⁺ʷ` (或 `read TΛ`). 新折叠在目标层字面有限时按头构造子保留 (`dfin`), 下一站丢掉的那一对现在保留 (`kept`); 看 `YiAboveStep` 的 `Stepᴳ` 在新折叠上能不能证. 做不过去时给出值停在哪里的编译事实, 或者把缺的写成带确切类型的前提, 并说清是不是派发在极限目标层上一律折叠造成的.

只要下界 (作者 2026-11-11 的原则: "只要证明 'BTBO是下界' 即可"): 选证法时不引入上界, 同值, 逐项精确; 有的话先找只用下界的证法. 下界从已闭合的最高锚点往上做.

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K (可交显式前提的条件定理); 堆到 6G 仍耗尽 (先按手册 §4.2). 做不成的部分写成带确切类型的模块参数. 没有编译的否定时只写 "未走通".

#### 2 过程要求

- 读完上面的文件后尽快动手: 第一个文件在 20 分钟内写出并编译.
- 每写完一个文件就编译; 每次回复都要有工具调用, 不要在一次回复里只思考.

#### 3 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiLamV` (模块名 `OCF.Lean.YiLamV…`). 都是验收文件, 文首标 "验收文件". 中文 literate Agda (`.lagda.md`). 不改任何已有文件 (包括 `YiLamFold`), 不碰 `src/`, `archive/`.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 函数外延只准作显式前提, 用到它的定理在文首标 "条件".
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 堆墙多出在比较具体闭项的地方: 陈述逐字写, 不用别名; 大参照树放 `opaque`; 经非单射的头求解的隐式参数显式写出 (手册第 4 节).
- 仓库文件里不写本机路径. 不要把仓库整个拷到临时目录 (要确认会不会重编共享接口时, 先问主审).
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块; 另一路也在编译.
- 你的临时目录: `<实验目录>/agents/lamv`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 4 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 做到第几步; 一段话说对目标意味着什么 (`TΛ` 的值是否不低于 BTBO; 已证的最高下界; 新折叠的派发在 ψ₀(Ω_Ω·2) 那一站掉不掉值).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 用到的参照与它的验收定理.
4. 办法: 与 `YiBtboLower`, `YiAbove` 相比新用到了什么.
5. 第一个障碍: 精确到引理, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
6. 偏离与事故.
不用 "只差", "自然" 一类形容; 判断与定理分开写.

## 回报原文

#### 1 判决

前两步做成, 都是编译定理, 无前提. 第 3 步只有条件定理: 前提 `Stepᴳʷ` 没有证出来, 也没有否定, 状态是"未走通".

对目标意味着什么:
- **`TΛ` 的值不低于 BTBO.** 这是编译定理, 无前提: `btbo-TΛ : D.BTBOᴵ ≼ NA.read W.TΛ`. 另有严格高过 BTBO 的一条: `aboveΛ : L.suc D.BTBOᴵ ≼ NA.read W.TΛ`. 主审定的 "值至少不低于 BTBO" 这一条, 对 `TΛ` 成立.
- **`TΛ` 已证的最高下界就是 `L.suc BTBO`.** 更高的下界只对同一折叠里的另一个闭项 `T⁺ʷ` (读法 ψ₀(Ω_{Ω+1})) 证出, 最高是 ψ₀(Ω_Ω+Ω₁) 的带标签参照. `T⁺ʷ ≼ TΛ` 没有证, 所以这些界没有转到 `TΛ` 上.
- **ψ₀(Ω_Ω·2) 那一站掉不掉值, 没有定论.**
  - 编译事实: `Stepᴳʷ` 问到的链里, 目标层号不是字面的有限数, `dfin` 在那里对一切位置都折叠, 包括 Ω_Ω 的根. 而那一层里有层号 0 的槽位 (`lost`, `root-lost`, `could`). 字面有限的层号 2 上, 同一个根保留 (`root-kept`).
  - 判断: 参照一侧 Level 的 `ψ` 用 `<ᴵ-dec` 在节点层号低于目标层时保留节点, 所以卡住证明的确实是 "派发在非字面有限的目标层上一律折叠".
  - 这会不会让值低于参照, 没有编译的证据, 两个方向都没有.

一处与简报的出入: 在 `YiLamFold` 里, `Tw n` 折的是第 `tw n` 层的 `top`. 所以与主线 `T₃` 对应的是 `Tw 2` (读法 ψ₀(Ω_Ω)), `Tw 3` 的读法是 ψ₀(Ω_{Ω_Ω}). 三个都证了: `Tw 2`, `Tw 3`, `TΛ`.

#### 2 文件表

都在 `probes/OCF/Lean/`, 都是验收文件. 每个都先删掉自己的 `.agdai`, 再按依赖次序冷编译, 6G 堆, 每次约 8 到 10 秒. 日志里只有本模块自己的 `Checking` 行.

| 文件 | 总行数 / 代码非空行 | 冷编译退出码 | 常驻内存峰值 |
|---|---|---|---|
| `YiLamVRel.lagda.md` | 132 / 103 | 0 | 1.46 GB |
| `YiLamVBtbo.lagda.md` | 123 / 82 | 0 | 1.77 GB |
| `YiLamVOne.lagda.md` | 171 / 119 | 0 | 1.74 GB |
| `YiLamVStep.lagda.md` | 89 / 61 | 0 | 1.72 GB |
| `YiLamVLost.lagda.md` | 84 / 48 | 0 | 1.63 GB |

自查结果:
- 检索 `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY`, `trustMe`, `irrelevant-projections`, `Funext`, 本机路径: 都是 0.
- 选项行都是 `{-# OPTIONS --safe --without-K --lossy-unification #-}`.

#### 3 定理表

##### 编译定理 (无前提)

**`YiLamVBtbo`**
- `btbo-Tw2 : D.BTBOᴵ ≼ NA.read (W.Tw 2)`: 新折叠的 `Tw 2` 不低于 BTBO.
- `btbo-Tw3 : D.BTBOᴵ ≼ NA.read (W.Tw 3)`
- `btbo-TΛ : D.BTBOᴵ ≼ NA.read W.TΛ`
- `T₃≼Tw2 : MA.read MT.T₃ ≼ NA.read (W.Tw 2)`: 主线 `T₃` 不高于新的 `Tw 2`.
- `obs≅ : ∀ n → MA.read (MT.obs (MT.pts n)) L.≅ NA.read (obs n)`: 两边第 n 个链观察的读回结构互模拟.
- `Tw2≼Tw3 : NA.read (W.Tw 2) ≼ NA.read (W.Tw 3)`: 证明是 `≼l 0 (≼-refl _)`, 即 `Tw 2` 定义性地是 `Tw 3` 链上的第 0 项.
- `Tw≼TΛ : ∀ n → NA.read (W.Tw n) ≼ NA.read W.TΛ`
- `Tw2-form : W.Tw 2 ≡ N.G.lim (NB.psum N.zero obs)`: `refl`. 新折叠的观察多取了一层部分和.

**`YiLamVRel`** (折叠互模拟的部件)
- `ΨRʷ : … → VRʷ V V′ → XR m m′ k k′ x x′ → RR k k′ ξ ξ′ → RR m m′ (MF.Ψ m V x ξ) (W.Ψ m′ V′ x′ ξ′)`
- `ΨCpPʷ`: 第一位置证明的路径相同.
- `ΨLglRʷ`: 合法性证明相关.
- 公共上界只取 `w0`, `ws`, `wl`.

**`YiLamVOne`**
- `aboveʷ : L.suc D.BTBOᴵ ≼ NA.read W.T⁺ʷ`
- `ΩΩ+1ʷ : L.ψ⁰ (L.suc (L.Ω S2.ℓ₀)) ≼ NA.read W.T⁺ʷ`: ψ₀(Ω_Ω+1).
- `χ₁≼ʷ : S2.χ 1 ≼ NA.read W.T⁺ʷ`: ψ₀(Ω_Ω+Ω₁).
- `aboveΛ : L.suc D.BTBOᴵ ≼ NA.read W.TΛ`
- `term₀ : Ψ₀ G.top ≡ W.Tw 2` 与 `term₁ : chain (tw 2) Φ₂ 1 ≡ G.lc p₀ gK`: 都是 `refl`.

**`YiLamVStep`**
- `χ₁-topʷ : S2.χ 1 ≼ NA.read (Ψ₀ (gK G.top))`
- `χ₁-d1ʷ : S2.χ 1 ≼ NA.read (d 1)`

**`YiLamVLost`** (关于定义的 `refl` 事实, 不是值定理)
- `asked : NA.read (Ψ₀ (gK ξa)) ≼ NA.read W.T⁺ʷ`, 其中 `ξa = plus zero G.top (G.suc (W.Tw 2))`. 意思是这个坐标上的结点会被 `T⁺ʷ` 的值问到.
- `Tt-node : Tt ξa ≡ G.lc rN gN`
- `lim-level : IsLimL (lev (tw 2) rN)`: 这个结点的层号是 ℕ 极限.
- `lost : ∀ r → W.cmpw V2 rN r ≡ fold`: 它的链对一切位置折叠.
- `root-lost : W.rootW (lev (tw 2) rN) zero ⌜_⌝ (W.witU zero) (W.cmpw V2 rN) ≡ fold`: Ω_Ω 的根 (层号 0) 也折叠.
- `could : Way (lev (tw 2) rN) zero` (`= keep (0 , 0 , 0 , inj₂ (inj₁ tt)) refl`): 这一层有层号 0 的槽位, 本可保留.
- `root-kept : W.rootW (lev (tw 2) rF) zero ⌜_⌝ (W.witU zero) (W.cmpw V2 rF) ≡ keep (inj₂ (inj₁ tt)) refl`: 对照, 层号 2 上同一个根保留.

##### 条件定理

**`YiLamVStep`**
- `Stepᴳʷ = ∀ k m → GL.χ k ≼ NA.read (d m) → GL.χ (suc k) ≼ NA.read (Ψ₀ (gK (d (suc m))))`
- `T2≼ᴳʷ : Stepᴳʷ → GL.T2ᴸ ≼ NA.read W.T⁺ʷ`
- 另有 `FromStepʷ.T2≼`: 对任意带 `Lab (L.lim f) S2.t2` 的参照 `f` 成立.

##### 用到的参照与它们的验收定理

| 参照 | 读法 | 验收定理 |
|---|---|---|
| `D.BTBOᴵ` | BTBO | 下界来自 `YiBtboLower.btbo` |
| `L.ψ⁰ (L.suc (L.Ω S2.ℓ₀))` | ψ₀(Ω_Ω+1) | `S2.ts-label` |
| `S2.χ 1` | ψ₀(Ω_Ω+Ω₁) | `S2.χ1-label` |
| `GL.T2ᴸ` | ψ₀(Ω_Ω·2) | `GL.T2-label`, 无条件 |

#### 4 办法

**与 `YiBtboLower` 相比**: 没有在新折叠上重做 `V3m`/`V2′` 的链, 走的是简报列出的另一个选项 (仿 `T₃≅` 的转运).
- `YiNextVal{Rel,Path,Lgl}` 里的加法和结点两行部件只读 `YiNextBase`, 直接拿来用.
- 新写的部件:
  - 公共上界的关系 `VRʷ` (主线 `Lv` 对 `Lw`, 不含 `wΩ`), 以及 `cmpRʷ`, `shiftRʷ`, `ΨRʷ`, `ΨCpPʷ`, `ΨLglRʷ`.
  - `shRʷ`: `lgl→Lw` 在极限处用 `cps ∘ cp→CP` 搬运位置, 与主线 `sh` 走同一条路径.
- 链点下一步的派发 `dfin zero _` 定义性地就是折叠, 所以链点逐项相关 (`ptRʷ`).
- 新折叠的观察多一层部分和, 用 `psum≽` (由 `NA.plus≽` 得到) 吸收. 最后接 `YiBtboLower.btbo`.
- 中间用了链观察的读回互模拟 (`obs≅`, 这一层是 "同值"). 进入结论的只有 `≅→≼` 这个方向; 最终陈述都只是下界.

**与 `YiAbove` 相比**: 证明逐字照搬, 换了以下几处:
- 分支族 `Kf` 换成 `Kfk zero`.
- 种子 `bt₃` 换成 `btbo-Tw2`.
- 新写了 `topᶜʷ` 的 `wΩ` 行 (用 `ΩT-top`, `Kfk` 与部分和的第 0 项都在 `top` 支上).
- 新写了 `one` 与 `aboveΛ`.

#### 5 第一个障碍

`Stepᴳʷ` 是缺的那条引理, 类型就是上面逐字写出的那一行. 没有写出过不了检查器的证明, 所以没有报错原文.

没有证出来的原因 (判断, 读定义所得):
- `GL.χ (suc k)` 由 `forceᴸ` 从 `Goodᴸ` 证书算出, 标签是 γ′_{k+2} = ψ₀(Ω_Ω+Ω_{γ′_{k+1}}).
- 它在层号不低于 χ_k 的地方用 Level 的 `ψ`. 那里节点层号低于目标层时, `ψ` 由 `<ᴵ-dec` 保留成 `limᵢ` 结点.
- 新折叠在同样的位置用 `dfin`: 目标层号不是字面的有限数时一律折叠, 结果是可数的链极限 (`YiLamVLost` 的编译实例).
- 所以没有逐步的模拟引理可写: 一边是保留的不可数结点, 另一边是可数极限.
- 判断: 派发一律折叠时, 第 c 层的折叠值只由 `top`、`succ`、`lim` 与第 c 层的加法搭成, 局部上比 Level 的 `ψ_c` 小.
- 判断: 整体上 `d (suc m)` 远大于 χ_k, 这一点可能把局部的损失补回来 (高一层的补偿). 但这需要全局的论证, 本轮没有做, 也没有上界方面的证据.

#### 6 偏离与事故

- **简报写的是 `Tw 3`.** 按上面的编号说明, 与主线 `T₃` 对应的是 `Tw 2`. 三者 (`Tw 2`, `Tw 3`, `TΛ`) 都给了.
- **多交了 `aboveΛ`.** 简报没有要, 加它是因为代价小, 而且它是对 `TΛ` 本身的陈述.
- **第 2 步的界在 `T⁺ʷ` 上, 不在 `TΛ` 上.** `T⁺ʷ ≼ TΛ` 没有证, 要证需要跨层的嵌入.
- **开发中的编译错误, 都已修好:**
  - `W.co` 不在作用域, 改成 `W.Pk.co`.
  - `topᶜʷ` 的 `wΩ` 行有未解元变量, 改为显式写出 `K` 与 `o`.
  - `L.zero` 的层级推不出, 改成 `L.𝟎 {L.zero}`.
- **文件操作:**
  - 只新建了五个 `YiLamV*` 文件, 没有改任何已有文件.
  - 两次只删自己的五个 `.agdai`, 用字面的精确路径. 没有用 `--ignore-interfaces`.
  - 日志在 `<实验目录>/agents/lamv/` (冷编译日志是 `cold-<模块>.log`).
