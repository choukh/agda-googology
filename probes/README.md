# probes 地图

给刚到的协作者. 按时间的完整记录在 `LOG.md`, 这里只说现在在哪、先读什么、哪里走不通. 文件名不带路径时都在 `OCF/Align/`, 省略扩展名. 一组文件的入口是不带后缀的那篇 (`LvGuard`), 文件头写判决; `Base` 是底座, `Neg` 放否定, `Accept` 放记号验收.

## 总纲领

见 `AGENTS.md`, 这里不重复.

## 现状

档: 定理 = 编译过的定理; 条件 = 编译过, 但带前提; 测试 = 有限测试; 判断 = 纸面或判断.

| 层 | 声称 | 文件 | 定理 | 档 |
|---|---|---|---|---|
| 证书 | **最高:** 高度是序数码 M 之下的位置 (结构 `HtB`, 三歧只在这一段内), 闭包定理对一切 M; 检查点 ω·2, ω², ω^ω, ε₀ 和回灌高度 `T-feed` 有闭项和 FGH. 读法 ψ₀(Ω_{Ω·(1+rk p)+α}) 是判断, 没有标签, 只在 ψ₀(Ω_{Ω²}) 之下算数 (`CrossM`); ω+ω 以内与 `HtS` 的树同值 | `LadderOrdMain`, `LadderOrdCert`, `LadderOrdClosed`, `LadderOrdAgree` | `GᴺTᵠ`, `Gᵒ`, `Gη`, `Gε₀`, `Tε₀`, `T-feed`, `agree₂`, `agree²`, `growᵖ` | 定理; 读法是判断 |
| 证书 | 跨段: 序数码的初始段上移 `up`, 树沿它一致 (`up-sim`); 分支对一切码的节点 `Node` 与闭包定理 `Gν`; 闭项 `T⊤`, 读法 ψ₀(Ω_{ψ₁(Ω)}) 是判断, 没有标签. 数据树节点 `tH` (`Tᵀ`, 读 ψ₀(Ω_{ψ₁(Ω)+α})) 只有定义, 没有证书 | `CrossMUp`, `CrossMUpTree`, `CrossMNode`, `CrossMClosed`, `CrossMTop`, `CrossMNeg` | `up`, `up-sim`, `Gν`, `T⊤`, `fgh⊤`, `Tᵀ`, `no-⊂⌈⌉` | 定理; `Tᵀ` 只有定义 |
| 证书 | `tH` 的分支与第 0 行同值 (`branch≈`, `G-E`), 第 0 行三个带证书的闭项; `T̂ᵀ` 与 `T⊤` 字面 ≅, 所以没有比 `T⊤` 更高; 字面的数据树第 0 行没有证书, 形状上差链生成器 (`Tᵀ-shape`, `T̄-shape`); 判断补它与 α ≥ 1 同量级; α ≥ 1 没有做 | `CrossNextDn`, `CrossNextSum`, `CrossNextInst` | `branch≈`, `D→≈ᵠ`, `G-E`, `E≅`, `T̂ᵀ`, `HS-T̂ᵀ`, `T⊤≅T̂ᵀ`, `fgh⊤≡`, `T̃ᵀ`, `T̄ᵀ`, `stepᵀ`, `Tᵀ-shape`, `T̄-shape`, `T̄≼T̃ᵀ`, `T̃≼T̄ᵀ`, `Sum` | 定理; α ≥ 1 未走通 |
| 定义 | **折叠是和的作用:** 极限节点是差的和, 部分和字面是第一位置, 合法性进定义 (`Lg-sum`, 十几行, 不提折叠); 折叠不要 `HS`, `Goodᴺ`, `WF`; ψ₀(Ω_Ω) 过序数值验收 (`T≈`, `TΣ≈`); 只有 ψ(a+1)=ψ(a)·ω 这一步是约定; 只到这一站, 超过要把回灌闭包写成和上的节点 | `TLRuleSum`, `TLRuleDiag`, `TLRuleAccept`, `TLRuleSpec`, `TLRuleVar` | `Run`, `sum-fst`, `Lg-sum`, `Lg-Ψ`, `Top`, `TopΣ`, `T≈`, `TΣ≈`, `T≇`, `ω-spec`, `ω-uniq`, `sum⊞`, `no-full`, `chain-least`, `gap-Ω₁`, `blind` | 定理; 只到 ψ₀(Ω_Ω) |
| 定义 | 和的树过第一个闭包: 回灌闭包写成和上的节点 `nκ`, ψ₀(Ω_{Ω+1}) 的闭项 `T₁` 带 `Lg-T₁`, 定义不读证书; 严格高于 ψ₀(Ω_Ω) (`step-T₁`); 上界没有. 第 3 层只比定义多 2 行; 不比较两条链. 只到 Ω+1 | `SumOneTree`, `SumOneFold`, `SumOneSim`, `SumOneTop`, `SumOneAccept` | `T₀`, `T₁`, `Lg-T₁`, `RS`, `CIs`, `T₀≈`, `step-T₁`, `T₀<T₁`, `gap₀`, `T₀≇`, `step≈` | 定理; Ω+1 只有下界 |
| 定义 | 和的树的层一般化成 (p, a) 加顶层: 闭项 `T`, `Tω`, `T²` 合法性仍由形状给出; 站与站严格增长 (`S1`..`S4`), 但只说明不塌缩, 是积木字面相接的结果; 读法到 Ω² 是判断, 没有序数值验收 | `SumHtTree`, `SumHtFold`, `SumHtClosed`, `SumHtGrow` | `T`, `Tω`, `T²`, `Lg-T²`, `S1`, `S2`, `S3`, `S4`, `Ω·ω<Ω²` | 定理; 强度是估计 |
| 定义 | 第 0 层中间层改回布劳威尔树: 合法性来自加法的第一位置 (`⊞-fst`, `Lg-⊞`, 28 行), 部分和的极限 `Σlim`; 与和的树值相等互译 (`round₁`, `round₂`), 字面不互逆 (`dif-not-id`, `sum-dif-not-≈ᴬ`); 闭项 `T₀`, `T₁` 停机直接过; 高层仍是差树; 序数值验收未走通 | `BrwMidZero`, `BrwMidFold` | `⊞-fst`, `Lg-⊞`, `Σlim`, `toA`, `dif`, `dif-ok`, `round₁`, `round₂`, `dif-not-id`, `T₀`, `T₁`, `Lg-T₁` | 定理; 验收未走通 |
| 定义 | 数类第 1 层: Ω-极限节点的分支按坐标递归 (正规分支 `Ig`), 沿前缀单调无前提; 存增量的树 `N₁` 读成合法的布劳威尔树 (`Lg-br`), 和的树第 1 层也能读成这种树 (`out-legal`); 只存布劳威尔树读不回增量 (`incr-blind`) | `BrwHighOne` | `B₁`, `⊞₁-fst`, `Lg-⊞₁`, `Ig`, `Ig-pre`, `Lg-node`, `N₁`, `br`, `Lg-br`, `nrm`, `out-legal`, `incr-blind` | 定理; 折叠未改 |
| 定义 | 按层归纳互译, 只做第 0 到 1 层: 一切第 1 层差树译成合法的布劳威尔树 (`Lg-toB`), 无前提; 回程值上不互逆 (`no-round`), 加条件 `Cv` 成立 (`round-Cv`), 条件可满足 (`Ω-Cv`) 也去不掉 (`xᶜ-not-Cv`); `nκ` 读不回差 (判断) | `LayerTrBase`, `LayerTrOne`, `LayerTrNeg`, `LayerTrRound`, `LayerTrOmega` | `toB`, `Lg-toB`, `dif₁`, `Ω≈`, `no-round`, `S-mono`, `round-Cv`, `Ω-Cv`, `xᶜ-not-Cv` | 定理; 回程条件 |
| 值 | 折叠在数类第 0 层坐标上产出的 `ni` 节点满足 `Cv` (`Kn-CO`); 不含 `nκ` 的输出段值上互译 (`Pk-round`, `A-round`); 折叠对坐标的规范化值同余 (`canon`, 条件 `HA`, 实例成立); `nκ` 段要高层输入的值同余, 未走通 | `CvFoldSub`, `CvFoldRun`, `CvFoldInst` | `S-congʸ`, `Cv⁰→Cv`, `canon`, `Kn-CO`, `Pk-round`, `A-round` | 定理; `nκ` 段未走通 |
| 定义 | 加法封闭的地位: ψ(a+1)=ψ(a)·ω 是约定, 不是树逼的 (`req-·2`, `no-clo-·2`: ·2 满足全部树侧要求但不对加法封闭); ψ₀(Ω_Ω) 这一站值把 S 逼进一个带 (`T-1+cω`, `T-c+cω`, `T²≼`); 地板 ψ(0)=Ω_τ 是值逼的 (`TD≺`) | `AddCloRel`, `AddCloNeg`, `AddCloInit`, `AddCloAccept` | `main`, `Ψ≤`, `req-·2`, `no-clo-·2`, `succ-spec`, `T²≼`, `T-1+cω`, `T-c+cω`, `TD≺`, `TI≽` | 定理; ·2 的下界未走通 |
| 证书 | 无前缀, 不用 `next`, `cumA`, ⊞: ψ₀(Ω_{Ω+1}) 的树有无条件证书 (`G₁`, `HS-T₁`), 一切 p 的 Ω·p+1 (`G-p₁`), 一切 p, a 条件于 `Root`; 绕过字面 `Hn`, 新增约 880 行; 大小没验, 第 0 项是 ψ₀(Ω_Ω); 判断 `add⁰` 把 W 带进链点, 是残留的等效累加 | `Om1HnMain`, `Om1HnOmega`, `Om1HnPsi`, `Om1HnAdd`, `Om1HnGd`, `Om1HnCx`, `Om1HnNeg`, `Om1HnAccept` | `G₁`, `HS-T₁`, `G-p₁`, `G-Tᴿ`, `Root`, `root₁`, `Psi`, `ΩG`, `no-Root`, `shift`, `term₀`, `label-term₀`, `low-T₁` | 定理; 大小是估计 |
| 证书 | 不累加, 第 (0,0) 层改成对项直接计值 (`val`), 去掉 `add⁰` 的残留; ψ₀(Ω_{Ω+1}) 的证书 `G₁`, 严格高于 ψ₀(Ω_Ω) (`BTBO≺T₁`), Ω 这一站逐项相等 (`same-Ω`); 没加 `oĉ`, 没克隆; 对 Ω+1 参照树的互模拟没写 | `NoCumNodeE`, `NoCumNodeMain`, `NoCumNodeAccept` | `val`, `val≅`, `E-tr`, `G-N`, `G₁`, `HS-T₁`, `anyΩ`, `same-Ω`, `BTBO≺T₁` | 定理; Ω+1 只有下界 |
| 证书 | 不累加: (p, a) 世界的 `ψW` 不碰链, 不靠累加; ψ₀(Ω_Ω) 这一站累加全去掉, `T⁰` 过基本列验收; Ω+1 及以上条件于 `Hn` (对应 `Vis`, `Hon` 的义务); 留世界前缀的 `Tᵖ` 无条件有 `HS`, 强度只有形状测试; 定义依赖证书 (`force`) | `NoCumMain`, `NoCumLit`, `NoCumOmega`, `NoCumForce`, `NoCumHon`, `NoCumPre`, `NoCumAcceptOmega`, `NoCum` | `ψW`, `lit`, `graft₀`, `T⁰`, `HS-T⁰`, `T⁰≅`, `label-T⁰`, `fgh⁰`, `WF-T`, `Hn`, `Hn-Ω`, `G-T`, `TΩᴺ`, `Tᵖ`, `HS-Tᵖ`, `no-Lit-x₀` | 定理; Ω+1 起条件 |
| 值 | (p, a) 世界的 ψ₀(Ω_Ω) 过序数值验收, 对任何证书 (`any-cert`, `TΩᴺ≈`, `TΩᴺ≅T⁰`); Ω+1 的 `Hn` 未证; `Bach` 是闭包这一行的一步定理; `Hn` 依赖折叠目标 (`no-Hn-b`), 不是源的形状的函数 | `NoCumHnCore`, `NoCumHnNeg`, `NoCumHnBridge`, `NoCumHnAccept` | `any-cert`, `TΩᴺ≈`, `TΩᴺ≅T⁰`, `Bach`, `Vis-lift`, `mono₂`, `≪→Fp`, `no-Hn-b`, `force-Y` | 定理; Ω+1 未走通 |
| 证书 | 高度放进世界 (r, p, a): 一条 `HS-T` 过读法 Ω², Ω²+1, 上确界读 Ω²·ω; 只有合法性, 大小没验; `HS-Nxˢ` 说不读输出的链也 `HS`, 是 `HS` 不说明大小的编译实例 | `CumHtMain`, `CumHtShape`, `CumHt`, `CumHtBase`, `CumHtCum` | `HS-T`, `ψW`, `T-mono`, `T-world`, `cmpH`, `HS-T²`, `HS-T²⁺¹`, `HS-Nxˢ`, `𝓝ᶜ` | 定理; 大小是估计 |
| 证书 | 高度类型 `Hg` (`ht`, `top`) 进世界, 读法 ψ₀(Ω_{Ω²+1}) 的闭树 `T₁` 有 `HS`, 严格高于同族 `T₀` (`T-strict`, `T₀≺T₁`); 与 `T⊤` 没有定理; 第 0 层闭包仍累加; 大小是估计 | `WorldTHW`, `WorldTHMain`, `WorldTHGrow`, `WorldTHInst` | `HS-T`, `ψW`, `T-strict`, `T₀≺T₁`, `HS-T₁`, `fgh₁`, `row-mono`, `top-val` | 定理; 大小是估计 |
| 证书 | 累加, 层是一对 (p, a): 一条闭包定理 `HS-T` 对一切 p 与合法的 a; ψ₀(Ω_Ω) 这一站过序数值验收 (`Tᶜ≈`); Ω+1 及以上的强度只有形状测试, 是估计. 高度只到 ℕ, 上确界 `TΩ·ω` | `CumUpW`, `CumUpMain`, `CumUp`, `CumUpAcceptVal`, `CumUpClean` | `Tψ`, `HS-T`, `T-mono`, `HS-TΩ+1`, `HS-TΩ·2`, `HS-TΩ·ω`, `Tᶜ≈`, `Tᶜ≈src`, `y₀≅γ₁`, `term-≥`, `term₁-strict`, `no-rd`, `dec⊲→LPO` | 定理; 强度是估计 |
| 值 | `Tψ` 的 ψ₀(Ω_Ω) 这一站过序数值验收 (`TΩ≈`, `TΩ≅Tᶜ`); Ω+1 起只有非严格下界 (`low-Ω+`), 没有上界, 连严格高于 ψ₀(Ω_Ω) 都没证. 判断要带基底的嵌入, 对照树的单调, 值严格性, 超 3000 行 | `CumVal`, `CumValZ` | `TΩ≈`, `TΩ≅Tᶜ`, `val≅`, `B-ψ`, `ψ₀-Y`, `low-Ω+`, `low-Ω+1` | 定理; Ω+1 未决 |
| 值 | 累加树一站高过一站 (`T-strict`), 严格高于 ψ₀(Ω_Ω) (`step-Ω+1`); ψ₀(Ω_{Ω+1}) 的序数值验收没有上界, 下界只高一步 | `Om1CumGrow`, `Om1CumIdx` | `T-strict`, `TΩ≺TΩ+1`, `step-Ω+1`, `ladder`, `V2ᶜ`, `no-V2`, `Fʸ-next` | 定理; Ω+1 未走通 |
| 证书 | 累加: 下标累加后去掉帧, 表, 地板; ψ₀(Ω_Ω) 的新树 `Tᶜ` 不经 `Goodᴺ` 有 `HS`, 没有闭包的层一步对一切字面合法的 η; 带闭包的层 (Ω+a, Ω·α, Ωⁿ) 只有定义, 没有证书. 这个世界没有接回 `LF`, 读法是判断 | `CumReadBase`, `CumReadCFThm`, `CumReadTop`, `CumReadW`, `CumReadWLv` | `Lg-cum`, `Legal-ordᴸ`, `dom-cum`, `absorb-ω`, `ψL`, `ψW`, `HS-Y`, `Y-mono`, `Tᶜ`, `HS-Tᶜ`, `Tψ`, `TP` | 定理; 带闭包只有定义 |
| 证书 | 不带高度的树 `T₀ʷ`: 一条定理对一切 θ 给 ψ₀(Ω_{Ω+θ}) 的 `Goodᴺ`, 计值与 `HSℕ` 的证书 ≅ (由 `≲-θ` 经 `Good-≲`); 带标签的 θ < ψ₀(Ω_{Ω·2}) 搬过桥后仍带标签 (`label-θ`). Ω·2 没做, 没有否定 | `WeakBridgeMain`, `WeakBridgeFold`, `WeakBridgeLabel`, `WeakBridgeNext` | `Good-θ`, `≲-θ`, `value-θ`, `fgh-agree`, `R-ψ`, `R-ψᵒ`, `label-θ`, `label-Ω`, `keep-Ω·2` | 定理 |
| 标签 | 标签搬到主线证书, 克隆证书 0 个, 克隆与主线的连接成为定理 (`clone-top`, `fgh-top`); 取极限的 `Tᴸ` 过基本列验收 ψ₀(Ω_{ψ₁(1)·2}), 码 ω·2 的顶与它互相 ⊑ (`same-M₂`) 但基本列错开一位, 基本列验收是假的 (`no-lab-M₂`); `PxB` 在这个码上不存在 | `OrdLabAccept`, `OrdLabCross`, `OrdLabChain`, `OrdLabRead`, `OrdLabReadTop`, `OrdLabBInst` | `label-top`, `ord-top₂`, `ord-top²`, `clone-top`, `fgh-top`, `chain-row`, `chain-needs-zero`, `label-Tᴸ`, `same-M₂`, `no-lab-M₂`, `no-lab-pos`, `no-lab-ω²`, `no-PxB-M₂` | 定理 |
| 值 | **序数值验收最高:** 码 ω² 的顶是 ψ₀(Ω_{ψ₁(2)}) (`vv-ω²`, 无条件); 码 ω² 内对一切 i, θ 是 ψ₀(Ω_{ψ₁(1)·(i+2)+θ}) (`vv-E`); 码 ω·2 第 α 行 (`vv-M₂`). 比较工具 `V-≃` 不读记号, 对一切 `HtB`. 参照树来自标签世界克隆, 没有证书克隆. ω^ω, ε₀, `T⊤` 未走通 | `EmbVVMain`, `EmbVVForce`, `EmbVVSame`, `EmbVVTop`, `EmbVVInstM2`, `EmbVVInstO2`, `EmbVVNF`, `EmbVVGap` | `V-≃`, `force≃`, `simᴴ`, `Y-val`, `succ-gap`, `vv-row`, `vv-M₂`, `vv-M₂-1`, `vv-E`, `vv-E₀`, `vv-E-1`, `vv-ω²`, `vv-ω²-via`, `NF-ψ⁺` | 定理 (序数值验收) |
| 值 | **已发表 BTBO 过序数值验收:** `BTBO≈`: `src` 的 BTBO 经 `tr₀` (`FGH-tr₀` 说不改大数) 与过基本列验收 ψ₀(Ω_Ω) 的 `BTBOᴵ` 互相 `≼`, 无条件; 基本列验收与前驱结构验收都是假的 (`no-lab`, `no-⊑⁰-lab`). 累加在这一站被吸收 (`St-x`, `absorb-x`, `V1`, `V2`, `V3`). 判据 `Ψ-emb` 只要前驱之间的保序映射. FGH 是否逐点不同未证 | `BTBOFull`, `BTBOFullEmb`, `BTBOFullSt`, `BTBOFullEb`, `BTBOFullV1`, `BTBOFullV3`, `BTBOFullLv` | `BTBO≈`, `Low`, `Upp`, `no-lab`, `St-x`, `absorb-x`, `PEmb`, `Ψ-emb`, `V1`, `V2`, `V3`, `Fmul`, `SV-L` | 定理 (序数值验收) |
| 值 | 已发表 BTBO: 对任意层号折叠差异不改值 (`ψ₀≈`), x₂ = ψ₀(Ω_ω) 是定理 (`x₂≈BO`), 对角线前四步交错; 整棵同值已由 `BTBOFull` 无条件证出 | `BTBOValBase`, `BTBOValMain`, `BTBOValLe`, `BTBOValLeInst`, `BTBOValAbsorb` | `ψ₀≈`, `x-step`, `x₂≈BO`, `row₃`, `ω+1≈`, `x-ω+1`, `FGH-tr₀`, `ordᴰ-≥`, `absorb`, `cond-main` | 定理; 整棵是条件 |
| 值 | 前驱结构验收的范围: 过基本列验收的树子树也带标签 (`lab-≺`), 记号的 `chain-rule` 排除行 [ω, t[0], …], 所以 ω·2 第 0 行之上都过不了; `VV` 只有链行类 `vv-chain` 和条件定理 `vv-ω²-if` | `ValLabBase`, `ValLabRow`, `ValLabPos` | `lab-≺`, `chain-rule`, `no-⊑`, `no-lab-pat`, `VA`, `VV`, `va→vv`, `suc-sep`, `hyp-2`, `no-NF-ω·2`, `rule-ctl` | 定理; 高处是条件 |
| 证书 | 带标签的最高处: 高度抽象成结构 `HtS`, 闭包定理对一切实例成立; 高度 ω+ω 的树有 `Goodᴺ`, 闭项和 FGH 无参数, 到 ψ₀(Ω_{ψ₁(1)+Ω·n+θ}) 对一切 n | `LadderInfMain`, `LadderInfCert`, `LadderInfClosed` | `GᴺTᵠ`, `G∞`, `G₂`, `G₂ψ₁+Ω`, `T₁∞`, `T₂Ω` | 定理 |
| 标签 | **最高:** ψ₀(Ω_{ψ₁(1)+Ω·n+θ}), 一切 n, θ 带标签且低于上界; 贴在克隆世界的证书上, 与主线的联系是代码逐字相同和有限测试. 上面证书的读法由此成立 | `LadderLabAccept`, `LadderLabTop`, `LadderLabNFTop` | `label-∞1`, `label-∞`, `label-ψ₁+Ω`, `label-top`, `label-cert`, `NF-ψ` | 定理 |
| 证书 | ψ₀(Ω_{Ω·ω}) = ψ₀(Ω_{ψ₁(1)}), 闭项与 FGH 无参数, 无假设, 导入闭包干净; 树有 ℕ 高度, 文法形状读自记号 | `LadderMonoMain`, `LadderMonoClosed` | `Tω-mono`, `GᴺTω`, `Tω₀`, `fgh` | 定理 |
| 证书 | ψ₀(Ω_{Ω·(m+1)+α}) 对一切 m, α, 同一条闭包定理, 无假设, 导入闭包干净 | `LadderNFMain` | `GᴺTᵠ`, `GᴺT`, `GᴺTΩ·2+1`, `GᴺTΩ·3` | 定理 |
| 标签 | 证书的计值带标签, 在克隆世界 (`LadderNFW*`, `LadderMonoW*`, 只改导入); 与主线的联系是代码逐字相同和有限测试, 不是定理 | `LadderNFAccept`, `LadderMonoAccept` | `label-cert`, `anchor-Ω₂`, `label-Ω·3`, `agree-P`, `Tω-cert-label` | 定理 |
| 证书 | 到 ψ₀(Ω_{Ω·2}) 的闭项与证书, 无参数, 导入闭包干净; 不说明没受记号启发 | `OCF/Free/Closed` | `TΩ₂`, `certᵀ`, `fgh` | 定理 |
| 证书 | ψ₀(Ω_{Ω+η}) 对一切 η, 同一条闭包定理 | `OCF/Free/Main` | `GᴺΩ̇`, `GᴺTΩ·2` | 定理 |
| 证书 | 上面那棵树的计算: fgh 0 = 1; fgh 1 的 refl 580 秒未完, 无结果 | `OCF/Free/Closed` | `fgh` | 测试 |
| 证书 | `Tω₀` 的计算: fgh 0 = 1, fgh 1 = 2; fgh 2 的 refl 170 秒无结果 | `LadderMonoClosed` | `fgh` | 测试 |
| 标签 | 标签接到无记号的树上 (闭包外验收) | `OCF/Free/Bridge` | `bridge`, `label-on-free`, `fgh-all` | 定理 |
| 标签 | ψ₀(Ω_{Ω·ω}) = ψ₀(Ω_{ψ₁(1)}); 证书走标签路线, 闭包不干净, 读作"记号引导的树" | `ScafLadderQTop` | `Tω-label`, `TΩᵠ-label`, `TΩ·-label` | 定理 |
| 闭项 | ψ₀(Ω_{ψ₁(Ω)}) 与第 5 站第一次是闭项; 树上没有 `Goodᴺ`, 只过种类检验; 导入闭包不干净 (经 `Uniform3Base`) | `LvGuardTree` | `T₀` | 定义编译过; 正确性只有测试 |
| 闭项 | `EBOᵀ` 对任何判决 S 有定义, 这不算定义了 EBO | `EBOTopRaw` | `EBOᵀ`, `EBO-lim` | 定义编译过; 正确性未证 |
| 闭项 | ψ₀(Λ), ψ₀(I) 对任意判决有定义; 证实的判决只有有限层, `ver` 的树已判错 | `InaccTree`, `InaccStrikeAccept` | `ver-sound`, `ver-dev` | 定义编译过; 这两条是定理 |
| 证书 | 不带高度的紧界树上第一条证书 ψ₀(Ω_Ω), 无条件, 导入闭包干净; 只搬自 `OCF/Free/Main`, 只走闭包以下; ψ₀(Ω_{Ω+1}) 起没有 | `GuardTightCert` | `Good-Ω₁` | 定理 |
| 证书 | 不带高度的树上第一条新证书 ψ₀(Ω_{Ω+1}), 无条件, 闭包干净; 经桥搬自 `OCF/Free`, 这条证明写死在 Ω+1, 不是闭包定理; 标签也有 | `GuardCertMain`, `GuardCertAccept` | `Good-Ω+1`, `value-Ω+1`, `label-Ω+1` | 定理 |
| 闭项 | 不带高度的树里与塔最接近的一棵: 帧留弱证据, 比较前规范化; 看界对塔, 宽 3, 含极限分支, 测到的范围内一致 (Ω·2 以上穷尽只到深度 5); 证书没有 | `GuardWeakTree`, `GuardWeakRd` | `T₀ʷ`, `Tc-of`, `Tc-Lv₅` | 定义编译过; 一致只有测试 (`GuardWeakAccept`) |
| 闭项 | 高度和逐层输入都去掉的树, 走到 ψ₁(1)+Ω (过 `noTimes`), `Tc` 按闭包形状给 | `GuardTightTree` | `T₀`, `keepP`, `trim` | 定义编译过; 宽 2 的界测试一致, 宽 3 在 Ω+1 上不一致 (`T₀-too-high`, `GuardBridgeAccept`) |
| 闭项 | a+η 型闭包的界是 b+1, 与穿过的分支 τ 无关 (模前序) | `GuardTightBound` | `tail-ub`, `tail-lb`, `tail-free`, `mark-tail` | 定理 |
| 闭项 | ψ₁(Ω_θ) 与第 5 站有紧的读法, 一个定义不按阶段; 读到的分支最小; 跨世界的无关性要字面公共上界; 证书没有因此变高 | `GuardReadRd`, `GuardReadBound` | `Tc-F`, `Tc-Lv₅`, `Tc-of`, `tight-min`, `bound-Lv₅`, `free-Lv₅` | 定理 |
| 闭项 | ψ₀(Ω_{u₁}), u₁ = ψ₁(Ω_Ω), 无参数, 带紧读法; 只有层号合法, 没有 `Goodᴺ` | `FeedGoodTc`, `FeedGoodFirst` | `u₁ᵗ`, `T₁ᵗ`, `Tc-u₁`, `feed≈` | 定理; 正确性只有测试 |
| 闭项 | ψ₀(Ω_{Ω₂}) 没有闭项: `Diag.TΩ₂` 的 `GoodFeed` 是假的, 改只沿链要求的 `FeedChain` 未证 | `FeedGoodFirst` | `TΩ₂ᶜ` | 条件 |
| 层号 | 一个归纳-递归类型 `LF` 含一切层号到 Λ, 没有外部编号; `Legal` 的闭包定理一步对一切层号; 闭项无条件到 ψ_k(Ω_{Ω_ω}) 和 x₂, x₃ 起条件于 `Un` (节点名字的 UIP); 只是带符号链的闭项, 界对塔不一致 (`Tc-id`), 没有 `HS` | `LevelFixCore`, `LevelFixVal`, `LevelFixFold` | `LF`, `Legal-Ω̂`, `Legal-Λ`, `Tψ-Ωω`, `x̂₂`; 条件 `x̂-if`, `ψ₀Λ-if` | 定义编译过; 条件 |
| 层号, 不开 K | 换折叠接口后 `Un` 消掉: `x̂`, `ψ₀Λ` 是不开 K 的无参数闭项, 类型 `T⁰` 里仍带待计值符号, 还不是序数, 没有 FGH 的值; 对旧树有限测试一致, 界的不一致照旧 | `LevelNoK`, `LevelNoKLv`, `LevelNoKU`, `LevelNoKFold` | `Cf-toU`, `self-U`, `WF-U`, `irr-U`, `cmpBr`, `x̂`, `ψ₀Λ` |
| 层号, 不开 K | 紧读法对一切合法层号一个定义 (`Tc-of`), 折叠改 `owk` 一行, 旧的三条界不一致在测到的范围内消失; `LF` 上的计值判据 `Goodᵁ` 只在 ψ₀(Ω₀) 有实例, 第一个障碍在 ψ₀(Ω_Ω): 证书要字面 `Lgl`, `HS` 给不出 (`no-HS→Lgl`) | `NoKCertRd`, `NoKCertTree`, `NoKCertTc`, `NoKCertEval`, `NoKCertSmall`, `NoKCertNeg` | `Tc-of`, `cut`, `cnt-Λ`, `Tψᵗ`, `x̂ᵗ`, `ψ₀Λᵗ`, `Goodᵁ`, `forceᵁ`, `G-x̂₀`, `HS-Y`, `no-HS→Lgl`, `no-⊑-Cp` | 定理; 界是有限测试 |
| 闭项 | ψ_k(Ω_{Ω_{n+2}}) 一个 `Fold` 对一切 n, 新守卫下 Ω_{n+2} 有 `WFˢ`; 闭项不等于序数: 链点读回要 `GoodFeed`, 高层只有恒等读法 | `DomFoldDiag`, `DomFoldNext` | `Tψₙ`, `Tψ₀ₙ`, `WF-Ωᶠ`, `Cf-Ωₙ` | 定义和层号证书编译过; 正确性只有测试 |
| 记号与树 | 带基本列下降证明的记号机械地转成树, FGH 逐点相同; 有标签的树都等于这样的树; 主线的 `fgh` 就是记号沿基本列的 FGH. 这棵树读记号, 不进成品 | `AccTree`, `AccTreeLab` | `fgh-tree`, `fgh-treeᴱ`, `lab-tree`, `Lab≅tree`, `fgh-main` | 定理 |
| 判据 | 值的相对判据: 高度结构上的 `V-rows` (后继严格升, 极限连续, 链行是上确界, 闭包行严格升) 对一切实例是定理; 它不决定值 (`rows-blind`). 高处树有无标签的严格上下界 | `ValueJudgeRow`, `ValueJudgeRowV`, `ValueJudgeRowNeg`, `ValueJudgeInst` | `Rows`, `V-rows`, `T₀∞≺T₁∞`, `T₁ᵀ≺T₂Ω`, `T₀-sup`, `rows-blind` | 定理 |
| 判据 | 字面 Ω_Ω, Ω_{Ω·2} 上的值规格 `IsPsiᴸ` | `ValueJudgeSpecInst` | `spec-ΩΩ`, `spec-Ω·2` | 条件 (前提未证) |
| 判据 | 证书的否定判据 `Pinch` 对一切树是定理; 恒等读法的树在 Ω+1 上没有证书; `HF` 降为读法的诊断 | `TreeJudge2Base`, `TreeJudge2Id`, `TreeJudge2Hf` | `pinch`, `no-id`, `no-bridge`, `hf-class`, `hf-fails` | 定理 |
| 判据 | 界的判据 `HF` 与 `ghost`; 盲测 66 条对 65 条 (`TreeJudgeBlindResult`), 大多是折叠行的展开, 证据不重; 没有定义值的判据 | `TreeJudgeBase` | `HF`, `ghost`, `force-≃`, `rebound`, `hf-indep` | 定理; 拒绝与盲测多为测试 |
| 读回 | ψ₁(Ω_θ) 读回成好层号, 对一切 θ, 无条件, 导入闭包干净 | `LvGuardUni` | `WF-F`, `Cf-F`, `F-mono`, `Cf-Lv₅` | 定理 |
| 读回 | 层号证书对一切 k; 给的是 `WFᴬ`, 不是 ψ₀ 输出的 `HS`, 对任何 S 只说明合法 | `LevelKTower` | `Cert∀` | 定理 |
| EBO 接口 | 裸层号路线恰好要一族 `Family`; 闭项是条件定理, EBO 还没定义 | `EBOTopRaw` | `res→fam`, `fam→res`, `G-good` | 条件 |
| EBO 接口 | 通用定义闭合到 BTBO 段 | `EBOTopLow` | `instᶜ` | 定理 |
| EBO 接口 | 不需要 S 处处正确, 不需要 I 层、`Syn`、到 Ω_Ω 的单一 `WF` | `EBOTop` | 无 | 判断 |

## 主线与下一步 (2026-11-04 作者定)

**主线是差树** (`TLRule`, `SumOne`, `SumHt`, `BrwMid`, `BrwHigh`, `LayerTr`): 极限节点存差, 部分和字面是第一位置, 合法性由形状给出; 中间层作为读法是布劳威尔树 (`BrwHigh.Lg-br`), 作为数据要存增量 (`incr-blind`). 其余路线封存, 现状与重开方法见 Survey/RouteSeal.md; 带高度的一族 (`LadderOrd`, `CrossM`, `EmbVV`) 是第 4 层的参照树, 要保持可编译.

1. **第 4 层:** 先证折叠的输出满足 `Cv` (CvFold 一路, 在跑), 由它得值同余, 再写带上下文的层单调, 在有参照树的几站验收: Ω+1, Ω·2, Ω·ω, Ω·ω². `Cv` 不成立就换备用: 同族树互比 (以 `TLRule.T≈` 为锚点) 或把 `BTBOFullEmb.Ψ-emb` 推广到差树.
2. **攀爬:** 每站先证严格增长 (只说明不塌缩), 记翻译账; 第 4 层只在有参照树的站上补. 参照树只到 ψ₀(Ω_{Ω·ω²}), 再往上要树侧的值判据.
3. **摆脱侧:** 让高度由回灌生成, 不逐维添加 (现在的 (p, a), (r, p, a) 是照 Ω 的算术写的).
4. 部分和算不算累加, 等 Ω+1 的毛刺有值层定理再由作者定.


路线审查: `Survey/RouteReview.md` (Fable 5.1, 2026-11-04), 含树语言的雏形, 脚手架分账, 三个实验; 附带实验 `TreeLangFeed`. 其中的路线建议是判断, 作者定.
实验 1 (`TLOne`): 不新增节点的原则版写得出, 带证书, 严格过 `T⊤`; 判断它只到下一批不动点, 缺的是对象层绑定. 见 `TLOneThm` 的 `above-α`, `T⊤≺T̃ᴬ`, `no-world`, `no-lift`.
实验 3 (`TLCode`): 高度只接受带证书的码 (`HL`), 主线没有 Σ 和 `⌈_⌉`, 没有新强度 (`new⊂old`); `T⊤` 的累加只剩参数 `padO`, 无累加的 `Out` 未走通. `exact→LPO`, `binder→LPO`.
实验 2 (`TLOps`): 高度也取 A, `View`, `HtB`, `Code`, `Z`, 地板都消失; `GᴺΩ̇`, `GᴺTᵠ` 的位置统一成 `ψW` 加 `C′`, 只在新树上; `Gν` 没有进来. `Tᵖ` 带世界前缀无条件有 `HS`, 新树与旧树的值到 ψ₀(Ω_Ω). 残余 `Hn`, 折叠的 Buchholz 形状. 见 `TLOpsMain`, `TLOpsPre`, `TLOpsClo`, `TLOpsAccept`.
前缀 (`TLPrefix`): 不改值的前缀 `VP`; 世界前缀在 ψ₀(Ω_Ω) 不改序数值 (`TᵖΩ≈`); 证据放进数据树的 `lim`, Ω 带证据造出, `HS-ord` 不要 `WF` (`TLPrefixNative`), 折叠还没写完. `graftV→LPO`, `abs-overshoot`, `no-⊕≼`.
走到头的判据 (`TLEnd`): 相对封顶是定理 (`closed-self`, `closed-min`, `rel-cap`); 绝对封顶是空的 (`cofinal`, `no-stop`, `gen-all`, `T₁-below-F`); 无外部输入的类有上界 (`Cap`), 分辨力未证. 树侧还不能不看记号判断必须加新东西.
对象行为的判据 (`TLBehave`): 不看记号, 在 `WorldTH` 一族有分辨力: 世界内的一切对象不 `Ad` (`no-ad`), `T₁` 的对象 `Ad` (`top-ad`), 高度行折叠一次被下一行吸收 (`abs-row`), 顶不被吸收 (`no-abs-top`). 是绑定的语义刻画, 没有推出必须加新原语; `blind`, `cap-trivial`, `floor-trivial` 否定单调的值判据.

## 翻译账

攀爬模块加了什么 (规则见 `AGENTS.md`). 依据多为判断, 第一批来自路线审查和各文件的自述.

| 模块 | 记号读来的字段或形状 | 类 |
|---|---|---|
| `LadderOrdTree` | 第 0 行三分, 链行第 0 项, 高度读法 | 加深 |
| `CrossMTop` | `tH` 按记号的基本列设计 | 加深 |
| `OrdLabZ*`, `EmbVVOZ*` | 克隆只为贴标签 | 加深 |
| `CrossMNode` | 无新字段; 对 `Node` 一步, 不动点刻画 `cof-out`, `cof-ht` | 提供信息 |
| `OrdLabReadTop` | 无新字段; `same-M₂` 给出与记号的差 | 提供信息 |
| `NoCumMain` | (p, a) 的形状照 Ω·p+a 写; `ψW` 分离累加 | 提供信息, 形状受记号影响 |
| `CumHtBase` | 三位 (r, p, a) 照 Ω²·r+Ω·p+a 写, `Ω̇′` 六种情形照基本列写 | 加深 |
| `WorldTHW` | `ht`, `top` 照 Ω·a, Ω² 写, 第一站对照记号的第 1 项; 没有新构造子 | 加深, 程度小于 `tH` |
| `TLOneDef`, `TLOneLeaf` | 第 0 支读自记号; 数据节点, 更高世界的分支, Kripke 分支由报错和定理逼出; α ≥ 1 的基本列由现成规则生成 (测试) | 提供信息 |
| `TLOpsW` | ψ(0)=Ω_τ, ψ(a+1)=ψ(a)·ω, `add` 读自折叠的 Buchholz 形状, 三算子导不出; 第一支与起点 η₀=1 读自记号; 没有新构造子 | 提供信息, 折叠形状受记号影响 |
| `Om1HnCx`, `Om1HnPsi` | 折叠没改, 没有新构造子; 类的写法照 `OCF.Free.Good`; 守卫字段树逼的 | 提供信息 |
| `TLRuleSum` | S = ω· 抄自旧折叠; Ω_{c+1} = Ω_c + ∑1 和坐标从 Ω_k 算起, 是对照旧树的链设计的; 少了 `add`, `rep`, `up` | 提供信息, 形状受旧树影响 |
| `SumOneTree`, `SumOneFold` | 世界照 `TLOpsW` 的形状 (壁垒要求); S = ω· 抄自旧折叠; 读当前输出就是 γ₁ = ψ₀(X) 的形状 | 提供信息, 形状受旧树影响 |
| `SumHtTree`, `SumHtFold` | 层照 Ω·p+a 写, 字典序照记号的序; 节点种类照 `TLOpsW`; S = ω· 抄自旧折叠; 没有新的读自基本列规则的构造子 | 提供信息, 形状受记号影响 |


## 按侧面的入口

**定义.** 先读 `OCF/Free/Tree`, `Uniform4Base`, `LvGuardBase`. 最好: 证书最高在 `LadderOrdTree` (高度是序数码之下的位置, `HB`), 标签最高在 `LadderInfTree` (结构 `HtS`, 实例 ℕ, ℕ∪{∞}, ω+ω; ℕ 实例与 `LadderNFTree` 的树 ≅, `agree-ℕ`); `noTimes` 只杀旧树; 不带高度、走得更高的是 `GuardWeakTree` (取代 `GuardTightTree`), 证书到 ψ₀(Ω_{Ω+1}) (`GuardCertMain`). 已取代: 帧塔 `Uniform3Base` (`Uniform4Expt`; 只限 ψ_{Ω+1} 以上, 以下仍是活定义), `Uniform5Syn` (下标形状由 `LadderNFTree` 继承), `UniformLvTree` (`noCert₂`), `LvKeyTree`.

**证书.** 先读 `OCF/Free/Good`, `OCF/Free/Main`, `UniformNF5Main` (讲解在这). 最好: `LadderOrdMain`, `LadderOrdCert`, `LadderInfMain`, `LadderInfCert`, `LadderMonoClosed`; 层号一侧 `LvGuardUni`. 已取代: `UniformNF4Main`, `UniformNF3*`, `UniformPending*`, `Pending`, `TreeNF`, `NotFree`. `GoodLBase` 的 `Goodᴸ` 带标签, 只能探路.

**标签.** 先读 `Correspond` (`Lab`), `Label` (`BTBO-label`), `ScafLadder`. 记号在 `EBO`, `StandardOmega`, `SystemOmega`. 最好: `LadderLabAccept`. 被更高处覆盖 (定理仍成立): `GoodL`, `OmegaK`, `OmegaExp`, `Uniform3Full`, `Uniform4Label`, `Uniform5Top`.

**正确性判据.** 先读 `OCFSpec` (`IsPsi`), `VerdictSpec`, `InaccModulusBase` (`Reg`, `wk`). 最好: `TreeJudge2Base` 的 `Pinch` (链的第 0 点读进头不高于 t₀ 的闭包的界, 则没有证书) 对一切树是定理; `HF` (同头同界) 只是读法的诊断 (`TreeJudge2Hf`), 不管值. 值的相对判据在 `ValueJudgeRow`, 字面 Ω_Ω 上的规格只有条件定理 (`ValueJudgeSpecInst`). `OCFSpec` 是低处的判官, 无条件的够不到 Ω_Ω; `VerdictSpec` 对判决是规格, 对树不是; 高处对值没有判据. 不再走: `Value` 的 `VLab` (不省代价), `InaccTreeAccept` 的 `Agree` (太弱, `b-bad`).

**终局.** 先读 `EBOTop`, `EBOTopRaw`, `EBOTopBarrier`. 最好: `EBOTop`, 但先后次序以 `ScafOmega2` 为准 (难点在 ψ₀(Ω_{Ω+1}) 内, 高处都要先过 ψ₀(Ω_{Ω·2+1})). 验收尺 `EBOI` 的新规则只有测试. 已取代: `LvIR` 的判断 "好输入要有公共上界", `InaccScout`.

**审计.** 先读 `Survey/scripts/importclosure.py`, `Survey/scripts/depslice.py`. 最好: 导入闭包, 这是编译器保证. 已取代: 只靠切片的结论 (`UniformNF5Main` 一带模块层仍导入记号).

## 死路索引

都是编译过的, 但只杀写明的那个想法. 动手前先对照.

| 定理 | 文件 | 杀掉的想法 |
|---|---|---|
| `barrier` | `OCF/Barrier` | 下标类型以 `Ordᴰ` 为精确初始段, 含 Ω-共尾元, 又有有界三歧 (推出 LPO) |
| `Toy.loop` | `Symbolic` | 不可数下标作可数层的构造子 (计值、取分支、下降成环) |
| `¬tri` | `Uniform5Wall` | `Ordᴵ` 上全局三歧 (同名的 `VerdictSpecEvid` 是另一条; `¬triᴵ` 在 `EBOTopBarrier`) |
| `dec→WLPO` | `Stage2` | 对一切 a 判定 a ≺ suc ω, 即第二层全分支节点 |
| `Trich₂→WLPO` | `InaccScout` | 第二层有界三歧 |
| `noBT` | `InaccTree` | 以 Ω_Ω 为界的结构三歧 (直接是假的) |
| `no-topᴵ` | `EBOTopBarrier` | `Ordᴵ` 里有 Ω-共尾元 |
| `dec-A→WLPO` | `InaccFloorNeg` | 判定分支可容许 (`Funext` 为前提); 证据须由树携带 |
| `¬WF-Reg` | `InaccFloorNeg` | `Reg` 当分支证据 |
| `no-uniform` | `InaccThetaNeg` | 一个读原始层号的 S 对一切层号正确 (同形见 `LevelKNeg`, `LvStratNeg`); 单个固定世界未解决 |
| `no-Ω₂` | `InaccThetaNeg` | Ω_{Ω₂} 的层号要第 1 层全部分支正确; 改成地板内就共存 (`¬full`) |
| `allReg→WLPO` | `InaccSingularBase` | 判决对全部规整树正确 (`Funext` 为前提); 类须是有向族 |
| `no-read` | `LvIRNeg` | 读证据的派发比 ω+1, 只要好输入含反例族 |
| `no-read-ᴵ` | `ScafOmega2Family` | `Ordᴵ` 上目标 ω+1 的无条件判决 |
| `no-read-GL` | `ScafOmega2GL` | 同上, 在 `GL` 上 |
| `no-read-GLG` | `LvGuardNeg` | 同上, 在守卫层号上 |
| `no-bra-cmp` | `LvGuardNeg` | Ω 上两条任意路径三歧, 比较两个分支 |
| `no-cut` | `GuardReadNeg` | 切口由 `⊴` 算出, `Str` 作判定 (推出 LPO); 结构给的切口不受影响 |
| `no-lim-cmp` | `GuardReadNeg` | 任一层号与极限节点总可比 (推出 LPO) |
| `no-GoodFeed` | `FeedGoodNeg` | `F⁺` 对一切 `GL` 给出合法层号 (`Tc` 可读证明, `≈` 自反被破坏); 不杀链上的 `FeedChain` |
| `no-≈₁` | `FeedGoodNeg` | `Lv₅` 与 u₀ 的回灌 `feedL` 相等 (下界 1 对 2); 正确形式是 `feed≈` |
| `chain-stuck` | `DomFoldNeg` | 第一路径守卫放得过带链的闭包: 同键活帧在 Ω₁+3 时链点 `Lv₅` 过不了; 旧守卫放得过但没有 `WFˢ`; 只否定这两个守卫 |
| `no-tn-ω⁺` | `DomFoldNeg` | 目标对 ω+1 不走路径 (推出 WLPO) |
| `T₀-too-high` | `GuardBridgeNeg` | `GuardTightTree` 的 `T₀` 经 `Good-≲` 的桥到 `OCF/Free` 的树 (界 2 对 1); 没否定 `T₀` 有 `Goodᴺ` |
| `floor-gap` | `GuardBridgeNeg` | 表的路线的地板 (`fk`) 不超过对面的地板 (`fb`), 分支值是极限时 |
| `no-join` | `GuardBridgeNeg` | L ⊑ η 时总有字面公共上界 (L = lim 2n, η = lim (2n+1)) |
| `hf-indep` | `TreeJudgeBase` | `HF` 是合法性: 有 `Goodᴺ` 的树可以违反它 |
| `hf-blind` | `TreeJudgeNeg` | `HF` 管值: 没有闭包的树都过 |
| `cover-false` | `GuardWeakNorm` | 规范位置的帧 ⊑ 节点的层, 对一切位置 (极限节点上假); 不否定只在后继和闭包处成立的版本, 也不否定 `Goodᴺ` |
| `H-vacuous` | `InaccStrikeFixed` | `InaccStrike` 的 `T₂-cert→⊥` 空真; 有效陈述是 `T₂-cert→⊥′`, 只否定判决实际返回 `pen` 且 `G` 含原像的情形 |
| `acc→nat` | `AccTree` | `EBO` 字面的 `Acc` (全部项上的序) 超过自然数; 要改成基本列下降或可数标准形上的良基 |
| `¬acc⇒lab` | `AccTreeLab` | 基本列下降的 `Acc` 自动给标签 (Ω 有 `Acc` 无标签); 可数标准形上的良基给标签 (`wf→lab`) |
| `no-triᴼ` | `LadderInfOrd` | `Ordᴵ` 字面地作 `HtS` 的高度 |
| `no-all-Ord` | `LadderOrdNeg` | 一个 `HtB` 字面忠实地含全部 `Ordᴵ` (前提不可满足, 这就是结论); 不否定 `HB` 按码分段 |
| `all-Ord→LPO` | `LadderOrdNeg` | 同上, 只忠实到值 (推出 LPO) |
| `viewE→LPO` | `LadderOrdNeg` | 不带证书的 `Ordᴵ` 都有第 0 行的写法, 改 `View` 加 "空" 也不行; 码的值上成立 |
| `no-tri-code` | `LadderOrdNeg` | 跨 M 的全局三歧; 固定 M 内成立 |
| `no-step²` | `LadderOrdNeg` | `view-step` 这个字段; 不否定 ω² 作高度 |
| `no-id` | `TreeJudge2Id` | 恒等读法的 `T₀` 在 Ω+1 上有 `Goodᴺ`; 紧读法的树没被否定 |
| `no-bridge` | `TreeJudge2Hf` | 折叠输出头相同推出目标相同 |
| `rows-blind` | `ValueJudgeRowNeg` | 序的五条行律 `Rows` 单独决定值 |
| `reg-blind` | `ValueJudgeReg` | `Reg⁰` 决定大数 (ω 与 ω⁺ 都过, FGH 不同); 它只排除 `slow` (`slow-not-reg`) |
| `no-triᴸ` | `GuardCertHt` | `LG` 的路径序字面地作 `HtS` 的高度 (全局三歧); 带公共上界的 `cmpN` 不受影响 |
| `no-min` | `GuardTightNeg` | 每个合法闭包都有最小的读位置; 落地规则代替读位置的证据 (推出 WLPO) |
| `no-WFˢ-Ω⁺` | `GuardTightUp` | 现在写法的 `Fold` 实例化到第 1 层定义域: Ω₂ 没有 `WFˢ`; 只杀这个 `WFˢ`, 局部比较 `cmpW` 没被否定 |
| `noAll` | `UniformLvNeg` | 一个层号装下全部地板: 该闭包对一切 K 有 `Goodᴺ` |
| `noCert₂` | `LvCertNeg` | `UniformLvTree` 的 `T₀` 过 Ω·2 还有证书; 种类测试看不见 |
| `noW` | `LvCertNeg` | 同高度支配: 界被抬到 τ+1, 第 0 点却不依赖 τ |
| `noTag` | `LvKeyNeg` | 尊重 ≅ 又分开 ≺ 的 ℕ 节点标签 |
| `noTimes` | `LvKeyNeg` | 旧树的 ℕ 高度标签够用: ψ₁(1)+Ω 上内外相撞 |
| `¬both-low` | `LevelKNeg` | 字面分离下两个 ≈ 的 `limᴼ` 同时作低层 (`LvStrat` 去掉 `low-≈` 后不适用) |
| `¬mono-0` | `LvStratNeg` | 层号好的树上 ψ₀ 单调 |
| `self-bound` | `LvStratNeg` | 有界地板装下目标 0 的链 (这条是引理, 否定是 `¬X∈A₀`) |
| `G-unbounded` | `ScafOmega2Family` | 好输入必须有公共上界 |
| `wrong-fold` | `VerdictSpecReject` | 判决全对就保证折叠对 |
| `spec-blind` | `OCFSpecNeg` | 值规格能管大数: 同值的树 FGH 不同 |
| `no-all-branch` | `EBOTopBarrier` | 好谓词对全部分支封闭 |
| `¬BaseRaise` | `UniformNF3D3Neg` | 底抬升闭包 (深度 1 为假, 也不需要) |
| `ψ⁰-not-cong` | `Value` | ψ⁰ 对层 ≥ 1 的参数尊重值 |
| `Good-not-value-fragment` | `OCFSpecNeg` | 单调分支片段就是折叠尊重值的片段 |
| `¬Acc-T` | `Uniform5NF` | 不带标准形的语法序作分层 (`Syn` 路线的边界) |
| `¬TΩ2-label` | `OmegaSqA` | 只对 `Uniform2Base` 的旧树; `Uniform3Full` 的 `TΩ2-label` 已越过, 不是普遍否定 |
| `no-⊑⁰-lab` | `BTBOValNeg` | 已发表 BTBO 经 ⊑⁰ 进过基本列验收 ψ₀(Ω_Ω) 的树; 不否定序数值相等 (`BTBO≈` 已证) |
| `ordᴰ-not-cong` | `BTBOValAbsorb` | `ordᴰ` 的放大只看值, `HS` 就够被吸收; 严格递增的树上 `absorb` 成立 |
| `no-val-T⊤` | `ValLabNegTop` | `T⊤` 经 ⊑⁰ 进过基本列验收的树; 同样的 `no-val-M₂`, `no-val-ω²`, `no-val-ω·3`, `no-val-ω^ω`, `no-val-ε₀` (`ValLabNeg`). 只否定前驱结构验收这一档, 不否定序数值验收, 强度, 读法 |
| `no-Legal-ordᴸ` | `CumReadBase` | 累加读回逐点读 `lc` 的分支后仍 `Legal`; 不否定只把下标累加 (`next`) |
| `no-⊞-left` | `CumReadBase` | 世界的加法左边对第一位置单调; 同一闭包在两个世界的链字面不可比, 是带闭包的层证书的卡点 |
| `no-rd` | `CumUpClean` | 逐点读对一切 `HS` 树字面合法; 不否定对折叠的输出合法 |
| `dec⊲→LPO` | `CumUpClean` | 判定第一位置再补偿 (推出 LPO); 不否定带证据的补偿 |
| `no-Hn-b` | `NoCumHnNeg` | 现在 `mx` 加字面第一位置的守卫, 对字面任意目标成立 (反例目标 w₂ = lim 2n); 不否定目标是链点前驱时的 `Hn`, 不否定 Ω+1, 不否定不累加 |
| `exact→LPO` | `TLCodeNeg` | 每个 `Ordᴵ` 都有精确的带证书的码; 带证书的 η 上成立 (`exact-Lit`), 不挡输出带证书 |
| `binder→LPO` | `TLCodeNeg` | ŝ 绑定的每支都有精确带证书的高度; 只否定不改绑定类型的写法 |
| `no-Good→Str` | `TLCodeNeg` | 只由 `Goodᴺ` 读出 `Str`; 同类 `Out0.no-Str-out` 否定对一切 α 输出都严格 |
| `cofinal`, `no-stop` | `TLEndNeg` | 用值的上界判断世界内操作走到头: 一切 `HS` 树低于某闭包点, 闭包点没有最后一个. 只否定这个判据形状, 不否定绑定有用 |
| `no-Root` | `Om1HnNeg` | 对字面任意 a 要 `Root`; a = 0, 1, 2 是定理 |
| `cap-trivial`, `floor-trivial`, `blind` | `TLBehaveNeg` | 单调的值判据分辨 `T₁` 与高度行; 非单调的值谓词没有否定 |
| `no-clo-·2`, `no-clo-+1` | `AddCloNeg` | 加法封闭由树侧要求 (`Req`: 回灌合法, 层严格, 单调, 保持严格) 逼出; 前提 `req-·2` 可满足 |
| `TD≺` | `AddCloAccept` | 去掉地板 ψ_t(0)=Ω_t 后值不变 (塌到 ≤ 1) |
| `incr-blind` | `BrwHighOne` | 只存合法的布劳威尔 Ω-节点, 靠沿前缀单调读回增量 (坐标 ω 处两节点值不同); 不否定带连续性证据的节点 |
| `no-round` | `LayerTrNeg` | 第 1 层差树经布劳威尔树往返值不变 (分支读坐标的字面形状); 加 `Cv` 成立 |
| `no-T` | `TightValGlobal` | 占位 0 的紧界树 `TΩ2′ˢ` 有证书 (Ω₃ 处就不合法); 只否定 `ψᵉ′` 这一族, 不否定别的紧界设计 |
| `no-cert` | `TightValFloor` | `Uniform2Base` 的旧地板树有证书, 对一切环境; 判断错在守卫, 不在值 |
| `drop-at` | `TightValAccept` | 把占位换成不增长的 (空转) 就能保住值: 上确界不超过 ψ₀(Ω_Ω·Ω₂) |

**已关闭的方向** (2026-11-03 经 Fable 5.1 逐条独立审核, 审核者先读代码; 详见 `LOG.md`). "不值得继续" 是判断, 不是否定:

| 方向 | 文件 | 审核结论 | 被定理否定的只有 | 还没被否定的 |
|---|---|---|---|---|
| `Lv` 上的总判决 | `InaccSingular` | 未否定, 不值得继续 | 对一切层号或一切规整树正确 (`noBT`, `no-uniform`, `allReg→WLPO`) | 只在折叠问到的有向类上正确 (奇异下标) |
| I 层降维打击 | `InaccStrike` | 字面版已否定; 其余未否定, 不值得继续 | 以 I 为公共界让比较有界 (`Trich₂→WLPO`, `no-middle`, `noBT`) | `Lv` 加外部判决的标签路线和证书路线; 两条的工作已被主线取代 |
| 值相等代替逐项一致 | `Value` | 未否定, 不值得作验收重开 | 同余式 (`ψ⁰-not-cong`, `Good-not-value-fragment`) | `VLab` 省不掉 `Lab`, 对记号的值代价更大 (判断); `IsPsi` 判官路线继续, 但它不判大数 (`slow`) |
| 帧塔 | `Uniform4Expt` | 未否定, 不值得继续 | 朴素 `Ψ₁ᶰ`, 且只是路径上的有限反例 | 换底, 分层 (纸面). ψ₀(Ω_{Ω+1}) 以下帧塔仍是带定理的活定义 |
| 归纳-递归块 | `LvIR` | 未否定, 不值得单独立项 | 块内对全部 `HS` 输入的带证据判决 (`no-read`) | 下界守卫进块 (`LvIRGuardProbe`, 只是形状测试), 无证据派发 |
| `limᴼ` 作低层接 `HS` | `LvStrat` | 未否定, 不值得继续 | 目标 0 上 `Cx` 级的 `mono-lv` (`¬mono-0`) 等 | 加树级边条件后就是守卫路线, 重开等于重复 |
| `Syn` 阶梯 | `Uniform5Assess` | 全语法变体未否定, 不值得继续; **下标为 (m, α) 的变体没有关闭, 就是 `LadderNFTree` 的下标** | 不带标准形的语法序 (`¬Acc-T`), 全局三歧 (`¬tri`) | 全语法加标准形 `Acc`, 进不了成品 |

## 不用读的

- `ScafLadderZ*`: 机械克隆, 由 `Survey/scripts/scafladder/mkworld.py` 生成 (`ScafLadderZLvWalk` 除外).
- `LadderLabZ*`: 机械克隆, 由 `Survey/scripts/ladderlab/mkall.sh` 生成, 只用于贴标签.
- `LadderNFW*`, `LadderMonoW*`, `LadderInfW*`: 机械克隆, 由 `Survey/scripts/laddernf/` 生成, 只用于验收. `LadderInf*` 的 23 个证书模块也是由 `mk_inf.py` 从 `LadderNF*` 改写的.
- `OCF/Free/Lab/`: 由 `Survey/scripts/freeextract/` 生成. `OCF/Free/` 主线也是切出来的 (`OCF/Free/Closed`, `OCF/Free/Bridge` 手写), 讲解看原文件.
- `archive/`: 冻结的旧材料.

## 工作方法

```sh
agda --library-file=<含 stdlib 与 cubical 路径的文件> -i src -i probes <文件>
python3 probes/Survey/scripts/importclosure.py --only OCF.Free. --only OCF.BTBO OCF.Free.Closed
python3 probes/Survey/scripts/depslice.py <H> <模块:名字>
python3 probes/Survey/scripts/mapcheck.py
```

- 报退出码时不要经过管道.
- `Survey/scripts/importclosure.py`: 只看模块导入, 粒度粗, 结论是编译器保证. 只保证不引用, 不说明没受记号启发.
- `Survey/scripts/depslice.py`: 定义级, 语法近似, 看不见隐式参数和模块别名. H 是 agda 的 --html 输出目录. 要带正对照.
- 三档不混: 编译过的定理, 有限测试, 判断. 种类检验不看界, 全过也不算证据 (`noCert₂`).
- 查文献看 `Survey/OrdinalNotationsGuide.md`, 查外部代码看 `Survey/CodeGuide.md`, Agda 的强度与可用特性看 `Survey/AgdaStrength.md`, 不要重新调研.
- 细节和历史查 `LOG.md`. 新结果记进 `LOG.md`; 状态变了改这张图, 再跑 `Survey/scripts/mapcheck.py`. 老文件说的 "probes/README 的认证规则" 现在在 `LOG.md`.
