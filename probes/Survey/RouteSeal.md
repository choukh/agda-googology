# 封存的路线 (2026-11-04)

作者 2026-11-04 定: 主线改为差树 (见 `probes/README.md` 的 "主线与下一步"). 下面的路线停止投入, 原样封存, 以备重开. 封存只是不再投入, **不是否定**: 除非写明某条编译过的否定定理, 每条都是 "暂停". 代码一律不动 (`probes/` 的规矩是不改已有文件), 所以封存的就是现在的文件.

每条写: 入口, 做到了什么 (定理), 估计到了哪 (判断), 第一个障碍, 重开时先读什么, 编译要注意什么. 强度写 ψ₀(Ω_x), x 不用 ψ₁ (可数 x 时 ψ₁(x) = Ω·ω^x, ψ₁(Ω) = Ω²; 文件里的陈述仍是 ψ₁ 写法).

验收三档: 基本列验收 (`Lab`, 逐项一致), 前驱结构验收 (互相 ⊑⁰), 序数值验收 (互相 ≼).

编译命令都是 agda --library-file=<库文件> -i src -i probes <文件> +RTS -M<堆> -RTS, 从仓库根目录. 库文件写两行 stdlib 与 cubical 的库文件路径.

## 1. 带高度的树: `LadderNF`, `LadderInf`, `LadderOrd`, `CrossM`, `CrossNext`, `TLOne`, `TLCode`

**这一族是第 4 层的参照树, 封存但要保留可编译.** 其余路线的序数值验收都要拿它作尺子.

- **入口:** `OCF/Align/LadderOrd.lagda.md`; 跨段 `CrossM.lagda.md`, `CrossNext.lagda.md`; 原则版实验 `TLOne.lagda.md`; 去累加的码 `TLCode.lagda.md`.
- **定理:** 闭包定理对一切高度结构 (`LadderOrdMain.GᴺTᵠ` 对一切 `HtB`; `HB` 对一切码); 上移与跨段 (`CrossMUp.up`, `CrossMUpTree.up-sim`, `CrossMNode.Gν`); 合法的最大闭项 `CrossMClosed.T⊤` (`HS⊤`, `fgh⊤`), 与 `CrossNextInst.T̂ᵀ` ≅; `TLOneThm.above-α`, `T⊤≺T̃ᴬ` (原则版严格过 `T⊤`).
- **验收:** 基本列验收到 ψ₀(Ω_{Ω·ω·2}) (`OrdLabReadTop.label-Tᴸ`, 主线 `OrdLabAccept`); 前驱结构验收到同一处 (`same-M₂`), 再往上是假的 (`ValLabNeg` 的 `no-val-M₂`, `no-val-ε₀` 等, `ValLabNegTop.no-val-T⊤`); 序数值验收到 ψ₀(Ω_{Ω·ω²}) (`EmbVVInstO2.vv-ω²`), 工具 `EmbVVMain.V-≃` 不读记号.
- **判断:** `T⊤` 读 ψ₀(Ω_{Ω²}); `LadderOrd` 的读法 ψ₀(Ω_{Ω·(1+rk p)+α}) 只在这个闭包点之下算数.
- **第一个障碍:** ψ₀(Ω_{Ω²+1}): `CrossNext` 的 α ≥ 1 要闭包定理约 1 万行带地板索引和 `tH`; `TLOne` 说不新增节点只到下一批不动点, 必须新增对象层绑定 (`top-new`, `no-world`). `WorldTH` 的 `Hg` 是绕开 `tH` 的另一写法 (见第 3 条).
- **否定 (只否定写明的形状):** `LadderOrdNeg` 的 `no-all-Ord`, `all-Ord→LPO`, `viewE→LPO`, `no-tri-code`, `no-step²`, `no-cofinal`; `CrossMNeg.no-⊂⌈⌉`; `CrossMNode.≼↛⊑`; `TLCodeNeg` 的 `exact→LPO`, `binder→LPO`, `no-Good→Str`.
- **重开先读:** `LadderOrd.lagda.md` 文件头, `CrossM.lagda.md` 的 "第一个障碍", `CrossNext.lagda.md` 的修法账, `TLOne.lagda.md`.
- **编译:** `LadderOrd` 主体要 >14G (45G 通过, 约 14 分钟); `CrossM` 25G; `CrossNext` 22G; `EmbVV` 入口约 5 分钟. 检查器比较 `forceᴺ` 或 `lvG` 的不同写法时会展开整条证书, 陈述逐字写, 不用别名 (见 `OrdLabReadTop`, `CrossMInst` 文件头).
- **克隆与脚本:** `LadderNFW*`, `LadderMonoW*`, `LadderInfW*`, `LadderLabZ*`, `OrdLabZ*`, `EmbVVOZ*` 是机械克隆; 脚本在 `Survey/scripts/laddernf/`, `ladderlab/`, `ladderord/`, `ordlab/`, `crossm/`, `crossnext/`, `embvv/`, `tlcode/`.

## 2. 不带高度的树: `GuardTight`, `GuardRead`, `GuardWeak`, `GuardCert`, `GuardBridge`, `WeakBridge`

- **入口:** `OCF/Align/WeakBridge.lagda.md`; 前史 `GuardCert.lagda.md`, `GuardWeak.lagda.md`.
- **定理:** `WeakBridgeMain.Good-θ`: 对一切 θ, ψ₀(Ω_{Ω+θ}) 一条定理, `value-θ`, `fgh-agree`; 基本列验收 `WeakBridgeLabel.label-θ` (带标签的 θ < ψ₀(Ω_{Ω·2}) 搬过桥).
- **第一个障碍:** Ω·2: `WeakBridgeNext.keep-Ω·2` 说比较要分键; 判断 1500 到 3000 行, 建议先把 `WeakBridgeFold` 对层的接口参数化.
- **否定:** `GuardBridgeNeg` 的 `T₀-too-high`, `floor-gap`, `no-join`; `GuardWeakNorm.cover-false`; `GuardCertHt` 的 `no-triᴸ`, `no-botᴸ`, `no-viewᴸ`.
- **编译:** `WeakBridgeOp` 峰值约 16G (堆上限 15G 内通过); `WeakBridge` 约 5 分钟.

## 3. 累加的树: `CumRead`, `CumUp`, `CumVal`, `CumHt`, `Om1Cum`, `WorldTH`; 已发表 BTBO 的验收 `BTBOVal`, `BTBOFull`

- **入口:** `OCF/Align/CumUp.lagda.md`, `CumHt.lagda.md`, `WorldTH.lagda.md`; BTBO: `BTBOFull.lagda.md`.
- **定理:** `CumUpMain.HS-T` (一切 Ω·p+a), `CumHtMain.HS-T` ((r, p, a) 读到 Ω²·ω), `WorldTHInst.HS-T₁`, `T₀≺T₁`; `CumUpAcceptVal.Tᶜ≈`, `CumVal.TΩ≈` (ψ₀(Ω_Ω) 序数值验收); `Om1CumGrow.T-strict`, `step-Ω+1` (严格高于 ψ₀(Ω_Ω)). 已发表 BTBO: `BTBOFull.BTBO≈` (经 `tr₀` 与 `BTBOᴵ` 互相 ≼, 序数值验收), `St-x`, `absorb-x`; 判据 `BTBOFullEmb.Ψ-emb`.
- **大小:** Ω+1 起只有下界; `CumHt.HS-Nxˢ` 说不读输出的链也 `HS`, 所以这一族的 `HS` 不是强度证据.
- **账:** `Om1Cum` 实测 ψ₀(Ω_Ω) 累加专属第 4 层约 1230 行; Ω+1 估计再加 2400 到 4300 行, 约 8 成是毛刺造成的 (估计).
- **第一个障碍:** 序数值上界 (带基底的嵌入, 对照树一侧的单调, 值严格性); `no-⊞-left` 在 (p, a) 世界里绕开了, 没搬到别处.
- **否定:** `Cumsum.overshoot`, `BTBOValAbsorb.ordᴰ-not-cong`, `BTBOValNeg.no-⊑⁰-lab`, `BTBOFull.no-lab`, `CumReadBase` 的 `no-Legal-ordᴸ`, `no-⊞-left`, `no-cum-⊲`, `CumUpClean` 的 `no-rd`, `dec⊲→LPO`, `Om1CumIdx.no-V2`.
- **编译:** `WorldTH` 约 15 分钟, 峰值约 15G; 其余都在 12G 内.

## 4. 不累加的世界: `NoCum`, `NoCumHn`, `Om1Hn`, `NoCumNode`, `TLOps`, `TLPrefix`, `CtxMono`

- **入口:** `OCF/Align/NoCumNode.lagda.md` (最新), `Om1Hn.lagda.md`, `TLOps.lagda.md`.
- **定理:** `NoCumNodeMain.G₁` (ψ₀(Ω_{Ω+1}) 无条件证书, 无前缀, 没有 `add⁰` 的残留), `NoCumNodeAccept.BTBO≺T₁`, `same-Ω`; `Om1HnMain.G₁` (新增 882 行, 绕过字面 `Hn`); `TLOpsMain.ψW` (高度取 A, 一条定理对一切高度); `NoCumHnCore.Bach`; `TLPrefixNative.HS-ord` (证据进 `lim`).
- **第一个障碍:** 序数值上界; `CtxMonoAccept.accept-Ω+1` 已把验收化成两个前提, `Up` 就是带上下文的层单调.
- **否定:** `NoCumHnNeg.no-Hn-b`, `Om1HnNeg.no-Root`, `NoCum.no-Lit-x₀`, `TLPrefixVal.graftV→LPO`, `abs-overshoot`, `no-⊕≼`.
- **重开:** 路线 A 不必加 `oĉ` 节点 (`NoCumNode` 把第 0 层改成计值); 跨树互模拟估计 1200 到 2000 行, 这个估计出现过三次都没写过, 不可靠.
- **编译:** `NoCumNode` 约 2 分钟, `NoCumNodeAccept` 约 2 分钟.

## 5. 一次封闭的层号: `LevelFix`, `LevelNoK`, `NoKCert`

- **入口:** `OCF/Align/LevelNoK.lagda.md`, `NoKCert.lagda.md`.
- **定理:** `LF` 含到 Λ 的一切层号, `Legal-Λ`; `LevelNoKU.Cf-toU` 无条件 (不开 K 消掉 `Un`); 闭项 `LevelNoKFold.ψ₀Λ` (类型是带待计值符号的数据树, 还不是序数); `NoKCertRd.Tc-of` (紧读法).
- **第一个障碍:** ψ₀(Ω_Ω): 证书要字面 `Lgl`, `NoKCertNeg.no-HS→Lgl` 说 `HS` 给不出. 判断: 差树的 "合法性由形状给出" 可能正好补上这一步, 重开时先试把 `LF` 的折叠换成和的作用.
- **否定:** `LevelFixNeg` 的 `no-Lgl-Ωlim`, `no-cp-Ω3-Ω2`; `NoKCertNeg.no-⊑-Cp`.

## 6. 树侧判据与约定: `TreeJudge`, `ValueJudge`, `TLEnd`, `TLBehave`, `AddClo`, `AddTwo`

- **入口:** `TLBehave.lagda.md`, `TLEnd.lagda.md`, `AddClo.lagda.md`.
- **定理:** `TLBehaveThm` 的 `no-ad`, `top-ad`, `no-abs-top`, `read-above` (行为判据在 `WorldTH` 一族有分辨力); `TLEndCap` 的 `closed-min`, `rel-cap`; `AddCloAccept` 的 `T-1+cω`, `T-c+cω` (ψ₀(Ω_Ω) 这一站 ·ω 是一个带的代表), `TD≺` (地板是值逼的); `AddTwoSim.simStep`.
- **否定:** `TLEndNeg` 的 `cofinal`, `no-stop`, `gen-all` (值的上界判据是空的); `TLBehaveNeg` 的 `cap-trivial`, `floor-trivial`, `blind` (单调的值判据分不开); `AddCloNeg` 的 `no-clo-·2`, `no-clo-+1` (加法封闭不由 `Req` 逼出).
- **第一个障碍:** 判据推不出 "必须加新原语"; ·2 的下界要值上的吸收引理 (与第 4 层的值比较是同一件事).

## 7. 更早的方向

`probes/README.md` 的 "已关闭方向" 一表 (Fable 5.1 审核过) 和 `archive/` 不变.
