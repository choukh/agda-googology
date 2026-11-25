# 第十一次路线审查: 主线是否最佳, 值定理有没有整体引理的侧路

2026-11-13. 作者原话: "我感觉我们可能又提前钻到一些并非最优的细节处在死磕了. 请再次跳出来, ……将所有成果视为数据, 只相信编译定理和条件定理, 高屋建瓴地做一次路线审查". 审查者 Fable 5.2 (本环境里最新的 Fable). 次序: 定义 (写 [预览](Reports-2026-11-12/Review11-preview.txt)), 定理陈述, 最后文档. 简报与回报原文: [Reports-2026-11-12/Review11.md](Reports-2026-11-12/Review11.md). 实验: [R11Exit](Reports-2026-11-12/attachments/Review11-R11Exit.agda.txt), [R11Mono](Reports-2026-11-12/attachments/Review11-R11Mono.agda.txt), [R11MonoInst](Reports-2026-11-12/attachments/Review11-R11MonoInst.agda.txt), [R11MonoTower](Reports-2026-11-12/attachments/Review11-R11MonoTower.agda.txt).

## 1 主审复核

四个纯 `.agda` (共 478 行) 拷到主审目录冷编, 退出码 0, 禁用构造 0. 读过的陈述:

- `R11Exit.exit : Closed P → P t X → (h : HC t) → toL (tree h) ≼ X` 与 `ebo-lower : Closed P → (Y : _) → (∀ k → Σ X. P (EBOψ k) X × (X ≼ Y)) → toL EBO-tree′ ≼ Y`. `Closed P` 是两条: 后继余尾时走到 `pred t`, ω 余尾时对每个 n 走到 `fsn t n`. 记号只在验收一侧.
- `R11Mono.M.mono : ∀ m {k} {V : Lw k} → MW V → (x : Ext m k) → Sim k ξ ξ′ → …`, 对任意派发 `D` (模块参数). `Sim` 是块内部两棵同层树的模拟, 不经参照框架. `MW` 里留一条 `KeepMono`.
- `R11MonoTower.Tower` 在审查者自写的无见证公共上界 (`Lw-twⁿ`, `VΛⁿ`, 与 YiBare 的上界同形) 上: `mw-tw`, `mw-Λ`, `TΛⁿ-legal`, `mono-tw`, `mono-Λ`, `value-Λ`, 无前提. 这是无见证折叠的闭项 `TΛⁿ`, 不是主线带见证的 `TΛ`.
- `R11MonoInst.Inst.mw2 : KeepMono … (witU zero) → MW (Lw-tw 2)`, `value2`: 主线的上界在塔的第 2 项上归到根见证上的一条 `KeepMono` (未证未否定).

主审另核了审查者引用的事实: `Stage2.X₂-unlabel : ¬ Lab X₂ (ctx (Ωt (natT 2)))` (第 694 行); `YiLeanValRel.RelF (lc k g) y a = ⊤`; `YiNextCore.add (lc j g) B x G.top = G.suc x`. 审查者没有核的一点主审核了: `YiLamVBtbo` 的 `D.BTBOᴵ` 与 `Label.BTBO-label` 的 `N.BTBOᴵ` 都是 `Diagonal Uniform` 的 `BTBOᴵ` (`NoCumsum` 里 `BTBOᴵ = D.BTBOᴵ`), 所以 `btbo-TΛ` 与 `BTBO-label` 接得上.

## 2 结论 (审查者; 档已标)

- **主线的块保留, 派发未定.** 合法性对任意派发成立 (`YiDlFold.Fold.Ψ-lgl`, 编译事实); 各折叠候选的无前提下界相同, 没有定理区分派发. 值定理应对派发参数化 (判断).
- **与记号有编译联系的值只有两站**: BTBO (`btbo-TΛ` 配 `BTBO-label`) 与 ψ₀(Ω_Ω·2) 的带标签参照 (`T2-label`; 对主线只有条件定理 `T2≼ᴳʷ`). ψ₀(Ω_Ω+Ω₂) 的参照 `S2.X₂` 用可数层号顶替 Ω, 且恰是标签失败的项 (`X₂-unlabel`); 它的读法是判断 (编译事实 + 判断).
- **按站往上 (ψ₀(Ω_Ω+Ω_n)) 对终点不提供信息** (判断): 不经过派发丢保留的位置; 参照框架没有 Ω 结点层号 (`RelF (lc k g) = ⊤`). 建议停掉 V44, V45 与按站新增规则; 这是停工建议, 不是否定.
- **整体策略 G 的四块**: G1 出口 (`R11Exit`, 临时试验); G2 同层单调 (`R11Mono`, 临时试验; 主线上剩 `KeepMono`); G3 跨层模拟与单调 `Simʰ`, `monoʰ`, 前提 `Compat` (未做, 判断 600 到 900 行); G4 记号直连: 对记号项递归的解释加六条基本列规则各一条引理, 交出 `Closed P` (未做, 试点 500 到 800 行, 到 Λ 2k 到 4k, 很不确定).
- **卡点在定义层** (编译事实 + 判断): 现派发在记号会保留的位置上折叠 (`dl-lim`, `not-full`), 处处完全的派发推出 LPO (`cmp-full→lpo`, `step-full→lpo`); 后者不否定 "在规范构造的读回域上完全". 决定性的实验在 ψ₀(Ω_Ω·2) 的带标签站上.
- **推荐的下一批**: A 跨层模拟与折叠单调 (先单独做, 后两路都要); A¬ 同一接口上的配对否定; A 之后 B 派发在规范域上完全 (验收站 ψ₀(Ω_Ω·2)) 与 C 记号直连试点 (`EBOψ 2` 的记号树 ≼ `read (Tw 2)`, 不经参照框架) 并行.

## 3 主审意见

- 接受: 停掉按站往上的工作 (V44, V45), 作为停工, 不作否定. 理由是两条编译事实: `X₂-unlabel` 与 `RelF (lc k g) = ⊤`; 此前首页与 RESULTS 的 "到 ψ₀(Ω_Ω+Ω₂)" 措辞已改成 "不低于参照 `S2.X₂`".
- 接受: 先闭合 A 再派 B, C (同一条未证引理的规则, 2026-11-11).
- 保留意见: G2 的无前提实例在无见证的上界上; 若 A 在主线上卡在 `KeepMono`, 主线的折叠可能要换成无见证的 (收缩见证与裸折叠两路已有回归, 判断). G4 的成本估计跨度大, 先由 C 的试点量出.
