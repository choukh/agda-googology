# 交接: 路线乙 (层号是树) (2026-11-08)

> 给接手的模型. 本文自足: 读完它和 §6 列的几份文件就能开工. 背景、三路审查与两条路线的比较在 [RouteReview3](RouteReview3.md).
>
> **路线乙是什么.** 坚持层号本身是布劳威尔树 (写法 A), 最终定义里不出现任何有限项上的序. 另一条路线 (甲, 用自写的码作层号) 不归你, 不要做.
>
> **作者对成功率的知情.** 主审判断, 相当投入下乙的成功率约 3–8%, 不设投入上限约 15–25% (判断, RouteReview3 后续讨论). 所以本线的首要产出是**把成败押在编译定理上**: 要么写出一个候选的值证明, 要么写出它到不了的定理. 不要再用 "读法" 推进.

## 0 固定不动的

1. **AGENTS.md 的四条纲领**, 含作者对第 1 条的解释: 中间层不直接用布劳威尔树时须有内部 View; ℕ-极限的相邻项按目标树自己的合法性步进, 即字面第一位置.
2. **终点:**
   - 一个 `Cd` 闭项 T (`OCF.Lean.CRwBase.Cd`, 只有 `hz`, `hs`, `hl`), 通过检查器, 有 FGH;
   - 定理 `TerminalFoldAccept.reference ≤ᵛ T`, 无条件;
   - T 与其证书的导入闭包无记号模块.
3. **乙线的前提:** 层号与层号之间的序由树给出, 不用自写的码或任何有限项序.

其余 AGENTS 的最佳实践照旧遵守, 但下面 §5 的进度判据优先.

## 1 你接手时的事实 (都核对过)

### 1.1 为什么难 (三路独立审查的共识, 判断, 各有定理)

- **W, 比较:**
  - 折叠在 Ω-结点处要比较 "目标层对结点层". 层号含 Ω-共尾元时, 这个比较没有字面公共上界.
  - 定理: `Barrier.barrier : Ω-Extension → LPO`, 以及约 25 条影子 (`dec→WLPO`, `upd→wdec`, `pos-dec→LPO`, `no-wash` 等).
  - 后果: 比较只能沿字面位置做, 输出回灌要带位置证据. 世界、可入、拷贝这些机制都由此而来.
- **V, 值:**
  - 折叠不是值的函数: `Value.ψ⁰-not-cong : Ω₁ ≈ᵛ Ω₁′ × ¬ (ψ⁰ Ω₁ ≼ ψ⁰ Ω₁′)`. 同族约 20 条, 包括 `TpPort2Tab.no-valmonoT⁺`.
  - 后果: 没有一般的单调引理, 值证明只能沿真实轨道模拟.
  - **从来没有一路把值证明对阶段参数化, 也没有一路写过把记号项整体解释进树侧的 ι.** 这是 "每站从头来" 的直接原因.
- **C, 坍缩:**
  - 高层信息被送进固定类型或有损读回: `SkelDxGen.fac-*`, `er-drop`, `leg-const`, `slot-zero`, `toD₁`.
  - 这是自我施加的类型决定, 不是定理.
- **主审的设计判断 (RR3-Design §2.4, 无定理):** 在写法 A 下 ψ 只能是部分函数, 证据要对 ψ 封闭. 对 ψ 封闭且能回答一切派发的证据类型, 可能就是一个可判定全序, 也就是一个记号. 这是乙线最大的风险, 也是 §2 的 O7 要用定理回答的问题.

### 1.2 值前沿

- 树侧无条件的最高值定理: `EmbVVInstO2.vv-ω²`, ψ₀(Ω_{Ω·ω²}). 它属于封存的带高度族, 自 11-04 未动.
- 其它值定理:
  - `BTBOFull.BTBO≈`: ψ₀(Ω_Ω);
  - `SumOneAccept.step-T₁`: 严格高于 ψ₀(Ω_Ω);
  - `TotalValueHighOmega.omega-lower`: ψ₀(Ω_Ω)+ω ≤ `RadicalValueNativeFinal.closed`.
- **严格越过前沿一个后继的闭项 (2026-11-08 主审核对补入):** `CrossMHighSeedAccept.labelled-strict-lower`. 内容: 存在 R, 使 `Lab R tω²` 且 `suc R ≼ T⊤ᶜ ω²ᶜ`. 即封存的 CrossM 闭项以 ω²ᶜ 为起点的实例严格高于 ψ₀(Ω_{Ω·ω²}) 那一行. 这是旧定理的串接, 只多一个后继, 所以 P1 的 x 仍是 Ω·ω².
- **树侧改写的同值闭项:** `TreeEmitBuildAccept.closed-value : VV closed tω²`. EmbVV 实例的保值改写, 与 ψ₀(Ω_{Ω·ω²}) 双向同值; 定义与证书的导入闭包无记号; 依赖切片比原来多 132 行.
- `VV X t` 的意思是: 存在 Y, 使 `Lab Y t`, `X ≼ Y`, `Y ≼ X` (`ValLabPos`). 即与带标签的参照树互相 ≼.
- 其余一切闭项的 "读法" 都是判断, 不算数. 例如 `RecB.Tω` 的 ψ₀(Ω_{Ω·ω}), `DiagK` 的 `Tdg₂` 的 ψ₀(Ω_{Ω₃}), 原起点 `CrossMClosed.T⊤` 的 ψ₀(Ω_{Ω²}).
- **堆:** `EmbVVInstO2`, `TreeEmitBuildAccept`, `CrossMHighSeedAccept` 即使接口已是最新, 6G 也载不进来 (退出码 251), 14G 退出 0 (主审 2026-11-08 实测). 导入它们的文件要单路用大堆, 并且此时别的路不编译.

### 1.3 终点的最省证明形状 (实验, 主审复现, 退出码 0)

RR3-Backward 的实验. 它原在会话的 scratch 目录, 下面是全文. 你要用它, 就放进你自己的新文件:

```agda
{-# OPTIONS --safe --without-K --cubical-compatible --guardedness --hidden-argument-puns #-}
module RR3BackwardCover where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.CRwBase using (Cd; hz; hs; hl)
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; l≤)
open import OCF.Lean.NegFold1Base using (≤ᵛ-trans)
open import OCF.Align.EboLeanDef using (T; cof; pred; fsn; HC; h0; h1; hω; c1; cω; EBOψ)
import OCF.Align.EboLean3Tree as E
open import OCF.Align.TerminalFoldAccept using (read; reference; all-branches)

module Cover
  (ι     : T → Cd)
  (ι-suc : ∀ t → cof t ≡ c1 → hs (ι (pred t)) ≤ᵛ ι t)
  (ι-lim : ∀ t → cof t ≡ cω → ∀ n → ι (fsn t n) ≤ᵛ ι t)
  where

  cover : ∀ {t} (h : HC t) → read (E.tree h) ≤ᵛ ι t
  cover (h0 _)       = z≤
  cover {t} (h1 e h) = ≤ᵛ-trans (s≤s (cover h)) (ι-suc t e)
  cover {t} (hω e h) = l≤ (λ n → ≤ᵛ-trans (cover (h n)) (ι-lim t e n))

  terminal : ∀ {X : Cd} → (∀ k → ι (EBOψ k) ≤ᵛ X) → reference ≤ᵛ X
  terminal up = all-branches (λ k → ≤ᵛ-trans (cover (E.hc-tower k)) (up k))
```

这段的意思: 终点下界等于下面三件事.

1. 一个值忠实的解释 ι : 记号项 → `Cd`;
2. 两条一步不等式 `ι-suc`, `ι-lim`;
3. 对一切 k 有 `ι (EBOψ k) ≤ᵛ T`.

它不需要记号的良基与封闭. ι 读记号, 所以只能放第 4 层 (验收文件), 不进成品, 这不违反纲领 4.

难点全在 ι 与 `ι-lim`: 规则 6 的 γ-链要求树侧折叠在 ι 的像上 "链支配" (RR3-Backward §3.3). 只有两种出路:

- 链逐项相等: 那是 Lab, 也就是翻译 (`AccTreeLab.Lab≅tree`);
- 受限的值单调: 只在 ι 的像 (生成域) 上单调.

不受限的单调已被否定 (`ψ⁰-not-cong`, `no-valmonoT⁺`).

### 1.4 现有的三个候选 (都有合法闭项, 都没有接近 EBO 的值定理)

| 候选 | 位置 | 已有 | 缺 |
|---|---|---|---|
| 归纳-递归层号 | `OCF/Align/LevelFix*`, `LevelNoK*`, `NoKCert*` | `LF` 含到 Λ 的一切层号, `LevelFixVal.Legal-Ω̂`, `Legal-Λ`; `LevelNoK` 去掉了 `Un`; 无参数闭项 `LevelNoKFold.ψ₀Λ : T⁰ 0` | `ψ₀Λ` 是带待计值符号的数据树, 不是序数; 读回 `feed` 的合法性没有定理; 封存障碍 `NoKCertNeg.no-HS→Lgl : (∀ y → HS y → Lgl LF.zero (rdR LF.zero y)) → ⊥`. 封存记录 (RouteSeal §5) 自写重开第一步: 把 `LF` 的折叠换成差树和的作用 |
| 改值候选 | `OCF/Align/RadicalValueNativeFinal`, 证明入口 `TotalValue` (98 件) | 带字面第一位置 View 与 FGH; ψ₀(Ω_Ω)+ω ≤ closed; 内部 rowB 与 BTBO 同值; 参数 1 的跨层回收 | 任意参数 η 的跨层回收; 准确值; 对象类型是 `Σ Cd LgB`, 可能装不下 ι 的像 (RR3-Backward 的担心) |
| 差树高度回灌 | `OCF/Align/HtFeedClosed.TΛ` 一族 (`HtOut` 等) | 合法闭项, FGH, 高度由输出生成 | 值定理为零; 类型封顶在 `Ht` (SkeletonAudit §1.3, 判断 ψ₀(Ω_{Ω₃}) 量级) |

封存的带高度族 (`EmbVV`, `LadderOrd`, `CrossM`) 是值前沿所在, 但翻译最重. 作者已选入本线 (§2 的 O4), 只作 O1 接口的实例; `LevelFix`/`LevelNoK` 也随 O3 解封. 两处解封只限本线的工作项, 不重开封存族的攀爬.

## 2 本线的工作项

> **作者选定的范围 (2026-11-08):** 下列六项全部纳入: O1, O7, O3, O8, O5, O4. 没有列在这里的不要做.
>
> **建议的顺序 (主审判断, 可调整, 调整要说明理由):**
> 1. 先交 P7 的前沿表.
> 2. O1 与 O7 并行. 两者文件不相交; O1 的结果决定 O3, O5, O4 值不值得深做.
> 3. O8 (两天封顶) 与 O3 的第一个里程碑.
> 4. O5 与 O4 都作为 O1 接口的实例来做, 不独立攀爬.
>
> **作者另定:** 1513 行只作成本参照. 汇报时要报行数, 但不以它取舍路线, 也不以 "逼近标杆" 为由停交闭项.

**O1. 阶段无关的值接口 (诊断).**

- 内容:
  - 以 §1.3 的 `Cover` 为模板, 在第 4 层写记录 `ChainDom`: 树侧折叠在 ι 的像上的链支配, 律里每对坐标带字面公共上界证据.
  - 对 §1.4 的每个候选写 `ChainDom → reference ≤ᵛ T` 的条件定理.
- 交付:
  - 写得出的候选: 条件定理, 加 ι 的定义.
  - 写不出的候选: 失败点的编译错误原文, 加一条说明它是哪种封顶.
- 预计: 约一周.
- 早期信号: ι 的像类型要随 k 改变; 需要 Funext, UIP 或 `Un`; 律要对裸坐标量化.

**O7. 写法 A 的否定定理.**

- 目标: 把 "写法 A 下 ψ 不能是全函数" 写成定理. 形状 (RR3-Design §4 第 6 步): 在 `T (Ω+1)` 上满足 BTBO 三路等式 (留 / 同层 / 在上) 的全函数 ψ ⟹ WLPO, 与 `Stage2.dec→WLPO` 共用开关序列.
- 更进一步 (若可行): "对 ψ 封闭并能回答一切派发的证据类型, 在 Λ 之下给出可判定全序".
- 结果的用法:
  - 成立: 乙线的证据维护有了定量依据.
  - 不成立: 给出证据类型必须满足的最弱条件.

**O3. LevelFix 接差树的合法性 (首选构造候选).**

- 里程碑:
  1. `Lgl-from-shape : ∀ y → <差树形状> → Lgl k (rd y)`, 替换 `no-HS→Lgl` 的前提.
  2. 把 `LevelNoKFold.ψ₀Λ` 计值到 `Cd` 并给 View.
  3. 写 ι_L : 记号项 → `LF`, 先只证 ι_L 与 Ω̂ 的塔的关系.
  4. 写 O1 的条件定理.
- 先读 `LevelFixNeg` 的 `no-Lgl-Ωlim`, `no-cp-Ω3-Ω2`: 它们划了两条边.
- 早期信号: 里程碑 1 需要 UIP 或 `Un` 回来; 里程碑 3 需要对 `Raw k` 的裸相等判定.

**O5. 改值候选的参数化.**

- 内容: 把 `TotalValue` 的 `Cumulative`/`Embedding` 一组证明对 HtB 或行号参数化, 使 ω² 端行成为同一定理的实例. 先把 "任意 η 的跨层回收" 写成接口记录, 再填, 不先填参数 2.
- 早期信号: 推广需要按 η 的形状另写一段.

**O4. 带高度族作值基座.**

- 内容: 把 `CrossMClosed.T⊤` 的读法 ψ₀(Ω_{Ω²}) 变成定理或反例, 用 `EmbVVMain.V-≃` 证上下界. 若做, 作为 O1 接口的第一个实例, 不独立攀爬.

**O8. 差树 SumOne 的上界.**

- 内容: 证 `SumOne.T₁` ≤ ψ₀(Ω_{Ω+1}) 的参照. 一路, 两天, 做不出就如实停.

## 3 不要做的

- 甲线 (码作层号): 不归本线.
- 继续 C 线 (`RecB`, `Third`, 第三种组织): 三路都不推荐. 只在 O1 对它们写得出条件定理时才重开.
- 没有值下界的新闭项; 以 1513 为目标的压缩; 以读法命名的站.
- 在裸下标上写世界更新或比较律. W 族已有 25 条, 不要再证一遍.
- 把高层信息送进固定类型再折叠 (障碍 C).
- 从低站重算基线. 新解释器或新候选先说明它与 ψ₀(Ω_{Ω·ω²}) 前沿的关系.
- 不改 `src/`, `archive/`, 不改任何已有 probes 文件的结论; 新文件另起前缀.

## 4 规则

- **选项:** `--safe --without-K`, 可加 `--lossy-unification`. 无 postulate、洞、停机或正性编译指示、trustMe. 不开 K.
- **Funext 与 UIP** 只准作前提, 结论标 "条件", 不进成品与证书.
- **编译:** 从仓库根 `agda --library-file=<库文件> -i src -i probes <文件> +RTS -M6G -RTS`.
  - 库文件写两行, 分别是 stdlib 与 cubical 的 `.agda-lib` 路径. 本机在 Homebrew 的 `agda/2.8.0.2_2/share/agda/` 下.
  - `~/.agda/libraries` 已过期, 不要用.
  - 仓库外的实验文件要自己写上 `--cubical-compatible --guardedness --hidden-argument-puns`.
- **退出码不经管道:** 0 通过, 42 类型错误或有洞, 251 堆耗尽 (不是类型错误, 也不是通过), 124 超时.
- 同时只跑一个 agda. 删 `.agdai` 只删自己模块的, 写字面路径. 不用 `--ignore-interfaces`.
- 堆墙多出在比较具体闭项处: 陈述逐字写; 大参照树放 `opaque`; 隐式参数显式写出. 见 `EBOHandbook.md` §4.
- **文章:** 中文 literate `.lagda.md`, 代码、讲解、结论交织, 不写 FINDINGS 文件.
- **结论的写法:**
  - 区分定理、有限测试、判断;
  - 否定路线要有编译定理, 否则只写 "未走通" 或 "暂停";
  - 否定与条件定理的每个前提给实例;
  - 穷尽是判断;
  - "自然", "只差" 一类词不进结论.
- **强度:** 写 ψ₀(Ω_x), x 用 Ω 的算术, 不用 ψ₁.
- **Git:** 不提交, 不推送, 除非作者要求.

## 5 进度判据 (本线优先于 AGENTS 的最佳实践)

> **作者选定的判据 (2026-11-08):** 下列 P1 到 P9 全部施加. 它们与 AGENTS 最佳实践冲突时, 以这里为准, 并在汇报里写明冲突在哪.

- **P1 值前沿数.** 每轮汇报一个数: 使 "ψ₀(Ω_x) ≼ 候选" 成为无条件编译定理的最大 x. 当前 x = Ω·ω². 结构性工作 (O1, O7) 不受这一条约束.
- **P2 阶段无关.** 站 k+1 的值定理须是站 k 的实例, 每升一站不新增证明模块.
- **P3 交付门槛.** 新闭项必须与它不低于前沿的值下界同一路交付. 缺后者不算交付. (主审补充, 作者未定:) 写不出值下界时, 交出写不出的编译事实, 也算交付.
- **P7 接手先交前沿表.** 开工前先交一张 "当前值前沿与最高闭项" 表, 作者核对后再动手.
- **其它 (RouteReview3 §3):**
  - P4: 接口定稿前过封顶清单;
  - P5: 同族第 3 条以上的否定不再派路;
  - P6: 跨结构估计乘 3;
  - P8: 同对象并行不超过两路;
  - P9: 有限测试不作读法上升的依据.

## 6 必读与入口

1. `AGENTS.md` (纲领与规则).
2. [RouteReview3](RouteReview3.md), 以及三份原报告 [RR3-Design](RR3-Design.md), [RR3-Evidence](RR3-Evidence.md), [RR3-Backward](RR3-Backward.md).
3. `probes/README.md` (当前状态), `probes/RESULTS.md` (成果与否定的范围), `Survey/ResearchHistory.md` (为什么走到今天).
4. 按工作项:
   - O1: `TerminalFoldAccept`, `EboLean3Tree`, `EboLeanDef`, `Fold1If`;
   - O3: `LevelFix.lagda.md` 与 `LevelNoK.lagda.md` 的文件头, `RouteSeal.md` §5, `NoKCertNeg`;
   - O5: `TotalValue.lagda.md`, `EBOEndgame.lagda.md` §13;
   - O7: `Barrier.lagda.md`, `Stage2` 的 `dec→WLPO`;
   - O4: `EmbVVMain`, `EmbVVInstO2`, `CrossMClosed`, `RouteSeal.md` §1.
5. `Survey/EBOHandbook.md`: 工程坑 (§4) 与反复出错的模式.

## 7 汇报

中文. 先说对终点意味着什么, 再给定理. 每条结论标档. 列出文件、编译命令与退出码、禁用构造检查. 第一次出现的内部名字配一句白话.
