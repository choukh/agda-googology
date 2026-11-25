# 交接: 以甲为脚手架完成乙 (2026-11-08)

> 给接手的模型. 本文自足: 读完它和 §8 列的文件就能开工. 背景见 [RouteReview3](RouteReview3.md), 特别是 §2 写法 A/B、§5.5 乙线五轮的结果、§5.6 作者的决定.
>
> 本文取代 [Handoff-TreeLevels](Handoff-TreeLevels-2026-11-08.md). 那条线在第五轮暂停于 LevelNoK 实际种子第 0 支到第 1 支的 `Cp`, 候选未关闭; 它的结果保留, 不再投入.

## 0 作者的决定 (原话)

- "不接受最终结果为甲线, 但可以接受接受甲线的指引或启发后完成乙线."
- "记号只允许作为启发, 最终形状必须遵循树的语言, 不能留翻译痕迹."

术语:

- **甲:** 层号用有限项 (码) 及其全序, 树族沿码序的 Acc 递归.
- **乙:** 层号本身是布劳威尔树, 比较只用树上的字面位置, 最终定义里没有任何有限项的序.

**甲只能作脚手架和启发, 只出现在第 4 层与探路文件里. 成品必须是乙, 并通过 §3 的清单.**

## 1 固定不动的

1. **AGENTS.md 的四条纲领**, 含作者对第 1 条的解释: 中间层不直接用布劳威尔树时须有内部 View; ℕ-极限的相邻项按目标树自己的合法性步进, 即字面第一位置.
2. **终点:**
   - 一个 `Cd` 闭项 T (`OCF.Lean.CRwBase.Cd`), 通过检查器, 有 FGH;
   - 无条件定理 `TerminalFoldAccept.reference ≤ᵛ T`;
   - T、它的证书与 View 的导入闭包无记号模块.
3. **乙的前提:** 成品里层号是树, 比较是树的字面位置. 不出现自写或导入的码及其序.

## 2 计划

只有 S5 的产物算成品. S1 到 S3 是到达 S5 的手段.

### S1 甲脚手架 (第 4 层, 不进成品)

**内容.** 按 RR3-Design §2.3 与 §4 的写法 B, 做出码作层号的完整构造, 到 ψ₀Λ 闭项 T甲, 并证明 `reference ≤ᵛ` T甲 (经 `Cover` 或直接).

- 码与良基可以直接导入记号侧: `EboLeanDef` 的项 `T` 与 `fsn`, `EboLean3Omega.wf : NF t → Acc′ t`, `EboLean3Cmp` 的比较. 这是脚手架, 不必拷贝.
- 层号取 (码, 树) 对, Ω 对树递归. 先例是 `LevelFixVal.Ω̂` 的三行.
- 树族沿 Acc 递归, ψ 照 BTBO 的四行, 在 Ω-结点处按码比较三路派发. 类型骨架见 §6.2 的实验 `RR3AccIdx`.

**交付.** T甲 的定义、FGH、`reference ≤ᵛ` T甲. 另附一份清单: 在 T甲 的运行中, ψ 在 Ω-结点处实际做了哪些码比较 (j 对 i, 及它们所在的层 ℓ). 这份清单是 S2 的输入.

**早期信号.**

- 码树配对在 Acc 搬运处需要 UIP (`LevelFix.Un` 的翻版);
- 链点码的标准形封闭接不上 `EboLean3` 的封闭定理;
- 沿 Acc 展开具体闭项撑爆堆.

出现其中任何一项, 先报告.

### S2 实现定理 (关键的一步)

**问题.** 甲的运行中用到的每一次码比较 cmp(j, i), 能否由树上的字面位置在公共上界下实现?

**依据 (判断).** ψ_i 处理层 ℓ 的结点 Ω_j 时, j 与 i 都在 ℓ 之下, 所以 ℓ 的树就是它们的字面公共上界. 若 j、i 的树都是 ℓ 的树里的字面位置 (`⊲[w]`, `CRwBase`), 比较就是 `cmpB` 在公共上界下的比较, 不撞 `Barrier.barrier`.

**交付二选一:**

- **(a) 正面:** 定理: 对 T甲 运行中出现的一切 (ℓ, j, i), 存在树上的位置证据与合法世界, 使 `cmpB` 的结果与码比较一致. 并说明这些证据如何随 ψ 的输出与回灌一起生成, 不在事后计算.
- **(b) 否定:** 编译反例, 指出某个实际出现的 (ℓ, j, i) 上, 位置证据跟不上码的序. 写清只否定什么. 这是 RR3-Design §2.4 的判断在合法公共界之下的第一个定理, 有独立价值.

**早期信号.**

- 位置要穿过 Ω-结点的分支坐标, 那里要求坐标在世界的界之下. 这是以前世界墙与拷贝墙出现的地方: `upd→wdec`, `CohWNeg.no-cross`, `no-wmatch`.
- 律若要对裸坐标量化, 就会重证 W 族, 停下.

### S3 抹掉码

**内容.** 把甲的派发换成 S2 (a) 的位置证据, 删掉码. 层号是树, 比较是 `cmpB` 一类的字面位置比较.

**交付.** 合法闭项 T₃、FGH、内部 View; 导入闭包无记号.

**S3 的核心任务 (2026-11-09 补记, 来自 S1 第四轮的卡点).** 在甲里, 奇异 Ω-结点 (如 Ω_Ω) 的分支若对原始树 y 定义, 就要输出以 y 为层号的 Ω_y, 而甲的层号是码, 原始树没有码 (`JiaExactIndex.root-index`, `successor-point`). 所以作者定: 脚手架里奇异结点的分支对码定义 (与记号的基本列一致), 正规结点仍对原始树定义. S3 必须把这一处换成乙的写法: 奇异分支对低层合法树定义, 层号由树本身给出, Ω_c 对树 c 按结构递归构造 (先例 `LevelFixVal.Ω̂`). 这正是 "层号是树" 的实质所在, S2 的实现定理也要覆盖这些结点.

**要求.** 合法性随构造给出 (像 `CRw` 的 `Sh-Φ`). 不要 "先运行, 再事后证明输出合法". 乙线第五轮正是卡在这里: 对实际闭项展开到 180 秒超时.

### S5 去除翻译痕迹 (成品)

**内容.** 以 S3 为起点, 按树的语言简化或重写. 把每一处照着甲或记号写下的结构, 换成由树自身要求推出的写法. 换不掉的, 交编译定理说明它是必需的.

**交付.** 成品闭项 T乙, 通过 §3 的七条清单, 逐条给出证据.

### S4 对最终形状证值

**内容.** 证 `reference ≤ᵛ` T乙. 两条路都可以:

- 经 T乙 ≥ T甲 的逐结点模拟 (两边都是树), 再接 S1;
- 直接用 `Cover` (§6.1).

**要求.** 若 S5 的改写使模拟失效, 宁可重证, 也不为保住证明而保留翻译形状. 值证明只放第 4 层, 可以读记号.

### 2026-11-09 更新: S1 结束, 直接进 S3 (作者选定)

**S1 停在第五轮.** 两轮卡点 (`JiaExactIndex`, `JiaRound5`) 合起来说明 (判断): 只要 ψ 在奇异结点的链上要用码, 码就会顺着分支传到正规结点的原始分支里. 所以脚手架要么全部分支对码 (完整翻译, 与 `EboLean3`/`DirectClosed` 的参照树同类, 对 S2 没有用), 要么 ψ 不用码 (即乙). S1 剩下能给的 T甲 ≥ EBO 与比较清单, 记号侧已有 (`EboLean3`, `DirectClosed`, `EboLeanDef.fsnc`).

**S1 交出、作为 S3 模板的东西:**

- `JiaExactFold` 的逐项 ψ 规则与 `JiaExactRep.Sound.ψ-rep` (种子合同下逐项保持对应);
- `JiaExactSeeds` 的种子合同 `SeedSpec`;
- `JiaMixedOmega` 的全部有限层 Ω 种子;
- `JiaExactIndex` 对奇异层的定位;
- `JiaRound4` 与 `JiaRound5` 的逐条翻译账.

**新的顺序:** S3 (并入 S2) → S5 → S4. 见下面 "S3 的执行要点".

### S3 的执行要点 (2026-11-09)

1. **层号是树, 且合法.** 层号的类型要对 x ↦ Ω_x 封闭到 Λ, Ω_c 对树 c 按结构递归 (先例 `LevelFixVal.Ω̂`, `Legal-Ω̂`, `Legal-Λ`). 派发比较要在公共上界下进行 (`cmpB` 要合法的界), 所以层号必须合法.
2. **派发用树上的位置.** ψ 处理层 ℓ 的结点 Ω_j、目标 i 时, j 与 i 都是 ℓ 之下的字面位置, 比较用 `cmpB` 一类以 ℓ 为公共上界的比较. 这就是原来 S2 要证的实现, 现在直接在定义里实现.
3. **规则照 S1 的模板.** 零、后继、ℕ-极限、三路比较与 γ-链的写法照 `JiaExactFold`. 每一处照搬的形状照常记翻译账, 留给 S5.
4. **合法性随构造给出.** ψ 的输出 (回灌作层号、作链点) 必须带着合法性与位置证据一起产生. 不要先运行再事后检查: 乙线第五轮在这里展开超时.
5. **阶段无关.** 定义与合法性定理一次覆盖一切层 (P2), 不按站推进. 中间可以用低层的闭项作测试, 但测试不作交付, 也不受 P3 约束; P3 只管成品闭项.
6. **值证明的准备.** 写 ι : 记号项 → 乙树, 对应关系仿 `JiaRep` 的 `Rep`, 供 S4 的 `Cover` 使用.
7. **已知的墙 (都是定理, 先读):**
   - 裸下标上的世界更新推出判定 (`DiagKLev.upd→wdec`, `CohWUpd.upd→wdec`);
   - 拷贝墙 (`CohWNeg` 的 `no-cross→`, `no-cross←`, `no-route`; `HtTowerNStage.no-wmatch`);
   - 坐标不能收缩自身高度 (`HtTowerNeg.no-retract`);
   - 回灌必须合法化 (`NegLHRecIf` 的 `fb-must-legalize`);
   - 留下结点带回灌时单调的下层规则对不上 (`NegThirdPre.keep-req`, `no-lower-rule`).

   S3 若撞上其中任何一堵, 停下报告, 并说明撞的是哪一条的前提.
8. **停止条件:** 需要 UIP 或 Funext; 需要在裸下标上量化的律; 需要把高层信息送进固定类型; 需要改纲领之外的约束. 遇到任何一条, 停下报告.

### 2026-11-10 更新: 第四次审查之后的做法

S3 的旧做法 (在一切合法树上求封闭, 逐轮补正则性形状) 已停. [第四次路线审查](RR4-Fable52.md) 之后的方向是 "读回域上携带证据, 链严格增长". 现状, 逐轮表与评估见 [RouteReview3](RouteReview3.md) §5.10, §5.11 与 [复盘](Retro-2026-11-10.md). 接手时注意:

1. **量化域.** 封闭与保持定理先对带证据的读回域陈述 (规范塔 `tw n`, `Ω̂` 的带 `LglB` 的坐标的读回), 不对 "一切合法树". 新接口先在规范实例 (tw 0 到 tw 3, Ω̂ 2) 上实填.
2. **共用接口.** `YiCarry` (V1) 与 `YiCarryPlus` 已定稿, 只增不改. `Carry⁺` 对全塔与 Λ 成立 (`tower-carry⁺`, `limit-carry⁺`). `YiCarry.K2′` 不可满足 (`no-K2′`), 用 `K2′⁺`.
3. **折叠.** gt 行的链用加法增长 (作者 D10: 算树侧候选, 记翻译账). 已有的只是目标层 0, Ω 结点层号为 0 的具体输入族.
4. **已知的新障碍.** 读证书的 ψ 要求输出与证书无关, 直到函数相等 (`certificate-coherence-required`); 只读树的 ψ 在有 Funext 时推出 WLPO (`funext-fold-tree→wlpo`). 处理办法待作者定 (复盘 D11). 上面 "停止条件" 里的 "需要 UIP 或 Funext 就停下报告" 仍然有效.
5. **记录.** 首页 README 只替换 "当前阶段" 一段, 过程记 LOG; 仓库文件里不写临时目录的路径.

### 顺序与停点

- **顺序:** S1 → S2 → S3 → S5 → S4. S4 的部分工作 (`Cover` 的接线) 可以与 S1 并行.
- **S2 若是 (b):** 停下报告, 交作者定. 不要自行改换方案.
- **任一步若必须修改已有定义或纲领之外的约束:** 停下报告.

## 3 "没有翻译痕迹" 的验收清单 (作者确认)

1. **字段审计:** 成品的每个构造子与字段, 都对应一条树侧理由: 合法性、壁垒定理、或编译过的否定定理. 读自记号基本列规则 (EBO 的规则 1 到 6, `EboLeanDef.fsnc`) 的字段数为零. 翻译账逐字段列出.
2. **没有专属前提:** 闭包定理与合法性定理对一切层一条, 不按阶段或按规则增加前提.
3. **验收只用序数值:** 不用 Lab, 不要求基本列与记号一致.
4. **导入闭包无记号:** 用 `probes/Survey/scripts/importclosure.py`, 并以 `agda --dependency-graph` 核对.
5. **不按记号的语法分情况:** 定义里没有按记号项形状 (0, +, ψ_u, Ω_u 一类) 的分情况. 分情况只按树的构造子 (零, 后继, ℕ-极限, Ω-极限) 与树上的位置关系.
6. **树有自己的基本列:** 至少一处编译定理, 说明成品的基本列与记号不同而序数值相同. 先例: `same-M₂` 与 `no-lab-M₂` (见 `OrdLab`, `OrdLabReadTop`, `ValLab`).
7. **简化可测:** S5 的成品比 S3 短, 并给出逐件对照, 说明删掉或合并了哪些结构. 行数只作参照, 但不能比 S3 长.

**去不掉的痕迹 (作者确认):** 若有编译定理说明某一处形状是必需的, 它就算 "由树侧要求逼出", 可以合法保留, 并按第 1 条记账.

## 4 进度判据

- **P1 值前沿数:** 每轮报告乙线成品 (S3 起) 上使 "ψ₀(Ω_x) ≼ 候选" 成为无条件编译定理的最大 x. 当前全仓库是 x = Ω·ω² (`EmbVVInstO2.vv-ω²`). S1 的 T甲 是脚手架, 它的值定理单列, 不计入 P1.
- **P2 阶段无关:** 值定理与合法性定理对一切层一条, 每升一站不新增证明模块.
- **P3 交付门槛:** 新闭项与它的值下界同一路交付. 写不出值下界时, 交写不出的编译事实, 也算交付.
- **P5:** 同族第 3 条以上的否定不再派路. 特别是不要再证 W 族 (裸下标比较 ⇒ LPO/WLPO), 已有约 26 条.
- **P6:** 跨结构的估计乘 3.
- **P8:** 同对象并行不超过两路.
- **P9:** 有限测试 (结点数、展开深度) 不作读法或机制相同的依据. `Fab6` 是前车之鉴: 深度 4 的结点数相同, 机制却不同.
- **1513 行:** 只作成本参照.

## 5 不要做的

- 把甲 (码作层号) 交作成品, 或在成品里留码与码的序.
- 继续乙线旧候选的事后合法性检查 (LevelNoK 的 `Cp`, `Shape`); 继续 C 线 (`RecB`, `Third`).
- 在裸下标上写世界更新或比较律.
- 把高层信息送进固定类型再折叠 (`Ht`, 固定的 `HB S₀`).
- 从低站重算基线. 新构造先说明它与 ψ₀(Ω_{Ω·ω²}) 前沿的关系.
- 改 `src/`, `archive/`, 或已有 probes 文件的结论. 新文件另起前缀: `Jia*` (S1, S2 的甲脚手架) 与 `Yi*` (S3 起的乙成品). (2026-11-08 更正: 原建议的 `Scaf*` 与 11-03 的标签阶梯族 `ScafLadder*` 等 70 余个文件同前缀, `TreeL*` 与 `TreeLevels*`, `TreeLang*` 同前缀, 都会混淆统计与检索. 第一轮已建的 `Scaf{Base,Fold,AuditClosure,Chain,ChainTower,Round1}` 请改名为 `Jia*`, 连同导入与 README、LOG 的链接一起改.)

## 6 可直接用的代码

两段都来自 RR3 审查的 scratch 实验 (不在仓库里), 主审复现过. 要用就放进你自己的新文件.

### 6.1 终点下界的最省形状 `Cover` (退出码 0)

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

仓库里已有同一形状的版本: `OCF/Align/TreeLevelsO1Cover` (`Cover.terminal`, `Generated.terminal`), 以及 `TreeLevelsO1Chain` 的 `ChainDom`. 可以直接导入.

### 6.2 写法 B 的类型骨架 `RR3AccIdx` (退出码 0; 码是玩具)

```agda
{-# OPTIONS --safe --without-K --cubical-compatible --guardedness --hidden-argument-puns #-}
module RR3AccIdx where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

data Code : Set where
  z : Code
  s : Code → Code

data Ordering : Set where
  lt eq gt : Ordering

cmpC : Code → Code → Ordering
cmpC z z = eq
cmpC z (s _) = lt
cmpC (s _) z = gt
cmpC (s a) (s b) = cmpC a b

cmp-eq : ∀ a b → cmpC a b ≡ eq → a ≡ b
cmp-eq z z _ = refl
cmp-eq (s a) (s b) e = cong s (cmp-eq a b e)

_<ᶜ_ : Code → Code → Set
a <ᶜ b = cmpC a b ≡ lt

data Acc (c : Code) : Set where
  acc : (∀ {j} → j <ᶜ c → Acc j) → Acc c

module Layer (ℓ : Code) (Low : ∀ j → j <ᶜ ℓ → Set) where
  data T₊ : Set where
    zero : T₊
    suc  : T₊ → T₊
    lim  : (ℕ → T₊) → T₊
    limΩ : ∀ {j} (p : j <ᶜ ℓ) → (Low j p → T₊) → T₊

  natT : ℕ → T₊
  natT zero = zero
  natT (suc n) = suc (natT n)

  ω : T₊
  ω = lim natT

  lfp : (T₊ → T₊) → T₊
  lfp f = lim go where
    go : ℕ → T₊
    go zero = zero
    go (suc n) = f (go n)

  _+_ : T₊ → T₊ → T₊
  x + zero = x
  x + suc y = suc (x + y)
  x + lim f = lim (λ n → x + f n)
  x + limΩ p f = limΩ p (λ y → x + f y)

mapT : ∀ {ℓ Low Low′} → (∀ j p → Low′ j p → Low j p) → Layer.T₊ ℓ Low → Layer.T₊ ℓ Low′
mapT m Layer.zero = Layer.zero
mapT m (Layer.suc x) = Layer.suc (mapT m x)
mapT m (Layer.lim f) = Layer.lim (λ n → mapT m (f n))
mapT m (Layer.limΩ p f) = Layer.limΩ p (λ y → mapT m (f (m _ p y)))

T : ∀ c → Acc c → Set
Low : ∀ c → Acc c → ∀ j → j <ᶜ c → Set
T c a = Layer.T₊ c (Low c a)
Low c (acc h) j p = T j (h p)

coe : ∀ {c} (a a′ : Acc c) → T c a → T c a′
coe (acc h) (acc h′) = mapT (λ j p → coe (h′ p) (h p))

iter : ∀ {A : Set} → (A → A) → A → ℕ → A
iter f x zero = x
iter f x (suc n) = f (iter f x n)

ψ : ∀ {ℓ i} (aℓ : Acc ℓ) (ai : Acc i) → T ℓ aℓ → T i ai
ψ {ℓ} {i} (acc h) (acc hi) = go where
  open Layer i (Low i (acc hi)) using (ω; lfp; _+_)
  go : T ℓ (acc h) → T i (acc hi)
  go Layer.zero = ω
  go (Layer.suc x) = lfp (λ y → go x + y)
  go (Layer.lim f) = Layer.lim (λ n → go (f n))
  go (Layer.limΩ {j} p f) with cmpC j i in e
  ... | lt = Layer.limΩ e (λ y → go (f (coe (hi e) (h p) y)))
  ... | gt = Layer.lim (λ n → go (f (iter (λ γ → ψ (acc h) (h p) (f γ)) Layer.zero n)))
  ... | eq with cmp-eq j i e
  ...   | refl = lfp (λ y → go (f (coe (acc hi) (h p) y)))
```

骨架的局限:

- 码是玩具, 层号的 Ω 用 ω 占位, 没有回灌.
- ψ 的几行是示意, 不是 EBO 规则的精确实现. S1 要按 BTBO (`src/OCF/BTBO.lagda.md`) 与 EBO 的规则写对.
- 实验 1 (`RR3NegPos`, 退出码 42) 说明: 分支类型不能取同族的低层, 必须先于本层定义, 所以要用 `Layer` 的参数化写法.

## 7 已知事实与教训

- **值前沿:**
  - 树侧无条件的最高是 `EmbVVInstO2.vv-ω²`, ψ₀(Ω_{Ω·ω²});
  - `CrossMHighSeedAccept.labelled-strict-lower` 严格越过它一个后继;
  - `TreeEmitBuildAccept.closed-value` 与它同值.
- **三个障碍 (RouteReview3 §1.2):**
  - W: 无公共上界的比较 (`Barrier.barrier` 与约 25 条影子);
  - V: 折叠不是值的函数 (`Value.ψ⁰-not-cong`, `no-valmonoT⁺`);
  - C: 坍缩到固定类型.
  S2 要正面面对 W; S4 要面对 V, 所以值证明必须沿结构走, 不靠一般单调.
- **乙线五轮 (RouteReview3 §5.5):** 事后检查实际闭项的合法性, 在第五轮展开超时. 所以合法性必须随构造给出.
- **有用的现成工具:**
  - `CRwBase` 的 `⊲[w]`, `cmpB` (公共上界下的比较);
  - `StallDxBdec.bdec` (公共界下判等可判定);
  - `LevelFixVal` 的 `Ω̂`, `Legal-Ω̂`, `Legal-Λ` (层号到 Λ 的树);
  - `TerminalFoldAccept` 的 `reference`, `all-branches`;
  - `EboLean3` 的良基与封闭.
- **堆:** `EmbVVInstO2`, `TreeEmitBuildAccept`, `CrossMHighSeedAccept` 即使接口最新, 6G 也载不进来, 14G 可以. 导入它们要单路大堆, 并且此时别的路不编译.

## 8 规则

- **选项:** `--safe --without-K`, 可加 `--lossy-unification`. 无 postulate、洞、停机或正性编译指示、trustMe. 不开 K. Funext 与 UIP 只准作前提, 结论标 "条件", 不进成品.
- **编译:** 从仓库根 `agda --library-file=<库文件> -i src -i probes <文件> +RTS -M6G -RTS`.
  - 库文件写两行: stdlib 与 cubical 的 `.agda-lib` 路径, 本机在 Homebrew 的 `agda/2.8.0.2_2/share/agda/` 下. 放仓库外.
  - 仓库外的实验文件自己写上 `--cubical-compatible --guardedness --hidden-argument-puns`.
  - 退出码不经管道: 0 通过, 42 类型错误或有洞, 251 堆耗尽, 124 超时.
  - 同时只跑一个 agda. 删 `.agdai` 只删自己模块的, 写字面路径; 不用 `--ignore-interfaces`.
- **仓库文件里不写本机绝对路径.** 粘贴编译器输出时, 把路径换成 `<实验目录>`, `<仓库>`.
- **文章:** 中文 literate `.lagda.md`, 不写 FINDINGS 文件.
- **结论:** 区分定理、有限测试、判断; 否定路线要有编译定理, 否则只写 "未走通" 或 "暂停"; 前提给实例; 穷尽是判断; 不用 "自然", "只差".
- **强度:** 写 ψ₀(Ω_x), x 用 Ω 的算术, 不用 ψ₁.
- **不提交, 不推送.**

## 9 必读

1. `AGENTS.md`.
2. [RouteReview3](RouteReview3.md) §1, §2 (O2), §5.5, §5.6; [RR3-Design](RR3-Design.md) 全文 (写法 A/B 的论证); [RR3-Backward](RR3-Backward.md) §3 (`Cover` 与链支配).
3. `src/OCF/BTBO.lagda.md` (ψ 的范本), `probes/OCF/Barrier.lagda.md`.
4. `probes/README.md`, `probes/RESULTS.md` (成果与否定的范围).
5. `Survey/EBOHandbook.md` §4 (工程坑).

## 10 汇报

中文. 每轮先写这一步交付的是哪一档 (正面、否定、卡点), 再给定理. 区分骨架、平凡实例与实质结果. 列出文件、编译命令与退出码、禁用构造检查. S3 起每轮报 P1 的 x.
