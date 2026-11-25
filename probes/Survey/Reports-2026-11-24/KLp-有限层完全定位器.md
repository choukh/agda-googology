# KLp：有限层上完全的层号定位器（构造一路，Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | high |
| 起止 (转录的时间戳，UTC) | 2026-11-25 03:08 至 03:12 |
| 工具调用 / agda 编译 (粗数) | 11 / 1 |
| token (usage 字段，按消息去重) | 输出 27470；新写入缓存的输入 108204；读缓存的输入 577392；其余输入 18 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `KLp` (在 `<实验目录>/m6p/`) |
| 主审复核后的一句结论 | 完成：pos : KLoc.PosStmt 编译，无前提，无模块参数；定位器 locF 的定义里不用任何证明作输入，cFin : CompleteFin locF；核心引理 limN（合法极限的第 n 项字面地含 sucⁿ zero）与副产品 lim-all（合法极限树的读回含一切有限层）。主审另目录冷编退出 0，禁用构造 0。附件 attachments/KLp-KLpFin.agda.txt、KLoc-KLoc.agda.txt、KLoc-简报-KLp.md |

## 简报原文

你的任务简报全文在这个文件里，请先完整读它，再严格照做（它是自足的，背景、任务、约束都在里面，其中第一步是读公共约束文件）：

<实验目录>/briefs/KLp.md

要点提示（以简报为准）：这是一个 Agda 形式化任务（--safe --without-K）。在已编译的接口 KLoc 上做构造一路：写一个层号定位器 locF（给两个层号 j、a，返回一条路径 j ≤ a 或者 nothing，定义里不用任何证明作输入），并证它在有限层上完全（CompleteFin locF：对一切 n 与一切第 0 层的树 z，只要 lvl n ≤ h₁ z 就找到），导出 pos : PosStmt。共享基目录是 scratchpad/w8（不是 w4），编译命令里的 -i 目录相应替换。只在你的工作目录 <实验目录>/m6p 里写，模块前缀 KLp；不改仓库、W4 与共享基目录里的任何文件；同时只跑一个 agda，堆上限 6G；不提交。无前提（不用函数外延，不加公设）；证不出时报出反例或卡住的确切位置，并把没证的部分写成带确切陈述的模块参数。你的最终消息就是回报原文，中文，按公共约束里的回报格式。

## 回报原文

KLp 回报

总结: 第一次编译就通过 (退出码 0), 没有用任何前提。有一个定位器在有限层上完全, 这件事是编译定理: 不用函数外延、不用公设、不用任何全知原理, 也没有模块参数。核心事实是 "合法极限的第 n 项字面地含 sucⁿ zero"。由它还得到一个副产品: 合法的 ℕ-极限树, 读回成层号后字面地含一切有限层 (`lim-all`)。

1. 文件
- <实验目录>/m6p/KLpFin.agda: 198 行, 最后一次编译退出码 0。
  - 日志在 <实验目录>/m6p/KLpFin.log, 只有 UnsupportedIndexedMatch 警告 (本模块 up1、compl 各有, w8 模块原本就有), 没有错误。
  - w8 的 .agdai 时间戳没有变。
  - 文件里检索 postulate、TERMINATING、NO_POSITIVITY、洞、funext, 结果为空。
  - 编译命令照公共约束, 其中 `-i` 用 w8 与 m6p。

2. 编译定理 (陈述逐字抄出)

定义 (不是定理, 列出来说明形状):
- `finQ : (j : L) → Maybe (Σ ℕ λ n → j ≡ lvl n)`: 认有限层。zero 认作 0; `nd sS h` 递归到 `h tt`, 相等由 `cong (λ y → nd sS (λ _ → y))` 给出, 靠 ⊤ 的 η, 不用外延; sL 和 sΩ 结点返回 nothing。
- `isLvl : (n : ℕ) (a : L) → Maybe (a ≡ lvl n)` 与 `selfP : (n : ℕ) (a : L) → Maybe (lvl n ≤ a)`: 判断 a 自身是否就是 lvl n, 是则给出路径 `self`。
- `find : (n : ℕ) (a : L) → Maybe (lvl n ≤ a)`: 对 a 结构递归的有限搜索。
  - `zero`: 只试自身。
  - `nd sS h`: 先试自身, 不成再进 `h tt` (用 `inc tt`)。
  - `nd sL g`: 只看第 n 个孩子 `g n` (用 `inc n`)。
  - `nd (sΩ _) _`: 返回 nothing。
- `locF : Locator`, 即 `locF j a = locG j a (finQ j)`。定义里没有任何证明作输入。

定理:
- `finQ-lvl : (n : ℕ) → finQ (lvl n) ≡ just (n , refl)`: 认有限层这一步认得出每个 lvl n。
- `locF-find : (n : ℕ) (a : L) → locF (lvl n) a ≡ find n a`: 在有限层上, locF 就是 find。
- `lt→ps : ∀ {x y} → zero ⊢ x ◃ y → Ps x y`: 第 0 层的步进证据就是字面的真子项。
- `up1 : (t : Tr zero) {u : Tr zero} → Ps u t → Sb (suc u) t`: 树 t 里若 u 是字面真子项, 则 suc u 是 t 的字面子项。这对一般的 u 都成立, 不限于 sucⁿ zero; 对 t 结构归纳, 极限一支用相邻项的步进证据。
- `zero-sb : (t : Tr zero) → Sb zero t`: 每棵第 0 层的树都含 zero。
- `limN : (f : ℕ → Tr zero) (a : (n : ℕ) → zero ⊢ f n ◃ f (suc n)) (n : ℕ) → Sb (nat n) (f n)`: 合法极限的第 n 项字面地含 sucⁿ zero。
- `sb→pth : ∀ {s t} → Sb s t → h₁ s ≤ h₁ t`: 字面子项经读回 h₁ 变成层号路径。
- `h₁-nat : (n : ℕ) → h₁ (nat n) ≡ lvl n`: sucⁿ zero 读回成有限层 lvl n。
- `lim-all : (f : ℕ → Tr zero) (a : (n : ℕ) → zero ⊢ f n ◃ f (suc n)) (n : ℕ) → lvl n ≤ h₁ (lim f a)`: 副产品。合法极限树的读回字面地含一切有限层, 不需要任何假设。
- `compl : (n : ℕ) (t : Tr zero) {j : L} → j ≡ lvl n → j ≤ h₁ t → IsJust (find n (h₁ t))`: find 在读回域上完全。对 t 归纳:
  - zero 与 suc 两支看路径的 self、inc、inu 三种情形;
  - lim 支不看原路径, 直接用 limN 造出指向第 n 个孩子的路径, 再递归。
- `cFin : CompleteFin locF`: 要交的完全性。
- `pos : PosStmt`: 要交的结论。
- 便于折叠使用的形式:
  - `locZ : (n : ℕ) (z : Tr zero) → Maybe (lvl n ≤ h₁ z)`, 定义为 `find n (h₁ z)`;
  - `locZ-locF : (n : ℕ) (z : Tr zero) → locF (lvl n) (h₁ z) ≡ locZ n z`: 它与 locF 在有限层上相同;
  - `locZ-ok : (n : ℕ) (z : Tr zero) → lvl n ≤ h₁ z → IsJust (locZ n z)`: 它同样完全。

3. 没做成的: 无。

4. 要证的命题不成立的情形: 未发现。

判断: 在 sL 结点只看第 n 个孩子就够了, 因为 `limN` 保证 lvl n 一定在那个孩子里, 而不只是在某个孩子里。所以对第 0 层读回的层号, `find n` 在 sL 结点总能成功, 不依赖输入的路径; 只在有限个 sS 结点上要比较自身。sΩ 结点放弃对 CompleteFin 没有影响, 因为 h₁ z 里没有 sΩ。若以后要对含 sΩ 的一般层号完全, 需要另加 `ink` 分支并另行证明, 这一点本次没有做。
