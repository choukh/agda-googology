# KKp：保留判定里的有限层（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | high |
| 起止 (转录的时间戳，UTC) | 2026-11-25 03:31 至 03:42 |
| 工具调用 / agda 编译 (粗数) | 38 / 3 |
| token (usage 字段，按消息去重) | 输出 41052；新写入缓存的输入 167233；读缓存的输入 4079176；其余输入 68 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `KKp` (在 `<实验目录>/m7/`) |
| 主审复核后的一句结论 | 完成：保留判定在 Ω 形层号上 孩子位置的结点、目标经指定孩子 那一格改成按有限层保留（目标层与槽位层都认得出是有限层且槽位层严格更低时给 just，其余给 nothing）；全链冷编通过，只补了 KBBase 的 kdLem 一格；形状事实 kp-keep、kp-chain 是 refl；候选的定位器 loc 在有限层上完全（cFin）。主审另目录冷编退出 0，核对相对基目录只改了 W4Fold（两行）、W4Loc（只增）、KBBase（kdLem）三个文件，禁用构造 0。源码随候选打包留档在 Reports-2026-11-25/attachments/W5-*.agda.txt |

## 简报原文

你的任务简报全文在这个文件里，请先完整读它，再严格照做（它是自足的，背景、任务、约束都在里面，其中第一步是读公共约束文件）：

<实验目录>/briefs/KKp.md

要点提示（以简报为准）：这是一个 Agda 形式化任务（--safe --without-K）。基目录 scratchpad/w9 是 W4 折叠的一份候选改写（已编译，只读）。你要把它整个拷到自己的工作目录 scratchpad/m7，在拷贝上只改保留判定 kp 的一格：Ω 形层号上"孩子位置上的结点、目标经指定孩子"现在无条件给 nothing；改成当目标层与槽位层都认得出是有限层且槽位层严格更低时保留（返回 just，位置取目标层里槽位层相同的那个位置，分支下标用 subst 搬回），其余情形仍给 nothing。然后让全链（W4Fold、W4Val、W4View、K 前缀模块直到 KBtbo）重新通过，预计要补 KBBase 的 kdLem 里对应的一格。另交几条 refl 的形状事实，以及对 W4Loc 的定位器 loc 证有限层上的完全性。模块名不要改，新文件前缀 KKp；只在 <实验目录>/m7 里写；不改仓库与基目录；同时只跑一个 agda，堆上限 6G；不提交。做不完时把没证的部分写成带确切陈述的模块参数并报出，不要留洞；发现"保留"使某条单调或合法性证明过不去时照实报，不要绕过。你的最终消息就是回报原文，中文，按公共约束里的回报格式，并列出改过的已有文件及各自改了什么。

## 回报原文

#### 结论

四项都做完了。全链冷编（工作目录的 .agdai 全部删掉后从 KBtbo 起重编）退出 0。没有模块参数，没有洞、公设或编译指示。

- `kp` 在 Ω 形层号上 "孩子位置上的结点、目标经指定孩子" 那一格，改成按有限层保留。全链只需要补 KBBase 的 `kdLem` 那一格。
- KMir 的 `K` 和 KOpBase 的 `KOk` 在 Ω 形层号上本来就是空情形（`IsS (nd (sΩ _) _) = ⊥`），不用动。
- `nodeLe`、`kpT`、W4Val、W4View 也不用动，原样通过。
- 没有发现哪条单调或合法性证明因为 "保留" 而过不去。

#### 1. 文件、行数与退出码（都是冷编后最后一次的结果）

改过的已有文件：
- **W4Loc.agda**（125 行，退出 0）
  - 导入行加了 `Data.Sum (inj₁; inj₂)`，等式导入加了 `trans`。
  - 文末新增辅助定义：`Lo` / `here` / `there`（m < n 的见证）、`loZ`、`loS`、`lo?`、`posLo`、`brLo`、`brLo-zero`、`atLo`、`subst-zero`、`KeepTy`（Keep 的展开写法）、`keepLo`、`keepL`、`keepN`、`keepFin`。
  - 已有函数一个字没改，`find` 的搜索次序也没改。
- **W4Fold.agda**（569 行，退出 0）
  - 导入改为 `using (loc; keepFin)`。
  - 只改第 54 行那一格，其余子句逐字不动。原来是
    `kp (nd (sΩ k) h) _ (inj₂ _) (inc _ _) = nothing`
    现在是
    `kp (nd (sΩ k) h) _ (inj₂ (c , t)) {j} (inc _ _) = keepFin j (proj₁ (sl⁼ (h c) t)) (proj₂ (sl⁼ (h c) t))`
  - 行为：`fin?` 认出目标层 j 是 lvl n、槽位层是 lvl m，并且 `lo? m n` 给出 m < n 时，返回 `just`。位置取 `posLo l`，即 j 里槽位层为 lvl m 的那个位置。分支搬运是 `λ z → fb (subst Tr (sym ea) (brLo l z))`，再沿 `sym ej` 用 subst 搬到 j 上。其余情形给 `nothing`。
- **KBBase.agda**（277 行，退出 0）
  - 导入加了 `Maybe` 和 `import W4Loc as WL`。
  - 在 `kdLem` 前新增引理 `kdSubst`、`subLo`、`domSubst`、`kdL`、`kdN`。
  - `kdLem` 那一格由 `tt` 改为
    `kdN j (proj₁ (sl⁼ (h c) t)) (proj₂ (sl⁼ (h c) t)) (toSub⁼ (h c) t) (WL.fin? j) (WL.fin? (proj₁ (sl⁼ (h c) t)))`

新文件：
- KKpShape.agda（55 行，退出 0）
- KKpLoc.agda（70 行，退出 0）

其余 32 个从 w9 拷来的 .agda 一个字没改，冷编全部退出 0。其中有 KBtbo、W4Val、W4View、Exp4Shape、KLpFin、KMir、KOpBase、KBRows、KBMain 等。Exp4Shape 的那几条 refl 原样通过。

另有一个编译用的脚本 ag.sh，不是数学文件。

#### 2. 编译通过的定理（陈述逐字）

**KBBase：保留时的槽位数据（第 2 项）**

```
kdSubst : ∀ {j₁ j₂ : L} (e : j₁ ≡ j₂) {X : Set} {x₀ : X} {A : L} {SubX : ∀ {kY} → Ordᶜ kY → X → Set} (r : Keep j₁ X x₀)
        → KDg j₁ A SubX r → KDg j₂ A SubX (subst (λ i → Keep i X x₀) e r)
subLo : ∀ {m n} (l : WL.Lo m n) {kY} {Y : Ordᶜ kY} (z : Br (WL.lvl n) (WL.posLo l))
      → SubD (WL.lvl n) (WL.posLo l) Y z → Dom (WL.lvl m) Y (WL.brLo l z)
domSubst : ∀ {a b : L} (e : a ≡ b) {kY} {Y : Ordᶜ kY} {T : Tr a} → Dom a Y T → Dom b Y (subst Tr e T)
kdL : (n m : ℕ) {a : L} {X : Set} (fb : Tr a → X) (ea : a ≡ WL.lvl m) {SubX : ∀ {kY} → Ordᶜ kY → X → Set}
    → (∀ {kY} {Y : Ordᶜ kY} {T : Tr a} → Dom a Y T → SubX Y (fb T))
    → (ml : Maybe (WL.Lo m n)) → KDg (WL.lvl n) a SubX (WL.keepL n m fb ea ml)
kdN : (j a : L) {X : Set} (fb : Tr a → X) {SubX : ∀ {kY} → Ordᶜ kY → X → Set}
    → (∀ {kY} {Y : Ordᶜ kY} {T : Tr a} → Dom a Y T → SubX Y (fb T))
    → (mj : Maybe (Σ ℕ λ n → j ≡ WL.lvl n)) (ma : Maybe (Σ ℕ λ m → a ≡ WL.lvl m)) → KDg j a SubX (WL.keepN j a fb mj ma)
```

白话：保留时，输出位置的槽位层等于原槽位层（`atLo` 接上 `sym ea`）。输出分支上的关系 SubD 先读回成第 m 层上的 Dom，再沿 lvl m ≡ 槽位层搬过去，最后由 `toSub⁼` 交回原位置。`kdLem` 的签名没有变。

**W4Loc 里的小引理**

```
brLo-zero : ∀ {m n} (l : Lo m n) → brLo l (fromBr (lvl n) (posLo l) zero) ≡ zero
atLo : ∀ {m n} (l : Lo m n) → at (lvl n) (posLo l) ≡ lvl m
subst-zero : ∀ {a b : L} (e : a ≡ b) → subst Tr e zero ≡ zero
```

**KKpShape：形状事实（第 3 项，全是 refl）**

记号：`K = tw 1`，`oK = Ok-tw 1`，`c₂ = suc (suc zero)`，`c₃ = suc (suc (suc zero))`，`p₂ = inj₂ (c₂ , inj₂ (inj₂ (tt , inj₁ tt)))`，`w₂ = inc c₃ (inc tt self)`，`w₁ = inc c₃ (inc tt (inc tt self))`。`posK` 取出 Keep 里的位置。

```
slot-p₂ : at K p₂ ≡ lvl1
w₂ : h₁ c₂ ≤ K
kp-keep : posK (kp K oK p₂ w₂) ≡ just (inj₂ (tt , inj₁ tt))
kp-keep-slot : at (h₁ c₂) (inj₂ (tt , inj₁ tt)) ≡ at K p₂
w₁ : lvl1 ≤ K
kp-chain : kp K oK p₂ w₁ ≡ nothing
```

白话：结点在孩子 c₂ 里，槽位层是第 1 层。
- 朝孩子 c₃ 里的第 2 层：`kp` 给 just，位置是第 2 层里槽位层为第 1 层的那个，两边槽位层相同。
- 朝孩子 c₃ 里的第 1 层：`kp` 给 nothing，即走链。

**KKpLoc：定位器在有限层上完全（第 4 项）**

```
lvl≡ : (n : ℕ) → KL.lvl n ≡ W.lvl n
fin?-lvl : (n : ℕ) → W.fin? (KL.lvl n) ≡ just (n , lvl≡ n)
eqL-lvl : (n : ℕ) → IsJust (W.eqL n (W.lvl n))
selfOk : (n : ℕ) (a : L) → a ≡ W.lvl n → IsJust (W.eqL n a)
compl : (n : ℕ) (t : Tr zero) {j : L} → j ≡ W.lvl n → j ≤ h₁ t → IsJust (W.find n (h₁ t))
viaFind : (j a : L) (n : ℕ) (e : j ≡ W.lvl n) → W.fin? j ≡ just (n , e) → IsJust (W.find n a) → IsJust (W.loc j a)
cFin : CompleteFin W.loc
pos : PosStmt
```

白话：W4Loc 的 `loc` 满足 `KLoc.CompleteFin`，无前提，`find` 不用改次序。
- sL 结点那一步：`find` 看第 n+1 个孩子。合法极限的第 n+1 项字面地含 sucⁿ⁺¹ zero（`KLpFin.limN`），从而也含 sucⁿ zero。
- sS 结点上，按路径进孩子。
- Ω 形结点不会出现，因为第 0 层的树读回后没有 Ω。
- `lvl≡` 用来衔接 KLoc 与 W4Loc 各自定义的 `lvl`。

#### 3. 没做成的

无。

#### 4. 反例

无。

#### 判断（未编译，供主审）

- KMir 的 `K`（kp 与 Level 判定一致）只对 `IsS` 层号陈述，不覆盖 Ω 形层号。因此新格子 "保留 ⇔ 槽位层低于目标层" 在 Level 码一侧没有编译过的一致性定理。
- 新格子目前能确认的只有两点：按构造只在 lvl m、lvl n 且 m < n 时给 just；`kdLem` 那一格证了槽位层相等与关系搬运。
- 目标层不是有限层时仍给 nothing，与简报一致。
