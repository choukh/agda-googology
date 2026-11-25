# 合成一个完整候选折叠并按对照表核一遍（Fable 5.2）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-17 04:52 至 05:07 |
| 工具调用 / agda 编译 (粗数) | 30 / 8 |
| token (usage 字段，按消息去重) | 输出 93411；新写入缓存的输入 245874；读缓存的输入 4005887；其余输入 50 |
| 写过的仓库文件 | `YiUFExit.lagda.md`, `YiUFLaw.lagda.md` |
| 文件前缀 | `YiUF` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 逐件冷编 5 件全部退出 0，禁用构造 0，导入闭包干净；候选是带深度 d 的一族折叠（不带 d 的写法不过停机检查，有限测试）；下标侧分叉格在地板之上时改成保留或同层对角（idx-case、idx-tw、keep₂、node₂）；地板之下一格仍分叉（lo-cross₂）；孩子侧槽位未改（diag-slotᶜ）；替身内部用同一族低一档（seen-eq、seen-full）；塔各项 Ω 树在域里（Ωt-tw）；LowKeep 只剩参照一侧；没有值的定理 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b78/YiUF.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。在仓库根目录 `<仓库>` 下工作。只新建你前缀的文件，不改任何已有文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

### YiUF 回报: 完整候选折叠, 按对照表逐出口核 (2026-11-17, Fable 5.2)

#### 1 判决

**对纲领与目标**: 候选只在新文件里, 主线定义未动; 全部 `--safe --without-K`, 无公理, 不读记号 (导入闭包禁用表命中 0). 三处改动都只用层号字面的地板, 路径复合与换基证据, 不比较孩子下标 (先验检查是判断, 见问题表 P6). 对 "让树自足": 本路的结论全是对层号, 证据, 槽位, 孩子, 目标路径一般的形状定理, 不按站, 不按塔的项数; **没有任何值的定理**, 候选是否抬高值未知.

**各步到哪**:
- 第 0 步 (设计, 停机): 完成. 不带参数的互递归写法不过停机检查 (有限测试, 一种写法, 退出 42 `TerminationIssue: seen, ψ, mono`). 改成带自然数 d 的一族折叠 `ψ d`: d 只在进替身时减一, d = 0 时嵌入行回退. 通过检查器. 没有找到良基度量 (未走通, 不是否定).
- 第 1 步 (实现): 完成. `ψ`, `mono`, `kp`, 闭项 `closed d n` (塔各项), `EBOᶜ d` (Λ, 证据 `rb-Λ`). 合法性是类型.
- 第 2 步 (按表核): 完成, 形状档. 表见下.
- 第 3 步 (接口): 完成树一侧. 候选满足 `YiBLIface` 的保留律, 回退律, 换基律, 单调, 得 `lowᴮ`; 域 `KD` 与两系统结点出口树一侧实填, 得 `lowᴰ`, 前提只剩参照一侧 (`OutRDT`, `OutDT`, 关系的生成规则 `Zero/Succ/Lim/Node/Emb/Weak`, `leR`, `Gen⁺`). 参照一侧未实填.
- 第 4 步 (代价与翻译账): 见 §6, 是判断.

**更新后的对照表 (候选一列; 只列分叉出口的格)**

| 格 (CompareTable) | 现行/换基 | 候选 `YiUFFold` | 落在哪个出口, 是否按规则 | 档 |
|---|---|---|---|---|
| C-X 下标侧槽位推进后分叉, 目标在地板之上 (`drop-idx`, `drop-tw`, `drop₂`) | `nothing`, 走链 | 结果是 `keepS`: 保留在层号字面相同的槽位上; 只有目标字面等于槽位层号时不保留 | `kept` 或同层对角, 不再分叉; 按 "低于目标保留, 同层对角" | 编(形) `idx-case`, `idx-tw` (一切 n, c′, 路径), `keep₂`, `node₂` |
| C-X 下标侧槽位, 目标在地板之下 (`route` 给 `inj₁`) | 推进后可分叉 | 未改, 与现行同一行 | 仍可在分叉出口; 实例: 槽位层 `zero`, 目标 `tw 1`, 经孩子路径不保留, 经下标层侧路径保留 | 编(形) `lo-cross₂`, `lo-ink₂`; 是否在实际链上被问到: 判断 |
| C-X 孩子侧槽位 R77 (`diag-slot`) | `nothing` | 未改 | 仍在分叉出口 | 编(形) `diag-slotᶜ`, `Main.main-noEv` |
| 同上, "读回域里不出现" | `KD` 只在塔第 1 项有实例 (`kept-tw1`) | 塔第 n+1 项的 Ω 树对一切 n, c′, 地板之上的目标在 `KD` 里, 除非目标字面是 `tw n` | 域内不出现这种结点 (对 Ω 树); 一般链上的树是否留在域里: 判断 | 编 `QDTw.Ωt-tw`, `kept-top`; 前提实例 `route₂` |
| C-UX 嵌入行 (`fallᶻ`, `fallᴮ`) | 回退 / 无证据回退 | 满证据且 d ≥ 1: 按 `route` 二分 (地板之下进孩子 c 朝原目标; 地板之上替身 ⊞ 第 0 层尾项), 不回退; d = 0: 回退 | X-a / X-b; 值未知 | 编(形) `row-full`, `row-alt`, `row-zero` |
| C-UX X-a, y 一般 | 只进第 0 层尾项 | 未改 | 低 (判断, 同原表) | 判断 |
| 替身内部 (`rb-no`) | 无证据, 回退 | 第 d 个折叠低一档, 证据由 `rb-row` 给且外满则内满; 内部嵌入行按 `row-full`, 保留行按 `idx-case`; 嵌套深度超过 d 处回退 | 截断点从 "第一层" 移到 "第 d 层" | 编 `seen-eq`, `seen-full`, `full-row`, `full-tw`, `full-Λ` |
| R80 (一致目标推进孩子 `zero`), R94 (`emb` 经孩子 0) | 未查 | 未改, 未查 | — | 未核 |
| 无证据处 | — | 保留判定逐点等于主线 `YiRWFold.kp` | 改动只在有 `Schema` 的结点起作用 | 编 `kp-no` |

**问题表**

| # | 问题 | 位置 | 档 |
|---|---|---|---|
| P1 | 没有值的定理; "候选在这些格上不低" 全无依据 | 全部 | — |
| P2 | 候选是一族 `ψ d`, 不是一个折叠; `EBOᶜ d` 随 d 变; 对 d 的单调与 "多大的 d 够用" 都没有; 嵌套深度不由塔的项数界住 | `YiUFFold` | 定义事实; "不由 n 界住" 是判断 |
| P3 | 下标侧槽位而目标在地板之下的格仍分叉, 有低于目标却不保留的实例 | `YiUFExit.lo-cross₂` | 编(形) |
| P4 | 孩子侧槽位 R77 未改; 域外的树不陈述 | `diag-slotᶜ` | 编(形) |
| P5 | 参照一侧出口 (`OutRDT`, `OutDT`, `Hand₁`, `SubDom`) 未实填 | `YiUFDom` | 前提 |
| P6 | 先验检查 (不落入 `obs→dec` 一族, `ColW.wdecα`, 壁垒) 没有编译判据 | — | 判断 |
| P7 | 与主线折叠没有比较定理 (只有 `kp-no`); 旧站值不能搬 | — | 判断 |

P6 的理由: 保留行与嵌入行的派发都经 `route S j c′ v`, 它是目标路径 v 与孩子 c′ 的偏移层号的函数, 交出的是路径, 不是两个孩子之间的见证, 也不是命题的判定; 目标是指定孩子的 (`inc c′ v`), 但没有孩子下标类型上的证据函数, 没有按存在性保留 (同一目标层换一条路径结果可以不同, `lo-cross₂` 对 `lo-ink₂`). 证据 `Rb` 只经 `↑`, `OkO` 读层号. 不要求带三歧的下标类型.

#### 2 文件表 (都在 `<仓库>/probes/OCF/Lean/`)

| 文件 | 总行 | 代码行 | 冷编退出码 |
|---|---|---|---|
| `YiUFBase.lagda.md` | 115 | 76 | 0 |
| `YiUFFold.lagda.md` | 176 | 140 | 0 |
| `YiUFExit.lagda.md` | 265 | 171 | 0 |
| `YiUFLaw.lagda.md` | 265 | 189 | 0 |
| `YiUFDom.lagda.md` | 307 | 215 | 0 |

冷编: 删五个自己的 `.agdai` 后一次编 `YiUFDom` (它导入其余四个), `-M6G`, 退出 0, 日志只有这五个模块的 `Checking` 行. 禁用构造与本机路径检索 0 条. `importclosure.py` 五个模块都 "禁用表命中: 0, OK".
绝对路径: `<仓库>/probes/OCF/Lean/YiUFBase.lagda.md`, `<仓库>/probes/OCF/Lean/YiUFFold.lagda.md`, `<仓库>/probes/OCF/Lean/YiUFExit.lagda.md`, `<仓库>/probes/OCF/Lean/YiUFLaw.lagda.md`, `<仓库>/probes/OCF/Lean/YiUFDom.lagda.md`.
临时文件 (不进仓库): `<实验目录>/work/YiUF/YiUF0.agda` (带 d, 退出 0), `<实验目录>/work/YiUF/YiUF0nf.agda` (不带 d, 退出 42, 停机检查).

#### 3 定理表

**定义 (YiUFBase, YiUFFold)**
- `Rb (nd (sΩ k) h) = (Rb k × Maybe (Schema k h)) × ((c : Tr k) → Rb (h c))`. 比 `YiBSBase.Rb` 多下标层的证据.
- `rb≤ : (ℓ : L) → Rb ℓ → ∀ {j} → j ≤ ℓ → Rb j`. 证据沿任何目标路径降下 (含 `ink`).
- `kp : (ℓ : L) → Ok ℓ → Rb ℓ → (p : Pos ℓ) → ∀ {j} → j ≤ ℓ → Keep j (Br ℓ p) (fromBr ℓ p zero)`. 唯一改的一行:
  `kp (nd (sΩ k) h) ((_ , kh) , oc) ((_ , m) , rc) (inj₁ t) (inc c v) = rb m (λ S → cW (route S _ c v) (λ _ → 原推进) (λ u → keepS S t u)) 原推进`.
- `ψ : ℕ → (ℓ : L) → Ok ℓ → Rb ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j`; `mono : ∀ d ℓ o r B j w β {x y} → ℓ ⊢ x ◃ y → j ⊢ proj₁ (ψ d ℓ o r B j w β x) ◃ proj₁ (ψ d ℓ o r B j w β y)`.
- `seen : ℕ → ∀ {k h} (S : Schema k h) (j : L) → Ok j → Rb j → floor S ≤ j → Tr⁺ j → Tr k → Tr⁺ j`.
- `closed : ℕ → (n : ℕ) → Tr⁺ zero`; `EBOᶜ : ℕ → Tr⁺ zero`, `EBOᶜ d = ψ₀ d Λ Ok-Λ rb-Λ (proj₁ (Ωt Λ))`.

**编译定理**

| 名字 | 逐字陈述 | 白话 | 文件 |
|---|---|---|---|
| `full-tw` | `(n : ℕ) → Full (tw n) (rb-tw n)` | 塔各项每个 Ω 形状结点 (含下标层里的) 都有 `Schema` | Base |
| `full-Λ` | `Full Λ rb-Λ` | Λ 同上 | Base |
| `full-row` | `∀ {k h} (S : Schema k h) j oj rj (u : floor S ≤ j) → Full j rj → (c : Tr k) → Full (j ⊕ offsets S c) (rb-row S j oj rj u c)` | 重建层号的证据满 | Base |
| `kp-exit` | `(ℓ : L) (o : Ok ℓ) (r : Rb ℓ) (p : Pos ℓ) → ∀ {j} (w : j ≤ ℓ) → Exit (at ℓ p) (kp ℓ o r p w)` | 候选的保留判定仍只有三个出口 (`YiCMExit.Exit` 原类型) | Exit |
| `keepS-lin` | `∀ {k h} (S : Schema k h) (t : Pos⁼ k) {j} (u : floor S ≤ j) → Lin (proj₁ (sl⁼ k t)) (keepS S t u)` | `keepS` 的结果: 保留在层号字面相同的槽位, 或目标字面等于槽位层号 | Exit |
| `idx-case` | `∀ k h (o : Ok (nd (sΩ k) h)) (rk : Rb k) (S : Schema k h) (rc : (c : Tr k) → Rb (h c)) (t : Pos⁼ k) c {j} (v : j ≤ h c) → (j ≤ floor S) ⊎ Lin (proj₁ (sl⁼ k t)) (kp (nd (sΩ k) h) o ((rk , just S) , rc) (inj₁ t) (inc c v))` | 有 `Schema` 时: 目标在地板之下, 或不分叉 | Exit |
| `idx-hi` | `… → (j ≤ floor S) ⊎ (Σ (floor S ≤ j) λ u → kp (nd (sΩ k) h) o ((rk , just S) , rc) (inj₁ t) (inc c v) ≡ keepS S t u)` (参数同上) | 同上, 给出等式 | Exit |
| `idx-tw` | `∀ n (t : Pos⁼ (tw n)) (c′ : Tr (tw n)) {j} (v : j ≤ tw n ⊕ ↑ (tw n) c′) → (j ≤ tw n) ⊎ Lin (proj₁ (sl⁼ (tw n) t)) (kp (tw (suc n)) (Ok-tw (suc n)) (rb-tw (suc n)) (inj₁ t) (inc c′ v))` | 塔各项是实例, `drop-tw` 的对应 | Exit |
| `top-keep` | `∀ {k h} (S : Schema k h) {j} (u : floor S ≤ j) → IsJust (keepS S (inj₁ tt) u) ⊎ (k ≡ j)` | 顶槽位保留, 除非目标字面是下标层 | Exit |
| `slot-keep` | `∀ {k h} (S : Schema k h) (p : Pos k) {j} (u : floor S ≤ j) → IsJust (keepS S (inj₂ p) u)` | 下标层里的真槽位总保留 | Exit |
| `keep₂` | `IsJust (kp (tw 2) (Ok-tw 2) (rb-tw 2) (inj₁ (inj₁ tt)) (inc c′₂ v₂))` | 审查 E 路 `drop₂` 的格现在保留 | Exit |
| `node₂` | `∀ d (B : Base (tw 2)) (β : Tr⁺ j₂) → IsΩ (proj₁ (ψ d (tw 2) (Ok-tw 2) (rb-tw 2) B j₂ (inc c′₂ v₂) β (proj₁ (Ωt (tw 2)))))` | `chain₂` 的反面: 输出是 Ω 结点, 对一切 d | Exit |
| `diag-slotᶜ` | `∀ k h (o : Ok (nd (sΩ k) h)) (r : Rb (nd (sΩ k) h)) c (p′ : Pos (h c)) → (kp (nd (sΩ k) h) o r (inj₂ (c , inj₂ p′)) (inc c self) ≡ nothing) × (Br (h c) p′ ≡ Br (nd (sΩ k) h) (inj₂ (c , inj₂ p′))) × (at (h c) p′ ≡ at (nd (sΩ k) h) (inj₂ (c , inj₂ p′)))` | 孩子侧槽位未改 | Exit |
| `lo-cross₂` | `kp (tw 2) (Ok-tw 2) (rb-tw 2) p₂ (inc c′₂ w₂) ≡ nothing` (`p₂-at : at (tw 2) p₂ ≡ zero`, `w₂ : tw 1 ≤ tw 1 ⊕ ↑ (tw 1) c′₂`) | 剩下的格: 槽位层 `zero`, 目标 `tw 1`, 不保留 | Exit |
| `lo-ink₂` | `IsJust (kp (tw 2) (Ok-tw 2) (rb-tw 2) p₂ (ink self))` | 同槽位同目标层, 经下标层侧路径保留 | Exit |
| `kp-no` | `(ℓ : L) (o : Ok ℓ) (p : Pos ℓ) → ∀ {j} (w : j ≤ ℓ) → kp ℓ o (rb-no ℓ) p w ≡ RW.kp ℓ o p w` | 无证据时等于主线的保留判定 | Exit |
| `row-zero` | `∀ k h o r B j c′ (v : j ≤ h c′) β x c y e → ψ zero (nd (sΩ k) h) o r B j (inc c′ v) β (up x c y e) ≡ ψ zero (nd (sΩ k) h) o r B j (inc c′ v) β x ⊞ ψ zero (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y` | d = 0 回退 | Exit |
| `row-full` | `∀ d k h o r (f : Full (nd (sΩ k) h) r) B j c′ (v : j ≤ h c′) β x c y e → (Σ (j ≤ floor S) λ u → ψ (suc d) … (up x c y e) ≡ ψ (suc d) (h c) (proj₂ o c) (proj₂ r c) (λ i u′ → ψ (suc d) (nd (sΩ k) h) o r B i (inc c u′) (B i (inc c u′)) x) j (back S c u) (ψ (suc d) … β x) y) ⊎ (Σ (floor S ≤ j) λ u → ψ (suc d) … (up x c y e) ≡ seen d S j (downOk (h c′) (proj₂ o c′) j v) (rb≤ (h c′) (proj₂ r c′) v) u (ψ (suc d) … β x) c ⊞ ψ (suc d) (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)`, 其中 S 逐字是 `proj₁ (proj₂ (proj₁ f))`, `…` 逐字是 `(nd (sΩ k) h) o r B j (inc c′ v) β` | 满证据, d ≥ 1: 嵌入行不回退 | Exit |
| `seen-eq` | `∀ d {k h} (S : Schema k h) j oj rj (u : floor S ≤ j) β c → seen d S j oj rj u β c ≡ ψ d (j ⊕ offsets S c) (Ok⊕ j (offsets S c) oj (raiseO (floor S) j (offsets S c) u (ok-offsets S c))) (rb-row S j oj rj u c) (B₀ _) j (lift j (offsets S c)) β (proj₁ (Ωt (j ⊕ offsets S c)))` | 替身是同一个折叠低一档 | Exit |
| `seen-full` | `∀ {k h} (r : (c : Tr k) → Rb (h c)) → ((c : Tr k) → Full (h c) (r c)) → (S : Schema k h) → ∀ j c′ (v : j ≤ h c′) oj (u : floor S ≤ j) (c : Tr k) → Full (j ⊕ offsets S c) (rb-row S j oj (rb≤ (h c′) (r c′) v) u c)` | 替身内部证据仍满 | Exit |
| `Pack.lowᴮ` | `(Le …) (wk : Weak) (lm : Lim) (nod : Node) → OutR sysᴮ sysᴬ keepᴬ embᴮ Le keepᴮ → Sys.Out sysᴬ Le keepᴬ fallᴬ → (∀ a → Gen⁺ Le a) → (β : Tr⁺ j) (K₀ : Cxtᴮ) → Bdᴮ (rt β) K₀ → (Kc : Cx ℓ j) → (∀ t → apᴮ K₀ t ≡ app Kc t) → ∀ {a x} → Rᵍ ℓ a x → Rᵍ j (app Kc a) (proj₁ (C.ψ (suc d) ℓ o r B j w β x))` | 候选换基行上的保持, 出口是前提 | Law |
| `kp-good` | `(ℓ : L) (o : Ok ℓ) (r : Rb ℓ) (p : Pos ℓ) {j : L} (w : j ≤ ℓ) → GoodK (at ℓ p) (slTᵍ ℓ p) (kp ℓ o r p w)` | 候选保留判定每行在换型下照搬关系 | Dom |
| `QDPack.WithRules.lowᴰ` | `OutRDT sysᴮ sysᴬ keepᴬ embᴮ Le keepᴮ Dᴮ ntᴮ → OutDT sysᴬ Le keepᴬ fallᴬ Dᴬ ntᴬ → (β : Tr⁺ j) (K₀ : Cxtᴮ) → Bdᴮ (rt β) K₀ → (Kc : Cx ℓ j) → (∀ t → apᴮ K₀ t ≡ app Kc t) → ∀ {a x} → KD x → Rᵍ ℓ a x → Rᵍ j (app Kc a) (proj₁ (C.ψ (suc d) ℓ o r B j w β x))` | 域里的 LowKeep, 前提只在参照一侧 | Dom |
| `QDTw.Ωt-tw` | `KD (proj₁ (Ωt (tw (suc n)))) ⊎ (tw n ≡ j)` (模块参数: d, n, B, j, c′, `v : j ≤ tw n ⊕ ↑ (tw n) c′`, `u : tw n ≤ j`, `eq : route (Sₙ n) j c′ v ≡ inj₂ u`) | 塔各项的 Ω 树在域里, 对一切 n | Dom |
| `route₂` | `route (Sₙ 1) j₂ c′₂ v₂ ≡ inj₂ (lift (tw 1) (nd sS (λ _ → zero)))` | `Ωt-tw` 的前提可满足 | Dom |

`Lin` 的两个构造子: `keptᴸ : ∀ q cv e → at j q ≡ a₀ → Lin a₀ (just (q , cv , e))`, `sameᴸ : j ≡ a₀ → Lin a₀ nothing`.

**有限测试**: 不带 d 的互递归写法不过停机检查 (一种写法).

#### 4 第一个障碍

- **把一族变成一个折叠**: 缺的引理是重建层号上的良基度量, 即一个 L 上的良基关系使 `j ⊕ offsets S c` (其中 `floor S ≤ j ≤ h c′`) 低于 `nd (sΩ k) h`; 或对 d 的单调 `ψ d … ≼ ψ (suc d) …`. 两条都没有试证. 前者是数学上的 (重建层号不是结构孩子, 它把一个 Ω 形状偏移结点换成两个孩子的部分之和, 判断上像多重集序), 不是工程上的.
- **值**: 第一处是参照一侧的 `OutRDT.embE` (`Hand₁`, `SubDom`: 两棵 Ω 树之间替身支配原材料) 与 `StepS`; 与第七十七批相同, 本路没有推进. 数学上挡住.
- **剩下的分叉格** (P3): 可试的写法 (判断, 未编译): `route` 给 `j ≤ floor` 时把槽位沿 `index-floor` 推进地板, 在地板里朝 j 判定 (塔上地板就是下标层, 等于走 `ink` 那一行, `lo-ink₂` 显示那里保留). 地板不是结构孩子, 同样要 d 或用主线的 `kp`. 简报写 "其余不变", 所以没有做.

#### 5 偏离与事故

- **证据类型另起**: 用 `YiUFBase.Rb` (多下标层分量), 没有逐字用 `YiBCCover.rb-row`; 重写的 `rb-row` 不要 `IsInj₂` 前提. 理由: 保留行经 `ink` 进下标层时要下标层的证据, `YiBSBase.Rb` 没有.
- **停机**: 没有做到 "同一个折叠", 是低一档的同一族; 也没有退到 `rb-no`.
- `YiUFDom` 的 `Move`, `AddR`, `QDPack` 三段用脚本从 `YiQDFold` 文本替换生成; 我核了 `lowᴰ` 的陈述与模块头, 没有逐行重读生成的中段.
- 冷编是一次运行编五个文件, 不是五次.
- 更新后的表只在本回报里, 没有写进 `CompareTable.md` (不改已有文件).
- 没有事故; 没有 251; 没有量峰值内存.
- **没有读, 只凭转述或检索**: `Barrier.lagda.md` (没有打开, 凭 AGENTS 的描述); `YiAbsObs` 与 `YiDGDiag` 只读文首与检索到的陈述; `YiQDIface` 只读签名; `AuditE.md` 只读检索到的行与附件 `AuditEKeep`; `EBOHandbook` 4.2, 4.6 与 Bedrock 性能手册没有读 (没有遇到性能问题); `YiVA`, `AuditD`, `YiSV*`, `YiEM*`, `YiZS*` 没有读.

#### 6 代价清单与翻译账 (判断)

候选替换主线要重做的:
- 站值 (第 0 到 2 站下界, `YiFYRef.target-low`): 证在 `YiTBRow.ψ` 配 `rbᶻ` 上. 塔各项的证据是满的, 候选的行从塔第 1 项起就可能不同, 与主线没有比较定理, 要重证或先证比较.
- 第一档成品 (View, FGH 入口): 闭项类型相同 (`Tr⁺ zero`), 但要先定 d.
- LowKeep 树一侧: 本路已对候选重做 (`YiUFLaw`, `YiUFDom`). 参照一侧形状不变.
- 替身的值与单调 (`YiSVRed.StepS`, `YiSVMono`, `YiBSCrit`): 替身的定义变了, 要重做.
- 码域 (`YiEM*`, `YiBC*`): 证据类型变了, 要重做.

每处改动的理由:
| 改动 | 来自 | 新脚手架 |
|---|---|---|
| 保留行接 `keepS` | 树侧: `kp-exit` 的分叉出口上槽位有到目标的字面路径却不保留 (`drop-idx`) | 无 |
| 嵌入行 | 沿用 `YiBSFold` | 无 |
| 替身调用候选自己 | 树侧: 替身内部与外面同一规则 | 参数 d: 停机检查逼出, 不是序数值需要的, 也不读自记号 |
| 证据带下标层分量 | 树侧: 证据要能沿 `ink` 降下 | `Rb` 多一个分量 |

没有字段形状读自记号的基本列规则; 没有用 `Lab` 验收; 闭包定理 (`lowᴮ`, `lowᴰ`) 没有为候选新增专属前提.

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：合成一个完整候选折叠，并按对照表逐出口核一遍（前缀 YiUF，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Fable 5.2。同批另一路（前缀 `YiXT`）与你互不导入。

#### 作者的话与决定（2026-11-17）
- 作者对方法的担心（原文）："真的只有这样一站一站吗？能否借助记号搞清楚内在结构，然后对比树的定义（包括整个归纳类型的规则）在树的生成上，和记号+基本列定义加终止证明生成的树，在什么节点和站上有区别。我的意思是更加结构化地高屋建瓴地分析，而不是盲目地一站一站深入"。
- 对照表一路（YiCM）的结论：`probes/Survey/CompareTable.md`。保留判定 `kp` 对一切层号、证据、槽位、目标只有三个出口：保留（槽位层号有到目标的字面路径，`YiCMExit.kept-below`）、同层或高于（走链）、分叉（Ω 形状结点上，材料在孩子 c 之下，目标在孩子 c′ 之下）（`YiCMExit.kp-exit`）。表里所有值上低与未知的格都在分叉出口（判断，逐格填表；R94 的 `emb` 经孩子 0、R80 的推进经孩子 `zero` 两处未查）。分叉出口上的缺陷对参数一般地成立（形状档）：`YiCMExit.diag-slot`、`diag-same`、`tb-nz`、`fallᶻ`、`YiCMCross.drop-idx`、`drop-tw`（实例 `c′-inst`）、`chainᴿ`、`chainᵀ`、`chainᴮ`、`chain-twᴮ`；换基证据给的保留 `YiCMCross.keepS`、`keepS-lift`（未接进折叠）。
- 作者选项原文："合成一个完整候选折叠并按表核一遍 (Recommended), 把 \"缺陷都在分叉出口\" 写成定理 (Recommended)"。前缀 `YiUF`（Fable 5.2）、`YiXT`（Opus 5.5），互不导入。**主线定义不动**；候选只在新文件，进主线由作者定（AGENTS "第 4 层不反过来改前 3 层"，改动理由来自树侧，翻译账单列 "第 4 层逼出"）。
- **分叉出口的三类格与已在手的手段（主审读表的判断，未编译，要判定的就是它）**：嵌入行 → 换基（`YiBSFold`；替身不再问原材料的槽位，`YiBLIface`/`YiBLFold`）；下标侧槽位推进后分叉 → 换基证据给的路径（`keepS`）；主系统孩子侧槽位 → 读回域里不出现（`YiQDFold` 的域 `KD`：本层结点都在有保留证据的槽位上，嵌入的原材料 `⊴` 孩子层号的 Ω 树）。另：替身内部 `YiBSBase.seen` 用无表证据 `rb-no`（审查 E 路，台账 V299；`YiBCCover.rb-row` 给了替身重建层的证据，接进去要过停机检查，V149 记过一种写法不过）。
- 第七十七批（主审 8G 冷编 13 件全部退出 0，已复核）：`YiQD*`（按读回域的充分性 `SuffD.keepAllᴰ`、`SuffRD.sys→lowᴰ`；换基上的 `WithRules.lowᴰ`、`QDTw1.low-tw1`，前提全在参照一侧；`kp-good`；链一支改成按关系支配 `AddR.chain-dom`，原形状被 `YiQDNeg.Min.no-chain₁` 否定；`SubstDom.raise→SubDom`），`YiZS*`（`StepS` 在 η = ω+n+1 成立 `YiZSLit.Seg.StepS-ωn`；ω·2+1 起要 ℕ 极限层号接口，`YiZSLim.Lim₊` 四条已编译；合并 `YiZSUni.Lift.genS`、`genL`），`YiEM*`（替身码加嵌入码 `YiEMRead.Read⁺`；同步对象各来源的块在码域里；现行 `seen` 不按块的码换基 `YiEMChain.seen≠code`，要按码换基须改定义）。审查 E 路：`Reports-2026-11-16/AuditE.md`，判定件附件 `attachments/AuditE-AuditEKeep.agda.txt`（`drop₂`、`chain₂`）、`AuditE-AuditEKeepFix.agda.txt`（`keepS`、`kp₂-kept`）。
- 主线现状：第一档成品已完成；终点无条件值 ψ₀(Ω_Ω+ψ₁(Ω_ω)+ω)（`YiFYRef.target-low`）；里程碑 ψ₀(Ω_{Ω₂}) 未达到；现行折叠上同步对象那一格已关闭（V287）。

#### 本路的问题
把分叉出口的三种手段合进**一个**候选折叠，然后按对照表**逐出口、对参数一般地**核：分叉格是否都被覆盖。不按站、不按塔的项数测。

#### 要做的（按序）
0. **设计与先验检查**（先写，在临时文件里编译类型）：
   - 嵌入行：用换基行（`YiBSFold` 那一行，路由 `split`/`route` 落在地板之上时经 `seen`）。
   - 保留行：在 `kp` 的分叉出口上，若换基证据的路由给 "地板 ≤ 目标"，用 `keepS` 给的路径保留；其余不变。
   - 替身内部：让 `seen` 调用同一个候选折叠（用 `YiBCCover.rb-row` 的证据），而不是 `rb-no`。这要过停机检查：试按层号分层定义，或找良基度量（V149 记过一种互递归写法不过，先读那条）。若两种都不过，退一步：内部保留 `rb-no`，写清这一处的后果。
   - 对每处改动按 AGENTS "开新行前的先验检查" 逐条对照 `YiAbsObs` 的 `obs→dec` 一族（`branch→wdec`、`hand→wdec`、`viaE→dec`、`full→dec`）、`YiDGDiag.ColW.wdecα`、壁垒 `probes/OCF/Barrier.lagda.md`；说明新行只用层号字面的地板、路径复合与换基证据，不看孩子下标。
   不成立就停下回报。
1. **实现**：在新文件里写出候选折叠（全函数，`mono` 与合法性），并写出它的闭项：塔各项与 EBO（`Rb Λ` 用 `rb-tw` 一类；"交付拆成闭项与值" 的 (a)）。
2. **按表核**：对 `CompareTable.md` 里分叉出口的每一类格，在候选上给对参数一般的形状事实（对一切层号变量、孩子、证据成立的编译定理），回答 "这一格现在落在哪个出口、效果是否按 '低于目标保留、同层对角、高于走链'"。至少覆盖：`diag-slot` 那类、`fallᶻ` 那类、`drop-idx`/`drop-tw` 那类、审查 E 路 `drop₂` 那一格、替身内部。交一张更新后的表（候选折叠一列），每格标档。
3. **接口**：候选满足 `YiBLIface` 的树一侧律（保留律、换基律）与 `YiQDFold` 的域（`KD`）吗；若满足，接上 `YiQDIface.SuffRD.sys→lowᴰ`，写出候选上 LowKeep 剩下的前提（应当只剩参照一侧）。
4. **代价清单与翻译账**：候选替换主线要重做什么（第一档成品、站值、LowKeep 引理）；每处改动的树侧理由。

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

