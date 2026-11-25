# KQ：规范 Ω 树及其折叠沿层号路径的字面单调（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | high |
| 起止 (转录的时间戳，UTC) | 2026-11-25 06:09 至 06:43 |
| 工具调用 / agda 编译 (粗数) | 42 / 2 |
| token (usage 字段，按消息去重) | 输出 206637；新写入缓存的输入 802010；读缓存的输入 7254988；其余输入 70 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `KQ` (在 `<实验目录>/kq/`) |

## 简报原文

你的任务简报全文在这个文件里，请先完整读它（以及它开头指向的公共约束文件），再严格照做：

<实验目录>/briefs/KQ.md

要点提示（以简报为准）：这是一个用布劳威尔树定义大序数的 Agda 项目（--safe --without-K，无公设、无洞、无停机或正性编译指示）。任务是一次探查，结论可以是否定的：规范 Ω 树的读回、以及它的折叠输出的读回，沿层号路径（特别是孩子下标的右加法）有没有字面的单调。分 B1（读回）、B2（折叠输出，朝第 0 层与朝私有层）、B3（若正面，写出可作块的合法性条件的陈述）。每条交定理、或闭实例上的事实、或带最小失败实例的障碍；否定要落在规范实例上。基目录 <实验目录>/w5build 只读；只在工作目录 <实验目录>/kq 里写，文件前缀 KQ；改块的试验只在自己目录的拷贝里做；不改仓库；同时只跑一个 agda，堆上限 6G；不提交。最终消息就是回报原文，中文，按公共约束里的回报格式，区分编译定理、有限测试与判断。

## 回报原文

### KQ 回报: 规范 Ω 树及其折叠沿层号路径的字面单调

#### 结论
- **B1 读回: 右加法下正面, 层号的序下否定.**
  - 现行块: 唯一卡点是 Ω̂ 的每一单步多出一层 `zero ⊕`. 首枝路径 FB (每步进第 0 个孩子) 与读回的右加法都无条件成立.
  - 改块之后 (`zero ⊕ b = b` 定义地成立): 对一切层号 k 与一切 x y : Tr k, 有 `Ω̂ (↑ k x) ⊑ Ω̂ (↑ k (x + y))`. lev 与塔的孩子族是推论.
  - 层号的序 a ≤ b **不**给 Ω̂ a ⊑ Ω̂ b. ℕ 极限层号从第 1 个成员起就失败, 改块之后也失败. 有编译否定: `lev 1 ⋢ lev ω`, 而 `lev 1 ⊑ lev (1+ω)` 成立.
  - 审查的纸面判断 "两种单步数学上成立, 只卡在 zero ⊕" 只对后继步和 ℕ 极限的第 0 个成员对. 对第 n ≥ 1 个成员, 字面路径不存在.
- **B2 折叠输出: 只在累加之前的单项上字面单调.**
  - 链结点 (`node⁺ nothing` → `limc⁺`) 的累加破坏单调.
  - 朝私有层: 规范实例 c′ = 1, d = 0, e = 1 有编译否定.
  - 朝第 0 层 (c ≥ 1 的后继、ℕ 极限第 n ≥ 1 个成员): 没证出, 也没否定, 记 "未走通".
- **B3:** 写出了候选条件 `RMono`, 并编译了它的自持性. 塔满足它; Ω̂ 与 a ⊕ 保持它, 其中 Ω̂ 的保持只在改过的块里. 折叠保持它缺的那条引理, 在 B2(b) 的实例上被否定.

#### 1. 文件
目录: <实验目录>/kq. 日志同名 `.log`. 下表是最终一轮编译.

| 文件 | 行数 | 退出码 | 内容 |
|---|---|---|---|
| KQBlock.agda | 296 | 0 | W4Block 的拷贝, 改了 `_⊕_` 与 `lift`, 新增 `z⊑` |
| KQOps.agda | 107 | 0 | 未改, 只换模块名与导入 |
| KQPath.agda | 181 | 0 | 改了 `⊕⊑`, `Ok⊕`, `OkO⊕`, 新增 `OkO0` |
| KQFold.agda | 443 | 0 | 未改, 只换模块名与导入 |
| KQLev.agda | 312 | 0 | 改过的块上的 B1 与 B3 |
| KQRead.agda | 155 | 0 | 现行块上的 B1, 及 FB 一族 |
| KQFail1.agda | 12 | 42 | 预期失败, 取首个错误原文 |
| KQFail2.agda | 12 | 42 | 预期失败, 取首个错误原文 |
| KQOut.agda | 195 | 0 | 现行块上的 B2 |
| KQOutNeg.agda | 142 | 0 | 现行块上 B2(b) 的否定 |

- 改前的首个错误: KQBlock-first.log, KQPath-first.log.
- 我写的六个文件 (KQLev, KQRead, KQFail1, KQFail2, KQOut, KQOutNeg) 里没有 postulate, 洞, TERMINATING/NO_POSITIVITY 编译指示, 也没有函数外延. 拷贝的四个模块与 W4 原文相比, 只多了上表列出的改动.
- 日志里只有 UnsupportedIndexedMatch 警告 (仓库的库文件里本来带 -W noUnsupportedIndexedMatch).

#### 2. 编译定理 (陈述逐字照抄)

记号: `Ω̂ a = ↑ a (proj₁ (Ωt a))`, 即规范 Ω 树的读回. `FB` 是首枝路径. `P0` 是在 ℕ 极限结点上只走第 0 个成员的路径 (其余结点任意).

##### B1, 现行块 (KQRead)

**无条件 (首枝路径):**
- `↑-FB+ : (k : L) (x y : Tr k) → FB (↑ k x) (↑ k (x + y))`. 读回对右加法给出首枝路径.
- `Eh-first : (A : RA) (R : FBR A) {m : L} (κ : Ctx A m) (x : Tr m) (F : OpA A) (u : Car A) → Rf R (proj₁ F u) (proj₁ (Eh A κ x F) u)`. 在一切阶的结果代数上, F u 都在 Eh x F u 的首枝上.
- `tw-RMono : (n : ℕ) (c d : Tr (tw n)) → P0 (tw n ⊕ ↑ (tw n) c) (tw n ⊕ ↑ (tw n) (c + d))`. 塔的孩子族满足候选条件.

**形状 (对变量都是 refl):**
- `Ω̂-sS : (h : ⊤ → L) → Ω̂ (nd sS h) ≡ nd (sΩ (h tt)) (λ z → nd sS (λ _ → zero ⊕ ↑ (h tt) z))`
- `Ω̂-sΩ : (k : L) (h : Tr k → L) → Ω̂ (nd (sΩ k) h) ≡ nd (sΩ k) (λ c → zero ⊕ Ω̂ (h c))`
- `Ω̂-sL₀ : (g : ℕ → L) → memL (Ω̂ (nd sL g)) 0 ≡ zero ⊕ Ω̂ (g 0)`
- `Ω̂-sL : (g : ℕ → L) (n : ℕ) → memL (Ω̂ (nd sL g)) (suc n) ≡ memL (Ω̂ (nd sL g)) n ⊕ Ω̂ (g (suc n))`
- `lev-suc : (c : Tr zero) → lev (suc c) ≡ nd (sΩ (h₁ c)) (λ z → nd sS (λ _ → zero ⊕ (zero ⊕ ↑ (h₁ c) z)))`. 在孩子 `Ωt (h₁ c)` 上看到的是 `zero ⊕ lev c`, 不是 `lev c`.

**有限测试:** `lev01 : lev zero ⊑ lev (suc zero)`. c = 0 时 `zero ⊕` 定义地消掉, 自然路径通过.

**条件定理, 条件 `Z : (x : L) → x ⊑ zero ⊕ x`:**
- `Cond.Ω̂-+ : (k : L) (x y : Tr k) → Ω̂ (↑ k x) ⊑ Ω̂ (↑ k (x + y))`
- `Cond.lev-mono : (c d : Tr zero) → lev c ⊑ lev (c + d)`

Z 只用在 Ω̂ 的三种单步上. 关于 Z 是否可满足, 我的判断 (未编译): Z 可由函数外延推出, 因为 `zero ⊕ x` 外延地等于 x; 不用函数外延, 我认为 Z 构造不出来. Z 在 `x = lev 0` 上定义地成立.

##### B1, 改过的块 (KQLev)

**单步:**
- `suc-step : (h : ⊤ → L) → Ω̂ (h tt) ⊑ Ω̂ (nd sS h)`
- `lim-step₀ : (g : ℕ → L) → Ω̂ (g 0) ⊑ Ω̂ (nd sL g)`
- `Ω-step : (k : L) (h : Tr k → L) (c : Tr k) → Ω̂ (h c) ⊑ Ω̂ (nd (sΩ k) h)`
- `lim-cum : (g : ℕ → L) (n : ℕ) → memL (Ω̂ (nd sL g)) (suc n) ≡ memL (Ω̂ (nd sL g)) n ⊕ Ω̂ (g (suc n))`. ℕ 极限层号的后续成员是累加.

**主定理:**
- `FB→Ω̂ : ∀ {j ℓ} → FB j ℓ → Ω̂ j ⊑ Ω̂ ℓ`
- `Ω̂-+ : (k : L) (x y : Tr k) → Ω̂ (↑ k x) ⊑ Ω̂ (↑ k (x + y))`
- `lev-mono : (c d : Tr zero) → lev c ⊑ lev (c + d)`. 这就是 B1(a); `lev-mono≤` 是它的 ≤ 版.
- `tw-Ω̂ : (n : ℕ) (c d : Tr (tw n)) → Ω̂ (hN n c) ⊑ Ω̂ (hN n (c + d))`. 对一切塔高成立.

**否定:**
- `lvl-path : h₁ (suc zero) ≤ h₁ ω`
- `right-ok : lev (suc zero) ⊑ lev (suc zero + ω)`
- `no-lim-member : lev (suc zero) ⊑ lev ω → ⊥`

否定的不变式: lev ω 的一切 Ω 形子项的首枝深度 zd ≥ 3, 而 `zd (lev 1) ≡ 2` (refl).

**B3 的自持性:**
- `Ω̂-P0 : ∀ {j ℓ} → P0 j ℓ → P0 (Ω̂ j) (Ω̂ ℓ)`
- `RMono k h = (c d : Tr k) → P0 (h c) (h (c + d))`
- `tw-RMono : (n : ℕ) → RMono (tw n) (hN n)`
- `Ω̂-RMono : (k : L) (h : Tr k → L) → RMono k h → RMono k (λ c → Ω̂ (h c))`
- `⊕-RMono : (a k : L) (h : Tr k → L) → RMono k h → RMono k (λ c → a ⊕ h c)`
- `lev-RMono : RMono zero lev`
- `Qr-RMono : (a₁ a₂ a₃ : L) → RMono zero (λ c → a₁ ⊕ (a₂ ⊕ (a₃ ⊕ lev c)))`. 这是 W5Trace 里层号 Qr 的孩子族形状; a₁ a₂ a₃ 取任意层号, 没有代入运行里的具体项.

##### B2(a), 现行块, 朝第 0 层 (KQOut; `st` 即 WVOne.st)
- `st-def : (c : Tr zero) → st c ≡ proj₁ (ψ (h₁ c) (oc c) (Bs c) zero (ws c) β₀ (Ωc c))` (refl)
- `st-suc : (c : Tr zero) (n : ℕ) → memT (st (suc c)) n ≡ cum (λ m → proj₁ (Gs c (zS c m))) n` (refl). st (c+1) 是链上各项的累加.
- `st-sum : (c : Tr zero) → zero ⊢ st c ◃ proj₁ (Gs c (zS c 1))`. 正面, 对一切 c: st c 字面地低于第 1 个累加项 (累加之前).
- `st-0 : zero ⊢ st zero ◃ st (suc zero)`
- `st-lim₀ : (f : ℕ → Tr zero) (a : (n : ℕ) → zero ⊢ f n ◃ f (suc n)) → zero ⊢ st (f 0) ◃ st (lim f a)`
- `st-lim` (refl, 形状): ℕ 极限的第 n+1 个成员是 Ωc (f (n+1)) 的折叠. 它的底是第 n 个成员, 状态按前缀 `cum (Fseg f a) n` 平移; st (f (n+1)) 的底则是 `Ωt zero`, 状态是 `Bs`.

##### B2(b), 现行块, 朝私有层 (KQOut)
设定:
- `G c′ d = ψ (h₁ (c′ + d)) (oc (c′ + d)) σ₀ (h₁ c′) (steer c′ d) (Ωt (h₁ c′)) (Ωc (c′ + d))`.
- `steer` 与 R15 的 `steerPath 0 c′ self d` 同一个正规形.
- 状态固定为 `σ₀ i u = Ωt i`, 底固定为 `Ωt j`.

定理:
- `G1-mem : (c′ : Tr zero) (m : ℕ) → memG (proj₁ (G c′ (suc zero))) m ≡ cum (λ n → proj₁ (Sb c′ (zz c′ n))) m` (refl, 对一切 c′)
- `G0-read : (c′ : Tr zero) → NZ c′ → ↑ (h₁ c′) (proj₁ (G c′ zero)) ≡ proj₁ (Eh AL tt (Ωc c′) (opR (Lβ c′))) (Lβ c′)`
- `G1-read₀ : (c′ : Tr zero) → NZ c′ → memL (↑ (h₁ c′) (proj₁ (G c′ (suc zero)))) 0 ≡ proj₁ (Eh AL {h₁ c′} tt (suc zero) (opR (Lβ c′))) (Lβ c′)`
- `G1-read : (c′ : Tr zero) → NZ c′ → (m : ℕ) → memL (↑ (h₁ c′) (proj₁ (G c′ (suc zero)))) (suc m) ≡ proj₁ (Eh AL tt (suc (zz c′ (suc m))) (opR (Lβ c′))) (↑ (h₁ c′) (cum (λ n → proj₁ (Sb c′ (zz c′ n))) m + Ωc c′))`
  - 读法: G 1 读回的第 m+1 个成员从 `↑ (前缀 + Ωt j)` 起迭代, 不从 Lβ 起.
- `sum01 : (c′ : Tr zero) → NZ c′ → ↑ (h₁ c′) (proj₁ (G c′ zero)) ⊑ ↑ (h₁ c′) (proj₁ (Sb c′ (zz c′ 1)))`. 正面: G 0 的读回在 G 1 第 1 个累加项 (累加之前) 的读回的首枝上.
- `G2-mem : (c′ d : Tr zero) (m : ℕ) → memG (proj₁ (G c′ (suc (suc d)))) m ≡ cum (λ n → proj₁ (Tm c′ d n)) m` (refl)
- `sumD : (c′ d : Tr zero) → h₁ c′ ⊢ proj₁ (G c′ (suc d)) ◃ proj₁ (Tm c′ d 1)`. 对一切 c′ 与 d: G (d+1) 是 G (d+2) 第 1 个累加项里迭代子 E 的起点.
- `sumD-read`: sumD 的读回版 (⊑).
- 闭实例 `i01-1`, `i01-2`, `i01-ω`, `i12-1`, `i12-2`, `i12-ω`, `i23-1`, `i23-ω`: 即 c′ = 1, 2, ω, d = 0, 1 (e = 1) 时上面两条定理的代入, 路径是显式的.

##### B2(b) 的否定 (KQOutNeg, c′ = 1, d = 0, e = 1)
- `A-shape : A ≡ nd (sΩ zero) (λ c → nd sL (λ n → iter (proj₁ (Eh AL tt c (opR (Lβ (suc zero))))) (Lβ (suc zero)) (suc n)))`
- `zdA : zd A ≡ 6`
- `no-01 : A ⊑ Bt → ⊥`. 其中 `A = ↑ j₁ (proj₁ (G (suc zero) zero))`, `Bt = ↑ j₁ (proj₁ (G (suc zero) (suc zero)))`.

不变式经块里已有的 `EP`/`PS` 机制证明: Bt 的一切 "第 0 个孩子是 ℕ 极限的 Ω 形子项" 首枝深度 ≥ 7. Ω 形与 ℕ 极限结点、"右边接上 L₁" 都保持它.

#### 3. 没做成的

**B1, 现行块.** 首个错误原文:
- 一般的后继一步 (KQFail1.log): `KQFail1.agda:12.46-50: error: [UnequalTerms] (↑ (h₁ c) (proj₁ (Ωt (zero ⊕ ↑ zero c)))) != (↑ (nd sS (λ c₁ → zero ⊕ ↑ zero c)) zero ⊕ ↑ (zero ⊕ ↑ zero c) (proj₁ (Ωt (zero ⊕ ↑ zero c))))`
- 最小闭实例 c = 1 (KQFail2.log): `KQFail2.agda:12.50-54: error: [UnequalTerms] (↑ (zero ⊕ ↑ zero zero) c) != (↑ (nd sS (λ c₁ → zero ⊕ ↑ zero zero)) zero ⊕ ↑ (zero ⊕ ↑ zero zero) c)`

**改块的结果.**
- (i) 引理随之可证, 而且推广到 `Ω̂-+` 与 `tw-Ω̂`.
- (ii) 各拷贝改动后的编译情况:
  - KQBlock 本身先坏: `KQBlock.agda:155.19-23: error: [UnequalTerms] a != a ⊕ zero of type L when checking that the expression self has type Pth b a (a ⊕ zero)`. 原因是 `lift`, 改成先对左参数分情形后通过.
  - KQOps 不改即通过.
  - KQPath 首个错误: `KQPath.agda:24.18-31: error: [UnequalTerms] nd _s_35 _h_36 != a ⊕ nd s h of type L` (在 `⊕⊑`). 把 `⊕⊑`, `Ok⊕`, `OkO⊕` 改成先对左参数分情形, 另加 `OkO0 : OkO zero b → Ok b`, 之后通过.
  - KQFold 不改即通过.
- 代价 (编译事实): 改块之后, `a ⊕ zero = a` 与 `a ⊕ nd s h = …` 对变量 a 不再定义地成立.
- 没拷贝也没检查的: W4Val, W4View, 以及 W5/K 系的模块. 改块之后的值的定理是否仍然成立, 没有检查.

**B2(a), c ≥ 1 的后继与 ℕ 极限第 n ≥ 1 个成员: 未走通.** 没有证出, 也没有否定.
- 一般证明里缺的不变式: `Σ t , (st c ≡ proj₁ (Gs c (zS c 0)) + t) × (zero ⊢ t ◃ proj₁ (Gs c (zS c 1)))`. 有了它, 由 `+-mono` 即得 `st c ◃ cum 1 ◃ st (c+1)`.
- 判断: 前半要 `+` 的结合律定义地成立. 而 `cum` 是左嵌套的, 结合律对卡住的项不定义地成立; 命题地要函数外延, 还要 lim 里步进证据的对齐.
- ℕ 极限成员是换底换状态 (见 `st-lim`). 要的是 "左参数/底的字面单调", 我判断它不成立, 但没有编译反例.
- 判断: 在现行块里, 这两件事不用函数外延既证不出也否定不了, 所以记 "未走通", 不记 "否定".

**B2(b), 其余闭实例.**
- c′ = 2, ω 及 d = 1 → 2 没有编译否定.
- `G1-read` 与 `G2-mem` 对一切 c′, d 给出同样的累加结构. 判断: 同一机制.
- 若状态取 R15 的 `λ i u → S i (inc d u)` 且 S 抽象, 则 G d 与 G (d+e) 读的是 S 在不同路径上的值, 无从谈字面关系 (判断).

**B3 (判断, 未编译).**
- 候选的块合法性条件: 在 `OkS (sΩ k) h` 里加 `RMono k h`. 形式必须是右加法加 P0, 不能写成 ≤ 或 ⊑, 否则 `no-lim-member` 就是反例.
- 已编译的部分: 塔满足 (`tw-RMono`, 两个块都成立); 被 Ω̂ 与 a ⊕ 保持 (Ω̂ 只在改过的块里).
- 折叠保持它还缺一条引理: 链结点输出 `limc⁺` 的读回上, 每一项要 P0 地高于前一个分支的输出. 这等于 "P0 (↑ j x) (↑ j (y + x))" (左加法), 在 `no-01` 的实例上不成立.
- 所以要么把链结点改成非累加的 ℕ 极限 (相邻项的步进证据用 `sumD`/`st-sum` 型的引理), 要么另证 "累加项支配". 改定义不在本任务范围内, 我没有做.

#### 4. 反例 (都是编译过的)
- `no-lim-member : lev (suc zero) ⊑ lev ω → ⊥`. 规范读回, 塔第 1 项的孩子; 改过的块里, `h₁ 1 ≤ h₁ ω` 与 `lev 1 ⊑ lev (1+ω)` 同时成立.
- `no-01 : A ⊑ Bt → ⊥`. 现行块, 规范实例 c′ = 1, d = 0, e = 1. 形状见 `A-shape`, `zdA`, `G1-read₀`, `G1-read`.
