# 换基的律接进整体接口（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-17 02:46 至 03:20 |
| 工具调用 / agda 编译 (粗数) | 63 / 18 |
| token (usage 字段，按消息去重) | 输出 205585；新写入缓存的输入 368758；读缓存的输入 13646600；其余输入 114 |
| 写过的仓库文件 | `YiBLFold.lagda.md`, `YiBLIface.lagda.md`, `YiBLNeg.lagda.md`, `YiBLToy.lagda.md` |
| 文件前缀 | `YiBL` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 4 件全部退出 0，禁用构造 0，四件导入闭包干净；换基律 RebAt 接进同一套充分性（SuffR.keepAll、sys→low），旧回退律是特例（fall→emb、out→outR）；换基折叠满足树一侧全部律（rebᴮ、keepᴮ 等），其上的 LowKeep 只剩参照一侧的出口（lowᴮ、lowᵗ）；目标槽位的副本由 lift 实填（ev-cp、nodeE-cp）；配对否定 cur-¬RebAt、up-¬lw、up-¬cpE；主系统孩子槽位仍不保留（main-noEv） |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b76/YiBL.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。在仓库根目录 `<仓库>` 下工作。只新建你前缀的文件，不改任何已有文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

### 回报：YiBL（换基的律接进整体接口；不读记号；摆脱侧）

#### 1. 判决

**对纲领与目标意味着什么**
- 纲领：四个新文件都不读记号（`importclosure.py` 对四个模块的禁用表命中都是 0），没有改树、折叠或合法性（`YiBSFold`、`YiRBSib` 原样导入，只新建系统、律和实例），没有公设、洞或停机指示。
- 目标（树自足）：换基行现在有了一条树一侧的律 `RebAt`，并接进了 `YiFIIface` 的同一套充分性。`YiFIIface` 原来的回退律是它的特例，由 `fall→emb`、`out→outR` 编译核对。律里被问到的槽位，证据来自树自己的字面路径 `lift j b`（全是 `inu`，即一致目标）。律对一切孩子 c 一致，只出现一个孩子下标，不比较两个孩子。这算 "树的语言" 第 2 层（充分侧判据）上的一条。
- 限度（判断）："替身支配原材料" 只写成了参照一侧的出口（接口关系 R 加 Le），没有树一侧的写法。原因是替身与原材料在不同层号上，第一位置序比较不了；树一侧要搬运就需要反变的换型（V149 的说法，我没有重核）。
- V50 在换基下的样子：
  - 编译定理：换基分支的保持只用替身，不对原材料 y 递归，所以原材料的槽位不再被问到。被问的是换基层号 `j ⊕ b` 的槽位。目标层槽位的副本上，证据、目标槽位和分支换型都由 `lift` 实填（`ev-cp`、`nodeE-cp`），只剩参照一侧三项。
  - 编译定理：替身自己孩子层号上的槽位不保留（`top-noEv`），出口在那里只能走链。
  - 编译定理：主系统 ℓ 层孩子槽位上的结点照旧不保留（`main-noEv`，即 `YiFINeg.kp-drop`）。所以 V50 的 "结点" 一半不因换基改变。

**各步到哪一步**
- 第 0 步（写律）：完成。第一个临时文件 `YiBLLaw0.agda` 在开工约 15 分钟时一次编译通过。
- 第 1 步（充分性）：完成。
- 第 2 步（实例化）：完成。范围比要求的宽：一切带 `Schema` 证据、`route` 落在地板之上的 Ω 形状层号。塔的每一项都是实例（`Tower`）；第 1 项目标取 `h₁ d`（d 非零）时，`route` 已由 `route-tw1` 填好（`Tw1`）。
- 第 3 步（配对否定）：完成。
- 第 4 步（律的清单与翻译账）：见本节末尾。
- 另加了一个模型文件 `YiBLToy`，说明前提可以同时满足（AGENTS "前提要可满足"）。

**问题表**

| # | 问题 | 位置 | 档 |
|---|---|---|---|
| 1 | 换基律能写进 `YiFIIface` 的框架 | `YiBLIface.RebAt`、`EmbLaw`、`EmbOut`、`OutR` | 编译定理（类型） |
| 2 | 律带公共上界：律里只有一个孩子下标 c；(j, 换基层号) 带字面路径 `lw`；(q, `cp q`) 是字面副本 | `RebAt` 逐字段核 | 判断 |
| 2′ | 出口里 "替身支配原材料" 那一条，比较的是 (`chL a c`, `Lr c x`) 两个层号上的参照项；抽象接口里这一对没有字面公共上界。实例里的字面成分是 `route` 给出的 `u : floor S ≤ j` 和共同的偏移 | `OutR.embE` 第二分量 | 判断 |
| 3 | 保留律 + 嵌入律 + 出口 + 辅助系统上的保持 ⇒ keepAll / LowKeep | `SuffR.keepAll`、`sys→low`、`SuffRA` | 编译定理 |
| 4 | 回退律是每行都回退的嵌入律；`Out` 给出 `OutR` | `fall→emb`、`out→outR` | 编译定理 |
| 5 | 前提可同时满足，且换基行非空 | `YiBLToy.toy-lowᴿ` | 编译定理（模型） |
| 6 | `YiBSFold` 根状态满足保留律与换基律；辅助系统满足保留律、回退律、单调 | `YiBLFold` 的 `keepᴮ`、`rebᴮ`、`keepᴬ`、`fallᴬ`、`monoᴬ`、`monoᴮ` | 编译定理 |
| 7 | `YiBSFold` 根状态上的 LowKeep 只剩参照一侧 | `lowᴮ`、`lowᵗ`、`Tw1` | 编译定理（条件见定理表） |
| 8 | `Out.nodeE` 在换基下要什么：副本一支由 `lift` 实填；替身自己的槽位与主系统孩子槽位不保留 | `nodeE-cp`、`top-noEv`、`main-noEv` | 编译定理 |
| 9 | 现行回退（`DX.Fold K false` 与主线 `YiTBRow.ψ`）违反 `reb` | `YiBLNeg` 的 `cur-¬RebAt`、`fb-¬reb`、`main-¬reb`、`sub-ω`、`fb-¬rebᴮ`、`main-¬rebᴮ` | 编译定理 |
| 10 | 上折回退违反 `lw`（对任何 K）与 `cpE`（K = `kp`） | `up-¬lw`、`lf-noEv`、`up-¬cpE` | 编译定理 |
| 11 | 主系统的 `OutR` 与辅助系统的 `Out` 实填 | — | 未做（不在本路范围） |
| 12 | 走链一支的树一侧条件 `∀ k → Φ s (g (z k)) ⊴ Φ s (nd p g)`：结点不保留时像是部分和极限（`node⁺ nothing = limc⁺`），k ≥ 1 处第一位置序一般不给出 F k ⊴ F0 + … + Fk。这是 `YiFIIface.Out` 形状的问题，不专属换基 | — | 判断（未编译） |
| 13 | 替身支配原材料的树一侧写法（跨层搬运） | — | 判断（V149，未重核） |

**律的清单**（标 "新" 的是本路新增，其余来自 `YiFIIface` / `YiAbsGIface`）
- 树一侧：
  - 𝒮.`KeepLaw`、𝒮.`Monoˢ`；
  - `EmbLaw.row`：每个状态的嵌入行是 `FallAt ⊎ RebAt`（新）；
  - `FallAt`（step、fall：`FallLaw` 落到一个状态上）；
  - `RebAt`（新）：`Lr`、`Sr`、`sub`、`reb`、`lw`、`cp`、`cpE`、`cpS`；
  - 𝒜.`KeepLaw`、𝒜.`FallLaw`、𝒜.`Monoˢ`；
  - 各层 `WfL`。
- 参照一侧：
  - `OutR`：`zeroE`、`succE`、`limE`、`leE`、`nodeE`，与 `Out` 逐字相同；
  - `embE`：回退行等于 `upE`；换基行是两条的积，即上下文交给替身状态（形状同 `upE`）× 支配（`R (chL a c) u (chT y) → Σ u″, R (Lr c x) u″ (sub c x) × Le (t ⊕ u) (t ⊕ u″)`，新）；
  - 𝒜 的 `Out`；
  - 各层 `Gen⁺ Le`，以及 `Weak`、`Lim`、`Node`。
- 在 `YiBLFold` 里实填的：树一侧全部（`lw = lift`；`cp` 沿第一孩子路径 `lf`；`cpE = ev-cp`；`cpS = refl`），以及辅助 `nodeE` 副本一支的树一侧部分。参照一侧一项都没有实填，全部是前提。

**翻译账**
- 新定义：没有新的树、折叠或合法性。新增的是抽象记录（`RebAt`、`FallAt`、`EmbLaw`、`EmbOut`、`OutR`）、两个系统的包装（`Stᴬ`、`Stᴮ`、`Evᴬ`、`Evᴮ`），以及副本 `Lf`、`cp`。新字段的形状都不读自记号的基本列。
- 由树的要求逼出的：
  - `reb`：嵌入行的输出必须不低于某个已知能保持的像；
  - `lw` 与 `cp`/`cpE`/`cpS`：辅助系统的结点要证据，`lift` 恰好给出；
  - `auxK`：换基层号不是孩子，不能进 `WfL` 递归。
- 脚手架：`route` 的等式前提（来自 `YiBSFold` 的派发），以及 `cW-eq`、`fall-self`、`dn₁`、`dnD`（处理下标）。`Lf` 把 `YiRKCell.keep-lift` 推广到任意一条到叶子的孩子路径。
- 换基行本身是已有的定义，来源按 `YiBSBase` 文首是 "Review18 的 seen 形状"；Review18 是否受记号引导，我没有核。
- 加深与信息（判断）：
  - 没有出现加深翻译的标志：字段不读自基本列；闭包定理新增的前提只有一种，即参照一侧的支配出口（`auxK` 由 `Suff` 推出）；不用 `Lab` 验收。
  - 有提供信息的标志：一步的、一致的充分性定理，并说出了新用到的字段（`reb`、`cpE`）；用否定定理划出了不能有的字段（`cur-¬RebAt` 对 `reb`，`up-¬lw` 对 `lw`，`up-¬cpE` 对 `cpE`）。

#### 2. 文件表

| 文件 | 代码行（非空） | 总行 | 冷编退出码 |
|---|---|---|---|
| `probes/OCF/Lean/YiBLIface.lagda.md` | 121 | 175 | 0（3 秒） |
| `probes/OCF/Lean/YiBLFold.lagda.md` | 236 | 356 | 0（3 秒） |
| `probes/OCF/Lean/YiBLNeg.lagda.md` | 92 | 143 | 0（2 秒） |
| `probes/OCF/Lean/YiBLToy.lagda.md` | 114 | 159 | 0（2 秒） |

- 冷编做法：删掉自己的四个 `.agdai`，依赖保持热，按依赖顺序逐个编译，堆上限 6G。每个日志只有自己模块的一行 `Checking`。
- 改完最后一处文首措辞后，又删接口重编了一遍，四个仍为 0。
- 检索：禁用构造、`cubical`、本机路径都是 0。
- 选项行都是 `--safe --without-K --lossy-unification`。

#### 3. 定理表

**YiBLIface**（编译定理，无前提；律与出口是记录）

- `RebAt`：
  ```
  record RebAt {a : Lv} (s : S.St a) : Set where
    field
      Lr  : Ch a → Tr a → Lv
      Sr  : (c : Ch a) (x : Tr a) → A.St (Lr c x)
      sub : (c : Ch a) (x : Tr a) → Tr (Lr c x)
      reb : (c : Ch a) (x : Tr a) (y : ChT a c) → A.Φ (Sr c x) (sub c x) ⊴ S.Φ s (up x c y)
      lw  : (c : Ch a) (x : Tr a) → j ⊑ Lr c x
      cp  : (c : Ch a) (x : Tr a) → Sl j → Sl (Lr c x)
      cpE : (c : Ch a) (x : Tr a) (q : Sl j) → A.Ev (Sr c x) (cp c x q)
      cpS : (c : Ch a) (x : Tr a) (q : Sl j) → KA.slot (Sr c x) (cp c x q) (cpE c x q) ≡ q
  ```
  白话：嵌入的像不低于替身在辅助系统里的像；目标是换基层号的字面前缀；目标槽位的副本带保留证据，并落回原槽位。
- `EmbLaw`：`row : ∀ {a} (s : S.St a) → FallAt s ⊎ RebAt s`。白话：每个状态的嵌入行要么是回退行，要么是换基行。
- `OutR.embE`：`∀ {a} (s : S.St a) K → S.Bdˢ s K → EmbOut Le s K (row s)`，其中换基分支为
  ```
  ((c : Ch a) → ∀ {t x} → R a t x → S.Q s K t x
      → Σ A.Cxt λ K″ → A.Bdˢ (RebAt.Sr r c x) K″ × (∀ u → A.ap K″ u ≡ S.ap K (t ⊕ u)))
  × ((c : Ch a) → ∀ {t u x} (y : ChT a c) → R a t x → R (chL a c) u (chT a c y)
      → Σ T λ u″ → R (RebAt.Lr r c x) u″ (RebAt.sub r c x) × Le (t ⊕ u) (t ⊕ u″))
  ```
  白话：上下文交给替身的状态；原材料下面的参照项换成替身下面的参照项。
- `SuffR.keepAll`（前提 `Le wk lm nod mono 𝓀 ex auxK gen`）：`∀ {a} → WfL a → (s : S.St a) (K : S.Cxt) → S.Bdˢ s K → ∀ {t x} → R a t x → S.Q s K t x`。白话：每个状态上保持成立。
- `SuffR.sys→low`：`∀ {ℓ} → WfL ℓ → (s : S.St ℓ) (K : S.Cxt) → S.Bdˢ s K → (b : Bs ℓ) (w : j ⊑ ℓ) (β : Bt j) (Kc : Cx ℓ j) → (∀ x → S.Φ s x ≡ ψ ℓ b j w β x) → (∀ t → S.ap K t ≡ app Kc t) → ∀ {a x} → R ℓ a x → R j (app Kc a) (ψ ℓ b j w β x)`。白话：这一点上的 LowKeep。
- `SuffRA`（前提 `Le wk lm nod mono 𝓀 ex monoᴬ 𝒻ᴬ exᴬ wfAll gen`）：`auxK` 由 `A.Suff.keepAll` 给出，并公开 `SuffR` 的两条定理。
- `fall→emb : S.FallLaw → EmbLaw`；`out→outR : ∀ {Le 𝓀 𝒻} → S.Out Le 𝓀 𝒻 → OutR (fall→emb 𝒻) Le 𝓀`。白话：旧接口是新接口的特例。

**YiBLFold**（编译定理）

- `keepᴬ′`：`Ω (slotᴬ s p e) (λ c → proj₁ (Φᴬ s (g (mvcᴬ s p e c)))) ⊴ᵗ proj₁ (Φᴬ s (Ω p g))`。辅助系统的保留律。
- `fallᴬ′`：`proj₁ (Φᴬ (stepᴬ s c x) (chTᵍ a c y)) ⊴ᵗ proj₁ (Φᴬ s (upᵍ x c y))`。辅助系统的回退律。
- `monoᴬ′`、`monoᴮ′`：单调。
- `ev-cp`：`(b : L) (l : Lf b) (o : Ok (j ⊕ b)) (q : Pos j) → Σ (Br j q → Br (j ⊕ b) (cp b l q)) λ cv → Σ (cv (fromBr j q zero) ≡ fromBr (j ⊕ b) (cp b l q) zero) λ e → kp (j ⊕ b) o (cp b l q) (lift j b) ≡ just (q , cv , e)`。白话：目标槽位的副本沿 `lift` 保留，落回 q。
- `top-noEv`：`∀ s h (o : Ok (j ⊕ nd s h)) B β (c : Ch s) → Evᴬ (rbs (nd s h) o B β) (inj₂ (c , inj₁ tt)) → ⊥`。替身自己孩子层号的槽位不保留。
- `main-noEv`：`∀ β (c : Tr k) (t : Pos⁼ (h c)) → Evᴮ (rt β) (inj₂ (c , t)) → ⊥`。主系统孩子槽位不保留。
- `row-reb`：`∀ β x c y e → BS.ψ ℓ o r B j w β (up x c y e) ≡ seen S j oj u (BS.ψ ℓ o r B j w β x) c ⊞ BS.ψ (h c) (proj₂ o c) (rc c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y`。白话：`route` 落在地板之上时，行的形状对一切 c 相同。
- `rebᴮ′`：`∀ β c x (y : ChTᵍ ℓ c) → proj₁ (Φᴬ (Srᴮ β c x) (subᴮ c x)) ⊴ᵗ proj₁ (Φᴮ (rt β) (upᵍ x c y))`。白话：替身的像严格低于行的输出。
- `rebᴮ : ∀ {a} (s : Stᴮ a) → RebAt sysᴮ sysᴬ keepᴬ s`；`embᴮ : EmbLaw sysᴮ sysᴬ keepᴬ`。
- `lowᴮ`：
  ```
  (Le : Ref.T 𝕋 → Ref.T 𝕋 → Set) (wk : Weak) (lm : Lim) (nod : Node)
    → OutR sysᴮ sysᴬ keepᴬ embᴮ Le keepᴮ → Sys.Out sysᴬ Le keepᴬ fallᴬ → (∀ a → Gen⁺ Le a)
    → (β : Tr⁺ j) (K₀ : Cxtᴮ) → Bdᴮ (rt β) K₀ → (Kc : Cx ℓ j) → (∀ t → apᴮ K₀ t ≡ app Kc t)
    → ∀ {a x} → Rᵍ ℓ a x → Rᵍ j (app Kc a) (proj₁ (BS.ψ ℓ o r B j w β x))
  ```
  条件定理，前提全在参照一侧。
- `lowᵗ`：同上，层号取 `tw (suc n)`，结论是 `BS.ψ (tw (suc n)) (Ok-tw (suc n)) (rb-tw (suc n)) …`。
- `rb-tw≡ : (n : ℕ) → rb-tw (suc n) ≡ (just (Sₙ n) , rcₙ n)`（`refl`）。
- `route-tw1 : ∀ {d} → NZ d → route (Sₙ 0) (h₁ d) d self ≡ inj₂ (lift zero (↑ zero d))`。
- `nodeE-cp`：给定 `CΩ (apᴬ K t) κ`、代入交换、`Nu j q κ`，就给出辅助系统 `nodeE` 保留一支的全部五项（证据、两条参照项照抄、`Nu`、分支搬运 `trR`）。白话：副本一支的树一侧部分由 `lift` 实填。

**YiBLNeg**（编译定理）

- `cur-¬RebAt`：`∀ {j} (𝒮 𝒜 : Sys j) (𝓀ᴬ : Sys.KeepLaw 𝒜) {a} (s : Sys.St 𝒮 a) (r : RebAt 𝒮 𝒜 𝓀ᴬ s) (c : CH a) (y : ChTᵍ a c) → NF (Sys.Φ 𝒮 s (upᵍ zero c y)) → (NF (Sys.Φ 𝒜 (RebAt.Sr r c zero) (RebAt.sub r c zero)) → ⊥) → ⊥`。白话：嵌入输出不含结点的状态，没有替身含结点的换基行。
- `fb-¬reb`、`main-¬reb`：现行回退与主线在前提为零、底值不含结点时，输出不低于任何含结点的树。
- `sub-ω`：`NF (proj₁ (Aux.Φᴬ j₁ (Aux.rbs (↑ zero ωᶜ) o′ B′ β) (proj₁ (Ωt (j₁ ⊕ ↑ zero ωᶜ))))) → ⊥`。塔第 1 项、目标 `h₁ 1`、孩子 ω 处，`YiBSFold` 的替身含结点。
- `fb-¬rebᴮ`、`main-¬rebᴮ`：在同一格上，两个现行折叠都不能以 `YiBSFold` 的替身为替身。
- `up-¬lw`：`(𝒮 𝒜 : Sys (h₁ ωᶜ)) (𝓀ᴬ : Sys.KeepLaw 𝒜) (s : Sys.St 𝒮 (tw 1)) (r : RebAt 𝒮 𝒜 𝓀ᴬ s) → (∀ c x → RebAt.Lr r c x ≡ h₁ c) → ⊥`。白话：换基层号取原材料的孩子层号时，没有字面公共上界（用 `no-ωᵉ`）。
- `kp-child`、`lf-noEv`：`∀ {a} (s : Stᴷ a) → IsLfD s → (p : Pos a) → Evᴷ s p → ⊥`。白话：K = `kp` 时，上折回退的孩子状态对一切槽位都没有证据。
- `up-¬cpE`：`(𝒮 : Sys j) → ∀ {a} (s : Sys.St 𝒮 a) (r : RebAt 𝒮 (sysᴷ Cxtᴷ apᴷ Bdᴷ) (keepᴷ Cxtᴷ apᴷ Bdᴷ) s) (c : CH a) (x : Tr a) → IsLfD (RebAt.Sr r c x) → Pos j → ⊥`。另有 `step-lf`：上折回退自己的孩子状态都满足 `IsLfD`，所以这个前提可满足。

**YiBLToy**（编译定理，模型）

- `toy-lowᴿ : (β K : ℕ) → K ≤ β → ∀ {a x} → a ≤ x → K + a ≤ β + x`，经 `SuffRA.sys→low` 得到；高层的嵌入行是换基行。

#### 4. 第一个障碍

本路四步都没有被挡住。往下要真正在 `YiBSFold` 上得到 LowKeep，需要实填出口；按顺序我判断会先撞到下面两处，二者都是数学上的（接口形状），不是工程上的，都没有编译：

1. 主系统 `OutR.nodeE` 在 ℓ 层孩子槽位的结点上：证据为空（`main-noEv`，编译），只能走链。槽位层号在目标之下时，参照一侧应当保留，走链就不成立。规范树 `Ωt ℓ` 在 ℓ 层只有顶结点（下标槽位），但 `SuffR` 与 `Suff` 一样对一切树陈述、没有量化域，所以出口要对这些结点也给出。出路是按读回域陈述的充分性（判断，未做）。
2. 辅助系统 `Out.nodeE` 走链一支的 `∀ k → Φ s (g (z k)) ⊴ Φ s (nd p g)`，对部分和极限在 k ≥ 1 处可能不成立（判断，见问题表 12）。

支配出口按 `Leaf` 律看是可写的（判断）。

#### 5. 偏离与事故

- **偏离**：
  - "替身支配原材料" 放在了出口（参照一侧），没有放在树一侧的律里；理由见第 1 节。
  - 另加了 `YiBLToy`，简报里没有要求，用来说明前提可满足。
  - 实例的范围比 "塔第 1 项" 宽。
  - `lw` 字段在证明里没有用到，只作字面公共上界的证据。
  - `route` 落在地板之下的行（`back`）与无证据的行没有处理。
- **事故**：
  - 没有 251、124 或 154。
  - `/usr/bin/time -l` 被沙箱拦下（`sysctl kern.clockrate: Operation not permitted`），所以没有量堆峰值；墙钟每件 2 到 3 秒。
  - 临时文件 `YiBLLaw0.agda`、`YiBLInst0.agda` 留在 `<实验目录>`。
  - 没有在本路范围之外写、删任何东西。
- **没有读、只凭转述引用的**：
  - V149 的 "方向反变"，以及 V287、V290 的内容，来自简报与 `IdeaLedger` 中 V290、V292、V293 三行；V149 原条目没读。
  - 留档 `YiVA.md`、`AuditD.md` 没读。`YiRKChain`、`YiCTCall`、`YiBSCrit`、`YiBSFam`、`YiBSAccept` 没读。
  - `YiAbsGRow`、`YiAbsGNeg`、`YiVALeaf`、`YiTBObs`、`YiDXFold`、`YiMTTab`、`YiTBTab` 只检索了签名。
  - Bedrock 手册只检索了 C-9、C-10、S-1、S-3、C-24、Q-1、Q-23、H-6 的条目头。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：换基的律接进整体接口（不读记号，兼作摆脱侧）（前缀 YiBL，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Opus 5.5。本路不读记号（验收文件除外），是这一批的摆脱侧。同批另三路与你互不导入。

#### 作者的决定与背景（2026-11-17）
- 作者已关闭现行折叠上同步对象那一步链步（`YiKTSlot.Cand` 及其变体，台账 V287），依据是两份先读定义的 Fable 5.2 封存审核（留档 `probes/Survey/Reports-2026-11-16/YiVA.md`、`AuditD.md`）。**主线定义不动**；改树、折叠、合法性只在新文件里做候选。
- 第七十六批作者选四路（选项原文）："换基替身的值 (Recommended), 换基的律接进整体接口 (Recommended), 换基证据对真实链孩子的覆盖 (Recommended), 比较表的对角条目不判等"。前缀 `YiSV`（Fable 5.2）、`YiBL`（Opus 5.5）、`YiBC`（Opus 5.5）、`YiDG`（Opus 5.5），互不导入。
- **第七十五批三路（主审冷编复核过）指向同一处**：折叠在被问到的孩子对上要字面证据。
  - `YiRKCell`（不读记号）：朝目标孩子 d（取 ω）的层号折塔第 1 项的 Ω 树时，顶结点在四种折叠里都保留（`top-ω`、`top₁` 到 `top₃`），一切分支 c 都被问到；三种写法的行都不看 c 是否字面延伸 d（`w1`、`w2`、`w3`）。现行行把孩子树折到第 0 层再加上（`w1`、`ι-free`）；上折回退在原材料任何深度的槽位走链（`w2-never`）；**换基**不用原材料，在 `h₁ d ⊕ ↑c` 上重建 Ω 树沿 `lift` 朝原目标折（`w3`、`w3′`），目标层副本的槽位保留（`keep-lift`、`keep-ω`），换基层号没有 Ω 形状子层号（`noΩ-reb`），后继孩子处替身树的顶走链（`seen-s`）。V50 按 "孩子对" 的提法为否：ω 与偶数列 ω 之间两个方向都没有字面路径（`no-ωᵉ`）；字面延伸给出路径（`ext-path`，`Ext d c = zero ⊢ d ◃ c`）。`YiRKChain`：chain 1 副本顶是 ℕ 极限（`Real.L₁`），链孩子层号是 ℕ 极限形状（`Real.child-L`）；副本照 `YiSYReduce`、`YiSYDesc` 重写，与原定义的相等未编译。
  - `YiCTCall`（不读记号）：候选 (C) 在 `cand₂` 实际路径上丢保留的那一格，槽位与目标同在孩子 3 下（对角），对一切来源表走链（`cell`、`org-P₁`）；只给比较表加 (3,3) 条目就保留（`cf-pos`，有限测试）。
  - `YiFIIface`（不读记号）：对折叠参数化的抽象充分性：保留律 `KeepLaw`、回退律 `FallLaw`、参照出口 `Out` ⇒ 每个状态上保持（`Suff.keepAll`）、LowKeep（`sys→low`）；`YiFIFold.lowᴷ`（上折回退的候选上只剩 `Out`，其结点一条 `Out.nodeE` 就是 V50）；`keepOf`（字面路径保留）；配对否定 `YiFINeg.kp-not-flr`、`kp-not-lit`、`kpᴬ-violates`、`main-nf`、`fb-nf`。
- **换基已有的原型**（`probes/OCF/Lean/`，都是候选、不替换主线；先读文首）：`YiBSBase`（`split : (a b : L) → OkO a b → ∀ {j} → j ≤ (a ⊕ b) → (j ≤ a) ⊎ (a ≤ j)`；`rbO : (a b : L) → Rb a → Ok a → OkO a b → Rb (a ⊕ b)`；`rb-tw : (n : ℕ) → Rb (tw n)`；`seen : ∀ {k h} (S : Schema k h) (j : L) → Ok j → floor S ≤ j → Tr⁺ j → Tr k → Tr⁺ j`），`YiBSFold`（换基折叠 `BS.ψ`，"该行的换基部分固定重建 Ω 树，原孩子树只进入低层尾项"），`YiBSRead`（`Read` 码），`YiBSReadNeg`、`YiBSUpNeg`（字面读回的两条否定，不否定值），`YiBSClean`、`YiBSInner`（干净对象上的闭项与内层整行），`YiBSFam`、`YiBSCrit`（有限读回层的保持；`finite-crit`、`finite-shift` 只到数字孩子），`YiBSAccept`（首链点 ψ₁(Ω₃) 关系，输出 ψ₀(Ω₃) 下界）；更早的 `YiRBSib`、`YiRBCrit`、`YiRBFam`。台账 V149（换基；"对任意一块不可写（纸面判断，方向反变）"，出路是改块的嵌入字段为族或收量化域）、V158、V290、V293。
- 主线现状：第一档成品已完成；终点无条件值 ψ₀(Ω_Ω+ψ₁(Ω_ω)+ω)（`YiFYRef.target-low`）；里程碑 ψ₀(Ω_{Ω₂}) 未达到。

#### 本路的问题
`YiFIIface` 的回退律 `FallLaw` 说 "孩子上的材料朝原目标折"。换基行不用原材料：它把原孩子树放进低层尾项，另在 `h₁ d ⊕ ↑c` 上重建 Ω 树沿 `lift` 朝原目标折（`YiRKCell.w3`、`YiBSFold`）。所以换基不满足现有回退律，要一条新的律，并接进同一套充分性。

#### 要做的（按序）
0. **写律**：在 `YiFIIface` 的框架里写 "换基律"：替身树支配原材料（以第一位置序或接口的关系表述，不读记号），替身里被问到的槽位的证据由 `lift` 给出（对应 `KeepLaw` 的 `Ev`）。在临时文件里编译类型。按 AGENTS "律带公共上界" 检查：律里出现的每一对下标都带字面公共上界的证据。不成立就停下回报。
1. **充分性**：证 "保留律 + 换基律 + 出口 ⇒ LowKeep"（仿 `Suff.keepAll`、`sys→low`，复用而不重写 `YiAbsG*` 与 `YiFIIface`）。
2. **实例化换基折叠**：`YiBSFold` 的折叠满足换基律与保留律（至少在塔第 1 项为前缀的层号上）；写出 `Out.nodeE` 在换基下要什么，能否由 `lift` 实填（这就是 V50 在换基下的样子）。
3. **配对否定**：现行折叠与上折回退违反换基律的哪一条（复用 `YiFINeg`、`YiRKCell` 的结果）。
4. 交律的清单与翻译账。

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

