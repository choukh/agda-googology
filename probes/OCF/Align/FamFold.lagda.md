# 族增量世界上的真折叠 (入口): 构造一路

> 不含记号. 作者选定原话: "族增量世界上写真折叠". 本篇是构造一路; 否定一路前缀 `NegFam`, 共用接口 [FamFoldIf](FamFoldIf.lagda.md) (接口定稿 2026-11-05 11:20, 变更记录: 无). 依赖 [LocUip](LocUip.lagda.md) 一族 (族增量 `Inc`, 连拷贝的族更新 `LocUipFeed.raiseFCᴮ`), 两种种类的折叠 ([HtTowerF](HtTowerF.lagda.md), `HtTowerFClosed.T⁺`) 与它的读回 (`HtTowerFRead.rd`, `HtTowerNRead.rd₂`). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 没有条件定理.
>
> **判决.**
>
> 1. **一级 (κ₂) 的折叠: 构造出来 (定理).** `FamFoldOne.F.fold`: 以族增量世界为参数 (外层世界, 坐标 1 的可入证据, 分量函数), 层 `HB S₂` ↦ 两种种类第 2 层的树. 在 κ₂ 节点处回灌: 世界链每一步是 $(1,p_0)$ 处连拷贝的族更新, 增量是**折叠自己**在分支 $g(\text{当前槽})$ 上的输出的读回 (输出读成两种种类的层, 两种种类折叠 $\Omega_{2\boxplus h}$ 的第 2 层输出, `rd₂` 读回); 读回不是参数. 接口记录 `Feed₁ raiseFCᴮ` 的实例 `feed₁` (链的定义律 `ch-s`, `fold-Ω` 都是 `refl`; 链上世界合法, 两种相干 `Coh≡ × CopyCoh` 都保, 只增). 读回对坐标一致: 族 `famRd` 只按坐标的构造子定义, 在 1 处定义相等 (`famO`, `sec₁`). 闭项 `T₃ Λ = T⁺ (idx Λ)` 合法, 有 FGH (`fghᵀ`, `fghᵀ²`); 合法与 FGH 都由形状给出.
> 2. **不被压回 (定理, 连同合法性).** 级顶 `Ωtop S₁` 的两种种类输入 `idx (Ωtop S₁)` 合法, 是格的 ℕ-极限, 第 2 格的最外是 `κH` 的 $\Omega$-节点 (计算), 所以不与 `Ω₂ᴴ` 互模拟, 也不与任何 `H₀` 嵌入互模拟 (`notPressed`, `notPressedᴸ`). 对照 `UipFbTop.pr₂-top`: 投影折叠把同一个级顶压回 `Ω₂ᴴ`. 世界侧: 链上第 1 个世界的 κ₂ 槽含新种类节点且有界 (`slot₁-new`, `slot₁-bd`).
> 3. **第二级 (κ₃): 构造出来 (定理).** `FamFoldTwo`: 多一个手写的第 3 层读回 `rd₃` (合法由形状给出), 旧种类 κ₂ 的节点读成过第 2 层的节点. 闭项 `Tᵀ₂ = T₄ (Ωtop S₂)`, FGH; 第二级中间输入 (`HB S₂`) 的第 2 格最外是 κ₂ 节点, 不与任何 `HB S₁` 嵌入互模拟 (`¬top₂≈up`).
> 4. **对一切级一条: 构造出来 (定理).** 一条对级数 $n$ 递归的定义, 不按站写: 种类提升 `FamFoldLift` (一步定理 `Lg-node`, `fst-node`: 第 $m\le k$ 级种类的连续分支合法, 底是第一位置, 一条证明对一切 $m\le k$), 读回包 `FamFoldRead.pkg n` (`Pkg (suc n)` 只用 `Pkg n`; 第 $n+1$ 层的树读成 `HB (Sk n)`, 合法由形状给出), 第 $n+1$ 级的折叠 `FamFoldAll.FK` 与下降 `dnR`. 接口 §5 的 `TowerDown` 有实例 `towerDown`. 闭项: 每级一个 `Tlv n`, 对角 `T∞ = T⁺ Λ∞` (`Λ∞` 是各级级顶的累加的 ℕ-极限), 合法, 有 FGH (`fgh∞`). 一般定义在 $n=1,2$ 上的检查 (对具体级数的计算定理): 级顶输入含该级的新种类节点 (`FamFoldAllTest`).
> 5. **值: 没有序数值定理.** 只有结构上的: 格逐个是第一位置 (`cells-st`), 级顶输入含新种类节点. 读法全是判断 (下文).
>
> **对纲领与目标.** 纲领 1: 一切闭项是 `A` 的元素, 层是布劳威尔树的高度, FGH 在树上算. 纲领 2: 无公理, 停机由检查器保证. 纲领 3: 不触壁垒: 没有序, 没有三歧, 一切坐标比较都在同一外层界之下 (`dD`); 第 1 级以上不做任何坐标比较. 纲领 4: 导入闭包与切片干净 (审计). 目标 "让树自足": 一切级的一步 (`Pkg n → Pkg (suc n)`, `Lg-node`) 写成对级数的一条定义与一条证明, 新用到的只是 `step` 的旧种类原样 (`liftK` 每步定义相等); 这是提供信息的一步 (判断). 不足: 第 1 级以上的 "折叠" 是层的下降 (把高一级的层折成低一级的层), 真正做坍缩的仍只有两种种类的折叠 `T⁺`; 数据树在第 1 级以上只被读回, 不被 `Run`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FamFold where

import OCF.Align.FamFoldIf
import OCF.Align.FamFoldOne
import OCF.Align.FamFoldTwo
import OCF.Align.FamFoldLift
import OCF.Align.FamFoldRead
import OCF.Align.FamFoldAll
import OCF.Align.FamFoldAllTest
```

## 接口

[FamFoldIf](FamFoldIf.lagda.md), 只有类型: `CohC` (= `Coh≡ × CopyCoh`), `slotAt`; 读回对坐标一致 `SecAt`, `Uniform`; 以世界为参数的一级折叠 `FoldW₁`, 回灌记录 `Feed₁ R` (`fold`, `rdO`, `famO`, `chain`, `ch-z`, `ch-s`, `fold-Ω`, `ch-lg`, `ch-coh`, `ch-≤`); 闭项 `Fold₁`, 输入 `Input₁`, `NotPressed`; 一切级 `Sk`, `FoldAll`, `Down`, `DownStep`, `TowerDown`. 律的定义域逐条写在接口文件头: 每对坐标带同一外层界的证据. 变更: 无 (定稿前改过一次 `Out₂` 的世界为显式参数, 那是定稿之前).

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `F.fold`, `F.chain`, `F.ch` | FamFoldOne | 一级折叠, 以族增量世界为参数; κ₂ 处的世界链 (`rFC`) | 定义 |
| `feed₁` | FamFoldOne | `Feed₁ raiseFCᴮ` 的实例: `ch-s`, `fold-Ω` 为 `refl`; 链合法, 保 `CohC`, 只增 | 定理 |
| `famO`, `sec₁`, `famRd-at` | FamFoldOne | 读回对坐标一致 (按构造子, 在 1 处 `refl`) | 定理 |
| `F.slot-s`, `F.slot-bd` | FamFoldOne | 新槽 = 旧槽 ⊞ 读回; 槽在世界里有界 | 定理 |
| `T₃`, `Lg-T₃`, `Tᵀ`, `fghᵀ`, `Tᵀ+1`, `Tᵀ·2`, `Tᵀ²`, `fghᵀ²` | FamFoldOne | 一级闭项, 合法, FGH | 定义; 合法是定理 |
| `top-hl`, `cell₂-ΩH`, `cell₂-new` | FamFoldOne | 级顶输入是格的极限, 第 2 格最外是 `κH` 节点 | 定理 (具体项的计算) |
| `¬top≈Ω₂`, `¬top≈up`, `notPressed`, **`notPressedᴸ`** | FamFoldOne | 不被压回, 连同 `Lg-idx` | 定理 |
| `slot₁-new`, `slot₁-bd`, `chain-lg`, `chain-coh`, `cells-st` | FamFoldOne | 世界侧: κ₂ 槽含新节点, 有界; 链合法相干; 格逐个是第一位置 | 定理 |
| `rd₃`, `rd₃-fst`, `Lg-rd₃`, `nbA₂`, `nbH₂` | FamFoldTwo | 第 3 层读回成 `HB S₂`, 合法由形状给出 | 定理 |
| `F3.fold`, `F3.ch-lg`, `F3.ch-coh`, `F3.ch-≤`, `F3.slot-s`, `famO₂` | FamFoldTwo | 第二级折叠与链的律, 读回对坐标一致 | 定理 |
| `T₄`, `Tᵀ₂`, `fghᵀ₂` | FamFoldTwo | 第二级闭项, FGH | 定义 |
| `cell₃-κ₂`, `cell₃-new`, `¬top₂≈up`, `slot₃-new`, `chain₃-coh` | FamFoldTwo | 第二级级顶不被压回到 `HB S₁` 嵌入; 世界侧 | 定理 |
| `Le`, `liftK`, `cvE`, `vcE`, `cv-vc`, `pwL`, `pw-pr`, `bd→`, `bd←`, `pr→`, `lw→`, `le→` | FamFoldLift | 种类沿 $m\le k$ 提升, 坐标/界/世界随之换 | 定理 |
| **`Lg-node`**, **`fst-node`** | FamFoldLift | 一步定理: 一切 $m\le k$ 级种类的连续分支合法, 底是第一位置 | 定理 |
| `trK`, `trN`, `rdN`, `fstN`, `lgN`, **`pkg`**, `Rd` | FamFoldRead | 一切级的翻译与读回, 对 $n$ 结构递归, 合法由形状给出 | 定理 |
| `eqG`, `famK`, `famK-at`, `Lg-famK-at` | FamFoldAll | `G₀ (fin k) ≡ Sk k`; 一切级的族读回 (按构造子匹配) | 定理 |
| `FK.fold`, `FK.ch-lg`, `FK.ch-coh`, `FK.ch-≤`, `FK.slot-s`, `FK.famOK` | FamFoldAll | 第 $n+1$ 级的折叠与链的律, 对一切 $n$ | 定理 |
| `dnR`, `idxK`, `Lg-idxK`, **`towerDown`** | FamFoldAll | 下降, 接口 `TowerDown` 的实例 | 定理 |
| `H`, `lgH`, `Tlv`, `cum`, `Λ∞`, `lΛ∞`, **`T∞`**, `Lg-T∞`, `fgh∞` | FamFoldAll | 每级闭项, 对角闭项, 合法, FGH | 定义; 合法是定理 |
| `H1-cell₂`, `¬H1≈Ω₂`, `¬H1≈up`, `notPressedᴸ`, `I₂-cell₂`, `¬I₂≈up` | FamFoldAllTest | 一般定义在第 1, 2 级上: 级顶输入含新种类节点, 不压回 | 定理 (具体级数) |

## 闭项与 FGH 的类型原文

```text
FamFoldOne.T₃      : Fold₁                   -- (Λ : HB S₂) → LgB Λ → A
FamFoldOne.Tᵀ      : A                       -- T₃ (Ωtop S₁) (Lg-Ωtop S₁)
FamFoldOne.Tᵀ²     : A                       -- T₃ Ω₃² Lg-Ω₃²
FamFoldOne.fghᵀ    : ℕ → ℕ                   -- FL.FGH (ord Tᵀ)
FamFoldTwo.T₄      : (Λ : HB S₃) → LgB Λ → A
FamFoldTwo.Tᵀ₂     : A                       -- T₄ (Ωtop S₂) (Lg-Ωtop S₂)
FamFoldTwo.fghᵀ₂   : ℕ → ℕ
FamFoldAll.Tlv     : ℕ → A                   -- T⁺ (H n) (lgH n)
FamFoldAll.T∞      : A                       -- T⁺ Λ∞ lΛ∞
FamFoldAll.Lg-T∞   : Lg T∞
FamFoldAll.fgh∞    : ℕ → ℕ                   -- FL.FGH (ord T∞)
```

全部无模块参数, 无前提.

## 前提实例

本路没有条件定理. 接口记录的实例与起点:

- `Feed₁ raiseFCᴮ`: `feed₁` (FamFoldOne §3).
- 起点世界: 外层 $(0,2)$ (`w₂`, 一级), $(0,3)$ (`w₃`, 二级), $(0,n+2)$ (`wK n`, 一般); 分量全 $0$ (`vz`), 合法 (`lgvz`), `Coh≡` (`cohvz`, `refl`), `CopyCoh` (`copyvz`, `copyvz₃`, `copyvzK`, `refl`). 证据 `p₁`, `p₂`, `pK n` 都是 `hsuc hself`.

## 第一个障碍

1. **值.** 没有任何序数值定理: 缺 `T⁺` 对输入的单调或跨输入比较 (同 `TdPlus`, `UipFb` 的 "缺的定理"). 互模拟的否定 (`notPressedᴸ`) 只说输入不同, 不说值更大.
2. **第 1 级以上不是数据树的折叠.** 一级以上的 "折叠" 把层折成低一级的层 (`idx`, `idxK`), 再交给 `T⁺`; 数据树只用来让读回合法由形状给出 (`rd₂`, `rdN`), 不被 `Run`. 三种种类以上的数据树折叠 (闭包 `nν` 与 `Run` 里的回灌) 没有写. 回灌的起点是当前槽本身, 不是 "槽接上状态里的输出" (`RunM` 的 $x_0=\mathrm{rd}(\text{界}, z_1)$); 本路没有状态 `St`.
3. **一切级的对角不在一个族增量世界里.** 第 $n$ 级的世界是外层 $(0,n+2)$, 坐标有限; 对角 `Λ∞` 在 `Ht` 里累加各级的级顶, 没有外层界为 $\omega$ 的世界. 在一个外层界含极限的世界里对一切级回灌, 要对极限坐标一致的读回; 否定一路 `uniformAll→fix` (主审转告, 我未复核) 说那推出 `LoopFix`. 本路没有碰它.

报错原文: 无 (障碍是没写的东西, 不是报错).

## 读法 (全部是判断)

按 `HtTowerNFb` 对 `T-fb₂ω` 的读法 (κ 节点的回灌链读成该级的 $\Omega$):

| 闭项 | 读法 (判断) | 测到哪里 |
|---|---|---|
| `Tᵀ` | $\psi_0(\Omega_{\Omega_3})$, 与 `Tᵁ`, `T-fb₂ω` 同读法 | 级顶输入的格链 (`top-hl`, `cell₂-ΩH`) |
| `Tᵀ+1`, `Tᵀ·2`, `Tᵀ²` | $\psi_0(\Omega_{\Omega_3+1})$, $\psi_0(\Omega_{\Omega_3\cdot2})$, $\psi_0(\Omega_{\Omega_3^2})$ 为下界 (累加的毛刺只往上) | 没测, 纸面 |
| `Tᵀ₂`, `Tlv 2` | $\psi_0(\Omega_{\Omega_4})$ | 中间输入含 κ₂ 节点 (`cell₃-κ₂`, `I₂-cell₂`) |
| `Tlv n` | $\psi_0(\Omega_{\Omega_{n+2}})$ | 纸面 |
| `T∞` | $\psi_0(\Omega_{\Omega_\omega})$ | 纸面 |

与 Buchholz 式基本列的差 (判断): (i) 层的 ℕ-极限与 $\Omega$-分支经数据树读回是累加 (`toD₁`, `nbᴮ` 的读法; 同 `HtTowerNRead` 的 "值不忠实" 选择), 只会往上偏; (ii) 分支里的内层 κ 节点相对当前槽求值 (世界语义, 同 `RunM`), 不是固定的 $\Omega_{k}$; (iii) `T∞` 是各级级顶的累加, 不是上确界 (`DiagKSum` 的毛刺一侧). 没有上界.

## 翻译账

本路不读记号. 新定义及来源:

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| κ 节点处的世界链 (读界, 族更新, 读回) | `HtTowerFFold.RunM`/`κc₁` 的三步, 换成 `LocUipFeed.rFC` | 沿用 (回灌形状的翻译痕迹记在 `StallDiagnosis` §4 (i)) |
| 读回 = 输出读成层, 两种种类折叠, 第 $n+1$ 层读回 | `HtTowerNFb.Fb₂` 的读回 | 沿用 |
| `famRd`, `cast₂`, `famK` (按构造子的族) | `LocUipFam.extF` (LocUip 第一个障碍的路 (ii)) | 树逼出 (族增量要的), 脚手架 |
| `trK` (第 0, 1 级 ↦ 闭包, 第 $j\ge2$ 级 ↦ 过第 $j$ 层的节点) | `toD₁`, `rd₂` 读节点的法子反过来用 | 树侧 |
| `rd₃`, `rdN`, `pkg` | `rd`, `rd₂` 的一般化 | 树侧 |
| `Le`, `liftK`, `cvE`, `pwL`, … | `step` 的旧种类原样; 类型论要求 | 脚手架, 序数值不需要 |
| `Lg-node`, `fst-node` | `HtTowerCont.cont→Lg` 的一般化 (旧种类上) | 树侧, 一步定理 |

归类: 提供信息 (判断). 一切级的一步写成对结构参数 ($n$) 的一条定义与一条证明, 新用到的字段只有 `step` 的 `inj₁` 原样 (`liftK` 每步定义相等); 没有新构造子, 闭包定理没有新专属前提, 不用 `Lab`, 没有序数值验收. 加深的地方: 回灌形状仍是 `RunM` 的三步.

## 对否定一路结论的回应 (主审转告, 我未复核那一路)

- (1) `famO-free`: 与 `famO`, `sec₁` 同向; 本路的族都只在有限坐标处用.
- (2) `uniformAll→fix`, `slotFam-sep`: 本路一切级的折叠每级只在一个有限坐标 `fin (n+1)` 处回灌 (`FK`), 族由构造子匹配给出 (`famK`, 不对一切坐标一致读界), 外层世界每级一个; 没有撞上. 对角若要在一个外层界含极限的世界里做, 就会撞上 (第一个障碍 3).
- (3) `offF→rd0`: 本路用的 `raiseFCᴮ` 连拷贝一起升, 不满足 `OffF`; 读回不为 0 (`slot₁-new`, `slot₃-new`).
- (4) `¬copy₂-raiseFCᴮ`: 本路只保一步拷贝相干 `CopyCoh` (`ch-coh`), 不声称两步的; 接口里没有 `CopyCoh₂`.
- (5) `notPressed-e₊`: 已补 `notPressedᴸ` (FamFoldOne, FamFoldAllTest), 连同合法性.

## 审计

- **从头编译**: 删本路八个模块的 `.agdai` (精确模块名), 依赖用共享接口, 入口 `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/FamFold.lagda.md +RTS -M6G -RTS`, 退出码 0, 5.4 秒, 峰值常驻约 0.61G.
- **导入闭包** (`importclosure.py`, 不加 `--only`): `FamFoldOne`, `FamFoldTwo`, `FamFoldAll`, `FamFoldAllTest`, 入口都是退出码 0, 禁用表命中 0; 入口闭包 60 个模块 (本地 49).
- **定义级切片** (`depslice.py`, 到达块 / 记号模块块 / 别处记号词): `FamFoldOne:Tᵀ` 292/0/0, `Lg-Tᵀ` 297/0/0, `fghᵀ` 310/0/0, `feed₁` 311/0/0, `notPressedᴸ` 298/0/0; `FamFoldTwo:Tᵀ₂` 333/0/0, `fghᵀ₂` 351/0/0; `FamFoldAll:T∞` 343/0/0, `Lg-T∞` 347/0/0, `fgh∞` 361/0/0, `towerDown` 325/0/0; `FamFoldAllTest:notPressedᴸ` 346/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 切片看不见模块应用 (`module F₂ = F …`), 导入闭包覆盖这一处. 只保证不引用, 不说明定义没有受记号启发.
- **禁用构造**: 八个文件里没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, `Funext` (全文搜索 0 处); 选项都是 `--safe --without-K --lossy-unification`.
- **代码行** (agda 块里非空非注释) / 文件行: `FamFoldIf` 74/159, `FamFoldOne` 158/266, `FamFoldTwo` 245/353, `FamFoldLift` 126/188, `FamFoldRead` 109/155, `FamFoldAll` 149/249, `FamFoldAllTest` 41/64, 入口 9/约 140.

## 接手清单

1. 值: 第一条值定理的候选是 `T⁺` 对输入的单调 (`x ⊲ y → T⁺ x ≤ T⁺ y` 一类, 按 `TLRuleSpec._≤_`); 有了它, `Tᵀ`, `Tᵀ₂`, `Tlv n`, `T∞` 之间与对 `Tᵁ`, `Tᴰ₊` 的比较都能写.
2. 数据树折叠: 第 1 级以上的闭包 (`nν`) 进数据树并在 `Run` 里回灌, 状态里记读回层的输出 (`RunM` 的 $z_1$); 本路的 `trK`, `rdN`, `Lg-node` 可直接复用.
3. 对角在一个世界里: 外层界 $\omega$ 的族增量世界上对一切有限坐标回灌; 先对照否定一路 `uniformAll→fix` 与 `slotFam-sep` 的前提, 找不要对极限坐标一致读回的写法.
4. 两步拷贝相干 `CopyCoh₂`: 若对角要它, `rFC` 要再升 `hs (hs c₀)` 的分量.
