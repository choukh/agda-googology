# 族增量世界上的真折叠: 否定一路的入口

> 不含记号. 作者选定原话: "族增量世界上写真折叠". 本路是**否定**一路, 与构造一路 `FamFold*` 配对 (手册 §5.2). 对着接口 [FamFoldIf](FamFoldIf.lagda.md) ("接口定稿 2026-11-05 11:20 (编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 分篇: [NegFamSec](NegFamSec.lagda.md) (读回对坐标一致), [NegFamFeed](NegFamFeed.lagda.md) (`Feed₁` 与只升 $c_1$ 的更新; 下一层拷贝), [NegFamTop](NegFamTop.lagda.md) (级顶的压回; 接口 §5). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延; `FE₀` (`ColimWNeg` 的 $\mathbb N\to H_0$ 外延) 只在 `NegFamSec` 作前提, 用到它的结论标 "条件".
>
> **判决: 对接口的主律 "读回对坐标一致" 在一级写不出否定, 它是定理; 否定落在它的一切级版本与一个更新的选择上.**
>
> 1. **一级的 `famO` 不是障碍 (定理, `famO-free`).** $c_1 = 1$ 是孤立点 (与它的相等对一切裸坐标按构造子可判定, `isolated-fin`), 孤立点上环都是 `refl` (局部 Hedberg, `Iso.isoK`), 所以任意读回都延成族: `∀ rd → Uniform O c₁ rd`. 族对不可入坐标的值由结构判定给出, 不触壁垒, 不推出任何判定.
> 2. **一切级的 `famO` 至少与 LocUip 的第一条引理一样强 (定理).** `uniform⇔sec`, `uniformAll→fix`, `uniformAll→irr`, `uniformAll→lemma1`: 对一切合法坐标的 `Uniform` 推出 `LoopFix` (环沿 `HB ∘ G₀` 的搬运平凡), 从而 `IncIrr`, `Lemma1`. 族的写法没有消掉外延性内容, 只把它从更新挪到了读回. 便宜的路 (孤立) 在 $\omega$ 处是禁忌: `iso-ω-sep` (定理), `iso-ω→WLPO` (条件 `FE₀`). 不是否定: `Uniform` 在 $\omega$ 处由外延推出与否, 未证.
> 3. **"读界" 的读回对一切级一致, 撞 `raiseA-sep` 的影子 (定理).** 若一切级的读回要成族且读的是各级的槽 (回灌第一格 $x_0=\mathrm{rd}(\text{界},z_1)$), 就要槽延成坐标族. `slotFam-sep`: 对**一切** `R : RaiseF` (只用 `atF`, `belowF`), 外层世界族 $w_\alpha$ 上从全 0 世界一次更新之后槽都延成族 ⇒ 对每个 $\alpha$, $y_\alpha\not\equiv\omega$ 或 $\alpha$ 恒假; `slotFam→WLPO` (条件 `FE₀`); 保 "槽是族" 的更新同样 (`pres-sep`, `pres→WLPO`); 单个增量 `RaiseB` 同样 (`slotFamB-sep`); "旧界接增量" 形式归约到它 (`cell→slot`). 接口的 `Feed₁` 不撞它: `famO` 读的是输出, 且只在 $c_1$.
> 4. **只升 $c_1$ 本身的族更新上, `Feed₁` 只能是平凡回灌 (定理).** `offF→rd0`: `OffF R` 且 `F : Feed₁ R`, 则在 $2$ 可入的相干世界上链的每一格读回为 $0$; `offF→flat`, `offF→branch`: 槽沿链不动, κ₂ 节点的每个分支都在起点的槽上取. 原因是 `ch-coh` 的 `CopyCoh`. 前提可满足: `triv : Feed₁ raiseFᵒ` 与 `offFᵒ`, 世界 `w₃`. 所以构造一路必须用升拷贝、不满足 `OffF` 的族更新 (`raiseF⁺`, `raiseFCᴮ` 一类; `FamFoldOne` 用的是 `raiseFCᴮ`, 与此一致).
> 5. **对一切级的折叠, `no-wmatch` 在新世界里一层一层地回来 (定理, 不是对接口的否定).** `raiseF⁺` 保 `CohC`, 但不保两步拷贝的相干 `CopyCoh₂`: `keep₂→¬copy₂` (对一切不动两步拷贝的族更新), `¬copy₂-raiseF⁺`, 以及构造一路 `FamFoldOne` 实际用的 `raiseFCᴮ` (`¬copy₂-raiseFCᴮ`). 接口只要 `CopyCoh` (一步).
> 6. **级顶的压回只由采样映射决定 (定理).** `pressed⇔`, `notPressed⇔`: 以 $e$ 采样的局部输入 (`Local inp e`) 的级顶与 $\mathrm{h\Omega}\,\kappa_H\,e$ 互模拟, 被压回当且仅当 $e$ 逐点是 `up`; `pr₂` 是 $e=$ `up` 的特例 (`pressed-pr₂`). 但 `NotPressed` 不含合法性: 只换采样映射的 `prE e₊` 就满足它 (`notPressed-e₊`); 它合不合法未证 (判断: 多半不合法). 接口 §5 的 `Down`, `DownStep`, `TowerDown` 由常值 $0$ 平凡满足 (`towerDown-triv`).
>
> **对纲领与目标.** 不触壁垒定理: 分离子来自 "族在裸坐标上的值" 与 "可入坐标上的律" 的夹击, 与 `ColimWNeg.raiseA-sep` 同族, 前提里没有序与三歧. 第 3, 4 条划出构造一路不能有的东西: 一切级一致地读界的族读回; 只升 $c_0$ 本身的更新. 第 1 条说一级的主律是免费的, 第 2 条说一切级的主律的价钱就是 `LoopFix`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegFam where

open import OCF.Align.NegFamSec public
open import OCF.Align.NegFamFeed public
  using (le⊞; lt⊞; ⊞≡→hz; offF→rd0; offF→flat; offF→branch; Z; bD-Z; chT; foldT; copyZ; triv; w₃; lo₃; v₃; coh₃; p₁₃; p₂₃; inst;
         nest₂; CopyCoh₂; Keep₂; RaiseCopy₂; keep₂→¬copy₂; keep₂-raiseF⁺; ¬copy₂-raiseF⁺; keep₂-raiseFCᴮ; ¬copy₂-raiseFCᴮ)
open import OCF.Align.NegFamTop public
```

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `isolated-fin`, `Iso.isoK`, `iso→sec`, `iso→uniform` | Sec §1 | 有限坐标孤立; 孤立点上环是 `refl`; 读回都延成族 | 定理 |
| **`famO-free`** | Sec §1 | `∀ O rd → Uniform O c₁ rd` | 定理 |
| `uniform⇔sec`, `sec→fix` | Sec §2 | `Uniform` (对一切 `O`, `rd`) ⇔ 一切 $\delta$ 的 `SecAt`; `SecAt` ⇒ 环搬运不动 $\delta$ | 定理 |
| **`uniformAll→fix`**, `uniformAll→irr`, `uniformAll→lemma1` | Sec §2 | 一切级的 `Uniform` ⇒ `LoopFix` ⇒ `IncIrr`, `Lemma1` | 定理 |
| `iso-ω-sep` / `iso-ω→WLPO` | Sec §2 | $\omega$ 孤立 ⇒ 分离子 / WLPO | 定理 / 条件 (FE₀) |
| `⊟`, `⊞⊟`, `cell→slot` | Sec §3 | "槽 ⊞ $d$" 是族 ⇒ 槽是族 | 定理 |
| `Sep.sep`, **`slotFam-sep`**, `slotFamB-sep`, `pres-sep` | Sec §3 | 族 (单个) 增量更新后槽延成族 / 保族的更新 ⇒ 分离子 | 定理 (否定方向) |
| `slotFam→WLPO`, `pres→WLPO` | Sec §3 | 同上 ⇒ WLPO | 条件 (FE₀) |
| `slotFam₀`, `fam₁` | Sec §3 | 全 0 世界与有限外界上更新后的世界, 槽是族 | 定理 (前提实例) |
| `le⊞`, `lt⊞`, `⊞≡→hz` | Feed §1 | 槽 ⊞ $d$ = 槽 ⇒ $d=0$ | 定理 |
| `slot-suc`, `copy-suc`, **`offF→rd0`**, **`offF→flat`**, `offF→branch` | Feed §2 | `OffF` 上的 `Feed₁`: 读回恒 $0$, 槽不动 | 定理 (否定方向) |
| `triv`, `w₃`, `coh₃`, `p₁₃`, `p₂₃`, `inst` | Feed §3 | `Feed₁ raiseFᵒ` 的实例与世界 | 定理 (前提实例) |
| `keep₂→¬copy₂`, `keep₂-raiseF⁺`, **`¬copy₂-raiseF⁺`**, **`¬copy₂-raiseFCᴮ`** | Feed §4 | 升一步拷贝的更新不保两步拷贝相干 | 定理 (否定, 不对接口) |
| `local-top`, **`pressed⇔`**, `never-up`, **`notPressed⇔`** | Top §1–2 | 局部输入的级顶 = 采样映射; 压回 ⇔ $e\approx$ `up` | 定理 |
| `local-pr₂`, `pressed-pr₂` | Top §3 | `pr₂-top` 是特例 | 定理 |
| `prE`, `local-prE`, `e₊-not-up`, **`notPressed-e₊`** | Top §3 | `NotPressed` 可由只换采样映射满足 | 定理 |
| `downZ`, `downStep-triv`, `towerDown-triv` | Top §4 | 接口 §5 的类型平凡有实例 | 定理 |

## 律为什么是构造一路需要的

- `SecAt`, `Uniform`, `famO`: 接口 §2, §3 原文 ("读回由输出对一切坐标给出一个族"); 构造一路要它, 因为 `ch-s` 的更新 `raiseF R` 吃的是族 `Inc`. 一切级的版本 `UniformAll` 是对一切级一条折叠时同一字段在每个级的坐标上的要求 (接口 §5 的目标).
- `SlotFam`: 回灌形状 `HtTowerFFold.κc₁` 的第一格读世界的界; 一切级的读回若要成族且读界, 各级的槽就得是族. 接口的 `Feed₁` 里的读回读的是输出, 所以 `slotFam-sep` 不否定 `Feed₁`.
- `OffF`, `CohC`, `ch-coh`: 接口 §1, §3 原文与 `LocUipIf` 原文. 接口文字 "更新只在判定 '是 $c_0$' 的分量上用它" 正是 `raiseFᴮ`/`raiseFᵒ` 的写法, 它们满足 `OffF`; `offF→rd0` 说这样写的 `Feed₁` 不升界.
- `CopyCoh₂`: 不在接口里; 列出是因为对一切级的折叠要 "同一种类一个界" 到一切深度 (判断, 依据 `HtTowerNStage.no-wmatch`).
- `NotPressed`, `Input₁`, `Down`: 接口 §4, §5 原文.

## 前提实例

- `famO-free`: 无前提. `UniformAll` 的结论 `LoopFix` 在函数外延下成立 (`LocUipNegLoop.uipᴸ→fix`), 前提本身: 有限坐标处成立 (`iso→uniform ∘ isolated-fin`), 一般情形未证.
- `slotFam-sep`: `R` 有实例 `raiseFᴮ`, `raiseFᵒ`, `raiseF⁺`; 世界 $w_\alpha$ 合法 (`loα`), $y_\alpha$ 可入 (`p₀α`), $\omega$ 在 $\alpha$ 某处为真时可入且严格在 $y_\alpha$ 之下 (`ptα`, `ltα`); `SlotFam` 在单个世界上可满足 (`slotFam₀`, `fam₁`); 对整族一致地, 经典地可满足 (判断, 同 `ColimWNeg`).
- `offF→rd0`: `triv : Feed₁ raiseFᵒ`, `offFᵒ`, `w₃`, `lo₃`, `v₃`, `coh₃`, `p₁₃`, `p₂₃` (闭项; `inst` 是实例化的结论).
- `keep₂→¬copy₂`: `raiseF⁺` 满足 `Keep₂` (`refl`); `w₃`, `v₃` 满足 `CopyCoh₂` (`copy₂₃`, `refl`).
- `pressed⇔`: `Local` 有实例 `pr₂`, `prE e` (对一切 $e$).

## 只否定什么, 不否定什么

- **不否定** 接口的 `Feed₁`, `famO`, `SecAt`, `Uniform` 在 $c_1$ (第 1 条是正面定理); 不否定 `Feed₁ R` 对不满足 `OffF` 的 `R`; 不否定 `NotPressed` 的可达成 (第 6 条反而给了一个); 不否定 $\omega$ 处的 `Uniform` (第 2 条只量强度).
- **否定** (编译的): 一切 `RaiseF` 对外层世界族一致地使槽成族 (分离子; 有 `FE₀` 时 WLPO); 保 "槽是族" 的更新 (同); `OffF` 更新上的 `Feed₁` 有非零读回 (在 $2$ 可入的相干世界上); `Keep₂` 更新保 `CopyCoh₂`; 以 `up` 采样的局部输入不被压回.

## 审计

见交回报告 (不改 README/LOG). 选项见各文件头.
