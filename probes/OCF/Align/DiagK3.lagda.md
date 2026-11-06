# 可数层的对角, 第三轮: `Lev` 新种类只在第 0 层回灌 (DiagK2 的选项 (ii))

> 接 [DiagK2](DiagK2.lagda.md). 入口. **判决: 第 0 级做到 (定理); 一切级的折叠暂停 (未走通, 不是否定).**
>
> 1. **第 0 级 (定理).** `towerL′` 第 0 级 (`L′ 1`) 的级顶以下**没有 `Lev` 种类的层** (`true-below`, `noLev₀`). 所以第 0 级的折叠把 `Lev` 一半投影掉 (`pr₀`, 保合法 `Lg-pr₀`) 再用 `HtTowerFClosed.T⁺`: `fold₀` 对 `HB (L′ 1)` 的一切合法高度, 合法由形状给出; 闭项 `t₀ = fold₀ (λh 0)`, `Lg-t₀`, `fgh₀`. `pr₀ (λh 0)` 与 `Ωtop S₀` 互模拟 (`pr₀-top`), 所以 `t₀` 与 `HtTowerFClosed.T-Ω₂` 是互模拟输入上的同一个折叠 (值相等是判断, 读 $\psi_0(\Omega_{\Omega_2})$). 这比选项 (ii) 更省: 第 0 级级顶下 `Lev` 种类既不回灌也不保留, 没有损失. [DiagK3Zero](DiagK3Zero.lagda.md).
> 2. **障碍的位置 (定理).** `Lev` 种类第一次进层是第 1 级 (`L′ 2`): `lev₁`, `lev₂` 在合法世界里给出 `λh 1` 下的层, 分支种类是 `L′ 1` 的 `Lev` 新种类, 坐标类型分别是 $H_0$ 与 `HB S₁` (`E₁`, `E₂`). 缺的一块缩成 `Fold₊` (第 $k\ge1$ 级); 条件候选 `Tᴰ₊` 合法 (`Lg-Tᴰ₊`), 第 0 项就是 `t₀` (`t-zero`). [DiagK3One](DiagK3One.lagda.md).
> 3. **选项 (ii) 要的世界操作 (定理).** 只增长的世界: 一切 `A` 界接 $f$, 一切高度界接 `embL` $h$ ($h$ 是第二数类的高度), 在 `L′ k` 的整个世界上, 一切 $k$ (`growL′`, `growL′-≤`, `lg-growL′`), 不判定. 在 `κH` 与坐标为 $H_0$ 的 `Lev` 新种类处恰好是 "旧界 $\boxplus h$" (`at-κH`, `at-lev`, `refl`); 这两种种类的回灌增量正是第 1 层的读回 (值在 $H_0$ 里), 所以对它们只增长的世界是**忠实的**. 比 `CohW2Grow.growA` (可数增量) 高一档. [DiagK3Grow](DiagK3Grow.lagda.md).
> 4. **第一个障碍 (形状是定理, 读法是判断).** 坐标是 `HB (Lev x)`, $x\ne$ `hz` 的 `Lev` 新种类 (第一个是 `κ₂`, 坐标 `HB S₁`): 忠实的增量是更高层的读回, 含新种类的 $\Omega$-节点; 但 "同一个增量进一切分量" 只能用一切分量共有的种类 (坐标 `hz` 处只有 `S₀`), 增量进 `κ₂` 的坐标后**没有新种类的节点** (`noNew-emb`, `⊞-noNew`): 每一步回灌都跨不过新种类的一个 $\Omega$-极限. 判断: 这让第 1 级起 `Lev` 种类的坍缩退成坐标为 $H_0$ 那一档, 读法低于 $\psi_0(\Omega_{\Lambda_1})$, 所以按选项 (ii) 写出的 `Fold₊` 读不到 $\psi_0\Lambda$ (精确读法未定). 恰好改一个分量要弱判定 (`DiagKLev.updL′→wdec`, `CohW2Need.raise-Lc→wdec`); 选项 (iii) (大世界搬回小世界) 管的是更高目标看见被升高的分量, 不提供增量, 没有试 (判断).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延. 定义不读记号, 没有验收文件, 没有打开 `EBO`, `Lab`, 标签. 没有改任何已有文件.

## 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `true-below`, `noLev₀` | DiagK3Zero | 第 0 级级顶以下全是 `ι true` 的像; 没有 `Lev` 种类的层 | 定理 |
| `bdBot`, `pr₀-mono`, **`Lg-pr₀`** | DiagK3Zero | 最小 `Lev` 世界里只有底坐标有界; 投影保第一位置, 保合法 | 定理 |
| **`fold₀`, `Lg-fold₀`** | DiagK3Zero | 第 0 级对一切合法高度的折叠, 合法 | 定理 |
| `pr∘ι`, `pr₀-top` | DiagK3Zero | 投影在级顶上与 `Ωtop S₀` 互模拟 | 定理 |
| `t₀`, `Lg-t₀`, `fgh₀` | DiagK3Zero | 第 0 级闭项, 合法, FGH; 读 $\psi_0(\Omega_{\Omega_2})$ | 定理 (读法是判断) |
| `embL`, `growW`, `grow-≤`, `lg-grow` | DiagK3Grow | $H_0$ 进一切 `Lev x`; 一切分量接同一增量, 变大, 保合法 | 定理 |
| **`growL′`, `growL′-≤`, `lg-growL′`** | DiagK3Grow | 同上, `L′ k` 的整个世界, 一切 $k$ | 定理 |
| `at-κH`, `at-lev`, `at-A`, `E-hs` | DiagK3Grow | 坐标为 $H_0$ 的种类与 `A` 处恰好是旧界接增量 | 定理 (`refl`) |
| `lgdW`, **`lev₁`, `lev₂`**, `head₁`, `head₂`, `E₁`, `E₂` | DiagK3One | 第 1 级级顶下有 `Lev` 新种类的层 (合法世界) | 定理 |
| `Fold₊`, `mkFd`, `Lg-Tᴰ₊`, `t-zero` | DiagK3One | 缺的一块缩到 $k\ge1$; 条件候选合法 | 定理 (条件于 `Fold₊`) |
| `NoNew`, `up-noNew`, `⊞-noNew`, **`noNew-emb`** | DiagK3One | `κ₂` 的坐标在只增长的世界里的增量没有新种类的节点 | 定理 |
| "按选项 (ii) 读法低于 $\psi_0\Lambda$" | — | 见判决第 4 条 | 判断 |

## 闭项与读法

- `t₀` (第 0 级): 合法, 有 FGH; 读 $\psi_0(\Omega_{\Omega_2})$ (判断, 与 `T-Ω₂` 互模拟输入). 不比 `Tdg₂` ($\psi_0(\Omega_{\Omega_3})$) 强.
- `Tᴰ₊` (条件于 `Fold₊`): 若 `Fold₊` 的第 $k$ 级读 $\psi_0(\Omega_{\Lambda_{k+1}})$, 则读 $\psi_0\Lambda$ (判断, 同 `DiagKTop`). `towerL′` 仍没有无条件的、读 $\psi_0\Lambda$ 的 `LevelFold`.

## 第一个障碍

判决第 4 条. 下一步可试 (判断, 没有试): 回灌坐标**取成** "旧界 $\boxplus\ \mathrm{tr}_{c_0\to c_0}(\text{增量})$", 一切分量 $c$ 接 $\mathrm{tr}_{c_0\to c}(\text{增量})$, $\mathrm{tr}$ 沿种类的路径做结构的翻译 (对不上处退成底). 这样恰好的位置是 `refl`, 忠实只差互模拟 ($\mathrm{tr}_{c_0\to c_0}\,x\approx x$), 不要函数外延 (`CohW2Grow` 判断要函数外延, 是因为要求坐标恰好是增量本身). 开放的是对不上的分量里翻译结果的合法性 (分支单调要跨世界的对应), 与 "结构对上但下标不同" 的分量把不同的种类混为一谈对读法的影响. 这也是 `CohW2` 那条线的问题, 本路没有重复.

## 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `pr₀` | 第 0 级级顶下没有 `Lev` 种类 (`noLev₀`), 投影在级顶上无损 | 树逼的 |
| `growL′`, `embL` | 恰好改一个分量要判定 (`updL′→wdec`); 一切分量共有的只有底种类 | **树逼的**; 增量 "旧界 $\boxplus$ 读回" 的形状沿用 `HtTowerFFold` 的 `κc`, `κc₁` |
| `Fold₊` | 把 `LevelFold` 缺的一块缩到 $k\ge1$ | 接口, 无新内容 |
| `noNew-emb` | 划出只增长的世界给不了的东西 | 否定形状 (提供信息) |

归类: 摆脱侧, 提供信息. 没有新构造子, 没有闭包定理, 没有验收, 没有标签.

## 层的行数 (定义级切片, `probes/Survey/scripts/diagk3/locslice_diagk3.py`, 口径同 `locslice_diagk.py`)

| 闭项 | 层 1 | 层 2 (去共用) | 层 3 (去共用) |
|---|---|---|---|
| `t₀` | 225 | 1071 (988) | **1081** (998) |
| `Tᴰ₊` (条件) | 237 | 1136 (1053) | 1138 (1055) |

都在 1513 之下. `t₀` 的层 3 里 `DiagK3Zero` 只占 57 行, 其余是 `HtTowerF` 的折叠 (导入, 没有复制).

## 审计

- 导入闭包 (`--only` 表同 `DiagK`): `DiagK3` 34 个模块 (本地 24), 退出码 0, 禁用表 0, `--only` 之外 0.
- 定义级切片: `DiagK3Zero:Lg-t₀` 243/0/0, `DiagK3One:Lg-Tᴰ₊` 282/0/0, `DiagK3Grow:lg-growL′` 86/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58.
- 禁用构造: 无. 从头编译 (删去本路的 `.agdai`, 堆上限 6G): 退出码 0.
- 文件级代码行 (非空): `DiagK3Zero` 112, `DiagK3Grow` 72, `DiagK3One` 94, 入口 5.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DiagK3 where

open import OCF.Align.DiagK3Zero using (true-below; noLev₀; pr₀; Lg-pr₀; fold₀; Lg-fold₀; _≈_; pr∘ι; pr₀-top; t₀; Lg-t₀; fgh₀) public
open import OCF.Align.DiagK3Grow using (embL; growW; grow-≤; lg-grow; growL′; growL′-≤; lg-growL′; at-κH; at-lev; at-A; E-hs) public
open import OCF.Align.DiagK3One using (lgdW; lev₁; lev₂; head₁; head₂; E₁; E₂; Fold₊; mkFd; Tᴰ₊; Lg-Tᴰ₊; t-zero; NoNew; up-noNew; ⊞-noNew; noNew-emb) public
```
