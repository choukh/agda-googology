# NegValX (入口): 跨底折叠的值, 否定一路

> 不含记号. 与构造一路 ValX 配对, 共用接口 [ValXIf](ValXIf.lagda.md) (接口定稿 2026-11-06 08:05; 本路不改它). 作者本轮选定原话: "值: 跨底单调与 TU2/Tω 值定理". 第 4 层: 只新增关系与定理, 不改树, 折叠, 合法性. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`, 不开 K; 不用 UIP 与函数外延作公设 (`NegValXUip` 的定理是以它们为前提的蕴含式).
>
> **对纲领与目标.** 纲领 1: 一切比较都在布劳威尔树上, 第 0 层落到 `TLRuleSpec._≤_`. 纲领 2, 4: 无公理, 不读记号. 纲领 3: 接口的律都在同一个世界 $B$ (字面公共上界) 之下; 本路的反例也在同一个世界里. 目标 "树侧的合法性标准": 本路给出 $\Omega_1$ 层值关系**本身**的一条树侧要求: $\Omega_1$ 本身 (进入分支时移动世界并回灌) 与分量里的拷贝 (不动世界) 层相同、坐标类型相同, 但不能按层比较成 "本身 ≤ 拷贝" (`self≰copy`, `self≤copy-excl`). 这条由折叠的两种策略 (`poΩ`/`poF`) 逼出, 不来自记号. 另外, ValC 的条件 (`Cd` 上的 UIP) 不能经 "自环只有 `hself`" 或 "`cmpB` 结果规范" 去掉: 两者都等价于 UIP (合法树上).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegValX where

import OCF.Lean.NegValXSelf
import OCF.Lean.NegValXIfSelf
import OCF.Lean.NegValXUip
import OCF.Lean.NegValXSh
import OCF.Lean.NegValXCopy
import OCF.Lean.NegValXInst
```

## 地图

| 名字 | 文件 | 陈述 | 档 |
|---|---|---|---|
| **`Self.self≰copy`** | Self §2 | 实例 `I₁`; 合法世界 $B$, $2\lhd B$, $g\,B=2$; 一切目标证据; 跨底折叠到第 0 层, 界 0: $\Phi(\Omega_1^{本身}g)\not\le\Phi(\Omega_1^{拷贝}g)$ (`TL.≤`) | 定理 |
| `Self.copy≤self`, `X≥`, `Y≤` | Self §2 | 反方向成立; $\Phi X\ge\omega+1$, $\Phi Y\le\omega$ | 定理 |
| `inst-ω`, `inst-B₁`, `selfω`, `selfB₁`, `copyB₁` | Self §3 | 世界的前提实例: $\hat\omega$, 与 `TX` 进入一次 $\Omega_1$ 分支后的世界 $B_1=1\boxplus\mathrm{leg}\,\hat\omega+1$ | 定理 |
| `Lg-X`, `Lg-Y`, `g-up`, `lvΩ`, `lvc` | Self §1 | 输入合法; $g$ 对 ValC 的第 0 层关系单调; 两个种类的层都是 $0$ | 定理 |
| **`OnB.self≤copy-excl`** | IfSelf | 对一切 `X : ValX`: `MoX Xn → MoX Yn → ¬ LeX Xn Yn` | 定理 |
| **`by-level-excl`** | IfSelf | 对一切 `X : ValX`: 按层比较 (`ByLevel`) 且两者值合法 ⟹ ⊥ | 定理 |
| **`loop→uip`**, `uip→loop` | Uip §2 | "一切 $r:k\lhd k$ 是 `hself`" ⟺ `Cd` 上的 UIP | 定理 |
| **`canon→K`**, `canon→uipᴸ`, `uip→canon` | Uip §3 | "`cmpB` 比较 $k+1\lhd L$ 与 $k\lhd L$ 得 `inj₁ (hsuc r)` 时 $r$ 是 `hself`" ⟹ 合法 $k$ 处的 K 与 UIP | 定理 |
| `uip→Kfun`, `canon→Kfun` | Uip §4 | UIP (或规范性) ⟹ 函数类型 $\mathbb N\to$ `Cd` 上的 K | 定理 |
| **`copies-same`**, `copy₁`, `copy₂` | Copy | 分量 1 与分量 2 里 $\Omega_1$ 的两个拷贝 (同分支, 同分支路径), 跨底折叠到第 0 层后字面相等 (对一切世界, 目标证据, 界) | 定理 |
| `leg-mono`, `≤leg`, **`sh-mono`**, `sh-infl`, `l11-unrelated` | Sh | ValC 的关系下回灌对世界与坐标单调、不降; `sh-not-mono≤` 的那一对在这里不相关 | 定理 |

## 只否定什么, 不否定什么

- `self≰copy`, `self≤copy-excl`, `by-level-excl`: 只否定 $\Omega_1$ 层的关系把本身与拷贝按层比较成 "本身 ≤ 拷贝" (两者都值合法时) 同时跨底单调. **不否定**: 按 (层, 策略) 比较; 只允许 "拷贝 ≤ 本身" (`copy≤self` 是这个方向的一个正例); 跨底单调本身.
- `NegValXUip`: 只说 ValC 的两条去 UIP 的出路等于 UIP (合法树上). **不说** UIP 不可证 (元定理, 判断), 也不说值定理必须用 UIP.
- `NegValXSh`: 不是否定, 是边界: `sh-not-mono≤` 只否定含 `l≤` 的关系.
- 本路**没有**找到跨底折叠在 ValC 式 (按 (层, 策略) 比较, `l≤l σ`) 关系下的不单调反例. 跨底折叠 "必然不单调" 没有被证明, 也没有被否定 (判断: 世界的移动在值上单调, 因为回灌在 ValC 的关系下单调, `sh-mono`).

## 前提实例

- 世界: `inst-ω`, `inst-B₁` (编译过). 输入: `Lg-X`, `Lg-Y`, 路径 `Self.ndX`, `Self.ndY`.
- `MoX Xn`, `MoX Yn`: 依构造一路的 `MoX`; ValC 式值合法下由 `g-up`, `g-cases` 支持 (判断, 要构造一路的定义才能编译).
- `ByLevel`: 构造一路 08:05 的计划 "Ω≤Ω 按层, 推广到 XS" 满足它 (判断).
- `NegValXUip` 的前提 (UIP, `Canon`) 由函数外延给出 (`ValCUip.fe→uipC`, `uip→canon`; 条件 Funext).

## 文件

| 文件 | 内容 |
|---|---|
| [NegValXSelf](NegValXSelf.lagda.md) | 本身与拷贝: `self≰copy`, `copy≤self`, 实例 (不依赖接口) |
| [NegValXIfSelf](NegValXIfSelf.lagda.md) | 对接口 `ValX`: `self≤copy-excl`, `by-level-excl` |
| [NegValXUip](NegValXUip.lagda.md) | 自环与 `cmpB` 规范性 ⟺ UIP; UIP ⟹ 函数类型上的 K |
| [NegValXSh](NegValXSh.lagda.md) | 回灌在 ValC 的关系下单调 (`sh-not-mono≤` 的边界) |
| [NegValXCopy](NegValXCopy.lagda.md) | 两个分量里的拷贝折叠后字面相同 (同种类关系的盲点, 折叠一侧) |
| 本篇 | 入口 |
