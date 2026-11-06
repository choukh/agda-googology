# `T⁺` 对输入单调: 否定一路 (入口)

> 不含记号. 作者选定原话: "A2: T⁺ 对输入单调". 本篇是否定一路 (前缀 `NegTpMono`); 构造一路前缀 `TpMono`, 共用接口 [TpMonoIf](TpMonoIf.lagda.md) (**对着的版本: 接口定稿 2026-11-05 12:11 的 §1–§4; 12:23 只增的 §5 见下**). 本路只导入接口, 不另造接口, 不直接导入构造一路的其他文件 (接口 §5 自己导入 `TpMonoHs`, `TpMonoHl`, 所以它们在本路的导入闭包里).
>
> **接口 §5 (12:23 增).** `ChangeHs`, `MonoStepHs`, `MonoHl` 是具体折叠之间的值不等式, 不是律的形状. 本路没有尝试否定它们 (判断: 它们是单种类折叠上 `MonoPort6`/`7` 已证成的同名步骤在两种种类折叠上的对应, 没有否定的迹象; 否定要算具体折叠的值, 与构造同量).
>
> **判决: 对接口本身, 否定写不出 (本路没有找到); 接口排除的两种形状, 否定成立 (定理).**
>
> 1. **接口的律合起来有模型** ([NegTpMonoBlind](NegTpMonoBlind.lagda.md) `rk-laws`, `rk-steps`, 定理): 一个不是 `T⁺` 的 `F` 满足 `Laws` (a)(b)(c) 与 `Steps`. 所以任何否定都必须用 `T⁺` 的定义; 本路在 `T⁺` 上没有找到反例 (`LgIrr` 的有限测试见第 5 条).
> 2. **接口排除的 "某一个世界里的第一位置" 是假的** ([NegTpMonoWorld](NegTpMonoWorld.lagda.md), 定理, 对任意输出合法的 `F`, 含 `T⁺`): 严格版无前提 (`no-fst<W`, 新种类 `no-fst<Wᴴ`); 非严格版以后继与 ℕ-极限两步严格为前提 (`no-fstW`, `no-fstWᴴ`); `T-Ω₂` 的输入上 "一切新种类分支都不高于整体" 也假 (`no-allΩ₂`). 接口 (b) 段把这件事写成判断 ("碰 `no-all` 那一类"), 这里是定理.
> 3. **接口排除的 "按值单调" 与一步律 `s-hΩ` 不相容** (`no-valmono`, 定理): 只要输入上的关系把常数 $0$ 分支的 $\Omega$-极限放在 $0$ 之下 (通常的值序 `_≤ᴴ_` 就是, `Ω0≤ᴴ0`). 所以 `T⁺` 若满足 `Steps`, 它就**不是**按值单调的: 它分得开值相等的两个输入 (输入侧的 `blindᴬ` 现象).
> 4. **接口的律对非最小坐标是盲的** (`blind₂`, `blindᴬ₂`, 定理): 有满足 `Laws` 与 `Steps` 的 `F` 使 $F(2)\not\le F(\Omega_2^H)$. 单靠接口推不出 "`T⁺ 2 ≤ T-Ω₂`" 这类要用 $\Omega$-极限非最小坐标的比较.
> 5. **(a) 与外延** ([NegTpMonoSim](NegTpMonoSim.lagda.md)): `LgB` 不是命题 (`l₁≢l₂`, 定理); `SimInv F → LgIrr F` (定理); `Funext → LgIrr F → SimInv F` (**条件**). 外延只消掉 "输入不同" 那一半, 消不掉 "合法性证明不同" 那一半. 有限测试 ([NegTpMonoTest](NegTpMonoTest.lagda.md)): 两个合法性证明上 `T⁺` 的输出在宽 3 深 12 同形 (`t12`), 比较器有分辨力 (`c8`). `T⁺` 的输出范式里字面读了合法性证明 (`refl` 不过, 报错原文见测试文件).
> 6. **(a) 的一个后果** (`collapse`, `collapse₀`, 条件定理, 前提 `SimInv T⁺`): `Tᴰ₊` 的每一项与 `T-Ω₂` 在值上互相 $\le$. `TdPlusVal` 的同名判断由此成为以 (a) 为前提的定理.
>
> **对纲领与目标.** 纲领 1-3: 本路的否定都是对 "律的形状" 的, 没有新树、新折叠; 第 2, 3 条正是壁垒的影子 (手册 §3.1: "在一个世界里有界的任意坐标", "只看值") 在 `T⁺` 上的具体形状, 证明不经 LPO, 是直接矛盾. 纲领 4: 导入闭包与切片干净 (审计). 目标 "让树自足": 第 1, 4 条说明接口的律是树侧的、与记号无关的, 但它们只约束最小坐标, 要比较 $\Omega$-极限的大小还缺一类律 (判断).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K. `Funext` 只在 `NegTpMonoSim` 作前提 (`≈→≡`, `fe-irr→sim`), 标 "条件".

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegTpMono where

open import OCF.Align.NegTpMonoWorld using
  (Ωᴬ; lΩᴬ; eᴬ; eH; FstMonoW; FstMono<W; StepsSL; steps→SL; id≤F; id≤FH; no-fst<W; no-fstW; no-fst<Wᴴ; no-fstWᴴ; no-allΩ₂;
   ValMono; no-valmono; _≤ᴴ_; Ω0≤ᴴ0; no-fst<W⁺; no-fstW⁺; no-allΩ₂⁺; no-valmono⁺) public
open import OCF.Align.NegTpMonoBlind using (rk; Lg-rk; Fᵣ; rk-laws; rk-steps; blind₂; blindᴬ₂) public
open import OCF.Align.NegTpMonoSim using (h₂; l₁; l₂; l₁≢l₂; sim→irr; Funext; ≈→≡; fe-irr→sim; collapse; collapse₀) public
import OCF.Align.NegTpMonoTest

-- 前提 StepsSL 的实例 (一个不是 T⁺ 的 F)
inst-SL : StepsSL Fᵣ Lg-rk
inst-SL = steps→SL Fᵣ Lg-rk rk-steps
```

## 定理表

| 名字 | 文件 | 陈述 (白话) | 档 |
|---|---|---|---|
| `id≤F`, `id≤FH` | World | `s-hs`, `s-hl` 成立 ⇒ $a\le F(e\,a)$, $a\le F(\mathrm{up}(e\,a))$ | 定理 (前提 `StepsSL`) |
| **`no-fst<W`**, **`no-fst<Wᴴ`**, `no-fst<W⁺` | World | $\neg$ `FstMono<W F` (严格第一位置只在一个合法世界里) | **否定, 定理, 无前提** |
| **`no-fstW`**, **`no-fstWᴴ`**, `no-fstW⁺` | World | `StepsSL F` ⇒ $\neg$ `FstMonoW F` | **否定, 定理** |
| **`no-allΩ₂`**, `no-allΩ₂⁺` | World | `StepsSL F` ⇒ $\neg\forall c.\ F(\mathrm{up}\,c)\le F(\Omega_2^H)$ | **否定, 定理** |
| **`no-valmono`**, `no-valmono⁺` | World | $R\,Z\,0$ ⇒ `Steps F` ⇒ $\neg$ `ValMono F R` | **否定, 定理** |
| `_≤ᴴ_`, `Ω0≤ᴴ0` | World | 通常的值序; 前提 $R\,Z\,0$ 的实例 | 定义, 定理 |
| `rk-laws`, `rk-steps` | Blind | `Laws Fᵣ`, `Steps Fᵣ` | 定理 (模型) |
| **`blind₂`**, **`blindᴬ₂`** | Blind | $\exists F$. `Laws` ∧ `Steps` ∧ $F(2)\not\le F(\Omega_2^H)$ (旧种类同理) | **盲, 定理** |
| `l₁≢l₂` | Sim | 同一高度两个不相等的合法性证明 | 定理 |
| `sim→irr` | Sim | `SimInv F → LgIrr F` | 定理 |
| `≈→≡`, `fe-irr→sim` | Sim | `Funext →` 互模拟 ⇒ 相等; `Funext → LgIrr F → SimInv F` | **条件** (`Funext`) |
| `collapse`, `collapse₀` | Sim | `SimInv T⁺` ⇒ $t_k$ 与 `T-Ω₂` 值互相 $\le$ | 条件定理 (`SimInv T⁺`) |
| `t12`, `c8` | Test | 两个合法性证明上的输出宽 3 深 12 同形; 对照分得开 | 有限测试 |

## 每条律为什么是构造一路要的; 只否定什么

| 律 / 形状 | 构造一路为什么要 | 本路的结论 | 只否定什么, 不否定什么 |
|---|---|---|---|
| (b) 严格版只在一个世界 (`FstMono<W`) | 最自然的写法 `∀ {w} → a ⊲⁺[ w ] b → …` 把 $w$ 放在外面; 要 "$\Omega$-极限高于它的分支" 也就要它 | `no-fst<W`: 假, 无前提 | 只否定 "外层任取一个合法世界". 不否定接口的 `FstMono<` (路径对一切世界), 也不否定 "世界有界于某个 $<F(\Omega^A)$ 的值" 的版本 (没有试) |
| (b) 非严格版只在一个世界 (`FstMonoW`) | 同上, 值比较要非严格的那条 | `no-fstW`: 与 `s-hs`, `s-hl` 不相容 | 只否定与后继/极限严格同时成立; 单独的 `FstMonoW` 有常数模型, 不否定 |
| 新种类分支一律低于 $\Omega_2^H$ | `FamFold`/`TdPlus` 要比较 `T-Ω₂` 与它的分支 | `no-allΩ₂`: 与 `s-hs`, `s-hl` 不相容 | 只否定 "一切 $c$". 对有界的 $c$ (例如走过的坐标) 不说什么 |
| 按值单调 (`ValMono`) | 想把值相等的输入 (同一个极限的不同写法, 分支被吸收) 送到相等的输出 | `no-valmono`: 与 `s-hΩ` 不相容 | 只要关系含 $Z\preccurlyeq0$. 不否定按值的**上界**律或只在 ℕ-极限上按值的律 (没有试) |
| (a) `SimInv` | `pr-top`, `pr₀-top` 只给互模拟; 要它才能把 `Tᴰ₊` 的项与 `T-Ω₂` 比 | 有模型; `Funext` 下 ⟺ `LgIrr`; 推出 `collapse` | 不否定. "不需要外延" 是判断 |
| `LgIrr` | `T⁺` 读合法性证明, 两个证明给两棵树 | `LgB` 不是命题 (定理); 测试同形 | 不否定 |
| (b) `FstMono`, `FstMono<` (一切世界), (c) `ShiftMono`, `Steps` | 序数值比较的主干 | 有模型; 对非最小坐标盲 | 不否定; 盲定理只说 "律不够", 不说 `T⁺` 不满足它们 |

## 前提实例

- `StepsSL F` (`no-fstW`, `no-allΩ₂` 的前提): `inst-SL` (由 `NegTpMonoBlind.rk-steps`) 给出 `Fᵣ` 的实例; 对 `T⁺` 是构造一路要证的 (`TpMonoHs.hs-reduce` 归结 `s-hs`).
- `Steps F` (`no-valmono`): 同上, `rk-steps`.
- `R Z hz` (`no-valmono`): `Ω0≤ᴴ0`.
- `Funext` (`fe-irr→sim`): 在 `--safe --without-K` 下不可证, 也不可否证 (判断, 标准事实); 只作前提.
- `SimInv T⁺` (`collapse`): 构造一路的目标; 对 `Fᵣ` 的同型律成立 (`rk-laws`), 所以形状可满足.
- 否定的反例本身都是合法输入: `lΩᴬ`, `lΩ₂`, `Lg-e`, `Lg-eH`, `lZ`; 世界合法 (`la , tt`, `tt , Lg-e a la`).

## 第一个障碍 (否定接口本身)

要否定 `Laws T⁺` 或 `Steps T⁺`, 只能用 `T⁺` 的定义 (第 1 条). 最便宜的候选是 `LgIrr` (合法性证明在折叠里被 `cmpB` 读): 两个证明上的输出在测试范围内同形, 没有找到分开的路径. 其余各律在 `T⁺` 上的反例要算 $\Omega$-极限处回灌的值, 本路没有做 (判断: 构造一路的 `MonoPort` 一族在单种类折叠上对应的律都已证成或无否定迹象).

## 审计

- **编译** (从仓库根, 退出码不经管道): 删本路五个模块的 `.agdai` (`NegTpMono`, `NegTpMonoWorld`, `NegTpMonoBlind`, `NegTpMonoSim`, `NegTpMonoTest`, 精确模块名), 依赖用共享接口, `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/NegTpMono.lagda.md +RTS -M6G -RTS`: 退出码 0, 约 33 秒 (几乎全在 `t12`), 峰值常驻约 0.6G.
- **禁用构造**: 五个文件的代码块里 `postulate`, 洞, `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY_CHECK`, `trustMe` 都是 0; 选项都是 `--safe --without-K --lossy-unification`. `Funext` 只在 `NegTpMonoSim` (定义为类型, 作 `≈→≡`, `fe-irr→sim` 的前提) 与入口的再导出里出现.
- **导入闭包** (`importclosure.py`, 不加 `--only`): 入口 45 个模块 (本地 35), `World` 36, `Blind` 37, `Sim` 41, `Test` 42; 禁用表命中 0, 退出码 0.
- **定义级切片** (`depslice.py`, 到达块 / 记号模块块 / 别处记号词): 正对照 `Om1HnAccept:label-term₀` 1188/92/58. `no-fst<W` 83/0/0, `no-fstW` 79/0/0, `no-allΩ₂⁺` 235/0/0, `no-valmono⁺` 215/0/0, `blind₂` 112/0/0, `rk-laws` 93/0/0, `collapse` 321/0/0, `fe-irr→sim` 67/0/0, `l₁≢l₂` 64/0/0, `t12` 203/0/0, `inst-SL` 86/0/0. 切片看不见模块应用; 记号无关由导入闭包保证.
- **行数** (代码块里非空非注释行 / 文件行): `NegTpMonoWorld` 130/218, `NegTpMonoBlind` 97/150, `NegTpMonoSim` 68/112, `NegTpMonoTest` 23/43, 入口 10/89. 合计代码 328 行, 全部手写.

## 翻译账

不读记号, 没有新树、折叠或合法性. 新增的只有: 嵌入 $e$ (`A` 原样换构造子), 反例输入 $\Omega^A$, $Z$ (由接口 (b) 的定义域与 `MonoPort9Neg.no-all` 的论证逼出), 值序 `_≤ᴴ_` (前提的实例, 只在否定里用), 模型 `rk` (只作反模型). 归类: 提供信息 (否定定理划出不能有的律的形状; 盲定理说明接口的律缺哪一类).
