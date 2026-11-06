# 方向 C: 按 `growL′` 写出的无条件闭项 `Tᴰ₊`

> 入口. 作者 2026-11-05 选定 "C 先交字面闭项 Tᴰ₊"; 目标原话 "写出 ψ₀Λ 的候选闭项" (合法、布劳威尔树值、有 FGH 的闭项, 读法可以是判断). 诊断 ([StallDiagnosis](../../Survey/StallDiagnosis.md) §3.3 末段, §5.3) 的要求: 交闭项, 同时交一条关于它的值的结论.
>
> **判决.**
>
> 1. **闭项 (定理).** `TdPlusFold.Tᴰ₊ : A` 无模块参数、无前提; 合法 `Lg-Tᴰ₊` (由形状给出), 停机由检查器保证, 值在 `A` 里 (布劳威尔树), `fgh-Tᴰ₊ = FL.FGH (ord Tᴰ₊)`. 它就是 `DiagK3One.Tᴰ₊` 在 `Fold₊` 的一个居民 `fold₊` 上的值 (定义相等). `fold₊` 的第 $k$ 级把 `L′ (k+2)` 的合法高度投影到两种种类的高度 (`TdPlusUni.pr`), 再交给 `HtTowerFClosed.T⁺`. 回灌只有统一的增量, 不挑分量, 不判定任何相等.
> 2. **"按 `growL′`" 的意思 (定理).** `T⁺` 的世界 $(a,\beta)$ 经 `uW` 是 `L′ k` 的一致世界 (一切 `A` 界为 $a$, 一切高度界为 $\beta$ 的嵌入). 从最小世界 `dW k` 出发经任意有限次 `growL′` 到达的世界都与某个一致世界互模拟 (`TdPlusGrow.reach-uni`), `growL′` 在一致世界上恰好是 $(a,\beta)\mapsto(f\,a,\beta\boxplus\delta)$ (`grow-uni`). 一致世界里有界的坐标都是 $H_0$ 的嵌入, 投影在一致世界上保第一位置与合法 (`TdPlusUni.embI`, `pr-mono`, `Lg-pr`). 一致世界在 `T⁺` 的世界变大时变大 (`Uni.uW≤`). **这个折叠与 "直接在 `L′` 的一切世界上写、回灌用 `growL′`" 的折叠是否值相同, 是判断**: 后者没有写出来. 已知的是两边的世界都落在一致世界里 (`T⁺` 一侧由构造, `growL′` 一侧由 `reach-uni`); 不同处有二: `T⁺` 的回灌把高度界从 $\beta$ 升到 `rd β z₁` ($\beta$ 是它的第一位置), `growL′` 升到 $\beta\boxplus\delta$; 直接写的折叠保留的闭包对 `L′` 的一切更大世界分支, 这里只对一致世界. 判断两处都不改值.
> 3. **值 (定理).** 下界: $t_0+1\le$ `Tᴰ₊` (`TdPlusVal.t₀<T`, $t_0=$ `DiagK3Zero.t₀`), 每一项 $\le$ `Tᴰ₊`, 部分和严格 (`pre<T`); 档是字面前缀式的严格增长 (最低一档, 不说大小). **每一级的输入都与 $\Omega_2$ 互模拟**: `pr-top k : prL (k+1) (λh k) ≈ Ω₂ᴴ`, 对一切 $k$; 所以 `Tᴰ₊` 的每一项都是 `T⁺` 在与 `T-Ω₂` 的输入互模拟的高度上的值 (第 0 项由 `DiagK3Zero.pr₀-top`). 依据是 `top-bd`: 一致世界里级顶那个种类有界的坐标只有 `embK k` 的像.
> 4. **读法 (判断).** 若 `T⁺` 在互模拟的输入上值相等 (没有定理, 与 `DiagK3Zero` 对 `t₀` 的判断同一件事), 每一项读 $\psi_0(\Omega_{\Omega_2})$, `Tᴰ₊` 读 $\psi_0(\Omega_{\Omega_2})\cdot\omega$ (部分和, 上确界不严格高于每一项, `DiagKSum` 的毛刺一侧). **低于 $\psi_0\Lambda$, 低于 $\psi_0(\Omega_{\Omega_2+1})$ (`T-Ω₂+1`), 也低于已有的 `DiagKInst.Tdg₂` ($\psi_0(\Omega_{\Omega_3})$, 判断).** 这比 `DiagK3` 判决第 4 条的判断 ("低于 $\psi_0(\Omega_{\Lambda_1})$, 精确读法未定") 准: 统一 $H_0$ 增量的回灌在**每一级**都把级顶压回 $\Omega_2$, 不只是 `Lev` 种类那一部分. 不要把 `Tᴰ₊` 说成 $\psi_0\Lambda$ 的候选: 它是字面的候选 (目标的字面), 读法不到 (目标的意图).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延. 定义不读记号, 没有验收文件, 没有打开 `EBO`, `Lab`, 标签. 没有改任何已有文件.

## 闭项与 FGH

```text
TdPlusFold.fold₊    : DiagK3One.Fold₊
TdPlusFold.Tᴰ₊      : A                    -- = DiagK3One.Tᴰ₊ fold₊ = Dg t₊
TdPlusFold.Lg-Tᴰ₊   : Lg Tᴰ₊
TdPlusFold.fgh-Tᴰ₊  : ℕ → ℕ                -- = FL.FGH (ord Tᴰ₊)
```

## 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `up-inv`, `ι-inv` | TdPlusUni | `up`, `ι` 的像在第一位置下封闭 | 定理 |
| `Uni`, `Cls`; `uS₀`, `uStep`, `uSup`, **`uLev`**, **`uL`** | TdPlusUni | 一致世界, 第二数类的嵌入及其逆, 种类的分类; 对一切 `Lev x`, `L′ k` | 定义 + 字段即定理 |
| **`pr-mono`**, **`Lg-pr`** | TdPlusUni | 一致世界里的第一位置投影成两种种类的第一位置; 合法投影成合法 | 定理 |
| **`fold₊`**, **`Tᴰ₊`**, **`Lg-Tᴰ₊`**, `fgh-Tᴰ₊` | TdPlusFold | 无条件的 `Fold₊` 与闭项, 合法, FGH | 定义; 合法是定理 |
| `embL≡`, `embK≡` | TdPlusGrow | 嵌入就是 `DiagK3Grow.embL`, `embK` | 定理 (`≡`) |
| **`grow-uni`**, `d-uni`, `grow-cong`, **`reach-uni`** | TdPlusGrow | `growL′` 在一致世界上是 $(a,\beta)\mapsto(f a,\beta\boxplus\delta)$; 最小世界一致; 从它经 `growL′` 到达的世界都一致 (互模拟) | 定理 |
| `Tᴰ₊≡`, `t-zero`, `t-suc` | TdPlusVal | `Tᴰ₊ = Dg t₊`, 第 0 项是 `t₀`, 第 $k+1$ 项是 `T⁺` 在投影级顶上 | 定理 (`refl`) |
| `one≤T⁺`, `t≤T`, `pre<T`, **`t₀<T`** | TdPlusVal | 每项 $\le$ `Tᴰ₊`; `Tᴰ₊` 严格高于 `t₀` 与每个部分和 | 定理 (字面前缀档) |
| `pr-up`, `pr-ι`, `pr-emb` | TdPlusVal | 投影穿过 `up`, `ι` 不变; 投影把嵌入还原成 `up` (互模拟) | 定理 |
| **`pr-top`**, `in-suc` | TdPlusVal | 每一级的输入与 `Ω₂ᴴ` 互模拟, 对一切 $k$ | 定理 |
| **`top-bd`** | TdPlusVal | 一致世界里级顶种类有界的坐标都是 `embK k` 的像 | 定理 |
| `fgh-T⁺`, `fgh-t` | TdPlusView | 每一项的第 0 层树经 `MainViewTower.Zero` 的 View 算的 FGH 等于 `fghA` 在该项上 | 定理 |
| "每项读 $\psi_0(\Omega_{\Omega_2})$, `Tᴰ₊` 读 $\psi_0(\Omega_{\Omega_2})\cdot\omega$" | — | 判决第 4 条 | 判断 |
| "`fold₊` 与直接写的 `growL′` 折叠值相同" | — | 判决第 2 条 | 判断 |

## 与 View 的关系

`Tᴰ₊ : A` 就是布劳威尔树 (`A` 的构造子 `azero`, `asuc`, `alim`), View 是恒等. 中间层: 每一项是 `T⁺ h = sum azero ΨΩ`, $\Psi\Omega$ 是 `HtTowerFTree` 的第 0 层树, [MainViewTower](MainViewTower.lagda.md) 的 `Zero` 给出无条件的 View, 部分良基, FGH 一致; [TdPlusView](TdPlusView.lagda.md) 把它套在各项上 (`fgh-t`). 第 1 层以上的 View (MainViewTower §4 暂停的那一块) 本路没有动. 折叠的输入 `HB (L′ k)` 是带多种 $\Omega$-分支的高度树, 只作下标, 不进值.

## 缺的定理

- `T⁺` 在互模拟输入上值相等 (或互相 $\le$). 有了它, 读法的第一半 ("每项与 `T-Ω₂` 值相等") 变成定理, `Tᴰ₊` 与 `Dg (λ _ → T-Ω₂)` 互相 $\le$. 这是跨实例的比较 (两个输入的差树类型不同), 与 `HtCross` 一类同族, 没有试.
- 与 `Tdg₂`, `T-fb₂ω`, `HtFeedClosed.TΛ` 的值比较: 都要 `T⁺` 对输入的单调, 没有.

## 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `Uni`, `uW` (一致世界) | `growL′` 从最小世界生成的世界 (`reach-uni`) | 树逼的 |
| `emb`, `embI` (嵌入及其逆) | `embL`, `embK` 的形状 (`embL≡`, `embK≡`); 逆由 `up`, `ι` 的像封闭给出 | 树逼的 |
| `Cls` (种类的分类) | 一致世界里种类的坐标只有两种来源: `A` 或 $H_0$ 的嵌入 | 树逼的; 按种类的字面构造子分, 不判定相等 |
| `pr` | `DiagK3Zero.pr₀` 推广到一切级 | 树逼的 |
| `fold₊ = T⁺ ∘ pr` | 复用 `HtTowerF` 的折叠 (它的翻译账在 `HtTowerF`, 回灌形状来自 `HtFeedFold`) | 无新内容 |

归类: 提供信息. 没有新构造子, 没有改树、折叠或合法性, 没有闭包定理, 没有 `Lab`, 没有序数值验收. 信息是一条形状定理 (`pr-top`/`top-bd`): 统一 $H_0$ 增量的回灌在每一级把级顶压回 $\Omega_2$, 所以选项 (ii) 不攀爬. 这一步没有加深翻译 (没有读规则的新字段), 也没有带来攀爬的新思路; 它把 "方向 C 的闭项值多少" 从开放的判断收窄成 "等于 `T-Ω₂` 档 (判断, 条件于一条互模拟不变性)".

## 审计

- **从头编译** (删去本路六个模块的 `.agdai`, 依赖用已有接口, 堆上限 6G): 入口退出码 0, 5.0 秒, 峰值常驻约 0.52G.
- **导入闭包** (`probes/Survey/scripts/tdplus/audit.sh`, `--only` 表同 `DiagK`, 加 `OCF.Align.TdPlus`, `MainView`, `BrwView`, `BrwWf`): `TdPlusUni` 19 个模块 (本地 10), `TdPlusFold` 35 (本地 25), `TdPlusVal` 36 (本地 26), `TdPlusGrow` 37 (本地 27), `TdPlusView` 45 (本地 34), 入口 47 (本地 36); 都是退出码 0, 禁用表 0, `--only` 之外 0. 闭项 `Tᴰ₊` 与证书 `Lg-Tᴰ₊` 在 `TdPlusFold` 的闭包里, 不含 View 一族.
- **定义级切片** (`depslice.py`, 到达块 / 记号模块块 / 别处记号词): `TdPlusFold:Tᴰ₊` 321/0/0, `Lg-Tᴰ₊` 323/0/0, `fgh-Tᴰ₊` 322/0/0, `fold₊` 255/0/0, `TdPlusVal:pr-top` 125/0/0, `t₀<T` 341/0/0, `TdPlusGrow:reach-uni` 143/0/0, `TdPlusView:fgh-t` 397/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用, 不说明定义没有受记号启发.
- **禁用构造**: 六个文件里没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, `Funext`; 选项都是 `--safe --without-K --lossy-unification`.
- **代码行** (agda 块里非空非注释): `TdPlusUni` 148, `TdPlusFold` 28, `TdPlusVal` 95, `TdPlusGrow` 138, `TdPlusView` 28, 入口 7; 合计 444. 闭项本身 (`TdPlusUni` + `TdPlusFold`) 176 行, 其余是值, `growL′` 的对应与 View.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TdPlus where

open import OCF.Align.TdPlusUni using (up-inv; ι-inv; Cls; cA; cH; Uni; uS₀; uStep; uSup; uLev; uTwo; uL; module Pr) public
open import OCF.Align.TdPlusFold using (prL; Lg-prL; foldK; Lg-foldK; fold₊; Tᴰ₊; Lg-Tᴰ₊; fgh-Tᴰ₊) public
open import OCF.Align.TdPlusVal using (t₊; Tᴰ₊≡; t-zero; t-suc; one≤T⁺; t≤T; pre<T; t₀<T; pr-up; pr-ι; pr₀-up; pr-emb; pr-top; in-suc; top-bd) public
open import OCF.Align.TdPlusGrow using (embL≡; embK≡; grow-uni; d-uni; grow-cong; Reach; r-d; r-g; reach-uni) public
open import OCF.Align.TdPlusView using (fgh-T⁺; fgh-t) public
```
