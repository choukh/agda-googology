# 可入下标上的比较式更新 (入口): 构造一路

> 不含记号. 方向 A (作者原话 "A 可入下标比较式更新"), 配合 [Survey/StallDiagnosis.md](../../Survey/StallDiagnosis.md) §2.2, §2.4, §3.3, §5.1, §5.4. 接口 [AdmWIf](AdmWIf.lagda.md) (与否定一路 `AdmWNeg*` 共用). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示; 函数外延只在 [AdmWUip](AdmWUip.lagda.md) 作前提 (条件).
>
> **判决.**
>
> 1. **第一条引理成立 (定理).** 在最小实例 (`Lev (Ωtop S₀)` 的后继分量, 下标带证据) 上, 比较式更新 `raiseᴮ` 满足接口的四条律 ([AdmWRaise](AdmWRaise.lagda.md)): 在 $(c_0,p_0)$ 处恰好接长 (**对一切证据**, 不只字面 `hself`), 严格在 $c_0$ 之下不动, 世界只增, 保合法. 同时 `UniTr.Open-build` 的可入版成立 (`adm-build`). 诊断 §3.3 义务 2 的 `--without-K` 难点 (`cmpB p₀ p₀` 经 `mo` 不必给 `hself`) 由一个对角上定义地给 `hself` 的比较 `cmpB₀` 绕开 ([AdmWCmp](AdmWCmp.lagda.md), `cmpB₀-diag`); 没有用 UIP.
> 2. **第二条引理: 需要跨证据的相干; 无条件的版本未走通.** `cmpK` 在同一证据的分量里是定义, 跨证据时要把一边的界搬进另一边的分量, 这一步要分量之间的关系 (相干). 有相干就有 `cmpK` (`coh≡→cmpK`, `coh≤→cmpK`, 定理). 相干由更新保持吗:
>    - 沿路径嵌入的 `raiseᴮ`: **不保** (`raise-splits`, 定理): 同一坐标 $\omega$ 的两个证据经界的单调 `mo` 得到两条不同的路径 $3\lhd\omega$, 增量落进 `sup ℕ` 的第 3, 第 4 个分量, 两个槽互不为第一位置; 更新后的合法世界里 `cmpK` 失败 (`raised-no-cmp`, `¬cmpK`). 这是拷贝墙在 "$c_0$ 之上" 的定理形式.
>    - 只升 $c_0$ 本身的 `raise₀ᴮ` (可入下标上的选择性更新, 带 `off` 律 `off₀`): 四条律是定理; 保 `Coh≡` 恰好要同一坐标的两条相等证明搬出同一个增量, 在 `UIPᴴ` 之下成立 (`uip→raise₀-coh`, 条件定理), 不加 `UIPᴴ` 未证出. `UIPᴴ` 由函数外延推出 (`fe→uip`, 条件).
>    - 合起来 `dirA-cond : UIPᴴ → …` (条件定理): 有满足四条律且保相干的更新, 相干世界上有 `cmpK`.
>
>    所以按简报的判据 "若需要证据相等, 停下": 停在这里. 需要的是 **同一坐标 $c$ 的两个可入证据之间的关系**: 对 `raiseᴮ` 是两条路径 $c_0\lhd c$ 的嵌入相同 (被 `raise-splits` 否定), 对 `raise₀ᴮ` 是两条相等证明 $c_0\equiv c$ 的搬运相同 (`HB S₀` 的 UIP, `--without-K` 下我没有证出, 判断它要函数外延).
> 3. **第三步 (回灌) 没有做.** 简报的条件是两条引理都过; 第二条只在条件下过, 不开回灌. 没有新的闭项.
>
> **对纲领与目标.** 不触壁垒 (没有序, 没有全局三歧; 一切比较都在同一个界 $b$ 之下). 第一条引理是诊断命题 W⁺ 构造一半的定理: 可入下标上的选择性更新写得出, 不推出任何判定 (`off₀` 是 `DiagKLev.UpdS.offS` 限制到可入下标后的定理). 第二条说明拷贝墙落在哪两个对象上 (路径嵌入的路径依赖; 高度相等证明的唯一性), 前者有编译的否定, 后者是 K 型的事实, 不是禁忌.
>
> **交付拆成两条.** (a) 合法的构造: `raiseᴮ`, `raise₀ᴮ` (两个满足四条律的更新), `adm-build`; 没有新的闭项. (b) 关于值的定理: 没有 (这一路不涉及序数值).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AdmW where

open import OCF.Align.AdmWIf public
open import OCF.Align.AdmWCmp public
open import OCF.Align.AdmWRaise public
open import OCF.Align.AdmWCoh public
open import OCF.Align.AdmWUip public
```

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `cmpB₀-diag` | AdmWCmp | `cmpB₀ p p ≡ inj₁ hself`, 一切 $p$ | 定理 |
| `dec₀-diag` | AdmWCmp | `dec₀ (cmpB₀ p p) ≡ inj₁ refl` | 定理 |
| `raiseᴮ` | AdmWRaise | 沿路径嵌入的更新, 四条律 `at` `below` `mono` `legal` | 定理 |
| `adm-build` | AdmWRaise | `Open-buildᴬ`: 可入下标上的 `UniTr`, 忠实取 `≡` | 定理 |
| `cmpK-same` | AdmWCoh | 同一证据的分量里两个坐标可比 | 定理 |
| `coh≡→cmpK`, `coh≤→cmpK` | AdmWCoh | 相干世界上有 `cmpK` (对一切 `SupB`) | 定理 |
| `raise-splits` | AdmWCoh | 合法相干世界, `raiseᴮ` 之后 `Coh≤` 不成立 | 定理 (否定, 只否定 `raiseᴮ` 保相干) |
| `¬raise-coh≤`, `¬raise-coh≡` | AdmWCoh | `raiseᴮ` 不满足 `RaiseCoh` | 定理 (同上) |
| `raised-no-cmp`, `¬cmpK` | AdmWCoh | 更新后的合法世界里种类 $(\omega,\text{new})$ 两坐标不可比; `Slot` 上无 `CmpK` | 定理 (否定, 只否定无相干前提的 `CmpK`) |
| `raise₀ᴮ`, `off₀` | AdmWCoh | 只升 $c_0$ 的更新, 四条律, 可入下标上的 `off` | 定理 |
| `uip→raise₀-coh` | AdmWCoh | `UIPᴴ` 之下 `raise₀ᴮ` 保 `Coh≡` | 条件定理 (UIPᴴ) |
| `dirA-cond` | AdmWCoh | `UIPᴴ` 之下: 保相干的更新 + 相干世界上的 `cmpK` | 条件定理 (UIPᴴ) |
| `fe→uip` | AdmWUip | `Funext → UIPᴴ` | 条件定理 (Funext) |

**前提实例.** `raise-splits` 的世界 `(wO, v₀)`: 合法 (`lgW₀`), 相干 (`coh≡₀`), 增量合法 (`Lg-δ₃`); 两个证据 `pω₁`, `pω₂` 是闭项. `uip→raise₀-coh` 的 `UIPᴴ`: 由 `fe→uip` 从函数外延推出 (函数外延在立方模型中成立; 在本仓库只作前提). `Coh≡` 的世界: `(wO, v₀)`.

**第一个障碍.** `cmpK` 跨证据. 具体位置: [AdmWCoh](AdmWCoh.lagda.md) `coh≡→cmpK` 里 `subst (…) (coh c p′ p) e′` 那一步, 没有 `coh` 就没有可写的项 (否定一路的 `AdmWNegCopy.copy→⊥` 说逐分量合法时它不存在). 有了 `coh`, 下一处是更新保 `coh`: `raiseᴮ` 被 `raise-splits` 否定; `raise₀ᴮ` 停在 `incD-irr` 的 `inj₁ e, inj₁ e′` 情形, 要 `e ≡ e′`.

**翻译账.** 本路不读记号. 新定义: `SupB` (世界以 (坐标, 证据) 为下标, 来自诊断 §3.3, 由 "比较要字面公共上界" 逼出, 树侧); `cmpB₀` (只为 `--without-K` 下的对角律, 是脚手架, 序数值不需要); `raise`/`raise₀` 的选择形状 (嵌入沿路径是 `UniTrNeg.emb⊲`, 底对齐, 树侧; "读界, 升一个槽" 的回灌形状仍来自 `HtTowerFFold.RunM`, 诊断 §4 第 4 条 (i) 记为翻译痕迹, 本路没有去掉它, 只把它的定义域换成可入下标). 新增字段没有读自记号基本列规则的. 这一步: 摆脱侧 (去掉 "裸下标" 这一条共同前提), 不加深翻译.
