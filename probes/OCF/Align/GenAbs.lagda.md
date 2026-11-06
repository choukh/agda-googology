# 规范形论证对树类型抽象: 入口

> **判决: HOLDS (四项都做了), 省下的行数不大.** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`, 没有验收文件, 不改任何已有定义.
>
> 1. **`Gen` 写一次 (HOLDS).** [GenAbsSig](GenAbsSig.lagda.md) 的记录 `Sig` 是第 0 层差树的签名: 世界与世界序, 五个构造子, 归纳原理, 读法 `sum`, `pt` 与七条计算方程, `sum-fst`, `Lg-sum`. [GenAbsCanon](GenAbsCanon.lagda.md) 的 `Canon.Gen` 对一切签名给出 `canon`, `M`, `cong0`, 结构律的参数与 `DValCanon.Gen` 逐条相同. 规范形改用读法 `sum`, 所以原文的 `TI`, `DEC`, `ZL` 与 `toA`, `pts` 都不需要.
> 2. **`SumOneTree.D azero` 上与原文一致 (HOLDS).** [GenAbsSO](GenAbsSO.lagda.md): 以 `DValCanon.Gen` 的参数为参数, 新的 `Gen` 推出原文 `Two.cong0` 与 `One.canon` 的类型 (`cong0ᵒ`, `canonᵒ`); 反方向 `cong0ⁿ`. 两个 `cong0` 只差前提里的读法 (`toA` 对 `sum`), 由 `BrwMidZero.sum₀` 互换.
> 3. **`HtFeedTree.D hz` 上不经翻译 (HOLDS).** [GenAbsHt](GenAbsHt.lagda.md) 重新得出 `MonoPortZero` 的 `cong0`, `chain`, 没有 `toS`, `ofS`, `rt`, `rt′`, 导入闭包里没有 `MonoPortBridge`, `SumOneTree`, `DValCanon`, `BrwMidZero` (编译器保证). 与原文同型 ([GenAbsHtCmp](GenAbsHtCmp.lagda.md): `Rl≡` 是 `refl`, 两个 `cong0` 互为对方类型的居民). 第二个使用者 `MonoPort2Zero` 也照做了 ([GenAbsM2](GenAbsM2.lagda.md), [GenAbsM2Cmp](GenAbsM2Cmp.lagda.md)); 它的导入闭包里仍有 `MonoPortBridge` (经 `MonoPort2Rel` 取 `val`), 定义级切片只到达 `val` 一块 (2 行, 就是 `sum azero`).
> 4. **`HtTowerFTree` 第 0 层 (HOLDS, 只有实例).** [GenAbsHtInst](GenAbsHtInst.lagda.md) 的 `σT`: 世界是一对, `nw` 用世界序 `≤`, 多一个空的 `nμ`, 签名不用改. 实例上有 `smonoᵀ` 与 `Canon.Gen σT`; 那一层还没有折叠一侧的关系去套它.
>
> **行数 (定义级切片, `locslice_htfeed.py` 的口径, 把模块别名 `GG` 两边都列为根):** `MonoPortZero` 的 `cong0`, `chain` 从 996 行降到 903 行 (省 93); `MonoPort2Zero` 的 `cong0₂`, `chain₂` 从 1247 降到 1165 (省 82); 两个合起来 1428 降到 1317 (**省 111**). 只有一个实例时抽象要多付钱: `SumOne` 一侧的 `Gen` 本身 (不含结构律) 从 286 升到 316 (多 30).
>
> **接口是树侧的.** 签名的每个字段都是差树已有的构造子或读法 `sum` 的定义方程, 实例里方程都是 `refl`. `GenAbsSig`, `GenAbsCanon` 的导入闭包只有 `CumReadCF`, `TLRuleSpec`, `TLRuleSum`, `OCF.BTBO`, `OCF.Free.Level` 与标准库.

## 1 签名

```text
record Sig : Set₁ where
  field
    Wd  : Set                              -- 世界
    _≺_ : Wd → Wd → Set                    -- nw 用的世界序
    T   : Wd → Set                         -- 第 0 层差树
    n0 n1 : ∀ {W} → T W
    _⨾_ : ∀ {W} → T W → T W → T W
    nl  : ∀ {W} → (ℕ → T W) → T W
    nw  : ∀ {W₀ W} → W₀ ≺ W → T W₀ → T W
    ind : (P : ∀ {W} → T W → Set) → (五种情形) → ∀ {W} (z : T W) → P z
    sum : ∀ {W} → A → T W → A               -- 读法: 从底 b 起加上树
    pt  : ∀ {W} → A → (ℕ → T W) → ℕ → A     -- 部分和
    pt-z, pt-s, sum-n0, sum-n1, sum-⨾, sum-nl, sum-nw   -- 七条计算方程 (命题相等)
    sum-fst : ∀ {W} b (x : T W) → b ⊲ sum b x
    Lg-sum  : ∀ {W} b (x : T W) → Lg b → Lg (sum b x)
```

为什么是这些 (都由 `Gen` 的代码逼出):

- 构造子只有五个: 原文对 `ni`, `nκ` 只写空模式, 第 0 层的节点种类是 $\bot$. 归纳原理只有五种情形, 实例自己处理空的构造子 (`HtTowerFTree` 还有 `nμ`).
- 原文对树归纳的只有两处: `refl⊑` 与规范形的 `Cc`. 所以要 `ind`.
- 原文的规范形读 `toA` (`SumOne` 专有). 改读 `sum` 后, `Cc` 说的是 "从底 $a$ 到 `sum a z` 的差与 $z$ 等价, 对一切第一位置与合法性证据"; 抽象的 `sum` 不能定义性计算, 所以计算方程是命题相等, 只经 `dif≡` (目标相等的两个差等价, `PI` 的推论) 用一次. `pt` 单列: 对通用部分和陈述 `sum b (nl d) ≡ alim (λ n → …)` 要外延性.
- `sum-fst`, `Lg-sum` 可以由前面导出, 实例里已有, 直接取.
- 世界与世界序作参数: `Gen` 里世界只出现在 `nw` 的类型里.

`Ops` (对签名通用): `pre`, `dif`, `val = sum 0`, `sum⊞` (`sum a x` 与 $a\oplus$ `val x` 互相 $\le$), `smono`. `sum⊞` 以前写过三次 (`TLRuleSpec.sum⊞`, `BrwMidZero.sum-toA`, `MonoPortBridge` 经翻译再借一次).

## 2 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `Ops.sum⊞`, `Ops.smono` | GenAbsSig | 对一切签名: 和对底的分解; `sum` 对底与值单调 | 定理 |
| `Canon.Gen.refl⊑`, `One.Cc`, **`One.canon`** | GenAbsCanon | 对一切签名: `Dz (sum 0 z) ~ z` | 条件定理 (结构律十四条作参数, 同原文) |
| `Two.M`, **`Two.cong0`** | GenAbsCanon | 对一切签名: `sum 0 z ≤ sum 0 z′` ⇒ `R i j z z′` | 条件定理 (同上, 加 `Hy i i`, `Hy j j`, `Hy i j`) |
| `σS`, **`FromOld.cong0ᵒ`**, **`FromOld.canonᵒ`** | GenAbsSO | 原文的参数推出原文 `Two.cong0`, `One.canon` 的类型 | 条件定理 (原文的参数) |
| `FromOld.cong0ⁿ` | GenAbsSO | 原文的 `cong0` 推出新陈述 | 条件定理 (同上) |
| `σH`, `σT`, `smonoᴴ`, `smonoᵀ` | GenAbsHtInst | 高度树与塔的第 0 层是签名的实例 | 定理 |
| **`cong0`**, **`chain`** | GenAbsHt | 与 `MonoPortZero` 同一陈述, 一切实例 $\Lambda$ | 条件定理 (三条 `HAᶜ`, 同原文) |
| `Rl≡`, `cong0ᴺ`, `cong0ᴼ`, `chainᴺ` | GenAbsHtCmp | 关系定义性相等, 结论互为对方类型的居民 | 定理 (`refl`, 同型) |
| **`cong0₂`**, **`chain₂`** | GenAbsM2 | 与 `MonoPort2Zero` 同一陈述 | 条件定理 (同原文) |
| `I≡`, `Rl≡`, `cong0₂ᴺ`, `cong0₂ᴼ`, `chain₂ᴺ` | GenAbsM2Cmp | 同上 | 定理 (`refl`, 同型) |

前提的可满足性没有变: 与原文相同 (`MonoPortOne.HA-Step` 给出 `HAᶜ` 的实例).

## 3 行数

**定义级切片** (`htfeed/locslice_htfeed.py` 的口径: 按到达的声明块计 agda 代码块里非空非注释行; 脚本在 scratch 的 `locslice_genabs.py`, 读 `locslice.py` 的前半). 切片看不见模块应用, 所以两边都把模块别名 `GG` (结构律传给 `Gen` 的地方) 列为根; 不列时新侧少算约 110 行.

| 比较 | 旧 | 新 | 差 | 只在旧 | 只在新 |
|---|---|---|---|---|---|
| `MonoPortZero` 的 `cong0`, `chain` 对 `GenAbsHt` | 996 | 903 | −93 | DValCanon 187, MonoPortZero 175, BrwMidZero 71, MonoPortBridge 54, SumOneTree 36, CumReadCF 3, LayerTrRound 2 | GenAbsCanon 169, GenAbsHt 152, GenAbsSig 90, GenAbsHtInst 24 |
| `MonoPort2Zero` 的 `cong0₂`, `chain₂` 对 `GenAbsM2` | 1247 | 1165 | −82 | MonoPort2Zero 341, DValCanon 187, BrwMidZero 71, MonoPortBridge 46, SumOneTree 36, … | GenAbsM2 321, GenAbsCanon 169, GenAbsSig 90, GenAbsHtInst 24 |
| 两处合起来 | 1428 | 1317 | **−111** | | |
| `SumOne` 一侧 `Gen` 的 `cong0` (不含结构律) | 286 | 316 | +30 | DValCanon 187, BrwMidZero 36, … | GenAbsCanon 169, GenAbsSig 41, SumOneTree 30, GenAbsSO 22 |

账的来源 (两处合起来): 共用的部分, 旧的规范形加翻译 (DValCanon, BrwMidZero, MonoPortBridge, SumOneTree 等) 351 行换成新的签名与 `Gen` (GenAbsCanon, GenAbsSig, 实例) 283 行, 省 68; 每个使用者去掉拉回 `Rˢ`, 往返 `rt`, `rt′`, 部分和的翻译 (`MonoPortZero` 175 → 152, `MonoPort2Zero` 341 → 321), 省 43. `GenAbsCanon` 与 `DValCanon` 差不多长 (169 对 187): 新的 `Cc` 比原文的 `TI`, `DEC`, `ZL`, `Cc` 短, 但多了 `dif≡` 与 `ind` 的写法; `PI` 一族两边都要. 判断: 再有第三个使用者 (例如第 1 层无节点的部分, 或 `HtTowerF` 第 0 层的折叠关系), 每个省约 20 行加上它自己那份不再需要的翻译.

**文件级** (agda 代码块里非空非注释的行):

| 文件 | 行 | 内容 |
|---|---|---|
| `GenAbsSig` | 99 | 签名, `≈` 小件, `Ops` (`pre`, `dif`, `sum⊞`, `smono`) |
| `GenAbsCanon` | 183 | 无环 `G`, `Canon.Gen` |
| `GenAbsSO` | 84 | `σS`, `FromOld` (对照, 导入原文) |
| `GenAbsHtInst` | 59 | `σH`, `σT` |
| `GenAbsHt` | 169 | `MonoPortZero` 的替代 (§1, §2, §4 逐字照抄) |
| `GenAbsHtCmp` | 28 | 对照 |
| `GenAbsM2` | 337 | `MonoPort2Zero` 的替代 (§1 到 §3, §5 逐字照抄) |
| `GenAbsM2Cmp` | 22 | 对照 |
| 入口 | 10 | |

`GenAbsHt`, `GenAbsM2` 是照抄的替代文件 (按项目规矩不改原文件, 用新文件取代), 所以仓库的总行数增加; 上面的切片账说的是 "一个结论依赖多少定义".

## 4 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| 签名 `Sig` 的构造子与归纳原理 | 三种第 0 层差树已有的构造子; `Gen` 只对树做两处归纳 | 树侧, 去重复 |
| 读法 `sum`, `pt` 与七条方程 | 差树自己的读法; 方程是 "抽象的 `sum` 不计算" 带来的, 实例里都是 `refl` | 树侧; 抽象的脚手架 (约 10 行字段, 每个实例 6 行 `refl`) |
| 世界与世界序作参数 | `HtTowerFTree` 的世界是一对, 序是 `≤` | 树逼的 (实例) |
| 规范形改读 `sum` (`Cc`, `dif≡`) | 原文读 `toA` 是 `SumOne` 专有; `sum` 是三种树共有的 | 树侧, 去掉了 `TI`, `DEC`, `ZL` |
| `pre≡` (3 行, 仅 `GenAbsM2`) | `MonoPort2Rel.preL` 对一切层, 与签名的 `pre` 是两个函数 | 去重复的残余 |
| 去掉: `toS`, `ofS`, `ofS-pre`, `sumT≤`, `sumT≥`, `toV`, `smono` 的翻译证明, `Rˢ`, `rt`, `rt′`, `ofS-preL` | 都是 "规范形论证写死在 `SumOne` 上" 带来的 | 翻译脚手架, 已去掉 |

**按 `AGENTS.md` 归类: 提供信息 (去掉翻译脚手架).** 没有新构造子, 没有新节点字段, 不改树, 不改折叠, 没有 `Lab`, 没有记号; 结论对一切签名成立, 没有为哪一站定制的前提. 这里的 "翻译" 是树与树之间的 (`HtFeedTree` 对 `SumOneTree`), 不是记号到树; 去掉它说明值同余的规范形论证只依赖第 0 层差树的五个构造子与读法. 没有序数值验收 (不涉及新的树).

## 5 审计

- **导入闭包** (`importclosure.py --only OCF.Free.Level --only OCF.BTBO --only OCF.Align.CumReadCF --only OCF.Align.TLRule --only OCF.Align.TLOpsW --only OCF.Align.SumOne --only OCF.Align.BrwMid --only OCF.Align.LayerTr --only OCF.Align.CvFold --only OCF.Align.CvHigh --only OCF.Align.CvLayer --only OCF.Align.NoCumLit --only OCF.Align.DVal --only OCF.Align.HtGen --only OCF.Align.HtFeed --only OCF.Align.HtTower --only OCF.Align.MonoPort --only OCF.Align.GenAbs`, 对每个文件单独跑): 入口 43 个模块 (本地 33), `GenAbsSig` 16 (6), `GenAbsCanon` 17 (7), `GenAbsSO` 27 (17), `GenAbsHtInst` 20 (10), `GenAbsHt` 23 (13), `GenAbsHtCmp` 35 (25), `GenAbsM2` 36 (26), `GenAbsM2Cmp` 38 (28); 都是退出码 0, 禁用表 0, `--only` 之外 0. `GenAbsSig`, `GenAbsCanon`, `GenAbsHtInst`, `GenAbsHt` 的闭包里没有 `MonoPortBridge`, `SumOneTree`, `DValCanon`, `BrwMidZero`; `GenAbsM2` 有 (经 `MonoPort2Rel`), 对照文件与 `GenAbsSO` 有 (有意导入原文).
- **定义级切片** (`depslice.py`, 到达块 / 记号块 / 词命中): `GenAbsHt:cong0` 179/0/0, `GenAbsHt:chain` 183/0/0, `GenAbsHt:module GG` 167/0/0, `GenAbsM2:cong0₂` 202/0/0, `GenAbsM2:chain₂` 221/0/0, `GenAbsM2:module GG` 215/0/0, `GenAbsCanon:cong0` 56/0/0, `GenAbsCanon:canon` 46/0/0, `GenAbsSig:smono` 29/0/0, `GenAbsSO:cong0ᵒ` 105/0/0, `GenAbsSO:canonᵒ` 111/0/0, `GenAbsHtInst:σH` 52/0/0, `GenAbsHtInst:σT` 104/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用, 不说明没受记号启发.
- **禁用构造**: 九个文件无 `postulate`, 无洞, 无 `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY_CHECK`, 无 `trustMe`, 不用 `--cubical`, 代码块里不出现 `Funext`; 都带 `--safe --without-K --lossy-unification`.
- **编译**: 删掉本组九个模块自己的 `.agdai` 后从仓库根编译入口, 退出码 0, 6 秒, 峰值 0.75G (`-M6G`; 依赖用已有接口, 没有用 `--ignore-interfaces`).

## 6 时间线

写定义前读过: `AGENTS.md`, `probes/README.md` 的翻译账, `Survey/EBOHandbook.md` 的工程与幽灵两节, `DValCanon`, `MonoPortBridge`, `MonoPort`, `MonoPortZero`, `MonoPort2Zero`, `HtFeedTree`, `HtTowerFTree` 的第 0 层与世界, `SumOneTree`, `BrwMidZero`, `TLRuleSpec`, `CumReadCF` 的签名, `locslice_htfeed.py`, `locslice.py`. 没有打开 `EBO`, `Correspond`, `Label`, 没有读任何基本列规则.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GenAbs where

open import OCF.Align.GenAbsSig using (Sig; module Ops) public
open import OCF.Align.GenAbsCanon using (module Canon) public
open import OCF.Align.GenAbsSO using (σS; module FromOld) public
open import OCF.Align.GenAbsHtInst using (σH; σT; smonoᴴ; smonoᵀ) public
import OCF.Align.GenAbsHt
import OCF.Align.GenAbsHtCmp
import OCF.Align.GenAbsM2
import OCF.Align.GenAbsM2Cmp
```
