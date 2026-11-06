# LeanT: 重写 TΛ 的前 3 层

> 不含记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`, 不用函数外延. 导入闭包只有 stdlib 与 `OCF.Lean.LeanT*` (见 §4).
>
> **任务** (作者 2026-11-05, 原话 "重写压缩 TΛ 的前 3 层"): 参考 [FabLFReGen](../Align/FabLFReGen.lagda.md) 的闭项 `TΛ = col collL (up Λ) _` 及其依赖, 从头重写定义、折叠与 FGH、合法性证书, 去依赖、去死代码、抽象重复, 得到没有水分的行数. 闭项与原来是同一个数学对象: 同一个一次封闭的层号 `LH`/`Lv`, 同一个对角 `Λ = hl tw`, 同一个一般折叠 (`GenFoldRun` 的各行), 同一个最终坍缩 (层 $1\boxplus$ `up Λ`, 基世界, `sum`).
>
> **文件.**
>
> | 文件 | 内容 | 重写自 |
> |---|---|---|
> | [LeanTBase](LeanTBase.lagda.md) | 种类结构 (自带顶坐标、基世界、向下封闭), 高度, 第一位置, 合法, 比较, `⊞`, `step`, `up`, `sup`, `ι`, `S⊥` | `HtTowerTy`, `GenFoldIf` §3 §6, `GenFoldInst` §2 §3, `FabLFReGen` §1, `LFReTy.S⊥`, `CumReadCF.A` |
> | [LeanTLv](LeanTLv.lagda.md) | `LH`, `Lv`, `SL`, `ofHB`, `Ω̂`, `tw`, `Λ` | `LFReTy`, `LFReTower` |
> | [LeanTTree](LeanTTree.lagda.md) | 结点, 数据树, `sum`, $\Omega_L$, `Int`, 读回 `rd₁`, `drp₁`, 折叠的类型, 级回灌参数 `Fb` | `GenFoldIf` §1 §2 §4, `GenFoldTree`, `GenFoldRd` §1–§4 |
> | [LeanTFold](LeanTFold.lagda.md) | 一般折叠, 带级回灌参数 `fb` | `GenFoldRun` 与 `KindLvRun` (合成一份) |
> | 本篇 | `SL` 的底种类, 层, 最终坍缩, 闭项 `TΛ′`, 证书, FGH | `FabLFReGen` §2 §3, `NewTwrColl`, `NewTwrIf.CollK`, `Free.Level.FGH` |
> | [LeanTFb](LeanTFb.lagda.md) | 级回灌参数的两个实例 (A-回灌, 按级回灌); 不在闭项的切片里 | `GenFoldIf.FBA`, `KindLvIf.KLv` |
> | [LeanTCmp](LeanTCmp.lagda.md) | 与原 `TΛ` 的对照 (有限测试); 验收文件, 导入原模块 | — |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LeanT where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanTTree
import OCF.Lean.LeanTFold as Fold
open Tree SL
```

## §1 `SL` 的底种类与层

底种类是第 0 层的新种类 `νL lz`: 坐标 `HB (Lv lz) = HB S⊥`, 读法是恒等 (原来是逐构造子的翻译 `frE⊥ : HB S⊥ → A`). 最终坍缩的层是 $1\boxplus$ `up Λ` (`NewTwrColl.one⊞`): 第 1 层字面地是它的第一位置.

```agda
bkL : BotK
bkL = record
  { aK = νL lz ; frE = λ e → e
  ; frE-lg = λ lw e → lgB⊲ e (proj₁ (lw lz)) (proj₂ (lw lz))
  ; frE-mono = λ _ _ _ p → ⊲ᴮ↑ (λ ()) p }

Λ′ : HB (step SL)
Λ′ = hs hz ⊞ up Λ

lΛ′ : LgB Λ′
lΛ′ = Lg-⊞ (hs hz) (up Λ) tt (Lg-up Λ Lg-Λ)

one⊲ : ∀ {w} → hs hz ⊲[ w ] Λ′
one⊲ = ⊞-fst (hs hz) (up Λ)

open FoldTy SL Λ′
```

## §2 闭项: 一切旧种类有损

级回灌参数取 "一切旧种类有损" (`λ _ → inj₂ tt`), 与 `FabLFReGen.GL` 的 `fbA = λ _ → inj₂ tt` 相同. 在基世界 `w₀ (step SL)` 里折叠 $\Omega_{\Lambda'}$, 输入的 `n1` 换成 "当前状态的一步" (`Stp`), 第 0 层的输出前接 $1$, 求和.

```agda
open Fold SL bkL Λ′ lΛ′ one⊲ (λ _ → inj₂ tt)

Act : ∀ {ly W} → Ig ly W
Act p lW′ _ Y = Stp Y

ΨΩ : D hz (w₀ L₀)
ΨΩ = n1 ⨾ yc (Run accᴸ (Ωd Λ′) ≤rf (lw₀ L₀) hself Act n0 (st zeroD n0 n0)) (τ₀ (lw₀ L₀))

TΛ′ : HB S⊥
TΛ′ = sum hz ΨΩ

Lg-TΛ′ : LgB TΛ′
Lg-TΛ′ = Lg-sum hz ΨΩ tt
```

**FGH** (同 `Free.Level.FGH`, 同 `OCF.BTBO.Ord-Ord.iter` 的次序).

```agda
iter : (ℕ → ℕ) → ℕ → ℕ → ℕ
iter f x zero = x
iter f x (suc n) = f (iter f x n)

FGH : HB S⊥ → ℕ → ℕ
FGH hz n = suc n
FGH (hs a) n = iter (FGH a) n n
FGH (hl f) n = FGH (f n) n
FGH (hΩ (() , _) g) n

fghΛ′ : ℕ → ℕ
fghΛ′ = FGH TΛ′
```

## §3 闭项只经过旧种类 (形状定理)

`Λ′` 以下的层都不含 `step SL` 的新种类: `up` 把一切种类搬成旧种类, `⊞` 不添种类, 第一位置的层是子项. 所以输入 $\Omega_{\Lambda'}$ 与目标层里都没有新种类的 $\Omega$-结点.

```agda
Old : ∀ {T} → HB (step T) → Set
Old hz = ⊤
Old (hs h) = Old h
Old (hl f) = ∀ n → Old (f n)
Old (hΩ (inj₁ _) g) = ∀ c → Old (g c)
Old (hΩ (inj₂ _) g) = ⊥

old-up : ∀ {T} (a : HB T) → Old (up a)
old-up hz = tt
old-up (hs a) = old-up a
old-up (hl f) n = old-up (f n)
old-up (hΩ κ g) c = old-up (g c)

old-⊞ : ∀ {T} {a : HB (step T)} b → Old a → Old b → Old (a ⊞ b)
old-⊞ hz oa ob = oa
old-⊞ (hs b) oa ob = old-⊞ b oa ob
old-⊞ (hl f) oa ob n = old-⊞ (f n) oa (ob n)
old-⊞ (hΩ (inj₁ _) g) oa ob c = old-⊞ (g c) oa (ob c)
old-⊞ (hΩ (inj₂ _) g) oa ()

old-⊲ : ∀ {T} {k L : HB (step T)} {w} → k ⊲[ w ] L → Old L → Old k
old-⊲ hself o = o
old-⊲ (hsuc p) o = old-⊲ p o
old-⊲ (hlim n p) o = old-⊲ p (o n)
old-⊲ (hLim {κ = inj₁ _} e p) o = old-⊲ p (o _)
old-⊲ (hLim {κ = inj₂ _} e p) ()

old-Λ′ : Old Λ′
old-Λ′ = old-⊞ (up Λ) tt (old-up Λ)

-- 一切目标层都只有旧种类
old-target : ∀ {t W} → t ⊲[ W ] Λ′ → Old t
old-target p = old-⊲ p old-Λ′
```

[判断, 依据上面的定理与代码] 新种类的闭包结点 `nc (inj₂ tt)` 只由 `Ωd (hΩ (inj₂ tt) _)` 生出 (其余各行只复制已有闭包结点的种类), 而一切进入 `Ωd` 的层都在 $\Lambda'$ 之下 (`old-target`), 所以 `TΛ′` 的计算不经过新种类的回灌 `κc₁`, 也不经过 `rd₁`. 这对原 `TΛ` 同样成立 (同一个折叠, 同一个层). 原 `FabLFReGen` 文件头写 "折叠里唯一有回灌的是 `step SL` 的新种类 ... `κc₁`"; 按这里的定理加上对折叠代码的阅读 (判断, 没有对数据的不变式证明), 那一行在 `TΛ` 上不被执行: **`TΛ` 的一切闭包结点都走有损的一行或保留的一行.** C6 要解决的不只是旧种类的升界, 还有让回灌的那一行真的被执行 (层里要有新种类, 或旧种类有回灌).

## §4 结论

- **[定理]** `TΛ′ : HB S⊥` (布劳威尔树, 只有 $0$, 后继, $\mathbb N$-极限), 证书 `Lg-TΛ′`, `fghΛ′ : ℕ → ℕ`; 形状 `old-Λ′`, `old-target`.
- **[同一个对象, 判断]** 构造与原 `TΛ` 逐步对应: 层号 `LH`/`Lv`, 塔 `tw`, 对角 `Λ`, 层 $1\boxplus$ `up Λ`, 基世界, 底种类 `νL lz`, 一切旧种类有损, 同一个折叠的各行, `sum`. 写法与数据表示的差列在各文件头. 没有跨类型的关系定理 (两边的种类结构、高度、数据树都是不同的类型, 互模拟要对整个折叠递归, 未做); [LeanTCmp](LeanTCmp.lagda.md) 有有限测试.
- **[判断]** `TΛ′` 不经过任何回灌 (§3).
- **[有限测试]** [LeanTCmp](LeanTCmp.lagda.md): 两边的路径指纹与有界展开结点数相同 (`refl`).

## §5 行数 (定义级切片)

口径同 `newtwr/locslice_newtwr.py`: 定义级切片, 计 agda 块里非空非注释行; 脚本 `probes/Survey/scripts/leant/locslice_leant.py`, 同一台切片机也重算原闭项.

| 层 | 重写 `TΛ′` | 原 `TΛ` (FabLFReGen) | 记号侧标杆 (EboLean3) |
|---|---|---|---|
| 1 定义 | 265 | 327 | 120 |
| 2 + 折叠, 闭项, FGH | 722 | 1040 | 131 |
| 3 + 证书 | **745** | **1042** | **1513** |
| 4 + 形状定理 (`old-*`; 标杆为标签) | 772 | — | 1533 |

第 3 层逐模块: `LeanTTree` 294, `LeanTBase` 183, `LeanTFold` 174, `LeanTLv` 62, 本篇 32. 原来: `HtTowerTy` 201, `GenFoldRun` 178, `GenFoldTree` 163, `GenFoldIf` 96, `FabLFReGen` 77, `GenFoldRd` 72, `LFReTy` 58, `Free.Level` 56, `CumReadCF` 36, `LFReTower` 32, `NewTwrColl` 28, `OCF.BTBO` 27, `GenFoldInst` 10, `NewTwrIf` 6, `KcFoldIf` 2.

**去掉的约 300 行是什么 (判断, 粗分, 逐项可在切片里查).** 接口层 (`GenFoldIf` 的 `TopG`, `GenK`, `LgDn`, `FbLg`, `DK`, `FoldTy` 的重复声明, `NewTwrIf.CollK`, `NewTwrColl.At`): 约 70; 三个记录的实例对层号各递归一遍 (`topLv`, `ldLv`, `w₀Lv`, `lw₀Lv`, `topStepG`, `topSupG`, `ldStep`, `ldSup`): 约 50, 现在是 `KS` 的字段, `step`, `sup` 各写一次; 第二套布劳威尔树 (`CumReadCF.A` 与它的 `⊲`, `Lg`, 翻译 `frE⊥`, `ordL`, `Free.Level.Ordᶜ`): 约 100, 现在闭项就在 `HB S⊥` 上; 手写的空结构 `LFReTy.Bot`: 约 20, 现在 `S⊥ = sup ⊥ (λ ())`; `OCF.BTBO.Trich`: 27, 现在用 stdlib; `LgE`, `lgBd`: 约 10; A-回灌换成级回灌参数: 约 10.

**剩下的为什么不可省 (判断).**

- `LeanTFold` 174: 一般折叠的各行 (状态, 目标比较, 结点的保留与上升链, 闭包的保留/有损/回灌), 与原 `GenFoldRun` 一一对应, 少的 4 行来自 A-回灌换成参数. 要 "同一个一般折叠", 这些行都在.
- `LeanTTree` 294: 数据树要对层号结构递归才能让 `ni` 的分支以低层数据为输入 (`DG₊`, `Vs`, `Vc` 与 `out`/`in` 的搬运); 第 0 层求和 (`sum` 及其两条证书) 是闭项的出口; `Int` 是折叠的输入改写; 结点证据的工具 (`StH`, `Kup`, `Sk`, `NZ`/`NZ₁` 的许可) 是折叠的类型要的; 读回 `rd₁`, `drp₁` 是新种类回灌那一行要的.
- `LeanTBase` 183: 折叠里唯一的比较 `cmpB` 与它要的合法性; `step` 让新种类的坐标是高度 (这是 "高度的高度" 的唯一构造); `sup`, `up`, `ι`, `⊞` 是层号与对角的构造要的.
- `LeanTLv` 62: 层号与种类结构的归纳-递归块, `Ω̂`, 塔, 对角.

**回灌部分在 `TΛ′` 上不执行.** 第 3 层里回灌专用的块 (`Cl₁`, `κc₁`, `κΔ₁`, `ClA`, `κcF`, `κΔA`, `Fb`, `BotK`, `nbA` 一族, `rd₁` 一族, `drp₁`) 共 139 行, 其余 606 行. 按 §3, `TΛ′` 的值只由这 606 行决定 (判断). 这 139 行是给 C6 的机器准备的, 现在闲着.

**参数化的代价.** 折叠里与级回灌有关的块: `Fb` 8, `κcF` 14, `RKa` 6, `ClA` 8, `κΔA` 4, 共 40; 原 `GenFoldRun` 的 A-回灌: `FBA` 7, `FbLgAt` 3, `FbLg` 2, `κcA` 20, `RKa` 6, `ClA` 8, `κΔA` 4, 共 50. 两个实例 (A-回灌, 按级回灌) 在 [LeanTFb](LeanTFb.lagda.md), 38 行, 不在闭项的切片里. 原来按级回灌要整份拷贝折叠 (`KindLvRun` 236 行代码, `GenFoldRun` 199 行).

## §6 C6 机器的增量 (估计, 判断)

在本重写上加 C6 的三件机器, 只算前 3 层 (定义, 构造, 证书), 不算值定理与否定:

| 机器 | 原实现 (代码行) | 在本重写上 (估计) | 依据 |
|---|---|---|---|
| 带证据的世界 (`RsOwnSW` 式: 世界带 "一切底拷贝同界", 一起升) | `RsOwnIf` 的 `subW`/`RsInv`/`RsK` 约 40, `RsOwnSh` 155, `RsOwnSW` 98 | 160–200 | `subW` 要多给 `w₀` 的证据 (约 +3); 不要 `topSub`, `genU`, `ldU`, `flU`, `shF`/`KLvB`/`lvAt` (改成一个 `Fb`, 约 −40); `ShB` 对 `S⊥`/`step`/`sup` 的递归 (原 155 的主体) 照写 |
| 共享槽 (`SlotGen` 式) | `SlotIf` 45, `SlotGen` 66 (加实例 `SlotCp` 125) | 60–80 (加实例 140–200) | 槽记录少 `LgE` 两个字段; 一起升到 `Fb` 的转换约 8 行 |
| 按级回灌的读回 (`KindLvRd` 式) | `KindLvEmb` 54, `KindLvRd` 110 | 130–170 | 级的下标从 `HB T` (经 `Lev`) 换成 `LH` (经 `Lv`), 多一个 `lΩ` 情形; 到 `Fb` 用现成的 `fromKLv` 形状 (约 10 行); 折叠不用再拷贝 |

三件全加, 第 3 层约 745 + 350–450 = 1100–1200 (判断), 仍低于标杆 1513; 这是在 "折叠只写一份" 之下的数, 原路线每加一种回灌要拷贝一份折叠 (约 200 行).
