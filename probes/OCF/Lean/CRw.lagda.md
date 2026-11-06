# CRw: C 线重写成一个折叠 (入口)

> 不含记号. 构造一路 CRw (配对否定一路 NegCRw), 2026-11-06. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`, 不用函数外延, 不用 UIP. 闭项, 证书, FGH 无模块参数. 导入闭包只有 stdlib 与 `OCF.Lean.CRw*`. 不改任何已有文件.
>
> **任务** (作者本轮选定, 原话 "摆脱+压缩: C 线重写成一个折叠"): 按 "重写" 把 TySup / PathOut / X1Up 三段合成一个对层号递归的带类型折叠 (路径, 世界序, 可数层与 $\Omega_1$ 层一份定义), 至少重现 `TU2`, 前 3 层明显低于 1111.
>
> | 文件 | 内容 | 参考 (只作参考, 未拷贝) |
> |---|---|---|
> | [CRwBase](CRwBase.lagda.md) | 种类结构, 高度, 第一位置, 合法, `cmpB`, `⊞`, `step`, `up`, `sup`, `ι`, `S⊥`, `Cd` | `HtTowerTy`, `LeanTBase` |
> | [CRwIf](CRwIf.lagda.md) | 接口: 世界的移动 (定稿 00:49) | `PathOutIf`, `X1UpIf` |
> | [CRwFold](CRwFold.lagda.md) | 塔, 层号 (底, 高度), 种类分类与嵌入, `pick`, 决定, 策略, 路径 `PH`, 地板, **折叠 `Φ`**, 形状 `Sh-Φ` | `TySupFold`, `TySupC`, `PathOutFold`, `PathOutX1`, `X1UpFold` §1–§4 |
> | [CRwPath](CRwPath.lagda.md) | 叠层的路径 (Kripke 式可入), 单调与加法, 搬运, **`PH-ΦX`** | `X1UpIf` §1, `X1UpFold` §5–§9 |
> | 本篇 | 实例 `I₁`, `leg`, 地板带路径, 闭项 `TX`, `TU`, `TU2`, 证书, FGH | `PathOutX1` §2, `PathOut`, `X1Up` §2 |
| [CRwCmp](CRwCmp.lagda.md) | 与原闭项的对照 (有限测试); 验收文件, 导入原模块 | — |

**一个折叠.** 原来三段各有层号类型、种类结构与决定: `TySupFold.Φ` (可数层号, `TySupC`), `PathOutFold.Ψ` ($X_1$ 折到可数层号, 带世界与路径), `X1UpFold.ΦU` ($X_1$ 上的叠层折到 $X_1$, 底种类一律留). 重写后:

1. **层号是 (底, 高度)**, 第 $(s,m)$ 层的种类结构是底上的塔 `Tw (bS s) m`. 可数层号是空底上的塔, 叠层是 $\Omega_1$ 层 `XS` 上的塔. 塔的种类分类 (`cl`: 底种类 / 第 $j$ 层的新种类), 嵌入 (`emb`, `along`), 地板 (`topT`) 对两种底是**同一份定义**.
2. **一个折叠 `Φ`**, 对层号的可达性递归. 后继、ℕ-极限两个子句共用; $\Omega$-结点按目标分两种: 同底 (`sm`): 底种类留, 新种类用 `cmpB` 以层号高度 $m$ 为公共上界比较; 跨底 (`cx`, 只从 $\Omega_1$ 层到可数层号): `XS` 的种类带证据 $c+1\lhd B$, 以世界的界 $B$ 为公共上界比较. 两种比较的结果由**同一个** `pick` 读成留 / 同层 / 在上. 原来的 `TySupC.decC` 是同底决定在空底上的特例 (没有底种类).
3. **路径只在跨底时要求** (`Nd`). 世界的移动是接口 [CRwIf](CRwIf.lagda.md) 的 7 个字段 (原来 `PathOutIf` 15 个字段 + `X1UpIf` 10 个 + `TySupIf` 17 个).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.CRw where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwIf
```

## §1 实例: 世界的移动

同 PathOut: 可入 $B\lhd e$ 且 $e$ 合法, 进入后世界是 $e+1$; 回灌 $c\mapsto B\boxplus\mathrm{leg}\,c$. `leg` 把可数树的 ℕ-极限换成部分和, 输出合法 (**累加**, 代价见文末).

```agda
Σ₀ : (ℕ → Cd) → ℕ → Cd
Σ₀ f zero = f 0
Σ₀ f (suc n) = Σ₀ f n ⊞ f (suc n)

leg : Cd → Cd
leg hz = hz
leg (hs x) = hs (leg x)
leg (hl f) = hl (Σ₀ (λ n → leg (f n)))
leg (hΩ () _)

Lg-leg : ∀ x → LgB (leg x)
Lg-Σ₀ : ∀ f n → LgB (Σ₀ (λ m → leg (f m)) n)
Lg-leg hz = tt
Lg-leg (hs x) = Lg-leg x
Lg-leg (hl f) = (λ n → ⊞-fst (Σ₀ (λ m → leg (f m)) n) (leg (f (suc n)))) , Lg-Σ₀ f
Lg-leg (hΩ () _)
Lg-Σ₀ f zero = Lg-leg (f 0)
Lg-Σ₀ f (suc n) = Lg-⊞ _ (leg (f (suc n))) (Lg-Σ₀ f n) (Lg-leg (f (suc n)))

I₁ : CRwIf
I₁ = record
  { Adm₀ = λ B e → (B ⊲ e) × LgB e
  ; nxt₀ = λ B e a → hs e
  ; sh₀ = λ B c → B ⊞ leg c
  ; adm-sh = λ {B} c lB → ⊞-fst B (leg c) , Lg-⊞ B (leg c) lB (Lg-leg c)
  ; nx-up = λ a → hsuc (proj₁ a)
  ; lg-nx = λ a lB → proj₂ a
  ; adm↓ = λ q a′ → (⊲ᴮ-tr q (proj₁ a′) , proj₂ a′) , hself }

open import OCF.Lean.CRwFold I₁
open import OCF.Lean.CRwPath I₁
```

## §2 $\Omega_1$ 层的地板带路径

`topL` 的根是 $\Omega_1$ 种类 (证据 $1\lhd B$); 分支 $y$ (可入: $B\lhd y$) 在世界 $y+1$ 里, 里面的种类都在第 $c+1$ 层 ($c<y$), 证据 $c+1\lhd y+1$.

```agda
PH-cd : ∀ {W} (e : Cd) → PH PSX W (ι {Cd} {λ c → Tw S⊥ (hs c)} hz (up e))
PH-cd hz = tt
PH-cd (hs e) = PH-cd e
PH-cd (hl f) = λ n → PH-cd (f n)
PH-cd (hΩ () _)

PH-ιu : ∀ c W → hs c ⊲ W → ∀ (e : HB (Tw S⊥ c)) → PH PSX W (ι {Cd} {λ c → Tw S⊥ (hs c)} c (up e))
PH-ιu c W q hz = tt
PH-ιu c W q (hs e) = PH-ιu c W q e
PH-ιu c W q (hl f) = λ n → PH-ιu c W q (f n)
PH-ιu c W q (hΩ κ g) = q , λ e _ → PH-ιu c W q (g e)

PH-Ωc : ∀ c W → hs c ⊲ W → PH PSX W (ι {Cd} {λ c → Tw S⊥ (hs c)} c (topT S⊥ hz (hs c)))
PH-Ωc hz W q = q , λ e a → PH-cd e
PH-Ωc (hs c) W q = q , λ e a → PH-ιu (hs c) W q e
PH-Ωc (hl f) W q = q , λ e a → PH-ιu (hl f) W q e
PH-Ωc (hΩ () _) W q

PH-gt : ∀ y W → y ⊲ W → PH PSX W (gt y)
PH-gt hz W q = tt
PH-gt (hs c) W q = PH-⊞ PSX (gt c) (ι {Cd} {λ c → Tw S⊥ (hs c)} c (topT S⊥ hz (hs c))) (PH-gt c W (⊲ᴮ-tr (hsuc hself) q)) (PH-Ωc c W q)
PH-gt (hl f) W q = λ n → PH-gt (f n) W (⊲ᴮ-tr (hlim n hself) q)
PH-gt (hΩ () _) W q

PH-topL : ∀ B → hs hz ⊲ B → PH PSX B topL
PH-topL B o = o , λ y a → PH-gt y (hs y) (hsuc hself)
```

## §3 闭项, 证书, FGH

初始世界 $B=1$. `TX`: $\Omega_1$ 层的地板经跨底折叠到第 0 层 (同 PathOut 的 `TXL`). `TU m`: 第 $\Omega_1\oplus m$ 层的地板先经同底折叠到 $\Omega_1$ 层 (界 `topL`), 再经跨底折叠到第 0 层; 路径由定理 `PH-ΦX` 给出. `TU2` 对角.

```agda
W₀ : Cd
W₀ = hs hz

TX : Cd
TX = Φ bX hz (wf bX hz) tt b⊥ hz (cx W₀ tt (z⊲ᴮ W₀)) hz topL (PH-topL W₀ hself)

open Thm PH-topL using (PH-ΦX)
open Top PH-topL using (PH-top)

-- Ω₁ ⊕ m 层折到 Ω₁ 层
inU : (m : Cd) → LgB m → HB XS
inU m lm = Φ bX m (wf bX m) lm bX hz (sm (z⊲ᴮ m)) topL (top bX m) tt

PH-inU : ∀ m lm → PH PSX W₀ (inU m lm)
PH-inU m lm = PH-ΦX m (wf bX m) lm hz (z⊲ᴮ m) topL (top bX m) W₀ hself (PH-topL W₀ hself) (PH-top m W₀ hself)

TU : (m : Cd) → LgB m → Cd
TU m lm = Φ bX hz (wf bX hz) tt b⊥ hz (cx W₀ tt (z⊲ᴮ W₀)) hz (inU m lm) (PH-inU m lm)

LgB-TX : LgB TX
LgB-TX = sh→lg TX (Sh-Φ bX hz (wf bX hz) tt b⊥ hz (cx W₀ tt (z⊲ᴮ W₀)) hz topL (PH-topL W₀ hself))

LgB-TU : ∀ m lm → LgB (TU m lm)
LgB-TU m lm = sh→lg (TU m lm) (Sh-Φ bX hz (wf bX hz) tt b⊥ hz (cx W₀ tt (z⊲ᴮ W₀)) hz (inU m lm) (PH-inU m lm))

TU1 : Cd
TU1 = TU (hs hz) tt

-- 对角: y₀ = 0, y_{n+1} = y_n ⊞ TU (y_n + 1)
yU : ℕ → Cd
lg-yU : ∀ n → LgB (yU n)
yU zero = hz
yU (suc n) = yU n ⊞ TU (hs (yU n)) (lg-yU n)
lg-yU zero = tt
lg-yU (suc n) = Lg-⊞ (yU n) (TU (hs (yU n)) (lg-yU n)) (lg-yU n) (LgB-TU (hs (yU n)) (lg-yU n))

TU2 : Cd
TU2 = hl yU

LgB-TU2 : LgB TU2
LgB-TU2 = (λ n → ⊞-fst (yU n) (TU (hs (yU n)) (lg-yU n))) , lg-yU
```

**FGH** (同 `Free.Level.FGH` 的次序).

```agda
iter : (ℕ → ℕ) → ℕ → ℕ → ℕ
iter f x zero = x
iter f x (suc n) = f (iter f x n)

FGH : Cd → ℕ → ℕ
FGH hz n = suc n
FGH (hs a) n = iter (FGH a) n n
FGH (hl f) n = FGH (f n) n
FGH (hΩ () _) n

fghX fghU1 fghU2 : ℕ → ℕ
fghX = FGH TX
fghU1 = FGH TU1
fghU2 = FGH TU2
```

## §4 读法与原闭项的关系

**读法 (判断, 没有值的定理).** 同 PathOut / X1Up 的约定 (ψ(a+1)=ψ(a)·ω, ψ(0)=1, 外加累加): `TX` 读 ψ₀(Ω_Ω); `TU m` 读 ψ₀(Ω_{Ω+m}); `TU2` 是 $\alpha\mapsto$ ψ₀(Ω_{Ω+α}) 的不动点迭代, 读 **ψ₀(Ω_{Ω·2})** (Ω = Ω₁). 没有越过原 `TU2` 的读法.

**与原闭项的关系 ([CRwCmp](CRwCmp.lagda.md), 有限测试).** 两边是不同类型的布劳威尔树, 没有跨类型的关系定理. 有界展开 (深度 4, 每个 ℕ-极限展开前 4 项) 的结点数: `TU2` 与 `X1Up.TU2` 都是 32, `TU1` 与 `X1Up.TU1` 都是 41 (`refl`); `TX` 是 41, PathOut 的 `TXL` 是 45 (`refl`), **不同**. 原因 (判断, 读代码): PathOut 的 $X_1$ 把 $\Omega_1$ 单独放一个分量, 分量 $0$ 里的 $\Omega_1$ 拷贝不移动世界; 本路 `XS` 的 $\Omega_1$ 就是分量 $0$ 的新种类, `topL` 分支里 `ι 0 Ω₁` 那个结点在本路移动世界并回灌. 读法不变是判断. 更深的展开在 6G 内堆耗尽 (路径指纹深度 40, 退出码 251), 没有做.

## §5 行数 (定义级切片)

脚本 `Survey/scripts/crw/locslice_crw.py` (口径同 `leant/locslice_leant.py`, `x1up/locslice_x1up.py`: 定义级切片, 计 agda 块里非空非注释行; `CRwFold`, `CRwPath` 经模块应用使用, 模块内定义手工列为根). 同一台切片机重算原 `X1Up.TU2` 得 1111 (与原文件一致). 2026-11-06 跑出 (主闭项 `TU2`):

| 层 | CRw (`TU2`) | X1Up (`TU2`, 同机重算) | 对照 (取自各文件) |
|---|---|---|---|
| 1 定义 | 251 | 501 | |
| 2 + 折叠, 实例, 闭项, FGH | 692 | 1101 | |
| 3 + 证书 | **696** | **1111** | PathOut 743 (ψ₀(Ω_Ω)), TySup 504 (ψ₀(Ω_Ω)), FabLFReGen 1513 |

第 3 层逐模块: `CRwFold` 258, `CRwPath` 192, `CRwBase` 149, `CRw` 87, `CRwIf` 10. 闭包里 `OCF.Lean.CRw*` 之外的仓库模块: 0. 记号模块: 0. 本路比 X1Up 少 415 行 (37%), 读法相同 (判断); 比 PathOut (读法更低) 也少 47 行. 跨读法的行数不作比较结论.

**口径差, 如实.** (1) X1Up 的 1111 含地板合法 `Lg-topU`, `Lg-topL` (第 3 层); 本路**不证地板合法** (证书由形状给出, 不读输入合法, 闭项不需要), 所以没有对应的行. (2) 层 2 已含路径与部分证书: 闭项 `TU` 要路径作跨底折叠的参数 (`PH-inU`), 对角 `yU` 要 `LgB-TU` (同 X1Up 的口径).

**逐块为什么不可省 (判断).**

- 折叠本身 (`Φ`, `caseDc`, `pick`, `dcl`, `dcx`, 累加 `mul`/`chain`/`Σ⁺`): 58 行. 三种结点处理 (留 / 同层 / 在上) 与两种目标 (同底 / 跨底) 各一次.
- 层号与种类 (`Tw`, `XS`, `Cl`/`cl`, `emb`/`frE`, `along`/`frA`, 可达性 `Acc`/`wf`): 塔的种类与坐标的搬运, 对两种底一份.
- 路径专用 (`CRwPath` 全部, `PS`/`PH`/`PSX`/`Nd`, 地板的路径): **239 行, 占 34%**. 跨底比较要证据 (壁垒: 裸坐标上没有精确决定, `Fab4LOm.exact→Sep`); 闭项 `TU` 的跨底输入是同底折叠的输出, 要证它带路径 (`PH-ΦX`), 叠层新种类的可入要 Kripke 式 (X1Up `naive-anti`). 这是本路剩下的最大一块脚手架.
- 底座 (`CRwBase`): `cmpB` 与它要的第一位置、合法; `step`/`sup` 是塔与 `XS` 的构造; `⊞` 是累加与回灌.
- 实例 (`I₁`, `leg`): 回灌坐标要合法 (`cmpB` 要合法的界), `leg` 用部分和给出.

## §6 翻译账

- **新结点, 新字段.** 无新结点. 新的组织: 层号 = (底, 高度), 种类结构 = 底上的塔 (原来 `LC`, `LS` 是两个独立的递归); 决定 = 一个 `pick` 作用在两种 `cmpB` 结果上 (原来 `TySupC.pick`, `PathOutX1.pickΩ`+`conv`, `X1UpFold.pickU` 三份). 接口只剩世界的移动 (7 个字段).
- **由树逼出.** (1) 跨底时证据相对同一世界 (`exact→Sep`). (2) 回灌 $B\boxplus\mathrm{leg}\,c$: 留下的 $\Omega_1$ 结点在任意坐标处有分支, 输入的分支要取在界之上的合法坐标. (3) 叠层新种类的 Kripke 式可入 (`naive-anti`). (4) **世界在 $1$ 之上** (`o : hs hz ⊲ B`): 本路的证据对一切 `XS` 种类同式 ($c+1\lhd B$), $\Omega_1$ 是分量 $0$ 的新种类, 证据是 $1\lhd B$; PathOut 把它放进世界合法 (`LgW₁`), 本路放进路径定理的前提. (5) 跨底目标只从 $\Omega_1$ 层出发 (`cx` 只在 `(bX, hz)`): 从叠层直接折到可数层号, 叠层新种类在上时要同底折叠的输出带路径, 那要在折叠的定义里用 `PH-ΦX` (未做, 见接手清单).
- **累加, 如实.** `Φ` 的后继与 ℕ-极限子句取部分积、部分和, 坍缩取回灌链 (同 `TySupFold`); 回灌坐标的 `leg` 取部分和; 地板 `ΣT` 取部分和. 证书由形状给出靠的就是这些累加; 否定一路 `NegCRwAcc` (主审复核前不算数) 报告: 去掉累加则证书须读输入合法并证单调.
- **受记号启发, 如实.** 读法是对照扩展 Buchholz 记号的判断; 塔 `Tw S⊥` 的形状同 `LFReTy.Lv` (那里已自述为记号引导); $\Omega_1\oplus m$ 的层号形状同 X1Up.
- **摆脱侧.** 没有读记号的基本列规则. 相对三段: 一个折叠、一个 `pick`、一份塔; 原来的 `TySupIf`, `PathOutIf`, `X1UpIf` 合成 7 字段的接口. 这一步**没有**让树自己说出下一步 (到 $X_2$ 怎么写仍是判断, 见接手清单 1).
- **攀爬侧.** 读法不升 (ψ₀(Ω_{Ω·2}), 同原 `TU2`).

## §7 接手清单

1. **到 $X_2$ (层号 $\Omega\cdot 2$ 作 $\Omega$-结点) 及以上.** 本路的底只有两种 (`b⊥`, `bX`), 跨底只从 `(bX, hz)` 出发. 下一步: (a) 跨底目标推广到一切 `(bX, m)`, 在折叠定义里用 `PH-ΦX` (`Φ` 与 `PH-ΦX` 互递归; 判断: 可行, 因为 `PH-ΦX` 只用同底子句); (b) 底做成递归: 第 $k+1$ 个底是 "第 $k$ 个底上某个塔的 $\Omega$-结点", 即 `XS` 的推广 `sup (HB (Lev k)) (λ c → Tw (bS k) (…))`; 那时跨底比较的公共上界是第 $k$ 层的值, 世界 `B` 要换成第 $k$ 层的高度, 证据的单调要 `⊲ᴮ↑` (否定一路 `NegCRwWorld.wdep₁`: 第 1 层值的 ⊲ 依赖世界, PathOut 式 "界 + 与世界无关的序" 不能逐字推广). 判断: 这是 "对 IR 层号 `LH` 递归" 的真正一步, 本路没有做.
2. **路径脚手架** (239 行, 34%) 是剩下最大的一块. 来源是闭项先同底再跨底的两步; 若 (1a) 做成, `PH-ΦX` 进折叠定义, 行数不降 (判断).
3. **地板合法** (`Lg-topL`, 叠层地板的 `LgB`) 没有证 (X1Up 有). 证书不需要它; 否定一路曾指出 "折叠用在不合法的输入上" (`NegPathOutInst.¬LgB-topX₁`), 补上约 35 行 (估计).
4. **`TX` 与 `TXL` 不同** (有限测试). 若要逐项重现 PathOut, 把 $\Omega_1$ 单独作 `XS` 的一个分量 (约 +10 行, 估计).
5. **值的定理**: 没有.

## §8 结论 (按档)

- **[定理]** 接口 `CRwIf` (定稿 00:49); 对一切 `I`: 折叠 `Φ` (一份定义, 对层号递归), 形状 `Sh-Φ`; 叠层路径 `PSL` 与 `PH-mono`, `PH-⊞`, `PH-chain`, 搬运 `clP`, `evE`, `upkE`, `evA`, `upkA`, **`PH-ΦX`** (同底折叠保路径, 对一切世界 $B\rhd 1$); 实例 `I₁`, 地板路径 `PH-topL`; 闭项 `TX`, `TU m`, `TU1`, **`TU2`** (`Cd`, 即只有 $0$, 后继, ℕ-极限的布劳威尔树), 证书 `LgB-TX`, `LgB-TU`, **`LgB-TU2`** (标准 `LgB`), FGH `fghX`, `fghU1`, `fghU2`.
- **[有限测试]** `CRwCmp`: `TU2`, `TU1` 的有界展开结点数与原闭项相同; `TX` 与 `TXL` 不同.
- **[判断]** 读法 `TU2` ψ₀(Ω_{Ω·2}); 逐块不可省的理由; 接手清单的方向.
