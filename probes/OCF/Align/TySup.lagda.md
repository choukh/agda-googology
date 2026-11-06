# 带类型折叠推广到 sup 层: 可数层号, 输出回灌作层号, ψ₀(Ω_Ω) 的候选闭项

> 不含记号. 构造一路 TySup (配对否定一路 NegTySup), 2026-11-05. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP. 闭项, 证书, FGH 无模块参数. 不改任何已有文件.
>
> 文件: 接口 [TySupIf](TySupIf.lagda.md) (定稿 21:37), 折叠 [TySupFold](TySupFold.lagda.md) (对一切满足接口的 `R`), 实例 [TySupC](TySupC.lagda.md) (可数层号), 本篇 (闭项, 证书, FGH, 字面事实).
>
> **这一篇做什么.** 作者本轮选定的打法: "带类型折叠推广到 sup 层". [Fab3Typed](Fab3Typed.lagda.md) 的 `Ψ` 每次坍缩顶种类, 只能沿后继层的塔走 (ψ₀(Ω_ω) 为止). sup 层没有顶种类, 每个种类要按**目标层**决定留还是坍缩. 本路的做法:
>
> 1. 层号是第 0 层的值 `HB S⊥` (可数层号, 含 ℕ-极限), 种类结构 `L x = Lv x` (LFReTy 的 `Lv` 限制到不含 `lΩ` 的层号, 即 `S⊥`/`step`/`sup ℕ`).
> 2. 折叠 `Φ X a lX t pt b` 把层号 $X$ 的高度折到目标层 $t$, 输出就是第 $t$ 层的值. 留/坍缩由 `dec` 决定: 用 `cmpB {S⊥}` 比较种类的位置 `hs i` 与目标 $t$, **公共上界是层号 $X$ 本身** (两者都是 $X$ 的字面第一位置, $X$ 合法). 同层: 链, 回灌恒等 (`feed-id`, refl). 在上: 先在种类自己的层 $i$ 坍缩, 再整个折到 $t$ (对可达性递归).
> 3. 证书由形状给出 (`Sh-Φ`, 对一切输入), 到第 0 层就是 `LgB` (`sh→lgB`).
> 4. **输出回灌作层号.** 闭项 `TC X` 的类型 `HB S⊥` 与层号的类型字面相同. 对角 $y_0=0$, $y_{n+1}=y_n\boxplus TC(y_n+1)$ 把输出直接用作下一个层号 (`code-feed`, refl); `TΩΩ = hl y`.
>
> **读法 (判断, 没有 `ord` 定理).** `TC X` 读 ψ₀(Ω_X) (按 Fab3Typed 的约定 ψ(a+1)=ψ(a)·ω, ψ(0)=1, 外加 ℕ-极限累加); `Tω = TC ω` 读 ψ₀(Ω_ω); `TΩΩ` 读 ψ₀(Ω_Ω): α ↦ ψ₀(Ω_α) 的第一个不动点 (纸面, 判断); `TΩΩ′ = TC TΩΩ` 因此读法相同, 不更高. 越过 Fab3Typed 的 ψ₀(Ω_ω) 是判断, 不是定理; 本篇没有值的比较定理.
>
> **代价, 如实.** (1) **ℕ-极限累加.** `Φ (hl f)` 取部分和, 所以合法不要单调; 不累加时 "在上" 处要比较两种折法 (直接折到 $t$ 与先到 $i$ 再到 $t$), 单调的证明**未找到** (判断, 不是否定). 值上累加对相邻项值相等的极限给 $x\cdot\omega$. (2) **只到可数层号.** `Lv` 的 `lΩ` 层 (共尾度 $\Omega_{k+1}$ 的层号, ψ₀Λ 要的那部分) 不在本实例里: 那里种类的位置要经 $\Omega$-分支, 路径 `hLim` 要带世界里的界, `dec` 的公共上界要在 `SL` 的合法世界里比 (接手清单第 1 条). (3) Fab3Typed 的单调 `Ψ-mono` 与世界的合法 `Lg*` 在本路都不用: 折叠只读界 $b$, 不读世界其余分量.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TySup where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥)
open import OCF.Align.TySupIf
open import OCF.Align.TySupC
import OCF.Align.TySupFold as F
open F ICd using (Φ; chain)
import OCF.Free.Level as FLv
```

## §1 闭项与证书

`TC X lX`: 层号 $X$ 的地板 $\Omega_X$ 折到第 0 层, 当前界 $0$. 第 0 层没有种类, `Sh` 就是 `LgB`.

```agda
sh→lgB : ∀ h → F.Sh ICd {S⊥} h → LgB h
sh→lgB hz s = tt
sh→lgB (hs h) s = sh→lgB h s
sh→lgB (hl f) (st , s) = (λ {w} n → st {w} n) , (λ n → sh→lgB (f n) (s n))
sh→lgB (hΩ () _) s

TC : (X : Cd) → LgB X → HB S⊥
TC X lX = Φ X (wfC X) lX hz (z⊲ᴮ X) hz (topC X)

LgB-TC : ∀ X lX → LgB (TC X lX)
LgB-TC X lX = sh→lgB (TC X lX) (F.Sh-Φ ICd X (wfC X) lX hz (z⊲ᴮ X) hz (topC X))
```

**层号.** 有限层号 `nat n`, ω. 合法由形状 (相邻项字面是后继).

```agda
nat : ℕ → Cd
nat zero = hz
nat (suc n) = hs (nat n)

ωc : Cd
ωc = hl nat

lg-nat : ∀ n → LgB (nat n)
lg-nat zero = tt
lg-nat (suc n) = lg-nat n

lg-ω : LgB ωc
lg-ω = (λ n → hsuc hself) , lg-nat

Tn : ℕ → HB S⊥
Tn n = TC (nat n) (lg-nat n)

Tω : HB S⊥
Tω = TC ωc lg-ω
```

**输出回灌作层号.** $y_{n+1}=y_n\boxplus TC(y_n+1)$; 每个 $y_n$ 合法 (由 `LgB-TC` 与 `Lg-⊞`), 对角的相邻项字面是第一位置 (`⊞-fst`).

```agda
yΩ : ℕ → Cd
lg-yΩ : ∀ n → LgB (yΩ n)
yΩ zero = hz
yΩ (suc n) = yΩ n ⊞ TC (hs (yΩ n)) (lg-yΩ n)
lg-yΩ zero = tt
lg-yΩ (suc n) = Lg-⊞ (yΩ n) (TC (hs (yΩ n)) (lg-yΩ n)) (lg-yΩ n) (LgB-TC (hs (yΩ n)) (lg-yΩ n))

TΩΩ : HB S⊥
TΩΩ = hl yΩ

LgB-TΩΩ : LgB TΩΩ
LgB-TΩΩ = (λ n → ⊞-fst (yΩ n) (TC (hs (yΩ n)) (lg-yΩ n))) , lg-yΩ

-- 对角本身也可作层号: Ω_{TΩΩ} 的坍缩 (读法同 TΩΩ: 不动点, 判断)
TΩΩ′ : HB S⊥
TΩΩ′ = TC TΩΩ LgB-TΩΩ
```

**FGH.** 第 0 层的树逐构造子读成 `Ordᶜ zero`.

```agda
ord⊥ : HB S⊥ → FLv.Ordᶜ FLv.zero
ord⊥ hz = FLv.zero
ord⊥ (hs h) = FLv.suc (ord⊥ h)
ord⊥ (hl f) = FLv.lim (λ n → ord⊥ (f n))
ord⊥ (hΩ () _)

fghω : ℕ → ℕ
fghω = FLv.FGH (ord⊥ Tω)

fghΩΩ : ℕ → ℕ
fghΩΩ = FLv.FGH (ord⊥ TΩΩ)
```

## §2 字面事实 (定理, refl)

**回灌是恒等.** `TC 1`: 第 0 层的新种类 ($\Omega_1$) 对目标 $0$ 是同层, 链的点是 "当前界上的分支折出的输出", 界与坐标是同一个值 (类型 `HB S⊥` 字面相同), 没有读回.

```agda
feed-id : Tn 1 ≡ hl (chain hz (λ b′ → Φ (nat 1) (wfC (nat 1)) tt hz (hsuc hself) b′ (up b′)))
feed-id = refl
```

**在上.** `TC 2`: 第 1 层的新种类 ($\Omega_2$) 对目标 $0$ 在上: 先在第 1 层坍缩 (链从地板 $\Omega_1$ 起, 分支折到第 1 层), 再整个折到第 0 层.

```agda
above-2 : Tn 2 ≡ Φ (nat 1) (wfC (nat 1)) tt hz (hsuc hself) hz
                   (hl (chain (topC (nat 1)) (λ b′ → Φ (nat 2) (wfC (nat 2)) tt (nat 1) (hsuc hself) b′ (up b′))))
above-2 = refl
```

**回灌作层号.** 对角的下一个层号字面就是上一个层号接上它的坍缩.

```agda
code-feed : ∀ n → yΩ (suc n) ≡ yΩ n ⊞ TC (hs (yΩ n)) (lg-yΩ n)
code-feed n = refl
```

## §3 测试 (有限样本, 不是证明)

`TC 1` 的第 0 个链点是 $1$ (同 Fab3Typed 的 `d₀`).

```agda
private
  d₀ : chain {S⊥} hz (λ b′ → Φ (nat 1) (wfC (nat 1)) tt hz (hsuc hself) b′ (up b′)) 0 ≡ hs hz
  d₀ = refl
```

## 行数 (定义级切片)

`Survey/scripts/tysup/locslice_tysup.py` (口径同 `fab3/locslice_fab3.py`; `TySupFold` 经模块应用使用, 模块内定义手工列根, 近似). 2026-11-05 跑出:

| 层 | 本路新增 | 树侧全部 (累计) | 记号模块 |
|---|---|---|---|
| 1 定义 (接口, 层号, `Lv`, `KS`/`HB`/`step`/`sup`) | 60 | 274 | 0 |
| 2 + 折叠 (`Φ`, `dec` 含 `cmpB`, 闭项 `Tn`, `Tω`, FGH) | 151 | 425 | 0 |
| 3 + 证书 (`Sh-Φ`, `LgB-TC`; 对角 `TΩΩ` 要证书才能定义, 归在这层) | 215 | 504 | 0 |
| 4 + 形状 (`feed-id`, `above-2`, `code-feed`) | 222 | 511 | 0 |

对照 (前 3 层, 同口径, 各自的切片): Fab3Typed 402 (读法 ψ₀(Ω_ω)), LeanT 745, FabLFReGen 1513 (后两者的读法与 ψ₀Λ 候选的读法都是判断). 本路 504 的读法 ψ₀(Ω_Ω) (判断). 跨读法的行数不作比较结论.

## 翻译账

- **新结点, 新字段.** 无新结点. 接口字段 (`lv`, `pos`, `toE`, `top`, `dec`) 都是树侧已有东西的抽象: 种类的读回层 (`LFReTy.lvl` 的形状), 地板 (Fab3Typed 的 `Ω`/`W`), 比较 (`cmpB`). `Dc` 的三种结果由 "目标层与种类层号" 的序给出 (低, 同, 高), 不读记号的基本列.
- **由树逼出.** (1) 决定要带公共上界: 两个层号在 ℕ-极限的不同分量里, 只能经 $X$ 的步进证明比 (`cmpB` 的 `hlim` 行); 裸下标的版本是 `NegTySupSel` 的分离子与 LPO. (2) "在上" 要先在种类自己的层坍缩: 坐标类型是第 $i$ 层的值, 直接回灌第 $t$ 层的输出要嵌入, 那是把 $\Omega_{i+1}$ 当 $\Omega_{t+1}$ 用 (判断). (3) 累加: 合法不靠单调 (单调未找到).
- **受记号启发, 如实.** 读法 (ψ₀(Ω_X), 不动点) 是对照 Buchholz 式记号的判断; "Ω_{i+1} 结点的基本列在第 $i$ 层取" 是 OCF 的标准做法, 本路沿用 Fab3Typed 的链形状. `Lv` 的形状 LFReTy 已自述为记号引导.
- **摆脱侧.** 相对 FabLFReGen/GenFold: 没有数据树 `D`, 状态, 目标 `Tg`, 读回 `rd₁`, 升界 `rsA`; 世界只剩一个界 $b$. sup 层的 C6 (按种类更新世界) 在可数层号上**没有出现**: 世界不按种类存界, 同层用当前界, 在上从第 $i$ 层的地板重起 (Fab3Typed 的基世界). 这一条是对可数层号的事实 (定义如此), 对 `lΩ` 层号未知.
- **攀爬侧.** 读法从 ψ₀(Ω_ω) 到 ψ₀(Ω_Ω) (判断), 低于 FabLFReGen 的 `TΛ` 树形.

## 接手清单

1. **`lΩ` 层号 (ψ₀Λ).** 新实例 `C = LH`: 种类的位置要经 `lΩ k g` 的分支 $g\,c$, 而接口的 `pos X κ` 不带世界; 目标路径与种类位置若都进 $g$ 的不同坐标 $c, c'$, 比较要 $c, c'$ 在同一合法世界的同一界之下 (`cmpB {Lv k}`). 所以 `pos` 要带世界与界 (接口只增: 新开记录 `TySupIfᵂ`, 位置与 `dec` 都以世界 $W$ 与 `LgW W` 为参数). 这就是 Fab3Typed 说的 "sup 层的 C6" 在本路的字面位置 (判断, 未写, 没有编译错误可引).
2. **值的定理.** 本路没有 `ord`/`≼` 定理. 先试: `Tn n` 与 Fab3Typed `TΩ n` 互相 `≼` (差别只在累加); `TC X ≼ TC (hs X)`. 字面的 `Φ ωc (ι n h) ≡ Φ (nat n) h` 不是 refl (分支里的变量挡住; scratch 测试 n=1 报 `hl nat != hs hz`), 要对 $h$ 归纳的模拟关系.
3. **单调.** 不累加时的字面单调在 "在上" 处要 "直接折到 $t$" 与 "经 $i$ 再到 $t$" 的比较; 未找到. 可请否定一路对它写否定或给反例.
4. **FGH 测试.** 本路没有算 FGH 的值 (`fghω`, `fghΩΩ` 只是定义).

## 结论 (按档)

- **[定理]** 接口 `TySupIf` (律带公共上界); 折叠 `TySupFold.Φ` (对一切 `R`) 与 `Sh-Φ` (输出由形状合法, 对一切输入); 实例 `ICd` (可数层号, `dec` 用 `cmpB` 以层号 $X$ 为公共上界); 闭项 `Tn n`, `Tω`, `TΩΩ`, `TΩΩ′` 与证书 `LgB-TC`, `LgB-TΩΩ`, FGH `fghω`, `fghΩΩ`; `feed-id`, `above-2`, `code-feed`.
- **[测试]** `d₀`.
- **[判断]** 读法 ψ₀(Ω_n), ψ₀(Ω_ω), ψ₀(Ω_Ω); 不累加时的单调未找到; `lΩ` 层号 (ψ₀Λ) 未做.
