# Fold1: 改 "在上" 的折法 (入口)

> 不含记号. 构造一路 Fold1 (配对否定一路 NegFold1), 2026-11-06. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`, 不用函数外延, 不用 UIP. 闭项, 证书, FGH 无模块参数. 导入闭包只有 stdlib, `OCF.Lean.CRwBase` 与 `OCF.Lean.Fold1*`. 不改任何已有文件.
>
> **任务** (作者本轮选定, 原话 "摆脱: 改 '在上' 的折法"; 说明 "毛刺的根在 '先折到种类自己的层再折到目标' 的两段折法; 试每次只折一层的写法推广到 sup 层, 或用值关系作证书"). 本路的写法是第三种: 不逐层复合 (否定一路 `NegFold1Sup.sup-not-one` 说 sup 层没有 "降一层" 的目标), 也不用值关系作证书, 而是**直接折到目标层, "在上" 的链只作坐标**.

| 文件 | 内容 |
|---|---|
| [Fold1If](Fold1If.lagda.md) | 接口 (定稿 08:07): 塔 `Lv`, 地板 `top`, `mul`, 不带世界的值关系 `≤ᵛ`; 契约 `Fold1If` |
| [Fold1Base](Fold1Base.lagda.md) | 合法 `Lg*` 与合法结构 `LS` (`step*`, `sup*`, 塔的 `ℓT`); 路径上的搬运; 地板合法, 地板世界 `Wi`; 值关系引理 |
| [Fold1Fold](Fold1Fold.lagda.md) | 输入一侧的世界 `ext`, 种类的视图 `vw`, **折叠 `Φ`**, **`Φ-mono`**, **`Φ-lg`**, `Φ-≤` |
| 本篇 | 接口实例, 闭项, 证书, FGH; 与 `NoAccStuck` 的对照; 测试; 两边账 |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.Fold1 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If
open import OCF.Lean.Fold1Base
open import OCF.Lean.Fold1Fold
```

## §1 接口实例

目标层的界 $b$ 在本实现里不用: 每个种类的界都在输入世界里, 初始世界是地板世界 `Wi m` (第 $x+1$ 层的种类, 界是第 $x$ 层的地板 `top x`). 合法 `Lg m` 是 `Lg*` (ℕ-极限在一切合法世界里步进); 第 $0$ 层只有一个世界, `Lg*` 推出 `LgB` (`lgB⊥`).

```agda
I : Fold1If
I = record
  { Φ = λ m lm t pt b h → Φ m lm t pt (Wi m) h
  ; Φ-z = λ _ _ _ _ _ → refl
  ; Φ-s = λ _ _ _ _ _ _ → refl
  ; Φ-pt = λ _ _ _ _ _ _ → refl
  ; Lg = λ m → Lg* (ℓT m)
  ; lg₀ = lgB⊥
  ; lg-top = λ m _ → lg-top* m
  ; Φ-lg = λ m lm t pt b _ h l → Φ-lg m lm t pt (lgWi m) h l
  ; Win = λ m lm b → Wi m
  ; Φ-mono = λ m lm pt {b} {a} {c} lb lc p →
      Φ-mono m lm hz pt {tt} {Wi m} tt (lgWi m) c lc (trW (Lv m) (trBd m lm pt) p)
  ; Φ-≤ = λ m lm t pt b oa oc p → Φ-≤ {m} {lm} {t} {pt} {Wi m} oa oc p
  ; Φ-l11 = λ m lm t pt b →
      Φ-≤ {m} {lm} {t} {pt} {Wi m} (λ _ → tt) tt (l≤ (λ _ → ≤-refl one)) ,
      Φ-≤ {m} {lm} {t} {pt} {Wi m} tt (λ _ → tt) (≤l 0 (≤-refl one))
  }
```

## §2 闭项, 证书, FGH

`TΩ m`: 第 $m$ 层的地板直接折到第 $0$ 层 (读法 ψ₀(Ω_m), 判断). 证书是 `Φ-lg` 加地板合法, 第 $0$ 层的 `Lg*` 就是 `LgB`. `TΩΩ`: 对角 $y_0=0$, $y_{n+1}=y_n\boxplus T\Omega(y_n+1)$ (同 CRw 的 `TU2` 的对角形状), 读法 ψ₀(Ω_Ω) (判断).

```agda
TΩ : (m : Cd) → LgB m → Cd
TΩ m lm = Φ m lm hz (z⊲ᴮ m) (Wi m) (top m)

LgB-TΩ : ∀ m lm → LgB (TΩ m lm)
LgB-TΩ m lm = lgB⊥ _ (Φ-lg m lm hz (z⊲ᴮ m) (lgWi m) (top m) (lg-top* m))

num : ℕ → Cd
num zero = hz
num (suc n) = hs (num n)

ω′ : Cd
ω′ = hl num

lg-num : ∀ n → LgB (num n)
lg-num zero = tt
lg-num (suc n) = lg-num n

lg-ω′ : LgB ω′
lg-ω′ = (λ n → hsuc hself) , lg-num

TΩ1 TΩω : Cd
TΩ1 = TΩ (hs hz) tt
TΩω = TΩ ω′ lg-ω′

yΩ : ℕ → Cd
lg-yΩ : ∀ n → LgB (yΩ n)
yΩ zero = hz
yΩ (suc n) = yΩ n ⊞ TΩ (hs (yΩ n)) (lg-yΩ n)
lg-yΩ zero = tt
lg-yΩ (suc n) = Lg-⊞ (yΩ n) _ (lg-yΩ n) (LgB-TΩ (hs (yΩ n)) (lg-yΩ n))

TΩΩ : Cd
TΩΩ = hl yΩ

LgB-TΩΩ : LgB TΩΩ
LgB-TΩΩ = (λ n → ⊞-fst (yΩ n) _) , lg-yΩ
```

**FGH** (同 `CRw.FGH` 的次序, 这里独立写出).

```agda
iter : (ℕ → ℕ) → ℕ → ℕ → ℕ
iter f x zero = x
iter f x (suc n) = f (iter f x n)

FGH : Cd → ℕ → ℕ
FGH hz n = suc n
FGH (hs a) n = iter (FGH a) n n
FGH (hl f) n = FGH (f n) n
FGH (hΩ () _) n

fghΩ1 fghΩω fghΩΩ : ℕ → ℕ
fghΩ1 = FGH TΩ1
fghΩω = FGH TΩω
fghΩΩ = FGH TΩΩ
```

## §3 与 `NoAccStuck` 的对照

`NoAccStuck` 的输入 (这里在本路的塔 `Lv 2` 上字面重写): $N=\lim(0,1,2,\dots)$, $\Omega_c=\Omega_2\{\_\mapsto N\}$, $\mathrm{inp}=\lim(N,\Omega_c,\Omega_c,\dots)$. 那里证了: 逐点的两段折法把 `inp` 折成不合法的树 (`no-cert`), 直接折与两段折不可比 (`route-mismatch`). 本路: `inp` 满足 `Lg*` (`Lg-inp`), 所以输出合法 (`out-lg`, 由一般定理 `Φ-lg`); 而且 $\Phi\,N\lhd\Phi\,\Omega_c$ 是字面的 (`route-ok`): 在上结点的输出第 $0$ 项就是在同一世界里直接折 $N$.

```agda
L2 : Cd
L2 = hs (hs hz)

nm : ℕ → HB (Lv L2)
nm zero = hz
nm (suc n) = hs (nm n)

N : HB (Lv L2)
N = hl nm

Ωc : HB (Lv L2)
Ωc = hΩ (inj₂ tt) (λ _ → N)

fI : ℕ → HB (Lv L2)
fI zero = N
fI (suc n) = Ωc

inp : HB (Lv L2)
inp = hl fI

lg-nm : ∀ n → Lg* (ℓT L2) (nm n)
lg-nm zero = tt
lg-nm (suc n) = lg-nm n

Lg-N : Lg* (ℓT L2) N
Lg-N = (λ lw n → hsuc hself) , lg-nm

Lg-inp : Lg* (ℓT L2) inp
Lg-inp = st , lg
  where
  st : ∀ {w} → LgW* (ℓT L2) w → ∀ n → fI n ⊲[ w ] fI (suc n)
  st {w} lw zero = hLim (botBd (Lv L2) (inj₂ tt) w) hself
  st lw (suc n) = hself
  lg : ∀ n → Lg* (ℓT L2) (fI n)
  lg zero = Lg-N
  lg (suc n) = (λ lw e e′ p → hself) , (λ c lc → Lg-N)

Φ20 : HB (Lv L2) → Cd
Φ20 = Φ L2 tt hz (z⊲ᴮ L2) (Wi L2)

out-lg : LgB (Φ20 inp)
out-lg = lgB⊥ _ (Φ-lg L2 tt hz (z⊲ᴮ L2) (lgWi L2) inp Lg-inp)

route-ok : Φ20 N ⊲ Φ20 Ωc
route-ok = hlim 0 hself
```

## §4 测试 (有限样本, 不是证明)

$\Omega_1$ 的地板折到第 $0$ 层: 坐标链从界 $0$ 起, 输出第 $0$ 项 $\Phi(\mathrm{up}\,0)=1$, 第 $1$ 项 $1\boxplus\Phi(\mathrm{up}\,1)=1\boxplus\omega$ (同 Fab3Typed 的 `d₀`, `d₁`). $\lim(1,1,\dots)$ 与 $1$ 折出的树: 前者是后者的常值 ℕ-极限 (逐点).

```agda
private
  hd : Cd → ℕ → Cd
  hd (hl f) n = f n
  hd x n = x

  d₀ : hd TΩ1 0 ≡ hs hz
  d₀ = refl

  d₁ : hd TΩ1 1 ≡ hs hz ⊞ hl (mul (hs hz))
  d₁ = refl

  l11-pt : Φ (hs hz) tt hz (hsuc hself) (Wi (hs hz)) (l11 {Lv (hs hz)}) ≡ hl (λ _ → Φ (hs hz) tt hz (hsuc hself) (Wi (hs hz)) one)
  l11-pt = refl
```

## §5 值: 本路证了什么, 没证什么

**常值 ℕ-极限 (定理, 对一切输入, 包括含 $\Omega$-结点的).** $\lim(h,h,\dots)$ 与 $h$ 互相 $\le$; 折叠后 $\Phi\lim(h,h,\dots)$ 与 $\Phi\,h$ 也互相 $\le$ (对一切层号, 目标, 世界). 对照 `NegValCInst.acc-not-mono≤`: CRw 的累加折叠把 $\lim(1,1,\dots)$ 折成严格高于 $\Phi\,1$ 的树. 本路这一条只来自 ℕ-极限子句逐点 (否定一路 `NegFold1If` 指出同类事实: 它是三个子句的推论).

```agda
const-in : ∀ {S : KS} (h : HB S) → (hl (λ _ → h) ≤ᵛ h) × (h ≤ᵛ hl (λ _ → h))
const-in h = l≤ (λ _ → ≤-refl h) , ≤l 0 (≤-refl h)

const-out : ∀ m lm t pt W (h : HB (Lv m)) →
  (Φ m lm t pt W (hl (λ _ → h)) ≤ᵛ Φ m lm t pt W h) × (Φ m lm t pt W h ≤ᵛ Φ m lm t pt W (hl (λ _ → h)))
const-out m lm t pt W h = l≤ (λ _ → ≤-refl _) , ≤l 0 (≤-refl _)
```

**[定理]** `Φ-≤` (Fold1Fold §6): 无 $\Omega$ 的输入上, 值关系被保持; 实例的 `Φ-l11`. **[没证]** 含 $\Omega$-结点的输入上折叠是值的函数. 否定一路 `NegFold1If.no-val-ext` 说: 用不带界的 `≤ᵛ` 这条不可能 ($\Omega$-极限在右边时任取坐标太松); 要用带界的值关系 (同 `Fab5ValRel` 的 `Bdᵛ`, `Moᴱ`) 重证 Fab5 的 `Ψ-mono≤`. 本路没有做 (接手清单 1). 坍缩处的输出仍是部分和 (`oO`). **否定一路的结果 (主审复核前不算数)**: `NegFold1X.col-acc` 给出第 1 层的合法输入 $A=\Omega_1\{\_\mapsto 1\}$, 折出 $\lim(\omega,\omega\boxplus\omega,\dots)$, 而 $1$ 折出 $\omega$, $\neg(\Phi A\le\Phi 1)$; 推论 `col-not-val`: 对任何含自反与带界 $\Omega$-左规则的值关系, 本路的折叠不保值序. 根是坍缩输出取部分和 (相邻输出点相等时抬高值). 所以 "折叠是值的函数" 在含 $\Omega$ 的输入上对本路**不成立** (若该结果复核通过), 累加从 ℕ-极限子句移到了坍缩子句, 没有消失. `NegFold1X.gl-TΩ1`: `TΩ1` 的第 1 项字面是 $1\boxplus\omega$ (测试 `d₁`), 值等于 $\omega$, 基本列有部分和的痕迹.

## §6 两边账: 与 CRw 比

| | CRw (`CRwFold.Φ`, 同底部分) | 本路 (`Fold1Fold.Φ`) |
|---|---|---|
| ℕ-极限子句 | 部分和 `Σ⁺` (累加) | **逐点** |
| 后继子句 | 部分积 `mul` | 部分积 `mul` (同) |
| 在上 ($t\lhd x$) | 两段: 第 $x$ 层的链 (起点 `top x`), 整条链再从 $x$ 折到 $t$ | 一段: 第 $x$ 层的链只作坐标 (起点是世界里的界, 初始世界里就是 `top x`), 输出点直接折到 $t$, 输出取部分和 |
| 同层 ($x=t$) | 回灌链 `chain b` (界 $b$ 是目标层的参数) | 与在上同一条规则 (界在输入世界里) |
| 决定 | `cmpB` 比较每个新种类的层号与 $t$ (公共上界 $m$) | 沿证据 $t\lhd m$ 走塔; 只在 ℕ-极限层的分量处 `cmpB` (公共上界 $m$) |
| 世界 | 同底时不用 | 每个种类一个界, 坍缩时换界 (`upd`, ℕ-极限层用 `≟` 换一个分量) |
| 证书 | 形状 `Sh-Φ`, 不读输入 (对一切输入) | **读输入合法** `Lg*` (`Φ-lg`), 要第一位置单调 `Φ-mono` |
| 值的函数 | 否 (`acc-not-mono≤`, 定理) | 无 $\Omega$ 输入与常值序列上是 (定理); 含 $\Omega$ 的输入上否 (`NegFold1X.col-acc`, 待复核: 坍缩输出的部分和) |
| `NoAccStuck` 的输入 | 合法 (`crw-lg`, 累加) | 合法 (`out-lg`), 且 $\Phi N\lhd\Phi\Omega_c$ 字面成立 (`route-ok`) |
| 闭项读法 (判断) | `TU2` ψ₀(Ω_{Ω·2}) (跨底) | `TΩΩ` ψ₀(Ω_Ω) (只有可数层号) |

**证明义务, 如实.** CRw 的证书对一切输入, 不要单调 (`CRwFold` §7 形状证书共 49 行); 代价是累加 (不是值的函数). 本路去掉 ℕ-极限与两段折的累加后, 由 `NegNoAccPt.pt-no-total`, 证书必须读输入合法; 本路付出的是: 合法结构 `LS`/`Lg*` 与塔的 `ℓT` (含 `sup*`), 输入一侧的世界 `ext` 与它的合法 `extLg`, 视图里的搬运字段 (界, `Pr`, 坐标合法), 路径搬运 (`liftK`/`frK`/`sub` 与五条引理), `Φ-mono`, `Φ-lg`, 地板合法 `lg-top*`. 跨底 (CRw 的 $\Omega_1$ 层作层号, 路径 `PH`) 本路没有.

## §7 行数 (定义级切片)

脚本 `Survey/scripts/fold1/locslice_fold1.py` (改写自 `crw/locslice_crw.py`, 同一切片机 `locslice.py`). 2026-11-06 跑出 (主闭项 `TΩΩ`):

| 层 | Fold1 (`TΩΩ`, ψ₀(Ω_Ω)) | 对照 (取自各文件) |
|---|---|---|
| 1 定义 | 185 | |
| 2 + 折叠, 闭项, FGH | 487 | |
| 3 + 证书 | **489** | CRw 696 (`TU2`, ψ₀(Ω_{Ω·2})), TySup 504 (ψ₀(Ω_Ω)), PathOut 743 (ψ₀(Ω_Ω)), FabLFReGen 1513 |

第 3 层逐模块: `Fold1Base` 148, `CRwBase` 144, `Fold1Fold` 137, `Fold1` 39, `Fold1If` 21. 闭包里 `Fold1*`, `CRwBase` 之外的仓库模块: 0; 记号模块: 0. 折叠本身 (`Φ`, `ΦV`, 视图 `vw`/`vwC`/`liftS`/`liftL`, 坍缩链 `Col`, `cmpk`, `lgk`): 60 行. 世界与路径搬运: 73 行.

**口径差, 如实.** (1) **层 1, 2 不能与 CRw 逐层比**: 视图 `Vw` 的构造子带搬运字段 (界, `Pr`, 坐标合法, 世界合法), 折叠用到视图, 所以 `Lg*`, `LS`, `ℓT`, `extLg` 一类证书的定义在层 1, 2 就进了闭包; 层 3 只多 2 行. 只有层 3 的总数可比. (2) 读法不同: 本路 489 对 ψ₀(Ω_Ω) (判断), CRw 696 对 ψ₀(Ω_{Ω·2}) (判断); 跨读法不作比较结论. 同读法 (判断) 的对照是 TySup 504 与 PathOut 743. (3) 本路的证书含地板合法 (`lg-top*`, 证书要它); CRw 不证地板合法.

## §8 翻译账

- **新结点, 新字段.** 无新结点. 新的组织: 坍缩的一条规则 (坐标链 + 直接折的输出); 种类的视图 (留 / 坍缩, 带搬运字段); 输入一侧的世界 `ext`.
- **由树逼出.** (1) 输出点直接折到 $t$: `NoAccStuck.route-mismatch` (编译过的否定) 说直接折与两段折不可比, 逐点之后输出的 ℕ-极限要步进, 所以输出的每一点都要同一种折法. (2) 坐标链在第 $x$ 层: 结点的坐标类型就是第 $x$ 层的高度. (3) 链的第 $0$ 点是世界里的界, 换界: `Φ-mono` 在坍缩结点处要 "界之下的坐标 $c'$ 满足 $g\,c'\lhd g\,e_0$", 只能取 $e_0=$ 界. (4) 证书读输入合法, 要单调: `NegNoAccPt.pt-no-total`. (5) 输入一侧的世界 `ext v W` (留下的分量换成目标世界的子世界): `Φ-lg` 的 ℕ-极限处要对一切合法的目标世界 $v$ 步进, 留下的结点的界必须是 $v$ 的界. (6) 坍缩处输出取部分和: 逐点的输出点在不同世界里折, 相邻点之间没有字面第一位置 (判断, 未写成否定定理; 对照 `NegNoAccX.⊞-not-monoˡ`: 回灌对世界不保第一位置).
- **受记号启发, 如实.** "在上的链只作坐标, 输出直接折到目标" 与扩展 Buchholz 记号的基本列 ($\psi_\nu(\alpha)[n+1]=\psi_\nu(\alpha[\beta_{n+1}])$, $\beta_{n+1}=\psi_\mu(\alpha[\beta_n])$, $\beta_0=\Omega_\mu$) 同形. 设计时我想到了这一形状 (凭记忆, 本轮没有读记号文件); 定义, 定理, 证书都不依赖记号. 读法是对照它的判断.
- **摆脱侧.** 去掉: ℕ-极限的部分和, "在上" 的两段折, 每个新种类的层号比较 (改为沿证据走塔), 同底折叠的 `Acc` 可达性 (折叠对高度结构递归, 层号不变). 留下的累加: 后继 `mul`, 坍缩的输出部分和与坐标链, 地板 `ΣT`, 对角 `yΩ`.
- **攀爬侧.** 读法不升 (ψ₀(Ω_Ω) < CRw 的 ψ₀(Ω_{Ω·2}), 判断). 这一步是摆脱侧.

## §9 接手清单

1. **含 $\Omega$ 的输入上的值定理.** 用带界的值关系 (`Fab5ValRel` 的形状, 对 `CRwBase` 重写) 证 `Φ` 对世界与输入联合值单调 (Fab5 的 `Ψ-mono≤` 推广到多层与视图). 难点 (判断): 坍缩的输出是部分和, 坐标链在第 $x$ 层另折一次, 两条链要同时比较.
2. **跨底, 重现 `TU2`.** $\Omega_1$ 层 (`XS`) 作层号时, 种类 $(c,\kappa)$ 与目标 $t$ 没有公共上界 $m$, 要 CRw 式的世界的界 $B$ 与路径证据. 本路的 "沿证据走塔" 在那里不直接适用 (判断). 估计: 需要 CRwPath 一类的路径脚手架 (CRw 192 行) 加 `XS` 上的视图.
3. **视图拆成数据与证明**, 使层 1, 2 只含定义 (估计 +30 行, 总数不降).
4. 接口的界 $b$ 在实例里不用; 若要与 CRw 的 `chain b` 逐项对照, 把 `Wi` 里目标层之上一层的界换成 $b$ (约 +15 行, 估计).
5. 坍缩处的输出部分和是否可换成逐点: 未走通 (见 §8 (6), 判断). 这是 `NegFold1X.col-acc` 指向的位置: 要值的函数, 下一步要在坍缩处去掉部分和, 同时给出输出 ℕ-极限的步进 (例如证明折叠对世界的界单调).

## §10 结论 (按档)

- **[定理]** 接口 `Fold1If` (定稿 08:07) 与实例 `I`; 合法 `Lg*`, `step*`, `sup*`, `ℓT`, `lgB⊥`, `lg-top*`, `lgWi`; 路径搬运 `ftK`, `bdDn`, `bdUp`, `prDn`, `lgDn`, `lgSub`, `trW`; 视图 `vw`; 折叠 `Φ` (对一切可数层号与目标一条定义); **`Φ-mono`**, **`Φ-lg`** (对一切层号, 目标, 世界; 读输入合法); `Φ-≤`, `const-in`, `const-out`, `trBd`; 闭项 `TΩ m`, `TΩ1`, `TΩω`, **`TΩΩ`** (`Cd`), 证书 `LgB-TΩ`, **`LgB-TΩΩ`** (标准 `LgB`), FGH `fghΩ1`, `fghΩω`, `fghΩΩ`; `NoAccStuck` 输入的对照 `Lg-inp`, `out-lg`, `route-ok`.
- **[有限测试]** `d₀`, `d₁`, `l11-pt`.
- **[判断]** 读法 `TΩ m` ψ₀(Ω_m), `TΩΩ` ψ₀(Ω_Ω); §8 (6); 接手清单的估计.
