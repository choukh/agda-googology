# 有内容的下降, 否定一路 (二): 忠实不说大小, 也不排除各站输出为常数

> 不含记号. 入口 [NegDnFold](NegDnFold.lagda.md). 对着接口 [DnFoldIf](DnFoldIf.lagda.md) ("接口定稿 2026-11-05 16:13 (首次编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> 嫌疑 (ii) 说有损下降 D2 必然压回统一形状, 使忠实不可能; 嫌疑 (iii) 说求值下降在第 2 站起输出为常数. 本篇的回答是一个**反模型** (定理): 接口的有损记录 `DnSq` 与忠实 `FaithRd`, `Faith0`, `FaithTower`, `DiffTkc` **同时**被一个几乎什么也不做的下降满足, 而它在每一站的回灌输出都是同一个常数 $2$.
>
> - **`sqC`** (对一切 `T`): `HB (step T) → Ht`, 后继照搬, ℕ-极限给 $0$, 旧种类的 $\Omega$-结点走底支 `bot`, 新种类的 $\Omega$-结点走坐标 $1$ 那一支. 输出全是有限高度 `finH n` (`sqC-fin`), 所以对任何输入都合法 (`lgC`).
> - **`dsqC T : DnSq T`**: `cs n = 1`, `comb f = f 0`, `sq-new` 是 `refl`. 嫌疑 (ii) 的 "压回" 在这里是真的 (一切都压成有限高度), 但 **`FaithRd T sqC` 成立** (`cheapFaith`): $\mathrm{sqC}(\mathrm{rdTop}\,T)=2\neq1=\mathrm{sqC}(\mathrm{rdCut}\,T)$, 因为读回在坐标 $1$ 处的分支是 $1$, 截断处是 $0$.
> - **塔 `dnC`, `dnLC`**: 层号是后继 `hs c` 时用 `sqC {Lev c}` (第 $c$ 级之上一级就是 `step (Lev c)`), 别处给 $0$. 定理: `Faith0 dnC` (`faith0C`), `FaithTower dnC dnLC` (`faithTC`), **每站回灌输出都是 $2$** (`HsC`), 而 `DiffTkc dnC dnLC` 也成立 (`diffC`: 第 0 站的 $2$ 不等于截断版 `TrK.Hs 0`).
>
> **这对构造一路的意思.** `FaithTower` 与 `DiffTkc` 是构造一路想用来说明 "读回进了闭项" 的形状要求; 本篇说它们与 "各站输出是同一个有限常数" 相容, 所以不能用它们说明下降有内容, 更不能说明大小 (手册 §3.3 的幽灵: `HS-Nxˢ`, `pinch`, `noCert₂` 同一类). 要排除这类实例, 忠实须写成值的陈述 (例如 `Hs s` 在 `ord` 下随 $s$ 严格增长, 或与参照树的界), 或至少要求下降对新种类结点的**一切**坐标的分支有反应 (判断: 后者对 D2 是不可能的, `sq-new` 只看 `cs`; 对 D1 是开放的).
>
> **只否定什么.** 编译的是满足接口全部形状律的反模型 (正面定理). 它否定的是**一个推断**: "满足 `FaithRd`/`FaithTower`/`DiffTkc` 的下降就让读回有内容地进入了闭项". **不否定** 接口的任何记录, 也不否定有损下降或求值下降能有内容 (那是值的问题, 本篇没有值定理).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegDnFoldBlind where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.CumReadCF using (azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.HtTowerFTree using (S₁; Ht; D; n0)
open import OCF.Align.ColimWIf using (finH)
open import OCF.Align.LvKtIf
open import OCF.Align.LvKtInst using (module TrK)
open import OCF.Align.KcFoldIf
open import OCF.Align.KcFoldTower using (module KD; module Shape)
open import OCF.Align.DnFoldIf
```

## §1 一个几乎什么也不做的有损下降

```agda
sqC : ∀ {T : KS} → HB (step T) → Ht
sqC hz = hz
sqC (hs x) = hs (sqC x)
sqC (hl f) = hz
sqC {T} (hΩ (inj₁ κ) g) = sqC (g (bot T κ))
sqC (hΩ (inj₂ tt) g) = sqC (g (hs hz))

-- 输出都是有限高度
sqC-fin : ∀ {T : KS} (x : HB (step T)) → Σ ℕ (λ n → sqC x ≡ finH n)
sqC-fin hz = zero , refl
sqC-fin (hs x) = suc (proj₁ (sqC-fin x)) , cong hs (proj₂ (sqC-fin x))
sqC-fin (hl f) = zero , refl
sqC-fin {T} (hΩ (inj₁ κ) g) = sqC-fin (g (bot T κ))
sqC-fin (hΩ (inj₂ tt) g) = sqC-fin (g (hs hz))

lgC : ∀ {T : KS} (x : HB (step T)) → LgB (sqC x)
lgC hz = tt
lgC (hs x) = lgC x
lgC (hl f) = tt
lgC {T} (hΩ (inj₁ κ) g) = lgC (g (bot T κ))
lgC (hΩ (inj₂ tt) g) = lgC (g (hs hz))

dsqC : ∀ (T : KS) → DnSq T
dsqC T = record
  { sq = sqC ; lsq = λ x _ → lgC x ; cs = λ _ → hs hz ; comb = λ f → f 0 ; sq-new = λ g → refl }

-- 接口的忠实成立
cheapFaith : ∀ (T : KS) → FaithRd T (DnSq.sq (dsqC T))
cheapFaith T ()

-- 两个读回的像: 2 与 1
top↦2 : ∀ (T : KS) → sqC (rdTop T) ≡ hs (hs hz)
top↦2 T = refl

cut↦1 : ∀ (T : KS) → sqC (rdCut T) ≡ hs hz
cut↦1 T = refl
```

## §2 塔上的实例: 忠实成立, 每站输出是常数 $2$

```agda
dC : ∀ {𝕂 : KS} (b : HB 𝕂) → LgB b → DnK (Lev b)
dC hz lb = (λ _ → hz) , (λ _ _ → tt)
dC (hs c) lb = sqC {Lev c} , (λ x _ → lgC x)
dC (hl f) lb = (λ _ → hz) , (λ _ _ → tt)
dC (hΩ κ g) lb = (λ _ → hz) , (λ _ _ → tt)

dnC : DnTower
dnC s b lb = dC b lb

dnLC : DnLim
dnLC b lb = dC b lb

faith0C : Faith0 dnC
faith0C = cheapFaith S₀

faithTC : FaithTower dnC dnLC
faithTC s = cheapFaith (Lev (Shape.X dnC dnLC s))

module KC = KD dnC dnLC

HsC : ∀ s → KC.Hs s ≡ hs (hs hz)
HsC zero = refl
HsC (suc s) = refl

diffC : DiffTkc dnC dnLC
diffC = 0 , λ ()
```

## §3 求值记录也不管 (对照, 接口自述的盲)

接口自己说了 "`DnEv` 的翻译取常数 `n0` 也是实例". 这里写出来, 作为 `DnEvTower` 不空的前提实例: 层 $L=2$, 世界 $(0,0)$.

```agda
evC : ∀ (S : KS) → DnEv S
evC S = record
  { Lw = hs (hs hz) ; lLw = tt ; o1 = hsuc hself ; Wv = azero , hz ; lWv = tt , tt ; ev2 = hself ; tr = λ _ → n0 }

evTC : DnEvTower
evTC s b lb = evC (Lev b)
```

## §4 结论 (按档)

- **[定理]** `sqC-fin`, `lgC`, `dsqC`: 对一切 `T` 有 `DnSq T` 的实例, 输出全是有限高度.
- **[定理]** **`cheapFaith`**, `top↦2`, `cut↦1`: 它满足 `FaithRd`.
- **[定理]** **`faith0C`**, **`faithTC`**, **`HsC`**, **`diffC`**: 塔上的下降 `dnC` 满足 `Faith0`, `FaithTower`, `DiffTkc`, 而每站的回灌输出都是 $2$.
- **[定理]** `evC`, `evTC`: `DnEv`, `DnEvTower` 有常数实例 (接口自述, 前提实例).
- **[判断]** 嫌疑 (ii) "D2 必然压回统一形状, 使忠实不可能": 后半不成立 (`cheapFaith`); 前半在接口的形状律之内只能说到 `sq-new` 本身 (输出只经 `cs` 看分支), 没有找到更强的编译陈述. 嫌疑 (iii) "第 2 站起为常数": 接口不排除 (`HsC` 是满足全部忠实律的常数实例), 也不强迫 (没有否定定理).
- 为什么构造一路需要这几条律: 接口 §5 原文 "`FaithTower dn dnL`: 第 $s+1$ 站的下降在该站的读回上忠实", "`DiffTkc`: 某站的回灌输出不等于截断版"; 构造一路的判决要靠它们说 "读回进了闭项" (`KcFold` 的第一个障碍).
