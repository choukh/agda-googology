# 结构关系, 第十七轮: 接口 (只放记录与类型)

> **接口定稿 2026-11-05 12:12.** 之后只增不改, 改动写在文末的变更记录. 构造一路 (前缀 `StrRel17`) 与否定一路 (前缀 `NegSR17`) 共用本文. 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 只有定义 (数据类型, 类型别名, 参数化模块里的类型), 没有定理.
>
> 作者选定 "B1: 带时间关系的语义". 内容 (对应 `StrRel16` 接手清单第 1 项与第 4 项的前半):
>
> 1. **时间关系** (§1). `Later Y₀ Y`: 同一世界里, $Y$ 在每个目标上的读数与第 $0$ 层累计都以 $Y_0$ 的为左前缀 (`StrRel16Lem.Lp`). 折叠里状态只经 `⊕` 向右延长时就是这样 (`HtFeedFold` 的 `_⊕⟨_⟩_`, `Rpt`, `Chn` 的状态). `Laterᵈ q Y₀ Y`: 跨世界 (路径 $q$) 只比差分量, 不比累计; `cv` 保持它而不保持 `Later` (`cv` 把累计置为 `n0`, 依 `NegSR16Kap.cvYN`).
> 2. **带条件的语义** `SemT` (§2): `StrRel16If.SemX²⁺` 加一个对再折叠状态对的条件 `Ok` (类型 `Cond`). `Ok` 恒真时就是 `SemX²⁺`.
> 3. **时间条件** `DomL` (§2): **右边的再折叠状态支配左边产生时的状态**, 即 `J²⁺ (左边产生时的状态) (右边再折叠时的状态)`. 这是 `StrRel16Val.valLK` 第 2 步实际用到的关系 (那里两者都是 $Y_1$ 的延长). 由字面的时间关系推出: `J²⁺ Y Y′` 且 `Later Y′ Y₂′` ⇒ `J²⁺ Y Y₂′` (`StrRel16Sem.jPfx⁺` 的形状).
> 4. **`rk⁺` 带时间条件的可靠性** `RkSoundT` (§3): `StrRel16If.RkSound` 的结论从 `SemX²⁺` 换成 `SemT … (DomL (左边产生时的状态))`.
> 5. **"ni 对 nκ" 的修补** (§4, 依 `NegSR16` §5 的建议): `Pos0` (第 $0$ 层的树字面地严格非零), `Lead1` (任意层的树字面地以 `n1` 开头), `ActNZ` (动作在第 $0$ 层目标上的输出字面地非零; `HtFeedClosed.Act` 是, `NegSR16Kap.Az` 不是), `HAWᴺ`/`SemXᴺ` (动作限制为 `ActNZ` 的语义), 修补后的规则的可靠性 `NKp` (只在右边 `nκ` 前有一段以 `n1` 开头的树时用) 与它在第 $0$ 层目标上的值的版本 `NKpV`.
>
> ## 律的定义域 (逐条检查, 依 `AGENTS.md` "律带公共上界")
>
> | 律 / 字段 | 被比较的一对 | 字面证据 | 只有值的部分 |
> |---|---|---|---|
> | `Later` | 同一世界的两个状态 | 左前缀 `Lp` (逐目标, 累计); 不比较两个下标 | 无 |
> | `Laterᵈ` | 世界 $W_0\lhd W$ 上的两个状态 | 路径 $q$ (字面); 目标经 `tg↑ q` 搬运 | 无 |
> | `SemT` | 同 `SemX²⁺` | 同 `StrRel16If` | 同 `StrRel16If` (`CP` 的 $W\le W'$) |
> | `DomL` | 左边产生时的世界 $W_0$ 对右边再折叠的世界 $W'$ | 同 `J²⁺`: 目标对是 `TX` ($t\sqsubseteq_\infty t'$, 世界 `CP`) | `CP` 的 $W_0\le W'$ (对齐的数据) |
> | `RkSoundT` | 同 `StrRel16If.RkSound` | 同 | 同 |
> | `Pos0`, `Lead1` | 一棵树 | 字面形状; 不比较 | 无 |
> | `ActNZ` | 一个动作在一切延长的世界上 | 路径 `p : W ⊲ W₁` | 无 |
> | `HAWᴺ`, `SemXᴺ` | 同 `HAW²⁺`, `SemX²⁺` | 同 | 同 |
> | `NKp` | 节点与 `nκ` 在**自身世界** (`self`) 上的分支 | 路径 `self`; 前一段的对 $x\le x'$ 同 `⨾⁺` | 无 |
> | `NKpV` | 两个运行世界 $W\le W'$ (`Top`) | `Top` | `CP` 的 $W\le W'$ |
>
> **检查的结论 (判断).** 新增的类型里没有裸下标上的律: 时间关系只看同一 (或字面路径相连的) 世界里状态读数的左前缀; `DomL` 是 `J²⁺` 的一个实例 (跨时间, 不跨新的下标); `NKp` 的分支只取 `self`.
>
> **范围 (判断, 写在这里, 不当作已解决).** (i) `Later` 只在同一世界里; 跨世界 (经 `cv`) 时累计被清零, `DomL` 的累计分量要另给 (见 `NegSR16` 的 `¬semNK`: 节点读差, `nκ` 读累计). (ii) `SemT` 不改目标对的范围: 右边在再折叠时**保留**的目标对上, 左边是 "上升输出的再运行", 右边是节点; `RelX⁺` 里以 (`nl …`, `ni …`) 为结论的规则只有字面的 `rk⁺`. 时间条件不触及这一点 (构造一路的 `StrRel17Obs` 把它写成编译的约化).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
module OCF.Align.StrRel17If (Λ : H) (lΛ : LgH Λ) where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤)
open import Data.Product using (Σ; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.HtFeedTree using (hz; StH; Vs; D; D₀; n0; n1; _⨾_; nl; ni; nκ; nw; NZ; AccY; ⊲ᴴ↑; sum)
open import OCF.Align.StrRel11Rk Λ lΛ using (_⊑∞_)
open import OCF.Align.StrRel12Al using (AP; CP)
open import OCF.Align.StrRel12Sem Λ lΛ using (Top)
open import OCF.Align.StrRel15If Λ lΛ using (TX)
open import OCF.Align.StrRel16Lem using (Lp)
open import OCF.Align.StrRel16If Λ lΛ using (module P; RelX⁺; OA²⁺; J²⁺; HAW²⁺; RkPre)

open P using (Tg; tg; wm; tm; lm; tg↑; τ₀; St; Df; yc; d; z; Run; Ig; LW; rkT; RKi; kk; rise; keep)
```

## 1 时间关系

```agda
Later : ∀ {W} → St W → St W → Set
Later {W} Y₀ Y = (∀ {t m} (T : Tg W t m) → Lp (yc (d Y₀) T) (yc (d Y) T)) × Lp (z Y₀) (z Y)

Laterᵈ : ∀ {W₀ W} → W₀ ⊲ W → St W₀ → St W → Set
Laterᵈ {W₀} {W} q Y₀ Y = ∀ {t m} (T : Tg W t m) → Lp (yc (d Y₀) (tg↑ q T)) (yc (d Y) T)
```

## 2 带条件的语义, 时间条件

`Cond`: 再折叠时两边状态对上的条件. `SemT … Ok x x′`: 同 `SemX²⁺`, 只对满足 `Ok` 的状态对要求结论.

```agda
Cond : Set₁
Cond = ∀ {W W′} → Lg W → Lg W′ → St W → St W′ → Set

SemT : ∀ L L′ {V V′} → Lg V → Lg V′ → Cond → D L V → D L′ V′ → Set
SemT L L′ {V} {V′} lV lV′ Ok x x′ =
  ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac′ : AccY L′) (ll : LW L W) (ll′ : LW L′ W′)
    (q : V ⊲ W) (q′ : V′ ⊲ W′) → CP lV lV′ q lW q′ lW′ →
  ∀ (A₀ : Ig L W) (A₀′ : Ig L′ W′) → HAW²⁺ L L′ lW lW′ A₀ A₀′ →
  ∀ w w′ → RelX⁺ L L′ lW lW′ w w′ → ∀ (Y : St W) (Y′ : St W′) → J²⁺ lW lW′ Y Y′ → Ok lW lW′ Y Y′ →
  OA²⁺ lW lW′ (Run ac x q lW ll A₀ w Y) (Run ac′ x′ q′ lW′ ll′ A₀′ w′ Y′)

-- 恒真的条件
Any : Cond
Any _ _ _ _ = ⊤

-- 右边再折叠的状态支配左边产生时的状态 Y₀
DomL : ∀ {W₀} → Lg W₀ → St W₀ → Cond
DomL lW₀ Y₀ lW lW′ Y Y′ = J²⁺ lW₀ lW′ Y₀ Y′
```

## 3 `rk⁺` 带时间条件的可靠性

结论层 $L$ (左边上升的目标层), $L'$ (右边保留的目标层). 前提同 `StrRel16If.RkSound`; 结论只对右边再折叠状态支配左边产生时状态 $Y$ 的再折叠要求.

```agda
RkSoundT : H → H → Set
RkSoundT L L′ =
  ∀ {ly ly′ W₀ W₀′ k k′ W W′ m m′} {lW₀ : Lg W₀} {lW₀′ : Lg W₀′} (r : StH W₀ k ly) (r′ : StH W₀′ k′ ly′)
    {u : ∀ {W₁} → W₀ ⊲ W₁ → Lg W₁ → Vs ly r W₁ → D ly W₁} {u′ : ∀ {W₁} → W₀′ ⊲ W₁ → Lg W₁ → Vs ly′ r′ W₁ → D ly′ W₁}
    (lW : Lg W) (lW′ : Lg W′) (ac : AccY ly) (ac₁ : AccY k) (ac′ : AccY ly′) (ac₁′ : AccY k′)
    (q₀ : W₀ ⊲ W) (q₀′ : W₀′ ⊲ W′) (ll : LW ly W) (ll′ : LW ly′ W′) (A₀ : Ig ly W) (A₀′ : Ig ly′ W′)
    (w : D ly W) (w′ : D ly′ W′) (Y : St W) (Y′ : St W′) (T : Tg W L m) (T′ : Tg W′ L′ m′) (R′ : StH m′ k′ L′) →
  RkPre {lW₀ = lW₀} {lW₀′} r r′ u u′ lW lW′ q₀ q₀′ A₀ A₀′ w w′ Y Y′ → TX lW lW′ T T′ →
  rkT (⊲ᴴ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T) ≡ rise → rkT (⊲ᴴ↑ (wm T′) (kk r′ q₀′ ll′)) (tm T′) (lm T′) ≡ keep R′ →
  SemT L L′ (lm T) (lm T′) (DomL lW Y)
    (RKi ac ac₁ r u q₀ lW ll A₀ w Y T rise) (RKi ac′ ac₁′ r′ u′ q₀′ lW′ ll′ A₀′ w′ Y′ T′ (keep R′))
```

## 4 "ni 对 nκ" 的修补

`Pos0 x`: 第 $0$ 层的树 $x$ 字面地严格非零 (沿 `⨾` 的一边, `nl` 的第 $0$ 项, `nw` 走到一个 `n1`). `Lead1 x`: 任意层的树 $x$ 沿左脊以 `n1` 开头. `ActNZ lW A₀`: 动作在一切延长的世界上, 第 $0$ 层目标上的输出字面地非零.

```agda
data Pos0 {W : A} : D₀ W → Set where
  p1 : Pos0 n1
  pL : ∀ {a b} → Pos0 a → Pos0 (a ⨾ b)
  pR : ∀ {a b} → Pos0 b → Pos0 (a ⨾ b)
  pE : ∀ {e : ℕ → D₀ W} → Pos0 (e 0) → Pos0 (nl e)
  pW : ∀ {W₀} {p : W₀ ⊲ W} {x : D₀ W₀} → Pos0 x → Pos0 (nw p x)

data Lead1 {L : H} {W : A} : D L W → Set where
  l1 : Lead1 n1
  lL : ∀ {a b} → Lead1 a → Lead1 (a ⨾ b)

ActNZ : ∀ {L W} → Lg W → Ig L W → Set
ActNZ {L} {W} lW A₀ = ∀ {W₁} (p : W ⊲ W₁) (lW₁ : Lg W₁) (w : D L W₁) (Y : St W₁) → Pos0 (yc (A₀ p lW₁ w Y) (τ₀ lW₁))

HAWᴺ : ∀ L L′ {W W′} → Lg W → Lg W′ → Ig L W → Ig L′ W′ → Set
HAWᴺ L L′ lW lW′ A₀ A₀′ = HAW²⁺ L L′ lW lW′ A₀ A₀′ × (ActNZ lW A₀ × ActNZ lW′ A₀′)

SemXᴺ : ∀ L L′ {V V′} → Lg V → Lg V′ → D L V → D L′ V′ → Set
SemXᴺ L L′ {V} {V′} lV lV′ x x′ =
  ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac′ : AccY L′) (ll : LW L W) (ll′ : LW L′ W′)
    (q : V ⊲ W) (q′ : V′ ⊲ W′) → CP lV lV′ q lW q′ lW′ →
  ∀ (A₀ : Ig L W) (A₀′ : Ig L′ W′) → HAWᴺ L L′ lW lW′ A₀ A₀′ →
  ∀ w w′ → RelX⁺ L L′ lW lW′ w w′ → ∀ (Y : St W) (Y′ : St W′) → J²⁺ lW lW′ Y Y′ →
  OA²⁺ lW lW′ (Run ac x q lW ll A₀ w Y) (Run ac′ x′ q′ lW′ ll′ A₀′ w′ Y′)
```

修补后的 "ni 对 nκ" (结论带开头一段): $x\le x'$, $x'$ 以 `n1` 开头, 节点 $\le$ `nκ` 在自身世界上的分支 ⇒ $x⨾\text{节点}\le x'⨾\mathrm{n\kappa}$. `NKp` 是它在 `SemXᴺ` 下的可靠性; `NKpV` 只在两边的第 $0$ 层目标上比值 (两个运行世界 `Top`, 底 $\beta\le\beta'$).

```agda
NKp : Set
NKp = ∀ {L L′ V V′ k} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {x′ : D L′ V′} {r : StH V k L}
        {u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′} {zz′ : NZ L′} {v′ : ∀ {c} → V′ ⊲ c → Lg c → D L′ c} →
      Lead1 x′ → RelX⁺ L L′ lV lV′ x x′ → SemXᴺ L L′ lV lV′ x x′ →
      RelX⁺ L L′ lV lV′ (ni r u) (v′ C.self lV′) → SemXᴺ L L′ lV lV′ (ni r u) (v′ C.self lV′) →
      SemXᴺ L L′ lV lV′ (x ⨾ ni r u) (x′ ⨾ nκ zz′ v′)

NKpV : Set
NKpV = ∀ {L L′ V V′ k} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {x′ : D L′ V′} {r : StH V k L}
         {u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′} {zz′ : NZ L′} {v′ : ∀ {c} → V′ ⊲ c → Lg c → D L′ c} →
       Lead1 x′ → RelX⁺ L L′ lV lV′ x x′ → SemXᴺ L L′ lV lV′ x x′ →
       RelX⁺ L L′ lV lV′ (ni r u) (v′ C.self lV′) → SemXᴺ L L′ lV lV′ (ni r u) (v′ C.self lV′) →
       ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac′ : AccY L′) (ll : LW L W) (ll′ : LW L′ W′)
         (q : V ⊲ W) (q′ : V′ ⊲ W′) → CP lV lV′ q lW q′ lW′ →
       ∀ (A₀ : Ig L W) (A₀′ : Ig L′ W′) → HAWᴺ L L′ lW lW′ A₀ A₀′ →
       ∀ w w′ → RelX⁺ L L′ lW lW′ w w′ → ∀ (Y : St W) (Y′ : St W′) → J²⁺ lW lW′ Y Y′ → ∀ β β′ → β ≤ β′ →
       sum β (yc (Run ac (x ⨾ ni r u) q lW ll A₀ w Y) (τ₀ lW)) ≤ sum β′ (yc (Run ac′ (x′ ⨾ nκ zz′ v′) q′ lW′ ll′ A₀′ w′ Y′) (τ₀ lW′))
```

## 变更记录

- 2026-11-05 12:12: 定稿 (首次编译通过, 退出码 0).
- 2026-11-05 12:43: 补注 (文字, 不改定义). (i) 文件头第 3 条 "由字面的时间关系推出" 指同一世界的 `Later`: `StrRel17Time.valLater` 用 `jPfx⁺` 这样推出 `DomL`; 经 `cv` 的跨世界情形不成立 (否定一路 `NegSR17Time.¬domFromLaterᵈ` 的文件头所述, 构造一路未复核). (ii) 文件头 "范围 (ii)" 的约化见 `StrRel17Obs.obsT`. §1–§4 未改.
