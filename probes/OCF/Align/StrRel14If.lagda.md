# 结构关系, 第十四轮: 接口 (只放记录与类型)

> **接口定稿 2026-11-05 10:18.** 之后只增不改, 改动写在文末的变更记录. 构造一路 (前缀 `StrRel14`) 与否定一路 (前缀 `StrRel14Neg`) 共用本文. 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 只有定义 (记录, 数据类型, 类型别名), 没有定理.
>
> 内容 (对应 `StrRel13` 接手清单第 1 到 3 项):
>
> 1. **带状态不变量的两世界语义** (§2): 不变量是记录 `Inv` (状态对上的谓词 `J`, 加三条封闭律: 推出 `R∀c`, 经 `cv` 封闭, 经 `⊕` 封闭). `SemJ`: `StrRel12Sem.SemW` 把 "状态按 `R∀c` 相关" 换成 "状态满足 `J`". `MonoPort7` 的单世界不变量 (`Good`/`SRel`) 与 `StrRel12` 的 `CP`/`R∀c` 在这里合成一个记录: `J` 自己带 `R∀c` (`toR`), 其余字段由使用者给.
> 2. **异质关系 `RelX L L′`** (§3): 左层 $L$, 右层 $L'$, 对左层递归 (与 `StrRel12Rel.Rel` 同形). 节点规则 `niˣ` 允许两边坐标层不同 ($k$ 对 $k'$), 但要**字面证据** $k\sqsubseteq_\infty k'$ (`StrRel11Rk._⊑∞_`); `κˣ` 的分支对是 `CPᴸ` (`CP` 加字面的 $c\lhd c'$).
> 3. **跨坐标层节点规则的类型** (§4): 按 `StrRel13Rk.rk-mono` 的三种情形 (升升, 留留, 左留右升) 各写一个义务的类型 (`OblRR`, `OblKK`, `OblKR`), 并写出它们合起来给出的节点规则可靠性的类型 (`NodeSound`).
> 4. **不经 `CP` 的顶层比较的类型** (§5): `TopV`, 只比第 $0$ 层的和 (值), 两边的树世界之间要字面的 $V\lhd V'$, 运行世界相同.

## 律的定义域 (逐条检查, 依 `AGENTS.md` "律带公共上界")

律里出现的每一对下标或路径, 都写出它带的字面公共上界的证据. "值" 一列指只有值上的 $\le$ 而没有字面证据的地方.

| 律 / 字段 | 被比较的一对 | 字面证据 | 只有值的部分 |
|---|---|---|---|
| `CPᴸ` (κ 分支对) | 分支世界 $c$, $c'$ | $c\lhd c'$ ($c'$ 是两者的字面公共上界) | `CP` 内的 $W\le W'$ (顶端世界的值, 由 `Al` 的 `aP` 用), `Al` 内各对应位置的 $c_i\le c_i'$ |
| `niˣ` | 坐标层 $k$, $k'$ | $k\sqsubseteq_\infty k'$ (忘掉世界的第一位置) | 无 |
| `niˣ` 的分支对 | 分支世界 | `CP` (同 `StrRel12`) | 同上 |
| `nwˣ` | 两段路径 $V_0\lhd V$, $V_0'\lhd V'$ | `AP` (逐步对齐的数据) | `Al` 的 `aP` 的 $c\le c'$ |
| `OAcJ`/`OAcX` 的目标对 | 目标层 $t$ (两边同一个), 目标世界 $m$, $m'$ | 目标层相同 (字面); 世界经 `TC` = `CP` | 同上 |
| `R∀c` (经 `toR`) | 同上 | 同上 | 同上 |
| `Inv.cvJ` | 换世界的路径对 | `AP` | 同上 |
| `Inv.⊕J` | 状态与输出的世界 | 两边各自的世界, 目标对同上 | 同上 |
| `OblRR`/`OblKK`/`OblKR` | 坐标层 $k\sqsubseteq_\infty k'$, 同一目标层 $t$ | `RkX` 的证据由 $k\sqsubseteq_\infty k'$ 与两个 `cmpH` 给出 (`rk-mono`) | 无 |
| `TopV` | 树世界 $V$, $V'$; 运行世界 $W$ | $V\lhd V'$; 运行世界相同 | 底 $\beta\le\beta'$ |

**已知的缺口 (检查的结论, 判断; 编译证据在 `StrRel14Rk`).**

- `StrRel12Rel.κᴸ` 与 `StrRel12Sem.HAW` 的分支对/目标对是 `CP`, 其中分支世界只有 `Al` 给出的值 $c\le c'$, **没有字面公共上界**. 由它们产生的节点对 (`Ωd (hΩ g)` 的分支, 坐标层 $g\,c$ 对 $g\,c'$) 没有 $g\,c\sqsubseteq_\infty g\,c'$, `rk-mono` 用不上; `StrRel14Rk.cpBad` 给出一个 `CP` 分支对, 其上两节点在同一目标层上是 "左升右留" (`rk-mono` 排除的那一种). 所以本接口的 `κˣ` 只取 `CPᴸ`.
- `CP` 本身的 $W\le W'$ 是值. 它只被 `Al` 的 `aP` 与 `genAl` 用 (产生格世界的对齐), 不用来比较两个高度; 本接口保留它, 不另加证据 (判断: 它不是 "比较两个下标" 的律, 是对齐的数据).
- `TopV` 不经 `CP`: `StrRel13Om.¬cpTop` 说 `MonoStep Ωᴴ` 的顶层路径对不是 `CP`; 本接口改成两树世界之间的字面 $V\lhd V'$, 结论只在第 $0$ 层比值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
module OCF.Align.StrRel14If (Λ : H) (lΛ : LgH Λ) where

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.HtFeedTree using (hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; StH; ss; sl; sL; Vs; D; outS;
  n0; n1; _⨾_; nl; ni; nκ; nw; NZ; AccY; sum)
open import OCF.Align.HtFeedClosed using (module At)
open import OCF.Align.StrRel11Rk Λ lΛ using (_⊑∞_)
open import OCF.Align.StrRel13Rk Λ lΛ using (RkX)
open import OCF.Align.StrRel12Al using (AP; CP)
open import OCF.Align.StrRel12Rel using (Rel)
open import OCF.Align.StrRel12Sem Λ lΛ using (Top; TC; OAc; R∀c; HAW)

module P = At Λ lΛ
open P using (Tg; tg; wm; tm; lm; St; Df; yc; d; z; cv; _⊕⟨_⟩_; Run; Ig; LW; Rk; rkT; RKi; kk)
```

## 1 字面的分支对

```agda
CPᴸ : ∀ {V V′ c c′} → Lg V → Lg V′ → V ⊲ c → Lg c → V′ ⊲ c′ → Lg c′ → Set
CPᴸ {c = c} {c′ = c′} lV lV′ p lc p′ lc′ = CP lV lV′ p lc p′ lc′ × (c ⊲ c′)
```

## 2 带状态不变量的两世界语义

`Inv`: 状态对上的谓词 `J` 与三条封闭律. `toR` 让 `J` 至少有 `StrRel12` 的状态关系; `cvJ` 与 `⊕J` 是折叠里状态的两种变化 (`Kp`, `Kb`, `BNi`, `Chn`, `κc` 的状态都由它们组成, 判断, 依据 `HtFeedFold` 的字面).

```agda
record Inv : Set₁ where
  field
    J   : ∀ {W W′} → Lg W → Lg W′ → St W → St W′ → Set
    toR : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} {Y : St W} {Y′ : St W′} → J lW lW′ Y Y′ → R∀c lW lW′ Y Y′
    cvJ : ∀ {W W′ W₂ W₂′} {lW : Lg W} {lW′ : Lg W′} {q : W ⊲ W₂} {lW₂ : Lg W₂} {q′ : W′ ⊲ W₂′} {lW₂′ : Lg W₂′} →
          AP lW lW′ q lW₂ q′ lW₂′ → ∀ (Y : St W) (Y′ : St W′) → J lW lW′ Y Y′ → J lW₂ lW₂′ (cv q Y) (cv q′ Y′)
    ⊕J  : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} → Top lW lW′ → ∀ (Y : St W) (Y′ : St W′) (Δ : Df W) (Δ′ : Df W′) →
          J lW lW′ Y Y′ → OAc lW lW′ Δ Δ′ → J lW lW′ (Y ⊕⟨ lW ⟩ Δ) (Y′ ⊕⟨ lW′ ⟩ Δ′)

module WithInv (I : Inv) where
  open Inv I

  HAWJ : ∀ L {W W′} → Lg W → Lg W′ → Ig L W → Ig L W′ → Set
  HAWJ L {W} {W′} lW lW′ A₀ A₀′ =
    ∀ {W₁ W₁′} (p : W ⊲ W₁) (p′ : W′ ⊲ W₁′) (lW₁ : Lg W₁) (lW₁′ : Lg W₁′) → CP lW lW′ p lW₁ p′ lW₁′ →
    ∀ w w′ → Rel L lW₁ lW₁′ w w′ → ∀ (Y : St W₁) (Y′ : St W₁′) → J lW₁ lW₁′ Y Y′ →
    OAc lW₁ lW₁′ (A₀ p lW₁ w Y) (A₀′ p′ lW₁′ w′ Y′)

  SemJ : ∀ L {V V′} → Lg V → Lg V′ → D L V → D L V′ → Set
  SemJ L {V} {V′} lV lV′ x x′ =
    ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (ac ac′ : AccY L) (ll : LW L W) (ll′ : LW L W′)
      (q : V ⊲ W) (q′ : V′ ⊲ W′) → CP lV lV′ q lW q′ lW′ →
    ∀ (A₀ : Ig L W) (A₀′ : Ig L W′) → HAWJ L lW lW′ A₀ A₀′ →
    ∀ w w′ → Rel L lW lW′ w w′ → ∀ (Y : St W) (Y′ : St W′) → J lW lW′ Y Y′ →
    OAc lW lW′ (Run ac x q lW ll A₀ w Y) (Run ac′ x′ q′ lW′ ll′ A₀′ w′ Y′)
```

## 3 异质关系 `RelX L L′`

与 `StrRel12Rel.LeF` 同形, 两边的层分开. 坐标关系沿左边节点的位置往下取 (`RelSX`/`RelAtX` 对左层递归), 右边的坐标层是任意的 $k'$.

```agda
LoX : H → H → Set₁
LoX L L′ = ∀ {V V′ k k′ c c′} (r : StH V k L) (r′ : StH V′ k′ L′) → Lg c → Lg c′ → Vs L r c → Vs L′ r′ c′ → Set

data LeX (L L′ : H) (Lo : LoX L L′) : ∀ {V V′} → Lg V → Lg V′ → D L V → D L′ V′ → Set where
  n0ˣ : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x′ : D L′ V′} → LeX L L′ Lo lV lV′ n0 x′
  n1ˣ : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} → LeX L L′ Lo lV lV′ n1 n1
  ⨾ˣ  : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x y : D L V} {x′ y′ : D L′ V′} →
        LeX L L′ Lo lV lV′ x x′ → LeX L L′ Lo lV lV′ y y′ → LeX L L′ Lo lV lV′ (x ⨾ y) (x′ ⨾ y′)
  nlˣ : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {d₁ : ℕ → D L V} {d₁′ : ℕ → D L′ V′} →
        (∀ n → LeX L L′ Lo lV lV′ (d₁ n) (d₁′ n)) → LeX L L′ Lo lV lV′ (nl d₁) (nl d₁′)
  prˣ : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {x′ y′ : D L′ V′} →
        LeX L L′ Lo lV lV′ x x′ → LeX L L′ Lo lV lV′ x (x′ ⨾ y′)
  nwˣ : ∀ {V₀ V₀′ V V′} {lV₀ : Lg V₀} {lV₀′ : Lg V₀′} {lV : Lg V} {lV′ : Lg V′} {p : V₀ ⊲ V} {p′ : V₀′ ⊲ V′}
          {x : D L V₀} {x′ : D L′ V₀′} →
        AP lV₀ lV₀′ p lV p′ lV′ → LeX L L′ Lo lV₀ lV₀′ x x′ → LeX L L′ Lo lV lV′ (nw p x) (nw p′ x′)
  niˣ : ∀ {V V′ k k′} {lV : Lg V} {lV′ : Lg V′} {r : StH V k L} {r′ : StH V′ k′ L′}
          {u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′} {u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ r′ W′ → D L′ W′} →
        k ⊑∞ k′ →
        (∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CP lV lV′ p lc p′ lc′ →
           ∀ y y′ → Lo r r′ lc lc′ y y′ → LeX L L′ Lo lc lc′ (u p lc y) (u′ p′ lc′ y′)) →
        LeX L L′ Lo lV lV′ (ni r u) (ni r′ u′)
  κˣ  : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {zz : NZ L} {zz′ : NZ L′}
          {u : ∀ {c} → V ⊲ c → Lg c → D L c} {u′ : ∀ {c} → V′ ⊲ c → Lg c → D L′ c} →
        (∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CPᴸ lV lV′ p lc p′ lc′ →
           LeX L L′ Lo lc lc′ (u p lc) (u′ p′ lc′)) →
        LeX L L′ Lo lV lV′ (nκ zz u) (nκ zz′ u′)

RelX   : ∀ L L′ {V V′} → Lg V → Lg V′ → D L V → D L′ V′ → Set
BelowX : ∀ L L′ → LoX L L′
RelSX  : ∀ L {V k} → StH V k L → ∀ k′ {c c′} → Lg c → Lg c′ → D k c → D k′ c′ → Set
RelAtX : ∀ b {V k} → k ⊲[ V ] b → ∀ k′ {c c′} → Lg c → Lg c′ → D k c → D k′ c′ → Set

RelX L L′ = LeX L L′ (BelowX L L′)
BelowX L L′ {k′ = k′} r r′ lc lc′ y y′ = RelSX L r k′ lc lc′ (outS r y) (outS r′ y′)
RelSX (hs b) (ss P) = RelAtX b P
RelSX (hl f) (sl n P) = RelAtX (f n) P
RelSX (hΩ g) (sL e P) = RelAtX (g _) P
RelAtX b hself k′ = RelX b k′
RelAtX (hs b) (hsuc P) = RelAtX b P
RelAtX (hl f) (hlim n P) = RelAtX (f n) P
RelAtX (hΩ g) (hLim e P) = RelAtX (g _) P
```

异质关系的语义: 输出在**同一目标层**上比 (两边的输出都是目标层 $t$ 的树), 用 `RelX t t`.

```agda
OAcX : ∀ {W W′} → Lg W → Lg W′ → Df W → Df W′ → Set
OAcX {W} {W′} lW lW′ Δ Δ′ = ∀ {t m m′} (T : Tg W t m) (T′ : Tg W′ t m′) → TC lW lW′ T T′ → RelX t t (lm T) (lm T′) (yc Δ T) (yc Δ′ T′)

R∀X : ∀ {W W′} → Lg W → Lg W′ → St W → St W′ → Set
R∀X lW lW′ Y Y′ = OAcX lW lW′ (d Y) (d Y′) × RelX hz hz lW lW′ (z Y) (z Y′)

HAWX : ∀ L L′ {W W′} → Lg W → Lg W′ → Ig L W → Ig L′ W′ → Set
HAWX L L′ {W} {W′} lW lW′ A₀ A₀′ =
  ∀ {W₁ W₁′} (p : W ⊲ W₁) (p′ : W′ ⊲ W₁′) (lW₁ : Lg W₁) (lW₁′ : Lg W₁′) → CP lW lW′ p lW₁ p′ lW₁′ →
  ∀ w w′ → RelX L L′ lW₁ lW₁′ w w′ → ∀ (Y : St W₁) (Y′ : St W₁′) → R∀X lW₁ lW₁′ Y Y′ →
  OAcX lW₁ lW₁′ (A₀ p lW₁ w Y) (A₀′ p′ lW₁′ w′ Y′)

SemX : ∀ L L′ {V V′} → Lg V → Lg V′ → D L V → D L′ V′ → Set
SemX L L′ {V} {V′} lV lV′ x x′ =
  ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac′ : AccY L′) (ll : LW L W) (ll′ : LW L′ W′)
    (q : V ⊲ W) (q′ : V′ ⊲ W′) → CP lV lV′ q lW q′ lW′ →
  ∀ (A₀ : Ig L W) (A₀′ : Ig L′ W′) → HAWX L L′ lW lW′ A₀ A₀′ →
  ∀ w w′ → RelX L L′ lW lW′ w w′ → ∀ (Y : St W) (Y′ : St W′) → R∀X lW lW′ Y Y′ →
  OAcX lW lW′ (Run ac x q lW ll A₀ w Y) (Run ac′ x′ q′ lW′ ll′ A₀′ w′ Y′)
```

## 4 跨坐标层节点规则的类型

一个节点对 `ni r u` (左, 坐标层 $k$, 层 $L$) 与 `ni r′ u′` (右, 坐标层 $k'$, 层 $L'$), $k\sqsubseteq_\infty k'$. 在一对目标 $T, T'$ (同一目标层 $t$) 上, 两边的读数是 `RKi … (rkT …)`. `RkX` (`StrRel13Rk`) 把种类对分成三种; 每种一个义务: 给定该种的两个 `Rk` 值, 两边的 `RKi` 输出按 `RelX t t` 相关.

```agda
module NodeObl {L L′ V V′ k k′} {lV : Lg V} {lV′ : Lg V′} (r : StH V k L) (r′ : StH V′ k′ L′)
               (u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′) (u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ r′ W′ → D L′ W′)
               {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac₁ : AccY k) (ac′ : AccY L′) (ac₁′ : AccY k′)
               (q₀ : V ⊲ W) (q₀′ : V′ ⊲ W′) (ll : LW L W) (ll′ : LW L′ W′) (A₀ : Ig L W) (A₀′ : Ig L′ W′)
               (w : D L W) (w′ : D L′ W′) (Y : St W) (Y′ : St W′) where
  Out : ∀ {t m m′} (T : Tg W t m) (T′ : Tg W′ t m′) → Rk k t m → Rk k′ t m′ → Set
  Out T T′ rk rk′ = RelX _ _ (lm T) (lm T′) (RKi ac ac₁ r u q₀ lW ll A₀ w Y T rk) (RKi ac′ ac₁′ r′ u′ q₀′ lW′ ll′ A₀′ w′ Y′ T′ rk′)

  -- 三种义务, 对一切 CP 目标对
  OblRR OblKK OblKR : Set
  OblRR = ∀ {t m m′} (T : Tg W t m) (T′ : Tg W′ t m′) → TC lW lW′ T T′ → Out T T′ P.rise P.rise
  OblKK = ∀ {t m m′} (T : Tg W t m) (T′ : Tg W′ t m′) → TC lW lW′ T T′ → ∀ R R′ → Out T T′ (P.keep R) (P.keep R′)
  OblKR = ∀ {t m m′} (T : Tg W t m) (T′ : Tg W′ t m′) → TC lW lW′ T T′ → ∀ R → Out T T′ (P.keep R) P.rise

  -- 三种合起来: 一切 RkX 对
  OblAll : Set
  OblAll = ∀ {t m m′} (T : Tg W t m) (T′ : Tg W′ t m′) → TC lW lW′ T T′ → ∀ {rk rk′} → RkX rk rk′ → Out T T′ rk rk′

-- 节点规则的可靠性 (语义的类型): 分支与坐标的关系 ⇒ 节点对的语义
NodeSound : Set
NodeSound = ∀ {L L′ V V′ k k′} {lV : Lg V} {lV′ : Lg V′} (r : StH V k L) (r′ : StH V′ k′ L′)
              {u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′} {u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ r′ W′ → D L′ W′} →
            k ⊑∞ k′ →
            (∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CP lV lV′ p lc p′ lc′ →
               ∀ y y′ → BelowX L L′ r r′ lc lc′ y y′ → RelX L L′ lc lc′ (u p lc y) (u′ p′ lc′ y′)) →
            SemX L L′ lV lV′ (ni r u) (ni r′ u′)
```

## 5 不经 `CP` 的顶层比较

顶层 (闭项的比较, 如 `MonoStep Ωᴴ`) 两边的运行世界相同 ($W$), 树世界 $V\lhd V'$ 字面, 路径 $q_0:V\lhd W$, $q_0':V'\lhd W$ 不要求对齐. 结论只在第 $0$ 层比和的值 (`TopOut`). 前提 (动作, 上下文, 状态) 随实例不同, 作参数 `Pre`.

```agda
TopOut : ∀ {W} → Lg W → Df W → Df W → Set
TopOut lW Δ Δ′ = ∀ β β′ → β ≤ β′ → sum β (yc Δ (P.τ₀ lW)) ≤ sum β′ (yc Δ′ (P.τ₀ lW))

PreT : H → Set₁
PreT L = ∀ {W} → Lg W → Ig L W → Ig L W → D L W → D L W → St W → St W → Set

TopV : ∀ L {V V′} → V ⊲ V′ → PreT L → D L V → D L V′ → Set
TopV L {V} {V′} vv Pre x x′ =
  ∀ {W} (lW : Lg W) (ac ac′ : AccY L) (ll : LW L W) (q₀ : V ⊲ W) (q₀′ : V′ ⊲ W) (A₀ A₀′ : Ig L W) (w w′ : D L W) (Y Y′ : St W) →
  Pre lW A₀ A₀′ w w′ Y Y′ → TopOut lW (Run ac x q₀ lW ll A₀ w Y) (Run ac′ x′ q₀′ lW ll A₀′ w′ Y′)
```

## 6 (增补) 按实际种类的义务

§4 的 `OblRR`/`OblKK`/`OblKR` 对**任意**一对 `Rk` 值量化, 不看 `rkT` 实际给出什么; 于是例如 `OblKR` 在 $k=k'$ 时也要求 "节点对极限", 而那时 `rkT` 根本不会给出这一对 (`rk-agree`). 这里补上只在 `rkT` 实际给出该种时才要求的版本 (带等式). §4 不改.

```agda
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.HtFeedTree using (⊲ᴴ↑)

module NodeObl⁼ {L L′ V V′ k k′} {lV : Lg V} {lV′ : Lg V′} (r : StH V k L) (r′ : StH V′ k′ L′)
                (u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′) (u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ r′ W′ → D L′ W′)
                {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac₁ : AccY k) (ac′ : AccY L′) (ac₁′ : AccY k′)
                (q₀ : V ⊲ W) (q₀′ : V′ ⊲ W′) (ll : LW L W) (ll′ : LW L′ W′) (A₀ : Ig L W) (A₀′ : Ig L′ W′)
                (w : D L W) (w′ : D L′ W′) (Y : St W) (Y′ : St W′) where
  open NodeObl {lV = lV} {lV′ = lV′} r r′ u u′ lW lW′ ac ac₁ ac′ ac₁′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′ public using (Out)

  rkL : ∀ {t m} → Tg W t m → Rk k t m
  rkL T = rkT (⊲ᴴ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T)
  rkR : ∀ {t m′} → Tg W′ t m′ → Rk k′ t m′
  rkR T′ = rkT (⊲ᴴ↑ (wm T′) (kk r′ q₀′ ll′)) (tm T′) (lm T′)

  OblRR⁼ OblKK⁼ OblKR⁼ : Set
  OblRR⁼ = ∀ {t m m′} (T : Tg W t m) (T′ : Tg W′ t m′) → TC lW lW′ T T′ → rkL T ≡ P.rise → rkR T′ ≡ P.rise → Out T T′ P.rise P.rise
  OblKK⁼ = ∀ {t m m′} (T : Tg W t m) (T′ : Tg W′ t m′) → TC lW lW′ T T′ → ∀ R R′ → rkL T ≡ P.keep R → rkR T′ ≡ P.keep R′ →
           Out T T′ (P.keep R) (P.keep R′)
  OblKR⁼ = ∀ {t m m′} (T : Tg W t m) (T′ : Tg W′ t m′) → TC lW lW′ T T′ → ∀ R → rkL T ≡ P.keep R → rkR T′ ≡ P.rise →
           Out T T′ (P.keep R) P.rise
```

## 变更记录

- 2026-11-05 10:18: 定稿 (首次编译通过, 退出码 0).
- 2026-11-05 10:40: 增补 §6 `NodeObl⁼` (按 `rkT` 实际种类的义务, 带等式). 理由: §4 的义务对任意 `Rk` 对量化, `OblKR` 在 `rkT` 不给出 "左留右升" 时也非空, 前提过强. §1 到 §5 未改.
