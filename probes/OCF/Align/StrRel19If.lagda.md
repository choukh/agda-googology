# 结构关系, 第十九轮: 接口 (只放记录与类型)

> **接口定稿 2026-11-05 16:01.** 之后只增不改, 改动写在文末的变更记录. 构造一路 (前缀 `StrRel19`) 与否定一路 (前缀 `NegSR19`) 共用本文. 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 只有定义 (数据类型, 类型别名), 没有定理.
>
> 作者选定 "值的一侧 + 第 4 层 B1 都派"; 本文是 B1 的下一步 (`StrRel18` 接手清单第 1–3 项). 内容:
>
> 1. **折叠实际用到的动作的语法 `ActS`** (§1). 一元谓词, 由三个构造子生成: `sAct` (闭项的动作 `Act`), `sIg↾` (`Ig↾ p A₀`, 搬到更大的世界), `sAi` (节点的分支动作 `Ai … A₀ w`). 折叠 (`HtFeedFold`) 里传给 `Run` 的动作只有这三种形状 (`Run` 原样传, `Ai`, `BNi`, `Chn`, `RKi` 用 `Ai`, `Kp`, `Kb`, `κΔ` 用 `Ig↾`). `ActS` 不提关系, 所以作规则前提时是正的.
> 2. **扩充的关系 `RelX⁺⁺`** (§2) = `StrRel16If.RelX⁺` 的十一条规则 (改名加 `⁺⁺`, 内容不变, `rk⁺⁺` 的前提仍是旧关系的 `RkPre`) 加一条:
>    - **`up` ("同一节点, 低目标上升 ⇒ 高目标保留"):** 同一节点同一组产生参数 (产生时动作 $A_0$ 满足 `ActS`), $x\le$ 它在低目标 $T$ 上的上升输出 ⇒ $x\le$ 它在高目标 $T'$ 上的保留输出.
>
>    为了让 `up` 的前提与结论的**右层不同** ($T$ 的层与 $T'$ 的层), 右层从参数改为**指标**; 左层仍是参数 (坐标关系 `Lo` 对左层结构递归先定义, 在 `ni⁺⁺` 的分支前提里负出现, 必须是参数). `up` 的前提是同一族 (同一左层, 另一右层) 的正出现, 加 `ActS` (不提关系). 所以 (判断, 依据 Agda 的正性检查规则; 由本文编译通过证实) 不撞严格正性.
> 3. **以 `RelX⁺⁺` 为输出关系与前提关系的语义** (§3–§4): `OA⁺⁺`, `R⁺⁺`, `J⁺⁺`, `HAW⁺⁺`; 再折叠的动作限为 `ActS` 的 `HAWS`; 带条件的语义 `SemS` (同 `StrRel17If.SemT` 的形状).
> 4. **kZ 下的时间条件 `DomZ`** (§4): `StrRel17If.DomL` 把左边产生时的状态 $Y_0$ 与右边再折叠的状态 $Y'$ 整个比 (`J²⁺`); `DomZ` 只把**累计分量**改成 "$Y_0$ 的累计 $\le$ $Y'$ 在第 $0$ 层目标上的读数" (读数经 `cv` 保留, 累计被 `cv` 清掉; 来自 `StrRel18` 的 `kZ` 变体). 差分量与 `NE` 同 `DomL`.
> 5. **可靠性** (§5): `UpSoundS Ok` (`up` 在 `SemS … Ok` 下可靠, 产生时动作 `ActS`), `UpSoundZ` (`Ok` 取这个节点产生状态的 `DomZ`), `RkSoundZ` (`rk⁺⁺` 的实例, 产生时两边动作 `ActS`, 结论 `SemS … (DomZ …)`), `OblRRZ` (同一对节点在两个都上升的目标上的输出: 升升义务), `Emb⁺⁺` (旧关系 `RelX⁺` 嵌进 `RelX⁺⁺`, 类型).
>
> ## 律的定义域 (逐条检查, 依 `AGENTS.md` "律带公共上界")
>
> | 律 / 规则 / 字段 | 被比较的一对 | 字面证据 | 只有值的部分 |
> |---|---|---|---|
> | `ActS` | 一个动作 (一元) | 构造子的字面 (`Act`, `Ig↾ p`, `Ai …`), 路径 $p$ 字面 | 无 |
> | 旧的十一条 (`n0⁺⁺` … `nκ⁺⁺`) | 同 `StrRel16If` | 同 `StrRel16If` | 同 `StrRel16If` (`CP` 的 $W\le W'$) |
> | `up` | 同一节点在同一世界 $W$ 上的两个目标 $T$, $T'$ | 两个目标的种类由 `rkT` 字面给出 (`≡ rise`, `≡ keep R′`); 左边 $x$ 与两个输出的比较来自前提的推导; 不比较两个目标或两个下标 | 无 |
> | `OA⁺⁺`, `R⁺⁺`, `J⁺⁺`, `HAW⁺⁺` | 同 `OA²⁺`, `R²⁺`, `J²⁺`, `HAW²⁺` | 目标对 `TX` ($t\sqsubseteq_\infty t'$, 世界 `CP`) | `CP` 的 $W\le W'$ |
> | `HAWS` | 同 `HAW⁺⁺`, 加两个一元的 `ActS` | 同 | 同 |
> | `SemS` | 同 `StrRel17If.SemT` | 同 | 同 |
> | `DomZ` | 左边产生时的世界 $W_0$ 对右边再折叠的世界 $W'$ | 差分量同 `J²⁺` (`TX` 对); 累计对读数: 两个第 $0$ 层的树 (`RelX⁺⁺ hz hz`, 第 $0$ 层没有节点, 没有 `nκ`) | `CP` 的 $W_0\le W'$ (差分量) |
> | `UpSoundS`, `UpSoundZ` | 同 `up`, 加 `SemS` | 同 | 同 |
> | `RkSoundZ` | 同 `StrRel16If.RkSound` | 同 | 同 |
> | `OblRRZ` | 一对节点在两个都上升的目标 $T$, $T'$ 上 | `TX` 对; 种类由 `rkT` 字面给出 | `CP` |
>
> **检查的结论 (判断).** 新增的规则 `up` 不比较两个下标: 它只看同一节点的同一组参数在两个目标上的输出, 种类由 `rkT` 的字面给出 (同 `StrRel18If.UpClosed`). `ActS` 是一元的字面语法. `DomZ` 是 `J⁺⁺` 的分量换一个第 $0$ 层的读数. 没有裸下标上的律.
>
> **范围 (判断, 写在这里, 不当作已解决).** (i) `ActS` 是一元的: 两个动作之间的关系仍由 `HAW⁺⁺` (负出现) 给, 只在语义里出现, 不在规则前提里. (ii) `rk⁺⁺` 原样保留旧关系的前提; 本文不给 `rk⁺⁺` 加 `ActS`, 只在它的可靠性 `RkSoundZ` 里加. (iii) `up` 的产生时动作要 `ActS`, 是为了排除 `NegSR18Up.¬UpSoundR` 的反例 (产生时动作 `Az` 读累计); `Az` 不属于 `ActS` 由构造一路的文件编译.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
module OCF.Align.StrRel19If (Λ : H) (lΛ : LgH Λ) where

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; StH; ss; sl; sL; Vs; D; D₀; outS;
  n0; n1; _⨾_; nl; ni; nκ; nw; NZ; AccY; ⊲ᴴ↑)
open import OCF.Align.StrRel11Rk Λ lΛ using (_⊑∞_)
open import OCF.Align.StrRel12Al using (AP; CP)
open import OCF.Align.StrRel14If Λ lΛ using (LoX; CPᴸ)
open import OCF.Align.StrRel14J Λ lΛ using (NE)
open import OCF.Align.StrRel15If Λ lΛ using (TX)
open import OCF.Align.StrRel16If Λ lΛ using (module P; In; RkPre; RelX⁺)
open import OCF.Align.StrRel17If Λ lΛ using (Cond)

open P using (Tg; tg; wm; tm; lm; τ₀; St; Df; yc; d; z; Run; Act; Ig; Ig↾; LW; Ai; rkT; RKi; kk; rise; keep)
```

## 1 折叠实际用到的动作的语法

```agda
data ActS : ∀ {L W} → Ig L W → Set where
  sAct : ∀ {L W} → ActS {L} {W} Act
  sIg↾ : ∀ {L W W′} (p : W ⊲ W′) {A₀ : Ig L W} → ActS A₀ → ActS (Ig↾ p A₀)
  sAi  : ∀ {ly W₀ W k} (ac : AccY ly) (ac₁ : AccY k) (r : StH W₀ k ly) (u : ∀ {W′} → W₀ ⊲ W′ → Lg W′ → Vs ly r W′ → D ly W′)
           (q₀ : W₀ ⊲ W) (hk : LW k W) (ll : LW ly W) {A₀ : Ig ly W} (w : D ly W) →
         ActS A₀ → ActS (Ai ac ac₁ r u q₀ hk ll A₀ w)
```

## 2 扩充的关系 `RelX⁺⁺`

左层 $L$ 是参数, 右层是指标. `LoF L`: 左层 $L$ 的坐标关系, 对一切右层.

```agda
LoF : H → Set₁
LoF L = ∀ {L′} → LoX L L′

data LeX⁺⁺ (L : H) (Lo : LoF L) : ∀ L′ {V V′} → Lg V → Lg V′ → D L V → D L′ V′ → Set where
  n0⁺⁺ : ∀ {L′ V V′} {lV : Lg V} {lV′ : Lg V′} {x′ : D L′ V′} → LeX⁺⁺ L Lo L′ lV lV′ n0 x′
  n1⁺⁺ : ∀ {L′ V V′} {lV : Lg V} {lV′ : Lg V′} → LeX⁺⁺ L Lo L′ lV lV′ n1 n1
  ⨾⁺⁺  : ∀ {L′ V V′} {lV : Lg V} {lV′ : Lg V′} {x y : D L V} {x′ y′ : D L′ V′} →
         LeX⁺⁺ L Lo L′ lV lV′ x x′ → LeX⁺⁺ L Lo L′ lV lV′ y y′ → LeX⁺⁺ L Lo L′ lV lV′ (x ⨾ y) (x′ ⨾ y′)
  nl⁺⁺ : ∀ {L′ V V′} {lV : Lg V} {lV′ : Lg V′} {d₁ : ℕ → D L V} {d₁′ : ℕ → D L′ V′} →
         (∀ n → LeX⁺⁺ L Lo L′ lV lV′ (d₁ n) (d₁′ n)) → LeX⁺⁺ L Lo L′ lV lV′ (nl d₁) (nl d₁′)
  pr⁺⁺ : ∀ {L′ V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {x′ y′ : D L′ V′} →
         LeX⁺⁺ L Lo L′ lV lV′ x x′ → LeX⁺⁺ L Lo L′ lV lV′ x (x′ ⨾ y′)
  nw⁺⁺ : ∀ {L′ V₀ V₀′ V V′} {lV₀ : Lg V₀} {lV₀′ : Lg V₀′} {lV : Lg V} {lV′ : Lg V′} {p : V₀ ⊲ V} {p′ : V₀′ ⊲ V′}
           {x : D L V₀} {x′ : D L′ V₀′} →
         AP lV₀ lV₀′ p lV p′ lV′ → LeX⁺⁺ L Lo L′ lV₀ lV₀′ x x′ → LeX⁺⁺ L Lo L′ lV lV′ (nw p x) (nw p′ x′)
  ni⁺⁺ : ∀ {L′ V V′ k k′} {lV : Lg V} {lV′ : Lg V′} {r : StH V k L} {r′ : StH V′ k′ L′}
           {u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′} {u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ r′ W′ → D L′ W′} →
         k ⊑∞ k′ →
         (∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CP lV lV′ p lc p′ lc′ →
            ∀ y y′ → Lo r r′ lc lc′ y y′ → LeX⁺⁺ L Lo L′ lc lc′ (u p lc y) (u′ p′ lc′ y′)) →
         LeX⁺⁺ L Lo L′ lV lV′ (ni r u) (ni r′ u′)
  κ⁺⁺  : ∀ {L′ V V′} {lV : Lg V} {lV′ : Lg V′} {zz : NZ L} {zz′ : NZ L′}
           {u : ∀ {c} → V ⊲ c → Lg c → D L c} {u′ : ∀ {c} → V′ ⊲ c → Lg c → D L′ c} →
         (∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CPᴸ lV lV′ p lc p′ lc′ →
            LeX⁺⁺ L Lo L′ lc lc′ (u p lc) (u′ p′ lc′)) →
         LeX⁺⁺ L Lo L′ lV lV′ (nκ zz u) (nκ zz′ u′)
  in⁺⁺ : ∀ {L′ V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {y′ x′ : D L′ V′} →
         LeX⁺⁺ L Lo L′ lV lV′ x y′ → In y′ x′ → LeX⁺⁺ L Lo L′ lV lV′ x x′
  rk⁺⁺ : ∀ {L′ ly ly′ W₀ W₀′ k k′ W W′ m m′} {lW₀ : Lg W₀} {lW₀′ : Lg W₀′} (r : StH W₀ k ly) (r′ : StH W₀′ k′ ly′)
           {u : ∀ {W₁} → W₀ ⊲ W₁ → Lg W₁ → Vs ly r W₁ → D ly W₁} {u′ : ∀ {W₁} → W₀′ ⊲ W₁ → Lg W₁ → Vs ly′ r′ W₁ → D ly′ W₁}
           (lW : Lg W) (lW′ : Lg W′) (ac : AccY ly) (ac₁ : AccY k) (ac′ : AccY ly′) (ac₁′ : AccY k′)
           (q₀ : W₀ ⊲ W) (q₀′ : W₀′ ⊲ W′) (ll : LW ly W) (ll′ : LW ly′ W′) (A₀ : Ig ly W) (A₀′ : Ig ly′ W′)
           (w : D ly W) (w′ : D ly′ W′) (Y : St W) (Y′ : St W′) (T : Tg W L m) (T′ : Tg W′ L′ m′) (R′ : StH m′ k′ L′) →
         RkPre {lW₀ = lW₀} {lW₀′} r r′ u u′ lW lW′ q₀ q₀′ A₀ A₀′ w w′ Y Y′ → TX lW lW′ T T′ →
         rkT (⊲ᴴ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T) ≡ rise → rkT (⊲ᴴ↑ (wm T′) (kk r′ q₀′ ll′)) (tm T′) (lm T′) ≡ keep R′ →
         LeX⁺⁺ L Lo L′ (lm T) (lm T′) (RKi ac ac₁ r u q₀ lW ll A₀ w Y T rise) (RKi ac′ ac₁′ r′ u′ q₀′ lW′ ll′ A₀′ w′ Y′ T′ (keep R′))
  nκ⁺⁺ : ∀ {L′ V V′ k} {lV : Lg V} {lV′ : Lg V′} {r : StH V k L} {u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′}
           {zz′ : NZ L′} {v′ : ∀ {c} → V′ ⊲ c → Lg c → D L′ c} →
         LeX⁺⁺ L Lo L′ lV lV′ (ni r u) (v′ C.self lV′) → LeX⁺⁺ L Lo L′ lV lV′ (ni r u) (nκ zz′ v′)
  -- 新: 同一节点, 低目标 T 上升 ⇒ 高目标 T′ 保留 (产生时动作 ActS)
  up   : ∀ {t t′ V} {lV : Lg V} {x : D L V} {ly W₀ k W m m′} {lW₀ : Lg W₀} (r : StH W₀ k ly)
           {u : ∀ {W₁} → W₀ ⊲ W₁ → Lg W₁ → Vs ly r W₁ → D ly W₁}
           (lW : Lg W) (ac : AccY ly) (ac₁ : AccY k) (q₀ : W₀ ⊲ W) (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W)
           (T : Tg W t m) (T′ : Tg W t′ m′) (R′ : StH m′ k t′) →
         ActS A₀ →
         rkT (⊲ᴴ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T) ≡ rise → rkT (⊲ᴴ↑ (wm T′) (kk r q₀ ll)) (tm T′) (lm T′) ≡ keep R′ →
         LeX⁺⁺ L Lo t lV (lm T) x (RKi ac ac₁ r u q₀ lW ll A₀ w Y T rise) →
         LeX⁺⁺ L Lo t′ lV (lm T′) x (RKi ac ac₁ r u q₀ lW ll A₀ w Y T′ (keep R′))

RelX⁺⁺   : ∀ L L′ {V V′} → Lg V → Lg V′ → D L V → D L′ V′ → Set
BelowX⁺⁺ : ∀ L → LoF L
RelSX⁺⁺  : ∀ L {V k} → StH V k L → ∀ k′ {c c′} → Lg c → Lg c′ → D k c → D k′ c′ → Set
RelAtX⁺⁺ : ∀ b {V k} → k ⊲[ V ] b → ∀ k′ {c c′} → Lg c → Lg c′ → D k c → D k′ c′ → Set

RelX⁺⁺ L L′ = LeX⁺⁺ L (BelowX⁺⁺ L) L′
BelowX⁺⁺ L {k′ = k′} r r′ lc lc′ y y′ = RelSX⁺⁺ L r k′ lc lc′ (outS r y) (outS r′ y′)
RelSX⁺⁺ (hs b) (ss P) = RelAtX⁺⁺ b P
RelSX⁺⁺ (hl f) (sl n P) = RelAtX⁺⁺ (f n) P
RelSX⁺⁺ (hΩ g) (sL e P) = RelAtX⁺⁺ (g _) P
RelAtX⁺⁺ b hself k′ = RelX⁺⁺ b k′
RelAtX⁺⁺ (hs b) (hsuc P) = RelAtX⁺⁺ b P
RelAtX⁺⁺ (hl f) (hlim n P) = RelAtX⁺⁺ (f n) P
RelAtX⁺⁺ (hΩ g) (hLim e P) = RelAtX⁺⁺ (g _) P

-- 旧关系嵌进新关系 (类型)
Emb⁺⁺ : Set
Emb⁺⁺ = ∀ L L′ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {x′ : D L′ V′} → RelX⁺ L L′ lV lV′ x x′ → RelX⁺⁺ L L′ lV lV′ x x′
```

## 3 输出关系, 状态关系, 动作前提

```agda
OA⁺⁺ : ∀ {W W′} → Lg W → Lg W′ → Df W → Df W′ → Set
OA⁺⁺ {W} {W′} lW lW′ Δ Δ′ =
  ∀ {t t′ m m′} (T : Tg W t m) (T′ : Tg W′ t′ m′) → TX lW lW′ T T′ → RelX⁺⁺ t t′ (lm T) (lm T′) (yc Δ T) (yc Δ′ T′)

R⁺⁺ : ∀ {W W′} → Lg W → Lg W′ → St W → St W′ → Set
R⁺⁺ lW lW′ Y Y′ = OA⁺⁺ lW lW′ (d Y) (d Y′) × RelX⁺⁺ hz hz lW lW′ (z Y) (z Y′)

J⁺⁺ : ∀ {W W′} → Lg W → Lg W′ → St W → St W′ → Set
J⁺⁺ lW lW′ Y Y′ = R⁺⁺ lW lW′ Y Y′ × (NE Y × NE Y′)

HAW⁺⁺ : ∀ L L′ {W W′} → Lg W → Lg W′ → Ig L W → Ig L′ W′ → Set
HAW⁺⁺ L L′ {W} {W′} lW lW′ A₀ A₀′ =
  ∀ {W₁ W₁′} (p : W ⊲ W₁) (p′ : W′ ⊲ W₁′) (lW₁ : Lg W₁) (lW₁′ : Lg W₁′) → CP lW lW′ p lW₁ p′ lW₁′ →
  ∀ w w′ → RelX⁺⁺ L L′ lW₁ lW₁′ w w′ → ∀ (Y : St W₁) (Y′ : St W₁′) → J⁺⁺ lW₁ lW₁′ Y Y′ →
  OA⁺⁺ lW₁ lW₁′ (A₀ p lW₁ w Y) (A₀′ p′ lW₁′ w′ Y′)

-- 再折叠的动作限为折叠的语法
HAWS : ∀ L L′ {W W′} → Lg W → Lg W′ → Ig L W → Ig L′ W′ → Set
HAWS L L′ lW lW′ A₀ A₀′ = HAW⁺⁺ L L′ lW lW′ A₀ A₀′ × (ActS A₀ × ActS A₀′)
```

## 4 带条件的语义, kZ 下的时间条件

```agda
SemS : ∀ L L′ {V V′} → Lg V → Lg V′ → Cond → D L V → D L′ V′ → Set
SemS L L′ {V} {V′} lV lV′ Ok x x′ =
  ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac′ : AccY L′) (ll : LW L W) (ll′ : LW L′ W′)
    (q : V ⊲ W) (q′ : V′ ⊲ W′) → CP lV lV′ q lW q′ lW′ →
  ∀ (A₀ : Ig L W) (A₀′ : Ig L′ W′) → HAWS L L′ lW lW′ A₀ A₀′ →
  ∀ w w′ → RelX⁺⁺ L L′ lW lW′ w w′ → ∀ (Y : St W) (Y′ : St W′) → J⁺⁺ lW lW′ Y Y′ → Ok lW lW′ Y Y′ →
  OA⁺⁺ lW lW′ (Run ac x q lW ll A₀ w Y) (Run ac′ x′ q′ lW′ ll′ A₀′ w′ Y′)

-- 左边产生时的状态 Y₀ (世界 W₀): 差分量被右边再折叠状态 Y′ 的差分量支配; 累计被 Y′ 在第 0 层目标上的读数支配
DomZ : ∀ {W₀} → Lg W₀ → St W₀ → Cond
DomZ lW₀ Y₀ lW lW′ Y Y′ =
  (OA⁺⁺ lW₀ lW′ (d Y₀) (d Y′) × RelX⁺⁺ hz hz lW₀ lW′ (z Y₀) (yc (d Y′) (τ₀ lW′))) × (NE Y₀ × NE Y′)
```

## 5 可靠性 (类型)

`UpSoundS Ok`: `up` 的每个实例 (产生时动作 `ActS`) 在 `SemS … Ok` 下可靠. `UpSoundZ`: `Ok` 取这个节点产生状态的 `DomZ`.

```agda
UpSoundS : (∀ {W} → Lg W → St W → Cond) → Set
UpSoundS Ok =
  ∀ {L₀ V} {lV : Lg V} {x : D L₀ V} {ly W₀ k W t t′ m m′} {lW₀ : Lg W₀} (r : StH W₀ k ly)
    {u : ∀ {W₁} → W₀ ⊲ W₁ → Lg W₁ → Vs ly r W₁ → D ly W₁}
    (lW : Lg W) (ac : AccY ly) (ac₁ : AccY k) (q₀ : W₀ ⊲ W) (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W)
    (T : Tg W t m) (T′ : Tg W t′ m′) (R′ : StH m′ k t′) →
  ActS A₀ →
  rkT (⊲ᴴ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T) ≡ rise → rkT (⊲ᴴ↑ (wm T′) (kk r q₀ ll)) (tm T′) (lm T′) ≡ keep R′ →
  SemS L₀ t lV (lm T) (Ok lW Y) x (RKi ac ac₁ r u q₀ lW ll A₀ w Y T rise) →
  SemS L₀ t′ lV (lm T′) (Ok lW Y) x (RKi ac ac₁ r u q₀ lW ll A₀ w Y T′ (keep R′))

UpSoundZ : Set
UpSoundZ = UpSoundS DomZ

RkSoundZ : H → H → Set
RkSoundZ L L′ =
  ∀ {ly ly′ W₀ W₀′ k k′ W W′ m m′} {lW₀ : Lg W₀} {lW₀′ : Lg W₀′} (r : StH W₀ k ly) (r′ : StH W₀′ k′ ly′)
    {u : ∀ {W₁} → W₀ ⊲ W₁ → Lg W₁ → Vs ly r W₁ → D ly W₁} {u′ : ∀ {W₁} → W₀′ ⊲ W₁ → Lg W₁ → Vs ly′ r′ W₁ → D ly′ W₁}
    (lW : Lg W) (lW′ : Lg W′) (ac : AccY ly) (ac₁ : AccY k) (ac′ : AccY ly′) (ac₁′ : AccY k′)
    (q₀ : W₀ ⊲ W) (q₀′ : W₀′ ⊲ W′) (ll : LW ly W) (ll′ : LW ly′ W′) (A₀ : Ig ly W) (A₀′ : Ig ly′ W′)
    (w : D ly W) (w′ : D ly′ W′) (Y : St W) (Y′ : St W′) (T : Tg W L m) (T′ : Tg W′ L′ m′) (R′ : StH m′ k′ L′) →
  RkPre {lW₀ = lW₀} {lW₀′} r r′ u u′ lW lW′ q₀ q₀′ A₀ A₀′ w w′ Y Y′ → TX lW lW′ T T′ →
  rkT (⊲ᴴ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T) ≡ rise → rkT (⊲ᴴ↑ (wm T′) (kk r′ q₀′ ll′)) (tm T′) (lm T′) ≡ keep R′ →
  ActS A₀ → ActS A₀′ →
  SemS L L′ (lm T) (lm T′) (DomZ lW Y)
    (RKi ac ac₁ r u q₀ lW ll A₀ w Y T rise) (RKi ac′ ac₁′ r′ u′ q₀′ lW′ ll′ A₀′ w′ Y′ T′ (keep R′))

-- 升升义务: 同一对节点 (前提同 RkSoundZ), 两边都上升的目标对
OblRRZ : H → H → Set
OblRRZ L L′ =
  ∀ {ly ly′ W₀ W₀′ k k′ W W′ m m′} {lW₀ : Lg W₀} {lW₀′ : Lg W₀′} (r : StH W₀ k ly) (r′ : StH W₀′ k′ ly′)
    {u : ∀ {W₁} → W₀ ⊲ W₁ → Lg W₁ → Vs ly r W₁ → D ly W₁} {u′ : ∀ {W₁} → W₀′ ⊲ W₁ → Lg W₁ → Vs ly′ r′ W₁ → D ly′ W₁}
    (lW : Lg W) (lW′ : Lg W′) (ac : AccY ly) (ac₁ : AccY k) (ac′ : AccY ly′) (ac₁′ : AccY k′)
    (q₀ : W₀ ⊲ W) (q₀′ : W₀′ ⊲ W′) (ll : LW ly W) (ll′ : LW ly′ W′) (A₀ : Ig ly W) (A₀′ : Ig ly′ W′)
    (w : D ly W) (w′ : D ly′ W′) (Y : St W) (Y′ : St W′) (T : Tg W L m) (T′ : Tg W′ L′ m′) →
  RkPre {lW₀ = lW₀} {lW₀′} r r′ u u′ lW lW′ q₀ q₀′ A₀ A₀′ w w′ Y Y′ → TX lW lW′ T T′ →
  rkT (⊲ᴴ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T) ≡ rise → rkT (⊲ᴴ↑ (wm T′) (kk r′ q₀′ ll′)) (tm T′) (lm T′) ≡ rise →
  ActS A₀ → ActS A₀′ →
  SemS L L′ (lm T) (lm T′) (DomZ lW Y)
    (RKi ac ac₁ r u q₀ lW ll A₀ w Y T rise) (RKi ac′ ac₁′ r′ u′ q₀′ lW′ ll′ A₀′ w′ Y′ T′ rise)
```

## 变更记录

- 2026-11-05 16:01: 定稿 (首次编译通过, 退出码 0, 约 4 秒, 峰值常驻约 0.7 GB).
- 2026-11-05 16:22: 补注 (文字, 不改定义). (i) `UpSoundS` 的隐式参数 `{lW₀ : Lg W₀}` 不出现在类型的其余部分; 把 `UpSoundZ` 的一个值当作参数传给另一个以 `UpSoundZ` 为类型的位置时, Agda 推不出它 (未解的元变量). 用法: 直接对假设应用并写出 `{lW₀ = …}` (见 `StrRel19Up.obsUpTT`). (ii) 判断 (未编译): `Emb⁺⁺` 可能不成立: `ni⁺⁺` 的分支前提里坐标关系负出现, `up` 让低层的关系变大. 第 $0$ 层的嵌入成立 (`StrRel19Up.emb00`). §1–§5 未改.
