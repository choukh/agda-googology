# 结构关系, 第十五轮: 接口 (只放记录与类型)

> **接口定稿 2026-11-05 10:48.** 之后只增不改, 改动写在文末的变更记录. 构造一路 (前缀 `StrRel15`) 与否定一路 (前缀 `StrRel15N`) 共用本文. 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 只有定义 (数据类型, 类型别名, 参数化模块里的类型), 没有定理.
>
> 内容 (对应 `StrRel14` 接手清单第 1, 2, 5, 6 项):
>
> 1. **跨目标层的目标对** `TX` (§1): 两个目标 $T$ (层 $t$, 世界 $m$) 与 $T'$ (层 $t'$, 世界 $m'$), 世界按 `CP` 对齐 (同 `StrRel12Sem.TC`), 目标层带字面证据 $t\sqsubseteq_\infty t'$. 同层 ($t=t'$) 是 `s∞`, 所以 `TC` 是 `TX` 的特例.
> 2. **推广到目标层对的输出关系** `OA²` (§2): 一切 `TX` 目标对上, 两边读数按 `StrRel14If.RelX t t′` 相关. **跨目标层的状态关系** `R²`: 差分量 `OA²`, 第 $0$ 层分量 `RelX hz hz`. **状态不变量** `J²` = `R²` 加两边都 "非空" (`StrRel14J.NE`: 一切目标上的读数在左脊上含 $\omega\cdot(\Omega_t⨾y)$). `NE` 一项依据 `StrRel14NegInv.inv-kill`: 含 "右边高坐标层读数为零树" 的状态对的不变量都推出反例; `NE` 排除零树读数.
> 3. **律** (§3, 只写类型): `Law⊕` (状态加上 `OA²` 相关的输出, 仍 `J²`), `Lawcv` (换世界, 路径 `AP` 对齐), `LawKp`/`LawKb` (`nκ` 的两种输出, 分支在 `CPᴸ` 对上相关且有语义时, 输出 `OA²` 相关).
> 4. **动作前提与语义** (§4): `HAW²` (输入 `RelX L L′`, 状态 `J²` ⇒ 动作输出 `OA²`), `SemX² L L′` (`StrRel14If.SemX` 的结论从同层 `OAcX` 换成 `OA²`, 状态前提从 `R∀X` 换成 `J²`).
> 5. **在其上重写的跨坐标层节点义务** (§5): 节点对 `ni r u` (坐标层 $k$) 与 `ni r′ u′` (坐标层 $k'$), $k\sqsubseteq_\infty k'$, 在一个 `TX` 目标对 $(T,T')$ 上, 两边 `rkT` 实际给出的种类对. 目标层不同时四种都可能出现 (判断, 依据 `rk-mono` 的证明: 左升要 $t\sqsubseteq k$, 右留要 $k'\sqsubset t'$, 两者在 $t\ne t'$ 时可以同时成立), 所以写四个义务 `OblRR²`, `OblKK²`, `OblKR²`, `OblRK²` (带 `≡` 证据, 同 `StrRel14If.NodeObl⁼`). `NodeSound²` 是节点规则的可靠性; `NodeSound²₀` 是左坐标层为 $0$ 的特例 (`StrRel13Val` 的 `xL`/`xR` 是这一种).
>
> ## 律的定义域 (逐条检查, 依 `AGENTS.md` "律带公共上界")
>
> 律里出现的每一对下标或路径, 都写出它带的字面公共上界的证据. "只有值" 一列指只有值上的 $\le$ 而没有字面证据的地方.
>
> | 律 / 字段 | 被比较的一对 | 字面证据 | 只有值的部分 |
> |---|---|---|---|
> | `TX` | 目标层 $t$, $t'$ | $t\sqsubseteq_\infty t'$ (字面); 两者都是 $\Lambda$ 的第一位置 (`tm`), $\Lambda$ 是字面公共上界 | 无 |
> | `TX` | 目标世界 $m$, $m'$ (经 $W\lhd m$, $W'\lhd m'$) | `CP` 的对齐 `AP` (逐步的 `Al`) | `CP` 的 $m\le m'$, `Al` 的 `aP` 的 $c\le c'$ (对齐的数据, 不是比较两个下标; 同 `StrRel14If` 的处理) |
> | `OA²`, `R²`, `J²` | 同上 | 同上 | 同上 |
> | `R²` 的第 $0$ 层分量 | 两个运行世界 $W$, $W'$ | 层相同 ($0$) | 无 |
> | `Law⊕` | 状态与输出的世界 | `Top` (= 两边路径 `self` 的 `CP`) | `CP` 的 $W\le W'$ |
> | `Lawcv` | 换世界的路径对 | `AP` | `Al` 的 `aP` |
> | `LawKp` | 目标世界对 $W^+$, $W^{+\prime}$ | `CP` (来自 `TX`) | 同上 |
> | `LawKb` | 格世界对 $c$, $c'$ | `CPᴸ` ($c\lhd c'$, $c'$ 是字面公共上界) | `CP` 部分 |
> | `HAW²`, `SemX²` 的路径与输入 | 世界对; 输入层 $L$, $L'$ | `CP`; 输入按 `RelX L L′` (节点处要 $\sqsubseteq_\infty$, `κ` 处要 `CPᴸ`) | `CP` 部分 |
> | `NodeObl²` | 坐标层 $k$, $k'$ | $k\sqsubseteq_\infty k'$ (`NodeSound²` 的前提); 两者在世界 $m$, $m'$ 里都是 $\Lambda$ 的第一位置 (`kk`) | 无 |
> | `NodeObl²` | 目标层 $t$, $t'$ | `TX` 的 $t\sqsubseteq_\infty t'$ | 无 |
>
> **检查的结论 (判断).** 每一对层 (目标层, 坐标层) 都带 $\sqsubseteq_\infty$ 的字面证据; 世界只经 `CP`/`AP`/`CPᴸ`, 其中值的部分与 `StrRel14If` 相同 (对齐的数据, 不用来比较两个高度). 没有裸下标上的律.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
module OCF.Align.StrRel15If (Λ : H) (lΛ : LgH Λ) where

open import Data.Product using (Σ; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
open import OCF.Align.HtFeedTree using (hz; StH; Vs; D; ni; AccY; ⊲ᴴ↑)
open import OCF.Align.HtFeedClosed using (module At)
open import OCF.Align.StrRel11Rk Λ lΛ using (_⊑∞_)
open import OCF.Align.StrRel12Al using (AP; CP)
open import OCF.Align.StrRel12Sem Λ lΛ using (Top)
open import OCF.Align.StrRel14If Λ lΛ using (RelX; BelowX; CPᴸ)
open import OCF.Align.StrRel14J Λ lΛ using (NE)

module P = At Λ lΛ
open P using (Tg; tg; wm; tm; lm; St; Df; yc; d; z; cv; _⊕⟨_⟩_; Run; Ig; LW; Rk; rkT; RKi; kk; rise; keep; Kp; Kb)
```

## 1 跨目标层的目标对

```agda
TX : ∀ {W W′ t t′ m m′} → Lg W → Lg W′ → Tg W t m → Tg W′ t′ m′ → Set
TX {t = t} {t′ = t′} lW lW′ T T′ = CP lW lW′ (wm T) (lm T) (wm T′) (lm T′) × (t ⊑∞ t′)
```

## 2 输出关系, 状态关系, 状态不变量

```agda
OA² : ∀ {W W′} → Lg W → Lg W′ → Df W → Df W′ → Set
OA² {W} {W′} lW lW′ Δ Δ′ =
  ∀ {t t′ m m′} (T : Tg W t m) (T′ : Tg W′ t′ m′) → TX lW lW′ T T′ → RelX t t′ (lm T) (lm T′) (yc Δ T) (yc Δ′ T′)

R² : ∀ {W W′} → Lg W → Lg W′ → St W → St W′ → Set
R² lW lW′ Y Y′ = OA² lW lW′ (d Y) (d Y′) × RelX hz hz lW lW′ (z Y) (z Y′)

J² : ∀ {W W′} → Lg W → Lg W′ → St W → St W′ → Set
J² lW lW′ Y Y′ = R² lW lW′ Y Y′ × (NE Y × NE Y′)
```

## 3 律 (类型)

```agda
Law⊕ : Set
Law⊕ = ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} → Top lW lW′ → ∀ (Y : St W) (Y′ : St W′) (Δ : Df W) (Δ′ : Df W′) →
       J² lW lW′ Y Y′ → OA² lW lW′ Δ Δ′ → J² lW lW′ (Y ⊕⟨ lW ⟩ Δ) (Y′ ⊕⟨ lW′ ⟩ Δ′)

Lawcv : Set
Lawcv = ∀ {W W′ W₂ W₂′} {lW : Lg W} {lW′ : Lg W′} {q : W ⊲ W₂} {lW₂ : Lg W₂} {q′ : W′ ⊲ W₂′} {lW₂′ : Lg W₂′} →
        AP lW lW′ q lW₂ q′ lW₂′ → ∀ (Y : St W) (Y′ : St W′) → J² lW lW′ Y Y′ → J² lW₂ lW₂′ (cv q Y) (cv q′ Y′)
```

## 4 动作前提与语义

```agda
HAW² : ∀ L L′ {W W′} → Lg W → Lg W′ → Ig L W → Ig L′ W′ → Set
HAW² L L′ {W} {W′} lW lW′ A₀ A₀′ =
  ∀ {W₁ W₁′} (p : W ⊲ W₁) (p′ : W′ ⊲ W₁′) (lW₁ : Lg W₁) (lW₁′ : Lg W₁′) → CP lW lW′ p lW₁ p′ lW₁′ →
  ∀ w w′ → RelX L L′ lW₁ lW₁′ w w′ → ∀ (Y : St W₁) (Y′ : St W₁′) → J² lW₁ lW₁′ Y Y′ →
  OA² lW₁ lW₁′ (A₀ p lW₁ w Y) (A₀′ p′ lW₁′ w′ Y′)

SemX² : ∀ L L′ {V V′} → Lg V → Lg V′ → D L V → D L′ V′ → Set
SemX² L L′ {V} {V′} lV lV′ x x′ =
  ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac′ : AccY L′) (ll : LW L W) (ll′ : LW L′ W′)
    (q : V ⊲ W) (q′ : V′ ⊲ W′) → CP lV lV′ q lW q′ lW′ →
  ∀ (A₀ : Ig L W) (A₀′ : Ig L′ W′) → HAW² L L′ lW lW′ A₀ A₀′ →
  ∀ w w′ → RelX L L′ lW lW′ w w′ → ∀ (Y : St W) (Y′ : St W′) → J² lW lW′ Y Y′ →
  OA² lW lW′ (Run ac x q lW ll A₀ w Y) (Run ac′ x′ q′ lW′ ll′ A₀′ w′ Y′)
```

`nκ` 的两种输出 (`Kp`: 走到目标世界的一段; `Kb`: 目标世界之上的格 $c$) 的律. 分支族 $u$ (层 $L$), $u'$ (层 $L'$) 在 `CPᴸ` 对上相关且有语义.

```agda
module KLaw {L L′ W₀ W₀′} {lW₀ : Lg W₀} {lW₀′ : Lg W₀′}
            (u : ∀ {c} → W₀ ⊲ c → Lg c → D L c) (u′ : ∀ {c} → W₀′ ⊲ c → Lg c → D L′ c) where
  BrOK : Set
  BrOK = ∀ {c c′} (p : W₀ ⊲ c) (p′ : W₀′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CPᴸ lW₀ lW₀′ p lc p′ lc′ →
         RelX L L′ lc lc′ (u p lc) (u′ p′ lc′) × SemX² L L′ lc lc′ (u p lc) (u′ p′ lc′)

  LawKp : Set
  LawKp = BrOK → ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac′ : AccY L′) (q₀ : W₀ ⊲ W) (q₀′ : W₀′ ⊲ W′) →
          CP lW₀ lW₀′ q₀ lW q₀′ lW′ → (ll : LW L W) (ll′ : LW L′ W′) (A₀ : Ig L W) (A₀′ : Ig L′ W′) → HAW² L L′ lW lW′ A₀ A₀′ →
          ∀ w w′ → RelX L L′ lW lW′ w w′ → ∀ (Y : St W) (Y′ : St W′) → J² lW lW′ Y Y′ →
          ∀ {W⁺ W⁺′} (wu : W ⊲ W⁺) (wu′ : W′ ⊲ W⁺′) (lW⁺ : Lg W⁺) (lW⁺′ : Lg W⁺′) → CP lW lW′ wu lW⁺ wu′ lW⁺′ →
          OA² lW⁺ lW⁺′ (Kp ac u q₀ ll A₀ w Y wu lW⁺) (Kp ac′ u′ q₀′ ll′ A₀′ w′ Y′ wu′ lW⁺′)

  LawKb : Set
  LawKb = BrOK → ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac′ : AccY L′) (q₀ : W₀ ⊲ W) (q₀′ : W₀′ ⊲ W′) →
          CP lW₀ lW₀′ q₀ lW q₀′ lW′ → (ll : LW L W) (ll′ : LW L′ W′) (A₀ : Ig L W) (A₀′ : Ig L′ W′) → HAW² L L′ lW lW′ A₀ A₀′ →
          ∀ w w′ → RelX L L′ lW lW′ w w′ → ∀ (Y : St W) (Y′ : St W′) → J² lW lW′ Y Y′ →
          ∀ {W⁺ W⁺′} (wu : W ⊲ W⁺) (wu′ : W′ ⊲ W⁺′) (lW⁺ : Lg W⁺) (lW⁺′ : Lg W⁺′) → CP lW lW′ wu lW⁺ wu′ lW⁺′ →
          ∀ {c c′} (p : W⁺ ⊲ c) (p′ : W⁺′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CPᴸ lW⁺ lW⁺′ p lc p′ lc′ →
          OA² lc lc′ (Kb ac u q₀ ll A₀ w Y wu lW⁺ p lc) (Kb ac′ u′ q₀′ ll′ A₀′ w′ Y′ wu′ lW⁺′ p′ lc′)
```

## 5 跨坐标层节点义务, 在目标层对上

```agda
module NodeObl² {L L′ V V′ k k′} {lV : Lg V} {lV′ : Lg V′} (r : StH V k L) (r′ : StH V′ k′ L′)
                (u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′) (u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ r′ W′ → D L′ W′)
                {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac₁ : AccY k) (ac′ : AccY L′) (ac₁′ : AccY k′)
                (q₀ : V ⊲ W) (q₀′ : V′ ⊲ W′) (ll : LW L W) (ll′ : LW L′ W′) (A₀ : Ig L W) (A₀′ : Ig L′ W′)
                (w : D L W) (w′ : D L′ W′) (Y : St W) (Y′ : St W′) where
  rkL : ∀ {t m} → Tg W t m → Rk k t m
  rkL T = rkT (⊲ᴴ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T)
  rkR : ∀ {t′ m′} → Tg W′ t′ m′ → Rk k′ t′ m′
  rkR T′ = rkT (⊲ᴴ↑ (wm T′) (kk r′ q₀′ ll′)) (tm T′) (lm T′)

  Out² : ∀ {t t′ m m′} (T : Tg W t m) (T′ : Tg W′ t′ m′) → Rk k t m → Rk k′ t′ m′ → Set
  Out² T T′ rk rk′ = RelX _ _ (lm T) (lm T′) (RKi ac ac₁ r u q₀ lW ll A₀ w Y T rk) (RKi ac′ ac₁′ r′ u′ q₀′ lW′ ll′ A₀′ w′ Y′ T′ rk′)

  OblRR² OblKK² OblKR² OblRK² : Set
  OblRR² = ∀ {t t′ m m′} (T : Tg W t m) (T′ : Tg W′ t′ m′) → TX lW lW′ T T′ → rkL T ≡ rise → rkR T′ ≡ rise → Out² T T′ rise rise
  OblKK² = ∀ {t t′ m m′} (T : Tg W t m) (T′ : Tg W′ t′ m′) → TX lW lW′ T T′ → ∀ R R′ → rkL T ≡ keep R → rkR T′ ≡ keep R′ →
           Out² T T′ (keep R) (keep R′)
  OblKR² = ∀ {t t′ m m′} (T : Tg W t m) (T′ : Tg W′ t′ m′) → TX lW lW′ T T′ → ∀ R → rkL T ≡ keep R → rkR T′ ≡ rise →
           Out² T T′ (keep R) rise
  OblRK² = ∀ {t t′ m m′} (T : Tg W t m) (T′ : Tg W′ t′ m′) → TX lW lW′ T T′ → ∀ R′ → rkL T ≡ rise → rkR T′ ≡ keep R′ →
           Out² T T′ rise (keep R′)

-- 节点规则的可靠性: 坐标层字面 k ⊑∞ k′, 分支在 CP 对上按 BelowX 相关 ⇒ 节点对的 SemX²
NodeSound² : Set
NodeSound² = ∀ {L L′ V V′ k k′} {lV : Lg V} {lV′ : Lg V′} (r : StH V k L) (r′ : StH V′ k′ L′)
               {u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′} {u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ r′ W′ → D L′ W′} →
             k ⊑∞ k′ →
             (∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CP lV lV′ p lc p′ lc′ →
                ∀ y y′ → BelowX L L′ r r′ lc lc′ y y′ → RelX L L′ lc lc′ (u p lc y) (u′ p′ lc′ y′)) →
             SemX² L L′ lV lV′ (ni r u) (ni r′ u′)

-- 左坐标层为 0 的特例
NodeSound²₀ : Set
NodeSound²₀ = ∀ {L L′ V V′ k′} {lV : Lg V} {lV′ : Lg V′} (r : StH V hz L) (r′ : StH V′ k′ L′)
                {u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′} {u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ r′ W′ → D L′ W′} →
              hz ⊑∞ k′ →
              (∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CP lV lV′ p lc p′ lc′ →
                 ∀ y y′ → BelowX L L′ r r′ lc lc′ y y′ → RelX L L′ lc lc′ (u p lc y) (u′ p′ lc′ y′)) →
              SemX² L L′ lV lV′ (ni r u) (ni r′ u′)
```

## 变更记录

- 2026-11-05 10:48: 定稿 (首次编译通过, 退出码 0).
