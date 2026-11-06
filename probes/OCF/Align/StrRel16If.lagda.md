# 结构关系, 第十六轮: 接口 (只放记录与类型)

> **接口定稿 2026-11-05 11:28.** 之后只增不改, 改动写在文末的变更记录. 构造一路 (前缀 `StrRel16`) 与否定一路 (前缀 `NegSR16`) 共用本文. 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 只有定义 (数据类型, 类型别名, 参数化模块里的类型), 没有定理.
>
> 内容 (对应 `StrRel15` 接手清单第 1–3 项):
>
> 1. **扩充的异质关系 `RelX⁺`** (§2) = `StrRel14If.RelX` 的八条规则 (改名加 `⁺`) 加三条:
>    - **`in⁺` ("节点 ≤ 链极限", 写成一般形):** $x\le y'$ 且 $y'$ 是 $x'$ 的一个分量 (`In`: 沿 `⨾` 的左右两边与 `nl` 的某一项往下走, 同一个世界) ⇒ $x\le x'$. 左边是节点 `ni …`, 右边是链的极限 `nl …` 时, 就是 `RKi` 的 keep 句的输出对 rise 句的输出: 节点在链的某一项的某个分量之下. 它把 `prˣ` (左分量) 包含在内.
>    - **`rk⁺` ("链极限 ≤ 节点", 字面形):** 结论的两边就是 `RKi` 的 rise 句与 keep 句的字面输出: 左节点 (坐标层 $k$) 在目标 $T$ 上上升, 右节点 (坐标层 $k'$) 在目标 $T'$ 上保留, $(T,T')$ 是 `TX` 对. 前提 `RkPre` 是 `StrRel15Node.Red².node-red²` 的前提 (路径 `CP`, $k\sqsubseteq_\infty k'$, 分支, 动作, 上下文, 状态), 但**用旧关系写** (`StrRel14If.RelX`, `StrRel15If.HAW²`, `StrRel15If.J²`). 理由见下面 "严格正性".
>    - **`nκ⁺` ("ni 对 nκ"):** 节点 $\le$ `nκ` 在**自身世界** (路径 `self`) 上的分支 ⇒ 节点 $\le$ `nκ`. 目的: $\Omega_1=1⨾\mathrm{ni}\ldots$ 对 $\Omega_\Omega=1⨾\mathrm{n\kappa}\ldots$ (`StrRel15Bar.¬ΩΩ`), 让 $\Omega^{\mathsf H}$ 处闭项的状态进入不变量.
> 2. **以 `RelX⁺` 为输出关系的语义** (§3–§5): `OA²⁺`, `R²⁺`, `J²⁺` (= `R²⁺` 加两边 `StrRel14J.NE`), 律 `Law⊕⁺`, `Lawcv⁺`, 动作前提 `HAW²⁺`, 语义 `SemX²⁺`, 节点义务 `NodeObl²⁺` (四种, 按 `rkT` 实际种类, 带 `≡`), 节点可靠性 `NodeSound²⁺`, 左坐标层为 $0$ 的特例 `NodeSound²⁺₀`; 嵌入的类型 `Emb` (旧关系 ⊆ 新关系).
>
> **严格正性 (判断, 依据 Agda 的正性检查规则).** `LeX⁺ L L′ Lo` 与 `LeX` 一样以层 $L,L'$ 为参数, 坐标层的关系 `Lo` 由对层的结构递归先定义 (`niˣ` 的分支前提里 `Lo` 出现在负位置, 正因为它是先定义的). 所以构造子的前提里不能出现别的层上的 `LeX⁺`. `rk⁺` 要的状态、动作、上下文、分支前提都在别的层 (节点层 $ly$, 坐标层, 一切目标层), 动作前提还在负位置. 于是这些前提只能用已定义的旧关系写. 后果 (判断): `SemX²⁺` 的节点情形给出的是 `J²⁺`/`HAW²⁺` 前提, 不一定是旧的 `J²`/`HAW²`, 所以 `rk⁺` 在 `NodeSound²⁺` 里不一定能用上. 这是本接口留下的缺口, 写在这里, 不当作已解决.
>
> **为什么 `in⁺` 不撞 `StrRel13Later.¬laterV`** (判断; 编译证据在 `StrRel16Kr`). `¬laterV` 的那一对是左留右升: 左 `ni …`, 右 `nl …`, 右边上升时的状态是空状态 $Y_0$, 链的每一项都是 `n0` (`StrRel13Val.xz`). `in⁺` 要节点 $\le$ 链的某一项的某个分量; `n0` 的分量只有 `n0`, 而 `RelX⁺` 里没有 "节点 $\le$ `n0`". 所以那一对不在 `RelX⁺` 里. 在 `J²` 的状态下 (带 `NE`: 每个目标上的读数在左脊上含 $\omega\cdot(\Omega_t⨾y)$), 链的第一项是状态在坐标层上的读数的运行, 它含 $\Omega_{k'}$ 里的节点, 节点可以落在它下面.
>
> ## 律的定义域 (逐条检查, 依 `AGENTS.md` "律带公共上界")
>
> | 律 / 规则 | 被比较的一对 | 字面证据 | 只有值的部分 |
> |---|---|---|---|
> | 旧的八条 (`n0⁺` … `κ⁺`) | 同 `StrRel14If` | 同 `StrRel14If` | 同 `StrRel14If` |
> | `in⁺` | $y'$ 与 $x'$ | $y'$ 是 $x'$ 的字面分量 (`In`), 同一层同一世界; 不比较两个下标 | 无 |
> | `rk⁺` | 两个节点的世界 $W_0,W_0'$ | 路径 `CP` (同 `NodeSound²`) | `CP` 的 $W\le W'$ |
> | `rk⁺` | 坐标层 $k$, $k'$ | $k\sqsubseteq_\infty k'$ | 无 |
> | `rk⁺` | 目标 $T$, $T'$ | `TX` ($t\sqsubseteq_\infty t'$, 世界 `CP`) | 同 `StrRel15If` |
> | `rk⁺` | 分支世界 | `CP` (同 `niˣ`) | 同上 |
> | `nκ⁺` | 分支的世界 | 路径 `self` ($V'\lhd V'$): 不比较两个世界 | 无 |
> | `OA²⁺`, `R²⁺`, `J²⁺`, `Law⊕⁺`, `Lawcv⁺`, `HAW²⁺`, `SemX²⁺`, `NodeObl²⁺` | 同 `StrRel15If` | 同 `StrRel15If` | 同 `StrRel15If` |
>
> **检查的结论 (判断).** 新增的三条规则里, `in⁺` 与 `nκ⁺` 不比较任何两个下标或世界; `rk⁺` 的每一对都带与 `StrRel15If` 相同的字面证据. 没有裸下标上的律.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
module OCF.Align.StrRel16If (Λ : H) (lΛ : LgH Λ) where

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; StH; ss; sl; sL; Vs; D; outS;
  n0; n1; _⨾_; nl; ni; nκ; nw; NZ; AccY; ⊲ᴴ↑)
open import OCF.Align.HtFeedClosed using (module At)
open import OCF.Align.StrRel11Rk Λ lΛ using (_⊑∞_)
open import OCF.Align.StrRel12Al using (AP; CP)
open import OCF.Align.StrRel12Sem Λ lΛ using (Top)
open import OCF.Align.StrRel14If Λ lΛ using (LoX; RelX; BelowX; CPᴸ)
open import OCF.Align.StrRel14J Λ lΛ using (NE)
open import OCF.Align.StrRel15If Λ lΛ using (TX; J²; HAW²)

module P = At Λ lΛ
open P using (Tg; tg; wm; tm; lm; St; Df; yc; d; z; cv; _⊕⟨_⟩_; Run; Ig; LW; Rk; rkT; RKi; kk; rise; keep)
```

## 1 分量, 与 `rk⁺` 的 (旧关系) 前提

`In y x`: $y$ 是 $x$ 的分量, 同一层同一世界; 只沿 `⨾` 的两边与 `nl` 的项走 (不进 `ni`, `nκ`, `nw`).

```agda
data In {L : H} {V : A} (y : D L V) : D L V → Set where
  here : In y y
  inL  : ∀ {a b} → In y a → In y (a ⨾ b)
  inR  : ∀ {a b} → In y b → In y (a ⨾ b)
  inE  : ∀ {e : ℕ → D L V} n → In y (e n) → In y (nl e)
```

`RkPre`: 一对节点运行的前提, 同 `StrRel15Node.Red².node-red²` 的前提加 `NodeSound²` 的分支前提, 全部是旧关系.

```agda
RkPre : ∀ {ly ly′ W₀ W₀′ k k′ W W′} {lW₀ : Lg W₀} {lW₀′ : Lg W₀′} (r : StH W₀ k ly) (r′ : StH W₀′ k′ ly′)
        (u : ∀ {W₁} → W₀ ⊲ W₁ → Lg W₁ → Vs ly r W₁ → D ly W₁) (u′ : ∀ {W₁} → W₀′ ⊲ W₁ → Lg W₁ → Vs ly′ r′ W₁ → D ly′ W₁)
        (lW : Lg W) (lW′ : Lg W′) (q₀ : W₀ ⊲ W) (q₀′ : W₀′ ⊲ W′) (A₀ : Ig ly W) (A₀′ : Ig ly′ W′)
        (w : D ly W) (w′ : D ly′ W′) (Y : St W) (Y′ : St W′) → Set
RkPre {ly} {ly′} {k = k} {k′} {lW₀ = lW₀} {lW₀′} r r′ u u′ lW lW′ q₀ q₀′ A₀ A₀′ w w′ Y Y′ =
  CP lW₀ lW₀′ q₀ lW q₀′ lW′ × (k ⊑∞ k′) ×
  (∀ {c c′} (p : _ ⊲ c) (p′ : _ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CP lW₀ lW₀′ p lc p′ lc′ →
     ∀ y y′ → BelowX ly ly′ r r′ lc lc′ y y′ → RelX ly ly′ lc lc′ (u p lc y) (u′ p′ lc′ y′)) ×
  HAW² ly ly′ lW lW′ A₀ A₀′ × RelX ly ly′ lW lW′ w w′ × J² lW lW′ Y Y′
```

## 2 扩充的异质关系 `RelX⁺`

```agda
data LeX⁺ (L L′ : H) (Lo : LoX L L′) : ∀ {V V′} → Lg V → Lg V′ → D L V → D L′ V′ → Set where
  n0⁺ : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x′ : D L′ V′} → LeX⁺ L L′ Lo lV lV′ n0 x′
  n1⁺ : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} → LeX⁺ L L′ Lo lV lV′ n1 n1
  ⨾⁺  : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x y : D L V} {x′ y′ : D L′ V′} →
        LeX⁺ L L′ Lo lV lV′ x x′ → LeX⁺ L L′ Lo lV lV′ y y′ → LeX⁺ L L′ Lo lV lV′ (x ⨾ y) (x′ ⨾ y′)
  nl⁺ : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {d₁ : ℕ → D L V} {d₁′ : ℕ → D L′ V′} →
        (∀ n → LeX⁺ L L′ Lo lV lV′ (d₁ n) (d₁′ n)) → LeX⁺ L L′ Lo lV lV′ (nl d₁) (nl d₁′)
  pr⁺ : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {x′ y′ : D L′ V′} →
        LeX⁺ L L′ Lo lV lV′ x x′ → LeX⁺ L L′ Lo lV lV′ x (x′ ⨾ y′)
  nw⁺ : ∀ {V₀ V₀′ V V′} {lV₀ : Lg V₀} {lV₀′ : Lg V₀′} {lV : Lg V} {lV′ : Lg V′} {p : V₀ ⊲ V} {p′ : V₀′ ⊲ V′}
          {x : D L V₀} {x′ : D L′ V₀′} →
        AP lV₀ lV₀′ p lV p′ lV′ → LeX⁺ L L′ Lo lV₀ lV₀′ x x′ → LeX⁺ L L′ Lo lV lV′ (nw p x) (nw p′ x′)
  ni⁺ : ∀ {V V′ k k′} {lV : Lg V} {lV′ : Lg V′} {r : StH V k L} {r′ : StH V′ k′ L′}
          {u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′} {u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ r′ W′ → D L′ W′} →
        k ⊑∞ k′ →
        (∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CP lV lV′ p lc p′ lc′ →
           ∀ y y′ → Lo r r′ lc lc′ y y′ → LeX⁺ L L′ Lo lc lc′ (u p lc y) (u′ p′ lc′ y′)) →
        LeX⁺ L L′ Lo lV lV′ (ni r u) (ni r′ u′)
  κ⁺  : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {zz : NZ L} {zz′ : NZ L′}
          {u : ∀ {c} → V ⊲ c → Lg c → D L c} {u′ : ∀ {c} → V′ ⊲ c → Lg c → D L′ c} →
        (∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CPᴸ lV lV′ p lc p′ lc′ →
           LeX⁺ L L′ Lo lc lc′ (u p lc) (u′ p′ lc′)) →
        LeX⁺ L L′ Lo lV lV′ (nκ zz u) (nκ zz′ u′)
  -- 新 1: 节点 ≤ 链极限 (一般形: 在某个分量之下)
  in⁺ : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {y′ x′ : D L′ V′} →
        LeX⁺ L L′ Lo lV lV′ x y′ → In y′ x′ → LeX⁺ L L′ Lo lV lV′ x x′
  -- 新 2: 链极限 ≤ 节点 (RKi 的 rise 句对 keep 句, 前提用旧关系)
  rk⁺ : ∀ {ly ly′ W₀ W₀′ k k′ W W′ m m′} {lW₀ : Lg W₀} {lW₀′ : Lg W₀′} (r : StH W₀ k ly) (r′ : StH W₀′ k′ ly′)
          {u : ∀ {W₁} → W₀ ⊲ W₁ → Lg W₁ → Vs ly r W₁ → D ly W₁} {u′ : ∀ {W₁} → W₀′ ⊲ W₁ → Lg W₁ → Vs ly′ r′ W₁ → D ly′ W₁}
          (lW : Lg W) (lW′ : Lg W′) (ac : AccY ly) (ac₁ : AccY k) (ac′ : AccY ly′) (ac₁′ : AccY k′)
          (q₀ : W₀ ⊲ W) (q₀′ : W₀′ ⊲ W′) (ll : LW ly W) (ll′ : LW ly′ W′) (A₀ : Ig ly W) (A₀′ : Ig ly′ W′)
          (w : D ly W) (w′ : D ly′ W′) (Y : St W) (Y′ : St W′) (T : Tg W L m) (T′ : Tg W′ L′ m′) (R′ : StH m′ k′ L′) →
        RkPre {lW₀ = lW₀} {lW₀′} r r′ u u′ lW lW′ q₀ q₀′ A₀ A₀′ w w′ Y Y′ → TX lW lW′ T T′ →
        rkT (⊲ᴴ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T) ≡ rise → rkT (⊲ᴴ↑ (wm T′) (kk r′ q₀′ ll′)) (tm T′) (lm T′) ≡ keep R′ →
        LeX⁺ L L′ Lo (lm T) (lm T′) (RKi ac ac₁ r u q₀ lW ll A₀ w Y T rise) (RKi ac′ ac₁′ r′ u′ q₀′ lW′ ll′ A₀′ w′ Y′ T′ (keep R′))
  -- 新 3: ni 对 nκ (自身世界上的分支)
  nκ⁺ : ∀ {V V′ k} {lV : Lg V} {lV′ : Lg V′} {r : StH V k L} {u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′}
          {zz′ : NZ L′} {v′ : ∀ {c} → V′ ⊲ c → Lg c → D L′ c} →
        LeX⁺ L L′ Lo lV lV′ (ni r u) (v′ C.self lV′) → LeX⁺ L L′ Lo lV lV′ (ni r u) (nκ zz′ v′)

RelX⁺   : ∀ L L′ {V V′} → Lg V → Lg V′ → D L V → D L′ V′ → Set
BelowX⁺ : ∀ L L′ → LoX L L′
RelSX⁺  : ∀ L {V k} → StH V k L → ∀ k′ {c c′} → Lg c → Lg c′ → D k c → D k′ c′ → Set
RelAtX⁺ : ∀ b {V k} → k ⊲[ V ] b → ∀ k′ {c c′} → Lg c → Lg c′ → D k c → D k′ c′ → Set

RelX⁺ L L′ = LeX⁺ L L′ (BelowX⁺ L L′)
BelowX⁺ L L′ {k′ = k′} r r′ lc lc′ y y′ = RelSX⁺ L r k′ lc lc′ (outS r y) (outS r′ y′)
RelSX⁺ (hs b) (ss P) = RelAtX⁺ b P
RelSX⁺ (hl f) (sl n P) = RelAtX⁺ (f n) P
RelSX⁺ (hΩ g) (sL e P) = RelAtX⁺ (g _) P
RelAtX⁺ b hself k′ = RelX⁺ b k′
RelAtX⁺ (hs b) (hsuc P) = RelAtX⁺ b P
RelAtX⁺ (hl f) (hlim n P) = RelAtX⁺ (f n) P
RelAtX⁺ (hΩ g) (hLim e P) = RelAtX⁺ (g _) P

-- 旧关系嵌进新关系 (类型)
Emb : Set
Emb = ∀ L L′ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {x′ : D L′ V′} → RelX L L′ lV lV′ x x′ → RelX⁺ L L′ lV lV′ x x′
```

## 3 输出关系, 状态关系, 状态不变量, 律

```agda
OA²⁺ : ∀ {W W′} → Lg W → Lg W′ → Df W → Df W′ → Set
OA²⁺ {W} {W′} lW lW′ Δ Δ′ =
  ∀ {t t′ m m′} (T : Tg W t m) (T′ : Tg W′ t′ m′) → TX lW lW′ T T′ → RelX⁺ t t′ (lm T) (lm T′) (yc Δ T) (yc Δ′ T′)

R²⁺ : ∀ {W W′} → Lg W → Lg W′ → St W → St W′ → Set
R²⁺ lW lW′ Y Y′ = OA²⁺ lW lW′ (d Y) (d Y′) × RelX⁺ hz hz lW lW′ (z Y) (z Y′)

J²⁺ : ∀ {W W′} → Lg W → Lg W′ → St W → St W′ → Set
J²⁺ lW lW′ Y Y′ = R²⁺ lW lW′ Y Y′ × (NE Y × NE Y′)

Law⊕⁺ : Set
Law⊕⁺ = ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} → Top lW lW′ → ∀ (Y : St W) (Y′ : St W′) (Δ : Df W) (Δ′ : Df W′) →
        J²⁺ lW lW′ Y Y′ → OA²⁺ lW lW′ Δ Δ′ → J²⁺ lW lW′ (Y ⊕⟨ lW ⟩ Δ) (Y′ ⊕⟨ lW′ ⟩ Δ′)

Lawcv⁺ : Set
Lawcv⁺ = ∀ {W W′ W₂ W₂′} {lW : Lg W} {lW′ : Lg W′} {q : W ⊲ W₂} {lW₂ : Lg W₂} {q′ : W′ ⊲ W₂′} {lW₂′ : Lg W₂′} →
         AP lW lW′ q lW₂ q′ lW₂′ → ∀ (Y : St W) (Y′ : St W′) → J²⁺ lW lW′ Y Y′ → J²⁺ lW₂ lW₂′ (cv q Y) (cv q′ Y′)
```

## 4 动作前提与语义

```agda
HAW²⁺ : ∀ L L′ {W W′} → Lg W → Lg W′ → Ig L W → Ig L′ W′ → Set
HAW²⁺ L L′ {W} {W′} lW lW′ A₀ A₀′ =
  ∀ {W₁ W₁′} (p : W ⊲ W₁) (p′ : W′ ⊲ W₁′) (lW₁ : Lg W₁) (lW₁′ : Lg W₁′) → CP lW lW′ p lW₁ p′ lW₁′ →
  ∀ w w′ → RelX⁺ L L′ lW₁ lW₁′ w w′ → ∀ (Y : St W₁) (Y′ : St W₁′) → J²⁺ lW₁ lW₁′ Y Y′ →
  OA²⁺ lW₁ lW₁′ (A₀ p lW₁ w Y) (A₀′ p′ lW₁′ w′ Y′)

SemX²⁺ : ∀ L L′ {V V′} → Lg V → Lg V′ → D L V → D L′ V′ → Set
SemX²⁺ L L′ {V} {V′} lV lV′ x x′ =
  ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac′ : AccY L′) (ll : LW L W) (ll′ : LW L′ W′)
    (q : V ⊲ W) (q′ : V′ ⊲ W′) → CP lV lV′ q lW q′ lW′ →
  ∀ (A₀ : Ig L W) (A₀′ : Ig L′ W′) → HAW²⁺ L L′ lW lW′ A₀ A₀′ →
  ∀ w w′ → RelX⁺ L L′ lW lW′ w w′ → ∀ (Y : St W) (Y′ : St W′) → J²⁺ lW lW′ Y Y′ →
  OA²⁺ lW lW′ (Run ac x q lW ll A₀ w Y) (Run ac′ x′ q′ lW′ ll′ A₀′ w′ Y′)
```

## 5 节点义务与节点可靠性

```agda
module NodeObl²⁺ {L L′ V V′ k k′} {lV : Lg V} {lV′ : Lg V′} (r : StH V k L) (r′ : StH V′ k′ L′)
                 (u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′) (u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ r′ W′ → D L′ W′)
                 {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac₁ : AccY k) (ac′ : AccY L′) (ac₁′ : AccY k′)
                 (q₀ : V ⊲ W) (q₀′ : V′ ⊲ W′) (ll : LW L W) (ll′ : LW L′ W′) (A₀ : Ig L W) (A₀′ : Ig L′ W′)
                 (w : D L W) (w′ : D L′ W′) (Y : St W) (Y′ : St W′) where
  rkL : ∀ {t m} → Tg W t m → Rk k t m
  rkL T = rkT (⊲ᴴ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T)
  rkR : ∀ {t′ m′} → Tg W′ t′ m′ → Rk k′ t′ m′
  rkR T′ = rkT (⊲ᴴ↑ (wm T′) (kk r′ q₀′ ll′)) (tm T′) (lm T′)

  Out²⁺ : ∀ {t t′ m m′} (T : Tg W t m) (T′ : Tg W′ t′ m′) → Rk k t m → Rk k′ t′ m′ → Set
  Out²⁺ T T′ rk rk′ = RelX⁺ _ _ (lm T) (lm T′) (RKi ac ac₁ r u q₀ lW ll A₀ w Y T rk) (RKi ac′ ac₁′ r′ u′ q₀′ lW′ ll′ A₀′ w′ Y′ T′ rk′)

  OblRR²⁺ OblKK²⁺ OblKR²⁺ OblRK²⁺ : Set
  OblRR²⁺ = ∀ {t t′ m m′} (T : Tg W t m) (T′ : Tg W′ t′ m′) → TX lW lW′ T T′ → rkL T ≡ rise → rkR T′ ≡ rise → Out²⁺ T T′ rise rise
  OblKK²⁺ = ∀ {t t′ m m′} (T : Tg W t m) (T′ : Tg W′ t′ m′) → TX lW lW′ T T′ → ∀ R R′ → rkL T ≡ keep R → rkR T′ ≡ keep R′ →
            Out²⁺ T T′ (keep R) (keep R′)
  OblKR²⁺ = ∀ {t t′ m m′} (T : Tg W t m) (T′ : Tg W′ t′ m′) → TX lW lW′ T T′ → ∀ R → rkL T ≡ keep R → rkR T′ ≡ rise →
            Out²⁺ T T′ (keep R) rise
  OblRK²⁺ = ∀ {t t′ m m′} (T : Tg W t m) (T′ : Tg W′ t′ m′) → TX lW lW′ T T′ → ∀ R′ → rkL T ≡ rise → rkR T′ ≡ keep R′ →
            Out²⁺ T T′ rise (keep R′)

NodeSound²⁺ : Set
NodeSound²⁺ = ∀ {L L′ V V′ k k′} {lV : Lg V} {lV′ : Lg V′} (r : StH V k L) (r′ : StH V′ k′ L′)
                {u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′} {u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ r′ W′ → D L′ W′} →
              k ⊑∞ k′ →
              (∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CP lV lV′ p lc p′ lc′ →
                 ∀ y y′ → BelowX⁺ L L′ r r′ lc lc′ y y′ → RelX⁺ L L′ lc lc′ (u p lc y) (u′ p′ lc′ y′)) →
              SemX²⁺ L L′ lV lV′ (ni r u) (ni r′ u′)

NodeSound²⁺₀ : Set
NodeSound²⁺₀ = ∀ {L L′ V V′ k′} {lV : Lg V} {lV′ : Lg V′} (r : StH V hz L) (r′ : StH V′ k′ L′)
                 {u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′} {u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ r′ W′ → D L′ W′} →
               hz ⊑∞ k′ →
               (∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CP lV lV′ p lc p′ lc′ →
                  ∀ y y′ → BelowX⁺ L L′ r r′ lc lc′ y y′ → RelX⁺ L L′ lc lc′ (u p lc y) (u′ p′ lc′ y′)) →
               SemX²⁺ L L′ lV lV′ (ni r u) (ni r′ u′)
```

## 6 (增补) `rk⁺` 的可靠性 (类型)

`RkSound L L′`: `rk⁺` 的每个实例 (结论层 $L$, $L'$) 满足 `SemX²⁺`. `RkSound₀ L′` 是左层为 $0$ 的特例 (`StrRel16Val` 的决定性实验是它的一个实例的值的那一半). §1–§5 不改.

```agda
RkSound : H → H → Set
RkSound L L′ =
  ∀ {ly ly′ W₀ W₀′ k k′ W W′ m m′} {lW₀ : Lg W₀} {lW₀′ : Lg W₀′} (r : StH W₀ k ly) (r′ : StH W₀′ k′ ly′)
    {u : ∀ {W₁} → W₀ ⊲ W₁ → Lg W₁ → Vs ly r W₁ → D ly W₁} {u′ : ∀ {W₁} → W₀′ ⊲ W₁ → Lg W₁ → Vs ly′ r′ W₁ → D ly′ W₁}
    (lW : Lg W) (lW′ : Lg W′) (ac : AccY ly) (ac₁ : AccY k) (ac′ : AccY ly′) (ac₁′ : AccY k′)
    (q₀ : W₀ ⊲ W) (q₀′ : W₀′ ⊲ W′) (ll : LW ly W) (ll′ : LW ly′ W′) (A₀ : Ig ly W) (A₀′ : Ig ly′ W′)
    (w : D ly W) (w′ : D ly′ W′) (Y : St W) (Y′ : St W′) (T : Tg W L m) (T′ : Tg W′ L′ m′) (R′ : StH m′ k′ L′) →
  RkPre {lW₀ = lW₀} {lW₀′} r r′ u u′ lW lW′ q₀ q₀′ A₀ A₀′ w w′ Y Y′ → TX lW lW′ T T′ →
  rkT (⊲ᴴ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T) ≡ rise → rkT (⊲ᴴ↑ (wm T′) (kk r′ q₀′ ll′)) (tm T′) (lm T′) ≡ keep R′ →
  SemX²⁺ L L′ (lm T) (lm T′) (RKi ac ac₁ r u q₀ lW ll A₀ w Y T rise) (RKi ac′ ac₁′ r′ u′ q₀′ lW′ ll′ A₀′ w′ Y′ T′ (keep R′))

RkSound₀ : H → Set
RkSound₀ L′ = RkSound hz L′
```

## 变更记录

- 2026-11-05 11:28: 定稿 (首次编译通过, 退出码 0).
- 2026-11-05 11:55: 增补 §6 `RkSound`, `RkSound₀` (`rk⁺` 的可靠性的类型). 理由: 构造一路的左层为 $0$ 的语义 (`StrRel16Sem.semX0⁺`) 以它为条件. §1–§5 未改.
- 2026-11-05 12:40: 补注 (文字, 不改定义). (i) 文件头 "为什么 `in⁺` 不撞 `¬laterV`" 一段说的是**可推导性**: `¬laterV` 的那一对在 `RelX⁺` 里推不出 (`StrRel16Kr.¬laterPair`), 与 `NE` 无关; `in⁺` 的可靠性也不用 `NE` (`StrRel16Sem.sem-in`; 否定一路的 `sem-in⁺` 同). `NE` 只在实例的推导里用到 (`StrRel16Kr.krAt`: 状态读数含 $\Omega_1$ 的节点). (ii) 否定一路 (`NegSR16`) 否定了 `nκ⁺` 的可靠性 (主审转告; 本文不改). (iii) 定稿时间: 首稿写的 "11:40" 是写文件时预填的时刻, 首次编译通过在 11:28, 随即 (在任何别的改动之前) 改为 11:28.
