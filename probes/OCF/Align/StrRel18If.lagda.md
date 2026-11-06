# 结构关系, 第十八轮: 接口 (只放记录与类型)

> **接口定稿 2026-11-05 14:22.** 之后只增不改, 改动写在文末的变更记录. 构造一路 (前缀 `StrRel18`) 与否定一路 (前缀 `NegSR18`) 共用本文. 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 只有定义 (数据类型, 类型别名), 没有定理.
>
> 作者选定 "B1: 试修补 (a)(c)" (修补方向见 `NegSR17` §5). 内容:
>
> 1. **(a) 不读第 $0$ 层累计的动作** (§1). `NoZ lW A₀`: 动作在一切延长的世界上, 把状态的累计 `z` 换成任意的树, 每个目标上的输出字面地 (命题相等) 不变. 律 **`AiNoZ`**: 节点的分支动作 `Ai` 继承 `NoZ`. `HAWᶻ`, `SemTᶻ`: 动作限制为 `NoZ` 的 `HAW²⁺`, `SemT`. **`RkSoundTᶻ`**: `StrRel17If.RkSoundT` 加 "产生时两边的动作都是 `NoZ`", 结论的语义也只用 `NoZ` 的再折叠动作.
> 2. **(c) 保留分支运行时的状态** (§2). `KSt …`: `RKi` 的 keep 句里, 保留输出的分支在世界 $W_1$ 上收到输入 $z$ 后, 分支的树运行时的状态 (`BNi` 的字面: `cv p Y ⊕ Run z …`). 三个变体 (`KV`): `kJ` (`DomK`): `J²⁺ (左边产生时的状态) (右边的 KSt)`, 对一切路径与输入; `kD` (`DomKᵈ`): 只比差分量 (`OA²⁺` 加两边 `NE`); `kZ` (`DomKz`): 左边产生时的**累计**被右边 `KSt` 在第 $0$ 层目标上的**读数** `RelX⁺ hz hz` 支配 (累计被 `cv` 清掉, 读数不被清掉). **`RkSoundTK v`**: `RkSoundT` 加 (c) 的前提 (变体 $v$), 结论同 `RkSoundT` (`SemT … (DomL …)`).
> 3. **`Up` 规则** (§3, `StrRel17Obs.Up` 的一般形). `UpClosed R`: 关系族 $R$ 对 "同一节点, 同一组参数: $x\le$ 它在低目标 $T$ 上的上升输出 ⇒ $x\le$ 它在高目标 $T'$ 上的保留输出" 封闭. `OAR`, `SemR`: 输出关系换成任意关系族 $R$ 的输出关系与语义 (前提仍是 `HAW²⁺`, `J²⁺`, `RelX⁺`). `UpSound R Ok`: `SemR` 对 `Up` 的封闭性. `Trans00`: `RelX⁺ hz hz` 的传递性 (`Up` 的可靠性的一个来源, `StrRel17` 接手清单第 2 项).
>
> ## 律的定义域 (逐条检查, 依 `AGENTS.md` "律带公共上界")
>
> | 律 / 字段 | 被比较的一对 | 字面证据 | 只有值的部分 |
> |---|---|---|---|
> | `NoZ` | 同一动作在同一世界 $W_1$ 上的两个状态 (只差累计) | 路径 $p:W\lhd W_1$; 两个状态的差分量字面相同 (`st (d Y) z′`) | 无 |
> | `AiNoZ` | 一个节点, 一个动作 | 节点的路径 $q_0$, 层的位置 `hk`, `ll` (同 `HtFeedFold.Ai`) | 无 |
> | `HAWᶻ`, `SemTᶻ` | 同 `HAW²⁺`, `SemT` | 同 | 同 (`CP` 的 $W\le W'$) |
> | `RkSoundTᶻ` | 同 `RkSoundT` | 同 | 同 |
> | `KSt` | 一个节点, 一个产生状态, 一条路径 $p$, 一个输入 | 路径 $p$ (字面), 同 `BNi` | 无 |
> | `DomK` | 左边产生时的世界 $W$ 对右边分支世界 $W_1$ | `J²⁺` 的 `TX` 对 (`CP`) | `CP` 的 $W\le W_1$ |
> | `DomKᵈ` | 同上, 只比差分量 | 同上 | 同上 |
> | `DomKz` | 左边的累计 (世界 $W$) 对右边分支世界 $W_1$ 的第 $0$ 层读数 | `RelX⁺ hz hz` (第 $0$ 层没有节点, 没有 `nκ`) | 无 |
> | `RkSoundTK` | 同 `RkSoundT`, 加上面一项 | 同 | 同 |
> | `UpClosed` | 同一节点在同一世界 $W$ 的两个目标 $T$, $T'$ 上的两个输出 | 两个目标的种类字面地由 `rkT` 给出 (`≡ rise`, `≡ keep R′`); 不比较两个目标 | 无 |
> | `OAR`, `SemR` | 同 `OA²⁺`, `SemX²⁺` | 同 | 同 |
> | `UpSound` | 同 `UpClosed` 加 `SemR` | 同 | 同 |
> | `Trans00` | 三个第 $0$ 层的树 (世界 $V,V',V''$) | 两段 `RelX⁺ hz hz` 的推导 | 无 |
>
> **检查的结论 (判断).** 新增的类型里没有裸下标上的律: `NoZ` 只在同一世界里换累计; (c) 的三个变体是 `J²⁺`/`OA²⁺`/`RelX⁺` 的实例, 被比较的世界对由路径 $p$ 字面连接 ($W_1$ 是右边的目标世界之上); `UpClosed` 只看同一个节点的同一组参数, 两个目标的种类由 `rkT` 的字面给出.
>
> **范围 (判断, 写在这里, 不当作已解决).** (i) `NoZ` 是字面的 (命题相等), 比 "值不依赖累计" 强; 它的否定 (例如 `AiNoZ` 不成立) 只说输出字面依赖累计, 不直接说值不同. (ii) `DomK`/`DomKᵈ`/`DomKz` 对一切输入 $z$ 量化; 只对再折叠里实际出现的输入量化的版本没有写. (iii) `Up` 的输出关系是任意的关系族 $R$; 含 `Up` 规则的具体关系 (`RelX⁺` 加一条构造子) 没有写成数据类型.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
module OCF.Align.StrRel18If (Λ : H) (lΛ : LgH Λ) where

open import Data.Product using (Σ; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (hz; StH; Vs; D; D₀; n0; AccY; ⊲ᴴ↑)
open import OCF.Align.StrRel12Al using (CP)
open import OCF.Align.StrRel14J Λ lΛ using (NE)
open import OCF.Align.StrRel15If Λ lΛ using (TX)
open import OCF.Align.StrRel16If Λ lΛ using (module P; RelX⁺; OA²⁺; J²⁺; HAW²⁺; RkPre)
open import OCF.Align.StrRel17If Λ lΛ using (Cond; SemT; DomL)

open P using (Tg; tg; wm; tm; lm; τ₀; St; st; Df; d; z; yc; cv; _⊕⟨_⟩_; Run; Ig; Ig↾; LW; Ai; rkT; RKi; kk; rise; keep)
```

## 1 (a) 不读第 $0$ 层累计的动作

```agda
NoZ : ∀ {L W} → Lg W → Ig L W → Set
NoZ {L} {W} lW A₀ =
  ∀ {W₁} (p : W ⊲ W₁) (lW₁ : Lg W₁) (w : D L W₁) (Y : St W₁) (z′ : D₀ W₁) {t m} (T : Tg W₁ t m) →
  yc (A₀ p lW₁ w Y) T ≡ yc (A₀ p lW₁ w (st (d Y) z′)) T

-- 律: 节点的分支动作继承 NoZ
AiNoZ : Set
AiNoZ = ∀ {ly W₀ W k} (ac : AccY ly) (ac₁ : AccY k) (r : StH W₀ k ly) (u : ∀ {W′} → W₀ ⊲ W′ → Lg W′ → Vs ly r W′ → D ly W′)
          (q₀ : W₀ ⊲ W) (hk : LW k W) (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (lW : Lg W) →
        NoZ lW A₀ → NoZ lW (Ai ac ac₁ r u q₀ hk ll A₀ w)

HAWᶻ : ∀ L L′ {W W′} → Lg W → Lg W′ → Ig L W → Ig L′ W′ → Set
HAWᶻ L L′ lW lW′ A₀ A₀′ = HAW²⁺ L L′ lW lW′ A₀ A₀′ × (NoZ lW A₀ × NoZ lW′ A₀′)

SemTᶻ : ∀ L L′ {V V′} → Lg V → Lg V′ → Cond → D L V → D L′ V′ → Set
SemTᶻ L L′ {V} {V′} lV lV′ Ok x x′ =
  ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac′ : AccY L′) (ll : LW L W) (ll′ : LW L′ W′)
    (q : V ⊲ W) (q′ : V′ ⊲ W′) → CP lV lV′ q lW q′ lW′ →
  ∀ (A₀ : Ig L W) (A₀′ : Ig L′ W′) → HAWᶻ L L′ lW lW′ A₀ A₀′ →
  ∀ w w′ → RelX⁺ L L′ lW lW′ w w′ → ∀ (Y : St W) (Y′ : St W′) → J²⁺ lW lW′ Y Y′ → Ok lW lW′ Y Y′ →
  OA²⁺ lW lW′ (Run ac x q lW ll A₀ w Y) (Run ac′ x′ q′ lW′ ll′ A₀′ w′ Y′)

RkSoundTᶻ : H → H → Set
RkSoundTᶻ L L′ =
  ∀ {ly ly′ W₀ W₀′ k k′ W W′ m m′} {lW₀ : Lg W₀} {lW₀′ : Lg W₀′} (r : StH W₀ k ly) (r′ : StH W₀′ k′ ly′)
    {u : ∀ {W₁} → W₀ ⊲ W₁ → Lg W₁ → Vs ly r W₁ → D ly W₁} {u′ : ∀ {W₁} → W₀′ ⊲ W₁ → Lg W₁ → Vs ly′ r′ W₁ → D ly′ W₁}
    (lW : Lg W) (lW′ : Lg W′) (ac : AccY ly) (ac₁ : AccY k) (ac′ : AccY ly′) (ac₁′ : AccY k′)
    (q₀ : W₀ ⊲ W) (q₀′ : W₀′ ⊲ W′) (ll : LW ly W) (ll′ : LW ly′ W′) (A₀ : Ig ly W) (A₀′ : Ig ly′ W′)
    (w : D ly W) (w′ : D ly′ W′) (Y : St W) (Y′ : St W′) (T : Tg W L m) (T′ : Tg W′ L′ m′) (R′ : StH m′ k′ L′) →
  RkPre {lW₀ = lW₀} {lW₀′} r r′ u u′ lW lW′ q₀ q₀′ A₀ A₀′ w w′ Y Y′ → TX lW lW′ T T′ →
  rkT (⊲ᴴ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T) ≡ rise → rkT (⊲ᴴ↑ (wm T′) (kk r′ q₀′ ll′)) (tm T′) (lm T′) ≡ keep R′ →
  NoZ lW A₀ → NoZ lW′ A₀′ →
  SemTᶻ L L′ (lm T) (lm T′) (DomL lW Y)
    (RKi ac ac₁ r u q₀ lW ll A₀ w Y T rise) (RKi ac′ ac₁′ r′ u′ q₀′ lW′ ll′ A₀′ w′ Y′ T′ (keep R′))
```

## 2 (c) 保留分支运行时的状态

`KSt`: 节点 $r$ (以 $Y$ 产生) 的保留输出的分支, 在世界 $W_1$ (路径 $p$) 上收到输入 $z$ 时, 分支的树运行的状态. 即 `HtFeedFold.BNi` 传给 `Ai` 的状态.

```agda
KSt : ∀ {ly W₀ W k W₁} (ac : AccY ly) (ac₁ : AccY k) (r : StH W₀ k ly) (u : ∀ {W′} → W₀ ⊲ W′ → Lg W′ → Vs ly r W′ → D ly W′)
        (q₀ : W₀ ⊲ W) (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) (hk : LW k W) (p : W ⊲ W₁) (lW₁ : Lg W₁) (y : D k W₁) → St W₁
KSt ac ac₁ r u q₀ ll A₀ w Y hk p lW₁ y =
  cv p Y ⊕⟨ lW₁ ⟩ Run ac₁ y C.self lW₁ (⊲ᴴ↑ p hk) (Ig↾ p (Ai ac ac₁ r u q₀ hk ll A₀ w)) n0 (cv p Y)

data KV : Set where
  kJ kD kZ : KV

-- 左边产生时的状态 Y (世界 W) 与右边保留输出的分支运行时的状态 (目标 T′ 的世界之上)
DomKv : KV → ∀ {W ly′ W₀′ W′ k′ t′ m′} → Lg W → St W →
        (ac′ : AccY ly′) (ac₁′ : AccY k′) (r′ : StH W₀′ k′ ly′) (u′ : ∀ {W₁} → W₀′ ⊲ W₁ → Lg W₁ → Vs ly′ r′ W₁ → D ly′ W₁)
        (q₀′ : W₀′ ⊲ W′) (ll′ : LW ly′ W′) (A₀′ : Ig ly′ W′) (w′ : D ly′ W′) (Y′ : St W′) (T′ : Tg W′ t′ m′) → Set
DomKv kJ lW Y ac′ ac₁′ r′ u′ q₀′ ll′ A₀′ w′ Y′ T′ =
  ∀ {W₁} (p : _ ⊲ W₁) (lW₁ : Lg W₁) (y : D _ W₁) →
  J²⁺ lW lW₁ Y (KSt ac′ ac₁′ r′ u′ q₀′ ll′ A₀′ w′ Y′ (kk r′ q₀′ ll′) (⊲-tr (wm T′) p) lW₁ y)
DomKv kD lW Y ac′ ac₁′ r′ u′ q₀′ ll′ A₀′ w′ Y′ T′ =
  ∀ {W₁} (p : _ ⊲ W₁) (lW₁ : Lg W₁) (y : D _ W₁) →
  OA²⁺ lW lW₁ (d Y) (d (KSt ac′ ac₁′ r′ u′ q₀′ ll′ A₀′ w′ Y′ (kk r′ q₀′ ll′) (⊲-tr (wm T′) p) lW₁ y)) ×
  (NE Y × NE (KSt ac′ ac₁′ r′ u′ q₀′ ll′ A₀′ w′ Y′ (kk r′ q₀′ ll′) (⊲-tr (wm T′) p) lW₁ y))
DomKv kZ lW Y ac′ ac₁′ r′ u′ q₀′ ll′ A₀′ w′ Y′ T′ =
  ∀ {W₁} (p : _ ⊲ W₁) (lW₁ : Lg W₁) (y : D _ W₁) →
  RelX⁺ hz hz lW lW₁ (z Y) (yc (d (KSt ac′ ac₁′ r′ u′ q₀′ ll′ A₀′ w′ Y′ (kk r′ q₀′ ll′) (⊲-tr (wm T′) p) lW₁ y)) (τ₀ lW₁))

RkSoundTK : KV → H → H → Set
RkSoundTK v L L′ =
  ∀ {ly ly′ W₀ W₀′ k k′ W W′ m m′} {lW₀ : Lg W₀} {lW₀′ : Lg W₀′} (r : StH W₀ k ly) (r′ : StH W₀′ k′ ly′)
    {u : ∀ {W₁} → W₀ ⊲ W₁ → Lg W₁ → Vs ly r W₁ → D ly W₁} {u′ : ∀ {W₁} → W₀′ ⊲ W₁ → Lg W₁ → Vs ly′ r′ W₁ → D ly′ W₁}
    (lW : Lg W) (lW′ : Lg W′) (ac : AccY ly) (ac₁ : AccY k) (ac′ : AccY ly′) (ac₁′ : AccY k′)
    (q₀ : W₀ ⊲ W) (q₀′ : W₀′ ⊲ W′) (ll : LW ly W) (ll′ : LW ly′ W′) (A₀ : Ig ly W) (A₀′ : Ig ly′ W′)
    (w : D ly W) (w′ : D ly′ W′) (Y : St W) (Y′ : St W′) (T : Tg W L m) (T′ : Tg W′ L′ m′) (R′ : StH m′ k′ L′) →
  RkPre {lW₀ = lW₀} {lW₀′} r r′ u u′ lW lW′ q₀ q₀′ A₀ A₀′ w w′ Y Y′ → TX lW lW′ T T′ →
  rkT (⊲ᴴ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T) ≡ rise → rkT (⊲ᴴ↑ (wm T′) (kk r′ q₀′ ll′)) (tm T′) (lm T′) ≡ keep R′ →
  DomKv v lW Y ac′ ac₁′ r′ u′ q₀′ ll′ A₀′ w′ Y′ T′ →
  SemT L L′ (lm T) (lm T′) (DomL lW Y)
    (RKi ac ac₁ r u q₀ lW ll A₀ w Y T rise) (RKi ac′ ac₁′ r′ u′ q₀′ lW′ ll′ A₀′ w′ Y′ T′ (keep R′))
```

## 3 `Up` 规则, 一般的输出关系, 第 $0$ 层的传递性

```agda
RelT : Set₁
RelT = ∀ L L′ {V V′} → Lg V → Lg V′ → D L V → D L′ V′ → Set

-- 同一节点, 同一组参数: x ≤ 低目标 T 上的上升输出 ⇒ x ≤ 高目标 T′ 上的保留输出
UpClosed : RelT → Set
UpClosed R =
  ∀ {L₀ V} {lV : Lg V} {x : D L₀ V} {ly W₀ k W t t′ m m′} {lW₀ : Lg W₀} (r : StH W₀ k ly)
    {u : ∀ {W₁} → W₀ ⊲ W₁ → Lg W₁ → Vs ly r W₁ → D ly W₁}
    (lW : Lg W) (ac : AccY ly) (ac₁ : AccY k) (q₀ : W₀ ⊲ W) (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W)
    (T : Tg W t m) (T′ : Tg W t′ m′) (R′ : StH m′ k t′) →
  rkT (⊲ᴴ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T) ≡ rise → rkT (⊲ᴴ↑ (wm T′) (kk r q₀ ll)) (tm T′) (lm T′) ≡ keep R′ →
  R L₀ t lV (lm T) x (RKi ac ac₁ r u q₀ lW ll A₀ w Y T rise) →
  R L₀ t′ lV (lm T′) x (RKi ac ac₁ r u q₀ lW ll A₀ w Y T′ (keep R′))

OAR : RelT → ∀ {W W′} → Lg W → Lg W′ → Df W → Df W′ → Set
OAR R {W} {W′} lW lW′ Δ Δ′ =
  ∀ {t t′ m m′} (T : Tg W t m) (T′ : Tg W′ t′ m′) → TX lW lW′ T T′ → R t t′ (lm T) (lm T′) (yc Δ T) (yc Δ′ T′)

SemR : RelT → ∀ L L′ {V V′} → Lg V → Lg V′ → Cond → D L V → D L′ V′ → Set
SemR R L L′ {V} {V′} lV lV′ Ok x x′ =
  ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac′ : AccY L′) (ll : LW L W) (ll′ : LW L′ W′)
    (q : V ⊲ W) (q′ : V′ ⊲ W′) → CP lV lV′ q lW q′ lW′ →
  ∀ (A₀ : Ig L W) (A₀′ : Ig L′ W′) → HAW²⁺ L L′ lW lW′ A₀ A₀′ →
  ∀ w w′ → RelX⁺ L L′ lW lW′ w w′ → ∀ (Y : St W) (Y′ : St W′) → J²⁺ lW lW′ Y Y′ → Ok lW lW′ Y Y′ →
  OAR R lW lW′ (Run ac x q lW ll A₀ w Y) (Run ac′ x′ q′ lW′ ll′ A₀′ w′ Y′)

UpSound : RelT → Cond → Set
UpSound R Ok =
  ∀ {L₀ V} {lV : Lg V} {x : D L₀ V} {ly W₀ k W t t′ m m′} {lW₀ : Lg W₀} (r : StH W₀ k ly)
    {u : ∀ {W₁} → W₀ ⊲ W₁ → Lg W₁ → Vs ly r W₁ → D ly W₁}
    (lW : Lg W) (ac : AccY ly) (ac₁ : AccY k) (q₀ : W₀ ⊲ W) (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W)
    (T : Tg W t m) (T′ : Tg W t′ m′) (R′ : StH m′ k t′) →
  rkT (⊲ᴴ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T) ≡ rise → rkT (⊲ᴴ↑ (wm T′) (kk r q₀ ll)) (tm T′) (lm T′) ≡ keep R′ →
  SemR R L₀ t lV (lm T) Ok x (RKi ac ac₁ r u q₀ lW ll A₀ w Y T rise) →
  SemR R L₀ t′ lV (lm T′) Ok x (RKi ac ac₁ r u q₀ lW ll A₀ w Y T′ (keep R′))

Trans00 : Set
Trans00 = ∀ {V V′ V″} {lV : Lg V} {lV′ : Lg V′} {lV″ : Lg V″} {x : D₀ V} {y : D₀ V′} {x″ : D₀ V″} →
          RelX⁺ hz hz lV lV′ x y → RelX⁺ hz hz lV′ lV″ y x″ → RelX⁺ hz hz lV lV″ x x″
```

## 变更记录

- 2026-11-05 14:22: 定稿 (首次编译通过, 退出码 0).
