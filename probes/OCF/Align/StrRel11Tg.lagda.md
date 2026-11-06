# 结构关系, 第十一轮: 主线折叠上的对齐路径对, 目标对与 `cv`

> 不读记号. 入口 [StrRel11](StrRel11.lagda.md). 在主线折叠 `HtFeedFold` (经 `HtFeedClosed.At Λ lΛ`) 上: 目标是 "世界 $m\ge W$ 加层的位置" (`Tg W t m`), `cv` 只把目标的世界路径接长 (`tg↑`). 本文把 "对齐的路径对" 写成一个记录 `APair` (对齐 `Al`, 底端领先量, 两条 `Lg` 等式, 即 `StrRel9Nw.snd-nwA` 的全部前提), 证明它对 `self` 与路径的复合封闭 (`ap-self`, `ap-tr`). 推论: 只对 **带对齐的目标对** 取读数关系的 `R∀` 经 `cv` 保持 (`cvR`, 对任意读数关系族, 只要 $0$ 在下), 经 `⊕` 保持 (`advR`); `Kp` 的状态 `cv wu Y` 与上下文 `nw wu w` 要的正是目标对的对齐 (`kpR`, `kp-nw`); `Kb` 叠起来的路径 `⊲-tr wu p` 的对齐是目标对与分支对的复合 (`stack`). 与 [StrRel11CvNeg](StrRel11CvNeg.lagda.md) 对照: 同一个 `R∀` 形状在 `SumOneFold` 上经不起 `cv`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
module OCF.Align.StrRel11Tg (Λ : H) (lΛ : LgH Λ) where

open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg; ⊲-tr; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (hz; D; n0; _⨾_; nw)
open import OCF.Align.HtFeedClosed using (module At)
open import OCF.Align.KNestAdm using (Adm; adm-tr)
open import OCF.Align.StrRel4Walk using (Al; aS)
open import OCF.Align.StrRel4Gen using (Al-map; lg-tr; cat; adm-self)

module P = At Λ lΛ
open P using (Tg; tg; wm; tm; lm; tg↑; τ₀; St; Df; yc; d; z; cv; _⊕⟨_⟩_)
```

## 1 对齐的路径对

`APair lV lV′ q lW q′ lW′`: 路径 $q: V\lhd W$, $q': V'\lhd W'$ 在顶端世界 $(W, W')$ 上逐步对齐, 底端有领先量 $\mathrm{Adm}(V,V';W,W')$, 底端的 `Lg` 就是沿路径带下来的那个. 这四件正是 `snd-nwA` 的前提 (那里写成四个参数).

```agda
APair : ∀ {V V′ W W′} → Lg V → Lg V′ → V ⊲ W → Lg W → V′ ⊲ W′ → Lg W′ → Set
APair {V} {V′} {W} {W′} lV lV′ q lW q′ lW′ =
  Al W W′ q lW q′ lW′ × Adm V V′ W W′ × (lV ≡ lg⊲ q lW) × (lV′ ≡ lg⊲ q′ lW′)

ap-self : ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) → APair lW lW′ C.self lW C.self lW′
ap-self {W} {W′} lW lW′ = aS C.self lW′ , adm-self W W′ , refl , refl

eq-tr : ∀ {a b c} (q : a ⊲ b) (r : b ⊲ c) (la : Lg a) (lb : Lg b) (lc : Lg c) →
        la ≡ lg⊲ q lb → lb ≡ lg⊲ r lc → la ≡ lg⊲ (⊲-tr q r) lc
eq-tr q r la lb lc e e′ = trans e (trans (cong (lg⊲ q) e′) (sym (lg-tr q r lc)))

ap-tr : ∀ {V V′ W W′ M M′} {lV : Lg V} {lV′ : Lg V′} {q : V ⊲ W} {lW : Lg W} {q′ : V′ ⊲ W′} {lW′ : Lg W′}
          {r : W ⊲ M} {lM : Lg M} {r′ : W′ ⊲ M′} {lM′ : Lg M′} →
        APair lV lV′ q lW q′ lW′ → APair lW lW′ r lM r′ lM′ → APair lV lV′ (⊲-tr q r) lM (⊲-tr q′ r′) lM′
ap-tr {lV = lV} {lV′} {q} {lW} {q′} {lW′} {r} {lM} {r′} {lM′} (H , ad , e , e′) (G , ad′ , f , f′) =
  cat (Al-map (λ a → adm-tr a ad′) H) G f f′ , adm-tr ad ad′ ,
  eq-tr q r lV lW lM e f , eq-tr q′ r′ lV′ lW′ lM′ e′ f′
```

## 2 目标对, 状态关系, `cv` 与 `⊕`

目标对 `TA`: 两个目标同层 ($t$), 世界路径 `wm` 构成对齐的路径对. 层的位置 `tm` 不要求什么 (两边都在 $\Lambda$ 之下的同一层).

```agda
TA : ∀ {W W′ t m m′} → Lg W → Lg W′ → Tg W t m → Tg W′ t m′ → Set
TA lW lW′ T T′ = APair lW lW′ (wm T) (lm T) (wm T′) (lm T′)

-- 读数关系族: 第 t 层的树, 两边世界与 Lg 可以不同
RelF : Set₁
RelF = ∀ t {V V′} → Lg V → Lg V′ → D t V → D t V′ → Set

R∀ : RelF → ∀ {W W′} → Lg W → Lg W′ → St W → St W′ → Set
R∀ Rl {W} {W′} lW lW′ Y Y′ =
  (∀ {t m m′} (T : Tg W t m) (T′ : Tg W′ t m′) → TA lW lW′ T T′ → Rl t (lm T) (lm T′) (yc (d Y) T) (yc (d Y′) T′)) ×
  Rl hz lW lW′ (z Y) (z Y′)

OA : RelF → ∀ {W W′} → Lg W → Lg W′ → Df W → Df W′ → Set
OA Rl {W} {W′} lW lW′ Δ Δ′ =
  ∀ {t m m′} (T : Tg W t m) (T′ : Tg W′ t m′) → TA lW lW′ T T′ → Rl t (lm T) (lm T′) (yc Δ T) (yc Δ′ T′)

Bot : RelF → Set
Bot Rl = ∀ t {V V′} {lV : Lg V} {lV′ : Lg V′} {x′ : D t V′} → Rl t lV lV′ n0 x′

Seq : RelF → Set
Seq Rl = ∀ t {V V′} {lV : Lg V} {lV′ : Lg V′} {x y : D t V} {x′ y′ : D t V′} →
         Rl t lV lV′ x x′ → Rl t lV lV′ y y′ → Rl t lV lV′ (x ⨾ y) (x′ ⨾ y′)

module _ (Rl : RelF) where

  -- 换世界: 只要两条 cv 路径构成对齐的路径对
  cvR : Bot Rl → ∀ {W W′ W₂ W₂′} {lW : Lg W} {lW′ : Lg W′} {q : W ⊲ W₂} {lW₂ : Lg W₂} {q′ : W′ ⊲ W₂′} {lW₂′ : Lg W₂′} →
        APair lW lW′ q lW₂ q′ lW₂′ → ∀ (Y : St W) (Y′ : St W′) → R∀ Rl lW lW′ Y Y′ → R∀ Rl lW₂ lW₂′ (cv q Y) (cv q′ Y′)
  cvR b ap Y Y′ (r , rz) = (λ T T′ ta → r (tg↑ _ T) (tg↑ _ T′) (ap-tr ap ta)) , b hz

  -- 状态前进: 第 0 层的和读 τ₀ 处的输出, τ₀ 这一对是对齐的
  advR : Seq Rl → ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} (Y : St W) (Y′ : St W′) (Δ : Df W) (Δ′ : Df W′) →
         R∀ Rl lW lW′ Y Y′ → OA Rl lW lW′ Δ Δ′ → R∀ Rl lW lW′ (Y ⊕⟨ lW ⟩ Δ) (Y′ ⊕⟨ lW′ ⟩ Δ′)
  advR sq {lW = lW} {lW′} Y Y′ Δ Δ′ (r , rz) O =
    (λ T T′ ta → sq _ (r T T′ ta) (O T T′ ta)) , sq hz rz (O (τ₀ lW) (τ₀ lW′) (ap-self lW lW′))
```

## 3 `Kp` 与 `Kb` 要的对齐

`Kp … wu lW⁺` 以 `cv wu Y` 为状态, 以 `nw wu w` 为上下文, 而 `RKk` 调用它时 `wu = wm T`. 所以目标对的对齐 `TA` 恰好是 `cvR` 对 `Kp` 状态要的前提 (`kpR`), 也恰好是 `snd-nwA` 对 `Kp` 上下文要的四个前提 (`kp-nw`, 只是把记录拆开). `Kb` 在 `nκ` 的分支 $p: W^+\lhd c$ 上再走一次, 动作与位置用叠起来的路径 `⊲-tr wu p`; 两边分支若构成对齐的路径对, 叠起来的路径也是 (`stack`).

```agda
  kpR : Bot Rl → ∀ {W W′ t m m′} {lW : Lg W} {lW′ : Lg W′} (T : Tg W t m) (T′ : Tg W′ t m′) → TA lW lW′ T T′ →
        ∀ (Y : St W) (Y′ : St W′) → R∀ Rl lW lW′ Y Y′ → R∀ Rl (lm T) (lm T′) (cv (wm T) Y) (cv (wm T′) Y′)
  kpR b T T′ ta = cvR b ta

kp-nw : ∀ {W W′ t m m′} {lW : Lg W} {lW′ : Lg W′} (T : Tg W t m) (T′ : Tg W′ t m′) → TA lW lW′ T T′ →
        Al m m′ (wm T) (lm T) (wm T′) (lm T′) × Adm W W′ m m′ × (lW ≡ lg⊲ (wm T) (lm T)) × (lW′ ≡ lg⊲ (wm T′) (lm T′))
kp-nw T T′ ta = ta

stack : ∀ {W W′ t m m′ c c′} {lW : Lg W} {lW′ : Lg W′} (T : Tg W t m) (T′ : Tg W′ t m′) {p : m ⊲ c} {lc : Lg c} {p′ : m′ ⊲ c′} {lc′ : Lg c′} →
        TA lW lW′ T T′ → APair (lm T) (lm T′) p lc p′ lc′ → APair lW lW′ (⊲-tr (wm T) p) lc (⊲-tr (wm T′) p′) lc′
stack T T′ ta bp = ap-tr ta bp
```

## 4 结论

- **(定理) `ap-self`, `ap-tr`**: 对齐的路径对构成一个范畴 (恒等与复合). `cvR`, `advR`, `kpR`, `stack` 是推论, 对一切读数关系族 (`cvR`, `kpR` 只要 `Bot`, `advR` 只要 `Seq`).
- **读法 (判断)**: 主线折叠里换世界的地方 (`BNi` 的 `cv p`, `κc` 的 `cv (sum-fst …)`, `Kp` 的 `cv wu`, `Kb` 的 `cv p`) 与包 `nw` 的地方 (`Ai` 的 `nw p w`, `Kp`/`Kb` 的 `nw wu w`, `nw p (…)`, `κc` 的 `nw (sum-fst …) w`) 都是 "一条路径加一个旧对象". 只要每一处的两条路径构成对齐的路径对, 状态关系与上下文关系都接得住. 要逐处给出对齐: `wu` 来自目标对 (`TA`), 分支路径 `p` 来自关系的 `ni`/`nκ` 规则 (所以这两条规则只能对对齐的分支对取前提, 见入口 §2), 格路径来自 `genᴾ` 一类的生成.
- 与 `StrRel11CvNeg.¬cv-al` 对照: `SumOneFold` 的 `cv` 要用 `cmpF` 把目标重新分成 "在世界之下" 与 "在世界之上", 对齐在这一步丢失; 主线没有这一步. 这是把逐层语义直接写在主线上的理由.
