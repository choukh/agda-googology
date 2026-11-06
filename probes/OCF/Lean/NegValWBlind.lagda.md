# NegValW (三): 对接口 `ValWIf` 的盲定理与边界定理

> 不含记号. 入口 [NegValW](NegValW.lagda.md). 导入构造一路的接口 [ValWIf](ValWIf.lagda.md) (接口定稿 2026-11-05 23:43), 不改它. 模块参数与接口相同 (任意 `T`, 底种类, 最高层, 两个级回灌参数), 所以下面的定理对一切实例成立. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> - **盲定理 `blindSim`** (定理): 记录 `SimW` (律 X1 `x-sum`, X2 `x-Ωd`) 被一个只在第 0 层对第 0 层有内容、其余处处为 `⊤` 的关系 `Bl` 满足. **`no-RunPres`**, **`no-Cross0`** (定理): 对这个关系, 律 X3 (`RunPres`) 与目标 `Cross0` 都不成立 (反例: 数据 `n1` 对 `n0`, 动作与状态都输出 $\Omega_t$). 所以 X1, X2 不推出 X3, 也不推出 `Cross0`; 值的内容全在 `Rx` 的选法与 `RunPres` 的证明里. 这也是 `SimW` 可满足的实例 (前提可满足).
> - **边界定理 `Forced.mono`** (定理, 前提 `SimW` 与 `RunPres`): 任何满足 X1, X2, X3 的关系都推出: 对一切 $\mathrm{ly}_1\lhd\mathrm{ly}_2$ (在 $W_2$ 里), $W_1\le W_2$, 两个折叠在 $\Omega_{\mathrm{ly}_1}$ (世界 $W_1$) 与 $\Omega_{\mathrm{ly}_2}$ (世界 $W_2$) 上, 前缀取 $\Omega$, 动作与状态输出 $\Omega_t$, 第 0 层读数左 $\le$ 右. 取 `fb₁ = fb₂` 时这是**同一个折叠**对层与世界同时单调 (在这组输入上); 这正是此前各路未证的 "跨世界的值单调" (`GoodUp`, `TpMonoIf` (b), `ValTK` 的 `DomW`), 本篇不证也不否定它.
>
> **只否定什么.** `no-RunPres`, `no-Cross0` 只否定 "律 X1, X2 本身足以推出 X3 或 `Cross0`" (也就是说, 不能指望任意一个满足 X1, X2 的关系). 不否定存在满足 X3 的关系. `Forced.mono` 不是否定, 是 X3 的一个必要条件, 给出 X3 至少要证什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTTree
module OCF.Lean.NegValWBlind (T : KS) (bk : Tree.BotK T) (Λ : HB (step T)) (lΛ : LgB Λ)
  (one⊲ : ∀ {w} → hs hz ⊲[ w ] Λ) (fb₁ fb₂ : K T → FoldTy.Fb T Λ ⊎ ⊤) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import OCF.Lean.NegLeanLvVal using (z≤; s≤; ≤l; l≤) renaming (_≤_ to _≤ᵥ_)
open Tree T
open FoldTy T Λ
open import OCF.Lean.ValWIf T bk Λ lΛ one⊲ fb₁ fb₂
```

## §1 盲的关系

`Bl x y`: 两边都是第 0 层时, $x$ 的读数被 $y$ 的读数支配 (正是 X1 要的); 其余一切层对 `⊤`.

```agda
Bl : ∀ {L₁ L₂ W₁ W₂} → D L₁ W₁ → D L₂ W₂ → Set
Bl {L₁ = hz} {L₂ = hz} x y = ∀ {b b′} → b ≤ᵥ b′ → sum b x ≤ᵥ sum b′ y
Bl {L₁ = hz} {L₂ = hs _} x y = ⊤
Bl {L₁ = hz} {L₂ = hl _} x y = ⊤
Bl {L₁ = hz} {L₂ = hΩ _ _} x y = ⊤
Bl {L₁ = hs _} x y = ⊤
Bl {L₁ = hl _} x y = ⊤
Bl {L₁ = hΩ _ _} x y = ⊤

Ωd-bl : ∀ {t₁ t₂ W₁ W₂} (e : t₁ ⊲[ W₂ ] t₂) (q : W₁ ≤ W₂) → Bl (Ωd t₁ {W₁}) (Ωd t₂ {W₂})
Ωd-bl {t₁ = hz} {t₂ = hz} e q le = s≤ le
Ωd-bl {t₁ = hz} {t₂ = hs _} e q = tt
Ωd-bl {t₁ = hz} {t₂ = hl _} e q = tt
Ωd-bl {t₁ = hz} {t₂ = hΩ _ _} e q = tt
Ωd-bl {t₁ = hs _} e q = tt
Ωd-bl {t₁ = hl _} e q = tt
Ωd-bl {t₁ = hΩ _ _} e q = tt

blindSim : SimW
blindSim = record { Rx = λ e q x y → Bl x y ; x-sum = λ e q r le → r le ; x-Ωd = Ωd-bl }

-- 最高层不是 0 (由 one⊲), 所以 Bl 在 (Λ, 任意层) 上是 ⊤
no1 : ∀ {w} → ¬ (_⊲[_]_ {L₀} (hs hz) w hz)
no1 ()

nz⊤ : ∀ L {L′ W₁ W₂} {x : D L W₁} {y : D L′ W₂} → (∀ {w} → hs hz ⊲[ w ] L) → Bl x y
nz⊤ hz p = ⊥-elim (no1 (p {w₀ L₀}))
nz⊤ (hs _) p = tt
nz⊤ (hl _) p = tt
nz⊤ (hΩ _ _) p = tt
```

## §2 输出 $\Omega_t$ 的动作与状态

```agda
AΩ : ∀ {ly W} → Ig ly W
AΩ _ _ _ _ = df (λ {t} _ → Ωd t)

YΩ : ∀ {W} → St W
YΩ = st (df (λ {t} _ → Ωd t)) n0 n0
```

## §3 盲: X3 与 `Cross0` 对 `Bl` 不成立

数据左 `n1` 右 `n0` (第 $\Lambda$ 层, `Bl` 是 `⊤`). 左边折叠 `n1` 就是动作的输出, 第 0 层是 $\Omega_0$ = `n1`, 读数 $1$; 右边 `n0` 的读数 $0$.

```agda
module Bld where
  open Goals blindSim

  IgX-AΩ : ∀ {ly₁ ly₂ W₁ W₂} (e : ly₁ ⊲[ W₂ ] ly₂) (q : W₁ ≤ W₂) → IgX e q (AΩ {ly₁} {W₁}) (AΩ {ly₂} {W₂})
  IgX-AΩ e q p₁ p₂ q′ l₁ l₂ r yy e′ qm T₁ T₂ = Ωd-bl e′ qm

  StX-YΩ : ∀ {W₁ W₂} (q : W₁ ≤ W₂) → StX q (YΩ {W₁}) (YΩ {W₂})
  StX-YΩ q e′ qm T₁ T₂ = Ωd-bl e′ qm

  no-RunPres : ¬ RunPres
  no-RunPres RP = no1 {w₀ L₀} (help (h z≤))
    where
    W = w₀ L₀
    lW : LgW L₀ W
    lW = lw₀ L₀
    h : Bl (yc (F₁.Run accᴸ n1 ≤rf lW hself AΩ n0 YΩ) (F₁.τ₀ lW))
           (yc (F₂.Run accᴸ n0 ≤rf lW hself AΩ n0 YΩ) (F₂.τ₀ lW))
    h = RP {ly₁ = Λ} {ly₂ = Λ} {W₀₁ = W} {W₀₂ = W} {W₁ = W} {W₂ = W} accᴸ accᴸ hself ≤rf ≤rf hself
          {x₁ = n1} {x₂ = n0} (nz⊤ Λ one⊲) ≤rf ≤rf lW lW hself hself
          {A₁ = AΩ} {A₂ = AΩ} (IgX-AΩ hself ≤rf) {w₁ = n0} {w₂ = n0} (nz⊤ Λ one⊲)
          {Y₁ = YΩ} {Y₂ = YΩ} (StX-YΩ ≤rf) hself ≤rf (F₁.τ₀ lW) (F₂.τ₀ lW)
    help : hs hz ≤ᵥ hz → hs hz ⊲[ W ] hz
    help ()

  no-Cross0 : ¬ Cross0
  no-Cross0 C0 = help (C0 {W = w₀ L₀} accᴸ accᴸ {x₁ = n1} {x₂ = n0} (nz⊤ Λ one⊲) (lw₀ L₀)
                          {A₁ = AΩ} {A₂ = AΩ} (IgX-AΩ hself ≤rf) {Y₁ = YΩ} {Y₂ = YΩ} (StX-YΩ ≤rf))
    where
    help : ¬ (hs hz ≤ᵥ hz)
    help ()
```

## §4 边界: X1–X3 推出折叠在 $\Omega$ 上对层与世界单调

```agda
module Forced (S : SimW) (RP : Goals.RunPres S) where
  open SimW S
  open Goals S

  IgΩ : ∀ {ly₁ ly₂ W₁ W₂} (e : ly₁ ⊲[ W₂ ] ly₂) (q : W₁ ≤ W₂) → IgX e q (AΩ {ly₁} {W₁}) (AΩ {ly₂} {W₂})
  IgΩ e q p₁ p₂ q′ l₁ l₂ r yy e′ qm T₁ T₂ = x-Ωd e′ qm

  StΩ : ∀ {W₁ W₂} (q : W₁ ≤ W₂) → StX q (YΩ {W₁}) (YΩ {W₂})
  StΩ q e′ qm T₁ T₂ = x-Ωd e′ qm

  mono : ∀ {ly₁ ly₂ W₁ W₂} (ac₁ : AccY ly₁) (ac₂ : AccY ly₂) (e : ly₁ ⊲[ W₂ ] ly₂) (q : W₁ ≤ W₂)
    (lW₁ : LgW L₀ W₁) (lW₂ : LgW L₀ W₂) (ll₁ : ly₁ ⊲[ W₁ ] Λ) (ll₂ : ly₂ ⊲[ W₂ ] Λ) →
    sum hz (yc (F₁.Run ac₁ (Ωd ly₁) ≤rf lW₁ ll₁ AΩ (Ωd ly₁) YΩ) (F₁.τ₀ lW₁)) ≤ᵥ
    sum hz (yc (F₂.Run ac₂ (Ωd ly₂) ≤rf lW₂ ll₂ AΩ (Ωd ly₂) YΩ) (F₂.τ₀ lW₂))
  mono {W₁ = W₁} {W₂} ac₁ ac₂ e q lW₁ lW₂ ll₁ ll₂ =
    x-sum hself q
      (RP {W₀₁ = W₁} {W₀₂ = W₂} ac₁ ac₂ e q q e (x-Ωd e q) ≤rf ≤rf lW₁ lW₂ ll₁ ll₂
          (IgΩ e q) (x-Ωd e q) (StΩ q) hself q (F₁.τ₀ lW₁) (F₂.τ₀ lW₂))
      z≤
```

## §5 结论 (按档)

- **[定理, 无条件, 对一切实例]** `blindSim : SimW`; `Bld.no-RunPres : ¬ Goals.RunPres blindSim`; `Bld.no-Cross0 : ¬ Goals.Cross0 blindSim`.
- **[定理, 前提 `S : SimW`, `RP : Goals.RunPres S`]** `Forced.mono`: 第 0 层读数 $\mathrm{Run}_1(\Omega_{\mathrm{ly}_1})@W_1 \le \mathrm{Run}_2(\Omega_{\mathrm{ly}_2})@W_2$.
- **前提实例.** `SimW` 的实例: `blindSim`. `RunPres` 的实例: 没有 (这是构造一路要给的); `Forced` 是条件定理, 条件是否可满足未知.
- **[判断]** 构造一路要证的 X3 至少包含 "同一折叠在 $\Omega$ 上对层与世界单调" (取 `fb₁ = fb₂`), 而回灌行与 `rkT` 的 `kr` 情形 (见 [NegValWInst](NegValWInst.lagda.md) `rk-split`) 都落在这条单调里.
