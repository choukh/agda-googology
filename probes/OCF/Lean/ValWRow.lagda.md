# ValW (三): 回灌那一行 (`RKa`) 是一步定理

> 不含记号. 入口 [ValW](ValW.lagda.md). 第 4 层: 只新增关系与定理. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延.
>
> 左实例 `F₁` 一切有损 (闭项 `TL` 的折叠), 右实例 `F₂` 的级回灌参数 `fb₂` 任意 (主要是 `TF` 的 `fb`). 两个实例只在 `RKa` 那一行不同 (`LeanTFold` 文件头). 本篇证: **这一行本身不是卡点.** 只要分支的折叠保持关系 (`RunH`, 递归调用的形状, 作前提), 有损的 `ω⋅ c` 被回灌的 `nl (λ n → Δₙ)` 逐格模拟 (`RKa-step`, 条件定理). 用到折叠字面的三件事 (都是定理, 无前提):
>
> - **世界** (`cell-≤`): 第 $n$ 格的世界 $(w_n, \beta)$ 在右边当前世界之上 (`qA`, 第二分量 `hself`).
> - **数据** (`cell-w`): 第 $n$ 格的前缀 `coA` 是右边前缀套 $n+1$ 层 `nw`.
> - **状态** (`cell-Y`): 第 $n$ 格的状态的累计输出 `d` 是右边状态的 `d` 在后面接上前几格的输出 (右边多出一段).
>
> 状态的关系只比 `d` (同 `ValNewRun.StR`). 回灌格把 `z`, `z₁` 清零 (否定一路 `NegValWReset.reset-z₁`), 而 `z₁` 只喂新种类的回灌 `κc₁`; 判断: 最高层没有新种类的 $\Omega$-结点 (`ΛF = up Λs`) 时折叠不经过 `κc₁`, 所以这里不比 `z`, `z₁`. 这个判断写成对折叠全程的不变式要另做 (接手清单).
>
> **前提 `RunH` 是什么.** 同层、两个世界 ($W_1\le W_2$)、相关的数据/前缀/状态/动作 ⇒ 两边的折叠在成对目标 (同一目标层, $m_1\le m_2$) 上输出相关. 它是 `RKa-step` 在完整证明里的递归调用; 完整的 `RunH` 卡在两边结点层不同 (`ValWRk.kr-occurs`), 见入口.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTTree
module OCF.Lean.ValWRow (T : KS) (bk : Tree.BotK T) (Λ : HB (step T)) (lΛ : LgB Λ)
  (one⊲ : ∀ {w} → hs hz ⊲[ w ] Λ) (fb₂ : K T → FoldTy.Fb T Λ ⊎ ⊤) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
import OCF.Lean.LeanTFold as Fold
open import OCF.Lean.ValWRel T
open Tree T
open FoldTy T Λ

module F₁ = Fold T bk Λ lΛ one⊲ (λ _ → inj₂ tt)
module F₂ = Fold T bk Λ lΛ one⊲ fb₂
```

## §1 关系的简写; `drp` 保持关系

```agda
Rl : ∀ {L W₁ W₂} → D L W₁ → D L W₂ → Set
Rl = RelA accᴸ

drp-M : ∀ (a a′ : AccY hz) {W₁ W₂ W₁′ W₂′} {x : D₀ W₁} {y : D₀ W₂} → RelA a x y →
        RelA a′ (drp {W₁} {W₁′} x) (drp {W₂} {W₂′} y)
drp-M (acc g) (acc g′) m1 = m1
drp-M (acc g) (acc g′) (m⨾ p q) = m⨾ (drp-M (acc g) (acc g′) p) (drp-M (acc g) (acc g′) q)
drp-M (acc g) (acc g′) (ml h) = ml (λ n → drp-M (acc g) (acc g′) (h n))
drp-M (acc g) (acc g′) (mi {R₁ = ()} _ _)
drp-M (acc g) (acc g′) (mc {κ = inj₁ _} {z₁ = ()} _)
drp-M (acc g) (acc g′) (mc {κ = inj₂ _} {z₁ = ()} _)
drp-M (acc g) (acc g′) (mw p) = drp-M (acc g) (acc g′) p
drp-M (acc g) (acc g′) (mw′ p) = drp-M (acc g) (acc g′) p
drp-M (acc g) (acc g′) mz = mz
drp-M (acc g) (acc g′) (mr p) = mr (drp-M (acc g) (acc g′) p)
drp-M (acc g) (acc g′) (me p) = me (drp-M (acc g) (acc g′) p)
drp-M (acc g) (acc g′) (mlₙ n p) = mlₙ n (drp-M (acc g) (acc g′) p)
```

## §2 输出、状态、动作的关系; 前提 `RunH`

同一目标层 $t$, 目标世界 $m_1\le m_2$ (字面证据).

```agda
DfM : ∀ {W₁ W₂} → Df W₁ → Df W₂ → Set
DfM {W₁} {W₂} Δ₁ Δ₂ = ∀ {t m₁ m₂} → m₁ ≤ m₂ → (T₁ : Tg W₁ t m₁) (T₂ : Tg W₂ t m₂) → Rl (yc Δ₁ T₁) (yc Δ₂ T₂)

StM : ∀ {W₁ W₂} → St W₁ → St W₂ → Set
StM Y₁ Y₂ = DfM (d Y₁) (d Y₂)

IgM : ∀ {ly W₁ W₂} → Ig ly W₁ → Ig ly W₂ → Set
IgM {ly} {W₁} {W₂} A₁ A₂ =
  ∀ {W₁′ W₂′} (p₁ : W₁ ≤ W₁′) (p₂ : W₂ ≤ W₂′) → W₁′ ≤ W₂′ → (l₁ : LgW L₀ W₁′) (l₂ : LgW L₀ W₂′) →
  {w₁ : D ly W₁′} {w₂ : D ly W₂′} → Rl w₁ w₂ → {Y₁ : St W₁′} {Y₂ : St W₂′} → StM Y₁ Y₂ → DfM (A₁ p₁ l₁ w₁ Y₁) (A₂ p₂ l₂ w₂ Y₂)

Ig↾-M : ∀ {ly W₁ W₂ W₂′} (p : W₂ ≤ W₂′) {A₁ : Ig ly W₁} {A₂ : Ig ly W₂} → IgM A₁ A₂ → IgM A₁ (F₂.Ig↾ p A₂)
Ig↾-M p hA p₁ p₂ = hA p₁ (≤tr p p₂)

RunH : Set
RunH = ∀ {ly W₀₁ W₀₂ W₁ W₂} (ac₁ ac₂ : AccY ly) {x₁ : D ly W₀₁} {x₂ : D ly W₀₂} → Rl x₁ x₂ →
  (q₁ : W₀₁ ≤ W₁) (q₂ : W₀₂ ≤ W₂) → W₁ ≤ W₂ → (lW₁ : LgW L₀ W₁) (lW₂ : LgW L₀ W₂) (ll₁ : F₁.LW ly W₁) (ll₂ : F₂.LW ly W₂) →
  {A₁ : Ig ly W₁} {A₂ : Ig ly W₂} → IgM A₁ A₂ → {w₁ : D ly W₁} {w₂ : D ly W₂} → Rl w₁ w₂ →
  {Y₁ : St W₁} {Y₂ : St W₂} → StM Y₁ Y₂ →
  DfM (F₁.Run ac₁ x₁ q₁ lW₁ ll₁ A₁ w₁ Y₁) (F₂.Run ac₂ x₂ q₂ lW₂ ll₂ A₂ w₂ Y₂)
```

## §3 回灌格的三件事 (定理, 无前提)

```agda
module Cells {ly W₀ W} (ac : AccY ly) (F : Fb) (u : F₂.Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W)
             (ll : F₂.LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) where
  c : ℕ → F₂.ClA W ly
  c = F₂.κcF ac F u q₀ lW ll A₀ w Y

  Wn : ℕ → Wd L₀
  Wn n = F₂.wA (c n) , proj₂ W

  cell-≤ : ∀ n → W ≤ Wn n
  cell-≤ n = F₂.qA (c n) , hself

  cell-w : ∀ {W₁} {x : D ly W₁} → Rl x w → ∀ n → Rl x (F₂.coA (c n))
  cell-w h zero = mw′ h
  cell-w h (suc n) = mw′ (cell-w h n)

  cell-Y : ∀ {W₁} {Y₁ : St W₁} → StM Y₁ Y → ∀ n → StM Y₁ (F₂.SA (c n))
  cell-Y h zero qm T₁ T₂ = h qm T₁ (F₂.tg↑ (nx≤ F lW (d₀ F lW Y) , hself) T₂)
  cell-Y {W₁} {Y₁} h (suc n) {t} {m₁} {m₂} qm T₁ T₂ =
    mr {e = yc (F₂.κΔA ac u q₀ lW ll A₀ (c n)) (F₂.tg↑ (nx≤ F (F₂.lwA (c n) , proj₂ lW)
          (yc (F₂.κΔA ac u q₀ lW ll A₀ (c n)) (tg ≤rf (ℓ⊲ F) (F₂.lwA (c n) , proj₂ lW))) , hself) T₂)}
     (cell-Y {W₁} {Y₁} h n {t} {m₁} {m₂} qm T₁ (F₂.tg↑ (nx≤ F (F₂.lwA (c n) , proj₂ lW)
          (yc (F₂.κΔA ac u q₀ lW ll A₀ (c n)) (tg ≤rf (ℓ⊲ F) (F₂.lwA (c n) , proj₂ lW))) , hself) T₂))
```

## §4 `RKa` 一行: 有损被回灌逐格模拟 (条件定理, 前提 `RunH`)

```agda
module _ (H : RunH) where
  RKa-step : ∀ {ly W₀₁ W₀₂ W₁ W₂ m₁ m₂} (ac₁ ac₂ : AccY ly) (s : Fb ⊎ ⊤)
    {u₁ : F₁.Bu ly W₀₁} {u₂ : F₂.Bu ly W₀₂} →
    (∀ {W₁′ W₂′} (p₁ : W₀₁ ≤ W₁′) (p₂ : W₀₂ ≤ W₂′) → W₁′ ≤ W₂′ → (l₁ : LgW L₀ W₁′) (l₂ : LgW L₀ W₂′) → Rl (u₁ p₁ l₁) (u₂ p₂ l₂)) →
    (q₁ : W₀₁ ≤ W₁) (q₂ : W₀₂ ≤ W₂) → W₁ ≤ W₂ → (lW₁ : LgW L₀ W₁) (lW₂ : LgW L₀ W₂) (ll₁ : F₁.LW ly W₁) (ll₂ : F₂.LW ly W₂) →
    {A₁ : Ig ly W₁} {A₂ : Ig ly W₂} → IgM A₁ A₂ → {w₁ : D ly W₁} {w₂ : D ly W₂} → Rl w₁ w₂ →
    {Y₁ : St W₁} {Y₂ : St W₂} → StM Y₁ Y₂ → (Tq₁ : Tg W₁ hz m₁) (Tq₂ : Tg W₂ hz m₂) →
    Rl (F₁.RKa ac₁ (inj₂ tt) u₁ q₁ lW₁ ll₁ A₁ w₁ Y₁ Tq₁) (F₂.RKa ac₂ s u₂ q₂ lW₂ ll₂ A₂ w₂ Y₂ Tq₂)
  RKa-step ac₁ ac₂ (inj₂ tt) hu q₁ q₂ q lW₁ lW₂ ll₁ ll₂ hA hw hY Tq₁ Tq₂ =
    ml (λ _ → drp-M accᴸ accᴸ
      (H ac₁ ac₂ (hu q₁ q₂ q lW₁ lW₂) ≤rf ≤rf q lW₁ lW₂ ll₁ ll₂ hA hw hY q (F₁.τ₀ lW₁) (F₂.τ₀ lW₂)))
  RKa-step {ly} {W₀₂ = W₀₂} {W₁} {W₂} ac₁ ac₂ (inj₁ F) {u₂ = u₂} hu q₁ q₂ q lW₁ lW₂ ll₁ ll₂ {A₂ = A₂} hA {w₁} {w₂} hw {Y₁} {Y₂} hY Tq₁ Tq₂ =
    ml (λ n → drp-M accᴸ accᴸ
      (H ac₁ ac₂ {x₂ = u₂ (≤tr q₂ (cell-≤ n)) (lW n)} (hu q₁ (≤tr q₂ (cell-≤ n)) (≤tr q (cell-≤ n)) lW₁ (lW n))
         ≤rf ≤rf (≤tr q (cell-≤ n)) lW₁ (lW n) ll₁ (⊲ᴮ↑ (cell-≤ n) ll₂) {A₂ = F₂.Ig↾ (cell-≤ n) A₂} (Ig↾-M (cell-≤ n) hA)
         {w₂ = F₂.coA (c n)} (cell-w {W₁} {w₁} hw n) {Y₂ = F₂.SA (c n)} (cell-Y {W₁} {Y₁} hY n) (≤tr q (cell-≤ n)) (F₁.τ₀ lW₁) (F₂.τ₀ (lW n))))
    where
    open Cells {ly} {W₀₂} {W₂} ac₂ F u₂ q₂ lW₂ ll₂ A₂ w₂ Y₂
    lW : ∀ n → LgW L₀ (Wn n)
    lW n = F₂.lwA (c n) , proj₂ lW₂
```
