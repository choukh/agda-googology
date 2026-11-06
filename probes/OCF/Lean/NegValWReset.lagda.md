# NegValW (一): 回灌格清零状态, 新种类闭包的起点世界不可比

> 不含记号. 入口 [NegValW](NegValW.lagda.md). 本篇**不依赖**构造一路的接口 (接口定稿之前写的部分), 只导入 [LeanTBase](LeanTBase.lagda.md), [LeanTTree](LeanTTree.lagda.md), [LeanTFold](LeanTFold.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** 构造一路要写一条带 $W\le W'$ 证据的模拟, 左边全有损 (`TL`), 右边回灌 (`TF`), 右边的世界更大. 回灌那一行 (`RKa`) 两边分开: 有损一边在当前世界 $W$, 用当前状态 $Y$ 跑分支; 回灌一边第 $n$ 格在世界 $(w_A, \beta)$ ($\beta$ = $W$ 的新种类界), 用状态 `SA (c n)` 跑分支. 本篇给出:
>
> - **`reset-z₁`, `reset-z`** (定理, `refl`): 回灌的每一格 (对一切 $n$, 一切级回灌 $F$) 的状态, 第 0, 1 层的累计输出 `z`, `z₁` 都是 `n0` (`cv` 清零). 有损一边用的是 $Y$ 本身 (`lossy-row`, `refl`).
> - **`start-L`, `start-R`** (定理, `refl`): 分支里若有新种类闭包 (第 0, 1 层目标的 `κc₁`), 它的第 0 格的界: 有损一边是 $\mathrm{rd}_1(\beta, z_1\,Y)$, 回灌一边是 $\beta$.
> - **`no-start-≤`** (定理): 只要 $z_1\,Y$ 的读回在 $\beta$ 之上严格多出一个后继 (`hs b ⊲ rd₁ β (z₁ Y)`, $\beta\lhd b$), 两边 `κc₁` 第 0 格的世界之间**没有** $W\le W'$ 的证据 (对任何 $w_A$). 原因是新种类的分量: 右边的界 $\beta$ 低于左边的 $\mathrm{rd}_1(\beta,z_1Y)$ (`no-hs⊲`, `strict`: $\neg(\mathrm{hs}\,a\lhd a)$).
> - **前提实例** `Y1` ($z_1 = $ `n1`) 与 `Y-Ωd₁`: 闭项的写法里 $\Omega_\Lambda$ 的第一步是 `n1`, 动作 `Stp` 之后状态的 `z₁` 正是 $\omega$ 份的 $\Omega_1\,⨾\,\dots$ (`after-n1`, `refl`), 它的读回满足前提 (`pos-after`).
>
> **只否定什么.** 只否定这样的模拟: 回灌那一行把有损一边的分支 (状态 $Y$) 与回灌一边**同下标**的格 (状态 `SA (c n)`) 用 "右边世界 $\ge$ 左边世界" 的关系相连, 并且关系穿进分支里的新种类闭包时逐格 (同下标) 要求 $W\le W'$. **不否定**: 回灌提高值; 换下标或换成值 (而不是世界) 的关系; 状态关系只看 `d` (不看 `z₁`) 而在 `κc₁` 那一行另写规则的模拟. 也不说 `TF` 的计算里这一配置在哪一步出现 (判断: 在 $\Omega_\Lambda$ 的闭包第一次碰到旧种类回灌时, 状态是 `after-n1` 的形状).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegValWReset where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTTree
import OCF.Lean.LeanTFold as Fold
```

## §1 第一位置不允许 $\mathrm{hs}\,a\lhd a$

`strict b`: $\mathrm{hs}\,a\lhd b$ 时 $b\not\lhd a$. 对 $b$ 结构归纳.

```agda
module _ {S : KS} where
  strict : ∀ {w} (b : HB S) {a} → hs a ⊲[ w ] b → ¬ (b ⊲[ w ] a)
  strict hz () q
  strict (hs b) hself q = strict b q hself
  strict (hs b) (hsuc p) q = strict b p (⊲ᴮ-tr (hsuc hself) q)
  strict (hl f) (hlim n p) q = strict (f n) p (⊲ᴮ-tr (hlim n hself) q)
  strict (hΩ κ g) (hLim e p) q = strict (g _) p (⊲ᴮ-tr (hLim e hself) q)

  no-hs⊲ : ∀ {w} (a : HB S) → ¬ (hs a ⊲[ w ] a)
  no-hs⊲ a p = strict a p hself

  -- β ⊲ b, hs b ⊲ X 则 X ⋪ β
  above : ∀ {w} {β b X : HB S} → β ⊲[ w ] b → hs b ⊲[ w ] X → ¬ (X ⊲[ w ] β)
  above βb hb Xβ = strict _ hb (⊲ᴮ-tr Xβ βb)
```

## §2 回灌格的状态

对一切折叠参数 (与 `LeanTFold` 同样的模块参数).

```agda
module Cells (T : KS) (bk : Tree.BotK T) (Λ : HB (step T)) (lΛ : LgB Λ)
  (one⊲ : ∀ {w} → hs hz ⊲[ w ] Λ) (fb : K T → FoldTy.Fb T Λ ⊎ ⊤) where
  open Tree T
  open Rd bk
  open FoldTy T Λ
  open Fold T bk Λ lΛ one⊲ fb

  module _ {ly W₀ W} (ac : AccY ly) (F : Fb) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W)
           (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) where
    c : ℕ → ClA W ly
    c = κcF ac F u q₀ lW ll A₀ w Y

    reset-z₁ : ∀ n → z₁ (SA (c n)) ≡ n0
    reset-z₁ zero = refl
    reset-z₁ (suc n) = refl

    reset-z : ∀ n → z (SA (c n)) ≡ n0
    reset-z zero = refl
    reset-z (suc n) = refl

    -- 回灌一边第 n 格跑分支的式子 (refl): 状态是 SA (c n)
    fed-cell : ∀ n → κΔA ac u q₀ lW ll A₀ (c n) ≡
      Run ac (u (≤tr q₀ (qA (c n) , hself)) (lwA (c n) , proj₂ lW)) ≤rf (lwA (c n) , proj₂ lW)
        (⊲ᴮ↑ (qA (c n) , hself) ll) (Ig↾ (qA (c n) , hself) A₀) (coA (c n)) (SA (c n))
    fed-cell n = refl

  -- 有损一边的式子 (refl): 状态是 Y 本身
  lossy-row : ∀ {ly W₀ W m} (ac : AccY ly) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W)
              (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) (Tq : Tg W hz m) →
    RKa ac (inj₂ tt) u q₀ lW ll A₀ w Y Tq ≡ ω⋅ (drp (yc (Run ac (u q₀ lW) ≤rf lW ll A₀ w Y) (τ₀ lW)))
  lossy-row ac u q₀ lW ll A₀ w Y Tq = refl
```

**新种类闭包的第 0 格.** 分支里的新种类闭包 (目标第 0, 1 层) 的第 0 格的界是 $\mathrm{rd}_1(\beta, z_1)$, $z_1$ 取当时的状态. 左边状态 $Y$, 右边状态 `SA (c n)` (`z₁` 是 `n0`), 所以右边的界就是 $\beta$.

```agda
  module _ {ly W₀ W} (ac : AccY ly) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W)
           (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) where
    start-L : v₁ (κc₁ ac u q₀ lW ll A₀ w Y zero) ≡ rd₁ lW (proj₂ W) (z₁ Y)
    start-L = refl

  -- 状态的 z₁ 是 n0 时, 第 0 格的界就是 β
  start-R : ∀ {ly W₀ W} (ac : AccY ly) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W)
            (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) → z₁ Y ≡ n0 →
            v₁ (κc₁ ac u q₀ lW ll A₀ w Y zero) ≡ proj₂ W
  start-R {W = W} ac u q₀ lW ll A₀ w Y e = cong (rd₁ lW (proj₂ W)) e
```

**没有世界证据.** 只要 $z_1\,Y$ 的读回在 $\beta$ 之上多出一个后继, 左边第 0 格的世界 $(w, \mathrm{rd}_1(\beta,z_1Y))$ 就不 $\le$ 右边第 0 格的世界 $(w_A, \beta)$, 无论 $w_A$ 多大.

```agda
  Pos : ∀ {W} → LgW L₀ W → D (hs hz) W → Set
  Pos {W} lW x = Σ (HB T) (λ b → (∀ {v} → proj₂ W ⊲[ v ] b) × (∀ {v} → hs b ⊲[ v ] rd₁ lW (proj₂ W) x))

  no-start-≤ : ∀ {W} (lW : LgW L₀ W) (x : D (hs hz) W) → Pos lW x →
    ∀ (wA : Wd T) → ¬ ((proj₁ W , rd₁ lW (proj₂ W) x) ≤ (wA , proj₂ W))
  no-start-≤ lW x (b , βb , hb) wA (_ , q) = above {w = wA} βb hb q
```

把三条连起来: 左边的界由 `start-L` 给出 ($x = z_1\,Y$), 右边由 `start-R` 给出 ($\beta$ = `proj₂ W`).

```agda
  module _ {ly W₀ W} (ac : AccY ly) (F : Fb) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W)
           (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) (pY : Pos lW (z₁ Y)) (n : ℕ)
           {ly′ W₀′} (ac′ : AccY ly′) (u′ : Bu ly′ W₀′) (q₀′ : W₀′ ≤ (wA (κcF ac F u q₀ lW ll A₀ w Y n) , proj₂ W))
           (ll′ : LW ly′ (wA (κcF ac F u q₀ lW ll A₀ w Y n) , proj₂ W))
           (A₀′ : Ig ly′ (wA (κcF ac F u q₀ lW ll A₀ w Y n) , proj₂ W))
           (w′ : D ly′ (wA (κcF ac F u q₀ lW ll A₀ w Y n) , proj₂ W))
           {ly″ W₀″} (ac″ : AccY ly″) (u″ : Bu ly″ W₀″) (q₀″ : W₀″ ≤ W) (ll″ : LW ly″ W) (A₀″ : Ig ly″ W) (w″ : D ly″ W) where
    cn : ClA W ly
    cn = κcF ac F u q₀ lW ll A₀ w Y n

    -- 左: 有损一边 (状态 Y) 的新种类闭包第 0 格; 右: 回灌第 n 格 (状态 SA cn) 里的同一处
    cL : Cl₁ W ly″
    cL = κc₁ ac″ u″ q₀″ lW ll″ A₀″ w″ Y zero
    cR : Cl₁ (wA cn , proj₂ W) ly′
    cR = κc₁ ac′ u′ q₀′ (lwA cn , proj₂ lW) ll′ A₀′ w′ (SA cn) zero

    no-cell-≤ : ¬ ((proj₁ W , v₁ cL) ≤ (wA cn , v₁ cR))
    no-cell-≤ le =
      no-start-≤ lW (z₁ Y) pY (wA cn)
        (subst (λ v → (proj₁ W , v₁ cL) ≤ (wA cn , v))
          (start-R ac′ u′ q₀′ (lwA cn , proj₂ lW) ll′ A₀′ w′ (SA cn) (reset-z₁ ac F u q₀ lW ll A₀ w Y n)) le)
```

## §3 前提实例

`Y1`: `z₁ = n1`, 读回是 $\mathrm{hs}\,\beta$. `after-n1`: $\Omega_\Lambda$ 的第一步 `n1` 在动作 `Stp` 下的输出接进状态之后, `z₁` 是 $\omega$ 份的 $\Omega_1⨾\dots$ (`refl`); 它的读回满足 `Pos` (`pos-after`).

```agda
  Y1 : ∀ {W} → St W
  Y1 = st zeroD n0 n1

  pos-Y1 : ∀ {W} (lW : LgW L₀ W) → Pos lW (z₁ (Y1 {W}))
  pos-Y1 {W} lW = proj₂ W , hself , hself

  StpI : ∀ {ly W} → Ig ly W
  StpI p lW′ _ Y = Stp Y

  after-n1 : ∀ {ly W₀ W} (ac : AccY ly) (q₀ : W₀ ≤ W) (lW : LgW L₀ W) (ll : LW ly W) (w : D ly W) (Y : St W) →
    z₁ (Y ⊕⟨ lW ⟩ Run ac n1 q₀ lW ll StpI w Y) ≡ z₁ Y ⨾ ω⋅ (Ωd (hs hz) ⨾ yc (d Y) (τ₁ lW))
  after-n1 ac q₀ lW ll w Y = refl

  -- 读回: rd₁ β (z₁ Y ⨾ nl (λ _ → (n1 ⨾ ni …) ⨾ …)) 的第 1 项从 hs (rd₁ β (z₁ Y)) 起
  pos-after : ∀ {W} (lW : LgW L₀ W) (Y : St W) → Pos lW (z₁ Y ⨾ ω⋅ (Ωd (hs hz) ⨾ yc (d Y) (τ₁ lW)))
  pos-after {W} lW Y = b , rd₁-fst lW (proj₂ W) (z₁ Y) , hlim 1 (rd₁-fst lW (hs b) (ni (ss hself) (λ _ _ _ → n1) ⨾ yc (d Y) (τ₁ lW)))
    where
    b : HB T
    b = rd₁ lW (proj₂ W) (z₁ Y)
```

## §4 结论 (按档)

- **[定理]** `reset-z₁`, `reset-z`: 回灌每一格的状态 `z`, `z₁` 为 `n0`. `lossy-row`, `fed-cell`: 两边跑分支的式子 (`refl`). `start-L`, `start-R`: 新种类闭包第 0 格的界, 左 $\mathrm{rd}_1(\beta,z_1Y)$, 右 $\beta$. **`no-cell-≤`**: 前提 `Pos lW (z₁ Y)` 下, 左右这两个世界之间没有 $\le$. `strict`, `no-hs⊲`, `above`.
- **[定理] 前提实例**: `pos-Y1`; `pos-after` 配 `after-n1` (闭项写法 `n1 ⨾ …` 在动作 `Stp` 下的状态).
- **[判断]** 构造一路的关系若在回灌那一行逐格比较世界, 要么状态关系不看 `z₁` 并在 `κc₁` 那一行改用别的比较 (例如右边的第 $k$ 格对左边的第 0 格, 或值), 要么承认这一处右边的世界并不更大. 这不说明回灌不提高值.
