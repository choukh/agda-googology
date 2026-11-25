# YiUni 接口：对塔的一切项与 Λ 一致的折叠要满足的律

**非验收文件。判决：接口 (记录与谓词)，没有定理；两个规范实例实填通过，接口定稿 (2026-11-12，此后只增不改)。** `Uni` 是一套折叠：公共上界 `Bd`、各行 (Ω 结点层号 `lc k g` 的 `k` 任意)、第一位置与合法性的保持；`Dom` 是塔与 Λ 的读回域。
律里成对出现的下标都带字面上界 (`Cp`、`Le`、`plus k η y`)。不含完全性；完全性作能力单列 (`CmpFull`, `StpFull`)，否定见 [YiUniNegCmp](YiUniNegCmp.lagda.md)、[YiUniNegStep](YiUniNegStep.lagda.md)。
不否定别的写法。实例在 [YiUniCnt](YiUniCnt.lagda.md) (可数层号)、[YiUniTw2](YiUniTw2.lagda.md) (`tw 2`)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUniIf where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
  using (lev; Way; keep; fold; Ext; Br; plus-lgl; succ; psum; self; Ψn; ΨN; ΩT)
```

## 1 一套折叠

`Bd k` 是层号 `k` 上折叠要的公共上界数据，`bS`、`bL`、`bC` 是孩子层的。Ω 结点层号 `lc k g` 的 `top` 读成层号 `k` 的结点 (分支是各支的 `top`)，
在 `Pre (lc k g)` 里没有字面的位置，所以它在派发 `x` 下保留与否 `ωw`、保留时的分支族 `Kb`、折叠时的链点 `cpt` 都是字段。
链的下一步把第 `η` 支的 `top` 折到结点自己的层 `k`，派发是 `stp`；观察折到目标层，派发是 `obd`。`top-up` 是链行合法要的单调：一对下标是 `η` 与 `η + y`。

```agda
record Uni : Set₁ where
  field
    Bd  : LF → Set
    bS  : ∀ {k} → Bd (suc k) → Bd k
    bL  : ∀ {f} → Bd (lim f) → ∀ n → Bd (f n)
    bC  : ∀ {k g} → Bd (lc k g) → ∀ η → Lgl k η → Bd (g η)
    Ψ   : ∀ m {k} → Bd k → Ext m k → Raw k → Raw m
    cmp : ∀ {k} → Bd k → (q r : Pre k) → Way (lev k q) (lev k r)
    ωw  : ∀ m {k g} → Bd (lc k g) → Ext m (lc k g) → Way m k
    Kb  : ∀ m {k g} → Bd (lc k g) → Ext m (lc k g) → Raw k → Raw m
    stp : ∀ {k g} (V : Bd (lc k g)) η → Lgl k η → Ext k (g η)
    obd : ∀ m {k g} (V : Bd (lc k g)) → Ext m (lc k g) → ∀ η → Lgl k η → Ext m (g η)
    cpt : ∀ {k g} → Bd (lc k g) → ℕ → Raw k
    cpt-lgl : ∀ {k g} (V : Bd (lc k g)) n → Lgl k (cpt V n)

    zero-row : ∀ m {k} (V : Bd k) x → Ψ m V x G.zero ≡ G.top
    suc-row  : ∀ m {k} (V : Bd k) x a → Ψ m V x (G.suc a) ≡ succ m (Ψ m V x a)
    lim-row  : ∀ m {k} (V : Bd k) x f → Ψ m V x (G.lim f) ≡ G.lim (λ n → Ψ m V x (f n))
    node-row : ∀ m {k} (V : Bd k) x r g → Ψ m V x (G.lc r g) ≡
      ΨN m k r (x r) (λ η → Ψ m V x (g η)) (λ η → Ψ (lev k r) V (cmp V r) (g η))
    em-rowˢ : ∀ m {k} (V : Bd (suc k)) x a → Ψ m V x (G.em tt a) ≡ Ψ m (bS V) (λ r → x (inj₂ r)) a
    em-rowˡ : ∀ m {f} (V : Bd (lim f)) x n a → Ψ m V x (G.em n a) ≡ Ψ m (bL V n) (λ r → x (n , r)) a
    em-rowᶜ : ∀ m {k g} (V : Bd (lc k g)) x η l a →
      Ψ m V x (G.em (η , l) a) ≡ Ψ m (bC V η l) (λ r → x (η , l , r)) a
    top-row⁰ : ∀ m (V : Bd zero) x → Ψ m V x G.top ≡ succ m G.top
    top-rowˢ : ∀ m {k} (V : Bd (suc k)) x → Ψ m V x G.top ≡
      Ψn m k (x (inj₁ tt)) (λ η → Ψ m (bS V) (λ r → x (inj₂ r)) η) (λ η → Ψ k (bS V) (self k) η)
    top-rowˡ : ∀ m {f} (V : Bd (lim f)) x → Ψ m V x G.top ≡
      G.lim (psum m (λ n → Ψ m (bL V n) (λ r → x (n , r)) G.top))
    top-rowᶜ : ∀ m {k g} (V : Bd (lc k g)) x → Ψ m V x G.top ≡
      ΩT m k (ωw m V x) (Kb m V x)
        (λ n → Ψ m (bC V (cpt V n) (cpt-lgl V n)) (obd m V x (cpt V n) (cpt-lgl V n)) G.top)
    cpt-zero : ∀ {k g} (V : Bd (lc k g)) → cpt V 0 ≡ G.top
    cpt-suc  : ∀ {k g} (V : Bd (lc k g)) n → cpt V (suc n) ≡
      plus k (cpt V n) (Ψ k (bC V (cpt V n) (cpt-lgl V n)) (stp V (cpt V n) (cpt-lgl V n)) G.top)

    Ψ-lgl : ∀ m {k} (V : Bd k) x ξ → Lgl k ξ → Lgl m (Ψ m V x ξ)
    Ψ-cp  : ∀ m {k} (V : Bd k) x {ξ ξ′} → Cp k ξ ξ′ → Cp m (Ψ m V x ξ) (Ψ m V x ξ′)
    Kb-br : ∀ m {k g} (V : Bd (lc k g)) x → Br (layer k) m (Kb m V x)
    top-up : ∀ m {k g} (V : Bd (lc k g)) x η l y ly →
      Cp m (Ψ m (bC V η l) (obd m V x η l) G.top)
           (Ψ m (bC V (plus k η y) (plus-lgl k η y l ly)) (obd m V x (plus k η y) (plus-lgl k η y l ly)) G.top)
```

## 2 读回域

塔的各项与 Λ 有公共上界数据；闭项是 `Ψ zero (bd-Λ) (λ _ → fold) G.top`。规范实例只填到有限的项 (`DomTo`)。

```agda
record Dom (U : Uni) : Set where
  open Uni U
  field
    bd-tw : ∀ n → Bd (tw n)
    bd-Λ  : Bd Λ

DomTo : Uni → ℕ → Set
DomTo U zero = Uni.Bd U zero
DomTo U (suc n) = DomTo U n × Uni.Bd U (tw (suc n))
```

## 3 能力：派发完全

`At m j`：目标层 `m` 有层号 `j` 的槽位。派发完全：能保留处都保留。接口不要求这些；它们是候选的额外能力。

```agda
At : LF → LF → Set
At m j = Σ (Pre m) λ s → lev m s ≡ j

IsKeep : ∀ {m j} → Way m j → Set
IsKeep (keep s e) = ⊤
IsKeep fold = ⊥

Full : ∀ m k → Ext m k → Set
Full m k x = ∀ r → At m (lev k r) → IsKeep (x r)

CmpFull : (U : Uni) → ∀ {k} → Uni.Bd U k → Set
CmpFull U {k} V = ∀ q → Full (lev k q) k (Uni.cmp U V q)

StpFull : (U : Uni) → ∀ {k g} → Uni.Bd U (lc k g) → ∀ η → Lgl k η → Set
StpFull U {k} {g} V η l = Full k (g η) (Uni.stp U V η l)
```
