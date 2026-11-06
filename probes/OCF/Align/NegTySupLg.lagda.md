# 带类型折叠到 sup 层, 否定一路 (一): `Lg*` 与 `LgB` 何时不同

> 不含记号. 入口 [NegTySup](NegTySup.lagda.md). 本篇**不依赖**构造一路的接口 `TySupIf` (接口定稿之前写的部分). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** [Fab3Typed](Fab3Typed.lagda.md) 的代价 (1) 说: 一般的 `T` 上 `Lg*` (ℕ-极限只在合法世界里步进) 与 `LgB` (ℕ-极限在一切世界里步进) **不可互推** (判断), 并说 `Ψ-mono` 用 `LgB` 陈述时证不出 (未走通). 本篇把判断写成定理, 并划出两者重合的范围.
>
> **结果.**
>
> 1. **`lg*⇏lgB` (定理, 反例).** 一个种类结构 `Bw (_≡ true)` 与**同一个**合法性 (`ℓB`: `LgW*` 就是 `LgW`, `LgE*` 就是 `LgE`) 上, 一棵 ℕ-极限 `bB` 满足 `Lg*` 而不满足 `LgB`: 它只在不合法的世界 `false` 里不步进. 所以 ℕ-极限处的量词改动本身就分开两者.
> 2. **`lgB⇏lg*` (定理, 反例).** 种类结构 `Bw (_≡ false)` 与合法世界更多的 `ℓA` (`LgW* = ⊤`) 上, 一个 $\Omega$-结点 `ΩA` 满足 `LgB` 而不满足 `Lg*`. 这正是 Fab3Typed 写的机制: `Lg*`-合法的界比 `LgB`-合法的多.
> 3. **`lgB⇒lg*` (定理).** 只要 `LgW* ⇒ LgW` 且 `LgE* ⇒ LgE`, 就有 `LgB ⇒ Lg*`. 所以反例 2 必须让 `LS` 的合法世界比种类结构的多.
> 4. **`Coin`, `coin⇒`, `coin⇐` (定理).** 若 `LS` 与种类结构的合法世界、合法坐标互推, 并且有一个 `Lg*`-合法的**最小世界** $w_0$ (在一切世界之下), 则 `Lg* ↔ LgB`. 最小世界让 "在合法世界里步进" 推出 "在一切世界里步进" (`⊲ᴮ↑`).
> 5. **`coin-⊥`, `coin-step`, `coin-sup` (定理, 一步).** `Coin` 对底 `S⊥`, 对 `step` (配 `step*`), 对 `sup` (配逐分量的 `sup*`) 都保持. 所以 **Fab3Typed 的塔 `T n` 上 `Lg*` 与 `LgB` 互推** (`coinT`), 一切层号 `LH` 的 `Lv x` 配逐分量的 `ℓLv x` 上也互推 (`coinLv`).
> 6. **`Ψ-monoᴮ`, `Ψ-lgᴮ` (定理).** 推论: 塔上 `Ψ-mono` 与 `Ψ-lg` 用 `LgB` 陈述**证得出** (由 Fab3Typed 的 `Lg*` 版经 `coinT` 搬过来). Fab3Typed 代价 (1) 里 "用 `LgB` 陈述证不出" 在塔上不成立; 它只在没有 `Coin` 的 `T` 上是开放的.
>
> **前提实例.** `Bw` 的两个实例都是具体的种类结构, `ℓB`, `ℓA` 是具体的 `LS`; `Coin` 的实例是 `coinT n`, `coinLv x`, `coin-⊥`.
>
> **只否定什么.** 只否定 "对一切 `(T, ℓ)`, `Lg*` 推出 `LgB`" 与反方向. **不否定**: Fab3Typed 的任何定理; 塔与 `Lv` 上的折叠 (那里两者互推); `sup*` 以外的 `sup` 合法性 (若构造一路的 sup 层合法性不是逐分量的, `coin-sup` 不直接适用, 要另查是否仍有最小合法世界).
>
> **对纲领与目标.** "合法性的量词换了" 在 sup 层之前不是代价: 只要每层都有一个合法的最小世界 (界全取 $0$), 两种合法性在值上不可分. 这是树侧的一个判据 (最小合法世界), 不看记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegTySupLg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥; LH; lz; ls; ll; lΩ; Lv)
open import OCF.Align.Fab3Typed
```

## §1 两个反例

`Bw P`: 一个种类, 坐标与世界都是 `Bool`, 界与第一位置都是 `Bool` 的 $\le$, 合法世界由 `P` 给出.

```agda
Le : Bool → Bool → Set
Le false w = ⊤
Le true true = ⊤
Le true false = ⊥

le-rf : ∀ {b} → Le b b
le-rf {b = false} = tt
le-rf {b = true} = tt

le-tr : ∀ {a b c} → Le a b → Le b c → Le a c
le-tr {a = false} p q = tt
le-tr {a = true} {b = true} {c = true} p q = tt
le-tr {a = true} {b = false} () q
le-tr {a = true} {b = true} {c = false} p ()

le-tot : ∀ a b → Le b a ⊎ Le a b
le-tot false b = inj₂ tt
le-tot true false = inj₁ tt
le-tot true true = inj₁ tt

Bw : (Bool → Set) → KS
Bw P = record
  { K = ⊤ ; E = λ _ → Bool ; Wd = Bool ; LgW = P ; _≤w_ = Le ; ≤w-rf = le-rf ; ≤w-tr = le-tr
  ; Bd = λ _ c w → Le c w ; Pr = λ _ _ c c′ → Le c c′
  ; Bd↑ = λ q e → le-tr e q ; cmpK = λ {_} {c} {c′} e e′ lw → le-tot c c′
  ; LgE = λ _ _ → ⊤ ; lgBd = λ _ _ → tt ; bot = λ _ → false ; botBd = λ _ _ → tt }

no1⊲0 : ∀ {S : KS} {w} → ¬ (hs {S} hz ⊲[ w ] hz)
no1⊲0 ()
```

**反例 1.** `P = (_≡ true)`, `ℓB` 与种类结构的合法性逐字相同. `ΩB` 的分支 $0\mapsto0$, $1\mapsto1$; `bB` 的第 0 项是 $1$, 以后都是 `ΩB`. 世界 `true` 里 $1$ 在 `ΩB` 的分支 $1$ 处, 是第一位置; 世界 `false` 里只有坐标 $0$, 不是.

```agda
module Ex1 where
  S₁ : KS
  S₁ = Bw (_≡ true)

  ℓB : LS S₁
  ℓB = record { LgW* = _≡ true ; LgE* = λ _ _ → ⊤ ; lgBd* = λ _ _ → tt }

  gB : Bool → HB S₁
  gB false = hz
  gB true = hs hz

  ΩB : HB S₁
  ΩB = hΩ tt gB

  fB : ℕ → HB S₁
  fB zero = hs hz
  fB (suc n) = ΩB

  bB : HB S₁
  bB = hl fB

  mono-gB : ∀ {w c c′} → Le c c′ → gB c ⊲[ w ] gB c′
  mono-gB {c = false} {c′ = false} p = hself
  mono-gB {c = false} {c′ = true} p = hsuc hself
  mono-gB {c = true} {c′ = false} ()
  mono-gB {c = true} {c′ = true} p = hself

  Lg*-ΩB : Lg* ℓB ΩB
  Lg*-ΩB = (λ lw e e′ p → mono-gB p) , λ { false _ → tt ; true _ → tt }

  st-true : ∀ {w} → w ≡ true → ∀ n → fB n ⊲[ w ] fB (suc n)
  st-true refl zero = hLim {S₁} {c = true} tt hself
  st-true refl (suc n) = hself

  Lg*-bB : Lg* ℓB bB
  Lg*-bB = (λ {w} lw n → st-true lw n) , λ { zero → tt ; (suc n) → Lg*-ΩB }

  ¬st-false : ¬ (hs hz ⊲[ false ] ΩB)
  ¬st-false (hLim {c = false} e p) = no1⊲0 p
  ¬st-false (hLim {c = true} () p)

  ¬LgB-bB : ¬ LgB bB
  ¬LgB-bB (st , _) = ¬st-false (st {w = false} 0)

lg*⇏lgB : Σ KS (λ S → Σ (LS S) (λ ℓ → Σ (HB S) (λ h → Lg* ℓ h × ¬ LgB h)))
lg*⇏lgB = Ex1.S₁ , Ex1.ℓB , Ex1.bB , Ex1.Lg*-bB , Ex1.¬LgB-bB
```

**反例 2.** `P = (_≡ false)`, `ℓA` 的合法世界是一切世界. `ΩA` 的分支 $0\mapsto1$, $1\mapsto0$ (反单调). 种类结构的合法世界只有 `false`, 那里界之下只有坐标 $0$, 单调是空的; `ℓA` 的合法世界含 `true`, 那里 $0\le1$ 要求 $1\lhd0$.

```agda
module Ex2 where
  S₂ : KS
  S₂ = Bw (_≡ false)

  ℓA : LS S₂
  ℓA = record { LgW* = λ _ → ⊤ ; LgE* = λ _ _ → ⊤ ; lgBd* = λ _ _ → tt }

  gA : Bool → HB S₂
  gA false = hs hz
  gA true = hz

  ΩA : HB S₂
  ΩA = hΩ tt gA

  mono-false : ∀ {w c c′} → w ≡ false → Le c w → Le c′ w → Le c c′ → gA c ⊲[ w ] gA c′
  mono-false {c = false} {c′ = false} refl e e′ p = hself
  mono-false {c = true} refl () e′ p
  mono-false {c = false} {c′ = true} refl e () p

  LgB-ΩA : LgB ΩA
  LgB-ΩA = (λ lw e e′ p → mono-false lw e e′ p) , λ { false _ → tt ; true _ → tt }

  ¬Lg*-ΩA : ¬ Lg* ℓA ΩA
  ¬Lg*-ΩA (mo , _) = no1⊲0 (mo {w = true} {c = false} {c′ = true} tt tt tt tt)

lgB⇏lg* : Σ KS (λ S → Σ (LS S) (λ ℓ → Σ (HB S) (λ h → LgB h × ¬ Lg* ℓ h)))
lgB⇏lg* = Ex2.S₂ , Ex2.ℓA , Ex2.ΩA , Ex2.LgB-ΩA , Ex2.¬Lg*-ΩA
```

**`LgB ⇒ Lg*` 只要两条蕴含.** 反例 2 因而必须让 `ℓ` 的合法世界比种类结构的多.

```agda
module _ {T : KS} (ℓ : LS T)
         (lw⇒ : ∀ {w} → LgW* ℓ w → LgW T w) (le⇒ : ∀ {κ c} → LgE* ℓ κ c → LgE T κ c) where
  lgB⇒lg* : ∀ h → LgB h → Lg* ℓ h
  lgB⇒lg* hz l = tt
  lgB⇒lg* (hs h) l = lgB⇒lg* h l
  lgB⇒lg* (hl f) (st , l) = (λ lw n → st n) , (λ n → lgB⇒lg* (f n) (l n))
  lgB⇒lg* (hΩ κ g) (mo , l) = (λ lw e e′ p → mo (lw⇒ lw) e e′ p) , (λ c lc → lgB⇒lg* (g c) (l c (le⇒ lc)))
```

## §2 重合: 合法性互推, 有最小合法世界

```agda
record Coin {T : KS} (ℓ : LS T) : Set where
  field
    lw⇒ : ∀ {w} → LgW* ℓ w → LgW T w
    lw⇐ : ∀ {w} → LgW T w → LgW* ℓ w
    le⇒ : ∀ {κ c} → LgE* ℓ κ c → LgE T κ c
    le⇐ : ∀ {κ c} → LgE T κ c → LgE* ℓ κ c
    w₀  : Wd T
    lw₀ : LgW* ℓ w₀
    w₀≤ : ∀ w → _≤w_ T w₀ w

module _ {T : KS} {ℓ : LS T} (cn : Coin ℓ) where
  open Coin cn

  coin⇒ : ∀ h → Lg* ℓ h → LgB h
  coin⇒ hz l = tt
  coin⇒ (hs h) l = coin⇒ h l
  coin⇒ (hl f) (st , l) = (λ {w} n → ⊲ᴮ↑ {T} (w₀≤ w) (st {w₀} lw₀ n)) , (λ n → coin⇒ (f n) (l n))
  coin⇒ (hΩ κ g) (mo , l) = (λ lw e e′ p → mo (lw⇐ lw) e e′ p) , (λ c lc → coin⇒ (g c) (l c (le⇐ lc)))

  coin⇐ : ∀ h → LgB h → Lg* ℓ h
  coin⇐ = lgB⇒lg* ℓ lw⇒ le⇒
```

**一步: 底, `step`, `sup`.**

```agda
coin-⊥ : Coin ls⊥
coin-⊥ = record
  { lw⇒ = λ _ → tt ; lw⇐ = λ _ → tt ; le⇒ = λ {κ} → e⊥ {κ} ; le⇐ = λ {κ} → e⊥ {κ}
  ; w₀ = tt ; lw₀ = tt ; w₀≤ = λ _ → tt }
  where
  e⊥ : ∀ {κ : ⊥} {c : ⊤} {A B : Set} → A → B
  e⊥ {()}

module _ {T : KS} {ℓ : LS T} (cn : Coin ℓ) where
  private module C = Coin cn

  lwS⇒ : ∀ {w} → LgW* (step* ℓ) w → LgW (step T) w
  lwS⇒ {w} (lw , lb) = C.lw⇒ lw , coin⇒ cn (proj₂ w) lb

  lwS⇐ : ∀ {w} → LgW (step T) w → LgW* (step* ℓ) w
  lwS⇐ {w} (lw , lb) = C.lw⇐ lw , coin⇐ cn (proj₂ w) lb

  leS⇒ : ∀ {κ c} → LgE* (step* ℓ) κ c → LgE (step T) κ c
  leS⇒ {inj₁ κ} l = C.le⇒ l
  leS⇒ {inj₂ _} {c} l = coin⇒ cn c l

  leS⇐ : ∀ {κ c} → LgE (step T) κ c → LgE* (step* ℓ) κ c
  leS⇐ {inj₁ κ} l = C.le⇐ l
  leS⇐ {inj₂ _} {c} l = coin⇐ cn c l

  coin-step : Coin (step* ℓ)
  coin-step = record
    { lw⇒ = lwS⇒ ; lw⇐ = lwS⇐ ; le⇒ = λ {κ} → leS⇒ {κ} ; le⇐ = λ {κ} → leS⇐ {κ}
    ; w₀ = C.w₀ , hz ; lw₀ = C.lw₀ , tt ; w₀≤ = λ w → C.w₀≤ (proj₁ w) , z⊲ᴮ (proj₂ w) }
```

`sup*`: 逐分量的合法性 (世界合法 = 每个分量合法). 这是 `sup` 的 `LgW` 的同形; 构造一路的 sup 层若用别的合法性, 本条要另查.

```agda
sup* : {I : Set} {F : I → KS} → ((i : I) → LS (F i)) → LS (sup I F)
sup* {I} {F} ℓ = record
  { LgW* = λ w → ∀ i → LgW* (ℓ i) (w i)
  ; LgE* = λ κ → LgE* (ℓ (proj₁ κ)) (proj₂ κ)
  ; lgBd* = λ {κ} e lw → lgBd* (ℓ (proj₁ κ)) e (lw (proj₁ κ)) }

coin-sup : {I : Set} {F : I → KS} {ℓ : (i : I) → LS (F i)} → ((i : I) → Coin (ℓ i)) → Coin (sup* {I} {F} ℓ)
coin-sup cn = record
  { lw⇒ = λ lw i → Coin.lw⇒ (cn i) (lw i)
  ; lw⇐ = λ lw i → Coin.lw⇐ (cn i) (lw i)
  ; le⇒ = λ {κ} l → Coin.le⇒ (cn (proj₁ κ)) l
  ; le⇐ = λ {κ} l → Coin.le⇐ (cn (proj₁ κ)) l
  ; w₀ = λ i → Coin.w₀ (cn i)
  ; lw₀ = λ i → Coin.lw₀ (cn i)
  ; w₀≤ = λ w i → Coin.w₀≤ (cn i) (w i) }
```

**塔与层号.** Fab3Typed 的塔 `T n` 配 `ℓT n`; `LFReTy` 的 `Lv x` 配逐分量的 `ℓLv x`.

```agda
coinT : ∀ n → Coin (ℓT n)
coinT zero = coin-⊥
coinT (suc n) = coin-step (coinT n)

ℓLv : ∀ x → LS (Lv x)
coinLv : ∀ x → Coin (ℓLv x)

ℓLv lz = ls⊥
ℓLv (ls x) = step* (ℓLv x)
ℓLv (ll f) = sup* (λ n → ℓLv (f n))
ℓLv (lΩ k g) = sup* (λ { (inj₁ _) → step* (ℓLv k) ; (inj₂ c) → ℓLv (g c) })

coinLv lz = coin-⊥
coinLv (ls x) = coin-step (coinLv x)
coinLv (ll f) = coin-sup (λ n → coinLv (f n))
coinLv (lΩ k g) = coin-sup (λ { (inj₁ _) → coin-step (coinLv k) ; (inj₂ c) → coinLv (g c) })
```

## §3 推论: 塔上折叠的两条一步定理用 `LgB` 陈述

```agda
module _ (n : ℕ) where
  private
    module F = Fold (T n)
    module Th = Fold.Thm (T n) (ℓT n)
    cn  = coinT n
    cn⁺ = coinT (suc n)

  Ψ-monoᴮ : ∀ {W v a b} → LgW (T n) v → LgB (proj₂ W) → LgB {T (suc n)} b →
            a ⊲[ (v , proj₂ W) ] b → F.Ψ W a ⊲[ v ] F.Ψ W b
  Ψ-monoᴮ {W} {v} {a} {b} lv lb l p =
    Th.Ψ-mono {W} {v} {a} {b} (Coin.lw⇐ cn lv) (coin⇐ cn (proj₂ W) lb) (coin⇐ cn⁺ b l) p

  Ψ-lgᴮ : ∀ {W} → LgW (T (suc n)) W → ∀ b → LgB b → LgB (F.Ψ W b)
  Ψ-lgᴮ {W} lW b l = coin⇒ cn (F.Ψ W b) (Th.Ψ-lg {W} (Coin.lw⇐ cn⁺ lW) b (coin⇐ cn⁺ b l))
```

## 结论 (按档)

- **[定理]** `lg*⇏lgB`, `lgB⇏lg*` (反例, 具体的种类结构与 `LS`); `lgB⇒lg*` (两条蕴含之下); `Coin`, `coin⇒`, `coin⇐`; `coin-⊥`, `coin-step`, `sup*`, `coin-sup`; `coinT`, `ℓLv`, `coinLv`; `Ψ-monoᴮ`, `Ψ-lgᴮ`.
- **[判断]** "构造一路的 sup 层合法性是逐分量的" 是本篇对构造一路的预期, 等接口定稿后核对 (入口).
