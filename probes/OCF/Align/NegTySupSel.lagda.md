# 带类型折叠到 sup 层, 否定一路 (三): 留还是坍缩, 裸下标上是判定, 公共上界之下是构造

> 不含记号. 入口 [NegTySup](NegTySup.lagda.md). 本篇**不依赖**构造一路的接口 `TySupIf`. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延 `FEᴴ` 只在标 "条件" 的定理里作前提.
>
> **问题.** [Fab3Typed](Fab3Typed.lagda.md) 的判断: "sup 层要决定留还是坍缩, 下标是 ℕ 时可判定, 是高度时要公共上界". 输出的类型就是高度时, sup 层的种类以高度为下标 (`Lev`, `Lv` 的 $\Omega$-并), 折到目标 $t$ 时, 每个下标 $c$ 要选 "留" (`false`) 或 "坍缩" (`true`). 本篇把这个选择写成两种律, 各在裸下标上与带公共上界时陈述.
>
> - **点律 `PtSel t`**: $t$ 处坍缩, 一切 $c\neq t$ 处留.
> - **严格律 `LtSel w t`**: 留的下标都是 $t$ 的第一位置; $t$ 的第一位置且 $\neq t$ 的下标都留.
>
> **结果.**
>
> 1. **`pt→wdec`, `pt-sep` (定理).** 裸下标上的点律推出相等的弱判定; 对目标 $t_0=\lim_n 0$ 推出分离子 `Sep`: 对一切 $\alpha$, $\alpha$ 全假或 $a_\alpha\neq t_0$. **`pt→WLPO` (定理, 条件 `FEᴴ`).**
> 2. **`lt→LPO` (定理, 无条件).** 若对一切目标 $t$ (只用到 $a_\alpha=\lim_n[\alpha\,n]$ 这一族) 都有裸下标上的严格律, 则 LPO. 严格律比点律多要了 "留的就是第一位置", 所以结论更强 (LPO, 不要外延).
> 3. **`bpt`, `blt` (定理, 构造).** 两种律限制在**同一合法界 $L$ 之下**的下标上 (目标也在 $L$ 之下, 世界合法), 都有构造: 点律由 `StallDxBdec.bdec`, 严格律由 `cmpB` 加 `bdec` 加反对称 (`antisym`).
>
> **前提实例.** `pt-hz`: 目标 $0$ 的裸点律有构造 (按构造子判 $c$ 是不是 $0$); `lt-hz`: 目标 $0$ 的裸严格律有构造 (什么都坍缩). 所以单个目标上的律可满足; 被否定的是对 $t_0$ 的点律 (分离子) 与对一族目标的严格律 (LPO). 经典地 (高度相等与第一位置都可判定) 两者都可满足. `bpt`, `blt` 的前提: 任一合法世界与合法高度 (例如 Fab3Typed 的 `W n`, `Ω n`).
>
> **只否定什么.** 只否定: 裸下标 (对**一切** $c$, 不带公共上界) 上的点律 (到分离子, 有外延时到 WLPO) 与一族目标的严格律 (到 LPO). **不否定**: 下标是 ℕ 的留/坍缩 (ℕ 上相等可判定); 带公共上界的律 (`bpt`, `blt` 是构造); 不按律陈述的折叠 (例如只在折叠实际访问的坐标上选择). 本篇没有关闭任何路线.
>
> **对纲领与目标.** 这是 AGENTS "律带公共上界" 在 sup 层的留/坍缩上的一个实例: 同一个选择, 裸下标上推出 LPO 或分离子, 公共上界之下是构造. 构造一路的接口若把 sup 层的选择写在裸下标上, 就落在 1, 2 里.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegTySupSel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.StallDxBdec using (_<ᴮ_; <s₀; <s; <l₀; <l; <Ω₀; <Ω; wf; irr; toLt; lt→≢; bdec)

LPO : Set
LPO = ∀ (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ Σ ℕ (λ n → α n ≡ true)

WLPO : Set
WLPO = ∀ (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ ¬ (∀ n → α n ≡ false)

t≢f : ¬ (true ≡ false)
t≢f ()
```

## §1 两种律

```agda
module _ {S : KS} where
  record PtSel (t : HB S) : Set where
    field
      sel : HB S → Bool
      at  : sel t ≡ true
      off : ∀ c → ¬ (c ≡ t) → sel c ≡ false

  record LtSel (w : Wd S) (t : HB S) : Set where
    field
      sel   : HB S → Bool
      keep⇒ : ∀ c → sel c ≡ false → c ⊲[ w ] t
      ⇒keep : ∀ c → c ⊲[ w ] t → ¬ (c ≡ t) → sel c ≡ false
```

## §2 裸下标: 点律到分离子

```agda
  pt→wdec : ∀ {t} → PtSel t → ∀ c → ¬ (c ≡ t) ⊎ ¬ ¬ (c ≡ t)
  pt→wdec {t} ps c = go (sel c) refl
    where
    open PtSel ps
    go : ∀ b → sel c ≡ b → ¬ (c ≡ t) ⊎ ¬ ¬ (c ≡ t)
    go false e = inj₁ (λ ct → t≢f (trans (sym at) (trans (cong sel (sym ct)) e)))
    go true e = inj₂ (λ nct → t≢f (trans (sym e) (off c nct)))

  bit : Bool → HB S
  bit true = hs hz
  bit false = hz

  aα : (ℕ → Bool) → HB S
  aα α = hl (λ n → bit (α n))

  t₀ : HB S
  t₀ = hl (λ _ → hz)

  Sep : Set
  Sep = ∀ (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ ¬ (aα α ≡ t₀)

  at-n : HB S → ℕ → HB S
  at-n (hl f) n = f n
  at-n x n = x

  bit0 : ∀ b → bit b ≡ hz → b ≡ false
  bit0 false e = refl
  bit0 true ()

  eq→F : ∀ (α : ℕ → Bool) → aα α ≡ t₀ → ∀ n → α n ≡ false
  eq→F α e n = bit0 (α n) (cong (λ h → at-n h n) e)

  nnF : ∀ (α : ℕ → Bool) n → ¬ ¬ (α n ≡ false) → α n ≡ false
  nnF α n nn with α n
  ... | false = refl
  ... | true = ⊥-elim (nn (λ ()))

  pt-sep : PtSel t₀ → Sep
  pt-sep ps α with pt→wdec ps (aα α)
  ... | inj₁ ne = inj₂ ne
  ... | inj₂ nn = inj₁ (λ n → nnF α n (λ ne → nn (λ e → ne (eq→F α e n))))

  FEᴴ : Set
  FEᴴ = ∀ (f g : ℕ → HB S) → (∀ n → f n ≡ g n) → f ≡ g

  -- 条件: FEᴴ
  pt→WLPO : FEᴴ → PtSel t₀ → WLPO
  pt→WLPO fe ps α with pt-sep ps α
  ... | inj₁ allF = inj₁ allF
  ... | inj₂ ne = inj₂ (λ allF → ne (cong hl (fe _ _ (λ n → cong bit (allF n)))))
```

## §3 裸下标: 一族目标的严格律到 LPO

$1\lhd a_\alpha$ 当且仅当某个 $\alpha\,n$ 为真; $1\neq a_\alpha$ (构造子不同). 所以严格律在 $1$ 处的选择就判定了 $\exists n.\,\alpha\,n$.

```agda
  one⊲→ : ∀ {w} α → hs hz ⊲[ w ] aα α → Σ ℕ (λ n → α n ≡ true)
  one⊲→ {w} α (hlim n p) = n , go (α n) refl p
    where
    no : ¬ (hs hz ⊲[ w ] hz)
    no ()
    go : ∀ b → α n ≡ b → hs hz ⊲[ w ] bit (α n) → α n ≡ true
    go true e p = e
    go false e p = ⊥-elim (no (subst (λ z → hs hz ⊲[ w ] bit z) e p))

  →one⊲ : ∀ {w} α n → α n ≡ true → hs hz ⊲[ w ] aα α
  →one⊲ {w} α n e = hlim n (subst (λ z → hs hz ⊲[ w ] bit z) (sym e) hself)

  one≢a : ∀ α → ¬ (hs hz ≡ aα α)
  one≢a α ()

  lt→LPO : (w : Wd S) → (∀ α → LtSel w (aα α)) → LPO
  lt→LPO w ls α = go (sel (hs hz)) refl
    where
    open LtSel (ls α)
    go : ∀ b → sel (hs hz) ≡ b → (∀ n → α n ≡ false) ⊎ Σ ℕ (λ n → α n ≡ true)
    go false e = inj₂ (one⊲→ α (keep⇒ (hs hz) e))
    go true e = inj₁ (λ n → fz n (α n) refl)
      where
      fz : ∀ n b → α n ≡ b → b ≡ false
      fz n false _ = refl
      fz n true an = ⊥-elim (t≢f (trans (sym e) (⇒keep (hs hz) (→one⊲ α n an) (one≢a α))))
```

**前提实例: 单个目标.** 目标 $0$: 点律按构造子判 (`pt-hz`); 严格律全部坍缩 (`lt-hz`, 因为 $0$ 的第一位置只有 $0$ 自己).

```agda
  pt-hz : PtSel hz
  pt-hz = record { sel = s ; at = refl ; off = o }
    where
    s : HB S → Bool
    s hz = true
    s _ = false
    o : ∀ c → ¬ (c ≡ hz) → s c ≡ false
    o hz ne = ⊥-elim (ne refl)
    o (hs c) ne = refl
    o (hl f) ne = refl
    o (hΩ κ g) ne = refl

  ⊲hz : ∀ {w : Wd S} {c : HB S} → c ⊲[ w ] hz → c ≡ hz
  ⊲hz hself = refl

  lt-hz : ∀ {w : Wd S} → LtSel w hz
  lt-hz = record { sel = λ _ → true ; keep⇒ = λ c () ; ⇒keep = λ c p ne → ⊥-elim (ne (⊲hz p)) }
```

## §4 公共上界之下: 两种律都是构造

律限制在同一合法界 $L$ 之下的下标上. 目标 $t\lhd L$, 世界合法, $L$ 合法.

```agda
  record BPt (w : Wd S) (L t : HB S) : Set where
    field
      sel : ∀ c → c ⊲[ w ] L → Bool
      at  : ∀ (p : t ⊲[ w ] L) → sel t p ≡ true
      off : ∀ c (p : c ⊲[ w ] L) → ¬ (c ≡ t) → sel c p ≡ false

  record BLt (w : Wd S) (L t : HB S) : Set where
    field
      sel   : ∀ c → c ⊲[ w ] L → Bool
      keep⇒ : ∀ c (p : c ⊲[ w ] L) → sel c p ≡ false → c ⊲[ w ] t
      ⇒keep : ∀ c (p : c ⊲[ w ] L) → c ⊲[ w ] t → ¬ (c ≡ t) → sel c p ≡ false

  dpt : ∀ {c t : HB S} → (c ≡ t) ⊎ ¬ (c ≡ t) → Bool
  dpt (inj₁ _) = true
  dpt (inj₂ _) = false

  dpt-at : ∀ {t : HB S} (d : (t ≡ t) ⊎ ¬ (t ≡ t)) → dpt d ≡ true
  dpt-at (inj₁ _) = refl
  dpt-at (inj₂ ne) = ⊥-elim (ne refl)

  dpt-off : ∀ {c t : HB S} (d : (c ≡ t) ⊎ ¬ (c ≡ t)) → ¬ (c ≡ t) → dpt d ≡ false
  dpt-off (inj₁ e) ne = ⊥-elim (ne e)
  dpt-off (inj₂ _) ne = refl

  bpt : ∀ {w L t} → LgW S w → LgB L → t ⊲[ w ] L → BPt w L t
  bpt {w} {L} {t} lw l q = record
    { sel = λ c p → dpt (bdec p q lw l)
    ; at = λ p → dpt-at (bdec p q lw l)
    ; off = λ c p ne → dpt-off (bdec p q lw l) ne }
```

**反对称.** 互为第一位置的两个高度相等 (非自反的第一位置是严格子项, 子项关系良基).

```agda
  lt-tr : ∀ {a b c : HB S} → a <ᴮ b → b <ᴮ c → a <ᴮ c
  lt-tr p <s₀ = <s p
  lt-tr p (<s q) = <s (lt-tr p q)
  lt-tr p (<l₀ n) = <l n p
  lt-tr p (<l n q) = <l n (lt-tr p q)
  lt-tr p (<Ω₀ c) = <Ω c p
  lt-tr p (<Ω c q) = <Ω c (lt-tr p q)

  antisym : ∀ {a b : HB S} {w} → a ⊲[ w ] b → b ⊲[ w ] a → a ≡ b
  antisym p q with toLt p | toLt q
  ... | inj₁ e | _ = e
  ... | inj₂ _ | inj₁ e = sym e
  ... | inj₂ ab | inj₂ ba = ⊥-elim (irr (wf _) (lt-tr ab ba))

  dlt : ∀ {c t : HB S} {w} → (t ⊲[ w ] c) ⊎ (c ⊲[ w ] t) → (c ≡ t) ⊎ ¬ (c ≡ t) → Bool
  dlt (inj₁ _) _ = true
  dlt (inj₂ _) (inj₁ _) = true
  dlt (inj₂ _) (inj₂ _) = false

  dlt-keep⇒ : ∀ {c t : HB S} {w} (r : (t ⊲[ w ] c) ⊎ (c ⊲[ w ] t)) d → dlt r d ≡ false → c ⊲[ w ] t
  dlt-keep⇒ (inj₁ _) _ ()
  dlt-keep⇒ (inj₂ _) (inj₁ _) ()
  dlt-keep⇒ (inj₂ x) (inj₂ _) _ = x

  dlt-⇒keep : ∀ {c t : HB S} {w} (r : (t ⊲[ w ] c) ⊎ (c ⊲[ w ] t)) d → c ⊲[ w ] t → ¬ (c ≡ t) → dlt r d ≡ false
  dlt-⇒keep (inj₁ tc) _ ct ne = ⊥-elim (ne (antisym ct tc))
  dlt-⇒keep (inj₂ _) (inj₁ e) ct ne = ⊥-elim (ne e)
  dlt-⇒keep (inj₂ _) (inj₂ _) ct ne = refl

  blt : ∀ {w L t} → LgW S w → LgB L → t ⊲[ w ] L → BLt w L t
  blt {w} {L} {t} lw l q = record
    { sel = λ c p → dlt (cmpB p q lw l) (bdec p q lw l)
    ; keep⇒ = λ c p → dlt-keep⇒ (cmpB p q lw l) (bdec p q lw l)
    ; ⇒keep = λ c p → dlt-⇒keep (cmpB p q lw l) (bdec p q lw l) }
```

## 结论 (按档)

- **[定理]** `PtSel`, `LtSel`; `pt→wdec`, `pt-sep` (无条件); `pt→WLPO` (条件: `FEᴴ`); `lt→LPO` (无条件); `pt-hz`, `lt-hz` (单个目标的实例); `antisym`; `bpt`, `blt` (公共上界之下的构造).
- **[判断]** `Sep` 与 LPO 经典成立, 在 Agda 里证不出 (与 `Fab2SLsNeg.Sep₂` 同档). "sup 层的留/坍缩就是这两种律之一" 是本篇对构造一路的建模, 接口定稿后对照 (入口).
