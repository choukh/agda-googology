# 树的算子语言 (七): 回灌闭包是一条定理

> 不含记号. 入口 [TLOps](TLOps.lagda.md). **`Clo`: 任何字面单调的族, 从一个有第一位置证据的起点, 回灌闭包都有 `Lit₀` (所以有 `HS`).** 对族的形状没有别的要求, 不分阶段. 这是最外层的闭包: 链点是输出的字面读出, 嫁接上一个链点作第一位置 (`graft₀`), **没有前缀, 没有累加.**
>
> 实例: `Top p` 取 $\eta\mapsto\psi_0(\Omega_{\Omega\cdot p+\eta})$, 读 $\psi_0(\Omega_{\Omega\cdot(p+1)})$; `Feed` 取 $\eta\mapsto\psi_0(\Omega_{\Omega\cdot\eta})$, 这就是 `CrossMClosed.T⊤` 的同类: 回灌作高度, 读 $\psi_0(\Omega_{\Omega^2})$. 读法是判断.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLOpsClo where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Free.Level as FL
open FL using (HS; toLevel; Ordᴵ; _≅_; z≅; s≅; l≅)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit
open import OCF.Align.TLOpsW
open import OCF.Align.TLOpsEq
open import OCF.Align.TLOpsLe
open import OCF.Align.TLOpsMain
open import OCF.Align.TLOpsPre
```

## §1 单调族

`Y`: 世界 (下标) 到第 0 层的值. `up`: 下标的第一位置给值的第一位置. 这是族要提供的全部东西.

```agda
record Fam : Set where
  field
    Y   : (η : A) → Gw η → Ord₀
    Yl  : ∀ η g → Lit₀ (Y η g)
    up  : ∀ {a b} (ga : Gw a) (gb : Gw b) → a ⊲ b → Y a ga ⊴₀ Y b gb
    η₀  : A
    g₀′ : Gw η₀
    x₀  : Ord₀
    e₀  : η₀ ≈ᴬ rd x₀
    s₀  : x₀ ⊴₀ Y η₀ g₀′
```

## §2 闭包定理

链: $y_0=Y(\eta_0)$, $\eta_{n+1}\approx\mathrm{rd}\,y_n$, $y_{n+1}=Y(\eta_{n+1})$, 输出 $\lim y_n$. `rd` 是字面读出, 差只有逐点相等的函数.

```agda
module Clo (F : Fam) where
  open Fam F

  record Cell : Set where
    field
      y    : Ord₀
      η    : A
      tie  : η ≈ᴬ rd y
      gη   : Gw η
      mono : y ⊴₀ Y η gη
  open Cell public

  start : Cell
  start = record { y = y₁ ; η = g (gE r) ; tie = eq (gE r) ; gη = gr₁ ; mono = up g₀′ gr₁ (at r) }
    where
    y₁ = Y η₀ g₀′
    r : Gr (rd y₁) η₀
    r = graft₀ s₀ (lit y₁ (Yl η₀ g₀′)) (el η₀ e₀ (lgw g₀′))
    gr₁ : Gw (g (gE r))
    gr₁ = gw (lg (gE r)) (⊲-tr (pos g₀′) (at r))

  -- 回灌一步: 上一格的输出读成下标, 接在上一格的下标上
  step : Cell → Cell
  step c = record { y = y₁ ; η = g (gE r) ; tie = eq (gE r) ; gη = gr₁ ; mono = up (gη c) gr₁ (at r) }
    where
    y₁ = Y (η c) (gη c)
    r : Gr (rd y₁) (η c)
    r = graft₀ (mono c) (lit y₁ (Yl (η c) (gη c))) (el (η c) (tie c) (lgw (gη c)))
    gr₁ : Gw (g (gE r))
    gr₁ = gw (lg (gE r)) (⊲-tr (pos (gη c)) (at r))

  cell : ℕ → Cell
  cell zero = start
  cell (suc n) = step (cell n)

  ys : ℕ → Ord₀
  ys n = y (cell n)

  T : Ord₀
  T = FL.lim ys

  Lit-T : Lit₀ T
  Lit-T = (λ n → mono (cell n)) , each
    where
    each : ∀ n → Lit₀ (ys n)
    each zero = Yl η₀ g₀′
    each (suc n) = Yl (η (cell n)) (gη (cell n))

  HS-T : HS T
  HS-T = HS₀ T Lit-T

  lv : Ordᴵ
  lv = toLevel T HS-T

  -- 链点互相第一位置, 输出是回灌
  η-step : ∀ n → η (cell n) ⊲ η (cell (suc n))
  η-step n = at (graft₀ (mono (cell n)) (lit (ys (suc n)) (Yl (η (cell n)) (gη (cell n)))) (el (η (cell n)) (tie (cell n)) (lgw (gη (cell n)))))

  feed : ∀ n → ys (suc n) ≡ Y (η (cell n)) (gη (cell n))
  feed n = refl

  tied : ∀ n → η (cell n) ≈ᴬ rd (ys n)
  tied n = tie (cell n)
```

## §3 实例

`Tp p a`: 数据树的闭包走前缀 ([TLOpsPre](TLOpsPre.lagda.md)). 世界 `a` 或 `one`.

```agda
1⊴₀ : ∀ {p a u} (x : 𝓞 p a u) (H : Hk p azero) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (tm : azero ⊲ m) (am : a ⊲ m) (d : G (ψ azero azero H x gu m gm um tm am)) → FL.suc FL.zero ⊴₀ force d
1⊴₀ x H gu m gm um tm am d = fo⊴ (Ωfst azero azero H x gu m gm um tm am) (gw (gs g0)) d

-- 高度固定, 层作下标: η ↦ ψ₀(Ω_{Ω·p+η})
module Top (p : A) (lp : Lg p) where
  Yt : (η : A) → Gw η → Ord₀
  Yt η g = Tᵖ p η η lp g C.self

  Yt-up : ∀ {a b} (ga : Gw a) (gb : Gw b) → a ⊲ b → Yt a ga ⊴₀ Yt b gb
  Yt-up {a} {b} ga gb P = fo⊴ (ψL′ azero azero (hk₀ lp) (hk₀ lp) (Ω⊴ p P) g₀ g₀ a ga (pos ga) (z⊲ a) C.self b gb (pos gb) (z⊲ b) C.self) (G-Tᵖ p a a lp ga C.self) (G-Tᵖ p b b lp gb C.self)

  F : Fam
  F = record
    { Y = Yt ; Yl = λ η g → Lit-Tᵖ p η η lp g C.self ; up = Yt-up
    ; η₀ = one ; g₀′ = g₀ ; x₀ = FL.suc FL.zero ; e₀ = s≈ z≈
    ; s₀ = 1⊴₀ (Ω̇ p one) (hk₀ lp) g₀ one g₀ (pos g₀) (z⊲ one) C.self (G-Tᵖ p one one lp g₀ C.self) }

  open Clo F public using (T; HS-T; Lit-T; lv)

-- 回灌作高度: η ↦ ψ₀(Ω_{Ω·η})
module Feed where
  Yf : (η : A) → Gw η → Ord₀
  Yf η g = Tᵖ η azero one (lgw g) g₀ (z⊲ one)

  Yf-up : ∀ {a b} (ga : Gw a) (gb : Gw b) → a ⊲ b → Yf a ga ⊴₀ Yf b gb
  Yf-up {a} {b} ga gb P = fo⊴ (ψL′ azero azero (hk₀ (lgw ga)) (hk₀ (lgw gb)) (Ωh⊴ P) g₀ g₀ one g₀ (pos g₀) (z⊲ one) (z⊲ one) one g₀ (pos g₀) (z⊲ one) (z⊲ one)) (G-Tᵖ a azero one (lgw ga) g₀ (z⊲ one)) (G-Tᵖ b azero one (lgw gb) g₀ (z⊲ one))

  F : Fam
  F = record
    { Y = Yf ; Yl = λ η g → Lit-Tᵖ η azero one (lgw g) g₀ (z⊲ one) ; up = Yf-up
    ; η₀ = one ; g₀′ = g₀ ; x₀ = FL.suc FL.zero ; e₀ = s≈ z≈
    ; s₀ = 1⊴₀ (Ω̇ one azero) (hk₀ tt) g₀ one g₀ (pos g₀) (z⊲ one) (z⊲ one) (G-Tᵖ one azero one tt g₀ (z⊲ one)) }

  open Clo F public using (T; HS-T; Lit-T; lv)
```
