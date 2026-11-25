# YiOmFold：目标在一支里时 `top` 的保留行，分支取相对坐标

**判决 (编译定理)：目标在第 `η` 支的位置 `r` 上、层号 `j` 里有层号 0 的槽位时，`top` 的根保留在那个槽位上 (`rowᴿ-kept`)，行合法，没有前提。
分支族对 `δ` 累加，第 `d` 项是坐标 `η + nrm d` 那一支的 `top` 折到目标：目标的位置沿 `η ⊲ η + nrm d` 的字面路径搬进那一支，用上一轮的 `Φᵐ`，
它问的比较就是 `compare-link` 在这条路径上的值 (`rel-compare`)。** 与本该有的行差两处：分支只取相对的归一坐标，并沿 `δ` 的路径累加。
不处理已经放在别的支的槽位上的结点 (那里没有路径)；没有值定理。归一在 [YiOmFoldNorm](YiOmFoldNorm.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiOmFoldRel where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw1; raw0-Nested)
open import OCF.Align.YiIrrIf using (R; _+ʳ_; read0; read0-cp; read0-legal; Legal)
open import OCF.Align.YiIrrFbRaw using (Cp-tr)
open import OCF.Align.YiIrrFoldBase using (add-legal)
open import OCF.Align.YiLvIf using (Plain; lev; lev-plain; shift; Tri; Kept)
open import OCF.Align.YiLvFoldAdd using (plus; rawAlg; add-weak; add-lgl; add-ns)
open import OCF.Align.YiLvFoldBase using (Way; keep)
open import OCF.Align.YiLvNegCanon using (ccompare)
open import OCF.Align.YiLvNegCum using (weak)
open import OCF.Align.YiRawIf using (Tgt; base; at; dispatch; tri→way; RawFold)
open import OCF.Align.YiRawFoldBase using (Ext; mix; NdR; nd; Ψn; Ψn-legal; Ψn-nested; Ψn-kept)
open import OCF.Align.YiRawFold using (Ψ; Ψ-pos; Ψ-legal; Ψ-nested; Φᵐ; rawFold)
open import OCF.Align.YiRawNegOmega using (K₂ω; root₂; br; Link; compare-link)
open import OCF.Align.YiOmFoldBase using (rplain)
open import OCF.Align.YiOmFoldNorm using (nrm; nrm-legal)
```

## 1 相对坐标那一支，与搬进去的目标位置

目标位置 `br η e r` 带相关的守卫。坐标 `η + nrm δ`：`1 ⊲ η ⊲ η + nrm δ` 的路径由加法给出，合法性由 `η` 的与归一的给出，都不看 `δ` 的守卫。
`read0 (η + nrm δ)` 是目标层与那一支各位置的字面公共上界。

```agda
module Rel (η : R) (e : Gd zero raw1 η) (r : Pre (read0 η)) where

  j : LF
  j = lev (read0 η) r

  pj : Plain j
  pj = lev-plain (read0 η) (rplain η) r

  ηᵟ : R → R
  ηᵟ δ = η +ʳ nrm δ

  lᵟ : ∀ δ → Lgl zero (ηᵟ δ)
  lᵟ δ = add-legal η (nrm δ) (proj₁ (proj₂ e)) (nrm-legal δ)

  eᵟ : ∀ δ → Gd zero raw1 (ηᵟ δ)
  eᵟ δ = Cp-tr zero (proj₁ e) (weak η (nrm δ)) , lᵟ δ , raw0-Nested (ηᵟ δ)

  linkᵟ : ∀ δ r′ → Link (br η e r) (br (ηᵟ δ) (eᵟ δ) r′)
  linkᵟ δ r′ = inj₁ (weak η (nrm δ))

  Kᵟ : R → LF
  Kᵟ δ = read0 (ηᵟ δ)

  Lᵟ : ∀ δ → Legal (Kᵟ δ)
  Lᵟ δ = read0-legal (ηᵟ δ) (lᵟ δ)

  qᵟ : ∀ δ → Pre (Kᵟ δ)
  qᵟ δ = proj₁ (shift (read0-cp (ηᵟ δ) (weak η (nrm δ))) r)

  eqᵟ : ∀ δ → lev (Kᵟ δ) (qᵟ δ) ≡ j
  eqᵟ δ = proj₂ (shift (read0-cp (ηᵟ δ) (weak η (nrm δ))) r)

  -- 那一支里折叠问的比较, 就是 compare-link 在这条路径上的值.
  rel-compare : ∀ δ r′ →
    compare-link (br η e r) (br (ηᵟ δ) (eᵟ δ) r′) (linkᵟ δ r′) ≡
    subst (λ z → Tri z (lev (Kᵟ δ) r′)) (eqᵟ δ)
      (ccompare (Kᵟ δ) (rplain (ηᵟ δ)) (Lᵟ δ) (qᵟ δ) r′)
  rel-compare δ r′ = refl

  rel-dispatch : ∀ δ r′ →
    dispatch (Kᵟ δ) (rplain (ηᵟ δ)) (Lᵟ δ) (at (qᵟ δ)) r′ ≡
    tri→way (ccompare (Kᵟ δ) (rplain (ηᵟ δ)) (Lᵟ δ) (qᵟ δ) r′)
  rel-dispatch δ r′ = refl
```

## 2 一支的折叠，搬回目标层

`Φᵐ` 的输出在 `Raw (lev (Kᵟ δ) (qᵟ δ))` 里，这个层号与 `j` 命题相等。值与两份证书捆在一起沿等式搬一次。

```agda
  Val : LF → Set
  Val m = Σ (Raw m) λ y → Lgl m y × Nested m y

  foldᵟ : ∀ δ → Val (lev (Kᵟ δ) (qᵟ δ))
  foldᵟ δ =
    Φᵐ (Kᵟ δ) (rplain (ηᵟ δ)) (Lᵟ δ) (at (qᵟ δ)) G.top tt tt ,
    RawFold.legal rawFold (Kᵟ δ) (rplain (ηᵟ δ)) (Lᵟ δ) (at (qᵟ δ)) G.top tt tt ,
    Ψ-nested (lev (Kᵟ δ) (qᵟ δ)) (Kᵟ δ) (rplain (ηᵟ δ)) (Lᵟ δ)
      (mix (dispatch (Kᵟ δ) (rplain (ηᵟ δ)) (Lᵟ δ) (at (qᵟ δ)))) G.top tt tt

  F : ∀ δ → Val j
  F δ = subst Val (eqᵟ δ) (foldᵟ δ)
```

## 3 行

`s` 是 `j` 里层号 0 的槽位 (`compare-link root₂ (br η e r)` 在 "之上" 那一种交出的就是它)。第一支：第一支的 `top` (主干上层号 0 的结点) 保留在 `s` 上。
分支族 `S` 沿 `δ` 的路径累加，不看 `δ` 的守卫。根上的结点取 `YiRawFoldBase.Ψn` 的保留行；它自己那一层 (层号 0) 的分支取那一支的目标层 0 折叠，保留时用不到。

```agda
  module Row (s : Pre j) (z : lev j s ≡ zero) where

    w₁ : (r₁ : Pre (suc zero)) → Way j (lev (suc zero) r₁)
    w₁ (inj₁ _) = keep s z

    t₁ : Raw j
    t₁ = Ψ j (suc zero) tt tt (mix w₁) G.top tt tt

    t₁-legal : Lgl j t₁
    t₁-legal = Ψ-legal j pj (suc zero) tt tt (mix w₁) tt G.top tt tt

    t₁-nested : Nested j t₁
    t₁-nested = Ψ-nested j (suc zero) tt tt (mix w₁) G.top tt tt

    S : R → Raw j
    S G.zero = t₁
    S (G.suc d) = plus j (S d) (proj₁ (F d))
    S (G.lim f) = G.lim (λ n → S (f n))
    S G.top = t₁

    S-first : ∀ δ → Cp j t₁ (S δ)
    S-first G.zero = inj₁ refl
    S-first (G.suc d) = Cp-tr j (S-first d) (add-weak j (rawAlg j) (S d) (proj₁ (F d)))
    S-first (G.lim f) = inj₂ (zero , S-first (f zero))
    S-first G.top = inj₁ refl

    S-cp : ∀ {δ} δ′ → Cp zero δ δ′ → Cp j (S δ) (S δ′)
    S-cp δ′ (inj₁ refl) = inj₁ refl
    S-cp (G.suc d) (inj₂ p) =
      Cp-tr j (S-cp d p) (add-weak j (rawAlg j) (S d) (proj₁ (F d)))
    S-cp (G.lim f) (inj₂ (n , p)) = inj₂ (n , S-cp (f n) p)

    S-legal : ∀ δ → Lgl zero δ → Lgl j (S δ)
    S-legal G.zero l = t₁-legal
    S-legal (G.suc d) l =
      add-lgl j pj (rawAlg j) (S d) (proj₁ (F d)) (S-legal d l) (proj₁ (proj₂ (F d)))
    S-legal (G.lim f) (st , lf) =
      (λ n → S-cp (f (suc n)) (st n)) , (λ n → S-legal (f n) (lf n))
    S-legal G.top l = t₁-legal

    S-nested : ∀ δ → Nested j (S δ)
    S-nested G.zero = t₁-nested
    S-nested (G.suc d) =
      add-ns j (rawAlg j) (S d) (proj₁ (F d)) (S-nested d) (proj₂ (proj₂ (F d)))
    S-nested (G.lim f) = λ n → S-nested (f n)
    S-nested G.top = t₁-nested

    own₀ : (δ : R) → .(Gd zero raw1 δ) → R
    own₀ δ e′ = Φᵐ (Kᵟ δ) (rplain (ηᵟ δ)) (Lᵟ δ) base G.top tt tt

    N : NdR j zero
    N = nd raw1 tt tt t₁ (λ δ e′ → S δ) own₀
      (λ δ e′ → RawFold.legal rawFold (Kᵟ δ) (rplain (ηᵟ δ)) (Lᵟ δ) base G.top tt tt)
      (λ δ e′ → raw0-Nested (own₀ δ e′))
      (λ δ e′ → Ψ-pos zero (Kᵟ δ) (rplain (ηᵟ δ)) (Lᵟ δ)
        (mix (dispatch (Kᵟ δ) (rplain (ηᵟ δ)) (Lᵟ δ) base)) G.top tt tt)

    rowᴿ : Raw j
    rowᴿ = Ψn j zero tt (keep s z) N

    rowᴿ-legal : Lgl j rowᴿ
    rowᴿ-legal = Ψn-legal j zero tt (keep s z) N
      (record
        { seed = inj₁ refl , tt , tt
        ; tg = λ δ e′ → S-first δ
        ; dir = λ δ e′ δ′ e″ q → S-cp δ′ (proj₁ q)
        ; lt = t₁-legal
        ; lg = λ δ e′ → S-legal δ (proj₁ (proj₂ e′))
        ; lkʳ = λ δ e′ →
            RawFold.legal rawFold (Kᵟ δ) (rplain (ηᵟ δ)) (Lᵟ δ) base G.top tt tt
        ; nkʳ = λ δ e′ → raw0-Nested (own₀ δ e′) })

    rowᴿ-nested : Nested j rowᴿ
    rowᴿ-nested = Ψn-nested j zero tt (keep s z) N
      (record
        { seed = inj₁ refl , tt , tt
        ; lcʳ = tt
        ; ncʳ = tt
        ; nt = t₁-nested
        ; ng = λ δ e′ → S-nested δ
        ; lkʳ = λ δ e′ →
            RawFold.legal rawFold (Kᵟ δ) (rplain (ηᵟ δ)) (Lᵟ δ) base G.top tt tt
        ; nkʳ = λ δ e′ → raw0-Nested (own₀ δ e′) })

    -- 保留律: 根 (层号 0) 是目标层里的保留结点.
    rowᴿ-kept : Kept j zero rowᴿ
    rowᴿ-kept = Ψn-kept j pj zero tt (keep s z) N tt

    -- 第 suc d 支: 前面的和, 加上坐标 η + nrm d 那一支的 top 折到目标.
    S-row : ∀ d → S (G.suc d) ≡ plus j (S d) (proj₁ (F d))
    S-row d = refl
```

## 4 规范实例：目标在第 3 支的根上

第 3 支的根层号是 2，层号 0 的槽位在它下面两格。`compare-link` 给出 "之上" 与这个槽位。

```agda
three : R
three = G.suc (G.suc (G.suc G.zero))

e₃ : Gd zero raw1 three
e₃ = inj₂ (inj₂ (inj₁ refl)) , tt , tt

open Rel three e₃ (inj₁ tt)

slot₃ : Pre j
slot₃ = inj₂ (inj₁ tt)

slot₃-level : lev j slot₃ ≡ zero
slot₃-level = refl

open Row slot₃ slot₃-level

row₃ : Raw (suc (suc zero))
row₃ = rowᴿ

row₃-legal : Lgl (suc (suc zero)) row₃
row₃-legal = rowᴿ-legal

row₃-kept : Kept (suc (suc zero)) zero row₃
row₃-kept = rowᴿ-kept
```
