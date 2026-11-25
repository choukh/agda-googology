# YiGenFold：对坐标谓词参数化的定义域、派发与 `top` 的行

**判决 (编译定理，一步定理)：分支槽位结点所在的支的坐标都满足一个可判定的谓词 `Good`，且满足它的坐标两两有字面的第一位置路径时，
`YiGenFold` 的折叠在这个定义域上问到的派发全都完全 (`honestˢ`)：目标与结点或者有一个在主干上，或者两支的坐标由 `join` 相连，三路取 `compare-link`。
`top` 在这样的目标下的行 `rowᶠ` 合法，根保留，分支族在 `Good` 的坐标上满足保留律 (`S-keep`)。** 定义域 `D` 对加法、ω 倍、`keepAll` 封闭。新用到的字段只有 "坐标两两相连"。
`rowᶠ` 仍是替代行 (分支族累加；不满足 `Good` 的坐标取相对坐标)。不否定别的定义域；`Good` 取 "不含极限" 的实例在 [YiGenFoldFin](YiGenFoldFin.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiGenFoldDom where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw1; raw0-Nested; cO)
open import OCF.Align.YiIrrIf using (R; _+ʳ_; read0; read0-legal)
open import OCF.Align.YiIrrFbRaw using (Cp-tr)
open import OCF.Align.YiLvIf using (Plain; lev; lev-plain; Tri; below; above; same; Kept)
open import OCF.Align.YiLvFoldAdd using (Pos; add; plus; rawAlg; add-weak; add-lgl; add-ns)
open import OCF.Align.YiLvFoldBase using (Way; keep; fold)
open import OCF.Align.YiLvFoldFin using (IsKeep)
open import OCF.Align.YiLvNegCompare using (At)
open import OCF.Align.YiLvNegCum using (weak)
open import OCF.Align.YiRawIf using (IsLim; tri→way; tri-complete)
open import OCF.Align.YiRawFoldBase using (mix; NdR; nd; Ψn; Ψn-legal; Ψn-nested; Ψn-pos; Ψn-kept)
open import OCF.Align.YiRawFold using (Ψ; Ψ-legal; Ψ-nested; Ψ-pos; Complete)
open import OCF.Align.YiRawFoldTw3 using (T₃ᵐ; T₃ᵐ-legal)
open import OCF.Align.YiRawNegOmega using (K₂ω; root₂; first₂; br; compare-zero; compare-link; flip)
open import OCF.Align.YiOmFoldBase
open import OCF.Align.YiOmFold using (F₀; t₀)
open import OCF.Align.YiOmFoldNorm using (Nod; nS; nL; keepAll; psumΩ; νᴮ; nrm; γ; KT)
open import OCF.Align.YiOmFoldRel using (module Rel)
open import OCF.Align.YiGenIf using (OwnFold; Honest)
open import OCF.Align.YiGenFold
```

## 1 定义域

`D ξ`：没有嵌入的孩子；分支槽位上的结点所在的支的坐标满足 `Good`。主干上的结点与 `top` 不受限制。

```agda
module Dm (Good : R → Set) where

  D : RΩ → Set
  D G.zero = ⊤
  D (G.suc a) = D a
  D (G.lim f) = ∀ n → D (f n)
  D (G.lc (inj₁ (inj₁ _)) c t g) = D t × (∀ η (e : Gd zero c η) → D (g η e))
  D (G.lc (inj₂ (inj₁ (inj₁ _))) c t g) = D t × (∀ η (e : Gd zero c η) → D (g η e))
  D (G.lc (inj₂ (inj₂ (η , e , r))) c t g) =
    Good η × D t × (∀ ζ (e′ : GdL (read0 η) r c ζ) → D (g ζ e′))
  D (G.em i a) = ⊥
  D G.top = ⊤

  GoodP : Pre K₂ω → Set
  GoodP (inj₁ (inj₁ _)) = ⊤
  GoodP (inj₂ (inj₁ (inj₁ _))) = ⊤
  GoodP (inj₂ (inj₂ (η , e , r))) = Good η
  GoodP (inj₁ (inj₂ ()))
  GoodP (inj₂ (inj₁ (inj₂ ())))

  D-first : ∀ p c t g → D (G.lc p c t g) → D t
  D-first (inj₁ (inj₁ _)) c t g d = proj₁ d
  D-first (inj₂ (inj₁ (inj₁ _))) c t g d = proj₁ d
  D-first (inj₂ (inj₂ (η , e , r))) c t g d = proj₁ (proj₂ d)

  D-branch : ∀ p c t g → D (G.lc p c t g) → ∀ ζ (e : GdL K₂ω p c ζ) → D (g ζ e)
  D-branch (inj₁ (inj₁ _)) c t g d = proj₂ d
  D-branch (inj₂ (inj₁ (inj₁ _))) c t g d = proj₂ d
  D-branch (inj₂ (inj₂ (η , e , r))) c t g d = proj₂ (proj₂ d)

  D-good : ∀ p c t g → D (G.lc p c t g) → GoodP p
  D-good (inj₁ (inj₁ _)) c t g d = tt
  D-good (inj₂ (inj₁ (inj₁ _))) c t g d = tt
  D-good (inj₂ (inj₂ (η , e , r))) c t g d = proj₁ d
```

## 2 封闭

加法：`x + top` 是主干上的结点 (`topᴬ`)。`keepAll` 的结点由 `ν` 造，`ν` 落在定义域里就封闭。

```agda
  add₀D : ∀ x → D x → ∀ (a : R) → D (add zero alg₀ x a)
  add₀D x dx G.zero = dx
  add₀D x dx (G.suc a) = add₀D x dx a
  add₀D x dx (G.lim f) = λ n → add₀D x dx (f n)
  add₀D x dx G.top = dx

  add₁D : ∀ x → D x → D (add (suc zero) alg₁ x G.top)
  add₁D x dx = add₀D x dx raw1 , (λ η e → add₀D x dx η)

  plusD : ∀ x a → D x → D a → D (plusΩ x a)
  plusD x G.zero dx da = dx
  plusD x (G.suc a) dx da = plusD x a dx da
  plusD x (G.lim f) dx da = λ n → plusD x (f n) dx (da n)
  plusD x (G.lc (inj₁ (inj₁ _)) c t g) dx (dt , dg) =
    plusD x t dx dt , (λ η e → plusD x (g η e) dx (dg η e))
  plusD x (G.lc (inj₂ (inj₁ (inj₁ _))) c t g) dx (dt , dg) =
    plusD x t dx dt , (λ η e → plusD x (g η e) dx (dg η e))
  plusD x (G.lc (inj₂ (inj₂ (η , e , r))) c t g) dx (h , dt , dg) =
    h , plusD x t dx dt , (λ ζ e′ → plusD x (g ζ e′) dx (dg ζ e′))
  plusD x G.top dx da =
    add₁D x dx , (λ η e → add₀D (add (suc zero) alg₁ x G.top) (add₁D x dx) η)

  copiesD : ∀ y → D y → ∀ n → D (copiesΩ y n)
  copiesD y dy zero = dy
  copiesD y dy (suc n) = plusD y (copiesΩ y n) dy (copiesD y dy n)

  psumD : ∀ g → (∀ n → D (g n)) → ∀ n → D (psumΩ g n)
  psumD g dg zero = dg zero
  psumD g dg (suc n) = plusD (psumΩ g n) (g (suc n)) (psumD g dg n) (dg (suc n))

  F₀D : ∀ a → D (F₀ a)
  F₀D G.zero = tt
  F₀D (G.suc a) = copiesD (F₀ a) (F₀D a)
  F₀D (G.lim f) = λ n → F₀D (f n)
  F₀D G.top = copiesD G.top tt

  t₀D : D t₀
  t₀D = F₀D raw1 , (λ η e → F₀D η)

  NodD : ∀ {k} → Nod k → Set
  NodD {k} ν = ∀ r c t g → D t → (∀ ζ (e : GdL k r c ζ) → D (g ζ e)) → D (ν r c t g)

  KA-D : ∀ k → Plain k → (ν : Nod k) → NodD ν → ∀ ζ → D (keepAll k ν ζ)
  KA-D k pl ν H G.zero = tt
  KA-D k pl ν H (G.suc a) = copiesD (keepAll k ν a) (KA-D k pl ν H a)
  KA-D k pl ν H (G.lim f) = λ n → KA-D k pl ν H (f n)
  KA-D k pl ν H (G.lc r c t g) =
    H r c _ _ (KA-D k pl ν H t) (λ ζ e → KA-D k pl ν H (g ζ e))
  KA-D (suc k) pl ν H (G.em _ a) = KA-D k pl (nS ν) (λ r → H (inj₂ r)) a
  KA-D (lim f) pl ν H (G.em n a) = KA-D (f n) (pl n) (nL ν n) (λ r → H (n , r)) a
  KA-D zero pl ν H G.top = copiesD G.top tt
  KA-D (suc k) pl ν H G.top =
    H (inj₁ tt) (cO k) _ _ (KA-D k pl (nS ν) (λ r → H (inj₂ r)) (cO k))
      (λ ζ e → KA-D k pl (nS ν) (λ r → H (inj₂ r)) ζ)
  KA-D (lim f) pl ν H G.top =
    psumD (λ n → keepAll (f n) (nL ν n) G.top)
      (λ n → KA-D (f n) (pl n) (nL ν n) (λ r → H (n , r)) G.top)

  νᴮD : ∀ η (e : Gd zero raw1 η) → Good η → NodD (νᴮ η e)
  νᴮD η e h r c t g dt dg = h , dt , dg

  KT-D : ∀ a → Good (G.suc (nrm a)) → D (KT a)
  KT-D a h = KA-D (suc (read0 (nrm a))) (rplain (nrm a))
    (νᴮ (G.suc (nrm a)) (γ a)) (νᴮD (G.suc (nrm a)) (γ a) h) G.top
```

## 3 派发与它的完全性

目标在第 `η` 支：主干上的结点 (层号 0) 用守卫里 `1 ⊲ η` 的路径 (`compare-zero`)；第 `η′` 支上的结点，两个坐标都判定为 `Good` 时用 `join` 给的路径。
判定不过时一律折叠；这一种在定义域里不出现 (`wayS-complete` 的两个前提)。派发不读树，也不读定义域的证据。

```agda
module Spine (Good : R → Set) (good? : ∀ η → Good η ⊎ (Good η → ⊥))
  (join : ∀ η η′ → Good η → Good η′ → Cp zero η η′ ⊎ Cp zero η′ η)
  (gd : ∀ d → Good (G.suc d) → Gd zero raw1 (G.suc d)) where

  open Dm Good public

  good-yes : ∀ η → Good η → Σ (Good η) λ h → good? η ≡ inj₁ h
  good-yes η h with good? η
  ... | inj₁ h′ = h′ , refl
  ... | inj₂ no = ⊥-elim (no h)

  wayB : ∀ η (e : Gd zero raw1 η) r η′ (e′ : Gd zero raw1 η′) r′ →
    Good η ⊎ (Good η → ⊥) → Good η′ ⊎ (Good η′ → ⊥) →
    Way (lev (read0 η) r) (lev (read0 η′) r′)
  wayB η e r η′ e′ r′ (inj₁ h) (inj₁ h′) =
    tri→way (compare-link (br η e r) (br η′ e′ r′) (join η η′ h h′))
  wayB η e r η′ e′ r′ (inj₁ h) (inj₂ n′) = fold
  wayB η e r η′ e′ r′ (inj₂ n) x′ = fold

  wayS : (τ : Tg) (p : Pre K₂ω) → Way (tl τ) (lev K₂ω p)
  wayS base p = fold
  wayS (at η e r) (inj₁ (inj₁ _)) = tri→way (flip (compare-zero η e r))
  wayS (at η e r) (inj₂ (inj₁ (inj₁ _))) = tri→way (flip (compare-zero η e r))
  wayS (at η e r) (inj₂ (inj₂ (η′ , e′ , r′))) = wayB η e r η′ e′ r′ (good? η) (good? η′)

```

`top` 在目标 "第 `η` 支的位置 `r`" 下的行。根 (层号 0) 保留在目标层里层号 0 的槽位上。第 `suc d` 支本该是第 `suc d` 支的 `top` 折到目标：
`η` 与 `suc d` 都满足 `Good` 时就取它 (`topB`：上一轮的 `Ψ` 在公共上界 `read0 (suc d)` 里折 `top`，派发取 `compare-link`)；否则取相对坐标 `η + nrm d` 那一支的 `top`。
各支沿 `δ` 累加，理由与 `rowᴿ` 相同。根自己那一层的分支 (`gk`) 保留时用不到，取常值。**替代行**：累加，以及不满足 `Good` 的坐标上的相对坐标。

```agda
  module TopRow (η : R) (e : Gd zero raw1 η) (r : Pre (read0 η)) where

    j : LF
    j = lev (read0 η) r

    pj : Plain j
    pj = lev-plain (read0 η) (rplain η) r

    wayκ : ∀ κ (eκ : Gd zero raw1 κ) → Cp zero η κ ⊎ Cp zero κ η →
      (r′ : Pre (read0 κ)) → Way j (lev (read0 κ) r′)
    wayκ κ eκ lk r′ = tri→way (compare-link (br η e r) (br κ eκ r′) lk)

    topB : ∀ κ (eκ : Gd zero raw1 κ) → Cp zero η κ ⊎ Cp zero κ η → Raw j
    topB κ eκ lk = Ψ j (read0 κ) (rplain κ) (read0-legal κ (proj₁ (proj₂ eκ)))
      (mix (wayκ κ eκ lk)) G.top tt tt

    topB-legal : ∀ κ eκ lk → Lgl j (topB κ eκ lk)
    topB-legal κ eκ lk = Ψ-legal j pj (read0 κ) (rplain κ) (read0-legal κ (proj₁ (proj₂ eκ)))
      (mix (wayκ κ eκ lk)) tt G.top tt tt

    topB-nested : ∀ κ eκ lk → Nested j (topB κ eκ lk)
    topB-nested κ eκ lk = Ψ-nested j (read0 κ) (rplain κ) (read0-legal κ (proj₁ (proj₂ eκ)))
      (mix (wayκ κ eκ lk)) G.top tt tt

    -- 这一支里 Ψ 问到的外部派发完全 (其余来源见 YiRawFold §5).
    topB-complete : ∀ κ eκ lk → Complete (mix (wayκ κ eκ lk))
    topB-complete κ eκ lk r′ a = tri-complete (compare-link (br η e r) (br κ eκ r′) lk) a

    relB : R → Raw j
    relB d = topB (η +ʳ nrm d) (Rel.eᵟ η e r d) (inj₁ (weak η (nrm d)))

    pick : ∀ d → Good η ⊎ (Good η → ⊥) → Good (G.suc d) ⊎ (Good (G.suc d) → ⊥) → Raw j
    pick d (inj₁ h) (inj₁ hd) = topB (G.suc d) (gd d hd) (join η (G.suc d) h hd)
    pick d (inj₁ h) (inj₂ n) = relB d
    pick d (inj₂ n) x = relB d

    pick-legal : ∀ d x x′ → Lgl j (pick d x x′)
    pick-legal d (inj₁ h) (inj₁ hd) = topB-legal (G.suc d) (gd d hd) (join η (G.suc d) h hd)
    pick-legal d (inj₁ h) (inj₂ n) =
      topB-legal (η +ʳ nrm d) (Rel.eᵟ η e r d) (inj₁ (weak η (nrm d)))
    pick-legal d (inj₂ n) x = topB-legal (η +ʳ nrm d) (Rel.eᵟ η e r d) (inj₁ (weak η (nrm d)))

    pick-nested : ∀ d x x′ → Nested j (pick d x x′)
    pick-nested d (inj₁ h) (inj₁ hd) = topB-nested (G.suc d) (gd d hd) (join η (G.suc d) h hd)
    pick-nested d (inj₁ h) (inj₂ n) =
      topB-nested (η +ʳ nrm d) (Rel.eᵟ η e r d) (inj₁ (weak η (nrm d)))
    pick-nested d (inj₂ n) x = topB-nested (η +ʳ nrm d) (Rel.eᵟ η e r d) (inj₁ (weak η (nrm d)))

    H : R → Raw j
    H d = pick d (good? η) (good? (G.suc d))

    -- 保留律: 第 suc d 支的 top 的根层号是 read0 d; 它在目标层的位置上时, 像是那个层号的保留结点.
    pick-kept : ∀ d x x′ (h : Good η) (hd : Good (G.suc d)) → x ≡ inj₁ h → x′ ≡ inj₁ hd →
      At j (read0 d) → Kept j (read0 d) (pick d x x′)
    pick-kept d .(inj₁ h) .(inj₁ hd) h hd refl refl a =
      Ψn-kept j pj (read0 d) (rplain d)
        (wayκ (G.suc d) (gd d hd) (join η (G.suc d) h hd) (inj₁ tt)) _
        (tri-complete
          (compare-link (br η e r) (br (G.suc d) (gd d hd) (inj₁ tt)) (join η (G.suc d) h hd)) a)

    H-kept : ∀ d → Good η → Good (G.suc d) → At j (read0 d) → Kept j (read0 d) (H d)
    H-kept d h hd a = pick-kept d (good? η) (good? (G.suc d))
      (proj₁ (good-yes η h)) (proj₁ (good-yes (G.suc d) hd))
      (proj₂ (good-yes η h)) (proj₂ (good-yes (G.suc d) hd)) a

    plus-kept : ∀ k x y → Kept j k y → Kept j k (plus j x y)
    plus-kept k x .(G.lc s c t g) (s , q , c , t , g , refl) = s , q , c , _ , _ , refl

    module Row (s₀ : Pre j) (z : lev j s₀ ≡ zero) where

      t₁ : Raw j
      t₁ = Rel.Row.t₁ η e r s₀ z

      S : R → Raw j
      S G.zero = t₁
      S (G.suc d) = plus j (S d) (H d)
      S (G.lim f) = G.lim (λ n → S (f n))
      S G.top = t₁

      S-first : ∀ δ → Cp j t₁ (S δ)
      S-first G.zero = inj₁ refl
      S-first (G.suc d) = Cp-tr j (S-first d) (add-weak j (rawAlg j) (S d) (H d))
      S-first (G.lim f) = inj₂ (zero , S-first (f zero))
      S-first G.top = inj₁ refl

      S-cp : ∀ {δ} δ′ → Cp zero δ δ′ → Cp j (S δ) (S δ′)
      S-cp δ′ (inj₁ refl) = inj₁ refl
      S-cp (G.suc d) (inj₂ p) = Cp-tr j (S-cp d p) (add-weak j (rawAlg j) (S d) (H d))
      S-cp (G.lim f) (inj₂ (n , p)) = inj₂ (n , S-cp (f n) p)

      S-legal : ∀ δ → Lgl zero δ → Lgl j (S δ)
      S-legal G.zero l = Rel.Row.t₁-legal η e r s₀ z
      S-legal (G.suc d) l = add-lgl j pj (rawAlg j) (S d) (H d) (S-legal d l)
        (pick-legal d (good? η) (good? (G.suc d)))
      S-legal (G.lim f) (st , lf) =
        (λ n → S-cp (f (suc n)) (st n)) , (λ n → S-legal (f n) (lf n))
      S-legal G.top l = Rel.Row.t₁-legal η e r s₀ z

      S-nested : ∀ δ → Nested j (S δ)
      S-nested G.zero = Rel.Row.t₁-nested η e r s₀ z
      S-nested (G.suc d) = add-ns j (rawAlg j) (S d) (H d) (S-nested d)
        (pick-nested d (good? η) (good? (G.suc d)))
      S-nested (G.lim f) = λ n → S-nested (f n)
      S-nested G.top = Rel.Row.t₁-nested η e r s₀ z

      N : NdR j zero
      N = nd raw1 tt tt t₁ (λ δ e′ → S δ) (λ δ e′ → T₃ᵐ)
        (λ δ e′ → T₃ᵐ-legal) (λ δ e′ → raw0-Nested T₃ᵐ) (λ δ e′ → tt)

      rowᶠ : Raw j
      rowᶠ = Ψn j zero tt (keep s₀ z) N

      rowᶠ-legal : Lgl j rowᶠ
      rowᶠ-legal = Ψn-legal j zero tt (keep s₀ z) N
        (record
          { seed = inj₁ refl , tt , tt
          ; tg = λ δ e′ → S-first δ
          ; dir = λ δ e′ δ′ e″ q → S-cp δ′ (proj₁ q)
          ; lt = Rel.Row.t₁-legal η e r s₀ z
          ; lg = λ δ e′ → S-legal δ (proj₁ (proj₂ e′))
          ; lkʳ = λ δ e′ → T₃ᵐ-legal
          ; nkʳ = λ δ e′ → raw0-Nested T₃ᵐ })

      rowᶠ-nested : Nested j rowᶠ
      rowᶠ-nested = Ψn-nested j zero tt (keep s₀ z) N
        (record
          { seed = inj₁ refl , tt , tt
          ; lcʳ = tt
          ; ncʳ = tt
          ; nt = Rel.Row.t₁-nested η e r s₀ z
          ; ng = λ δ e′ → S-nested δ
          ; lkʳ = λ δ e′ → T₃ᵐ-legal
          ; nkʳ = λ δ e′ → raw0-Nested T₃ᵐ })

      rowᶠ-pos : Pos j rowᶠ
      rowᶠ-pos = Ψn-pos j zero tt (keep s₀ z) N

      rowᶠ-kept : Kept j zero rowᶠ
      rowᶠ-kept = Ψn-kept j pj zero tt (keep s₀ z) N tt

      S-keep : ∀ d → Good η → Good (G.suc d) → At j (read0 d) → Kept j (read0 d) (S (G.suc d))
      S-keep d h hd a = plus-kept (read0 d) (S d) (H d) (H-kept d h hd a)

  topS : ∀ η (e : Gd zero raw1 η) (r : Pre (read0 η)) → Raw (lev (read0 η) r)
  topS η e r = topTri (lev (read0 η) r) (compare-zero η e r) (TopRow.Row.rowᶠ η e r)

  topS-legal : ∀ η e r → Lgl (lev (read0 η) r) (topS η e r)
  topS-legal η e r = topTri-ind Lgl T₃ᵐ-legal (lev (read0 η) r) (compare-zero η e r)
    (TopRow.Row.rowᶠ η e r) (TopRow.Row.rowᶠ-legal η e r)

  topS-nested : ∀ η e r → Nested (lev (read0 η) r) (topS η e r)
  topS-nested η e r = topTri-ind Nested (raw0-Nested T₃ᵐ) (lev (read0 η) r) (compare-zero η e r)
    (TopRow.Row.rowᶠ η e r) (TopRow.Row.rowᶠ-nested η e r)

  topS-pos : ∀ η e r → Pos (lev (read0 η) r) (topS η e r)
  topS-pos η e r = topTri-ind Pos tt (lev (read0 η) r) (compare-zero η e r)
    (TopRow.Row.rowᶠ η e r) (TopRow.Row.rowᶠ-pos η e r)

  -- top 的根在目标层里有层号 0 的槽位时保留.
  topS-kept : ∀ η e r → At (lev (read0 η) r) zero → Kept (lev (read0 η) r) zero (topS η e r)
  topS-kept η e r = go (lev (read0 η) r) (compare-zero η e r) (TopRow.Row.rowᶠ η e r)
    (TopRow.Row.rowᶠ-kept η e r)
    where
    go : ∀ j (x : Tri zero j) mk → (∀ s z → Kept j zero (mk s z)) → At j zero →
      Kept j zero (topTri j x mk)
    go j (below () q) mk h a
    go j (above s z) mk h a = h s z
    go .zero (same refl) mk h (() , q)
```

```agda
  spine : Disp
  spine = record
    { Dom = λ τ ξ → D ξ
    ; d-pred = λ d → d
    ; d-term = λ d n → d n
    ; d-first = D-first
    ; d-obs = D-branch
    ; d-drive = D-branch
    ; d-em = λ i a d → d
    ; way = λ τ p c t g d → wayS τ p
    ; topᴮ = topS
    ; topᴮ-legal = topS-legal
    ; topᴮ-nested = topS-nested
    ; topᴮ-pos = topS-pos }

  open Fold spine public

  FinT : Tg → Set
  FinT base = ⊤
  FinT (at η e r) = Good η

  own-fin : ∀ p → GoodP p → FinT (own p)
  own-fin (inj₁ (inj₁ _)) h = tt
  own-fin (inj₂ (inj₁ (inj₁ _))) h = tt
  own-fin (inj₂ (inj₂ (η , e , r))) h = h

  wayB-complete : ∀ η e r η′ e′ r′ x x′ (h : Good η) (h′ : Good η′) →
    x ≡ inj₁ h → x′ ≡ inj₁ h′ →
    At (lev (read0 η) r) (lev (read0 η′) r′) → IsKeep (wayB η e r η′ e′ r′ x x′)
  wayB-complete η e r η′ e′ r′ .(inj₁ h) .(inj₁ h′) h h′ refl refl a =
    tri-complete (compare-link (br η e r) (br η′ e′ r′) (join η η′ h h′)) a

  TrunkP : Pre K₂ω → Set
  TrunkP (inj₁ (inj₁ _)) = ⊤
  TrunkP (inj₂ (inj₁ (inj₁ _))) = ⊤
  TrunkP (inj₂ (inj₂ _)) = ⊥

  -- 主干上的结点: 对一切目标完全, 不要 Good.
  wayS-trunk : ∀ τ p → TrunkP p → At (tl τ) (lev K₂ω p) → IsKeep (wayS τ p)
  wayS-trunk base p tp (() , q)
  wayS-trunk (at η e r) (inj₁ (inj₁ _)) tp a = tri-complete (flip (compare-zero η e r)) a
  wayS-trunk (at η e r) (inj₂ (inj₁ (inj₁ _))) tp a = tri-complete (flip (compare-zero η e r)) a

  wayS-complete : ∀ τ → FinT τ → ∀ p → GoodP p → At (tl τ) (lev K₂ω p) → IsKeep (wayS τ p)
  wayS-complete base ft p gp (() , q)
  wayS-complete (at η e r) ft (inj₁ (inj₁ _)) gp a = tri-complete (flip (compare-zero η e r)) a
  wayS-complete (at η e r) ft (inj₂ (inj₁ (inj₁ _))) gp a =
    tri-complete (flip (compare-zero η e r)) a
  wayS-complete (at η e r) ft (inj₂ (inj₂ (η′ , e′ , r′))) gp a =
    wayB-complete η e r η′ e′ r′ (good? η) (good? η′)
      (proj₁ (good-yes η ft)) (proj₁ (good-yes η′ gp))
      (proj₂ (good-yes η ft)) (proj₂ (good-yes η′ gp)) a
```

## 4 问到的派发都完全

`ask-closed`：从定义域里的树与 `Good` 的目标出发，调用的闭包不出定义域，目标保持 `Good`。所以闭包里每个结点上两条都成立。
量化域是闭包 `Ask`；它包含分支函数在一切带守卫坐标上的值，链实际走到的坐标在其中。

```agda
  ask-closed : ∀ {τ₀ ξ₀ τ ξ} → Ask τ₀ ξ₀ τ ξ → FinT τ₀ → D ξ₀ → FinT τ × D ξ
  ask-closed here ft d = ft , d
  ask-closed (pred a) ft d = ask-closed a ft d
  ask-closed (term a n) ft d = proj₁ (ask-closed a ft d) , proj₂ (ask-closed a ft d) n
  ask-closed (first {p = p} {c} {t} {g} a) ft d =
    proj₁ (ask-closed a ft d) , D-first p c t g (proj₂ (ask-closed a ft d))
  ask-closed (obs {p = p} {c} {t} {g} a ζ e) ft d =
    proj₁ (ask-closed a ft d) , D-branch p c t g (proj₂ (ask-closed a ft d)) ζ e
  ask-closed (drive {p = p} {c} {t} {g} a ζ e) ft d =
    own-fin p (D-good p c t g (proj₂ (ask-closed a ft d))) ,
    D-branch p c t g (proj₂ (ask-closed a ft d)) ζ e

  honestᴰ : ∀ τ → FinT τ → ∀ p c t g (d : D (G.lc p c t g))
    (l : Lgl K₂ω (G.lc p c t g)) (nb : Nested K₂ω (G.lc p c t g)) →
    (At (tl τ) (lev K₂ω p) → Kept (tl τ) (lev K₂ω p) (Ψᶠ τ (G.lc p c t g) d l nb)) ×
    ((At (tl τ) (lev K₂ω p) → ⊥) → IsLim (Ψᶠ τ (G.lc p c t g) d l nb))
  honestᴰ τ ft p c t g d l nb =
    honest τ p c t g d l nb (wayS-complete τ ft p (D-good p c t g d))

  honestˢ : ∀ {τ₀ ξ₀ τ p c t g} → FinT τ₀ → D ξ₀ → (a : Ask τ₀ ξ₀ τ (G.lc p c t g))
    (d : D (G.lc p c t g)) (l : Lgl K₂ω (G.lc p c t g)) (nb : Nested K₂ω (G.lc p c t g)) →
    Honest (posT τ) (ownAt τ (G.lc p c t g) d l nb) (G.lc p c t g)
  honestˢ {τ = τ} {p} {c} {t} {g} ft d₀ a d l nb =
    honest-if τ p c t g d l nb
      (wayS-complete τ (proj₁ (ask-closed a ft d₀)) p (D-good p c t g d))
```
