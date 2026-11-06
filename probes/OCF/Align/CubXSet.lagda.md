# Cubical 验证实验 (二): 高度是集合, 一般种类结构上的 UIP

> **验证实验, 作者 2026-11-05 准许, 不进成品, 不改规则.** `--cubical --safe` 模块 (库文件另加 `--cubical-compatible --guardedness --hidden-argument-puns`), 不开 K. 不改任何已有文件, 只导入它们. 无公设, 无洞, 无停机或正性编译指示. 不含记号. 入口 [CubXFe](CubXFe.lagda.md).
>
> [CubXFe](CubXFe.lagda.md) 只处理 `HB S₀` (那里 `AdmWUip.fe→uip` 的编码-解码只写了 `S₀`). [NegColimALoop](NegColimALoop.lagda.md) 的 `uip→raise1`, `uip→fix` 对一般 `S` 以 `UIPˢ` (`HB S` 上的 UIP) 为前提. 本篇问: 对哪些 `S` 能在立方类型论里证出 `UIPˢ`.
>
> **结果 (编译过的定理, 在 `--cubical` 下).**
>
> 1. `isSetHB : isSet (K S) → isSet (HB S)` (对一切 `S`). 只要分支种类 `K S` 是集合; 坐标类型 `E S κ` **不需要**是集合 (它们只作分支的定义域, 由函数外延处理). 证明: `HB S` 同构于 cubical 库的带下标的 W 类型 (`Cubical.Data.W.Indexed`, 形状 `⊤ ⊎ ⊤ ⊎ ⊤ ⊎ K S`, 位置 `⊥, ⊤, ℕ, E S κ`), 后者在形状是集合时是集合 (`isOfHLevelSuc-IW`); 往返的同伦用 `funExt`.
> 2. `uipOf : isSet X → ∀ (e e′ : x ≡ y) → e ≡ e′`: 路径意义的集合推出标准库 `_≡_` 的 UIP (经 `Cubical.Data.Equality.Conversion` 的 `pathToEq`, `eqToPath`).
> 3. 闭包 `SetKS` (种类是集合, 一切坐标类型是集合): `S₀` (`setS₀`, 要 `isSetA`), `step` (`setStep`), `sup` 在下标是集合时 (`setSup`), 以及 **`Lev x` 对一切 `x : HB S`, 只要 `SetKS S`** (`setLev`). 于是 `G₀ c = Lev (up c)` (一切 `c : HB S₀`), `S₁ = step S₀`, 一切 `Lev x` 上都有 UIP. 坐标类型是集合这一半是 `Lev (hΩ κ g)` 必需的: 那里新种类的下标就是 `E S κ`.
> 4. 无条件化: `uipˢ` (`UIPˢ` 对一切 `SetKS` 的 `S`), `raise1` (`uip→raise1`, 一般 `S`, 只要 `K S` 是集合), `loopFixAt` (`uip→fix`), `raise1ω` (`raise1ω-sat`, `S₁` 上的最小实例), `fixω` (`raise1→fixω` 的结论), `uipG₀` (`HB (G₀ c)` 上的 UIP, 这是 `Slot`, `Inst` 的坐标类型).
>
> **卡住的地方 (一般 `S`).** 对**任意** `S`, `UIPˢ` 在立方类型论里不成立: 若 `K S` 是圆周 `S¹`, `HB S` 不是集合 (`hΩ` 把种类的环带进高度). 这条写成编译的否定 `¬uip-S¹` ([CubXSetNeg](CubXSetNeg.lagda.md)). 所以卡点恰好是 "`K S` 是集合"; 仓库里实际用到的种类结构都由 `S₀`, `step`, `sup ℕ`, `sup (E S κ)`, `Lev` 搭成, 都满足 `SetKS` (第 3 条).

```agda
{-# OPTIONS --cubical --safe --lossy-unification #-}
module OCF.Align.CubXSet where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Cubical.Foundations.Prelude as P using (isSet; funExt; _∙_) renaming (_≡_ to _≡ₚ_)
open import Cubical.Foundations.Isomorphism using (Iso; iso)
open import Cubical.Foundations.HLevels using (isOfHLevelRetractFromIso; isSetΣ)
open import Cubical.Data.Sum using (isSet⊎; inl; inr) renaming (_⊎_ to _⊎ᶜ_)
open import Cubical.Data.Unit using (isSetUnit)
open import Cubical.Data.Empty using () renaming (⊥ to ⊥ᶜ)
open import Cubical.Data.Nat using (isSetℕ)
open import Cubical.Data.W.Indexed using (IW; node; isOfHLevelSuc-IW)
open import Cubical.Data.Equality.Conversion using (pathToEq; eqToPath; pathToEq-eqToPath)

open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.HtTowerTy
open import OCF.Align.AdmWIf using (G₀)
open import OCF.Align.ColimWIf using (S₁; x₀; ω₀)
open import OCF.Align.ColimWNeg using (wω)
open import OCF.Align.ColimAIf using (module Adm)
open import OCF.Align.NegColimALoop using (UIPˢ; uip→fix; uip→raise1; raise1ω-sat; raise1→fixω; LoopFixAt; LoopFix₀At)
```

## §1 路径意义的集合推出 `_≡_` 的 UIP

```agda
uipOf : ∀ {X : Set} → isSet X → ∀ {x y : X} (e e′ : x ≡ y) → e ≡ e′
uipOf h {x} {y} e e′ =
  pathToEq (P.sym (pathToEq-eqToPath e) ∙ P.cong pathToEq (h x y (eqToPath e) (eqToPath e′)) ∙ pathToEq-eqToPath e′)
```

## §2 标准库的 `⊎` 是集合

标准库的 `_⊎_` (构造子 `inj₁`, `inj₂`) 与 cubical 库的 `_⊎_` (`inl`, `inr`) 是两个类型; 用一个平凡同构搬 `isSet⊎`. (`Σ`, `⊤`, `ℕ` 两边是同一个内建类型, 不用搬.)

```agda
isSet⊎ˢ : ∀ {X Y : Set} → isSet X → isSet Y → isSet (X ⊎ Y)
isSet⊎ˢ {X} {Y} hX hY = isOfHLevelRetractFromIso 2 (iso f g fg gf) (isSet⊎ hX hY)
  where
  f : X ⊎ Y → X ⊎ᶜ Y
  f (inj₁ x) = inl x
  f (inj₂ y) = inr y
  g : X ⊎ᶜ Y → X ⊎ Y
  g (inl x) = inj₁ x
  g (inr y) = inj₂ y
  fg : ∀ b → f (g b) ≡ₚ b
  fg (inl x) = P.refl
  fg (inr y) = P.refl
  gf : ∀ a → g (f a) ≡ₚ a
  gf (inj₁ x) = P.refl
  gf (inj₂ y) = P.refl
```

## §3 `HB S` 是集合, 只要 `K S` 是

`HB S` 同构于带下标的 W 类型 (下标类型取 `⊤`). 形状: `inl` 是 $0$, `inr (inl _)` 是后继, `inr (inr (inl _))` 是 ℕ-极限, `inr (inr (inr κ))` 是种类 κ 的 Ω-极限. 位置: 空, 一点, ℕ, `E S κ`.

```agda
module HBW (S : KS) where
  Sh : Set
  Sh = ⊤ ⊎ᶜ (⊤ ⊎ᶜ (⊤ ⊎ᶜ K S))

  Pos : Sh → Set
  Pos (inl _) = ⊥ᶜ
  Pos (inr (inl _)) = ⊤
  Pos (inr (inr (inl _))) = ℕ
  Pos (inr (inr (inr κ))) = E S κ

  Wt : Set
  Wt = IW {X = ⊤} (λ _ → Sh) (λ _ s → Pos s) (λ _ _ _ → tt) tt

  to : HB S → Wt
  to hz = node (inl tt) (λ ())
  to (hs x) = node (inr (inl tt)) (λ _ → to x)
  to (hl f) = node (inr (inr (inl tt))) (λ n → to (f n))
  to (hΩ κ g) = node (inr (inr (inr κ))) (λ c → to (g c))

  from : Wt → HB S
  from (node (inl _) t) = hz
  from (node (inr (inl _)) t) = hs (from (t tt))
  from (node (inr (inr (inl _))) t) = hl (λ n → from (t n))
  from (node (inr (inr (inr κ))) t) = hΩ κ (λ c → from (t c))

  ft : ∀ x → from (to x) ≡ₚ x
  ft hz = P.refl
  ft (hs x) = P.cong hs (ft x)
  ft (hl f) = P.cong hl (funExt (λ n → ft (f n)))
  ft (hΩ κ g) = P.cong (hΩ κ) (funExt (λ c → ft (g c)))

  tf : ∀ w → to (from w) ≡ₚ w
  tf (node (inl tt) t) = P.cong (node (inl tt)) (funExt (λ ()))
  tf (node (inr (inl tt)) t) = P.cong (node (inr (inl tt))) (funExt (λ _ → tf (t tt)))
  tf (node (inr (inr (inl tt))) t) = P.cong (node (inr (inr (inl tt)))) (funExt (λ n → tf (t n)))
  tf (node (inr (inr (inr κ))) t) = P.cong (node (inr (inr (inr κ)))) (funExt (λ c → tf (t c)))

  isSetHB : isSet (K S) → isSet (HB S)
  isSetHB hK = isOfHLevelRetractFromIso 2 (iso to from tf ft)
    (isOfHLevelSuc-IW 1 (λ _ → isSet⊎ isSetUnit (isSet⊎ isSetUnit (isSet⊎ isSetUnit hK))) tt)

open HBW using (isSetHB) public
```

布劳威尔树 `A` 同样 (形状 `⊤ ⊎ ⊤ ⊎ ⊤`, 没有种类).

```agda
module AW where
  ShA : Set
  ShA = ⊤ ⊎ᶜ (⊤ ⊎ᶜ ⊤)

  PosA : ShA → Set
  PosA (inl _) = ⊥ᶜ
  PosA (inr (inl _)) = ⊤
  PosA (inr (inr _)) = ℕ

  WA : Set
  WA = IW {X = ⊤} (λ _ → ShA) (λ _ s → PosA s) (λ _ _ _ → tt) tt

  toA : A → WA
  toA azero = node (inl tt) (λ ())
  toA (asuc a) = node (inr (inl tt)) (λ _ → toA a)
  toA (alim f) = node (inr (inr tt)) (λ n → toA (f n))

  fromA : WA → A
  fromA (node (inl _) t) = azero
  fromA (node (inr (inl _)) t) = asuc (fromA (t tt))
  fromA (node (inr (inr _)) t) = alim (λ n → fromA (t n))

  ftA : ∀ a → fromA (toA a) ≡ₚ a
  ftA azero = P.refl
  ftA (asuc a) = P.cong asuc (ftA a)
  ftA (alim f) = P.cong alim (funExt (λ n → ftA (f n)))

  tfA : ∀ w → toA (fromA w) ≡ₚ w
  tfA (node (inl tt) t) = P.cong (node (inl tt)) (funExt (λ ()))
  tfA (node (inr (inl tt)) t) = P.cong (node (inr (inl tt))) (funExt (λ _ → tfA (t tt)))
  tfA (node (inr (inr tt)) t) = P.cong (node (inr (inr tt))) (funExt (λ n → tfA (t n)))

  isSetA : isSet A
  isSetA = isOfHLevelRetractFromIso 2 (iso toA fromA tfA ftA)
    (isOfHLevelSuc-IW 1 (λ _ → isSet⊎ isSetUnit (isSet⊎ isSetUnit isSetUnit)) tt)

open AW using (isSetA) public
```

## §4 闭包: `S₀`, `step`, `sup`, `Lev`

```agda
record SetKS (S : KS) : Set where
  field
    sK : isSet (K S)
    sE : ∀ κ → isSet (E S κ)
open SetKS public

setS₀ : SetKS S₀
setS₀ = record { sK = isSetUnit ; sE = λ _ → isSetA }

setStep : ∀ {S} → SetKS S → SetKS (step S)
setStep {S} s = record { sK = isSet⊎ˢ (sK s) isSetUnit ; sE = e }
  where
  e : ∀ κ → isSet (E (step S) κ)
  e (inj₁ κ) = sE s κ
  e (inj₂ _) = isSetHB S (sK s)

setSup : ∀ {I : Set} {F : I → KS} → isSet I → (∀ i → SetKS (F i)) → SetKS (sup I F)
setSup hI s = record { sK = isSetΣ hI (λ i → sK (s i)) ; sE = λ κ → sE (s (proj₁ κ)) (proj₂ κ) }

setLev : ∀ {S} → SetKS S → (x : HB S) → SetKS (Lev x)
setLev s hz = setS₀
setLev s (hs x) = setStep (setLev s x)
setLev s (hl f) = setSup isSetℕ (λ n → setLev s (f n))
setLev s (hΩ κ g) = setSup (sE s κ) (λ c → setLev s (g c))

setS₁ : SetKS S₁
setS₁ = setStep setS₀

setG₀ : ∀ c → SetKS (G₀ c)
setG₀ c = setLev setS₁ (up c)
```

## §5 无条件化

`UIPˢ` 与 `uip→raise1`, `uip→fix` 在 [NegColimALoop](NegColimALoop.lagda.md) 的参数化模块里 (隐式参数 `S`, `X`, `w`; `UIPˢ` 不依赖 `X`, `w`).

```agda
uipˢ : ∀ {S} {X : HB S} {w : Wd S} → isSet (K S) → UIPˢ {S = S} {X = X} {w = w}
uipˢ {S} hK = uipOf (isSetHB S hK)

-- 一般 S: 种类是集合时, 有满足 at1, coh1 的单个增量更新
raise1 : ∀ {S} {X : HB S} {w : Wd S} → isSet (K S) → LgW S w → LgB X → Adm.RaiseA1 X w
raise1 {S} {X} {w} hK = uip→raise1 {S = S} {X = X} {w = w} (uipˢ {S} {X} {w} hK)

loopFixAt : ∀ {S} {X : HB S} {w : Wd S} → isSet (K S) → ∀ y₀ → LoopFixAt {S = S} {X = X} {w = w} y₀
loopFixAt {S} {X} {w} hK = uip→fix {S = S} {X = X} {w = w} (uipˢ {S} {X} {w} hK)

-- S₁ 上的最小实例 (接口 §6): 原来以 HB S₁ 的 UIP 为前提
raise1ω : Adm.RaiseA1 x₀ wω
raise1ω = raise1ω-sat (uipˢ {S₁} {x₀} {wω} (sK setS₁))

fixω : LoopFix₀At {X = x₀} {w = wω} (up ω₀)
fixω = raise1→fixω raise1ω

-- Slot, Inst 的坐标类型 HB (G₀ c) 上的 UIP
uipG₀ : ∀ c {a b : HB (G₀ c)} (e e′ : a ≡ b) → e ≡ e′
uipG₀ c = uipOf (isSetHB (G₀ c) (sK (setG₀ c)))

-- 一切 Lev x (x 在种类为集合的 S 上) 的高度上的 UIP
uipLev : ∀ {S} → SetKS S → ∀ (x : HB S) {a b : HB (Lev x)} (e e′ : a ≡ b) → e ≡ e′
uipLev s x = uipOf (isSetHB (Lev x) (sK (setLev s x)))
```
