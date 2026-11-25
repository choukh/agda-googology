# 自身折叠的保持: 对折叠参数化

> 验收文件 (读记号). 判决: 编译定理, 无前提. `SelfF.LF`: 第 `nd s h` 层上任何像 F (每棵树的折叠) 满足五条律 (单调; 后继、结点的像不低于逐项取像, 即 `YiFIIface` 的 `KeepLaw.keep` 在恒等槽位上; 槽位读法 κ 满足 `Pen (cmpᵀ (κ+1) ν)`; 嵌入一行 `upF`, 即 `FallLaw.fall` 接孩子层的保持) 与底值的界时, 对一切树保持到 ψ_ν(t ++ ·). 它是五参数接口的 `Hold`: 目标即源层, 路径 `self`, 上下文头 ν 前缀 t, 域全体 (`self-hold`).
> 两份旧引理由它推出: `YiGTSelf.Self.LF` (折叠 `YiTBRow.ψ`, `gt-self`; 落到 `foldᵍ` 上的 `LowAt`, `gt-low`) 与 `YiWCTw1.Self₁.LF` (折叠 `YiRBSib.ψ`, ν = 1, `wc-self`). 证明照 `YiGTSelf.Self.LF` 逐行改写, 用到的定义等式换成律.
> 不给出什么: 第 0 层 (`zero-self`) 不在内; 不给出新的保持.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMISelf where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiRBSib as RB
import OCF.Lean.YiBSBase as BB
open import OCF.Lean.YiKVRel using (_⊴_; ⊴r; ++[])
open import OCF.Lean.YiGTGen using (weakᴿ; weakenᴿ; closeᴿ; zlᴿ; nextψ; limψ; nodeψ; app≤ν)
open import OCF.Lean.YiGTNode using (NodeFrame)
open import OCF.Lean.YiGTUp using (up-pres; up-zero)
open import OCF.Lean.YiGTEmb using (self-child)
open import OCF.Lean.YiANFam using (Pen)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E
open import OCF.Lean.YiGIBlock using (blkᵍ; foldᵍ; rowsᵍ; Bsᵍ)
open import OCF.Lean.YiAbsGIface using (Doms)
open import OCF.Lean.YiMIGraded using (gradedᴹ)
open import OCF.Lean.YiMIIface
import OCF.Lean.YiGTSelf as GT
import OCF.Lean.YiWCTw1 as WC
open import OCF.Lean.YiBAEbo using (j₁)
```

## 参数化的保持

```agda
module SelfF (s : Sh) (h : Ch s → L) (ν t : E.T) (F : Tr (nd s h) → Tr⁺ (nd s h))
    (mono : ∀ {x y} → nd s h ⊢ x ◃ y → nd s h ⊢ proj₁ (F x) ◃ proj₁ (F y))
    (sucF : ∀ x → proj₁ (next⁺ (F x)) ⊴ proj₁ (F (suc x)))
    (ndF  : ∀ p (g : Br (nd s h) p → Tr (nd s h)) → Ω p (λ c → proj₁ (F (g c))) ⊴ proj₁ (F (Ω p g)))
    (pen  : ∀ p κ → GR.Nu (nd s h) p κ → Pen (E.cmpᵀ (E.sucT κ) ν))
    (upF  : ∀ c {u b x y e} → GR.R (nd s h) (E.ψ ν u ∷ []) (proj₁ (F x)) → GR.R (h c) b y
          → GR.R (nd s h) (E.ψ ν (u ++ b) ∷ []) (proj₁ (F (up x c y e))))
    (mb   : GR.R (nd s h) (E.ψ ν t ∷ []) (proj₁ (F zero))) where

  LF : ∀ {a x} → GR.R (nd s h) a x → GR.R (nd s h) (E.ψ ν (t ++ a) ∷ []) (proj₁ (F x))
  LF (H.mz {x = x}) = ++[] (λ z → GR.R (nd s h) (E.ψ ν z ∷ []) (proj₁ (F x))) t
    (zlᴿ (nd s h) (λ y → proj₁ (F y)) mono mb x)
  LF (H.m1 {t = a} {x = x} e m) = weakenᴿ (nd s h) (nextψ (nd s h) ν t a e (F x) (LF m)) (sucF x)
  LF (H.mL {t = a} {x = x} e m) = limψ (nd s h) ν t a e (proj₁ (F x)) (λ n → LF (m n))
  LF (H.mΩ {t = a} {ν = κ} {p = p} {g = g} e nu m) =
    weakenᴿ (nd s h) (nodeψ (nd s h) ν t a p e (pen p κ nu) nu (λ η c lc → LF (m η c lc))) (ndF p g)
  LF (H.mU {t = a} {s = b} {x = x} {c = c} {y = y} {e = e} m ch) =
    subst (λ z → GR.R (nd s h) (E.ψ ν z ∷ []) (proj₁ (F (up x c y e)))) (++-assoc t a b) (upF c (LF m) ch)
  LF (H.mw m d) = weakᴿ (nd s h) (LF m) (mono d)
  LF (H.mc le m) = closeᴿ (nd s h) (app≤ν ν t le) (LF m)
```

在五参数接口里: 分级实例取 `gradedᴹ` 在折叠 𝔽 上、上下文 (头, 前缀) 的取值, 读法域与底的条件任意.

```agda
module InMI {Rd : L → E.T → Set} {Bd : ∀ {ℓ j} → Bsᵍ ℓ → j ≤ ℓ → Tr⁺ j → E.T × E.T → Set} (𝔻 : Doms blkᵍ foldᵍ)
    (s : Sh) (h : Ch s → L) (ν t : E.T) (F : Tr (nd s h) → Tr⁺ (nd s h))
    (mono : ∀ {x y} → nd s h ⊢ x ◃ y → nd s h ⊢ proj₁ (F x) ◃ proj₁ (F y))
    (sucF : ∀ x → proj₁ (next⁺ (F x)) ⊴ proj₁ (F (suc x)))
    (ndF  : ∀ p (g : Br (nd s h) p → Tr (nd s h)) → Ω p (λ c → proj₁ (F (g c))) ⊴ proj₁ (F (Ω p g)))
    (pen  : ∀ p κ → GR.Nu (nd s h) p κ → Pen (E.cmpᵀ (E.sucT κ) ν))
    (upF  : ∀ c {u b x y e} → GR.R (nd s h) (E.ψ ν u ∷ []) (proj₁ (F x)) → GR.R (h c) b y
          → GR.R (nd s h) (E.ψ ν (u ++ b) ∷ []) (proj₁ (F (up x c y e))))
    (mb   : GR.R (nd s h) (E.ψ ν t ∷ []) (proj₁ (F zero))) where
  open MI (gradedᴹ foldᵍ rowsᵍ proj₁ GR.Nu Rd (E.T × E.T) proj₁ proj₂ Bd) 𝔻

  self-hold : Hold (λ x → proj₁ (F x)) (λ a → E.ψ ν (t ++ a) ∷ []) ⊤ᴰ
  self-hold _ r = SelfF.LF s h ν t F mono sucF ndF pen upF mb r
```

## 两份旧引理

`YiTBRow.ψ` 与 `YiRBSib.ψ` 在 `self` 路径上, 后继与结点两条律逐字成立 (`⊴r`); 嵌入一行分别是 `up-pres` 与 `up-zero`.

```agda
module _ (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (r : TB.Rb (nd s h)) (B : Base (nd s h)) (ν t : E.T)
    (fr : NodeFrame (nd s h) o (nd s h) self ν) (β : Tr⁺ (nd s h)) (mb : GR.R (nd s h) (E.ψ ν t ∷ []) (proj₁ β)) where
  private
    F : Tr (nd s h) → Tr⁺ (nd s h)
    F x = TB.ψ (nd s h) o r B (nd s h) self β x

  gt-self : ∀ {a x} → GR.R (nd s h) a x → GR.R (nd s h) (E.ψ ν (t ++ a) ∷ []) (proj₁ (GT.Self.F s h o r B ν t fr β mb x))
  gt-self = SelfF.LF s h ν t F (TB.mono (nd s h) o r B (nd s h) self β) (λ _ → ⊴r) (λ _ _ → ⊴r)
    (λ p κ nu → proj₁ (fr p κ nu))
    (λ c {u} {b} {x} r ch → up-pres (h c) ν (down {s = s} {h = h} stop c) (self-child s h o ν fr c) u (F x) r ch) mb

  module _ {Rd : L → E.T → Set} {Bd : ∀ {ℓ j} → Bsᵍ ℓ → j ≤ ℓ → Tr⁺ j → E.T × E.T → Set} (𝔻 : Doms blkᵍ foldᵍ) where
    open MI (gradedᴹ foldᵍ rowsᵍ proj₁ GR.Nu Rd (E.T × E.T) proj₁ proj₂ Bd) 𝔻

    gt-low : LowAt (o , r , B) self β (ν , t) ⊤ᴰ
    gt-low _ = gt-self

module _ (o : Ok j₁) (r : BB.Rb j₁) (B : Base j₁) (t : E.T) (β : Tr⁺ j₁) (mb : GR.R j₁ (E.ψ WC.𝟙 t ∷ []) (proj₁ β)) where
  private
    F : Tr j₁ → Tr⁺ j₁
    F x = RB.ψ j₁ o r B j₁ self β x

  wc-self : ∀ {a x} → GR.R j₁ a x → GR.R j₁ (E.ψ WC.𝟙 (t ++ a) ∷ []) (proj₁ (WC.Self₁.F o r B t β mb x))
  wc-self = SelfF.LF sS (λ _ → zero) WC.𝟙 t F (RB.mono j₁ o r B j₁ self β) (λ _ → ⊴r) (λ _ _ → ⊴r) WC.pen₁
    (λ { tt {u} {b} {x} r ch → up-zero WC.𝟙 (down {s = sS} {h = λ _ → zero} stop tt) u (F x) r ch }) mb
```
