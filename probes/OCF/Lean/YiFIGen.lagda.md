# 整体接口在主线关系上: `Graded` 与生成原理

> 验收文件 (读记号). 判决: 编译定理, 无前提. 候选折叠 `Fold K lifted` 连同主线的关系 `YiGIRel.R` 填进 `Graded` (`gradedᴷ`); 每层的关系满足带向下封闭的生成原理 `Gen⁺ _≤ᵀ_` (`genᴷ`), 以及 `Weak`, `Lim`, `Node` (`weakᴷ`, `limᴷ`, `nodeᴷ`). 所以 `YiFIFold.lowᴷ` 在主线关系上余下的前提只有出口 `Out`.
> 不给出什么: 没有实填 `Out`; 六条规则的 `Gen` (不带 `mc`) 对主线关系成立与否没有判定, `YiFINeg.main-¬low` 因此没有主线关系上的实例.
> 来源: 归纳原理照 `YiAbsGFin.Ind`, 加 `mc` 一条.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFIGen where
open import Data.Bool using (Bool)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock hiding (R)
import OCF.Lean.YiRWBlock as B
open import OCF.Lean.YiDXFold using (KeepFn)
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiKVRel as KV
open import OCF.Lean.YiHCRel using (Mᴴ; mz; m1; mL; mΩ; mU; mw; mc)
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Lean.YiAbsSimInst using (𝕍)
open import OCF.Lean.YiAbsGEbo using (refᴱ)
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiAbsGRow using (module Row)
open import OCF.Lean.YiGIBlock using (blkᵍ; slTᵍ; slT⁼ᵍ)
open import OCF.Lean.YiGIInst using (Bdᵍ; domsᵍ)
open import OCF.Lean.YiFIIface
open import OCF.Lean.YiFIFold using (foldᴷ; rowsᴷ)
```

## 分支关系与槽位层的关系

`GR.Low ℓ p` 按槽位的位置递归到槽位层的 `GR.R`; 两个方向都是恒等.

```agda
mutual
  →low : ∀ ℓ p {η c} → GR.R (at ℓ p) η (slTᵍ ℓ p c) → GR.Low ℓ p η c
  →low (nd s h)      (inj₂ (c , t)) = →low⁼ (h c) t
  →low (nd (sΩ k) h) (inj₁ t)       = →low⁼ k t

  →low⁼ : ∀ a t {η c} → GR.R (proj₁ (sl⁼ a t)) η (slT⁼ᵍ a t c) → GR.Low⁼ a t η c
  →low⁼ a (inj₁ _) m = m
  →low⁼ a (inj₂ p) m = →low a p m

mutual
  low→ : ∀ ℓ p {η c} → GR.Low ℓ p η c → GR.R (at ℓ p) η (slTᵍ ℓ p c)
  low→ (nd s h)      (inj₂ (c , t)) = low→⁼ (h c) t
  low→ (nd (sΩ k) h) (inj₁ t)       = low→⁼ k t

  low→⁼ : ∀ a t {η c} → GR.Low⁼ a t η c → GR.R (proj₁ (sl⁼ a t)) η (slT⁼ᵍ a t c)
  low→⁼ a (inj₁ _) m = m
  low→⁼ a (inj₂ p) m = low→ a p m
```

## 归纳原理

```agda
module Ind {S : Sg} {Low : (p : P S) → E.T → B.B S p → Set} {Chd : (c : C S) → E.T → D S c → Set}
           {Nu : P S → E.T → Set} (Q : E.T → T S → Set)
    (qz : ∀ {x} → Q [] x)
    (q1 : ∀ {t x} → E.cof t ≡ E.c1 → Mᴴ S Low Chd Nu (E.pred t) x → Q (E.pred t) x → Q t (suc x))
    (qL : ∀ {t x} → E.cof t ≡ E.cω → (∀ n → Mᴴ S Low Chd Nu (E.fsn t n) x) → (∀ n → Q (E.fsn t n) x) → Q t x)
    (qΩ : ∀ {t ν} (p : P S) (g : B.B S p → T S) → E.cof t ≡ E.cΩ ν → Nu p ν
        → (∀ η c → Low p η c → Mᴴ S Low Chd Nu (E.fsT t η) (g c))
        → (∀ η c → Low p η c → Q (E.fsT t η) (g c)) → Q t (Ω p g))
    (qU : ∀ {t s x} (c : C S) (y : D S c) (e : B.R S c (z₀ S c) y) → Mᴴ S Low Chd Nu t x → Q t x → Chd c s y
        → Q (t ++ s) (up x c y e))
    (qw : ∀ {t x x′} → Mᴴ S Low Chd Nu t x → Q t x → Lt S x x′ → Q t x′)
    (qc : ∀ {s t x} → s ≤ᵀ t → Mᴴ S Low Chd Nu t x → Q t x → Q s x) where

  ind : ∀ {t x} → Mᴴ S Low Chd Nu t x → Q t x
  ind mz                          = qz
  ind (m1 e r)                    = q1 e r (ind r)
  ind (mL e h)                    = qL e h (λ n → ind (h n))
  ind (mΩ {p = p} {g = g} e nu h) = qΩ p g e nu h (λ η c l → ind (h η c l))
  ind (mU {c = c} {y = y} {e = e} m ch) = qU c y e m (ind m) ch
  ind (mw m d)                    = qw m (ind m) d
  ind (mc le m)                   = qc le m (ind m)
```

## 实例

```agda
module _ (K : KeepFn) (lifted : Bool) where
  gradedᴷ : Graded blkᵍ (foldᴷ K lifted) (rowsᴷ K lifted) refᴱ 𝕍
  gradedᴷ = record
    { ℓ₀ = zero ; v = KV.readRW ; R = GR.R ; Rd = GR.Rd ; Nu = GR.Nu ; bt = proj₁
    ; cl = λ _ t → E.ψ [] t ∷ [] ; Cx = λ _ _ → E.T ; app = λ t₀ a → E.ψ [] (t₀ ++ a) ∷ [] ; Bd = Bdᵍ }

  domsᴷ : Doms blkᵍ (foldᴷ K lifted)
  domsᴷ = record { Gx = λ _ _ → E.T ; Gb = λ _ _ → E.T ; Wl = λ _ → E.T ; Gl = λ _ _ → E.T }

  open FI gradedᴷ domsᴷ using (Gen⁺)
  open Laws gradedᴷ domsᴷ using (Weak; Lim; Node)
  open Row gradedᴷ domsᴷ using (Rules)

  genᴷ : ∀ ℓ → Gen⁺ _≤ᵀ_ ℓ
  genᴷ zero Q rs qc = Ind.ind Q (qz refl) q1 qL (λ ()) (λ ()) qw qc
    where open Rules rs
  genᴷ (nd s h) Q rs qc = Ind.ind Q (qz refl) q1 qL
    (λ p g e nu hR hQ → qΩ p g e nu (λ η c l → hR η c (→low (nd s h) p l)) (λ η c l → hQ η c (→low (nd s h) p l)))
    (λ c y e m q ch → qU c (y , e) m q ch) qw qc
    where open Rules rs

  weakᴷ : Weak
  weakᴷ {ℓ = zero}   = mw
  weakᴷ {ℓ = nd s h} = mw

  limᴷ : Lim
  limᴷ {ℓ = zero}   = mL
  limᴷ {ℓ = nd s h} = mL

  nodeᴷ : Node
  nodeᴷ {ℓ = nd s h} p g e nu hyp = mΩ e nu (λ η c l → hyp η c (low→ (nd s h) p l))
```
