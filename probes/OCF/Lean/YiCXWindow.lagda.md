# 局部派发允许非唯一的槽位标签
验收文件，读记号；编译定理：`fn 3 → fn 2` 的全部槽位有非空标签窗，同一槽位的 0、1 均满足完整 `KeepSpec`。
`no-frame-Ω` 把 `YiGLFrame.no-frame-S` 的零标签冲突移到 Ω 形状的 `ink self`；复用 `nu0`、`pen-gt`。
不否定 LowKeep；标签窗没有递归保持定理，不给新序数界，不改树、折叠与合法性。
入口：`window-frame`、`window-nonunique`；统一量化的限制见 `YiCXLabels`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCXWindow where
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (kp)
open import OCF.Lean.YiGTNode using (KeepSpec; NodeFrame)
open import OCF.Lean.YiCLFam using (fn; okf)
open import OCF.Lean.YiGLFrame using (nu0)
open import OCF.Lean.YiGTIndexNeg using (pen-gt)
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E


no-frame-Ω : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h))
  (q : Pos k) (ν : E.T) → NodeFrame (nd (sΩ k) h) o k (ink self) ν → ⊥
no-frame-Ω k h o q ν fr = pen-gt
  (proj₁ (fr (inj₁ (inj₂ q)) [] (nu0 k q)))
  (fr (inj₁ (inj₁ tt)) [] (GR.c0 refl))

Ω-one : L
Ω-one = nd (sΩ (fn 1)) (λ _ → fn 1)
Ω-one-ok : Ok Ω-one
Ω-one-ok = (okf 1 , λ _ → self) , λ _ → okf 1
Ω-one-slot : Pos (fn 1)
Ω-one-slot = inj₂ (tt , inj₁ tt)

check-premises : (ν : E.T) → NodeFrame Ω-one Ω-one-ok (fn 1) (ink self) ν → ⊥
check-premises = no-frame-Ω (fn 1) (λ _ → fn 1) Ω-one-ok Ω-one-slot

no-frame-tw2 : (ν : E.T) → NodeFrame (tw 2) (Ok-tw 2) (tw 1) (ink self) ν → ⊥
no-frame-tw2 = no-frame-Ω (tw 1) (λ c → tw 1 ⊕ ↑ (tw 1) c)
  (Ok-tw 2) (inj₁ (inj₁ tt))

p₂ p₁ p₀ : Pos (fn 3)
p₂ = inj₂ (tt , inj₁ tt)
p₁ = inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))
p₀ = inj₂ (tt , inj₂ (inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))))

data Window : Pos (fn 3) → E.T → Set where
  at₂ : Window p₂ (E.natT 2)
  at₁₀ : Window p₁ []
  at₁₁ : Window p₁ (E.natT 1)
  at₀ : Window p₀ []

window-rd : ∀ {p κ} → Window p κ → GR.Nu (fn 3) p κ
window-rd at₂ = GR.ca (inj₂ (refl , GR.ca (inj₂ (refl , GR.c0 refl))))
window-rd at₁₀ = GR.c0 refl
window-rd at₁₁ = GR.ca (inj₂ (refl , GR.c0 refl))
window-rd at₀ = GR.c0 refl

window-frame : (p : Pos (fn 3)) (κ : E.T) → Window p κ
  → KeepSpec (fn 3) (fn 2) (E.natT 2) p κ (kp (fn 3) (okf 3) p (inc tt self))
window-frame .p₂ .(E.natT 2) at₂ = refl
window-frame .p₁ .[] at₁₀ = inj₁ refl , GR.c0 refl , λ η c r → r
window-frame .p₁ .(E.natT 1) at₁₁ = inj₂ refl , GR.ca (inj₂ (refl , GR.c0 refl)) , λ η c r → r
window-frame .p₀ .[] at₀ = inj₁ refl , GR.c0 refl , λ η c r → r

window-nonunique : ((p : Pos (fn 3)) {κ ν : E.T} → Window p κ → Window p ν → κ ≡ ν) → ⊥
window-nonunique unique with unique p₁ at₁₀ at₁₁
... | ()

window-covers : (p : Pos (fn 3)) → Σ E.T (Window p)
window-covers (inj₂ (tt , inj₁ tt)) = E.natT 2 , at₂
window-covers (inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))) = E.natT 1 , at₁₁
window-covers (inj₂ (tt , inj₂ (inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))))) = [] , at₀

Ω-one-rd : GR.Rd (fn 1) (E.natT 1)
Ω-one-rd = GR.ca (inj₂ (refl , GR.c0 refl))
```
