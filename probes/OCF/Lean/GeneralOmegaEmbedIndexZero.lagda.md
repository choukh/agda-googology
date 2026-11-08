# 原第二Ω塔地板的完整嵌入实例

这里处理原twL 2的整个lΩ地板，而非选定分量。其指标为Cd；不同反馈
的Same由纯坐标树结构运输到分量层号，再证明这些原地板异层相关。
没有把任意层号函数g当作保持Same。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaEmbedIndexZero where
open import Data.Nat using (zero; suc)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay using (_⊕L_; upL; twL)
open import OCF.Lean.LHRecFl using (flL; ΣF; cxI; gcF)
open import OCF.Lean.LHRecLeg using (module New)
open import OCF.Lean.HigherIndexConsumeCode using (pure)
open import OCF.Lean.GeneralOmegaEmbedIf
open import OCF.Lean.GeneralOmegaEmbedRun
open import OCF.Lean.GeneralOmegaEmbedGenerated using (up-both; up-right; sum-both; branch-right)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo; same-value; same-sym)
open import OCF.Lean.GeneralOmegaConsumeLayerRun using (leg-same)
import OCF.Lean.GeneralOmegaConsumeRun as R
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.BoundedDiagonalSame using (same-add)

data Shape : LH → LH → Set where
  sz : Shape lz lz
  ss′ : ∀ {x y} → Shape x y → Shape (ls x) (ls y)
  sl : ∀ {f g} → (∀ n → Shape (f n) (g n)) → Shape (OCF.Lean.LHRecTy.ll f) (OCF.Lean.LHRecTy.ll g)

floors : ∀ {x y} → Shape x y → Coded x y (flL x) (flL y)
sums : ∀ {f g} → (∀ n → Shape (f n) (g n)) → ∀ n →
  Coded (OCF.Lean.LHRecTy.ll f) (OCF.Lean.LHRecTy.ll g) (ΣF f n) (ΣF g n)
floors sz = cz
floors {ls x} {ls y} (ss′ p) = co (λ q → up-both (add (floors p) (pure-related x y (leg-same q))))
floors (sl p) = cl (sums p)
sums p zero = sum-both (floors (p zero))
sums p (suc n) = add (sums p n) (sum-both (floors (p (suc n))))

family : Cd → LH
family c = ls lz ⊕L upL lz c
family-shape : ∀ {a b} → Same a b → Shape (family a) (family b)
family-shape zz = ss′ sz
family-shape (ss p) = ss′ (family-shape p)
family-shape (ll p) = sl (λ n → family-shape (p n))
family-shape (oo {κ = ()} p)

branch-both : ∀ {k j f g e d a b} → Coded (f e) (g d) a b →
  Coded (lΩ k f) (lΩ j g)
    (ι {IxL k} {FXL k f} (inj₂ e) a) (ι {IxL j} {FXL j g} (inj₂ d) b)
branch-both cz = cz
branch-both (cs p) = cs (branch-both p)
branch-both (cl p) = cl (λ n → branch-both (p n))
branch-both (co p) = co (λ q → branch-both (p q))

X : LH
X = twL 2
φ : Cd → HB (Lv X)
φ d = ι {IxL lz} {FXL lz family} (inj₂ d) (flL (family d))
θ : Cd → HB (Lv X)
θ = New.θ (cxI lz family) (gcF φ)

theta-related : ∀ {a b} → Same a b → Coded X X (θ a) (θ b)
theta-related zz = cz
theta-related (ss p) = add (theta-related p) (branch-both (floors (family-shape p)))
theta-related (ll p) = cl (λ n → theta-related (p n))
theta-related (oo {κ = ()} p)

pure-same : ∀ {a b : Cd} → Same a b → Same (pure S⊥ a) (pure S⊥ b)
pure-same zz = zz
pure-same (ss p) = ss (pure-same p)
pure-same (ll p) = ll (λ n → pure-same (p n))
pure-same (oo {κ = ()} p)

second-floor : Coded (twL 2) (twL 2) (flL (twL 2)) (flL (twL 2))
second-floor = co (λ q → theta-related (same-add zz (pure-same (leg-same q))))
second-up : Same (R.run (twL 2) (flL (twL 2)))
  (R.run (ls (twL 2)) (up (flL (twL 2))))
second-up = sound (up-right second-floor)

second-branch : ∀ k g e → g e ≡ twL 2 →
  Same (R.run (g e) (flL (g e)))
    (R.run (lΩ k g) (ι {IxL k} {FXL k g} (inj₂ e) (flL (g e))))
second-branch k g e p = sound (branch-right
  (subst (λ x → Coded x x (flL x) (flL x)) (sym p) second-floor))

module Index (f g : Cd → LH)
  (components : ∀ {a b} → Same a b → Coded (f a) (g b) (flL (f a)) (flL (g b))) where
  θf : Cd → HB (Lv (lΩ lz f))
  θf = New.θ (cxI lz f) (gcF (λ a → ι {IxL lz} {FXL lz f} (inj₂ a) (flL (f a))))
  θg : Cd → HB (Lv (lΩ lz g))
  θg = New.θ (cxI lz g) (gcF (λ a → ι {IxL lz} {FXL lz g} (inj₂ a) (flL (g a))))
  theta : ∀ {a b} → Same a b → Coded (lΩ lz f) (lΩ lz g) (θf a) (θg b)
  theta zz = cz
  theta (ss p) = add (theta p) (branch-both (components p))
  theta (ll p) = cl (λ n → theta (p n))
  theta (oo {κ = ()} p)
  floor : Coded (lΩ lz f) (lΩ lz g) (flL (lΩ lz f)) (flL (lΩ lz g))
  floor = co (λ q → theta (same-add zz (pure-same (leg-same q))))

second-general : Coded (twL 2) (twL 2) (flL (twL 2)) (flL (twL 2))
second-general = Index.floor family family (λ p → floors (family-shape p))

second-lower : R.run (twL 2) (flL (twL 2)) ≤ᵛ
  R.run (ls (twL 2)) (up (flL (twL 2)))
second-lower = same-value second-up
second-upper : R.run (ls (twL 2)) (up (flL (twL 2))) ≤ᵛ
  R.run (twL 2) (flL (twL 2))
second-upper = same-value (same-sym second-up)
```

second-up完整解决这一实际lΩ站的A跨层身份（结构Same，因而Cd值
双向比较可直接取已有Same→值）。下一高指标层的坐标本身含Ω，
family-shape的空Ω分支不再适用；尚未取得全twL族与EBO下界。
