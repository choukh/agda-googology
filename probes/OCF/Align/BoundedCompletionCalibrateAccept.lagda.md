# 原Fold1闭项的ε₀值验收及完成项下界

验收专用：原定义完全不改。参照具有既有Lab，实际闭项只作双向值比较，
没有要求基本列逐项相同。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionCalibrateAccept where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase using (Cd; hl; hs)
open import OCF.Lean.Fold1If using (_≤ᵛ_; mul; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans; mul-≤)
import OCF.Lean.Fold1 as Old
import OCF.Align.Level as L
import OCF.Align.OCFSpecBase as S
import OCF.Align.OCFSpecAnchor as Anchor
import OCF.Align.Value as V
import OCF.Align.Correspond as Labels
import OCF.Align.LambdaOrderBridge as Order
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.BoundedCompletionCalibrateTower as Tower
import OCF.Align.BoundedCompletionCalibrateReference as Ref
import OCF.Align.BoundedCompletionPureAccept as Pure
import OCF.Align.BoundedNativeCompletionClosed as C
import OCF.Align.BoundedCompletionLowerFamily as Lower
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)

psi-mono : ∀ {a b : L.Ordᶜ L.zero} → a S.≼ b → L.ψ⁰ a S.≼ L.ψ⁰ b
psi-mono p = Order.backward (V.ψ⁰-mono⁰ (Order.forward p))

tower≤gamma : ∀ n → B.read (Tower.tower n) S.≼ Anchor.γ n
tower≤gamma zero = S.≼-refl _
tower≤gamma (suc n) = S.≼-trans (Pure.F≤ψ (Tower.tower n)) (psi-mono (tower≤gamma n))
gamma≤tower : ∀ n → Anchor.γ n S.≼ B.read (Tower.tower n)
gamma≤tower zero = S.≼-refl _
gamma≤tower (suc n) = S.≼-trans (psi-mono (gamma≤tower n)) (Pure.ψ≤F (Tower.tower n))

tower≤reference : B.read Tower.tower-limit S.≼ Ref.reference
tower≤reference = S.l≼ (λ n → S.≼l n
  (S.≼-trans (tower≤gamma n) (S.≼-trans (S.≺→≼ (Anchor.γ-step n)) (Anchor.γ≼Fδ n))))
reference≤tower : Ref.reference S.≼ B.read Tower.tower-limit
reference≤tower = S.l≼ (λ n → S.≼l (suc n)
  (S.≼-trans (Anchor.Fδ≼γ n) (gamma≤tower (suc n))))

A≤reference : B.read Old.TΩ1 S.≼ Ref.reference
A≤reference = S.≼-trans (B.read-mono Tower.A≤E) tower≤reference
reference≤A : Ref.reference S.≼ B.read Old.TΩ1
reference≤A = S.≼-trans reference≤tower (B.read-mono Tower.E≤A)

A-value-label : V.VLab (B.read Old.TΩ1) (Labels.γᴱ 1)
A-value-label = Ref.reference , Ref.reference-label ,
  Order.forward A≤reference , Order.forward reference≤A

-- 此处ε只在验收侧，绝不成为完成项定义的参数。
epsilon : Cd
epsilon = B.forget Ref.reference
epsilon≤A : epsilon ≤ᵛ Old.TΩ1
epsilon≤A = B.reference-lower-reflect reference≤A

epsilon-successor≤completed : hs epsilon ≤ᵛ C.tree
epsilon-successor≤completed = ≤-trans (OCF.Lean.Fold1If.s≤s epsilon≤A) C.strict-old-lower

epsilon-times-omega≤completed : hl (mul epsilon) ≤ᵛ C.tree
epsilon-times-omega≤completed = ≤-trans
  (l≤ (λ n → ≤l n (mul-≤ epsilon≤A n))) Lower.old-times-omega
-- 在既有Ordᶜ值语义里明确写出ε₀·ω，消除载体/加法读法的歧义。
epsilon-times-omega-reference : L.Ordᶜ L.zero
epsilon-times-omega-reference = L.lim (iter (Ref.reference L.+_) L.zero)

reference-multiples≤ : epsilon-times-omega-reference S.≼ B.read (hl (mul epsilon))
reference-multiples≤ = S.l≼ branch
  where
  branch : ∀ n → iter (Ref.reference L.+_) L.zero n S.≼ B.read (hl (mul epsilon))
  branch zero = S.z≼
  branch (suc n) = S.≼l n (S.≼-trans
    (Pure.iter-mono Ref.reference (B.read epsilon)
      (S.≅→≼ (L.≅-sym (B.reference-roundtrip Ref.reference))) (suc n))
    (S.≅→≼ (L.≅-sym (Pure.read-mul epsilon n))))

epsilon-times-omega-bound : epsilon-times-omega-reference S.≼ B.read C.tree
epsilon-times-omega-bound = S.≼-trans reference-multiples≤
  (B.read-mono epsilon-times-omega≤completed)
```

A-value-label是实际旧闭项A=Fold1.TΩ1的值验收：ψ₀(Ω₁)=ε₀。
完成项C仍是原合法闭项；所得下界为ε₀·ω的重复加法参照，也给ε₀+1。
未给C上界或EBO下界，不将这些中间界命名为ψ₀Λ。
