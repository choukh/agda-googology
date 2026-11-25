# 指定 Ω 结点的整行值下界
验收文件；编译定理：F2 对照结点的标准底输出不低于 BTBO，尚需 YiC0Connect 的公共接线。
formE 忽略合法性证明的差异，以同形关系作出口，不要求树的字面相等。
来源：E-cum/E→≅ 复用 YiLSTw1，迭代相等复用 YiLPFGH；链用 YiC0Node。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiC0Rows where
open import Data.Unit using (tt)
import Data.Product
open import Data.Sum using (inj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold
import OCF.Lean.YiC0Node as N
p : Pos N.ΩN
p = inj₁ (inj₁ tt)
g : Tr zero → Tr N.ΩN
g x = up zero x (Ωt (N.h₁ x)) (Ωt-nz (N.h₁ x))
G : Tr zero → Tr zero
G x = ψ⊥ N.ΩN N.εN N.ρN (B₀ N.ΩN) (g x)
K : Tr zero → Tr zero
K x = fromBr N.ΩN p (ψs N.ΩN N.εN N.ρN (B₀ N.ΩN) (at N.ΩN p) (posW N.ΩN p)
  (bs (B₀ N.ΩN) (at N.ΩN p) (posW N.ΩN p)) (ns (B₀ N.ΩN) (at N.ΩN p) (posW N.ΩN p)) (g x))
G-eq : ∀ x → G x ≡ N.G x
G-eq x = refl
K-eq : ∀ x → K x ≡ N.K x
K-eq x = refl
form : N.output ≡ limc (λ n → G (iter K zero n))
  (λ n → nz⊥ N.ΩN N.εN N.ρN (B₀ N.ΩN) (g (iter K zero n)))
form = refl
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (sym; subst; cong; trans)
open import OCF.Lean.YiLSTw1 using (E; E-cum; E→≅)
open import OCF.Lean.YiKABY using (E-reflF)
open import OCF.Lean.YiLPFGH using (iter-cong)
import OCF.Lean.YiLSRead as RD
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≅→≼; l≼)
open import OCF.Align.BTBOFullEmb using (Ψ-emb)
open import OCF.Align.YiBtValBT using (module D)
point : ∀ n → G (iter K zero n) ≡ N.G (N.pt n)
point n = trans (G-eq (iter K zero n)) (cong N.G (iter-cong K N.K K-eq zero n))
series : Tr zero
series = limc (λ n → N.G (N.pt n)) (λ n → N.G-nz (N.pt n))
formE : E N.output series
formE = subst (λ x → E x series) (sym form)
  (E-cum (λ n → G (iter K zero n)) (λ n → N.G (N.pt n))
    (λ n → subst (E (G (iter K zero n))) (point n) (E-reflF (G (iter K zero n)))))
btbo-series : D.BTBOᴵ ≼ RD.read series
btbo-series = l≼ (λ n → ≼-trans (Ψ-emb (N.emb n (Data.Product.proj₁ (N.chainV n)) (Data.Product.proj₂ (N.chainV n))))
  (RD.limcum≽ (λ k → N.G (N.pt k)) (λ k → N.G-nz (N.pt k)) (Data.Nat.suc (Data.Product.proj₁ (N.chainV n)))
    (N.LOWER (Data.Nat.suc (Data.Product.proj₁ (N.chainV n))))))
btbo : D.BTBOᴵ ≼ RD.read N.output
btbo = ≼-trans btbo-series (≅→≼ (L.≅-sym (E→≅ formE)))
```
