# 换基折叠的变体: 替身的底取外层折叠在目标层以下各层的值

> 判决: 候选定义, 不替换 `YiBSFold`, 进主线由作者定; 编译通过 (停机检查, 类型即合法性, `mono`). 不读记号.
> 做了什么: `YiBSFold.ψ` 逐行照搬, 只改换基行 (`route` 落在地板之上): 替身 `seenᵛ` 的底从 `B₀` 换成 `subB`, 在目标层 j 及以下的层 i 取外层折叠在左项 x 上朝 i 的值 (底族经目标孩子 c′ 的那一项, 即孩子回退 `dn` 的写法), 严格高于 j 的层仍取 Ω 树. 不比较孩子, 只对路径用 `split`.
> 不给出什么: 没有值的定理; 高于 j 的槽位层的链仍与上下文无关 (`YiABCell.top-free`). 形状与那一格的链在 [YiABCell](YiABCell.lagda.md), 代价在 [YiABCost](YiABCost.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiABFold where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; kp; node⁺; nodeLe)
open import OCF.Lean.YiRBSib using (rb; rb-ind; rb-ind₂)
import OCF.Lean.YiRBSib as R
open import OCF.Lean.YiBSBase
```

## 替身的底

`Low j`: 目标层 j 及以下每一层上一棵非零的树 (外层折叠交来). `subB`: 换基层号 `j ⊕ b` 的底; 路径经 `split` 落到 j 以下就取 `Low` 的那一项, 否则 (层号不低于 j, 且不是偏移取尽后的 j 自身) 取 Ω 树. `split` 只读路径的字面形状.

```agda
Low : L → Set
Low j = (i : L) → i ≤ j → Tr⁺ i

subB : (j b : L) → OkO j b → Low j → Base (j ⊕ b)
subB j b ob D i q = cW (split j b ob q) (D i) (λ _ → Ωt i)

seenᵛ : ∀ {k h} (S : Schema k h) (j : L) → Ok j → floor S ≤ j → Low j → Tr⁺ j → Tr k → Tr⁺ j
seenᵛ S j oj u D β c = R.ψ (j ⊕ offsets S c)
  (Ok⊕ j (offsets S c) oj (raiseO (floor S) j (offsets S c) u (ok-offsets S c)))
  (R.rb-no _) (subB j (offsets S c) (raiseO (floor S) j (offsets S c) u (ok-offsets S c)) D)
  j (lift j (offsets S c)) β (proj₁ (Ωt (j ⊕ offsets S c)))

seen-stepᵛ : ∀ {k h} (S : Schema k h) j oj u D β c → j ⊢ proj₁ β ◃ proj₁ (seenᵛ S j oj u D β c)
seen-stepᵛ S j oj u D β c = R.mono (j ⊕ offsets S c)
  (Ok⊕ j (offsets S c) oj (raiseO (floor S) j (offsets S c) u (ok-offsets S c)))
  (R.rb-no _) (subB j (offsets S c) (raiseO (floor S) j (offsets S c) u (ok-offsets S c)) D)
  j (lift j (offsets S c)) β (proj₂ (Ωt (j ⊕ offsets S c)))
```

## 折叠与单调

除换基行外逐字同 `YiBSFold` (来源: `YiBSFold`, 其普通行搬自 `YiRBSib`). 换基行里交给替身的 `Low` 是 `λ i u′ → ψ ℓ o r B i (inc c′ (u′ ∙ v)) (B i (inc c′ (u′ ∙ v))) x`: 递归在 x 上, 结构下降.

```agda
mutual
  ψ : (ℓ : L) → Ok ℓ → Rb ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j
  ψ ℓ o r B j w β zero      = β
  ψ ℓ o r B j w β (suc x)   = next⁺ (ψ ℓ o r B j w β x)
  ψ ℓ o r B j w β (lim f a) = lim⁺ (λ n → ψ ℓ o r B j w β (f n)) (λ n → mono ℓ o r B j w β (a n))
  ψ ℓ o r B j w β (Ω p g)   = node⁺ (kp ℓ o p w) (λ z → ψ ℓ o r B j w β (g z))
    (λ z → fromBr ℓ p (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z))))
  ψ (nd s h) o r B _ self β (up x c y e) = Up (h c) (down stop c) (ψ (nd s h) o r B _ self β x) y
  ψ (nd s h) o r B j (inu ws) β (up x c y e) =
    ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o r B j (inu ws) β x) y
  ψ (nd (sΩ k) h) o r B j (ink v) β (up x c y e) =
    ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd (sΩ k) h) o r B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
      (ψ (nd (sΩ k) h) o r B j (ink v) β x) y
  ψ (nd sS h) o r B j (inc c′ v) β (up x c y e) =
    ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd sS h) o r B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o r B j (inc c′ v) β x) y
  ψ (nd sL g) o r B j (inc n v) β (up x m y e) = cW (way g (proj₁ o) m n)
    (λ u → ψ (g n) (proj₂ o n) (proj₂ r n) (λ i u′ → ψ (nd sL g) o r B i (inc n u′) (B i (inc n u′)) x) j v
             (ψ (nd sL g) o r B j (inc n v) β x) (proj₁ (emb (g n) (proj₂ o n) u (y , e))))
    (λ u → ψ (g m) (proj₂ o m) (proj₂ r m) (λ i u′ → ψ (nd sL g) o r B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
             (ψ (nd sL g) o r B j (inc n v) β x) y)
  ψ (nd (sΩ k) h) o r B j (inc c′ v) β (up x c y e) = rb (proj₁ r)
    (λ S → cW (route S j c′ v)
      (λ u → ψ (h c) (proj₂ o c) (proj₂ r c)
        (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c u′) (B i (inc c u′)) x) j (back S c u)
        (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) y)
      (λ u → seenᵛ S j (downOk (h c′) (proj₂ o c′) j v) u
        (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c′ (u′ ∙ v)) (B i (inc c′ (u′ ∙ v))) x)
        (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) c
        ⊞ ψ (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y))
    (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x ⊞ ψ (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)


  mono : (ℓ : L) (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) {x y : Tr ℓ}
       → ℓ ⊢ x ◃ y → j ⊢ proj₁ (ψ ℓ o r B j w β x) ◃ proj₁ (ψ ℓ o r B j w β y)
  mono ℓ o r B j w β ◃s           = ◃l zero
  mono ℓ o r B j w β (◃l n)       = ◃l n
  mono ℓ o r B j w β (◃w {p = p}) = nodeLe (kp ℓ o p w) _ _
  mono (nd s h) o r B _ self β (◃u x c y e) = Upm (h c) (down stop c) (ψ (nd s h) o r B _ self β x) e
  mono (nd s h) o r B j (inu ws) β (◃u x c y e) =
    mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o r B j (inu ws) β x) e
  mono (nd (sΩ k) h) o r B j (ink v) β (◃u x c y e) =
    mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd (sΩ k) h) o r B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
      (ψ (nd (sΩ k) h) o r B j (ink v) β x) e
  mono (nd sS h) o r B j (inc c′ v) β (◃u x c y e) =
    mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd sS h) o r B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o r B j (inc c′ v) β x) e
  mono (nd sL g) o r B j (inc n v) β (◃u x m y e) =
    cW-ind (λ Z → j ⊢ proj₁ (ψ (nd sL g) o r B j (inc n v) β x) ◃ proj₁ Z) (way g (proj₁ o) m n)
      (λ u → mono (g n) (proj₂ o n) (proj₂ r n) (λ i u′ → ψ (nd sL g) o r B i (inc n u′) (B i (inc n u′)) x) j v
               (ψ (nd sL g) o r B j (inc n v) β x) (proj₂ (emb (g n) (proj₂ o n) u (y , e))))
      (λ u → mono (g m) (proj₂ o m) (proj₂ r m) (λ i u′ → ψ (nd sL g) o r B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
               (ψ (nd sL g) o r B j (inc n v) β x) e)
  mono (nd (sΩ k) h) o r B j (inc c′ v) β (◃u x c y e) =
    rb-ind (λ Z → j ⊢ proj₁ (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) ◃ proj₁ Z) (proj₁ r)
      (λ S → cW-ind (λ Z → j ⊢ proj₁ (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) ◃ proj₁ Z) (route S j c′ v)
        (λ u → mono (h c) (proj₂ o c) (proj₂ r c)
          (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c u′) (B i (inc c u′)) x) j (back S c u)
          (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) e)
        (λ u → ◃t (seen-stepᵛ S j (downOk (h c′) (proj₂ o c′) j v) u
          (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c′ (u′ ∙ v)) (B i (inc c′ (u′ ∙ v))) x)
          (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) c)
          (+-mono _ (ι-mono j (proj₂ (ψ (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y))))))
      (+-mono _ (ι-mono j (proj₂ (ψ (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y))))

  mono (nd s h) o r B _ self β (◃c x c d) = Upm (h c) (down stop c) (ψ (nd s h) o r B _ self β x) d
  mono (nd s h) o r B j (inu ws) β (◃c x c d) =
    mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o r B j (inu ws) β x) d
  mono (nd (sΩ k) h) o r B j (ink v) β (◃c x c d) =
    mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd (sΩ k) h) o r B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
      (ψ (nd (sΩ k) h) o r B j (ink v) β x) d
  mono (nd sS h) o r B j (inc c′ v) β (◃c x c d) =
    mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd sS h) o r B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o r B j (inc c′ v) β x) d
  mono (nd sL g) o r B j (inc n v) β (◃c x m d) =
    cW-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (way g (proj₁ o) m n)
      (λ u → mono (g n) (proj₂ o n) (proj₂ r n) (λ i u′ → ψ (nd sL g) o r B i (inc n u′) (B i (inc n u′)) x) j v
               (ψ (nd sL g) o r B j (inc n v) β x) (emb-mono (g n) (proj₂ o n) u d))
      (λ u → mono (g m) (proj₂ o m) (proj₂ r m) (λ i u′ → ψ (nd sL g) o r B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
               (ψ (nd sL g) o r B j (inc n v) β x) d)
  mono (nd (sΩ k) h) o r B j (inc c′ v) β (◃c x c d) =
    rb-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (proj₁ r)
      (λ S → cW-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (route S j c′ v)
        (λ u → mono (h c) (proj₂ o c) (proj₂ r c)
          (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c u′) (B i (inc c u′)) x) j (back S c u)
          (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) d)
        (λ u → +-mono _ (ι-mono j (mono (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) d))))
      (+-mono _ (ι-mono j (mono (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) d)))

  mono ℓ o r B j w β (◃t d d′) = ◃t (mono ℓ o r B j w β d) (mono ℓ o r B j w β d′)
ψ₀ : (ℓ : L) → Ok ℓ → Rb ℓ → Tr ℓ → Tr⁺ zero
ψ₀ ℓ o r = ψ ℓ o r (B₀ ℓ) zero (z≤ ℓ) (Ωt zero)
closed : (n : ℕ) → Tr⁺ zero
closed n = ψ₀ (tw n) (Ok-tw n) (rb-tw n) (proj₁ (Ωt (tw n)))
```
