# 替代写法的探针 (二): 折叠的两个候选

> 判决: 原型 (两个候选折叠), 合法性由类型给出, 无前提; 不替换主线. 改动的是 Ω 形状上经指定孩子 c′ 的两行 (结点的保留判定, 嵌入 `up x c y`), 其余各行与 `YiRWFold` 逐字相同. 两行都不比较 c 与 c′, 只在同一层号里比较路径 (`YiAltCmp.cmp`).
> 候选一 (`lv = false`, 归一): 目标路径 v : j ≤ h c′ 若经下标层 (cmp 交出 j ≤ k), 就按下标层侧那一行处理 (对一切孩子 c 交接, 结点按孩子层判定); 否则同主线. 候选二 (`lv = true`, 层号比较): 另加两条: 结点的槽位层号 a 经下标层且 a 在 j 之下时, 保留在路径末端的槽位; 嵌入在 k ≤ j 时先折到下标层 k 再嵌进 j.
> 不否定什么. 行律与无关性在 `YiAltCheck`, 有限测试在 `YiAltTest`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAltFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; mapK; node⁺; nodeLe)
open import OCF.Lean.YiAltCmp
```

同一层里两棵非零树的和 (右项不必来自第 0 层).

```agda
infixl 6 _⊹_
_⊹_ : ∀ {j} → Tr⁺ j → Tr⁺ j → Tr⁺ j
(b , nb) ⊹ (y , ny) = b + y , ◃t nb (+-mono b ny)
```

## 保留判定, 折叠, 单调

改动的三处: `kp` 的 `(inj₂ (c , t)) (inc c′ v)` 一行, `ψ` 与 `mono` 的 `(inc c′ v) … (up x c y e)` 各行. 其余与 `YiRWFold` 逐字相同.

```agda
module Fold (lv : Bool) where

  mutual
    kp : (ℓ : L) → Ok ℓ → (p : Pos ℓ) → ∀ {j} → j ≤ ℓ → Keep j (Br ℓ p) (fromBr ℓ p zero)
    kp ℓ             o               p              self      = just (p , (λ z → z) , refl)
    kp (nd s h)      (_ , oc)        (inj₂ (c , t)) (inu vs)  = kp⁼ (h c) (oc c) t (vs c)
    kp (nd (sΩ k) h) ((_ , kh) , oc) (inj₂ (c , t)) (ink v)   = kp⁼ (h c) (oc c) t (v ∙ kh c)
    kp (nd sS h)     (_ , oc)        (inj₂ (c , t)) (inc _ v) = kp⁼ (h c) (oc c) t v
    kp (nd sL g)     (r , oc)        (inj₂ (m , t)) (inc n v) =
      cW (way g r m n) (λ u → mapK (pshBr u t) (pshFirst u t) (kp⁼ (g n) (oc n) (psh u t) v))
                       (λ u → kp⁼ (g m) (oc m) t (v ∙ u))
    kp (nd (sΩ k) h) ((_ , kh) , oc) (inj₂ (c , t)) (inc c′ v) =
      cM (cmp (h c′) (oc c′) v (kh c′)) (λ u → kp⁼ (h c) (oc c) t (u ∙ kh c))
        (sel lv (cM (cmp (h c) (oc c) (posW⁼ (h c) t) (kh c))
                   (λ u → cM (cmp (h c′) (oc c′) (u ∙ kh c′) v)
                            (λ w → mapK (proj₂ (sl⁼ (h c) t)) refl (end w)) nothing)
                   nothing)
                nothing)
    kp (nd (sΩ k) h) ((ok , _) , _)  (inj₁ t)       (ink v)   = kp⁼ k ok t v
    kp (nd (sΩ k) h) ((_ , kh) , oc) (inj₁ t)       (inc c v) =
      mapK (pshBr (kh c) t) (pshFirst (kh c) t) (kp⁼ (h c) (oc c) (psh (kh c) t) v)
    kp (nd (sΩ k) h) ((_ , kh) , oc) (inj₁ t)       (inu vs)  =
      mapK (pshBr (kh zero) t) (pshFirst (kh zero) t) (kp⁼ (h zero) (oc zero) (psh (kh zero) t) (vs zero))

    kp⁼ : (a : L) → Ok a → (t : Pos⁼ a) → ∀ {j} → j ≤ a → Keep j (Br⁼ a t) (bz⁼ a t)
    kp⁼ a o (inj₁ _) w = nothing
    kp⁼ a o (inj₂ p) w = kp a o p w

  mutual
    ψ : (ℓ : L) → Ok ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j
    ψ ℓ o B j w β zero      = β
    ψ ℓ o B j w β (suc x)   = next⁺ (ψ ℓ o B j w β x)
    ψ ℓ o B j w β (lim f a) = lim⁺ (λ n → ψ ℓ o B j w β (f n)) (λ n → mono ℓ o B j w β (a n))
    ψ ℓ o B j w β (Ω p g)   = node⁺ (kp ℓ o p w) (λ z → ψ ℓ o B j w β (g z))
      (λ z → fromBr ℓ p (proj₁ (ψ ℓ o B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z))))
    ψ (nd s h) o B _ self β (up x c y e) = Up (h c) (down stop c) (ψ (nd s h) o B _ self β x) y
    ψ (nd s h) o B j (inu ws) β (up x c y e) =
      ψ (h c) (proj₂ o c) (λ i u → ψ (nd s h) o B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o B j (inu ws) β x) y
    ψ (nd (sΩ k) h) o B j (ink v) β (up x c y e) =
      ψ (h c) (proj₂ o c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
        (ψ (nd (sΩ k) h) o B j (ink v) β x) y
    ψ (nd sS h) o B j (inc c′ v) β (up x c y e) =
      ψ (h c) (proj₂ o c) (λ i u → ψ (nd sS h) o B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o B j (inc c′ v) β x) y
    ψ (nd sL g) o B j (inc n v) β (up x m y e) = cW (way g (proj₁ o) m n)
      (λ u → ψ (g n) (proj₂ o n) (λ i u′ → ψ (nd sL g) o B i (inc n u′) (B i (inc n u′)) x) j v
               (ψ (nd sL g) o B j (inc n v) β x) (proj₁ (emb (g n) (proj₂ o n) u (y , e))))
      (λ u → ψ (g m) (proj₂ o m) (λ i u′ → ψ (nd sL g) o B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
               (ψ (nd sL g) o B j (inc n v) β x) y)
    ψ (nd (sΩ k) h) o B j (inc c′ v) β (up x c y e) =
      cM (cmp (h c′) (proj₂ o c′) v (proj₂ (proj₁ o) c′))
        (λ u → ψ (h c) (proj₂ o c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x) j (u ∙ proj₂ (proj₁ o) c) (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) y)
        (sel lv (cM (cmp (h c′) (proj₂ o c′) (proj₂ (proj₁ o) c′) v)
                   (λ u → (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) ⊹ (emb j (Ok-≤ (h c′) (proj₂ o c′) v) u (ψ (h c) (proj₂ o c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x) k (proj₂ (proj₁ o) c) (B k (ink self)) y)))
                   ((ψ (nd (sΩ k) h) o B j (inc c′ v) β x) ⊞ ψ (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y))
                ((ψ (nd (sΩ k) h) o B j (inc c′ v) β x) ⊞ ψ (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y))

    mono : (ℓ : L) (o : Ok ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) {x y : Tr ℓ}
         → ℓ ⊢ x ◃ y → j ⊢ proj₁ (ψ ℓ o B j w β x) ◃ proj₁ (ψ ℓ o B j w β y)
    mono ℓ o B j w β ◃s           = ◃l zero
    mono ℓ o B j w β (◃l n)       = ◃l n
    mono ℓ o B j w β (◃w {p = p}) = nodeLe (kp ℓ o p w) _ _
    mono (nd s h) o B _ self β (◃u x c y e) = Upm (h c) (down stop c) (ψ (nd s h) o B _ self β x) e
    mono (nd s h) o B j (inu ws) β (◃u x c y e) =
      mono (h c) (proj₂ o c) (λ i u → ψ (nd s h) o B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o B j (inu ws) β x) e
    mono (nd (sΩ k) h) o B j (ink v) β (◃u x c y e) =
      mono (h c) (proj₂ o c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
        (ψ (nd (sΩ k) h) o B j (ink v) β x) e
    mono (nd sS h) o B j (inc c′ v) β (◃u x c y e) =
      mono (h c) (proj₂ o c) (λ i u → ψ (nd sS h) o B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o B j (inc c′ v) β x) e
    mono (nd sL g) o B j (inc n v) β (◃u x m y e) =
      cW-ind (λ Z → j ⊢ proj₁ (ψ (nd sL g) o B j (inc n v) β x) ◃ proj₁ Z) (way g (proj₁ o) m n)
        (λ u → mono (g n) (proj₂ o n) (λ i u′ → ψ (nd sL g) o B i (inc n u′) (B i (inc n u′)) x) j v
                 (ψ (nd sL g) o B j (inc n v) β x) (proj₂ (emb (g n) (proj₂ o n) u (y , e))))
        (λ u → mono (g m) (proj₂ o m) (λ i u′ → ψ (nd sL g) o B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
                 (ψ (nd sL g) o B j (inc n v) β x) e)
    mono (nd (sΩ k) h) o B j (inc c′ v) β (◃u x c y e) =
      cM-ind (λ Z → j ⊢ proj₁ (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) ◃ proj₁ Z) (cmp (h c′) (proj₂ o c′) v (proj₂ (proj₁ o) c′))
        (λ u → mono (h c) (proj₂ o c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x) j (u ∙ proj₂ (proj₁ o) c) (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) e)
        (sel-ind (λ Z → j ⊢ proj₁ (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) ◃ proj₁ Z) lv
          (cM-ind (λ Z → j ⊢ proj₁ (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) ◃ proj₁ Z) (cmp (h c′) (proj₂ o c′) (proj₂ (proj₁ o) c′) v)
            (λ u → +-mono _ (proj₂ (emb j (Ok-≤ (h c′) (proj₂ o c′) v) u (ψ (h c) (proj₂ o c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x) k (proj₂ (proj₁ o) c) (B k (ink self)) y))))
            (+-mono _ (ι-mono j (proj₂ (ψ (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)))))
          (+-mono _ (ι-mono j (proj₂ (ψ (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)))))
    mono (nd s h) o B _ self β (◃c x c r) = Upm (h c) (down stop c) (ψ (nd s h) o B _ self β x) r
    mono (nd s h) o B j (inu ws) β (◃c x c r) =
      mono (h c) (proj₂ o c) (λ i u → ψ (nd s h) o B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o B j (inu ws) β x) r
    mono (nd (sΩ k) h) o B j (ink v) β (◃c x c r) =
      mono (h c) (proj₂ o c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
        (ψ (nd (sΩ k) h) o B j (ink v) β x) r
    mono (nd sS h) o B j (inc c′ v) β (◃c x c r) =
      mono (h c) (proj₂ o c) (λ i u → ψ (nd sS h) o B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o B j (inc c′ v) β x) r
    mono (nd sL g) o B j (inc n v) β (◃c x m r) =
      cW-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (way g (proj₁ o) m n)
        (λ u → mono (g n) (proj₂ o n) (λ i u′ → ψ (nd sL g) o B i (inc n u′) (B i (inc n u′)) x) j v
                 (ψ (nd sL g) o B j (inc n v) β x) (emb-mono (g n) (proj₂ o n) u r))
        (λ u → mono (g m) (proj₂ o m) (λ i u′ → ψ (nd sL g) o B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
                 (ψ (nd sL g) o B j (inc n v) β x) r)
    mono (nd (sΩ k) h) o B j (inc c′ v) β (◃c x c r) =
      cM-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (cmp (h c′) (proj₂ o c′) v (proj₂ (proj₁ o) c′))
        (λ u → mono (h c) (proj₂ o c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x) j (u ∙ proj₂ (proj₁ o) c) (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) r)
        (sel-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) lv
          (cM-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (cmp (h c′) (proj₂ o c′) (proj₂ (proj₁ o) c′) v)
            (λ u → +-mono _ (emb-mono j (Ok-≤ (h c′) (proj₂ o c′) v) u
                      (mono (h c) (proj₂ o c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x) k (proj₂ (proj₁ o) c) (B k (ink self)) r)))
            (+-mono _ (ι-mono j (mono (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) r))))
          (+-mono _ (ι-mono j (mono (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) r))))
    mono ℓ o B j w β (◃t d d′) = ◃t (mono ℓ o B j w β d) (mono ℓ o B j w β d′)

  ψ₀ : (ℓ : L) → Ok ℓ → Tr ℓ → Tr⁺ zero
  ψ₀ ℓ o = ψ ℓ o (B₀ ℓ) zero (z≤ ℓ) (Ωt zero)

  twᶜ : ℕ → Tr zero
  twᶜ n = proj₁ (ψ₀ (tw n) (Ok-tw n) (proj₁ (Ωt (tw n))))

  EBOᶜ : Tr zero
  EBOᶜ = proj₁ (ψ₀ Λ Ok-Λ (proj₁ (Ωt Λ)))
```
