# 有限层端点的等式换型
验收文件；编译定理。与指定有限层相等可判定，由此给有限端点等式的证据无关。
来源：标准库 Constant⇒UIP 的常值正规化证明，在固定有限右端点上重写；没有全局 K 或函数外延。
MB 的两份端点证据由此换型，不改树、折叠、合法性与原关系。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPJPoint where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (recompute; recompute-constant)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Relation.Binary.PropositionalEquality.Properties using (trans-symʳ)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiCLFam using (fn)
open import OCF.Lean.YiHCBridge using (MB)
import OCF.Align.EboLeanDef as E
open import OCF.Lean.YiPJPath using (height; height-fn; rank-e)

S : L → L
S ℓ = nd sS (λ _ → ℓ)
child : L → L
child zero = zero
child (nd sS h) = h tt
child (nd sL h) = zero
child (nd (sΩ k) h) = zero

decFin : (n : ℕ) (ℓ : L) → Dec (ℓ ≡ fn n)
decFin zero zero = yes refl
decFin zero (nd s h) = no (λ ())
decFin (suc n) zero = no (λ ())
decFin (suc n) (nd sL h) = no (λ ())
decFin (suc n) (nd (sΩ k) h) = no (λ ())
decFin (suc n) (nd sS h) with decFin n (h tt)
... | yes e = yes (cong S e)
... | no ne = no (λ e → ne (cong child e))

normal : ∀ n ℓ → ℓ ≡ fn n → ℓ ≡ fn n
normal n ℓ e = recompute (decFin n ℓ) e
correct : ∀ n ℓ (e : ℓ ≡ fn n) → trans (normal n ℓ e) (sym (normal n (fn n) refl)) ≡ e
correct n .(fn n) refl = trans-symʳ (normal n (fn n) refl)
proof-irrel : ∀ n ℓ (e e′ : ℓ ≡ fn n) → e ≡ e′
proof-irrel n ℓ e e′ = trans (sym (correct n ℓ e))
  (trans (cong (λ p → trans p (sym (normal n (fn n) refl))) (recompute-constant (decFin n ℓ) e e′)) (correct n ℓ e′))
index-eq : ∀ N j ℓ → ℓ ≡ fn N → ℓ ≡ fn j → N ≡ j
index-eq N j ℓ e e′ = trans (sym (rank-e ℓ e)) (rank-e ℓ e′)

change : ∀ N j (d : N ≡ j) ℓ (e : ℓ ≡ fn N) (e′ : ℓ ≡ fn j) {a : E.T} {x : Tr ℓ}
       → MB ℓ e a x → MB ℓ e′ a x
change N .N refl ℓ e e′ {a} {x} m = subst (λ q → MB ℓ q a x) (proof-irrel N ℓ e e′) m
```
