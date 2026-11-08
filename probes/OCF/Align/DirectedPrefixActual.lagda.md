# 原 component 0 的完整输出就是 unary 的逐形实例

只验收原保留片段，不改算法。所有世界、原路径及 GT 证书原样保留，
没有对证书使用命题相等或函数外延。并非完整 gtX 或 EBO 的模拟。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DirectedPrefixActual where
open import Data.Nat using (zero; suc)
open import Data.Product using (proj₁)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (mul; _≤ᵛ_)
open import OCF.Lean.DirectedPrefixIf using (unary; sums; point)
import OCF.Lean.DirectedPrefixBuild as Prefix
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo; same-value)
import OCF.Align.GridBaseKeep as Keep
import OCF.Lean.ThirdFold as Fold

module _ {S : KS} where
  add-shape : ∀ {a b c d : HB S} → Same a b → Same c d → Same (a ⊞ c) (b ⊞ d)
  add-shape p zz = p
  add-shape p (ss q) = ss (add-shape p q)
  add-shape p (ll q) = ll (λ n → add-shape p (q n))
  add-shape p (oo q) = oo (λ e → add-shape p (q e))

module Actual (V : KS) (w : Wd V) (lw : LgW V w)
  (fb : HB V) (normal : HB V → HB V) (normal-legal : ∀ a → LgB (normal a))
  (pk : (κ : K V) → E V κ) (pk-bd : ∀ κ → Bd V κ (pk κ) w)
  (B : HB V) (lB : LgB B) (p : hs hz ⊲[ w ] B)
  (b : Fold.GT V w lw hz) where
  module K = Keep.Kept V w lw fb normal normal-legal pk pk-bd B lB p b
  module F = Fold V w lw

  mul-shape : ∀ {a} (x : F.GT hz) → Same a (proj₁ x) → ∀ n →
    Same (mul a n) (proj₁ (F.mulG x n))
  mul-shape x q zero = q
  mul-shape x q (suc n) = add-shape (mul-shape x q n) q

  sum-shape : ∀ {f} (g : _ → F.GT hz) → (∀ n → Same (f n) (proj₁ (g n))) → ∀ n →
    Same (sums f n) (proj₁ (F.ΣG g n))
  sum-shape g q zero = q zero
  sum-shape g q (suc n) = add-shape (sum-shape g q n) (q (suc n))

  shape : ∀ a → Same (unary a) (K.run a)
  shape hz = ss zz
  shape (hs a) = ll (mul-shape _ (shape a))
  shape (hl f) = ll (sum-shape _ (λ n → shape (f n)))
  shape (hΩ κ g) = oo (λ e → shape (g e))

  prefix-lower : ∀ η A a → η ≤ᵛ unary A → point η a ≤ᵛ K.run (A ⊞ a)
  prefix-lower η A a q = trans (Prefix.lower η A a q) (same-value (shape (A ⊞ a)))
    where open import OCF.Lean.NegFold1Base renaming (≤ᵛ-trans to trans)
```

此桥有 GridBaseKeep.Actual 的全部原 Sb 地板实例作可满足性依据。
后续若要放回完整高根链，仍须处理原 same/above 与真实前缀的调用，
不能将本片段的逐形等式推广成整个原运行器的值单调性。
