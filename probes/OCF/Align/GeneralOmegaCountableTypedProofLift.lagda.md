# 原source位置的参照层嵌入与逐点组合

验收专用。只从原p:A⊲B构造旧严格前驱的嵌入，较小侧合法证沿p
取出。组合律显式保留这份合法证的subst，不用函数外延或任意证据
无关。它用于Read的up子证书，不反射完成前后的旧层。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedProofLift where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import OCF.Lean.CRwBase
import OCF.Align.Level as L
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height)

lift : ∀ {A B : Cd} (p : A ⊲ B) lB → L.Simᴵ (height A (lgB⊲ p tt lB)) (height B lB)
lift hself lB q = q
lift (hsuc p) lB q = L.suc (lift p lB q)
lift (hlim n p) lB q = L.lim n (lift p (proj₂ lB n) q)
lift (hLim {κ = ()} e p) lB q

legal-compose : ∀ {A C B : Cd} (p : A ⊲ C) (r : C ⊲ B) lB →
  lgB⊲ p tt (lgB⊲ r tt lB) ≡ lgB⊲ (⊲ᴮ-tr p r) tt lB
legal-compose p hself lB = refl
legal-compose p (hsuc r) lB = legal-compose p r lB
legal-compose p (hlim n r) lB = legal-compose p r (proj₂ lB n)
legal-compose p (hLim {κ = ()} e r) lB

lift-compose : ∀ {A C B : Cd} (p : A ⊲ C) (r : C ⊲ B) lB {j}
  (q : j L.<ᴵ height A (lgB⊲ p tt (lgB⊲ r tt lB))) →
  lift r lB (lift p (lgB⊲ r tt lB) q) ≡
  lift (⊲ᴮ-tr p r) lB (subst (λ la → j L.<ᴵ height A la) (legal-compose p r lB) q)
lift-compose p hself lB q = refl
lift-compose p (hsuc r) lB q = cong L.suc (lift-compose p r lB q)
lift-compose p (hlim n r) lB q = cong (L.lim n) (lift-compose p r (proj₂ lB n) q)
lift-compose p (hLim {κ = ()} e r) lB q

suc-lift : ∀ {A B : Cd} (p : hs A ⊲ B) lB {j}
  (q : j L.<ᴵ height A (lgB⊲ p tt lB)) →
  lift p lB (L.suc q) ≡ lift (⊲ᴮ-tr (hsuc hself) p) lB
    (subst (λ la → j L.<ᴵ height A la) (legal-compose (hsuc hself) p lB) q)
suc-lift p lB q = lift-compose (hsuc hself) p lB q

lim-lift : ∀ {f : ℕ → Cd} {B} (p : hl f ⊲ B) lB n {j}
  (q : j L.<ᴵ height (f n) (proj₂ (lgB⊲ p tt lB) n)) →
  lift p lB (L.lim n q) ≡ lift (⊲ᴮ-tr (hlim n hself) p) lB
    (subst (λ la → j L.<ᴵ height (f n) la) (legal-compose (hlim n hself) p lB) q)
lim-lift p lB n q = lift-compose (hlim n hself) p lB q
```

每个律都是单条旧严格路径的等式，未拼出两嵌入函数的等式。原Read
的ru-s/ru-l因此可沿实际source子位置继续，但Read在两端合法证下的
完整运输仍须由关系递归另证。
