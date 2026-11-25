# 第 2 项比较中的第一位置前提
不读记号；编译否定：现有路径嵌入的源 Ω 树不在目标 Ω 树的第一位置之前。
只否定以此第一位置证据直接调用 mono 的办法，不否定第 2 项值比较或 Cover。
来源：YiRWBlock 的第一位置构造子、YiTQChain.shifted-path 与 YiTZLocal.source-chain-one。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTYNoDirect where
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiTZLocal as T
import OCF.Lean.YiTQChain as Q

Dry : (a : B.L) → B.Tr a → Set
Dry a B.zero = ⊤
Dry a (B.suc x) = Dry a x
Dry a (B.lim f s) = ∀ n → Dry a (f n)
Dry a (B.Ω p g) = ⊥
Dry B.zero (B.up x () y e)
Dry (B.nd s h) (B.up x c y e) = Dry (B.nd s h) x × Dry (h c) y

dry-down : ∀ a {x y : B.Tr a} → B._⊢_◃_ a x y → Dry a y → Dry a x
dry-down a B.◃s q = q
dry-down a (B.◃l n) q = q n
dry-down a B.◃w ()
dry-down B.zero (B.◃u _ () _ _) q
dry-down (B.nd s h) (B.◃u _ c _ _) q = proj₁ q
dry-down B.zero (B.◃c _ () _) q
dry-down (B.nd s h) (B.◃c _ c d) q = proj₁ q , dry-down (h c) d (proj₂ q)
dry-down a (B.◃t d e) q = dry-down a d (dry-down a e q)

below-Ω : ∀ a (p : B.Pos a) (g : B.Br a p → B.Tr a) → Dry a (g (B.fromBr a p B.zero))
  → {x : B.Tr a} → B._⊢_◃_ a x (B.Ω p g) → Dry a x
below-Ω a p g q B.◃w = q
below-Ω a p g q (B.◃t d e) = dry-down a d (below-Ω a p g q e)

emb-dry : ∀ {a b} (v : P._⊑_ a b) (o : P.Ok b) (y : O.Tr⁺ a) →
  Dry b (proj₁ (P.emb b o (P.wk v) y)) → Dry a (proj₁ y)
emb-dry P.self o y q = q
emb-dry {b = B.nd s h} (P.inc c v) o y q = emb-dry v (proj₂ o c) y (proj₂ q)
emb-dry {b = B.nd s h} (P.inu vs) o y q = emb-dry (vs (O.c₀ s)) (proj₂ o (O.c₀ s)) y (proj₂ q)

shift : B.Tr B.zero → B.L
shift d = T.two B.⊕ (B.zero B.⊕ (B.zero B.⊕ B.↑ B.zero d))
wet-omega : Dry (shift Q.omega) (proj₁ (O.Ωt (shift Q.omega))) → ⊥
wet-omega q = proj₂ (q 0)
source-wet : Dry Q.shifted-source (proj₁ (O.Ωt Q.shifted-source)) → ⊥
source-wet q = wet-omega (subst (λ a → Dry a (proj₁ (O.Ωt a)))
  (cong shift T.source-chain-one) q)
below-successor : (h : ⊤ → B.L) {x : B.Tr (B.nd B.sS h)} →
  B._⊢_◃_ (B.nd B.sS h) x (proj₁ (O.Ωt (B.nd B.sS h))) → Dry (B.nd B.sS h) x
below-successor h e = below-Ω (B.nd B.sS h) _ _ (tt , tt) e
no-direct : (d : B.Tr B.zero) (o : P.Ok (T.child d))
  (v : P._⊑_ Q.shifted-source (T.child d)) →
  B._⊢_◃_ (T.child d)
    (proj₁ (P.emb (T.child d) o (P.wk v) (O.Ωt Q.shifted-source)))
    (proj₁ (O.Ωt (T.child d))) → ⊥
no-direct d o v e = source-wet (emb-dry v o (O.Ωt Q.shifted-source)
  (below-successor (λ _ → shift d) e))
actual-no-direct :
  B._⊢_◃_ (T.child (T.Canonical.Target.chain 1))
    (proj₁ (P.emb (T.child (T.Canonical.Target.chain 1))
      (T.o-child (T.Canonical.Target.chain 1)) (P.wk Q.Canonical.shifted-path)
      (O.Ωt Q.shifted-source)))
    (proj₁ (O.Ωt (T.child (T.Canonical.Target.chain 1)))) → ⊥
actual-no-direct = no-direct (T.Canonical.Target.chain 1)
  (T.o-child (T.Canonical.Target.chain 1)) Q.Canonical.shifted-path
```
