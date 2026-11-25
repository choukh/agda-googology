# YiXVFiniteTransportShape
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteTransportShape where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteCoerce as C
import OCF.Lean.YiXVFiniteBridge as E

data Dir : Set where
  fwd bwd : Dir
op : Dir → Dir
op fwd = bwd
op bwd = fwd
raw : (d : Dir) (i : L.Ordᴵ) → L.Ordᶜ i → L.Ordᶜ i
raw fwd i = L.tr (L.≅ᴵ-refl i)
raw bwd i = L.tr⁻ (L.≅ᴵ-refl i)
τ : ∀ d n → I.T n → I.T n
τ d n = raw d (L.natᴵ n)
pull : ∀ d {i ℓ} (q : i L.<ᴵ ℓ) → L.U i (L.<→◃ q) → L.U i (L.<→◃ q)
pull d {i} q u = L.into (L.<→◃ q) (raw (op d) i (L.out (L.<→◃ q) u))

z : ∀ d n → τ d n L.zero ≡ L.zero
z fwd n = refl
z bwd n = refl
o : ∀ d n → τ d n (L.suc L.zero) ≡ L.suc L.zero
o fwd n = refl
o bwd n = refl
s : ∀ d n X → τ d n (L.suc X) ≡ L.suc (τ d n X)
s fwd n X = refl
s bwd n X = refl
l : ∀ d n (a : ℕ → I.T n) → τ d n (L.lim a) ≡ L.lim (λ k → τ d n (a k))
l fwd n a = refl
l bwd n a = refl
u : ∀ d n X → τ d (suc n) (L.up L.zero X) ≡ L.up L.zero (τ d n X)
u fwd n X = refl
u bwd n X = refl
node : ∀ d n {i} (q : i L.<ᴵ L.natᴵ n) (a : L.U i (L.<→◃ q) → I.T n) →
  τ d n (L.limᵢ q a) ≡ L.limᵢ q (λ x → τ d n (a (pull d q x)))
node fwd n q a rewrite C.res-self n q = refl
node bwd n q a rewrite C.res⁻-self n q = refl

pull-next : ∀ d {i ℓ} (q : i L.<ᴵ ℓ) (x : L.U i (L.<→◃ q)) → pull d q (C.next q x) ≡ C.next q (pull d q x)
pull-next fwd {i} q x = trans
  (cong (λ y → L.into (L.<→◃ q) (L.tr⁻ (L.≅ᴵ-refl i) y)) (L.out-into (L.<→◃ q) (L.suc (L.out (L.<→◃ q) x))))
  (sym (cong (λ y → L.into (L.<→◃ q) (L.suc y)) (L.out-into (L.<→◃ q) (L.tr⁻ (L.≅ᴵ-refl i) (L.out (L.<→◃ q) x)))))
pull-next bwd {i} q x = trans
  (cong (λ y → L.into (L.<→◃ q) (L.tr (L.≅ᴵ-refl i) y)) (L.out-into (L.<→◃ q) (L.suc (L.out (L.<→◃ q) x))))
  (sym (cong (λ y → L.into (L.<→◃ q) (L.suc y)) (L.out-into (L.<→◃ q) (L.tr (L.≅ᴵ-refl i) (L.out (L.<→◃ q) x)))))

ref-pull : ∀ d n {i} (q : i L.<ᴵ L.natᴵ (suc n)) x →
  I.Uref n q (pull d q x) ≡ τ (op d) (E.num n q) (I.Uref n q x)
ref-pull fwd n {i} q x = trans
  (cong (subst L.Ordᶜ (E.eq n q)) (L.out-into (L.<→◃ q) (L.tr⁻ (L.≅ᴵ-refl i) (L.out (L.<→◃ q) x))))
  (C.cast-tr⁻ (E.eq n q) (L.out (L.<→◃ q) x))
ref-pull bwd n {i} q x = trans
  (cong (subst L.Ordᶜ (E.eq n q)) (L.out-into (L.<→◃ q) (L.tr (L.≅ᴵ-refl i) (L.out (L.<→◃ q) x))))
  (C.cast-tr (E.eq n q) (L.out (L.<→◃ q) x))
```
