# Ω 高度内全部自然数分量的实际 Safe 混合输入

B=Ω、β=ω；所有自然数分量同在公共界中。这里只加 Pos 证书，
擦除后逐构造子双模拟原 BoundedContextClosed.output，没有换成单分量。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedFoldValueMixed where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldIf using (Pos; Safe; T; G)
open import OCF.Lean.LHRecFl using (flL; Lg-flL)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo; same-sym)
open import OCF.Align.FrozenInnerOuter using (same-refl; same-add)
open import OCF.Align.FrozenOutputModel using (same-trans)
import OCF.Align.BoundedValueUpper as V
import OCF.Lean.BoundedContextClosed as C
import OCF.Lean.BoundedFoldRun as Run

β : Cd
β = hl C.num
S : KS
S = Safe β C.B
F : ℕ → KS
F n = T (up (C.num n))

finite-pos : ∀ n κ → Pos β (up (C.num n)) κ
finite-pos zero κ = tt
finite-pos (suc n) (inj₁ κ) = finite-pos n κ
finite-pos (suc n) (inj₂ _) = tt

put : ∀ n → HB (F n) → HB S
put n hz = hz
put n (hs a) = hs (put n a)
put n (hl f) = hl (λ j → put n (f j))
put n (hΩ κ g) = hΩ ((inj₂ (C.num n) , κ) , (hlim n hself , finite-pos n κ))
  (λ c → put n (g c))

put-position : ∀ n {a b W} → a ⊲[ W (inj₂ (C.num n)) ] b → put n a ⊲[ W ] put n b
put-position n hself = hself
put-position n (hsuc p) = hsuc (put-position n p)
put-position n (hlim j p) = hlim j (put-position n p)
put-position n (hLim b p) = hLim b (put-position n p)

put-legal : ∀ n a → LgB a → LgB (put n a)
put-legal n hz l = tt
put-legal n (hs a) l = put-legal n a l
put-legal n (hl f) (st , l) = (λ j → put-position n (st j)) , (λ j → put-legal n (f j) (l j))
put-legal n (hΩ κ g) (mo , l) =
  (λ lw b b′ p → put-position n (mo (lw (inj₂ (C.num n))) b b′ p)) ,
  (λ lw b → put-legal n (g _) (l (lw (inj₂ (C.num n))) b))

floor : ℕ → HB S
floor n = put n (flL (G (up (C.num n))))
sums : ℕ → HB S
sums zero = floor zero
sums (suc n) = sums n ⊞ floor (suc n)
input : HB S
input = hl sums

legal-floor : ∀ n → LgB (floor n)
legal-floor n = put-legal n _ (Lg-flL _)
legal-sums : ∀ n → LgB (sums n)
legal-sums zero = legal-floor zero
legal-sums (suc n) = Lg-⊞ _ _ (legal-sums n) (legal-floor (suc n))
legal-input : LgB input
legal-input = (λ n → ⊞-fst _ _) , legal-sums

erase : HB S → HB (T C.B)
erase hz = hz
erase (hs a) = hs (erase a)
erase (hl f) = hl (λ n → erase (f n))
erase (hΩ (κ , p) g) = hΩ κ (λ c → erase (g c))
erase-put : ∀ n a → Same (erase (put n a)) (ι (inj₂ (C.num n)) a)
erase-put n hz = zz
erase-put n (hs a) = ss (erase-put n a)
erase-put n (hl f) = ll (λ j → erase-put n (f j))
erase-put n (hΩ κ g) = oo (λ c → erase-put n (g c))
erase-add : ∀ a b → Same (erase (a ⊞ b)) (erase a ⊞ erase b)
erase-add a hz = same-refl _
erase-add a (hs b) = ss (erase-add a b)
erase-add a (hl f) = ll (λ n → erase-add a (f n))
erase-add a (hΩ κ g) = oo (λ c → erase-add a (g c))

erase-floor : ∀ n → Same (erase (floor n)) (C.M.embed (C.M.floor (C.member n)))
erase-floor n = same-trans (erase-put n _) (same-sym (V.component n _))
erase-sums : ∀ n → Same (erase (sums n)) (C.M.embed (C.M.sums C.member n))
erase-sums zero = erase-floor zero
erase-sums (suc n) = same-trans (erase-add (sums n) (floor (suc n)))
  (same-trans (same-add (erase-sums n) (erase-floor (suc n)))
    (same-sym (V.embed-add (C.M.sums C.member n) (C.M.floor (C.member (suc n))))))
erase-input : Same (erase input) C.output
erase-input = ll erase-sums

module Fold = Run.Run β (proj₂ C.legal-w) C.B C.legal-B
output : HB (T hz)
output = Fold.fold hz (z⊲ᴮ C.B) input
```

合法输入已经给出；运行器输出可计算。尚未据此证明 output 合法，
也未把擦除后的 Same 自动当成 fold 同余。
