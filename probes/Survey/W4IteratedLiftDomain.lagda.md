# 单凭槽覆盖不能推出累计正块的结构证书

第四层。取标准证书的第二塔运行，以实际标准 Ω 为底构造一个 ex 正槽，其余槽仍标准。覆盖成立，但该正槽不属于正块生成类。这个反例只限制结构判据的量化范围。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4IteratedLiftDomain where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl; subst)
import W4Block as W
import W4Fold as F
import W4Ops as O
import W4Path as P
open import WVOne using (𝟏; read)
open import WVTwo using (◃→≼)
open import OCF.Align.Value using (_≼_; ≼-refl)
import B12Terminal as T
import B12ActualSlots as C
import Survey.W4IteratedLiftBlock as B

head : B.Tr → Set
head (W.ex a b nb t e) = ⊥
head _ = ⊤
first : ∀ e a → head (B.wrap e (a O.+ B.base))
first [] a = tt
first (b ∷ e) a = first e (b O.+ a)
next : ∀ e t → head (B.wrap e (W.suc t))
next [] t = tt
next (b ∷ e) t = next e (b O.+ t)
lim : ∀ e f d → head (B.wrap e (W.lim f d))
lim [] f d = tt
lim (b ∷ e) f d = lim e (λ n → b O.+ f n) (λ n → O.+-mono b (d n))
tail : ∀ e b z → head (B.wrap e b) → head (B.wrap e (b O.+ O.ι B.k z))
tail e b W.zero u = u
tail e b (W.suc z) u = next e (b O.+ O.ι B.k z)
tail e b (W.lim f d) u = lim e (λ n → b O.+ O.ι B.k (f n)) (λ n → O.+-mono b (O.ι-mono B.k (d n)))
preserved : ∀ {t} → B.Positive t → ∀ e → head (B.wrap e t)
preserved B.seed e = first e W.zero
preserved (B.join {a} q r) e = preserved r (a ∷ e)
preserved (B.append {a} q z) e = tail e a z (preserved q e)
preserved (B.collect {g} {d} q) e = lim e g d

big : O.Tr⁺ B.k
big = W.ex B.base B.base (proj₂ (O.Ωt B.k)) W.zero tt , W.◃t (proj₂ (O.Ωt B.k)) W.◃e
family : F.Base (W.tw 2)
family .B.k (W.ink W.self) = big
family j _ = O.Ωt j
covered : ∀ j w → C._⊴_ (proj₁ (O.Ωt j)) (proj₁ (family j w))
covered .B.k (W.ink W.self) = inj₂ W.◃e
covered _ (W.ink (W.ink q)) = inj₁ refl
covered _ (W.ink (W.inc c q)) = inj₁ refl
covered _ (W.ink (W.inu q)) = inj₁ refl
covered _ (W.inc c q) = inj₁ refl
covered _ (W.inu q) = inj₁ refl
covered _ W.self = inj₁ refl
floor : ∀ w → 𝟏 ≼ read (proj₁ (family W.zero w))
floor w with covered W.zero w
... | inj₁ e = subst (λ z → 𝟏 ≼ read z) e (≼-refl _)
... | inj₂ d = ◃→≼ d
real = T.makeRun (P.Ok-tw 2) family (O.Ωt W.zero) floor (covered _) (≼-refl _)
valid : C.Covered real
valid = covered
counter : B.Positive (proj₁ (T.Run.bs real B.k (W.ink W.self))) → ⊥
counter q = preserved q []
```
