# K1′：全原守卫域的有限次 Ω 正则性

这里先交 Reg 的全域部分，不用 LglB 缩小量词。
归纳包只保存次数以内的结果，非零次数内部按第 0 层 Raw 的结构递归。
它调用 Base 的同一个读回定理，不按塔的具体层号枚举槽位。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiK1bReg where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import OCF.Align.LevelFixCore as F
open F using (module G)
import OCF.Align.LevelFixVal as V
open import OCF.Align.YiRegBase using (Reg)
open import OCF.Align.YiDispBase using (Below; one; e-branch)
import OCF.Align.YiK1 as K
import OCF.Align.RR4RegOmega2 as R
open import OCF.Align.YiK1bBase

coordinate-suc-root : ∀ η → F.Gd F.zero (V.cO F.zero) η →
  Below (F.suc (V.up F.zero η)) (V.Ω̂ (V.up F.zero η))
coordinate-suc-root η e = R.below-cp
  (one (e-branch (G.suc η) (inj₂ (proj₁ e) , proj₂ e)))
  (V.Ω̂-CP (V.cp→CP F.zero (proj₁ e)))

one-to-pow : ∀ n → V.CP (F.suc F.zero) (pow n (F.suc F.zero))
one-to-pow zero = V.self
one-to-pow (suc n) = V.CP-tr (one-to-pow n) (pow-cp n (V.fst V.self))

Stage : ℕ → Set
Stage n = Regs (suc n) F.zero ×
  (∀ η → F.Gd F.zero (V.cO F.zero) η → Regs n (V.up F.zero η))

stage-step : ∀ n → Stage n → Stage (suc n)
stage-step n (r , old) = (r , rn) , coordinates
  where
  rn : Reg (pow (suc (suc n)) F.zero)
  rn = pow-node-reg n F.zero R.raw1 (F.suc F.zero)
    (λ η e → V.up F.zero η) (cp-weak (one-to-pow n)) tt
    (regs-last (suc n) F.zero r)
    (λ η e → regs-last n (V.up F.zero η) (old η e))

  under-one : ∀ a → F.Cp F.zero a R.raw1 → Reg (pow (suc n) (V.up F.zero a))
  under-one a (inj₁ refl) = rn
  under-one a (inj₂ (inj₁ refl)) = regs-last (suc n) F.zero r
  under-one a (inj₂ (inj₂ ()))

  go : ∀ η → F.Lgl F.zero η → F.Cp F.zero R.raw1 η →
    Reg (pow (suc n) (V.up F.zero η))
  go G.zero l (inj₁ ())
  go G.zero l (inj₂ ())
  go (G.suc a) l (inj₁ refl) = rn
  go (G.suc a) l (inj₂ q) =
    pow-node-reg n (V.up F.zero a) (V.cO (V.up F.zero a))
      (V.Ω̂ (V.up F.zero a)) (λ ζ d → V.up (V.up F.zero a) ζ)
      (inj₂ (root-pow n (V.up F.zero a) pa)) (R.read0-reg a) (go a l q)
      (λ ζ d → regs-last n (V.up (V.up F.zero a) ζ)
        (read-regs n (V.up F.zero a) pa ra ζ d))
    where
    ea : F.Gd F.zero (V.cO F.zero) a
    ea = q , l
    pa : Below (F.suc (V.up F.zero a)) (V.Ω̂ (V.up F.zero a))
    pa = coordinate-suc-root a ea
    ra : Regs (suc n) (V.up F.zero a)
    ra = old a ea , go a l q
  go (G.lim f) (st , lf) (inj₁ ())
  go (G.lim f) (st , lf) (inj₂ (m , q)) =
    pow-lim-reg (suc n) (λ j → V.up F.zero (f j)) term
    where
    term : ∀ j → Reg (pow (suc n) (V.up F.zero (f j)))
    term j with F.cmpC F.zero (f (j + m))
      (subst (λ z → F.Cp F.zero (f j) (f z)) (+-comm m j) (K.up-to F.zero f st m j))
      (F.Cp-tr F.zero q (K.up-to F.zero f st j m)) (lf (j + m))
    ... | inj₁ below-one = under-one (f j) below-one
    ... | inj₂ above-one = go (f j) (lf j) above-one
  go (G.lc () c t g) l q
  go (G.em () a) l q
  go G.top l (inj₁ ())
  go G.top l (inj₂ ())

  coordinates : ∀ η → F.Gd F.zero (V.cO F.zero) η →
    Regs (suc n) (V.up F.zero η)
  coordinates η e = old η e , go η (proj₂ e) (proj₁ e)

stages : ∀ n → Stage n
stages zero = (tt , tt) , (λ η e → R.read0-reg η)
stages (suc n) = stage-step n (stages n)

pow-zero-reg : ∀ n → Reg (pow n F.zero)
pow-zero-reg n = regs-last n F.zero (proj₁ (proj₁ (stages n)))

tower-reg : ∀ n → Reg (V.tw n)
tower-reg n = subst Reg (pow-tw n) (pow-zero-reg n)

limit-reg : Reg V.Λ
limit-reg = tower-reg
```
