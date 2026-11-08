# 最后树表示的转换只留在验收

这里证明直接树的 FGH 与转换后的 FGH 逐点相同。新旧 TotalOrbit
表示的序数值读取字面相同；不牵涉旧 forceᴺ 的值，不恢复其证书。

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.TotalOrbitNativeAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
import OCF.Free.Level as L
open import OCF.BTBO using (module Ord-Ord)
import OCF.Free.TotalOrbitBuild as A
import OCF.Free.NativeBrouwer as N
import OCF.Align.TotalOrbitClosed as S
import OCF.Align.TotalOrbitNative as C

iterate-cong : ∀ {f g : ℕ → ℕ} → (∀ n → f n ≡ g n) → ∀ a n → Ord-Ord.iter f a n ≡ N.iterate g a n
iterate-cong h a zero = refl
iterate-cong {g = g} h a (suc n) = trans (h _) (cong g (iterate-cong h a n))

fgh-read : ∀ a n → L.FGH (A.read a) n ≡ N.FGH a n
fgh-read L.zero n = refl
fgh-read (L.suc a) n = iterate-cong (fgh-read a) n n
fgh-read (L.lim f st) n = fgh-read (f n) n

read-closed : A.read C.closed ≡ S.closed
read-closed = refl

fgh-closed : ∀ n → S.fgh n ≡ C.fgh n
fgh-closed n = fgh-read C.closed n
```
