# 当前带码域不封闭于上折
编译否定（字面读回）：规范的第 1 层 Ω 树上折到第 2 层后，不是任何 Read 码在第 2 层的解释。
输入与输出均是合法闭项；差别是根槽位深度，否定只针对 YiBSRead 这份小文法。
不否定序数值互相支配，也不否定加入结点或上折码的 V149 变体。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBSUpNeg where
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiBSRead
one two : L
one = nd sS (λ _ → zero)
two = nd sS (λ _ → one)
slot : Pos two → Bool
slot (inj₁ ())
slot (inj₂ (tt , inj₁ _)) = false
slot (inj₂ (tt , inj₂ _)) = true
mark : Tr two → Bool
mark zero = false
mark (suc x) = false
mark (lim f a) = false
mark (Ω p g) = slot p
mark (up x c y e) = false
mark-plus : (x y : Tr two) → mark x ≡ false → mark y ≡ false → mark (x + y) ≡ false
mark-plus x zero hx hy = hx
mark-plus x (suc y) hx hy = refl
mark-plus x (lim f a) hx hy = refl
mark-plus x (Ω p g) hx hy = hy
mark-plus x (up y c w e) hx hy = refl
mark-read : (d : Read) → mark (proj₁ (read two d)) ≡ false
mark-read omega = refl
mark-read (next d) = refl
mark-read (plus d e) = mark-plus (proj₁ (read two d)) (proj₁ (read two e)) (mark-read d) (mark-read e)
mark-read (limit f) = refl
lifted : Tr⁺ two
lifted = Up one (down stop tt) (Ωt two) (proj₁ (read one omega))
lifted-mark : mark (proj₁ lifted) ≡ true
lifted-mark = refl
no-up-code : (d : Read) → proj₁ (read two d) ≡ proj₁ lifted → ⊥
no-up-code d eq with trans (sym (mark-read d)) (cong mark eq)
... | ()
```
