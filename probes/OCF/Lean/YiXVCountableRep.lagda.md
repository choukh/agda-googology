# YiXVCountableRep
> 验收文件。档位：编译定理。父层号字面相等时，原限制代表字面相等；回搬保持后继并在 Ω 起点上同值。
> 推广 YiXVFiniteFamily/Level 的结构递归；共享映射证明供搬运与加法复用。未证明可数层折叠闭包或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableRep where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
import OCF.Align.Level as L
import OCF.Lean.YiXVLiteralSim as M

plus : ∀ {i a b} (q : i L.<ᴵ a) (e : a L.≅ᴵ b) → a ≡ b → i ≡ L.Restr.rep (L.res q e)
plus L.zero (L.s≅ e) same = cong M.pred same
plus (L.suc q) (L.s≅ e) same = plus q e (cong M.pred same)
plus (L.lim n q) (L.l≅ h) same = plus q (h n) (cong (λ a → M.at a n) same)
minus : ∀ {i a b} (q : i L.<ᴵ b) (e : a L.≅ᴵ b) → a ≡ b → i ≡ L.Restr.rep (L.res⁻ q e)
minus L.zero (L.s≅ e) same = sym (cong M.pred same)
minus (L.suc q) (L.s≅ e) same = minus q e (cong M.pred same)
minus (L.lim n q) (L.l≅ h) same = minus q (h n) (cong (λ a → M.at a n) same)
plus-suc : ∀ {i a b} (q : i L.<ᴵ a) (e : a L.≅ᴵ b) X →
  L.Restr.back (L.res q e) (L.suc X) ≡ L.suc (L.Restr.back (L.res q e) X)
plus-suc L.zero (L.s≅ e) X = refl
plus-suc (L.suc q) (L.s≅ e) X = plus-suc q e X
plus-suc (L.lim n q) (L.l≅ h) X = plus-suc q (h n) X
minus-suc : ∀ {i a b} (q : i L.<ᴵ b) (e : a L.≅ᴵ b) X →
  L.Restr.back (L.res⁻ q e) (L.suc X) ≡ L.suc (L.Restr.back (L.res⁻ q e) X)
minus-suc L.zero (L.s≅ e) X = refl
minus-suc (L.suc q) (L.s≅ e) X = minus-suc q e X
minus-suc (L.lim n q) (L.l≅ h) X = minus-suc q (h n) X
plus-Ω : ∀ {i a b} (q : i L.<ᴵ a) (e : a L.≅ᴵ b) → L.Restr.back (L.res q e) (L.Ω (L.Restr.rep (L.res q e))) L.≅ L.Ω i
plus-Ω L.zero (L.s≅ e) = L.tr⁻-≅ e (L.Ω-≅ (L.≅ᴵ-sym e))
plus-Ω (L.suc q) (L.s≅ e) = plus-Ω q e
plus-Ω (L.lim n q) (L.l≅ h) = plus-Ω q (h n)
minus-Ω : ∀ {i a b} (q : i L.<ᴵ b) (e : a L.≅ᴵ b) → L.Restr.back (L.res⁻ q e) (L.Ω (L.Restr.rep (L.res⁻ q e))) L.≅ L.Ω i
minus-Ω L.zero (L.s≅ e) = L.tr-≅ e (L.Ω-≅ e)
minus-Ω (L.suc q) (L.s≅ e) = minus-Ω q e
minus-Ω (L.lim n q) (L.l≅ h) = minus-Ω q (h n)
```
