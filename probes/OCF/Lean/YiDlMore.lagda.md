# 新派发逐点保留得不少于 `dfin`

非验收文件. 编译定理, 无前提: `more : ∀ k K r → IsKeep (dfin k K r) → IsKeep (dl k K r)`. 办法: `dfin` 保留时目标层字面是 `fin n`, 源层号字面是 `fin m` 且 `m < n`; 这时燃料 `m` 的搜索在 `fin n` 里找得到 (`YiLamNFuel.look-fin`). 不陈述值 ("保留得多, 值不降" 的后半没有证).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDlMore where

open import Data.Nat.Base using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (≤-refl; m<n⇒m<1+n)
open import Data.Unit.Base using (⊤; tt)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (lev; Way; keep; fold; Ext)
open import OCF.Lean.YiLamFold using (fin; eqFin; slotFin; finOf; dfin₀; dfin)
open import OCF.Lean.YiLamNFuel using (IsJust; pol; byFin; byLook; look-fin; finOf-fin; byLook-j)
open import OCF.Lean.YiUniIf using (IsKeep)
open import OCF.Lean.YiDlFold using (dl)
```

```agda
slotFin-fin : ∀ n L → IsJust (slotFin n L) → Σ ℕ λ m → (fin m ≡ L) × (m < n)
slotFin-fin zero L ()
slotFin-fin (suc n) L h with eqFin n L
... | just e = n , e , ≤-refl
... | nothing with slotFin n L | slotFin-fin n L
...   | just _ | rec with rec tt
...     | m , e , p = m , e , m<n⇒m<1+n p

dfin₀-keep : ∀ n K r → IsKeep (dfin₀ n K r) → IsJust (slotFin n (lev K r))
dfin₀-keep n K r with slotFin n (lev K r)
... | just _ = λ _ → tt
... | nothing = λ ()

keep-subst : ∀ {a b j : LF} (e : a ≡ b) (w : Way a j) → IsKeep (subst (λ t → Way t j) e w) → IsKeep w
keep-subst refl w h = h

dfin-keep : ∀ k K r → IsKeep (dfin k K r) → Σ ℕ λ n → (fin n ≡ k) × IsJust (slotFin n (lev K r))
dfin-keep k K r with finOf k
... | just (n , e) = λ h → n , e , dfin₀-keep n K r (keep-subst e (dfin₀ n K r) h)
... | nothing = λ ()

pol-keep : ∀ N L m → fin m ≡ L → m < N → IsKeep (pol (λ n → n) (fin N) L)
pol-keep N .(fin m) m refl p = subst (λ mb → IsKeep (byFin (λ n → n) (fin N) (fin m) mb)) (sym (finOf-fin m))
  (byLook-j (fin N) (fin m) m refl _ (look-fin m N m p))

more : ∀ k K r → IsKeep (dfin k K r) → IsKeep (dl k K r)
more k K r h with dfin-keep k K r h
... | zero , refl , ()
... | suc n , refl , j with slotFin-fin (suc n) (lev K r) j
...   | m , e , p = pol-keep (suc n) (lev K r) m e p
```
