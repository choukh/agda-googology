# NoΩ 层号的精确对应与路径比较
验收文件；编译定理：Corr 的函数性、槽位严格下降与路径 notBelow。
来源：YiLSRel.Corr 与 YiLSFold.POS/notBelow，按 YiRWBlock 的统一形状重写。
对应的 ℕ 极限要求参照相邻项严格步进；不把下界 Rd 当成精确对应。
ω 孩子上的实填见 YiGCOmega。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGCCorr where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (proj₁; _,_)
open import Relation.Nullary using (¬_)
open import OCF.Lean.YiRWBlock renaming (L to LF)
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiNRHit using (NoΩ; chN)
import OCF.Lean.YiRWOps
import OCF.Align.Level as L
data Corr : L.Ordᴵ → LF → Set where
  cz : Corr L.zero zero
  cs : ∀ {a h} → Corr a (h tt) → Corr (L.suc a) (nd sS h)
  cl : ∀ {g s f} → (∀ n → Corr (g n) (f n)) → (∀ n → g n L.≺ᴵ g (suc n)) → Corr (L.lim g s) (nd sL f)
uniq : ∀ {a b x} → Corr a x → Corr b x → a L.≅ᴵ b
uniq cz cz = L.z≅
uniq (cs c) (cs d) = L.s≅ (uniq c d)
uniq (cl c _) (cl d _) = L.l≅ (λ n → uniq (c n) (d n))
notBelow : ∀ {j a} (w : j ≤ a) → NoΩ a → ∀ {i i′} → Corr i j → Corr i′ a → ¬ (i′ L.≺ᴵ i)
notBelow self ns ci ci′ bl = L.≺ᴵ-irrefl (L.≺ᴵ-respˡ (uniq ci ci′) bl)
notBelow (inc tt w) ns ci (cs c) bl = notBelow w (ns tt) ci c (L.≺ᴵ-trans (L.via (L.≅ᴵ-refl _) L.zero) bl)
notBelow (inc n w) ns ci (cl c st) bl = notBelow w (ns n) ci (c n) (L.≺ᴵ-trans (L.≺-lim (suc n) (st n)) bl)
notBelow (inu ws) ns ci (cs c) bl = notBelow (ws tt) (ns tt) ci c (L.≺ᴵ-trans (L.via (L.≅ᴵ-refl _) L.zero) bl)
notBelow (inu ws) ns ci (cl c st) bl = notBelow (ws zero) (ns zero) ci (c zero) (L.≺ᴵ-trans (L.≺-lim (suc zero) (st zero)) bl)
notBelow (ink w) ()

noΩW : ∀ {j a} → j ≤ a → NoΩ a → NoΩ j
noΩW self ns = ns
noΩW {a = nd s h} (inc c w) ns = noΩW w (chN s h ns c)
noΩW {a = nd s h} (inu ws) ns = noΩW (ws (OCF.Lean.YiRWOps.c₀ s)) (chN s h ns (OCF.Lean.YiRWOps.c₀ s))
noΩW (ink w) ()
mutual
  noΩ-at : ∀ {a} → NoΩ a → (p : Pos a) → NoΩ (at a p)
  noΩ-at {nd s h} ns (inj₂ (c , t)) = noΩ-at⁼ (chN s h ns c) t
  noΩ-at {nd (sΩ k) h} () (inj₁ t)
  noΩ-at⁼ : ∀ {a} → NoΩ a → (t : Pos⁼ a) → NoΩ (proj₁ (sl⁼ a t))
  noΩ-at⁼ ns (inj₁ _) = ns
  noΩ-at⁼ ns (inj₂ p) = noΩ-at ns p
POS : ∀ {m} → NoΩ m → (p : Pos m) → ∀ {j i} → Corr j (at m p) → Corr i m → j L.≺ᴵ i
POS ns (inj₂ (tt , inj₁ tt)) cj (cs c) = L.via (uniq cj c) L.zero
POS ns (inj₂ (tt , inj₂ p)) cj (cs c) = L.≺-suc (POS (ns tt) p cj c)
POS ns (inj₂ (n , inj₁ tt)) cj (cl c st) = L.≺-lim (suc n) (L.≺ᴵ-respˡ (uniq cj (c n)) (st n))
POS ns (inj₂ (n , inj₂ p)) cj (cl c st) = L.≺-lim n (POS (ns n) p cj (c n))
no-zero-one : ¬ (Corr L.zero (nd sS (λ _ → zero)))
no-zero-one ()
```
