# 所有原生高度的相干世界证书及实际地板

Good只要求seed世界域的步进与单调；高阶坐标递归要求同一Good，
零层Cd坐标仍要求原LgB。下面直接给全部实际原生地板实例。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeReadyGood where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (lz; ls)
open import OCF.Lean.LHRecLay using (_⊕L_; upL)
open import OCF.Lean.LHRecFl using (flL; ΣF; up-⊲; ι-⊲)
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Align.BoundedNativeZeroWorld using (seed)
import OCF.Align.BoundedNativeTerminalReady as T

Good : ∀ c → HB (Native c) → Set
Coord : ∀ c κ → E (Native c) κ → Set
Good c hz = ⊤
Good c (hs a) = Good c a
Good c (hl f) =
  (∀ {v} → LgW (Native hz) v → ∀ n → f n ⊲[ seed c v ] f (suc n)) ×
  (∀ n → Good c (f n))
Good c (hΩ κ g) =
  (∀ {v e d} → LgW (Native hz) v → Bd (Native c) κ e (seed c v) →
    Bd (Native c) κ d (seed c v) → Pr (Native c) κ (seed c v) e d →
    g e ⊲[ seed c v ] g d) ×
  (∀ e → Coord c κ e → Good c (g e))
Coord hz (inj₁ ()) e
Coord hz (inj₂ _) e = LgB e
Coord (hs c) (inj₁ κ) e = Coord c κ e
Coord (hs c) (inj₂ _) e = Good c e
Coord (hl f) (n , κ) e = Coord (f n) κ e

add-good : ∀ c (a b : HB (Native c)) → Good c a → Good c b → Good c (a ⊞ b)
add-good c a hz la lb = la
add-good c a (hs b) la lb = add-good c a b la lb
add-good c a (hl f) la (st , l) =
  (λ lv n → ⊞-⊲ a (st lv n)) , (λ n → add-good c a (f n) la (l n))
add-good c a (hΩ κ g) la (mo , l) =
  (λ lv e d p → ⊞-⊲ a (mo lv e d p)) , (λ e le → add-good c a (g e) la (l e le))

up-good : ∀ c (a : HB (Native c)) → Good c a → Good (hs c) (up a)
up-good c hz l = tt
up-good c (hs a) l = up-good c a l
up-good c (hl f) (st , l) =
  (λ lv n → up-⊲ (st lv n)) , (λ n → up-good c (f n) (l n))
up-good c (hΩ κ g) (mo , l) =
  (λ lv e d p → up-⊲ (mo lv e d p)) , (λ e le → up-good c (g e) (l e le))

inject-good : ∀ f n (a : HB (Native (f n))) → Good (f n) a → Good (hl f) (ι n a)
inject-good f n hz l = tt
inject-good f n (hs a) l = inject-good f n a l
inject-good f n (hl g) (st , l) =
  (λ lv j → ι-⊲ (st lv j)) , (λ j → inject-good f n (g j) (l j))
inject-good f n (hΩ κ g) (mo , l) =
  (λ lv e d p → ι-⊲ (mo lv e d p)) , (λ e le → inject-good f n (g e) (l e le))

pure-good : ∀ (a : Cd) → LgB a → Good hz (up a)
pure-good hz l = tt
pure-good (hs a) l = pure-good a l
pure-good (hl f) (st , l) =
  (λ lv n → up-⊲ (st n)) , (λ n → pure-good (f n) (l n))

floor-good : ∀ c → Good c (flL (ls lz ⊕L upL lz c))
sums-good : ∀ f n → Good (hl f) (ΣF (λ j → ls lz ⊕L upL lz (f j)) n)
floor-good hz = (λ lv e d p → up-⊲ p) , pure-good
floor-good (hs c) = (λ lv e d p → up-⊲ p) , up-good c
floor-good (hl f) = (λ lv n → ⊞-fst _ _) , sums-good f
sums-good f zero = inject-good f 0 _ (floor-good (f 0))
sums-good f (suc n) = add-good (hl f) _ _ (sums-good f n)
  (inject-good f (suc n) _ (floor-good (f (suc n))))

ready : ∀ (h : HB (Native hz)) → Good hz h → ∀ b → LgB b → T.Ready b h
ready hz l b lb = tt
ready (hs h) l b lb = ready h l b lb
ready (hl f) (st , l) b lb = (λ n → st (tt , lb) n) , (λ n → ready (f n) (l n) b lb)
ready (hΩ (inj₁ ()) g) l b lb
ready (hΩ (inj₂ _) g) (mo , l) b lb =
  (λ bc bd p → mo (tt , lb) bc bd p) ,
  (λ c bc → ready (g c) (l c (lgB⊲ bc tt lb)) b lb) ,
  (λ c lc → ready (g c) (l c lc) c lc)
```

floor-good对任意Cd层给实际flL的证书，不限于有限自然数层。ready把零层
Good转成末段实际采样所需证书；仍须证明原生fold把这些Good输入送成Good，
以及θ累加的固定分量混合版本。本文没有宣称原countable-output已合法。
