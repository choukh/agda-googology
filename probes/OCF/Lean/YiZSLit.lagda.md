# `StepS` 在 η = ω+n+1 一段成立 (原前提形状)

> 验收文件 (读记号), 不进成品. 判决: 编译定理, 无前提. `StepS-ωn`: `YiSVRed.Red.StepS` 在 η = `νᵀ (suc n)` (即 ω+n+1) 处对一切 n, x 成立; `StepS-ω2`: 前提 `M⁰ (νᵀ n) x` 下结论对一切 η ≤ ω·2 成立.
> 做法: 第 0 层的树要么是字面自然数, 要么字面含每个 `nat n` (`dec`, 树侧, 不读记号); 字面自然数 `nat k` 只承载自然数项 (`sound`, 记号一侧), 所以承载 ω+n 的 x 不是字面自然数, 再用 [YiZSTower](YiZSTower.lagda.md) 的 `seg`.
> 不给出什么: η = ω·2+1 起没有做 (`pred η` = ω·2 时 x 的字面形状不由 `dec` 一类的判定给出); `StepS` 整体未证, 没有否定.
> 来源: 新写; `pos⁰` 一类对第 0 层树的递归见 `YiHCRel`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiZSLit where
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; n≤1+n; m≤n⇒m≤1+n; m≤n⇒m<n∨m≡n; 1+n≰n)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (∷-injectiveˡ; ∷-injectiveʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiHCRel using (Mᴴ; mz; m1; mL; mΩ; mU; mw; mc; M⁰)
import OCF.Align.EboLeanDef as E
open E using (cof; c0; c1; cω; cΩ; pred; fsn; fsT; γT; natT; sucT; cmpᵀ; lt; eq; gt; _<ᵀ_; _<ᴾ_; []<; hd<; tl<; lv<; ar<)
open import OCF.Align.EBO using (pred-suc)
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Lean.YiANFam using (pred-nat)
open import OCF.Lean.YiDCRel using (suc-nat)
open import OCF.Lean.YiCLPhi using (ωᵀ; rep1)
open import OCF.Lean.YiTBRow using (nat)
open import OCF.Lean.YiSVMono
open import OCF.Lean.YiSVOmega
open import OCF.Lean.YiSVRed using (Qη; module Red)
open import OCF.Lean.YiZSTower
```

## 树侧: 第 0 层的树与字面自然数

```agda
sinj : ∀ {x y : Tr zero} → _≡_ {A = Tr zero} (suc x) (suc y) → x ≡ y
sinj refl = refl

◃nat : ∀ {x y : Tr zero} → zero ⊢ x ◃ y → ∀ k → y ≡ nat k → Σ ℕ λ k′ → (x ≡ nat k′) × (suc k′ ≤ⁿ k)
◃nat ◃s            zero    ()
◃nat ◃s            (suc k) e = k , sinj e , ≤-refl
◃nat (◃l n)        zero    ()
◃nat (◃l n)        (suc k) ()
◃nat (◃w {p = ()}) k e
◃nat (◃u x () y _) k e
◃nat (◃c x () _)   k e
◃nat (◃t d d′)     k e with ◃nat d′ k e
... | k′ , e′ , le with ◃nat d k′ e′
... | k″ , e″ , le′ = k″ , e″ , ≤-trans le′ (≤-trans (n≤1+n k′) le)

chainlen : (f : ℕ → Tr zero) → ((n : ℕ) → zero ⊢ f n ◃ f (suc n)) → ∀ m k → f m ≡ nat k → m ≤ⁿ k
chainlen f a zero    k e = z≤n
chainlen f a (suc m) k e with ◃nat (a m) k e
... | k′ , e′ , le = ≤-trans (s≤s (chainlen f a m k′ e′)) le

z⊴ : (x : Tr zero) → zero ⊴ x
z⊴ x with zl x
... | inj₁ refl = ⊴r
... | inj₂ d    = ⊴◃ d

dec : ∀ n (x : Tr zero) → (Σ ℕ λ k → (x ≡ nat k) × (suc k ≤ⁿ n)) ⊎ (nat n ⊴ x)
dec zero    x    = inj₂ (z⊴ x)
dec (suc n) zero = inj₁ (0 , refl , s≤s z≤n)
dec (suc n) (suc y) with dec (suc n) y
... | inj₂ v = inj₂ (⊴-trans v (⊴◃ ◃s))
... | inj₁ (k , e , s≤s le) with m≤n⇒m<n∨m≡n le
...   | inj₁ l    = inj₁ (suc k , cong suc e , s≤s l)
...   | inj₂ refl = inj₂ (subst (λ z → nat (suc k) ⊴ suc z) (sym e) ⊴r)
dec (suc n) (lim f a) with dec (suc n) (f (suc n))
... | inj₂ v = inj₂ (⊴-trans v (⊴◃ (◃l (suc n))))
... | inj₁ (k , e , le) = ⊥-elim (1+n≰n (≤-trans le (chainlen f a (suc n) k e)))
dec (suc n) (Ω () _)
dec (suc n) (up _ () _ _)
```

## 记号一侧: 字面自然数只承载自然数项

`lim-big`: 共尾 ω 的项的第 k+1 个基本列项不是 ≤ k 的自然数项 (各子句照 `fsn` 的定义分情况; 哑值子句由共尾度的前提排除).

```agda
argP lvP : E.PT → E.T
argP (E.ψ u a) = a
lvP  (E.ψ u a) = u

¬<𝟏 : ∀ {x} → x <ᴾ E.𝟏 → ⊥
¬<𝟏 (lv< ())
¬<𝟏 (ar< ())

natT-below : ∀ {s} i → s <ᵀ natT i → Σ ℕ λ i′ → (s ≡ natT i′) × (suc i′ ≤ⁿ i)
natT-below zero    ()
natT-below (suc i) []<     = 0 , refl , s≤s z≤n
natT-below (suc i) (hd< p) = ⊥-elim (¬<𝟏 p)
natT-below (suc i) (tl< p) with natT-below i p
... | i′ , e , le = suc i′ , cong (E.𝟏 ∷_) e , s≤s le

rep-len : ∀ k (q : E.PT) i → replicate k q ≡ natT i → k ≡ i
rep-len zero    q zero    e  = refl
rep-len zero    q (suc i) ()
rep-len (suc k) q zero    ()
rep-len (suc k) q (suc i) e  = cong suc (rep-len k q i (∷-injectiveʳ e))

cofA≢c0 : ∀ u c → E.cofA u c ≡ c0 → ⊥
cofA≢c0 u c0     ()
cofA≢c0 u c1     ()
cofA≢c0 u cω     ()
cofA≢c0 u (cΩ μ) e with cmpᵀ (sucT μ) u
cofA≢c0 u (cΩ μ) () | lt
cofA≢c0 u (cΩ μ) () | eq
cofA≢c0 u (cΩ μ) () | gt

cofψ0≢c0 : ∀ u c → (c ≡ c0 → ⊥) → E.cofψ0 u c ≡ c0 → ⊥
cofψ0≢c0 u c0     nz e  = nz refl
cofψ0≢c0 u c1     nz ()
cofψ0≢c0 u cω     nz ()
cofψ0≢c0 u (cΩ μ) nz ()

cof≢c0 : ∀ x xs → cof (x ∷ xs) ≡ c0 → ⊥
cof≢c0 x (y ∷ ys) e = cof≢c0 y ys e
cof≢c0 (E.ψ u (y ∷ ys)) [] e = cofA≢c0 u (cof (y ∷ ys)) e
cof≢c0 (E.ψ (w ∷ ws) []) [] e = cofψ0≢c0 (w ∷ ws) (cof (w ∷ ws)) (cof≢c0 w ws) e
cof≢c0 (E.ψ [] []) [] ()

fsTc≢ : ∀ u b ν m η → E.fsTc u b ν m η ≡ [] → ⊥
fsTc≢ u b ν lt η ()
fsTc≢ u b ν eq η ()
fsTc≢ u b ν gt η ()

fsT₊≢ : ∀ u b c η → E.fsT₊ u b c η ≡ [] → ⊥
fsT₊≢ u b c0     η ()
fsT₊≢ u b c1     η ()
fsT₊≢ u b cω     η ()
fsT₊≢ u b (cΩ ν) η e = fsTc≢ u b ν (cmpᵀ (sucT ν) u) η e

fsT0≢ : ∀ u c p ps → E.fsT0 u c (p ∷ ps) ≡ [] → ⊥
fsT0≢ u c0     p ps ()
fsT0≢ u c1     p ps ()
fsT0≢ u cω     p ps ()
fsT0≢ u (cΩ ν) p ps ()

fsT≢ : ∀ b {ν} → cof b ≡ cΩ ν → ∀ p ps → fsT b (p ∷ ps) ≡ [] → ⊥
fsT≢ []                        () p ps q
fsT≢ (x ∷ y ∷ ys)              e  p ps ()
fsT≢ (E.ψ u (y ∷ ys) ∷ [])     e  p ps q = fsT₊≢ u (y ∷ ys) (cof (y ∷ ys)) (p ∷ ps) q
fsT≢ (E.ψ (w ∷ ws) [] ∷ [])    e  p ps q = fsT0≢ (w ∷ ws) (cof (w ∷ ws)) p ps q
fsT≢ (E.ψ [] [] ∷ [])          () p ps q

Big : E.T → Set
Big t = cof t ≡ cω → ∀ k i → fsn t (suc k) ≡ natT i → suc k ≤ⁿ i

bigc : ∀ u b ν m → cof b ≡ cΩ ν → E.cofψ₊ u ν m ≡ cω → ∀ k i → E.fsnc u b ν m (suc k) ≡ natT i → suc k ≤ⁿ i
bigc u b ν lt eb ()
bigc u b ν eq eb ()
bigc u b ν gt eb e k zero          ()
bigc u b ν gt eb e k (suc zero)    q = ⊥-elim (fsT≢ b eb _ _ (cong argP (∷-injectiveˡ q)))
bigc u b ν gt eb e k (suc (suc i)) q with ∷-injectiveʳ q
... | ()

big₊ : ∀ u b c → cof b ≡ c → (cof b ≡ c0 → ⊥) → Big b → E.cofA u c ≡ cω → ∀ k i → E.fsn₊ u b c (suc k) ≡ natT i → suc k ≤ⁿ i
big₊ u b c0     eb nz ih e k i q = ⊥-elim (nz eb)
big₊ u b c1     eb nz ih e k i q = ≤-reflexive (rep-len (suc k) _ i q)
big₊ u b cω     eb nz ih e k zero          ()
big₊ u b cω     eb nz ih e k (suc zero)    q = ⊥-elim (1+n≰n (≤-trans (s≤s z≤n) (≤-trans (ih eb k 0 (cong argP (∷-injectiveˡ q))) z≤n)))
big₊ u b cω     eb nz ih e k (suc (suc i)) q with ∷-injectiveʳ q
... | ()
big₊ u b (cΩ ν) eb nz ih e k i q = bigc u b ν (cmpᵀ (sucT ν) u) eb e k i q

big0 : ∀ u c → cof u ≡ c → Big u → E.cofψ0 u c ≡ cω → ∀ k i → E.fsn0 u c (suc k) ≡ natT i → suc k ≤ⁿ i
big0 u c0     eu ih ()
big0 u c1     eu ih ()
big0 u (cΩ μ) eu ih ()
big0 u cω     eu ih e k zero          ()
big0 u cω     eu ih e k (suc zero)    q = ⊥-elim (1+n≰n (≤-trans (s≤s z≤n) (≤-trans (ih eu k 0 (cong lvP (∷-injectiveˡ q))) z≤n)))
big0 u cω     eu ih e k (suc (suc i)) q with ∷-injectiveʳ q
... | ()

lim-big : ∀ t → Big t
lim-big []                     ()
lim-big (x ∷ y ∷ ys)           e k zero    ()
lim-big (x ∷ y ∷ ys)           e k (suc i) q = m≤n⇒m≤1+n (lim-big (y ∷ ys) e k i (∷-injectiveʳ q))
lim-big (E.ψ u (y ∷ ys) ∷ [])  e k i q = big₊ u (y ∷ ys) (cof (y ∷ ys)) refl (cof≢c0 y ys) (lim-big (y ∷ ys)) e k i q
lim-big (E.ψ (w ∷ ws) [] ∷ []) e k i q = big0 (w ∷ ws) (cof (w ∷ ws)) refl (lim-big (w ∷ ws)) e k i q
lim-big (E.ψ [] [] ∷ [])       ()

sound : ∀ {t x} → M⁰ t x → ∀ k → x ≡ nat k → Σ ℕ λ i → (t ≡ natT i) × (i ≤ⁿ k)
sound mz k e = 0 , refl , z≤n
sound (m1 c r) zero ()
sound (m1 {t = t} c r) (suc k) e with sound r k (sinj e)
... | i , q , le = suc i , trans (sym (pred-suc t c)) (trans (cong sucT q) (suc-nat i)) , s≤s le
sound (mL {t = t} c h) k e with sound (h (suc k)) k e
... | i , q , le = ⊥-elim (1+n≰n (≤-trans (lim-big t c k i q) le))
sound (mΩ {p = ()} _ _ _) k e
sound (mU {c = ()} _ _) k e
sound (mw m d) k e with ◃nat d k e
... | k′ , e′ , le with sound m k′ e′
... | i , q , le′ = i , q , ≤-trans le′ (≤-trans (n≤1+n k′) le)
sound (mc (inj₂ refl) m) k e = sound m k e
sound (mc (inj₁ l) m) k e with sound m k e
... | i , refl , le with natT-below i l
... | i′ , q′ , le″ = i′ , q′ , ≤-trans (≤-trans (n≤1+n i′) le″) le

ν≢nat : ∀ n i → νᵀ n ≡ natT i → ⊥
ν≢nat n zero    ()
ν≢nat n (suc i) ()

no-nat : ∀ n k → M⁰ (νᵀ n) (nat k) → ⊥
no-nat n k m with sound m k refl
... | i , q , _ = ν≢nat n i q
```

## `StepS` 的这一段

```agda
module Seg (oc : (k : ℕ) → Ok (G k)) where
  open Base oc

  lit : ∀ n N {x} → M⁰ (νᵀ n) x → nat (suc N) ⊴ suc x
  lit n N {x} m with dec (suc N) (suc x)
  ... | inj₂ v = v
  ... | inj₁ (zero , () , le)
  ... | inj₁ (suc k , e , le) = ⊥-elim (no-nat n k (subst (M⁰ (νᵀ n)) (sinj e) m))

  StepS-fin : ∀ n N {η x} → η ≤ᵀ νᵀ (suc N) → M⁰ (νᵀ n) x → R.Car (Qη η) (↑ zero (suc x))
  StepS-fin n N le m = seg N le (lit n N m)

  pν : ∀ n → pred (νᵀ (suc n)) ≡ νᵀ n
  pν n = cong (E.ψ [] (E.𝟏 ∷ []) ∷_) (pred-nat n)

  StepS-ωn : ∀ n {x} → M⁰ (pred (νᵀ (suc n))) x → R.Car (Qη (pred (νᵀ (suc n)))) (↑ zero x)
           → R.Car (Qη (νᵀ (suc n))) (↑ zero (suc x))
  StepS-ωn n {x} m _ = StepS-fin n n (inj₂ refl) (subst (λ z → M⁰ z x) (pν n) m)

  StepS-ω2 : ∀ n {x} → M⁰ (νᵀ n) x → R.Car (Qη ω2ᵀ) (↑ zero (suc x))
  StepS-ω2 n {x} m =
    R.CL refl (λ k → subst (λ z → R.Car (Qη (E.ψ [] (E.𝟏 ∷ []) ∷ z)) (↑ zero (suc x))) (sym (rep1 k)) (go k))
    where
    go : ∀ k → R.Car (Qη (νᵀ k)) (↑ zero (suc x))
    go zero    = car-ω (suc x)
    go (suc k) = StepS-fin n k (inj₂ refl) m
```
