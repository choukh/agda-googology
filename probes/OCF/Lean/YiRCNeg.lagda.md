# 验收: 主线原行与 FGH 式折叠的那一支不过判据 (否定)

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 编译的否定定理, 无前提: `main-neg : ∀ k → CritAt gᴹ (2+k) → ⊥` (主线 `YiRWFold` 原来那一行), `fg-neg : ∀ k → CritAt gᶠ (2+k) → ⊥` (`YiFGFold`); 对一切孩子 c 也成立 (`main-neg-all`, `fg-neg-all`).
> 机制: 谓词 `Sm` (第 2 层的 Ω 树, 它的第一支, 零, 以及在它们之上只用后继与 ℕ 极限搭出的树) 沿 `◃` 向下封闭 (`dwn`); `M 2 (ψ₂(Ω₂)) x` 在 `Sm` 内只能落到 Ω 树这一个结点, 取 η = 0 的分支得 `M 2 (Ω₂) (第一支)`, 不成立; ψ₂(Ω_{3+k}) 经基本列第 0 项降到 ψ₂(Ω₂).
> 否定的是不带项序封闭的关系 `YiCLFam.M 2` 下的判据在这两行上成立; 不涉及候选 A、统一规则 `φ` (那两支不在 `Sm` 内, 见 `YiRCCandA.a-chain`), 不涉及序数值的上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRCNeg where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKVRel using (Mᴰ; mz; m1; mL; mΩ; mU; mw)
import OCF.Align.EboLeanDef as E
open E using (cof; c0; c1; cω; cΩ; fsn; fsT; γT; natT)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ; cofΩ; fsTΩ; cmp-gt; cofG; fsnG)
open import OCF.Lean.YiCLFam using (nat; fn; M)
open import OCF.Lean.YiRBCrit using (two; CritAt; gᴹ)
open import OCF.Lean.YiRCFG using (gᶠ)
```

## 记号一侧: ψ₂(Ω_{2+k})

```agda
Tk : ℕ → E.T
Tk k = ψᴺ 2 (Ωᴺ (suc (suc k)))

cofT0 : cof (Tk 0) ≡ cΩ (natT 1)
cofT0 = refl

fsT0 : fsT (Tk 0) [] ≡ Ωᴺ 2
fsT0 = refl

cofTs : ∀ k → cof (Tk (suc k)) ≡ cω
cofTs k = cofG (natT 2) (Ωᴺ (suc (suc (suc k)))) (cmp-gt {b = 2} {a = suc (suc k)} (s≤s (s≤s z≤n))) (cofΩ (suc (suc k)))

fsnTs : ∀ k → fsn (Tk (suc k)) 0 ≡ Tk k
fsnTs k = trans (fsnG (natT 2) (Ωᴺ (suc (suc (suc k)))) 0 (cmp-gt {b = 2} {a = suc (suc k)} (s≤s (s≤s z≤n))) (cofΩ (suc (suc k))))
                (cong (ψᴺ 2) (fsTΩ (suc (suc k)) (γT (Ωᴺ (suc (suc (suc k)))) (natT (suc (suc k))) 0)))

c1≢cΩ : ∀ {ν} → c1 ≡ cΩ ν → ⊥
c1≢cΩ ()

cω≢cΩ : ∀ {ν} → cω ≡ cΩ ν → ⊥
cω≢cΩ ()

c1≢cω : c1 ≡ cω → ⊥
c1≢cω ()

cΩ≢cω : ∀ {ν} → cΩ ν ≡ cω → ⊥
cΩ≢cω ()

split1 : (t s : E.T) {p : E.PT} → t ++ s ≡ p ∷ [] → (t ≡ [] × s ≡ p ∷ []) ⊎ (t ≡ p ∷ [] × s ≡ [])
split1 []          s       refl = inj₁ (refl , refl)
split1 (x ∷ [])    []      refl = inj₂ (refl , refl)
split1 (x ∷ [])    (_ ∷ _) ()
split1 (x ∷ _ ∷ _) s       ()
```

## 一般的小引理: 零与一

对任意一层的关系 `Mᴰ`: 共尾是 Ω 的项不对着零与一; ψ₂(Ω_{2+k}) 也不.

```agda
module _ {S : Sg} where
  nz : {x : T S} → Lt S x zero → ⊥
  nz (◃t d d′) = nz d′

  lt1 : {x : T S} → Lt S x (suc zero) → x ≡ zero
  lt1 ◃s = refl
  lt1 (◃t d d′) with lt1 d′
  ... | refl = ⊥-elim (nz d)

module _ {S : Sg} {Low : (p : P S) → E.T → B S p → Set} {Chd : (c : C S) → E.T → D S c → Set} {Nu : P S → E.T → Set} where
  private
    Rel : E.T → T S → Set
    Rel = Mᴰ S Low Chd Nu

  hΩ0 : ∀ {t ν} → cof t ≡ cΩ ν → Rel t zero → ⊥
  hΩ0 () mz
  hΩ0 e (mL e′ h) = cω≢cΩ (trans (sym e′) e)
  hΩ0 e (mw m d)  = nz d

  hΩ1 : ∀ {t ν} → cof t ≡ cΩ ν → Rel t (suc zero) → ⊥
  hΩ1 () mz
  hΩ1 e (m1 e′ r) = c1≢cΩ (trans (sym e′) e)
  hΩ1 e (mL e′ h) = cω≢cΩ (trans (sym e′) e)
  hΩ1 e (mw m d) with lt1 d
  ... | refl = hΩ0 e m

  tiny0 : ∀ k {t} → t ≡ Tk k → Rel t zero → ⊥
  tiny0 zero    q    m         = hΩ0 (trans (cong cof q) cofT0) m
  tiny0 (suc k) ()   mz
  tiny0 (suc k) q    (mL e h)  = tiny0 k (trans (cong (λ t → fsn t 0) q) (fsnTs k)) (h 0)
  tiny0 (suc k) q    (mw m d)  = nz d

  tiny1 : ∀ k {t} → t ≡ Tk k → Rel t (suc zero) → ⊥
  tiny1 zero    q    m         = hΩ1 (trans (cong cof q) cofT0) m
  tiny1 (suc k) ()   mz
  tiny1 (suc k) q    (m1 e r)  = c1≢cω (trans (sym e) (trans (cong cof q) (cofTs k)))
  tiny1 (suc k) q    (mL e h)  = tiny1 k (trans (cong (λ t → fsn t 0) q) (fsnTs k)) (h 0)
  tiny1 (suc k) q    (mw m d) with lt1 d
  ... | refl = tiny0 (suc k) q m
```

## 谓词 `Sm`

```agda
data Sm : Tr two → Set where
  k0 : Sm zero
  kb : ∀ {e} → Sm (up zero tt (suc zero) e)
  kΩ : Sm (proj₁ (Ωt two))
  ks : ∀ {x} → Sm x → Sm (suc x)
  kl : ∀ {f a} → (∀ n → Sm (f n)) → Sm (lim f a)

dwn : ∀ {x x′} → Sm x → two ⊢ x′ ◃ x → Sm x′
dwn k0     d                = ⊥-elim (nz d)
dwn kb     (◃u _ _ _ _)     = k0
dwn kb     (◃c _ _ {e′ = e′} r) with lt1 r
... | refl = ⊥-elim (nz e′)
dwn kb     (◃t d d′)        = dwn (dwn kb d′) d
dwn kΩ     ◃w               = kb
dwn kΩ     (◃t d d′)        = dwn (dwn kΩ d′) d
dwn (ks s) ◃s               = s
dwn (ks s) (◃t d d′)        = dwn (dwn (ks s) d′) d
dwn (kl h) (◃l n)           = h n
dwn (kl h) (◃t d d′)        = dwn (dwn (kl h) d′) d

Sm+ι : ∀ {b} → Sm b → (y : Tr zero) → Sm (b + ι two y)
Sm+ι s zero      = s
Sm+ι s (suc y)   = ks (Sm+ι s y)
Sm+ι s (lim f a) = kl (λ n → Sm+ι s (f n))

belowB : ∀ {x′ e} → two ⊢ x′ ◃ up zero tt (suc zero) e → x′ ≡ zero
belowB (◃u _ _ _ _) = refl
belowB (◃c _ _ {e′ = e′} r) with lt1 r
... | refl = ⊥-elim (nz e′)
belowB (◃t d d′) with belowB d′
... | refl = ⊥-elim (nz d)
```

## 否定

`negB`: Ω₂ 不对着 Ω 树的第一支. `negS`: ψ₂(Ω_{2+k}) 不对着 `Sm` 里的树.

```agda
negB : ∀ {t e} → t ≡ Ωᴺ 2 → M 2 t (up zero tt (suc zero) e) → ⊥
negB q (mU {t = t′} {s = s} m ch) with split1 t′ s q
... | inj₁ (_ , qs) = hΩ1 (trans (cong cof qs) (cofΩ 1)) ch
... | inj₂ (qt , _) = hΩ0 (trans (cong cof qt) (cofΩ 1)) m
negB q (mL e h) = cω≢cΩ (trans (sym e) (trans (cong cof q) (cofΩ 1)))
negB q (mw m d) with belowB d
... | refl = hΩ0 (trans (cong cof q) (cofΩ 1)) m

negS : ∀ k {t x} → t ≡ Tk k → Sm x → M 2 t x → ⊥
negS zero    () sm      mz
negS zero    q  (ks sm) (m1 e r)     = c1≢cΩ (trans (sym e) (trans (cong cof q) cofT0))
negS zero    q  sm      (mL e h)     = cω≢cΩ (trans (sym e) (trans (cong cof q) cofT0))
negS zero    q  kΩ      (mΩ e nu h)  = negB (trans (cong (λ t → fsT t []) q) fsT0) (h [] zero mz)
negS zero    q  kb      (mU {t = t′} {s = s} m ch) with split1 t′ s q
... | inj₁ (_ , qs) = tiny1 0 qs ch
... | inj₂ (qt , _) = tiny0 0 qt m
negS zero    q  sm      (mw m d)     = negS zero q (dwn sm d) m
negS (suc k) () sm      mz
negS (suc k) q  (ks sm) (m1 e r)     = c1≢cω (trans (sym e) (trans (cong cof q) (cofTs k)))
negS (suc k) q  sm      (mL e h)     = negS k (trans (cong (λ t → fsn t 0) q) (fsnTs k)) sm (h 0)
negS (suc k) q  kΩ      (mΩ e nu h)  = cΩ≢cω (trans (sym e) (trans (cong cof q) (cofTs k)))
negS (suc k) q  kb      (mU {t = t′} {s = s} m ch) with split1 t′ s q
... | inj₁ (_ , qs) = tiny1 (suc k) qs ch
... | inj₂ (qt , _) = tiny0 (suc k) qt m
negS (suc k) q  sm      (mw m d)     = negS (suc k) q (dwn sm d) m
```

## 两行

主线原行的那一支是 `Ωt two + ι two …` (`YiRBCrit.main-shape`), `YiFGFold` 的是 `suc (Ωt two) + ι two …` (`YiRCFG.fg-shape`); 都在 `Sm` 内, 对一切孩子 c.

```agda
main-neg-all : ∀ k (c : Tr zero) → M 2 (ψᴺ 2 (Ωᴺ (suc (suc k)))) (proj₁ (gᴹ c)) → ⊥
main-neg-all k c = negS k refl (Sm+ι kΩ _)

fg-neg-all : ∀ k (c : Tr zero) → M 2 (ψᴺ 2 (Ωᴺ (suc (suc k)))) (proj₁ (gᶠ c)) → ⊥
fg-neg-all k c = negS k refl (Sm+ι (ks kΩ) _)

main-neg : ∀ k → CritAt gᴹ (suc (suc k)) → ⊥
main-neg k = main-neg-all k (nat (suc (suc k)))

fg-neg : ∀ k → CritAt gᶠ (suc (suc k)) → ⊥
fg-neg k = fg-neg-all k (nat (suc (suc k)))
```
