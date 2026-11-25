# 记号侧: EBO 标准形上 ω-基本列共尾 (一切下标)

> 验收文件 (读记号, 不进成品). 判决: 定理 `cofin`, 对 `EboLeanBase.NF` 的一切项成立, 不要可数, 不限下标; 推论 `YiNFOCond.CofinNF` 见 [YiCFMono](YiCFMono.lagda.md).
> 做法: 沿 `EboLeanView` 的视图 `VΩ`/`Vω` 重走 `StandardOmega.cofin₁`; 奇异叶 $\Omega_u$ 对任意 $u$ 都是对下标 $u$ 递归, 可见参数经 `gw` 进下标, 门槛 $\nu\le x$ 由 `vis<` (标准形 $x$ 有 $\nu$-可见参数则 $\nu<x$) 给出.
> 不否定什么: 只说语法序 `_<ᵀ_` 上的共尾, 不涉及值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCFCofin where

open import Data.List.Base using (List; []; _∷_; replicate)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _<_; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Product.Base using (Σ; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import OCF.Align.EboLeanDef
open import OCF.Align.EBO using (pred-suc; <-sucT)
open import OCF.Align.EboLeanBase
open import OCF.Align.EboLeanView
```

## §1 可见参数的三条工具

```agda
vis< : ∀ {ν ζ x} → NF x → InG ν ζ x → ν <ᵀ x
vis< {x = ψ w a ∷ xs} n (gp (gh l))   = ≤-< l (idx< w a xs)
vis< {x = ψ w a ∷ xs} n (gp (gw l _)) = ≤-< l (idx< w a xs)
vis< {x = ψ w a ∷ xs} n (gp (gc l _)) = ≤-< l (idx< w a xs)
vis< {x = y ∷ ys} n (gtl i) = <ᵀ-trans (vis< (nf-tl n) i) (tail< y ys (nf-le n) (nf-tl n))

nf-G : ∀ {u z t} → NF t → InG u z t → NF z
nf-G n (gp (gh _))   = nfp-a (nf-hd n)
nf-G n (gp (gw _ i)) = nf-G (nfp-u (nf-hd n)) i
nf-G n (gp (gc _ i)) = nf-G (nfp-a (nf-hd n)) i
nf-G n (gtl i)       = nf-G (nf-tl n) i

G-trans  : ∀ {u z d t} → InG u z d → InG u d t → InG u z t
GP-trans : ∀ {u z d x} → InG u z d → InGP u d x → InGP u z x
G-trans i (gp j)  = gp (GP-trans i j)
G-trans i (gtl j) = gtl (G-trans i j)
GP-trans i (gh l)   = gc l i
GP-trans i (gw l j) = gw l (G-trans i j)
GP-trans i (gc l j) = gc l (G-trans i j)
```

## §2 Ω-共尾: 对 $c<b$ 找 $\theta<\Omega_{\nu+1}$

`ΩC w c`: 对一切 $\eta>\theta$ 有 $c<b[\eta]$; $\theta$ 的首项若是 $\psi_x(\zeta)$, $x\ge\nu$, 则 $\zeta$ 是 $c$ 的 $\nu$-可见参数. 奇异叶 `ωl` 对下标递归, 不限 $u$.

```agda
HdV : T → T → T → Set
HdV ν θ c = ∀ {x ζ θs} → θ ≡ ψ x ζ ∷ θs → ν ≤ᵀ x → InG ν ζ c

hv[] : ∀ {ν c} → HdV ν [] c
hv[] () _

record ΩC {b ν : T} (w : VΩ b ν) (c : T) : Set where
  constructor ωc
  field
    θ  : T
    θ< : θ <ᵀ Ωs ν
    fθ : ∀ {η} → θ <ᵀ η → c <ᵀ fΩ w η
    hv : HdV ν θ c

Ωcof : ∀ {b ν} → NF b → (w : VΩ b ν) → ∀ {c} → NF c → c <ᵀ b → ΩC w c
Ωcof nb (ωs v) nc []<     = ωc [] []< (λ _ → []<) hv[]
Ωcof nb (ωs v) nc (hd< q) = ωc [] []< (λ _ → hd< q) hv[]
Ωcof nb (ωs v) nc (tl< q) with Ωcof (nf-tl nb) v (nf-tl nc) q
... | ωc θ θ< fθ hv = ωc θ θ< (λ r → tl< (fθ r)) (λ eθ h → gtl (hv eθ h))
Ωcof nb (ωr e) {c} nc p =
  ωc c (subst (c <ᵀ_) (sym (reg-eq e)) p) (λ r → r)
     (λ {x} {ζ} {θs} eθ h → subst (InG _ ζ) (sym eθ) (gp (gh h)))
Ωcof nb (ωl e v) nc []< = ωc [] []< (λ _ → []<) hv[]
Ωcof nb (ωl e v) nc (hd< (lv< q)) with Ωcof (nfp-u (nf-hd nb)) v (nfp-u (nf-hd nc)) q
... | ωc θ θ< fθ hv =
  ωc θ θ< (λ r → hd< (lv< (fθ r)))
     (λ eθ h → gp (gw (inj₁ (vis< (nfp-u (nf-hd nc)) (hv eθ h))) (hv eθ h)))
Ωcof nb (ωl e v) nc (hd< (ar< ()))
Ωcof nb (ωl e v) nc (tl< ())
Ωcof nb (ωp be pen v) nc []< = ωc [] []< (λ _ → []<) hv[]
Ωcof nb (ωp be pen v) nc (hd< (lv< q)) = ωc [] []< (λ _ → hd< (lv< q)) hv[]
Ωcof {ν = ν} nb (ωp {u = u} be pen v) nc (hd< (ar< q)) with Ωcof (nfp-a (nf-hd nb)) v (nfp-a (nf-hd nc)) q
... | ωc θ θ< fθ hv =
  ωc θ θ< (λ r → hd< (ar< (fθ r)))
     (λ eθ h → gp (gc (inj₁ (<-≤ (<-sucT ν) (Pen→≤ (sucT ν) u pen))) (hv eθ h)))
Ωcof nb (ωp be pen v) nc (tl< ())
```

## §3 规则 6: γ-链共尾 (对 $c$ 的大小递归)

```agda
data Six {b ν : T} (w : VΩ b ν) (c : T) : Set where
  base : c <ᵀ fΩ w (γ w zero) → Six w c
  up   : ∀ {ζ} → InG ν ζ c → (∀ {η} → ζ <ᵀ η → c <ᵀ fΩ w (ψ ν η ∷ [])) → Six w c

six : ∀ {b ν c} {w : VΩ b ν} → ΩC w c → Six w c
six {ν = ν} (ωc [] θ< fθ hv) = base (fθ {Ωt ν} []<)
six {ν = ν} (ωc (ψ x ζ ∷ θs) (hd< (lv< q)) fθ hv) with <sucT ν q
... | inj₁ r    = base (fθ {Ωt ν} (hd< (lv< r)))
... | inj₂ refl = up (hv refl (inj₂ refl)) (λ r → fθ (hd< (ar< r)))
six (ωc (ψ x ζ ∷ θs) (hd< (ar< ())) fθ hv)
six (ωc (ψ x ζ ∷ θs) (tl< ()) fθ hv)

Cof6 : ∀ m {b ν A c} → NF b → (w : VΩ b ν) → A ≤ᵀ ν → size c < m → NF c → c <ᵀ b →
       (∀ {ζ} → InG A ζ c → ζ <ᵀ b) → Σ ℕ λ n → c <ᵀ fΩ w (γ w n)
Cof6 zero nb w Aν () nc p H
Cof6 (suc m) nb w Aν (s≤s hm) nc p H with six (Ωcof nb w nc p)
... | base r = 0 , r
... | up vz f with Cof6 m nb w Aν (≤-trans (G-size vz) hm) (nf-G nc vz)
                        (H (G-mono Aν vz)) (λ i → H (G-trans i (G-mono Aν vz)))
...   | k , r = suc k , f r
```

## §4 ω-共尾

```agda
repb : ∀ x {vs} → NF vs → HdLe x vs → Σ ℕ λ m → vs <ᵀ replicate m x
repb x n[] h = 1 , []<
repb x (n∷ p h′ n) (inj₁ q) = 1 , hd< q
repb x (n∷ p h′ n) (inj₂ refl) with repb x n h′
... | m , r = suc m , tl< r

cofinV : ∀ {t} → NF t → (v : Vω t) → ∀ {s} → NF s → s <ᵀ t → Σ ℕ λ n → s <ᵀ fω v n
cofinV nt (ws v) ns []<     = 0 , []<
cofinV nt (ws v) ns (hd< q) = 0 , hd< q
cofinV nt (ws v) ns (tl< q) with cofinV (nf-tl nt) v (nf-tl ns) q
... | n , r = n , tl< r
cofinV nt (wl e v) ns []< = 0 , []<
cofinV nt (wl e v) ns (hd< (lv< q)) with cofinV (nfp-u (nf-hd nt)) v (nfp-u (nf-hd ns)) q
... | n , r = n , hd< (lv< r)
cofinV nt (wl e v) ns (hd< (ar< ()))
cofinV nt (wl e v) ns (tl< ())
cofinV nt (w4 e) ns []< = 1 , []<
cofinV nt (w4 e) ns (hd< (lv< q)) = 1 , hd< (lv< q)
cofinV nt (w4 {u} {b} e) {ψ _ a ∷ ss} (n∷ p h n) (hd< (ar< q))
  with <sucT (pred b) (subst (a <ᵀ_) (sym (pred-suc b e)) q)
... | inj₁ r = 1 , hd< (ar< r)
... | inj₂ refl with repb (ψ u (pred b)) n h
...   | m , r = suc m , tl< r
cofinV nt (w4 e) ns (tl< ())
cofinV nt (w5 e v) ns []< = 0 , []<
cofinV nt (w5 e v) ns (hd< (lv< q)) = 0 , hd< (lv< q)
cofinV nt (w5 e v) ns (hd< (ar< q)) with cofinV (nfp-a (nf-hd nt)) v (nfp-a (nf-hd ns)) q
... | n , r = n , hd< (ar< r)
cofinV nt (w5 e v) ns (tl< ())
cofinV nt (w6 be g w) ns []< = 0 , []<
cofinV nt (w6 be g w) ns (hd< (lv< q)) = 0 , hd< (lv< q)
cofinV nt (w6 {u} {b} {ν} be g w) {ψ _ a ∷ ss} ns (hd< (ar< q))
  with Cof6 (suc (size a)) (nfp-a (nf-hd nt)) w (gt→≤ ν u g) ≤-refl (nfp-a (nf-hd ns)) q
            (λ i → <ᵀ-trans (nfp-g (nf-hd ns) i) q)
... | n , r = n , hd< (ar< r)
cofinV nt (w6 be g w) ns (tl< ())

cofin : ∀ {t} → NF t → cof t ≡ cω → ∀ {s} → NF s → s <ᵀ t → Σ ℕ λ n → s <ᵀ fsn t n
cofin {t} nt e ns p with cofinV nt (vω t e) ns p
... | n , r = n , subst (_ <ᵀ_) (sym (fω-eq (vω t e) n)) r
```
