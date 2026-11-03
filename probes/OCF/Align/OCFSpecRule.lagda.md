# 折叠的外部规格: 折叠的每一行都是规格的定理 (底座)

> 底座, 不含记号. 结论写在 [OCFSpec](OCFSpec.lagda.md). 本文对任意目标 $v$ 证明: $\psi_v(0)=\Omega_v$ (`T0`), 后继行 `Tsuc`, 链行 `Tchain` (ω-极限行 `Tlim` 是它的特例). 前提都是值上的, 没有折叠, 没有项文法.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OCFSpecRule where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ᴺ_)
open import Data.Nat.Properties using (+-comm)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst; subst₂; trans)

open import OCF.BTBO using (module Ord-Ord; module Trich; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.Level
open import OCF.Align.OCFSpecBase
```

## §1 关于 $\Omega$ 的值

`bd⇒`: $x<\Omega_{v+1}$ 给出第 $v$ 层的见证. `Ω-pt`: $y<\Omega_v$ 给出第 $v$ 层的见证, 它自己也 $<\Omega_v$. `Ω-≼`: $\Omega$ 对层号的 $\sqsubseteq^\mathsf{I}$ 单调, 值的版本. `Ω-prin`: $\Omega_v$ 对加法封闭, 对一切层号; 极限层靠层号的步进证据 `steps`.

```agda
𝟏 : ∀ {ℓ} → Ordᶜ ℓ
𝟏 = suc zero

bd⇒ : ∀ {v m} {x : Ordᶜ m} → x ≺ᵛ Ω (suc v) → Σ (Ordᶜ v) λ z → (z ≅ z) × (x ≺ᵛ z)
bd⇒ (≼i z ez (≼u q)) = z , ez , q

⇒bd : ∀ {v m} {x : Ordᶜ m} (z : Ordᶜ v) → z ≅ z → x ≼ z → x ≺ᵛ Ω (suc v)
⇒bd z ez q = ≼i (suc z) (s≅ ez) (≼u (s≼s q))

Ω≺Ω⁺ : ∀ v → Ω v ≺ᵛ Ω (suc v)
Ω≺Ω⁺ v = ⇒bd (Ω v) (Ω-refl v) (≼-refl (Ω v))

1≼Ω : ∀ {ℓ₀} v → 𝟏 {ℓ₀} ≼ Ω v
1≼Ω zero      = s≼s z≼
1≼Ω (suc v)   = ≼i 𝟏 (s≅ z≅) (≼u (s≼s z≼))
1≼Ω (lim f s) = ≼l 0 (≼u (1≼Ω (f 0)))

0≺Ω : ∀ {m} v → 𝟎 {m} ≺ᵛ Ω v
0≺Ω zero      = s≼s z≼
0≺Ω (suc v)   = ≼i 𝟏 (s≅ z≅) (≼u (s≼s z≼))
0≺Ω (lim f s) = ≼l 0 (≼u (0≺Ω (f 0)))

below-≼ : ∀ {a b} → a <ᴵ b → {x : Ordᶜ a} → x ≅ x → x ≼ Ω b
below-≼ zero {x} ex = ≼i x ex (≼u (≼-refl x))
below-≼ {b = suc b} (suc q) ex = ≼i (Ω b) (Ω-refl b) (≼u (below-≼ q ex))
below-≼ (lim n q) ex = ≼l n (≼u (below-≼ q ex))

Ω-≼ : ∀ {a b} → a ⊑ᴵ b → Ω a ≼ Ω b
Ω-≼ {b = b} z⊑ = 1≼Ω b
Ω-≼ (s⊑ e q) = i≼ (λ x ex → u≼ (≼-trans (≅→≼ (≅-tr e ex)) (below-≼ q (tr-≅ e (≅-tr e ex)))))
Ω-≼ (l⊑ k) = l≼ (λ n → u≼ (Ω-≼ (k n)))

Ω-pt : ∀ v {m} {y : Ordᶜ m} → y ≺ᵛ Ω v → Σ (Ordᶜ v) λ p → (p ≺ᵛ Ω v) × (y ≼ p) × (p ≅ p)
Ω-pt zero (s≼s q) = zero , s≼s z≼ , q , z≅
Ω-pt (suc v) (≼i z ez (≼u q)) = up zero z , ≼i (suc z) (s≅ ez) (≼u (s≼s (u≼ (≼-refl z)))) , ≼u (≺→≼ q) , upˡ (upʳ ez)
Ω-pt (lim f s) (≼l n (≼u q)) with Ω-pt (f n) q
... | p , b , d , ep = up (self n) p , ≼l n (≼u (≼-trans (s≼s (u≼ (≼-refl p))) b)) , ≼u d , upˡ (upʳ ep)

Prin : ∀ {n} → Ordᶜ n → Set
Prin t = ∀ {m k} {x : Ordᶜ m} {y : Ordᶜ k} (σ : Simᴵ k m) → x ≺ᵛ t → y ≺ᵛ t → add x σ y ≺ᵛ t

Ω-prin : ∀ v → Prin (Ω v)
Ω-prin zero σ (s≼s p) (s≼s q) = s≼s (add-mono {σ′ = λ r → r} p q)
Ω-prin (suc v) σ p q with bd⇒ p | bd⇒ q
... | z₁ , e₁ , d₁ | z₂ , e₂ , d₂ = ⇒bd (z₁ + z₂) (add-≅ e₁ e₂) (add-mono (≺→≼ d₁) (≺→≼ d₂))
Ω-prin (lim f s) σ (≼l n (≼u p)) (≼l m (≼u q)) with <ᴺ-dec n m
... | injᵃ n<m = ≼l m (≼u (Ω-prin (f m) σ (≼-trans p (Ω-≼ (steps s n<m))) q))
... | injᵇ m<n = ≼l n (≼u (Ω-prin (f n) σ p (≼-trans q (Ω-≼ (steps s m<n)))))
... | injᶜ refl = ≼l n (≼u (Ω-prin (f n) σ p q))
```

## §2 下界 `Ω-floor`, 比较的钩子 `ΩO`

规格给出的值都不低于 $\Omega_u$. `ΩO v` 是下面对 $v$ 的唯一要求: $\Omega_u$ 落在 $\Omega_{v+1}$ 以下就 $\preccurlyeq\Omega_v$. 对 $v=0$ 与 $v=1$ 在 [OCFSpecAnchor](OCFSpecAnchor.lagda.md) 证. 一般的 $v$ 没有证 (判断: 要层号的值序与字面序的对接, 与 `Lift` 同类).

```agda
Ω-floor : ∀ {u k n} {ξ : Ordᶜ k} {w : Ordᶜ n} (ac : Acc ξ) → IsPsiₐ u ξ ac w → Ω u ≼ w
Ω-floor {u} {w = w} (acc h) r =
  below→≼ (Ω u) (λ q → ub r (base q) (≼-trans q (≺→≼ (Ω≺Ω⁺ u))))

1≼ψ̂ : ∀ {ℓ₀ u k n} {ξ : Ordᶜ k} {w : Ordᶜ n} (ac : Acc ξ) → IsPsiₐ u ξ ac w → 𝟏 {ℓ₀} ≼ w
1≼ψ̂ {u = u} ac r = ≼-trans (1≼Ω u) (Ω-floor ac r)

ΩO : Ordᴵ → Set
ΩO v = ∀ u (z : Ordᶜ v) → z ≅ z → Ω u ≼ z → Ω u ≼ Ω v

col-bound : ∀ {u v k k′ n n′} {ξ : Ordᶜ k} {a : Ordᶜ k′} {w : Ordᶜ n} {t : Ordᶜ n′} (ac : Acc ξ) →
            ΩO v → ξ ≼ a → IsPsiₐ u ξ ac w → IsPsi v a t → w ≺ᵛ Ω (suc v) → w ≼ t
col-bound {u} {v} {a = a} ac hO e r s b with bd⇒ b
... | z , ez , d = ψ̂-mono ac (wf a) (hO u z ez (≼-trans (Ω-floor ac r) (≺→≼ d))) e r s b
```

## §3 `ub` 的归纳原理

`I` 是调用者的不变量. 要 `I` 对基底、加法、值相等、$\psi$ 封闭, 其中 $\psi$ 的情形可以用 `I ξ`.

```agda
module Ind {v k} {a : Ordᶜ k} {R : (u : Ordᴵ) → ∀ {m} (ξ : Ordᶜ m) → ξ ≺ᵛ a → ∀ {n} → Ordᶜ n → Set}
           (I : ∀ {m} → Ordᶜ m → Set)
           (ib : ∀ {m} {x : Ordᶜ m} → x ≺ᵛ Ω v → I x)
           (ip : ∀ {m k′} {x : Ordᶜ m} {y : Ordᶜ k′} (σ : Simᴵ k′ m) → I x → I y → I (add x σ y))
           (ic : ∀ {u m n} {ξ : Ordᶜ m} {w : Ordᶜ n} → (q : ξ ≺ᵛ a) → R u ξ q w → I (forget u) → I ξ → I w)
           (ig : ∀ {m n} {x : Ordᶜ m} {y : Ordᶜ n} → y ≈ᵛ x → I x → I y) where
  go : ∀ {m} {x : Ordᶜ m} → Cl₊ v a R x → I x
  go (base q)        = ib q
  go (plus σ c d)    = ip σ (go c) (go d)
  go (col cu cξ q r) = ic q r (go cu) (go cξ)
  go (cg e c)        = ig e (go c)

-- 最常用的不变量: x < Ω_{v+1} → x < t
BndI : ∀ (v : Ordᴵ) {n} (t : Ordᶜ n) {m} → Ordᶜ m → Set
BndI v t x = x ≺ᵛ Ω (suc v) → x ≺ᵛ t

Bnd-plus : ∀ {v n} {t : Ordᶜ n} → Prin t → ∀ {m k′} {x : Ordᶜ m} {y : Ordᶜ k′} (σ : Simᴵ k′ m) →
           BndI v t x → BndI v t y → BndI v t (add x σ y)
Bnd-plus {v} pt {x = x} {y = y} σ ix iy b =
  pt σ (ix (≼-≺ (add-≽ˡ x σ y) b)) (iy (≼-≺ (add-≽ʳ x σ y) b))

Bnd-cg : ∀ {v n} {t : Ordᶜ n} {m m′} {x : Ordᶜ m} {y : Ordᶜ m′} → y ≈ᵛ x → BndI v t x → BndI v t y
Bnd-cg (e , e′) ix b = ≼-≺ e (ix (≼-≺ e′ b))
```

## §4 $\psi_v(0)=\Omega_v$, 对一切 $v$

```agda
T0 : ∀ v → IsPsi v (𝟎 {zero}) (Ω v)
T0 v = sup (Ω≺Ω⁺ v) (Ind.go (BndI v (Ω v)) (λ q _ → q) (Bnd-plus (Ω-prin v)) (λ { () }) Bnd-cg)
  (λ q → let p , b , d , ep = Ω-pt v q in wit (base b) (⇒bd p ep (≼-refl p)) d)
```

## §5 后继行

`M x` 就是折叠的后继行 $\lim_n x\cdot n$. 前提: $b$ 处的值已知, $b\in C_v(b+1)$ (这是标准形条件, 不是技术性的: `fold-wrong-at-gap` 说没有它结论是假的), $v\in C_v(b+1)$.

```agda
_·_ : ∀ {ℓ} → Ordᶜ ℓ → ℕ → Ordᶜ ℓ
x · n = iter (x +_) zero n

M : ∀ {ℓ} → Ordᶜ ℓ → Ordᶜ ℓ
M x = lim (x ·_)

0+≼ : ∀ {k ℓ} (σ : Simᴵ k ℓ) (w : Ordᶜ k) → add 𝟎 σ w ≼ w
0+≼ σ zero    = z≼
0+≼ σ (suc w) = s≼s (0+≼ σ w)
0+≼ σ (lim f) = l≼ (λ n → ≼l n (0+≼ σ (f n)))
0+≼ σ (limᵢ q f) = i≼ (λ x ex → ≼i x ex
  (subst (λ u → add 𝟎 σ (f u) ≼ f (into (<→◃ q) x)) (sym (coe-into (<→◃ (σ q)) (<→◃ q) x)) (0+≼ σ (f (into (<→◃ q) x)))))
0+≼ σ (up zero x)     = ≼u (0+≼ _ x)
0+≼ σ (up (self n) x) = ≼u (0+≼ _ x)

·-add : ∀ {ℓ} (x : Ordᶜ ℓ) n m → x · n + x · m ≼ x · (n +ᴺ m)
·-add x zero    m = 0+≼ (λ q → q) (x · m)
·-add x (suc n) m = ≼-trans (+-assoc x (x · n) (λ q → q) (x · m)) (+-mono (≼-refl x) (·-add x n m))

·-≼ : ∀ {ℓ ℓ′} {x : Ordᶜ ℓ} {z : Ordᶜ ℓ′} → x ≼ z → ∀ n → x · n ≼ z · n
·-≼ e zero    = z≼
·-≼ e (suc n) = +-mono e (·-≼ e n)

·-≅ : ∀ {ℓ} {z : Ordᶜ ℓ} → z ≅ z → ∀ n → z · n ≅ z · n
·-≅ e zero    = z≅
·-≅ e (suc n) = add-≅ e (·-≅ e n)

M-prin : ∀ {ℓ} (x : Ordᶜ ℓ) → Prin (M x)
M-prin x σ (≼l n p) (≼l m q) = ≼l (n +ᴺ m) (≼-trans (add-mono (≺→≼ p) q) (·-add x n m))

M-lt : ∀ {v ℓ} {x : Ordᶜ ℓ} → x ≺ᵛ Ω (suc v) → M x ≺ᵛ Ω (suc v)
M-lt p with bd⇒ p
... | z , ez , d = ⇒bd (M z) (l≅ (·-≅ ez)) (l≼ (λ n → ≼l n (·-≼ (≺→≼ d) n)))

·-lt : ∀ {v ℓ} {x : Ordᶜ ℓ} → x ≺ᵛ Ω (suc v) → ∀ n → x · n ≺ᵛ Ω (suc v)
·-lt p n = ≼-≺ (≼l n (≼-refl _)) (M-lt p)

suc≼M : ∀ {ℓ n} {x : Ordᶜ ℓ} → 𝟏 {ℓ} ≼ x → (w : Ordᶜ n) → w ≼ x → w ≺ᵛ M x
suc≼M {x = x} one w d = ≼-trans (s≼s d) (≼l 2 (+-mono (≼-refl x) one))

Tsuc : ∀ {v k} {b : Ordᶜ k} {x : Ordᶜ v} → ΩO v →
       IsPsi v b x → C v (suc b) b → C v (suc b) (forget v) → IsPsi v (suc b) (M x)
Tsuc {v} {b = b} {x = x} hO s cb cv =
  sup (M-lt (lt s))
      (Ind.go (BndI v (M x))
        (λ q _ → ≼-trans (≼-trans q (Ω-floor (wf b) s)) (≼l 1 (≼-refl x)))
        (Bnd-plus (M-prin x))
        (λ {u} {m} {n} {ξ} {w} q r _ _ bw →
           suc≼M (1≼ψ̂ (wf b) s) w (col-bound (belowᵛ (suc b) ξ q) hO (s≼s⁻ q) r s bw))
        Bnd-cg)
      (λ { (≼l n q) → wit (cn n) (·-lt (lt s) n) (≺→≼ q) })
  where
  cx : C v (suc b) x
  cx = col cv cb (≼-refl (suc b)) (irr≡ (wf b) _ s)
  cn : ∀ n → C v (suc b) (x · n)
  cn zero    = base (0≺Ω v)
  cn (suc n) = plus (λ r → r) cx (cn n)
```

## §6 链行

`Tchain`: 输入 $a$, 点列 $\hat f_n\preccurlyeq a$, $\psi_v(\hat f_n)=F_n$, $F_n$ 严格增. 不变量 `I` 由调用者给: 它在 $\psi$ 的情形可以用 "`ξ` 落在某个 $\hat f_n$ 以下就有 `w<t`". `I-br` 是**托架**: `I ξ` 且 $\xi<a$ 时 $\xi$ 落在某个 $\hat f_n$ 以下. 这是规格对折叠的链的全部要求, 也是 $\Omega$-共尾的节点上唯一不平凡的东西.

`Tlim` 是 $\omega$-极限, 托架平凡. `Tsup` 是 $\Omega$ 上的: 托架由 `ub` 的归纳假设给出.

```agda
Flim-prin : ∀ {n} {F : ℕ → Ordᶜ n} → (∀ i → F i ≺ᵛ F (suc i)) →
            (∀ i → Prin (F i)) → Prin (lim F)
Flim-prin {F = F} st pr σ (≼l n p) (≼l m q) =
  ≼l (n +ᴺ m) (pr (n +ᴺ m) σ (≼-trans p (up-n n m)) (≼-trans q (subst (λ c → F m ≼ F c) (+-comm m n) (up-n m n))))
  where
  up-n : ∀ i j → F i ≼ F (i +ᴺ j)
  up-n i zero    = subst (λ c → F i ≼ F c) (sym (+-right i)) (≼-refl (F i)) where
    +-right : ∀ i → i +ᴺ 0 ≡ i
    +-right zero    = refl
    +-right (suc i) = cong suc (+-right i)
  up-n i (suc j) = subst (λ c → F i ≼ F c) (sym (+-s i j)) (≼-trans (up-n i j) (≺→≼ (st (i +ᴺ j)))) where
    +-s : ∀ i j → i +ᴺ suc j ≡ suc (i +ᴺ j)
    +-s zero    j = refl
    +-s (suc i) j = cong suc (+-s i j)

-- 规格的值对加法封闭: 对任何 v, 只用 cof 与 ub
ψ̂-prin : ∀ {v k n} {a : Ordᶜ k} {t : Ordᶜ n} → IsPsi v a t → Prin t
ψ̂-prin {v} s σ p q =
  let w₁ = cof s p ; w₂ = cof s q in
  ≼-trans (s≼s (add-mono {σ′ = λ r → r} (dom w₁) (dom w₂)))
          (ub s (plus (λ r → r) (mem w₁) (mem w₂)) (Ω-prin (suc v) (λ r → r) (bd w₁) (bd w₂)))

⇒lim-lt : ∀ {v n} {F : ℕ → Ordᶜ n} → (∀ i → F i ≺ᵛ Ω (suc v)) → lim F ≺ᵛ Ω (suc v)
⇒lim-lt {v} {F = F} h = ⇒bd (lim z) (l≅ (λ i → proj₁ (proj₂ (bd⇒ (h i))))) (l≼ (λ i → ≼l i (≺→≼ (proj₂ (proj₂ (bd⇒ (h i)))))))
  where
  z : ℕ → Ordᶜ v
  z i = proj₁ (bd⇒ (h i))

module Chain {v k n} {a : Ordᶜ k} {F : ℕ → Ordᶜ n} {lv : ℕ → Ordᴵ} {f̂ : (i : ℕ) → Ordᶜ (lv i)}
             (hO : ΩO v)
             (ef : ∀ i → f̂ i ≼ a)
             (s : ∀ i → IsPsi v (f̂ i) (F i))
             (st : ∀ i → F i ≺ᵛ F (suc i)) where

  t : Ordᶜ n
  t = lim F

  t-prin : Prin t
  t-prin = Flim-prin st (λ i → ψ̂-prin (s i))

  t-lt : t ≺ᵛ Ω (suc v)
  t-lt = ⇒lim-lt (λ i → lt (s i))

  t-cof : ∀ {m} {y : Ordᶜ m} → y ≺ᵛ t → Wit v (C v a) y
  t-cof (≼l i q) = let w = cof (s i) q in wit (C-a (ef i) (mem w)) (bd w) (dom w)

  t-floor : ∀ {m} {x : Ordᶜ m} → x ≺ᵛ Ω v → x ≺ᵛ t
  t-floor q = ≼l 0 (≼-trans q (Ω-floor (wf (f̂ 0)) (s 0)))

  -- 落在 f̂ i 以下的 ξ 的 ψ 值严格低于 t
  under : ∀ {u m n′} {ξ : Ordᶜ m} {w : Ordᶜ n′} (ac : Acc ξ) → IsPsiₐ u ξ ac w → w ≺ᵛ Ω (suc v) →
          ∀ i → ξ ≼ f̂ i → w ≺ᵛ t
  under ac r bw i e = ≼l (suc i) (≼-trans (s≼s (col-bound ac hO e r (s i) bw)) (st i))

record Bracket {v k n} (a : Ordᶜ k) (F : ℕ → Ordᶜ n) {lv : ℕ → Ordᴵ} (f̂ : (i : ℕ) → Ordᶜ (lv i)) : Set₁ where
  field
    I    : ∀ {m} → Ordᶜ m → Set
    i-b  : ∀ {m} {x : Ordᶜ m} → x ≺ᵛ Ω v → I x
    i-p  : ∀ {m k′} {x : Ordᶜ m} {y : Ordᶜ k′} (σ : Simᴵ k′ m) → I x → I y → I (add x σ y)
    i-g  : ∀ {m n′} {x : Ordᶜ m} {y : Ordᶜ n′} → y ≈ᵛ x → I x → I y
    i-ub : ∀ {m} {x : Ordᶜ m} → I x → x ≺ᵛ Ω (suc v) → x ≺ᵛ lim F
    i-br : ∀ {m} {ξ : Ordᶜ m} → I ξ → ξ ≺ᵛ a → Σ ℕ λ i → ξ ≼ f̂ i
    i-c  : ∀ {u m n′} {ξ : Ordᶜ m} {w : Ordᶜ n′} → (w ≺ᵛ Ω (suc v) → w ≺ᵛ lim F) →
           (q : ξ ≺ᵛ a) → Recₐ a (wf a) u ξ q w → I (forget u) → I ξ → I w

Tchain : ∀ {v k n} {a : Ordᶜ k} {F : ℕ → Ordᶜ n} {lv : ℕ → Ordᴵ} {f̂ : (i : ℕ) → Ordᶜ (lv i)} →
         ΩO v → (∀ i → f̂ i ≼ a) → (s : ∀ i → IsPsi v (f̂ i) (F i)) → (∀ i → F i ≺ᵛ F (suc i)) →
         Bracket {v} a F f̂ → IsPsi v a (lim F)
Tchain {v} {a = a} {F = F} {f̂ = f̂} hO ef s st B =
  sup C.t-lt (λ c b → B.i-ub (J c) b) C.t-cof
  where
  module C = Chain {f̂ = f̂} hO ef s st
  module B = Bracket B
  J : ∀ {m} {x : Ordᶜ m} → C v a x → B.I x
  J = Ind.go B.I B.i-b B.i-p
        (λ {u} {m} {n′} {ξ} {w} q r iu iξ →
           B.i-c (λ bw → let i , e = B.i-br iξ q in C.under (belowᵛ a ξ q) r bw i e) q r iu iξ)
        B.i-g
```

**`Tsup`, `Tlim`.** 不变量取 `BndI`.

```agda
Tsup : ∀ {v k n} {a : Ordᶜ k} {F : ℕ → Ordᶜ n} {lv : ℕ → Ordᴵ} {f̂ : (i : ℕ) → Ordᶜ (lv i)} →
       ΩO v → (∀ i → f̂ i ≼ a) → (s : ∀ i → IsPsi v (f̂ i) (F i)) → (∀ i → F i ≺ᵛ F (suc i)) →
       (∀ {m} {ξ : Ordᶜ m} → BndI v (lim F) ξ → ξ ≺ᵛ a → Σ ℕ λ i → ξ ≼ f̂ i) → IsPsi v a (lim F)
Tsup {v} {a = a} {F = F} {f̂ = f̂} hO ef s st br = Tchain hO ef s st record
  { I    = BndI v (lim F)
  ; i-b  = λ q _ → Chain.t-floor {f̂ = f̂} hO ef s st q
  ; i-p  = Bnd-plus (Chain.t-prin {f̂ = f̂} hO ef s st)
  ; i-g  = Bnd-cg
  ; i-ub = λ i → i
  ; i-br = br
  ; i-c  = λ h _ _ _ _ → h
  }

step-from : ∀ {v k k′ n n′} {x : Ordᶜ k} {y : Ordᶜ k′} {X : Ordᶜ n} {Y : Ordᶜ n′} →
            IsPsi v x X → IsPsi v y Y → x ≺ᵛ y → C v y x → C v y (forget v) → X ≺ᵛ Y
step-from {v} {x = x} {y = y} sx sy q cx cv = ub sy (col cv cx q (irr≡ (wf x) _ sx)) (lt sx)

Tlim : ∀ {v n} {lv : Ordᴵ} {f : ℕ → Ordᶜ lv} {F : ℕ → Ordᶜ n} → ΩO v →
       (s : ∀ i → IsPsi v (f i) (F i)) → (∀ i → f i ≺ᵛ f (suc i)) → (∀ i → C v (f (suc i)) (f i)) →
       (∀ i → C v (f (suc i)) (forget v)) → IsPsi v (lim f) (lim F)
Tlim {f = f} hO s st cf cv =
  Tsup {f̂ = f} hO (λ i → ≼l i (≼-refl (f i))) s (λ i → step-from (s i) (s (suc i)) (st i) (cf i) (cv i))
       (λ _ q → let i , r = ≼lim⁻ q in i , ≺→≼ r)
```
