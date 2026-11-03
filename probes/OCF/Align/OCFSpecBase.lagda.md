# 折叠的外部规格: 闭包与严格上确界 (底座)

> 底座, 不含记号. 结论写在 [OCFSpec](OCFSpec.lagda.md). 这里定义值序 `≼` (与 [Value](Value.lagda.md) §1 的构造子逐字相同, 重写一遍是为了不经它导入记号), 闭包 `Cl₊`, 规格 `IsPsi`, 并证明规格只依赖值: 单调, 唯一, 对 $a$ 与 $t$ 都不变.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OCFSpecBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst; subst₂; trans)

open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.Level
```

## §1 值序

`≼` 与 Value 相同. `x ≺ᵛ y` 是 `suc x ≼ y`.

```agda
infix 4 _≼_ _≈ᵛ_ _≺ᵛ_

data _≼_ : ∀ {ℓ₁ ℓ₂} → Ordᶜ ℓ₁ → Ordᶜ ℓ₂ → Set where
  z≼  : ∀ {ℓ₁ ℓ₂} {b : Ordᶜ ℓ₂} → 𝟎 {ℓ₁} ≼ b
  s≼s : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≼ b → suc a ≼ suc b
  ≼l  : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {f : ℕ → Ordᶜ ℓ₂} n → a ≼ f n → a ≼ lim f
  l≼  : ∀ {ℓ₁ ℓ₂} {f : ℕ → Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → (∀ n → f n ≼ b) → lim f ≼ b
  ≼i  : ∀ {ℓ₁ ℓ₂ j} {a : Ordᶜ ℓ₁} {p : j <ᴵ ℓ₂} {f : U j (<→◃ p) → Ordᶜ ℓ₂}
        (x : Ordᶜ j) → x ≅ x → a ≼ f (into (<→◃ p) x) → a ≼ limᵢ p f
  i≼  : ∀ {ℓ₁ ℓ₂ j} {p : j <ᴵ ℓ₁} {f : U j (<→◃ p) → Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} →
        (∀ (x : Ordᶜ j) → x ≅ x → f (into (<→◃ p) x) ≼ b) → limᵢ p f ≼ b
  ≼u  : ∀ {ℓ₁ ℓ₂ k} {a : Ordᶜ ℓ₁} {r : k ◃₁ ℓ₂} {y : U k (◃₁→◃ r)} → a ≼ out (◃₁→◃ r) y → a ≼ up r y
  u≼  : ∀ {ℓ₁ ℓ₂ k} {r : k ◃₁ ℓ₁} {y : U k (◃₁→◃ r)} {b : Ordᶜ ℓ₂} → out (◃₁→◃ r) y ≼ b → up r y ≼ b

≼-refl : ∀ {ℓ} (a : Ordᶜ ℓ) → a ≼ a
≼-refl zero            = z≼
≼-refl (suc a)         = s≼s (≼-refl a)
≼-refl (lim f)         = l≼ (λ n → ≼l n (≼-refl (f n)))
≼-refl (limᵢ p f)      = i≼ (λ x ex → ≼i x ex (≼-refl (f (into (<→◃ p) x))))
≼-refl (up zero y)     = u≼ (≼u (≼-refl y))
≼-refl (up (self n) y) = u≼ (≼u (≼-refl y))

≼-trans : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} {c : Ordᶜ ℓ₃} → a ≼ b → b ≼ c → a ≼ c
≼-trans z≼          q           = z≼
≼-trans p           (≼l n q)    = ≼l n (≼-trans p q)
≼-trans p           (≼i x ex q) = ≼i x ex (≼-trans p q)
≼-trans p           (≼u q)      = ≼u (≼-trans p q)
≼-trans (l≼ p)      q           = l≼ (λ n → ≼-trans (p n) q)
≼-trans (i≼ p)      q           = i≼ (λ x ex → ≼-trans (p x ex) q)
≼-trans (u≼ p)      q           = u≼ (≼-trans p q)
≼-trans (s≼s p)     (s≼s q)     = s≼s (≼-trans p q)
≼-trans (≼l n p)    (l≼ q)      = ≼-trans p (q n)
≼-trans (≼i x ex p) (i≼ q)      = ≼-trans p (q x ex)
≼-trans (≼u p)      (u≼ q)      = ≼-trans p q

_≈ᵛ_ : ∀ {ℓ₁ ℓ₂} → Ordᶜ ℓ₁ → Ordᶜ ℓ₂ → Set
a ≈ᵛ b = a ≼ b × b ≼ a

_≺ᵛ_ : ∀ {ℓ₁ ℓ₂} → Ordᶜ ℓ₁ → Ordᶜ ℓ₂ → Set
a ≺ᵛ b = suc a ≼ b

≼-suc : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≼ b → a ≼ suc b
≼-suc z≼                          = z≼
≼-suc (s≼s p)                     = s≼s (≼-suc p)
≼-suc (≼l {f = f} n p)            = ≼-trans (≼-suc p) (s≼s (≼l n (≼-refl (f n))))
≼-suc (l≼ p)                      = l≼ (λ n → ≼-suc (p n))
≼-suc (≼i {p = q} {f = f} x ex p) = ≼-trans (≼-suc p) (s≼s (≼i x ex (≼-refl (f (into (<→◃ q) x)))))
≼-suc (i≼ p)                      = i≼ (λ x ex → ≼-suc (p x ex))
≼-suc (≼u {r = r} {y = y} p)      = ≼-trans (≼-suc p) (s≼s (≼u (≼-refl (out (◃₁→◃ r) y))))
≼-suc (u≼ p)                      = u≼ (≼-suc p)

≼-self-suc : ∀ {ℓ} (a : Ordᶜ ℓ) → a ≼ suc a
≼-self-suc a = ≼-suc (≼-refl a)

≺→≼ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≺ᵛ b → a ≼ b
≺→≼ p = ≼-trans (≼-self-suc _) p

s≼s⁻ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → suc a ≼ suc b → a ≼ b
s≼s⁻ (s≼s p) = p

≼lim⁻ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {f : ℕ → Ordᶜ ℓ₂} → suc a ≼ lim f → Σ ℕ (λ n → suc a ≼ f n)
≼lim⁻ (≼l n p) = n , p

≺-≼ : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} {c : Ordᶜ ℓ₃} → a ≺ᵛ b → b ≼ c → a ≺ᵛ c
≺-≼ = ≼-trans

≼-≺ : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} {c : Ordᶜ ℓ₃} → a ≼ b → b ≺ᵛ c → a ≺ᵛ c
≼-≺ p q = ≼-trans (s≼s p) q

≅→≼ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≅ b → a ≼ b
≅→≼ z≅      = z≼
≅→≼ (s≅ e)  = s≼s (≅→≼ e)
≅→≼ (l≅ h)  = l≼ (λ n → ≼l n (≅→≼ (h n)))
≅→≼ (lᵢ≅ {p = p} e h) =
  i≼ (λ x ex → ≼i (tr e x) (tr-≅ e (≅-tr e ex)) (≅→≼ (h x (tr e x) (≅→R (<→◃ p) (≅-tr e ex)))))
≅→≼ (upˡ {r = zero} e)   = u≼ (≅→≼ e)
≅→≼ (upˡ {r = self n} e) = u≼ (≅→≼ e)
≅→≼ (upʳ {r = zero} e)   = ≼u (≅→≼ e)
≅→≼ (upʳ {r = self n} e) = ≼u (≅→≼ e)

≅→≈ᵛ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≅ b → a ≈ᵛ b
≅→≈ᵛ e = ≅→≼ e , ≅→≼ (≅-sym e)
```

## §2 $\prec^\mathsf{v}$ 良基

值的递归不是结构的, 所以规格的递归走 `Acc`. 证明对树递归. 没有用 `≅`.

```agda
data Acc {k} (a : Ordᶜ k) : Set where
  acc : (∀ {m} (ξ : Ordᶜ m) → ξ ≺ᵛ a → Acc ξ) → Acc a

acc-≼ : ∀ {k m} {x : Ordᶜ k} {y : Ordᶜ m} → x ≼ y → Acc y → Acc x
acc-≼ p (acc h) = acc (λ ξ q → h ξ (≼-trans q p))

wf    : ∀ {k} (a : Ordᶜ k) → Acc a
belowᵛ : ∀ {k} (a : Ordᶜ k) → ∀ {m} (ξ : Ordᶜ m) → ξ ≺ᵛ a → Acc ξ
wf a = acc (belowᵛ a)
belowᵛ (suc b)         ξ (s≼s p)   = acc-≼ p (wf b)
belowᵛ (lim f)         ξ (≼l n q)  = belowᵛ (f n) ξ q
belowᵛ (limᵢ p f)      ξ (≼i x e q) = belowᵛ (f (into (<→◃ p) x)) ξ q
belowᵛ (up zero y)     ξ (≼u q)    = belowᵛ y ξ q
belowᵛ (up (self n) y) ξ (≼u q)    = belowᵛ y ξ q

≺ᵛ-irrefl : ∀ {k} (a : Ordᶜ k) → ¬ (a ≺ᵛ a)
≺ᵛ-irrefl a = go (wf a) where
  go : ∀ {k} {a : Ordᶜ k} → Acc a → ¬ (a ≺ᵛ a)
  go {a = a} (acc h) q = go (h a q) q
```

## §3 闭包与规格

Buchholz 的定义是: $C_v(a)$ 是含 $\Omega_v$ 以下全部序数, 对 $+$ 与 $(u,\xi)\mapsto\psi_u(\xi)$ ($u,\xi\in C$, $\xi<a$) 封闭的最小集, $\psi_v(a)=\min$ 补集. 这里逐条写成树上的归纳谓词. **`Rec` 是 $\psi_u(\xi)$ 的取值**, 不是折叠: 规格里没有折叠.

`cong` 使 `Cl₊` 只依赖值. 没有项文法: 成员是树, 闭包的条件都用值序说.

```agda
module _ (v : Ordᴵ) {k} (a : Ordᶜ k)
         (Rec : (u : Ordᴵ) → ∀ {m} (ξ : Ordᶜ m) → ξ ≺ᵛ a → ∀ {n} → Ordᶜ n → Set) where
  data Cl₊ : ∀ {m} → Ordᶜ m → Set where
    base : ∀ {m} {x : Ordᶜ m} → x ≺ᵛ Ω v → Cl₊ x
    plus : ∀ {m k′} {x : Ordᶜ m} {y : Ordᶜ k′} (σ : Simᴵ k′ m) → Cl₊ x → Cl₊ y → Cl₊ (add x σ y)
    col  : ∀ {u m n} {ξ : Ordᶜ m} {x : Ordᶜ n} → Cl₊ (forget u) → Cl₊ ξ → (q : ξ ≺ᵛ a) → Rec u ξ q x → Cl₊ x
    cg   : ∀ {m n} {x : Ordᶜ m} {y : Ordᶜ n} → y ≈ᵛ x → Cl₊ x → Cl₊ y
```

**规格的形状.** "$t$ 是 $C$ 外最小的" 有两个直接的构造性写法, 都不对 ([OCFSpecNeg](OCFSpecNeg.lagda.md) 有编译的否定):

- "$t$ 以下全在 $C$ 里" 对 $v=0$, $t\ge2$ 就推出 LPO (`naive→LPO`): $y=\lim_n[\mathsf{any}_\alpha(n)]$ 在 $2$ 以下, 而 $C$ 的成员都能判定是 $0$ 还是 $\ge 1$.
- "$C$ 的成员都与 $t$ 可比" 对 $v=1$ 也推出 LPO (`gap→LPO`): 任何可数层 $u$ 都在 $C_1$ 的基底里, 所以 $\Omega_u\in C_1(1)$, 而 $\Omega_{1+\lim[\mathsf{any}_\alpha]}$ 与 $\psi_1(1)$ 比较就判定了 $\alpha$.

Buchholz 的定理 $C_v(a)\cap\Omega_{v+1}=\psi_v(a)$ 说 $\psi_v(a)$ 也是 $C_v(a)\cap\Omega_{v+1}$ 的**严格上确界**. 这个说法没有判定, 所以取它作规格: 三个字段 `lt`, `ub` (上界, 严格), `cof` (共尾). 共尾的见证取在第 $v$ 层, 这样两个见证能相加 (经典地 $\Omega_{v+1}$ 以下的值都有第 $v$ 层的树). 由 `ub` 得 $t\notin C$ (`¬in`). 经典地它与 "$C$ 外最小" 等价 (纸面, 用 Buchholz 的定理). 比较只出现在陈述里, 从不判定, 也不进定义.

```agda
record Wit (v : Ordᴵ) (S : ∀ {m} → Ordᶜ m → Set) {n} (y : Ordᶜ n) : Set where
  constructor wit
  field
    {pt} : Ordᶜ v
    mem  : S pt
    bd   : pt ≺ᵛ Ω (suc v)
    dom  : y ≼ pt

record Sup (v : Ordᴵ) (S : ∀ {m} → Ordᶜ m → Set) {n} (t : Ordᶜ n) : Set where
  constructor sup
  field
    lt  : t ≺ᵛ Ω (suc v)
    ub  : ∀ {m} {x : Ordᶜ m} → S x → x ≺ᵛ Ω (suc v) → x ≺ᵛ t
    cof : ∀ {m} {y : Ordᶜ m} → y ≺ᵛ t → Wit v S y
open Sup public
open Wit public

IsPsiₐ : (v : Ordᴵ) → ∀ {k} (a : Ordᶜ k) → Acc a → ∀ {n} → Ordᶜ n → Set
IsPsiₐ v a (acc h) t = Sup v (Cl₊ v a (λ u ξ q x → IsPsiₐ u ξ (h ξ q) x)) t

Recₐ : ∀ {k} (a : Ordᶜ k) → Acc a → (u : Ordᴵ) → ∀ {m} (ξ : Ordᶜ m) → ξ ≺ᵛ a → ∀ {n} → Ordᶜ n → Set
Recₐ a (acc h) u ξ q x = IsPsiₐ u ξ (h ξ q) x

C : (v : Ordᴵ) → ∀ {k} (a : Ordᶜ k) → ∀ {m} → Ordᶜ m → Set
C v a = Cl₊ v a (Recₐ a (wf a))

IsPsi : (v : Ordᴵ) → ∀ {k} (a : Ordᶜ k) → ∀ {n} → Ordᶜ n → Set
IsPsi v a t = IsPsiₐ v a (wf a) t
```

`IsPsi v a t` 只说 $t$ 的值. 下面证这件事: 规格对 $a$ 的值不变 (`IsPsi-a`), 对 $t$ 的值不变 (`IsPsi-t`), `Acc` 的选择无关.

```agda
Cl-map : ∀ {v v′ k k′} {a : Ordᶜ k} {a′ : Ordᶜ k′}
         {R : (u : Ordᴵ) → ∀ {m} (ξ : Ordᶜ m) → ξ ≺ᵛ a → ∀ {n} → Ordᶜ n → Set}
         {R′ : (u : Ordᴵ) → ∀ {m} (ξ : Ordᶜ m) → ξ ≺ᵛ a′ → ∀ {n} → Ordᶜ n → Set} →
         Ω v ≼ Ω v′ → (ea : a ≼ a′) →
         (∀ u {m} (ξ : Ordᶜ m) (q : ξ ≺ᵛ a) {n} (x : Ordᶜ n) → R u ξ q x → R′ u ξ (≼-trans q ea) x) →
         ∀ {m} {x : Ordᶜ m} → Cl₊ v a R x → Cl₊ v′ a′ R′ x
Cl-map ev ea rr (base q)      = base (≼-trans q ev)
Cl-map ev ea rr (plus σ c d)  = plus σ (Cl-map ev ea rr c) (Cl-map ev ea rr d)
Cl-map ev ea rr (col cu cξ q r) = col (Cl-map ev ea rr cu) (Cl-map ev ea rr cξ) (≼-trans q ea) (rr _ _ q _ r)
Cl-map ev ea rr (cg e c)      = cg e (Cl-map ev ea rr c)

Sup-map : ∀ {v} {S S′ : ∀ {m} → Ordᶜ m → Set} {n} {t : Ordᶜ n} →
          (∀ {m} {x : Ordᶜ m} → S x → S′ x) → (∀ {m} {x : Ordᶜ m} → S′ x → S x) → Sup v S t → Sup v S′ t
Sup-map f g (sup l u c) = sup l (λ s b → u (g s) b) (λ q → let w = c q in wit (f (mem w)) (bd w) (dom w))

irr : ∀ {v k k′} {a : Ordᶜ k} {a′ : Ordᶜ k′} (ac : Acc a) (ac′ : Acc a′) → a ≈ᵛ a′ →
      ∀ {n} {t : Ordᶜ n} → IsPsiₐ v a ac t → IsPsiₐ v a′ ac′ t
irr (acc h) (acc h′) (e , e′) =
  Sup-map (Cl-map (≼-refl _) e (λ u ξ q x r → irr (h ξ q) (h′ ξ (≼-trans q e)) (≼-refl _ , ≼-refl _) r))
          (Cl-map (≼-refl _) e′ (λ u ξ q x r → irr (h′ ξ q) (h ξ (≼-trans q e′)) (≼-refl _ , ≼-refl _) r))

irr≡ : ∀ {v k} {a : Ordᶜ k} (ac : Acc a) (ac′ : Acc a) → ∀ {n} {t : Ordᶜ n} → IsPsiₐ v a ac t → IsPsiₐ v a ac′ t
irr≡ {a = a} ac ac′ = irr ac ac′ (≼-refl a , ≼-refl a)

IsPsi-a : ∀ {v k k′} {a : Ordᶜ k} {a′ : Ordᶜ k′} → a ≈ᵛ a′ → ∀ {n} {t : Ordᶜ n} → IsPsi v a t → IsPsi v a′ t
IsPsi-a {a = a} {a′ = a′} e = irr (wf a) (wf a′) e

Cₐ-map : ∀ {v v′ k k′} {a : Ordᶜ k} {a′ : Ordᶜ k′} (ac : Acc a) (ac′ : Acc a′) →
         Ω v ≼ Ω v′ → a ≼ a′ → ∀ {m} {x : Ordᶜ m} →
         Cl₊ v a (Recₐ a ac) x → Cl₊ v′ a′ (Recₐ a′ ac′) x
Cₐ-map (acc h) (acc h′) ev ea = Cl-map ev ea (λ u ξ q x r → irr≡ (h ξ q) (h′ ξ (≼-trans q ea)) r)

C-map : ∀ {v v′ k k′} {a : Ordᶜ k} {a′ : Ordᶜ k′} → Ω v ≼ Ω v′ → a ≼ a′ → ∀ {m} {x : Ordᶜ m} → C v a x → C v′ a′ x
C-map {a = a} {a′ = a′} = Cₐ-map (wf a) (wf a′)

C-a : ∀ {v k k′} {a : Ordᶜ k} {a′ : Ordᶜ k′} → a ≼ a′ → ∀ {m} {x : Ordᶜ m} → C v a x → C v a′ x
C-a = C-map (≼-refl _)

Sup-t : ∀ {v} {S : ∀ {m} → Ordᶜ m → Set} {n n′} {t : Ordᶜ n} {t′ : Ordᶜ n′} → t ≈ᵛ t′ → Sup v S t → Sup v S t′
Sup-t (e , e′) (sup l u c) = sup (≼-≺ e′ l) (λ s b → ≺-≼ (u s b) e) (λ q → c (≺-≼ q e′))

IsPsi-t : ∀ {v k} {a : Ordᶜ k} {n n′} {t : Ordᶜ n} {t′ : Ordᶜ n′} → t ≈ᵛ t′ → IsPsi v a t → IsPsi v a t′
IsPsi-t = Sup-t
```

## §4 由规格得到的性质

- `below→≼`: 值序由严格前驱决定.
- `Sup-≼`, `IsPsi-uniq`: 同一个闭包的严格上确界只有一个值.
- `ψ̂-mono`: 规格给出的值对 $a$ 单调. 不要求 $a$ 是标准形. 这是规格本身的定理, 与折叠无关.
- `¬in`: $t\notin C_v(a)$.

```agda
below→≼ : ∀ {n n′} (t : Ordᶜ n) {t′ : Ordᶜ n′} → (∀ {m} {y : Ordᶜ m} → y ≺ᵛ t → y ≺ᵛ t′) → t ≼ t′
below→≼ zero h = z≼
below→≼ (suc c) h = h (≼-refl (suc c))
below→≼ (lim g) h = l≼ (λ n → below→≼ (g n) (λ q → h (≼l n q)))
below→≼ (limᵢ p g) h = i≼ (λ x ex → below→≼ (g (into (<→◃ p) x)) (λ q → h (≼i x ex q)))
below→≼ (up zero y) h = u≼ (below→≼ y (λ q → h (≼u q)))
below→≼ (up (self n) y) h = u≼ (below→≼ y (λ q → h (≼u q)))

Sup-≼ : ∀ {v v′} {S S′ : ∀ {m} → Ordᶜ m → Set} {n n′} {t : Ordᶜ n} {t′ : Ordᶜ n′} →
        (∀ {m} {x : Ordᶜ m} → S x → S′ x) → (∀ {m} {x : Ordᶜ m} → S x → x ≺ᵛ Ω (suc v) → x ≺ᵛ Ω (suc v′)) →
        Sup v S t → Sup v′ S′ t′ → t ≼ t′
Sup-≼ {t = t} f b s s′ = below→≼ t (λ q → let w = cof s q in ≼-≺ (dom w) (ub s′ (f (mem w)) (b (mem w) (bd w))))

IsPsiₐ-uniq : ∀ {v k k′} {a : Ordᶜ k} {a′ : Ordᶜ k′} (ac : Acc a) (ac′ : Acc a′) → a ≼ a′ →
              ∀ {n n′} {t : Ordᶜ n} {t′ : Ordᶜ n′} → IsPsiₐ v a ac t → IsPsiₐ v a′ ac′ t′ → t ≼ t′
IsPsiₐ-uniq (acc h) (acc h′) e =
  Sup-≼ (Cl-map (≼-refl _) e (λ u ξ q x r → irr≡ (h ξ q) (h′ ξ (≼-trans q e)) r)) (λ _ b → b)

IsPsi-mono : ∀ {v k k′} {a : Ordᶜ k} {a′ : Ordᶜ k′} → a ≼ a′ → ∀ {n n′} {t : Ordᶜ n} {t′ : Ordᶜ n′} →
             IsPsi v a t → IsPsi v a′ t′ → t ≼ t′
IsPsi-mono {a = a} {a′ = a′} = IsPsiₐ-uniq (wf a) (wf a′)

IsPsi-uniq : ∀ {v k} {a : Ordᶜ k} {n n′} {t : Ordᶜ n} {t′ : Ordᶜ n′} → IsPsi v a t → IsPsi v a t′ → t ≈ᵛ t′
IsPsi-uniq {a = a} p q = IsPsi-mono (≼-refl a) p q , IsPsi-mono (≼-refl a) q p

¬in : ∀ {v k} {a : Ordᶜ k} {n} {t : Ordᶜ n} → IsPsi v a t → ¬ (C v a t)
¬in {t = t} s c = ≺ᵛ-irrefl t (ub s c (lt s))
```

`ψ̂-mono` 跨下标: $\Omega_u\preccurlyeq\Omega_v$ 时 $\psi_u$ 的值在 $\psi_v$ 的值之下. 要 `w ≺ Ω (suc v)`, 这是调用处的前提.

```agda
ψ̂-mono : ∀ {u v k k′} {ξ : Ordᶜ k} {a : Ordᶜ k′} (ac : Acc ξ) (ac′ : Acc a) → Ω u ≼ Ω v → ξ ≼ a →
         ∀ {n n′} {w : Ordᶜ n} {t : Ordᶜ n′} → IsPsiₐ u ξ ac w → IsPsiₐ v a ac′ t → w ≺ᵛ Ω (suc v) → w ≼ t
ψ̂-mono {u = u} {v = v} (acc h) (acc h′) ev e {w = w} {t = t} s s′ bw =
  below→≼ w (λ q → let wt = cof s q ; pw = ub s (mem wt) (bd wt) in
    ≼-≺ (dom wt) (ub s′ (Cl-map ev e (λ u′ ξ′ q′ x r → irr≡ (h ξ′ q′) (h′ ξ′ (≼-trans q′ e)) r) (mem wt)) (≼-≺ (≺→≼ pw) bw)))
```

## §5 值上的加法

对一切层. 与 `≼` 的跨层形状一致: 左右的层可以不同.

```agda
coe-into : ∀ {i ℓ₁ ℓ₂} (r : i ◃ ℓ₁) (r′ : i ◃ ℓ₂) (x : Ordᶜ i) → coe r r′ (into r x) ≡ into r′ x
coe-into r r′ x = cong (into r′) (out-into r x)

add-≽ˡ : ∀ {k ℓ} (a : Ordᶜ ℓ) (σ : Simᴵ k ℓ) (b : Ordᶜ k) → a ≼ add a σ b
add-≽ˡ a σ zero    = ≼-refl a
add-≽ˡ a σ (suc b) = ≼-suc (add-≽ˡ a σ b)
add-≽ˡ a σ (lim f) = ≼l 0 (add-≽ˡ a σ (f 0))
add-≽ˡ a σ (limᵢ q f) = ≼i zero z≅ (add-≽ˡ a σ _)
add-≽ˡ a σ (up zero x)     = add-≽ˡ a _ x
add-≽ˡ a σ (up (self n) x) = add-≽ˡ a _ x

add-≽ʳ : ∀ {k ℓ} (a : Ordᶜ ℓ) (σ : Simᴵ k ℓ) (b : Ordᶜ k) → b ≼ add a σ b
add-≽ʳ a σ zero    = z≼
add-≽ʳ a σ (suc b) = s≼s (add-≽ʳ a σ b)
add-≽ʳ a σ (lim f) = l≼ (λ n → ≼l n (add-≽ʳ a σ (f n)))
add-≽ʳ a σ (limᵢ q f) = i≼ (λ x ex → ≼i x ex
  (subst (λ w → f (into (<→◃ q) x) ≼ add a σ (f w)) (sym (coe-into (<→◃ (σ q)) (<→◃ q) x)) (add-≽ʳ a σ (f (into (<→◃ q) x)))))
add-≽ʳ a σ (up zero x)     = u≼ (add-≽ʳ a _ x)
add-≽ʳ a σ (up (self n) x) = u≼ (add-≽ʳ a _ x)

add-mono : ∀ {k k′ ℓ ℓ′} {a : Ordᶜ ℓ} {a′ : Ordᶜ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} {b : Ordᶜ k} {b′ : Ordᶜ k′} →
           a ≼ a′ → b ≼ b′ → add a σ b ≼ add a′ σ′ b′
add-mono {a′ = a′} {σ′ = σ′} {b′ = b′} pa z≼ = ≼-trans pa (add-≽ˡ a′ σ′ b′)
add-mono pa (s≼s q)  = s≼s (add-mono pa q)
add-mono pa (≼l n q) = ≼l n (add-mono pa q)
add-mono pa (l≼ h)   = l≼ (λ n → add-mono pa (h n))
add-mono {a = a} {a′ = a′} {σ = σ} {σ′ = σ′} {b = b} pa (≼i {p = p} {f = f} x ex q) =
  ≼i x ex (subst (λ w → add a σ b ≼ add a′ σ′ (f w)) (sym (coe-into (<→◃ (σ′ p)) (<→◃ p) x)) (add-mono pa q))
add-mono {a = a} {a′ = a′} {σ = σ} {σ′ = σ′} {b′ = b′} pa (i≼ {p = p} {f = f} h) =
  i≼ (λ x ex → subst (λ w → add a σ (f w) ≼ add a′ σ′ b′) (sym (coe-into (<→◃ (σ p)) (<→◃ p) x)) (add-mono pa (h x ex)))
add-mono {σ′ = σ′} pa (≼u {r = zero} q)   = add-mono {σ′ = λ q → σ′ (suc q)} pa q
add-mono {σ′ = σ′} pa (≼u {r = self n} q) = add-mono {σ′ = λ q → σ′ (lim n q)} pa q
add-mono {σ = σ} pa (u≼ {r = zero} q)   = add-mono {σ = λ q → σ (suc q)} pa q
add-mono {σ = σ} pa (u≼ {r = self n} q) = add-mono {σ = λ q → σ (lim n q)} pa q

+-mono : ∀ {ℓ ℓ′} {a b : Ordᶜ ℓ} {a′ b′ : Ordᶜ ℓ′} → a ≼ a′ → b ≼ b′ → a + b ≼ a′ + b′
+-mono = add-mono

+-≽ˡ : ∀ {ℓ} (a b : Ordᶜ ℓ) → a ≼ a + b
+-≽ˡ a b = add-≽ˡ a (λ q → q) b

+-≽ʳ : ∀ {ℓ} (a b : Ordᶜ ℓ) → b ≼ a + b
+-≽ʳ a b = add-≽ʳ a (λ q → q) b
```

结合律, 只要一个方向. 对右参数 $c$ 递归, `limᵢ` 处两层 `coe`.

```agda
+-assoc : ∀ {k ℓ} (a b : Ordᶜ ℓ) (σ : Simᴵ k ℓ) (c : Ordᶜ k) → add (a + b) σ c ≼ a + add b σ c
+-assoc a b σ zero    = ≼-refl _
+-assoc a b σ (suc c) = s≼s (+-assoc a b σ c)
+-assoc a b σ (lim f) = l≼ (λ n → ≼l n (+-assoc a b σ (f n)))
+-assoc a b σ (limᵢ q f) = i≼ (λ x ex → ≼i x ex
  (subst₂ (λ u w → add (a + b) σ (f u) ≼ a + add b σ (f w))
          (sym (coe-into (<→◃ (σ q)) (<→◃ q) x))
          (sym (trans (cong (coe (<→◃ (σ q)) (<→◃ q)) (coe-into (<→◃ (σ q)) (<→◃ (σ q)) x)) (coe-into (<→◃ (σ q)) (<→◃ q) x)))
          (+-assoc a b σ (f (into (<→◃ q) x)))))
+-assoc a b σ (up zero x)     = +-assoc a b _ x
+-assoc a b σ (up (self n) x) = +-assoc a b _ x
```
