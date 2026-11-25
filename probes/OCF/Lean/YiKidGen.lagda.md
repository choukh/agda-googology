# 孩子单调: 精简块的违反推广到一切塔项与一切后继孩子

> 验收文件. 判决: 编译定理, 无前提. 对一切 n 与塔第 n+1 项的一切孩子 c″, 记 c = c″+1: 左边取该层的 Ω 树 β 时, 孩子 c+1 的 Ω 树嵌入后的值不高于孩子 c 的某棵树 `Yw` 的 (`inv`), 严格低于 `Yw + 1` 的 (`inv⁺`); 所以任何含 `Yw + 1` 的量化域上 `KidMono` 不成立 (`¬mono`).
> 机制与 YiInv 相同: 孩子 c+1 进孩子 tt 之后的底与孩子 c 的底逐字相同 (`base-same`, `refl`), Ω 树的折叠是孩子 c 一列树的折叠的部分和极限 (`lhs-form`, `refl`), 后继形状的层号上任一这样的极限被一棵同层的树吸收 (`Absorb.absorb`, 对一切层号与底).
> 同一处规范域 `OnlyΩ` 的判据成立: c 的 Ω 树嵌入后的值不高于 c+1 的 (`Ωmono`). 不否定什么: 孩子 c 是零或极限时, 左边不是 β 时, c′ 不是 c+1 时没有结论.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKidGen where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold
open import OCF.Lean.YiRWCheck using (¬◃z)
open import OCF.Lean.YiBRValue using (readRW)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≼-suc; ≅→≼) renaming (+-mono to +ᵛ-mono)
open import OCF.Lean.YiKidCrit
open import OCF.Lean.YiKidRW using (RW; val; suc-strict)
open Crit RW
```

## 第 0 层读回的加法与单调

```agda
read-+ᴿ : (x y : Tr zero) → readRW (x + y) L.≅ (readRW x L.+ readRW y)
read-+ᴿ x zero      = L.≅-refl⁰ (readRW x)
read-+ᴿ x (suc y)   = L.s≅ (read-+ᴿ x y)
read-+ᴿ x (lim f _) = L.l≅ (λ n → read-+ᴿ x (f n))

plus≼ : (a b a′ b′ : Tr zero) → readRW a ≼ readRW a′ → readRW b ≼ readRW b′ → readRW (a + b) ≼ readRW (a′ + b′)
plus≼ a b a′ b′ p q = ≼-trans (≅→≼ (read-+ᴿ a b)) (≼-trans (+ᵛ-mono p q) (≅→≼ (L.≅-sym (read-+ᴿ a′ b′))))

plus≽ : (a b : Tr zero) → readRW b ≼ readRW (a + b)
plus≽ a zero      = z≼
plus≽ a (suc b)   = s≼s (plus≽ a b)
plus≽ a (lim f _) = l≼ (λ n → ≼l n (plus≽ a (f n)))

◃→≼ : {x y : Tr zero} → zero ⊢ x ◃ y → readRW x ≼ readRW y
◃→≼ ◃s       = ≼-suc (≼-refl _)
◃→≼ (◃l n)   = ≼l n (≼-refl _)
◃→≼ (◃t d e) = ≼-trans (◃→≼ d) (◃→≼ e)

iter-mono : (u v : Tr zero) → readRW u ≼ readRW v → (n : ℕ) → readRW (iter (u +_) u n) ≼ readRW (iter (v +_) v n)
iter-mono u v p zero    = p
iter-mono u v p (suc n) = plus≼ u (iter (u +_) u n) v (iter (v +_) v n) p (iter-mono u v p n)

next-mono : (u v : Tr⁺ zero) → readRW (proj₁ u) ≼ readRW (proj₁ v) → readRW (proj₁ (next⁺ u)) ≼ readRW (proj₁ (next⁺ v))
next-mono (u , _) (v , _) p = l≼ (λ n → ≼l n (iter-mono u v p n))
```

## 吸收 (后继形状的层号, 一切底)

层号 `nd sS (λ _ → a)`; `Tw n+1` 是孩子 tt 自身槽位上的 Ω 结点, 第一分支是 `Tw n`, 其余分支 z 是 `Sf n z`. 折叠 `Fd` 朝第 0 层, 路径 `z≤`.

```agda
module Absorb (a : L) (o : Ok (nd sS (λ _ → a))) (B : Base (nd sS (λ _ → a))) (b : Tr⁺ zero)
              (Sf : ℕ → Tr a → Tr (nd sS (λ _ → a))) where

  ℓ : L
  ℓ = nd sS (λ _ → a)

  sel : {A : Set} → Tr a → A → A → A
  sel zero         x y = x
  sel (suc _)      x y = y
  sel (lim _ _)    x y = y
  sel (Ω _ _)      x y = y
  sel (up _ _ _ _) x y = y

  sel-nz : {A : Set} (c : Tr a) (x y : A) → a ⊢ zero ◃ c → sel c x y ≡ y
  sel-nz zero         x y d = ⊥-elim (¬◃z d)
  sel-nz (suc _)      x y d = refl
  sel-nz (lim _ _)    x y d = refl
  sel-nz (Ω _ _)      x y d = refl
  sel-nz (up _ _ _ _) x y d = refl

  Tw : ℕ → Tr ℓ
  Tw zero    = zero
  Tw (suc n) = Ω (inj₂ (tt , inj₁ tt)) (λ c → sel c (Tw n) (Sf n c))

  Yw : Tr ℓ
  Yw = lim Tw (λ n → ◃w)

  Yw-nz : ℓ ⊢ zero ◃ Yw
  Yw-nz = ◃l zero

  Fd : Tr ℓ → Tr⁺ zero
  Fd x = ψ ℓ o B zero (z≤ ℓ) b x

  c₁ : ℕ → Tr⁺ a
  c₁ n = ψ ℓ o B a (inc tt self) (B a (inc tt self)) (Tw n)

  two-rows : ∀ n → readRW (proj₁ (Fd (Tw n)) + proj₁ (Fd (Sf n (proj₁ (c₁ n))))) ≼ readRW (proj₁ (Fd (Tw (suc n))))
  two-rows n = subst (λ t → readRW (proj₁ (Fd (Tw n)) + proj₁ (Fd t)) ≼ readRW (proj₁ (Fd (Tw (suc n)))))
    (sel-nz (proj₁ (c₁ n)) (Tw n) (Sf n (proj₁ (c₁ n))) (proj₂ (c₁ n))) (≼l 1 (≼-refl _))

  module _ (R : ℕ → Tr⁺ zero) (dom : ∀ n c → a ⊢ zero ◃ c → readRW (proj₁ (R n)) ≼ readRW (proj₁ (Fd (Sf n c)))) where

    step : ∀ n → readRW (proj₁ (Fd (Tw n)) + proj₁ (R n)) ≼ readRW (proj₁ (Fd (Tw (suc n))))
    step n = ≼-trans (plus≼ _ _ _ _ (≼-refl _) (dom n (proj₁ (c₁ n)) (proj₂ (c₁ n)))) (two-rows n)

    acc : ∀ n → readRW (cum (λ m → proj₁ (R m)) n) ≼ readRW (proj₁ (Fd (Tw (suc n))))
    acc zero    = ≼-trans (plus≽ (proj₁ (Fd (Tw zero))) (proj₁ (R zero))) (step zero)
    acc (suc n) = ≼-trans (plus≼ (cum (λ m → proj₁ (R m)) n) (proj₁ (R (suc n))) (proj₁ (Fd (Tw (suc n)))) (proj₁ (R (suc n)))
                                 (acc n) (≼-refl _)) (step (suc n))

    absorb : readRW (proj₁ (limc⁺ R)) ≼ readRW (proj₁ (Fd Yw))
    absorb = l≼ (λ n → ≼l (suc n) (acc n))
```

一行 `x + 1` 的折叠不高于 `x + (z+1)` 的 (z 非零): 两边都是 `next⁺`, 右边的底是孩子层从 x 的折叠出发的折叠, 由 `mono` 不低于 x 的折叠.

```agda
  dom₁ : (x : Tr ℓ) (z : Tr a) → a ⊢ zero ◃ z → readRW (proj₁ (Fd (suc x))) ≼ readRW (proj₁ (Fd (up x tt (suc z) (z◃ z ◃s))))
  dom₁ x z d = next-mono (Fd x) (ψ a (proj₂ o tt) Bx zero (z≤ a) (Fd x) z) (◃→≼ (mono a (proj₂ o tt) Bx zero (z≤ a) (Fd x) d))
    where
    Bx : Base a
    Bx i u = ψ ℓ o B i (inc tt u) (B i (inc tt u)) x
```

## 塔第 n+1 项, 左边 β, 孩子 c″+1 与 c″+2

```agda
module Tower (n : ℕ) where
  hn : Tr (tw n) → L
  hn c = tw n ⊕ ↑ (tw n) c

  on : Ok (tw (suc n))
  on = Ok-tw (suc n)

  βn : Tr (tw (suc n))
  βn = proj₁ (Ωt (tw (suc n)))

  Bn : (c : Tr (tw n)) → Base (hn c)
  Bn c i u = ψ (tw (suc n)) on (B₀ (tw (suc n))) i (inc c u) (B₀ (tw (suc n)) i (inc c u)) βn

  bn : Tr⁺ zero
  bn = ψ (tw (suc n)) on (B₀ (tw (suc n))) zero (z≤ (tw (suc n))) (Ωt zero) βn

  base-same : (c : Tr (tw n))
    → (λ i u → ψ (hn (suc c)) (proj₂ on (suc c)) (Bn (suc c)) i (inc tt u) (Bn (suc c) i (inc tt u)) zero) ≡ Bn c
  base-same c = refl

  row : (c : Tr (tw n)) → Tr (hn c) → Tr⁺ zero
  row c z = ψ (hn c) (proj₂ on c) (Bn c) zero (z≤ (hn c)) bn (suc z)

  chain : (c : Tr (tw n)) → Tr (hn c) → Tr (hn c)
  chain c z = proj₁ (ψ (hn (suc c)) (proj₂ on (suc c)) (Bn (suc c)) (hn c) (inc tt self)
                       (Bn (suc c) (hn c) (inc tt self)) (up zero tt (suc z) (z◃ z ◃s)))

  lhs : Tr (tw n) → Tr (tw (suc n))
  lhs c = up βn (suc c) (proj₁ (Ωt (hn (suc c)))) (proj₂ (Ωt (hn (suc c))))

  lhs-form : (c : Tr (tw n)) → ψ₀ (tw (suc n)) on (lhs c) ≡ limc⁺ (λ k → row c (iter (chain c) zero k))
  lhs-form c = refl

  module Kid (c″ : Tr (tw n)) where
    c : Tr (tw n)
    c = suc c″

    zz : ℕ → Tr (hn c)
    zz = iter (chain c) zero

    Sf : ℕ → Tr (hn c″) → Tr (hn c)
    Sf k z = up (zz k) tt (suc z) (z◃ z ◃s)

    open Absorb (hn c″) (proj₂ on c) (Bn c) bn Sf public

    inv : val (tw (suc n)) on (lhs c) ≼ val (tw (suc n)) on (up βn c Yw Yw-nz)
    inv = absorb (λ k → row c (zz k)) (λ k z d → dom₁ (zz k) z d)

    inv⁺ : L.suc (val (tw (suc n)) on (lhs c)) ≼ val (tw (suc n)) on (up βn c (suc Yw) (z◃ Yw ◃s))
    inv⁺ = ≼-trans (s≼s inv) (suc-strict (sΩ (tw n)) hn on βn c Yw Yw-nz)

    ¬mono : (D : Dom) → D (tw (suc n)) on βn c (suc Yw , z◃ Yw ◃s) → KidMono D → ⊥
    ¬mono D d = strict→¬mono D (tw (suc n)) on βn c (suc c) ◃s (suc Yw , z◃ Yw ◃s) d inv⁺
```

同一处的规范域: 孩子 c 自己的 Ω 树嵌入后的值不高于孩子 c+1 的 Ω 树的. 链的第 1 点是 β 折到孩子 c 层的结点的 `next⁺`, 它的第一分支是 "c 的 Ω 树加非零"; 所以 c 的 Ω 树在第一位置序下低于 `zz 1 + 1`, 再用 `mono` 与部分和的第 1 项.

```agda
    Y0 : Tr⁺ zero
    Y0 = ψ (hn zero) (proj₂ on zero) (B₀ (hn zero)) zero (z≤ (hn zero)) (Ωt zero) (proj₁ (Ωt (hn zero)))

    D₁ : hn c ⊢ proj₁ (Ωt (hn c)) ◃ suc (zz 1)
    D₁ = ◃t (+-mono (proj₁ (Ωt (hn c))) (ι-mono (hn c) (proj₂ Y0)))
         (◃t (mono (tw (suc n)) on (B₀ (tw (suc n))) (hn c) (inc (suc c) (inc tt self)) (Ωt (hn c))
                   (◃w {p = inj₁ (inj₁ tt)} {g = λ z → proj₁ (upz z (Ωt (hn z)))}))
             (◃t (◃l 0) ◃s))

    Ωmono : val (tw (suc n)) on (up βn c (proj₁ (Ωt (hn c))) (proj₂ (Ωt (hn c)))) ≼ val (tw (suc n)) on (lhs c)
    Ωmono = ≼l 1 (≼-trans (◃→≼ (mono (hn c) (proj₂ on c) (Bn c) zero (z≤ (hn c)) bn D₁))
                          (plus≽ (proj₁ (row c (zz 0))) (proj₁ (row c (zz 1)))))

    Ωmono-frame : OnlyΩ (tw (suc n)) on βn c (Ωt (hn c))
      × (val (tw (suc n)) on (up βn c (proj₁ (Ωt (hn c))) (proj₂ (Ωt (hn c)))) ≼ val (tw (suc n)) on (lhs c))
    Ωmono-frame = isΩ , Ωmono
```
