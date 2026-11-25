# 空白页候选 B: 值的验收 (判据未成立, 交归约与第一个挡住的引理)

> 验收文件 (读记号). 编译定理: 层 0 的读回 `read`; 目标在层 0 时折叠输出不低于 1 (`nz`, 无前提, 实例 `nz-tB`, `nz-ψΛ`); 一步单调 (`mono-suc` 严格, `mono-lim`, `mono-Ω`); 判据 `Crit` 归约到逐项的界 (`crit-red`). 判据本身未证.
> 第一个挡住的引理是 n = 0 那一项 `Row0` (记号 ψ₀(Ω_Ω+Ω₁) 的参照不高于链的某一项), 它已含 BTBO 一行 (`row0→btbo`). 不否定什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBPAccept where

open import Data.Unit using (tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)

open import OCF.Lean.YiBPBlock
open import OCF.Lean.YiBPFold
open import OCF.Lean.YiBPShape using (A₁; base₁; t1; topB; botB; chB)

open import OCF.Align.EboLeanDef using (HC; h0; h1; hω; fsn; EBOψ; _<ᵀ_; hd<; ar<; tl<; []<)
open import OCF.Align.EboLeanTree using (hc-tower)
open import OCF.Lean.YiRefTw2 using (Rt; hω-inv)
open import OCF.Lean.YiNFO using (mono≤)
open import OCF.Lean.YiNFOCase using (tB; hB; nfB; nbtbo₁)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≼-suc; 𝟏)
```

## 读回

层 z 没有位置也没有孩子, 树只有零, 后继, ℕ 极限.

```agda
read : Tr z → L.Ordᶜ L.zero
read zero       = L.zero
read (suc x)    = L.suc (read x)
read (lim f)    = L.lim (λ n → read (f n))
read (Ω () _)
read (ex _ () _)
```

## 输出不低于 1

目标在层 z 时, 只要底的输出不低于 1, 折叠的输出就不低于 1. 层 z 没有位置, 所以 `cmpT` 不会给 `below`.

```agda
nzΩ : ∀ {X : Set} (c : Cmp z X) (F : X → Tr z) G t₀ → (∀ t → 𝟏 ≼ read (F t)) → 𝟏 ≼ read (ψΩ c F G t₀)
nzΩ (below () _) F G t₀ hF
nzΩ other F G t₀ hF = ≼l 0 (hF t₀)

mutual
  nz : ∀ ℓ (T : Tg ℓ z) (bot : Bot ℓ) → (∀ (T′ : Tg ℓ z) → 𝟏 ≼ read (bot T′)) →
       ∀ w → 𝟏 ≼ read (ψc ℓ T bot w)
  nz ℓ T bot hb zero       = hb T
  nz ℓ T bot hb (suc v)    = ≼l 0 (nz ℓ T bot hb v)
  nz ℓ T bot hb (lim g)    = ≼l 0 (nz ℓ T bot hb (g 0))
  nz ℓ T bot hb (Ω r g)    = nzΩ (cmpT ℓ T r) _ _ _ (λ t → nz ℓ T bot hb (g t))
  nz ℓ T bot hb (ex v a u) = nzx ℓ a (enter ℓ a T) _ (λ T″ → nz ℓ (up ℓ a T″) bot hb v) u

  nzx : ∀ ℓ (a : Ch ℓ) (T : Tg (chAt ℓ a) z) (bot : Bot (chAt ℓ a)) →
        (∀ (T′ : Tg (chAt ℓ a) z) → 𝟏 ≼ read (bot T′)) → ∀ y → 𝟏 ≼ read (ψx ℓ a T bot y)
  nzx z ()
  nzx (μ ⊞ c) (inj₁ a)             T bot hb y = nzx μ a T bot hb y
  nzx (μ ⊞ c) (inj₂ ia)            T bot hb y = nzxI μ c ia T bot hb y
  nzx (l f) (n , a)                T bot hb y = nzx (f n) a T bot hb y
  nzx (Ωₗ μ) (inj₁ a)              T bot hb y = nzx μ a T bot hb y
  nzx (Ωₗ μ) (inj₂ (c , inj₁ _))   T bot hb y = nz (μ ⊞ c) T bot hb y
  nzx (Ωₗ μ) (inj₂ (c , inj₂ ia))  T bot hb y = nzxI μ c ia T bot hb y

  nzxI : ∀ μ c (ia : ChI μ c) (T : Tg (μ ⊞ subC μ c ia) z) (bot : Bot (μ ⊞ subC μ c ia)) →
         (∀ (T′ : Tg (μ ⊞ subC μ c ia) z) → 𝟏 ≼ read (bot T′)) → ∀ y → 𝟏 ≼ read (ψxI μ c ia T bot y)
  nzxI μ (suc c) ia             T bot hb y = nzxI μ c ia T bot hb y
  nzxI μ (lim f) (n , ia)       T bot hb y = nzxI μ (f n) ia T bot hb y
  nzxI μ (Ω q f) (e , inj₁ _)   T bot hb y = nz (μ ⊞ f e) T bot hb y
  nzxI μ (Ω q f) (e , inj₂ ia)  T bot hb y = nzxI μ (f e) ia T bot hb y
  nzxI μ (ex x a′ w) ia         T bot hb y = nzxI μ x ia T bot hb y

nzψ : ∀ ℓ (T : Tg ℓ z) w → 𝟏 ≼ read (ψ ℓ T w)
nzψ ℓ T w = nz ℓ T topB (λ _ → s≼s z≼) w

nz-tB : 𝟏 ≼ read tB′
nz-tB = nzψ (Ωₗ z) (pos (inj₁ (inj₁ tt))) argB

nz-ψΛ : 𝟏 ≼ read ψΛ
nz-ψΛ = nzψ Λ (pos (0 , inj₁ tt)) (top Λ)
```

## 一步单调

沿树自己的构造子: 后继严格上升, ℕ 极限与对角链的每一项都不高于整体. 不是对参数的全序单调.

```agda
≼+ : ∀ (x y : Tr z) → read x ≼ read (x + y)
≼+ x zero    = ≼-refl (read x)
≼+ x (suc y) = ≼-suc (≼+ x y)
≼+ x (lim f) = ≼l 0 (≼+ x (f 0))
≼+ x (Ω () _)
≼+ x (ex _ () _)

≺+ : ∀ (x y : Tr z) → 𝟏 ≼ read y → L.suc (read x) ≼ read (x + y)
≺+ x zero ()
≺+ x (suc y) p      = s≼s (≼+ x y)
≺+ x (lim f) (≼l n p) = ≼l n (≺+ x (f n) p)
≺+ x (Ω () _) p
≺+ x (ex _ () _) p

mono-suc : ∀ ℓ (T : Tg ℓ z) (bot : Bot ℓ) → (∀ (T′ : Tg ℓ z) → 𝟏 ≼ read (bot T′)) →
           ∀ v → L.suc (read (ψc ℓ T bot v)) ≼ read (ψc ℓ T bot (suc v))
mono-suc ℓ T bot hb v = ≼l 1 (≺+ (ψc ℓ T bot v) (ψc ℓ T bot v) (nz ℓ T bot hb v))

mono-lim : ∀ ℓ (T : Tg ℓ z) (bot : Bot ℓ) g n → read (ψc ℓ T bot (g n)) ≼ read (ψc ℓ T bot (lim g))
mono-lim ℓ T bot g n = ≼l n (≼-refl _)

monoΩ : ∀ {X : Set} (c : Cmp z X) (F : X → Tr z) G t₀ n → read (F (itc G t₀ n)) ≼ read (ψΩ c F G t₀)
monoΩ (below () _) F G t₀ n
monoΩ other F G t₀ n = ≼l n (≼-refl _)

mono-Ω : ∀ ℓ (T : Tg ℓ z) (bot : Bot ℓ) r g n →
         read (ψc ℓ T bot (g (itc (λ e → into ℓ r (ψc ℓ (pos r) bot (g e))) (into ℓ r zero) n)))
         ≼ read (ψc ℓ T bot (Ω r g))
mono-Ω ℓ T bot r g n = monoΩ (cmpT ℓ T r) _ _ _ n
```

## 判据与它的归约

`tBₘ m`: 闭项 `tB′` 的第 m 项, 即 ψ₀(Ω_Ω + 链的第 m 项) (读法是判断). 判据归约到: 对记号基本列的每一项, 有链的某一项不低于它.

```agda
tBₘ : ℕ → Tr z
tBₘ m = ψc (z ⊞ suc zero) (pos base₁) botB (embS z zero (chB m))

Crit : Set
Crit = (h : HC tB) → Rt h ≼ read tB′

crit-red : (∀ n → Σ ℕ λ m → (h : HC (fsn tB n)) → Rt h ≼ read (tBₘ m)) → Crit
crit-red r (h0 ())
crit-red r (h1 () _)
crit-red r (hω _ hs) = l≼ (λ n → ≼l (proj₁ (r n)) (proj₂ (r n) (hs n)))
```

第一个挡住的引理: n = 0 的一项 `Row0`. 记号一侧 tB[0] = ψ₀(Ω_Ω+Ω₁), 项序上高于 BTBO 一行 ψ₀(Ω_Ω), 所以 `Row0` 推出 BTBO 一行 (`row0→btbo`, 用 `YiNFO.mono≤`).

```agda
Row0 : Set
Row0 = Σ ℕ λ m → (h : HC (fsn tB 0)) → Rt h ≼ read (tBₘ m)
```

```agda
btbo<B₀ : EBOψ 2 <ᵀ fsn tB 0
btbo<B₀ = hd< (ar< (tl< []<))

row0→btbo : Row0 → Σ ℕ λ m → Rt (hc-tower 2) ≼ read (tBₘ m)
row0→btbo (m , r) = m , ≼-trans (mono≤ nbtbo₁ (nfB 0) (hc-tower 2) h₀ (inj₁ btbo<B₀)) (r h₀)
  where
  h₀ : HC (fsn tB 0)
  h₀ = hω-inv hB refl 0
```
