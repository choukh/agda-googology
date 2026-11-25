# YiBtVal：新折叠的闭项在一切合法层号上的值下界

**验收文件，档位：编译定理 (下界，不是同值)。** `interfaceᴮ : ∀ M → YiRawValBase.Interface M`，所以 `closedᵐ (fin n)`, `closed (fin n)` 对一切 `n` 不低于参照的 ψ₀(Ω_n)。
`lower-any`：对一切 `Plain`, `Legal` 的层号 `K` 与结构对应的参照层号 `κ` (另要 `Zs κ`)，`closedᵐ K`, `closed K` 不低于 ψ₀(Ω_κ)；含极限的层号经极限层号上 `top` 的部分和一行。
实例：ψ₀(Ω_ω), ψ₀(Ω_{ω+n})。被验收的是 [YiRawFoldInst](YiRawFoldInst.lagda.md) 的 `closed`, `closedᵐ`。没有上界，没有 Funext。主引理在 [YiBtValFold](YiBtValFold.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiBtValFin where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import OCF.Align.RR5IrrCore as B
open B using (module G; LF; Raw)
open import OCF.Align.RR5IrrCheck using (cO)
open import OCF.Align.YiIrrIf using (R; Legal; iterate; self)
open import OCF.Align.YiIrrFbIf using (Pt; pt) renaming (at to atᵖ)
open import OCF.Align.YiLvIf using (Plain)
open import OCF.Align.YiLvFoldFin using (fin; fin-plain; fin-legal; ω; ω-plain; ω-legal)
open import OCF.Align.YiRawIf using (dispatch; base)
open import OCF.Align.YiRawFoldBase using (Ext; low; mix; inS; NdR; Ψn; psum)
import OCF.Align.YiRawFold as N
open import OCF.Align.YiLvFoldBase using (fold)
open import OCF.Align.YiRawFoldInst using (closed; closedᵐ; ω+; ω+-plain; ω+-legal; Ωω+1; Ωω+2)
open import OCF.Align.YiIrrFoldValue using (read)
open import OCF.Align.YiLvValBase using (⟨_⟩; plus≽; suc-lower)
open import OCF.Align.YiRawValBase using (Interface; module FromInterface)
open import OCF.Align.YiLvAll using (z<M)
open import OCF.Align.YiLvAllRel using (un0)
open import OCF.Align.YiBtValRel using (RelF; Corr; cz; cs; cl; START)
open import OCF.Align.YiBtValAdd using (ABSORB)
open import OCF.Align.YiBtValAdm using (module CPClass; natC; ωp; ωC; toIL; toIL-c)
import OCF.Align.Level as L
import OCF.Align.Value as V
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open V using (_≼_; ≼-refl; ≼-trans; ≅→≼; ≼l; l≼)
```

## 1 目标第 0 层的派发总是完全的；参照层号含字面的零

```agda
cmp0 : ∀ {k} (y : Ext B.zero k) → N.Complete y
cmp0 y r (() , _)

Zs : L.Ordᴵ → Set
Zs L.zero = ⊤
Zs (L.suc a) = L.zero L.<ᴵ L.suc a
Zs (L.lim g s) = ∀ n → Zs (g n)

ZsN : ∀ n → Zs (L.natᴵ n)
ZsN zero = tt
ZsN (suc n) = z<M n

zW : ∀ n → L.zero L.<ᴵ ωp n
zW zero = L.lim 1 L.zero
zW (suc n) = L.suc (zW n)

ZsW : ∀ n → Zs (ωp n)
ZsW zero = ZsN
ZsW (suc n) = L.suc (zW n)
```

## 2 一切有限层号：`YiRawValBase` 的接口

```agda
interfaceᴮ : ∀ M → Interface M
interfaceᴮ M = record
  { Rel = λ x η → RelF (fin M) x η
  ; start = START (fin M) (natC M)
  ; step = λ r l nb →
      FOLD (fin M) self (fin-plain M) (fin-legal M) (fin M) self
        (N.ownT (fin M) (fin-plain M) (fin-legal M)) (N.complete-ownT (fin M) (fin-plain M) (fin-legal M))
        r (natC M) L.zero (λ q → L.suc q) l nb
  ; absorb = λ θ r → ABSORB (fin M) θ r
  ; lower = λ y r s l nb →
      ≼-trans (≅→≼ (L.ψ⁰≅ψ {p = z<M M} {σ = λ q → L.suc q} s))
        (un0 (FOLD (fin M) self (fin-plain M) (fin-legal M) B.zero adm0 y (cmp0 y)
          r cz (z<M M) (λ q → L.suc q) l nb))
  }
  where open CPClass (fin M) (fin-plain M) (fin-legal M)

lower-allᵐ : ∀ n → L.ψ⁰ (L.Ω ⟨ n ⟩) ≼ read (closedᵐ (fin n) (fin-plain n) (fin-legal n))
lower-allᵐ zero = suc-lower (cO B.zero) (≼-refl _)
lower-allᵐ (suc M) = FromInterface.theoremᵐ M (interfaceᴮ M)

lower-all : ∀ n → L.ψ⁰ (L.Ω ⟨ n ⟩) ≼ read (closed (fin n) (fin-plain n) (fin-legal n))
lower-all zero = suc-lower (cO B.zero) (≼-refl _)
lower-all (suc M) = FromInterface.theorem M (interfaceᴮ M)
```

## 3 一般层号：`closedᵐ (suc k)` 的链

`Run k`：链在 `Raw k` 里，起点 `cO k`；参照的链 `γ` 在任一结构对应于 `k` 的层号 `κ` 上。层号类取 `k` 的字面子项。

```agda
module Run (k : LF) (pl : Plain k) (Lg : Legal k) {κ : L.Ordᴵ} (c : Corr κ k)
  (Z : L.zero L.<ᴵ L.suc κ) (y : Ext B.zero (B.suc k)) where
  open CPClass k pl Lg

  Ψᴿ : L.Ordᶜ κ → L.Ordᶜ κ
  Ψᴿ = L.ψ {i = κ} {k = κ} {ℓ = L.suc κ} L.zero (λ q → L.suc q)

  γ : ℕ → L.Ordᶜ κ
  γ = iter Ψᴿ (L.Ω κ)

  γ-self : ∀ i → γ i L.≅ γ i
  γ-self zero = L.Ω-≅ (L.≅ᴵ-refl κ)
  γ-self (suc i) =
    L.ψ-≅ {p = L.zero} {σ = λ q → L.suc q} {p′ = L.zero} {σ′ = λ q → L.suc q}
      (L.≅ᴵ-refl κ) (γ-self i)

  Nd₀ : NdR B.zero k
  Nd₀ = N.ndT B.zero k pl Lg (inS y)

  pts : ℕ → Pt k (cO k)
  pts = iterate (N.nextᴿ pl Nd₀) (N.startᴿ Nd₀)

  step-at : ∀ (P : Pt k (cO k)) {x : L.Ordᶜ κ} → RelF k x (atᵖ P) → RelF k (Ψᴿ x) (N.bodyᴿ Nd₀ P)
  step-at (pt η e) r =
    FOLD k self pl Lg k self (N.ownT k pl Lg) (N.complete-ownT k pl Lg) r c
      L.zero (λ q → L.suc q) (proj₁ (proj₂ e)) (proj₂ (proj₂ e))

  chain : ∀ i → RelF k (γ i) (atᵖ (pts i))
  chain zero = START k c
  chain (suc i) = ABSORB k (atᵖ (pts i)) (step-at (pts i) (chain i))

  out-at : ∀ (P : Pt k (cO k)) {x : L.Ordᶜ κ} → RelF k x (atᵖ P) → x L.≅ x →
    L.ψ⁰ x ≼ read (N.obsᴿ Nd₀ P)
  out-at (pt η e) r s =
    ≼-trans (≅→≼ (L.ψ⁰≅ψ {p = Z} {σ = λ q → L.suc q} s))
      (un0 (FOLD k self pl Lg B.zero adm0 (inS y) (cmp0 (inS y)) r cz Z (λ q → L.suc q)
        (proj₁ (proj₂ e)) (proj₂ (proj₂ e))))

  value : L.ψ⁰ (L.Ω (L.suc κ)) ≼ read (Ψn B.zero k pl fold Nd₀)
  value = l≼ (λ i → ≼l i (out-at (pts i) {γ i} (chain i) (γ-self i)))

psum≽ : ∀ (g : ℕ → R) n {X : L.Ordᶜ L.zero} → X ≼ read (g n) → X ≼ read (psum B.zero g n)
psum≽ g zero h = h
psum≽ g (suc n) h = plus≽ (psum B.zero g n) (g (suc n)) h
```

## 4 一切合法层号

极限层号上 `closedᵐ` 是各支的部分和 (`Φᵐ-lim-row`)，`closed` 是各支的极限 (`closed-lim`)。

```agda
lower-any : ∀ K (pl : Plain K) (Lg : Legal K) {κ} → Corr κ K → Zs κ →
  L.ψ⁰ (L.Ω κ) ≼ read (closedᵐ K pl Lg)
lower-any B.zero pl Lg cz z = suc-lower (cO B.zero) (≼-refl _)
lower-any (B.suc k) pl Lg (cs c) z = Run.value k pl Lg c z (mix (dispatch (B.suc k) pl Lg base))
lower-any (B.lim f) pl Lg (cl c) z =
  l≼ (λ n → ≼l n (psum≽ _ n (lower-any (f n) (pl n) (proj₂ Lg n) (c n) (z n))))
lower-any (B.lc k c w b t g) () Lg κc z

lower-anyᶜ : ∀ K (pl : Plain K) (Lg : Legal K) {κ} → Corr κ K → Zs κ →
  L.ψ⁰ (L.Ω κ) ≼ read (closed K pl Lg)
lower-anyᶜ B.zero pl Lg cz z = suc-lower (cO B.zero) (≼-refl _)
lower-anyᶜ (B.suc k) pl Lg (cs c) z = Run.value k pl Lg c z low
lower-anyᶜ (B.lim f) pl Lg (cl c) z =
  l≼ (λ n → ≼l n (lower-anyᶜ (f n) (pl n) (proj₂ Lg n) (c n) (z n)))
lower-anyᶜ (B.lc k c w b t g) () Lg κc z

-- 参照层号取 toIL (由 Legal 的步进造出, 与 K 结构对应).
lower-toIL : ∀ K (pl : Plain K) (Lg : Legal K) → Zs (toIL K pl Lg) →
  L.ψ⁰ (L.Ω (toIL K pl Lg)) ≼ read (closedᵐ K pl Lg)
lower-toIL K pl Lg z = lower-any K pl Lg (toIL-c K pl Lg) z
```

## 5 实例：有限层号 (任意 `Plain`, `Legal`)、ω、ω+n

```agda
lower-finᵐ : ∀ n (pl : Plain (fin n)) (Lg : Legal (fin n)) →
  L.ψ⁰ (L.Ω ⟨ n ⟩) ≼ read (closedᵐ (fin n) pl Lg)
lower-finᵐ n pl Lg = lower-any (fin n) pl Lg (natC n) (ZsN n)

lower-ωᵐ : L.ψ⁰ (L.Ω L.ωᴵ) ≼ read (closedᵐ ω ω-plain ω-legal)
lower-ωᵐ = lower-any ω ω-plain ω-legal (ωC 0) ZsN

lower-ω : L.ψ⁰ (L.Ω L.ωᴵ) ≼ read (closed ω ω-plain ω-legal)
lower-ω = lower-anyᶜ ω ω-plain ω-legal (ωC 0) ZsN

lower-ω+ᵐ : ∀ n → L.ψ⁰ (L.Ω (ωp n)) ≼ read (closedᵐ (ω+ n) (ω+-plain n) (ω+-legal n))
lower-ω+ᵐ n = lower-any (ω+ n) (ω+-plain n) (ω+-legal n) (ωC n) (ZsW n)

lower-ω+ : ∀ n → L.ψ⁰ (L.Ω (ωp n)) ≼ read (closed (ω+ n) (ω+-plain n) (ω+-legal n))
lower-ω+ n = lower-anyᶜ (ω+ n) (ω+-plain n) (ω+-legal n) (ωC n) (ZsW n)

-- YiRawFoldInst 的两个具名闭项 (读法 ψ₀(Ω_{ω+1}), ψ₀(Ω_{ω+2})).
Ωω+1-lower : L.ψ⁰ (L.Ω (L.suc L.ωᴵ)) ≼ read Ωω+1
Ωω+1-lower = lower-ω+ 1

Ωω+2-lower : L.ψ⁰ (L.Ω (L.suc (L.suc L.ωᴵ))) ≼ read Ωω+2
Ωω+2-lower = lower-ω+ 2
```
