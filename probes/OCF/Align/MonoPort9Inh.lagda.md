# Ω-极限高度 (八): 每一格都走过坐标 (`growC` 的前提可满足)

> 入口 [MonoPort9](MonoPort9.lagda.md). 不含记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.
>
> [MonoPort9Cell](MonoPort9Cell.lagda.md) 的 `growC n` 以 "坐标 $c$ 被第 $n$ 格走过" 为前提. 这里证明对一切 $n$ 都有这样的 $c$ (`walked`), 所以 `growC` 对每一格都不空:
>
> - `NZW`/`L4′`: 照 `HtFeedGrow.G.W` 的 `W-suc`, `W-ext`, `L4` (那里的节点族在世界 $\omega$ 上, 这里是 $u$, 起点 $0$): 若 $z$ 在第 0 层非零, 沿 `sum-fst b z` 的路径走的 `Walk` 在第 0 层非零.
> - `wExt`/`wL4`: 同一个归纳, 产出一个走过的坐标.
> - `nzCell`: 对 $n$ 归纳, 第 $n$ 格的输出非零 (第 $0$ 格的路径来自 $Y_1$ 的 $z$, 第 $n+1$ 格的路径来自第 $n$ 格的输出).
> - `walked n`: 第 $n$ 格走过某个坐标.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPort9Inh where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree
open import OCF.Align.HtFeedClosed using (module At; one)
open import OCF.Align.HtFeedGrow using (NZ₀; nz1; nzL; nzR; nzl; nzw; ⊲-as; ⊲-idl; module G)
open import OCF.Align.MonoPort8Om using (module Om)
open import OCF.Align.MonoPort9One using (Walked; wHere; wThere; wPre; wSub)
```

## 1 走过一个坐标

```agda
wExt : ∀ {W₀′} b″ {a} (P : a ⊲ b″) lb″ (y : D₀ W₀′) {c} → Walked b″ P lb″ c → Walked (sum b″ y) (⊲-tr P (sum-fst b″ y)) (Lg-sum b″ y lb″) c
wExt b″ P lb″ n0 h = h
wExt b″ P lb″ n1 h = wThere h
wExt b″ P lb″ (y₁ ⨾ y₂) h =
  subst (λ π → Walked (sum (sum b″ y₁) y₂) π (Lg-sum (sum b″ y₁) y₂ (Lg-sum b″ y₁ lb″)) _)
        (sym (⊲-as P (sum-fst b″ y₁) (sum-fst (sum b″ y₁) y₂)))
        (wExt (sum b″ y₁) (⊲-tr P (sum-fst b″ y₁)) (Lg-sum b″ y₁ lb″) y₂ (wExt b″ P lb″ y₁ h))
wExt b″ P lb″ (nl e) h = wPre h
wExt b″ P lb″ (ni () u) h
wExt b″ P lb″ (nκ () u) h
wExt b″ P lb″ (nw p y) h = wExt b″ P lb″ y h

wL4 : ∀ {W₀′} (z : D₀ W₀′) → NZ₀ z → ∀ b′ {a} (Rr : a ⊲ b′) lb′ → Σ A (Walked (sum b′ z) (⊲-tr Rr (sum-fst b′ z)) (Lg-sum b′ z lb′))
wL4 n1 nz1 b′ Rr lb′ = b′ , wHere
wL4 (x ⨾ y) (nzL nx) b′ Rr lb′ =
  proj₁ ih , subst (λ π → Walked (sum (sum b′ x) y) π (Lg-sum (sum b′ x) y (Lg-sum b′ x lb′)) (proj₁ ih))
                   (sym (⊲-as Rr (sum-fst b′ x) (sum-fst (sum b′ x) y)))
                   (wExt (sum b′ x) (⊲-tr Rr (sum-fst b′ x)) (Lg-sum b′ x lb′) y (proj₂ ih))
  where ih = wL4 x nx b′ Rr lb′
wL4 (x ⨾ y) (nzR ny) b′ Rr lb′ =
  proj₁ ih , subst (λ π → Walked (sum (sum b′ x) y) π (Lg-sum (sum b′ x) y (Lg-sum b′ x lb′)) (proj₁ ih))
                   (sym (⊲-as Rr (sum-fst b′ x) (sum-fst (sum b′ x) y))) (proj₂ ih)
  where ih = wL4 y ny (sum b′ x) (⊲-tr Rr (sum-fst b′ x)) (Lg-sum b′ x lb′)
wL4 (nl e) (nzl ne) b′ Rr lb′ =
  proj₁ ih , wSub 0 (subst (λ π → Walked (sum b′ (e 0)) π (Lg-sum b′ (e 0) lb′) (proj₁ ih)) (⊲-idl (sum-fst b′ (e 0))) (proj₂ ih))
  where ih = wL4 (e 0) ne b′ C.self lb′
wL4 (nw p x) (nzw nx) b′ Rr lb′ = wL4 x nx b′ Rr lb′
```

## 2 每一格非零, 每一格走过坐标

```agda
module Inh (g : A → H) (l : LgH (hΩ g)) where
  open Om g l using (Λ; module P; module GG; u; κ; Y₁; iY₁)

  NZW : ∀ b {a} → a ⊲ b → azero ⊲ a → Lg b → Set
  NZW b Q ap lb = ∀ {V₁} (bV : b ⊲ V₁) (lV : Lg V₁) (A₀ : P.Ig Λ V₁) → GG.NZA A₀ lV (P.τ₀ lV) → ∀ co (Y : P.St V₁) → GG.Inv Y →
                  NZ₀ (P.yc (P.Walk accᴸ u b Q ap lb bV lV hself A₀ co Y) (P.τ₀ lV))

  W-suc : ∀ c {a} (Q : a ⊲ c) ap lb → NZW (asuc c) (C.suc Q) ap lb
  W-suc c Q ap lb bV lV A₀ hA co Y v =
    nzR (GG.L2 accᴸ (sL C.self hself) (⊲-tr (C.suc C.self) bV) lV hself A₀ (co ⨾ Cut u c Q ap lb (⊲-tr (C.suc C.self) bV))
           (P._⊕⟨_⟩_ Y lV (P.Walk accᴸ u c Q ap lb (⊲-tr (C.suc C.self) bV) lV hself A₀ co Y)) (P.τ₀ lV) hA
           (GG.inv⊕ lV (P.Walk accᴸ u c Q ap lb (⊲-tr (C.suc C.self) bV) lV hself A₀ co Y) v))

  W-ext : ∀ {W₀′} b″ {a} (Q : a ⊲ b″) ap lb″ (y : D₀ W₀′) → NZW b″ Q ap lb″ → NZW (sum b″ y) (⊲-tr Q (sum-fst b″ y)) ap (Lg-sum b″ y lb″)
  W-ext b″ Q ap lb″ n0 h = h
  W-ext b″ Q ap lb″ n1 h = W-suc b″ Q ap lb″
  W-ext b″ Q ap lb″ (y₁ ⨾ y₂) h =
    subst (λ π → NZW (sum (sum b″ y₁) y₂) π ap (Lg-sum (sum b″ y₁) y₂ (Lg-sum b″ y₁ lb″)))
          (sym (⊲-as Q (sum-fst b″ y₁) (sum-fst (sum b″ y₁) y₂)))
          (W-ext (sum b″ y₁) (⊲-tr Q (sum-fst b″ y₁)) ap (Lg-sum b″ y₁ lb″) y₂ (W-ext b″ Q ap lb″ y₁ h))
  W-ext b″ Q ap lb″ (nl e) h bV lV A₀ hA co Y v = nzL (h _ lV A₀ hA co Y v)
  W-ext b″ Q ap lb″ (ni () u′) h
  W-ext b″ Q ap lb″ (nκ () u′) h
  W-ext b″ Q ap lb″ (nw p y) h = W-ext b″ Q ap lb″ y h

  L4′ : ∀ {W₀′} (z : D₀ W₀′) → NZ₀ z → ∀ b′ {a} (Rr : a ⊲ b′) ap lb′ → NZW (sum b′ z) (⊲-tr Rr (sum-fst b′ z)) ap (Lg-sum b′ z lb′)
  L4′ n1 nz1 b′ Rr ap lb′ = W-suc b′ Rr ap lb′
  L4′ (x ⨾ y) (nzL nx) b′ Rr ap lb′ =
    subst (λ π → NZW (sum (sum b′ x) y) π ap (Lg-sum (sum b′ x) y (Lg-sum b′ x lb′)))
          (sym (⊲-as Rr (sum-fst b′ x) (sum-fst (sum b′ x) y)))
          (W-ext (sum b′ x) (⊲-tr Rr (sum-fst b′ x)) ap (Lg-sum b′ x lb′) y (L4′ x nx b′ Rr ap lb′))
  L4′ (x ⨾ y) (nzR ny) b′ Rr ap lb′ =
    subst (λ π → NZW (sum (sum b′ x) y) π ap (Lg-sum (sum b′ x) y (Lg-sum b′ x lb′)))
          (sym (⊲-as Rr (sum-fst b′ x) (sum-fst (sum b′ x) y)))
          (L4′ y ny (sum b′ x) (⊲-tr Rr (sum-fst b′ x)) ap (Lg-sum b′ x lb′))
  L4′ (nl e) (nzl ne) b′ Rr ap lb′ bV lV A₀ hA co Y v =
    nzR (nzl (subst (λ π → NZW (sum b′ (e 0)) π (⊲-tr ap Rr) (Lg-sum b′ (e 0) lb′)) (⊲-idl (sum-fst b′ (e 0)))
                    (L4′ (e 0) ne b′ C.self (⊲-tr ap Rr) lb′) (⊲-tr (C.lim 1 C.self) bV) lV A₀ hA
                    (co ⨾ Cut u b′ Rr ap lb′ (⊲-tr (C.lim 0 C.self) bV))
                    (P._⊕⟨_⟩_ Y lV (P.Walk accᴸ u b′ Rr ap lb′ (⊲-tr (C.lim 0 C.self) bV) lV hself A₀ co Y))
                    (GG.inv⊕ lV (P.Walk accᴸ u b′ Rr ap lb′ (⊲-tr (C.lim 0 C.self) bV) lV hself A₀ co Y) v)))
  L4′ (nw p x) (nzw nx) b′ Rr ap lb′ = L4′ x nx b′ Rr ap lb′

  -- 每一格的起始状态非零
  invS : ∀ n → GG.Inv (P.Sv (κ n))
  invS zero = GG.invcv (P.wv (κ 0)) iY₁
  invS (suc n) = GG.invcv (P.av (κ (suc n))) (GG.inv⊕ (P.lv (κ n)) (P.κΔ accᴸ u hself P.Act (κ n)) (invS n))

  cellT : ∀ n → D₀ (P.v (κ n))
  cellT n = P.yc (P.κΔ accᴸ u hself P.Act (κ n)) (P.τ₀ (P.lv (κ n)))

  hA : ∀ n → GG.NZA {Λ} (P.Ig↾ (P.wv (κ n)) P.Act) (P.lv (κ n)) (P.τ₀ (P.lv (κ n)))
  hA n = GG.na (λ w Y → GG.nz-Step Y (P.τ₀ (P.lv (κ n))))

  nzY₁ : NZ₀ (P.z Y₁)
  nzY₁ = nzR (GG.nz-Step (P.Y₀ {one}) (P.τ₀ tt))

  nzCell : ∀ n → NZ₀ (cellT n)
  nzCell zero = L4′ (P.z Y₁) nzY₁ one (C.suc C.self) C.self tt C.self (P.lv (κ 0)) (P.Ig↾ (P.wv (κ 0)) P.Act) (hA 0) (P.co (κ 0)) (P.Sv (κ 0)) (invS 0)
  nzCell (suc n) =
    subst (λ π → NZW (P.v (κ (suc n))) π (P.ap (κ (suc n))) (P.lv (κ (suc n)))) (⊲-idl (P.av (κ (suc n))))
          (L4′ (cellT n) (nzCell n) (P.v (κ n)) C.self (P.ap (κ (suc n))) (P.lv (κ n)))
          C.self (P.lv (κ (suc n))) (P.Ig↾ (P.wv (κ (suc n))) P.Act) (hA (suc n)) (P.co (κ (suc n))) (P.Sv (κ (suc n))) (invS (suc n))

  -- 每一格走过某个坐标
  walked : ∀ n → Σ A (Walked (P.v (κ n)) (P.av (κ n)) (P.lv (κ n)))
  walked zero = wL4 (P.z Y₁) nzY₁ one (C.suc C.self) tt
  walked (suc n) =
    proj₁ w , subst (λ π → Walked (P.v (κ (suc n))) π (P.lv (κ (suc n))) (proj₁ w)) (⊲-idl (P.av (κ (suc n)))) (proj₂ w)
    where w = wL4 (cellT n) (nzCell n) (P.v (κ n)) C.self (P.lv (κ n))
```
