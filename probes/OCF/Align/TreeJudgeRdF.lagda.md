# 第二次使用: $\psi_1(\Omega)$ 的紧读法 (定义)

> 不含记号. 结论写在 [TreeJudge](TreeJudge.lagda.md). [GuardTight](GuardTight.lagda.md) 文件头说: $F\theta=\psi_1(\Omega_\theta)$ 的分支不是字面的 ($\psi_1(\eta+1)=\lim_n\psi_1(\eta)\cdot n$), 紧的读法 "要比较 $F\eta$ 与位置, 判断: 就是 `Str` (`cmpF`) 与 `Cont`, 没有写". 所以那里用 `Tc-id`.
>
> **这里写出来了, 不要比较, 也不要 `Str`/`Cont`.** 判据的要求 (`ghost`, `HF`) 只是: 界不读头不读的分支值. 按这个要求问的问题是: 位置 $P$ 在 $\psi_1(\eta)\cdot(k+1)=\psi_1(\eta)+y$ 里, 是不是落在前缀 $\psi_1(\eta)$ 上? **这是对 $y$ 的结构递归 (`vA₁`, `vA₀`), 不比较任何东西:** $y$ 走到 $0$ 就在前缀上, 否则节点比前缀高. 落在前缀上就读到分支 $\eta$, 否则留在 $\eta+1$. 这正好是 `Tail` 的 `VS` 视图.
>
> `Tc-ψ` 也是新的: 分支本身的读法, 对一切 $\eta$. 前缀 $W$ 在迭代里增长 (`Wc`), 终止度量是 $\eta$ 的结构.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeJudgeRdF where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans; sym)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.GuardTightCum using (Ordᴵ; Ordᶜ; add; _+_; Ω; zero; suc; lim; limᵢ; up; Simᴵ)
open import OCF.Align.GuardTightLv
open Lv Dom₀
import OCF.Align.GuardTightUni as Uni
private module Un = Uni Dom₀
open Un using (rb₀; rb₁; em; ψ¹; F)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightRd
open import OCF.Align.TreeJudgeRd using (Wr; module RdPre)

open RdIter using (c; tcS)
```

## §1 位置在不在前缀上

`InA x P`: 位置 $P$ 其实在前缀 $x$ 里. 带可容许性的搬运. `vA₁`, `vA₀`: 对 $y$ 结构递归. 第 0 层的 `up`: `add` 把 $\sigma$ 换成 `suc`, 所以 `vA₀` 的 $\sigma$ 是一般的.

```agda
InA : (x : Ordᶜ (suc zero)) {k L : LG} (P : Cp k L) → Set
InA x {k} P = Σ (Cp k (rb₁ x)) λ P′ → ∀ E → AdmC E P → AdmC E P′

vA₀ : ∀ (x : Ordᶜ (suc zero)) (σ : Simᴵ zero (suc zero)) (y : Ordᶜ zero) {k} (P : Cp k (rb₁ (add x σ y))) → InA x P ⊎ ⊤
vA₀ x σ zero P = inj₁ (P , (λ _ a → a))
vA₀ x σ (suc y) self = inj₂ tt
vA₀ x σ (suc y) (suc P) = vA₀ x σ y P
vA₀ x σ (lim h) self = inj₂ tt
vA₀ x σ (lim h) (lim n P) = vA₀ x σ (h n) P

vA₁ : ∀ (x : Ordᶜ (suc zero)) (y : Ordᶜ (suc zero)) {k} (P : Cp k (rb₁ (x + y))) → InA x P ⊎ ⊤
vA₁ x zero P = inj₁ (P , (λ _ a → a))
vA₁ x (suc y) self = inj₂ tt
vA₁ x (suc y) (suc P) = vA₁ x y P
vA₁ x (lim h) self = inj₂ tt
vA₁ x (lim h) (lim n P) = vA₁ x (h n) P
vA₁ x (limᵢ zero f) self = inj₂ tt
vA₁ x (limᵢ zero f) (fst P) = vA₁ x (f (suc zero)) P
vA₁ x (limᵢ zero f) (bra η e P) with vA₁ x (f (em η)) P
... | inj₁ (P′ , tr) = inj₁ (P′ , (λ E a → tr E (proj₂ a)))
... | inj₂ t = inj₂ t
vA₁ x (limᵢ (suc ()) f) P
vA₁ x (up zero y) P = vA₀ x (λ q → suc q) y P
```

## §2 视图与读法

`G η` $=\psi_1(\eta)$ 的层号. 后继: 位置 `lim (k+1) P`, 问 $P$ 在不在前缀 $\psi_1(\eta)$ 上. 第一支: $\psi_1(0)=\Omega_1$ 的位置放进 $\psi_1(1)$ 的第 1 项.

```agda
ψe : Ordᴵ → Ordᶜ (suc zero)
ψe η = ψ¹ (em η)

G : Ordᴵ → LG
G η = rb₁ (ψe η)

vsF : ∀ b {k} (P : Cp k (G (suc b))) → VS G b P
vsF b self = vS₀
vsF b (lim zero P) = vS₀
vsF b (lim (suc m) P) with vA₁ (ψe b) (iter (ψe b +_) zero m) P
... | inj₁ (P′ , tr) = vS₁ P′ tr
... | inj₂ _ = vS₀

vlF : ∀ f s {k} (P : Cp k (G (lim f s))) → VL G f s P
vlF f s self = vL₀
vlF f s (lim n P) = vL₁ n P (λ _ a → a)

IF : TailI
IF = record { G = G ; t₁ = G (suc zero) ; toT = λ P → lim 1 P ; adT = λ P a → a }

rdψ : Rdr (suc zero) (G (suc zero)) (λ η e → G η)
rdψ = Tail.rdA IF vsF vlF
```

## §3 分支本身的读法

`Wc R x hx`: 前缀 $W$ 之后再接 $x+\_$. `Tc-Wψ R η`: $W(\psi_1(\eta))$ 的读法, 对一切 $\eta$. 后继要 $W(x\cdot n)$, $x=\psi_1(b)$, 对 $n$ 归纳时前缀变长. 终止: 对 $\eta$ 结构递归, 里面对 $n$.

```agda
module _ (R : Wr) where
  open Wr R

  -- W ∘ (x +_)
  Wc : (x : Ordᶜ (suc zero)) → Tc (rb₁ (W x)) → Wr
  Wc x tx = record
    { W = λ u → W (x + u)
    ; Ws = λ u → Ws (x + u)
    ; Wl = λ h → Wl (λ n → x + h n)
    ; Wi = λ f → Wi (λ y → x + f y)
    ; Vs = λ y → Ws (add x (λ q → suc q) y)
    ; Vl = λ h → Wl (λ n → add x (λ q → suc q) (h n))
    ; V0 = refl
    ; tc0 = tx }

Tc-Wψ : (R : Wr) (η : Ordᴵ) → Tc (rb₁ (Wr.W R (ψe η)))
Tc-Witer : (R : Wr) (b : Ordᴵ) (n : ℕ) → Tc (rb₁ (Wr.W R (iter (ψe b +_) zero n)))

Tc-Wψ R zero = RdPre.Tc-Wc R
Tc-Wψ R (suc b) = tcS (Wr.Wl R (iter (ψe b +_) zero)) (Tc-Witer R b)
Tc-Wψ R (lim f s) = tcS (Wr.Wl R (λ n → ψe (f n))) (λ n → Tc-Wψ R (f n))

Tc-Witer R b zero = Wr.tc0 R
Tc-Witer R b (suc n) = Tc-Witer (Wc R (ψe b) (Tc-Wψ R b)) b n

-- 没有前缀
Tc-ψ : ∀ η → Tc (G η)
Tc-ψ zero = RdIter.Tc-c
Tc-ψ (suc b) = go
  where
  x = ψe b
  R₁ : Wr
  R₁ = record
    { W = x +_ ; Ws = λ u → refl ; Wl = λ h → refl ; Wi = λ f → refl
    ; Vs = λ y → refl ; Vl = λ h → refl ; V0 = refl ; tc0 = Tc-ψ b }
  go : Tc (G (suc b))
  go zero = tt
  go (suc n) = Tc-Witer R₁ b n
Tc-ψ (lim f s) = λ n → Tc-ψ (f n)

-- ψ₁(Ω) 的层号
Tc-F1 : Tc (F (suc zero))
Tc-F1 = rdψ , Tc-ψ (suc zero) , (λ η e → Tc-ψ η)
```
