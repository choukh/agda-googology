# 塔第 2 项 (五): 自身行的帧, 对一切层号 (记号直连)

> 验收文件 (读记号). 判决: 编译定理, 对一切层号 ℓ (含 Ω 结点层号, 下标层号任意) 与 `YiMEStep.Lev.Mᴸ` 的任意 `Ix`: 目标为自身的折叠保持关系, `PF : Mᴸ ℓ a x → Mᴸ ℓ (ψ_u a) (ψs ℓ … ℓ self β … x)`; `up` 一行 (自身行, 上折) 是 `PU`, 沿下行链对孩子层号的关系递归. 前提: 底在 ψ_u(0) 之上; 槽位允许的记号下标 ν 满足 ν+1 ≤ u (`kept`, 记号一侧结点保留).
> 实例 (条件定理): `chain-sim`: 给了 `tw 1` 上的这两条前提, `T⁺` 的链满足 `Mᴸ (tw 1) (γ₊ n) (d⁺ (n+1))`. 前提没有实例: `Ωt (tw 1)` 在 Ω_Ω 之上要层号对记号下标的关系在孩子层号上给出, 这里没有做.
> 不给出什么: 朝第 0 层与朝孩子层的折叠 (`QH`, `VW` 的一般层号版) 不在这里; 自身行的输出再朝孩子层折叠时的保留与记号不一致 (`YiT2Frame.flat-lim`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiT2Self where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; Ev; Ev-tw; Rt-tw) renaming (Rt to Rtᴾ)
open import OCF.Lean.YiLegFold
import OCF.Align.EboLeanDef as E
open E using (cof; c1; cω; cΩ; pred; fsn; fsT; ψ; cmpᵀ; sucT; cofψ₊; fsTc)
open import OCF.Lean.YiMEBase using (Mᴰ; mz; m1; mL; mΩ; mU; mw; module Gen)
open import OCF.Lean.YiMENote
open import OCF.Lean.YiMEAnchor using (Ω₁ᵗ)
open import OCF.Lean.YiMEStep using (module Lev; γ₊)
open import OCF.Lean.YiT2Desc using (d⁺)
```

## 记号一侧: 结点保留的情形

`Le c`: 比较结果不是 "大于". ν+1 ≤ u 时 ψ_u(b) 的余尾仍是 Ω_{ν+1}, Ω-基本列穿透 (规则 5Ω).

```agda
Le : E.Cmp → Set
Le E.lt = ⊤
Le E.eq = ⊤
Le E.gt = ⊥

cofΩk : ∀ u b {ν} → cof b ≡ cΩ ν → Le (cmpᵀ (sucT ν) u) → cof (ψ u b ∷ []) ≡ cΩ ν
cofΩk u b {ν} e le = trans (cofψΩ u b e) (aux (cmpᵀ (sucT ν) u) le)
  where
  aux : ∀ c → Le c → cofψ₊ u ν c ≡ cΩ ν
  aux E.lt _ = refl
  aux E.eq _ = refl
  aux E.gt ()

fsTk : ∀ u b {ν} η → cof b ≡ cΩ ν → Le (cmpᵀ (sucT ν) u) → fsT (ψ u b ∷ []) η ≡ ψ u (fsT b η) ∷ []
fsTk u b {ν} η e le = trans (fsTψΩ u b η e) (aux (cmpᵀ (sucT ν) u) le)
  where
  aux : ∀ c → Le c → fsTc u b ν c η ≡ ψ u (fsT b η) ∷ []
  aux E.lt _ = refl
  aux E.eq _ = refl
  aux E.gt ()

cof++Ω : ∀ t s {ν} → cof s ≡ cΩ ν → cof (t ++ s) ≡ cΩ ν
cof++Ω t []       ()
cof++Ω t (y ∷ ys) e = trans (cof++ t y ys) e

fsT++′ : ∀ t y ys η → fsT (t ++ y ∷ ys) η ≡ t ++ fsT (y ∷ ys) η
fsT++′ []           y ys η = refl
fsT++′ (x ∷ [])     y ys η = refl
fsT++′ (x ∷ z ∷ t)  y ys η = cong (x ∷_) (fsT++′ (z ∷ t) y ys η)

fsT++ : ∀ t s η {ν} → cof s ≡ cΩ ν → fsT (t ++ s) η ≡ t ++ fsT s η
fsT++ t []       η ()
fsT++ t (y ∷ ys) η e = fsT++′ t y ys η
```

## 槽位搬运与关系

上折把孩子层的槽位搬进 ℓ (`mv`); 槽位所在的层号不变, 槽位的低层关系沿换型搬回去.

```agda
at-ch : (j : LF) (c : Ch j) (p : Pos (chL j c)) → at j (chP j c p) ≡ at (chL j c) p
at-ch (suc a)  _ p = refl
at-ch (lim g)  n p = refl
at-ch (Ωₗ k h) c p = refl

at-mv : ∀ {ℓ j} (d : Dn ℓ j) (p : Pos j) → at ℓ (mv d p) ≡ at j p
at-mv stop           p = refl
at-mv (down {j} d c) p = trans (at-mv d (chP j c p)) (at-ch j c p)

module Self (Ix : LF → E.T → Set) (u : E.T) where
  open Lev Ix

  ψᵘ : E.T → E.T
  ψᵘ a = ψ u a ∷ []

  Kept : LF → Set
  Kept ℓ = (p : Pos ℓ) (ν : E.T) → Ix (at ℓ p) ν → Le (cmpᵀ (sucT ν) u)

  low-ch : (j : LF) (c : Ch j) (p : Pos (chL j c)) (η : E.T) (z : Br j (chP j c p))
    → Lowᴸ j (chP j c p) η z → Lowᴸ (chL j c) p η (chBr j c p z)
  low-ch (suc a)  _ p η z l = l
  low-ch (lim g)  n p η z l = l
  low-ch (Ωₗ k h) c p η z l = l

  low-mv : ∀ {ℓ j} (d : Dn ℓ j) (p : Pos j) (η : E.T) (z : Br ℓ (mv d p))
    → Lowᴸ ℓ (mv d p) η z → Lowᴸ j p η (mvBr d p z)
  low-mv stop           p η z l = l
  low-mv (down {j} d c) p η z l = low-ch j c p η (mvBr d (chP j c p) z) (low-mv d (chP j c p) η z l)
```

## 上折 (`PU`) 与自身折叠 (`PF`)

`PU`: 记号一侧是 ψ_u(t + s), 块一侧是以 b 为底把孩子层的树 y 上折; 对 `Mᴸ j s y` 归纳. 结点保留 (两边都是), 嵌套的 `up` 沿链再下一层.

```agda
  PU : (ℓ : LF) → Kept ℓ → (j : LF) (d : Dn ℓ j) {t : E.T} (b : Tr ℓ) (nb : ℓ ⊢ zero ◃ b) → Mᴸ ℓ (ψᵘ t) b
     → ∀ {s y} → Mᴸ j s y → Mᴸ ℓ (ψᵘ (t ++ s)) (Up j d b nb y)
  PU ℓ kp j d {t} b nb mb (mz {x = y}) =
    subst (λ z → Mᴸ ℓ (ψᵘ z) (Up j d b nb y)) (sym (++-identityʳ t))
      (Gen.m-zl (Up j d b nb) (Up-mono j d b nb) mb y)
  PU ℓ kp j d {t} b nb mb (m1 {t = s} {x = y} e r) =
    Gen.m-next (Up-nz j d b nb y) (cofψ1 u (t ++ s) (cof++1 t s e))
      (λ n → trans (fsnψ1 u (t ++ s) n (cof++1 t s e)) (cong (λ z → replicate n (ψ u z)) (pred++ t s e)))
      (PU ℓ kp j d b nb mb r)
  PU ℓ kp j d {t} b nb mb (mL {t = s} {x = y} e h) =
    mL (cofψω u (t ++ s) (cof++ω t s e))
      (λ n → subst (λ z → Mᴸ ℓ z (Up j d b nb y))
        (sym (trans (fsnψω u (t ++ s) n (cof++ω t s e)) (cong ψᵘ (fsn++ t s n e))))
        (PU ℓ kp j d b nb mb (h n)))
  PU ℓ kp j d {t} b nb mb (mΩ {t = s} {ν = ν} {p = p} {g = g} e nu h) =
    mΩ (cofΩk u (t ++ s) (cof++Ω t s e) (kp (mv d p) ν (subst (λ k → Ix k ν) (sym (at-mv d p)) nu)))
       (subst (λ k → Ix k ν) (sym (at-mv d p)) nu)
       (λ η c l → subst (λ z → Mᴸ ℓ z (Up j d b nb (g (mvBr d p c))))
         (sym (trans (fsTk u (t ++ s) η (cof++Ω t s e) (kp (mv d p) ν (subst (λ k → Ix k ν) (sym (at-mv d p)) nu)))
                     (cong ψᵘ (fsT++ t s η e))))
         (PU ℓ kp j d b nb mb (h η (mvBr d p c) (low-mv d p η c l))))
  PU ℓ kp zero     d b nb mb (mU {c = ()} m ch)
  PU ℓ kp (suc a)  d {t} b nb mb (mU {t = s₁} {s = s₂} {x = y} {c = c} {y = y′} m ch) =
    subst (λ z → Mᴸ ℓ (ψᵘ z) (Up a (down d c) (Up (suc a) d b nb y) (Up-nz (suc a) d b nb y) y′)) (++-assoc t s₁ s₂)
      (PU ℓ kp a (down d c) (Up (suc a) d b nb y) (Up-nz (suc a) d b nb y) (PU ℓ kp (suc a) d b nb mb m) ch)
  PU ℓ kp (lim g)  d {t} b nb mb (mU {t = s₁} {s = s₂} {x = y} {c = n} {y = y′} m ch) =
    subst (λ z → Mᴸ ℓ (ψᵘ z) (Up (g n) (down d n) (Up (lim g) d b nb y) (Up-nz (lim g) d b nb y) y′)) (++-assoc t s₁ s₂)
      (PU ℓ kp (g n) (down d n) (Up (lim g) d b nb y) (Up-nz (lim g) d b nb y) (PU ℓ kp (lim g) d b nb mb m) ch)
  PU ℓ kp (Ωₗ k h) d {t} b nb mb (mU {t = s₁} {s = s₂} {x = y} {c = c} {y = y′} m ch) =
    subst (λ z → Mᴸ ℓ (ψᵘ z) (Up (h c) (down d c) (Up (Ωₗ k h) d b nb y) (Up-nz (Ωₗ k h) d b nb y) y′)) (++-assoc t s₁ s₂)
      (PU ℓ kp (h c) (down d c) (Up (Ωₗ k h) d b nb y) (Up-nz (Ωₗ k h) d b nb y) (PU ℓ kp (Ωₗ k h) d b nb mb m) ch)
  PU ℓ kp j d b nb mb (mw m dd) = mw (PU ℓ kp j d b nb mb m) (Up-mono j d b nb dd)

  PUc : (ℓ : LF) → Kept ℓ → (c : Ch ℓ) {t : E.T} (b : Tr ℓ) (nb : ℓ ⊢ zero ◃ b) → Mᴸ ℓ (ψᵘ t) b
      → ∀ {s y} → Chdᴸ ℓ c s y → Mᴸ ℓ (ψᵘ (t ++ s)) (Upc ℓ c b nb y)
  PUc zero     kp () b nb mb ch
  PUc (suc a)  kp c b nb mb ch = PU (suc a) kp a (down stop c) b nb mb ch
  PUc (lim g)  kp n b nb mb ch = PU (lim g) kp (g n) (down stop n) b nb mb ch
  PUc (Ωₗ k h) kp c b nb mb ch = PU (Ωₗ k h) kp (h c) (down stop c) b nb mb ch

  PF : (ℓ : LF) → Kept ℓ → (ε : Ev ℓ) (ρ : Rtᴾ ℓ) (B : Base ℓ) (β : Tr ℓ) (nβ : ℓ ⊢ zero ◃ β) → Mᴸ ℓ (ψᵘ []) β
     → ∀ {a x} → Mᴸ ℓ a x → Mᴸ ℓ (ψᵘ a) (ψs ℓ ε ρ B ℓ self β nβ x)
  PF ℓ kp ε ρ B β nβ hβ (mz {x = x}) =
    Gen.m-zl (ψs ℓ ε ρ B ℓ self β nβ) (monos ℓ ε ρ B ℓ self β nβ) hβ x
  PF ℓ kp ε ρ B β nβ hβ (m1 {t = a} {x = x} e r) =
    Gen.m-next (nzs ℓ ε ρ B ℓ self β nβ x) (cofψ1 u a e) (λ n → fsnψ1 u a n e) (PF ℓ kp ε ρ B β nβ hβ r)
  PF ℓ kp ε ρ B β nβ hβ (mL {t = a} {x = x} e h) =
    mL (cofψω u a e)
      (λ n → subst (λ z → Mᴸ ℓ z (ψs ℓ ε ρ B ℓ self β nβ x)) (sym (fsnψω u a n e)) (PF ℓ kp ε ρ B β nβ hβ (h n)))
  PF ℓ kp ε ρ B β nβ hβ (mΩ {t = a} {ν = ν} {p = p} {g = g} e nu h) =
    mΩ (cofΩk u a e (kp p ν nu)) nu
      (λ η c l → subst (λ z → Mᴸ ℓ z (ψs ℓ ε ρ B ℓ self β nβ (g c))) (sym (fsTk u a η e (kp p ν nu)))
        (PF ℓ kp ε ρ B β nβ hβ (h η c l)))
  PF ℓ kp ε ρ B β nβ hβ (mU {x = x} {c = c} m ch) =
    PUc ℓ kp c (ψs ℓ ε ρ B ℓ self β nβ x) (nzs ℓ ε ρ B ℓ self β nβ x) (PF ℓ kp ε ρ B β nβ hβ m) ch
  PF ℓ kp ε ρ B β nβ hβ (mw m d) = mw (PF ℓ kp ε ρ B β nβ hβ m) (monos ℓ ε ρ B ℓ self β nβ d)
```

## 实例: `T⁺` 的链 (条件定理)

u 取 Ω₁ (记号的 ψ_Ω), ℓ 取 `tw 1`. γ₊ 0 = Ω_Ω = ψ_Ω(0), γ₊ (n+1) = ψ_Ω(γ₊ n); 块的链 `d⁺ (n+1) = next (ψs … self … (d⁺ n))`, 晚一步.

```agda
module Chain (Ix : LF → E.T → Set) where
  open Lev Ix
  open Self Ix Ω₁ᵗ

  chain-sim : Kept (tw 1) → Mᴸ (tw 1) (E.Ωt Ω₁ᵗ) (Ωt (tw 1)) → ∀ n → Mᴸ (tw 1) (γ₊ n) (d⁺ (suc n))
  chain-sim kp hβ zero    = mw hβ (◃l zero)
  chain-sim kp hβ (suc n) =
    mw (PF (tw 1) kp (Ev-tw 1) (Rt-tw 1) (B₀ (tw 1)) (Ωt (tw 1)) (Ωt-nz (tw 1)) hβ (chain-sim kp hβ n)) (◃l zero)
```
