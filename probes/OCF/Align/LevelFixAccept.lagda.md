# 验收: 对 EBO 的有限比较

> **验收节.** 记号只在本文件. 结论写在 [LevelFix](LevelFix.lagda.md). **全部是有限测试, 不是证明.** 比较器 `dfO`, `dfL` 逐字取自 [DomFoldAccept](DomFoldAccept.lagda.md): 看种类, 闭包的共尾层, 第一支, 走分支 $c+k$; **这两个不看界.** 界用 `misQ`: 对 [LadderNFTree](LadderNFTree.lagda.md) 的塔, 宽度 3, 逐闭包比下界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LevelFixAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.GuardTightLv using (module Lv)
open import OCF.Align.LevelFixX using (XU)
open import OCF.Align.LevelFixCore
open import OCF.Align.LevelFixVal
open import OCF.Align.LevelFixU
open import OCF.Align.LevelFixFold hiding (O; rb; Tn; T⁰; natL)
import OCF.Align.EBO as E
open E using (T; fsn; fsT; cof; c0; c1; cω; cΩ; pred; Ωt; natT; sucT; 𝟏) renaming (ψ to ψᵗ)
open import OCF.Align.Uniform3Base using (ψ₀ᵗ)
open import OCF.Free.Prefix using (Z)
import OCF.Free.Prefix as ZP
import OCF.Free.Level as FL
import OCF.Align.LadderNFTree as Q
```

## §1 比较器

```agda
data Why : Set where
  kindBad : Why
  headBad : Why

γ₀ : ℕ → T
γ₀ zero = natT 1
γ₀ (suc n) = Ωt (natT (suc n))

is-ok : Maybe (Why × List ℕ) → Bool
is-ok nothing  = true
is-ok (just _) = false

module CmpO (brs : (c : Elt) → ℕ → Maybe (Σ Elt λ η → (c ⊑̂ η) × T)) where
  open Lv 𝕌
  open TT
  open XU XF using (ix)

  dfO : ℕ → ℕ → T → ∀ {π} → O zero π → Maybe (Why × List ℕ)
  dfOs : ℕ → ℕ → ℕ → T → ∀ {π} → (ℕ → O zero π) → Maybe (Why × List ℕ)
  dfO zero w t x = nothing
  dfO (suc d) w t o0 with cof t
  ... | c0 = nothing
  ... | _  = just (kindBad , [])
  dfO (suc d) w t (os x) with cof t
  ... | c1 = dfO d w (pred t) x
  ... | _  = just (kindBad , [])
  dfO (suc d) w t (ol f) with cof t
  ... | cω = dfOs w d w t f
  ... | _  = just (kindBad , [])
  dfO (suc d) w t (oŝ c t′ g) with cof t
  ... | cω = dfO d w (fsn t 0) t′
  ... | _  = just (kindBad , [])
  dfO (suc d) w t (oĉ c z zg o₀ o) with cof t
  ... | cω = dfO d w (fsn t 0) o₀
  ... | _  = just (kindBad , [])
  dfO (suc d) w t (owk _ x) = dfO (suc d) w t x
  dfO (suc d) w t (ocv _ x) = dfO (suc d) w t x
  dfO (suc d) w t (omk () _ _ _ _)
  dfO (suc d) w t (oΩ () _ _)
  dfO (suc d) w t (ocl () _ _ _ _)

  dfOs zero d w t f = nothing
  dfOs (suc n) d w t f with dfO d w (fsn t n) (f n)
  ... | just (g , p) = just (g , n ∷ p)
  ... | nothing = dfOs n d w t f

  dfL : ℕ → ℕ → T → LG → Maybe (Why × List ℕ)
  dfLs : ℕ → ℕ → ℕ → T → (ℕ → LG) → Maybe (Why × List ℕ)
  dfLb : ℕ → ℕ → ℕ → T → (c : D) → ((η : D) → c ⊑ᴰ η → LG) → Maybe (Why × List ℕ)
  dfL zero w t x = nothing
  dfL (suc d) w t zero with cof t
  ... | c0 = nothing
  ... | _  = just (kindBad , [])
  dfL (suc d) w t (suc x) with cof t
  ... | c1 = dfL d w (pred t) x
  ... | _  = just (kindBad , [])
  dfL (suc d) w t (lim f) with cof t
  ... | cω = dfLs w d w t f
  ... | _  = just (kindBad , [])
  dfL (suc d) w t (lc c t′ g) with cof t
  dfL (suc d) w t (lc c t′ g) | cω = dfL d w (fsn t 0) t′
  dfL (suc d) w t (lc c t′ g) | cΩ μ with E.cmpᵀ μ (natT (ix c))
  ...   | E.eq with dfL d w (fsT t (γ₀ (ix c))) t′
  ...     | just r = just r
  ...     | nothing = dfLb w d w t c g
  dfL (suc d) w t (lc c t′ g) | cΩ μ | E.lt = just (headBad , [])
  dfL (suc d) w t (lc c t′ g) | cΩ μ | E.gt = just (headBad , [])
  dfL (suc d) w t (lc c t′ g) | c0 = just (headBad , [])
  dfL (suc d) w t (lc c t′ g) | c1 = just (headBad , [])

  dfLs zero d w t f = nothing
  dfLs (suc n) d w t f with dfL d w (fsn t n) (f n)
  ... | just (g , p) = just (g , n ∷ p)
  ... | nothing = dfLs n d w t f

  -- 闭包的分支: c + k, 记号一侧是 fsT t (c + k). brs 认不出的下界不走.
  dfLb zero d w t c g = nothing
  dfLb (suc k) d w t c g with brs c k
  ... | nothing = dfLb k d w t c g
  ... | just (η , e , τ) with dfL d w (fsT t τ) (g η e)
  ...   | just (w′ , p) = just (w′ , (100 ∷ p))
  ...   | nothing = dfLb k d w t c g
```

## §2 分支: 下界认得出记号才走

`toT`: 字面的后继, `em`, `top`. 其余不走 (这是比较器的盲区, 见文件末).

```agda
addT : T → ℕ → T
addT τ zero = τ
addT τ (suc k) = sucT (addT τ k)

toT : (j : LF) → Raw j → Maybe T
toT j G.zero = just (natT 0)
toT j (G.suc x) with toT j x
... | just τ = just (sucT τ)
... | nothing = nothing
toT zero G.top = just (natT 1)
toT (suc k) G.top = just (Ωt (natT (natOfL (suc k))))
toT (suc k) (G.em _ x) = toT k x
toT _ _ = nothing

lglS : (j : LF) (x : Raw j) → Maybe (Lgl j x)
lglS j G.zero = just tt
lglS j (G.suc x) = lglS j x
lglS j G.top = just tt
lglS (suc k) (G.em _ x) = lglS k x
lglS _ _ = nothing

sucs : ∀ {j} → Raw j → ℕ → Raw j
sucs x zero = x
sucs x (suc k) = G.suc (sucs x k)

cp-sucs : ∀ {j} (x : Raw j) k → Cp j x (sucs x k)
cp-sucs x zero = inj₁ refl
cp-sucs x (suc k) = inj₂ (cp-sucs x k)

lgl-sucs : ∀ {j} (x : Raw j) k → Lgl j x → Lgl j (sucs x k)
lgl-sucs x zero l = l
lgl-sucs x (suc k) l = lgl-sucs x k l

brsU : (c : Elt) → ℕ → Maybe (Σ Elt λ η → (c ⊑̂ η) × T)
brsU (el j c) k with toT j c | lglS j c
... | just τ | just l = just (el j (sucs c k) , gd (cp-sucs c k , lgl-sucs c k l) , addT τ k)
... | _ | _ = nothing

module C = CmpO brsU
module Cn = CmpO (λ _ _ → nothing)
```

## §3 对 EBO: 种类, 第一支, 分支

$\psi_0(\Omega_L)$. `Tψ L` 的 `L` 就是这里的下标.

```agda
ΩL₁ : LF
ΩL₁ = Ω̂ (natF 1)

Un-Ω₁ : Un ΩL₁
Un-Ω₁ = Un-T 1

L-Ω₁ : Legal ΩL₁
L-Ω₁ = Legal-Ω̂ (natF 1) tt

Ω₁₊₁ Ω₁₂ Ω₁₂₊₁ Ω₁₃ : LF
Ω₁₊₁ = suc ΩL₁
Ω₁₂ = ΩL₁ +ᴸ ΩL₁
Ω₁₂₊₁ = suc Ω₁₂
Ω₁₃ = Ω₁₂ +ᴸ ΩL₁

L-Ω₁₂ : Legal Ω₁₂
L-Ω₁₂ = Legal-add ΩL₁ ΩL₁ L-Ω₁ L-Ω₁
U-Ω₁₂ : Un Ω₁₂
U-Ω₁₂ = Un-add ΩL₁ ΩL₁ Un-Ω₁ Un-Ω₁
L-Ω₁₃ : Legal Ω₁₃
L-Ω₁₃ = Legal-add Ω₁₂ ΩL₁ L-Ω₁₂ L-Ω₁
U-Ω₁₃ : Un Ω₁₃
U-Ω₁₃ = Un-add Ω₁₂ ΩL₁ U-Ω₁₂ Un-Ω₁

t₁ tΩ tΩ+1 tΩ2 tΩ2+1 tΩ3 : T
t₁ = natT 1
tΩ = Ωt t₁
tΩ+1 = sucT tΩ
tΩ2 = tΩ ++ tΩ
tΩ2+1 = sucT tΩ2
tΩ3 = tΩ2 ++ tΩ

tω : T
tω = ψᵗ [] 𝟏′ ∷ []
  where
  𝟏′ : T
  𝟏′ = natT 1

-- ψ₀(Ω_Ω)
a-Ω₁ : C.dfO 14 3 (ψ₀ᵗ (Ωt tΩ)) (Tψ ΩL₁ L-Ω₁ Un-Ω₁ 0) ≡ nothing
a-Ω₁ = refl
-- ψ₀(Ω_{Ω+1})
a-Ω₊₁ : C.dfO 12 3 (ψ₀ᵗ (Ωt tΩ+1)) (Tψ Ω₁₊₁ L-Ω₁ Un-Ω₁ 0) ≡ nothing
a-Ω₊₁ = refl
-- ψ₀(Ω_{Ω·2})
a-Ω₂ₘ : C.dfO 12 3 (ψ₀ᵗ (Ωt tΩ2)) (Tψ Ω₁₂ L-Ω₁₂ U-Ω₁₂ 0) ≡ nothing
a-Ω₂ₘ = refl
-- ψ₀(Ω_{Ω·2+1})
a-Ω₂₁ : C.dfO 11 3 (ψ₀ᵗ (Ωt tΩ2+1)) (Tψ Ω₁₂₊₁ L-Ω₁₂ U-Ω₁₂ 0) ≡ nothing
a-Ω₂₁ = refl
-- ψ₀(Ω_{Ω·3})
a-Ω₃ₘ : C.dfO 11 3 (ψ₀ᵗ (Ωt tΩ3)) (Tψ Ω₁₃ L-Ω₁₃ U-Ω₁₃ 0) ≡ nothing
a-Ω₃ₘ = refl
-- ψ₀(Ω_{Ω₂}), ψ₀(Ω_{Ω₃})
a-Ωn₂ : C.dfO 12 3 (ψ₀ᵗ (Ωt (Ωt (natT 2)))) (Tψ-Ωn 2 0) ≡ nothing
a-Ωn₂ = refl
a-Ωn₃ : C.dfO 12 3 (ψ₀ᵗ (Ωt (Ωt (natT 3)))) (Tψ-Ωn 3 0) ≡ nothing
a-Ωn₃ = refl
-- ψ₀(Ω_{Ω_ω})
a-Ωω : C.dfO 12 3 (ψ₀ᵗ (Ωt (Ωt tω))) (Tψ-Ωω 0) ≡ nothing
a-Ωω = refl
-- ψ₁(Ω_{Ω₂}) 读回
a-ψ₁ : C.dfL 10 3 (ψᵗ (natT 1) (Ωt (Ωt (natT 2))) ∷ []) (TT.rb (Tψ-Ωn 2 1)) ≡ nothing
a-ψ₁ = refl
a-ψ₂ : C.dfL 10 3 (ψᵗ (natT 2) (Ωt (Ωt (natT 2))) ∷ []) (TT.rb (Tψ-Ωn 2 2)) ≡ nothing
a-ψ₂ = refl
-- 对照: 比较器分得开
ctl₁ : is-ok (C.dfO 12 3 (ψ₀ᵗ (Ωt tΩ2)) (Tψ Ω₁₃ L-Ω₁₃ U-Ω₁₃ 0)) ≡ false
ctl₁ = refl
ctl₂ : is-ok (C.dfO 12 3 (ψ₀ᵗ (Ωt (Ωt (natT 3)))) (Tψ-Ωn 2 0)) ≡ false
ctl₂ = refl

-- 更高: 名字都是自然数
ΩωL Ωω₊₁ Ω₂₂ Ω₂₂₊₁ : LF
ΩωL = Ωω
Ωω₊₁ = suc Ωω
Ω₂₂ = Ω̂ (natF 2) +ᴸ Ω̂ (natF 2)
Ω₂₂₊₁ = suc Ω₂₂

L-Ωn : ∀ n → Legal (Ω̂ (natF n))
L-Ωn n = Legal-Ω̂ (natF n) (Legal-nat n)
L-Ω₂₂ : Legal Ω₂₂
L-Ω₂₂ = Legal-add (Ω̂ (natF 2)) (Ω̂ (natF 2)) (L-Ωn 2) (L-Ωn 2)
U-Ω₂₂ : Un Ω₂₂
U-Ω₂₂ = Un-add (Ω̂ (natF 2)) (Ω̂ (natF 2)) (Un-T 2) (Un-T 2)

tΩ₂ tΩ₂2 : T
tΩ₂ = Ωt (natT 2)
tΩ₂2 = tΩ₂ ++ tΩ₂

-- ψ₀(Ω_{Ω_ω+1}), ψ₀(Ω_{Ω₂·2}), ψ₀(Ω_{Ω₂·2+1}) (chain-stuck 那一带)
a-Ωω₊₁ : C.dfO 11 3 (ψ₀ᵗ (Ωt (sucT (Ωt tω)))) (Tψ Ωω₊₁ Legal-Ωω Un-Ωω 0) ≡ nothing
a-Ωω₊₁ = refl
a-Ω₂₂ : C.dfO 11 3 (ψ₀ᵗ (Ωt tΩ₂2)) (Tψ Ω₂₂ L-Ω₂₂ U-Ω₂₂ 0) ≡ nothing
a-Ω₂₂ = refl
a-Ω₂₂₁ : C.dfO 10 3 (ψ₀ᵗ (Ωt (sucT tΩ₂2))) (Tψ Ω₂₂₊₁ L-Ω₂₂ U-Ω₂₂ 0) ≡ nothing
a-Ω₂₂₁ = refl
```

## §4 界: 对塔, 宽度 3

`misQ d w`: 第 0 层的树对 `Z`, 逐闭包比下界 (`toN`), 走 $\lim$ 与分支的下标 $<w$. 对照 [LadderNFTree](LadderNFTree.lagda.md) 的 `Tᵠ m α`, 即 $\psi_0(\Omega_{\Omega\cdot(m+1)+\alpha})$. 这里读位置是恒等读法 (`Tc-id`), 紧读法没有写.

```agda
toNR : ∀ {j} → Raw j → ℕ
toNR G.zero = 0
toNR (G.suc a) = suc (toNR a)
toNR (G.lim f) = toNR (f 1)
toNR (G.lc _ _ _ _) = 0
toNR (G.em _ _) = 0
toNR G.top = 1

toNE : Elt → ℕ
toNE (el j c) = toNR c

toNI : FL.Ordᴵ → ℕ
toNI FL.zero = 0
toNI (FL.suc a) = suc (toNI a)
toNI (FL.lim f s) = toNI (f 1)

iterᴵ : FL.Ordᴵ → ℕ → FL.Ordᴵ
iterᴵ c zero = c
iterᴵ c (suc k) = FL.suc (iterᴵ c k)

up⊑ : ∀ {c} k → c FL.⊑ᴵ iterᴵ c k
up⊑ {c} zero = FL.⊑ᴵ-refl
up⊑ (suc k) = FL.⊑ᴵ-trans (up⊑ k) (FL.Sim→⊑ᴵ (λ q → FL.suc q))

_==_ : ℕ → ℕ → Bool
zero == zero = true
suc a == suc b = a == b
_ == _ = false

data Mis : Set where
  kind : List ℕ → Mis
  bnd  : List ℕ → ℕ → ℕ → Mis

misQ : ℕ → ℕ → List ℕ → ∀ {π} → TT.O (TT.natL 0) π → Z → Maybe Mis
misL : ℕ → ℕ → ℕ → List ℕ → ∀ {π} → (ℕ → TT.O (TT.natL 0) π) → (ℕ → Z) → Maybe Mis
misB : ℕ → ℕ → ℕ → List ℕ → ∀ {π} {j c} {c′ : FL.Ordᴵ} → ((η : Elt) → el j c ⊑̂ η → TT.O (TT.natL 0) π) → ((η : FL.Ordᴵ) → c′ FL.⊑ᴵ η → Z) → Maybe Mis
misQ zero w p _ _ = nothing
misQ (suc d) w p TT.o0 Z.zero = nothing
misQ (suc d) w p (TT.os x) (Z.suc y) = misQ d w (1 ∷ p) x y
misQ (suc d) w p (TT.ol f) (Z.lim g) = misL w d w p f g
misQ (suc d) w p (TT.owk _ x) y = misQ (suc d) w p x y
misQ (suc d) w p (TT.ocv _ x) y = misQ (suc d) w p x y
misQ (suc d) w p (TT.oŝ (el j c) o₀ o) (Z.ĉᴸ c′ z′ zg′ o₀′ o′) with toNR c == toNI c′
... | false = just (bnd p (toNR c) (toNI c′))
... | true with misQ d w (2 ∷ p) o₀ o₀′
...   | just m = just m
...   | nothing = misB w d w p o o′
misQ (suc d) w p (TT.oĉ (el j c) _ _ o₀ o) (Z.ĉᴸ c′ z′ zg′ o₀′ o′) with toNR c == toNI c′
... | false = just (bnd p (toNR c) (toNI c′))
... | true with misQ d w (2 ∷ p) o₀ o₀′
...   | just m = just m
...   | nothing = misB w d w p o o′
misQ (suc d) w p _ _ = just (kind p)

misL zero d w p f g = nothing
misL (suc n) d w p f g with misQ d w (n ∷ p) (f n) (g n)
... | just m = just m
... | nothing = misL n d w p f g

misB zero d w p o o′ = nothing
misB (suc k) d w p {j = j} {c = c} {c′ = c′} o o′ with lglS j c
... | nothing = nothing
... | just l with misQ d w (300 ∷ p) (o (el j (sucs c k)) (gd (cp-sucs c k , lgl-sucs c k l))) (o′ (iterᴵ c′ k) (up⊑ k))
...   | just m = just m
...   | nothing = misB k d w p o o′

qΩ qΩ+1 qΩ2 : Z
qΩ = ZP.toZ (Q.Tᵠ 0 FL.zero {FL.zero} {FL.suc FL.zero} (tt , (λ q → q)) FL.zero)
qΩ+1 = ZP.toZ (Q.Tᵠ 0 (FL.suc FL.zero) {FL.zero} {FL.suc FL.zero} (tt , (λ q → q)) FL.zero)
qΩ2 = ZP.toZ (Q.Tᵠ 1 FL.zero {FL.zero} {FL.suc FL.zero} (tt , (λ q → q)) FL.zero)

b-Ω : misQ 10 3 [] (Tψ ΩL₁ L-Ω₁ Un-Ω₁ 0) qΩ ≡ nothing
b-Ω = refl

-- 恒等读法的界不紧: 与 GuardTight 的 Tc-id 同一个现象, 这里是测试, 记下结果. 紧读法在 𝕌 上没有写.
b-Ω+1 : misQ 10 3 [] (Tψ Ω₁₊₁ L-Ω₁ Un-Ω₁ 0) qΩ+1 ≡ just (bnd (2 ∷ 2 ∷ 2 ∷ 0 ∷ 300 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ []) 3 2)
b-Ω+1 = refl
b-Ω+1₂ : misQ 10 2 [] (Tψ Ω₁₊₁ L-Ω₁ Un-Ω₁ 0) qΩ+1 ≡ just (bnd (0 ∷ 1 ∷ 2 ∷ 1 ∷ 1 ∷ 1 ∷ 300 ∷ 1 ∷ []) 2 1)
b-Ω+1₂ = refl
b-Ω2 : misQ 10 3 [] (Tψ Ω₁₂ L-Ω₁₂ U-Ω₁₂ 0) qΩ2 ≡ just (bnd (2 ∷ 2 ∷ 0 ∷ 300 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ []) 2 1)
b-Ω2 = refl
```
