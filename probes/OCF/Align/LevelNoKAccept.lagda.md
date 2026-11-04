# 验收: 对 EBO 的有限比较

> **验收节.** 记号只在本文件 (这个文件不要求闭包干净). 结论写在 [LevelNoK](LevelNoK.lagda.md). **全部是有限测试, 不是证明.** §1-§4 由 [LevelFixAccept](LevelFixAccept.lagda.md) 用脚本改写, 去掉 `Un`: 比较器 `dfO`, `dfL` 看种类, 闭包的共尾层, 第一支, 走分支 $c+k$, 不看界; 界用 `misQ`. **§5 是新的:** 新树对 [LevelFixTree](LevelFixTree.lagda.md) 的树直接比, 看种类, 下界与链的指纹 (`fpE`), 第一支, 分支, 宽度 3. 另外有旧树没有的闭项的测试. 全文编译约 5 分钟.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LevelNoKAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
import OCF.Align.LevelFixU as OU
import OCF.Align.LevelFixFold as OF
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.LevelNoKLv using (module Lv)
open import OCF.Align.LevelNoKX using (XU)
open import OCF.Align.LevelFixCore
open import OCF.Align.LevelFixVal
open import OCF.Align.LevelNoKU
open import OCF.Align.LevelNoKFold hiding (O; rb; Tn; T⁰; natL)
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

L-Ω₁ : Legal ΩL₁
L-Ω₁ = Legal-Ω̂ (natF 1) tt

Ω₁₊₁ Ω₁₂ Ω₁₂₊₁ Ω₁₃ : LF
Ω₁₊₁ = suc ΩL₁
Ω₁₂ = ΩL₁ +ᴸ ΩL₁
Ω₁₂₊₁ = suc Ω₁₂
Ω₁₃ = Ω₁₂ +ᴸ ΩL₁

L-Ω₁₂ : Legal Ω₁₂
L-Ω₁₂ = Legal-add ΩL₁ ΩL₁ L-Ω₁ L-Ω₁
L-Ω₁₃ : Legal Ω₁₃
L-Ω₁₃ = Legal-add Ω₁₂ ΩL₁ L-Ω₁₂ L-Ω₁

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
a-Ω₁ : C.dfO 14 3 (ψ₀ᵗ (Ωt tΩ)) (Tψ ΩL₁ L-Ω₁ 0) ≡ nothing
a-Ω₁ = refl
-- ψ₀(Ω_{Ω+1})
a-Ω₊₁ : C.dfO 12 3 (ψ₀ᵗ (Ωt tΩ+1)) (Tψ Ω₁₊₁ L-Ω₁ 0) ≡ nothing
a-Ω₊₁ = refl
-- ψ₀(Ω_{Ω·2})
a-Ω₂ₘ : C.dfO 12 3 (ψ₀ᵗ (Ωt tΩ2)) (Tψ Ω₁₂ L-Ω₁₂ 0) ≡ nothing
a-Ω₂ₘ = refl
-- ψ₀(Ω_{Ω·2+1})
a-Ω₂₁ : C.dfO 11 3 (ψ₀ᵗ (Ωt tΩ2+1)) (Tψ Ω₁₂₊₁ L-Ω₁₂ 0) ≡ nothing
a-Ω₂₁ = refl
-- ψ₀(Ω_{Ω·3})
a-Ω₃ₘ : C.dfO 11 3 (ψ₀ᵗ (Ωt tΩ3)) (Tψ Ω₁₃ L-Ω₁₃ 0) ≡ nothing
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
ctl₁ : is-ok (C.dfO 12 3 (ψ₀ᵗ (Ωt tΩ2)) (Tψ Ω₁₃ L-Ω₁₃ 0)) ≡ false
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

tΩ₂ tΩ₂2 : T
tΩ₂ = Ωt (natT 2)
tΩ₂2 = tΩ₂ ++ tΩ₂

-- ψ₀(Ω_{Ω_ω+1}), ψ₀(Ω_{Ω₂·2}), ψ₀(Ω_{Ω₂·2+1}) (chain-stuck 那一带)
a-Ωω₊₁ : C.dfO 11 3 (ψ₀ᵗ (Ωt (sucT (Ωt tω)))) (Tψ Ωω₊₁ Legal-Ωω 0) ≡ nothing
a-Ωω₊₁ = refl
a-Ω₂₂ : C.dfO 11 3 (ψ₀ᵗ (Ωt tΩ₂2)) (Tψ Ω₂₂ L-Ω₂₂ 0) ≡ nothing
a-Ω₂₂ = refl
a-Ω₂₂₁ : C.dfO 10 3 (ψ₀ᵗ (Ωt (sucT tΩ₂2))) (Tψ Ω₂₂₊₁ L-Ω₂₂ 0) ≡ nothing
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

b-Ω : misQ 10 3 [] (Tψ ΩL₁ L-Ω₁ 0) qΩ ≡ nothing
b-Ω = refl

-- 恒等读法的界不紧: 与 GuardTight 的 Tc-id 同一个现象, 这里是测试, 记下结果. 紧读法在 𝕌 上没有写.
b-Ω+1 : misQ 10 3 [] (Tψ Ω₁₊₁ L-Ω₁ 0) qΩ+1 ≡ just (bnd (2 ∷ 2 ∷ 2 ∷ 0 ∷ 300 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ []) 3 2)
b-Ω+1 = refl
b-Ω+1₂ : misQ 10 2 [] (Tψ Ω₁₊₁ L-Ω₁ 0) qΩ+1 ≡ just (bnd (0 ∷ 1 ∷ 2 ∷ 1 ∷ 1 ∷ 1 ∷ 300 ∷ 1 ∷ []) 2 1)
b-Ω+1₂ = refl
b-Ω2 : misQ 10 3 [] (Tψ Ω₁₂ L-Ω₁₂ 0) qΩ2 ≡ just (bnd (2 ∷ 2 ∷ 0 ∷ 300 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ []) 2 1)
b-Ω2 = refl
```

## §5 新树对旧树: 直接比

`fpL`: 层号的有界指纹 (种类, 节点的名字, 下界读回, 第一支, 字面后继的分支). `fpE`: 下标的指纹, 名字加读回. `cmpᵒ`: 第 0 层的树逐节点比, 闭包比下界与链的指纹, 第一支, 分支 $c+k$, $k<w$. 结果 `ok n`: 比了 $n$ 个节点, 都一致. 下界不是字面后继, `em`, `top` 时两边都不走分支 (盲区, 与 `brsU` 同).

```agda
_+ₙ_ : ℕ → ℕ → ℕ
zero +ₙ b = b
suc a +ₙ b = suc (a +ₙ b)

fpL : ℕ → LF → List ℕ
fpL zero _ = []
fpL (suc d) zero = 0 ∷ []
fpL (suc d) (suc a) = 1 ∷ fpL d a
fpL (suc d) (lim f) = 2 ∷ (fpL d (f 1) ++ (8 ∷ fpL d (f 2)))
fpL (suc d) (lc k c t g) with lglS k c
... | nothing = 3 ∷ (fpL d k ++ (7 ∷ (fpL d (up k c) ++ (8 ∷ fpL d t))))
... | just l = 4 ∷ (fpL d k ++ (7 ∷ (fpL d (up k c) ++ (8 ∷ (fpL d t ++ (6 ∷ fpL d (g (G.suc c) (cp-sucs c 1 , l))))))))

eqL : List ℕ → List ℕ → Bool
eqL [] [] = true
eqL (a ∷ x) (b ∷ y) with a == b
... | true = eqL x y
... | false = false
eqL _ _ = false

fpE : (j : LF) → Raw j → List ℕ
fpE j c = toNR c ∷ (fpL 4 j ++ (9 ∷ fpL 4 (up j c)))

data Res : Set where
  bad : List ℕ → Res
  ok  : ℕ → Res

_⊕ᵣ_ : Res → Res → Res
bad p ⊕ᵣ _ = bad p
ok a ⊕ᵣ bad p = bad p
ok a ⊕ᵣ ok b = ok (a +ₙ b)

cmpᵒ : ℕ → ℕ → List ℕ → ∀ {π π′} → OF.TT.O (OF.TT.natL 0) π → TT.O (TT.natL 0) π′ → Res
cmpL : ℕ → ℕ → ℕ → List ℕ → ∀ {π π′} → (ℕ → OF.TT.O (OF.TT.natL 0) π) → (ℕ → TT.O (TT.natL 0) π′) → Res
cmpB : ℕ → ℕ → ℕ → List ℕ → ∀ {π π′ j j′} {c : Raw j} {c′ : Raw j′} →
       ((η : OU.Elt) → OU.el j c OU.⊑̂ η → OF.TT.O (OF.TT.natL 0) π) → ((η : Elt) → el j′ c′ ⊑̂ η → TT.O (TT.natL 0) π′) → Res
cmpZ : ℕ → List ℕ → ∀ {j j′} {c : Raw j} {c′ : Raw j′} → ((η : OU.Elt) → OU.el j c OU.⊑̂ η → OU.U.LG) → ((η : Elt) → el j′ c′ ⊑̂ η → U.LG) → Res

cmpᵒ zero w p _ _ = ok 0
cmpᵒ (suc d) w p (OF.TT.owk _ x) y = cmpᵒ (suc d) w p x y
cmpᵒ (suc d) w p (OF.TT.ocv _ x) y = cmpᵒ (suc d) w p x y
cmpᵒ (suc d) w p x (TT.owk _ y) = cmpᵒ (suc d) w p x y
cmpᵒ (suc d) w p x (TT.ocv _ y) = cmpᵒ (suc d) w p x y
cmpᵒ (suc d) w p OF.TT.o0 TT.o0 = ok 1
cmpᵒ (suc d) w p (OF.TT.os x) (TT.os y) = ok 1 ⊕ᵣ cmpᵒ d w (1 ∷ p) x y
cmpᵒ (suc d) w p (OF.TT.ol f) (TT.ol g) = cmpL w d w p f g
cmpᵒ (suc d) w p (OF.TT.oŝ (OU.el j c) x₀ o) (TT.oŝ (el j′ c′) y₀ o′) with eqL (fpE j c) (fpE j′ c′)
... | false = bad (5 ∷ p)
... | true = ok 1 ⊕ᵣ (cmpᵒ d w (2 ∷ p) x₀ y₀ ⊕ᵣ cmpB w d w p {j = j} {j′} {c} {c′} o o′)
cmpᵒ (suc d) w p (OF.TT.oĉ (OU.el j c) z zg x₀ o) (TT.oĉ (el j′ c′) z′ zg′ y₀ o′) with eqL (fpE j c) (fpE j′ c′) | eqL (fpL 4 (OU.fromU z)) (fpL 4 (fromU z′))
... | true | true = ok 1 ⊕ᵣ (cmpᵒ d w (2 ∷ p) x₀ y₀ ⊕ᵣ (cmpB w d w p {j = j} {j′} {c} {c′} o o′ ⊕ᵣ cmpZ w p {j} {j′} {c} {c′} zg zg′))
... | _ | _ = bad (5 ∷ p)
cmpᵒ (suc d) w p _ _ = bad (6 ∷ p)

cmpL zero d w p f g = ok 0
cmpL (suc n) d w p f g = cmpᵒ d w (n ∷ p) (f n) (g n) ⊕ᵣ cmpL n d w p f g

cmpB zero d w p o o′ = ok 0
cmpB (suc k) d w p {j = j} {j′} {c} {c′} o o′ with lglS j c | lglS j′ c′
... | nothing | nothing = ok 0
... | just l | just l′ =
  cmpᵒ d w (300 ∷ p) (o (OU.el j (sucs c k)) (OU.gd (cp-sucs c k , lgl-sucs c k l))) (o′ (el j′ (sucs c′ k)) (gd (cp-sucs c′ k , lgl-sucs c′ k l′)))
  ⊕ᵣ cmpB k d w p {j = j} {j′} {c} {c′} o o′
... | _ | _ = bad (7 ∷ p)

cmpZ zero p zg zg′ = ok 0
cmpZ (suc k) p {j} {j′} {c} {c′} zg zg′ with lglS j c | lglS j′ c′
... | nothing | nothing = ok 0
... | just l | just l′ with eqL (fpL 4 (OU.fromU (zg (OU.el j (sucs c k)) (OU.gd (cp-sucs c k , lgl-sucs c k l))))) (fpL 4 (fromU (zg′ (el j′ (sucs c′ k)) (gd (cp-sucs c′ k , lgl-sucs c′ k l′)))))
...   | true = cmpZ k p {j} {j′} {c} {c′} zg zg′
...   | false = bad (8 ∷ p)
cmpZ (suc k) p zg zg′ | _ | _ = bad (7 ∷ p)

-- 旧树的 Un 证明
OU-Ω₁ : OU.Un ΩL₁
OU-Ω₁ = OU.Un-T 1
OU-Ω₁₂ : OU.Un Ω₁₂
OU-Ω₁₂ = OU.Un-add ΩL₁ ΩL₁ OU-Ω₁ OU-Ω₁
OU-Ω₁₃ : OU.Un Ω₁₃
OU-Ω₁₃ = OU.Un-add Ω₁₂ ΩL₁ OU-Ω₁₂ OU-Ω₁
OU-Ω₂₂ : OU.Un Ω₂₂
OU-Ω₂₂ = OU.Un-add (Ω̂ (natF 2)) (Ω̂ (natF 2)) (OU.Un-T 2) (OU.Un-T 2)

Tψ′ : (x : LF) → Legal x → OU.Un x → (n : ℕ) → OF.TT.T⁰ n
Tψ′ = OF.Tψ

isOk : Res → Bool
isOk (ok _) = true
isOk (bad _) = false

-- 新树的计数: (节点数, 名字不是自然数时读的分支数). 能算出字面的数就说明没有卡在任何 subst 上; 这不说明值对.
nonNat : LF → Bool
nonNat zero = false
nonNat (suc a) = nonNat a
nonNat (lim _) = true
nonNat (lc _ _ _ _) = true

_+₂_ : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ
(a , b) +₂ (c , d) = (a +ₙ c) , (b +ₙ d)

cnt : ℕ → ℕ → ∀ {π} → TT.O (TT.natL 0) π → ℕ × ℕ
cntL : ℕ → ℕ → ℕ → ∀ {π} → (ℕ → TT.O (TT.natL 0) π) → ℕ × ℕ
cntB : ℕ → ℕ → ℕ → ∀ {π j} {c : Raw j} → ((η : Elt) → el j c ⊑̂ η → TT.O (TT.natL 0) π) → ℕ × ℕ
cnt zero w _ = 0 , 0
cnt (suc d) w (TT.owk _ x) = cnt (suc d) w x
cnt (suc d) w (TT.ocv _ x) = cnt (suc d) w x
cnt (suc d) w TT.o0 = 1 , 0
cnt (suc d) w (TT.os x) = (1 , 0) +₂ cnt d w x
cnt (suc d) w (TT.ol f) = (1 , 0) +₂ cntL w d w f
cnt (suc d) w (TT.oŝ (el j c) x₀ o) = (1 , 0) +₂ (cnt d w x₀ +₂ cntB w d w {j = j} {c} o)
cnt (suc d) w (TT.oĉ (el j c) _ _ x₀ o) = (1 , 0) +₂ (cnt d w x₀ +₂ cntB w d w {j = j} {c} o)
cnt (suc d) w (TT.omk () _ _ _ _)
cnt (suc d) w (TT.oΩ () _ _)
cnt (suc d) w (TT.ocl () _ _ _ _)

cntL zero d w f = 0 , 0
cntL (suc n) d w f = cnt d w (f n) +₂ cntL n d w f

cntB zero d w o = 0 , 0
cntB (suc k) d w {j = j} {c} o with lglS j c | nonNat j
... | nothing | _ = 0 , 0
... | just l | b = ((tag b) , 0 ) +₂ᵣ (cnt d w (o (el j (sucs c k)) (gd (cp-sucs c k , lgl-sucs c k l))) +₂ cntB k d w {j = j} {c} o)
  where
  tag : Bool → ℕ
  tag true = 1
  tag false = 0
  _+₂ᵣ_ : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ
  (a , _) +₂ᵣ (c′ , d′) = c′ , (a +ₙ d′)

-- ψ₀(Λ) 的第 n 项对记号的 ψ₀(Ω-塔_n)
dfΛ : ℕ → ℕ → ℕ → ∀ {π} → TT.O (TT.natL 0) π → Maybe (Why × List ℕ)
dfΛ m d w (TT.owk _ x) = dfΛ m d w x
dfΛ m d w (TT.ocv _ x) = dfΛ m d w x
dfΛ m d w (TT.ol f) = go m
  where
  go : ℕ → Maybe (Why × List ℕ)
  go zero = nothing
  go (suc n) with C.dfO d w (ψ₀ᵗ (E.ΩTower n)) (f n)
  ... | just (g , p) = just (g , n ∷ p)
  ... | nothing = go n
dfΛ m d w _ = just (kindBad , [])
```

**新树对旧树 (有限测试).** 深度, 宽度写在陈述里. `ok n`: 比了 $n$ 个节点全部一致, 包括下界与链的指纹. 对照 `ctl-d₁`, `ctl-d₂`: 比较器分得开; `ctl-d₂` 败在下界指纹 (路径头 5), 所以它确实看界.

```agda
d-x₀ : cmpᵒ 10 3 [] OF.x̂₀ (x̂ 0) ≡ ok 6
d-x₀ = refl
d-x₁ : cmpᵒ 10 3 [] OF.x̂₁ (x̂ 1) ≡ ok 254
d-x₁ = refl
d-x₂ : cmpᵒ 10 3 [] OF.x̂₂ (x̂ 2) ≡ ok 1209
d-x₂ = refl
d-Ω₊₁ : cmpᵒ 6 3 [] (Tψ′ Ω₁₊₁ L-Ω₁ OU-Ω₁ 0) (Tψ Ω₁₊₁ L-Ω₁ 0) ≡ ok 130
d-Ω₊₁ = refl
d-Ω₂ₘ : cmpᵒ 6 3 [] (Tψ′ Ω₁₂ L-Ω₁₂ OU-Ω₁₂ 0) (Tψ Ω₁₂ L-Ω₁₂ 0) ≡ ok 123
d-Ω₂ₘ = refl
d-Ω₂₁ : cmpᵒ 6 3 [] (Tψ′ Ω₁₂₊₁ L-Ω₁₂ OU-Ω₁₂ 0) (Tψ Ω₁₂₊₁ L-Ω₁₂ 0) ≡ ok 129
d-Ω₂₁ = refl
d-Ω₃ₘ : cmpᵒ 6 3 [] (Tψ′ Ω₁₃ L-Ω₁₃ OU-Ω₁₃ 0) (Tψ Ω₁₃ L-Ω₁₃ 0) ≡ ok 187
d-Ω₃ₘ = refl
d-Ωn₂ : cmpᵒ 6 3 [] (OF.Tψ-Ωn 2 0) (Tψ-Ωn 2 0) ≡ ok 129
d-Ωn₂ = refl
d-Ωn₃ : cmpᵒ 6 3 [] (OF.Tψ-Ωn 3 0) (Tψ-Ωn 3 0) ≡ ok 162
d-Ωn₃ = refl
d-Ωω : cmpᵒ 6 3 [] (OF.Tψ-Ωω 0) (Tψ-Ωω 0) ≡ ok 102
d-Ωω = refl
d-Ωω₊₁ : cmpᵒ 6 3 [] (Tψ′ Ωω₊₁ Legal-Ωω OU.Un-Ωω 0) (Tψ Ωω₊₁ Legal-Ωω 0) ≡ ok 107
d-Ωω₊₁ = refl
r-ψ₁ : eqL (fpL 6 (OU.fromU (OF.TT.rb (OF.Tψ-Ωn 2 1)))) (fpL 6 (fromU (TT.rb (Tψ-Ωn 2 1)))) ≡ true
r-ψ₁ = refl
r-ψ₂ : eqL (fpL 6 (OU.fromU (OF.TT.rb (OF.Tψ-Ωn 2 2)))) (fpL 6 (fromU (TT.rb (Tψ-Ωn 2 2)))) ≡ true
r-ψ₂ = refl
ctl-d₁ : cmpᵒ 6 3 [] (Tψ′ Ω₁₂ L-Ω₁₂ OU-Ω₁₂ 0) (Tψ Ω₁₃ L-Ω₁₃ 0) ≡ bad (6 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ [])
ctl-d₁ = refl
ctl-d₂ : cmpᵒ 6 3 [] (OF.Tψ-Ωn 2 0) (Tψ-Ωn 3 0) ≡ bad (5 ∷ [])
ctl-d₂ = refl
```

下面两条太慢 (几小时), **不在这个文件里编译**. 用同样的比较器单独跑过一次, 陈述写错值, 从报错读出的数:

```text
cmpᵒ 6 3 [] (Tψ′ Ω₂₂ L-Ω₂₂ OU-Ω₂₂ 0) (Tψ Ω₂₂ L-Ω₂₂ 0)     → ok 330   (Ω₂·2, 约 5.8 小时)
cmpᵒ 6 3 [] (Tψ′ Ω₂₂₊₁ L-Ω₂₂ OU-Ω₂₂ 0) (Tψ Ω₂₂₊₁ L-Ω₂₂ 0) → ok 261   (Ω₂·2+1, 约 2.3 小时)
```

**旧树没有的闭项 (有限测试).** `x̂ n`, $n\ge 3$, `ψ₀Λ`, 以及 $\psi_0(\Omega_{\Omega_{\omega+1}})$ 在 [LevelFixFold](LevelFixFold.lagda.md) 里只是条件定义. 这里能算. `e-*`: 对 EBO, 比较器 `dfO`: **不看界, 不走第 0 层闭包的分支**, 所以这是很弱的测试. `n-*`: 只数节点, `(节点数, 名字不是自然数时读的分支数)`: 算出字面的数说明没有卡在 `subst` 上, **不说明值对**. $x_3$, $\psi_0(\Lambda)$ 在这个深度宽度下没有读到非自然数名字的分支; $x_4$ 读到 204 次, $\Omega_{\Omega_{\omega+1}}$ 读到 3 次.

```agda
e-x₀ : C.dfO 12 3 (ψ₀ᵗ (E.ΩTower 0)) (x̂ 0) ≡ nothing
e-x₀ = refl
e-x₁ : C.dfO 12 3 (ψ₀ᵗ (E.ΩTower 1)) (x̂ 1) ≡ nothing
e-x₁ = refl
e-x₂ : C.dfO 12 3 (ψ₀ᵗ (E.ΩTower 2)) (x̂ 2) ≡ nothing
e-x₂ = refl
e-x₃ : C.dfO 12 3 (ψ₀ᵗ (E.ΩTower 3)) (x̂ 3) ≡ nothing
e-x₃ = refl
e-x₄ : C.dfO 12 3 (ψ₀ᵗ (E.ΩTower 4)) (x̂ 4) ≡ nothing
e-x₄ = refl
ctl-x₃ : is-ok (C.dfO 12 3 (ψ₀ᵗ (E.ΩTower 4)) (x̂ 3)) ≡ false
ctl-x₃ = refl
e-Λ : dfΛ 4 8 3 ψ₀Λ ≡ nothing
e-Λ = refl

n-x₃ : cnt 6 3 (x̂ 3) ≡ (731 , 0)
n-x₃ = refl
n-x₄ : cnt 6 3 (x̂ 4) ≡ (1069 , 204)
n-x₄ = refl
n-Ωω₁ : cnt 6 3 (Tψ (Ω̂ (suc (lim natF))) (Legal-Ω̂ (suc (lim natF)) Legal-ω) 0) ≡ (589 , 3)
n-Ωω₁ = refl
n-Λ : cnt 6 3 ψ₀Λ ≡ (207 , 0)
n-Λ = refl
```
