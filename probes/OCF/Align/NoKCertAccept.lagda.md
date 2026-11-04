# 验收: 紧读法对塔

> **验收节.** 记号与塔只在本文件. 结论写在 [NoKCert](NoKCert.lagda.md). **全部是有限测试, 不是证明.** `misQ` 逐字取自 [LevelNoKAccept](LevelNoKAccept.lagda.md): 第 0 层的树对塔 [LadderNFTree](LadderNFTree.lagda.md) 的 `Z`, 逐闭包比下界 (`toN`, 取极限的第 1 项读成自然数), 走 $\lim$ 与分支 $c+k$ 的下标 $<w$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoKCertAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.LevelNoKLv using (module Lv)
open import OCF.Align.LevelFixCore
open import OCF.Align.LevelFixVal
open import OCF.Align.LevelNoKU
import OCF.Align.LevelNoKFold as FF
module TT = FF.TT
open import OCF.Align.NoKCertRd
open import OCF.Align.NoKCertTc
open import OCF.Free.Prefix using (Z)
import OCF.Free.Prefix as ZP
import OCF.Free.Level as FL
import OCF.Align.LadderNFTree as Q
```

```agda
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


ΩL₁ Ω₁₊₁ Ω₁₊₂ Ω₁₂ Ω₁₂₊₁ Ω₁₃ : LF
ΩL₁ = Ω̂ (natF 1)
Ω₁₊₁ = suc ΩL₁
Ω₁₊₂ = suc Ω₁₊₁
Ω₁₂ = ΩL₁ +ᴸ ΩL₁
Ω₁₂₊₁ = suc Ω₁₂
Ω₁₃ = Ω₁₂ +ᴸ ΩL₁

L-Ω₁ : Legal ΩL₁
L-Ω₁ = Legal-Ω̂ (natF 1) tt
L-Ω₁₂ : Legal Ω₁₂
L-Ω₁₂ = Legal-add ΩL₁ ΩL₁ L-Ω₁ L-Ω₁
L-Ω₁₃ : Legal Ω₁₃
L-Ω₁₃ = Legal-add Ω₁₂ ΩL₁ L-Ω₁₂ L-Ω₁

c-Ω₁ : Cnt ΩL₁
c-Ω₁ = cnt-Ω̂ (natF 1) tt
c-Ω₁₂ : Cnt Ω₁₂
c-Ω₁₂ = cnt-add ΩL₁ ΩL₁ c-Ω₁ c-Ω₁
c-Ω₁₃ : Cnt Ω₁₃
c-Ω₁₃ = cnt-add Ω₁₂ ΩL₁ c-Ω₁₂ c-Ω₁

qΩ+2 qΩ2+1 qΩ3 : Z
qΩ+2 = ZP.toZ (Q.Tᵠ 0 (FL.suc (FL.suc FL.zero)) {FL.zero} {FL.suc FL.zero} (tt , (λ q → q)) FL.zero)
qΩ2+1 = ZP.toZ (Q.Tᵠ 1 (FL.suc FL.zero) {FL.zero} {FL.suc FL.zero} (tt , (λ q → q)) FL.zero)
qΩ3 = ZP.toZ (Q.Tᵠ 2 FL.zero {FL.zero} {FL.suc FL.zero} (tt , (λ q → q)) FL.zero)

-- 沿给定路径比界. 步子: 极限的下标, 闭包的第一支 (2), 闭包的分支 c+k (300, 试 k < w), 后继 (1). 走不下去就停 (答 nothing)
misP : ℕ → List ℕ → ∀ {π} → TT.O (TT.natL 0) π → Z → Maybe Mis
misPB : ℕ → ℕ → List ℕ → ∀ {π} {j c} {c′ : FL.Ordᴵ} → ((η : Elt) → el j c ⊑̂ η → TT.O (TT.natL 0) π) → ((η : FL.Ordᴵ) → c′ FL.⊑ᴵ η → Z) → Maybe Mis
misP w p (TT.owk _ x) y = misP w p x y
misP w p (TT.ocv _ x) y = misP w p x y
misP w [] _ _ = nothing
misP w (_ ∷ p) TT.o0 Z.zero = nothing
misP w (_ ∷ p) (TT.os x) (Z.suc y) = misP w p x y
misP w (n ∷ p) (TT.ol f) (Z.lim g) = misP w p (f n) (g n)
misP w (s ∷ p) (TT.oŝ (el j c) o₀ o) (Z.ĉᴸ c′ z′ zg′ o₀′ o′) with toNR c == toNI c′ | s == 300
... | false | _ = just (bnd [] (toNR c) (toNI c′))
... | true | false = misP w p o₀ o₀′
... | true | true = misPB w w p {j = j} {c = c} {c′ = c′} o o′
misP w (s ∷ p) (TT.oĉ (el j c) _ _ o₀ o) (Z.ĉᴸ c′ z′ zg′ o₀′ o′) with toNR c == toNI c′ | s == 300
... | false | _ = just (bnd [] (toNR c) (toNI c′))
... | true | false = misP w p o₀ o₀′
... | true | true = misPB w w p {j = j} {c = c} {c′ = c′} o o′
misP w (_ ∷ p) _ _ = just (kind p)

misPB zero w p o o′ = nothing
misPB (suc k) w p {j = j} {c = c} {c′ = c′} o o′ with lglS j c
... | nothing = nothing
... | just l with misP w p (o (el j (sucs c k)) (gd (cp-sucs c k , lgl-sucs c k l))) (o′ (iterᴵ c′ k) (up⊑ k))
...   | just m = just m
...   | nothing = misPB k w p {j = j} {c = c} {c′ = c′} o o′

-- 路径上比过的闭包数, 用来看比较不是空的. 走法同 misP, 不看对面
visit : ℕ → List ℕ → ∀ {π} → TT.O (TT.natL 0) π → ℕ
visitB : ℕ → ℕ → List ℕ → ∀ {π} {j c} → ((η : Elt) → el j c ⊑̂ η → TT.O (TT.natL 0) π) → ℕ
visit w p (TT.owk _ x) = visit w p x
visit w p (TT.ocv _ x) = visit w p x
visit w [] _ = 0
visit w (_ ∷ p) TT.o0 = 0
visit w (_ ∷ p) (TT.os x) = visit w p x
visit w (n ∷ p) (TT.ol f) = visit w p (f n)
visit w (s ∷ p) (TT.oŝ (el j c) o₀ o) with s == 300
... | false = suc (visit w p o₀)
... | true = suc (visitB w w p {j = j} {c = c} o)
visit w (s ∷ p) (TT.oĉ (el j c) _ _ o₀ o) with s == 300
... | false = suc (visit w p o₀)
... | true = suc (visitB w w p {j = j} {c = c} o)
visit w (_ ∷ p) (TT.omk () _ _ _ _)
visit w (_ ∷ p) (TT.oΩ () _ _)
visit w (_ ∷ p) (TT.ocl () _ _ _ _)

_+ᴺ_ : ℕ → ℕ → ℕ
zero +ᴺ b = b
suc a +ᴺ b = suc (a +ᴺ b)

visitB zero w p o = 0
visitB (suc k) w p {j = j} {c = c} o with lglS j c
... | nothing = 0
... | just l = visit w p (o (el j (sucs c k)) (gd (cp-sucs c k , lgl-sucs c k l))) +ᴺ visitB k w p {j = j} {c = c} o
```
