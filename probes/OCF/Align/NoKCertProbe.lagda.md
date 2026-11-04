# 定位: 高层链点过不过守卫 (有限测试)

> 不含记号. 结论写在 [NoKCert](NoKCert.lagda.md). **全部是有限测试, 不是证明.** 走第 0 层的树, 到第一个带链的闭包 (`oĉ`), 看计值要的两件事:
>
> 1. 守卫的第一位置: 下界 $c_0$ 读成层号 `up j c`, 是否在链点 $z$ 的第一路径上. 比较器 `eqL`: 有界结构比较 (头, 下界的数值, 第一支, 极限的前 `w` 项). **它只能放过假的相等, 不能冤枉:** `eqL` 答否时, 字面的 `≡` 一定不成立 (只比结构). `onF` 三值: `no` 只说第一路径 (极限取第 `w` 项) 走到底没有, `unk` 是步数用完. 第一路径上的极限只看第 `w` 项, 所以 `onFirst` 答否只说明第 `w` 项上没有, 不说明更大的项也没有.
> 2. `Lgl` 的步进: 链点里第一路径上的极限, 相邻项是否字面第一位置, 只查前 `w` 项.
>
> 盲区: 不走分支 `bra`; 深度有界; 第 0 层的 `oŝ` 只走第一支.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoKCertProbe where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.LevelFixCore
open import OCF.Align.LevelFixVal
open import OCF.Align.LevelNoKU hiding (ŝ)
open import OCF.Align.LevelNoKLv using (module Lv)
open Lv 𝕌 using (LG)
import OCF.Align.LevelNoKFold as FF
open FF using (O; T⁰)
open FF.TT using (o0; os; ol; oŝ; oĉ; owk; ocv; omk; oΩ; ocl)

_==ᴺ_ : ℕ → ℕ → Bool
zero ==ᴺ zero = true
suc a ==ᴺ suc b = a ==ᴺ b
_ ==ᴺ _ = false

numR : ∀ {j} → Raw j → ℕ
numR G.zero = 0
numR (G.suc a) = suc (numR a)
numR (G.lim f) = 100
numR (G.lc _ _ _ _) = 200
numR (G.em _ _) = 300
numR G.top = 400

layer : LF → ℕ
layer LF.zero = 0
layer (LF.suc a) = suc (layer a)
layer (LF.lim _) = 500
layer (lc _ _ _ _) = 600

numE : Elt → ℕ × ℕ
numE (el j c) = layer j , numR c

allN : ℕ → (ℕ → Bool) → Bool
allN zero p = true
allN (suc n) p = allN n p ∧ p n

anyN : ℕ → (ℕ → Bool) → Bool
anyN zero p = false
anyN (suc n) p = anyN n p ∨ p n

-- 有界结构比较. 答否 ⟹ 字面不等 (头不同, 或下界的头/层不同, 或子项不等)
eqL : ℕ → ℕ → LG → LG → Bool
eqL zero w _ _ = true
eqL (suc d) w U.zero U.zero = true
eqL (suc d) w (U.suc a) (U.suc b) = eqL d w a b
eqL (suc d) w (U.lim f) (U.lim g) = allN w (λ n → eqL d w (f n) (g n))
eqL (suc d) w (U.lc c t g) (U.lc c′ t′ g′) =
  (proj₁ (numE c) ==ᴺ proj₁ (numE c′)) ∧ ((proj₂ (numE c) ==ᴺ proj₂ (numE c′)) ∧ eqL d w t t′)
eqL (suc d) w _ _ = false

-- 三值: 在 (yes), 走到底没有 (no), 步数用完 (unk). 只有 no 算数
data Tri : Set where
  yes no unk : Tri

onF : ℕ → ℕ → ℕ → LG → LG → Tri
onF d zero w a b = unk
onF d (suc s) w a b with eqL d 2 a b
... | true = yes
... | false with b
... | U.zero = no
... | U.suc x = onF d s w a x
... | U.lim f = onF d s w a (f w)
... | U.lc c t g = onF d s w a t

-- a 是否在 b 的第一路径上. 极限只看第 w 项: 字面步进下前面的项都在它的第一路径上. 结构比较的极限宽 2, 深度有界
onFirst : ℕ → ℕ → ℕ → LG → LG → Bool
onFirst d zero w a b = false
onFirst d (suc s) w a b = eqL d 2 a b ∨ next b
  where
  next : LG → Bool
  next U.zero = false
  next (U.suc x) = onFirst d s w a x
  next (U.lim f) = onFirst d s w a (f w)
  next (U.lc c t g) = onFirst d s w a t

data Rep : Set where
  noChain : Rep
  guardOk : ℕ × ℕ → ℕ → Rep
  guardNo : ℕ × ℕ → ℕ → Rep
  guardUn : ℕ × ℕ → ℕ → Rep

ixOf : Elt → ℕ
ixOf (el j _) = layer j

-- 走到第一个 oĉ: 看它的下界在不在链点 z 的第一路径上
find : ℕ → ℕ → ℕ → ℕ → ∀ {π} → O U.zero π → List Rep
findL : ℕ → ℕ → ℕ → ℕ → ℕ → ∀ {π} → (ℕ → O U.zero π) → List Rep

_++ᴿ_ : List Rep → List Rep → List Rep
[] ++ᴿ b = b
(x ∷ a) ++ᴿ b = x ∷ (a ++ᴿ b)

find zero d s w x = []
find (suc k) d s w o0 = []
find (suc k) d s w (os x) = find k d s w x
find (suc k) d s w (ol f) = findL w k d s w f
find (suc k) d s w (oŝ c t g) = find k d s w t
find (suc k) d s w (oĉ (el j c) z zg o₀ o) with onFirst d s w (toU (up j c)) z
... | true = guardOk (numE (el j c)) (numR c) ∷ find k d s w o₀
... | false = guardNo (numE (el j c)) (numR c) ∷ find k d s w o₀
find (suc k) d s w (owk _ x) = find (suc k) d s w x
find (suc k) d s w (ocv _ x) = find (suc k) d s w x
find (suc k) d s w (omk () _ _ _ _)
find (suc k) d s w (oΩ () _ _)
find (suc k) d s w (ocl () _ _ _ _)

findL zero k d s w f = []
findL (suc n) k d s w f = findL n k d s w f ++ᴿ find k d s w (f n)
```

```agda
-- 数目: (过的, 没过的), 以及第一个没过的下界
tally : List Rep → ℕ × ℕ
tally [] = 0 , 0
tally (noChain ∷ r) = tally r
tally (guardOk _ _ ∷ r) = suc (proj₁ (tally r)) , proj₂ (tally r)
tally (guardNo _ _ ∷ r) = proj₁ (tally r) , suc (proj₂ (tally r))
tally (guardUn _ _ ∷ r) = tally r

firstNo : List Rep → Maybe (ℕ × ℕ)
firstNo [] = nothing
firstNo (guardNo c _ ∷ r) = just c
firstNo (_ ∷ r) = firstNo r
```

`stepNo`: 第一路径上的极限, 相邻项不在第一路径上的个数 (取前 `w` 项, 比较器同上). 非零说明这个链点的 `Lgl` 在这个比较器下不成立.

```agda
_+ᴺ_ : ℕ → ℕ → ℕ
zero +ᴺ b = b
suc a +ᴺ b = suc (a +ᴺ b)

sumN : ℕ → (ℕ → ℕ) → ℕ
sumN zero p = 0
sumN (suc n) p = sumN n p +ᴺ p n

t2n : Tri → ℕ
t2n no = 1
t2n _ = 0

stepNo : ℕ → ℕ → ℕ → ℕ → LG → ℕ
stepNo zero d s w _ = 0
stepNo (suc k) d s w U.zero = 0
stepNo (suc k) d s w (U.suc x) = stepNo k d s w x
stepNo (suc k) d s w (U.lim f) =
  sumN w (λ n → t2n (onF d s w (f n) (f (suc n))) +ᴺ stepNo k d s w (f n))
stepNo (suc k) d s w (U.lc c t g) = stepNo k d s w t

-- 第一个带链的闭包的链点 z 的 stepNo
chainSteps : ℕ → ℕ → ℕ → ℕ → ℕ → ∀ {π} → O U.zero π → ℕ
chainStepsL : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ∀ {π} → (ℕ → O U.zero π) → ℕ
chainSteps zero k d s w x = 0
chainSteps (suc m) k d s w o0 = 0
chainSteps (suc m) k d s w (os x) = chainSteps m k d s w x
chainSteps (suc m) k d s w (ol f) = chainStepsL w m k d s w f
chainSteps (suc m) k d s w (oŝ c t g) = chainSteps m k d s w t
chainSteps (suc m) k d s w (oĉ c z zg o₀ o) = stepNo k d s w z +ᴺ chainSteps m k d s w o₀
chainSteps (suc m) k d s w (owk _ x) = chainSteps (suc m) k d s w x
chainSteps (suc m) k d s w (ocv _ x) = chainSteps (suc m) k d s w x
chainSteps (suc m) k d s w (omk () _ _ _ _)
chainSteps (suc m) k d s w (oΩ () _ _)
chainSteps (suc m) k d s w (ocl () _ _ _ _)
chainStepsL zero m k d s w f = 0
chainStepsL (suc n) m k d s w f = chainStepsL n m k d s w f +ᴺ chainSteps m k d s w (f n)
```

`legalNo`: 读回的层号上 `Legal` 的有限检查: 极限的相邻项, 闭包的第一支在分支 $c$ 的第一路径上, 分支 $c+i$ 在 $c+i+1$ 的第一路径上 (`Legal` 的 `tg`, `dir`). 分支只走字面的 $c+i$, 下界要 `lglS` 认得.

```agda
lglS : (j : LF) (x : Raw j) → Maybe (Lgl j x)
lglS j G.zero = just tt
lglS j (G.suc x) = lglS j x
lglS j G.top = just tt
lglS (LF.suc k) (G.em _ x) = lglS k x
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

legalNo : ℕ → ℕ → ℕ → ℕ → LG → ℕ
legalBr : ℕ → ℕ → ℕ → ℕ → ℕ → ∀ {j c} → Lgl j c → LG → ((η : Elt) → el j c ⊑̂ η → LG) → ℕ
legalNo zero d s w _ = 0
legalNo (suc k) d s w U.zero = 0
legalNo (suc k) d s w (U.suc x) = legalNo k d s w x
legalNo (suc k) d s w (U.lim f) =
  sumN w (λ n → t2n (onF d s w (f n) (f (suc n))) +ᴺ legalNo k d s w (f n))
legalNo (suc k) d s w (U.lc (el j c) t g) with lglS j c
... | nothing = legalNo k d s w t
... | just l = legalNo k d s w t +ᴺ legalBr w k d s w {j} {c} l t g

legalBr zero k d s w l t g = 0
legalBr (suc i) k d s w {j} {c} l t g =
  legalBr i k d s w {j} {c} l t g +ᴺ
  (t2n (onF d s w t (B i)) +ᴺ (t2n (onF d s w (B i) (B (suc i))) +ᴺ legalNo k d s w (B i)))
  where
  B : ℕ → LG
  B m = g (el j (sucs c m)) (gd (cp-sucs c m , lgl-sucs c m l))
```

`findB`: 同 `find`, 另外走闭包的分支 $c+i$ (第一层下界要 `lglS` 认得), 这样活帧才有非平凡的值, 地板才升高. 这是 [DomFoldNeg](DomFoldNeg.lagda.md) 的 `chain-stuck` 那个局面在真树上的取样: `chain-stuck` 的状态是手造的, 这里是闭项里走到的.

```agda
tag : Tri → ℕ × ℕ → ℕ → Rep
tag yes = guardOk
tag no = guardNo
tag unk = guardUn

findB : ℕ → ℕ → ℕ → ℕ → ∀ {π} → O U.zero π → List Rep
findBL : ℕ → ℕ → ℕ → ℕ → ℕ → ∀ {π} → (ℕ → O U.zero π) → List Rep
findBB : ℕ → ℕ → ℕ → ℕ → ℕ → ∀ {π} {j c} → Lgl j c → ((η : Elt) → el j c ⊑̂ η → O U.zero π) → List Rep

findB zero d s w x = []
findB (suc k) d s w o0 = []
findB (suc k) d s w (os x) = findB k d s w x
findB (suc k) d s w (ol f) = findBL w k d s w f
findB (suc k) d s w (oŝ (el j c) t g) with lglS j c
... | nothing = findB k d s w t
... | just l = findB k d s w t ++ᴿ findBB w k d s w {j = j} {c = c} l g
findB (suc k) d s w (oĉ (el j c) z zg o₀ o) with onF d s w (toU (up j c)) z | lglS j c
... | r | nothing = tag r (numE (el j c)) (numR c) ∷ findB k d s w o₀
... | r | just l = tag r (numE (el j c)) (numR c) ∷ (findB k d s w o₀ ++ᴿ findBB w k d s w {j = j} {c = c} l o)
findB (suc k) d s w (owk _ x) = findB (suc k) d s w x
findB (suc k) d s w (ocv _ x) = findB (suc k) d s w x
findB (suc k) d s w (omk () _ _ _ _)
findB (suc k) d s w (oΩ () _ _)
findB (suc k) d s w (ocl () _ _ _ _)

findBL zero k d s w f = []
findBL (suc n) k d s w f = findBL n k d s w f ++ᴿ findB k d s w (f n)

findBB zero k d s w l o = []
findBB (suc i) k d s w {j = j} {c = c} l o =
  findBB i k d s w {j = j} {c = c} l o ++ᴿ findB k d s w (o (el j (sucs c i)) (gd (cp-sucs c i , lgl-sucs c i l)))
```

**比较器看得见不在第一路径上.** `ctl-no`: $\Omega_1+3$ 不在 $\Omega_1\cdot 2$ 的第一路径上 ([LevelFixNeg](LevelFixNeg.lagda.md) 的 `no-cp-Ω3-Ω2` 的同一个例子), 比较器答否.

```agda
Ω₁L Ω₁+3L Ω₁·2L : LG
Ω₁L = toU Ω₁
Ω₁+3L = U.suc (U.suc (U.suc Ω₁L))
Ω₁·2L = toU Ω₁·2

ctl-no : onF 6 8 3 Ω₁+3L Ω₁·2L ≡ no
ctl-no = refl

ctl-yes : onF 6 8 3 Ω₁L Ω₁·2L ≡ yes
ctl-yes = refl
```

诊断: 第一个答 `no` 的链点的第一路径读成头的序列.

```agda
pathOf : ℕ → ℕ → LG → List ℕ
pathOf zero w x = []
pathOf (suc s) w U.zero = 0 ∷ []
pathOf (suc s) w (U.suc x) = 1 ∷ pathOf s w x
pathOf (suc s) w (U.lim f) = 2 ∷ pathOf s w (f w)
pathOf (suc s) w (U.lc c t g) = (1000 +ᴺ proj₂ (numE c)) ∷ pathOf s w t

firstZ : ℕ → ℕ → ℕ → ℕ → ∀ {π} → O U.zero π → Maybe (List ℕ)
firstZL : ℕ → ℕ → ℕ → ℕ → ℕ → ∀ {π} → (ℕ → O U.zero π) → Maybe (List ℕ)
firstZB : ℕ → ℕ → ℕ → ℕ → ℕ → ∀ {π} {j c} → Lgl j c → ((η : Elt) → el j c ⊑̂ η → O U.zero π) → Maybe (List ℕ)
orM : ∀ {A : Set} → Maybe A → Maybe A → Maybe A
orM (just x) _ = just x
orM nothing y = y
firstZ zero d s w x = nothing
firstZ (suc k) d s w o0 = nothing
firstZ (suc k) d s w (os x) = firstZ k d s w x
firstZ (suc k) d s w (ol f) = firstZL w k d s w f
firstZ (suc k) d s w (oŝ (el j c) t g) with lglS j c
... | nothing = firstZ k d s w t
... | just l = orM (firstZ k d s w t) (firstZB w k d s w {j = j} {c = c} l g)
firstZ (suc k) d s w (oĉ (el j c) z zg o₀ o) with onF d s w (toU (up j c)) z | lglS j c
... | no | _ = just (pathOf 14 w z)
... | _ | nothing = firstZ k d s w o₀
... | _ | just l = orM (firstZ k d s w o₀) (firstZB w k d s w {j = j} {c = c} l o)
firstZ (suc k) d s w (owk _ x) = firstZ (suc k) d s w x
firstZ (suc k) d s w (ocv _ x) = firstZ (suc k) d s w x
firstZ (suc k) d s w (omk () _ _ _ _)
firstZ (suc k) d s w (oΩ () _ _)
firstZ (suc k) d s w (ocl () _ _ _ _)
firstZL zero k d s w f = nothing
firstZL (suc n) k d s w f = orM (firstZL n k d s w f) (firstZ k d s w (f n))
firstZB zero k d s w l o = nothing
firstZB (suc i) k d s w {j = j} {c = c} l o =
  orM (firstZB i k d s w {j = j} {c = c} l o) (firstZ k d s w (o (el j (sucs c i)) (gd (cp-sucs c i , lgl-sucs c i l))))
```
