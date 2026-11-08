# 第二分量首个外层输出：实际内层回灌

本文件只验收实际第二分量，不改折叠定义。先把低界写入连接到实际 Φ 展开。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenInnerFirst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (Lv; top; _≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l; mul)
open import OCF.Lean.Fold1Base using (Wi; updAt; mul-≤; ≤-refl)
import OCF.Lean.Fold1Fold as O
import OCF.Lean.SupCollapseFrozen as N
import OCF.Lean.SupCollapseClosed as C
import OCF.Align.FrozenValueSecond as S
open import OCF.Align.FrozenValueFirst using (Pure; add-mono)
import OCF.Align.FrozenValueFirst as A

child : Cd → HB (Lv C.ω)
child c = S.prefix ⊞ ι 2 (up (up c))

IX : Wd (Lv C.ω) → Cd → Cd
IX w c = O.Φ C.ω C.legal-ω hz (hlim 2 (hsuc (hsuc hself))) w (child c)
IT : Wd (Lv C.ω) → Cd → Cd
IT w c = O.Φ C.ω C.legal-ω hz (z⊲ᴮ C.ω) w (child c)
JX : Wd (Lv C.ω) → Cd → Cd
JX w c = N.Φ C.ω C.legal-ω hz (hlim 2 (hsuc (hsuc hself))) w (child c)
JT : Wd (Lv C.ω) → Cd → Cd
JT w c = N.Φ C.ω C.legal-ω hz (z⊲ᴮ C.ω) w (child c)

module InnerOld = O.Col _⊞_ _⊞_ S.W hz S.writeLow IX IT
module InnerFrozen = N.Col _⊞_ _⊞_ S.W hz (λ w e → w) JX JT

old-first-output : S.Old.oo 0 ≡ hl InnerOld.oO
old-first-output = refl
frozen-first-output : S.Frozen.oo 0 ≡ hl InnerFrozen.oO
frozen-first-output = refl

-- 内层回灌确实写到其下一次旧 Ω 所读取的低界。
inner-low : ∀ n → proj₂ (proj₁ (InnerOld.cw (suc n) 2)) ≡ InnerOld.ce (suc n)
inner-low n = refl
inner-first : ∀ n → InnerOld.cw n 1 ≡ S.W 1
inner-first zero = refl
inner-first (suc n) = refl
```

第二分量的低界写入不改变第一分量。以下比较第一分量前缀，随后允许
任意可数尾部；不是把实际分支改成常量。

```agda
pureChild : Cd → HB (Lv C.ω)
pureChild c = hz ⊞ ι 1 (up c)
PX : Wd (Lv C.ω) → Cd → Cd
PX w c = O.Φ C.ω C.legal-ω hz (hlim 1 (hsuc hself)) w (pureChild c)
QX : Wd (Lv C.ω) → Cd → Cd
QX w c = N.Φ C.ω C.legal-ω hz (hlim 1 (hsuc hself)) w (pureChild c)
PY : Wd (Lv C.ω) → Cd → Cd
PY w c = O.Φ C.ω C.legal-ω hz (hlim 2 (hsuc (hsuc hself))) w (pureChild c)
QY : Wd (Lv C.ω) → Cd → Cd
QY w c = N.Φ C.ω C.legal-ω hz (hlim 2 (hsuc (hsuc hself))) w (pureChild c)
PZ : Wd (Lv C.ω) → Cd → Cd
PZ w c = O.Φ C.ω C.legal-ω hz (z⊲ᴮ C.ω) w (pureChild c)
QZ : Wd (Lv C.ω) → Cd → Cd
QZ w c = N.Φ C.ω C.legal-ω hz (z⊲ᴮ C.ω) w (pureChild c)

purePX : Pure PX
purePX = record { at0 = λ w → refl ; ats = λ w c → refl ; atl = λ w f → refl }
pureQX : Pure QX
pureQX = record { at0 = λ w → refl ; ats = λ w c → refl ; atl = λ w f → refl }
purePY : Pure PY
purePY = record { at0 = λ w → refl ; ats = λ w c → refl ; atl = λ w f → refl }
pureQY : Pure QY
pureQY = record { at0 = λ w → refl ; ats = λ w c → refl ; atl = λ w f → refl }
purePZ : Pure PZ
purePZ = record { at0 = λ w → refl ; ats = λ w c → refl ; atl = λ w f → refl }
pureQZ : Pure QZ
pureQZ = record { at0 = λ w → refl ; ats = λ w c → refl ; atl = λ w f → refl }

writeOne : Wd (Lv C.ω) → Cd → Wd (Lv C.ω)
writeOne w e = updAt w 1 (proj₁ (w 1) , e)

module PrefixCompare (w v : Wd (Lv C.ω))
  (PT QT : Wd (Lv C.ω) → Cd → Cd) (p : Pure PT) (q : Pure QT) where
  module L = O.Col _⊞_ _⊞_ w hz writeOne PX PT
  module R = N.Col _⊞_ _⊞_ v hz (λ w e → w) QX QT
  module CX = A.Compare purePX pureQX
  module CT = A.Compare p q
  coordinates : ∀ n → L.ce n ≤ᵛ R.ce n
  coordinates zero = z≤
  coordinates (suc n) = add-mono (coordinates n) (CX.mono (L.cw n) (R.cw n) (coordinates n))
  outputs : ∀ n → L.oo n ≤ᵛ R.oo n
  outputs n = CT.mono (L.cw n) (R.cw n) (coordinates n)
  sums : ∀ n → L.oO n ≤ᵛ R.oO n
  sums zero = outputs zero
  sums (suc n) = add-mono (sums n) (outputs (suc n))
  result : hl L.oO ≤ᵛ hl R.oO
  result = l≤ (λ n → ≤l n (sums n))

baseX : ∀ w v → proj₂ (w 1) ≡ hz → proj₂ (v 1) ≡ hz → IX w hz ≤ᵛ JX v hz
baseX w v ew ev rewrite ew | ev = PrefixCompare.result w v PY QY purePY pureQY
baseT : ∀ w v → proj₂ (w 1) ≡ hz → proj₂ (v 1) ≡ hz → IT w hz ≤ᵛ JT v hz
baseT w v ew ev rewrite ew | ev = PrefixCompare.result w v PZ QZ purePZ pureQZ
```

```agda
module TailCompare
  (F G : Wd (Lv C.ω) → Cd → Cd)
  (fs : ∀ w c → F w (hs c) ≡ hl (mul (F w c)))
  (fl : ∀ w f → F w (hl f) ≡ hl (λ n → F w (f n)))
  (gs : ∀ w c → G w (hs c) ≡ hl (mul (G w c)))
  (gl : ∀ w f → G w (hl f) ≡ hl (λ n → G w (f n))) where

  positive : ∀ w v → F w hz ≤ᵛ G v hz → ∀ c → F w hz ≤ᵛ G v c
  positive w v b hz = b
  positive w v b (hs c) rewrite gs v c = ≤l 0 (positive w v b c)
  positive w v b (hl f) rewrite gl v f = ≤l 0 (positive w v b (f 0))

  mono : ∀ w v → F w hz ≤ᵛ G v hz → ∀ {a b} → a ≤ᵛ b → F w a ≤ᵛ G v b
  mono w v base {b = b} z≤ = positive w v base b
  mono w v base {a = hs a} {hs b} (s≤s p) rewrite fs w a | gs v b =
    l≤ (λ n → ≤l n (mul-≤ (mono w v base p) n))
  mono w v base {b = hs b} (≤s p) rewrite gs v b = ≤l 0 (mono w v base p)
  mono w v base {a = hl f} (l≤ h) rewrite fl w f = l≤ (λ n → mono w v base (h n))
  mono w v base {b = hl f} (≤l n p) rewrite gl v f = ≤l n (mono w v base p)

module TX = TailCompare IX JX (λ w c → refl) (λ w f → refl) (λ w c → refl) (λ w f → refl)
module TT = TailCompare IT JT (λ w c → refl) (λ w f → refl) (λ w c → refl) (λ w f → refl)

left-support : ∀ n → proj₂ (InnerOld.cw n 1) ≡ hz
left-support zero = refl
left-support (suc n) = refl
right-support : ∀ n → proj₂ (InnerFrozen.cw n 1) ≡ hz
right-support zero = refl
right-support (suc n) = refl

inner-coordinates : ∀ n → InnerOld.ce n ≤ᵛ InnerFrozen.ce n
inner-coordinates zero = z≤
inner-coordinates (suc n) = add-mono (inner-coordinates n)
  (TX.mono (InnerOld.cw n) (InnerFrozen.cw n)
    (baseX _ _ (left-support n) (right-support n)) (inner-coordinates n))

inner-outputs : ∀ n → InnerOld.oo n ≤ᵛ InnerFrozen.oo n
inner-outputs n = TT.mono (InnerOld.cw n) (InnerFrozen.cw n)
  (baseT _ _ (left-support n) (right-support n)) (inner-coordinates n)

inner-sums : ∀ n → InnerOld.oO n ≤ᵛ InnerFrozen.oO n
inner-sums zero = inner-outputs zero
inner-sums (suc n) = add-mono (inner-sums n) (inner-outputs (suc n))

first-outer-output : S.Old.oo 0 ≤ᵛ S.Frozen.oo 0
first-outer-output = l≤ (λ n → ≤l n (inner-sums n))

first-outer-output≤second : S.Old.oo 0 ≤ᵛ N.Φ C.ω C.legal-ω hz
  (z⊲ᴮ C.ω) S.W (OCF.Lean.Fold1If.ΣT S⊥ hz C.num 2)
first-outer-output≤second = ≤l 0 first-outer-output

first-outer-output≤Tω : S.Old.oo 0 ≤ᵛ C.Tω
first-outer-output≤Tω = ≤l 2 first-outer-output≤second
```

结论覆盖第二分量首个外层输出中的全部内层回灌项，带实际前缀和任意可数尾部。
支持关系是第一分量低界仍为零，已在两条实际内层轨道逐项实例化。
尚未比较后续外层输出：其坐标不再只是最初的 `top1`，累加会产生第二分量旧 Ω
的前缀，此时本文件使用的第一分量前缀比较不能直接复用。
没有据此宣称完整第二分量同值，也没有给它未验收的 ψ 读法。
