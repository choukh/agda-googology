# 原有限分量的提升与地板统一有证书

本篇直接使用原 M.F n 与原 flL，不重建同形树。提升保持相对Reg与
Legal，因而每个有限分量的原地板都有Good；中间层不要求raw LgB。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedFiniteRegUp where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldIf using (P; G)
open import OCF.Lean.LHRecFl using (flL; Lg-flL; up-⊲)
import OCF.Lean.BoundedContextClosed as C
open import OCF.Align.BoundedFiniteRegIf
open import OCF.Align.BoundedFiniteRegClosure using (seed-map)

reg-up : ∀ n a → Reg n a → Reg (suc n) (up a)
reg-up zero hz r = tt
reg-up zero (hs a) r = reg-up zero a tt
reg-up zero (hl f) r = λ j → reg-up zero (f j) tt
reg-up zero (hΩ κ g) r = tt , (λ c rc → reg-up zero (g c) tt)
reg-up (suc n) hz r = tt
reg-up (suc n) (hs a) r = reg-up (suc n) a r
reg-up (suc n) (hl f) r = λ j → reg-up (suc n) (f j) (r j)
reg-up (suc n) (hΩ κ g) (s , r) =
  seed-map (suc n) (λ W → W) (λ W → W , one (suc n)) κ g (λ c → up (g c))
    (λ W rw c d rc rd p → up-⊲ p) s ,
  (λ c rc → reg-up (suc n) (g c) (r c rc))

steps : ∀ n f → Legal n (hl f) → ∀ {W} → RegWorld n W →
  ∀ j → f j ⊲[ W ] f (suc j)
steps zero f l rw j = proj₁ l j
steps (suc n) f l rw j = proj₁ l rw j

children : ∀ n f → Legal n (hl f) → ∀ j → Legal n (f j)
children zero f l = proj₂ l
children (suc n) f l = proj₂ l

node-mono : ∀ n κ g → Legal n (hΩ κ g) →
  ∀ {W c d} → LegalWorld n W → Bd (F n) κ c W → Bd (F n) κ d W →
    Pr (F n) κ W c d → g c ⊲[ W ] g d
node-mono zero κ g l = proj₁ l
node-mono (suc n) κ g l = proj₁ l

node-branch : ∀ n κ g → Legal n (hΩ κ g) →
  ∀ c → LegalCoord n κ c → Legal n (g c)
node-branch zero κ g l c (W , lw , b) = proj₂ l lw b
node-branch (suc n) κ g l c lc = proj₂ l c lc

tail-legal : ∀ n a → Legal n (hs a) → Legal n a
tail-legal zero a l = l
tail-legal (suc n) a l = l

legal-up : ∀ n a → Legal n a → Legal (suc n) (up a)
legal-up n hz l = tt
legal-up n (hs a) l = legal-up n a (tail-legal n a l)
legal-up n (hl f) l =
  (λ rw j → up-⊲ (steps n f l (proj₁ rw) j)) ,
  (λ j → legal-up n (f j) (children n f l j))
legal-up n (hΩ κ g) l =
  (λ lw b b′ p → up-⊲ (node-mono n κ g l (proj₁ lw) b b′ p)) ,
  (λ c lc → legal-up n (g c) (node-branch n κ g l c lc))

good-up : ∀ n a → Good n a → Good (suc n) (up a)
good-up n a (r , l) = reg-up n a r , legal-up n a l

floor : ∀ n → HB (F n)
floor n = flL (G (up (C.num n)))

floor-good : ∀ n → Good n (floor n)
floor-good zero = tt , Lg-flL P
floor-good (suc n) =
  ((λ rw bc bd p → up-⊲ p) , (λ c rc → reg-up n c rc)) ,
  ((λ lw bc bd p → up-⊲ p) , (λ c lc → legal-up n c (proj₂ lc)))
```

floor-good对所有n一次归纳，非有限测试；新增kind的分支只消费低阶
证书，不把任意raw坐标当作有证书。尚不说明旧多层direct fold等于
逐层down，也没有给原生P到可数层的合法性或终点强度。
