# 处处严格候选：LF 的 Ω 分支也要求真第一路径

按作者选定形状在平行 LF 上另定义 Legalˢˢ，不改旧 Legalˢ 或 Raw 的 Lgl。
ℕ 极限仍要求 Properˢ；Ω 分支在 Dn 坐标步下要求 Properˢ。
同一坐标的守卫证据无关性、第一支弱 CP 与 Gd 的下界等号均保留。
新增字段由 no-rule-preservation 的常 Ω 分支反例逼出，规则模板仍来自 JiaExactFold。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLglAllBase where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_×_; _,_; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import OCF.Align.YiLglCore as F
open F using (module G)
open import OCF.Align.YiLglVal using (CP)
import OCF.Align.YiLglVal as V
open import OCF.Align.YiLglStrict using (Properˢ; Legalˢ; weak)
import OCF.Align.YiLglStrict as S
import OCF.Align.YiLglFoldPause as P

Legalˢˢ : F.LF → Set
Legalˢˢ F.zero = ⊤
Legalˢˢ (F.suc x) = Legalˢˢ x
Legalˢˢ (F.lim f) = (∀ n → Properˢ (f n) (f (suc n))) × (∀ n → Legalˢˢ (f n))
Legalˢˢ (F.lc k c t g) =
  Legalˢˢ k × (∀ η e → CP t (g η e)) ×
  (∀ η e η′ e′ → F.Dn k η η′ → Properˢ (g η e) (g η′ e′)) ×
  (∀ η e e′ → g η e ≡ g η e′) × Legalˢˢ t × (∀ η e → Legalˢˢ (g η e))

weaken-branch : ∀ k c (g : (η : F.Raw k) → F.Gd k c η → F.LF) →
  (∀ η e η′ e′ → F.Dn k η η′ → Properˢ (g η e) (g η′ e′)) →
  (∀ η e e′ → g η e ≡ g η e′) →
  ∀ η e η′ e′ → F.Gd k η η′ → CP (g η e) (g η′ e′)
weaken-branch k c g strict same η e .η e′ (inj₁ refl , lawful) =
  subst (CP (g η e)) (same η e e′) V.self
weaken-branch k c g strict same η e η′ e′ (inj₂ d , lawful) =
  weak (strict η e η′ e′ d)

forget : ∀ x → Legalˢˢ x → Legalˢ x
forget F.zero lawful = tt
forget (F.suc x) lawful = forget x lawful
forget (F.lim f) (step , lawful) = step , (λ n → forget (f n) (lawful n))
forget (F.lc k c t g) (lk , first , strict , same , lt , lg) =
  forget k lk , first , weaken-branch k c g strict same , same ,
  forget t lt , (λ η e → forget (g η e) (lg η e))

no-proper-one : Properˢ (F.suc F.zero) (F.suc F.zero) → ⊥
no-proper-one (S.under-suc ())

no-old-source : Legalˢˢ P.source → ⊥
no-old-source (lk , first , strict , same , lt , lg) =
  no-proper-one (strict P.raw1 (proj₂ P.coordinate1)
    P.raw2 (proj₂ P.coordinate2) P.raw-strict)

nat-legal : ∀ n → Legalˢˢ (V.natF n)
nat-legal 0 = tt
nat-legal (suc n) = nat-legal n

read-zero : ∀ η → F.Lgl F.zero η → Legalˢˢ (V.up F.zero η)
read-zero G.zero lawful = tt
read-zero (G.suc η) lawful = read-zero η lawful
read-zero (G.lim f) (step , lawful) =
  (λ n → S.dn-proper F.zero (f (suc n)) (step n)) ,
  (λ n → read-zero (f n) (lawful n))
read-zero (G.lc () c t g) lawful
read-zero (G.em () T) lawful
read-zero G.top lawful = tt

omega-one-legal : Legalˢˢ (V.Ω̂ (F.suc F.zero))
omega-one-legal = tt , (λ η e → V.cO-CP F.zero (Data.Product.Base.proj₁ e)) ,
  (λ η e η′ e′ d → S.dn-proper F.zero η′ d) , (λ η e e′ → refl) ,
  tt , (λ η e → read-zero η (proj₂ e))
```

weaken-branch 的相等行只用守卫无关性，不识别两份证据，也不用 UIP。
forget 给 Legalˢˢ→Legalˢ；no-old-source 排上一轮的常1分支源。
nat-legal 与 omega-one-legal 给非空实例，尚未声称全层 Ω 闭包或全塔成立。
