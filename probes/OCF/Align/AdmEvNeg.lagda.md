# 种类带证据, 比较取 `cmpB₀` (五): 两条否定, 说明正面结果的范围

> 不含记号. 入口 [AdmEv](AdmEv.lagda.md).
>
> - **`no-indep₀`** (否定): 换成 `cmpB₀` 之后, 同一坐标两个证据下的重放仍然一般不可比 (`EvWNeg.no-indep` 在新比较下的重演, 同一个反例, 界由 `refl` 算出). 所以 `cmpB₀` 去掉的是对角上的自环 (`new-gen₀`), **没有去掉拷贝**; 种类仍须带证据. **只否定**: 以 `AdmEvBase.Rp₀.rp` 为界, 同一坐标的两个证据的界对一切合法外层世界相等或可比.
> - **`not-image`** (否定): 外层界接上头部非零的 δ 之后, 新事件世界里有不是任何旧事件世界的像 (`wm`) 的世界 (在新界自己那个坐标上的事件). 这是 `EvW` §3 那句 "新世界不都是旧世界的像" 的定理形式. 它**不**阻止改贴保合法: `AdmEvGrow.sim` 说新世界在旧种类上的读数总等于某个旧世界 (`rest H`) 的读数, `Lg-rl` 由此得到. **只否定**: "一切新世界都是旧世界的像".
>
> 前提实例: `EvWNeg` 的 `la₀`, `lbΩ`, `p₁`, `p₂`, `pz`, `lΩz` (闭项); `not-image` 对一切合法 $a, b$ 与一切头部非零的合法 δ. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AdmEvNeg where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; map)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)
open import OCF.Align.CumReadCF using (A; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvWNeg using (ω₀; bΩ; lbΩ; a₀; la₀; Ωz; lΩz; p₁; p₂; pz; R₁; R₂; R-ne; R₁⋬R₂; R₂⋬R₁; Rel)
open import OCF.Align.AdmEvBase
open import OCF.Align.AdmEvGrow using (module Grow₀)
open import OCF.Align.AdmEvFeed using (NZ; ⊞-strict; not-below)
```

## §1 拷贝仍在

```agda
H₁ : Rp₀.Hist a₀ bΩ la₀ lbΩ
H₁ = record { ec = hz ; ep = pz ; eδ = Ωz ; elδ = lΩz } ∷ []

rp₁ : Rp₀.rp a₀ bΩ la₀ lbΩ H₁ ω₀ p₁ ≡ R₁
rp₁ = refl

rp₂ : Rp₀.rp a₀ bΩ la₀ lbΩ H₁ ω₀ p₂ ≡ R₂
rp₂ = refl

Indep₀ : Set
Indep₀ = ∀ {a b} (la : Lg a) (lb : LgB b) H c (p p′ : c ⊲[ a ] b) →
         Rel c (Rp₀.rp a b la lb H c p) (Rp₀.rp a b la lb H c p′)

no-indep₀ : ¬ Indep₀
no-indep₀ I with I la₀ lbΩ H₁ ω₀ p₁ p₂
... | inj₁ e = R-ne e
... | inj₂ (inj₁ (v , q)) = R₁⋬R₂ q
... | inj₂ (inj₂ (v , q)) = R₂⋬R₁ q
```

## §2 新世界不都是旧世界的像

```agda
module NotImage (a : A) (la : Lg a) (b : HB S₀) (lb : LgB b) (δ : HB S₀) (lδ : LgB δ) (nz : NZ δ) where
  open Grow₀ a la b lb δ lδ

  first-c : N.Hist → HB S₀
  first-c [] = hz
  first-c (e ∷ _) = N.ec e

  Htop : N.Hist
  Htop = record { ec = b ⊞ δ ; ep = hself ; eδ = hz ; elδ = tt } ∷ []

  not-image : ¬ (Σ O.Hist (λ H₀ → wm H₀ ≡ Htop))
  not-image ([] , ())
  not-image (e ∷ H , eq) =
    not-below (⊞-strict b δ nz a) (subst (λ z → z ⊲[ a ] b) (cong first-c eq) (O.ep e))
```
