# 目标来源：前驱、共尾层与 Ω 基本列的语法保持

第 4 层的纯语法辅助律，不要求输入标准形或可达性。
前驱和 Ω 基本列不引入新的正参数 ψ 目标；γ 链只允许新引入给定的 ν。
这些结论不写树侧 ψ，不修改旧定义，也不把任意语法子项当成实际比较。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiTargetTransport where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([]; _∷_)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.EboLeanDef
  using (T; ψ; Cof; c0; c1; cω; cΩ; Cmp; lt; eq; gt;
         pred; cof; cofA; cofψ0; cofψ₊; cmpᵀ; sucT;
         fsT; fsT0; fsT₊; fsTc; γT)
open import OCF.Align.YiTargetBase

pred-tags : ∀ {P} a → AllTags P a → AllTags P (pred a)
pred-tags [] h = tt
pred-tags (ψ u b ∷ y ∷ ys) (h , tu , tb , ts) =
  h , tu , tb , pred-tags (y ∷ ys) ts
pred-tags (ψ [] [] ∷ []) h = tt
pred-tags a@(ψ [] (_ ∷ _) ∷ []) h = h
pred-tags a@(ψ (_ ∷ _) b ∷ []) h = h

cof-tags : ∀ {P} a {ν} → AllTags P a → cof a ≡ cΩ ν → AllTags P ν
cof0-tags : ∀ {P} u k {ν} → AllTags P u → cof u ≡ k →
  cofψ0 u k ≡ cΩ ν → AllTags P ν
cofA-tags : ∀ {P} u b k {ν} → AllTags P b → cof b ≡ k →
  cofA u k ≡ cΩ ν → AllTags P ν
cofψ-tags : ∀ {P} u μ m {ν} → AllTags P μ →
  cofψ₊ u μ m ≡ cΩ ν → AllTags P ν

cof-tags [] h ()
cof-tags (ψ u b ∷ y ∷ ys) (h , tu , tb , ts) e = cof-tags (y ∷ ys) ts e
cof-tags (ψ u b@(_ ∷ _) ∷ []) (h , tu , tb , ts) e =
  cofA-tags u b (cof b) tb refl e
cof-tags (ψ u@(_ ∷ _) [] ∷ []) (h , tu , tb , ts) e =
  cof0-tags u (cof u) tu refl e
cof-tags (ψ [] [] ∷ []) h ()

cof0-tags u c0 tu eu ()
cof0-tags u c1 tu eu refl = pred-tags u tu
cof0-tags u cω tu eu ()
cof0-tags u (cΩ μ) tu eu refl = cof-tags u tu eu

cofA-tags u b c0 tb eb ()
cofA-tags u b c1 tb eb ()
cofA-tags u b cω tb eb ()
cofA-tags u b (cΩ μ) tb eb e =
  cofψ-tags u μ (cmpᵀ (sucT μ) u) (cof-tags b tb eb) e

cofψ-tags u μ lt tμ refl = tμ
cofψ-tags u μ eq tμ refl = tμ
cofψ-tags u μ gt tμ ()

fsT-tags : ∀ {P} a η → AllTags P a → AllTags P η → AllTags P (fsT a η)
fsT0-tags : ∀ {P} u k η → AllTags P u → AllTags P η → AllTags P (fsT0 u k η)
fsT₊-tags : ∀ {P} u b k η → P u → AllTags P u → AllTags P b → AllTags P η →
  AllTags P (fsT₊ u b k η)
fsTc-tags : ∀ {P} u b ν m η → P u → AllTags P u → AllTags P b → AllTags P η →
  AllTags P (fsTc u b ν m η)

fsT-tags [] η h tη = tt
fsT-tags (ψ u b ∷ y ∷ ys) η (h , tu , tb , ts) tη =
  h , tu , tb , fsT-tags (y ∷ ys) η ts tη
fsT-tags (ψ u b@(_ ∷ _) ∷ []) η (h , tu , tb , ts) tη =
  fsT₊-tags u b (cof b) η h tu tb tη
fsT-tags (ψ u@(_ ∷ _) [] ∷ []) η (h , tu , tb , ts) tη =
  fsT0-tags u (cof u) η tu tη
fsT-tags (ψ [] [] ∷ []) η h tη = tt

fsT0-tags u c0 η tu tη = omega tu
fsT0-tags u c1 η tu tη = tη
fsT0-tags u cω η tu tη = omega tu
fsT0-tags u (cΩ ν) η tu tη = omega (fsT-tags u η tu tη)

fsT₊-tags u b c0 η pu tu tb tη = singleton (head-from pu b) tu tb
fsT₊-tags u b c1 η pu tu tb tη = singleton (head-from pu b) tu tb
fsT₊-tags u b cω η pu tu tb tη = singleton (head-from pu b) tu tb
fsT₊-tags u b (cΩ ν) η pu tu tb tη =
  fsTc-tags u b ν (cmpᵀ (sucT ν) u) η pu tu tb tη

fsTc-tags u b ν lt η pu tu tb tη =
  singleton (head-from pu (fsT b η)) tu (fsT-tags b η tb tη)
fsTc-tags u b ν eq η pu tu tb tη =
  singleton (head-from pu (fsT b η)) tu (fsT-tags b η tb tη)
fsTc-tags u b ν gt η pu tu tb tη = singleton (head-from pu b) tu tb

gamma-tags : ∀ {P} β ν n → P ν → AllTags P β → AllTags P ν → AllTags P (γT β ν n)
gamma-tags β ν zero pν tβ tν = omega tν
gamma-tags β ν (suc n) pν tβ tν =
  singleton (head-from pν (fsT β (γT β ν n))) tν
    (fsT-tags β (γT β ν n) tβ (gamma-tags β ν n pν tβ tν))
```

这里的 P 可取严格先前历史环境的成员关系。`gamma-tags` 的 Pν 是显式
允许加入的新头，而 ν 内部已有的正 ψ 仍由 `cof-tags` 从原项中运输。
本篇没有据此判定固定层号的目标集合有限或稠密；实际历史环境覆盖另证。
