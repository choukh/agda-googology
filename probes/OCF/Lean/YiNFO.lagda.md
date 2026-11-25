# 记号参照: 项序推出值序

> 验收文件 (读记号). 编译定理, 无前提: 对 `StandardOmega` 的标准形 `NF₁` (ψ-下标可数或为 Ω+可数) 带任意 `HC` 推导, 项序 s < t 推出 `L.suc (Rt h) ≼ Rt h′` (`mono<`), s ≤ t 推出 `Rt h ≼ Rt h′` (`mono≤`); 推论: 上界沿项序上移 (`up≼`, `up≺`), 严格时反向不成立 (`mono<-strict`).
> 做法: 对 t 的 `HC` 推导归纳; 后继处 s ≤ t − 1, 极限处用 `cofin₁` (s 低于某个基本列项). 不碰树、折叠. 不覆盖 `NF₁` 之外的项 (如塔第 3 行 ψ₀(Ω_{Ω_Ω}), 下标 Ω_Ω 不是 Ω+可数). 实例在 [YiNFOCase](YiNFOCase.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNFO where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

import OCF.Align.EBO as E
open import OCF.Align.EboLeanDef using (T; ψ; 𝟏; HC; h0; h1; hω; cof; c0; c1; cω; cΩ; lt; eq; gt;
  cmpᵀ; sucT; pred; fsn; fsn0; fsn₊; fsnc; fsT; _<ᵀ_)
open import OCF.Align.Correspond using (cof-ne)
open import OCF.Align.Bachmann using (<sucT)
open import OCF.Align.StandardOmega using (NF₁; NF₁-pred; NF₁-fsn; cofin₁)
open import OCF.Lean.YiRefTw2 using (Rt; tree-≼)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; s≼s; ≼l; ≼-refl; ≼-trans; ≼-suc)
```

## 两个 `fsn` 的值相同

`HC` 沿 `EboLeanDef` 的裸值 `fsn`, `cofin₁` 沿 EBO 带证书版本去掉证书的 `E.fsn`. 证明逐字取自 `EboLeanCmp` §1 (那个模块的导入闭包经 `WfFsn` 到 `archive/`, 不能导入).

```agda
fsn≡  : ∀ t n → fsn t n ≡ E.fsn t n
fsn≡ˣ : ∀ x xs n → fsn (x ∷ xs) n ≡ E.trm (E.fsn↓ x xs n)
fsn≡0 : ∀ w ws c (e : cof (w ∷ ws) ≡ c) n → fsn0 (w ∷ ws) c n ≡ E.trm (E.fsn↓0 w ws c e n)
fsn≡₊ : ∀ u y ys c (e : cof (y ∷ ys) ≡ c) n → fsn₊ u (y ∷ ys) c n ≡ E.trm (E.fsn↓₊ u y ys c e n)
fsn≡c : ∀ u y ys ν (e : cof (y ∷ ys) ≡ cΩ ν) m n → fsnc u (y ∷ ys) ν m n ≡ E.trm (E.fsn↓c u y ys ν e m n)

fsn≡ [] n = refl
fsn≡ (x ∷ xs) n = fsn≡ˣ x xs n

fsn≡ˣ x (y ∷ ys) n = cong (x ∷_) (fsn≡ˣ y ys n)
fsn≡ˣ (ψ u (y ∷ ys)) [] n = fsn≡₊ u y ys (cof (y ∷ ys)) refl n
fsn≡ˣ (ψ (w ∷ ws) []) [] n = fsn≡0 w ws (cof (w ∷ ws)) refl n
fsn≡ˣ 𝟏 [] n = refl

fsn≡0 w ws c0 e n = refl
fsn≡0 w ws c1 e n = refl
fsn≡0 w ws cω e n = cong (λ z → ψ z [] ∷ []) (fsn≡ˣ w ws n)
fsn≡0 w ws (cΩ ν) e n = cong (λ z → ψ z [] ∷ []) (sym (E.fsT↓-trm (w ∷ ws) e (E.natT<Ωs n ν)))

fsn≡₊ u y ys c0 e n = refl
fsn≡₊ u y ys c1 e n = sym (E.rep-trm u (E.pred-< (y ∷ ys) e) n)
fsn≡₊ u y ys cω e n = cong (λ z → ψ u z ∷ []) (fsn≡ˣ y ys n)
fsn≡₊ u y ys (cΩ ν) e n = fsn≡c u y ys ν e (cmpᵀ (sucT ν) u) n

fsn≡c u y ys ν e gt n =
  cong (λ z → ψ u z ∷ [])
       (sym (trans (E.fsT↓-trm (y ∷ ys) e (E.dec (E.γ↓ (y ∷ ys) ν e n))) (cong (fsT (y ∷ ys)) (E.γ↓-trm (y ∷ ys) ν e n))))
fsn≡c u y ys ν e lt n = cong (λ z → ψ u z ∷ []) (sym (E.fsT↓-trm (y ∷ ys) e (E.natT<Ωs n ν)))
fsn≡c u y ys ν e eq n = cong (λ z → ψ u z ∷ []) (sym (E.fsT↓-trm (y ∷ ys) e (E.natT<Ωs n ν)))
```

## 句法的两步

零之下没有项; 后继 t 之下的项不超过 t − 1 (对一切项, 不要标准形).

```agda
c0-min : ∀ {s t} → cof t ≡ c0 → s <ᵀ t → ⊥
c0-min {t = []}     e ()
c0-min {t = x ∷ xs} e _ = cof-ne x xs e

pred-≤ : ∀ {s t} → cof t ≡ c1 → s <ᵀ t → (s <ᵀ pred t) ⊎ (s ≡ pred t)
pred-≤ {s} {t} e p = <sucT (pred t) (subst (s <ᵀ_) (sym (E.pred-suc t e)) p)
```

## 主定理

```agda
↓suc : ∀ {a b : L.Ordᶜ L.zero} → L.suc a ≼ b → a ≼ b
↓suc {a} p = ≼-trans (≼-suc (≼-refl a)) p

mono< : ∀ {s t} → NF₁ s → NF₁ t → (h : HC s) (h′ : HC t) → s <ᵀ t → L.suc (Rt h) ≼ Rt h′
mono< ns nt h (h0 e) p = ⊥-elim (c0-min e p)
mono< {s} {t} ns nt h (h1 e hp) p with pred-≤ e p
... | inj₁ q = s≼s (↓suc (mono< ns (NF₁-pred nt e) h hp q))
... | inj₂ r = s≼s (tree-≼ r h hp)
mono< {s} {t} ns nt h (hω e hs) p with cofin₁ nt e ns p
... | n , q = ≼l n (mono< ns (subst NF₁ (sym (fsn≡ t n)) (NF₁-fsn nt e n)) h (hs n)
                       (subst (s <ᵀ_) (sym (fsn≡ t n)) q))

mono≤ : ∀ {s t} → NF₁ s → NF₁ t → (h : HC s) (h′ : HC t) → (s <ᵀ t) ⊎ (s ≡ t) → Rt h ≼ Rt h′
mono≤ ns nt h h′ (inj₁ p) = ↓suc (mono< ns nt h h′ p)
mono≤ ns nt h h′ (inj₂ r) = tree-≼ r h h′
```

## 推论

上界沿项序上移; 严格时反向的 `≼` 不成立 (`≼` 上 `suc a ≼ a` 不可能).

```agda
up≼ : ∀ {s t} {X : L.Ordᶜ L.zero} → NF₁ s → NF₁ t → (h : HC s) (h′ : HC t) →
      (s <ᵀ t) ⊎ (s ≡ t) → X ≼ Rt h → X ≼ Rt h′
up≼ ns nt h h′ p q = ≼-trans q (mono≤ ns nt h h′ p)

up≺ : ∀ {s t} {X : L.Ordᶜ L.zero} → NF₁ s → NF₁ t → (h : HC s) (h′ : HC t) →
      s <ᵀ t → X ≼ Rt h → L.suc X ≼ Rt h′
up≺ ns nt h h′ p q = ≼-trans (s≼s q) (mono< ns nt h h′ p)

s≼-irrefl : (a : L.Ordᶜ L.zero) → L.suc a ≼ a → ⊥
s≼-irrefl L.zero ()
s≼-irrefl (L.suc a) (s≼s p) = s≼-irrefl a p
s≼-irrefl (L.lim f) (≼l n p) =
  s≼-irrefl (f n) (≼-trans {ℓ₂ = L.zero} (s≼s {ℓ₁ = L.zero} {ℓ₂ = L.zero} (≼l n (≼-refl (f n)))) p)
s≼-irrefl (L.limᵢ () f)
s≼-irrefl (L.up () x)

mono<-strict : ∀ {s t} → NF₁ s → NF₁ t → (h : HC s) (h′ : HC t) → s <ᵀ t → ¬ (Rt h′ ≼ Rt h)
mono<-strict ns nt h h′ p q = s≼-irrefl (Rt h) (≼-trans (mono< ns nt h h′ p) q)
```
