# 共尾层的字面来源：原 Ω 字段的前驱

第 4 层的语法来源证明。`Field` 的参数 w、a 表示原项 a 中字面出现 Ω_w，
沿下标、参数或和尾部定位；不按值闭包，也不将 ν 自动当作某个子项。
共尾度为 Ω_{ν+1} 时，ν 是这样一个原字段 w 的前驱。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiTargetOrigin where

open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import OCF.Align.EboLeanDef
  using (T; ψ; pred; cof; Cof; c0; c1; cω; cΩ;
         cofψ0; cofA; cofψ₊; cmpᵀ; sucT; Cmp; lt; eq; gt)
open import OCF.Align.YiTargetScan using (scan; scan₀; scan₊)

data Field (w : T) : T → Set where
  head : ∀ {xs} → Field w (ψ w [] ∷ xs)
  index : ∀ {u b xs} → Field w u → Field w (ψ u b ∷ xs)
  argument : ∀ {u b xs} → Field w b → Field w (ψ u b ∷ xs)
  tail : ∀ {u b xs} → Field w xs → Field w (ψ u b ∷ xs)

Origin : T → T → Set
Origin a ν = Σ T (λ w → Field w a × (cof w ≡ c1) × (pred w ≡ ν))

origin-map : ∀ {a b ν} → (∀ {w} → Field w a → Field w b) → Origin a ν → Origin b ν
origin-map lift (w , f , ec , ep) = w , lift f , ec , ep

origin-rename : ∀ {a μ ν} → μ ≡ ν → Origin a μ → Origin a ν
origin-rename e (w , f , ec , ep) = w , f , ec , trans ep e

Omega-inj : ∀ {μ ν} → cΩ μ ≡ cΩ ν → μ ≡ ν
Omega-inj refl = refl

cof-origin : ∀ a {ν} → cof a ≡ cΩ ν → Origin a ν
cof₀-origin : ∀ u k {ν} → cof u ≡ k → cofψ0 u k ≡ cΩ ν → Origin (ψ u [] ∷ []) ν
cof₊-origin : ∀ u b k {ν} → cof b ≡ k → cofA u k ≡ cΩ ν → Origin (ψ u b ∷ []) ν
cofψ-origin : ∀ u μ m a {ν} → Origin a μ → cofψ₊ u μ m ≡ cΩ ν → Origin a ν

cof-origin [] ()
cof-origin (ψ u b ∷ y ∷ ys) e =
  origin-map {a = y ∷ ys} {b = ψ u b ∷ y ∷ ys} tail (cof-origin (y ∷ ys) e)
cof-origin (ψ u b@(_ ∷ _) ∷ []) e = cof₊-origin u b (cof b) refl e
cof-origin (ψ u@(_ ∷ _) [] ∷ []) e = cof₀-origin u (cof u) refl e
cof-origin (ψ [] [] ∷ []) ()

cof₀-origin u c0 eu ()
cof₀-origin u c1 eu e = u , head , eu , Omega-inj e
cof₀-origin u cω eu ()
cof₀-origin u (cΩ μ) eu e = origin-map {a = u} {b = ψ u [] ∷ []} index
  (origin-rename (Omega-inj e) (cof-origin u eu))

cof₊-origin u b c0 eb ()
cof₊-origin u b c1 eb ()
cof₊-origin u b cω eb ()
cof₊-origin u b (cΩ μ) eb e = origin-map {a = b} {b = ψ u b ∷ []} argument
  (cofψ-origin u μ (cmpᵀ (sucT μ) u) b (cof-origin b eb) e)

cofψ-origin u μ lt a o e = origin-rename (Omega-inj e) o
cofψ-origin u μ eq a o e = origin-rename (Omega-inj e) o
cofψ-origin u μ gt a o ()

scan-origin : ∀ t {ν u} → scan t ≡ just (ν , u) → Origin t ν
scan₀-origin : ∀ v k {ν u} → cof v ≡ k → scan₀ v k ≡ just (ν , u) →
  Origin (ψ v [] ∷ []) ν
scan₊-origin : ∀ v b k {ν u} → cof b ≡ k → scan₊ v b k ≡ just (ν , u) →
  Origin (ψ v b ∷ []) ν

scan-origin [] ()
scan-origin (ψ v b ∷ y ∷ ys) e =
  origin-map {a = y ∷ ys} {b = ψ v b ∷ y ∷ ys} tail (scan-origin (y ∷ ys) e)
scan-origin (ψ v b@(_ ∷ _) ∷ []) e = scan₊-origin v b (cof b) refl e
scan-origin (ψ v@(_ ∷ _) [] ∷ []) e = scan₀-origin v (cof v) refl e
scan-origin (ψ [] [] ∷ []) ()

scan₀-origin v c0 ev ()
scan₀-origin v c1 ev ()
scan₀-origin v cω ev e = origin-map {a = v} {b = ψ v [] ∷ []} index (scan-origin v e)
scan₀-origin v (cΩ μ) ev ()

scan₊-origin v b c0 eb ()
scan₊-origin v b c1 eb ()
scan₊-origin v b cω eb e = origin-map {a = b} {b = ψ v b ∷ []} argument (scan-origin b e)
scan₊-origin v b (cΩ μ) eb refl =
  origin-map {a = b} {b = ψ v b ∷ []} argument (cof-origin b eb)
```

`scan-origin` 将一次扫描许可加入的 ν 定位到同一原项里的字面 Ω 字段，
其后继共尾证据与前驱等式都随证明给出。结合历史环境使用时，这是先前
展开步骤的字面来源证，不是把当前目标 u 放进候选表。
本篇没有证明固定层号的全部目标集合有限或稠密，也没有写树侧 ψ。
