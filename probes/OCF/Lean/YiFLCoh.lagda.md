# 折叠带证据 (F1 原型): 相干的证据 (只到定义)

> 判决: 原型, 只到定义; 后续未走通. `Eᶜ` 在 `YiFLBlock.E` 上加一条: ℕ 极限处各项的证据要等于后一项的证据沿相邻序的限制 (`dn`). 这是单调性能陈述的前提 (`YiFLCheck.dep`).
> 编译定理: 限制 `dn` 对一切第一位置序的推导全定义; 各层 Ω 树的规范证据相干 (`Ωt-Eᶜ`, 相干一栏是 `refl`).
> 不否定什么. 下一步 "加法保持相干" 两种写法都过不了停机检查 (推导里 `◃t` 的中间树不是结构上更小的), 没有编译的否定, 只写未走通; 报错原文在回报里.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFLCoh where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (Ωt)
open import OCF.Lean.YiFreshLegal using (_⊢_◃_; ◃s; ◃l; ◃w; ◃u; ◃c; ◃t; Ωt-leg; seq)
```

## 证据与限制 (互递归)

`dn d ey` 是 y 的证据沿 d : x ◃ y 限制到 x 上. `Eᶜ` 的 ℕ 极限一行引用 `dn`; `dn` 的各行只调用自己, 所以停机通过.

```agda
mutual
  Eᶜ : (ℓ : L) → Tr ℓ → Set
  Eᶜ ℓ zero       = ⊤
  Eᶜ ℓ (suc x)    = Eᶜ ℓ x
  Eᶜ ℓ (lim f)    = Σ ((n : ℕ) → Eᶜ ℓ (f n)) λ ef →
                      Maybe (Σ ((n : ℕ) → ℓ ⊢ f n ◃ f (suc n)) λ a → (n : ℕ) → ef n ≡ dn (a n) (ef (suc n)))
  Eᶜ ℓ (Ω p g)    = EPᶜ ℓ p × ((z : Br ℓ p) → EBrᶜ ℓ p z → Eᶜ ℓ (g z))
  Eᶜ ℓ (up x c y) = Eᶜ ℓ x × EIᶜ ℓ c × EChᶜ ℓ c y

  EPᶜ : (ℓ : L) → Pos ℓ → Set
  EPᶜ (suc a)  t              = EP⁼ᶜ a t
  EPᶜ (lim g)  (n , t)        = EP⁼ᶜ (g n) t
  EPᶜ (Ωₗ k h) (inj₁ t)       = EP⁼ᶜ k t
  EPᶜ (Ωₗ k h) (inj₂ (c , t)) = Eᶜ k c × EP⁼ᶜ (h c) t

  EP⁼ᶜ : (a : L) → Pos⁼ a → Set
  EP⁼ᶜ a (inj₁ _) = ⊤
  EP⁼ᶜ a (inj₂ p) = EPᶜ a p

  EBrᶜ : (ℓ : L) (p : Pos ℓ) → Br ℓ p → Set
  EBrᶜ (suc a)  t              z = EBr⁼ᶜ a t z
  EBrᶜ (lim g)  (n , t)        z = EBr⁼ᶜ (g n) t z
  EBrᶜ (Ωₗ k h) (inj₁ t)       z = EBr⁼ᶜ k t z
  EBrᶜ (Ωₗ k h) (inj₂ (c , t)) z = EBr⁼ᶜ (h c) t z

  EBr⁼ᶜ : (a : L) (t : Pos⁼ a) → Br⁼ a t → Set
  EBr⁼ᶜ a (inj₁ _) z = Eᶜ a z
  EBr⁼ᶜ a (inj₂ p) z = EBrᶜ a p z

  EIᶜ : (ℓ : L) → Ch ℓ → Set
  EIᶜ zero     ()
  EIᶜ (suc a)  _ = ⊤
  EIᶜ (lim g)  n = ⊤
  EIᶜ (Ωₗ k h) c = Eᶜ k c

  EChᶜ : (ℓ : L) (c : Ch ℓ) → ChT ℓ c → Set
  EChᶜ (suc a)  _ y = Eᶜ a y
  EChᶜ (lim g)  n y = Eᶜ (g n) y
  EChᶜ (Ωₗ k h) c y = Eᶜ (h c) y

  eFromᶜ : (ℓ : L) (p : Pos ℓ) (x : Tr (at ℓ p)) → Eᶜ (at ℓ p) x → EBrᶜ ℓ p (fromBr ℓ p x)
  eFromᶜ (suc a)  t              x e = eFrom⁼ᶜ a t x e
  eFromᶜ (lim g)  (n , t)        x e = eFrom⁼ᶜ (g n) t x e
  eFromᶜ (Ωₗ k h) (inj₁ t)       x e = eFrom⁼ᶜ k t x e
  eFromᶜ (Ωₗ k h) (inj₂ (c , t)) x e = eFrom⁼ᶜ (h c) t x e

  eFrom⁼ᶜ : (a : L) (t : Pos⁼ a) (x : Tr (at⁼ a t)) → Eᶜ (at⁼ a t) x → EBr⁼ᶜ a t (fromBr⁼ a t x)
  eFrom⁼ᶜ a (inj₁ _) x e = e
  eFrom⁼ᶜ a (inj₂ p) x e = eFromᶜ a p x e

  dn : ∀ {ℓ x y} → ℓ ⊢ x ◃ y → Eᶜ ℓ y → Eᶜ ℓ x
  dn ◃s       ey = ey
  dn (◃l n)   ey = proj₁ ey n
  dn {ℓ} (◃w {p = p}) ey = proj₂ ey (fromBr ℓ p zero) (eFromᶜ ℓ p zero tt)
  dn (◃u _)   ey = proj₁ ey
  dn (◃c {ℓ} {c = c} d) ey = proj₁ ey , proj₁ (proj₂ ey) , dnCh ℓ c d (proj₂ (proj₂ ey))
  dn (◃t d e) ez = dn d (dn e ez)

  dnCh : (ℓ : L) (c : Ch ℓ) {y′ y : ChT ℓ c} → chL ℓ c ⊢ chT ℓ c y′ ◃ chT ℓ c y → EChᶜ ℓ c y → EChᶜ ℓ c y′
  dnCh (suc a)  _ d e = dn d e
  dnCh (lim g)  n d e = dn d e
  dnCh (Ωₗ k h) c d e = dn d e
```

## 规范证据相干

`Ωt (lim g)` 的第 n+1 项是第 n 项再嵌入一个孩子, 证据的限制就是取第一分量.

```agda
Ωt-Eᶜ : (ℓ : L) → Eᶜ ℓ (Ωt ℓ)
Ωt-Eᶜ zero     = tt
Ωt-Eᶜ (suc a)  = tt , λ z ez → tt , tt , ez
Ωt-Eᶜ (lim g)  = cl , just (proj₂ (Ωt-leg (lim g)) , λ n → refl)
  where
  cl : (n : ℕ) → Eᶜ (lim g) (seq (Ωt (lim g)) n)
  cl zero    = tt , tt , Ωt-Eᶜ (g zero)
  cl (suc n) = cl n , tt , Ωt-Eᶜ (g (suc n))
Ωt-Eᶜ (Ωₗ k h) = tt , λ c ec → tt , ec , Ωt-Eᶜ (h c)
```
