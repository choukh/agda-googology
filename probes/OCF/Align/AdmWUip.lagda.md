# 可入下标上的比较式更新 (四): 函数外延推出高度的 UIP (条件)

> 不含记号. 入口 [AdmW](AdmW.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. **函数外延 `Funext` 只作前提** (模块参数), 本篇的结论都是条件定理 (条件: Funext); 不进成品.
>
> 用途: [AdmWCoh](AdmWCoh.lagda.md) 的 `dirA-cond` 以 `UIPᴴ` (高度 `HB S₀` 的相等证明唯一) 为前提. 本篇说明这个前提可满足: 有函数外延就有它 (`fe→uip`). 证明是标准的编码-解码: 结构相等 `Code x y` 是命题 (用外延), 相等 $x\equiv y$ 是它的收缩 (解码在 `refl` 上规范化, 不需要外延在 `refl` 上的计算), 所以相等是命题.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AdmWUip where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Binary.PropositionalEquality.Properties using (trans-symʳ)
open import OCF.Align.HtTowerTy
open import OCF.Align.AdmWCoh using (UIPᴴ)

Funext : Set₁
Funext = ∀ {X : Set} {Y : X → Set} {f g : (x : X) → Y x} → (∀ x → f x ≡ g x) → f ≡ g

Code : HB S₀ → HB S₀ → Set
Code hz hz = ⊤
Code (hs x) (hs y) = Code x y
Code (hl f) (hl g) = ∀ n → Code (f n) (g n)
Code (hΩ _ f) (hΩ _ g) = ∀ a → Code (f a) (g a)
Code _ _ = ⊥

rc : ∀ x → Code x x
rc hz = tt
rc (hs x) = rc x
rc (hl f) = λ n → rc (f n)
rc (hΩ κ f) = λ a → rc (f a)

encode : ∀ {x y} → x ≡ y → Code x y
encode {x} refl = rc x

module _ (fe : Funext) where
  decode : ∀ x y → Code x y → x ≡ y
  decode hz hz _ = refl
  decode (hs x) (hs y) c = cong hs (decode x y c)
  decode (hl f) (hl g) c = cong hl (fe (λ n → decode (f n) (g n) (c n)))
  decode (hΩ κ f) (hΩ κ′ g) c = cong (hΩ κ) (fe (λ a → decode (f a) (g a) (c a)))
  decode hz (hs _) ()
  decode hz (hl _) ()
  decode hz (hΩ _ _) ()
  decode (hs _) hz ()
  decode (hs _) (hl _) ()
  decode (hs _) (hΩ _ _) ()
  decode (hl _) hz ()
  decode (hl _) (hs _) ()
  decode (hl _) (hΩ _ _) ()
  decode (hΩ _ _) hz ()
  decode (hΩ _ _) (hs _) ()
  decode (hΩ _ _) (hl _) ()

  isP : ∀ x y (c c′ : Code x y) → c ≡ c′
  isP hz hz c c′ = refl
  isP (hs x) (hs y) c c′ = isP x y c c′
  isP (hl f) (hl g) c c′ = fe (λ n → isP (f n) (g n) (c n) (c′ n))
  isP (hΩ _ f) (hΩ _ g) c c′ = fe (λ a → isP (f a) (g a) (c a) (c′ a))
  isP hz (hs _) ()
  isP hz (hl _) ()
  isP hz (hΩ _ _) ()
  isP (hs _) hz ()
  isP (hs _) (hl _) ()
  isP (hs _) (hΩ _ _) ()
  isP (hl _) hz ()
  isP (hl _) (hs _) ()
  isP (hl _) (hΩ _ _) ()
  isP (hΩ _ _) hz ()
  isP (hΩ _ _) (hs _) ()
  isP (hΩ _ _) (hl _) ()

  -- 在 refl 上规范化的解码
  r : ∀ {x y} → Code x y → x ≡ y
  r {x} {y} c = trans (decode x y c) (sym (decode y y (rc y)))

  r-enc : ∀ {x y} (e : x ≡ y) → r (encode e) ≡ e
  r-enc {x} refl = trans-symʳ (decode x x (rc x))

fe→uip : Funext → UIPᴴ
fe→uip fe e e′ = trans (sym (r-enc fe e)) (trans (cong (r fe) (isP fe _ _ (encode e) (encode e′))) (r-enc fe e′))
```
