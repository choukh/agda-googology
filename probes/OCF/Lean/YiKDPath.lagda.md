# 龙骨原型: 证书

> 判决: 候选原型 (证据), 不替换主线. 逐行是候选 A 的 `YiKVPath`, 只改一处: 证书 `ab` 在 Ω 形状上多带一条路径 "该形状的下标层 ≤ 地板" (`AbS`); 读回层号 a ⊕ b 的证书由 `OkO a b` 里已有的同一条路径填出 (`ab⊕`).
> 编译定理: 塔各项与 Λ 的证据是闭项 (`Ok-tw`, `Ok-Λ`), 无前提. 不否定什么. 折叠在 `YiKDFold`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKDPath where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath public
  hiding (Ok; OkS; Ok-at; Ok-at⁼; OkOS; OkO; OkS⊕; Ok⊕; OkO⊕; OkO↑; Ok-tw; Ok-Λ; emb; emb-mono)
```

## 证书

`Ab a m`: m 由地板 a 对一切孩子一致地搭起.

```agda
AbS : L → Sh → Set
AbS a sS     = ⊤
AbS a sL     = ⊤
AbS a (sΩ k) = k ≤ a

data Ab (a : L) : L → Set where
  here : Ab a a
  ab   : ∀ {s h} → AbS a s → ((c : Ch s) → Ab a (h c)) → Ab a (nd s h)

ab→≤ : ∀ {a m} → Ab a m → a ≤ m
ab→≤ here     = self
ab→≤ (ab _ f) = inu (λ c → ab→≤ (f c))
```

## 层号的证据

```agda
mutual
  Ok : L → Set
  Ok zero     = ⊤
  Ok (nd s h) = OkS s h × ((c : Ch s) → Ok (h c))

  OkS : (s : Sh) → (Ch s → L) → Set
  OkS sS     h = ⊤
  OkS sL     g = (n : ℕ) → g n ≤ g (suc n)
  OkS (sΩ k) h = Ok k × Σ L λ a → (k ≤ a) × ((c : Tr k) → Ab a (h c))

flr : ∀ {k h} → Ok (nd (sΩ k) h) → L
flr o = proj₁ (proj₂ (proj₁ o))

kfl : ∀ {k h} (o : Ok (nd (sΩ k) h)) → k ≤ flr o
kfl o = proj₁ (proj₂ (proj₂ (proj₁ o)))

crt : ∀ {k h} (o : Ok (nd (sΩ k) h)) (c : Tr k) → Ab (flr o) (h c)
crt o = proj₂ (proj₂ (proj₂ (proj₁ o)))

kh : ∀ {k h} (o : Ok (nd (sΩ k) h)) (c : Tr k) → k ≤ h c
kh o c = kfl o ∙ ab→≤ (crt o c)

mutual
  Ok-at : (ℓ : L) → Ok ℓ → (p : Pos ℓ) → Ok (at ℓ p)
  Ok-at (nd s h)      (_ , oc)       (inj₂ (c , t)) = Ok-at⁼ (h c) (oc c) t
  Ok-at (nd (sΩ k) h) ((ok , _) , _) (inj₁ t)       = Ok-at⁼ k ok t

  Ok-at⁼ : (a : L) → Ok a → (t : Pos⁼ a) → Ok (proj₁ (sl⁼ a t))
  Ok-at⁼ a o (inj₁ _) = o
  Ok-at⁼ a o (inj₂ p) = Ok-at a o p

OkOS : L → (s : Sh) → (Ch s → L) → Set
OkOS a sS     h = ⊤
OkOS a sL     g = (n : ℕ) → g n ⊑ g (suc n)
OkOS a (sΩ k) h = (k ≤ a) × Ok k

OkO : L → L → Set
OkO a zero     = ⊤
OkO a (nd s h) = OkOS a s h × ((c : Ch s) → OkO a (h c))

abS : (a : L) (s : Sh) (h : Ch s → L) → OkOS a s h → AbS a s
abS a sS     h _ = tt
abS a sL     g _ = tt
abS a (sΩ k) h e = proj₁ e

ab⊕ : (a b : L) → OkO a b → Ab a (a ⊕ b)
ab⊕ a zero     _ = here
ab⊕ a (nd s h) e = ab (abS a s h (proj₁ e)) (λ c → ab⊕ a (h c) (proj₂ e c))

OkS⊕ : (a : L) (s : Sh) (h : Ch s → L) → OkOS a s h → ((c : Ch s) → OkO a (h c)) → OkS s (λ c → a ⊕ h c)
OkS⊕ a sS     h _        _  = tt
OkS⊕ a sL     g r        _  = λ n → wk (⊕⊑ a (r n))
OkS⊕ a (sΩ k) h (v , ok) ob = ok , (a , v , λ c → ab⊕ a (h c) (ob c))

Ok⊕ : (a b : L) → Ok a → OkO a b → Ok (a ⊕ b)
Ok⊕ a zero     oa _         = oa
Ok⊕ a (nd s h) oa (os , ob) = OkS⊕ a s h os ob , λ c → Ok⊕ a (h c) oa (ob c)

OkO⊕ : (a b₁ b₂ : L) → OkO a b₁ → OkO a b₂ → OkO a (b₁ ⊕ b₂)
OkO⊕ a b₁ zero          e₁ _         = e₁
OkO⊕ a b₁ (nd sS h)     e₁ (_ , e₂)  = tt , λ c → OkO⊕ a b₁ (h c) e₁ (e₂ c)
OkO⊕ a b₁ (nd sL g)     e₁ (r , e₂)  = (λ n → ⊕⊑ b₁ (r n)) , λ n → OkO⊕ a b₁ (g n) e₁ (e₂ n)
OkO⊕ a b₁ (nd (sΩ k) h) e₁ (o , e₂)  = o , λ c → OkO⊕ a b₁ (h c) e₁ (e₂ c)

OkO↑ : (a k : L) → Ok k → k ≤ a → (t : Tr k) → OkO a (↑ k t)
OkO↑ a k        ok v zero         = tt
OkO↑ a k        ok v (suc x)      = tt , λ _ → OkO↑ a k ok v x
OkO↑ a k        ok v (lim f r)    = (λ n → ◃→⊑ k (r n)) , λ n → OkO↑ a k ok v (f n)
OkO↑ a k        ok v (Ω p g)      = (posW k p ∙ v , Ok-at k ok p) , λ c → OkO↑ a k ok v (g (fromBr k p c))
OkO↑ a (nd s h) ok v (up x c y _) =
  OkO⊕ a (↑ (nd s h) x) (↑ (h c) y) (OkO↑ a (nd s h) ok v x) (OkO↑ a (h c) (proj₂ ok c) (inc c self ∙ v) y)

Ok-tw : (n : ℕ) → Ok (tw n)
Ok-tw zero    = tt
Ok-tw (suc n) = (Ok-tw n , (tw n , self , λ c → ab⊕ (tw n) (↑ (tw n) c) (OkO↑ (tw n) (tw n) (Ok-tw n) self c))) , λ c →
  Ok⊕ (tw n) (↑ (tw n) c) (Ok-tw n) (OkO↑ (tw n) (tw n) (Ok-tw n) self c)

Ok-Λ : Ok Λ
Ok-Λ = (λ n → ink self) , Ok-tw
```

## 孩子树沿路径搬进高层

```agda
emb : (ℓ : L) → Ok ℓ → ∀ {k} → k ≤ ℓ → Tr⁺ k → Tr⁺ ℓ
emb ℓ             o self      y = y
emb (nd s h)      o (inc c v) y = upz c (emb (h c) (proj₂ o c) v y)
emb (nd s h)      o (inu vs)  y = upz (c₀ s) (emb (h (c₀ s)) (proj₂ o (c₀ s)) (vs (c₀ s)) y)
emb (nd (sΩ k) h) o (ink v)   y = upz zero (emb (h zero) (proj₂ o zero) (v ∙ kh o zero) y)

emb-mono : (ℓ : L) (o : Ok ℓ) {k : L} (v : k ≤ ℓ) {y′ y : Tr⁺ k}
         → k ⊢ proj₁ y′ ◃ proj₁ y → ℓ ⊢ proj₁ (emb ℓ o v y′) ◃ proj₁ (emb ℓ o v y)
emb-mono ℓ             o self      d = d
emb-mono (nd s h)      o (inc c v) d = ◃c zero c (emb-mono (h c) (proj₂ o c) v d)
emb-mono (nd s h)      o (inu vs)  d = ◃c zero (c₀ s) (emb-mono (h (c₀ s)) (proj₂ o (c₀ s)) (vs (c₀ s)) d)
emb-mono (nd (sΩ k) h) o (ink v)   d = ◃c zero zero (emb-mono (h zero) (proj₂ o zero) (v ∙ kh o zero) d)
```
