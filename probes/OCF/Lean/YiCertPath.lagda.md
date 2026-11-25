# 原型 (a): 层号的字面证书

> 判决: 原型, 不替换主线. 树, 层号, 运算逐字是精简块的 (`YiRWBlock`, `YiRWOps`, 直接导入); 只改层号的证据: Ω 形状的 "下标层 ≤ 每个孩子" 由一条路径换成字面证书 `Ab k (h c)` (孩子层由下标层逐形状一致地搭起, 叶子处是下标层本身 `here` 或一条路径 `via`).
> 编译定理: 塔各项与 Λ 的证据仍是闭项 (`Ok-tw`, `Ok-Λ`), 塔的孩子层的证书叶子全是 `here` (`ab⊕ here`); 读回层号的证书叶子是 `via`.
> 不否定什么. 折叠在 `YiCertFold`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCertPath where

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

`Ab k m`: m 由 k 搭起. `ab` 对形状的一切孩子一致下行, 所以它给出的路径只含 `inu`; 叶子 `here` 处层号逐字是 k, 叶子 `via` 处只有一条路径.

```agda
data Ab (k : L) : L → Set where
  here : Ab k k
  via  : ∀ {a} → k ≤ a → Ab k a
  ab   : ∀ {s h} → ((c : Ch s) → Ab k (h c)) → Ab k (nd s h)

ab→≤ : ∀ {k m} → Ab k m → k ≤ m
ab→≤ here    = self
ab→≤ (via w) = w
ab→≤ (ab f)  = inu (λ c → ab→≤ (f c))

ab⊕ : ∀ {k a} → Ab k a → (b : L) → Ab k (a ⊕ b)
ab⊕ u zero     = u
ab⊕ u (nd s h) = ab (λ c → ab⊕ u (h c))
```

## 层号的证据

与 `YiRWPath` 逐行相同, 只有 Ω 形状的第二个分量换成证书.

```agda
mutual
  Ok : L → Set
  Ok zero     = ⊤
  Ok (nd s h) = OkS s h × ((c : Ch s) → Ok (h c))

  OkS : (s : Sh) → (Ch s → L) → Set
  OkS sS     h = ⊤
  OkS sL     g = (n : ℕ) → g n ≤ g (suc n)
  OkS (sΩ k) h = Ok k × ((c : Tr k) → Ab k (h c))

kh : ∀ {k h} → Ok (nd (sΩ k) h) → (c : Tr k) → k ≤ h c
kh o c = ab→≤ (proj₂ (proj₁ o) c)

mutual
  Ok-at : (ℓ : L) → Ok ℓ → (p : Pos ℓ) → Ok (at ℓ p)
  Ok-at (nd s h)      (_ , oc)      (inj₂ (c , t)) = Ok-at⁼ (h c) (oc c) t
  Ok-at (nd (sΩ k) h) ((ok , _) , _) (inj₁ t)      = Ok-at⁼ k ok t

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

OkS⊕ : (a : L) (s : Sh) (h : Ch s → L) → OkOS a s h → OkS s (λ c → a ⊕ h c)
OkS⊕ a sS     h _        = tt
OkS⊕ a sL     g r        = λ n → wk (⊕⊑ a (r n))
OkS⊕ a (sΩ k) h (v , ok) = ok , λ c → ab⊕ (via v) (h c)

Ok⊕ : (a b : L) → Ok a → OkO a b → Ok (a ⊕ b)
Ok⊕ a zero     oa _         = oa
Ok⊕ a (nd s h) oa (os , ob) = OkS⊕ a s h os , λ c → Ok⊕ a (h c) oa (ob c)

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
Ok-tw (suc n) = (Ok-tw n , λ c → ab⊕ here (↑ (tw n) c)) , λ c →
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
