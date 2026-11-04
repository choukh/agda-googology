# 严格列 (二): 只接受带证书的码

> 入口 [TLCode](TLCode.lagda.md). **判决: HOLDS (编译过, 无条件).** `Lit t`: $t$ 里每个极限 `lim f s` 都有 $f_n$ 是 $f_{n+1}$ 的**字面子项** (`f n <ᴵ f (suc n)`). 高度结构 `HL h : HtB` 对每个带证书的 $t$ 给出, 11 个字段全闭合.
>
> - **值是字面的.** `rkT h end ≡ t` (`rk-top`, `refl`). 秩就是 $t$ 的字面子项, 没有求和: 导入闭包不含 `plus`, `Sb`, `val`, `⌈_⌉`, `ᶜ+`, `Code`.
> - **极限的第 $i$ 项是绝对的.** 顶的链是 $f_0,f_1,\dots$ 本身 (`rk-chain`), 不是 $\sum_{j\le i}(g_j+1)$.
> - **位置按块分解.** 块 $i+1$ 是 $f_{i+1}$ 里高于证书切点的部分 (`above`), 所以位置表示唯一, 三歧的相等是 $\equiv$. 证书的切点不用规范化: 切点走 `lim j q` 就从第 $j$ 块开始, 下面的块不算.
> - **字面严格与前缀.** 证书说 $f_{n+1}$ 字面含 $f_n$. 这不是额外的累加, 也去不掉: 它就是 "$<$ 映到字面路径" (`rk<`), 见 [TLCode](TLCode.lagda.md) 的说明.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLCodeLit where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Free.Level using (Ordᴵ; zero; suc; lim; _<ᴵ_; _⊑ᴵ_; <ᴵ-trans; _≅ᴵ_; _≺ᴵ_; via; ≺ᴵ-irrefl; ≅ᴵ-sym; ≅ᴵ-refl)
open import OCF.Align.LadderOrdBase using (HtB; Tri; tlt; teq; tgt; chain)
open import OCF.Align.TLCodeShape
```

## §1 证书

```agda
data Lit : Ordᴵ → Set where
  lz : Lit zero
  ls : ∀ {a} → Lit a → Lit (suc a)
  ll : ∀ {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} → (∀ n → Lit (f n)) → (∀ n → f n <ᴵ f (suc n)) → Lit (lim f s)
```

## §2 块形

`above h q`: $t$ 里严格高于切点 $q$ 的部分的块形. `shape h`: $t$ 全部的块形. 块 $0$ 由切点决定, 块 $i+1$ 是 $f_{i+j+1}$ 高于证书切点的部分. 这里只用证书的路径, 不比较.

```agda
above : ∀ {a t} → Lit t → a <ᴵ t → Sh
tailb : ∀ {f : ℕ → Ordᴵ} → (∀ n → Lit (f n)) → (∀ n → f n <ᴵ f (suc n)) → ℕ → Sh → ℕ → Sh
above (ls h) zero = sz
above (ls h) (suc q) = ss (above h q)
above (ll hf hr) (lim j q) = sl (tailb hf hr j (above (hf j) q))
tailb hf hr j c₀ zero = c₀
tailb hf hr j c₀ (suc i) = above (hf (suc i + j)) (hr (i + j))

shape : ∀ {t} → Lit t → Sh
shape lz = sz
shape (ls h) = ss (shape h)
shape (ll hf hr) = sl (tailb hf hr 0 (shape (hf 0)))
```

## §3 秩: 字面子项

```agda
rkL : ∀ {g : ℕ → Sh} → (∀ i → Pos (ss (g i)) → Ordᴵ) → Pos (sl g) → Ordᴵ
rkL ρ (blk j p) = ρ j p

rkS : ∀ {t} (h : Lit t) → Pos (shape h) → Ordᴵ
rkA : ∀ {a t} (h : Lit t) (q : a <ᴵ t) → Pos (above h q) → Ordᴵ
tailρ : ∀ {f : ℕ → Ordᴵ} (hf : ∀ n → Lit (f n)) (hr : ∀ n → f n <ᴵ f (suc n)) j c₀ → (Pos c₀ → Ordᴵ) → ∀ i → Pos (ss (tailb hf hr j c₀ i)) → Ordᴵ
rkS (ls {a} h) end = a
rkS (ls h) (low p) = rkS h p
rkS (ll hf hr) p = rkL (tailρ hf hr 0 _ (rkS (hf 0))) p
rkA (ls {a} h) (suc q) end = a
rkA (ls h) (suc q) (low p) = rkA h q p
rkA (ll hf hr) (lim j q) p = rkL (tailρ hf hr j _ (rkA (hf j) q)) p
tailρ {f} hf hr j c₀ r₀ zero end = f j
tailρ hf hr j c₀ r₀ zero (low p) = r₀ p
tailρ {f} hf hr j c₀ r₀ (suc i) end = f (suc i + j)
tailρ hf hr j c₀ r₀ (suc i) (low p) = rkA (hf (suc i + j)) (hr (i + j)) p

rkT : ∀ {t} (h : Lit t) → Pos (ss (shape h)) → Ordᴵ
rkT {t} h end = t
rkT h (low p) = rkS h p

-- 值是字面的
rk-top : ∀ {t} (h : Lit t) → rkT h end ≡ t
rk-top h = refl
```

## §4 秩保序

块间: 块 $i$ 的顶低于块 $i+1$ 的每个点.

```agda
ltB-gen : ∀ (g : ℕ → Sh) (ρ : ∀ i → Pos (ss (g i)) → Ordᴵ)
  (in< : ∀ i (p q : Pos (ss (g i))) → p <ᴾ q → ρ i p <ᴵ ρ i q)
  (st : ∀ i (q : Pos (ss (g (suc i)))) → ρ i end <ᴵ ρ (suc i) q)
  → ∀ j k (p : Pos (ss (g j))) (q : Pos (ss (g k))) → ltB g j k p q → ρ j p <ᴵ ρ k q
ltB-gen g ρ in< st zero zero p q x = in< 0 p q x
ltB-gen g ρ in< st zero (suc k) end q x = up0 k q
  where
  up0 : ∀ k (q : Pos (ss (g (suc k)))) → ρ 0 end <ᴵ ρ (suc k) q
  up0 zero q = st 0 q
  up0 (suc k) q = <ᴵ-trans (up0 k end) (st (suc k) q)
ltB-gen g ρ in< st zero (suc k) (low p) q x = <ᴵ-trans (in< 0 (low p) end tt) (ltB-gen g ρ in< st zero (suc k) end q tt)
ltB-gen g ρ in< st (suc j) (suc k) p q x = ltB-gen (λ i → g (suc i)) (λ i → ρ (suc i)) (λ i → in< (suc i)) (λ i → st (suc i)) j k p q x
```

```agda
f<+ : ∀ {f : ℕ → Ordᴵ} (hr : ∀ n → f n <ᴵ f (suc n)) {a} j i → a <ᴵ f j → a <ᴵ f (i + j)
f<+ hr j zero x = x
f<+ hr j (suc i) x = <ᴵ-trans (f<+ hr j i x) (hr (i + j))

rkS< : ∀ {t} (h : Lit t) p → rkS h p <ᴵ t
rkA< : ∀ {a t} (h : Lit t) (q : a <ᴵ t) p → rkA h q p <ᴵ t
rkA> : ∀ {a t} (h : Lit t) (q : a <ᴵ t) p → a <ᴵ rkA h q p
tail< : ∀ {f : ℕ → Ordᴵ} (hf : ∀ n → Lit (f n)) (hr : ∀ n → f n <ᴵ f (suc n)) j c₀ (r₀ : Pos c₀ → Ordᴵ) → (∀ p → r₀ p <ᴵ f j) → ∀ i x → tailρ hf hr j c₀ r₀ i x <ᴵ f (suc (i + j))
rkS< (ls h) end = zero
rkS< (ls h) (low p) = suc (rkS< h p)
rkS< (ll hf hr) (blk i x) = lim (suc (i + 0)) (tail< hf hr 0 _ (rkS (hf 0)) (rkS< (hf 0)) i x)
rkA< (ls h) (suc q) end = zero
rkA< (ls h) (suc q) (low p) = suc (rkA< h q p)
rkA< (ll hf hr) (lim j q) (blk i x) = lim (suc (i + j)) (tail< hf hr j _ (rkA (hf j) q) (rkA< (hf j) q) i x)
tail< hf hr j c₀ r₀ r< zero end = hr j
tail< hf hr j c₀ r₀ r< zero (low p) = <ᴵ-trans (r< p) (hr j)
tail< hf hr j c₀ r₀ r< (suc i) end = hr (suc (i + j))
tail< hf hr j c₀ r₀ r< (suc i) (low p) = <ᴵ-trans (rkA< (hf (suc i + j)) (hr (i + j)) p) (hr (suc (i + j)))

rkA> (ls h) (suc q) end = q
rkA> (ls h) (suc q) (low p) = rkA> h q p
rkA> (ll hf hr) (lim j q) (blk zero end) = q
rkA> (ll hf hr) (lim j q) (blk zero (low p)) = rkA> (hf j) q p
rkA> (ll hf hr) (lim j q) (blk (suc i) end) = <ᴵ-trans (f<+ hr j i q) (hr (i + j))
rkA> (ll hf hr) (lim j q) (blk (suc i) (low p)) = <ᴵ-trans (f<+ hr j i q) (rkA> (hf (suc i + j)) (hr (i + j)) p)

monoS : ∀ {t} (h : Lit t) (p q : Pos (shape h)) → p <ᴾ q → rkS h p <ᴵ rkS h q
monoA : ∀ {a t} (h : Lit t) (c : a <ᴵ t) (p q : Pos (above h c)) → p <ᴾ q → rkA h c p <ᴵ rkA h c q
tailin : ∀ {f : ℕ → Ordᴵ} (hf : ∀ n → Lit (f n)) (hr : ∀ n → f n <ᴵ f (suc n)) j c₀ (r₀ : Pos c₀ → Ordᴵ) → (∀ p → r₀ p <ᴵ f j) → (∀ p q → p <ᴾ q → r₀ p <ᴵ r₀ q) →
         ∀ i (p q : Pos (ss (tailb hf hr j c₀ i))) → p <ᴾ q → tailρ hf hr j c₀ r₀ i p <ᴵ tailρ hf hr j c₀ r₀ i q
tailst : ∀ {f : ℕ → Ordᴵ} (hf : ∀ n → Lit (f n)) (hr : ∀ n → f n <ᴵ f (suc n)) j c₀ (r₀ : Pos c₀ → Ordᴵ) →
         ∀ i (q : Pos (ss (tailb hf hr j c₀ (suc i)))) → tailρ hf hr j c₀ r₀ i end <ᴵ tailρ hf hr j c₀ r₀ (suc i) q
monoS (ls h) (low p) end x = rkS< h p
monoS (ls h) (low p) (low q) x = monoS h p q x
monoS (ll hf hr) (blk j p) (blk k q) x =
  ltB-gen _ (tailρ hf hr 0 _ (rkS (hf 0))) (tailin hf hr 0 _ (rkS (hf 0)) (rkS< (hf 0)) (monoS (hf 0))) (tailst hf hr 0 _ (rkS (hf 0))) j k p q x
monoA (ls h) (suc c) (low p) end x = rkA< h c p
monoA (ls h) (suc c) (low p) (low q) x = monoA h c p q x
monoA (ll hf hr) (lim j c) (blk k p) (blk l q) x =
  ltB-gen _ (tailρ hf hr j _ (rkA (hf j) c)) (tailin hf hr j _ (rkA (hf j) c) (rkA< (hf j) c) (monoA (hf j) c)) (tailst hf hr j _ (rkA (hf j) c)) k l p q x
tailin hf hr j c₀ r₀ r< rm zero (low p) end x = r< p
tailin hf hr j c₀ r₀ r< rm zero (low p) (low q) x = rm p q x
tailin hf hr j c₀ r₀ r< rm (suc i) (low p) end x = rkA< (hf (suc i + j)) (hr (i + j)) p
tailin hf hr j c₀ r₀ r< rm (suc i) (low p) (low q) x = monoA (hf (suc i + j)) (hr (i + j)) p q x
tailst hf hr j c₀ r₀ zero end = hr j
tailst hf hr j c₀ r₀ zero (low p) = rkA> (hf (suc j)) (hr j) p
tailst hf hr j c₀ r₀ (suc i) end = hr (suc (i + j))
tailst hf hr j c₀ r₀ (suc i) (low p) = rkA> (hf (suc (suc (i + j)))) (hr (suc (i + j))) p

rk< : ∀ {t} (h : Lit t) (p q : Pos (ss (shape h))) → p <ᴾ q → rkT h p <ᴵ rkT h q
rk< h (low p) end x = rkS< h p
rk< h (low p) (low q) x = monoS h p q x
```

## §5 实例

```agda
HL : ∀ {t} → Lit t → HtB
HL h = record
  { Ht = Pos (ss (shape h))
  ; _<ᴸ_ = _<ᴾ_
  ; h₀ = fstS (shape h)
  ; tr< = λ {m} {c} {d} → <ᴾ-trans m c d
  ; <-prop = <ᴾ-prop
  ; bot = botS (shape h)
  ; tri = <ᴾ-tri
  ; rk = rkT h
  ; rk< = λ {a} {b} → rk< h a b
  ; view = λ m → proj₁ (V.vw (shape h) m)
  ; view-ok = λ m → proj₂ (V.vw (shape h) m)
  }
```

顶的第 0 行是链, 链的第 $i$ 项是第 $i$ 块的顶 (`view-top`), 它的秩是 $f_i$ (`rk-chain`, §6).

```agda
view-top : ∀ {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} (hf : ∀ n → Lit (f n)) (hr : ∀ n → f n <ᴵ f (suc n)) →
           HtB.view (HL (ll {s = s} hf hr)) end ≡ chain (λ i → low (blk i end)) (λ i → tt)
view-top hf hr = refl
```

## §6 秩的像就是字面子项

`rk<` 说位置是 $t$ 的字面子项里的一条严格链. 反过来, 每个字面子项都是某个位置的秩: 字面严格的树的子项是线性的 (`linear`), 所以切点下面的子项总能在前面的块里找到. 这说明 `HL h` 没有放大也没有缩小: 位置与 $t$ 的字面子项一一对应 (`rk-inj`, `find`).

```agda
cmpℕ : ∀ j k → (Σ ℕ λ d → k ≡ d + j) ⊎ (Σ ℕ λ d → j ≡ d + k)
cmpℕ zero k = inj₁ (k , sym (+-identityʳ k))
cmpℕ (suc j) zero = inj₂ (suc j , cong suc (sym (+-identityʳ j)))
cmpℕ (suc j) (suc k) with cmpℕ j k
... | inj₁ (d , e) = inj₁ (d , trans (cong suc e) (sym (+-suc d j)))
... | inj₂ (d , e) = inj₂ (d , trans (cong suc e) (sym (+-suc d k)))

irrᴵ : ∀ {a} → a <ᴵ a → ⊥
irrᴵ {a} x = ≺ᴵ-irrefl (via (≅ᴵ-refl a) x)

-- 字面严格的树, 子项线性
linear : ∀ {t} (h : Lit t) {a b} → a <ᴵ t → b <ᴵ t → (a <ᴵ b) ⊎ ((a ≡ b) ⊎ (b <ᴵ a))
linear (ls h) zero zero = inj₂ (inj₁ refl)
linear (ls h) zero (suc q) = inj₂ (inj₂ q)
linear (ls h) (suc p) zero = inj₁ p
linear (ls h) (suc p) (suc q) = linear h p q
linear (ll hf hr) (lim j p) (lim k q) with cmpℕ j k
... | inj₁ (d , refl) = linear (hf (d + j)) (f<+ hr j d p) q
... | inj₂ (d , refl) = linear (hf (d + k)) p (f<+ hr k d q)

findS : ∀ {t a} (h : Lit t) → a <ᴵ t → Σ (Pos (shape h)) λ p → rkS h p ≡ a
findA : ∀ {t a b} (h : Lit t) (c : b <ᴵ t) → a <ᴵ t → b <ᴵ a → Σ (Pos (above h c)) λ p → rkA h c p ≡ a
findT : ∀ {f : ℕ → Ordᴵ} (hf : ∀ n → Lit (f n)) (hr : ∀ n → f n <ᴵ f (suc n)) j c₀ (r₀ : Pos c₀ → Ordᴵ) {a} →
        (a <ᴵ f j → Σ (Pos c₀) λ p → r₀ p ≡ a) → ∀ i → a <ᴵ f (i + j) → Σ (Pos (sl (tailb hf hr j c₀))) λ p → rkL (tailρ hf hr j c₀ r₀) p ≡ a
findT hf hr j c₀ r₀ b zero q with b q
... | p , e = blk 0 (low p) , e
findT {f} hf hr j c₀ r₀ b (suc i) q with linear (hf (suc i + j)) q (hr (i + j))
... | inj₁ x = findT hf hr j c₀ r₀ b i x
... | inj₂ (inj₁ refl) = topAt i
  where
  topAt : ∀ i → Σ (Pos (sl (tailb hf hr j c₀))) λ p → rkL (tailρ hf hr j c₀ r₀) p ≡ f (i + j)
  topAt zero = blk 0 end , refl
  topAt (suc i) = blk (suc i) end , refl
... | inj₂ (inj₂ x) with findA (hf (suc i + j)) (hr (i + j)) q x
...   | p , e = blk (suc i) (low p) , e
findS (ls h) zero = end , refl
findS (ls h) (suc q) with findS h q
... | p , e = low p , e
findS {a = a} (ll {f} hf hr) (lim k q) = findT hf hr 0 _ (rkS (hf 0)) (findS (hf 0)) k (subst (λ z → a <ᴵ f z) (sym (+-identityʳ k)) q)
findA (ls h) (suc c) zero x = end , refl
findA (ls h) (suc c) (suc q) x with findA h c q x
... | p , e = low p , e
findA (ls h) zero zero x = ⊥-elim (irrᴵ x)
findA (ls h) zero (suc q) x = ⊥-elim (irrᴵ (<ᴵ-trans x q))
findA (ll hf hr) (lim j c) (lim k q) x with cmpℕ j k
... | inj₁ (d , refl) = findT hf hr j _ (rkA (hf j) c) (λ q′ → findA (hf j) c q′ x) d q
... | inj₂ (d , refl) = findT hf hr (d + k) _ (rkA (hf (d + k)) c) (λ q′ → findA (hf (d + k)) c q′ x) 0 (f<+ hr k d q)

find : ∀ {t a} (h : Lit t) → a <ᴵ suc t → Σ (Pos (ss (shape h))) λ p → rkT h p ≡ a
find h zero = end , refl
find h (suc q) with findS h q
... | p , e = low p , e

-- 秩单射: 位置就是字面子项
rk-inj : ∀ {t} (h : Lit t) (p q : Pos (ss (shape h))) → rkT h p ≡ rkT h q → p ≡ q
rk-inj h p q e with <ᴾ-tri p q
... | tlt x = ⊥-elim (irrᴵ (subst (rkT h p <ᴵ_) (sym e) (rk< h p q x)))
... | teq x = x
... | tgt x = ⊥-elim (irrᴵ (subst (_<ᴵ rkT h p) (sym e) (rk< h q p x)))
```

顶的链就是列本身.

```agda
rk-chain : ∀ {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} (hf : ∀ n → Lit (f n)) (hr : ∀ n → f n <ᴵ f (suc n)) i →
           rkT (ll {s = s} hf hr) (low (blk i end)) ≡ f (i + 0)
rk-chain hf hr zero = refl
rk-chain hf hr (suc i) = refl
```
