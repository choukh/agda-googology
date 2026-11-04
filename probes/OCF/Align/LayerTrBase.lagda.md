# 差树按层互译 (一): 第 1 层的布劳威尔树

> 不含记号. 入口 [LayerTr](LayerTr.lagda.md). 第 1 层 (数类 $\Omega_1$ 到 $\Omega_2$ 之间) 的布劳威尔树 `B₁ W`, 它的第一位置 `_⊲⟨_⟩_`, 合法性 `LgB`, 值前序 `_≼_`.
>
> - `bi f`: $\Omega_1$-分支极限, 分支对**合法的第 0 层布劳威尔树** $y$ (`A`, 带 `Lg y`) 给出, 而且在更大的世界上才有 (同差树的 `ni`).
> - `bκ g`: 按世界分支的极限, 分支对世界之上的合法层 $c$ 给出 (同差树的 `nκ`).
> - `bw`: 世界的懒抬升 (同 `nw`), 在第一位置和值里都透明.
>
> 合法性是结构的, 只要字面的第一位置: $\mathbb N$-极限相邻项; $\Omega_1$-分支沿后继坐标 ($y$ 到 $y+1$); 世界分支沿后继世界 ($c$ 到 $c+1$); 都遗传. **不要求**分支在极限坐标或极限世界上连续, 也不要求分支对值单调. 标记 `Fl`: `no` 的第一位置不进世界分支 (`inκ` 只在 `yes` 里有), 读回差 (`LayerTrOne.dif₁`) 只在 `no` 上有定义.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LayerTrBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤)
```

## §1 树

```agda
data B₁ : A → Set where
  bz : ∀ {W} → B₁ W
  bs : ∀ {W} → B₁ W → B₁ W
  bl : ∀ {W} → (ℕ → B₁ W) → B₁ W
  bi : ∀ {W} → (∀ {W′} → W ⊲ W′ → Lg W′ → (y : A) → Lg y → B₁ W′) → B₁ W
  bκ : ∀ {W} → (∀ {c} → W ⊲ c → Lg c → B₁ c) → B₁ W
  bw : ∀ {W₀ W} → W₀ ⊲ W → B₁ W₀ → B₁ W

-- 第 0 层的树嵌进来
emb : ∀ {W} → A → B₁ W
emb azero = bz
emb (asuc a) = bs (emb a)
emb (alim f) = bl (λ n → emb (f n))

-- 标准的 Ω₁: 分支就是坐标自己
Ωᴮ : ∀ {W} → B₁ W
Ωᴮ = bi (λ _ _ y _ → emb y)
```

## §2 第一位置与合法性

`a ⊲⟨ fl ⟩ b`: $a$ 字面地是 $b$ 的第一位置. 两边的世界可以不同 (`bw` 透明). 进 `bi` 只经世界自身 (`C.self`) 上坐标 $0$ 的那一支; 进 `bκ` 只经世界自身那一支.

```agda
data Fl : Set where
  yes no : Fl

infix 4 _⊲⟨_⟩_
data _⊲⟨_⟩_ : ∀ {W W′} → B₁ W → Fl → B₁ W′ → Set where
  self : ∀ {W fl} {a : B₁ W} → a ⊲⟨ fl ⟩ a
  suc  : ∀ {W W′ fl} {a : B₁ W′} {b : B₁ W} → a ⊲⟨ fl ⟩ b → a ⊲⟨ fl ⟩ bs b
  lim  : ∀ {W W′ fl} {a : B₁ W′} {f : ℕ → B₁ W} n → a ⊲⟨ fl ⟩ f n → a ⊲⟨ fl ⟩ bl f
  wR   : ∀ {W₀ W W′ fl} {a : B₁ W′} {p : W₀ ⊲ W} {b : B₁ W₀} → a ⊲⟨ fl ⟩ b → a ⊲⟨ fl ⟩ bw p b
  wL   : ∀ {W₀ W W′ fl} {p : W₀ ⊲ W} {a : B₁ W₀} {b : B₁ W′} → a ⊲⟨ fl ⟩ b → bw p a ⊲⟨ fl ⟩ b
  ini  : ∀ {W W′ fl} {a : B₁ W′} {f : ∀ {W′} → W ⊲ W′ → Lg W′ → (y : A) → Lg y → B₁ W′} (l : Lg W) →
         a ⊲⟨ fl ⟩ f C.self l azero tt → a ⊲⟨ fl ⟩ bi f
  inκ  : ∀ {W W′} {a : B₁ W′} {g : ∀ {c} → W ⊲ c → Lg c → B₁ c} (l : Lg W) →
         a ⊲⟨ yes ⟩ g C.self l → a ⊲⟨ yes ⟩ bκ g

⊲ᴮ-tr : ∀ {W₁ W₂ W₃ fl} {a : B₁ W₁} {b : B₁ W₂} {c : B₁ W₃} → a ⊲⟨ fl ⟩ b → b ⊲⟨ fl ⟩ c → a ⊲⟨ fl ⟩ c
trL   : ∀ {W₀ W₁ W₂ W₃ fl} {r : W₀ ⊲ W₂} {a : B₁ W₁} {b : B₁ W₀} {c : B₁ W₃} → a ⊲⟨ fl ⟩ bw r b → b ⊲⟨ fl ⟩ c → a ⊲⟨ fl ⟩ c
⊲ᴮ-tr p self = p
⊲ᴮ-tr p (suc q) = suc (⊲ᴮ-tr p q)
⊲ᴮ-tr p (lim n q) = lim n (⊲ᴮ-tr p q)
⊲ᴮ-tr p (wR q) = wR (⊲ᴮ-tr p q)
⊲ᴮ-tr p (wL q) = trL p q
⊲ᴮ-tr p (ini l q) = ini l (⊲ᴮ-tr p q)
⊲ᴮ-tr p (inκ l q) = inκ l (⊲ᴮ-tr p q)
trL self q = wL q
trL (wR p) q = ⊲ᴮ-tr p q
trL (wL p) q = wL (trL p q)
```

**合法性.** 后继坐标: $y$ 的后继是 `asuc y` (`Lg (asuc y)` 就是 `Lg y`). 后继世界: 路径 `C.suc p`.

```agda
LgB : ∀ {W} → Fl → B₁ W → Set
LgB fl bz = ⊤
LgB fl (bs b) = LgB fl b
LgB fl (bl f) = (∀ n → f n ⊲⟨ fl ⟩ f (suc n)) × (∀ n → LgB fl (f n))
LgB fl (bi f) = ∀ {W′} p l y ly → LgB fl (f {W′} p l y ly) × (f p l y ly ⊲⟨ fl ⟩ f p l (asuc y) ly)
LgB fl (bκ g) = ∀ {c} p l → LgB fl (g {c} p l) × (g p l ⊲⟨ fl ⟩ g (C.suc p) l)
LgB fl (bw p b) = LgB fl b
```

## §3 值前序

与 [Value](Value.lagda.md) 的 $\preccurlyeq$ 同形 (`src/WellFormed/CrossTree` 的四条加分支极限各两条, 抬升透明). 两个分支极限的值都是分支的上确界, 分支取遍一切更大的世界与一切合法坐标 (或合法层). 这里不导入 `Value` (它的导入闭包含记号).

```agda
infix 4 _≼_ _≈_
data _≼_ : ∀ {W W′} → B₁ W → B₁ W′ → Set where
  z≼  : ∀ {W W′} {b : B₁ W′} → bz {W} ≼ b
  s≼s : ∀ {W W′} {a : B₁ W} {b : B₁ W′} → a ≼ b → bs a ≼ bs b
  ≼l  : ∀ {W W′} {a : B₁ W} {f : ℕ → B₁ W′} n → a ≼ f n → a ≼ bl f
  l≼  : ∀ {W W′} {f : ℕ → B₁ W} {b : B₁ W′} → (∀ n → f n ≼ b) → bl f ≼ b
  ≼i  : ∀ {W W′ W″} {a : B₁ W} {f : ∀ {W′} → W″ ⊲ W′ → Lg W′ → (y : A) → Lg y → B₁ W′} (p : W″ ⊲ W′) l y ly →
        a ≼ f p l y ly → a ≼ bi f
  i≼  : ∀ {W W′} {f : ∀ {W′} → W ⊲ W′ → Lg W′ → (y : A) → Lg y → B₁ W′} {b : B₁ W′} →
        (∀ {W″} p l y ly → f {W″} p l y ly ≼ b) → bi f ≼ b
  ≼κ  : ∀ {W W′ c} {a : B₁ W} {g : ∀ {c} → W′ ⊲ c → Lg c → B₁ c} (p : W′ ⊲ c) l → a ≼ g p l → a ≼ bκ g
  κ≼  : ∀ {W W′} {g : ∀ {c} → W ⊲ c → Lg c → B₁ c} {b : B₁ W′} → (∀ {c} p l → g {c} p l ≼ b) → bκ g ≼ b
  ≼w  : ∀ {W₀ W W′} {a : B₁ W′} {p : W₀ ⊲ W} {b : B₁ W₀} → a ≼ b → a ≼ bw p b
  w≼  : ∀ {W₀ W W′} {p : W₀ ⊲ W} {a : B₁ W₀} {b : B₁ W′} → a ≼ b → bw p a ≼ b

≼-refl : ∀ {W} (a : B₁ W) → a ≼ a
≼-refl bz = z≼
≼-refl (bs a) = s≼s (≼-refl a)
≼-refl (bl f) = l≼ (λ n → ≼l n (≼-refl (f n)))
≼-refl (bi f) = i≼ (λ p l y ly → ≼i p l y ly (≼-refl (f p l y ly)))
≼-refl (bκ g) = κ≼ (λ p l → ≼κ p l (≼-refl (g p l)))
≼-refl (bw p a) = w≼ (≼w (≼-refl a))

≼-trans : ∀ {W₁ W₂ W₃} {a : B₁ W₁} {b : B₁ W₂} {c : B₁ W₃} → a ≼ b → b ≼ c → a ≼ c
≼-trans z≼ q = z≼
≼-trans p (≼l n q) = ≼l n (≼-trans p q)
≼-trans p (≼i r l y ly q) = ≼i r l y ly (≼-trans p q)
≼-trans p (≼κ r l q) = ≼κ r l (≼-trans p q)
≼-trans p (≼w q) = ≼w (≼-trans p q)
≼-trans (l≼ p) q = l≼ (λ n → ≼-trans (p n) q)
≼-trans (i≼ p) q = i≼ (λ r l y ly → ≼-trans (p r l y ly) q)
≼-trans (κ≼ p) q = κ≼ (λ r l → ≼-trans (p r l) q)
≼-trans (w≼ p) q = w≼ (≼-trans p q)
≼-trans (s≼s p) (s≼s q) = s≼s (≼-trans p q)
≼-trans (≼l n p) (l≼ q) = ≼-trans p (q n)
≼-trans (≼i r l y ly p) (i≼ q) = ≼-trans p (q r l y ly)
≼-trans (≼κ r l p) (κ≼ q) = ≼-trans p (q r l)
≼-trans (≼w p) (w≼ q) = ≼-trans p q

_≈_ : ∀ {W W′} → B₁ W → B₁ W′ → Set
a ≈ b = a ≼ b × b ≼ a

≈-trans : ∀ {W₁ W₂ W₃} {a : B₁ W₁} {b : B₁ W₂} {c : B₁ W₃} → a ≈ b → b ≈ c → a ≈ c
≈-trans (p , q) (p′ , q′) = ≼-trans p p′ , ≼-trans q′ q

emb-mono : ∀ {W W′ a b} → a ≤ b → emb {W} a ≼ emb {W′} b
emb-mono z≤ = z≼
emb-mono (s≤ p) = s≼s (emb-mono p)
emb-mono (≤l n p) = ≼l n (emb-mono p)
emb-mono (l≤ p) = l≼ (λ n → emb-mono (p n))
```

## §4 值为零的树

`Zv b`: $b$ 里没有后继. 这样的树不 $\succcurlyeq 1$ (`no-suc`). 反例要用.

```agda
Zv : ∀ {W} → B₁ W → Set
Zv bz = ⊤
Zv (bs b) = ⊥
Zv (bl f) = ∀ n → Zv (f n)
Zv (bi f) = ∀ {W′} p l y ly → Zv (f {W′} p l y ly)
Zv (bκ g) = ∀ {c} p l → Zv (g {c} p l)
Zv (bw p b) = Zv b

no-suc : ∀ {W W′} {a : B₁ W} {b : B₁ W′} → Zv b → ¬ (bs a ≼ b)
no-suc () (s≼s h)
no-suc z (≼l n h) = no-suc (z n) h
no-suc z (≼i p l y ly h) = no-suc (z p l y ly) h
no-suc z (≼κ p l h) = no-suc (z p l) h
no-suc z (≼w h) = no-suc z h
```
