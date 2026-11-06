# 高度是树 (六): 哪些高度的形状不行

> 不含记号. 入口 [HtFeed](HtFeed.lagda.md). 四条编译过的定理, 划出 [HtFeedTree](HtFeedTree.lagda.md) 的 `H` 里哪些字段是比较逼出来的. 前提都可满足 (定理里给了见证).
>
> 1. `top-Ω`, **`no-world-top`**: $\Omega$ (`Ωᴴ = hΩ emb`) 在一切可数高度之上, 但只是每个高度在自己的世界里在它之下; **没有一个世界让一切可数高度都在 $\Omega$ 之下.** 这是 `HtGen.no-top` 的对偶: `A` 里没有顶, `H` 里有顶, 代价是顶的第一位置按世界分开. 与壁垒的关系: 在任何一个固定的世界里, $\Omega$ 的第一位置都是可数有界的 (`world-bound`), 所以壁垒要的 "$\Omega$-共尾元 + 有界三歧" 在一个世界里不会同时出现.
> 2. **`no-glob`**: 若 $\Omega$-分支的第一位置不要求在同一个世界里, 比较就不可能: 两个在不同世界里的第一位置 (`emb ω`, `emb ω′`) 既不是互相的第一位置, 也没有字面公共上界 (`no-common`). 否定的是: "两个第一位置, 世界各自取, 可比".
> 3. **`no-weak`**: `LgH` 的 $\Omega$-单调 (沿坐标的一切第一位置) 不能减弱成只在后继坐标处步进 (`LgW`, 即 `LayerTr` 的 `LgB` 对 `bi` 的要求): 有一棵弱合法的高度, 在世界 $\omega$ 里有两个不可比的第一位置.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtFeedNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲; cmpF)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤; ≤-suc)
open import OCF.Align.HtGenGen using (lt-irr)
open import OCF.Align.HtFeedTree using (H; hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; LgH)
open import OCF.Align.HtFeedHt using (emb; Ωᴴ; Lg-Ωᴴ; below-Ω)
```

## §1 $\Omega$ 是顶, 但不在任何一个世界里

```agda
top-Ω : ∀ x → emb x ⊲[ x ] Ωᴴ
top-Ω x = below-Ω x C.self

rk : H → A
rk hz = azero
rk (hs h) = asuc (rk h)
rk (hl f) = alim (λ n → rk (f n))
rk (hΩ g) = azero

rk-emb≥ : ∀ a → a ≤ rk (emb a)
rk-emb≥ azero = z≤
rk-emb≥ (asuc a) = s≤ (rk-emb≥ a)
rk-emb≥ (alim f) = l≤ (λ n → ≤l n (rk-emb≥ (f n)))

rk-emb≤ : ∀ a → rk (emb a) ≤ a
rk-emb≤ azero = z≤
rk-emb≤ (asuc a) = s≤ (rk-emb≤ a)
rk-emb≤ (alim f) = l≤ (λ n → ≤l n (rk-emb≤ (f n)))

rk⊲ : ∀ {W h} c → h ⊲[ W ] emb c → rk h ≤ c
rk⊲ azero hself = z≤
rk⊲ (asuc c) hself = s≤ (rk-emb≤ c)
rk⊲ (asuc c) (hsuc p) = ≤-suc (rk⊲ c p)
rk⊲ (alim f) hself = rk-emb≤ (alim f)
rk⊲ (alim f) (hlim n p) = ≤l n (rk⊲ (f n) p)

Ω-pos : ∀ {W h} → h ⊲[ W ] Ωᴴ → (h ≡ Ωᴴ) ⊎ (Σ A λ c → (c ⊲ W) × (h ⊲[ W ] emb c))
Ω-pos hself = inj₁ refl
Ω-pos (hLim e p) = inj₂ (_ , e , p)

emb≢Ω : ∀ a → emb a ≡ Ωᴴ → ⊥
emb≢Ω azero ()
emb≢Ω (asuc a) ()
emb≢Ω (alim f) ()

-- 在世界 W 里, Ω 之下的可数高度都不超过 W
world-bound : ∀ {W} a → emb a ⊲[ W ] Ωᴴ → a ≤ W
world-bound a p with Ω-pos p
... | inj₁ eq = ⊥-elim (emb≢Ω a eq)
... | inj₂ (c , e , q) = ≤-trans (rk-emb≥ a) (≤-trans (rk⊲ c q) (⊲→≤ e))

no-world-top : ∀ W → Lg W → ¬ (∀ x → Lg x → emb x ⊲[ W ] Ωᴴ)
no-world-top W lW h = lt-irr W (world-bound (asuc W) (h (asuc W) lW))
```

## §2 第一位置要在同一个世界里

`ω′` 与 `ω` 同值, 字面不同. 它们各自是 $\Omega$ 的第一位置 (在各自的世界里), 但互相不是第一位置, 也没有合法的字面公共上界.

```agda
natA : ℕ → A
natA zero = azero
natA (suc n) = asuc (natA n)

ω ω′ : A
ω = alim natA
ω′ = alim (λ n → natA (suc n))

FinA : A → Set
FinA azero = ⊤
FinA (asuc a) = FinA a
FinA (alim _) = ⊥

finA⊲ : ∀ {a b} → a ⊲ b → FinA b → FinA a
finA⊲ C.self f = f
finA⊲ (C.suc p) f = finA⊲ p f
finA⊲ (C.lim n p) ()

finN : ∀ n → FinA (natA n)
finN zero = tt
finN (suc n) = finN n

hd0 : A → A
hd0 (alim f) = f 0
hd0 a = a

ω′≢ω : ω′ ≡ ω → ⊥
ω′≢ω e with cong hd0 e
... | ()

noP : ∀ {a b} → a ⊲ b → a ≡ ω′ → b ≡ ω → ⊥
noP C.self refl e = ω′≢ω e
noP (C.suc p) e₁ ()
noP (C.lim n p) refl refl = finA⊲ p (finN n)

noP′ : ∀ {a b} → a ⊲ b → a ≡ ω → b ≡ ω′ → ⊥
noP′ C.self refl e = ω′≢ω (sym e)
noP′ (C.suc p) e₁ ()
noP′ (C.lim n p) refl refl = finA⊲ p (finN (suc n))

-- 没有合法的世界同时含 ω 与 ω′
no-common : ∀ {W} → Lg W → ω ⊲ W → ω′ ⊲ W → ⊥
no-common lW p q with cmpF p q lW
... | inj₁ ω′⊲ω = noP ω′⊲ω refl refl
... | inj₂ ω⊲ω′ = noP′ ω⊲ω′ refl refl
```

同样的事在高度里.

```agda
FinH : H → Set
FinH hz = ⊤
FinH (hs h) = FinH h
FinH (hl _) = ⊥
FinH (hΩ _) = ⊥

finH⊲ : ∀ {W h k} → h ⊲[ W ] k → FinH k → FinH h
finH⊲ hself f = f
finH⊲ (hsuc p) f = finH⊲ p f
finH⊲ (hlim n p) ()
finH⊲ (hLim e p) ()

finE : ∀ {a} → FinA a → FinH (emb a)
finE {a = azero} f = tt
finE {a = asuc a} f = finE {a = a} f
finE {a = alim _} ()

hd0H : H → H
hd0H (hl f) = f 0
hd0H h = h

eω′≢eω : emb ω′ ≡ emb ω → ⊥
eω′≢eω e with cong hd0H e
... | ()

noPH : ∀ {V h k} → h ⊲[ V ] k → h ≡ emb ω′ → k ≡ emb ω → ⊥
noPH hself refl e = eω′≢eω e
noPH (hsuc p) e₁ ()
noPH (hlim n p) refl refl = finH⊲ p (finE (finN n))
noPH (hLim e p) e₁ ()

noPH′ : ∀ {V h k} → h ⊲[ V ] k → h ≡ emb ω → k ≡ emb ω′ → ⊥
noPH′ hself refl e = eω′≢eω (sym e)
noPH′ (hsuc p) e₁ ()
noPH′ (hlim n p) refl refl = finH⊲ p (finE (finN (suc n)))
noPH′ (hLim e p) e₁ ()

-- 世界各自取的第一位置可比: 不可能
GlobCmp : Set
GlobCmp = ∀ {a b L W W′} → a ⊲[ W ] L → b ⊲[ W′ ] L → LgH L → (Σ A λ V → b ⊲[ V ] a) ⊎ (Σ A λ V → a ⊲[ V ] b)

no-glob : ¬ GlobCmp
no-glob cmp with cmp (below-Ω ω C.self) (below-Ω ω′ C.self) Lg-Ωᴴ
... | inj₁ (V , p) = noPH p refl refl
... | inj₂ (V , p) = noPH′ p refl refl
```

## §3 $\Omega$-单调不能只在后继坐标处

```agda
LgW : H → Set
LgW hz = ⊤
LgW (hs h) = LgW h
LgW (hl f) = (∀ n → f n ⊲[ azero ] f (suc n)) × (∀ n → LgW (f n))
LgW (hΩ g) = (∀ c → Lg c → g c ⊲[ azero ] g (asuc c)) × (∀ c → Lg c → LgW (g c))

emb⊲₀ : ∀ {a b} → a ⊲ b → emb a ⊲[ azero ] emb b
emb⊲₀ C.self = hself
emb⊲₀ (C.suc p) = hsuc (emb⊲₀ p)
emb⊲₀ (C.lim n p) = hlim n (emb⊲₀ p)

LgW-emb : ∀ a → Lg a → LgW (emb a)
LgW-emb azero _ = tt
LgW-emb (asuc a) l = LgW-emb a l
LgW-emb (alim f) (st , l) = (λ n → emb⊲₀ (st n)) , (λ n → LgW-emb (f n) (l n))

-- 反例: 0 支是 Ω, 后继支往上一格, 极限支一律是 ω′
gx : A → H
gx azero = Ωᴴ
gx (asuc c) = hs (gx c)
gx (alim f) = emb ω′

lω′ : Lg ω′
lω′ = (λ n → C.suc C.self) , (λ n → lgN (suc n))
  where
  lgN : ∀ n → Lg (natA n)
  lgN zero = tt
  lgN (suc n) = lgN n

lgW-gx : ∀ c → Lg c → LgW (gx c)
lgW-gx azero _ = (λ c _ → hsuc hself) , LgW-emb
lgW-gx (asuc c) l = lgW-gx c l
lgW-gx (alim f) _ = LgW-emb ω′ lω′

lgW-x : LgW (hΩ gx)
lgW-x = (λ c _ → hsuc hself) , lgW-gx

lω : Lg ω
lω = (λ n → C.suc C.self) , lgN
  where
  lgN : ∀ n → Lg (natA n)
  lgN zero = tt
  lgN (suc n) = lgN n

WeakCmp : Set
WeakCmp = ∀ {a b L W} → a ⊲[ W ] L → b ⊲[ W ] L → Lg W → LgW L → (b ⊲[ W ] a) ⊎ (a ⊲[ W ] b)

-- ω′ 不在世界 ω 里的 Ω 之下
no₁ : emb ω′ ⊲[ ω ] Ωᴴ → ⊥
no₁ p with Ω-pos p
... | inj₁ ()
... | inj₂ (c , C.self , q) = noPH q refl refl
... | inj₂ (c , C.lim n e , q) = finH⊲ q (finE (finA⊲ e (finN n)))

-- Ω 不在 ω′ 之下
no₂ : Ωᴴ ⊲[ ω ] emb ω′ → ⊥
no₂ p = go p refl refl
  where
  go : ∀ {V h k} → h ⊲[ V ] k → h ≡ Ωᴴ → k ≡ emb ω′ → ⊥
  go hself refl ()
  go (hsuc p) e ()
  go (hlim n p) refl refl = finH⊲ p (finE (finN (suc n)))
  go (hLim e p) e₁ ()

no-weak : ¬ WeakCmp
no-weak cmp with cmp {L = hΩ gx} (hLim {c = azero} (z⊲ ω) hself) (hLim {c = ω} C.self hself) lω lgW-x
... | inj₁ p = no₁ p
... | inj₂ p = no₂ p
```
