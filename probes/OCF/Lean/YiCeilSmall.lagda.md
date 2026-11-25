# 上界工具 (三): 线性类的值不超过 Ω₁·d (d 可数)

> 诊断：上界. 不进成品. 档: 编译定理, 无前提. 第 1 层的树读成以 ℕ 与第 0 层的树为分支的布劳威尔树 `W` (`rd`; `up x tt y` 读成 x 的读回加 y, 与块自己的读回 `↑` 同一约定), 值前序 `≤ʷ` 与 `OCF.Align.Value` 的同形.
> `lin-small`: `Lin` 里的树, 读回不超过 `mulΩ d` (读作 Ω₁·d), d 是参照框架第 0 层的树. `feed-small`: 见证树 N₂ 的回灌 `Gw (br₂ z)` 对一切 z 如此; `chain-small`: 链 `e₂` 的每一项如此. `feed-below-sq`: `sq` (读作 Ω₁²) 不低于等于任何一个回灌值.
> 不给出什么: 没有 `read (ψ₀ … N₂)` 的上界, 没有与记号参照的比较; "记号在这里回灌的 ψ₁(Ω_Ω·…) 高于 Ω₁·d" 是判断. `W` 只在本文件里用.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCeilSmall where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLSRead using (T₀; read; limcum≽)
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import OCF.Lean.YiDecWit using (br₂; Gw; e₂)
open import OCF.Lean.YiLSTw1 using (h₁)
open import OCF.Lean.YiT2Frame using (β)
open import OCF.Lean.YiDecWit using (nb)
open import OCF.Lean.YiCeilWit using (Lin; l0; lx; ll; l+; ext; feed-Lin; chain-Lin; self-Lin)
import OCF.Align.Level as L
```

## 第 1 层的值

```agda
data W : Set where
  wz : W
  ws : W → W
  wl : (ℕ → W) → W
  wo : (Tr zero → W) → W

infixl 6 _⊞_
_⊞_ : W → W → W
a ⊞ wz   = a
a ⊞ ws b = ws (a ⊞ b)
a ⊞ wl f = wl (λ n → a ⊞ f n)
a ⊞ wo g = wo (λ c → a ⊞ g c)

infix 4 _≤ʷ_
data _≤ʷ_ : W → W → Set where
  z≤ : ∀ {b} → wz ≤ʷ b
  s≤ : ∀ {a b} → a ≤ʷ b → ws a ≤ʷ ws b
  ≤l : ∀ {a f} (n : ℕ) → a ≤ʷ f n → a ≤ʷ wl f
  l≤ : ∀ {f b} → ((n : ℕ) → f n ≤ʷ b) → wl f ≤ʷ b
  ≤o : ∀ {a g} (c : Tr zero) → a ≤ʷ g c → a ≤ʷ wo g
  o≤ : ∀ {g b} → ((c : Tr zero) → g c ≤ʷ b) → wo g ≤ʷ b

≤-refl : (a : W) → a ≤ʷ a
≤-refl wz     = z≤
≤-refl (ws a) = s≤ (≤-refl a)
≤-refl (wl f) = l≤ (λ n → ≤l n (≤-refl (f n)))
≤-refl (wo g) = o≤ (λ c → ≤o c (≤-refl (g c)))

≤-trans : ∀ {a b c} → a ≤ʷ b → b ≤ʷ c → a ≤ʷ c
≤-trans z≤       q        = z≤
≤-trans p        (≤l n q) = ≤l n (≤-trans p q)
≤-trans p        (≤o c q) = ≤o c (≤-trans p q)
≤-trans (l≤ p)   q        = l≤ (λ n → ≤-trans (p n) q)
≤-trans (o≤ p)   q        = o≤ (λ c → ≤-trans (p c) q)
≤-trans (s≤ p)   (s≤ q)   = s≤ (≤-trans p q)
≤-trans (≤l n p) (l≤ q)   = ≤-trans p (q n)
≤-trans (≤o c p) (o≤ q)   = ≤-trans p (q c)

≤s : ∀ {a b} → a ≤ʷ b → a ≤ʷ ws b
≤s z≤               = z≤
≤s (s≤ p)           = s≤ (≤s p)
≤s (≤l {f = f} n p) = ≤-trans (≤s p) (s≤ (≤l n (≤-refl (f n))))
≤s (l≤ p)           = l≤ (λ n → ≤s (p n))
≤s (≤o {g = g} c p) = ≤-trans (≤s p) (s≤ (≤o c (≤-refl (g c))))
≤s (o≤ p)           = o≤ (λ c → ≤s (p c))

⊞-incr : (a b : W) → a ≤ʷ a ⊞ b
⊞-incr a wz     = ≤-refl a
⊞-incr a (ws b) = ≤s (⊞-incr a b)
⊞-incr a (wl f) = ≤l zero (⊞-incr a (f zero))
⊞-incr a (wo g) = ≤o zero (⊞-incr a (g zero))

⊞-mono : ∀ {a a′ b b′} → a ≤ʷ a′ → b ≤ʷ b′ → a ⊞ b ≤ʷ a′ ⊞ b′
⊞-mono {a′ = a′} {b′ = b′} p z≤ = ≤-trans p (⊞-incr a′ b′)
⊞-mono p (s≤ q)   = s≤ (⊞-mono p q)
⊞-mono p (≤l n q) = ≤l n (⊞-mono p q)
⊞-mono p (l≤ q)   = l≤ (λ n → ⊞-mono p (q n))
⊞-mono p (≤o c q) = ≤o c (⊞-mono p q)
⊞-mono p (o≤ q)   = o≤ (λ c → ⊞-mono p (q c))

assoc≤ : (a b c : W) → (a ⊞ b) ⊞ c ≤ʷ a ⊞ (b ⊞ c)
assoc≤ a b wz     = ≤-refl (a ⊞ b)
assoc≤ a b (ws c) = s≤ (assoc≤ a b c)
assoc≤ a b (wl f) = l≤ (λ n → ≤l n (assoc≤ a b (f n)))
assoc≤ a b (wo g) = o≤ (λ c → ≤o c (assoc≤ a b (g c)))

assoc≥ : (a b c : W) → a ⊞ (b ⊞ c) ≤ʷ (a ⊞ b) ⊞ c
assoc≥ a b wz     = ≤-refl (a ⊞ b)
assoc≥ a b (ws c) = s≤ (assoc≥ a b c)
assoc≥ a b (wl f) = l≤ (λ n → ≤l n (assoc≥ a b (f n)))
assoc≥ a b (wo g) = o≤ (λ c → ≤o c (assoc≥ a b (g c)))
```

## 读回

第 1 层只有一个槽位 (分支是第 0 层的树) 与一种嵌入 (孩子是第 0 层的树).

```agda
emb : Tr zero → W
emb zero          = wz
emb (suc x)       = ws (emb x)
emb (lim f _)     = wl (λ n → emb (f n))
emb (Ω () _)
emb (up _ () _ _)

rd : Tr (suc zero) → W
rd zero             = wz
rd (suc x)          = ws (rd x)
rd (lim f _)        = wl (λ n → rd (f n))
rd (Ω (inj₁ tt) g)  = wo (λ c → rd (g c))
rd (Ω (inj₂ ()) g)
rd (up x tt y _)    = rd x ⊞ emb y

rd-ι : (x : Tr (suc zero)) (w : Tr zero) → rd (x + ι (suc zero) w) ≤ʷ rd x ⊞ emb w
rd-ι x zero          = ≤-refl (rd x)
rd-ι x (suc w)       = s≤ (rd-ι x w)
rd-ι x (lim f _)     = l≤ (λ n → ≤l n (rd-ι x (f n)))
rd-ι x (Ω () _)
rd-ι x (up _ () _ _)

rd-+ : (x y : Tr (suc zero)) → rd (x + y) ≤ʷ rd x ⊞ rd y
rd-+ x zero            = ≤-refl (rd x)
rd-+ x (suc y)         = s≤ (rd-+ x y)
rd-+ x (lim f _)       = l≤ (λ n → ≤l n (rd-+ x (f n)))
rd-+ x (Ω (inj₁ tt) g) = o≤ (λ c → ≤o c (rd-+ x (g c)))
rd-+ x (Ω (inj₂ ()) g)
rd-+ x (up y tt w _)   =
  ≤-trans (⊞-mono (rd-+ x y) (≤-refl (emb w))) (assoc≤ (rd x) (rd y) (emb w))
```

## Ω₁ 的可数倍

```agda
Ω₁ʷ : W
Ω₁ʷ = wo emb

mulΩ : T₀ → W
mulΩ L.zero        = wz
mulΩ (L.suc d)     = mulΩ d ⊞ Ω₁ʷ
mulΩ (L.lim f)     = wl (λ n → mulΩ (f n))
mulΩ (L.limᵢ () f)
mulΩ (L.up () x)

mulΩ-+ : (d₁ d₂ : T₀) → mulΩ d₁ ⊞ mulΩ d₂ ≤ʷ mulΩ (d₁ L.+ d₂)
mulΩ-+ d₁ L.zero        = ≤-refl (mulΩ d₁)
mulΩ-+ d₁ (L.suc d)     =
  ≤-trans (assoc≥ (mulΩ d₁) (mulΩ d) Ω₁ʷ) (⊞-mono (mulΩ-+ d₁ d) (≤-refl Ω₁ʷ))
mulΩ-+ d₁ (L.lim f)     = l≤ (λ n → ≤l n (mulΩ-+ d₁ (f n)))
mulΩ-+ d₁ (L.limᵢ () f)
mulΩ-+ d₁ (L.up () x)

Ωt1≤ : rd (Ωt (suc zero)) ≤ʷ mulΩ (L.suc L.zero)
Ωt1≤ = o≤ (λ c → ≤o (suc c) (≤-refl (ws (wz ⊞ emb c))))

ext≤ : (x : Tr (suc zero)) (y : Tr zero → Tr zero) → rd (ext x y) ≤ʷ rd x ⊞ Ω₁ʷ
ext≤ x y = o≤ (λ c → ≤-trans (rd-ι x (y c)) (≤o (y c) (≤-refl (rd x ⊞ emb (y c)))))
```

## 线性类的上界

对 `Lin` 的推导归纳: 起点 1 倍; 接一个结点多 1 倍; ℕ 极限取倍数的极限; 加法取倍数的和.

```agda
lin-small : {x : Tr (suc zero)} → Lin x → Σ T₀ λ d → rd x ≤ʷ mulΩ d
lin-small l0 = L.suc L.zero , Ωt1≤
lin-small (lx {x} s y) with lin-small s
... | d , q = L.suc d , ≤-trans (ext≤ x y) (⊞-mono q (≤-refl Ω₁ʷ))
lin-small (ll h) = L.lim (λ n → proj₁ (lin-small (h n))) , l≤ (λ n → ≤l n (proj₂ (lin-small (h n))))
lin-small (l+ {x} {y} s₁ s₂) with lin-small s₁ | lin-small s₂
... | d₁ , q₁ | d₂ , q₂ = d₁ L.+ d₂ , ≤-trans (rd-+ x y) (≤-trans (⊞-mono q₁ q₂) (mulΩ-+ d₁ d₂))

feed-small : (z : Tr (suc zero)) → Σ T₀ λ d → rd (Gw (br₂ z)) ≤ʷ mulΩ d
feed-small z = lin-small (feed-Lin z)

chain-small : (n : ℕ) → Σ T₀ λ d → rd (e₂ (suc n)) ≤ʷ mulΩ d
chain-small n = lin-small (chain-Lin n)

self-small : (c : Tr zero) (y : Tr (h₁ c)) → Σ T₀ λ d → rd (Gw (Upc (tw 1) c β nb y)) ≤ʷ mulΩ d
self-small c y = lin-small (self-Lin c y)
```

## 严格低于 Ω₁²

`sq` 是 Ω₁ 的各个可数倍的上确界 (分支取第 0 层的合法树). 它不低于等于任何 `mulΩ d`: 取一棵读回不低于 d+1 的合法树 (`dom`), 得到 `mulΩ d` 加 1 不高于 `mulΩ d`, 与 `irr` 矛盾.

```agda
sq : W
sq = wo (λ c → mulΩ (read c))

irr : (a : W) → ¬ (ws a ≤ʷ a)
irr wz     ()
irr (ws a) (s≤ p)   = irr a p
irr (wl f) (≤l n p) = irr (f n) (≤-trans (s≤ (≤l n (≤-refl (f n)))) p)
irr (wo g) (≤o c p) = irr (g c) (≤-trans (s≤ (≤o c (≤-refl (g c)))) p)

mulΩ-mono : {d d′ : T₀} → d ≼ d′ → mulΩ d ≤ʷ mulΩ d′
mulΩ-mono z≼       = z≤
mulΩ-mono (s≼s e)  = ⊞-mono (mulΩ-mono e) (≤-refl Ω₁ʷ)
mulΩ-mono (≼l n e) = ≤l n (mulΩ-mono e)
mulΩ-mono (l≼ h)   = l≤ (λ n → mulΩ-mono (h n))
mulΩ-mono (≼i {p = ()} x ex e)
mulΩ-mono (i≼ {p = ()} h)
mulΩ-mono (≼u {r = ()} e)
mulΩ-mono (u≼ {r = ()} e)

mutual
  dom : T₀ → Tr zero
  dom L.zero        = suc zero
  dom (L.suc d)     = suc (dom d)
  dom (L.lim f)     = limc (λ n → dom (f n)) (λ n → dom-nz (f n))
  dom (L.limᵢ () f)
  dom (L.up () x)

  dom-nz : (d : T₀) → zero ⊢ zero ◃ dom d
  dom-nz L.zero        = ◃s
  dom-nz (L.suc d)     = z◃s (dom d)
  dom-nz (L.lim f)     = ◃t (dom-nz (f zero)) (◃l zero)
  dom-nz (L.limᵢ () f)
  dom-nz (L.up () x)

dom≽ : (d : T₀) → d ≼ read (dom d)
dom≽ L.zero        = z≼
dom≽ (L.suc d)     = s≼s (dom≽ d)
dom≽ (L.lim f)     = l≼ (λ n → limcum≽ (λ m → dom (f m)) (λ m → dom-nz (f m)) n (dom≽ (f n)))
dom≽ (L.limᵢ () f)
dom≽ (L.up () x)

not-sq : (d : T₀) → ¬ (sq ≤ʷ mulΩ d)
not-sq d p = irr (mulΩ d)
  (≤-trans (⊞-mono (≤-refl (mulΩ d)) (≤o (suc zero) (s≤ z≤)))
  (≤-trans (⊞-mono (mulΩ-mono (dom≽ d)) (≤-refl Ω₁ʷ))
  (≤-trans (≤o (suc (dom d)) (≤-refl (mulΩ (read (dom d)) ⊞ Ω₁ʷ))) p)))

feed-below-sq : (z : Tr (suc zero)) → ¬ (sq ≤ʷ rd (Gw (br₂ z)))
feed-below-sq z p with feed-small z
... | d , q = not-sq d (≤-trans p q)

self-below-sq : (c : Tr zero) (y : Tr (h₁ c)) → ¬ (sq ≤ʷ rd (Gw (Upc (tw 1) c β nb y)))
self-below-sq c y p with self-small c y
... | d , q = not-sq d (≤-trans p q)
```
