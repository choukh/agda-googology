# 值判据 (十一): 基本列的条件 `Reg⁰` 与大数

> 底座. 结论写在 [ValueJudge](ValueJudge.lagda.md). 只导入 `OCF.Free.Level`, [TreeJudgeBase](TreeJudgeBase.lagda.md) §6, [ValueJudgeBase](ValueJudgeBase.lagda.md). 值判据不决定 FGH (`spec-blind`, `slow`). 这里配上 `Reg⁰`:
>
> - **能排除的:** `slow` (`slow-not-reg`). 一般地: `Reg⁰` 的树在 $k\ge2$ 处 FGH 至少 $2k$ (`reg-floor`), 而 `slow` 在 $k$ 处是 $k+1$. `Reg⁰` 下 FGH 沿 1-走步单调 (`walk-mono`), 对参数单调 (`arg-mono`).
> - **排除不了的, 最小反例:** `reg-blind`: 都 `Reg⁰`, 值都是 $\omega$, FGH 在 2 处是 8 与 2048 ($\omega$, $\omega^+$, 就是 `spec-blind` 那一对). `reg-fast`: 任何严格增的 $g$, $\lim_n g(n)$ 都 `Reg⁰`, 值都是 $\omega$, 所以 FGH 没有上界. `reg-gap`: 一棵 `Reg⁰` 的树值是 $\omega\cdot2$, 严格大于 $\omega$, FGH 在 2 处却也是 8.
>
> **判决 (这一半): PARTIAL.** `Reg⁰` 给下界, 排除退化; 值加 `Reg⁰` 不决定 FGH, 连同值的两棵树也差出任意多. 缺的是基本列的**速度**, 而不是形状. 这是编译过的否定, 否定的是 "`Reg⁰` 加值判据决定大数".

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValueJudgeReg where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s; _+_; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤n⇒m≤1+n; <-irrefl; n≤1+n; +-mono-≤; +-identityʳ; +-suc; m≤m+n; ≤⇒≤′; ≤′⇒≤)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Free.Level using (Ordᶜ; zero; suc; lim; limᵢ; up; FGH)
open import OCF.Align.TreeJudgeBase using (Tr; t0; ts; tl; wk⁰; W⁰; w0; ws; wl0; wl; Reg⁰; wk-<; no-self; lim-const)
open import OCF.Align.ValueJudgeBase using (_≼_; _≈ᵛ_; _≺ᵛ_; ≼-refl; ≼-trans; ≼-suc; z≼; s≼s; ≼l; l≼)

toTr : Ordᶜ zero → Tr
toTr zero    = t0
toTr (suc x) = ts (toTr x)
toTr (lim f) = tl (λ n → toTr (f n))
toTr (limᵢ () f)
toTr (up () x)

Reg : Ordᶜ zero → Set
Reg x = Reg⁰ (toTr x)

fg : Tr → ℕ → ℕ
fg t0     n = suc n
fg (ts a) n = iter (fg a) n n
fg (tl f) n = fg (f n) n

-- Tr 上的 FGH 就是原来的 FGH
iter-≡ : ∀ {f g : ℕ → ℕ} → (∀ n → f n ≡ g n) → ∀ s c → iter f s c ≡ iter g s c
iter-≡ h s zero    = refl
iter-≡ {f} {g} h s (suc c) = subst (λ w → f (iter f s c) ≡ g w) (iter-≡ h s c) (h (iter f s c))

fg-FGH : ∀ x n → fg (toTr x) n ≡ FGH x n
fg-FGH zero    n = refl
fg-FGH (suc x) n = iter-≡ (fg-FGH x) n n
fg-FGH (lim f) n = fg-FGH (f n) n
fg-FGH (limᵢ () f) n
fg-FGH (up () x) n
```

## §1 单调

全部要 `Reg⁰`. 参数 $\ge1$: `iter f 0 0 = 0`, FGH 在 0 处不增长.

```agda
infl : ∀ x n → suc n < fg x (suc n)
iter-≥ : ∀ a s c → suc s ≤ iter (fg a) (suc s) c
iter-> : ∀ a s c → suc (suc s) ≤ iter (fg a) (suc s) (suc c)

iter-≥ a s zero    = ≤-refl
iter-≥ a s (suc c) = ≤-trans (n≤1+n _) (iter-> a s c)

iter-> a s c with iter (fg a) (suc s) c | iter-≥ a s c
... | suc y | s≤s le = ≤-trans (s≤s (s≤s le)) (infl a y)

infl t0 n = ≤-refl
infl (ts a) n = iter-> a n n
infl (tl f) n = infl (f (suc n)) n

-- 迭代次数上单调: 每多一次至少不减 (起点 ≥ 1)
iter-step : ∀ a s c → iter (fg a) (suc s) c ≤ iter (fg a) (suc s) (suc c)
iter-step a s c with iter (fg a) (suc s) c | iter-≥ a s c
... | suc y | _ = ≤-trans (n≤1+n _) (infl a y)

iter-c : ∀ a s {c c′} → c ≤′ c′ → iter (fg a) (suc s) c ≤ iter (fg a) (suc s) c′
iter-c a s ≤′-refl = ≤-refl
iter-c a s {c} {suc c′} (≤′-step p) = ≤-trans (iter-c a s p) (iter-step a s c′)

iter-st : ∀ {f : ℕ → ℕ} → (∀ {x y} → x ≤ y → f x ≤ f y) → ∀ {s s′} → s ≤ s′ → ∀ c → iter f s c ≤ iter f s′ c
iter-st h le zero    = le
iter-st h le (suc c) = h (iter-st h le c)

iter-f≥ : ∀ a → (∀ {x y} → x ≤ y → fg a x ≤ fg a y) → ∀ s c → fg a (suc s) ≤ iter (fg a) (suc s) (suc c)
iter-f≥ a am s c = am (iter-≥ a s c)

arg-mono  : ∀ x → Reg⁰ x → ∀ {n m} → n ≤ m → fg x n ≤ fg x m
walk-mono : ∀ x → Reg⁰ x → ∀ {y} → W⁰ y x → ∀ m → fg y (suc m) ≤ fg x (suc m)
chainG    : ∀ h → Reg⁰ (tl h) → ∀ {n k} → n ≤′ k → ∀ m → fg (h n) (suc m) ≤ fg (h k) (suc m)

arg-mono t0 r le = s≤s le
arg-mono (ts a) r {n = zero} {m = zero} le = ≤-refl
arg-mono (ts a) r {n = zero} {m = suc m} le = z≤n
arg-mono (ts a) r {n = suc n} {m = suc m} (s≤s le) =
  ≤-trans (iter-st (arg-mono a r) (s≤s le) (suc n)) (iter-c a m (≤⇒≤′ (s≤s le)))
arg-mono (tl h) r {n = zero} {m = zero} le = ≤-refl
arg-mono (tl h) r {n = zero} {m = suc m} le =
  ≤-trans (arg-mono (h 0) (proj₂ r 0) z≤n) (chainG h r (≤⇒≤′ z≤n) m)
arg-mono (tl h) r {n = suc n} {m = suc m} (s≤s le) =
  ≤-trans (arg-mono (h (suc n)) (proj₂ r (suc n)) (s≤s le)) (chainG h r (≤⇒≤′ (s≤s le)) m)

walk-mono (ts a) r w0 m = iter-f≥ a (arg-mono a r) m m
walk-mono (ts a) r (ws w) m = ≤-trans (walk-mono a r w m) (iter-f≥ a (arg-mono a r) m m)
walk-mono (tl f) r (wl0 refl) m = chainG f r (≤⇒≤′ (s≤s z≤n)) m
walk-mono (tl f) r (wl w) m = ≤-trans (walk-mono (f 1) (proj₂ r 1) w m) (chainG f r (≤⇒≤′ (s≤s z≤n)) m)

chainG h r ≤′-refl m = ≤-refl
chainG h r {k = suc k} (≤′-step p) m = ≤-trans (chainG h r p m) (walk-mono (h (suc k)) (proj₂ r (suc k)) (proj₁ r k) m)
```

## §2 下界

`wk⁰` 是 1-走步的长度. `Reg⁰` 下 $h_k$ 的走步长度 $\ge k$. `fl`: 参数 $\ge2$ 时 FGH $\ge$ 参数加走步长度. 对极限节点要第 1 项之后的增长, 所以要 2.

```agda
wk-chain : ∀ h → Reg⁰ (tl h) → ∀ {n k} → n ≤′ k → wk⁰ (h n) ≤ wk⁰ (h k)
wk-chain h r ≤′-refl = ≤-refl
wk-chain h r {k = suc k} (≤′-step p) = ≤-trans (wk-chain h r p) (m≤n⇒m≤1+n′ (wk-< (proj₁ r k)))
  where
  m≤n⇒m≤1+n′ : ∀ {a b} → a < b → a ≤ b
  m≤n⇒m≤1+n′ (s≤s p₁) = m≤n⇒m≤1+n p₁

wk-nat : ∀ h → Reg⁰ (tl h) → ∀ k → k ≤ wk⁰ (h k)
wk-nat h r zero = z≤n
wk-nat h r (suc k) = ≤-trans (s≤s (wk-nat h r k)) (wk-< (proj₁ r k))

fl : ∀ x → Reg⁰ x → ∀ m → suc (suc m) + wk⁰ x ≤ fg x (suc (suc m))
fl t0 r m = subst (_≤ suc (suc (suc m))) (sym (+-identityʳ (suc (suc m)))) (n≤1+n _)
fl (ts a) r m =
  subst (_≤ iter (fg a) s s) (sym (+-suc s (wk⁰ a))) (go₂)
  where
  s = suc (suc m)
  -- 第 c+1 次迭代不低于 s + wk a
  lo : ∀ c → s + wk⁰ a ≤ iter (fg a) s (suc c)
  lo c with iter (fg a) s c | iter-≥ a (suc m) c
  ... | suc (suc y) | s≤s (s≤s le) = ≤-trans (+-mono-≤ (s≤s (s≤s le)) ≤-refl) (fl a r y)
  go₂ : suc (s + wk⁰ a) ≤ iter (fg a) s (suc (suc m))
  go₂ with iter (fg a) s (suc m) | lo m | iter-≥ a (suc m) (suc m)
  ... | suc y | le | _ = ≤-trans (s≤s le) (infl a y)
fl (tl h) r m =
  ≤-trans (subst (_≤ suc (suc m) + wk⁰ (h (suc (suc m)))) refl
             (+-mono-≤ {suc (suc m)} ≤-refl (≤-trans (wk-< (proj₁ r 1)) (wk-chain h r (≤⇒≤′ (s≤s (s≤s z≤n)))))))
          (fl (h (suc (suc m))) (proj₂ r (suc (suc m))) m)

-- 一切 Reg⁰ 的极限树: k ≥ 2 时 FGH ≥ 2k
reg-floor : ∀ h → Reg⁰ (tl h) → ∀ m → suc (suc m) + suc (suc m) ≤ fg (tl h) (suc (suc m))
reg-floor h r m = ≤-trans (+-mono-≤ {suc (suc m)} ≤-refl (wk-nat h r (suc (suc m)))) (fl (h (suc (suc m))) (proj₂ r (suc (suc m))) m)
```

## §3 能排除的: `slow`

`slowt k` 与 [OCFSpecNeg](OCFSpecNeg.lagda.md) 同形, 取自那里, 搬到 `OCF.Free.Level`: 前 $k+1$ 项是 0.

```agda
natᶠ : ℕ → Ordᶜ zero
natᶠ zero = zero
natᶠ (suc n) = suc (natᶠ n)

le : ℕ → ℕ → Bool
le k       zero    = true
le zero    (suc n) = false
le (suc k) (suc n) = le k n

sa : ℕ → ℕ → Ordᶜ zero
sa k n = if le k n then zero else natᶠ n

slowt : ℕ → Ordᶜ zero
slowt k = lim (sa k)

slow-not-reg : ∀ k → ¬ Reg (slowt (suc k))
slow-not-reg k r = no-self (proj₁ r 0)

le-refl : ∀ k → le k k ≡ true
le-refl zero    = refl
le-refl (suc k) = le-refl k

slow-fgh : ∀ k → FGH (slowt k) k ≡ suc k
slow-fgh k = subst (λ b → FGH (if b then zero else natᶠ k) k ≡ suc k) (sym (le-refl k)) refl

-- 第二个理由: 下界
slow-floor : ∀ m → ¬ Reg (slowt (suc (suc m)))
slow-floor m r = bad (≤-trans (reg-floor (λ n → toTr (sa (suc (suc m)) n)) r m) (subst (_≤ suc (suc (suc m))) (sym (trans′ (fg-FGH (slowt (suc (suc m))) (suc (suc m))) (slow-fgh (suc (suc m))))) ≤-refl))
  where
  trans′ : ∀ {a b c : ℕ} → a ≡ b → b ≡ c → a ≡ c
  trans′ refl q = q
  bad : ¬ (suc (suc m) + suc (suc m) ≤ suc (suc (suc m)))
  bad (s≤s (s≤s h)) = <-irrefl refl (≤-trans (s≤s (m≤m+n m m)) (lem h))
    where
    lem : m + suc (suc m) ≤ suc m → suc (m + m) ≤ m
    lem h₁ with subst (_≤ suc m) (+-suc m (suc m)) h₁
    ... | s≤s h₂ = subst (_≤ m) (+-suc m m) h₂
```

## §4 排除不了的

```agda
ωᶠ ω⁺ᶠ : Ordᶜ zero
ωᶠ = lim natᶠ
ω⁺ᶠ = lim (λ n → natᶠ (suc n))

reg-nat : ∀ n → Reg (natᶠ n)
reg-nat zero = tt
reg-nat (suc n) = reg-nat n

nat-walk : ∀ {a b} → a < b → W⁰ (toTr (natᶠ a)) (toTr (natᶠ b))
nat-walk {a} {suc b} (s≤s p) with ≤⇒≤′ p
... | ≤′-refl = w0
... | ≤′-step q = ws (nat-walk (s≤s (≤′⇒≤ q)))

nat-≼ : ∀ {a b} → a ≤ b → natᶠ a ≼ natᶠ b
nat-≼ z≤n = z≼
nat-≼ (s≤s p) = s≼s (nat-≼ p)

reg-gen : ∀ (g : ℕ → ℕ) → (∀ n → g n < g (suc n)) → Reg (lim (λ n → natᶠ (g n)))
reg-gen g st = (λ n → nat-walk (st n)) , (λ n → reg-nat (g n))

g≥ : ∀ (g : ℕ → ℕ) → (∀ n → g n < g (suc n)) → ∀ n → n ≤ g n
g≥ g st zero = z≤n
g≥ g st (suc n) = ≤-trans (s≤s (g≥ g st n)) (st n)

-- 任何严格增的 g: 值都是 ω, FGH 随 g 走, 所以没有上界
reg-fast : ∀ (g : ℕ → ℕ) → (∀ n → g n < g (suc n)) →
           Reg (lim (λ n → natᶠ (g n))) × (lim (λ n → natᶠ (g n)) ≈ᵛ ωᶠ) × (∀ k → FGH (lim (λ n → natᶠ (g n))) k ≡ FGH (natᶠ (g k)) k)
reg-fast g st = reg-gen g st ,
  (l≼ (λ n → ≼l (g n) (≼-refl (natᶠ (g n)))) , l≼ (λ n → ≼l n (nat-≼ (g≥ g st n)))) ,
  (λ k → refl)

reg-blind : Reg ωᶠ × Reg ω⁺ᶠ × (ωᶠ ≈ᵛ ω⁺ᶠ) × FGH ωᶠ 2 ≡ 8 × FGH ω⁺ᶠ 2 ≡ 2048
reg-blind = reg-gen (λ n → n) (λ n → ≤-refl) , reg-gen suc (λ n → ≤-refl) ,
  (l≼ (λ n → ≼l n (≼-suc (≼-refl (natᶠ n)))) , l≼ (λ n → ≼l (suc n) (≼-refl (natᶠ (suc n))))) ,
  refl , refl
```

**`reg-gap`.** 值严格大, FGH 在 2 处一样. 树的前三项是 0, 1, 2, 第 3 项起跳到 $\omega$ 以上. 跳的那一项 $X=\lim_j (3+j)$ 的第 1 项是 4, 2 在它的 1-走步上, 所以 `Reg⁰` 过得去. 这个构造对任何 $K$ 都可以做 (前 $K$ 项是 $0,\dots,K-1$), 这里只写 $K=3$.

```agda
Xᶠ : Ordᶜ zero
Xᶠ = lim (λ j → natᶠ (3 + j))

sucs : Ordᶜ zero → ℕ → Ordᶜ zero
sucs x zero = x
sucs x (suc j) = suc (sucs x j)

hᵍ : ℕ → Ordᶜ zero
hᵍ 0 = natᶠ 0
hᵍ 1 = natᶠ 1
hᵍ 2 = natᶠ 2
hᵍ (suc (suc (suc j))) = sucs Xᶠ j

tᵍ : Ordᶜ zero
tᵍ = lim hᵍ

X-reg : Reg Xᶠ
X-reg = reg-gen (3 +_) (λ n → ≤-refl)

sucs-reg : ∀ j → Reg (sucs Xᶠ j)
sucs-reg zero = X-reg
sucs-reg (suc j) = sucs-reg j

reg-tᵍ : Reg tᵍ
reg-tᵍ = st , rg
  where
  st : ∀ n → W⁰ (toTr (hᵍ n)) (toTr (hᵍ (suc n)))
  st 0 = w0
  st 1 = w0
  st 2 = wl (nat-walk {a = 2} {b = 4} (s≤s (s≤s (s≤s z≤n))))
  st (suc (suc (suc j))) = w0
  rg : ∀ n → Reg⁰ (toTr (hᵍ n))
  rg 0 = tt
  rg 1 = tt
  rg 2 = tt
  rg (suc (suc (suc j))) = sucs-reg j

ω≼X : ωᶠ ≼ Xᶠ
ω≼X = l≼ (λ n → ≼l n (nat-≼ (≤-trans (m≤m+n n 3) (subst (_≤ 3 + n) (+-comm′ n) ≤-refl))))
  where
  +-comm′ : ∀ n → 3 + n ≡ n + 3
  +-comm′ zero = refl
  +-comm′ (suc n) = cong suc (+-comm′ n)

reg-gap : Reg tᵍ × ωᶠ ≺ᵛ tᵍ × FGH tᵍ 2 ≡ 8 × FGH ωᶠ 2 ≡ 8
reg-gap = reg-tᵍ , ≼l 4 (s≼s ω≼X) , refl , refl
```
