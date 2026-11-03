# 归纳-递归块: 证据派发在内在的好输入上仍是 WLPO

> 不含记号. 结论写在 [LvIR](LvIR.lagda.md). 主定理 `no-read`: 设 `G` 是**任何**第 0 层上的谓词, 只要它含反例族 `y s` (`Gy`), 那么任何**读证据**的派发 `(y : O₀) → G y → Dec (y ≺⁰ ω+1)` 都给出 WLPO. 反例族 `HS`, 严格 (`y-strict`), 而且规整 (`y-walk`: 每一项都在下一项的 1-走步上, 即 [InaccModulusBase](InaccModulusBase.lagda.md) 的 `Reg` 的条件). 所以 `G = HS`, `G =` 严格, `G =` 规整都过不了目标 $\omega+1$.
>
> **这不是 `no-uniform`, 也不是 `bad-S`.** 它们说的是拿原始层号对的 `S`. 这里的函数读证据, 而且证据可以任意丰富; 结论照样成立, 因为反例族的每一项本身就带证据. 能逃掉的只有 "`G` 不含反例族", 也就是 `G` 必须窄到是一个有公共上界的族 ([LvIRPos](LvIRPos.lagda.md) 说明这样的 `G` 在块里写不出来).

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LvIRNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import OCF.Align.LvIRBase
```

## §1 反例族

$h_s(n)=n$ 直到 `s` 第一次为真. 设第一次为真在 $n$, 则 $h_s(n)=\omega_{n-1}$ (从 $n-1$ 起数的 $\omega$), 此后每步加一. 所以 `s` 全假时 $y_s$ 就是 $\omega$; 否则 $y_s$ 的值是 $\omega\cdot2$. 关键的一项是 $\omega_{n-1}$: 它的 1-走步经过 $n-1$, 所以规整性不挡它.

```agda
natO : ℕ → O₀
natO zero    = O₀.zero
natO (suc n) = O₀.suc (natO n)

ω : O₀
ω = O₀.lim natO

-- a, a+1, a+2, ...
plus : O₀ → ℕ → O₀
plus a zero    = a
plus a (suc n) = O₀.suc (plus a n)

ωf : O₀ → O₀
ωf a = O₀.lim (plus a)

flag : (ℕ → Bool) → ℕ → Bool
flag s zero    = s zero
flag s (suc n) = flag s n ∨ s (suc n)

h : (ℕ → Bool) → ℕ → O₀
stepH : Bool → Bool → O₀ → ℕ → O₀
h s zero    = stepH false (s zero) O₀.zero zero
h s (suc n) = stepH (flag s n) (s (suc n)) (h s n) (suc n)

-- 已经翻转: 加一. 正要翻转: 从当前项起数的 ω. 没有翻转: 加一 (就是下一个自然数)
stepH true  _     p n = O₀.suc p
stepH false true  p n = ωf p
stepH false false p zero    = p
stepH false false p (suc n) = O₀.suc p

y : (ℕ → Bool) → O₀
y s = O₀.lim (h s)

flag-false : ∀ s → (∀ n → s n ≡ false) → ∀ n → flag s n ≡ false
flag-false s e zero    = e zero
flag-false s e (suc n) rewrite flag-false s e n | e (suc n) = refl

∨-true : ∀ b → (b ∨ true) ≡ true
∨-true true  = refl
∨-true false = refl

flag-true : ∀ s n → s n ≡ true → flag s n ≡ true
flag-true s zero    p = p
flag-true s (suc n) p rewrite p = ∨-true (flag s n)

flag-up : ∀ s n → flag s n ≡ true → flag s (suc n) ≡ true
flag-up s n p rewrite p = refl

-- s 全假: 就是自然数
h-false : ∀ s → (∀ n → s n ≡ false) → ∀ n → h s n ≅⁰ natO n
h-false s e zero rewrite e zero = z≅
h-false s e (suc n) rewrite flag-false s e n | e (suc n) = s≅ (h-false s e n)
```

## §2 证据: 反例族 `HS`, 严格, 规整

```agda
-- a ≺ a + m + 1
≺-plus : ∀ a m → a ≺⁰ plus a (suc m)
≺-plus a zero    = ≺z (≅⁰-refl a)
≺-plus a (suc m) = ≺s (≺-plus a m)

≺-ωf : ∀ a → a ≺⁰ ωf a
≺-ωf a = ≺l 1 (≺-plus a 0)

⊑-suc : ∀ a → a ⊑⁰ O₀.suc a
⊑-suc a q = ≺s q

⊑-ωf : ∀ a → a ⊑⁰ ωf a
⊑-ωf a q = ≺l 0 q

plus-HS : ∀ {a} → HS a → ∀ m → HS (plus a m)
plus-HS ha zero    = ha
plus-HS ha (suc m) = hs (plus-HS ha m)

ωf-HS : ∀ {a} → HS a → HS (ωf a)
ωf-HS {a} ha = hl (plus-HS ha) (λ n → ⊑-suc (plus a n))

stepH-HS : ∀ b c {p} n → HS p → HS (stepH b c p n)
stepH-HS true  c     n       hp = hs hp
stepH-HS false true  n       hp = ωf-HS hp
stepH-HS false false zero    hp = hp
stepH-HS false false (suc n) hp = hs hp

h-HS : ∀ s n → HS (h s n)
h-HS s zero    = stepH-HS false (s zero) zero hz
h-HS s (suc n) = stepH-HS (flag s n) (s (suc n)) (suc n) (h-HS s n)

stepH-⊑ : ∀ b c p n → p ⊑⁰ stepH b c p (suc n)
stepH-⊑ true  c     p n = ⊑-suc p
stepH-⊑ false true  p n = ⊑-ωf p
stepH-⊑ false false p n = ⊑-suc p

h-step : ∀ s n → h s n ⊑⁰ h s (suc n)
h-step s n = stepH-⊑ (flag s n) (s (suc n)) (h s n) n

y-HS : ∀ s → HS (y s)
y-HS s = hl (h-HS s) (h-step s)

-- 严格: 每一项都是下一项的前驱
stepH-≺ : ∀ b c p n → p ≺⁰ stepH b c p (suc n)
stepH-≺ true  c     p n = ≺z (≅⁰-refl p)
stepH-≺ false true  p n = ≺-ωf p
stepH-≺ false false p n = ≺z (≅⁰-refl p)

y-strict : ∀ s n → h s n ≺⁰ h s (suc n)
y-strict s n = stepH-≺ (flag s n) (s (suc n)) (h s n) n

-- 规整: 每一项都在下一项的 1-走步上
data Wk (a : O₀) : O₀ → Set where
  here  : ∀ {b} → a ≅⁰ b → Wk a (O₀.suc b)
  down  : ∀ {b} → Wk a b → Wk a (O₀.suc b)
  go    : ∀ {f} → Wk a (f 1) → Wk a (O₀.lim f)

stepH-w : ∀ b c p n → Wk p (stepH b c p (suc n))
stepH-w true  c     p n = here (≅⁰-refl p)
stepH-w false true  p n = go (here (≅⁰-refl p))
stepH-w false false p n = here (≅⁰-refl p)

y-walk : ∀ s n → Wk (h s n) (h s (suc n))
y-walk s n = stepH-w (flag s n) (s (suc n)) (h s n) n
```

## §3 读出

`s` 全假时 $y_s\cong\omega$, 所以 $y_s\prec\omega+1$. 若 $y_s\prec\omega+1$, 那么 $y_s\cong\omega$ 或 $y_s\prec\omega$; 后者不可能, 因为 $\omega$ 的前驱都是自然数, 而自然数不 $\cong$ 极限. 前者说 $h_s(n)\cong n$ 对一切 $n$. 而 `s` 在 $n$ 为真时, $h_s(n)$ 不 $\cong n$: 翻转那一项是极限, 此后的项头上是 `suc` 但里面有极限.

```agda
WLPO : Set
WLPO = ∀ (s : ℕ → Bool) → (∀ n → s n ≡ false) ⊎ ¬ (∀ n → s n ≡ false)

-- 自然数里没有极限
data NoLim : O₀ → Set where
  nz : NoLim O₀.zero
  ns : ∀ {a} → NoLim a → NoLim (O₀.suc a)

≅-noLim : ∀ {a b} → a ≅⁰ b → NoLim a → NoLim b
≅-noLim z≅     nz     = nz
≅-noLim (s≅ e) (ns h) = ns (≅-noLim e h)

nat-noLim : ∀ n → NoLim (natO n)
nat-noLim zero    = nz
nat-noLim (suc n) = ns (nat-noLim n)

-- 翻转之后 h 不是自然数. 这里只用第一次为真的那一项或其后继
h-true : ∀ s n → flag s n ≡ true → NoLim (h s n) → ⊥
h-true s zero p nl with s zero
... | true = lim-not nl where
  lim-not : NoLim (ωf O₀.zero) → ⊥
  lim-not ()
h-true s (suc n) p nl with flag s n in fe | s (suc n)
... | true  | c = h-true s n fe (peel nl) where
  peel : NoLim (O₀.suc (h s n)) → NoLim (h s n)
  peel (ns x) = x
... | false | true = lim-not nl where
  lim-not : NoLim (ωf (h s n)) → ⊥
  lim-not ()

-- ω 的前驱都是自然数
≺ω-nat : ∀ {c} → c ≺⁰ ω → NoLim c
≺ω-nat (≺l n q) = gon n q where
  gon : ∀ n {c} → c ≺⁰ natO n → NoLim c
  gon (suc n) (≺z e) = ≅-noLim (≅⁰-sym e) (nat-noLim n)
  gon (suc n) (≺s q) = gon n q

y-not-nat : ∀ s → NoLim (y s) → ⊥
y-not-nat s ()

read-yes : ∀ s → y s ≺⁰ O₀.suc ω → (∀ n → flag s n ≡ false)
read-yes s (≺z (l≅ e)) n with flag s n in fe
... | false = refl
... | true  = ⊥-elim (h-true s n fe (≅-noLim (≅⁰-sym (e n)) (nat-noLim n)))
read-yes s (≺s q) n = ⊥-elim (y-not-nat s (≺ω-nat q))

all-false→ : ∀ s → (∀ n → s n ≡ false) → y s ≺⁰ O₀.suc ω
all-false→ s e = ≺z (l≅ (h-false s e))

flag→s : ∀ s → (∀ n → flag s n ≡ false) → ∀ n → s n ≡ false
flag→s s e n with s n in sn
... | false = refl
... | true  with trans′ (sym (flag-true s n sn)) (e n) where
  trans′ : {x y z : Bool} → x ≡ y → y ≡ z → x ≡ z
  trans′ refl q = q
... | ()
```

## §4 主定理

`no-read` 的 `G` 是任意的, 派发 `d` 可以读证据. `no-read-HS`: `G = HS`.

```agda
no-read : (G : O₀ → Set) → (∀ s → G (y s)) → (∀ a → G a → Dec (a ≺⁰ O₀.suc ω)) → WLPO
no-read G Gy d s with d (y s) (Gy s)
... | yes q = inj₁ (flag→s s (read-yes s q))
... | no  q = inj₂ (λ e → q (all-false→ s e))

no-read-HS : (∀ a → HS a → Dec (a ≺⁰ O₀.suc ω)) → WLPO
no-read-HS = no-read HS y-HS
```

**穿透或上升的判决也一样.** 把 `Dec` 换成判决的语义: 穿透给 $y\prec\omega+1$, 上升给 $\omega+1\sqsubseteq y$. 第二支推出 `s` 不全假: 全假时 $y_s\cong\omega$, $\omega\prec\omega+1\sqsubseteq y_s$, 而 $\omega\prec y_s\cong\omega$ 与无自反矛盾. 所以这条否定对 "带正确性证据的判决" 成立, 不只对 `Dec`.

```agda
data Vd (a : O₀) : Set where
  pen  : a ≺⁰ O₀.suc ω → Vd a
  rise : O₀.suc ω ⊑⁰ a → Vd a

no-verdict : (G : O₀ → Set) → (∀ s → G (y s)) → (∀ a → G a → Vd a) → WLPO
no-verdict G Gy d s with d (y s) (Gy s)
... | pen q  = inj₁ (flag→s s (read-yes s q))
... | rise q = inj₂ (λ e → ≺⁰-irrefl (≺⁰-respʳ (q (≺z (≅⁰-refl ω))) (l≅ (h-false s e))))

-- 分支的形状: 好输入是 v = a + 1, 比的是它的前驱 a (LvIRReach 的 `ask`)
no-branch : (G : O₀ → Set) → (∀ s → G (O₀.suc (y s))) → (∀ a → G (O₀.suc a) → Vd a) → WLPO
no-branch G Gy d = no-verdict (λ a → G (O₀.suc a)) Gy d

no-branch-HS : (∀ a → HS (O₀.suc a) → Vd a) → WLPO
no-branch-HS = no-branch HS (λ s → hs (y-HS s))
```
