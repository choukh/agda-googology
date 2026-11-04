# 否定: 为什么切口只能是结构证据

> 不含记号. 结论写在 [GuardRead](GuardRead.lagda.md). 这些否定**只否定下面列的想法**, 不否定切口本身 (`Sp`, `Tc-F` 是定理).
>
> - `no-cut`: 想法 "切口由 `⊴` 推出 (`Str` 作判定, 比较 $F\eta$ 与位置)". **若 $A\trianglelefteq B$ 总给出读法 `Cu`, 则 LPO.** 反例 $A=\lim_n\mathrm{sel}(\exists m\le n.\,y\,m)$, $B=2$, 节点 1. 所以 `Str` 不能由 `WFˢ` 算出, 只能由闭包的结构给, 与 `no-min` 同一个方向, 这里下界是字面的.
> - `no-fp-move`: 想法 "比较第一位置" (`⊴` 搬第一位置). **`⊴` 不搬极限的第一位置, 这是闭合的反例.** `⊴-lim-l` 是闭包定理用的七条之一, 带上这个搬运它就假了.
> - `no-F₀-first`: 想法 "比较第一路径 (`cmpF`)": $F\,0$ 不是 $F\,1$ 的第一路径前驱, 它是第一支本身. `cmpF` 的输入拿不到.
> - `no-lim-cmp`: 想法 "极限节点也要回答". **若 $A$ 与 $\lim h$ 总可比, 则 LPO.** 这就是 `Cu` 留 `cUn` 的理由, 也是 `s-lim` 不带证据的理由.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardReadNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.GuardTightCum using (Ordᴵ; zero; suc)
open import OCF.Align.GuardTightLv
open Lv Dom₀
open import OCF.Align.GuardTightTab Dom₀ using (irr)
open import OCF.Align.GuardTightBase using (Lk; fromCpS)
import OCF.Align.GuardTightUni as Uni
open Uni Dom₀ using (F)
open import OCF.Align.GuardReadCut using (Cu; cIn; cNw; cUn)
open import OCF.Align.GuardReadBound using (pth→st)
```

## §1 反例族

```agda
LPO : Set
LPO = ∀ (y : ℕ → Bool) → (Σ ℕ λ m → y m ≡ true) ⊎ (∀ n → y n ≡ false)

any : (ℕ → Bool) → ℕ → Bool
any y zero    = y zero
any y (suc n) = any y n ∨ y (suc n)

any→ : ∀ y n → any y n ≡ true → Σ ℕ λ m → y m ≡ true
any→ y zero e = zero , e
any→ y (suc n) e with any y n in eq
... | true = any→ y n eq
... | false = suc n , e

→any : ∀ y m → y m ≡ true → any y m ≡ true
→any y zero e = e
→any y (suc m) e = go (any y m) e
  where
  go : ∀ a {b} → b ≡ true → (a ∨ b) ≡ true
  go true r = refl
  go false r = r

sel : Bool → LG
sel true  = suc zero
sel false = zero

sel-≈ : ∀ b → sel b ≈ sel b
sel-≈ true = s≈ z≈
sel-≈ false = z≈

sel-wf : ∀ b → WFˢ (sel b)
sel-wf true = tt
sel-wf false = tt

⊴-sel : ∀ a b → sel a ⊴ sel (a ∨ b)
⊴-sel true b = ≈→⊴ (s≈ z≈)
⊴-sel false b = ⊴-zero

hy : (ℕ → Bool) → ℕ → LG
hy y n = sel (any y n)

Ay : (ℕ → Bool) → LG
Ay y = lim (hy y)

Ay-st : ∀ y n → hy y n ⊴ hy y (suc n)
Ay-st y n = ⊴-sel (any y n) (y (suc n))

Ay-wf : ∀ y → WFˢ (Ay y)
Ay-wf y = Ay-st y , (λ n → sel-wf (any y n))

Ay-≈ : ∀ y → Ay y ≈ Ay y
Ay-≈ y = l≈ (λ n → sel-≈ (any y n))

two : LG
two = suc (suc zero)

sel⊴two : ∀ b → sel b ⊴ two
sel⊴two true = ⊴-suc-r (≈→⊴ (s≈ z≈))
sel⊴two false = ⊴-zero

Ay⊴two : ∀ y → Ay y ⊴ two
Ay⊴two y = ⊴-lim-l (λ n → sel⊴two (any y n))
```

## §2 `no-cut`

```agda
CutFrom⊴ : Set
CutFrom⊴ = ∀ A B → A ⊴ B → WFˢ A → WFˢ B → A ≈ A → B ≈ B → ∀ {k} (P : Cp k B) → Cu A P

-- 位置 1 落在 sel b 里, 则 b 是 true
in-sel : ∀ b {rep} → Lk (suc zero) rep → Cp rep (sel b) → b ≡ true
in-sel true d Q = refl
in-sel false (inj₁ ()) self
in-sel false (inj₂ ()) self

no-cut : CutFrom⊴ → LPO
no-cut H y with H (Ay y) two (Ay⊴two y) (Ay-wf y) tt (Ay-≈ y) (s≈ (s≈ z≈)) {suc zero} (suc self)
... | cIn (inj₁ ()) self t
... | cIn (inj₂ ()) self t
... | cIn d (lim n Q) t = inj₁ (any→ y n (in-sel (any y n) d Q))
... | cNw ev = inj₂ all-false
  where
  no : ∀ n → any y n ≡ true → ⊥
  no n e with ⊴p ev {k = zero} (lim n (subst (λ b → zero < sel b) (sym e) zero))
  ... | viaᴸ d () t

  all-false : ∀ n → y n ≡ false
  all-false n with y n in eq
  ... | false = refl
  ... | true = ⊥-elim (no n (→any y n eq))
```

## §3 `no-fp-move`, `no-F₀-first`, `no-lim-cmp`

```agda
A₀ : LG
A₀ = lim (λ _ → zero)

A₀⊴ : A₀ ⊴ suc zero
A₀⊴ = ⊴-lim-l (λ _ → ⊴-zero)

no-fp-move : (Σ LG λ rep → (A₀ ≈ rep) × Cpᶠ rep (suc zero)) → ⊥
no-fp-move (.(suc zero) , () , self)
no-fp-move (.zero , () , suc self)

-- F 0 是 F 1 的第一支本身, 不是第一路径的前驱
no-F₀-first : F zero ≺ᶠ F (suc zero) → ⊥
no-F₀-first (preᶠ d (fst p)) = irr (F zero) (pth→st (≪→< p)) d

-- 极限节点的回答
sel₃ : Bool → LG
sel₃ true  = suc (suc (suc zero))
sel₃ false = suc zero

sel₃-mono : ∀ a b → sel₃ a ⊴ sel₃ (a ∨ b)
sel₃-mono true b = ≈→⊴ (s≈ (s≈ (s≈ z≈)))
sel₃-mono false false = ≈→⊴ (s≈ z≈)
sel₃-mono false true = ⊴-suc-r (⊴-suc-r (≈→⊴ (s≈ z≈)))

hy₃ : (ℕ → Bool) → ℕ → LG
hy₃ y n = sel₃ (any y n)

no-lt2 : ∀ {rep} → suc (suc zero) ≈ rep → rep < two → ⊥
no-lt2 (s≈ ()) zero
no-lt2 _ (suc (suc ()))

LimCmp : Set
LimCmp = ∀ (A : LG) (h : ℕ → LG) → (∀ n → h n ⊴ h (suc n)) → (A ⊴ lim h) ⊎ (lim h ⊴ A)

no-lim-cmp : LimCmp → LPO
no-lim-cmp H y with H two (hy₃ y) (λ n → sel₃-mono (any y n) (y (suc n)))
... | inj₁ a = inj₁ (some (⊴p a {k = suc zero} zero))
  where
  -- 1 < lim h: 某个 h n 是 3
  in₃ : ∀ b {rep} → (suc zero ≈ rep) → rep < sel₃ b → b ≡ true
  in₃ true d r = refl
  in₃ false (s≈ z≈) (suc ())
  some : (suc zero) ≺⟨ _ ⟩ lim (hy₃ y) → Σ ℕ λ m → y m ≡ true
  some (viaᴸ d (lim n r) _) = any→ y n (in₃ (any y n) d r)
... | inj₂ b = inj₂ all-false
  where
  no : ∀ n → any y n ≡ true → ⊥
  no n e with ⊴p b {k = suc (suc zero)} (lim n (subst (λ c → suc (suc zero) < sel₃ c) (sym e) zero))
  ... | viaᴸ d p t = no-lt2 d p

  all-false : ∀ n → y n ≡ false
  all-false n with y n in eq
  ... | false = refl
  ... | true = ⊥-elim (no n (→any y n eq))
```
