# YiUB 归约：两个方向的折叠值，归约到后继层号

**验收文件，档位：编译定理 (带前提 `Str`)。** `FOLD2 : ∀ a l → Str a l → Two (ψ⁰ (Ω (L′ a l))) (read (F a l))`，`Two A B` 是两个方向的 `≼ˣ`。
`Str` 对 `a` 递归：零与 `top` 无前提 (第 0、1 层的定理)；极限处要相邻两支的读回是结构前驱 (树侧的条件，部分和由 `YiFlatAbs` 的 `absΩ`/`absΩR` 吸收)；`suc b` 处是这一层的两向陈述 `SucP b` (`b = zero` 是定理 `sucP₀`，其余未证)。
`sucP-chain`：`SucP b` 归约到两条链 (主线累加、参照不累加) 逐项两向 `ChainPt b l n`；第 0 项是 `FOLD2 b` (`chainPt₀`)，未证的只剩第 1 层以上的链的一步 (n ≥ 1)。
不否定什么：`Str` 在常值极限上不成立，与 [YiUBNeg](YiUBNeg.lagda.md) 一致；`SucP` 没有证也没有否定。用法在 [YiUBP2](YiUBP2.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUBRed where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import OCF.Lean.YiLeanCore
open import OCF.Lean.YiLeanFold
open import OCF.Lean.YiLeanTw3 using (R; F; ⌜_⌝; lv)
open import OCF.Lean.YiLeanAccFin using (read; read-plus)
open import OCF.Lean.YiLeanValFin using (HS-read)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl)
open import OCF.Align.YiVmConExact using (_≼ˣ_; ≼lˣ; lˣ; reflˣ; ≅→≼ˣ; ˣ→≼)
open import OCF.Lean.YiZeroAccP using (+ˣ)
open import OCF.Lean.YiChainBase using (T₀; transˣ)
open import OCF.Lean.YiChainOne using (x₁; module Phi)
open import OCF.Lean.YiChainBack using (module PhiR)
open import OCF.Lean.YiFlatAbs using (absΩ; absΩR)
open import OCF.Lean.YiUBOne using (lb₁ˣ; ub₁ˣ)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
```

## 1 两向的吸收

`absorb2`：`X` 与 ψ⁰(Ω a) 两向、`Y` 与 ψ⁰(Ω b) 两向、`a ≺ᴵ b`，则 `X + Y` 与 ψ⁰(Ω b) 两向。

```agda
Two : T₀ → T₀ → Set
Two A B = (A ≼ˣ B) × (B ≼ˣ A)

absorb2 : ∀ {X Y : T₀} {a b} → a L.≺ᴵ b → Two (L.ψ⁰ (L.Ω a)) X → Two (L.ψ⁰ (L.Ω b)) Y →
  Two (L.ψ⁰ (L.Ω b)) (X L.+ Y)
absorb2 {X} r (x₀ , x₁′) (y₀ , y₁) =
  transˣ (absΩ r x₀ (ˣ→≼ x₁′)) (+ˣ (reflˣ X) (≼-refl X) y₀) ,
  transˣ (+ˣ (reflˣ X) (≼-refl X) y₁) (absΩR r x₁′ (ˣ→≼ x₀))

Two-≅ʳ : ∀ {A B C : T₀} → Two A B → B L.≅ C → Two A C
Two-≅ʳ (p , q) e = transˣ p (≅→≼ˣ e) , transˣ (≅→≼ˣ (L.≅-sym e)) q
```

## 2 前提 `Str` 与主定理

`L′ a l` 是 `a` 读成的层号。主线在极限层号上取各支的部分和 (`psum`)，参照逐项取：第 n 个部分和与第 n 支的参照两向，要第 n-1 支被第 n 支吸收，见证由读回的结构前驱经 `toLevel-≺` 给出。

```agda
L′ : (a : R) → Lgl zero a → L.Ordᴵ
L′ a l = L.toLevel (read a) (HS-read a l)

SucP : (b : R) → Lgl zero b → Set
SucP b l = Two (L.ψ⁰ (L.Ω (L′ (G.suc b) l))) (read (F (G.suc b) l))

Str : (a : R) → Lgl zero a → Set
Str G.zero l = ⊤
Str (G.suc b) l = SucP b l
Str (G.lim f) (st , lf) = (∀ n → Str (f n) (lf n)) × (∀ n → read (f n) L.≺ read (f (suc n)))
Str (G.lc () g) l
Str (G.em () a) l
Str G.top l = ⊤

module PSum (f : ℕ → R) (lf : ∀ n → Lgl zero (f n))
  (P : ∀ n → Two (L.ψ⁰ (L.Ω (L′ (f n) (lf n)))) (read (F (f n) (lf n))))
  (fs : ∀ n → read (f n) L.≺ read (f (suc n))) where

  h : ℕ → R
  h n = F (f n) (lf n)

  sums : ∀ n → Two (L.ψ⁰ (L.Ω (L′ (f n) (lf n)))) (read (psum zero h n))
  sums zero = P zero
  sums (suc n) = Two-≅ʳ
    (absorb2 (L.toLevel-≺ (HS-read (f n) (lf n)) (HS-read (f (suc n)) (lf (suc n))) (fs n)) (sums n) (P (suc n)))
    (L.≅-sym (read-plus (psum zero h n) (h (suc n))))

FOLD2 : ∀ a (l : Lgl zero a) → Str a l → Two (L.ψ⁰ (L.Ω (L′ a l))) (read (F a l))
FOLD2 G.zero l s = proj₁ (Phi.PHI x₁ G.top) , proj₁ (PhiR.PHIR x₁ G.top)
FOLD2 (G.suc b) l s = s
FOLD2 (G.lim f) (st , lf) (ss , fs) =
  lˣ (λ n → ≼lˣ n (proj₁ (PSum.sums f lf (λ n → FOLD2 (f n) (lf n) (ss n)) fs n))) ,
  lˣ (λ n → ≼lˣ n (proj₂ (PSum.sums f lf (λ n → FOLD2 (f n) (lf n) (ss n)) fs n)))
FOLD2 (G.lc () g) l s
FOLD2 (G.em () a) l s
FOLD2 G.top l s = lb₁ˣ , ub₁ˣ

UB-str : ∀ a (l : Lgl zero a) → Str a l → read (F a l) ≼ L.ψ⁰ (L.Ω (L.toLevel (read a) (HS-read a l)))
UB-str a l s = ˣ→≼ (proj₂ (FOLD2 a l s))
```

## 3 `SucP` 在第 1 层

`F (suc zero)` 与 `F top` 定义性相同 (层号都是 1)。

```agda
sucP₀ : SucP G.zero tt
sucP₀ = lb₁ˣ , ub₁ˣ
```

## 4 `SucP` 归约到链点

`F (suc b)` 定义性地是第 `⌜ b ⌝` 层上从 `top` 起的累加链折到第 0 层再取极限；参照 ψ⁰ (Ω (L′ b + 1)) 定义性地是不累加的链 `refγ` 逐项取 ψ⁰。`ChainPt b l n`：两条链的第 n 项两向。第 0 项就是 `FOLD2 b`；剩下的是 n ≥ 1，即第 1 层以上的链的一步 (`b = zero` 时由 `YiChainOne` 的 `J`/`JR` 给出)。

```agda
refγ : (c : L.Ordᴵ) → ℕ → L.Ordᶜ c
refγ c = iterᴸ (λ x → L.ψ L.zero (λ r → r) (L.up L.zero x)) (L.Ω c)

ChainPt : (b : R) → Lgl zero b → ℕ → Set
ChainPt b l n = Two (L.ψ⁰ (refγ (L′ b l) n))
  (read (Ψ zero (lv b l) (λ _ → fold) (chain ⌜ b ⌝ (Ψ ⌜ b ⌝ (lv b l) (self ⌜ b ⌝)) n)))

chainPt₀ : ∀ b (l : Lgl zero b) → Str b l → ChainPt b l 0
chainPt₀ b l s = FOLD2 b l s

sucP-chain : ∀ b (l : Lgl zero b) → (∀ n → ChainPt b l n) → SucP b l
sucP-chain b l P = lˣ (λ n → ≼lˣ n (proj₁ (P n))) , lˣ (λ n → ≼lˣ n (proj₂ (P n)))
```
