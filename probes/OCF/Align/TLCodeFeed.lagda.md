# 严格列 (八): 证据的链

> 入口 [TLCode](TLCode.lagda.md). **判决: 条件定理 (编译过, 条件是 `Out`).** 链的每一步带证据, 没有 `⌈_⌉`, 没有 `ᶜ+`, 导入闭包不含 `Code`:
>
> $$C_{n+1}=C_n\oplus(\mathrm{out}(C_n)+1)$$
>
> `⊕` 是序数加法. 这一步的证据是 $C_n$ 的块形是 $C_{n+1}$ 的初始段 (`⊂⊕`), 所以分支严格增长 (`up≺ᶜ`). 唯一的参数是 `Out`: 给每个带证书的高度 $c$ 一个带证书的 $\mathrm{out}(c)$, 不低于第 0 行的层号.
>
> - `Chain.Gν o M₀`: 闭包定理, 一步, 对任何分支. `𝕋ʷ.T⊤ o M₀`: 塔的闭项.
> - `Chain.Fx.feed-up`, `feed-dn`, `cof-out`, `cof-ht`, `y≺`: 输出与高度互相共尾. 对一切 `Out`.
> - `ofExact`: 只要每个输出有精确的带证书的码, 就有 `Out`. `ofLit`: 输出的层号本身带证书时, `out` 就是它.
>
> **没有的: `Out` 的无累加实例.** 第一个障碍见 [TLCodeNeg](TLCodeNeg.lagda.md), [TLCode](TLCode.lagda.md). 有累加的实例在 [TLCodeFeedPad](TLCodeFeedPad.lagda.md), 说明 `Out` 不空, 并且 `T⊤` 就是它的一个实例.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLCodeFeed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Free.Level hiding (up; sim; out)
open import OCF.Free.Prefix using (Z; toZ)
open import OCF.Free.Force using (Goodᴺ; gl; forceᴺ; forceᴺ-HS)
open import OCF.Free.Class using (lvG)
open import OCF.Align.TLCodeShape using (end)
open import OCF.Align.TLCodeLit
open import OCF.Align.TLCodeLe
open import OCF.Align.TLCodeArith using (_⊕_; L⊕)
open import OCF.Align.TLCodeCert using (Gᴸ; val≼ᴸ; ev₀; Tᴸ)
open import OCF.Align.TLCodeUp using (up≺ᴸ; ⊂⊕)
```

## §1 带证书的码

全部写成 `Gᴸ (cert c) end zero` 的字面形式, 再抽象成模块参数. 这不是风格 ([CrossMInst](CrossMInst.lagda.md) 有同样的话): 检查器比较 `forceᴺ` 的两个不同写法时要先化简证书项, 那是整条闭包定理. 所以 §2, §3 对证书抽象, §4 才代入.

```agda
record LC : Set where
  constructor lc
  field
    ⟦_⟧  : Ordᴵ
    cert : Lit ⟦_⟧
open LC public

_⊞_ : LC → LC → LC
c ⊞ d = lc (⟦ c ⟧ ⊕ suc ⟦ d ⟧) (L⊕ (cert c) (ls (cert d)))

≺-tr : ∀ {ℓ₁ ℓ₂ ℓ₃} {c : Ordᶜ ℓ₁} {a : Ordᶜ ℓ₂} {b : Ordᶜ ℓ₃} → c ≺ a → a ≺ b → c ≺ b
≺-tr h (≺z e) = ≺s (≺-respʳ h e)
≺-tr h (≺s r) = ≺s (≺-tr h r)
≺-tr h (≺l n r) = ≺l n (≺-tr h r)
≺-tr h (≺i x ex r) = ≺i x ex (≺-tr h r)
≺-tr h (≺u r) = ≺u (≺-tr h r)

≺→⊑′ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≺ b → a ⊑ b
≺→⊑′ r h = ≺-tr h r

≼⊕ : ∀ a x → x ≼ a ⊕ x
≼⊕ a zero = z≼
≼⊕ a (suc x) = s≼ (≼⊕ a x)
≼⊕ a (lim f s) = l≼ (λ n → l≼ʳ n (≼⊕ a (f n)))
```

## §2 链

```agda
module Chain (br : LC → Z) (G : ∀ c → Goodᴺ (br c)) (u≺ : ∀ c d → forceᴺ _ (G c) ≺ forceᴺ _ (G (c ⊞ d))) (val≼ : ∀ c → ⟦ c ⟧ ≼ lvG (G c)) where
  ly : LC → Ordᴵ
  ly c = lvG (G c)

  yv : LC → Ordᶜ zero
  yv c = forceᴺ _ (G c)

  record Out : Set where
    constructor mkOut
    field
      out  : LC → LC
      out≼ : ∀ c → ly c ≼ ⟦ out c ⟧
  open Out public

  C : Out → LC → ℕ → LC
  C o M₀ zero = M₀
  C o M₀ (suc n) = C o M₀ n ⊞ out o (C o M₀ n)

  νZ : Out → LC → Z
  νZ o M₀ = Z.lim (λ n → br (C o M₀ n))

  -- 闭包定理: 对任何 Out, 任何起点
  Gν : (o : Out) (M₀ : LC) → Goodᴺ (νZ o M₀)
  Gν o M₀ = gl (λ n → G (C o M₀ n)) (λ n → ≺→⊑′ (u≺ (C o M₀ n) (out o (C o M₀ n))))

  T⊤ : Out → LC → Ordᶜ zero
  T⊤ o M₀ = forceᴺ _ (Gν o M₀)

  HS⊤ : (o : Out) (M₀ : LC) → HS (T⊤ o M₀)
  HS⊤ o M₀ = forceᴺ-HS _ (Gν o M₀)

  fgh⊤ : Out → LC → ℕ → ℕ
  fgh⊤ o M₀ = FGH (T⊤ o M₀)
```

## §3 定点

```agda
  module Fx (o : Out) (M₀ : LC) where
    Cₜ : ℕ → LC
    Cₜ = C o M₀

    νlv : Ordᴵ
    νlv = lvG (Gν o M₀)

    -- 输出的层号不超过下一个高度
    feed-up : ∀ n → ly (Cₜ n) ≼ ⟦ Cₜ (suc n) ⟧
    feed-up n = ≼-trans (out≼ o (Cₜ n)) (≼-trans (s≼ʳ (≼-refl _)) (≼⊕ ⟦ Cₜ n ⟧ (suc ⟦ out o (Cₜ n) ⟧)))

    -- 高度不超过输出的层号
    feed-dn : ∀ n → ⟦ Cₜ n ⟧ ≼ ly (Cₜ n)
    feed-dn n = val≼ (Cₜ n)

    lv-is : ∀ n → ly (Cₜ n) ≼ νlv
    lv-is n = l≼ʳ n (≼-refl _)

    cof-out : ∀ n → ⟦ Cₜ n ⟧ ≼ νlv
    cof-out n = ≼-trans (feed-dn n) (lv-is n)

    y≺ : ∀ n → yv (Cₜ n) ≺ yv (Cₜ (suc n))
    y≺ n = u≺ (Cₜ n) (out o (Cₜ n))

    cof-ht : ∀ {x} → x ≺ᴵ νlv → Σ ℕ λ n → x ≼ ⟦ Cₜ (suc n) ⟧
    cof-ht (via e (lim n q)) = n , ≼-trans (≺→≼ (via e q)) (feed-up n)
```

## §4 无累加的 `Out` 的来源 (条件)

`ExactOut`: 每个输出的层号都有带证书的码, 值互相 `≼`. `LitOut`: 层号自己带证书. 两条都是假设, 这里不证. 这一步是 [TLCode](TLCode.lagda.md) 目标 3 的第一个障碍.

```agda
  ExactOut : Set
  ExactOut = ∀ c → Σ LC λ d → Eqv ⟦ d ⟧ (ly c)

  ofExact : ExactOut → Out
  ofExact x = mkOut (λ c → proj₁ (x c)) (λ c → proj₂ (proj₂ (x c)))

  LitOut : Set
  LitOut = ∀ c → Lit (ly c)

  ofLit : LitOut → Out
  ofLit x = mkOut (λ c → lc (ly c) (x c)) (λ c → ≼-refl (ly c))

  -- 条件定理: 只要输出有精确的码, 就有闭项, 没有 ⌈_⌉
  T⊤ˣ : ExactOut → LC → Ordᶜ zero
  T⊤ˣ x = T⊤ (ofExact x)
```

## §5 塔

```agda
up≺ᶜ : ∀ c d → forceᴺ _ (Gᴸ (cert c) end zero) ≺ forceᴺ _ (Gᴸ (cert (c ⊞ d)) end zero)
up≺ᶜ c d = up≺ᴸ (cert c) (cert (c ⊞ d)) (⊂⊕ (cert c) (ls (cert d))) end end tt

module 𝕋ʷ = Chain (λ c → toZ (Tᴸ (cert c) end zero ev₀ zero)) (λ c → Gᴸ (cert c) end zero) up≺ᶜ (λ c → val≼ᴸ (cert c))
```
