# 值序作前提的下标单调不成立

> 判决: 编译定理, 无前提, 不读记号. 对任意合法层 k, 记 K 为 k 上的后继形状层; 在下标位置 `K ⊕ ↑ K t` 上, "下标的树侧值 (`YiVWVal`) 互相 ≼ 就推出 `ψ₀ᶻ` 输出 ≼" 推出矛盾 (`Gen.no-value-index-mono≈`; 前提只要单向 ≼ 的 `Gen.no-value-index-mono` 是它的推论).
> 反例: c′ 与 `Ωt K` 值互相 ≼ (`le₁`, `le₂`); c′ 处对角链停住 (`stall`, `chain-stops`: 每项所在孩子都是 `g′` 的零值, 层号恒为 K), 输出 ≼ `ψ₀ᶻ K (Ωt K)` 的 ω 倍 (`upper`); `Ωt K` 处输出严格高于这个界, 中间经 `ψ₀ᶻ K⁺ (Ωt K⁺)` (`lower`, `out-g0`).
> 不否定什么: 只否定量化域含这一对树的版本; 以字面路径 ⊑/≤ 或关系 M 为前提的版本、只在读回域上量化的版本不在其内 (这一对没有字面路径, 见 [YiVNPath](YiVNPath.lagda.md)).
> 实例 `inst₀` (K 为第 1 层), `inst₁` (K 为第 2 层, 即 `YiUTTwo` 的层号位置, 对接见 [YiVNTwo](YiVNTwo.lagda.md)).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVNIdx where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂; trans; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiTBRow using (ψ; mono)
open import OCF.Lean.YiMTTab using (rbᶻ; ψ₀ᶻ)
open import OCF.Lean.YiVWVal using (V; val; _≼_; _≈_; z≼; s≼s; ≼l; l≼; ≼Ω; Ω≼; ≼-refl; ≼-trans;
  _⊹_; ⊹-mono; ⊹-monoˡ; ⊹-assoc; val-+; ◁→≼; val-mono)
import OCF.Lean.YiVWVal as V
```

## 值序的一般引理

`¬s≼` 是值序的无环; `◃→s≼` 用零层树自带的相邻步进把第一位置序变成严格值序.

```agda
¬s≼ : ∀ {k} (a : V k) → V.suc a ≼ a → ⊥
¬s≼ V.zero ()
¬s≼ (V.suc a) (s≼s d)  = ¬s≼ a d
¬s≼ (V.lim f) (≼l n d) = ¬s≼ (f n) (≼-trans (s≼s (≼l n (≼-refl (f n)))) d)
¬s≼ (V.Ω p h) (≼Ω z d) = ¬s≼ (h z) (≼-trans (s≼s (≼Ω z (≼-refl (h z)))) d)

◃→s≼ : {x y : Tr zero} → zero ⊢ x ◃ y → V.suc (val zero x) ≼ val zero y
◃→s≼ ◃s             = s≼s (≼-refl _)
◃→s≼ (◃l {a = a} n) = ≼l (suc n) (◃→s≼ (a n))
◃→s≼ (◃w {p = ()})
◃→s≼ (◃u x () y e)
◃→s≼ (◃c x () r)
◃→s≼ (◃t d e)       = ≼-trans (◃→s≼ d) (◁→≼ (val-mono zero e))

≼⊹r : ∀ {k} (w v : V k) → v ≼ w ⊹ v
≼⊹r w V.zero    = z≼
≼⊹r w (V.suc v) = s≼s (≼⊹r w v)
≼⊹r w (V.lim f) = l≼ (λ n → ≼l n (≼⊹r w (f n)))
≼⊹r w (V.Ω p h) = Ω≼ (λ z → ≼Ω z (≼⊹r w (h z)))

module _ (A : Tr zero) where
  it : ℕ → Tr zero
  it = iter (A +_) A

  comm : ∀ n → val zero (it n) ⊹ val zero A ≼ val zero A ⊹ val zero (it n)
  comm zero    = ≼-refl _
  comm (suc n) =
    ≼-trans (⊹-monoˡ (proj₁ (val-+ A (it n))) (val zero A))
    (≼-trans (proj₁ (⊹-assoc (val zero A) (val zero (it n)) (val zero A)))
    (≼-trans (⊹-mono (val zero A) (comm n))
             (⊹-mono (val zero A) (proj₂ (val-+ A (it n))))))

  cum≼it : ∀ n → val zero (cum (λ _ → A) n) ≼ val zero (it n)
  cum≼it zero    = ≼-refl _
  cum≼it (suc n) =
    ≼-trans (proj₁ (val-+ (cum (λ _ → A) n) A))
    (≼-trans (⊹-monoˡ (cum≼it n) (val zero A))
    (≼-trans (comm n) (proj₂ (val-+ A (it n)))))

cum-cong : (F G : ℕ → Tr zero) → (∀ m → F m ≡ G m) → ∀ n → cum F n ≡ cum G n
cum-cong F G e zero    = e zero
cum-cong F G e (suc n) = cong₂ _+_ (cum-cong F G e n) (e (suc n))
```

## 反例

在层 k 上取变量 (C-10): K 的 Ω 树 `Ωt K` 的分支是 `g d = d + 1` 嵌进 K; c′ 在后继孩子上错一位 (`g′ (suc d) = g d`), 其余孩子取零. 两者的值逐分支互相嵌入, 层号读回却不同.

```agda
module Gen (k : L) (ok : Ok k) where
  K K⁺ : L
  K  = nd sS (λ _ → k)
  K⁺ = nd sS (λ _ → K)

  oK : Ok K
  oK = tt , λ _ → ok

  oK⁺ : Ok K⁺
  oK⁺ = tt , λ _ → oK

  p : Pos K
  p = inj₂ (tt , inj₁ tt)

  g : Tr k → Tr K
  g d = up zero tt (suc d) (z◃ d ◃s)

  ΩK : Tr K
  ΩK = proj₁ (Ωt K)

  ΩK-eq : ΩK ≡ Ω p g
  ΩK-eq = refl

  g′ : Tr k → Tr K
  g′ zero         = zero
  g′ (suc d)      = g d
  g′ (lim f a)    = zero
  g′ (Ω q h)      = zero
  g′ (up x c y e) = zero

  c′ : Tr K
  c′ = Ω p g′

  le₁ : val K ΩK ≼ val K c′
  le₁ = Ω≼ (λ d → ≼Ω (suc d) (≼-refl _))

  le₂h : (d : Tr k) → val K (g′ d) ≼ val K ΩK
  le₂h zero         = z≼
  le₂h (suc d)      = ≼Ω d (≼-refl _)
  le₂h (lim f a)    = z≼
  le₂h (Ω q h)      = z≼
  le₂h (up x c y e) = z≼

  le₂ : val K c′ ≼ val K ΩK
  le₂ = Ω≼ le₂h
```

下标位置与输出: 层号 `K ⊕ ↑ K t`, 证据是 `Ok⊕`/`OkO↑` 给的标准证据, 折叠是主线的 `ψ₀ᶻ`.

```agda
  ℓ : Tr K → L
  ℓ t = K ⊕ ↑ K t

  okℓ : (t : Tr K) → Ok (ℓ t)
  okℓ t = Ok⊕ K (↑ K t) oK (OkO↑ K K oK self t)

  out : Tr K → Tr zero
  out t = proj₁ (ψ₀ᶻ (ℓ t) (okℓ t) (proj₁ (Ωt (ℓ t))))

  ℓ-0 : ℓ zero ≡ K
  ℓ-0 = refl

  ℓ-g0 : ℓ (g zero) ≡ K⁺
  ℓ-g0 = refl
```

## 上界: c′ 处的链停住

`ℓ c′` 是以 k 为下标层的 Ω 形状层号; 折到第 0 层不保留, 输出是链 `X′` 上各项输出的部分和极限 (`out-c′`, `refl`). 链的一步是孩子 `g′ z` 的层上折到 k 层 (`S′`); 从零出发每一步的头都是 `lim`, 而 `g′` 把零与 `lim` 都送到零, 所以每项的层号都是 `ℓ zero = K`.

```agda
  pk : (u : Tr K) → k ≤ ℓ u
  pk u = self ∙ (inc tt self ∙ lift K (↑ K u))

  S′ : Tr K → Tr k
  S′ u = proj₁ (ψ (ℓ u) (okℓ u) (rbᶻ (ℓ u)) (B₀ (ℓ u)) k (pk u) (Ωt k) (proj₁ (Ωt (ℓ u))))

  X′ : ℕ → Tr k
  X′ = iter (λ z → S′ (g′ z)) zero

  out-c′ : val zero (out c′) ≡ V.lim (λ n → val zero (cum (λ m → out (g′ (X′ m))) n))
  out-c′ = refl

  stall : ∀ m → g′ (X′ m) ≡ zero
  stall zero    = refl
  stall (suc m) = cong (λ u → g′ (S′ u)) (stall m)

  chain-stops : ∀ m → X′ (suc m) ≡ S′ zero
  chain-stops m = cong S′ (stall m)

  A⁺ : Tr⁺ zero
  A⁺ = ψ₀ᶻ K oK ΩK

  A : Tr zero
  A = proj₁ A⁺

  out0 : out zero ≡ A
  out0 = refl

  U : V zero
  U = V.lim (λ n → val zero (cum (λ _ → A) n))

  upper : val zero (out c′) ≼ U
  upper = subst (λ v → v ≼ U) (sym out-c′)
    (l≼ (λ n → ≼l n (subst (λ t → val zero t ≼ val zero (cum (λ _ → A) n))
      (sym (cum-cong (λ m → out (g′ (X′ m))) (λ _ → A) (λ m → trans (cong out (stall m)) out0) n)) (≼-refl _))))
```

## 下界: Ωt K 处的第一项已越过

`Ωt K` 处链的第 0 项是层 K⁺ 的 `ψ₀ᶻ` (`out-g0`); 它的链第 1 项含 `ψ₀ᶻ K (Ωt K · ω)`, 后者的结点第 0 支是 `next⁺ A` (A 的 ω 倍). 每一步是 `mono` 或部分和极限的一支 (`◃l`), 只在最后一步用值序的加法.

```agda
  Y : Tr K
  Y = proj₁ (next⁺ (Ωt K))

  T₀ T₁ : Tr zero
  T₀ = proj₁ (next⁺ (Ωt zero))
  T₁ = proj₁ (next⁺ (ψ₀ᶻ K oK Y))

  st1 : zero ⊢ proj₁ (next⁺ A⁺) ◃ proj₁ (ψ₀ᶻ K oK (ΩK + ΩK))
  st1 = mono K oK (rbᶻ K) (B₀ K) zero (z≤ K) (Ωt zero) (◃w {p = p} {g = λ z → ΩK + g z})

  st2 : zero ⊢ proj₁ (ψ₀ᶻ K oK (ΩK + ΩK)) ◃ proj₁ (ψ₀ᶻ K oK Y)
  st2 = mono K oK (rbᶻ K) (B₀ K) zero (z≤ K) (Ωt zero) (◃l {f = iter (ΩK +_) ΩK} {a = nextA ΩK (proj₂ (Ωt K))} 1)

  st3 : zero ⊢ proj₁ (ψ₀ᶻ K oK Y) ◃ T₁
  st3 = ◃l 0

  st4 : zero ⊢ T₀ + T₁ ◃ out (g zero)
  st4 = ◃l 1

  st5 : zero ⊢ out (g zero) ◃ out ΩK
  st5 = mono (ℓ ΩK) (okℓ ΩK) (rbᶻ (ℓ ΩK)) (B₀ (ℓ ΩK)) zero (z≤ (ℓ ΩK)) (Ωt zero) {y = proj₁ (Ωt (ℓ ΩK))} ◃w

  out-g0 : out (g zero) ≡ proj₁ (ψ₀ᶻ K⁺ oK⁺ (proj₁ (Ωt K⁺)))
  out-g0 = refl

  lower : V.suc U ≼ val zero (out ΩK)
  lower = ≼-trans (s≼s (l≼ (λ n → ≼l n (cum≼it A n))))
    (≼-trans (◃→s≼ (◃t st1 (◃t st2 st3)))
    (≼-trans (≼-trans (≼⊹r (val zero T₀) (val zero T₁)) (proj₂ (val-+ T₀ T₁)))
             (◁→≼ (val-mono zero (◃t st4 st5)))))
```

## 定理

`IdxMono≈` 的前提是值互相 ≼, 比 `IdxMono` 的单向 ≼ 强, 所以先否定它.

```agda
  IdxMono≈ : Set
  IdxMono≈ = (t t′ : Tr K) → val K t ≈ val K t′ → val zero (out t) ≼ val zero (out t′)

  IdxMono : Set
  IdxMono = (t t′ : Tr K) → val K t ≼ val K t′ → val zero (out t) ≼ val zero (out t′)

  no-value-index-mono≈ : IdxMono≈ → ⊥
  no-value-index-mono≈ H = ¬s≼ U (≼-trans lower (≼-trans (H ΩK c′ (le₁ , le₂)) upper))

  no-value-index-mono : IdxMono → ⊥
  no-value-index-mono H = no-value-index-mono≈ (λ t t′ e → H t t′ (proj₁ e))
```

## 实例

```agda
one : L
one = nd sS (λ _ → zero)

module G₀ = Gen zero tt
module G₁ = Gen one (tt , λ _ → tt)

inst₀ : G₀.IdxMono → ⊥
inst₀ = G₀.no-value-index-mono

inst₁ : G₁.IdxMono → ⊥
inst₁ = G₁.no-value-index-mono
```
