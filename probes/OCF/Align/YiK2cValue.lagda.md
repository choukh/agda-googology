# K2′ 续做第 4 层：Ω₁·ω 闭族的值下界

验收文件。定义与证书文件不导入本篇，也不读取 Value 的序。
把上轮固定前缀的值证明改为对带结构自模拟 X ≅ X 的任意第 1 层前缀 X、
任意已认证种子的一步定理。使用前缀自模拟、种子合法性、正性及已给的值下界；没有给某个阶段
新增专属支配前提。再对有限和递归，最后交 Ω₁·ω 的闭输出下界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiK2cValue where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product.Base using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.LevelFixCore as F
import OCF.Align.YiCarry as C
import OCF.Align.YiK2Base as A
import OCF.Align.YiK2Value as R
import OCF.Align.YiK2bBase as B
import OCF.Align.YiK2bNested as N
import OCF.Align.YiK2cFamily as D
import OCF.Align.Level as L
import OCF.Align.Value as V
import OCF.Align.RR4MonoFragment as M
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open F using (module G)
open V using (_≼_; ≼-refl; ≼-trans; ≼l; l≼; ≼i; i≼; ≼u; u≼; z≼; s≼s)

raw-suc-lower : ∀ a {x : L.Ordᶜ (L.suc L.zero)} →
  L.ψ⁰ x ≼ R.read a → L.ψ⁰ (L.suc x) ≼ R.read (A.successor a)
raw-suc-lower a low = l≼ (λ n → ≼l n
  (≼-trans (V.iter-≼ low n)
    (proj₂ (V.≅→≈ᵛ (R.read-copies a (R.read a) (L.≅-refl⁰ (R.read a)) n)))))

module Bound (X : L.Ordᶜ (L.suc L.zero)) (ex : X L.≅ X)
  (seed : B.Output) (low : L.ψ⁰ X ≼ R.read (B.raw seed)) where

  prefix : L.Ordᶜ L.zero → L.Ordᶜ (L.suc L.zero)
  prefix x = L.add X (λ q → L.suc q) x

  H : L.Ordᶜ L.zero → L.Ordᶜ L.zero
  H x = L.ψ⁰ (prefix x)

  base≤H : ∀ x → H L.zero ≼ H x
  base≤H L.zero = ≼-refl (H L.zero)
  base≤H (L.suc x) = ≼l 1 (base≤H x)
  base≤H (L.lim f) = ≼l 0 (base≤H (f 0))
  base≤H (L.limᵢ () f)
  base≤H (L.up () x)

  H-mono : ∀ {x y} → x ≼ y → H x ≼ H y
  H-mono {y = y} z≼ = base≤H y
  H-mono (s≼s p) = V.ψ⁰-suc-≼ (H-mono p)
  H-mono (≼l n p) = ≼l n (H-mono p)
  H-mono (l≼ h) = l≼ (λ n → H-mono (h n))
  H-mono (≼i {p = ()} x e p)
  H-mono (i≼ {p = ()} h)
  H-mono (≼u {r = ()} p)
  H-mono (u≼ {r = ()} p)

  tail-lower : ∀ a → H (R.read a) ≼ R.read (N.tail (B.raw seed) a)
  tail-lower G.zero = low
  tail-lower (G.suc a) = raw-suc-lower (N.tail (B.raw seed) a) (tail-lower a)
  tail-lower (G.lim f) = l≼ (λ n → ≼l n (tail-lower (f n)))
  tail-lower (G.lc () c t g)
  tail-lower (G.em () a)
  tail-lower G.top = raw-suc-lower (B.raw seed) low

  step : L.Ordᶜ L.zero → L.Ordᶜ L.zero
  step x = L.ψ L.zero (λ q → q) (prefix x)

  original : ℕ → L.Ordᶜ L.zero
  original = iter step (L.suc L.zero)

  reference-row : L.ψ⁰ (X L.+ V.Ω₁) ≡ L.lim (λ n → H (original n))
  reference-row = refl

  prefix-self : ∀ x → prefix x L.≅ prefix x
  prefix-self x = L.add-≅ {σ = λ q → L.suc q} {σ′ = λ q → L.suc q}
    ex (L.≅-refl⁰ x)

  step≤H : ∀ x → step x ≼ H x
  step≤H x = proj₂ (V.≅→≈ᵛ
    (L.ψ⁰≅ψ {p = L.zero} {σ = λ q → q} (prefix-self x)))

  points : ℕ → A.R
  points n = C.coordinate (D.Append.Chain.chain seed (D.Append.initial seed) n)

  chain-lower : ∀ n → original n ≼ R.read (points n)
  chain-lower zero = ≼-refl (L.suc L.zero)
  chain-lower (suc n) =
    ≼-trans (step≤H (original n))
    (≼-trans (H-mono (chain-lower n))
    (≼-trans (tail-lower (points n))
    (≼-trans (M.≼-+ˡ (R.read (points n))
        (R.read (N.tail (B.raw seed) (points n))))
      (proj₂ (R.read-add-≈ (points n) (N.tail (B.raw seed) (points n)))))))

  append-lower : L.ψ⁰ (X L.+ V.Ω₁) ≼ R.read (B.raw (D.Append.result seed))
  append-lower = l≼ (λ n → ≼l n
    (≼-trans (H-mono (chain-lower n)) (tail-lower (points n))))
```

## 有限和与极限

条件前提不是未填的强度假设：下面实填全部有限和的实例，初项用上轮
规范 Ω₁ 的无条件值定理。没有使用“高层 ψ 对序数值单调”的错误泛化。

```agda
reference : ℕ → L.Ordᶜ (L.suc L.zero)
reference zero = V.Ω₁
reference (suc n) = reference n L.+ V.Ω₁

reference-self : ∀ n → reference n L.≅ reference n
reference-self zero = L.Ω-refl (L.suc L.zero)
reference-self (suc n) = L.add-≅ {σ = λ q → q} {σ′ = λ q → q}
  (reference-self n) (L.Ω-refl (L.suc L.zero))

finite-lower : ∀ n → L.ψ⁰ (reference n) ≼ R.read (B.raw (D.fold n))
finite-lower zero = proj₂ R.same-on-Ω₁
finite-lower (suc n) = Bound.append-lower (reference n) (reference-self n)
  (D.fold n) (finite-lower n)

omega-reference : L.Ordᶜ (L.suc L.zero)
omega-reference = L.lim reference

omega-lower : L.ψ⁰ omega-reference ≼ R.read (B.raw D.closed)
omega-lower = l≼ (λ n → ≼l n (finite-lower n))
```

## 输入确实高于 Ω₁+Ω₁

`irr₁` 是整个第 1 层的后继非自反，不只针对几个闭项。
limᵢ 行只使用给定比较中的同一个分支，没有高层全分支比较器。

```agda
irr₁ : ∀ (x : L.Ordᶜ (L.suc L.zero)) → L.suc x ≼ x → ⊥
irr₁ L.zero ()
irr₁ (L.suc x) (s≼s p) = irr₁ x p
irr₁ (L.lim f) (≼l n p) = irr₁ (f n)
  (≼-trans (s≼s (≼l n (≼-refl (f n)))) p)
irr₁ (L.limᵢ q f) (≼i x ex p) = irr₁ (f (L.into (L.<→◃ q) x))
  (≼-trans (s≼s (≼i x ex (≼-refl (f (L.into (L.<→◃ q) x))))) p)
irr₁ (L.up L.zero x) (≼u p) = M.irr x
  (≼-trans (s≼s (≼u (≼-refl x))) p)

above-previous : L.suc (V.Ω₁ L.+ V.Ω₁) ≼ omega-reference
above-previous = ≼l 2 (≼i (L.suc L.zero) (L.s≅ L.z≅)
  (≼-refl (L.suc (V.Ω₁ L.+ V.Ω₁))))

not-below-previous : omega-reference ≼ (V.Ω₁ L.+ V.Ω₁) → ⊥
not-below-previous p = irr₁ (V.Ω₁ L.+ V.Ω₁) (≼-trans above-previous p)
```

这是主任务之外单独交付的 (b)：无条件闭输出的序数值下界，以及输入高于
上轮输入的定理。尚无反向比较，没有把 Ω₁·ω 的比较改写成某个更高
ψ₀(Ω_x) 站的精确强度，没有基本列或 FGH 相同的主张。
