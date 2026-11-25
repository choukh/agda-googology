# K2′ 第 4 层：嵌套闭项的值下界

本篇是验收文件，允许 Value 的记号导入闭包。定义与证书文件不导入它。
验收的输入是原块 `Ω₁ +ᴸ Ω₁`，参照为 Level 的 `Ω₁ + Ω₁`。
这里只证下界，不把它升级成序数值互相 ≼ 或一般节点定理。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiK2bValue where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.LevelFixCore as F
import OCF.Align.YiCarry as C
import OCF.Align.YiK2Base as A
import OCF.Align.YiK2Value as R
import OCF.Align.YiK2bBase as B
import OCF.Align.YiK2bNested as N
import OCF.Align.Level as L
import OCF.Align.Value as V
import OCF.Align.RR4MonoFragment as M
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open F using (module G)
open V using (_≼_; _≈ᵛ_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼;
  ≼-refl; ≼-trans; +-mono; iter-≼; ≅→≈ᵛ)

-- 与原 LF 的固定左前缀相同，右侧沿可数树递归。
prefix : L.Ordᶜ L.zero → L.Ordᶜ (L.suc L.zero)
prefix x = L.add V.Ω₁ (λ q → L.suc q) x

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
H-mono (≼i {p = ()} x ex p)
H-mono (i≼ {p = ()} h)
H-mono (≼u {r = ()} p)
H-mono (u≼ {r = ()} p)

-- Raw 的后继行，按值运输种子；不是用 Funext 把极限函数改成相等。
successor-value : ∀ a {x : L.Ordᶜ (L.suc L.zero)} →
  R.read a ≈ᵛ L.ψ⁰ x → R.read (A.successor a) ≈ᵛ L.ψ⁰ (L.suc x)
successor-value a e =
  l≼ (λ n → ≼l n (≼-trans
    (proj₁ (≅→≈ᵛ (R.read-copies a (R.read a) (L.≅-refl⁰ (R.read a)) n)))
    (iter-≼ (proj₁ e) n))) ,
  l≼ (λ n → ≼l n (≼-trans (iter-≼ (proj₂ e) n)
    (proj₂ (≅→≈ᵛ (R.read-copies a (R.read a) (L.≅-refl⁰ (R.read a)) n)))))

tail-value : ∀ a → R.read (N.tail A.closed a) ≈ᵛ H (R.read a)
tail-value G.zero = R.same-on-Ω₁
tail-value (G.suc a) = successor-value (N.tail A.closed a) (tail-value a)
tail-value (G.lim f) =
  l≼ (λ n → ≼l n (proj₁ (tail-value (f n)))) ,
  l≼ (λ n → ≼l n (proj₂ (tail-value (f n))))
tail-value (G.lc () c t g)
tail-value (G.em () a)
tail-value G.top = successor-value A.closed R.same-on-Ω₁

reference : L.Ordᶜ (L.suc L.zero)
reference = V.Ω₁ L.+ V.Ω₁

step : L.Ordᶜ L.zero → L.Ordᶜ L.zero
step x = L.ψ L.zero (λ q → q) (prefix x)

reference-chain : ℕ → L.Ordᶜ L.zero
reference-chain = iter step (L.suc L.zero)

reference-row : L.ψ⁰ reference ≡ L.lim (λ n → H (reference-chain n))
reference-row = refl

prefix-self : ∀ x → prefix x L.≅ prefix x
prefix-self x = L.add-≅ {σ = λ q → L.suc q} {σ′ = λ q → L.suc q}
  (L.Ω-refl (L.suc L.zero)) (L.≅-refl⁰ x)

step≤H : ∀ x → step x ≼ H x
step≤H x = proj₂ (≅→≈ᵛ
  (L.ψ⁰≅ψ {p = L.zero} {σ = λ q → q} (prefix-self x)))

points : ℕ → A.R
points n = C.coordinate (N.NestedChain.chain N.initial n)

chain-lower : ∀ n → reference-chain n ≼ R.read (points n)
chain-lower zero = ≼-refl (L.suc L.zero)
chain-lower (suc n) =
  ≼-trans (step≤H (reference-chain n))
  (≼-trans (H-mono (chain-lower n))
  (≼-trans (proj₂ (tail-value (points n)))
  (≼-trans (M.≼-+ˡ (R.read (points n)) (R.read (N.tail A.closed (points n))))
    (proj₂ (R.read-add-≈ (points n) (N.tail A.closed (points n)))))))

nested-lower : L.ψ⁰ (V.Ω₁ L.+ V.Ω₁) ≼ R.read (B.raw N.closed)
nested-lower = l≼ (λ n → ≼l n
  (≼-trans (H-mono (chain-lower n)) (proj₂ (tail-value (points n)))))
```

## 输入确实高于 Ω₁

先给 `suc Ω₁ ≼ reference`，再否定反向。这个否定针对输入的值，
不是某一行 ψ 保持失败，不消耗止损的一次更换机会。

```agda
suc-Ω₁≤reference : L.suc V.Ω₁ ≼ reference
suc-Ω₁≤reference = ≼i (L.suc L.zero) (L.s≅ L.z≅)
  (≼-refl (L.suc V.Ω₁))

strip-up : ∀ {x y : L.Ordᶜ L.zero} → L.up L.zero x ≼ y → x ≼ y
strip-up (u≼ p) = p
strip-up (≼l n p) = ≼l n (strip-up p)
strip-up (≼i {p = ()} x ex p)
strip-up (≼u {r = ()} p)

no-Ω₁-countable : ∀ (x : L.Ordᶜ L.zero) → V.Ω₁ ≼ x → ⊥
no-Ω₁-countable x (i≼ h) = M.irr x
  (strip-up (h (L.suc x) (L.s≅ (L.≅-refl⁰ x))))
no-Ω₁-countable (L.lim f) (≼l n p) = no-Ω₁-countable (f n) p
no-Ω₁-countable (L.limᵢ () f) (≼i x ex p)
no-Ω₁-countable (L.up () x) (≼u p)

no-suc-Ω₁≤Ω₁ : L.suc V.Ω₁ ≼ V.Ω₁ → ⊥
no-suc-Ω₁≤Ω₁ (≼i x ex (≼u p)) =
  no-Ω₁-countable x (≼-trans (V.≼-suc (≼-refl V.Ω₁)) p)

reference-not≤Ω₁ : reference ≼ V.Ω₁ → ⊥
reference-not≤Ω₁ p = no-suc-Ω₁≤Ω₁ (≼-trans suc-Ω₁≤reference p)
```

以上是闭项的序数值下界，不是基本列验收，也不是有限测试。
没有把 FGH 的比较作为验收；没有反改定义以方便本篇的值证明。
