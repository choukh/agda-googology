# YiUB 否定：对一切合法层号的上界不成立 (常值极限)

**验收文件，档位：编译的否定定理。** `no-UB : ¬ (∀ a (l : Lgl zero a) → read (F a l) ≼ L.ψ⁰ (L.Ω (L.toLevel (read a) (HS-read a l))))`。
反例 `aₒ = lim (λ _ → top)` 合法 (相邻两项相等也算第一位置)：主线极限层号的 `top` 取各支的部分和，值是 ε₀·ω 一类 (`suc X ≼ read (F aₒ lₒ)`)，参照逐项取，值是 X = ψ₀(Ω₁) (`ref≼X`)。
读作 "量化域太宽"：不否定链点 `co (pts n)` 上的上界 (那里极限严格增长，部分和被吸收)，也不否定有限层号上的上界 ([YiUBOne](YiUBOne.lagda.md) 是第 1 层)。
`no-str`：[YiUBRed](YiUBRed.lagda.md) 的前提 `Str` 在这个反例上不成立 (相邻两支的读回不是结构前驱)，所以两者相容。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUBNeg where

open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)
open import OCF.Lean.YiLeanCore
open import OCF.Lean.YiLeanTw3 using (R; F)
open import OCF.Lean.YiLeanAccFin using (read; read-plus; fin)
open import OCF.Lean.YiLeanValFin using (HS-read)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; ≼l; l≼; +-mono)
open import OCF.Align.YiVmConExact using (ˣ→≼; irr)
open import OCF.Lean.YiUBOne using (lb₁ˣ)
open import OCF.Lean.YiUBRed using (Str)
```

```agda
aₒ : R
aₒ = G.lim (λ _ → G.top)

lₒ : Lgl zero aₒ
lₒ = (λ _ → inj₁ refl) , (λ _ → tt)

X : L.Ordᶜ L.zero
X = L.ψ⁰ (L.Ω (L.suc L.zero))

X≼F : X ≼ read (F G.top tt)
X≼F = ˣ→≼ lb₁ˣ

sX≼X+X : L.suc X ≼ (X L.+ X)
sX≼X+X = ≼l 0 (≼l 1 (≼-refl (L.suc X)))

-- 部分和的第 1 项是 F top + F top.
low : L.suc X ≼ read (F aₒ lₒ)
low = ≼l 1 (≼-trans sX≼X+X (≼-trans (+-mono X≼F X≼F)
  (≅→≼ (L.≅-sym (read-plus (F G.top tt) (F G.top tt))))))

ref≼X : L.ψ⁰ (L.Ω (L.toLevel (read aₒ) (HS-read aₒ lₒ))) ≼ X
ref≼X = l≼ (λ _ → ≼-refl X)

no-ub : ¬ (read (F aₒ lₒ) ≼ L.ψ⁰ (L.Ω (L.toLevel (read aₒ) (HS-read aₒ lₒ))))
no-ub h = irr X (≼-trans low (≼-trans h ref≼X))

no-UB : ¬ (∀ a (l : Lgl zero a) → read (F a l) ≼ L.ψ⁰ (L.Ω (L.toLevel (read a) (HS-read a l))))
no-UB H = no-ub (H aₒ lₒ)

no-str : ¬ Str aₒ lₒ
no-str (_ , fs) = L.≺-irrefl (fs 0)
```
