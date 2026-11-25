# YiCarry V1：域非空与 V0 坏坐标的排除

此叶模块引用 V0 作核对，主共用接口不导入本篇或 V0。
“坏坐标被排除”精确指它不能携带 V1 访问所必需的 LglB；
完整 ψ 的实际访问都满足 LglB 仍是 K2′ 要交的生成保持义务。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiCarryExamples where

open import Data.Nat.Base using (ℕ)
open import Data.Unit.Base using (tt)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Sum.Base using (inj₁)
import OCF.Align.LevelFixCore as F
open F using (module G)
import OCF.Align.LevelFixVal as V
open import OCF.Align.YiCarry
import OCF.Align.YiCarryV0 as V0
import OCF.Align.YiK2Base as A
import OCF.Align.YiK2Stop as S
import OCF.Align.YiCarryBounds as B
open import OCF.Align.YiRegBase using (Reg)
open import OCF.Align.YiDispBase using (Below; one; e-suc; e-first)
import OCF.Align.RR4RegOmega2 as R

no-v0-bad-coordinate-B : LglB (F.suc F.zero) V0.bad-coordinate → ⊥
no-v0-bad-coordinate-B (l , lc , bc , bt , bg) = S.no-bound-legal lc

module CanonicalB = B.ChainB A.one A.id-body
  (λ η e → proj₂ e) (λ η e η′ e′ d → proj₁ d)

canonical-chain-B : ∀ n →
  LglB F.zero (proj₁ (A.Canonical.chain A.start n))
canonical-chain-B = CanonicalB.chain-B A.start (tt , tt)

source-tw0 : Source
source-tw0 = source (V.tw 0) tw0-carry (V.Legal-tw 0)

source-tw1 : Source
source-tw1 = source (V.tw 1) tw1-carry (V.Legal-tw 1)

source-tw2 : Source
source-tw2 = source (V.tw 2) tw2-carry (V.Legal-tw 2)

source-tw3 : Source
source-tw3 = source (V.tw 3) tw3-carry (V.Legal-tw 3)

source-Ω₂ : Source
source-Ω₂ = source (V.Ω̂ (F.suc (F.suc F.zero))) Ω₂-carry V.Legal-Ω₂
```

这些都是闭证据或全 n 定理，没有有限采样，也没有构造 K1′／K2′。
不改变 V0 的坏坐标仍过原守卫、读回仍 Legal 且 Reg 的旧事实。

## 条件读回的两组逐项闭实例

环境字段分别声明，不能用一个尚未交付的环境假设遮住缺失前提。
k=Ω₁ 时的下一项就是 tw 3，其 Carry 已由主接口给出；
tw3-carry 内部的 Reg 字段直接使用 YiK1.tw3-reg。

```agda
zero-env-reg : Reg F.zero
zero-env-reg = tt

zero-env-root : Below F.zero (V.Ω̂ F.zero)
zero-env-root = one e-suc

zero-env-carry : Carry (V.Ω̂ F.zero)
zero-env-carry = tw1-carry

zero-input-guard : F.Gd F.zero (V.cO F.zero) (V.cO F.zero)
zero-input-guard = inj₁ refl , V.Lgl-cO F.zero

zero-input-B : LglB F.zero (V.cO F.zero)
zero-input-B = cO-B F.zero

zero-conditional-read : Carry (V.up F.zero (V.cO F.zero))
zero-conditional-read = guard-read-carry F.zero
  zero-env-reg zero-env-root zero-env-carry (V.cO F.zero)
  zero-input-guard zero-input-B

omega1-env-reg : Reg (V.tw 2)
omega1-env-reg = R.Ω₁-reg

omega1-env-root : Below (V.tw 2) (V.Ω̂ (V.tw 2))
omega1-env-root = one e-first

omega1-env-carry : Carry (V.Ω̂ (V.tw 2))
omega1-env-carry = tw3-carry

omega1-input-guard : F.Gd (V.tw 2) (V.cO (V.tw 2)) (V.cO (V.tw 2))
omega1-input-guard = inj₁ refl , V.Lgl-cO (V.tw 2)

omega1-input-B : LglB (V.tw 2) (V.cO (V.tw 2))
omega1-input-B = cO-B (V.tw 2)

omega1-conditional-read : Carry (V.up (V.tw 2) (V.cO (V.tw 2)))
omega1-conditional-read = guard-read-carry (V.tw 2)
  omega1-env-reg omega1-env-root omega1-env-carry (V.cO (V.tw 2))
  omega1-input-guard omega1-input-B
```

两组均无模块参数、条件假设或 Funext；这些闭项是条件定理前提可满足的
编译证据。它们没有给出一般 k 的环境，也不证明全塔归纳已完成。
