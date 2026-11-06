# Review2Blind: 主线的序数值验收 (`TLRuleSpec._≤_` 互相) 不决定 `fgh`

> 路线审查 2 (Fable 5.1, 2026-11-05) 附带的小实验. 不读记号. `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.
>
> `OCFSpecNeg.spec-blind` 已在 `Ordᶜ` 上说明值规格不管大数. 这里把同一件事落到主线自己的类型上: 差树与高度树的闭项都是 `A`, 验收用的序是 `TLRuleSpec._≤_` (`T≈`, `TΣ≈`, `EndLowAccept` 的 `≤→≼ᴬ` 都经它), 大数经 `HtFeedClosed.ord` 再 `FGH`. 两个都字面合法 (`Lg`) 的 `A`, 互相 `≤`, `fgh` 在 2 处是 8 与 2048. 所以: **主线定义的序数值验收 (互相 `≤`/`≼`) 对最终大数没有约束力**, 基本列差一位就差三个数量级; 终点 "互相 `≼`" 只验序数, 不验大数. 这与 `AGENTS.md` 已承认的 "基本列不一致, FGH 的值可能不同" 一致, 这里只是把它写成主线类型上的编译事实, 供风险表引用.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Review2Blind where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg; _⊲_; self; suc)
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl)
open import OCF.Align.HtFeedClosed using (ord)
import OCF.Free.Level as FL

nat : ℕ → A
nat zero = azero
nat (suc n) = asuc (nat n)

-- ω 的两个写法: 基本列 n ↦ n 与 n ↦ n+1
ωᴬ ω⁺ᴬ : A
ωᴬ  = alim nat
ω⁺ᴬ = alim (λ n → nat (suc n))

Lg-nat : ∀ n → Lg (nat n)
Lg-nat zero = tt
Lg-nat (suc n) = Lg-nat n

Lg-ω : Lg ωᴬ
Lg-ω = (λ n → suc self) , Lg-nat

Lg-ω⁺ : Lg ω⁺ᴬ
Lg-ω⁺ = (λ n → suc self) , (λ n → Lg-nat (suc n))

≤-up : ∀ n → nat n ≤ nat (suc n)
≤-up zero = z≤
≤-up (suc n) = s≤ (≤-up n)

-- 互相 ≤: 序数值验收这一档过了
ω≤ω⁺ : ωᴬ ≤ ω⁺ᴬ
ω≤ω⁺ = l≤ (λ n → ≤l n (≤-up n))

ω⁺≤ω : ω⁺ᴬ ≤ ωᴬ
ω⁺≤ω = l≤ (λ n → ≤l (suc n) (≤-refl (nat (suc n))))

-- 大数不同
fgh-ω : FL.FGH (ord ωᴬ) 2 ≡ 8
fgh-ω = refl

fgh-ω⁺ : FL.FGH (ord ω⁺ᴬ) 2 ≡ 2048
fgh-ω⁺ = refl

8≢2048 : 8 ≡ 2048 → ⊥
8≢2048 ()

blindᴬ : (ωᴬ ≤ ω⁺ᴬ × ω⁺ᴬ ≤ ωᴬ) × Lg ωᴬ × Lg ω⁺ᴬ × (FL.FGH (ord ωᴬ) 2 ≡ FL.FGH (ord ω⁺ᴬ) 2 → ⊥)
blindᴬ = (ω≤ω⁺ , ω⁺≤ω) , Lg-ω , Lg-ω⁺ , λ e → 8≢2048 e
```
