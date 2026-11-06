# 带类型折叠的 sup 层: 合法的地板 (ℕ-极限层号用 ⊞ 接起来)

> 不含记号. 入口 [TySup](TySup.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 不改已有文件 (否定一路导入了 `TySupC` 的 `topC`).
>
> **为什么.** 否定一路 `NegTySupC.¬LgB-topω`: `TySupC.topC ωc = hl (λ n → ι n (topC (nat n)))` 是 `no-naive-diag` 的形状, 不满足 `LgB`; `Tω` 是把 `Φ` 用在不合法的输入上 (`Sh-Φ` 不看输入, 证书仍成立). 本篇把 ℕ-极限层号的地板改成部分和 $\iota_0\,\Omega_{f_0}\boxplus\iota_1\,\Omega_{f_1}\boxplus\cdots$ (`HtTowerU.θ` 的形状), 证明对一切合法层号 `LgB` (`Lg-topΣ`), 换进实例 `ICdΣ`, 得到输入合法的 `TωΣ` 与对角 `TΩΩΣ`. 读法同 `Tω`, `TΩΩ` (判断).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TySupSum where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥)
open import OCF.Align.TySupIf
open import OCF.Align.TySupC
open import OCF.Align.TySup using (sh→lgB; nat; ωc; lg-ω; ord⊥)
import OCF.Align.TySupFold as F
import OCF.Free.Level as FLv
```

## §1 地板与它的合法

```agda
topΣ : ∀ X → HB (LC X)
ΣΩ : (f : ℕ → Cd) → ℕ → HB (LC (hl f))
topΣ hz = hz
topΣ (hs x) = hΩ (inj₂ tt) up
topΣ (hl f) = hl (ΣΩ f)
topΣ (hΩ () _)
ΣΩ f zero = ι 0 (topΣ (f 0))
ΣΩ f (suc n) = ΣΩ f n ⊞ ι (suc n) (topΣ (f (suc n)))

Lg-topΣ : ∀ X → LgB (topΣ X)
Lg-ΣΩ : ∀ f n → LgB (ΣΩ f n)
Lg-topΣ hz = tt
Lg-topΣ (hs x) = (λ lw e e′ p → up-⊲ p) , (λ c lc → Lg-up c lc)
Lg-topΣ (hl f) = (λ n → ⊞-fst (ΣΩ f n) (ι (suc n) (topΣ (f (suc n))))) , Lg-ΣΩ f
Lg-topΣ (hΩ () _)
Lg-ΣΩ f zero = Lg-ι 0 (topΣ (f 0)) (Lg-topΣ (f 0))
Lg-ΣΩ f (suc n) = Lg-⊞ (ΣΩ f n) (ι (suc n) (topΣ (f (suc n)))) (Lg-ΣΩ f n) (Lg-ι (suc n) (topΣ (f (suc n))) (Lg-topΣ (f (suc n))))
```

`Lg-topΣ` 不要层号合法: 地板的合法由形状给出.

## §2 换进实例, 闭项

```agda
ICdΣ : TySupIf
ICdΣ = record
  { C = Cd ; _⊑_ = _⊑ᶜ_ ; _⊏_ = _⊏ᶜ_ ; LgC = LgB
  ; ⊏→⊑ = ⊏→⊑ᶜ ; lgC↓ = lgC↓ᶜ ; wf = wfC
  ; L = LC ; lv = lvC ; pos = posC ; toE = toC ; top = topΣ
  ; z = hz ; z⊑ = λ X → z⊲ᴮ X ; noK = noKC ; dec = decC }

TCΣ : (X : Cd) → LgB X → HB S⊥
TCΣ X lX = F.Φ ICdΣ X (wfC X) lX hz (z⊲ᴮ X) hz (topΣ X)

LgB-TCΣ : ∀ X lX → LgB (TCΣ X lX)
LgB-TCΣ X lX = sh→lgB (TCΣ X lX) (F.Sh-Φ ICdΣ X (wfC X) lX hz (z⊲ᴮ X) hz (topΣ X))

-- 输入合法: 折叠的输入 topΣ ωc 满足 LgB
TωΣ : HB S⊥
TωΣ = TCΣ ωc lg-ω

in-legal-ω : LgB (topΣ ωc)
in-legal-ω = Lg-topΣ ωc

yΣ : ℕ → Cd
lg-yΣ : ∀ n → LgB (yΣ n)
yΣ zero = hz
yΣ (suc n) = yΣ n ⊞ TCΣ (hs (yΣ n)) (lg-yΣ n)
lg-yΣ zero = tt
lg-yΣ (suc n) = Lg-⊞ (yΣ n) (TCΣ (hs (yΣ n)) (lg-yΣ n)) (lg-yΣ n) (LgB-TCΣ (hs (yΣ n)) (lg-yΣ n))

TΩΩΣ : HB S⊥
TΩΩΣ = hl yΣ

LgB-TΩΩΣ : LgB TΩΩΣ
LgB-TΩΩΣ = (λ n → ⊞-fst (yΣ n) (TCΣ (hs (yΣ n)) (lg-yΣ n))) , lg-yΣ

fghωΣ : ℕ → ℕ
fghωΣ = FLv.FGH (ord⊥ TωΣ)

fghΩΩΣ : ℕ → ℕ
fghΩΩΣ = FLv.FGH (ord⊥ TΩΩΣ)
```

## 结论 (按档)

- **[定理]** `topΣ`, `Lg-topΣ` (对一切层号, 不要层号合法); 实例 `ICdΣ`; 闭项 `TωΣ`, `TΩΩΣ`, 证书 `LgB-TCΣ`, `LgB-TΩΩΣ`; `in-legal-ω`.
- **[判断]** 读法同 `Tω` (ψ₀(Ω_ω)), `TΩΩ` (ψ₀(Ω_Ω)). 地板换了, 闭项不同; 后继层号的地板不变 (`topΣ (hs x)` 与 `topC (hs x)` 字面相同), 只有 ℕ-极限层号处不同.
- 本篇只修 "输入不合法" 一条. 否定一路的另两条 (接口 `Dc` 与 `lv` 之间无律, `constOf` 盲区; 累加版 `Φ` 不单调 `NegTySupMono.Φ-not-mono`) 记入接手清单, 本篇不处理.
