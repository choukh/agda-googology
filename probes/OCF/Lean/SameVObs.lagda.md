# SameV (六): `crossX` 用不到 `TU 1` 的输入上 (下一个卡点)

> 不含记号. 入口 [SameV](SameV.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 模块参数 `uipC` 只因为 `U`, `g₀` 所在的 [ValXP1](ValXP1.lagda.md) 带它; 下面的论证不用它.
>
> **定理 `¬Mo-u₀`.** `TU 1` 的回灌链的第 0 点 $u_0=\Omega_1\{c\mapsto U(\mathrm{gt}\,c)\}$ (`ValXGoal.u₀≡`) 不是 `MoX`: 与 `floor-block` 同一对坐标, $U$ 保不变量 `Inv`, 根的种类不变.
>
> **后果.** `crossX`, `monoX` 右边要 `MoX`. 所以比较 `TU 1` 与更高的闭项, 不能把 `inU 1` 放在右边. 本篇的 `goal` 绕开了这一点: `ValXGoal` 在根上拆开回灌链, `crossX` 只用在第 0 点的**分支** $U(\mathrm{gt}\,C)$ 上 (对每个固定的 $C$ 是 `MoX`). 要 `TU m` 单调, 须把值合法 `MoX` 也换成跨层的版本, 或再次在根上拆开.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwBase using (Cd)
open import Relation.Binary.PropositionalEquality using (_≡_)
module OCF.Lean.SameVObs (uipC : ∀ {x y : Cd} (e e′ : x ≡ y) → e ≡ e′) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁)
open import OCF.Lean.CRwFold I₁
open import OCF.Lean.ValCRel I₁ using (LeAt; MoAt)
open import OCF.Lean.ValXRel I₁
open import OCF.Lean.ValXObs I₁
open import OCF.Lean.ValXGoal using (κΩ; g₀)
open import OCF.Lean.ValXP1 uipC using (U)

Inv-mul : ∀ {W} x → Inv W x → ∀ n → Inv W (mul x n)
Inv-mul x v zero = v
Inv-mul x v (suc n) = Inv-⊞ (mul x n) x (Inv-mul x v n) v

Inv-Σ : ∀ {W} F → (∀ n → Inv W (F n)) → ∀ n → Inv W (Σ⁺ F n)
Inv-Σ F v zero = v 0
Inv-Σ F v (suc n) = Inv-⊞ (Σ⁺ F n) (F (suc n)) (Inv-Σ F v n) (v (suc n))

Inv-U : ∀ {W} b x → Inv W x → Inv W (U b x)
Inv-U b hz v = tt
Inv-U b (hs x) v = Inv-mul (U b x) (Inv-U b x v)
Inv-U b (hl f) v = Inv-Σ (λ k → U b (f k)) (λ k → Inv-U b (f k) (v k))
Inv-U b (hΩ κ g) (q , v) = q , λ e → Inv-U b (g e) (v e)

¬Mo-u₀ : ¬ MoX (hΩ κΩ g₀)
¬Mo-u₀ (mo , _) = not⊲ (has-inv (refl≤X r) (Inv-U topL (gt (hs ω₂)) (Inv-gt (hs ω₂) hself)))
  where
  r : g₀ (hs ω₁) ≤X g₀ (hs ω₂)
  r = mo (hs ω₁) (hs ω₂) (moAll (hs ω₁)) (moAll (hs ω₂)) le₁₂
```

## 结论 (按档)

- **[定理, 不用 UIP (参数只是命名空间)]** `Inv-mul`, `Inv-Σ`, `Inv-U`, **`¬Mo-u₀`**.
