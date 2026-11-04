# 跨段 (二): 树沿上移一致

> 入口 [CrossM](CrossM.lagda.md). **判决: HOLDS (编译过, 无条件).** 对一切 $M$, $N$, 位置 $p$, $\alpha$:
>
> - `up-sim e`: `Tᵖ M p α ≈ᴿ Tᵖ M′ (up e p) α′`, $\alpha\cong\alpha'$, 对一切 `e : M ⊂ M′`.
> - `up-≅`, `up-fgh`: 计值 $\cong$, FGH 逐点相等.
> - `up-lvl`: 读回的层号 $\cong$.
> - `up≺`, `step≺`: `Tᵖ M p 0` 的计值严格低于 $M'$ 上任何高于 `up e p` 的位置. 字面的 $\prec$. 比较发生在 $M'$ 这一个世界里, 它就是字面公共上界.
>
> 只用 [CrossMUp](CrossMUp.lagda.md) 的 `rowq` 和 [CrossMSim](CrossMSim.lagda.md) 的 `bridge`; 对 $M$, $M'$ 一致, 不分阶段. 右边写成 `Gᵖ` 的字面形式: 见 [CrossMInst](CrossMInst.lagda.md) 的说明.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CrossMUpTree where

open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Free.Level hiding (up)
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Eq using (z≅; toZ-≅; _≈ᴿ_)
open import OCF.Free.Force using (forceᴺ; forceᴺ-≅; forceᴺ-HS)
open import OCF.Free.Class using (lvG)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode using (_ᶜ+_)
open import OCF.Align.LadderOrdCert using (ev₀; Tᵖ; Gᵖ; growᵖ)
open import OCF.Align.CrossMUp
import OCF.Align.CrossMSim

module Sm {M M′ : Code} (e : M ⊂ M′) where
  open UpWorld e using (𝔸; 𝔹; u; ε; rowq)
  open OCF.Align.CrossMSim 𝔸 𝔹 u ε <ᴾ-tri-self rowq public using (bridge)

up-sim : ∀ {M M′} (e : M ⊂ M′) (p : Pos (cs M)) α α′ → α ≅ᴵ α′ → Tᵖ M p α ≈ᴿ Tᵖ M′ (up e p) α′
up-sim e = Sm.bridge e

Tv : ∀ M → Pos (cs M) → Ordᴵ → Ordᶜ zero
Tv M p α = forceᴺ _ (Gᵖ M p α)

up-≅ : ∀ {M M′} (e : M ⊂ M′) (p : Pos (cs M)) α → forceᴺ _ (Gᵖ M p α) ≅ forceᴺ _ (Gᵖ M′ (up e p) α)
up-≅ e p α = forceᴺ-≅ (toZ-≅ (up-sim e p α α (≅ᴵ-refl α) ev₀ zero ev₀ zero z≅)) _ _

up-fgh : ∀ {M M′} (e : M ⊂ M′) (p : Pos (cs M)) α n → FGH (forceᴺ _ (Gᵖ M p α)) n ≡ FGH (forceᴺ _ (Gᵖ M′ (up e p) α)) n
up-fgh e p α = FGH-≅ (up-≅ e p α)

up-lvl : ∀ {M M′} (e : M ⊂ M′) (p : Pos (cs M)) α → lvG (Gᵖ M p α) ≅ᴵ lvG (Gᵖ M′ (up e p) α)
up-lvl e p α = toLevel-≅ (forceᴺ-HS _ _) (forceᴺ-HS _ _) (up-≅ e p α)

≺-≅ˡ : ∀ {ℓ₁ ℓ₂ ℓ₃} {c : Ordᶜ ℓ₁} {c′ : Ordᶜ ℓ₃} {a : Ordᶜ ℓ₂} → c′ ≅ c → c ≺ a → c′ ≺ a
≺-≅ˡ e (≺z e₀) = ≺z (≅-trans e e₀)
≺-≅ˡ e (≺s h) = ≺s (≺-≅ˡ e h)
≺-≅ˡ e (≺l n h) = ≺l n (≺-≅ˡ e h)
≺-≅ˡ e (≺i x ex h) = ≺i x ex (≺-≅ˡ e h)
≺-≅ˡ e (≺u h) = ≺u (≺-≅ˡ e h)

-- 跨段的严格增长: 比较在字面公共上界 M′ 里做
up≺ : ∀ {M M′} (e : M ⊂ M′) (p : Pos (cs M)) (m : Pos (cs M′)) → up e p <ᴾ m → forceᴺ _ (Gᵖ M p zero) ≺ forceᴺ _ (Gᵖ M′ m zero)
up≺ {M} {M′} e p m r = ≺-≅ˡ (up-≅ e p zero) (growᵖ M′ {up e p} {m} r)

step≺ : ∀ M N → forceᴺ _ (Gᵖ M end zero) ≺ forceᴺ _ (Gᵖ (M ᶜ+ cs N) end zero)
step≺ M N = up≺ (⊂+ M (cs N)) end end tt
```
