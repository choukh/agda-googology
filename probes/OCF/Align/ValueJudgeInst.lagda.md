# 值判据 (三): 实例上的上下界

> **判决: HOLDS (闭合, 无假设; 上界没有标签).** 底座. 结论写在 [ValueJudge](ValueJudge.lagda.md). 实例 `HS∞`, `HS₂` 上的闭合定理. 证明的唯一性 `Uq` 在这里证, 所以 `ValueJudgeBridge` 的条件在实例上消掉了.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValueJudgeInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (≡-irrelevant)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Free.Level
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Eq using (toZ-≅; ≅ᶻ-sym)
open import OCF.Free.Force using (Goodᴺ; forceᴺ; forceᴺ-≅)
open import OCF.Align.ValueJudgeBase
open import OCF.Align.LadderNFTree using (_<ᴸ_; zero; suc)
import OCF.Align.LadderNFTree as N
import OCF.Align.LadderNFMain as NM
open import OCF.Align.LadderInfBase using (HtS)
open import OCF.Align.LadderInfTop using (HS∞; ∞; inf) renaming (H to H∞; fin to fin∞; _<∞_ to _<∞_; irrℕ to irrℕ′)
open import OCF.Align.LadderInfTop2 using (HS₂; H; fin; top; sw; _<₂_)
import OCF.Align.LadderInfBridgeTop as B∞N
import OCF.Align.ValueJudgeBridgeN as B₂N
import OCF.Align.LadderInfMain
import OCF.Align.LadderInfCert as Ce
import OCF.Align.ValueJudgeLadder
import OCF.Align.ValueJudgeBridge
module I∞ = OCF.Align.LadderInfMain HS∞
module I₂ = OCF.Align.LadderInfMain HS₂
module J∞ = OCF.Align.ValueJudgeLadder HS∞
module J₂ = OCF.Align.ValueJudgeLadder HS₂
```

## §1 高度证明唯一

`aux` 走一个索引的等式, 不用 K: `suc a ≡ suc a` 那一处用 ℕ 的 `≡-irrelevant`.

```agda
aux : ∀ {a b b′} (e : b ≡ b′) (p : a <ᴸ b) (q : a <ᴸ b′) → subst (a <ᴸ_) e p ≡ q
aux {a} e zero zero = subst (λ e′ → subst (a <ᴸ_) e′ zero ≡ zero) (≡-irrelevant refl e) refl
aux refl zero (suc q) = ⊥-elim (irrℕ′ q)
aux refl (suc p) zero = ⊥-elim (irrℕ′ p)
aux refl (suc p) (suc q) = cong suc (aux refl p q)

uipℕ : ∀ {a b} (p q : a <ᴸ b) → p ≡ q
uipℕ p q = aux refl p q

uip∞ : ∀ {a b} (p q : a <∞ b) → p ≡ q
uip∞ (OCF.Align.LadderInfTop.fin p) (OCF.Align.LadderInfTop.fin q) = cong OCF.Align.LadderInfTop.fin (uipℕ p q)
uip∞ (inf _) (inf _) = refl

uip₂ : ∀ {a b} (p q : a <₂ b) → p ≡ q
uip₂ (fin p) (fin q) = cong fin (uipℕ p q)
uip₂ (sw _ _) (sw _ _) = refl
uip₂ (top p) (top q) = cong top (uipℕ p q)

module B∞ = OCF.Align.ValueJudgeBridge HS∞ uip∞
module B₂ = OCF.Align.ValueJudgeBridge HS₂ uip₂
```

## §2 无穷高度: $T_0^\infty\prec T_1^\infty$, 后继层严格更大

`T∞ α` 就是 [LadderInfClosed](LadderInfClosed.lagda.md) 的 `T₀∞` ($\alpha=0$), `T₁∞` ($\alpha=1$): 同一个 `forceᴺ _ (G∞ α)`.

```agda
T∞ : Ordᴵ → Ordᶜ zero
T∞ = J∞.V ∞

T∞-step : ∀ α → T∞ α ≺ᵛ T∞ (suc α)
T∞-step α = ≺→s≼ (J∞.V-≺ ∞ α)

T∞-lim : ∀ f s → T∞ (lim f s) ≅ lim (λ n → T∞ (f n))
T∞-lim = J∞.V-lim ∞

T∞-mono : ∀ {a b} → a ⊑ᴵ b → T∞ a ≼ T∞ b
T∞-mono = J∞.V-≼ ∞

T∞-strict : ∀ {a b} → a ≺ᴵ b → T∞ a ≺ᵛ T∞ b
T∞-strict = J∞.V-≺≺ ∞

T₀≺T₁ : T∞ zero ≺ᵛ T∞ (suc zero)
T₀≺T₁ = T∞-step zero
```

**下界有标签.** `V (fin n) 0` 都严格在 $T_0^\infty$ 以下. 这些树与 `LadderNFTree` 的树同值 (`B∞N.bridge`), 那些树带标签 (验收在 [LadderNFAccept](LadderNFAccept.lagda.md) 的克隆世界). `T∞ 0` 是它们的上确界 (`V-chain`).

```agda
T₀-sup : T∞ zero ≈ᵛ lim (λ i → J∞.V (fin∞ i) zero)
T₀-sup = J∞.V-chain ∞ fin∞ inf refl

fin≺fin : ∀ n → J∞.V (fin∞ n) zero ≺ᵛ J∞.V (fin∞ (suc n)) zero
fin≺fin n = J∞.V-clos-≺ {fin∞ n} {fin∞ (suc n)} (OCF.Align.LadderInfTop.fin zero) refl

fin≺T₀ : ∀ n → J∞.V (fin∞ n) zero ≺ᵛ T∞ zero
fin≺T₀ n = ≼-trans (fin≺fin n) (≼-trans (≼l (suc n) (≼-refl _)) (proj₂ T₀-sup))

-- 第 1 行也在下一个高度以下
fin₁≺ : ∀ n → J∞.V (fin∞ n) (suc zero) ≺ᵛ J∞.V (fin∞ (suc n)) zero
fin₁≺ n = B∞.V₁≺ {fin∞ n} {fin∞ (suc n)} (OCF.Align.LadderInfTop.fin zero) refl
```
## §3 ω+ω: $T_1\prec T_{2\Omega}$

`T₂Ω` 是 `HS₂` 的 `V (top 1) 0`. `HS₂` 里 `top 0` 这一行的写法与 `HS∞` 的 ∞ 相同, 但类型不同. `T₀ᵀ` 与 `T₀∞` 同值是定理 (`T₀ᵀ≈T₀∞`). **`T₁ᵀ` 与 `T₁∞` 同值没有证**: 那要 `HS∞` 到 `HS₂` 的跨世界模拟, 现成的模拟都以 ℕ 为源 (`mk_inf_bridge.py`). 判断: 成立, 因为定义逐行相同.

```agda
T₀ᵀ T₁ᵀ T₂Ω : Ordᶜ zero
T₀ᵀ = J₂.V (top 0) zero
T₁ᵀ = J₂.V (top 0) (suc zero)
T₂Ω = J₂.V (top 1) zero

T₀ᵀ≺T₁ᵀ : T₀ᵀ ≺ᵛ T₁ᵀ
T₀ᵀ≺T₁ᵀ = ≺→s≼ (J₂.V-≺ (top 0) zero)

-- 上界: T₂Ω 严格高于 top 0 这一行的第 1 项
T₁ᵀ≺T₂Ω : T₁ᵀ ≺ᵛ T₂Ω
T₁ᵀ≺T₂Ω = B₂.V₁≺ {top 0} {top 1} (top zero) refl

T₀ᵀ≺T₂Ω : T₀ᵀ ≺ᵛ T₂Ω
T₀ᵀ≺T₂Ω = J₂.V-clos-≺ {top 0} {top 1} (top zero) refl

T₂Ω≺next : T₂Ω ≺ᵛ J₂.V (top 1) (suc zero)
T₂Ω≺next = ≺→s≼ (J₂.V-≺ (top 1) zero)

T₂Ω≺top₂ : T₂Ω ≺ᵛ J₂.V (top 2) zero
T₂Ω≺top₂ = J₂.V-clos-≺ {top 1} {top 2} (top zero) refl

-- 两个世界的第 0 行同值
T₀ᵀ-sup : T₀ᵀ ≈ᵛ lim (λ i → J₂.V (fin i) zero)
T₀ᵀ-sup = J₂.V-chain (top 0) fin (λ i → sw i 0) refl

fin-≈ : ∀ i → J₂.V (fin i) zero ≅ J∞.V (fin∞ i) zero
fin-≈ i = ≅-trans (≅-sym (J₂.V-G (fin i) zero G₂))
          (≅-trans (≅-sym (forceᴺ-≅ (toZ-≅ (B₂N.bridge i zero zero z≅ J₂.ev₀ zero J₂.ev₀ zero z≅)) GN G₂))
          (≅-trans (forceᴺ-≅ (toZ-≅ (B∞N.bridge i zero zero z≅ J₂.ev₀ zero J₂.ev₀ zero z≅)) GN G∞)
                   (J∞.V-G (fin∞ i) zero G∞)))
  where
  G₂ = J₂.GV (fin i) zero
  G∞ = J∞.GV (fin∞ i) zero
  GN = NM.GᴺTᵠ i zero J₂.ev₀ zero

T₀ᵀ≈T₀∞ : T₀ᵀ ≈ᵛ T∞ zero
T₀ᵀ≈T₀∞ = ≼-trans (proj₁ T₀ᵀ-sup) (≼-trans (l≼ (λ i → ≼l i (≅→≼ (fin-≈ i)))) (proj₂ T₀-sup)) ,
          ≼-trans (proj₁ T₀-sup) (≼-trans (l≼ (λ i → ≼l i (≅→≼ (≅-sym (fin-≈ i))))) (proj₂ T₀ᵀ-sup))

-- 带标签的 T₀∞ 严格在 T₂Ω 以下: 跨世界
T₀∞≺T₂Ω : T∞ zero ≺ᵛ T₂Ω
T₀∞≺T₂Ω = ≼-≺ (proj₂ T₀ᵀ≈T₀∞) T₀ᵀ≺T₂Ω
```

## §4 接到 `LadderInfClosed` 的闭项

[LadderInfClosed](LadderInfClosed.lagda.md) 定义 `T₀∞ = forceᴺ _ (G∞ zero)`, `T₁∞ = forceᴺ _ (G∞ (suc zero))`, `T₂Ω = forceᴺ _ (G₂ 1 zero)`. 下面直接写这些右边: 写 `C.T₀∞` 会让检查器去展开证书, 6G 内存不够 (`forceᴺ` 要算证书的范式). 这是检查器的代价, 内容相同.

```agda
closed-T₀ : forceᴺ _ (Ce.G∞ zero) ≅ T∞ zero
closed-T₀ = J∞.V-G′ ∞ zero Ce.ev₀ (Ce.G∞ zero)

closed-T₁ : forceᴺ _ (Ce.G∞ (suc zero)) ≅ T∞ (suc zero)
closed-T₁ = J∞.V-G′ ∞ (suc zero) Ce.ev₀ (Ce.G∞ (suc zero))

closed-T₂Ω : forceᴺ _ (Ce.G₂ 1 zero) ≅ T₂Ω
closed-T₂Ω = J₂.V-G′ (top 1) zero Ce.ev₀ (Ce.G₂ 1 zero)

T₀∞≺T₁∞ : forceᴺ _ (Ce.G∞ zero) ≺ᵛ forceᴺ _ (Ce.G∞ (suc zero))
T₀∞≺T₁∞ = ≼-trans (s≼s (≅→≼ closed-T₀)) (≼-trans T₀≺T₁ (≅→≼ (≅-sym closed-T₁)))

T₀∞≺T₂Ω′ : forceᴺ _ (Ce.G∞ zero) ≺ᵛ forceᴺ _ (Ce.G₂ 1 zero)
T₀∞≺T₂Ω′ = ≼-trans (s≼s (≅→≼ closed-T₀)) (≼-trans T₀∞≺T₂Ω (≅→≼ (≅-sym closed-T₂Ω)))
```
