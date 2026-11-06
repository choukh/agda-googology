# 一族关系, 结构版 (二): `StrRel` 的两层关系接进核

> 不含记号. 入口 [MonoPort4](MonoPort4.lagda.md). 实例 $\Lambda=2$, 世界 $W$. 观测取 `StrRelDef` 的 `Obs`: $T_0$ 上 $\sqsubseteq_0$, $T_1$ 上 $\sqsubseteq_1$. 它满足核的全部输出律与 `PreLaw` (`O₂`, `pre₂`), **不要 `LimLaw`**; $T_0$ 分量就是 $\sqsubseteq_0$ (`proj₀ = proj₁`). 于是 [MonoPort4Zero](MonoPort4Zero.lagda.md) 的 `snd₀ᴳ` 在这里就是 `StrRelZero.snd₀` 的两动作版 (`snd₀²`), `chain₀ᴳ` 是第 1 层节点上升的链.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
module OCF.Align.MonoPort4Inst2 {W : A} (lW : Lg W) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import OCF.Align.HtFeedTree using (D; hz; hs; n0; _⨾_; nl)
open import OCF.Align.StrRelDef lW
import OCF.Align.MonoPort3Gen as Gen
import OCF.Align.MonoPort4Zero as Z
module G = Gen Λ₂ tt lW k0

O₂ : G.OutLaws
O₂ = record
  { _≼_ = λ Δ Δ′ → (o₀ Δ ⊑₀ o₀ Δ′) × (o₁ Δ ⊑₁ o₁ Δ′)
  ; L0 = z0 , n0⊑
  ; L⨾ = λ a a′ h k → sq (proj₁ h) (proj₁ k) , ⨾⊑ (proj₂ a) (proj₂ a′) (proj₂ h) (proj₂ k)
  ; Lnl = λ r r′ h → lm (λ n → proj₁ (h n)) , nl⊑ (λ n → proj₂ (r n)) (λ n → proj₂ (r′ n)) (λ n → proj₂ (h n))
  ; Ltr = λ h k → tr (proj₁ h) (proj₁ k) , tr (proj₂ h) (proj₂ k)
  ; Lu0ˡ = λ h → u0l (proj₁ h) , u0ˡ (proj₂ h)
  ; Lu0ʳ = λ h → u0r (proj₁ h) , u0ʳ (proj₂ h)
  ; Lu1ˡ = λ h → u1l (proj₁ h) , u1ˡ (proj₂ h)
  ; Lu1ʳ = λ h → u1r (proj₁ h) , u1ʳ (proj₂ h)
  ; Lasˡ = λ a b c h → al (proj₁ h) , asˡ (proj₂ a) (proj₂ b) (proj₂ c) (proj₂ h)
  ; Lasˡ′ = λ a b c h → al′ (proj₁ h) , asˡ′ (proj₂ a) (proj₂ b) (proj₂ c) (proj₂ h)
  ; Lasʳ = λ a b c h → ar (proj₁ h) , asʳ (proj₂ a) (proj₂ b) (proj₂ c) (proj₂ h)
  ; Lasʳ′ = λ a b c h → ar′ (proj₁ h) , asʳ′ (proj₂ a) (proj₂ b) (proj₂ c) (proj₂ h)
  }

-- 核的部分和在两个目标上的读数, 字面就是 StrRelDef 的部分和
o₀pre : ∀ (F : ℕ → P.Df W) k → o₀ (G.preᴰ F k) ≡ preL (λ n → o₀ (F n)) k
o₀pre F zero = refl
o₀pre F (suc k) = cong (λ t → t ⨾ o₀ (F k)) (o₀pre F k)

o₁pre : ∀ (F : ℕ → P.Df W) k → o₁ (G.preᴰ F k) ≡ preL (λ n → o₁ (F n)) k
o₁pre F zero = refl
o₁pre F (suc k) = cong (λ t → t ⨾ o₁ (F k)) (o₁pre F k)

pre₂ : G.PreLaw O₂
pre₂ {a} {a′} {F} {F′} ra ra′ rF rF′ h hF k =
  subst (λ t → (o₀ a ⨾ t) ⊑₀ (o₀ a′ ⨾ nl (λ n → o₀ (F′ n)))) (sym (o₀pre F k)) (pr (proj₁ h) (λ n → proj₁ (hF n)) k) ,
  subst (λ t → (o₁ a ⨾ t) ⊑₁ (o₁ a′ ⨾ nl (λ n → o₁ (F′ n)))) (sym (o₁pre F k))
        (pre⊑ (proj₂ ra) (proj₂ ra′) (λ n → proj₂ (rF n)) (λ n → proj₂ (rF′ n)) (proj₂ h) (λ n → proj₂ (hF n)) k)

module R = Z.R0 Λ₂ tt lW k0 O₂ pre₂ proj₁

snd₀² : ∀ {V₁ V₂} {x : D hz V₁} {x′ : D hz V₂} → x ⊑₀ x′ → R.Sem₀ x x′
snd₀² = R.snd₀ᴳ
```
