# Third 全种类合法化：共享接口与富累加

本实验不改变原 Third。沿 `LHRecLeg.Ctx` 保留低层种类；后继额外加入
原坐标的分支，使 `g d` 在 `hs d` 的输出中出现。这里不声明值不缩，
也不改变旧折叠、世界或地板。坐标比较仅在同一个投影世界下进行。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ThirdRichLegIf where

open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecLeg using (Ctx; ek; frC; pw; lgpw; bdTo; bdFr; prFr; frto)

module New {T U : KS} (c : Ctx T (step U)) (g : HB U → HB T) where
  θ : HB U → HB T
  θ hz = g hz
  θ (hs d) = (θ d ⊞ g d) ⊞ g (hs d)
  θ (hl f) = hl (λ n → θ (f n))
  θ (hΩ κ h) = hΩ (ek c (inj₁ κ)) (λ e → θ (h (frC c (inj₁ κ) e)))

  θ-⊲ : ∀ {W d d′} → d ⊲[ proj₁ (pw c W) ] d′ → θ d ⊲[ W ] θ d′
  θ-⊲ hself = hself
  θ-⊲ {d′ = hs d} (hsuc p) = ⊲ᴮ-tr (θ-⊲ p)
    (⊲ᴮ-tr (⊞-fst (θ d) (g d)) (⊞-fst (θ d ⊞ g d) (g (hs d))))
  θ-⊲ (hlim n p) = hlim n (θ-⊲ p)
  θ-⊲ {W} (hLim {κ = κ} {g = h} {c = e} b p) =
    hLim (bdTo c (inj₁ κ) b)
      (subst (λ z → _ ⊲[ W ] θ (h z)) (sym (frto c (inj₁ κ) e)) (θ-⊲ p))

  Lg-θ : (∀ d → LgB (g d)) → ∀ d → LgB d → LgB (θ d)
  Lg-θ lg hz l = lg hz
  Lg-θ lg (hs d) l = Lg-⊞ _ _ (Lg-⊞ _ _ (Lg-θ lg d l) (lg d)) (lg (hs d))
  Lg-θ lg (hl f) (st , l) = (λ {W} n → θ-⊲ {W} (st n)) , (λ n → Lg-θ lg (f n) (l n))
  Lg-θ lg (hΩ κ h) (mo , l) =
    (λ {W} lw b b′ p → θ-⊲ {W} (mo (proj₁ (lgpw c lw)) (bdFr c (inj₁ κ) b) (bdFr c (inj₁ κ) b′) (prFr c (inj₁ κ) p))) ,
    (λ {W} lw b → Lg-θ lg _ (l (proj₁ (lgpw c lw)) (bdFr c (inj₁ κ) b)))

record AllKinds (S : KS) : Set₁ where
  field
    θK : ∀ {T} (c : Ctx T S) (κ : K S) → (E S κ → HB T) → E S κ → HB T
    position : ∀ {T} (c : Ctx T S) κ g {W d d′} → Pr S κ (pw c W) d d′ →
      θK c κ g d ⊲[ W ] θK c κ g d′
    legal : ∀ {T} (c : Ctx T S) κ g → (∀ d → LgB (g d)) →
      ∀ {W d} → LgW T W → Bd S κ d (pw c W) → LgB (θK c κ g d)
```

`AllKinds` 只记录合法化所需的局部律，不单独验收算法；实际实例须沿
每一种类找到其原 `step`，调用上述同一 `New.θ`，不得以常值分支填记录。
全部律保留同一 `W`；不增加裸坐标比较或任意世界的相干性。
