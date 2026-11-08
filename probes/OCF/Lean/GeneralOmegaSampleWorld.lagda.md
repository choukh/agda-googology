# 全LH实际编码的统一世界

每个后继新界取本层原地板加同一完成反馈的纯树嵌入；并层逐分量
递归。原code正好落在该种类的最大界，故不需坐标判等或单槽更新。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaSampleWorld where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecFl using (flL; Lg-flL)
open import OCF.Lean.HigherIndexConsumeCode using (pure)
open import OCF.Lean.GeneralOmegaConsumeIf using (code)
open import OCF.Lean.GeneralOmegaSampleIf

pure-position : ∀ S {a b} {w : Wd S} → a ⊲ b → pure S a ⊲[ w ] pure S b
pure-position S hself = hself
pure-position S (hsuc p) = hsuc (pure-position S p)
pure-position S (hlim n p) = hlim n (pure-position S p)
pure-position S (hLim {κ = ()} e p)
pure-legal : ∀ S a → LgB a → LgB (pure S a)
pure-legal S hz l = tt
pure-legal S (hs a) l = pure-legal S a l
pure-legal S (hl f) (s , l) = (λ n → pure-position S (s n)) , (λ n → pure-legal S (f n) (l n))
pure-legal S (hΩ () f) l

bound : ∀ x → Cd → HB (Lv x)
bound x d = flL x ⊞ pure (Lv x) (leg d)
bound-legal : ∀ x d → LgB (bound x d)
bound-legal x d = Lg-⊞ (flL x) _ (Lg-flL x) (pure-legal (Lv x) (leg d) (Lg-leg d))
bound-position : ∀ x {d e} {w : Wd (Lv x)} → leg d ⊲ leg e → bound x d ⊲[ w ] bound x e
bound-position x p = ⊞-⊲ (flL x) (pure-position (Lv x) p)

World : ∀ x → Cd → Wd (Lv x)
World lz d = tt
World (ls x) d = World x d , bound x d
World (ll f) d = λ n → World (f n) d
World (lΩ k f) d (inj₁ _) = World k d , bound k d
World (lΩ k f) d (inj₂ a) = World (f a) d
legal : ∀ x d → LgW (Lv x) (World x d)
legal lz d = tt
legal (ls x) d = legal x d , bound-legal x d
legal (ll f) d = λ n → legal (f n) d
legal (lΩ k f) d (inj₁ _) = legal k d , bound-legal k d
legal (lΩ k f) d (inj₂ a) = legal (f a) d

admitted : ∀ x κ d → Bd (Lv x) κ (code x κ d) (World x d)
admitted lz () d
admitted (ls x) (inj₁ κ) d = admitted x κ d
admitted (ls x) (inj₂ _) d = hself
admitted (ll f) (n , κ) d = admitted (f n) κ d
admitted (lΩ k f) (inj₁ _ , inj₁ κ) d = admitted k κ d
admitted (lΩ k f) (inj₁ _ , inj₂ _) d = hself
admitted (lΩ k f) (inj₂ a , κ) d = admitted (f a) κ d

growth : ∀ x {d e} → leg d ⊲ leg e → _≤w_ (Lv x) (World x d) (World x e)
growth lz p = tt
growth (ls x) p = growth x p , bound-position x p
growth (ll f) p = λ n → growth (f n) p
growth (lΩ k f) p (inj₁ _) = growth k p , bound-position k p
growth (lΩ k f) p (inj₂ a) = growth (f a) p

position : ∀ x κ {d e} → leg d ⊲ leg e →
  Pr (Lv x) κ (World x e) (code x κ d) (code x κ e)
position lz () p
position (ls x) (inj₁ κ) p = position x κ p
position (ls x) (inj₂ _) p = bound-position x p
position (ll f) (n , κ) p = position (f n) κ p
position (lΩ k f) (inj₁ _ , inj₁ κ) p = position k κ p
position (lΩ k f) (inj₁ _ , inj₂ _) p = bound-position k p
position (lΩ k f) (inj₂ a , κ) p = position (f a) κ p

instance-worlds : SampleWorlds
instance-worlds = record
  { World = World ; legal = legal ; admitted = admitted ; growth = growth
  ; pair = λ x κ {d} {e} p → Bd↑ (Lv x) (growth x p) (admitted x κ d) ,
      admitted x κ e , position x κ p }
```

World对任意raw反馈合法，已覆盖原全部code而非有限测试。它证明准入
与坐标第一位置，不证明源分支的所有前驱被run访问，更不证明run单调。
