# 甲脚手架：所有 Ω 视图的零起步码链

S1 的闭包接线。树上 ψ 的跨层链从零起步，现成 `tow` 从 Ων 起步；
正规结点可错位接线，奇异结点未必可以。本篇直接对零起步链证明
标准形及 `GB` 不变量，处理一切 Ω 视图，不按 Ω 塔阶段新增前提。
这仍是码层定理；没有把码链当作树上实际运行的对应证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaChain where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import OCF.Align.EboLeanDef using (T; ψ; Ωt; Ωs; _<ᵀ_; []<; hd<; ar<; fsT)
open import OCF.Align.EBO using (<-sucT)
open import OCF.Align.EboLeanBase
  using (NF; n[]; nf-ψ; nf-hd; nfp-a; nfp-g;
         _≤ᵀ_; ≤-trans′; ≤-<; <-≤; GB; GB[]; G-mono; gp; gh; gw; gc; gtl)
open import OCF.Align.EboLean3Base using (Ω≤)
open import OCF.Align.EboLeanView
  using (VΩ; fΩ; fΩ-eq; fΩ-mono; nf-ν)
open import OCF.Align.EboLeanOmega using (NFΩ)
open import OCF.Align.EboLeanTrian using (Gtri; TΩ)
open import OCF.Align.EboLeanClosure using (hZ0)
open import OCF.Align.JiaAuditClosure using (fromZero; singular; normal-a)

chain : ∀ {B ν} → VΩ B ν → ℕ → T
chain w zero = []
chain {ν = ν} w (suc n) = ψ ν (fΩ w (chain w n)) ∷ []

chain-below : ∀ {B ν} (w : VΩ B ν) n → chain w n <ᵀ Ωs ν
chain-below w zero = []<
chain-below {ν = ν} w (suc n) = hd< (OCF.Align.EboLeanDef.lv< (<-sucT ν))

chain-increasing : ∀ {B ν} (w : VΩ B ν) n → chain w n <ᵀ chain w (suc n)
chain-increasing w zero = []<
chain-increasing w (suc n) = hd< (ar< (fΩ-mono w (chain-increasing w n)))

branch-increasing : ∀ {B ν} (w : VΩ B ν) n →
  fΩ w (chain w n) <ᵀ fΩ w (chain w (suc n))
branch-increasing w n = fΩ-mono w (chain-increasing w n)

fΩ-≤ : ∀ {B ν} (w : VΩ B ν) {x y} → x ≤ᵀ y → fΩ w x ≤ᵀ fΩ w y
fΩ-≤ w (inj₁ p) = inj₁ (fΩ-mono w p)
fΩ-≤ w (inj₂ refl) = inj₂ refl

floor-after-first : ∀ {B ν} (w : VΩ B ν) n → Ωt ν ≤ᵀ chain w (suc n)
floor-after-first {ν = ν} w n = Ω≤ ν (fΩ w (chain w n)) []

chain≡ : ∀ {B ν} (w : VΩ B ν) n → chain w n ≡ fromZero B ν n
chain≡ w zero = refl
chain≡ {ν = ν} w (suc n) = cong (λ x → ψ ν x ∷ [])
  (trans (cong (fΩ w) (chain≡ w n)) (sym (fΩ-eq w _)))
```

## 同一条不变量，含零初项

`GB A x y` 表示码 x 中由阈值 A 可见的参数都小于 y。
父折叠码的标准形同时给这条不变量的起点与递推所需的界；
这比只要求父输入码标准形强，不能省略。

```agda
zero-tower : ∀ {A B ν} → NF (ψ A B ∷ []) → (w : VΩ B ν) → A ≤ᵀ ν →
  ∀ n → NF (chain w n) × GB A (chain w n) (fΩ w (chain w n))
zero-tower n w l zero = n[] , GB[]
zero-tower {A} {B} {ν} n w l (suc k) =
  nf-ψ (nf-ν nB w) (NFΩ nB w (proj₁ ih) (chain-below w k)) (hGY ν l) , guard
  where
  nB = nfp-a (nf-hd n)
  ih = zero-tower n w l k
  hGY : ∀ u′ → A ≤ᵀ u′ → GB u′ (fΩ w (chain w k)) (fΩ w (chain w k))
  hGY u′ m = Gtri (TΩ w (chain-below w k))
    (λ i → nfp-g (nf-hd n) (G-mono m i))
    (λ i → proj₂ ih (G-mono m i))
  guard : GB A (chain w (suc k)) (fΩ w (chain w (suc k)))
  guard (gp (gh _)) = branch-increasing w k
  guard (gp (gw _ i)) = <-≤
    (hZ0 n w (≤-trans′ l (inj₁ (<-sucT ν))) i)
    (fΩ-≤ w (floor-after-first w k))
  guard (gp (gc _ i)) = ≤-< (inj₁ (hGY A (inj₂ refl) i)) (branch-increasing w k)
  guard (gtl ())

zero-chain-normal : ∀ {A B ν} → NF (ψ A B ∷ []) → (w : VΩ B ν) → A ≤ᵀ ν →
  ∀ n → NF (fromZero B ν n)
zero-chain-normal n w l k = subst NF (chain≡ w k) (proj₁ (zero-tower n w l k))
```

零初项本身低于 Ων，但第一步起总不低于 Ων；这正好补上现成
`hZ0` 所需的地板，而无需假定分支在零处仍为零。
