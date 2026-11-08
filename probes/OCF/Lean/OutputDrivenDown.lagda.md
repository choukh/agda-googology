# 任意实际合法底世界族上的完整下降

继承 ThirdTm 的逐底算法与泛 Q 路径证明，移除其固定世界实例的限制。
本篇的参数由后续输出驱动世界族实填；每站读取该世界的实际界，
富合法化只用于原跨底算法的回灌界。没有在下降途中插入合法化。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.OutputDrivenDown where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to Amap)
open import Data.List.Relation.Unary.All.Properties using (map⁻)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdTw using (Sb; fl; gtX; topT; Ix; FX)
open import OCF.Lean.ThirdPS
open import OCF.Lean.OutputDrivenTop using (topS; topS-bd)
import OCF.Lean.ThirdFold as TF
import OCF.Lean.ThirdSan as San
import OCF.Lean.ThirdX as Cross
import OCF.Lean.ThirdRichLegBuild as Rich
import OCF.Lean.OutputDrivenBuild as Whole

module With (worlds : ∀ n → Wd (Sb n))
  (legal : ∀ n → LgW (Sb n) (worlds n)) where

  module St (n : ℕ) where
    U = Sb n
    w = worlds n
    lw = legal n
    open San U w lw (fl n) public using (Er; gd-z; module Ph)
    module X = Cross U w lw Er (Rich.legS n) (Rich.Lg-legS n)
      (topS n w) (topS-bd n w)
    open X public using (PoU; PSX; ΦX; Sh-ΦX; module Down)
    open TF U w lw public using (_⊲ᵘ_; Gd; GT)

  -- 原全地板的自己的路径由已实填的整源构造复用。
  own-path : ∀ n B → hs hz ⊲[ worlds n ] B → PH (St.PSX n) B (fl (suc n))
  own-path n = Whole.Whole.source-path (Sb n) (worlds n) (legal n) (fl n)
    (Rich.legS n) (Rich.Lg-legS n) (topS n (worlds n)) (topS-bd n (worlds n))

  -- 此证明对全部 Q，不要求把一个世界的 QL 偷搬到另一个世界。
  lifted-floor : ∀ n {P : Po} (Q : PS P (Sb n)) y B →
    PH (lift Q) B (gtX (Sb n) (fl n) y)
  lifted-floor n Q hz B = tt
  lifted-floor n Q (hs c) B = PH-⊞ (lift Q)
    (gtX (Sb n) (fl n) c) (ι {Ix (Sb n)} {FX (Sb n)} (inj₂ c) (topT (Sb n) (fl n) (hs c)))
    (lifted-floor n Q c B)
    (PH-ι (FQ Q) (inj₂ c) (topT (Sb n) (fl n) (hs c))
      (tt , λ e a → PH-up (PSL Q c) e (proj₂ (proj₂ a))))
  lifted-floor n Q (hl f) B = λ k → lifted-floor n Q (f k) B
  lifted-floor n Q (hΩ κ g) B = tt , λ e _ → lifted-floor n Q (g e) B

  record Qs (n : ℕ) : Set₁ where
    field
      P : Po
      Q : PS P (Sb (suc n))
      O : Po.W P → Set
      o↑ : ∀ {a b} → Po._≤_ P a b → O a → O b
      W₀ : Po.W P
      oW₀ : O W₀
      ptl : ∀ B → O B → PH Q B (fl (suc n))
  open Qs

  own : ∀ n → Qs n
  own n = record { P = St.PoU n ; Q = St.PSX n
    ; O = λ B → hs hz ⊲[ worlds n ] B ; o↑ = λ q o → ⊲ᴮ-tr o q
    ; W₀ = hs hz ; oW₀ = hself ; ptl = own-path n }

  liftE : ∀ {n} → Qs n → Qs (suc n)
  liftE {n} q = record { P = P q ; Q = lift (Q q) ; O = O q ; o↑ = o↑ q
    ; W₀ = W₀ q ; oW₀ = oW₀ q
    ; ptl = λ B o → tt , λ y _ → lifted-floor (suc n) (Q q) y B }

  QL : ∀ n → List (Qs n)
  QL zero = own zero ∷ []
  QL (suc n) = own (suc n) ∷ map liftE (QL n)

  Gdn : ∀ n → HB (Sb (suc n)) → Set₁
  Gdn n h = All (λ q → PH (Q q) (W₀ q) h) (QL n)

  seed : ∀ n → St.GT n hz
  seed n = fl n , St.gd-z n (fl n)

  stp : ∀ n (h : HB (Sb (suc n))) → PH (St.PSX n) (hs hz) h → HB (Sb n)
  stp n h p = proj₁ (St.ΦX n hz (hs hz) tt (hsuc hself) (seed n) h p)

  downward : ∀ n (h : HB (Sb (suc (suc n)))) (p : PH (St.PSX (suc n)) (hs hz) h) →
    All (λ q → PH (lift (Q q)) (W₀ q) h) (QL n) → Gdn n (stp (suc n) h p)
  downward n h p = Amap (λ {q} pq →
    let open St (suc n)
        module Pq = Ph (Q q) (O q) (ptl q)
        module D = Down (Q q) (O q) (o↑ q) Pq.ph-san Pq.ph-tp
    in D.PH-ΦX↓ hz (hs hz) tt (hsuc hself) (seed (suc n)) h p
      (W₀ q) (oW₀ q) (ptl q (W₀ q) (oW₀ q)) pq)

  desc : ∀ n (h : HB (Sb (suc n))) → Gdn n h → Cd
  desc zero h (p ∷ []) = stp zero h p
  desc (suc n) h (p ∷ ps) = desc n (stp (suc n) h p) (downward n h p (map⁻ ps))

  module F0 = TF.F (Sb zero) (worlds zero) (legal zero) (St.Er zero)

  shape-desc : ∀ n h g → F0.Sh (desc n h g)
  shape-desc zero h (p ∷ []) = St.Sh-ΦX zero hz (hs hz) tt (hsuc hself) (seed zero) h p
  shape-desc (suc n) h (p ∷ ps) = shape-desc n _ _

  shape-legal : ∀ (h : Cd) → F0.Sh h → LgB h
  shape-legal hz p = tt
  shape-legal (hs h) p = shape-legal h p
  shape-legal (hl f) (st , p) = (λ n → st n) , (λ n → shape-legal (f n) (p n))
  shape-legal (hΩ () _) p

  every : ∀ {A : Set₁} {R : A → Set} → (∀ x → R x) → ∀ xs → All R xs
  every f [] = []
  every f (x ∷ xs) = f x ∷ every f xs

  floor-path : ∀ n → Gdn n (fl (suc n))
  floor-path n = every (λ q → ptl q (W₀ q) (oW₀ q)) (QL n)

  TN : ℕ → Cd
  TN n = desc n (fl (suc n)) (floor-path n)

  legal-TN : ∀ n → LgB (TN n)
  legal-TN n = shape-legal _ (shape-desc n (fl (suc n)) (floor-path n))
```

世界族只需实际合法；没有额外相干性、世界自反公理或高层比较字段。
这提供完整下降，不给输出值界，也不声称原 San 的损失已经去除。
