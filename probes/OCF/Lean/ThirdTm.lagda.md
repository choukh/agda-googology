# Third (七): 世界塔, 下降, 闭项, 证书, FGH

> 不含记号. 入口 [Third](Third.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 闭项, 证书, FGH 无模块参数.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ThirdTm where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to Amap)
open import Data.List.Relation.Unary.All.Properties using (map⁻)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (FGH)
open import OCF.Lean.ThirdIf
open import OCF.Lean.ThirdTw
open import OCF.Lean.ThirdPS
open import OCF.Lean.ThirdLeg
import OCF.Lean.ThirdFold as TF
import OCF.Lean.ThirdSan as TS
import OCF.Lean.ThirdX as TX
```

## §1 每一站的实例

```agda
module Cn (c₀ : Cd) (lc₀ : LgB c₀) where
  open W c₀ lc₀

  module St (n : ℕ) where
    open TS (Sb n) (wS n) (lwS n) (fl n) public using (Er; Gd-up; gd-z; module Ph)
    module X = TX (Sb n) (wS n) (lwS n) Er (legS n) (Lg-legS n) (pkS n) (pk-bd n)
    open X public using (PoU; PSX; ΦX; Sh-ΦX; module Down)
    open TF (Sb n) (wS n) (lwS n) public using (_⊲ᵘ_; Gd; GT; AdT)
```

## §2 地板带路径

自己的结构: 第 $c$ 个分量里的树带 `Gd (hs c)`, 世界在 $c+1$ 之上; 地板的分支 $y$ 进入世界 $y+1$, 坐标的 $\Omega$-结点走 `Bd` 证据 (`hLim`). 上抬的结构: 指标分量平凡, 一切坐标都带路径.

```agda
  module Fl (n : ℕ) where
    open St n
    U = Sb n
    FU = FX U

    PH-cp : ∀ c W → hs c ⊲ᵘ W → ∀ x → Gd (hs c) x → PH PSX W (ι {Ix U} {FU} (inj₂ c) x)
    PH-cp c W q hz p = tt
    PH-cp c W q (hs x) p = PH-cp c W q x p
    PH-cp c W q (hl f) p = λ k → PH-cp c W q (f k) (p k)
    PH-cp c W q (hΩ κ g) (pos , pg) = (q , pos) , λ e a → PH-cp c W q (g e) (pg e a)

    gdT : ∀ c → Gd (hs c) (topT U (fl n) (hs c))
    gdT c = tt , λ e a → Gd-up c e a

    PH-gt : ∀ y W → y ⊲ᵘ W → PH PSX W (gtX U (fl n) y)
    PH-gt hz W q = tt
    PH-gt (hs c) W q = PH-⊞ PSX (gtX U (fl n) c) (ι {Ix U} {FU} (inj₂ c) (topT U (fl n) (hs c)))
      (PH-gt c W (⊲ᴮ-tr {U} (hsuc hself) q)) (PH-cp c W q _ (gdT c))
    PH-gt (hl f) W q = λ k → PH-gt (f k) W (⊲ᴮ-tr {U} (hlim k hself) q)
    PH-gt (hΩ κ h) W q = tt , λ e a → PH-gt (h e) W (⊲ᴮ-tr {U} (hLim a hself) q)

    PH-fl : ∀ B → hs hz ⊲ᵘ B → PH PSX B (fl (suc n))
    PH-fl B o = o , λ y a → PH-gt y (hs y) (hsuc hself)

    module _ {P : Po} (Q : PS P U) where
      PH-gtL : ∀ y W → PH (lift Q) W (gtX U (fl n) y)
      PH-gtL hz W = tt
      PH-gtL (hs c) W = PH-⊞ (lift Q) (gtX U (fl n) c) (ι {Ix U} {FU} (inj₂ c) (topT U (fl n) (hs c))) (PH-gtL c W)
        (PH-ι (FQ Q) (inj₂ c) (topT U (fl n) (hs c)) (tt , λ e a → PH-up (PSL Q c) e (proj₂ (proj₂ a))))
      PH-gtL (hl f) W = λ k → PH-gtL (f k) W
      PH-gtL (hΩ κ h) W = tt , λ e _ → PH-gtL (h e) W
```

## §3 世界塔与下降

```agda
  record Qs (n : ℕ) : Set₁ where
    field
      P   : Po
      Q   : PS P (Sb (suc n))
      O   : Po.W P → Set
      o↑  : ∀ {a b} → Po._≤_ P a b → O a → O b
      W₀  : Po.W P
      oW₀ : O W₀
      ptl : ∀ B → O B → PH Q B (fl (suc n))
  open Qs

  own : ∀ n → Qs n
  own n = record { P = PoU ; Q = PSX ; O = λ B → hs hz ⊲ᵘ B ; o↑ = λ q o → ⊲ᴮ-tr {Sb n} o q
                 ; W₀ = hs hz ; oW₀ = hself ; ptl = Fl.PH-fl n }
    where open St n

  liftE : ∀ {n} → Qs n → Qs (suc n)
  liftE {n} q = record { P = P q ; Q = lift (Q q) ; O = O q ; o↑ = o↑ q ; W₀ = W₀ q ; oW₀ = oW₀ q
                       ; ptl = λ B o → tt , λ y _ → Fl.PH-gtL (suc n) (Q q) y B }

  QL : ∀ n → List (Qs n)
  QL zero = own 0 ∷ []
  QL (suc n) = own (suc n) ∷ map liftE (QL n)

  Gdn : ∀ n → HB (Sb (suc n)) → Set₁
  Gdn n h = All (λ q → PH (Q q) (W₀ q) h) (QL n)

  -- 第 n 站: 目标第 0 层, 界 1, 当前界是第 n 个底的地板
  b₀ : ∀ n → St.GT n hz
  b₀ n = fl n , St.gd-z n (fl n)

  stp : ∀ n (h : HB (Sb (suc n))) → PH (St.PSX n) (hs hz) h → HB (Sb n)
  stp n h p = proj₁ (St.ΦX n hz (hs hz) tt (hsuc hself) (b₀ n) h p)

  ↓Gd : ∀ n (h : HB (Sb (suc (suc n)))) (p : PH (St.PSX (suc n)) (hs hz) h) →
        All (λ q → PH (lift (Q q)) (W₀ q) h) (QL n) → Gdn n (stp (suc n) h p)
  ↓Gd n h p = Amap (λ {q} pq →
    let open St (suc n)
        module Pq = Ph (Q q) (O q) (ptl q)
        module D = Down (Q q) (O q) (o↑ q) Pq.ph-san Pq.ph-tp
    in D.PH-ΦX↓ hz (hs hz) tt (hsuc hself) (b₀ (suc n)) h p (W₀ q) (oW₀ q) (ptl q (W₀ q) (oW₀ q)) pq)

  desc : ∀ n (h : HB (Sb (suc n))) → Gdn n h → Cd
  desc zero h (p ∷ []) = stp 0 h p
  desc (suc n) h (p ∷ ps) = desc n (stp (suc n) h p) (↓Gd n h p (map⁻ ps))

  module F0 = TF.F (Sb 0) (wS 0) (lwS 0) (St.Er 0)

  Sh-desc : ∀ n h g → F0.Sh (desc n h g)
  Sh-desc zero h (p ∷ []) = St.Sh-ΦX 0 hz (hs hz) tt (hsuc hself) (b₀ 0) h p
  Sh-desc (suc n) h (p ∷ ps) = Sh-desc n _ _

  sh→lg : ∀ (h : Cd) → F0.Sh h → LgB h
  sh→lg hz s = tt
  sh→lg (hs h) s = sh→lg h s
  sh→lg (hl f) (st , s) = (λ {w} n → st {w} n) , (λ n → sh→lg (f n) (s n))
  sh→lg (hΩ () _) s
```

## §4 闭项, 证书, FGH

`TN n`: 第 $n+1$ 个底的地板一路下降到可数树. `TΛ`: 对 $n$ 的累加对角.

```agda
  every : ∀ {A : Set₁} {R : A → Set} → (∀ x → R x) → ∀ xs → All R xs
  every f [] = []
  every f (x ∷ xs) = f x ∷ every f xs

  gd-fl : ∀ n → Gdn n (fl (suc n))
  gd-fl n = every (λ q → ptl q (W₀ q) (oW₀ q)) (QL n)

  TN : ℕ → Cd
  TN n = desc n (fl (suc n)) (gd-fl n)

  LgB-TN : ∀ n → LgB (TN n)
  LgB-TN n = sh→lg _ (Sh-desc n (fl (suc n)) (gd-fl n))
```

**闭项.** 对角: $y_0=0$, $y_{k+1}=y_k\boxplus$ `TN` $(y_k+1)$ $k$: 第 $k$ 项用第 $k+1$ 个底, 世界的第 $0$ 层的界是上一项加一 (折叠输出回灌作下标).

```agda
yΛ : ℕ → Cd
lg-yΛ : ∀ k → LgB (yΛ k)
yΛ zero = hz
yΛ (suc k) = yΛ k ⊞ Cn.TN (hs (yΛ k)) (lg-yΛ k) k
lg-yΛ zero = tt
lg-yΛ (suc k) = Lg-⊞ (yΛ k) (Cn.TN (hs (yΛ k)) (lg-yΛ k) k) (lg-yΛ k) (Cn.LgB-TN (hs (yΛ k)) (lg-yΛ k) k)

TΛ : Cd
TΛ = hl yΛ

LgB-TΛ : LgB TΛ
LgB-TΛ = (λ k → ⊞-fst (yΛ k) (Cn.TN (hs (yΛ k)) (lg-yΛ k) k)) , lg-yΛ

fghΛ : ℕ → ℕ
fghΛ = FGH TΛ
```
