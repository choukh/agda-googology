# 单层 `nκ` (二): 前 $n$ 格拼成一个区间和

> 不含记号. 入口 [KValK](KValK.lagda.md). 一边的 `nκ u` (树世界 $V$, 在世界 $W$ 里从状态 $Y$ 走) 在目标第 0 层的输出是 $\lim_n$ 前 $n$ 格之和. 第 $n$ 格在世界 $v_n$ 里走区间 $[a_n,v_n)$. 本文证:
>
> - **`cl`**: 前 $n$ 格之和与把**一棵树** `Pre n` 从 `cv Y` 走一次值相同 (两个方向), 第 $n$ 格起步的状态与 `cv Y ⊕ (Pre n 的输出)` 值相同 (两个方向). `Pre n` 是前 $n$ 个区间和依次相接 (`Pre (n+1) = nw (Pre n ⨾ P n)`, `P n = Cut u [a_n, v_n)`). 每一步用: 一格 = 一个区间和 (`KValKWalk`), 跨世界的自比 (`snd-lo`, 一边在 $v_n$, 一边在 $v_{n+1}$), 换世界不改值 (`cv≤`, `≤cv`).
> - **`PreCut`**: `Pre n` 与一个区间和 `Cut u [V, a_n)` 相关 (两个方向), 纯树侧, 用 `T` 与 `PI`.
> - `vpt`, `ptv`: 第 $n$ 格的层 $v_n$ 与 $\ell+$ 前 $n$ 格之和值相同, $\ell=W+z$.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KValKIter where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; ≤l; l≤; ≤-refl; ≤-trans)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; nw; sum; pt; cnt; Cut; tailP; drp)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KValTree
open import OCF.Align.KValSem
open import OCF.Align.KValSound
open import OCF.Align.KValCut using (_≈ᵏ_; module One)
import OCF.Align.KValKWalk as KW
```

## §1 一边的回灌

```agda
module It (s : Sd) (o : Ok s s) {V : A} (u : Bk V) (mono : KMono u) (q : V ⊲ W s) (w : D one (W s)) (Y : F.St (W s)) (cY : CohY Y) where
  module O = One u mono

  K : ℕ → F.Cl (W s) V (cnt one)
  K n = F.κc ac₁ u q (lW s) (ll s) (act s) w Y n

  side : ℕ → Sd
  side n = lift s (F.wv (K n)) (F.lv (K n))

  okn : ∀ n m → Ok (side n) (side m)
  okn n m = ok↾ o (F.wv (K n)) (F.wv (K m)) (F.lv (K n)) (F.lv (K m))

  κn : ∀ n → C.Tg azero (F.v (K n))
  κn n = inj₁ (κ₀ (ll (side n)))

  Δ : ∀ n → F.Df (F.v (K n))
  Δ n = F.κΔ ac₁ u (ll s) (act s) (K n)

  d₀ : ∀ n → D azero (F.v (K n))
  d₀ n = F.yc (Δ n) (inj₁ (z⊲ (F.v (K n)))) tt

  dκ : ℕ → D azero (W s)
  dκ n = drp (d₀ n)

  Y⁰ : ∀ n → F.St (F.v (K n))
  Y⁰ n = F.cv (F.wv (K n)) (F.lv (K n)) Y

  P : ∀ n → D one (F.v (K n))
  P n = Cut u (F.v (K n)) (F.av (K n)) (F.ap (K n)) (F.lv (K n)) C.self

  Pre : ∀ n → D one (F.v (K n))
  Pre zero = n0
  Pre (suc n) = nw (F.av (K (suc n))) (Pre n ⨾ P n)

  RP : ∀ n → F.Df (F.v (K n))
  RP n = Rn (side n) (Pre n) C.self n0 (Y⁰ n)

  -- 第 n+1 个 Pre 在世界 v_{n+1} 里分两段走
  RPre′ : ∀ n → F.Df (F.v (K (suc n)))
  RPre′ n = Rn (side (suc n)) (Pre n) (F.av (K (suc n))) n0 (Y⁰ (suc n))

  RP′ : ∀ n → F.Df (F.v (K (suc n)))
  RP′ n = Rn (side (suc n)) (P n) (F.av (K (suc n))) (n0 ⨾ nw (F.av (K (suc n))) (Pre n)) (Y⁰ (suc n) F.⊕ RPre′ n)
```

## §2 判据与一致

```agda
  rfP : ∀ n → Rfᵏ lo (P n)
  rfP n = O.CutRf _ _ _ _ _

  rfPre : ∀ n → Rfᵏ lo (Pre n)
  rfPre zero = n0⊑
  rfPre (suc n) = nwˡ (nwʳ (⨾⊑ (rfPre n) (rfP n)))

  cohY⁰ : ∀ n → CohY (Y⁰ n)
  cohY⁰ n = cohCv Y (F.wv (K n)) (F.lv (K n)) cY

  cvv : ∀ n m → vY (side n) (Y⁰ n) ≤ vY (side m) (Y⁰ m)
  cvv n m = ≤-trans (cv≤ Y (F.wv (K n)) (F.lv (K n)) cY (inj₁ (κ₀ (ll (side n)))) (inj₁ (κ₀ (ll s))))
                    (≤cv Y (F.wv (K m)) (F.lv (K m)) cY (inj₁ (κ₀ (ll s))) (inj₁ (κ₀ (ll (side m)))))

  cohSv : ∀ n → CohY (F.Sv (K n))
  cohΔ : ∀ n → CohD (Δ n)
  cohSv zero = cohCv Y _ _ cY
  cohSv (suc n) = cohCv (F.Sv (K n) F.⊕ Δ n) _ _ (coh⊕ (cohSv n) (cohΔ n))
  cohΔ n = KW.W.cohW u mono (side n) (okn n n) _ (F.av (K n)) (F.ap (K n)) (F.lv (K n)) C.self (F.co (K n)) (F.Sv (K n)) (cohSv n)

  -- 读回灌层的路径 z⊲ v 换到规范路径, 再去掉 drp
  conv⁺ : ∀ n b b′ → b ≤ b′ → sum b (dκ n) ≤ sum b′ (F.yc (Δ n) (κn n) tt)
  conv⁺ n b b′ h = ≤-trans (drp≤ (d₀ n) h) (cdA (cohΔ n) (inj₁ (z⊲ (F.v (K n)))) (κn n) b′)

  conv⁻ : ∀ n b b′ → b ≤ b′ → sum b (F.yc (Δ n) (κn n) tt) ≤ sum b′ (dκ n)
  conv⁻ n b b′ h = ≤-trans (cdA (cohΔ n) (κn n) (inj₁ (z⊲ (F.v (K n)))) b) (≤drp (d₀ n) h)
```

## §3 两个世界之间的一步

```agda
  PC⁺ : ∀ n b b′ → b ≤ b′ → sum b (F.yc (RP n) (κn n) tt) ≤ sum b′ (F.yc (RPre′ n) (κn (suc n)) tt)
  PC⁺ n = snd-lo (rfPre n) (side n) (side (suc n)) (okn n (suc n)) C.self (F.av (K (suc n))) n0 n0 (Y⁰ n) (Y⁰ (suc n))
                 (cx (cohY⁰ n) (cohY⁰ (suc n)) (cvv n (suc n)) tt)

  PC⁻ : ∀ n b b′ → b ≤ b′ → sum b (F.yc (RPre′ n) (κn (suc n)) tt) ≤ sum b′ (F.yc (RP n) (κn n) tt)
  PC⁻ n = snd-lo (rfPre n) (side (suc n)) (side n) (okn (suc n) n) (F.av (K (suc n))) C.self n0 n0 (Y⁰ (suc n)) (Y⁰ n)
                 (cx (cohY⁰ (suc n)) (cohY⁰ n) (cvv (suc n) n) tt)

  cohR′ : ∀ n → CohY (Y⁰ (suc n) F.⊕ RPre′ n)
  cohR′ n = cR₁ (side (suc n)) (c0 (okn (suc n) (suc n))) (Pre n) (F.av (K (suc n))) n0 (Y⁰ (suc n)) (cohY⁰ (suc n))

  Wk⁺ : ∀ n → vY (side n) (F.Sv (K n)) ≤ vY (side (suc n)) (Y⁰ (suc n) F.⊕ RPre′ n) →
        ∀ b b′ → b ≤ b′ → sum b (F.yc (Δ n) (κn n) tt) ≤ sum b′ (F.yc (RP′ n) (κn (suc n)) tt)
  Wk⁺ n U b b′ h =
    ≤-trans (KW.W.WCf u mono (side n) (okn n n) _ (F.av (K n)) (F.ap (K n)) (F.lv (K n)) C.self (F.co (K n)) n0 (F.Sv (K n)) (F.Sv (K n))
                      (cx-refl lo _ _ (cohSv n)) b b (≤-refl b))
            (snd-lo (rfP n) (side n) (side (suc n)) (okn n (suc n)) C.self (F.av (K (suc n))) n0 _ (F.Sv (K n)) _
                    (cx (cohSv n) (cohR′ n) U tt) b b′ h)

  Wk⁻ : ∀ n → vY (side (suc n)) (Y⁰ (suc n) F.⊕ RPre′ n) ≤ vY (side n) (F.Sv (K n)) →
        ∀ b b′ → b ≤ b′ → sum b (F.yc (RP′ n) (κn (suc n)) tt) ≤ sum b′ (F.yc (Δ n) (κn n) tt)
  Wk⁻ n U b b′ h =
    ≤-trans (snd-lo (rfP n) (side (suc n)) (side n) (okn (suc n) n) (F.av (K (suc n))) C.self _ n0 _ (F.Sv (K n))
                    (cx (cohR′ n) (cohSv n) U tt) b b′ h)
            (KW.W.WCb u mono (side n) (okn n n) _ (F.av (K n)) (F.ap (K n)) (F.lv (K n)) C.self (F.co (K n)) n0 (F.Sv (K n)) (F.Sv (K n))
                      (cx-refl lo _ _ (cohSv n)) b′ b′ (≤-refl b′))
```

## §4 归纳: 前 $n$ 格就是 `Pre n`

```agda
  Cl : ℕ → Set
  Cl n = (∀ c c′ → c ≤ c′ → pt c dκ n ≤ sum c′ (F.yc (RP n) (κn n) tt)) ×
         ((∀ c c′ → c ≤ c′ → sum c (F.yc (RP n) (κn n) tt) ≤ pt c′ dκ n) ×
          ((vY (side n) (F.Sv (K n)) ≤ vY (side n) (Y⁰ n F.⊕ RP n)) ×
           (vY (side n) (Y⁰ n F.⊕ RP n) ≤ vY (side n) (F.Sv (K n)))))

  cl : ∀ n → Cl n
  cl zero = (λ c c′ h → h) , ((λ c c′ h → h) , (≤-refl _ , ≤-refl _))
  cl (suc n) = E⁺ , (E⁻ , (S⁺ , S⁻))
    where
    IH = cl n
    U⁺ : vY (side n) (F.Sv (K n)) ≤ vY (side (suc n)) (Y⁰ (suc n) F.⊕ RPre′ n)
    U⁺ = ≤-trans (proj₁ (proj₂ (proj₂ IH))) (PC⁺ n _ _ (cvv n (suc n)))
    U⁻ : vY (side (suc n)) (Y⁰ (suc n) F.⊕ RPre′ n) ≤ vY (side n) (F.Sv (K n))
    U⁻ = ≤-trans (PC⁻ n _ _ (cvv (suc n) n)) (proj₂ (proj₂ (proj₂ IH)))
    E⁺ : ∀ c c′ → c ≤ c′ → pt c dκ (suc n) ≤ sum c′ (F.yc (RP (suc n)) (κn (suc n)) tt)
    E⁺ c c′ h = ≤-trans (conv⁺ n _ _ (≤-refl _)) (Wk⁺ n U⁺ _ _ (≤-trans (proj₁ IH c c (≤-refl c)) (PC⁺ n c c′ h)))
    E⁻ : ∀ c c′ → c ≤ c′ → sum c (F.yc (RP (suc n)) (κn (suc n)) tt) ≤ pt c′ dκ (suc n)
    E⁻ c c′ h = ≤-trans (Wk⁻ n U⁻ _ _ (≤-trans (PC⁻ n c c (≤-refl c)) (proj₁ (proj₂ IH) c c′ h))) (conv⁻ n _ _ (≤-refl _))
    S⁺ : vY (side (suc n)) (F.Sv (K (suc n))) ≤ vY (side (suc n)) (Y⁰ (suc n) F.⊕ RP (suc n))
    S⁺ = ≤-trans (cv≤ (F.Sv (K n) F.⊕ Δ n) (F.av (K (suc n))) (F.lv (K (suc n))) (coh⊕ (cohSv n) (cohΔ n))
                      (inj₁ (κ₀ (ll (side (suc n))))) (κn n))
                 (Wk⁺ n U⁺ _ _ U⁺)
    S⁻ : vY (side (suc n)) (Y⁰ (suc n) F.⊕ RP (suc n)) ≤ vY (side (suc n)) (F.Sv (K (suc n)))
    S⁻ = ≤-trans (Wk⁻ n U⁻ _ _ U⁻)
                 (≤cv (F.Sv (K n) F.⊕ Δ n) (F.av (K (suc n))) (F.lv (K (suc n))) (coh⊕ (cohSv n) (cohΔ n))
                      (κn n) (inj₁ (κ₀ (ll (side (suc n))))))
```

## §5 层与和

```agda
  ℓ : A
  ℓ = sum (W s) (F.z Y)

  vpt : ∀ n → F.v (K n) ≤ pt ℓ dκ n
  ptv : ∀ n → pt ℓ dκ n ≤ F.v (K n)
  vpt zero = ≤-refl _
  vpt (suc n) = ≤drp (d₀ n) (vpt n)
  ptv zero = ≤-refl _
  ptv (suc n) = drp≤ (d₀ n) (ptv n)
```

## §6 树侧: `Pre n` 是一个区间和

```agda
  CutA : ∀ n → D one (F.v (K n))
  CutA n = Cut u (F.a (K n)) (F.ap (K n)) C.self (lg⊲ (F.av (K n)) (F.lv (K n))) (F.av (K n))

  PreCut : ∀ n → Pre n ≈ᵏ CutA n
  PreCut zero = n0⊑ , n0⊑
  PreCut (suc n) =
    nwˡ (trʳ (⨾⊑ (trˡ (proj₁ IH) (proj₁ PI₁)) (proj₁ PI₂)) (proj₂ Tn)) ,
    trˡ (proj₁ Tn) (nwʳ (⨾⊑ (trʳ (proj₂ PI₁) (proj₂ IH)) (proj₂ PI₂)))
    where
    IH = PreCut n
    av₊ = F.av (K (suc n))
    L₊ = lg⊲ av₊ (F.lv (K (suc n)))
    Tn = O.T (F.ap (K n)) (F.av (K n)) C.self L₊ av₊
    PI₁ = O.PI (F.a (K n)) (F.ap (K n)) (F.ap (K n)) C.self C.self (lg⊲ (F.av (K n)) (F.lv (K n))) (lg⊲ (F.av (K n)) L₊)
               (F.av (K n)) (⊲-tr (F.av (K n)) av₊)
    PI₂ = O.PI (F.v (K n)) (F.av (K n)) (F.av (K n)) (F.ap (K n)) (⊲-tr C.self (F.ap (K n))) (F.lv (K n)) L₊ C.self av₊
```
