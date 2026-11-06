# 嵌套 `nκ` (五): 单个 `nκ` 的一步归结为一格

> 不含记号. 入口 [KNest2](KNest2.lagda.md). 接 [KNestSound](KNestSound.lagda.md) 的 `KStepᴬ`, 加一条前提 (两边树世界可比, `V ≤ V′ ⊎ V′ ≤ V`), 记作 `KStep²`.
>
> **定理** (`kstep : CellStep → KStep²`): 只要**一格**的比较 `CellStep` 成立, 单个 `nκ` 的一步就成立. `CellStep` 的格是 "左边沿 $a\lhd W$ 在世界 $W$ 里走, 右边沿 $a'\lhd W'$ 在 $W'$ 里走", 前提是:
>
> - 两边状态的上下文 `Cxᴵ` (值可比, 单边不变量, 路径一致), 左边进格时回灌层不超过格世界 ($\ell\le W$);
> - 区间 $[a,W)$ 放得进 $[a',W')$ (`Adm a a′ W W′`), 两个起点可比, 格世界 $W\le W'$.
>
> 结论是两格在第 0 层的输出 (路径 `z⊲ W`) 对一切底 $e\le e'$ 可比.
>
> 证明对格号 $n$ 归纳, 每一格都满足这些前提:
>
> - **第 0 格.** 起点是两边的树世界 $V$, $V'$ (`κc zero`), 格世界是回灌层 $\ell$, $\ell'$. Adm 由支配 $\mathrm{Adm}(V,V';\alpha,\alpha')$ 与上下文的 $\mathrm{Adm}(\alpha,\alpha';\ell,\ell')$ 复合 (`adm-tr`). 起点可比是新前提. $\ell\le\ell'$ 由 `hℓ-inv`.
> - **第 $n+1$ 格.** 起点是上一格的格世界 $v_n\le v'_n$, 格世界是 $v_n+d_n$, $v'_n+d'_n$. 由上一格的输出可比得 $V_0(d_n)\le V_0(d'_n)$, 于是 Adm 取 $\delta=V_0(d_n)$, 起点取 `inj₁`.
> - **状态.** `Cxᴵ` 经 `cv` 推进 (`cv≤`, `≤cv`, 单边不变量 `invU-cv`/`invL-cv`, 路径一致 `cohW`), 值的比较用上一格的输出在 `κ₀` 路径上可比 (由路径一致从 `z⊲` 换过去).
>
> 部分和逐格累加, 极限由 `l≤`/`≤l`. 这里**没有**对齐问题: 对齐全在一格之内 (`CellStep`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KNest2Glue where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤; _⊞_; ⊞-mono)
open import OCF.Align.SumOneTree using (D; nκ; cnt; sum; pt; sum-fst; drp)
import OCF.Align.SumOneClosed as F
open import OCF.Align.BrwMidZero using (sum-toA)
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KValTree using (Bk; V0)
open import OCF.Align.KValSem using (CohY; CohD; CohA; cdA; coh⊕; cohCv; cohA↾; cv≤; ≤cv; ac₁; κ₀; sbase; smono; toV0; drp≤; ≤drp)
open import OCF.Align.KValSound using (Sd; W; lW; ll; act; Ok; c0; c1; lift; ok↾; vY)
open import OCF.Align.KNestInv using (ℓ; InvU; InvL; invU⊕; invL⊕; invU-cv; invL-cv; cohW; hℓ-inv; Cxᴵ; cxᴵ; b; b′; b≤; iU; iL; cLᴵ; cRᴵ; vleᴵ)
open import OCF.Align.KNestAdm using (Adm; adm-tr)
open import OCF.Align.KNestSound using (Cxᴬ; cxᴬ; OutLeᴬ; SX)
```

## §1 一格与一步

```agda
d0 : ∀ {W} → F.Df W → D azero W
d0 {W} Δ = F.yc Δ (inj₁ (z⊲ W)) tt

-- 一格: 沿 a ⊲ W s 在世界 W s 里走 (格世界就是区间的终点)
Wk : ∀ {V} (u : Bk V) (s : Sd) {a} (p : a ⊲ W s) (ap : V ⊲ a) → D one (W s) → F.St (W s) → F.Df (W s)
Wk u s p ap co Y = F.Walk ac₁ u (W s) p ap (lW s) C.self (lW s) (ll s) (act s) co Y

CellStep : Set
CellStep = ∀ {V V′} {u : Bk V} {u′ : Bk V′} → SX u u → SX u′ u′ → SX u u′ →
           ∀ (s s′ : Sd) → Ok s s′ → ∀ {a a′} (p : a ⊲ W s) (p′ : a′ ⊲ W s′) (ap : V ⊲ a) (ap′ : V′ ⊲ a′) co co′ Y Y′ →
           Cxᴵ s s′ Y Y′ → ℓ Y ≤ W s → Adm a a′ (W s) (W s′) → (a ≤ a′ ⊎ a′ ≤ a) → W s ≤ W s′ →
           ∀ e e′ → e ≤ e′ → sum e (d0 (Wk u s p ap co Y)) ≤ sum e′ (d0 (Wk u′ s′ p′ ap′ co′ Y′))

KStep² : Set
KStep² = ∀ {α α′ V V′ zz zz′} {u : Bk V} {u′ : Bk V′} → Adm V V′ α α′ → (V ≤ V′ ⊎ V′ ≤ V) →
         SX u u → SX u′ u′ → SX u u′ → OutLeᴬ α α′ (nκ zz u) (nκ zz′ u′)
```

## §2 一边的格

```agda
module Side {V} (u : Bk V) (s : Sd) (cA : CohA (act s)) (q : V ⊲ W s) (w : D one (W s)) (Y : F.St (W s)) (cY : CohY Y) where
  cl : ℕ → F.Cl (W s) V (cnt one)
  cl = F.κc ac₁ u q (lW s) (ll s) (act s) w Y

  side : ℕ → Sd
  side n = lift s (F.wv (cl n)) (F.lv (cl n))

  Δ : ∀ n → F.Df (F.v (cl n))
  Δ n = F.κΔ ac₁ u (ll s) (act s) (cl n)

  dn : ∀ n → D azero (F.v (cl n))
  dn n = d0 (Δ n)

  cohS : ∀ n → CohY (F.Sv (cl n))
  cohΔ : ∀ n → CohD (Δ n)
  cohS zero = cohCv Y _ _ cY
  cohS (suc n) = cohCv (F.Sv (cl n) F.⊕ Δ n) _ _ (coh⊕ (cohS n) (cohΔ n))
  cohΔ n = cohW u (F.v (cl n)) (F.av (cl n)) (F.ap (cl n)) (F.lv (cl n)) C.self (F.lv (cl n)) (⊲-tr (ll s) (F.wv (cl n)))
                (F.Ig↾ (F.wv (cl n)) (act s)) (F.co (cl n)) (F.Sv (cl n)) (cohA↾ (F.wv (cl n)) cA) (cohS n)

  ℓv : ∀ n → ℓ (F.Sv (cl n)) ≤ F.v (cl n)
  ℓv zero = ≤-refl _
  ℓv (suc n) = ≤-refl _

  invU : ∀ {b₀} → InvU b₀ Y → ∀ n → InvU b₀ (F.Sv (cl n))
  invU h zero = invU-cv Y _ _ cY (≤-refl _) h
  invU h (suc n) =
    invU-cv (F.Sv (cl n) F.⊕ Δ n) _ _ (coh⊕ (cohS n) (cohΔ n)) (sbase (dn n) (⊲→≤ (sum-fst (F.v (cl n)) (F.z (F.Sv (cl n))))))
            (invU⊕ (Δ n) (invU h n))

  invL : ∀ {b₀} → InvL b₀ Y → ∀ n → InvL b₀ (F.Sv (cl n))
  invL h zero = invL-cv Y _ _ cY (≤-refl _) h
  invL h (suc n) = invL-cv (F.Sv (cl n) F.⊕ Δ n) _ _ (coh⊕ (cohS n) (cohΔ n)) (sbase (dn n) (ℓv n)) (invL⊕ (Δ n) (invL h n))

  -- 一格的输出在规范路径与回灌路径上可比
  κL : ∀ n e → sum e (F.yc (Δ n) (inj₁ (κ₀ (ll (side n)))) tt) ≤ sum e (dn n)
  κL n e = cdA (cohΔ n) _ _ e
  κR : ∀ n e → sum e (dn n) ≤ sum e (F.yc (Δ n) (inj₁ (κ₀ (ll (side n)))) tt)
  κR n e = cdA (cohΔ n) _ _ e
```

## §3 归纳

```agda
kstep : CellStep → KStep²
kstep cs {α} {α′} {V} {V′} {zz} {zz′} {u} {u′} dom cmp mu mu′ cr s s′ o q q′ w w′ Y Y′ (cxᴬ ci ad) c c′ cb =
  l≤ (λ n → ≤l n (proj₁ (go n) c c′ cb))
  where
  module L = Side u s (c0 o) q w Y (cLᴵ ci)
  module R = Side u′ s′ (c1 o) q′ w′ Y′ (cRᴵ ci)

  DL : ℕ → D azero (W s)
  DL n = drp (L.dn n)
  DR : ℕ → D azero (W s′)
  DR n = drp (R.dn n)

  St : ℕ → Set
  St n = Cxᴵ (L.side n) (R.side n) (F.Sv (L.cl n)) (F.Sv (R.cl n)) ×
         Adm (F.a (L.cl n)) (F.a (R.cl n)) (F.v (L.cl n)) (F.v (R.cl n)) ×
         ((F.a (L.cl n) ≤ F.a (R.cl n)) ⊎ (F.a (R.cl n) ≤ F.a (L.cl n))) ×
         (F.v (L.cl n) ≤ F.v (R.cl n))

  CC : ∀ n → St n → ∀ e e′ → e ≤ e′ → sum e (L.dn n) ≤ sum e′ (R.dn n)
  CC n (k , ad′ , md , vl) =
    cs mu mu′ cr (L.side n) (R.side n) (ok↾ o (F.wv (L.cl n)) (F.wv (R.cl n)) (F.lv (L.cl n)) (F.lv (R.cl n)))
       (F.av (L.cl n)) (F.av (R.cl n)) (F.ap (L.cl n)) (F.ap (R.cl n)) (F.co (L.cl n)) (F.co (R.cl n)) (F.Sv (L.cl n)) (F.Sv (R.cl n))
       k (L.ℓv n) ad′ md vl

  st0 : St zero
  st0 = cxᴵ (b ci) (b′ ci) (b≤ ci) (L.invU (iU ci) zero) (R.invL (iL ci) zero) (L.cohS zero) (R.cohS zero) vv ,
        adm-tr dom ad , cmp , hℓ-inv s s′ (b≤ ci) (iU ci) (iL ci) (cLᴵ ci) (cRᴵ ci) (vleᴵ ci)
    where
    vv = ≤-trans (cv≤ Y _ _ (cLᴵ ci) _ (inj₁ (κ₀ (ll s)))) (≤-trans (vleᴵ ci) (≤cv Y′ _ _ (cRᴵ ci) (inj₁ (κ₀ (ll s′))) _))

  stS : ∀ n → St n → St (suc n)
  stS n st@(k , ad′ , md , vl) =
    cxᴵ (b ci) (b′ ci) (b≤ ci) (L.invU (iU ci) (suc n)) (R.invL (iL ci) (suc n)) (L.cohS (suc n)) (R.cohS (suc n)) vv ,
    (V0 (L.dn n) , proj₁ (sum-toA (F.v (L.cl n)) (L.dn n)) , ≤-trans (⊞-mono (≤-refl _) V0≤) (proj₂ (sum-toA (F.v (R.cl n)) (R.dn n)))) ,
    inj₁ vl ,
    smono {x = L.dn n} {x′ = R.dn n} vl V0≤
    where
    H = CC n st
    V0≤ : V0 (L.dn n) ≤ V0 (R.dn n)
    V0≤ = toV0 (L.dn n) (R.dn n) (H azero azero z≤)
    Hκ : ∀ e e′ → e ≤ e′ → sum e (F.yc (L.Δ n) (inj₁ (κ₀ (ll (L.side n)))) tt) ≤ sum e′ (F.yc (R.Δ n) (inj₁ (κ₀ (ll (R.side n)))) tt)
    Hκ e e′ h = ≤-trans (L.κL n e) (≤-trans (H e e′ h) (R.κR n e′))
    vv = ≤-trans (cv≤ (F.Sv (L.cl n) F.⊕ L.Δ n) _ _ (coh⊕ (L.cohS n) (L.cohΔ n)) _ (inj₁ (κ₀ (ll (L.side n)))))
         (≤-trans (Hκ _ _ (vleᴵ k))
                  (≤cv (F.Sv (R.cl n) F.⊕ R.Δ n) _ _ (coh⊕ (R.cohS n) (R.cohΔ n)) (inj₁ (κ₀ (ll (R.side n)))) _))

  go : ∀ n → (∀ e e′ → e ≤ e′ → pt e DL n ≤ pt e′ DR n) × St n
  go zero = (λ e e′ h → h) , st0
  go (suc n) =
    let (P , st) = go n
    in (λ e e′ h → ≤-trans (drp≤ (L.dn n) (≤-refl _)) (≤-trans (CC n st _ _ (P e e′ h)) (≤drp (R.dn n) (≤-refl _)))) ,
       stS n st
```
