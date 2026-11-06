# 两种种类的单调 (六): 第 ≥1 层的上升链

> 入口 [TpPort](TpPort.lagda.md). 不含记号. **生成文件**: 由 `probes/Survey/scripts/tpport/mk_tpport.py` 从 [MonoPort5Chn](MonoPort5Chn.lagda.md) 逐字节可重生成 (公共变换在同目录的 `tpgen.py`). 公共变换只改: 世界的类型与序 (`A`, `_⊲_` 换成两种种类的 `Wd₂`, `_≤ʷ_`; `C.self`, `C.⊲-tr` 换成 `≤rf`, `≤tr`; `Lg` 换成 `LgW₂`), 高度的类型 (`H` 换成 `Ht`, `LgH` 换成 `LgB`, `hΩ g` 换成 `hΩ κ g`), 模块参数多一个 `oΛ` (第 1 层是实例在一切世界里的第一位置, 两种种类的折叠要它), 数据树多一个构造子 `nμ` (每个 `nκ` 的空子句后加一句), `Step` 换名 `Stp`. 证明逐句不变. 
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`, 不改树、折叠、合法性.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.HtTowerTy using (HB; hz; hs; _⊲[_]_; LgB)
open import OCF.Align.HtTowerFTree using (Ht; Wd₂; LgW₂; AccY; D)
import OCF.Align.TpPortGen as Gen
module OCF.Align.TpPortChn (Λ : Ht) (lΛ : LgB Λ) (oΛ : ∀ {w} → hs hz ⊲[ w ] Λ) {W : Wd₂} (lW : LgW₂ W) (t₀ : hz ⊲[ W ] Λ)
  (O : Gen.OutLaws Λ lΛ oΛ lW t₀) (ly : Ht) (ac : AccY ly) (ll : ly ⊲[ W ] Λ)
  (Cx₀ In₀ : D ly W → D ly W → Set) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤l; l≤; ≤-refl)
open import OCF.Align.HtTowerFTree using (n0; _⨾_; nl; sum; pt; ≤rf) renaming (_≤_ to _≤ʷ_)

open Gen Λ lΛ oΛ lW t₀ using (module P; o₀; module Core)

module K = Core O ly ac ll ⊤ (λ _ → W) (λ _ → ⊤) (λ _ → ≤rf) Cx₀ (λ x x′ → In₀ x x′)
open K

Tl : P.Tg W ly W
Tl = P.tg ≤rf ll lW

module Chain (cl : CxLaws) (Pt : D ly W → D ly W → Set)
  (sndP : ∀ {x x′} → Pt x x′ → ∀ (Aᵢ Aⱼ : Act) → HA Aᵢ Aᵢ → HA Aⱼ Aⱼ → HA Aᵢ Aⱼ → Sem Aᵢ Aⱼ {tt} {tt} x x′)
  (prj : ∀ {Δ Δ′} → Δ ≼ Δ′ → Pt (P.yc Δ Tl) (P.yc Δ′ Tl))
  (cxn : Cx n0 n0)
  (cxc : ∀ {c c′ δ δ′} → Cx c c′ → Pt δ δ′ → Pt δ δ → Pt δ′ δ′ → Cx (c ⨾ δ) (c′ ⨾ δ′))
  (Aᵢ Aⱼ : Act) (hi : HA Aᵢ Aᵢ) (hj : HA Aⱼ Aⱼ) (hij : HA Aᵢ Aⱼ) where
  open CxLaws cl

  CC : Act → P.St W → ℕ → D ly W × (D ly W × P.St W)
  CC A₂ Y = P.Chn ac ll lW A₂ Y

  outs : Act → P.St W → ℕ → P.Df W
  outs A₂ Y n = Run A₂ (proj₁ (proj₂ (CC A₂ Y n))) tt (proj₁ (CC A₂ Y n)) (proj₂ (proj₂ (CC A₂ Y n)))

  chainG : ∀ (Y Y′ : P.St W) b b′ → Good Y → Good Y′ → SRel Y Y′ → b ≤ b′ →
           (sum b (nl (λ n → o₀ (outs Aᵢ Y n))) ≤ sum b′ (nl (λ n → o₀ (outs Aⱼ Y′ n)))) × (∀ n → outs Aᵢ Y n ≼ outs Aⱼ Y′ n)
  chainG Y Y′ b b′ g g′ s cb =
    l≤ (λ n → ≤l n (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (go n))))))))) , (λ n → proj₂ (h n azero azero z≤))
    where
    c  = λ n → proj₁ (CC Aᵢ Y n)
    c′ = λ n → proj₁ (CC Aⱼ Y′ n)
    δ  = λ n → proj₁ (proj₂ (CC Aᵢ Y n))
    δ′ = λ n → proj₁ (proj₂ (CC Aⱼ Y′ n))
    Yn  = λ n → proj₂ (proj₂ (CC Aᵢ Y n))
    Yn′ = λ n → proj₂ (proj₂ (CC Aⱼ Y′ n))
    sg  = λ n → o₀ (outs Aᵢ Y n)
    sg′ = λ n → o₀ (outs Aⱼ Y′ n)
    go : ∀ n → Cx (c n) (c′ n) × (Pt (δ n) (δ′ n) × (Pt (δ n) (δ n) × (Pt (δ′ n) (δ′ n) ×
               (Good (Yn n) × (Good (Yn′ n) × (SRel (Yn n) (Yn′ n) × (pt b sg n ≤ pt b′ sg′ n)))))))
    h : ∀ n e₁ e₂ → e₁ ≤ e₂ → Obs e₁ e₂ (outs Aᵢ Y n) (outs Aⱼ Y′ n)
    h n e₁ e₂ eb = let (cc , (pd , (_ , (_ , (gy , (gy′ , (sy , _))))))) = go n in
      sndP pd Aᵢ Aⱼ hi hj hij tt tt (c n) (c′ n) e₁ e₂ (Yn n) (Yn′ n) cc gy gy′ sy eb
    go zero = cxn , (prj (proj₂ s) , (prj g , (prj g′ , (g , (g′ , (s , cb))))))
    go (suc n) =
      let (cc , (pd , (pdd , (pdd′ , (gy , (gy′ , (sy , gb))))))) = go n
          oi = sndP pdd Aᵢ Aᵢ hi hi hi tt tt (c n) (c n) azero azero (Yn n) (Yn n) (cxL cc) gy gy (sr gy) z≤
          oj = sndP pdd′ Aⱼ Aⱼ hj hj hj tt tt (c′ n) (c′ n) azero azero (Yn′ n) (Yn′ n) (cxR cc) gy′ gy′ (sr gy′) z≤
      in cxc cc pd pdd pdd′ ,
         (prj (proj₂ (h n azero azero z≤)) ,
          (prj (proj₂ oi) , (prj (proj₂ oj) ,
           (G⊕ {Yn n} gy (proj₂ oi) , (G⊕ {Yn′ n} gy′ (proj₂ oj) ,
            (S⊕ gy gy′ sy (h n _ _ (proj₁ sy)) , proj₁ (h n _ _ gb)))))))
```
