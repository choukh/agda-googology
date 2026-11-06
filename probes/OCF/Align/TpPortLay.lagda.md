# 两种种类的单调 (十): 层 $L$ 的核实例

> 入口 [TpPort](TpPort.lagda.md). 不含记号. **生成文件**: 由 `probes/Survey/scripts/tpport/mk_tpport.py` 从 [MonoPort7Lay](MonoPort7Lay.lagda.md) 逐字节可重生成 (公共变换在同目录的 `tpgen.py`). 公共变换只改: 世界的类型与序 (`A`, `_⊲_` 换成两种种类的 `Wd₂`, `_≤ʷ_`; `C.self`, `C.⊲-tr` 换成 `≤rf`, `≤tr`; `Lg` 换成 `LgW₂`), 高度的类型 (`H` 换成 `Ht`, `LgH` 换成 `LgB`, `hΩ g` 换成 `hΩ κ g`), 模块参数多一个 `oΛ` (第 1 层是实例在一切世界里的第一位置, 两种种类的折叠要它), 数据树多一个构造子 `nμ` (每个 `nκ` 的空子句后加一句), `Step` 换名 `Stp`. 证明逐句不变. 
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`, 不改树、折叠、合法性.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.HtTowerTy using (HB; hz; hs; _⊲[_]_; LgB)
open import OCF.Align.HtTowerFTree using (Ht; Wd₂; LgW₂; AccY; D)
module OCF.Align.TpPortLay (Λ : Ht) (lΛ : LgB Λ) (oΛ : ∀ {w} → hs hz ⊲[ w ] Λ) {W : Wd₂} (lW : LgW₂ W) (t₀ : hz ⊲[ W ] Λ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤)
open import OCF.Align.HtTowerTy using (⊲ᴮ↑)
open import OCF.Align.HtTowerFTree using (n0; _⨾_; nw; ≤rf) renaming (_≤_ to _≤ʷ_)
open import OCF.Align.TpPortRel Λ lΛ oΛ lW t₀
open import OCF.Align.TpPortRelM lW using (module RelM)
import OCF.Align.TpPortChn as Chn
import OCF.Align.TpPortGen as Gen


InS : ∀ L → D L W → D L W → Set
InS L x x′ = RelN L x x′ × (RelN L x x × RelN L x′ x′)

-- 上下文取 CxN 的动作前提 (对 hs b 与 hl f 定义性地就是 HAK)
HAKN : ∀ L → P.Ig L W → P.Ig L W → Set
HAKN L A₀ A₁ = ∀ w w′ c c′ Y Y′ → CxN L w w′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ → Obs c c′ (A₀ ≤rf lW w Y) (A₁ ≤rf lW w′ Y′)

module L (b : Ht) (ac : AccY b) (ll : b ⊲[ W ] Λ) where
  module Cn = Chn Λ lΛ oΛ lW t₀ O b ac ll (CxN b) (InS b)
  module K = Cn.K
  open RL b using (OkRf; rnw; nwd; nwd′; nwᵉ; ⨾⊑; tr; asʳ′; asˡ; nwˡ; nwʳ; u1ˡ; u1ʳ; n0⊑)

  cl : K.CxLaws
  cl = record
    { cxL = λ { (K.cx (_ , (o , _))) → K.cx (OkRf o , (o , o)) }
    ; cxR = λ { (K.cx (_ , (_ , o′))) → K.cx (OkRf o′ , (o′ , o′)) }
    ; cx⨾ = λ { _ _ (K.cx (hw , (o , o′))) (K.inn (hx , (rx , rx′))) →
                K.cx (⨾⊑ (OkRf o) (OkRf o′) hw (nwˡ (nwʳ hx)) , ((o , rnw rx) , (o′ , rnw rx′))) }
    ; cx0ˡ = λ { _ (K.cx (hw , (o , o′))) →
                 K.cx (tr (⨾⊑ (OkRf o) (OkRf o) (OkRf o) (nwˡ n0⊑)) (u1ˡ hw) , ((o , rnw n0⊑) , o′)) }
    ; cx0ʳ = λ { _ (K.cx (hw , (o , o′))) →
                 K.cx (tr (u1ʳ hw) (⨾⊑ (OkRf o′) (OkRf o′) (OkRf o′) n0⊑) , (o , (o′ , rnw n0⊑))) }
    ; cxas = λ { _ (K.cx (_ , (o , _))) (K.inn (_ , (rx , _))) (K.inn (_ , (ry , _))) →
                 K.cx (asʳ′ (OkRf o) (rnw rx) (rnw ry) (⨾⊑ (OkRf o) (OkRf o) (OkRf o) (nwd rx ry)) ,
                        ((o , rnw (⨾⊑ rx rx rx ry)) , ((o , rnw rx) , rnw ry))) }
    ; cxas′ = λ { _ (K.cx (_ , (o , _))) (K.inn (_ , (rx , _))) (K.inn (_ , (ry , _))) →
                  K.cx (asˡ (OkRf o) (rnw rx) (rnw ry) (⨾⊑ (OkRf o) (OkRf o) (OkRf o) (nwd′ rx ry)) ,
                         (((o , rnw rx) , rnw ry) , (o , rnw (⨾⊑ rx rx rx ry)))) }
    ; cxpre = λ { {d = d} _ _ n (K.cx (h , ((o , rP) , oR))) (K.inn (he , (rd , re))) →
                  let rP′ = nwᵉ rP
                      rw = OkRf o
                      rwP = ⨾⊑ rw rw rw rP
                  in K.cx (tr (asʳ′ rw rP (rnw rd) (⨾⊑ rw rw rw (nwd rP′ rd))) (⨾⊑ rwP (OkRf oR) h (nwˡ (nwʳ he))) ,
                           ((o , rnw (⨾⊑ rP′ rP′ rP′ rd)) , (oR , rnw re))) }
    ; cxlim = λ { {d = d} _ n (K.cx (h , (oL , (o , rP)))) (K.inn (_ , (rd , _))) →
                  let rP′ = nwᵉ rP
                      rw = OkRf o
                      rwP = ⨾⊑ rw rw rw rP
                  in K.cx (tr (⨾⊑ (OkRf oL) rwP h (rnw rd)) (asˡ rw rP (rnw rd) (⨾⊑ rw rw rw (nwd′ rP′ rd))) ,
                           ((oL , rnw rd) , (o , rnw (⨾⊑ rP′ rP′ rP′ rd)))) }
    }

  open K.Steps cl public

  toHA : ∀ (i j : K.Act) → HAKN b i j → K.HA i j
  toHA i j h w w′ c c′ Y Y′ (K.cx cw) = h w w′ c c′ Y Y′ cw

  fromHA : ∀ (i j : K.Act) → K.HA i j → HAKN b i j
  fromHA i j h w w′ c c′ Y Y′ cw = h w w′ c c′ Y Y′ (K.cx cw)

  SemS : D b W → D b W → Set
  SemS x x′ = ∀ (Aᵢ Aⱼ : K.Act) → HAKN b Aᵢ Aᵢ → HAKN b Aⱼ Aⱼ → HAKN b Aᵢ Aⱼ → K.Sem Aᵢ Aⱼ {tt} {tt} x x′

  -- 第 ≥1 层的上升链: 链点按 Rel, 上下文按 Ctx
  cxc : ∀ {c c′ δ δ′} → K.Cx c c′ → RelN b δ δ′ → RL.Rf b δ → RL.Rf b δ′ → K.Cx (c ⨾ δ) (c′ ⨾ δ′)
  cxc (K.cx (hc , (oc , oc′))) pd pdd pdd′ = K.cx (⨾⊑ (OkRf oc) (OkRf oc′) hc pd , ((oc , pdd) , (oc′ , pdd′)))

  module Ch (snd : ∀ {x x′} → RelN b x x′ → SemS x x′) (tN : ∀ {x x′} → Rel b x x′ → RelN b x x′) (i j : K.Act) (hi : HAKN b i i) (hj : HAKN b j j) (hij : HAKN b i j) =
    Cn.Chain cl (RelN b) (λ pd Aᵢ Aⱼ h₁ h₂ h₁₂ → snd pd Aᵢ Aⱼ (fromHA Aᵢ Aᵢ h₁) (fromHA Aⱼ Aⱼ h₂) (fromHA Aᵢ Aⱼ h₁₂)) (λ h → tN (h ll))
      (K.cx (n0⊑ , (n0⊑ , n0⊑))) cxc i j (toHA i i hi) (toHA j j hj) (toHA i j hij)

  -- 分支一步: 先在坐标上走一次 (从 n0 起), 再走动作
  Sv : K.Act → P.St W → D b W → P.St W
  Sv i Y z = P.cv ≤rf Y G.⊕ K.Run (P.Ig↾ ≤rf i) z tt n0 (P.cv ≤rf Y)

  brn : ∀ (i j : K.Act) → HAKN b i i → HAKN b j j → HAKN b i j → ∀ (Y Y′ : P.St W) → Good Y → Good Y′ → SRel Y Y′ →
        ∀ {z z′} → SemS z z′ → SemS z z → SemS z′ z′ → CxN b z z′ → i ≤rf lW z (Sv i Y z) ≼ j ≤rf lW z′ (Sv j Y′ z′)
  brn i j hi hj hij Y Y′ g g′ s {z} {z′} sz sz₁ sz₂ cz = proj₂ (hij z z′ azero azero S S′ cz gS gS′ sS z≤)
    where
    i′ = P.Ig↾ ≤rf i
    j′ = P.Ig↾ ≤rf j
    Y₁ = P.cv ≤rf Y
    Y₁′ = P.cv ≤rf Y′
    Δ = K.Run i′ z tt n0 Y₁
    Δ′ = K.Run j′ z′ tt n0 Y₁′
    S = Y₁ G.⊕ Δ
    S′ = Y₁′ G.⊕ Δ′
    c00 = K.cx (n0⊑ , (n0⊑ , n0⊑))
    o = sz i′ j′ hi hj hij tt tt n0 n0 (G.vY Y) (G.vY Y′) Y₁ Y₁′ c00 g g′ s (proj₁ s)
    rΔ = proj₂ (sz₁ i′ i′ hi hi hi tt tt n0 n0 azero azero Y₁ Y₁ c00 g g (K.sr {Y₁} g) z≤)
    rΔ′ = proj₂ (sz₂ j′ j′ hj hj hj tt tt n0 n0 azero azero Y₁′ Y₁′ c00 g′ g′ (K.sr {Y₁′} g′) z≤)
    gS = K.G⊕ {Y₁} {Δ} g rΔ
    gS′ = K.G⊕ {Y₁′} {Δ′} g′ rΔ′
    sS = K.S⊕ {Y₁} {Y₁′} {Δ} {Δ′} g g′ s o
```
