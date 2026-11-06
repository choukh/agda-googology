# 一步对一切有限高度 (四): 第 $\ge1$ 层的核实例, 对一切良基证明与位置

> 入口 [MonoPort6](MonoPort6.lagda.md). 不含记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.
>
> 对层 `hs b`, 良基证明 `ac`, 位置 `ll` 取核的实例 (经 `MonoPort5Chn`, 与上一组同一个 `Core` 用法). 上下文关系 `Ctx (hs b)`, 输入关系 "相关且两边自比". 上下文律 `cl` 对 $b$ 写一次 (与 `MonoPort5One.cl₁` 同一个论证, 只把 `R1` 换成 `R b`). 动作前提在实例之间换算 (`toHA`, `fromHA`): 核的 `HA` 用核内记录 `Cx`, 不同的 `ll` 给出不同的记录类型; `MonoPort6Rel.HAK` 不依赖实例. 第 $\ge1$ 层的分支一步 `brn` 不递归, 下层的语义作参数.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.HtFeedTree using (H; LgH; hz; _⊲[_]_)
module OCF.Align.MonoPort6Lay (Λ : H) (lΛ : LgH Λ) {W : A} (lW : Lg W) (t₀ : hz ⊲[ W ] Λ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤)
open import OCF.Align.HtFeedTree using (hs; D; AccY; n0; _⨾_; nw; ⊲ᴴ↑)
open import OCF.Align.MonoPort6Rel Λ lΛ lW t₀
open import OCF.Align.MonoPort5Rel lW using (module RelM)
import OCF.Align.MonoPort5Chn as Chn
import OCF.Align.MonoPort3Gen as Gen

InS : ∀ b → D (hs b) W → D (hs b) W → Set
InS b x x′ = Rel (hs b) x x′ × (Rf (hs b) x × Rf (hs b) x′)

module L (b : H) (ac : AccY (hs b)) (ll : hs b ⊲[ W ] Λ) where
  module Cn = Chn Λ lΛ lW t₀ O (hs b) ac ll (Ctx (hs b)) (InS b)
  module K = Cn.K
  open R b using (OkRf; rnw; nwd; nwd′; nwᵉ; ⨾⊑; tr; asʳ′; asˡ; nwˡ; nwʳ; u1ˡ; u1ʳ; n0⊑)

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

  toHA : ∀ (i j : K.Act) → HAK (hs b) i j → K.HA i j
  toHA i j h w w′ c c′ Y Y′ (K.cx cw) = h w w′ c c′ Y Y′ cw

  fromHA : ∀ (i j : K.Act) → K.HA i j → HAK (hs b) i j
  fromHA i j h w w′ c c′ Y Y′ cw = h w w′ c c′ Y Y′ (K.cx cw)

  SemS : D (hs b) W → D (hs b) W → Set
  SemS x x′ = ∀ (Aᵢ Aⱼ : K.Act) → HAK (hs b) Aᵢ Aᵢ → HAK (hs b) Aⱼ Aⱼ → HAK (hs b) Aᵢ Aⱼ → K.Sem Aᵢ Aⱼ {tt} {tt} x x′

  -- 第 ≥1 层的上升链: 链点按 Rel, 上下文按 Ctx
  cxc : ∀ {c c′ δ δ′} → K.Cx c c′ → Rel (hs b) δ δ′ → Rf (hs b) δ → Rf (hs b) δ′ → K.Cx (c ⨾ δ) (c′ ⨾ δ′)
  cxc (K.cx (hc , (oc , oc′))) pd pdd pdd′ = K.cx (⨾⊑ (OkRf oc) (OkRf oc′) hc pd , ((oc , pdd) , (oc′ , pdd′)))

  module Ch (snd : ∀ {x x′} → Rel (hs b) x x′ → SemS x x′) (i j : K.Act) (hi : HAK (hs b) i i) (hj : HAK (hs b) j j) (hij : HAK (hs b) i j) =
    Cn.Chain cl (Rel (hs b)) (λ pd Aᵢ Aⱼ h₁ h₂ h₁₂ → snd pd Aᵢ Aⱼ (fromHA Aᵢ Aᵢ h₁) (fromHA Aⱼ Aⱼ h₂) (fromHA Aᵢ Aⱼ h₁₂)) (λ h → h ll)
      (K.cx (n0⊑ , (n0⊑ , n0⊑))) cxc i j (toHA i i hi) (toHA j j hj) (toHA i j hij)

  -- 分支一步: 先在坐标上走一次 (从 n0 起), 再走动作
  Sv : K.Act → P.St W → D (hs b) W → P.St W
  Sv i Y z = P.cv C.self Y G.⊕ K.Run (P.Ig↾ C.self i) z tt n0 (P.cv C.self Y)

  brn : ∀ (i j : K.Act) → HAK (hs b) i i → HAK (hs b) j j → HAK (hs b) i j → ∀ (Y Y′ : P.St W) → Good Y → Good Y′ → SRel Y Y′ →
        ∀ {z z′} → SemS z z′ → SemS z z → SemS z′ z′ → Ctx (hs b) z z′ → i C.self lW z (Sv i Y z) ≼ j C.self lW z′ (Sv j Y′ z′)
  brn i j hi hj hij Y Y′ g g′ s {z} {z′} sz sz₁ sz₂ cz = proj₂ (hij z z′ azero azero S S′ cz gS gS′ sS z≤)
    where
    i′ = P.Ig↾ C.self i
    j′ = P.Ig↾ C.self j
    Y₁ = P.cv C.self Y
    Y₁′ = P.cv C.self Y′
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
