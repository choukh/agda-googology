# 结构关系, 第十二轮 (六): `κᴸ` 的可靠性

> 不读记号. 入口 [StrRel12](StrRel12.lagda.md). 交接单第 2 项. `nκ zz u` 在目标 $T$ 上按目标层分两种 (`RKy`):
>
> - **第 0 层目标: 回灌.** 输出是各格 (`κc`) 的走法 (`κΔ`) 在 `τ₀` 上读数的极限. 对格 $n$ 归纳维持不变量 `CS` (格世界可比且自洽, 格路径 `wv` 是 `AP` 对, 从树世界到格的底端的前段 `ap` 是 `AP` 对, 走过的一段 `av` 对齐, 上下文与状态相关). 第 0 格与第 $n+1$ 格的路径都是 `sum-fst`, 对齐由第 0 层关系生成 (`StrRel12Rel.genAl`): 第 0 格用状态的第 0 层分量 (`R∀c` 的第二项) 与运行世界可比 (`CP` 的顶端可比), 第 $n+1$ 格用上一格的输出 (`WalkR.walkR` 在 `τ₀` 上的读数). 这就是 `GoD`/`genᴾ` 的主线版.
> - **别的目标层: 走到目标的世界, 再保留.** `Kp` 是沿目标路径 `wm T` 的一次走法 (目标对的 `CP` 给出对齐, `StrRel11Tg.kpR`/`kp-nw` 的主线形式); `Kb` 在输出 `nκ` 的 `CP` 分支对 $(p,p')$ 上: 状态两次 `cv` (`cvRc`), 走法沿 $p$ (`walkR`), 上下文是两段 `Cut` (`cutR`), 树在叠起来的路径 `q₀ ∘ (wm T ∘ p)` 上 (`StrRel11Tg.stack`).
>
> 以分支的关系 `h` 与语义 `sb` 为模块参数; 入口的 `sem` 以闭包填上.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
module OCF.Align.StrRel12Kp (Λ : H) (lΛ : LgH Λ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg; ⊲-tr; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.HtFeedTree using (hz; hs; hl; hΩ; D; NZ; nκ; nw; _⨾_; AccY; Cut; sum; sum-fst; Lg-sum; ⊲ᴴ↑)
open import OCF.Align.HtFeedClosed using (module At)
open import OCF.Align.StrRel4Walk using (Al)
open import OCF.Align.StrRel4Gen using (adm-self)
open import OCF.Align.StrRel12Al using (Coh; AP; CP; ap-self; ap-tr; cp-self; cp-top; cp-tr; al-adm)
open import OCF.Align.StrRel12Rel using (Rel; ⨾ᴸ; nlᴸ; nwAᴸ; κᴸ; vsum; drpR; lgsf; cohSum; genAl)
open import OCF.Align.StrRel12Int using (module CutR)
open import OCF.Align.StrRel12Sem Λ lΛ using (Top; TC; OAc; R∀c; cvRc; advRc; HAW; haw↾; SemW; module WalkR)

module P = At Λ lΛ
open P using (Tg; tg; wm; tm; lm; τ₀; St; yc; z; cv; _⊕⟨_⟩_; Run; Ig; Ig↾; LW; Cl; RKy; RKk; Kp; Kb; κc; κΔ)
```

## 1 不变量

```agda
record CS {L W W′ V V′} {lV : Lg V} {lV′ : Lg V′} (lW : Lg W) (lW′ : Lg W′) (c₁ : Cl W V L) (c₂ : Cl W′ V′ L) : Set where
  field
    vle : P.v c₁ ≤ P.v c₂
    ch  : Coh (P.lv c₁)
    ch′ : Coh (P.lv c₂)
    apW : AP lW lW′ (P.wv c₁) (P.lv c₁) (P.wv c₂) (P.lv c₂)
    la  : Lg (P.a c₁)
    la′ : Lg (P.a c₂)
    hap : AP lV lV′ (P.ap c₁) la (P.ap c₂) la′
    ea  : la ≡ lg⊲ (P.av c₁) (P.lv c₁)
    ea′ : la′ ≡ lg⊲ (P.av c₂) (P.lv c₂)
    Hav : Al (P.v c₁) (P.v c₂) (P.av c₁) (P.lv c₁) (P.av c₂) (P.lv c₂)
    hco : Rel L (P.lv c₁) (P.lv c₂) (P.co c₁) (P.co c₂)
    hS  : R∀c (P.lv c₁) (P.lv c₂) (P.Sv c₁) (P.Sv c₂)
open CS
```

## 2 `nκ` 规则的语义

```agda
module KpS {L V V′} {lV : Lg V} {lV′ : Lg V′} {zz zz′ : NZ L}
           {u : ∀ {c} → V ⊲ c → Lg c → D L c} {u′ : ∀ {c} → V′ ⊲ c → Lg c → D L c}
           (h : ∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CP lV lV′ p lc p′ lc′ → Rel L lc lc′ (u p lc) (u′ p′ lc′))
           (sb : ∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CP lV lV′ p lc p′ lc′ → SemW L lc lc′ (u p lc) (u′ p′ lc′)) where
  open CutR h

  module Go {W W′} (lW : Lg W) (lW′ : Lg W′) (ac ac′ : AccY L) (ll : LW L W) (ll′ : LW L W′) (q₀ : V ⊲ W) (q₀′ : V′ ⊲ W′)
            (hq : CP lV lV′ q₀ lW q₀′ lW′) (A₀ : Ig L W) (A₀′ : Ig L W′) (ha : HAW L lW lW′ A₀ A₀′)
            (w : D L W) (w′ : D L W′) (hw : Rel L lW lW′ w w′) (Y : St W) (Y′ : St W′) (hY : R∀c lW lW′ Y Y′) where

    -- 别的目标层
    module K {t m m′} (T : Tg W t m) (T′ : Tg W′ t m′) (tc : TC lW lW′ T T′) where
      apk = ap-tr (proj₁ hq) (proj₁ tc)
      tpk = cp-top tc
      KpO : OAc (lm T) (lm T′) (Kp ac u q₀ ll A₀ w Y (wm T) (lm T)) (Kp ac′ u′ q₀′ ll′ A₀′ w′ Y′ (wm T′) (lm T′))
      KpO = WalkR.walkR ac ac′ h sb (⊲ᴴ↑ (wm T) ll) (⊲ᴴ↑ (wm T′) ll′) (Ig↾ (wm T) A₀) (Ig↾ (wm T′) A₀′) (haw↾ L (proj₁ tc) ha) tpk
              (proj₁ apk) C.self C.self (ap-self lV lV′) (proj₁ (proj₂ (proj₂ apk))) (proj₂ (proj₂ (proj₂ apk)))
              C.self C.self tpk (nwAᴸ (proj₁ tc) hw) (cvRc (proj₁ tc) Y Y′ hY)
      hco₀ : Rel L (lm T) (lm T′) (nw (wm T) w ⨾ Cut u m (⊲-tr q₀ (wm T)) C.self (lm T) C.self)
                                  (nw (wm T′) w′ ⨾ Cut u′ m′ (⊲-tr q₀′ (wm T′)) C.self (lm T′) C.self)
      hco₀ = ⨾ᴸ (nwAᴸ (proj₁ tc) hw) (cutR (proj₁ apk) C.self C.self (ap-self lV lV′) (proj₁ (proj₂ (proj₂ apk))) (proj₂ (proj₂ (proj₂ apk))) C.self C.self tpk)

      kb : ∀ {c c′} (p : m ⊲ c) (p′ : m′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CP (lm T) (lm T′) p lc p′ lc′ →
           Rel t lc lc′ (yc (Kb ac u q₀ ll A₀ w Y (wm T) (lm T) p lc) (tg C.self (⊲ᴴ↑ p (tm T)) lc))
                        (yc (Kb ac′ u′ q₀′ ll′ A₀′ w′ Y′ (wm T′) (lm T′) p′ lc′) (tg C.self (⊲ᴴ↑ p′ (tm T′)) lc′))
      kb p p′ lc lc′ cpp =
        sb (⊲-tr q₀ (⊲-tr (wm T) p)) (⊲-tr q₀′ (⊲-tr (wm T′) p′)) lc lc′ (cp-tr (proj₁ hq) (cp-tr (proj₁ tc) cpp))
           lc lc′ ac ac′ (⊲ᴴ↑ (⊲-tr (wm T) p) ll) (⊲ᴴ↑ (⊲-tr (wm T′) p′) ll′) C.self C.self tpc
           (Ig↾ (⊲-tr (wm T) p) A₀) (Ig↾ (⊲-tr (wm T′) p′) A₀′) haP
           _ _ (⨾ᴸ hco₁ (cutR (proj₁ (proj₁ cpp)) (⊲-tr q₀ (wm T)) (⊲-tr q₀′ (wm T′)) apk
                              (proj₁ (proj₂ (proj₂ (proj₁ cpp)))) (proj₂ (proj₂ (proj₂ (proj₁ cpp)))) C.self C.self tpc))
           _ _ (advRc tpc _ _ _ _ hY₂ WO)
           (tg C.self (⊲ᴴ↑ p (tm T)) lc) (tg C.self (⊲ᴴ↑ p′ (tm T′)) lc′) tpc
        where
        tpc = cp-top cpp
        apP = ap-tr (proj₁ tc) (proj₁ cpp)
        haP = haw↾ L apP ha
        hco₁ = nwAᴸ (proj₁ cpp) hco₀
        hY₂ = cvRc (proj₁ cpp) _ _ (advRc tpk _ _ _ _ (cvRc (proj₁ tc) Y Y′ hY) KpO)
        WO = WalkR.walkR ac ac′ h sb (⊲ᴴ↑ (⊲-tr (wm T) p) ll) (⊲ᴴ↑ (⊲-tr (wm T′) p′) ll′) (Ig↾ (⊲-tr (wm T) p) A₀) (Ig↾ (⊲-tr (wm T′) p′) A₀′) haP tpc
               (proj₁ (proj₁ cpp)) (⊲-tr q₀ (wm T)) (⊲-tr q₀′ (wm T′)) apk
               (proj₁ (proj₂ (proj₂ (proj₁ cpp)))) (proj₂ (proj₂ (proj₂ (proj₁ cpp)))) C.self C.self tpc hco₁ hY₂

      kRel : ∀ (z₁ z₂ : NZ t) → Rel t (lm T) (lm T′) (RKk ac u q₀ ll A₀ w Y T z₁) (RKk ac′ u′ q₀′ ll′ A₀′ w′ Y′ T′ z₂)
      kRel z₁ z₂ = ⨾ᴸ (KpO (tg C.self (tm T) (lm T)) (tg C.self (tm T′) (lm T′)) tpk) (κᴸ kb)

    -- 第 0 层目标: 格
    c₁ = κc ac u q₀ lW ll A₀ w Y
    c₂ = κc ac′ u′ q₀′ lW′ ll′ A₀′ w′ Y′

    topS : ∀ {c d} → CS {L} {lV = lV} {lV′} lW lW′ c d → Top (P.lv c) (P.lv d)
    topS s = cp-self _ _ (vle s) (ch s) (ch′ s)

    OΔ : ∀ {c d} → CS {L} {lV = lV} {lV′} lW lW′ c d → OAc (P.lv c) (P.lv d) (κΔ ac u ll A₀ c) (κΔ ac′ u′ ll′ A₀′ d)
    OΔ {c} {d} s = WalkR.walkR ac ac′ h sb (⊲ᴴ↑ (P.wv c) ll) (⊲ᴴ↑ (P.wv d) ll′) (Ig↾ (P.wv c) A₀) (Ig↾ (P.wv d) A₀′) (haw↾ L (apW s) ha) (topS s)
                     (Hav s) (P.ap c) (P.ap d) (hap s) (ea s) (ea′ s) C.self C.self (topS s) (hco s) (hS s)

    cs : ∀ n → CS {L} {lV = lV} {lV′} lW lW′ (c₁ n) (c₂ n)
    cs zero = record { vle = vsum hz₀ le ; ch = cohSum W (z Y) lW cW ; ch′ = cohSum W′ (z Y′) lW′ cW′ ; apW = apS
                     ; la = lV ; la′ = lV′ ; hap = ap-self lV lV′ ; ea = proj₁ (proj₂ (proj₂ apF)) ; ea′ = proj₂ (proj₂ (proj₂ apF))
                     ; Hav = proj₁ apF ; hco = nwAᴸ apS hw ; hS = cvRc apS Y Y′ hY }
      where
      hz₀ = proj₂ hY
      le = proj₁ (proj₂ hq)
      cW = proj₁ (proj₂ (proj₂ hq))
      cW′ = proj₂ (proj₂ (proj₂ hq))
      G₀ = genAl hz₀ lW lW′ le (adm-self _ _)
      apS = G₀ , al-adm G₀ , sym (lgsf W (z Y) lW) , sym (lgsf W′ (z Y′) lW′)
      apF = ap-tr (proj₁ hq) apS
    cs (suc n) = record { vle = vsum hd (vle s) ; ch = cohSum (P.v (c₁ n)) d₁ (P.lv (c₁ n)) (ch s) ; ch′ = cohSum (P.v (c₂ n)) d₂ (P.lv (c₂ n)) (ch′ s)
                        ; apW = ap-tr (apW s) apS ; la = P.lv (c₁ n) ; la′ = P.lv (c₂ n)
                        ; hap = ap-tr (hap s) (Hav s , al-adm (Hav s) , ea s , ea′ s)
                        ; ea = sym (lgsf (P.v (c₁ n)) d₁ (P.lv (c₁ n))) ; ea′ = sym (lgsf (P.v (c₂ n)) d₂ (P.lv (c₂ n)))
                        ; Hav = G₁
                        ; hco = nwAᴸ apS (⨾ᴸ (hco s) (cutR (Hav s) (P.ap (c₁ n)) (P.ap (c₂ n)) (hap s) (ea s) (ea′ s) C.self C.self (topS s)))
                        ; hS = cvRc apS _ _ (advRc (topS s) _ _ _ _ (hS s) O) }
      where
      s = cs n
      O = OΔ s
      d₁ = yc (κΔ ac u ll A₀ (c₁ n)) (τ₀ (P.lv (c₁ n)))
      d₂ = yc (κΔ ac′ u′ ll′ A₀′ (c₂ n)) (τ₀ (P.lv (c₂ n)))
      hd = O (τ₀ (P.lv (c₁ n))) (τ₀ (P.lv (c₂ n))) (topS s)
      G₁ = genAl hd (P.lv (c₁ n)) (P.lv (c₂ n)) (vle s) (adm-self _ _)
      apS = G₁ , al-adm G₁ , sym (lgsf (P.v (c₁ n)) d₁ (P.lv (c₁ n))) , sym (lgsf (P.v (c₂ n)) d₂ (P.lv (c₂ n)))

    goT : ∀ t {m m′} (T : Tg W t m) (T′ : Tg W′ t m′) → TC lW lW′ T T′ →
          Rel t (lm T) (lm T′) (RKy ac u q₀ lW ll A₀ w Y t T) (RKy ac′ u′ q₀′ lW′ ll′ A₀′ w′ Y′ t T′)
    goT hz T T′ tc = nlᴸ (λ n → drpR (OΔ (cs n) (τ₀ (P.lv (c₁ n))) (τ₀ (P.lv (c₂ n))) (topS (cs n))))
    goT (hs b) T T′ tc = K.kRel T T′ tc tt tt
    goT (hl f) T T′ tc = K.kRel T T′ tc tt tt
    goT (hΩ g) T T′ tc = K.kRel T T′ tc tt tt

  sem-κ : SemW L lV lV′ (nκ zz u) (nκ zz′ u′)
  sem-κ lW lW′ ac ac′ ll ll′ q₀ q₀′ hq A₀ A₀′ ha w w′ hw Y Y′ hY {t} T T′ tc = G.goT t T T′ tc
    where module G = Go lW lW′ ac ac′ ll ll′ q₀ q₀′ hq A₀ A₀′ ha w w′ hw Y Y′ hY
```
