# 结构关系, 第十四轮 (二): 同层节点规则 `niᴸ` 的可靠性, 带不变量 (生成)

> 由 `probes/Survey/scripts/strrel14/mk_semj.py` 从 [StrRel12Ni](StrRel12Ni.lagda.md) 生成 (从仓库根运行 `python3 probes/Survey/scripts/strrel14/mk_semj.py .`, 逐字节可重生成). 入口 [StrRel14J](StrRel14J.lagda.md). 不读记号. 证明逐句不变, 只换状态前提: `R∀c` 换成不变量记录 `I : Inv` ([StrRel14If](StrRel14If.lagda.md)) 的 `J`, `advRc`/`cvRc` 换成记录的封闭律 `⊕J`/`cvJ`, `R∀c` 的两个分量经 `toR` 取, `HAW`/`SemW`/`haw↾` 换成 `HAWJ`/`SemJ`/`haw↾J`. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
open import OCF.Align.StrRel14If using (Inv)
module OCF.Align.StrRel14NiJ (Λ : H) (lΛ : LgH Λ) (I : Inv Λ lΛ) where

open import OCF.Align.StrRel14If Λ lΛ using (module WithInv)
open WithInv I using (HAWJ; SemJ)
open Inv I using (J; toR; cvJ; ⊕J)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (StH; Vs; D; n0; ni; NZ-S; AccY; acc; mkOf; inS; outS; ⊲ᴴ↑)
open import OCF.Align.HtFeedClosed using (module At)
open import OCF.Align.StrRel11Rk Λ lΛ using (RkRel; rr; kp; rk-agree)
open import OCF.Align.StrRel12Al using (CP; ap-tr; cp-top; cp-tr)
open import OCF.Align.StrRel12Rel using (Rel; Below; n0ᴸ; ⨾ᴸ; nlᴸ; nwAᴸ; niᴸ; belowIn; belowOut)
open import OCF.Align.StrRel12Int using (IntM)
open import OCF.Align.StrRel12Sem Λ lΛ using (TC; OAc; R∀c)
open import OCF.Align.StrRel14SemJ Λ lΛ I using (haw↾J)

module P = At Λ lΛ
open P using (Tg; tg; wm; tm; lm; St; yc; d; cv; _⊕⟨_⟩_; Run; Ig; Ig↾; LW; Rk; rise; keep; rkT; RKi; Ai; Chn; kk)
```

## 1 节点规则的语义

```agda
module NiS {L V V′ k} {lV : Lg V} {lV′ : Lg V′} (r : StH V k L) (r′ : StH V′ k L)
           {u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′} {u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L r′ W′ → D L W′}
           (hu : ∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CP lV lV′ p lc p′ lc′ →
                 ∀ y y′ → Below L r r′ lc lc′ y y′ → Rel L lc lc′ (u p lc y) (u′ p′ lc′ y′))
           (su : ∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CP lV lV′ p lc p′ lc′ →
                 ∀ y y′ → Below L r r′ lc lc′ y y′ → SemJ L lc lc′ (u p lc y) (u′ p′ lc′ y′))
           (sk : ∀ {U U′} {lU : Lg U} {lU′ : Lg U′} {x : D k U} {x′ : D k U′} → Rel k lU lU′ x x′ → SemJ k lU lU′ x x′) where

  module Go {W W′} (lW : Lg W) (lW′ : Lg W′) (f : ∀ {W₁ j} → StH W₁ j L → AccY j) (f′ : ∀ {W₁ j} → StH W₁ j L → AccY j)
            (ll : LW L W) (ll′ : LW L W′) (q₀ : V ⊲ W) (q₀′ : V′ ⊲ W′) (hq : CP lV lV′ q₀ lW q₀′ lW′)
            (A₀ : Ig L W) (A₀′ : Ig L W′) (ha : HAWJ L lW lW′ A₀ A₀′) (w : D L W) (w′ : D L W′) (hw : Rel L lW lW′ w w′) where
    hk = kk r q₀ ll
    hk′ = kk r′ q₀′ ll′
    A² = Ai (acc f) (f r) r u q₀ hk ll A₀ w
    A²′ = Ai (acc f′) (f′ r′) r′ u′ q₀′ hk′ ll′ A₀′ w′
    tp = cp-top hq

    -- 坐标层的动作前提
    haAi : HAWJ k lW lW′ A² A²′
    haAi p p′ lW₁ lW₁′ cpp z z′ hz Y₁ Y₁′ hY₁ =
      su (⊲-tr q₀ p) (⊲-tr q₀′ p′) lW₁ lW₁′ (cp-tr (proj₁ hq) cpp) (inS r z) (inS r′ z′) (belowIn L r r′ hz)
         lW₁ lW₁′ (acc f) (acc f′) (⊲ᴴ↑ p ll) (⊲ᴴ↑ p′ ll′) C.self C.self (cp-top cpp) (Ig↾ p A₀) (Ig↾ p′ A₀′) (haw↾J L (proj₁ cpp) ha)
         _ _ (⨾ᴸ (nwAᴸ (proj₁ cpp) hw)
                 (IntM (f r) (f′ r′) hz (cp-top cpp) (NZ-S r) (NZ-S r′) (mkOf r (⊲-tr q₀ p)) (mkOf r′ (⊲-tr q₀′ p′)) _ _
                       (λ p₂ p₂′ l₂ l₂′ cp₂ y y′ hy →
                          hu (⊲-tr (⊲-tr q₀ p) p₂) (⊲-tr (⊲-tr q₀′ p′) p₂′) l₂ l₂′ (cp-tr (ap-tr (proj₁ hq) (proj₁ cpp)) cp₂)
                             (inS r y) (inS r′ y′) (belowIn L r r′ hy))
                       n0ᴸ))
         Y₁ Y₁′ hY₁

    module Ch (Y : St W) (Y′ : St W′) (hY : J lW lW′ Y Y′) where
      C₁ = Chn (f r) hk lW A² Y
      C₂ = Chn (f′ r′) hk′ lW′ A²′ Y′
      Cs : ℕ → Set
      Cs n = Rel k lW lW′ (proj₁ (C₁ n)) (proj₁ (C₂ n)) × Rel k lW lW′ (proj₁ (proj₂ (C₁ n))) (proj₁ (proj₂ (C₂ n))) ×
             J lW lW′ (proj₂ (proj₂ (C₁ n))) (proj₂ (proj₂ (C₂ n)))
      outn : ∀ n → Cs n → OAc lW lW′ (Run (f r) (proj₁ (proj₂ (C₁ n))) C.self lW hk A² (proj₁ (C₁ n)) (proj₂ (proj₂ (C₁ n))))
                                     (Run (f′ r′) (proj₁ (proj₂ (C₂ n))) C.self lW′ hk′ A²′ (proj₁ (C₂ n)) (proj₂ (proj₂ (C₂ n))))
      outn n (hc , hz , hs) = sk hz lW lW′ (f r) (f′ r′) hk hk′ C.self C.self tp A² A²′ haAi _ _ hc _ _ hs
      cs : ∀ n → Cs n
      cs zero = n0ᴸ , proj₁ (toR hY) (tg C.self hk lW) (tg C.self hk′ lW′) tp , hY
      cs (suc n) = ⨾ᴸ (proj₁ (cs n)) (proj₁ (proj₂ (cs n))) ,
                   outn n (cs n) (tg C.self hk lW) (tg C.self hk′ lW′) tp ,
                   ⊕J tp _ _ _ _ (proj₂ (proj₂ (cs n))) (outn n (cs n))

    goRk : ∀ (Y : St W) (Y′ : St W′) → J lW lW′ Y Y′ → ∀ {t m m′} (T : Tg W t m) (T′ : Tg W′ t m′) → TC lW lW′ T T′ →
           ∀ (rk : Rk k t m) (rk′ : Rk k t m′) → RkRel rk rk′ →
           Rel t (lm T) (lm T′) (RKi (acc f) (f r) r u q₀ lW ll A₀ w Y T rk) (RKi (acc f′) (f′ r′) r′ u′ q₀′ lW′ ll′ A₀′ w′ Y′ T′ rk′)
    goRk Y Y′ hY T T′ tc _ _ rr = nlᴸ (λ n → Ch.outn Y Y′ hY n (Ch.cs Y Y′ hY n) T T′ tc)
    goRk Y Y′ hY T T′ tc _ _ (kp R₁ R₂) =
      niᴸ (λ p p′ lc lc′ cpp y y′ hb →
        haAi (⊲-tr (wm T) p) (⊲-tr (wm T′) p′) lc lc′ (cp-tr (proj₁ tc) cpp) (outS R₁ y) (outS R₂ y′) (belowOut _ R₁ R₂ hb)
          _ _
          (⊕J (cp-top cpp) (cv (⊲-tr (wm T) p) Y) (cv (⊲-tr (wm T′) p′) Y′) _ _
             (cvJ (ap-tr (proj₁ tc) (proj₁ cpp)) Y Y′ hY)
             (sk (belowOut _ R₁ R₂ hb) lc lc′ (f r) (f′ r′) (⊲ᴴ↑ (⊲-tr (wm T) p) hk) (⊲ᴴ↑ (⊲-tr (wm T′) p′) hk′) C.self C.self (cp-top cpp)
                 (Ig↾ (⊲-tr (wm T) p) A²) (Ig↾ (⊲-tr (wm T′) p′) A²′) (haw↾J k (ap-tr (proj₁ tc) (proj₁ cpp)) haAi)
                 n0 n0 n0ᴸ _ _ (cvJ (ap-tr (proj₁ tc) (proj₁ cpp)) Y Y′ hY)))
          (tg C.self (⊲ᴴ↑ p (tm T)) lc) (tg C.self (⊲ᴴ↑ p′ (tm T′)) lc′) (cp-top cpp))

  sem-ni : SemJ L lV lV′ (ni r u) (ni r′ u′)
  sem-ni lW lW′ (acc f) (acc f′) ll ll′ q₀ q₀′ hq A₀ A₀′ ha w w′ hw Y Y′ hY T T′ tc =
    G.goRk Y Y′ hY T T′ tc _ _ (rk-agree (⊲ᴴ↑ (wm T) G.hk) (tm T) (lm T) (⊲ᴴ↑ (wm T′) G.hk′) (tm T′) (lm T′))
    where module G = Go lW lW′ f f′ ll ll′ q₀ q₀′ hq A₀ A₀′ ha w w′ hw
```
