# 结构关系, 第十二轮 (三): `Cut`, `IW` 与 `Int` 的两世界单调

> 不读记号, 不提折叠. 入口 [StrRel12](StrRel12.lagda.md). 交接单第 1 项 (d): `Int` 把第 $k$ 层的坐标嵌进第 $\mathrm{ly}$ 层 (节点分支收到的上下文). 本文证明两世界版的单调 **`IntM`**: 坐标按 `Rel k` 相关, 运行路径是 `CP` 对, 分支函数在 `CP` 扩张上把 `Rel k` 送到 `Rel ly` (`UH`), 上下文相关 ⇒ 两边的 `Int` 按 `Rel ly` 相关. 对 (良基证明, 推导) 字典序归纳 (同 `MonoPort6Int.IntMS`): `ni` 句内层的 `Int` 用更小的良基证明 `g R`, 外层用同一个良基证明、更小的推导. **`ni` 句不要求两边的 `mk` 相同** (`MonoPort6Int` 要求): 输出节点的 `StH` 证明可以不同 (`niᴸ` 允许), 坐标关系经 `belowOut` 取出, 与 `mk` 无关.
>
> `nκ` 句要沿两条路径走: `Cut` (`cutR`) 与 `IW` (`iwR`), 两者都对 `Al` 的推导递归, 每个位置的前段与后段由 [StrRel12Al](StrRel12Al.lagda.md) 给出. `iwR` 以 `Int` 的单调为参数 (`IH`), 在 `IntM` 的子句体里以闭包给出, 所以停机由结构检查直接给出.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel12Int where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (H; StH; D; n0; n1; _⨾_; nl; ni; nκ; nw; NZ; NZ-S; AccY; acc; Int; IW; Cut; Pre; tailP; mkOf; Kup; inS)
open import OCF.Align.StrRel4Walk using (Al; aS; aP; aR; aRL; aL)
open import OCF.Align.StrRel12Al using (AP; CP; ap-self; ap-tr; cp-top; cp-tr; cp-coh; extR; sfxS; posCP; module LimW)
open import OCF.Align.StrRel12Rel using (Rel; n0ᴸ; n1ᴸ; ⨾ᴸ; nlᴸ; prᴸ; nwAᴸ; niᴸ; κᴸ; belowIn; belowOut)
```

## 1 `Cut`

```agda
module CutR {ly W₀ W₀′} {lW₀ : Lg W₀} {lW₀′ : Lg W₀′} {v : ∀ {c} → W₀ ⊲ c → Lg c → D ly c} {v′ : ∀ {c} → W₀′ ⊲ c → Lg c → D ly c}
            (h : ∀ {c c′} (P : W₀ ⊲ c) (P′ : W₀′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CP lW₀ lW₀′ P lc P′ lc′ → Rel ly lc lc′ (v P lc) (v′ P′ lc′)) where
  cutR : ∀ {L L′ a b a′ b′} {p : a ⊲ b} {lb : Lg b} {p′ : a′ ⊲ b′} {lb′ : Lg b′} → Al L L′ p lb p′ lb′ →
         ∀ {la la′} (ap : W₀ ⊲ a) (ap′ : W₀′ ⊲ a′) → AP lW₀ lW₀′ ap la ap′ la′ → la ≡ lg⊲ p lb → la′ ≡ lg⊲ p′ lb′ →
         ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} (bV : b ⊲ V) (bV′ : b′ ⊲ V′) → CP lb lb′ bV lV bV′ lV′ →
         Rel ly lV lV′ (Cut v b p ap lb bV) (Cut v′ b′ p′ ap′ lb′ bV′)
  cutR (aS p′ lb′) ap ap′ hap e e′ bV bV′ hs = n0ᴸ
  cutR (aP {c = c} {c′ = c′} {p = p} {lc} {p′} {lc′} H c≤ ad) ap ap′ hap e e′ bV bV′ hs =
    ⨾ᴸ (cutR H ap ap′ hap e e′ (⊲-tr (C.suc C.self) bV) (⊲-tr (C.suc C.self) bV′) (sfxS c≤ hs))
       (nwAᴸ (proj₁ (sfxS c≤ hs)) (h (⊲-tr ap p) (⊲-tr ap′ p′) lc lc′ (posCP hap H e e′ c≤ hs)))
  cutR (aR H) ap ap′ hap e e′ bV bV′ hs =
    prᴸ (cutR H ap ap′ hap e e′ bV (⊲-tr (C.suc C.self) bV′) (extR (C.suc C.self) hs))
  cutR (aRL {n′ = n′} H) ap ap′ hap e e′ bV bV′ hs =
    prᴸ (cutR H ap ap′ hap e e′ bV (⊲-tr (C.lim n′ C.self) bV′) (extR (C.lim n′ C.self) hs))
  cutR (aL {f = f} {n} {f′ = f′} {n′} {p} {p′} {stp} {wl} {stp′} {wl′} H G) ap ap′ hap e e′ bV bV′ hs =
    ⨾ᴸ (cutR H ap ap′ hap e e′ (⊲-tr (C.lim n C.self) bV) (⊲-tr (C.lim n′ C.self) bV′) (cp-tr (W.limSelf 0) hs))
       (nlᴸ (λ m → cutR (G m) (⊲-tr ap (tailP f stp p m)) (⊲-tr ap′ (tailP f′ stp′ p′ m)) (W.hapT hap e e′ m) (W.eaT m) (W.eaT′ m)
                        (⊲-tr (C.lim (suc (m + n)) C.self) bV) (⊲-tr (C.lim (suc (m + n′)) C.self) bV′) (cp-tr (W.limSelf (suc m)) hs)))
    where module W = LimW H G (proj₁ (cp-coh hs)) (proj₂ (cp-coh hs))
```

## 2 分支函数的前提, 沿扩张搬运

```agda
UH : ∀ {ly k W W′} (lW : Lg W) (lW′ : Lg W′) → (∀ {W₂} → W ⊲ W₂ → Lg W₂ → D k W₂ → D ly W₂) → (∀ {W₂} → W′ ⊲ W₂ → Lg W₂ → D k W₂ → D ly W₂) → Set
UH {ly} {k} {W} {W′} lW lW′ uu uu′ =
  ∀ {W₂ W₂′} (p : W ⊲ W₂) (p′ : W′ ⊲ W₂′) (l₂ : Lg W₂) (l₂′ : Lg W₂′) → CP lW lW′ p l₂ p′ l₂′ →
  ∀ y y′ → Rel k l₂ l₂′ y y′ → Rel ly l₂ l₂′ (uu p l₂ y) (uu′ p′ l₂′ y′)

uh↾ : ∀ {ly k W W′ W₁ W₁′} {lW : Lg W} {lW′ : Lg W′} {l₁ : Lg W₁} {l₁′ : Lg W₁′} {p : W ⊲ W₁} {p′ : W′ ⊲ W₁′}
        {uu : ∀ {W₂} → W ⊲ W₂ → Lg W₂ → D k W₂ → D ly W₂} {uu′ : ∀ {W₂} → W′ ⊲ W₂ → Lg W₂ → D k W₂ → D ly W₂} →
      AP lW lW′ p l₁ p′ l₁′ → UH lW lW′ uu uu′ → UH l₁ l₁′ (λ p₂ → uu (⊲-tr p p₂)) (λ p₂ → uu′ (⊲-tr p′ p₂))
uh↾ {p = p} {p′} ap U p₂ p₂′ l l′ cp = U (⊲-tr p p₂) (⊲-tr p′ p₂′) l l′ (cp-tr ap cp)
```

## 3 `IW`

```agda
module IWm {ly k W₀ W₀′ W W′} {lW₀ : Lg W₀} {lW₀′ : Lg W₀′} {lW : Lg W} {lW′ : Lg W′} (ac ac₂ : AccY k)
           {v : ∀ {c} → W₀ ⊲ c → Lg c → D k c} {v′ : ∀ {c} → W₀′ ⊲ c → Lg c → D k c}
           (h : ∀ {c c′} (P : W₀ ⊲ c) (P′ : W₀′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CP lW₀ lW₀′ P lc P′ lc′ → Rel k lc lc′ (v P lc) (v′ P′ lc′))
           (zy zy′ : NZ ly) (mk : ∀ {W₁ j} → W ⊲ W₁ → StH W₁ j k → StH W₁ j ly) (mk′ : ∀ {W₁ j} → W′ ⊲ W₁ → StH W₁ j k → StH W₁ j ly)
           (uu : ∀ {W₂} → W ⊲ W₂ → Lg W₂ → D k W₂ → D ly W₂) (uu′ : ∀ {W₂} → W′ ⊲ W₂ → Lg W₂ → D k W₂ → D ly W₂)
           (IH : ∀ {c c′} (P : W₀ ⊲ c) (P′ : W₀′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CP lW₀ lW₀′ P lc P′ lc′ →
                 (q : c ⊲ W) (q′ : c′ ⊲ W′) → CP lc lc′ q lW q′ lW′ → ∀ co co′ → Rel k lW lW′ co co′ →
                 Rel ly lW lW′ (Int ac (v P lc) q lW zy mk uu co) (Int ac₂ (v′ P′ lc′) q′ lW′ zy′ mk′ uu′ co′)) where
  open CutR h

  iwR : ∀ {L L′ a b a′ b′} {p : a ⊲ b} {lb : Lg b} {p′ : a′ ⊲ b′} {lb′ : Lg b′} → Al L L′ p lb p′ lb′ →
        ∀ {la la′} (ap : W₀ ⊲ a) (ap′ : W₀′ ⊲ a′) → AP lW₀ lW₀′ ap la ap′ la′ → la ≡ lg⊲ p lb → la′ ≡ lg⊲ p′ lb′ →
        (bW : b ⊲ W) (bW′ : b′ ⊲ W′) → CP lb lb′ bW lW bW′ lW′ → ∀ {co co′} → Rel k lW lW′ co co′ →
        Rel ly lW lW′ (IW ac v b p ap lb bW lW zy mk uu co) (IW ac₂ v′ b′ p′ ap′ lb′ bW′ lW′ zy′ mk′ uu′ co′)
  iwR (aS p′ lb′) ap ap′ hap e e′ bW bW′ hs hco = n0ᴸ
  iwR (aP {c = c} {c′ = c′} {p = p} {lc} {p′} {lc′} H c≤ ad) ap ap′ hap e e′ bW bW′ hs hco =
    ⨾ᴸ (iwR H ap ap′ hap e e′ _ _ (sfxS c≤ hs) hco)
       (IH (⊲-tr ap p) (⊲-tr ap′ p′) lc lc′ (posCP hap H e e′ c≤ hs) _ _ (sfxS c≤ hs) _ _
           (⨾ᴸ hco (cutR H ap ap′ hap e e′ _ _ (sfxS c≤ hs))))
  iwR (aR H) ap ap′ hap e e′ bW bW′ hs hco =
    prᴸ (iwR H ap ap′ hap e e′ bW (⊲-tr (C.suc C.self) bW′) (extR (C.suc C.self) hs) hco)
  iwR (aRL {n′ = n′} H) ap ap′ hap e e′ bW bW′ hs hco =
    prᴸ (iwR H ap ap′ hap e e′ bW (⊲-tr (C.lim n′ C.self) bW′) (extR (C.lim n′ C.self) hs) hco)
  iwR (aL {f = f} {n} {f′ = f′} {n′} {p} {p′} {stp} {wl} {stp′} {wl′} H G) ap ap′ hap e e′ bW bW′ hs hco =
    ⨾ᴸ (iwR H ap ap′ hap e e′ _ _ (cp-tr (W.limSelf 0) hs) hco)
       (nlᴸ (λ m → iwR (G m) (⊲-tr ap (tailP f stp p m)) (⊲-tr ap′ (tailP f′ stp′ p′ m)) (W.hapT hap e e′ m) (W.eaT m) (W.eaT′ m)
                       _ _ (cp-tr (W.limSelf (suc m)) hs)
                       (⨾ᴸ hco (cutR (W.TP m) ap ap′ hap (W.eqA e m) (W.eqA′ e′ m) _ _ (cp-tr (W.limSelf m) hs)))))
    where module W = LimW H G (proj₁ (cp-coh hs)) (proj₂ (cp-coh hs))
```

## 4 `Int` 的两世界单调

```agda
IntM : ∀ {ly k W₀ W₀′ W W′} {lW₀ : Lg W₀} {lW₀′ : Lg W₀′} {lW : Lg W} {lW′ : Lg W′} (ac ac₂ : AccY k) {z : D k W₀} {z′ : D k W₀′} →
       Rel k lW₀ lW₀′ z z′ → ∀ {q₀ : W₀ ⊲ W} {q₀′ : W₀′ ⊲ W′} → CP lW₀ lW₀′ q₀ lW q₀′ lW′ →
       (zy zy′ : NZ ly) (mk : ∀ {W₁ j} → W ⊲ W₁ → StH W₁ j k → StH W₁ j ly) (mk′ : ∀ {W₁ j} → W′ ⊲ W₁ → StH W₁ j k → StH W₁ j ly)
       (uu : ∀ {W₂} → W ⊲ W₂ → Lg W₂ → D k W₂ → D ly W₂) (uu′ : ∀ {W₂} → W′ ⊲ W₂ → Lg W₂ → D k W₂ → D ly W₂) →
       UH lW lW′ uu uu′ → ∀ {w w′} → Rel k lW lW′ w w′ →
       Rel ly lW lW′ (Int ac z q₀ lW zy mk uu w) (Int ac₂ z′ q₀′ lW′ zy′ mk′ uu′ w′)
IntM ac ac₂ n0ᴸ hq zy zy′ mk mk′ uu uu′ U hw = n0ᴸ
IntM ac ac₂ n1ᴸ hq zy zy′ mk mk′ uu uu′ U hw = U C.self C.self _ _ (cp-top hq) _ _ hw
IntM ac ac₂ (⨾ᴸ hx hy) hq zy zy′ mk mk′ uu uu′ U hw =
  ⨾ᴸ (IntM ac ac₂ hx hq zy zy′ mk mk′ uu uu′ U hw) (IntM ac ac₂ hy hq zy zy′ mk mk′ uu uu′ U (⨾ᴸ hw (nwAᴸ (proj₁ hq) hx)))
IntM {k = k} {lW = lW} {lW′} ac ac₂ (nlᴸ {d = d} {d′} hd) {q₀} {q₀′} hq zy zy′ mk mk′ uu uu′ U hw =
  nlᴸ (λ n → IntM ac ac₂ (hd n) hq zy zy′ mk mk′ uu uu′ U (⨾ᴸ hw (preR n)))
  where
  preR : ∀ n → Rel k lW lW′ (Pre q₀ d n) (Pre q₀′ d′ n)
  preR zero = n0ᴸ
  preR (suc n) = ⨾ᴸ (preR n) (nwAᴸ (proj₁ hq) (hd n))
IntM ac ac₂ (prᴸ hx) hq zy zy′ mk mk′ uu uu′ U hw = prᴸ (IntM ac ac₂ hx hq zy zy′ mk mk′ uu uu′ U hw)
IntM ac ac₂ (nwAᴸ hp hx) hq zy zy′ mk mk′ uu uu′ U hw = IntM ac ac₂ hx (cp-tr hp hq) zy zy′ mk mk′ uu uu′ U hw
IntM {ly} {k} (acc g) (acc g₂) (niᴸ {r = R} {r′ = R′} {u = v} {u′ = v′} h) {q₀} {q₀′} hq zy zy′ mk mk′ uu uu′ U {w} {w′} hw =
  niᴸ (λ p p′ lc lc′ cpp y y′ hb →
    IntM (acc g) (acc g₂)
      (h (⊲-tr q₀ p) (⊲-tr q₀′ p′) lc lc′ (cp-tr (proj₁ hq) cpp) _ _
         (belowIn k R R′ (belowOut ly (mk C.self (Kup q₀ R)) (mk′ C.self (Kup q₀′ R′)) hb)))
      (cp-top cpp) zy zy′ (λ p₂ → mk (⊲-tr p p₂)) (λ p₂ → mk′ (⊲-tr p′ p₂)) (λ p₂ → uu (⊲-tr p p₂)) (λ p₂ → uu′ (⊲-tr p′ p₂))
      (uh↾ (proj₁ cpp) U)
      (⨾ᴸ (nwAᴸ (proj₁ cpp) hw)
          (IntM (g R) (g₂ R′) (belowOut ly (mk C.self (Kup q₀ R)) (mk′ C.self (Kup q₀′ R′)) hb) (cp-top cpp) (NZ-S R) (NZ-S R′)
                (mkOf R (⊲-tr q₀ p)) (mkOf R′ (⊲-tr q₀′ p′))
                (λ p₂ l₂ z₂ → v (⊲-tr (⊲-tr q₀ p) p₂) l₂ (inS R z₂)) (λ p₂ l₂ z₂ → v′ (⊲-tr (⊲-tr q₀′ p′) p₂) l₂ (inS R′ z₂))
                (λ p₂ p₂′ l₂ l₂′ cp₂ y₂ y₂′ h₂ →
                   h (⊲-tr (⊲-tr q₀ p) p₂) (⊲-tr (⊲-tr q₀′ p′) p₂′) l₂ l₂′ (cp-tr (ap-tr (proj₁ hq) (proj₁ cpp)) cp₂) _ _ (belowIn k R R′ h₂))
                n0ᴸ)))
IntM {ly} {k} ac ac₂ (κᴸ {u = v} {u′ = v′} h) {q₀} {q₀′} hq zy zy′ mk mk′ uu uu′ U {w} {w′} hw =
  ⨾ᴸ (IWm.iwR ac ac₂ h zy zy′ mk mk′ uu uu′
        (λ P P′ lc lc′ cp q q′ cq co co′ hco → IntM ac ac₂ (h P P′ lc lc′ cp) cq zy zy′ mk mk′ uu uu′ U hco)
        (proj₁ (proj₁ hq)) C.self C.self (ap-self _ _) (proj₁ (proj₂ (proj₂ (proj₁ hq)))) (proj₂ (proj₂ (proj₂ (proj₁ hq))))
        C.self C.self (cp-top hq) hw)
     (κᴸ (λ p p′ lc lc′ cpp →
        IntM ac ac₂ (h (⊲-tr q₀ p) (⊲-tr q₀′ p′) lc lc′ (cp-tr (proj₁ hq) cpp)) (cp-top cpp) zy zy′
          (λ p₂ → mk (⊲-tr p p₂)) (λ p₂ → mk′ (⊲-tr p′ p₂)) (λ p₂ → uu (⊲-tr p p₂)) (λ p₂ → uu′ (⊲-tr p′ p₂)) (uh↾ (proj₁ cpp) U)
          (⨾ᴸ (nwAᴸ (proj₁ cpp) hw)
              (CutR.cutR h (proj₁ (proj₁ (cp-tr (proj₁ hq) cpp))) C.self C.self (ap-self _ _)
                 (proj₁ (proj₂ (proj₂ (proj₁ (cp-tr (proj₁ hq) cpp))))) (proj₂ (proj₂ (proj₂ (proj₁ (cp-tr (proj₁ hq) cpp)))))
                 C.self C.self (cp-top cpp)))))
```
