# 结构关系, 第十六轮 (六): 以 `RelX⁺` 为结论重证升升与留留 (左坐标层为 $0$)

> 不读记号. 入口 [StrRel16](StrRel16.lagda.md). 接口 [StrRel16If](StrRel16If.lagda.md).
>
> **(条件定理) `Zero².oblRR`, `Zero².oblKK`**: `StrRel15Node.Zero` 的证明逐句搬到 `RelX⁺`/`J²⁺`/`HAW²⁺` (由脚本式替换得到, 手工检查): 左坐标层 $0$, 右坐标层 $k'$ 任意, 结论 `OblRR²⁺`, `OblKK²⁺`. 唯一多出的前提是模块参数 `sem0`: 坐标层上 (`hz` 对 $k'$) 的 `RelX⁺ ⇒ SemX²⁺`. 它的两个来源:
>
> - $k'=0$: `StrRel16Sem.semX00⁺`, 无条件 (**`rr00`, `kk00`**: 两个坐标层都是 $0$ 时, 升升与留留无条件成立, 前提只剩 `Top`, 分支动作的 `HAW²⁺`, `J²⁺`).
> - 一般的 $k'$: `StrRel16Sem.Zero⁺.semX0⁺`, 以 `RkSound₀ k′` 为条件 (**`rrRk`, `kkRk`**).
>
> 辅助 `sOutX⁺` (从 `BelowX⁺` 取出坐标层上的 `RelX⁺`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
module OCF.Align.StrRel16Node (Λ : H) (lΛ : LgH Λ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; StH; ss; sl; sL; Vs; D; n0; _⨾_; ni; AccY; acc; ⊲ᴴ↑; outS)
open import OCF.Align.StrRel12Al using (CP; cp-top; cp-tr)
open import OCF.Align.StrRel12Sem Λ lΛ using (Top)
open import OCF.Align.StrRel15If Λ lΛ using (TX)
open import OCF.Align.StrRel15Sem Λ lΛ using (z⊑)
open import OCF.Align.StrRel16If Λ lΛ
open import OCF.Align.StrRel16Sem Λ lΛ using (law⊕⁺; lawcv⁺; haw↾²⁺; semX00⁺; module Zero⁺)

open P using (Tg; tg; wm; tm; lm; St; Df; yc; d; cv; _⊕⟨_⟩_; Run; Ig; Ig↾; LW; Rk; rkT; RKi; BNi; Ai; Chn; kk; rise; keep)
```

## 1 坐标层上的关系

```agda
atOutX⁺ : ∀ b {V k} (Q : k ⊲[ V ] b) k′ {c c′} {lc : Lg c} {lc′ : Lg c′} {y : D k c} {y′ : D k′ c′} →
          RelAtX⁺ b Q k′ lc lc′ y y′ → RelX⁺ k k′ lc lc′ y y′
atOutX⁺ b hself k′ h = h
atOutX⁺ (hs b) (hsuc Q) k′ h = atOutX⁺ b Q k′ h
atOutX⁺ (hl f) (hlim n Q) k′ h = atOutX⁺ (f n) Q k′ h
atOutX⁺ (hΩ g) (hLim e Q) k′ h = atOutX⁺ (g _) Q k′ h

sOutX⁺ : ∀ L {V k} (r : StH V k L) k′ {c c′} {lc : Lg c} {lc′ : Lg c′} {y : D k c} {y′ : D k′ c′} →
         RelSX⁺ L r k′ lc lc′ y y′ → RelX⁺ k k′ lc lc′ y y′
sOutX⁺ (hs b) (ss Q) = atOutX⁺ b Q
sOutX⁺ (hl f) (sl n Q) = atOutX⁺ (f n) Q
sOutX⁺ (hΩ g) (sL e Q) = atOutX⁺ (g _) Q
```

## 2 左坐标层为 $0$: 升升与留留, 以坐标层上的语义为参数

```agda
module Zero² {L L′ V V′ k′} {lV : Lg V} {lV′ : Lg V′} (r : StH V hz L) (r′ : StH V′ k′ L′)
            (u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′) (u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ r′ W′ → D L′ W′)
            {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac₁ : AccY hz) (ac′ : AccY L′) (ac₁′ : AccY k′)
            (q₀ : V ⊲ W) (q₀′ : V′ ⊲ W′) (ll : LW L W) (ll′ : LW L′ W′) (A₀ : Ig L W) (A₀′ : Ig L′ W′)
            (w : D L W) (w′ : D L′ W′) (Y : St W) (Y′ : St W′)
            (sem0 : ∀ {c c′} {lc : Lg c} {lc′ : Lg c′} {x : D hz c} {x′ : D k′ c′} → RelX⁺ hz k′ lc lc′ x x′ → SemX²⁺ hz k′ lc lc′ x x′) where
  open NodeObl²⁺ {lV = lV} {lV′ = lV′} r r′ u u′ lW lW′ ac ac₁ ac′ ac₁′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′ public

  hk : LW hz W
  hk = kk r q₀ ll
  hk′ : LW k′ W′
  hk′ = kk r′ q₀′ ll′

  A² : Ig hz W
  A² = Ai ac ac₁ r u q₀ hk ll A₀ w
  A²′ : Ig k′ W′
  A²′ = Ai ac′ ac₁′ r′ u′ q₀′ hk′ ll′ A₀′ w′

  Ch : ℕ → D hz W × (D hz W × St W)
  Ch = Chn ac₁ hk lW A² Y
  Ch′ : ℕ → D k′ W′ × (D k′ W′ × St W′)
  Ch′ = Chn ac₁′ hk′ lW′ A²′ Y′

  module Chain (tp : Top lW lW′) (ha : HAW²⁺ hz k′ lW lW′ A² A²′) (hY : J²⁺ lW lW′ Y Y′) where
    CS : ℕ → Set
    CS n = RelX⁺ hz k′ lW lW′ (proj₁ (Ch n)) (proj₁ (Ch′ n)) ×
           (RelX⁺ hz k′ lW lW′ (proj₁ (proj₂ (Ch n))) (proj₁ (proj₂ (Ch′ n))) × J²⁺ lW lW′ (proj₂ (proj₂ (Ch n))) (proj₂ (proj₂ (Ch′ n))))

    OS : ∀ n → CS n → OA²⁺ lW lW′ (Run ac₁ (proj₁ (proj₂ (Ch n))) C.self lW hk A² (proj₁ (Ch n)) (proj₂ (proj₂ (Ch n))))
                                  (Run ac₁′ (proj₁ (proj₂ (Ch′ n))) C.self lW′ hk′ A²′ (proj₁ (Ch′ n)) (proj₂ (proj₂ (Ch′ n))))
    OS n (hc , (hy , hS)) = sem0 hy lW lW′ ac₁ ac₁′ hk hk′ C.self C.self tp A² A²′ ha _ _ hc _ _ hS

    cs : ∀ n → CS n
    cs zero = n0⁺ , (proj₁ (proj₁ hY) (tg C.self hk lW) (tg C.self hk′ lW′) (tp , z⊑ k′) , hY)
    cs (suc n) =
      ⨾⁺ (proj₁ (cs n)) (proj₁ (proj₂ (cs n))) ,
      (OS n (cs n) (tg C.self hk lW) (tg C.self hk′ lW′) (tp , z⊑ k′) ,
       law⊕⁺ tp _ _ _ _ (proj₂ (proj₂ (cs n))) (OS n (cs n)))

  oblRR : Top lW lW′ → HAW²⁺ hz k′ lW lW′ A² A²′ → J²⁺ lW lW′ Y Y′ → OblRR²⁺
  oblRR tp ha hY T T′ tx eL eR = nl⁺ (λ n → K.OS n (K.cs n) T T′ tx)
    where module K = Chain tp ha hY

  -- 留留: 分支 BNi
  module Br (ha : HAW²⁺ hz k′ lW lW′ A² A²′) (hY : J²⁺ lW lW′ Y Y′)
            {c c′} (P : W ⊲ c) (P′ : W′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) (cpW : CP lW lW′ P lc P′ lc′)
            (z₁ : D hz c) (z₁′ : D k′ c′) (hz₁ : RelX⁺ hz k′ lc lc′ z₁ z₁′) where
    hcv = lawcv⁺ (proj₁ cpW) Y Y′ hY
    OΔ = sem0 hz₁ lc lc′ ac₁ ac₁′ (⊲ᴴ↑ P hk) (⊲ᴴ↑ P′ hk′) C.self C.self (cp-top cpW) (Ig↾ P A²) (Ig↾ P′ A²′)
               (haw↾²⁺ hz k′ (proj₁ cpW) ha) n0 n0 n0⁺ (cv P Y) (cv P′ Y′) hcv
    hYs = law⊕⁺ (cp-top cpW) (cv P Y) (cv P′ Y′) _ _ hcv OΔ

    bni : OA²⁺ lc lc′ (BNi ac ac₁ r u q₀ ll A₀ w Y hk P lc z₁) (BNi ac′ ac₁′ r′ u′ q₀′ ll′ A₀′ w′ Y′ hk′ P′ lc′ z₁′)
    bni = ha P P′ lc lc′ cpW z₁ z₁′ hz₁ _ _ hYs

  oblKK : HAW²⁺ hz k′ lW lW′ A² A²′ → J²⁺ lW lW′ Y Y′ → OblKK²⁺
  oblKK ha hY {t} {t′} T T′ tx R R′ eL eR =
    ni⁺ {r = R} {r′ = R′} (z⊑ k′)
      (λ p p′ lc lc′ cp y y′ hb →
         Br.bni ha hY (⊲-tr (wm T) p) (⊲-tr (wm T′) p′) lc lc′ (cp-tr (proj₁ (proj₁ tx)) cp) (outS R y) (outS R′ y′) (sOutX⁺ t R k′ hb)
           (tg C.self (⊲ᴴ↑ p (tm T)) lc) (tg C.self (⊲ᴴ↑ p′ (tm T′)) lc′)
           (cp-top (cp-tr (proj₁ (proj₁ tx)) cp) , proj₂ tx))
```

## 3 两种来源

```agda
module Z00 {L L′ V V′} {lV : Lg V} {lV′ : Lg V′} (r : StH V hz L) (r′ : StH V′ hz L′)
           (u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′) (u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ r′ W′ → D L′ W′)
           {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac₁ : AccY hz) (ac′ : AccY L′) (ac₁′ : AccY hz)
           (q₀ : V ⊲ W) (q₀′ : V′ ⊲ W′) (ll : LW L W) (ll′ : LW L′ W′) (A₀ : Ig L W) (A₀′ : Ig L′ W′)
           (w : D L W) (w′ : D L′ W′) (Y : St W) (Y′ : St W′) where
  module Z = Zero² {lV = lV} {lV′ = lV′} r r′ u u′ {W} {W′} lW lW′ ac ac₁ ac′ ac₁′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′ semX00⁺
  rr00 : Top lW lW′ → HAW²⁺ hz hz lW lW′ Z.A² Z.A²′ → J²⁺ lW lW′ Y Y′ → Z.OblRR²⁺
  rr00 = Z.oblRR
  kk00 : HAW²⁺ hz hz lW lW′ Z.A² Z.A²′ → J²⁺ lW lW′ Y Y′ → Z.OblKK²⁺
  kk00 = Z.oblKK

module ZRk {L L′ V V′ k′} {lV : Lg V} {lV′ : Lg V′} (rkS : RkSound₀ k′) (r : StH V hz L) (r′ : StH V′ k′ L′)
           (u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′) (u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ r′ W′ → D L′ W′)
           {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac₁ : AccY hz) (ac′ : AccY L′) (ac₁′ : AccY k′)
           (q₀ : V ⊲ W) (q₀′ : V′ ⊲ W′) (ll : LW L W) (ll′ : LW L′ W′) (A₀ : Ig L W) (A₀′ : Ig L′ W′)
           (w : D L W) (w′ : D L′ W′) (Y : St W) (Y′ : St W′) where
  module Z = Zero² {lV = lV} {lV′ = lV′} r r′ u u′ {W} {W′} lW lW′ ac ac₁ ac′ ac₁′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′ (Zero⁺.semX0⁺ k′ rkS)
  rrRk : Top lW lW′ → HAW²⁺ hz k′ lW lW′ Z.A² Z.A²′ → J²⁺ lW lW′ Y Y′ → Z.OblRR²⁺
  rrRk = Z.oblRR
  kkRk : HAW²⁺ hz k′ lW lW′ Z.A² Z.A²′ → J²⁺ lW lW′ Y Y′ → Z.OblKK²⁺
  kkRk = Z.oblKK
```
