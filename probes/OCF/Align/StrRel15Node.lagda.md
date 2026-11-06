# 结构关系, 第十五轮 (二): 节点对归到四种义务; 左坐标层为 $0$ 时的升升与留留

> 不读记号. 入口 [StrRel15](StrRel15.lagda.md). 接口 [StrRel15If](StrRel15If.lagda.md).
>
> 1. **(条件定理) `Red².node-red²`**: 节点对 `ni r u` (坐标层 $k$) 与 `ni r′ u′` (坐标层 $k'$) 的 `SemX²` 由接口 §5 的四种义务 (`OblRR²`, `OblKK²`, `OblKR²`, `OblRK²`, 每种只在 `rkT` 实际给出该种时要求) 给出. 证明对两边 `rkT` 的值分四种情形; 折叠在节点处定义性地是 `RKi … (rkT …)`. 不用 $k\sqsubseteq_\infty k'$ (它只在义务里用).
> 2. **(条件定理) `Zero.oblRR`, `Zero.oblKK`**: 左坐标层为 $0$ ($r:\mathrm{StH}\,V\,0\,L$), 右坐标层 $k'$ 任意. 前提: 两边的运行世界 `Top` (只升升要), 分支动作 `Ai` 这一对满足 `HAW² hz k′`, 状态 `J²`. 结论: 升升义务与留留义务, 对一切 `TX` 目标对 (目标层可以不同).
>    - 升升: 两边的输出是坐标层 $0$ 与 $k'$ 的链的极限. 链的起点是状态在 (坐标层 $0$, 坐标层 $k'$) 这对目标上的读数, 由 `J²` 的跨目标层分量给出 `RelX hz k′` (这正是 `StrRel13Val.¬valX` 的反例状态不满足的那一条); 链的每一步是 `semX0` (左层为 $0$ 的语义) 在 (坐标层, 坐标层) 这对目标上的输出; 状态沿链用 `law⊕` 前进 (`Chain.cs`, 对 $n$ 归纳). 最后在给定的目标对上逐段 `nlˣ`.
>    - 留留: 两边的输出是节点 (第 $t$ 层坐标 $0$, 第 $t'$ 层坐标 $k'$), `niˣ` 的字面证据是 $0\sqsubseteq_\infty k'$ (`z⊑`). 分支是 `BNi`: 状态先换世界 (`lawcv`), 再加上输入的运行 (`semX0`, 动作沿路径搬运 `haw↾²`), 再交给分支动作 (`HAW²` 前提).
>
> **范围.** `oblRR`, `oblKK` 对左坐标层为 $0$ 的一切节点对、一切右坐标层、一切层 $\Lambda$ 成立, 前提只有 `HAW² hz k′` (分支动作) 与 `J²`. 分支动作的前提在 `StrRel15Fin` 里对 `xL`/`xR` (分支是常数 `n1`, 动作 `Act`, 有限的 $\Lambda$) 填上. 左留右升 (`OblKR²`) 与左升右留 (`OblRK²`) 本文不证; 它们在 `RelX` 里不成立, 见 [StrRel15Bar](StrRel15Bar.lagda.md).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
module OCF.Align.StrRel15Node (Λ : H) (lΛ : LgH Λ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (hz; StH; Vs; D; n0; _⨾_; ni; AccY; acc; ⊲ᴴ↑; outS)
open import OCF.Align.HtFeedClosed using (module At)
open import OCF.Align.StrRel12Al using (CP; cp-top; cp-tr)
open import OCF.Align.StrRel12Sem Λ lΛ using (Top)
open import OCF.Align.StrRel14If Λ lΛ using (RelX; n0ˣ; ⨾ˣ; nlˣ; niˣ)
open import OCF.Align.StrRel15If Λ lΛ using (TX; OA²; J²; HAW²; SemX²; module NodeObl²)
open import OCF.Align.StrRel15Sem Λ lΛ using (law⊕; lawcv; semX0; z⊑; sOutX; haw↾²)

module P = At Λ lΛ
open P using (Tg; tg; wm; tm; lm; St; Df; yc; d; cv; _⊕⟨_⟩_; Run; Ig; Ig↾; LW; Rk; rise; keep; rkT; RKi; BNi; Ai; Chn; kk)
```

## 1 节点对归到四种义务

```agda
module Red² {L L′ V V′ k k′} {lV : Lg V} {lV′ : Lg V′} (r : StH V k L) (r′ : StH V′ k′ L′)
            (u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′) (u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ r′ W′ → D L′ W′) where

  Obl : ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (f : ∀ {W₁ j} → StH W₁ j L → AccY j) (f′ : ∀ {W₁ j} → StH W₁ j L′ → AccY j)
        (q₀ : V ⊲ W) (q₀′ : V′ ⊲ W′) (ll : LW L W) (ll′ : LW L′ W′) (A₀ : Ig L W) (A₀′ : Ig L′ W′)
        (w : D L W) (w′ : D L′ W′) (Y : St W) (Y′ : St W′) → Set
  Obl lW lW′ f f′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′ =
    O.OblRR² × (O.OblKK² × (O.OblKR² × O.OblRK²))
    where module O = NodeObl² {lV = lV} {lV′ = lV′} r r′ u u′ lW lW′ (acc f) (f r) (acc f′) (f′ r′) q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′

  module Split {W W′} (lW : Lg W) (lW′ : Lg W′) (f : ∀ {W₁ j} → StH W₁ j L → AccY j) (f′ : ∀ {W₁ j} → StH W₁ j L′ → AccY j)
               (q₀ : V ⊲ W) (q₀′ : V′ ⊲ W′) (ll : LW L W) (ll′ : LW L′ W′) (A₀ : Ig L W) (A₀′ : Ig L′ W′)
               (w : D L W) (w′ : D L′ W′) (Y : St W) (Y′ : St W′) (ob : Obl lW lW′ f f′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′) where
    module O = NodeObl² {lV = lV} {lV′ = lV′} r r′ u u′ lW lW′ (acc f) (f r) (acc f′) (f′ r′) q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′

    go : ∀ {t t′ m m′} (T : Tg W t m) (T′ : Tg W′ t′ m′) → TX lW lW′ T T′ → ∀ (rk : Rk k t m) (rk′ : Rk k′ t′ m′) →
         O.rkL T ≡ rk → O.rkR T′ ≡ rk′ → O.Out² T T′ rk rk′
    go T T′ tx rise rise eL eR = proj₁ ob T T′ tx eL eR
    go T T′ tx (keep R) (keep R′) eL eR = proj₁ (proj₂ ob) T T′ tx R R′ eL eR
    go T T′ tx (keep R) rise eL eR = proj₁ (proj₂ (proj₂ ob)) T T′ tx R eL eR
    go T T′ tx rise (keep R′) eL eR = proj₂ (proj₂ (proj₂ ob)) T T′ tx R′ eL eR

  node-red² : (∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (f : ∀ {W₁ j} → StH W₁ j L → AccY j) (f′ : ∀ {W₁ j} → StH W₁ j L′ → AccY j)
                 (ll : LW L W) (ll′ : LW L′ W′) (q₀ : V ⊲ W) (q₀′ : V′ ⊲ W′) → CP lV lV′ q₀ lW q₀′ lW′ →
                 ∀ (A₀ : Ig L W) (A₀′ : Ig L′ W′) → HAW² L L′ lW lW′ A₀ A₀′ →
                 ∀ w w′ → RelX L L′ lW lW′ w w′ → ∀ (Y : St W) (Y′ : St W′) → J² lW lW′ Y Y′ →
                 Obl lW lW′ f f′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′) →
              SemX² L L′ lV lV′ (ni r u) (ni r′ u′)
  node-red² ob lW lW′ (acc f) (acc f′) ll ll′ q₀ q₀′ hq A₀ A₀′ ha w w′ hw Y Y′ hY T T′ tx =
    S.go T T′ tx _ _ refl refl
    where module S = Split lW lW′ f f′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′ (ob lW lW′ f f′ ll ll′ q₀ q₀′ hq A₀ A₀′ ha w w′ hw Y Y′ hY)
```

## 2 左坐标层为 $0$: 升升与留留

```agda
module Zero {L L′ V V′ k′} {lV : Lg V} {lV′ : Lg V′} (r : StH V hz L) (r′ : StH V′ k′ L′)
            (u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′) (u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ r′ W′ → D L′ W′)
            {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac₁ : AccY hz) (ac′ : AccY L′) (ac₁′ : AccY k′)
            (q₀ : V ⊲ W) (q₀′ : V′ ⊲ W′) (ll : LW L W) (ll′ : LW L′ W′) (A₀ : Ig L W) (A₀′ : Ig L′ W′)
            (w : D L W) (w′ : D L′ W′) (Y : St W) (Y′ : St W′) where
  open NodeObl² {lV = lV} {lV′ = lV′} r r′ u u′ lW lW′ ac ac₁ ac′ ac₁′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′ public

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

  module Chain (tp : Top lW lW′) (ha : HAW² hz k′ lW lW′ A² A²′) (hY : J² lW lW′ Y Y′) where
    CS : ℕ → Set
    CS n = RelX hz k′ lW lW′ (proj₁ (Ch n)) (proj₁ (Ch′ n)) ×
           (RelX hz k′ lW lW′ (proj₁ (proj₂ (Ch n))) (proj₁ (proj₂ (Ch′ n))) × J² lW lW′ (proj₂ (proj₂ (Ch n))) (proj₂ (proj₂ (Ch′ n))))

    OS : ∀ n → CS n → OA² lW lW′ (Run ac₁ (proj₁ (proj₂ (Ch n))) C.self lW hk A² (proj₁ (Ch n)) (proj₂ (proj₂ (Ch n))))
                                  (Run ac₁′ (proj₁ (proj₂ (Ch′ n))) C.self lW′ hk′ A²′ (proj₁ (Ch′ n)) (proj₂ (proj₂ (Ch′ n))))
    OS n (hc , (hy , hs)) = semX0 hy lW lW′ ac₁ ac₁′ hk hk′ C.self C.self tp A² A²′ ha _ _ hc _ _ hs

    cs : ∀ n → CS n
    cs zero = n0ˣ , (proj₁ (proj₁ hY) (tg C.self hk lW) (tg C.self hk′ lW′) (tp , z⊑ k′) , hY)
    cs (suc n) =
      ⨾ˣ (proj₁ (cs n)) (proj₁ (proj₂ (cs n))) ,
      (OS n (cs n) (tg C.self hk lW) (tg C.self hk′ lW′) (tp , z⊑ k′) ,
       law⊕ tp _ _ _ _ (proj₂ (proj₂ (cs n))) (OS n (cs n)))

  oblRR : Top lW lW′ → HAW² hz k′ lW lW′ A² A²′ → J² lW lW′ Y Y′ → OblRR²
  oblRR tp ha hY T T′ tx eL eR = nlˣ (λ n → K.OS n (K.cs n) T T′ tx)
    where module K = Chain tp ha hY

  -- 留留: 分支 BNi
  module Br (ha : HAW² hz k′ lW lW′ A² A²′) (hY : J² lW lW′ Y Y′)
            {c c′} (P : W ⊲ c) (P′ : W′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) (cpW : CP lW lW′ P lc P′ lc′)
            (z₁ : D hz c) (z₁′ : D k′ c′) (hz₁ : RelX hz k′ lc lc′ z₁ z₁′) where
    hcv = lawcv (proj₁ cpW) Y Y′ hY
    OΔ = semX0 hz₁ lc lc′ ac₁ ac₁′ (⊲ᴴ↑ P hk) (⊲ᴴ↑ P′ hk′) C.self C.self (cp-top cpW) (Ig↾ P A²) (Ig↾ P′ A²′)
               (haw↾² hz k′ (proj₁ cpW) ha) n0 n0 n0ˣ (cv P Y) (cv P′ Y′) hcv
    hYs = law⊕ (cp-top cpW) (cv P Y) (cv P′ Y′) _ _ hcv OΔ

    bni : OA² lc lc′ (BNi ac ac₁ r u q₀ ll A₀ w Y hk P lc z₁) (BNi ac′ ac₁′ r′ u′ q₀′ ll′ A₀′ w′ Y′ hk′ P′ lc′ z₁′)
    bni = ha P P′ lc lc′ cpW z₁ z₁′ hz₁ _ _ hYs

  oblKK : HAW² hz k′ lW lW′ A² A²′ → J² lW lW′ Y Y′ → OblKK²
  oblKK ha hY {t} {t′} T T′ tx R R′ eL eR =
    niˣ {r = R} {r′ = R′} (z⊑ k′)
      (λ p p′ lc lc′ cp y y′ hb →
         Br.bni ha hY (⊲-tr (wm T) p) (⊲-tr (wm T′) p′) lc lc′ (cp-tr (proj₁ (proj₁ tx)) cp) (outS R y) (outS R′ y′) (sOutX t R k′ hb)
           (tg C.self (⊲ᴴ↑ p (tm T)) lc) (tg C.self (⊲ᴴ↑ p′ (tm T′)) lc′)
           (cp-top (cp-tr (proj₁ (proj₁ tx)) cp) , proj₂ tx))
```
