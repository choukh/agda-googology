# 第十九轮的否定 (工具): `ActS` 动作的输出的形状

> 不读记号. 入口 [NegSR19](NegSR19.lagda.md). 对着接口 [StrRel19If](StrRel19If.lagda.md) (定稿 2026-11-05 16:01) §1 的 `ActS` 写. 一切 $\Lambda$.
>
> 1. **(定理) `goodRun`**: 动作的每个输出 (一切路径, 世界, 上下文, 状态, 一切层的目标) 都 "好" (`Good`: 不是 `n1`, 也不是 `a ⨾ n1` 的形状) 时, 以它运行任何树, 每个目标上的输出也都好. 理由是折叠的字面: `n0` 给 `n0`; `n1` 给动作的输出; `x ⨾ y` 给 "`x` 的输出 ⨾ `y` 的输出", 右边不是 `n1`; `nl` 给 `nl`; 节点在一切目标上给 `ni` (保留) 或 `nl` (上升); `nκ` 在第 $0$ 层目标上给 `nl` (回灌), 在别的层给 "`Kp` 的输出 ⨾ `nκ` …".
> 2. **(定理) `goodActS`**: `ActS` 的每个动作都好 (`Act` 给 `nl`; `Ig↾` 不变; `Ai` 是以好的动作运行分支, 用第 1 条).
> 3. **(定理) `¬ActS-Az`**: 读累计的动作 `Az⁰` (输出 "累计 ⨾ 1", 即 `NegSR17RkT.Az` 的形状) 不属于 `ActS`.
>
> **用处.** `NegSR19Tr` 用第 2 条对 `up` 的结论求逆: `up` 的右边是保留输出, 它的分支是 `ActS` 动作的分支动作的输出, 所以分支的值都好; `rk⁺⁺` 的右边可以用 `Az` (`rk⁺⁺` 的前提不要 `ActS`), 分支的值是 `… ⨾ n1`, 不好. 第 3 条是接口 "范围 (iii)" 说由构造一路编译的那一条; 本文用形状独立地证了一遍 (构造一路的证明本路未读).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
module OCF.Align.NegSR19Good (Λ : H) (lΛ : LgH Λ) where

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (hz; hs; hl; hΩ; D; D₀; n0; n1; _⨾_; nl; ni; nκ; nw; AccY; acc; StH; Vs; inS; Int; NZ-S; mkOf; ⊲ᴴ↑)
open import OCF.Align.StrRel16If Λ lΛ using (module P)
open import OCF.Align.StrRel19If Λ lΛ using (ActS; sAct; sIg↾; sAi)
open import OCF.Align.NegSR17RkT using (lift)

open P using (Tg; τ₀; St; st; Df; df; yc; z; zeroD; Run; RKi; RKy; Ig; Ig↾; LW; Ai; Act; Rk; rise; keep)
```

## 1 好的输出

```agda
snd : ∀ {t m} → D t m → D t m
snd (a ⨾ b) = b
snd x = x

Good : ∀ {t m} → D t m → Set
Good o = ¬ (o ≡ n1) × (∀ a → ¬ (o ≡ a ⨾ n1))

Bad : ∀ {t m} → D t m → Set
Bad {t} {m} o = Σ (D t m) (λ a → o ≡ a ⨾ n1)

good→¬bad : ∀ {t m} {o : D t m} → Good o → ¬ Bad o
good→¬bad g (a , e) = proj₂ g a e

GoodA : ∀ {L W} → Ig L W → Set
GoodA {L} {W} A₀ = ∀ {W₁} (p : W ⊲ W₁) (lW₁ : Lg W₁) (w : D L W₁) (Y : St W₁) {t m} (T : Tg W₁ t m) → Good (yc (A₀ p lW₁ w Y) T)

good⨾ : ∀ {t m} {a b : D t m} → ¬ (b ≡ n1) → Good (a ⨾ b)
good⨾ hb = (λ ()) , (λ a e → hb (cong snd e))

goodNl : ∀ {t m} {e : ℕ → D t m} → Good (nl e)
goodNl = (λ ()) , (λ a ())
```

## 2 以好的动作运行

```agda
goodRKi : ∀ {ly W₀ W k t m} (ac : AccY ly) (ac′ : AccY k) (r : StH W₀ k ly) (u : ∀ {W′} → W₀ ⊲ W′ → Lg W′ → Vs ly r W′ → D ly W′)
            (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W)
            (T : Tg W t m) (rk : Rk k t m) → Good (RKi ac ac′ r u q₀ lW ll A₀ w Y T rk)
goodRKi ac ac′ r u q₀ lW ll A₀ w Y T (keep R′) = (λ ()) , (λ a ())
goodRKi ac ac′ r u q₀ lW ll A₀ w Y T rise = goodNl

goodRKy : ∀ {ly W₀ W} (ac : AccY ly) (u : ∀ {c} → W₀ ⊲ c → Lg c → D ly c) (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : LW ly W) (A₀ : Ig ly W)
            (w : D ly W) (Y : St W) t {m} (T : Tg W t m) →
          Good (RKy ac u q₀ lW ll A₀ w Y t T)
goodRKy ac u q₀ lW ll A₀ w Y hz T = goodNl
goodRKy ac u q₀ lW ll A₀ w Y (hs b) T = good⨾ (λ ())
goodRKy ac u q₀ lW ll A₀ w Y (hl f) T = good⨾ (λ ())
goodRKy ac u q₀ lW ll A₀ w Y (hΩ g) T = good⨾ (λ ())

goodRun : ∀ {ly W₀ W} (ac : AccY ly) (x : D ly W₀) (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) →
          GoodA A₀ → ∀ {t m} (T : Tg W t m) → Good (yc (Run ac x q₀ lW ll A₀ w Y) T)
goodRun ac n0 q₀ lW ll A₀ w Y hA T = (λ ()) , (λ a ())
goodRun ac n1 q₀ lW ll A₀ w Y hA T = hA C.self lW w Y T
goodRun ac (x ⨾ y) q₀ lW ll A₀ w Y hA T =
  good⨾ (proj₁ (goodRun ac y q₀ lW ll A₀ (w ⨾ nw q₀ x) (Y P.⊕⟨ lW ⟩ Run ac x q₀ lW ll A₀ w Y) hA T))
goodRun ac (nl F) q₀ lW ll A₀ w Y hA T = goodNl
goodRun ac (nw p x) q₀ lW ll A₀ w Y hA T = goodRun ac x (⊲-tr p q₀) lW ll A₀ w Y hA T
goodRun (acc f) (ni r u) q₀ lW ll A₀ w Y hA T =
  goodRKi (acc f) (f r) r u q₀ lW ll A₀ w Y T (P.rkT (⊲ᴴ↑ (P.wm T) (P.kk r q₀ ll)) (P.tm T) (P.lm T))
goodRun ac (nκ zz u) q₀ lW ll A₀ w Y hA {t} T = goodRKy ac u q₀ lW ll A₀ w Y t T
```

## 3 `ActS` 的动作都好; `Az` 不属于 `ActS`

```agda
goodActS : ∀ {L W} {A₀ : Ig L W} → ActS A₀ → GoodA A₀
goodActS sAct p lW₁ w Y T = goodNl
goodActS (sIg↾ p h) p′ = goodActS h (⊲-tr p p′)
goodActS (sAi ac ac₁ r u q₀ hk ll {A₀} w h) p lW′ z′ Y′ T =
  goodRun ac (u (⊲-tr q₀ p) lW′ (inS r z′)) C.self lW′ (⊲ᴴ↑ p ll) (Ig↾ p A₀)
    (nw p w ⨾ Int ac₁ z′ C.self lW′ (NZ-S r) (mkOf r (⊲-tr q₀ p)) (λ p′ l′ z″ → u (⊲-tr (⊲-tr q₀ p) p′) l′ (inS r z″)) n0) Y′
    (λ p′ → goodActS h (⊲-tr p p′)) T

-- 读累计的动作 (NegSR17RkT.Az 的形状)
Az⁰ : ∀ {L W} → Ig L W
Az⁰ p l w Y = df (λ T → lift (z Y) ⨾ n1)

¬ActS-Az : ∀ {L W} (lW : Lg W) → ¬ ActS (Az⁰ {L} {W})
¬ActS-Az lW h = proj₂ (goodActS h C.self lW n0 (st zeroD n0) (τ₀ lW)) (lift n0) refl
```
