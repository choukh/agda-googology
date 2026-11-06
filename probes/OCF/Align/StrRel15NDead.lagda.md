# 结构关系, 第十五轮的否定 (一): 混合种类的两条义务一出现就是假的; 两条状态律成立

> 不读记号. 入口 [StrRel15N](StrRel15N.lagda.md). 对着接口 [StrRel15If](StrRel15If.lagda.md) (定稿 2026-11-05 10:48) 写, 对一切合法的 $\Lambda$.
>
> 接口 §2 的输出关系 `OA²` 在跨目标层的目标对 (`TX`, 目标层 $t\sqsubseteq_\infty t'$) 上仍用 `StrRel14If.RelX t t′`. 节点在目标上的读数 (`RKi`) 按种类有两种字面形状: `rise` 给出链的极限 `nl …`, `keep R` 给出节点 `ni R …`. 而 `RelX` 的八个构造子里, 结论是 "左 `nl`, 右 `ni`" 或 "左 `ni`, 右 `nl`" 的一个也没有 (左 `n0` 的 `n0ˣ`, 两边同形的 `n1ˣ`/`⨾ˣ`/`nlˣ`/`nwˣ`/`niˣ`/`κˣ`, 右边 `⨾` 的 `prˣ`).
>
> 1. **(定理) `¬nlni`, `¬ninl`**: 对一切层 $t,t'$, `RelX t t′` 不含 (`nl d`, `ni r u`), 也不含 (`ni r u`, `nl d`).
> 2. **(定理) `rk-dead`, `kr-dead`**: 对 `NodeObl²` 的一切参数 (节点对, 运行世界, 路径, 动作, 上下文, **一切状态**) 与一切目标对, `Out² T T′ rise (keep R′)` 与 `Out² T T′ (keep R) rise` 都不成立. 所以 `OblRK²` 只在 "没有一个 `TX` 目标对实际给出左升右留" 时成立 (空真), `OblKR²` 同理; 一旦这种目标对存在, 义务就是假的 (`rk-dead⇒`, `kr-dead⇒`). 实例见 [StrRel15NNode](StrRel15NNode.lagda.md) (左升右留, **同一个节点**) 与 [StrRel15NKind](StrRel15NKind.lagda.md) (左留右升).
> 3. **(定理, 正面) `law⊕`, `lawcv`**: 接口 §3 的 `Law⊕` 与 `Lawcv` 对一切 $\Lambda$ 成立 (证明同 `StrRel12Sem.advRc`/`cvRc`, `NE` 一项用 `StrRel14J.ne⊕`/`necv`). 所以问题不在状态律, 在输出关系.
>
> **只否定什么.** 只否定: 以 `StrRel14If.RelX` 作跨目标层输出关系时的混合种类义务 (`OblRK²`, `OblKR²`) 在非空的情形. 与状态无关 (对一切状态, 不论是否满足 `J²`), 所以换任何状态不变量都救不回. **不否定**: 给跨目标层的输出关系另加 "极限对节点" / "节点对极限" 规则之后的版本 (那时要另看那些规则的语义; 见入口 §4); 不否定 `OblRR²`, `OblKK²`; 不否定 `LawKp`, `LawKb` (本文没有处理). 没有推出 LPO/WLPO 或判定: 种类由 `cmpH` 在一个世界里算出, 失败来自字面形状.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
module OCF.Align.StrRel15NDead (Λ : H) (lΛ : LgH Λ) where

open import Data.Nat using (ℕ)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
open import OCF.Align.HtFeedTree using (hz; StH; Vs; D; nl; ni; AccY)
open import OCF.Align.StrRel11Rk Λ lΛ using (_⊑∞_; s∞)
open import OCF.Align.StrRel12Al using (CP; cp-tr)
open import OCF.Align.StrRel14If Λ lΛ using (RelX; n0ˣ; ⨾ˣ)
open import OCF.Align.StrRel14J Λ lΛ using (ne⊕; necv)
open import OCF.Align.StrRel15If Λ lΛ
open P using (Tg; tg↑; τ₀; St; Df; d; z; cv; _⊕⟨_⟩_; Ig; LW; Rk; rise; keep)
```

## 1 `RelX` 没有 "极限对节点", 也没有 "节点对极限"

```agda
¬nlni : ∀ {t t′ V V′ k} {lV : Lg V} {lV′ : Lg V′} {e : ℕ → D t V} {r : StH V′ k t′}
          {u : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs t′ r W′ → D t′ W′} → ¬ RelX t t′ lV lV′ (nl e) (ni r u)
¬nlni ()

¬ninl : ∀ {t t′ V V′ k} {lV : Lg V} {lV′ : Lg V′} {r : StH V k t} {u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs t r W′ → D t W′}
          {e : ℕ → D t′ V′} → ¬ RelX t t′ lV lV′ (ni r u) (nl e)
¬ninl ()
```

## 2 混合种类的义务: 一出现就假

```agda
module Dead {L L′ V V′ k k′} {lV : Lg V} {lV′ : Lg V′} (r : StH V k L) (r′ : StH V′ k′ L′)
            (u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′) (u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ r′ W′ → D L′ W′)
            {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac₁ : AccY k) (ac′ : AccY L′) (ac₁′ : AccY k′)
            (q₀ : V ⊲ W) (q₀′ : V′ ⊲ W′) (ll : LW L W) (ll′ : LW L′ W′) (A₀ : Ig L W) (A₀′ : Ig L′ W′)
            (w : D L W) (w′ : D L′ W′) (Y : St W) (Y′ : St W′) where
  open NodeObl² {lV = lV} {lV′ = lV′} r r′ u u′ lW lW′ ac ac₁ ac′ ac₁′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′

  rk-dead : ∀ {t t′ m m′} (T : Tg W t m) (T′ : Tg W′ t′ m′) R′ → ¬ Out² T T′ rise (keep R′)
  rk-dead T T′ R′ = ¬nlni

  kr-dead : ∀ {t t′ m m′} (T : Tg W t m) (T′ : Tg W′ t′ m′) R → ¬ Out² T T′ (keep R) rise
  kr-dead T T′ R = ¬ninl

  -- 只要有一个 TX 目标对实际给出该种, 义务就不成立
  rk-dead⇒ : ∀ {t t′ m m′} (T : Tg W t m) (T′ : Tg W′ t′ m′) → TX lW lW′ T T′ → ∀ R′ → rkL T ≡ rise → rkR T′ ≡ keep R′ → ¬ OblRK²
  rk-dead⇒ T T′ tx R′ eL eR ob = rk-dead T T′ R′ (ob T T′ tx R′ eL eR)

  kr-dead⇒ : ∀ {t t′ m m′} (T : Tg W t m) (T′ : Tg W′ t′ m′) → TX lW lW′ T T′ → ∀ R → rkL T ≡ keep R → rkR T′ ≡ rise → ¬ OblKR²
  kr-dead⇒ T T′ tx R eL eR ob = kr-dead T T′ R (ob T T′ tx R eL eR)
```

## 3 两条状态律成立 (正面)

```agda
law⊕ : Law⊕
law⊕ {lW = lW} {lW′} tp Y Y′ Δ Δ′ ((r , rz) , (ne , ne′)) O =
  ((λ T T′ tx → ⨾ˣ (r T T′ tx) (O T T′ tx)) , ⨾ˣ rz (O (τ₀ lW) (τ₀ lW′) (tp , s∞))) ,
  (ne⊕ {lW = lW} Y Δ ne , ne⊕ {lW = lW′} Y′ Δ′ ne′)

lawcv : Lawcv
lawcv {q = q} {q′ = q′} ap Y Y′ ((r , rz) , (ne , ne′)) =
  ((λ T T′ tx → r (tg↑ q T) (tg↑ q′ T′) (cp-tr ap (proj₁ tx) , proj₂ tx)) , n0ˣ) ,
  (necv q Y ne , necv q′ Y′ ne′)
```
