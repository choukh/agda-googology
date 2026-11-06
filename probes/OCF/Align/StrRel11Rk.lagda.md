# 结构关系, 第十一轮: 两个世界上 `rkT` 的取值一致

> 不读记号. 入口 [StrRel11](StrRel11.lagda.md). 节点 (`RunNi`) 在目标 $T$ 上的读数按 `rkT (kk r q₀ ll) (tm T) (lm T)` 分两种: `rise` (输出是坐标层的链) 与 `keep R` (输出是同一种节点). `MonoPort6Snd.Node.step` 只有一个世界, 两边算的是同一个 `rkT`. 两个世界 $m, m'$ 上, `cmpH` 走的路径不同, 结果的证明项也不同. 本文证明: **两边的种类总是一致** (`rk-agree`): 同为 `rise`, 或同为 `keep` (各带自己的 `StH` 证明). 证明不看值, 只用 "第一位置的严格部分不成环" (`irr`): 把世界下标忘掉 (`⊑∞`), 严格的第一位置不能回到自己. 所以两世界的 `Node.step` 只要处理 `rise/rise` 与 `keep/keep`, 不会出现 "一边是链, 一边是节点".

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
module OCF.Align.StrRel11Rk (Λ : H) (lΛ : LgH Λ) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Align.CumReadCF using (A; Lg)
open import OCF.Align.HtFeedTree using (hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; StH; ss; sl; sL; cmpH)
open import OCF.Align.HtFeedClosed using (module At)

module P = At Λ lΛ
open P using (Rk; rise; keep; rkS; rkT)
```

## 1 忘掉世界的第一位置, 严格部分不成环

```agda
infix 4 _⊑∞_ _⊏_
data _⊑∞_ : H → H → Set where
  s∞ : ∀ {a} → a ⊑∞ a
  u∞ : ∀ {a b} → a ⊑∞ b → a ⊑∞ hs b
  l∞ : ∀ {a f} n → a ⊑∞ f n → a ⊑∞ hl f
  L∞ : ∀ {a g} c → a ⊑∞ g c → a ⊑∞ hΩ g

data _⊏_ : H → H → Set where
  cs : ∀ {a b} → a ⊑∞ b → a ⊏ hs b
  cl : ∀ {a f} n → a ⊑∞ f n → a ⊏ hl f
  cL : ∀ {a g} c → a ⊑∞ g c → a ⊏ hΩ g

tr∞ : ∀ {a b c} → a ⊑∞ b → b ⊑∞ c → a ⊑∞ c
tr∞ p s∞ = p
tr∞ p (u∞ q) = u∞ (tr∞ p q)
tr∞ p (l∞ n q) = l∞ n (tr∞ p q)
tr∞ p (L∞ c q) = L∞ c (tr∞ p q)

⊏⊑ : ∀ {a b c} → a ⊏ b → b ⊑∞ c → a ⊏ c
⊏⊑ r s∞ = r
⊏⊑ r (u∞ q) = cs (tr∞ (⊏→⊑ r) q)
  where
  ⊏→⊑ : ∀ {a b} → a ⊏ b → a ⊑∞ b
  ⊏→⊑ (cs p) = u∞ p
  ⊏→⊑ (cl n p) = l∞ n p
  ⊏→⊑ (cL c p) = L∞ c p
⊏⊑ r (l∞ n q) = cl n (tr∞ (⊏→⊑′ r) q)
  where
  ⊏→⊑′ : ∀ {a b} → a ⊏ b → a ⊑∞ b
  ⊏→⊑′ (cs p) = u∞ p
  ⊏→⊑′ (cl n p) = l∞ n p
  ⊏→⊑′ (cL c p) = L∞ c p
⊏⊑ r (L∞ c q) = cL c (tr∞ (⊏→⊑″ r) q)
  where
  ⊏→⊑″ : ∀ {a b} → a ⊏ b → a ⊑∞ b
  ⊏→⊑″ (cs p) = u∞ p
  ⊏→⊑″ (cl n p) = l∞ n p
  ⊏→⊑″ (cL c p) = L∞ c p

irr : ∀ b → b ⊏ b → ⊥
irr hz ()
irr (hs b) (cs h) = irr b (⊏⊑ (cs s∞) h)
irr (hl f) (cl n h) = irr (f n) (⊏⊑ (cl n s∞) h)
irr (hΩ g) (cL c h) = irr (g c) (⊏⊑ (cL c s∞) h)

fg : ∀ {a b W} → a ⊲[ W ] b → a ⊑∞ b
fg hself = s∞
fg (hsuc p) = u∞ (fg p)
fg (hlim n p) = l∞ n (fg p)
fg (hLim {c = c} e p) = L∞ c (fg p)

fgS : ∀ {W k t} → StH W k t → k ⊏ t
fgS (ss P) = cs (fg P)
fgS (sl n P) = cl n (fg P)
fgS (sL {c = c} e P) = cL c (fg P)

-- 一个世界里 k 严格在 t 之下, 另一个世界里 t 在 k 之下: 不可能
mix : ∀ {m m′ k t} → StH m k t → t ⊲[ m′ ] k → ⊥
mix {k = k} R P = irr k (⊏⊑ (fgS R) (fg P))
```

## 2 种类一致

```agda
data RkRel {k t : H} {m m′ : A} : Rk k t m → Rk k t m′ → Set where
  rr : RkRel rise rise
  kp : ∀ R R′ → RkRel (keep R) (keep R′)

-- 一边 t ⊲ k, 另一边 rkS (k ⊲ t): 只能是 hself
rise-rkS : ∀ {m m′ k t} → t ⊲[ m ] k → (p′ : k ⊲[ m′ ] t) → RkRel {m = m} rise (rkS p′)
rise-rkS a hself = rr
rise-rkS a (hsuc p′) = ⊥-elim (mix (ss p′) a)
rise-rkS a (hlim n p′) = ⊥-elim (mix (sl n p′) a)
rise-rkS a (hLim e p′) = ⊥-elim (mix (sL e p′) a)

rkS-rise : ∀ {m m′ k t} (p : k ⊲[ m ] t) → t ⊲[ m′ ] k → RkRel {m′ = m′} (rkS p) rise
rkS-rise hself a = rr
rkS-rise (hsuc p) a = ⊥-elim (mix (ss p) a)
rkS-rise (hlim n p) a = ⊥-elim (mix (sl n p) a)
rkS-rise (hLim e p) a = ⊥-elim (mix (sL e p) a)

-- rkS 的种类: hself 给 rise, 别的给 keep
rkS-kp : ∀ {m m′ k t} (p : k ⊲[ m ] t) (p′ : k ⊲[ m′ ] t) → RkRel (rkS p) (rkS p′)
rkS-kp hself p′ = rise-rkS hself p′
rkS-kp {k = k} (hsuc p) hself = ⊥-elim (irr k (fgS (ss p)))
rkS-kp {k = k} (hlim n p) hself = ⊥-elim (irr k (fgS (sl n p)))
rkS-kp {k = k} (hLim e p) hself = ⊥-elim (irr k (fgS (sL e p)))
rkS-kp (hsuc p) (hsuc p′) = kp _ _
rkS-kp (hlim n p) (hlim n′ p′) = kp _ _
rkS-kp (hLim e p) (hLim e′ p′) = kp _ _

rk-agree : ∀ {k t m m′} (km : k ⊲[ m ] Λ) (tm : t ⊲[ m ] Λ) (lm : Lg m) (km′ : k ⊲[ m′ ] Λ) (tm′ : t ⊲[ m′ ] Λ) (lm′ : Lg m′) →
           RkRel (rkT km tm lm) (rkT km′ tm′ lm′)
rk-agree km tm lm km′ tm′ lm′ with cmpH km tm lm lΛ | cmpH km′ tm′ lm′ lΛ
... | inj₁ a | inj₁ b = rr
... | inj₁ a | inj₂ b = rise-rkS a b
... | inj₂ a | inj₁ b = rkS-rise a b
... | inj₂ a | inj₂ b = rkS-kp a b
```

## 3 结论 (定理)

`rk-agree`: 对一切坐标层 $k$, 目标层 $t$, 两个世界 $m, m'$ 与其中的任意位置, 节点读数的种类一致. 不比较值, 不要 "树世界可比", 不判定极限点 (只用了归纳类型上严格子项不成环). 这是两世界版 `Node.step` 的第一块: `MonoPort6Snd.Node.rkRel` 对 `Rk` 的值分情形, 两世界时要对一对值分情形, `rk-agree` 说只有对角线上的两种.
