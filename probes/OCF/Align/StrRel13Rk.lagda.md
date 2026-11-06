# 结构关系, 第十三轮 (一): 坐标层 $k\sqsubseteq k'$ 时两边 `rkT` 的取值

> 不读记号. 入口 [StrRel13](StrRel13.lagda.md). `StrRel11Rk.rk-agree` 说: 同一坐标层 $k$, 同一目标层 $t$, 两个世界上 `rkT` 同为 `rise` 或同为 `keep`. 坐标层不同 ($k$ 对 $k'$) 时它不适用. 本文证明它的跨层版 **`rk-mono`**: 若 $k\sqsubseteq_\infty k'$ (忘掉世界的第一位置, `StrRel11Rk._⊑∞_`), 两边的种类只有三种:
>
> | 左 ($k$) | 右 ($k'$) | 目标层 $t$ |
> |---|---|---|
> | `rise` | `rise` | $t\sqsubseteq k$ |
> | `keep` | `keep` | $k'\sqsubset t$ |
> | `keep` | `rise` | $k\sqsubset t\sqsubseteq k'$ (目标层夹在中间) |
>
> **"左升右留" 不出现** (它要 $t\sqsubseteq k\sqsubseteq k'\sqsubset t$, 严格部分成环, `StrRel11Rk.irr`). 所以 "一边升一边留" 只有一种方向: 左边留成第 $t$ 层的节点, 右边升成坐标层 $k'$ 的链. 三种都实际出现: [StrRel13Kr](StrRel13Kr.lagda.md) 的 `rkL`, `rkR` 是第三种的实例, 目标层取第 $0$ 层是第一种, 目标层取 $\Lambda$ 是第二种.
>
> 只用严格部分不成环, 不比较值. 前提是字面的 $k\sqsubseteq_\infty k'$; 对齐给出的坐标对一般只有值上的 $c\le c'$ (`Al` 的 `aP`), 这时 `emb c` 与 `emb c′` 之间可以没有 $\sqsubseteq_\infty$ (判断, 例: 两个值相等、写法不同的 $\omega$). 值上的版本要把高度映到值, 本文没有做.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
module OCF.Align.StrRel13Rk (Λ : H) (lΛ : LgH Λ) where

open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Align.CumReadCF using (A; Lg)
open import OCF.Align.HtFeedTree using (hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; StH; ss; sl; sL; cmpH)
open import OCF.Align.HtFeedClosed using (module At)
open import OCF.Align.StrRel11Rk Λ lΛ using (_⊑∞_; _⊏_; irr; ⊏⊑; tr∞; fg; fgS)

module P = At Λ lΛ
open P using (Rk; rise; keep; rkS; rkT)
```

## 1 三种

```agda
data RkX {k k′ t : H} {m m′ : A} : Rk k t m → Rk k′ t m′ → Set where
  rr : RkX rise rise
  kk : ∀ R R′ → RkX (keep R) (keep R′)
  kr : ∀ R → RkX (keep R) rise
```

## 2 证明

```agda
-- 左边升 (t ⊑ k ⊑ k′): 右边只能升
rR : ∀ {m m′ k k′ t} → t ⊑∞ k′ → (p′ : k′ ⊲[ m′ ] t) → RkX {k = k} {m = m} rise (rkS p′)
rR a hself = rr
rR {k′ = k′} a (hsuc p′) = ⊥-elim (irr k′ (⊏⊑ (fgS (ss p′)) a))
rR {k′ = k′} a (hlim n p′) = ⊥-elim (irr k′ (⊏⊑ (fgS (sl n p′)) a))
rR {k′ = k′} a (hLim e p′) = ⊥-elim (irr k′ (⊏⊑ (fgS (sL e p′)) a))

-- 右边升, 左边由 k ⊲ t 分类
lK : ∀ {m m′ k k′ t} (p : k ⊲[ m ] t) → RkX {k′ = k′} {m′ = m′} (rkS p) rise
lK hself = rr
lK (hsuc p) = kr (ss p)
lK (hlim n p) = kr (sl n p)
lK (hLim e p) = kr (sL e p)

-- 两边都由第一位置分类
lKK : ∀ {m m′ k k′ t} → k ⊑∞ k′ → (p : k ⊲[ m ] t) (p′ : k′ ⊲[ m′ ] t) → RkX (rkS p) (rkS p′)
lKK kk′ hself p′ = rR kk′ p′
lKK kk′ (hsuc p) hself = kr (ss p)
lKK kk′ (hsuc p) (hsuc p′) = kk _ _
lKK kk′ (hlim n p) hself = kr (sl n p)
lKK kk′ (hlim n p) (hlim n′ p′) = kk _ _
lKK kk′ (hLim e p) hself = kr (sL e p)
lKK kk′ (hLim e p) (hLim e′ p′) = kk _ _

rk-mono : ∀ {k k′ t m m′} → k ⊑∞ k′ →
          (km : k ⊲[ m ] Λ) (tm : t ⊲[ m ] Λ) (lm : Lg m) (km′ : k′ ⊲[ m′ ] Λ) (tm′ : t ⊲[ m′ ] Λ) (lm′ : Lg m′) →
          RkX (rkT km tm lm) (rkT km′ tm′ lm′)
rk-mono kk′ km tm lm km′ tm′ lm′ with cmpH km tm lm lΛ | cmpH km′ tm′ lm′ lΛ
... | inj₁ a | inj₁ b = rr
... | inj₁ a | inj₂ b = rR (tr∞ (fg a) kk′) b
... | inj₂ a | inj₁ b = lK a
... | inj₂ a | inj₂ b = lKK kk′ a b
```

## 3 结论 (定理)

`rk-mono`: 坐标层字面地 $k\sqsubseteq_\infty k'$ 时, 节点读数的种类对只有 (升, 升), (留, 留), (左留, 右升). `rk-agree` 是 $k=k'$ 的特例 (那时第三种也排除, 因为 $k\sqsubset t\sqsubseteq k$ 成环). 这把 "跨坐标层的节点规则" 的可靠性证明要处理的情形确定为三种; 第三种的输出是 "第 $t$ 层的节点" 对 "坐标层 $k'$ 的链的极限", 见 `StrRel13Kr`.
