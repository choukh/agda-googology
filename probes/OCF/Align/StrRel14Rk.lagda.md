# 结构关系, 第十四轮 (五): 跨坐标层节点规则归到三种义务; κ 分支对的定义域

> 不读记号. 入口 [StrRel14](StrRel14.lagda.md). 接口 [StrRel14If](StrRel14If.lagda.md).
>
> 1. **(条件定理) `node-red`**: 坐标层字面地 $k\sqsubseteq_\infty k'$ 时, 异质节点对 `ni r u`/`ni r′ u′` 的语义 `SemX` 由三种义务 (`NodeObl⁼` 的 `OblRR⁼`, `OblKK⁼`, `OblKR⁼`, 每一种只在 `rkT` 实际给出该种时要求) 给出. 证明只用 `rk-mono` 分情形, 折叠在节点处定义性地是 `RKi … (rkT …)`. 前提: 三种义务 (对一切运行上下文).
> 2. **(定理) `kr-vac`**: 同一坐标层 ($k=k'$) 时第三种 (左留右升) 不出现, 所以 `OblKR⁼` 空真地成立 (`krDiag`). 第三种只在坐标层不同时是真义务.
> 3. **(定理) 律的定义域: `cpBad`.** 实例 $\Omega^{\mathsf H}$. 分支世界对 $(c,c')=(\lim_n 0,\ 0)$ 是 `CP` 对 (顶端值 $\lim_n 0\le 0$, 对齐 `aS`, 自洽); `Ωd Ωᴴ` 在这两个世界上的分支节点坐标层是 `emb c` $=\mathrm{hl}(\lambda\_.\,0)$ 与 `emb c′` $=0$. 在同一目标层 $t=\mathrm{hl}(\lambda\_.\,0)$ 的一对 `TC` 目标上, 左边 `rkT` 是 `rise`, 右边是 `keep` (`rkBadL`, `rkBadR`): 这正是 `rk-mono` 排除的 "左升右留". 所以 `StrRel12Rel.κᴸ` (分支对取 `CP`) 的定义域里有坐标层**没有** $\sqsubseteq_\infty$ 关系、种类对落在 `rk-mono` 三种之外的节点对. 本接口的 `κˣ` 改取 `CPᴸ` 的理由就是这一条.
> 4. **(定理) `κlit`**: 分支对带字面 $c\lhd c'$ (`CPᴸ`) 时, 合法的 $\Omega$-极限层 $\mathrm{h\Omega}\,g$ 的两个分支层满足 $g\,c\sqsubseteq_\infty g\,c'$ (由 `LgH` 的单调), 所以 `κˣ` 产生的节点对都在 `rk-mono` 的前提之内 (`κRk`).
>
> **范围.** `cpBad` 不是否定定理: 它只是一个实例, 说 `CP` 分支对的定义域含一个 "左升右留" 的节点对; 它不说这一对在值上不可比. `node-red` 的前提里, `OblKR⁼` 在坐标层不同时就是 `StrRel13Kr.¬krX` 那种 "节点对极限" (`RelX` 也没有这样的构造子, 判断); 所以 `node-red` 对坐标层不同、目标层夹在中间的节点对是**不可用的**, 除非结论层加规则. `OblRR⁼`/`OblKK⁼` 本文没有证 (见入口 §3).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
module OCF.Align.StrRel14Rk (Λ : H) (lΛ : LgH Λ) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
open import OCF.Align.HtFeedTree using (hΩ; _⊲[_]_; StH; Vs; D; ni; AccY; acc; ⊲ᴴ↑)
open import OCF.Align.HtFeedClosed using (module At)
open import OCF.Align.StrRel11Rk Λ lΛ using (_⊑∞_; fg; RkRel; rr; kp; rk-agree)
open import OCF.Align.StrRel13Rk Λ lΛ using (RkX; kk; kr; rk-mono)
import OCF.Align.StrRel13Rk as R13
open import OCF.Align.StrRel12Al using (CP)
open import OCF.Align.StrRel12Sem Λ lΛ using (TC)
open import OCF.Align.StrRel14If Λ lΛ using (RelX; R∀X; HAWX; SemX; CPᴸ; module NodeObl⁼)

module P = At Λ lΛ
open P using (Tg; wm; tm; lm; St; Ig; LW; Rk; rise; keep; rkT)
```

## 1 节点规则归到三种义务

```agda
module Red {L L′ V V′ k k′} {lV : Lg V} {lV′ : Lg V′} (r : StH V k L) (r′ : StH V′ k′ L′)
           (u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′) (u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ r′ W′ → D L′ W′)
           (kk′ : k ⊑∞ k′) where

  Obl : ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (f : ∀ {W₁ j} → StH W₁ j L → AccY j) (f′ : ∀ {W₁ j} → StH W₁ j L′ → AccY j)
        (q₀ : V ⊲ W) (q₀′ : V′ ⊲ W′) (ll : LW L W) (ll′ : LW L′ W′) (A₀ : Ig L W) (A₀′ : Ig L′ W′)
        (w : D L W) (w′ : D L′ W′) (Y : St W) (Y′ : St W′) → Set
  Obl lW lW′ f f′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′ =
    O.OblRR⁼ × (O.OblKK⁼ × O.OblKR⁼)
    where module O = NodeObl⁼ {lV = lV} {lV′ = lV′} r r′ u u′ lW lW′ (acc f) (f r) (acc f′) (f′ r′) q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′

  module Split {W W′} (lW : Lg W) (lW′ : Lg W′) (f : ∀ {W₁ j} → StH W₁ j L → AccY j) (f′ : ∀ {W₁ j} → StH W₁ j L′ → AccY j)
               (q₀ : V ⊲ W) (q₀′ : V′ ⊲ W′) (ll : LW L W) (ll′ : LW L′ W′) (A₀ : Ig L W) (A₀′ : Ig L′ W′)
               (w : D L W) (w′ : D L′ W′) (Y : St W) (Y′ : St W′) (ob : Obl lW lW′ f f′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′) where
    module O = NodeObl⁼ {lV = lV} {lV′ = lV′} r r′ u u′ lW lW′ (acc f) (f r) (acc f′) (f′ r′) q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′

    go : ∀ {t m m′} (T : Tg W t m) (T′ : Tg W′ t m′) → TC lW lW′ T T′ → ∀ (rk : Rk k t m) (rk′ : Rk k′ t m′) →
         O.rkL T ≡ rk → O.rkR T′ ≡ rk′ → RkX rk rk′ → O.Out T T′ rk rk′
    go T T′ tc .rise .rise eL eR R13.rr = proj₁ ob T T′ tc eL eR
    go T T′ tc .(keep R) .(keep R′) eL eR (kk R R′) = proj₁ (proj₂ ob) T T′ tc R R′ eL eR
    go T T′ tc .(keep R) .rise eL eR (kr R) = proj₂ (proj₂ ob) T T′ tc R eL eR

  node-red : (∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (f : ∀ {W₁ j} → StH W₁ j L → AccY j) (f′ : ∀ {W₁ j} → StH W₁ j L′ → AccY j)
                (ll : LW L W) (ll′ : LW L′ W′) (q₀ : V ⊲ W) (q₀′ : V′ ⊲ W′) → CP lV lV′ q₀ lW q₀′ lW′ →
                ∀ (A₀ : Ig L W) (A₀′ : Ig L′ W′) → HAWX L L′ lW lW′ A₀ A₀′ →
                ∀ w w′ → RelX L L′ lW lW′ w w′ → ∀ (Y : St W) (Y′ : St W′) → R∀X lW lW′ Y Y′ →
                Obl lW lW′ f f′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′) →
             SemX L L′ lV lV′ (ni r u) (ni r′ u′)
  node-red ob lW lW′ (acc f) (acc f′) ll ll′ q₀ q₀′ hq A₀ A₀′ ha w w′ hw Y Y′ hY T T′ tc =
    S.go T T′ tc _ _ refl refl
      (rk-mono kk′ (⊲ᴴ↑ (wm T) (P.kk r q₀ ll)) (tm T) (lm T) (⊲ᴴ↑ (wm T′) (P.kk r′ q₀′ ll′)) (tm T′) (lm T′))
    where module S = Split lW lW′ f f′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′ (ob lW lW′ f f′ ll ll′ q₀ q₀′ hq A₀ A₀′ ha w w′ hw Y Y′ hY)
```

## 2 同一坐标层时第三种不出现

```agda
kr-vac : ∀ {k t m m′} (km : k ⊲[ m ] Λ) (tm₁ : t ⊲[ m ] Λ) (lm₁ : Lg m) (km′ : k ⊲[ m′ ] Λ) (tm′ : t ⊲[ m′ ] Λ) (lm′ : Lg m′) R →
         rkT km tm₁ lm₁ ≡ keep R → rkT km′ tm′ lm′ ≡ rise → ⊥
kr-vac km tm₁ lm₁ km′ tm′ lm′ R eL eR = no (subst (λ x → RkRel x (rkT km′ tm′ lm′)) eL (rk-agree km tm₁ lm₁ km′ tm′ lm′)) eR
  where
  no : ∀ {k t m m′} {R : StH m k t} {y : Rk k t m′} → RkRel (keep R) y → y ≡ rise → ⊥
  no (kp _ _) ()

-- 坐标层相同 (两边同一个 StH 的层 k): OblKR⁼ 空真
module Diag {L L′ V V′ k} {lV : Lg V} {lV′ : Lg V′} (r : StH V k L) (r′ : StH V′ k L′)
            (u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′) (u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ r′ W′ → D L′ W′)
            {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac₁ : AccY k) (ac′ : AccY L′) (ac₁′ : AccY k)
            (q₀ : V ⊲ W) (q₀′ : V′ ⊲ W′) (ll : LW L W) (ll′ : LW L′ W′) (A₀ : Ig L W) (A₀′ : Ig L′ W′)
            (w : D L W) (w′ : D L′ W′) (Y : St W) (Y′ : St W′) where
  module O = NodeObl⁼ {lV = lV} {lV′ = lV′} r r′ u u′ lW lW′ ac ac₁ ac′ ac₁′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′

  krDiag : O.OblKR⁼
  krDiag T T′ tc R eL eR =
    ⊥-elim (kr-vac (⊲ᴴ↑ (wm T) (P.kk r q₀ ll)) (tm T) (lm T) (⊲ᴴ↑ (wm T′) (P.kk r′ q₀′ ll′)) (tm T′) (lm T′) R eL eR)
```

## 3 字面的分支对给出坐标层的 $\sqsubseteq_\infty$

```agda
κlit : ∀ {g : A → H} → LgH (hΩ g) → ∀ {c c′} → Lg c′ → c ⊲ c′ → g c ⊑∞ g c′
κlit (mo , _) lc′ e = fg (mo lc′ e)

κRk : ∀ {g : A → H} → LgH (hΩ g) → ∀ {V V′ c c′} {lV : Lg V} {lV′ : Lg V′} {p : V ⊲ c} {lc : Lg c} {p′ : V′ ⊲ c′} {lc′ : Lg c′} →
      CPᴸ lV lV′ p lc p′ lc′ →
      ∀ {t m m′} (km : g c ⊲[ m ] Λ) (tm₁ : t ⊲[ m ] Λ) (lm₁ : Lg m) (km′ : g c′ ⊲[ m′ ] Λ) (tm′ : t ⊲[ m′ ] Λ) (lm′ : Lg m′) →
      RkX (rkT km tm₁ lm₁) (rkT km′ tm′ lm′)
κRk lg {lc′ = lc′} (_ , e) km tm₁ lm₁ km′ tm′ lm′ = rk-mono (κlit lg lc′ e) km tm₁ lm₁ km′ tm′ lm′
```
