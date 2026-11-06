# 结构关系, 第十三轮 (二): 跨坐标层的节点对, 在同目标的状态关系下值上就错 (否定)

> 不读记号. 入口 [StrRel13](StrRel13.lagda.md). 实例 $\Lambda_2=2$ (`hs (hs hz)`, 不含 $\Omega$-极限, 世界不起作用). 层 $2$ 上两个节点, 分支都是常数 `n1`:
>
> - 左 `xL = ni (ss (hsuc hself)) …`: 坐标层 $k=0$;
> - 右 `xR = ni (ss hself) …`: 坐标层 $k'=1$. $k\lhd k'$ 是字面的第一位置.
>
> 任何 "跨坐标层的节点规则" (坐标层 $k\le k'$, 分支在一切坐标上相关 ⇒ 两个节点相关) 都会把这一对放进关系 (分支是 `n1` 对 `n1`). 本文证明: 在 `StrRel12Sem` 的运行设定里 (同一世界 $0$, 路径 `self`, 动作 `Act`, 上下文 `n0`, 状态按 `R∀c` 相关), 两次运行在第 $0$ 层目标上的读数**值上**左边严格大 (`¬valX`), 所以 `SemW Λ₂ tt tt xL xR` 不成立 (`¬semX`).
>
> 原因只在状态: `R∀c` 只比**同一个目标**上的读数, 不比状态在第 $k$ 层与第 $k'$ 层上的两个读数. 目标是第 $0$ 层时两边都上升 (`rise`), 输出是坐标层的链, 链从状态在坐标层上的读数起: 左边读第 $0$ 层, 右边读第 $1$ 层. 反例状态 `Yv` 在第 $0$ 层读 `n1`, 在别的层读 `n0`; 它与自己按 `R∀c` 相关 (`hYv`). 左边的链第一段就碰到 `n1`, 经动作 `Act` 输出 $\omega$; 右边的链从 `n0` 起, 每段都是 `n0` (`xz`, `pt≤`).
>
> **范围.** 否定的是: 以 `R∀c` (同目标对) 为状态前提、第 $0$ 层结论蕴含值 $\le$ 的任何语义, 对这一对跨坐标层的节点. 与结论层取结构关系还是取值都无关 (`¬valX` 只说值). 不否定带 "跨目标层" 状态不变量的语义 (例如要求状态在第 $k'$ 层的读数支配第 $k$ 层的读数; 反例状态不满足它), 不否定同层的 `niᴸ` (那时两边读同一层).
>
> **前提可满足.** 全部给出: `hYv`, `cp00`, `StrRel12.haAct tt`, `n0ᴸ`. 分支相关是 `n1ᴸ`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel13Val where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; irr)
open import OCF.Align.HtFeedTree using (H; hz; hs; hl; hΩ; hself; hsuc; ss; StH; D; D₀; n0; n1; _⨾_; nl; ni; AccY; accL; sum; pt)
open import OCF.Align.HtFeedClosed using (module At)
open import OCF.Align.StrRel12Al using (CP; cp-self)
open import OCF.Align.StrRel12Rel using (Rel; n0ᴸ; n1ᴸ; niᴸ; vsum)
import OCF.Align.StrRel12Sem as Sm
import OCF.Align.StrRel12 as E

Λ₂ : H
Λ₂ = hs (hs hz)

module P = At Λ₂ tt
module S = Sm Λ₂ tt
module E₂ = E Λ₂ tt
```

## 1 两个节点, 一个状态

```agda
r₀ : StH azero hz Λ₂
r₀ = ss (hsuc hself)

r₁ : StH azero (hs hz) Λ₂
r₁ = ss hself

xL xR : D Λ₂ azero
xL = ni r₀ (λ _ _ _ → n1)
xR = ni r₁ (λ _ _ _ → n1)

-- 第 0 层读 n1, 别的层读 n0
rdv : ∀ t {m} → D t m
rdv hz = n1
rdv (hs b) = n0
rdv (hl f) = n0
rdv (hΩ g) = n0

Yv : P.St azero
Yv = P.st (P.df (λ {t} T → rdv t)) n0

rr : ∀ t {m m′} {lm : Lg m} {lm′ : Lg m′} → Rel t lm lm′ (rdv t {m}) (rdv t {m′})
rr hz = n1ᴸ
rr (hs b) = n0ᴸ
rr (hl f) = n0ᴸ
rr (hΩ g) = n0ᴸ

hYv : S.R∀c tt tt Yv Yv
hYv = (λ {t} T T′ tc → rr t) , n0ᴸ

cp00 : CP {V = azero} {V′ = azero} tt tt C.self tt C.self tt
cp00 = cp-self tt tt (≤-refl azero) tt tt
```

## 2 两次运行的第 0 层读数

```agda
OutL OutR : D₀ azero
OutL = P.yc (P.Run (accL Λ₂) xL C.self tt hself P.Act n0 Yv) (P.τ₀ tt)
OutR = P.yc (P.Run (accL Λ₂) xR C.self tt hself P.Act n0 Yv) (P.τ₀ tt)

-- 左: 链的第一段是 ω⋅(1 ⨾ 1)
lowL : asuc azero ≤ sum azero OutL
lowL = ≤l 1 (≤l 1 (s≤ z≤))

-- 右: 链从 n0 起, 每段都是 n0
xz : ∀ {k W} (ac : AccY k) (hk : P.LW k W) (lW : Lg W) (A² : P.Ig k W) (Y : P.St W) →
     P.yc (P.d Y) (P.tg C.self hk lW) ≡ n0 → ∀ n → proj₁ (proj₂ (P.Chn ac hk lW A² Y n)) ≡ n0
xz ac hk lW A² Y e zero = e
xz ac hk lW A² Y e (suc n) =
  cong (λ x → P.yc (P.Run ac x C.self lW hk A² (proj₁ (P.Chn ac hk lW A² Y n)) (proj₂ (proj₂ (P.Chn ac hk lW A² Y n)))) (P.tg C.self hk lW))
       (xz ac hk lW A² Y e n)

pt≤ : ∀ {W} b (d : ℕ → D₀ W) → (∀ n → d n ≡ n0) → ∀ n → pt b d n ≤ b
pt≤ b d e zero = ≤-refl b
pt≤ b d e (suc n) = subst (λ y → sum (pt b d n) y ≤ b) (sym (e n)) (pt≤ b d e n)

chz : ∀ {k W} (ac : AccY k) (hk : P.LW k W) (lW : Lg W) (A² : P.Ig k W) (Y : P.St W) →
      P.yc (P.d Y) (P.tg C.self hk lW) ≡ n0 → ∀ b →
      sum b (nl (λ n → P.yc (P.Run ac (proj₁ (proj₂ (P.Chn ac hk lW A² Y n))) C.self lW hk A²
                               (proj₁ (P.Chn ac hk lW A² Y n)) (proj₂ (proj₂ (P.Chn ac hk lW A² Y n)))) (P.τ₀ lW))) ≤ b
chz ac hk lW A² Y e b =
  l≤ (pt≤ b _ (λ n → cong (λ x → P.yc (P.Run ac x C.self lW hk A² (proj₁ (P.Chn ac hk lW A² Y n)) (proj₂ (proj₂ (P.Chn ac hk lW A² Y n)))) (P.τ₀ lW))
                          (xz ac hk lW A² Y e n)))

upR : sum azero OutR ≤ azero
upR = chz _ _ tt _ Yv refl azero
```

## 3 否定

```agda
¬valX : ¬ (sum azero OutL ≤ sum azero OutR)
¬valX h = irr azero (≤-trans lowL (≤-trans h upR))

¬semX : ¬ S.SemW Λ₂ tt tt xL xR
¬semX s = ¬valX (vsum (s tt tt (accL Λ₂) (accL Λ₂) hself hself C.self C.self cp00 P.Act P.Act (E₂.haAct tt Λ₂)
                         n0 n0 n0ᴸ Yv Yv hYv (P.τ₀ tt) (P.τ₀ tt) cp00) (≤-refl azero))
```

## 4 对照: 同层时没有这个问题

`xR` 与自己相关 (`StrRel12.ΩR` 那样的 `niᴸ`), 于是 `StrRel12.sem∀` 给出同一设定下的 `OAc`. 两边读状态的同一层, 反例状态不起作用.

```agda
selfR : Rel Λ₂ tt tt xR xR
selfR = niᴸ {r = r₁} {r′ = r₁} (λ p p′ lc lc′ cp y y′ hb → n1ᴸ)

selfOk : S.OAc tt tt (P.Run (accL Λ₂) xR C.self tt hself P.Act n0 Yv) (P.Run (accL Λ₂) xR C.self tt hself P.Act n0 Yv)
selfOk = E₂.sem∀ Λ₂ selfR tt tt (accL Λ₂) (accL Λ₂) hself hself C.self C.self cp00 P.Act P.Act (E₂.haAct tt Λ₂) n0 n0 n0ᴸ Yv Yv hYv
```
