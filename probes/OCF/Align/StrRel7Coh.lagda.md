# 结构关系, 第七轮: 单个状态的结构自洽 (`coh₁` 的结构版)

> 入口见 [StrRel7](StrRel7.lagda.md). 本文只做一件事: 自洽的状态跑任意第 1 层树, 输出自洽. "自洽" 指同一状态在任意两条读数路径上的读数 $\sqsubseteq^{\mathsf P}$ 相关, 即 `R∀ Y Y`. 含 `ni` (第 0 层的链 `Chn`) 与 `nκ` (格) 两种节点, 不要对齐数据, 不要领先量, 不看值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel7Coh where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; Tg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (≤-refl)
open import OCF.Align.SumOneTree using (D; Dl; drp; n0; n1; _⨾_; nl; ni; nκ; nw; cnt; kk; inV)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KNestAdm using (split)
open import OCF.Align.StrRel4Walk using (Al; aS; aP; aL)
open import OCF.Align.StrRel4Pr using (_⊑ᴾ_; z0; o1; sq; lm; wl; wr)
open import OCF.Align.StrRel5Nest using (OA; R∀; advA; drpR)
```

## 1 两条自反律

第 0 层的树只有 `n0, n1, ⨾, nl, nw` 五种节点, $\sqsubseteq^{\mathsf P}$ 自反. 对齐 `Al` 在同一个世界上自反: 每个位置与自己配对, 领先量由字面路径的长度给出 (`KNestAdm.split`). 归纳在路径的终点上 (终点是 `A` 的项, 极限的尾巴是它的子项), 与 `Walk` 的写法相同.

```agda
rfP : ∀ {V} (x : D azero V) → x ⊑ᴾ x
rfP n0 = z0
rfP n1 = o1
rfP (x ⨾ y) = sq (rfP x) (rfP y)
rfP (nl d) = lm (λ n → rfP (d n))
rfP (ni () u)
rfP (nκ () u)
rfP (nw p x) = wl (wr (rfP x))

alR : ∀ {L} (lL : Lg L) b {a} (p : a ⊲ b) (lb : Lg b) → b ⊲ L → Al L L p lb p lb
alR lL b C.self lb bL = aS C.self lb
alR lL (asuc c) (C.suc p) lb bL =
  aP (alR lL c p lb (⊲-tr (C.suc C.self) bL)) (≤-refl c) (split (⊲-tr (C.suc C.self) bL) lL)
alR lL (alim f) (C.lim n p) (stp , wf) bL =
  aL (alR lL (f n) p (wf n) (⊲-tr (C.lim n C.self) bL))
     (λ m → alR lL (f (suc (m + n))) (stp (m + n)) (wf (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bL))
```

## 2 自洽的动作, 自洽的状态

动作自洽: 对自洽的状态, 输出自洽. `Ig↾` 保持它 (动作只是换了起点).

```agda
Ch : ∀ {W} → F.St W → Set
Ch Y = R∀ Y Y

CA : ∀ {ly W} → F.Ig ly W → Set
CA {ly} {W} A₀ = ∀ {W′} (p : W ⊲ W′) (l : Lg W′) (w : Dl ly W′) (Y : F.St W′) → Ch Y → OA (A₀ p l w Y) (A₀ p l w Y)

CA↾ : ∀ {ly W W′} {A₀ : F.Ig ly W} (p : W ⊲ W′) → CA A₀ → CA (F.Ig↾ p A₀)
CA↾ p cA p′ = cA (⊲-tr p p′)
```

## 3 第 0 层: 链里的坐标树

第 0 层的跑法只经过 `n0, n1, ⨾, nl, nw`; `n1` 调用动作. 输出自洽由动作自洽与状态的推进 (`advA`) 得出. 动作在这里是 `Ai`, 它跑 `ni` 的分支, 所以第 0 层的引理以动作自洽为参数, 不与第 1 层互递归.

```agda
coh₀ : ∀ {W₀ W} (ac : F.AccY (cnt azero)) (x : D azero W₀) (q : W₀ ⊲ W) (lW : Lg W) (ll : azero ⊲ W)
       (A₀ : F.Ig (cnt azero) W) → CA A₀ → ∀ w (Y : F.St W) → Ch Y →
       OA (F.Run ac x q lW ll A₀ w Y) (F.Run ac x q lW ll A₀ w Y)
coh₀ (F.acc f) n0 q lW ll A₀ cA w Y r τ τ′ = z0
coh₀ (F.acc f) n1 q lW ll A₀ cA w Y r = cA C.self lW w Y r
coh₀ (F.acc f) (x ⨾ y) q lW ll A₀ cA w Y r τ τ′ =
  sq (Ox τ τ′) (coh₀ (F.acc f) y q lW ll A₀ cA (w ⨾ nw q x) (Y F.⊕ Δ) (advA {Y = Y} {Y′ = Y} Δ Δ r Ox) τ τ′)
  where
  Δ = F.Run (F.acc f) x q lW ll A₀ w Y
  Ox = coh₀ (F.acc f) x q lW ll A₀ cA w Y r
coh₀ (F.acc f) (nl d) q lW ll A₀ cA w Y r τ τ′ = lm (λ n → coh₀ (F.acc f) (d n) q lW ll A₀ cA _ _ (st n) τ τ′)
  where
  P = λ n → F.Rpt (F.acc f) d q lW ll A₀ w Y n
  st : ∀ n → Ch (proj₂ (P n))
  st zero = r
  st (suc n) = advA {Y = proj₂ (P n)} {Y′ = proj₂ (P n)} Δ Δ (st n) (coh₀ (F.acc f) (d n) q lW ll A₀ cA _ _ (st n))
    where Δ = F.Run (F.acc f) (d n) q lW ll A₀ (proj₁ (P n)) (proj₂ (P n))
coh₀ (F.acc f) (ni () u) q lW ll A₀ cA w Y r
coh₀ (F.acc f) (nκ () u) q lW ll A₀ cA w Y r
coh₀ (F.acc f) (nw p x) q lW ll A₀ cA w Y r = coh₀ (F.acc f) x (⊲-tr p q) lW ll A₀ cA w Y r
```

## 4 第 1 层: 一切树

- `nκ`: 输出在第 0 层的读数是 `RKy … azero τ` = 各格首读数 (经 `drp` 换到 τ 的世界) 的 `nl`, **除世界下标外与读数路径 τ 无关**, 所以只要第 0 层自反 `rfP` 与 `drpR`. 格内的状态不必自洽.
- `ni`: `rkT` 在第 0 层的读数上只能是 `rise` (`keep` 要 `Strict k azero`, 空), 输出是链 `Chn` 各项再跑一次后的读数的 `nl`. 链本身与 τ 无关 (只在固定路径 `kW` 上读), 所以两边是同一条链; 每项由第 0 层引理给出, 链上的状态逐项自洽. 动作 `Ai` 的自洽由分支 `u …` 上的归纳给出 (分支是 `ni r u` 的结构子项).

```agda
coh₁ : ∀ {W₀ W} (ac : F.AccY (cnt one)) (x : D one W₀) (q : W₀ ⊲ W) (lW : Lg W) (ll : one ⊲ W)
       (A₀ : F.Ig (cnt one) W) → CA A₀ → ∀ w (Y : F.St W) → Ch Y →
       OA (F.Run ac x q lW ll A₀ w Y) (F.Run ac x q lW ll A₀ w Y)
coh₁ (F.acc f) n0 q lW ll A₀ cA w Y r τ τ′ = z0
coh₁ (F.acc f) n1 q lW ll A₀ cA w Y r = cA C.self lW w Y r
coh₁ (F.acc f) (x ⨾ y) q lW ll A₀ cA w Y r τ τ′ =
  sq (Ox τ τ′) (coh₁ (F.acc f) y q lW ll A₀ cA (w ⨾ nw q x) (Y F.⊕ Δ) (advA {Y = Y} {Y′ = Y} Δ Δ r Ox) τ τ′)
  where
  Δ = F.Run (F.acc f) x q lW ll A₀ w Y
  Ox = coh₁ (F.acc f) x q lW ll A₀ cA w Y r
coh₁ (F.acc f) (nl d) q lW ll A₀ cA w Y r τ τ′ = lm (λ n → coh₁ (F.acc f) (d n) q lW ll A₀ cA _ _ (st n) τ τ′)
  where
  P = λ n → F.Rpt (F.acc f) d q lW ll A₀ w Y n
  st : ∀ n → Ch (proj₂ (P n))
  st zero = r
  st (suc n) = advA {Y = proj₂ (P n)} {Y′ = proj₂ (P n)} Δ Δ (st n) (coh₁ (F.acc f) (d n) q lW ll A₀ cA _ _ (st n))
    where Δ = F.Run (F.acc f) (d n) q lW ll A₀ (proj₁ (P n)) (proj₂ (P n))
coh₁ (F.acc f) (nw p x) q lW ll A₀ cA w Y r = coh₁ (F.acc f) x (⊲-tr p q) lW ll A₀ cA w Y r
coh₁ (F.acc f) (nκ zz u) q lW ll A₀ cA w Y r τ τ′ = lm (λ n → drpR (rfP _))
coh₁ {W = W} (F.acc f) (ni (C.ss C.self) u) q lW ll A₀ cA w Y r τ τ′ = go (F.rkT kW τ lW) (F.rkT kW τ′ lW)
  where
  R = C.ss C.self
  kW = kk (cnt one) R q ll
  A² = F.Ai (F.acc f) R u q kW ll A₀ w
  cA² : CA A²
  cA² p l z Y′ r′ =
    coh₁ (F.acc f) (u (⊲-tr q p) l (inV (cnt one) R z)) C.self l (⊲-tr ll p) (F.Ig↾ p A₀) (CA↾ p cA) _ Y′ r′
  Cn = F.Chn (f R) kW lW (lg⊲ kW lW) A² Y
  st : ∀ n → Ch (proj₂ (proj₂ (Cn n)))
  st zero = r
  st (suc n) = advA {Y = Yn} {Y′ = Yn} Δ Δ (st n)
                    (coh₀ (f R) (proj₁ (proj₂ (Cn n))) C.self lW kW A² cA² (proj₁ (Cn n)) Yn (st n))
    where
    Yn = proj₂ (proj₂ (Cn n))
    Δ = F.Run (f R) (proj₁ (proj₂ (Cn n))) C.self lW kW A² (proj₁ (Cn n)) Yn
  go : (a : F.Rk′ azero azero) (b : F.Rk′ azero azero) →
       F.RKi (F.acc f) (f R) R u q lW ll A₀ w Y τ tt a ⊑ᴾ F.RKi (F.acc f) (f R) R u q lW ll A₀ w Y τ′ tt b
  go (F.keep ()) b
  go (F.rise _) (F.keep ())
  go (F.rise _) (F.rise _) =
    lm (λ n → coh₀ (f R) (proj₁ (proj₂ (Cn n))) C.self lW kW A² cA² (proj₁ (Cn n)) (proj₂ (proj₂ (Cn n))) (st n) τ τ′)
```

## 5 推论: 主线的动作与初始状态

`Step` 的动作自洽 (`stepR` 取两边同一状态); 空状态自洽. 于是从空状态出发, 跑任意第 1 层树后的状态都自洽 (`reach`).

```agda
open import OCF.Align.StrRel5Nest using (stepA; stepR)
open import OCF.Align.KValSem using (ac₁)

cA-step : ∀ {W} → CA (stepA {W})
cA-step p l w Y r = stepR {Y = Y} {Y′ = Y} r

Y∅ : ∀ {W} → F.St W
Y∅ = F.st F.zeroD n0

ch∅ : ∀ {W} → Ch (Y∅ {W})
ch∅ = (λ τ τ′ → z0) , z0

reach : ∀ {W₀ W} (x : D one W₀) (q : W₀ ⊲ W) (lW : Lg W) (ll : one ⊲ W) w (Y : F.St W) → Ch Y →
        Ch (Y F.⊕ F.Run ac₁ x q lW ll stepA w Y)
reach x q lW ll w Y r = advA {Y = Y} {Y′ = Y} Δ Δ r (coh₁ ac₁ x q lW ll stepA cA-step w Y r)
  where Δ = F.Run ac₁ x q lW ll stepA w Y
```
