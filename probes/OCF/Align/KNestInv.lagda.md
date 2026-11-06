# 嵌套 `nκ` (二): 回灌层就是已有的输出

> 不含记号. 入口 [KNest](KNest.lagda.md). 对象是 `SumOneClosed` 的折叠在目标第 0 层上的状态.
>
> `KVal` 判决 5 担心: 外层两边的格世界 $v_n$, $v'_n$ 不对齐, 同一层 $c$ 在两边落进不同的格, 格的上下文里没有 "格世界可比" 一条, 内层 `nκ` 的回灌层 $\ell=\text{格世界}+z$ 就无从比较. 本文证明**这一条不需要**: 回灌层只由状态的值决定.
>
> - **不变量 `InvU b`, `InvL b`** (单边): $\ell=W+z\ \le\ b+\delta$ 与反向, $\delta$ 是状态在第 0 层的累计差. 它被**任何**一步 $Y\oplus\Delta$ 保持 (`invU⊕`, `invL⊕`, 定义性的), 被**回灌格的换世界**保持 (`invU-cv`, `invL-cv`: 新世界不超过 / 不低于旧的 $\ell$), 起点 `Y₀` 满足 (`inv-top`, $b=1$).
> - **回灌的每一格都满足** (`inv-κc`): 对一切输入族 $u$ (含嵌套的 `nκ`), 格 $n$ 的状态满足 `InvU b`, `InvL b`, 路径一致, 且格世界就是它的 $\ell$. 证明对 $n$ 归纳, 一步用到格的 `Walk` 输出路径一致 (`cohW`, 对 `Walk`/`WRp` 结构归纳, 每层分支用 `KValSem.coh₁`).
> - **`Hℓ` 由值推出** (`hℓ-inv`): 左边 `InvU b`, 右边 `InvL b′`, $b\le b'$, 状态值可比 ⇒ $\ell\le\ell'$. 所以把 `KValSound.Cx hi` 的 `Hℓ` 换成两条单边不变量 (`Cxᴵ`), 上下文就不再提格世界; `Cxᴵ` 被 `snd` 的每一步推进 (`nextᴵ`), 因为 `snd` 只用 $\oplus$.
>
> **它不解决什么.** [KNestNeg](KNestNeg.lagda.md) 的反例满足这里的全部条件 (`inv-cex`): 两边状态相同, $\ell=\ell'$. 嵌套的障碍不在格世界, 在内层 `nκ` 的**树世界** (区间起点) 与回灌层的相对位置.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KNestInv where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.SumOneTree using (D; n0; cnt; sum; sum-fst; Lg-sum; tailP)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KValTree using (Md; hi)
open import OCF.Align.KValSem
open import OCF.Align.KValSound using (Sd; W; ll; vY; Hℓ; Cx; cx; cL; cR; vle; hl)
import OCF.Align.KNestNeg as N
```

## §1 不变量

```agda
ℓ : ∀ {W} → F.St W → A
ℓ {W} Y = sum W (F.z Y)

dz : ∀ {W} → F.St W → D azero W
dz {W} Y = F.yc (F.d Y) (inj₁ (z⊲ W)) tt

InvU InvL : A → ∀ {W} → F.St W → Set
InvU b Y = ℓ Y ≤ sum b (dz Y)
InvL b Y = sum b (dz Y) ≤ ℓ Y

module _ {b W} {Y : F.St W} (Δ : F.Df W) where
  invU⊕ : InvU b Y → InvU b (Y F.⊕ Δ)
  invU⊕ h = sbase (F.yc Δ (inj₁ (z⊲ W)) tt) h

  invL⊕ : InvL b Y → InvL b (Y F.⊕ Δ)
  invL⊕ h = sbase (F.yc Δ (inj₁ (z⊲ W)) tt) h

-- 换世界: 新世界不超过 (不低于) 旧的回灌层
module _ {b W W′} (Y : F.St W) (q : W ⊲ W′) (lW′ : Lg W′) (cY : CohY Y) where
  invU-cv : W′ ≤ ℓ Y → InvU b Y → InvU b (F.cv q lW′ Y)
  invU-cv le h = ≤-trans le (≤-trans h (svmono (dz Y) (dz (F.cv q lW′ Y)) (≤-refl b) (≤cv Y q lW′ cY _ _)))

  invL-cv : ℓ Y ≤ W′ → InvL b Y → InvL b (F.cv q lW′ Y)
  invL-cv le h = ≤-trans (svmono (dz (F.cv q lW′ Y)) (dz Y) (≤-refl b) (cv≤ Y q lW′ cY _ _)) (≤-trans h le)

inv-top : InvU one F.Y₀ × InvL one F.Y₀
inv-top = ≤-refl one , ≤-refl one

-- KNestNeg 的反例满足不变量 (b = 2), 两边相同
inv-cex : InvU N.two N.Y₂ × InvL N.two N.Y₂
inv-cex = ≤-refl N.two , ≤-refl N.two
```

## §2 `Walk` 的输出路径一致

```agda
cohW : ∀ {W₀ V₁} (u : ∀ {c} → W₀ ⊲ c → Lg c → D one c) b {a} (p : a ⊲ b) (ap : W₀ ⊲ a) (lb : Lg b) (bV : b ⊲ V₁) (lV : Lg V₁)
       (l₁ : one ⊲ V₁) (A₀ : F.Ig (cnt one) V₁) co Y → CohA A₀ → CohY Y → CohD (F.Walk ac₁ u b p ap lb bV lV l₁ A₀ co Y)
cohR : ∀ {W₀ V₁ a n} (u : ∀ {c} → W₀ ⊲ c → Lg c → D one c) (f : ℕ → A) (stp : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n))
       (p : a ⊲ f n) (ap : W₀ ⊲ a) (fV : ∀ m → f m ⊲ V₁) (lV : Lg V₁) (l₁ : one ⊲ V₁) (A₀ : F.Ig (cnt one) V₁) co Y →
       CohA A₀ → CohY Y → ∀ m → CohY (proj₂ (F.WRp ac₁ u f stp wl p ap fV lV l₁ A₀ co Y m))

cohW u b C.self ap lb bV lV l₁ A₀ co Y cA cY = cohZ
cohW u (C.asuc c) (C.suc p) ap lb bV lV l₁ A₀ co Y cA cY =
  coh⨾ IH (coh₁ (u (⊲-tr ap p) lb) (⊲-tr (C.suc C.self) bV) lV l₁ A₀ _ _ cA (coh⊕ cY IH))
  where IH = cohW u c p ap lb (⊲-tr (C.suc C.self) bV) lV l₁ A₀ co Y cA cY
cohW u (C.alim f) {a} (C.lim n p) ap (stp , wl) bV lV l₁ A₀ co Y cA cY =
  coh⨾ IH (cohNl (λ m → cohW u (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV (suc (m + n))) lV l₁ A₀ _ _ cA
                          (cohR u f stp wl p ap fV lV l₁ A₀ _ _ cA (coh⊕ cY IH) m)))
  where
  fV : ∀ m → f m ⊲ _
  fV m = ⊲-tr (C.lim m C.self) bV
  IH = cohW u (f n) p ap (wl n) (fV n) lV l₁ A₀ co Y cA cY

cohR u f stp wl p ap fV lV l₁ A₀ co Y cA cY zero = cY
cohR {n = n} u f stp wl p ap fV lV l₁ A₀ co Y cA cY (suc m) =
  coh⊕ IH (cohW u (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV (suc (m + n))) lV l₁ A₀ _ _ cA IH)
  where IH = cohR u f stp wl p ap fV lV l₁ A₀ co Y cA cY m
```

## §3 回灌的每一格

格 $n$ 的状态 `Sv`: 世界是格世界 $v_n$, 满足两条不变量, 路径一致, 且 $\ell(\mathrm{Sv})\le v_n$ (格世界就是进格时的回灌层). 对一切输入族 $u$, 不要分支的任何性质.

```agda
module Cells {W₀ W} (u : ∀ {c} → W₀ ⊲ c → Lg c → D one c) (q₀ : W₀ ⊲ W) (lW : Lg W) (l₁ : one ⊲ W)
             (A₀ : F.Ig (cnt one) W) (w : D one W) (Y : F.St W) (cA : CohA A₀) where
  cl : ℕ → F.Cl W W₀ (cnt one)
  cl = F.κc ac₁ u q₀ lW l₁ A₀ w Y

  Good : A → ∀ {V} → F.St V → Set
  Good b S = InvU b S × InvL b S × CohY S

  CellOk : A → ℕ → Set
  CellOk b n = Good b (F.Sv (cl n)) × (ℓ (F.Sv (cl n)) ≤ F.v (cl n))

  inv-κc : ∀ {b} → InvU b Y → InvL b Y → CohY Y → ∀ n → CellOk b n
  inv-κc hU hL cY zero =
    (invU-cv Y q lv cY (≤-refl _) hU , invL-cv Y q lv cY (≤-refl _) hL , cohCv Y q lv cY) , ≤-refl _
    where
    q = sum-fst W (F.z Y)
    lv = Lg-sum W (F.z Y) lW
  inv-κc {b} hU hL cY (suc n) =
    (invU-cv S′ q lv′ cS′ upper (invU⊕ Δ gU) , invL-cv S′ q lv′ cS′ lower (invL⊕ Δ gL) , cohCv S′ q lv′ cS′) , ≤-refl _
    where
    IH = inv-κc hU hL cY n
    c = cl n
    gU = proj₁ (proj₁ IH)
    gL = proj₁ (proj₂ (proj₁ IH))
    cS = proj₂ (proj₂ (proj₁ IH))
    Δ = F.κΔ ac₁ u l₁ A₀ c
    cΔ : CohD Δ
    cΔ = cohW u (F.v c) (F.av c) (F.ap c) (F.lv c) C.self (F.lv c) (⊲-tr l₁ (F.wv c)) (F.Ig↾ (F.wv c) A₀) (F.co c) (F.Sv c)
              (cohA↾ (F.wv c) cA) cS
    S′ = F.Sv c F.⊕ Δ
    cS′ = coh⊕ cS cΔ
    d₀ = F.yc Δ (inj₁ (z⊲ (F.v c))) tt
    q = sum-fst (F.v c) d₀
    lv′ = Lg-sum (F.v c) d₀ (F.lv c)
    upper : sum (F.v c) d₀ ≤ ℓ S′
    upper = sbase d₀ (⊲→≤ (sum-fst (F.v c) (F.z (F.Sv c))))
    lower : ℓ S′ ≤ sum (F.v c) d₀
    lower = sbase d₀ (proj₂ IH)
```

## §4 `Hℓ` 由值推出; 不提格世界的上下文

```agda
hℓ-inv : ∀ {b b′} (s s′ : Sd) {Y : F.St (W s)} {Y′ : F.St (W s′)} → b ≤ b′ → InvU b Y → InvL b′ Y′ → CohY Y → CohY Y′ →
         vY s Y ≤ vY s′ Y′ → Hℓ hi Y Y′
hℓ-inv {b} {b′} s s′ {Y} {Y′} b≤ hU hL cY cY′ v≤ =
  ≤-trans hU (≤-trans (svmono (dz Y) (dz Y′) b≤ (≤-trans (cyA cY _ _) (≤-trans v≤ (cyA cY′ _ _)))) hL)

-- Cx hi 的 Hℓ 换成两条单边不变量
record Cxᴵ (s s′ : Sd) (Y : F.St (W s)) (Y′ : F.St (W s′)) : Set where
  constructor cxᴵ
  field
    b b′ : A
    b≤  : b ≤ b′
    iU  : InvU b Y
    iL  : InvL b′ Y′
    cLᴵ : CohY Y
    cRᴵ : CohY Y′
    vleᴵ : vY s Y ≤ vY s′ Y′
open Cxᴵ public

toCx : ∀ {s s′ Y Y′} → Cxᴵ s s′ Y Y′ → Cx hi s s′ Y Y′
toCx {s} {s′} (cxᴵ b b′ b≤ iU iL c c′ v) = cx c c′ v (hℓ-inv s s′ b≤ iU iL c c′ v)

-- snd 的每一步只用 ⊕: Cxᴵ 随之推进 (值与一致性由 snd 给出, 不变量是定义性的)
nextᴵ : ∀ {s s′ Y Y′} (Δ : F.Df (W s)) (Δ′ : F.Df (W s′)) → (k : Cxᴵ s s′ Y Y′) →
        CohY (Y F.⊕ Δ) → CohY (Y′ F.⊕ Δ′) → vY s (Y F.⊕ Δ) ≤ vY s′ (Y′ F.⊕ Δ′) → Cxᴵ s s′ (Y F.⊕ Δ) (Y′ F.⊕ Δ′)
nextᴵ Δ Δ′ (cxᴵ b b′ b≤ iU iL _ _ _) c c′ v = cxᴵ b b′ b≤ (invU⊕ Δ iU) (invL⊕ Δ′ iL) c c′ v
```
