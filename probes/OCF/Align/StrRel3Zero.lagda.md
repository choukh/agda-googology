# 结构关系, 第三轮 (一): `SumOne` 折叠的第 0 层输入, 两边世界不同

> 不含记号. 入口 [StrRel3](StrRel3.lagda.md). 对象是 `SumOneClosed` 的折叠在**目标第 0 层**上的输出 (`KVal`/`KNest` 的语义只读这一层). 与 [StrRelZero](StrRelZero.lagda.md) 的差别:
>
> - 树是 `SumOneTree` 的第 0 层树; 关系 `_⊑ᴼ_` 是 `StrRelDef._⊑₀_` 的**核心子集** (`n0 ⊑ z`, `n1`, `⨾`, `nl` 逐项, `nw` 两边, 传递), 足够折叠的输出与坐标 (`toH` 送进 $\sqsubseteq_0$, 所以 `StrRel2Pos.walkHeadᴼ` 可用);
> - 一边 (`S₀`) 是世界、合法性、到第 0 层的路径 `kW₀`、动作; **两边世界可以不同**, 读数各在自己的路径上;
> - **只读第 0 层**, 所以状态关系只有第 0 层的差 (`⊑ᴼ`), 第 0 层的树一律自比, **不要 `Good`, 不要自比的子推导, 不要路径一致** (`CohY` 在 `KVal` 里是为 `nκ` 的 `cv` 与 `hi` 档; 本文没有 `nκ`).
>
> **`snd0`**: $z\sqsubseteq^{\mathsf O} z'$, 动作满足结构前提 `HA0` (左边自比与左右) ⇒ 一切坐标 $w\sqsubseteq^{\mathsf O} w'$、一切第 0 层差结构相关的状态, 输出结构相关. **`chainᴼ`**: 第 1 层节点上升的链.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel3Zero where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; cnt)
import OCF.Align.SumOneClosed as F
open import OCF.Align.StrRel2Pos using (ofS)
import OCF.Align.StrRelDef as SD0
module SD = SD0 {azero} tt
```

## §1 关系

```agda
infix 4 _⊑ᴼ_
data _⊑ᴼ_ : ∀ {V V′} → D azero V → D azero V′ → Set where
  z0 : ∀ {V V′} {x : D azero V′} → n0 {W = V} ⊑ᴼ x
  o1 : ∀ {V V′} → n1 {W = V} ⊑ᴼ n1 {W = V′}
  sq : ∀ {V V′} {x y : D azero V} {x′ y′ : D azero V′} → x ⊑ᴼ x′ → y ⊑ᴼ y′ → (x ⨾ y) ⊑ᴼ (x′ ⨾ y′)
  lm : ∀ {V V′} {d : ℕ → D azero V} {d′ : ℕ → D azero V′} → (∀ n → d n ⊑ᴼ d′ n) → nl d ⊑ᴼ nl d′
  wl : ∀ {V₀ V V′} {p : V₀ ⊲ V} {x : D azero V₀} {x′ : D azero V′} → x ⊑ᴼ x′ → nw p x ⊑ᴼ x′
  wr : ∀ {V₀ V V′} {p : V₀ ⊲ V′} {x : D azero V} {x′ : D azero V₀} → x ⊑ᴼ x′ → x ⊑ᴼ nw p x′
  tr : ∀ {V V′} {x y : D azero V} {z : D azero V′} → x ⊑ᴼ y → y ⊑ᴼ z → x ⊑ᴼ z

reflᴼ : ∀ {V} (x : D azero V) → x ⊑ᴼ x
reflᴼ n0 = z0
reflᴼ n1 = o1
reflᴼ (x ⨾ y) = sq (reflᴼ x) (reflᴼ y)
reflᴼ (nl d) = lm (λ n → reflᴼ (d n))
reflᴼ (ni () u)
reflᴼ (nκ () u)
reflᴼ (nw p x) = wl (wr (reflᴼ x))

-- 送进 StrRelDef 的 ⊑₀ (于是 StrRelHead, StrRel2Pos 的首对齐可用)
toH : ∀ {V V′} {x : D azero V} {x′ : D azero V′} → x ⊑ᴼ x′ → ofS x SD.⊑₀ ofS x′
toH z0 = SD.z0
toH o1 = SD.o1
toH (sq h h′) = SD.sq (toH h) (toH h′)
toH (lm h) = SD.lm (λ n → toH (h n))
toH (wl h) = SD.wl (toH h)
toH (wr h) = SD.wr (toH h)
toH (tr h h′) = SD.tr (toH h) (toH h′)
```

## §2 一边, 结构的动作前提, 语义

```agda
ac₀ : F.AccY (cnt azero)
ac₀ = F.accCn azero

record S₀ : Set where
  constructor s0
  field
    W₀  : A
    lW₀ : Lg W₀
    kW₀ : azero ⊲ W₀
    act : F.Ig (cnt azero) W₀
open S₀ public

O : (i : S₀) → F.Df (W₀ i) → D azero (W₀ i)
O i Δ = F.yc Δ (inj₁ (kW₀ i)) tt

Rn : (i : S₀) → ∀ {V} → D azero V → V ⊲ W₀ i → D azero (W₀ i) → F.St (W₀ i) → F.Df (W₀ i)
Rn i z q w Y = F.Run ac₀ z q (lW₀ i) (kW₀ i) (act i) w Y

SR : (i j : S₀) → F.St (W₀ i) → F.St (W₀ j) → Set
SR i j Y Y′ = O i (F.d Y) ⊑ᴼ O j (F.d Y′)

HA0 : S₀ → S₀ → Set
HA0 i j = ∀ w w′ → w ⊑ᴼ w′ → ∀ Y Y′ → SR i j Y Y′ → O i (act i C.self (lW₀ i) w Y) ⊑ᴼ O j (act j C.self (lW₀ j) w′ Y′)

Sem0 : S₀ → S₀ → ∀ {V₁ V₂} → D azero V₁ → D azero V₂ → Set
Sem0 i j z z′ = ∀ q q′ w w′ → w ⊑ᴼ w′ → ∀ Y Y′ → SR i j Y Y′ → O i (Rn i z q w Y) ⊑ᴼ O j (Rn j z′ q′ w′ Y′)
```

## §3 可靠性

```agda
snd0 : ∀ (i j : S₀) → HA0 i i → HA0 i j → ∀ {V₁ V₂} {z : D azero V₁} {z′ : D azero V₂} → z ⊑ᴼ z′ → Sem0 i j z z′
snd0 i j hi hj z0 q q′ w w′ hw Y Y′ s = z0
snd0 i j hi hj o1 q q′ w w′ hw Y Y′ s = hj w w′ hw Y Y′ s
snd0 i j hi hj (sq {x = x} {x′ = x′} hx hy) q q′ w w′ hw Y Y′ s =
  let ox = snd0 i j hi hj hx q q′ w w′ hw Y Y′ s
      oy = snd0 i j hi hj hy q q′ (w ⨾ nw q x) (w′ ⨾ nw q′ x′) (sq hw (wl (wr hx))) _ _ (sq s ox)
  in sq ox oy
snd0 i j hi hj (lm {d = d} {d′} hd) q q′ w w′ hw Y Y′ s = lm (λ n → proj₂ (go n))
  where
  Q  = λ n → F.Rpt ac₀ d q (lW₀ i) (kW₀ i) (act i) w Y n
  Q′ = λ n → F.Rpt ac₀ d′ q′ (lW₀ j) (kW₀ j) (act j) w′ Y′ n
  go : ∀ n → ((proj₁ (Q n) ⊑ᴼ proj₁ (Q′ n)) × SR i j (proj₂ (Q n)) (proj₂ (Q′ n))) ×
             (O i (Rn i (d n) q (proj₁ (Q n)) (proj₂ (Q n))) ⊑ᴼ O j (Rn j (d′ n) q′ (proj₁ (Q′ n)) (proj₂ (Q′ n))))
  st : ∀ n → (proj₁ (Q n) ⊑ᴼ proj₁ (Q′ n)) × SR i j (proj₂ (Q n)) (proj₂ (Q′ n))
  st zero = hw , s
  st (suc n) = let ((a , e) , o) = go n in sq a (wl (wr (hd n))) , sq e o
  go n = let (a , e) = st n in (a , e) , snd0 i j hi hj (hd n) q q′ _ _ a _ _ e
snd0 i j hi hj (wl {p = p} hx) q q′ = snd0 i j hi hj hx (⊲-tr p q) q′
snd0 i j hi hj (wr {p = p} hx) q q′ = snd0 i j hi hj hx q (⊲-tr p q′)
snd0 i j hi hj (tr hx hy) q q′ w w′ hw Y Y′ s =
  tr (snd0 i i hi hi hx q q w w (reflᴼ w) Y Y (reflᴼ _)) (snd0 i j hi hj hy q q′ w w′ hw Y Y′ s)
```

## §4 链

第 1 层节点在目标第 0 层上上升时的链 (`Chn`). 链点是上一个链点的输出, 所以 "链点结构相关" 就是 "输出结构相关", 每一步一次 `snd0`.

```agda
module _ (i j : S₀) (hi : HA0 i i) (hj : HA0 i j) where
  CC : (k : S₀) → F.St (W₀ k) → ℕ → D azero (W₀ k) × (D azero (W₀ k) × F.St (W₀ k))
  CC k Y = F.Chn ac₀ (kW₀ k) (lW₀ k) tt (act k) Y

  segs : (k : S₀) → F.St (W₀ k) → ℕ → D azero (W₀ k)
  segs k Y n = O k (Rn k (proj₁ (proj₂ (CC k Y n))) C.self (proj₁ (CC k Y n)) (proj₂ (proj₂ (CC k Y n))))

  chainᴼ : ∀ (Y : F.St (W₀ i)) (Y′ : F.St (W₀ j)) → SR i j Y Y′ → nl (segs i Y) ⊑ᴼ nl (segs j Y′)
  chainᴼ Y Y′ s = lm (λ n → step n)
    where
    st : ∀ n → (proj₁ (CC i Y n) ⊑ᴼ proj₁ (CC j Y′ n)) × ((proj₁ (proj₂ (CC i Y n)) ⊑ᴼ proj₁ (proj₂ (CC j Y′ n))) ×
               SR i j (proj₂ (proj₂ (CC i Y n))) (proj₂ (proj₂ (CC j Y′ n))))
    step : ∀ n → segs i Y n ⊑ᴼ segs j Y′ n
    step n = let (c , (d , e)) = st n in snd0 i j hi hj d C.self C.self _ _ c _ _ e
    st zero = z0 , (s , s)
    st (suc n) = let (c , (d , e)) = st n in sq c d , (step n , sq e (step n))
```
