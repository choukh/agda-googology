# 结构关系, 第三轮 (二): `SumOne` 折叠的第 1 层输入, 两边世界不同 (`lo` 档的结构版)

> 不含记号. 入口 [StrRel3](StrRel3.lagda.md). 取代 `KValSound.snd-lo` 的那一种: `KNest2Sound` 的 `lo²` 一句把第 1 层树 (无 `nκ`) 交给它, 它的 `ni⊑` 按值对齐坐标, 链经 `KValZero.chain` 套 `Gen`, 关系里有 `lim⊑`. 这里:
>
> - **(a) 结构的动作前提 `HAˢ`**: 与 `KValSound.HA⁺` 同形 (一切抬升、一切到第 0 层的路径), 结论是第 0 层输出的 $\sqsubseteq^{\mathsf O}$, 前提是状态第 0 层差的 $\sqsubseteq^{\mathsf O}$.
> - **(b) 关系 `_⊑ˡ_`**: 第 1 层树, 两边世界不同; `n0 ⊑ z`, `n1`, `⨾`, `nl` 逐项, `nw` 两边, 传递 (中间项与左边同世界), **`ni⊑ˡ` 的分支按坐标的结构关系对齐** (跨世界: 左边分支在 $W$, 右边在 $W'$). **没有 `lim⊑`, 没有单位律、结合律、部分和** (本轮的范围; 主线里的树 `nest k`, $\Omega$ 的形状只用前几条).
> - **语义 `OutLeˡ`**: 两边各自一个 `Sd`, 状态的第 0 层差 (规范路径 `κ₀ ll`) 结构相关 ⇒ 输出的第 0 层读数结构相关. 不要 `CohY`, 不要值.
> - **`sndˡ`**: 关系推出语义, 对推导归纳. `ni⊑ˡ` 一句: 节点在目标第 0 层上升 (`rkT` 两边都只能 `rise`), 链的动作是 `Ai`, 它的结构前提由分支的两条前提加归纳给出, 链由 `StrRel3Zero.chainᴼ`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel3Lo where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg; ⊲-tr; ss)
import OCF.Align.CumReadCF as C
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; cnt)
import OCF.Align.SumOneClosed as F
open import OCF.Align.StrRel3Zero using (_⊑ᴼ_; z0; o1; sq; lm; wl; wr; tr; reflᴼ; S₀; s0; HA0; snd0; chainᴼ)
import OCF.Align.StrRel3Zero as Z
```

## §1 一边与结构的动作前提

```agda
one : A
one = asuc azero

κ₀ : ∀ {W} → one ⊲ W → azero ⊲ W
κ₀ ll = ⊲-tr (C.suc C.self) ll

record Sd : Set where
  constructor sd
  field
    W   : A
    lW  : Lg W
    ll  : one ⊲ W
    act : F.Ig (cnt one) W
open Sd public

lift : (s : Sd) → ∀ {V} → W s ⊲ V → Lg V → Sd
lift s {V} p lV = sd V lV (⊲-tr (ll s) p) (F.Ig↾ p (act s))

-- 读数: 规范路径上的第 0 层差
Ob : (s : Sd) → F.Df (W s) → D azero (W s)
Ob s Δ = F.yc Δ (inj₁ (κ₀ (ll s))) tt

HAˢ : Sd → Sd → Set
HAˢ s s′ = ∀ {V V′} (p : W s ⊲ V) (p′ : W s′ ⊲ V′) (lV : Lg V) (lV′ : Lg V′) w w′ (Y : F.St V) (Y′ : F.St V′)
           (k : azero ⊲ V) (k′ : azero ⊲ V′) → F.yc (F.d Y) (inj₁ k) tt ⊑ᴼ F.yc (F.d Y′) (inj₁ k′) tt →
           F.yc (act s p lV w Y) (inj₁ k) tt ⊑ᴼ F.yc (act s′ p′ lV′ w′ Y′) (inj₁ k′) tt

record Ok (s s′ : Sd) : Set where
  constructor ok
  field
    hx : HAˢ s s′
    h0 : HAˢ s s
open Ok public

okL : ∀ {s s′} → Ok s s′ → Ok s s
okL o = ok (h0 o) (h0 o)

ok↾ : ∀ {s s′} → Ok s s′ → ∀ {V V′} (p : W s ⊲ V) (p′ : W s′ ⊲ V′) (lV : Lg V) (lV′ : Lg V′) → Ok (lift s p lV) (lift s′ p′ lV′)
ok↾ o p p′ lV lV′ = ok (λ r r′ → hx o (⊲-tr p r) (⊲-tr p′ r′)) (λ r r′ → h0 o (⊲-tr p r) (⊲-tr p r′))

ac₁ : F.AccY (cnt one)
ac₁ = F.accCn one

Rn : (s : Sd) → ∀ {V} → D one V → V ⊲ W s → D one (W s) → F.St (W s) → F.Df (W s)
Rn s x q w Y = F.Run ac₁ x q (lW s) (ll s) (act s) w Y

SRˡ : (s s′ : Sd) → F.St (W s) → F.St (W s′) → Set
SRˡ s s′ Y Y′ = Ob s (F.d Y) ⊑ᴼ Ob s′ (F.d Y′)

OutLeˡ : ∀ {V V′} → D one V → D one V′ → Set
OutLeˡ {V} {V′} x x′ = ∀ (s s′ : Sd) → Ok s s′ → ∀ (q : V ⊲ W s) (q′ : V′ ⊲ W s′) w w′ Y Y′ → SRˡ s s′ Y Y′ →
                       Ob s (Rn s x q w Y) ⊑ᴼ Ob s′ (Rn s′ x′ q′ w′ Y′)
```

## §2 关系

```agda
Br : A → Set
Br V = ∀ {W′} → V ⊲ W′ → Lg W′ → D azero W′ → D one W′

infix 4 _⊑ˡ_
data _⊑ˡ_ : ∀ {V V′} → D one V → D one V′ → Set where
  n0ˡ : ∀ {V V′} {x : D one V′} → n0 {W = V} ⊑ˡ x
  n1ˡ : ∀ {V V′} → n1 {W = V} ⊑ˡ n1 {W = V′}
  ⨾ˡ  : ∀ {V V′} {x y : D one V} {x′ y′ : D one V′} → x ⊑ˡ x′ → y ⊑ˡ y′ → (x ⨾ y) ⊑ˡ (x′ ⨾ y′)
  nlˡ : ∀ {V V′} {d : ℕ → D one V} {d′ : ℕ → D one V′} → (∀ n → d n ⊑ˡ d′ n) → nl d ⊑ˡ nl d′
  nwˡ : ∀ {V₀ V V′} {p : V₀ ⊲ V} {x : D one V₀} {x′ : D one V′} → x ⊑ˡ x′ → nw p x ⊑ˡ x′
  nwʳ : ∀ {V₀ V V′} {p : V₀ ⊲ V′} {x : D one V} {x′ : D one V₀} → x ⊑ˡ x′ → x ⊑ˡ nw p x′
  -- 逐分支, 跨世界, 坐标按结构关系对齐: 左边自比, 左右
  niˡ : ∀ {V V′} {u : Br V} {u′ : Br V′} →
        (∀ {W W′} (q : V ⊲ W) (q′ : V ⊲ W′) (l : Lg W) (l′ : Lg W′) (z : D azero W) (z′ : D azero W′) → z ⊑ᴼ z′ → u q l z ⊑ˡ u q′ l′ z′) →
        (∀ {W W′} (q : V ⊲ W) (q′ : V′ ⊲ W′) (l : Lg W) (l′ : Lg W′) (z : D azero W) (z′ : D azero W′) → z ⊑ᴼ z′ → u q l z ⊑ˡ u′ q′ l′ z′) →
        ni (ss C.self) u ⊑ˡ ni (ss C.self) u′
  trˡ : ∀ {V V′} {x y : D one V} {z : D one V′} → x ⊑ˡ y → y ⊑ˡ z → x ⊑ˡ z
```

## §3 可靠性

```agda
sndˡ : ∀ {V V′} {x : D one V} {x′ : D one V′} → x ⊑ˡ x′ → OutLeˡ x x′
sndˡ n0ˡ s s′ o q q′ w w′ Y Y′ e = z0
sndˡ n1ˡ s s′ o q q′ w w′ Y Y′ e = hx o C.self C.self (lW s) (lW s′) w w′ Y Y′ _ _ e
sndˡ (⨾ˡ hx′ hy) s s′ o q q′ w w′ Y Y′ e =
  let ox = sndˡ hx′ s s′ o q q′ w w′ Y Y′ e in sq ox (sndˡ hy s s′ o q q′ _ _ _ _ (sq e ox))
sndˡ (nlˡ {d = d} {d′} h) s s′ o q q′ w w′ Y Y′ e = lm (λ n → proj₂ (go n))
  where
  P = λ n → F.Rpt ac₁ d q (lW s) (ll s) (act s) w Y n
  P′ = λ n → F.Rpt ac₁ d′ q′ (lW s′) (ll s′) (act s′) w′ Y′ n
  st : ∀ n → SRˡ s s′ (proj₂ (P n)) (proj₂ (P′ n))
  go : ∀ n → SRˡ s s′ (proj₂ (P n)) (proj₂ (P′ n)) ×
             (Ob s (Rn s (d n) q (proj₁ (P n)) (proj₂ (P n))) ⊑ᴼ Ob s′ (Rn s′ (d′ n) q′ (proj₁ (P′ n)) (proj₂ (P′ n))))
  go n = st n , sndˡ (h n) s s′ o q q′ _ _ _ _ (st n)
  st zero = e
  st (suc n) = let (a , b) = go n in sq a b
sndˡ (nwˡ {p = p} h) s s′ o q q′ = sndˡ h s s′ o (⊲-tr p q) q′
sndˡ (nwʳ {p = p} h) s s′ o q q′ = sndˡ h s s′ o q (⊲-tr p q′)
sndˡ (trˡ h h′) s s′ o q q′ w w′ Y Y′ e =
  tr (sndˡ h s s (okL o) q q w w Y Y (reflᴼ _)) (sndˡ h′ s s′ o q q′ w w′ Y Y′ e)
sndˡ (niˡ {u = u} {u′} mu cr) s s′ o q q′ w w′ Y Y′ e = rs (F.rkT kW (inj₁ kW) (lW s)) (F.rkT kW′ (inj₁ kW′) (lW s′))
  where
  kW = κ₀ (ll s)
  kW′ = κ₀ (ll s′)
  A² = F.Ai ac₁ (ss C.self) u q kW (ll s) (act s) w
  A²′ = F.Ai ac₁ (ss C.self) u′ q′ kW′ (ll s′) (act s′) w′
  i j : S₀
  i = s0 (W s) (lW s) kW A²
  j = s0 (W s′) (lW s′) kW′ A²′
  sL = lift s C.self (lW s)
  sR = lift s′ C.self (lW s′)
  hii : HA0 i i
  hii z z′ hz Z Z′ sZ = sndˡ (mu q q (lW s) (lW s) z z′ hz) sL sL (ok↾ (okL o) C.self C.self (lW s) (lW s)) C.self C.self _ _ Z Z′ sZ
  hij : HA0 i j
  hij z z′ hz Z Z′ sZ = sndˡ (cr q q′ (lW s) (lW s′) z z′ hz) sL sR (ok↾ o C.self C.self (lW s) (lW s′)) C.self C.self _ _ Z Z′ sZ
  rs : ∀ (rk rk′ : F.Rk′ azero azero) →
       F.RKi ac₁ Z.ac₀ (ss C.self) u q (lW s) (ll s) (act s) w Y (inj₁ kW) tt rk ⊑ᴼ
       F.RKi ac₁ Z.ac₀ (ss C.self) u′ q′ (lW s′) (ll s′) (act s′) w′ Y′ (inj₁ kW′) tt rk′
  rs (F.keep ()) rk′
  rs (F.rise _) (F.keep ())
  rs (F.rise _) (F.rise _) = chainᴼ i j hii hij Y Y′ e
```
