# 结构关系, 第七轮: 第 0 层对 $\sqsubseteq^{\mathsf P}$ 的全部构造子可靠

> 入口见 [StrRel7](StrRel7.lagda.md). `ni` 的链 `Chn` 跑第 0 层的坐标树, 两边的坐标由上一项输出给出, 只知道 $\sqsubseteq^{\mathsf P}$ 相关, 所以第 0 层要对 $\sqsubseteq^{\mathsf P}$ 的**全部**八个构造子可靠 (含 `tr`, `pr`, `wl`, `wr`), 结论对一切读数路径对. 这是 `StrRel3Zero.snd0` 的 "一切读数路径" 版.
>
> 两处与 `snd0` 不同:
> - 动作读累计的坐标 `w` (`Ai` 把它交给分支 `u`), 所以动作的关系带 $w\sqsubseteq^{\mathsf P}w'$, 跑的时候逐段维护.
> - `tr` 的中间一棵在**左边**的环境里跑 (同一状态、同一动作), 所以要左边状态自洽 (`Ch`) 与左边动作自比 (`AR A A`). 第 0 层的跑法不读路径 `q` 与世界的序, 所以这里不要对齐, 也不要 $W\le W'$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel7Zero where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; cnt)
import OCF.Align.SumOneClosed as F
open import OCF.Align.StrRel4Pr using (_⊑ᴾ_; z0; o1; sq; lm; wl; wr; tr; pr)
open import OCF.Align.StrRel5Nest using (OA; R∀; advA)
open import OCF.Align.StrRel7Coh using (rfP; Ch)
```

## 1 动作的关系

第 0 层的 `n1` 以 `C.self` 调用动作, 所以只在 `C.self` 上比.

```agda
AR : ∀ {W W′} → Lg W → Lg W′ → F.Ig (cnt azero) W → F.Ig (cnt azero) W′ → Set
AR lW lW′ A₀ A₀′ = ∀ w w′ Y Y′ → w ⊑ᴾ w′ → Ch Y → R∀ Y Y′ → OA (A₀ C.self lW w Y) (A₀′ C.self lW′ w′ Y′)
```

## 2 左边自洽 (只要动作在 `C.self` 上自比)

与 `StrRel7Coh.coh₀` 同, 前提换成 `AR A A`.

```agda
cohᴬ : ∀ {W₀ W} (ac : F.AccY (cnt azero)) (x : D azero W₀) (q : W₀ ⊲ W) (lW : Lg W) (ll : azero ⊲ W)
       (A₀ : F.Ig (cnt azero) W) → AR lW lW A₀ A₀ → ∀ w (Y : F.St W) → Ch Y →
       OA (F.Run ac x q lW ll A₀ w Y) (F.Run ac x q lW ll A₀ w Y)
cohᴬ (F.acc f) n0 q lW ll A₀ a w Y r τ τ′ = z0
cohᴬ (F.acc f) n1 q lW ll A₀ a w Y r = a w w Y Y (rfP w) r r
cohᴬ (F.acc f) (x ⨾ y) q lW ll A₀ a w Y r τ τ′ =
  sq (Ox τ τ′) (cohᴬ (F.acc f) y q lW ll A₀ a (w ⨾ nw q x) (Y F.⊕ Δ) (advA {Y = Y} {Y′ = Y} Δ Δ r Ox) τ τ′)
  where
  Δ = F.Run (F.acc f) x q lW ll A₀ w Y
  Ox = cohᴬ (F.acc f) x q lW ll A₀ a w Y r
cohᴬ (F.acc f) (nl d) q lW ll A₀ a w Y r τ τ′ = lm (λ n → cohᴬ (F.acc f) (d n) q lW ll A₀ a _ _ (st n) τ τ′)
  where
  P = λ n → F.Rpt (F.acc f) d q lW ll A₀ w Y n
  st : ∀ n → Ch (proj₂ (P n))
  st zero = r
  st (suc n) = advA {Y = proj₂ (P n)} {Y′ = proj₂ (P n)} Δ Δ (st n) (cohᴬ (F.acc f) (d n) q lW ll A₀ a _ _ (st n))
    where Δ = F.Run (F.acc f) (d n) q lW ll A₀ (proj₁ (P n)) (proj₂ (P n))
cohᴬ (F.acc f) (ni () u) q lW ll A₀ a w Y r
cohᴬ (F.acc f) (nκ () u) q lW ll A₀ a w Y r
cohᴬ (F.acc f) (nw p x) q lW ll A₀ a w Y r = cohᴬ (F.acc f) x (⊲-tr p q) lW ll A₀ a w Y r
```

## 3 可靠性

对 $\sqsubseteq^{\mathsf P}$ 的推导归纳. `tr` 一句: 中间一棵 `y` 与 `x` 同一树世界, 在左边的环境里跑, 前一半是左边自比 (状态 $(Y,Y)$, 坐标 $(w,w)$), 后一半是原来的比较.

```agda
snd0 : ∀ {V V′} {x : D azero V} {x′ : D azero V′} → x ⊑ᴾ x′ →
       ∀ {W W′} (ac : F.AccY (cnt azero)) (ac′ : F.AccY (cnt azero)) (q : V ⊲ W) (q′ : V′ ⊲ W′) (lW : Lg W) (lW′ : Lg W′)
       (ll : azero ⊲ W) (ll′ : azero ⊲ W′) (A₀ : F.Ig (cnt azero) W) (A₀′ : F.Ig (cnt azero) W′) →
       AR lW lW A₀ A₀ → AR lW lW′ A₀ A₀′ →
       ∀ w w′ → w ⊑ᴾ w′ → (Y : F.St W) (Y′ : F.St W′) → Ch Y → R∀ Y Y′ →
       OA (F.Run ac x q lW ll A₀ w Y) (F.Run ac′ x′ q′ lW′ ll′ A₀′ w′ Y′)
snd0 z0 (F.acc f) (F.acc f′) q q′ lW lW′ ll ll′ A₀ A₀′ aa a w w′ hw Y Y′ c r τ τ′ = z0
snd0 o1 (F.acc f) (F.acc f′) q q′ lW lW′ ll ll′ A₀ A₀′ aa a w w′ hw Y Y′ c r = a w w′ Y Y′ hw c r
snd0 (sq {x = x} {x′ = x′} hx hy) (F.acc f) (F.acc f′) q q′ lW lW′ ll ll′ A₀ A₀′ aa a w w′ hw Y Y′ c r τ τ′ =
  sq (Ox τ τ′)
     (snd0 hy (F.acc f) (F.acc f′) q q′ lW lW′ ll ll′ A₀ A₀′ aa a (w ⨾ nw q x) (w′ ⨾ nw q′ x′) (sq hw (wl (wr hx)))
           (Y F.⊕ Δ) (Y′ F.⊕ Δ′) (advA {Y = Y} {Y′ = Y} Δ Δ c (cohᴬ (F.acc f) x q lW ll A₀ aa w Y c))
           (advA {Y = Y} {Y′ = Y′} Δ Δ′ r Ox) τ τ′)
  where
  Δ = F.Run (F.acc f) x q lW ll A₀ w Y
  Δ′ = F.Run (F.acc f′) x′ q′ lW′ ll′ A₀′ w′ Y′
  Ox = snd0 hx (F.acc f) (F.acc f′) q q′ lW lW′ ll ll′ A₀ A₀′ aa a w w′ hw Y Y′ c r
snd0 (lm {d = d} {d′} hd) (F.acc f) (F.acc f′) q q′ lW lW′ ll ll′ A₀ A₀′ aa a w w′ hw Y Y′ c r τ τ′ =
  lm (λ n → proj₁ (go n) τ τ′)
  where
  P = λ n → F.Rpt (F.acc f) d q lW ll A₀ w Y n
  P′ = λ n → F.Rpt (F.acc f′) d′ q′ lW′ ll′ A₀′ w′ Y′ n
  Δ = λ n → F.Run (F.acc f) (d n) q lW ll A₀ (proj₁ (P n)) (proj₂ (P n))
  Δ′ = λ n → F.Run (F.acc f′) (d′ n) q′ lW′ ll′ A₀′ (proj₁ (P′ n)) (proj₂ (P′ n))
  St : ℕ → Set
  St n = (proj₁ (P n) ⊑ᴾ proj₁ (P′ n)) × Ch (proj₂ (P n)) × R∀ (proj₂ (P n)) (proj₂ (P′ n))
  st : ∀ n → St n
  go : ∀ n → OA (Δ n) (Δ′ n) × St n
  go n = let (hw′ , c′ , r′) = st n in
         snd0 (hd n) (F.acc f) (F.acc f′) q q′ lW lW′ ll ll′ A₀ A₀′ aa a _ _ hw′ _ _ c′ r′ , st n
  st zero = hw , c , r
  st (suc n) = let (hw′ , c′ , r′) = st n in
    sq hw′ (wl (wr (hd n))) ,
    advA {Y = proj₂ (P n)} {Y′ = proj₂ (P n)} (Δ n) (Δ n) c′ (cohᴬ (F.acc f) (d n) q lW ll A₀ aa _ _ c′) ,
    advA {Y = proj₂ (P n)} {Y′ = proj₂ (P′ n)} (Δ n) (Δ′ n) r′ (proj₁ (go n))
snd0 (wl {p = p} h) (F.acc f) (F.acc f′) q q′ lW lW′ ll ll′ A₀ A₀′ aa a w w′ hw Y Y′ c r =
  snd0 h (F.acc f) (F.acc f′) (⊲-tr p q) q′ lW lW′ ll ll′ A₀ A₀′ aa a w w′ hw Y Y′ c r
snd0 (wr {p = p} h) (F.acc f) (F.acc f′) q q′ lW lW′ ll ll′ A₀ A₀′ aa a w w′ hw Y Y′ c r =
  snd0 h (F.acc f) (F.acc f′) q (⊲-tr p q′) lW lW′ ll ll′ A₀ A₀′ aa a w w′ hw Y Y′ c r
snd0 (tr {y = y} hx hy) (F.acc f) (F.acc f′) q q′ lW lW′ ll ll′ A₀ A₀′ aa a w w′ hw Y Y′ c r τ τ′ =
  tr (snd0 hx (F.acc f) (F.acc f) q q lW lW ll ll A₀ A₀ aa aa w w (rfP w) Y Y c c τ τ)
     (snd0 hy (F.acc f) (F.acc f′) q q′ lW lW′ ll ll′ A₀ A₀′ aa a w w′ hw Y Y′ c r τ τ′)
snd0 (pr h) (F.acc f) (F.acc f′) q q′ lW lW′ ll ll′ A₀ A₀′ aa a w w′ hw Y Y′ c r τ τ′ =
  pr (snd0 h (F.acc f) (F.acc f′) q q′ lW lW′ ll ll′ A₀ A₀′ aa a w w′ hw Y Y′ c r τ τ′)
```
