# 结构关系, 第五轮 (一): `walk` 的结构结论

> 不含记号. 入口 [StrRel5](StrRel5.lagda.md). 接 [StrRel4Walk](StrRel4Walk.lagda.md) 的对齐 `Al`, [StrRel4Pr](StrRel4Pr.lagda.md) 的 $\sqsubseteq^{\mathsf P}$.
>
> `StrRel4Walk.walk` 的结论是值. 这里把它换成**结构**: 两边 `Walk` 的第 0 层读数 (各自固定一条读数路径 $k_L$, $k_R$) 由 $\sqsubseteq^{\mathsf P}$ 相关. 状态关系 $R$ 与分支前提都作参数, 只要求:
>
> - `adv`: $R$ 对 `⊕` 封闭, 只要两段输出的读数 $\sqsubseteq^{\mathsf P}$ 相关;
> - `br`: 对齐的一对位置 ($c\le c'$, 领先量 $\mathrm{Adm}(c,c';W,W')$) 上, 在 $R$ 相关的状态里, 两个分支的输出读数 $\sqsubseteq^{\mathsf P}$ 相关 (对一切 $q,q',w,w'$).
>
> **定理 `walkˢ`**: 对一切对齐推导, 两边 `Walk` 的读数 $\sqsubseteq^{\mathsf P}$ 相关. 五句一一对应: `aS` ↦ `z0`, `aP` ↦ `sq`, `aR`/`aRL` ↦ `pr`, `aL` ↦ `sq` 加 `lm`. 部分和规则 `pr` 正是右边多出位置时要的.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel5Walk where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.SumOneTree using (D; _⨾_; Cut; tailP; cnt)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KValTree using (Bk)
open import OCF.Align.KValSem using (ac₁)
open import OCF.Align.KNestAdm using (Adm)
open import OCF.Align.StrRel4Walk using (Al; aS; aP; aR; aRL; aL)
open import OCF.Align.StrRel4Pr using (_⊑ᴾ_; z0; sq; lm; pr)
```

## §1 参数

一边的运行环境: 世界 $W$, 长度证据, 回灌层路径, 动作, 读数路径. 不用 `KValSound.Sd`, 所以对值语义和 `StrRel3Lo` 的结构语义都适用.

```agda
record Env : Set where
  constructor env
  field
    W   : A
    lW  : Lg W
    ll  : one ⊲ W
    act : F.Ig (cnt one) W
    k   : azero ⊲ W
open Env public

Rd : (s : Env) → F.Df (W s) → D azero (W s)
Rd s Δ = F.yc Δ (inj₁ (k s)) tt

Rn : (s : Env) → ∀ {V} → D one V → V ⊲ W s → D one (W s) → F.St (W s) → F.Df (W s)
Rn s x q w Y = F.Run ac₁ x q (lW s) (ll s) (act s) w Y

Wlk : (s : Env) → ∀ {V} (u : Bk V) {a b} (p : a ⊲ b) (ap : V ⊲ a) (lb : Lg b) (bV : b ⊲ W s) → D one (W s) → F.St (W s) → F.Df (W s)
Wlk s u {b = b} p ap lb bV co Y = F.Walk ac₁ u b p ap lb bV (lW s) (ll s) (act s) co Y
```

## §2 定理

```agda
module GoS (s s′ : Env) {V V′} (u : Bk V) (u′ : Bk V′) (R : F.St (W s) → F.St (W s′) → Set)
           (adv : ∀ {Y Y′} (Δ : F.Df (W s)) (Δ′ : F.Df (W s′)) → R Y Y′ → Rd s Δ ⊑ᴾ Rd s′ Δ′ → R (Y F.⊕ Δ) (Y′ F.⊕ Δ′))
           (br : ∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → c ≤ c′ → Adm c c′ (W s) (W s′) →
                 ∀ (q : c ⊲ W s) (q′ : c′ ⊲ W s′) w w′ Y Y′ → R Y Y′ → Rd s (Rn s (u p lc) q w Y) ⊑ᴾ Rd s′ (Rn s′ (u′ p′ lc′) q′ w′ Y′)) where

  walkˢ : ∀ {a b a′ b′} {p : a ⊲ b} {lb : Lg b} {p′ : a′ ⊲ b′} {lb′ : Lg b′} → Al (W s) (W s′) p lb p′ lb′ →
          ∀ ap ap′ bV bV′ co co′ Y Y′ → R Y Y′ → Rd s (Wlk s u p ap lb bV co Y) ⊑ᴾ Rd s′ (Wlk s′ u′ p′ ap′ lb′ bV′ co′ Y′)
  walkˢ (aS p′ lb′) ap ap′ bV bV′ co co′ Y Y′ r = z0
  walkˢ (aR H) ap ap′ bV bV′ co co′ Y Y′ r = pr (walkˢ H ap ap′ bV (⊲-tr (C.suc C.self) bV′) co co′ Y Y′ r)
  walkˢ (aRL H) ap ap′ bV bV′ co co′ Y Y′ r = pr (walkˢ H ap ap′ bV (⊲-tr (C.lim _ C.self) bV′) co co′ Y Y′ r)
  walkˢ (aP {c = c} {c′ = c′} {p = p} {lc} {p′} {lc′} H c≤ ad) ap ap′ bV bV′ co co′ Y Y′ r =
    sq O (br (⊲-tr ap p) (⊲-tr ap′ p′) lc lc′ c≤ ad (⊲-tr (C.suc C.self) bV) (⊲-tr (C.suc C.self) bV′)
             (co ⨾ Cut u c p ap lc (⊲-tr (C.suc C.self) bV)) (co′ ⨾ Cut u′ c′ p′ ap′ lc′ (⊲-tr (C.suc C.self) bV′))
             (Y F.⊕ Δ) (Y′ F.⊕ Δ′) (adv Δ Δ′ r O))
    where
    Δ = Wlk s u p ap lc (⊲-tr (C.suc C.self) bV) co Y
    Δ′ = Wlk s′ u′ p′ ap′ lc′ (⊲-tr (C.suc C.self) bV′) co′ Y′
    O = walkˢ H ap ap′ (⊲-tr (C.suc C.self) bV) (⊲-tr (C.suc C.self) bV′) co co′ Y Y′ r
  walkˢ (aL {f = f} {n} {f′ = f′} {n′} {p} {p′} {stp} {wl} {stp′} {wl′} H G) ap ap′ bV bV′ co co′ Y Y′ r =
    sq O (lm (λ m → proj₁ (go m)))
    where
    fV : ∀ m → f m ⊲ W s
    fV m = ⊲-tr (C.lim m C.self) bV
    fV′ : ∀ m → f′ m ⊲ W s′
    fV′ m = ⊲-tr (C.lim m C.self) bV′
    Δ = Wlk s u p ap (wl n) (fV n) co Y
    Δ′ = Wlk s′ u′ p′ ap′ (wl′ n′) (fV′ n′) co′ Y′
    O = walkˢ H ap ap′ (fV n) (fV′ n′) co co′ Y Y′ r
    Rp = F.WRp ac₁ u f stp wl p ap fV (lW s) (ll s) (act s) (co ⨾ Cut u (f n) p ap (wl n) (fV n)) (Y F.⊕ Δ)
    Rp′ = F.WRp ac₁ u′ f′ stp′ wl′ p′ ap′ fV′ (lW s′) (ll s′) (act s′) (co′ ⨾ Cut u′ (f′ n′) p′ ap′ (wl′ n′) (fV′ n′)) (Y′ F.⊕ Δ′)
    Sg : ℕ → F.Df (W s)
    Sg m = Wlk s u (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV (suc (m + n))) (proj₁ (Rp m)) (proj₂ (Rp m))
    Sg′ : ℕ → F.Df (W s′)
    Sg′ m = Wlk s′ u′ (stp′ (m + n′)) (⊲-tr ap′ (tailP f′ stp′ p′ m)) (wl′ (suc (m + n′))) (fV′ (suc (m + n′))) (proj₁ (Rp′ m)) (proj₂ (Rp′ m))
    st : ∀ m → R (proj₂ (Rp m)) (proj₂ (Rp′ m))
    go : ∀ m → (Rd s (Sg m) ⊑ᴾ Rd s′ (Sg′ m)) × R (proj₂ (Rp m)) (proj₂ (Rp′ m))
    go m = walkˢ (G m) _ _ _ _ _ _ _ _ (st m) , st m
    st zero = adv Δ Δ′ r O
    st (suc m) = adv (Sg m) (Sg′ m) (st m) (proj₁ (go m))
```
