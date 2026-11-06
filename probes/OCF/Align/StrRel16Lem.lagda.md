# 结构关系, 第十六轮 (一): 小引理: 分量的值, 左前缀, 状态向右延长

> 不读记号. 入口 [StrRel16](StrRel16.lagda.md). 接口 [StrRel16If](StrRel16If.lagda.md).
>
> 1. **(定理) `sum-mono`, `pt-ge`, `inSum`**: 第 $0$ 层的和对底单调; 分量 (`StrRel16If.In`) 的和不超过整棵树的和 (同一个底). `inSum` 是 `in⁺` 在第 $0$ 层的值可靠性的那一半.
> 2. **(定理) `Lp`, `lp→rel`, `lp-lf`, `jPfx`**: `Lp a c`: $a$ 是 $c$ 的左前缀 (只向左走). 若 $Y'$ 在每个目标上的读数与第 $0$ 层分量都是 $S$ 的左前缀 (`Pfx`: 折叠里状态只经 `⊕` 向右延长时就是这样), 则 `J² Y Y′ ⇒ J² Y S` (`StrRel15If.J²`, 旧关系; `prˣ` 与 `StrRel14J.Lf` 的 `left`).
> 3. **(定理) `V0.embX00`, `V0.vsum⁺`**: 两边都是第 $0$ 层时旧关系嵌进 `RelX⁺`; `RelX⁺ hz hz` 值可靠 (第 $0$ 层的和).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel16Lem where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.HtFeedTree using (H; LgH; D; D₀; n0; n1; _⨾_; nl; ni; nκ; nw; sum; pt; sum-fst)
open import OCF.Align.HtFeedClosed using (module At)
import OCF.Align.StrRel14If as If
import OCF.Align.StrRel14J as J14
import OCF.Align.StrRel15If as If²
import OCF.Align.StrRel16If as If³
```

## 1 第 $0$ 层: 分量的和

```agda
sum-mono : ∀ {W} (x : D₀ W) {β β′} → β ≤ β′ → sum β x ≤ sum β′ x
sum-mono n0 h = h
sum-mono n1 h = s≤ h
sum-mono (x ⨾ y) h = sum-mono y (sum-mono x h)
sum-mono (nl e) {β} {β′} h = l≤ (λ n → ≤l n (go n))
  where
  go : ∀ n → pt β e n ≤ pt β′ e n
  go zero = h
  go (suc n) = sum-mono (e n) (go n)
sum-mono (ni () u) h
sum-mono (nκ () u) h
sum-mono (nw p x) h = sum-mono x h

pt-ge : ∀ {W} β (e : ℕ → D₀ W) n → β ≤ pt β e n
pt-ge β e zero = ≤-refl β
pt-ge β e (suc n) = ≤-trans (pt-ge β e n) (⊲→≤ (sum-fst (pt β e n) (e n)))

module _ (Λ : H) (lΛ : LgH Λ) where
  open If³ Λ lΛ using (In; here; inL; inR; inE)

  inSum : ∀ {W} {y x : D₀ W} → In y x → ∀ β → sum β y ≤ sum β x
  inSum here β = ≤-refl _
  inSum {x = a ⨾ b} (inL h) β = ≤-trans (inSum h β) (⊲→≤ (sum-fst (sum β a) b))
  inSum {x = a ⨾ b} (inR h) β = ≤-trans (inSum h β) (sum-mono b (⊲→≤ (sum-fst β a)))
  inSum {x = nl e} (inE n h) β =
    ≤-trans (inSum h β) (≤-trans (sum-mono (e n) (pt-ge β e n)) (≤l (suc n) (≤-refl (pt β e (suc n)))))
```

## 2 左前缀与状态向右延长

```agda
data Lp {t : H} {m : A} (s : D t m) : D t m → Set where
  here : Lp s s
  left : ∀ {x y} → Lp s x → Lp s (x ⨾ y)

module Pf (Λ : H) (lΛ : LgH Λ) where
  open If Λ lΛ using (RelX; prˣ)
  open J14 Λ lΛ using (NE; Lf)
  open If² Λ lΛ using (J²)
  module Q = At Λ lΛ
  open Q using (Tg; St; yc; d; z)

  lp→rel : ∀ {t t′ V V′} {lV : Lg V} {lV′ : Lg V′} {a : D t V} {b c : D t′ V′} → RelX t t′ lV lV′ a b → Lp b c → RelX t t′ lV lV′ a c
  lp→rel h here = h
  lp→rel h (left p) = prˣ (lp→rel h p)

  lp-lf : ∀ {t m} {s a c : D t m} → Lf s a → Lp a c → Lf s c
  lp-lf h here = h
  lp-lf h (left p) = J14.left (lp-lf h p)

  Pfx : ∀ {W} → St W → St W → Set
  Pfx {W} Y S = (∀ {t m} (T : Tg W t m) → Lp (yc (d Y) T) (yc (d S) T)) × Lp (z Y) (z S)

  jPfx : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} {Y : St W} {Y′ S : St W′} → J² lW lW′ Y Y′ → Pfx Y′ S → J² lW lW′ Y S
  jPfx ((r , rz) , (ne , ne′)) (pf , pz) =
    ((λ T T′ tx → lp→rel (r T T′ tx) (pf T′)) , lp→rel rz pz) , (ne , (λ T → proj₁ (ne′ T) , lp-lf (proj₂ (ne′ T)) (pf T)))
```

## 3 第 $0$ 层对第 $0$ 层: 旧关系嵌入, 值可靠

`embX00`: 两边都是第 $0$ 层时, 旧的 `RelX hz hz` 嵌进 `RelX⁺ hz hz` (第 $0$ 层没有节点, `niˣ` 的逆变前提不出现). `vsum⁺`: `RelX⁺ hz hz` 的值可靠性 (`StrRel14NegNode.G.vsumX` 加 `in⁺` 一句, 用 `inSum`; `rk⁺` 不出现, 因为 `StH _ _ hz` 是空的).

```agda
module V0 (Λ : H) (lΛ : LgH Λ) where
  open If Λ lΛ using (RelX; n0ˣ; n1ˣ; ⨾ˣ; nlˣ; prˣ; nwˣ; niˣ; κˣ)
  open If³ Λ lΛ using (RelX⁺; n0⁺; n1⁺; ⨾⁺; nl⁺; pr⁺; nw⁺; ni⁺; κ⁺; in⁺; rk⁺; nκ⁺)
  open import OCF.Align.HtFeedTree using (hz)

  embX00 : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D₀ V} {x′ : D₀ V′} → RelX hz hz lV lV′ x x′ → RelX⁺ hz hz lV lV′ x x′
  embX00 n0ˣ = n0⁺
  embX00 n1ˣ = n1⁺
  embX00 (⨾ˣ hx hy) = ⨾⁺ (embX00 hx) (embX00 hy)
  embX00 (nlˣ hd) = nl⁺ (λ n → embX00 (hd n))
  embX00 (prˣ hx) = pr⁺ (embX00 hx)
  embX00 (nwˣ hp hx) = nw⁺ hp (embX00 hx)
  embX00 (niˣ {r = ()} _ _)
  embX00 (κˣ {zz = ()} _)

  vsum⁺ : ∀ {V V′ b b′} {lV : Lg V} {lV′ : Lg V′} {x : D₀ V} {x′ : D₀ V′} → RelX⁺ hz hz lV lV′ x x′ → b ≤ b′ → sum b x ≤ sum b′ x′
  vsum⁺ {b′ = b′} {x′ = x′} n0⁺ h = ≤-trans h (⊲→≤ (sum-fst b′ x′))
  vsum⁺ n1⁺ h = s≤ h
  vsum⁺ {b = b} {b′} (⨾⁺ {x = x} {y} {x′} {y′} hx hy) h = vsum⁺ {b = sum b x} {sum b′ x′} {x = y} {y′} hy (vsum⁺ {x = x} {x′} hx h)
  vsum⁺ {b = b} {b′} (nl⁺ {d₁ = e} {d₁′ = e′} hd) h = l≤ (λ n → ≤l n (go n))
    where
    go : ∀ n → pt b e n ≤ pt b′ e′ n
    go zero = h
    go (suc n) = vsum⁺ {b = pt b e n} {pt b′ e′ n} {x = e n} {e′ n} (hd n) (go n)
  vsum⁺ {b = b} {b′} (pr⁺ {x = x} {x′ = x′} {y′} hx) h = ≤-trans (vsum⁺ {b = b} {b′} {x = x} {x′} hx h) (⊲→≤ (sum-fst (sum b′ x′) y′))
  vsum⁺ {b = b} {b′} (nw⁺ {x = x} {x′} hp hx) h = vsum⁺ {b = b} {b′} {x = x} {x′} hx h
  vsum⁺ (ni⁺ {r = ()} _ _)
  vsum⁺ (κ⁺ {zz = ()} _)
  vsum⁺ {b′ = b′} (in⁺ hx p) h = ≤-trans (vsum⁺ hx h) (inSum Λ lΛ p b′)
  vsum⁺ (rk⁺ r r′ lW lW′ ac ac₁ ac′ ac₁′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′ T T′ () pre tx eL eR)
  vsum⁺ (nκ⁺ {r = ()} _)
```
