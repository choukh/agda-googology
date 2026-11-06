# 第十九轮的否定 (工具): `RelX⁺⁺` 的第 $0$ 层值, $\Omega_t$ 的比较, `Act` 的再折叠

> 不读记号. 入口 [NegSR19](NegSR19.lagda.md). 对着接口 [StrRel19If](StrRel19If.lagda.md) (定稿 2026-11-05 16:01) 写. 把 `StrRel16Lem.V0.vsum⁺`, `StrRel16Fin.FinΛ⁺` 的几条与 `NegSR17Rk.RK.ge` 搬到 `RelX⁺⁺` 与动作 `Act` 上.
>
> 1. **(定理) `vsum⁺⁺`**: 第 $0$ 层对第 $0$ 层的 `RelX⁺⁺` 推出和的 $\le$ (一切 $\Lambda$). `rk⁺⁺` 与 `up` 的右边是第 $L'$ 层的节点, `StH _ _ hz` 是空的, 所以都不出现.
> 2. **(定理) `ΩRX⁺⁺`, `stepOA⁺⁺`, `hawAct⁺⁺`, `hawS`**: 有限的 $\Lambda$ 上, $t\sqsubseteq_\infty t'$ ⇒ $\Omega_t\le\Omega_{t'}$; `Act` 对 `Act` 满足 `HAW⁺⁺`, 加上两个 `sAct` 就是 `HAWS`.
> 3. **(定理) `jYs⁺⁺`**: 差为 `dN` (同 `NegSR17RkT.dN`) 的状态, 累计相关则 `J⁺⁺`.
> 4. **(定理) `RKA.ge`**: 以每次至少加一的第 $0$ 层动作 (例如 `Act`, `hActT`) 再折叠第 $0$ 层的树, 和不减.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSR19Lem where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.HtFeedTree using (H; LgH; hz; hs; hself; ss; D; D₀; n0; n1; _⨾_; nl; ni; nκ; nw; Ωd; AccY; sum; pt; sum-fst)
open import OCF.Align.HtFeedClosed using (module At)
import OCF.Align.StrRel11Rk as Rk
import OCF.Align.StrRel14J as J14
import OCF.Align.StrRel16If as If³
import OCF.Align.StrRel19If as If⁵
open import OCF.Align.StrRel15Fin using (Fin; fin⊲)
open import OCF.Align.StrRel16Lem using (sum-mono; inSum)
```

## 1 第 $0$ 层的值

```agda
module V0⁺⁺ (Λ : H) (lΛ : LgH Λ) where
  open If⁵ Λ lΛ

  vsum⁺⁺ : ∀ {V V′ b b′} {lV : Lg V} {lV′ : Lg V′} {x : D₀ V} {x′ : D₀ V′} → RelX⁺⁺ hz hz lV lV′ x x′ → b ≤ b′ → sum b x ≤ sum b′ x′
  vsum⁺⁺ {b′ = b′} {x′ = x′} n0⁺⁺ h = ≤-trans h (⊲→≤ (sum-fst b′ x′))
  vsum⁺⁺ n1⁺⁺ h = s≤ h
  vsum⁺⁺ {b = b} {b′} (⨾⁺⁺ {x = x} {y} {x′} {y′} hx hy) h = vsum⁺⁺ {b = sum b x} {sum b′ x′} {x = y} {y′} hy (vsum⁺⁺ {x = x} {x′} hx h)
  vsum⁺⁺ {b = b} {b′} (nl⁺⁺ {d₁ = e} {d₁′ = e′} hd) h = l≤ (λ n → ≤l n (go n))
    where
    go : ∀ n → pt b e n ≤ pt b′ e′ n
    go zero = h
    go (suc n) = vsum⁺⁺ {b = pt b e n} {pt b′ e′ n} {x = e n} {e′ n} (hd n) (go n)
  vsum⁺⁺ {b = b} {b′} (pr⁺⁺ {x = x} {x′ = x′} {y′} hx) h = ≤-trans (vsum⁺⁺ {b = b} {b′} {x = x} {x′} hx h) (⊲→≤ (sum-fst (sum b′ x′) y′))
  vsum⁺⁺ {b = b} {b′} (nw⁺⁺ {x = x} {x′} hp hx) h = vsum⁺⁺ {b = b} {b′} {x = x} {x′} hx h
  vsum⁺⁺ (ni⁺⁺ {r = ()} _ _)
  vsum⁺⁺ (κ⁺⁺ {zz = ()} _)
  vsum⁺⁺ {b′ = b′} (in⁺⁺ hx p) h = ≤-trans (vsum⁺⁺ hx h) (inSum Λ lΛ p b′)
  vsum⁺⁺ (rk⁺⁺ r r′ lW lW′ ac ac₁ ac′ ac₁′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′ T T′ () pre tx eL eR)
  vsum⁺⁺ (nκ⁺⁺ {r = ()} _)
  vsum⁺⁺ (up r lW ac ac₁ q₀ ll A₀ w Y T T′ () sA eL eR h)
```

## 2 有限的 $\Lambda$: $\Omega_t$ 的比较, `Act` 的动作前提, 差为 `dN` 的状态

```agda
module Fin⁺⁺ (Λ : H) (lΛ : LgH Λ) (fΛ : Fin Λ) where
  open Rk Λ lΛ using (_⊑∞_; s∞; u∞; tr∞)
  open If⁵ Λ lΛ
  open If³.P Λ lΛ using (Tg; tm; St; st; Df; df; yc; d; z; Step; Act)

  -- 每个目标 (层 t) 上读 ω⋅(Ω_t ⨾ 0) 的差 (同 NegSR17RkT.dN), 累计任意
  dN : ∀ {W} → Df W
  dN = df (λ {t} T → nl (λ _ → Ωd t ⨾ n0))

  Ys : ∀ {W} → D₀ W → St W
  Ys zz = st dN zz

  pred⊑ : ∀ {b b′} → hs b ⊑∞ hs b′ → b ⊑∞ b′
  pred⊑ s∞ = s∞
  pred⊑ (u∞ h) = tr∞ (u∞ s∞) h

  ΩRX⁺⁺ : ∀ {t t′} → Fin t → Fin t′ → t ⊑∞ t′ → ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} → RelX⁺⁺ t t′ lW lW′ (Ωd t {W}) (Ωd t′ {W′})
  ΩRX⁺⁺ {t = hz} {t′ = hz} f f′ h = n1⁺⁺
  ΩRX⁺⁺ {t = hz} {t′ = hs b′} f f′ h = pr⁺⁺ n1⁺⁺
  ΩRX⁺⁺ {t = hs b} {t′ = hz} f f′ ()
  ΩRX⁺⁺ {t = hs b} {t′ = hs b′} f f′ h = ⨾⁺⁺ n1⁺⁺ (ni⁺⁺ {r = ss hself} {r′ = ss hself} (pred⊑ h) (λ p p′ lc lc′ cp y y′ hb → n1⁺⁺))

  stepOA⁺⁺ : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} {Y : St W} {Y′ : St W′} → J⁺⁺ lW lW′ Y Y′ → OA⁺⁺ lW lW′ (Step Y) (Step Y′)
  stepOA⁺⁺ hY T T′ tx = nl⁺⁺ (λ _ → ⨾⁺⁺ (ΩRX⁺⁺ (fin⊲ (tm T) fΛ) (fin⊲ (tm T′) fΛ) (proj₂ tx)) (proj₁ (proj₁ hY) T T′ tx))

  hawAct⁺⁺ : ∀ L L′ {W W′} {lW : Lg W} {lW′ : Lg W′} → HAW⁺⁺ L L′ lW lW′ (Act {L} {W}) (Act {L′} {W′})
  hawAct⁺⁺ L L′ p p′ l l′ cp w w′ hw Y Y′ hY = stepOA⁺⁺ hY

  hawS : ∀ L L′ {W W′} {lW : Lg W} {lW′ : Lg W′} → HAWS L L′ lW lW′ (Act {L} {W}) (Act {L′} {W′})
  hawS L L′ = hawAct⁺⁺ L L′ , (sAct , sAct)

  oaN : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} → OA⁺⁺ lW lW′ (dN {W}) (dN {W′})
  oaN T T′ tx = nl⁺⁺ (λ _ → ⨾⁺⁺ (ΩRX⁺⁺ (fin⊲ (tm T) fΛ) (fin⊲ (tm T′) fΛ) (proj₂ tx)) n0⁺⁺)

  neN : ∀ {W} (zz : D₀ W) → J14.NE Λ lΛ (Ys zz)
  neN zz T = n0 , J14.here

  jYs⁺⁺ : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} {zz : D₀ W} {zz′ : D₀ W′} → RelX⁺⁺ hz hz lW lW′ zz zz′ → J⁺⁺ lW lW′ (Ys zz) (Ys zz′)
  jYs⁺⁺ {zz = zz} {zz′} rz = (oaN , rz) , (neN zz , neN zz′)
```

## 3 以至少加一的动作再折叠第 $0$ 层的树

```agda
module RKA (Λ : H) (lΛ : LgH Λ) where
  open If³.P Λ lΛ using (Tg; τ₀; St; yc; d; Run; Rpt; Ig; LW; Act; _⊕⟨_⟩_)

  -- Act 在第 0 层目标上至少加一 (一切目标, 不只 τ₀)
  hActT : ∀ {W} (lW : Lg W) (w : D hz W) (Y : St W) {m} (T : Tg W hz m) b → asuc b ≤ sum b (yc (Act {hz} {W} C.self lW w Y) T)
  hActT lW w Y T b = ≤l 1 (⊲→≤ (sum-fst (asuc b) (yc (d Y) T)))

  module Ge {W} (lW : Lg W) (A₀ : Ig hz W) (hA : ∀ (w : D hz W) (Y : St W) {m} (T : Tg W hz m) b → asuc b ≤ sum b (yc (A₀ C.self lW w Y) T)) where
    ge : ∀ (ac : AccY hz) {V} (x : D₀ V) (q : V ⊲ W) (ll : LW hz W) (w : D₀ W) (Y : St W) {m} (T : Tg W hz m) b →
         sum b x ≤ sum b (yc (Run ac x q lW ll A₀ w Y) T)
    ge ac n0 q ll w Y T b = ≤-refl b
    ge ac n1 q ll w Y T b = hA w Y T b
    ge ac (x ⨾ y) q ll w Y T b =
      ≤-trans (sum-mono y (ge ac x q ll w Y T b))
              (ge ac y q ll (w ⨾ nw q x) (Y ⊕⟨ lW ⟩ Run ac x q lW ll A₀ w Y) T (sum b (yc (Run ac x q lW ll A₀ w Y) T)))
    ge ac (nl F) q ll w Y T b = l≤ (λ n → ≤l n (go n))
      where
      go : ∀ n → pt b F n ≤ pt b (λ n → yc (Run ac (F n) q lW ll A₀ (proj₁ (Rpt ac F q lW ll A₀ w Y n)) (proj₂ (Rpt ac F q lW ll A₀ w Y n))) T) n
      go zero = ≤-refl b
      go (suc n) = ≤-trans (sum-mono (F n) (go n)) (ge ac (F n) q ll (proj₁ (Rpt ac F q lW ll A₀ w Y n)) (proj₂ (Rpt ac F q lW ll A₀ w Y n)) T _)
    ge ac (nw p x) q ll w Y T b = ge ac x (⊲-tr p q) ll w Y T b
    ge ac (ni () u) q ll w Y T b
    ge ac (nκ () u) q ll w Y T b
```
