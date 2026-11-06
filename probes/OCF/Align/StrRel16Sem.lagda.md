# 结构关系, 第十六轮 (三): `RelX⁺` 的两条状态律, 六条规则, `in⁺` 的可靠性, 左层为 $0$ 的语义

> 不读记号. 入口 [StrRel16](StrRel16.lagda.md). 接口 [StrRel16If](StrRel16If.lagda.md).
>
> 1. **(定理) `law⊕⁺`, `lawcv⁺`**: 接口的 `Law⊕⁺`, `Lawcv⁺` (证明同 `StrRel15Sem.law⊕`/`lawcv`, 构造子换成 `⁺`).
> 2. **(定理) `ext⁺`, `jPfx⁺`**: 状态向右延长 (`⊕`), 或右边状态的读数是左前缀 (`StrRel16Lem.Lp`) 时, `J²⁺` 保持.
> 3. **(定理) 六条规则 `sem-n0` … `sem-pr`** (`Six`): 同 `StrRel15Sem.Six`, 对一切层, 结论 `OA²⁺`.
> 4. **(定理) `sem-in`: 新规则 `in⁺` 可靠, 对一切层.** 若 $x\le y'$ 有语义, $y'$ 是 $x'$ 的分量, 则 $x\le x'$ 有语义. 证明: $x'$ 的运行在 $y'$ 的位置上运行 $y'$, 那里的上下文与状态是 $x'$ 的上下文与状态向右延长 (`pos`, `posOK`), 输出是 $x'$ 的输出的分量 (`runIn`). 于是在每个 `TX` 目标对上, $x$ 的输出 $\le$ $y'$ 的输出 (前提), 再由 `in⁺` 到 $x'$ 的输出.
> 5. **(定理) `semX00⁺`: 两边都是第 $0$ 层时, `RelX⁺ hz hz ⇒ SemX²⁺ hz hz`, 无条件.** 这时 `rk⁺` 不出现 (它的右边是第 $L'$ 层的节点, `StH _ _ hz` 是空的), `ni⁺`, `κ⁺`, `nκ⁺` 也不出现.
> 6. **(条件定理) `semX0⁺`: 左层为 $0$, 右层 $L'$ 任意: `RkSound₀ L′` ⇒ (`RelX⁺ hz L′ ⇒ SemX²⁺ hz L′`).** 只有 `rk⁺` 一条要条件 (接口 §6).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
module OCF.Align.StrRel16Sem (Λ : H) (lΛ : LgH Λ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; StH; ss; sl; sL; D; n0; n1; _⨾_; nl; nw; AccY;
  outS)
open import OCF.Align.HtFeedClosed using (module At)
open import OCF.Align.StrRel11Rk Λ lΛ using (_⊑∞_; s∞; u∞; l∞; L∞)
open import OCF.Align.StrRel12Al using (AP; CP; cp-top; cp-tr)
open import OCF.Align.StrRel12Sem Λ lΛ using (Top)
open import OCF.Align.StrRel14J Λ lΛ using (NE; ne⊕; necv)
open import OCF.Align.StrRel15If Λ lΛ using (TX)
open import OCF.Align.StrRel16Lem using (Lp; here; left)
open import OCF.Align.StrRel16If Λ lΛ

open P using (Tg; tg; wm; tm; lm; tg↑; τ₀; St; Df; yc; d; z; cv; _⊕⟨_⟩_; Run; Rpt; Ig; Ig↾; LW)
open import OCF.Align.StrRel16Lem using (module Pf)
open Pf Λ lΛ using (lp-lf)
```

## 1 两条状态律, 状态向右延长

```agda
law⊕⁺ : Law⊕⁺
law⊕⁺ {lW = lW} {lW′} tp Y Y′ Δ Δ′ ((r , rz) , (ne , ne′)) O =
  ((λ T T′ tx → ⨾⁺ (r T T′ tx) (O T T′ tx)) , ⨾⁺ rz (O (τ₀ lW) (τ₀ lW′) (tp , s∞))) ,
  (ne⊕ {lW = lW} Y Δ ne , ne⊕ {lW = lW′} Y′ Δ′ ne′)

lawcv⁺ : Lawcv⁺
lawcv⁺ {q = q} {q′ = q′} ap Y Y′ ((r , rz) , (ne , ne′)) =
  ((λ T T′ tx → r (tg↑ q T) (tg↑ q′ T′) (cp-tr ap (proj₁ tx) , proj₂ tx)) , n0⁺) , (necv q Y ne , necv q′ Y′ ne′)

ext⁺ : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} {Y : St W} {Y′ : St W′} → J²⁺ lW lW′ Y Y′ → ∀ (Δ′ : Df W′) → J²⁺ lW lW′ Y (Y′ ⊕⟨ lW′ ⟩ Δ′)
ext⁺ {lW′ = lW′} {Y′ = Y′} ((r , rz) , (ne , ne′)) Δ′ = ((λ T T′ tx → pr⁺ (r T T′ tx)) , pr⁺ rz) , (ne , ne⊕ {lW = lW′} Y′ Δ′ ne′)

lp→rel⁺ : ∀ {t t′ V V′} {lV : Lg V} {lV′ : Lg V′} {a : D t V} {b c : D t′ V′} → RelX⁺ t t′ lV lV′ a b → Lp b c → RelX⁺ t t′ lV lV′ a c
lp→rel⁺ h here = h
lp→rel⁺ h (left p) = pr⁺ (lp→rel⁺ h p)

Pfx : ∀ {W} → St W → St W → Set
Pfx {W} Y S = (∀ {t m} (T : Tg W t m) → Lp (yc (d Y) T) (yc (d S) T)) × Lp (z Y) (z S)

jPfx⁺ : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} {Y : St W} {Y′ S : St W′} → J²⁺ lW lW′ Y Y′ → Pfx Y′ S → J²⁺ lW lW′ Y S
jPfx⁺ ((r , rz) , (ne , ne′)) (pf , pz) =
  ((λ T T′ tx → lp→rel⁺ (r T T′ tx) (pf T′)) , lp→rel⁺ rz pz) , (ne , (λ T → proj₁ (ne′ T) , lp-lf (proj₂ (ne′ T)) (pf T)))

haw↾²⁺ : ∀ L L′ {W W′ W₁ W₁′} {lW : Lg W} {lW′ : Lg W′} {p : W ⊲ W₁} {lW₁ : Lg W₁} {p′ : W′ ⊲ W₁′} {lW₁′ : Lg W₁′}
           {A₀ : Ig L W} {A₀′ : Ig L′ W′} → AP lW lW′ p lW₁ p′ lW₁′ → HAW²⁺ L L′ lW lW′ A₀ A₀′ → HAW²⁺ L L′ lW₁ lW₁′ (Ig↾ p A₀) (Ig↾ p′ A₀′)
haw↾²⁺ L L′ {p = p} {p′ = p′} ap ha p₂ p₂′ l l′ cp = ha (⊲-tr p p₂) (⊲-tr p′ p₂′) l l′ (cp-tr ap cp)
```

## 2 六条规则

```agda
module Six {L L′ : H} where
  sem-n0 : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x′ : D L′ V′} → SemX²⁺ L L′ lV lV′ n0 x′
  sem-n0 lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r T T′ ta = n0⁺

  sem-n1 : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} → SemX²⁺ L L′ lV lV′ n1 n1
  sem-n1 lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r = ha C.self C.self lW lW′ (cp-top hq) w w′ hw Y Y′ r

  sem-⨾ : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x y : D L V} {x′ y′ : D L′ V′} →
          RelX⁺ L L′ lV lV′ x x′ → SemX²⁺ L L′ lV lV′ x x′ → SemX²⁺ L L′ lV lV′ y y′ → SemX²⁺ L L′ lV lV′ (x ⨾ y) (x′ ⨾ y′)
  sem-⨾ {x = x} {x′ = x′} hx sx sy lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r T T′ ta =
    ⨾⁺ (Ox T T′ ta)
       (sy lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha (w ⨾ nw q x) (w′ ⨾ nw q′ x′) (⨾⁺ hw (nw⁺ (proj₁ hq) hx))
           _ _ (law⊕⁺ (cp-top hq) Y Y′ Δ Δ′ r Ox) T T′ ta)
    where
    Δ = Run ac x q lW ll A₀ w Y
    Δ′ = Run ac′ x′ q′ lW′ ll′ A₀′ w′ Y′
    Ox = sx lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r

  sem-nw : ∀ {V₀ V₀′ V V′} {lV₀ : Lg V₀} {lV₀′ : Lg V₀′} {lV : Lg V} {lV′ : Lg V′} {p : V₀ ⊲ V} {p′ : V₀′ ⊲ V′}
             {x : D L V₀} {x′ : D L′ V₀′} →
           AP lV₀ lV₀′ p lV p′ lV′ → SemX²⁺ L L′ lV₀ lV₀′ x x′ → SemX²⁺ L L′ lV lV′ (nw p x) (nw p′ x′)
  sem-nw hp sx lW lW′ ac ac′ ll ll′ q q′ hq = sx lW lW′ ac ac′ ll ll′ (⊲-tr _ q) (⊲-tr _ q′) (cp-tr hp hq)

  sem-pr : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {x′ y′ : D L′ V′} →
           SemX²⁺ L L′ lV lV′ x x′ → SemX²⁺ L L′ lV lV′ x (x′ ⨾ y′)
  sem-pr sx lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r T T′ ta =
    pr⁺ (sx lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r T T′ ta)

  module NL {V V′} {lV : Lg V} {lV′ : Lg V′} {d₁ : ℕ → D L V} {d₁′ : ℕ → D L′ V′}
            (hd : ∀ n → RelX⁺ L L′ lV lV′ (d₁ n) (d₁′ n)) (sd : ∀ n → SemX²⁺ L L′ lV lV′ (d₁ n) (d₁′ n))
            {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac′ : AccY L′) (ll : LW L W) (ll′ : LW L′ W′)
            (q : V ⊲ W) (q′ : V′ ⊲ W′) (hq : CP lV lV′ q lW q′ lW′)
            (A₀ : Ig L W) (A₀′ : Ig L′ W′) (ha : HAW²⁺ L L′ lW lW′ A₀ A₀′)
            (w : D L W) (w′ : D L′ W′) (hw : RelX⁺ L L′ lW lW′ w w′) (Y : St W) (Y′ : St W′) (r : J²⁺ lW lW′ Y Y′) where
    Pn : ℕ → D L W × St W
    Pn = Rpt ac d₁ q lW ll A₀ w Y
    Pn′ : ℕ → D L′ W′ × St W′
    Pn′ = Rpt ac′ d₁′ q′ lW′ ll′ A₀′ w′ Y′

    St′ : ℕ → Set
    St′ n = RelX⁺ L L′ lW lW′ (proj₁ (Pn n)) (proj₁ (Pn′ n)) × J²⁺ lW lW′ (proj₂ (Pn n)) (proj₂ (Pn′ n))

    out : ∀ n → St′ n → OA²⁺ lW lW′ (Run ac (d₁ n) q lW ll A₀ (proj₁ (Pn n)) (proj₂ (Pn n)))
                                     (Run ac′ (d₁′ n) q′ lW′ ll′ A₀′ (proj₁ (Pn′ n)) (proj₂ (Pn′ n)))
    out n (h , s) = sd n lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha _ _ h _ _ s

    go : ∀ n → St′ n
    go zero = hw , r
    go (suc n) = ⨾⁺ (proj₁ (go n)) (nw⁺ (proj₁ hq) (hd n)) ,
                 law⊕⁺ (cp-top hq) (proj₂ (Pn n)) (proj₂ (Pn′ n)) _ _ (proj₂ (go n)) (out n (go n))

  sem-nl : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {d₁ : ℕ → D L V} {d₁′ : ℕ → D L′ V′} →
           (∀ n → RelX⁺ L L′ lV lV′ (d₁ n) (d₁′ n)) → (∀ n → SemX²⁺ L L′ lV lV′ (d₁ n) (d₁′ n)) → SemX²⁺ L L′ lV lV′ (nl d₁) (nl d₁′)
  sem-nl hd sd lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r T T′ ta =
    nl⁺ (λ n → N.out n (N.go n) T T′ ta)
    where module N = NL hd sd lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r

open Six public
```

## 3 `in⁺` 的可靠性

`pos h w Y`: $x'$ 的运行走到分量 $y'$ (路径 `h`) 时的上下文与状态. `runIn`: 那里 $y'$ 的输出是 $x'$ 的输出的分量 (逐目标, 定义性的). `posOK`: 左边的上下文与状态和那里的仍相关 (向右延长).

```agda
module RunIn {L L′ V′ W W′} {lW : Lg W} (lW′ : Lg W′) (ac′ : AccY L′) (q′ : V′ ⊲ W′) (ll′ : LW L′ W′) (A₀′ : Ig L′ W′) where
  pos : ∀ {y′ x′ : D L′ V′} → In y′ x′ → D L′ W′ → St W′ → D L′ W′ × St W′
  pos here w Y = w , Y
  pos (inL h) w Y = pos h w Y
  pos {x′ = a ⨾ b} (inR h) w Y = pos h (w ⨾ nw q′ a) (Y ⊕⟨ lW′ ⟩ Run ac′ a q′ lW′ ll′ A₀′ w Y)
  pos {x′ = nl e} (inE n h) w Y = pos h (proj₁ (Rpt ac′ e q′ lW′ ll′ A₀′ w Y n)) (proj₂ (Rpt ac′ e q′ lW′ ll′ A₀′ w Y n))

  runIn : ∀ {y′ x′ : D L′ V′} (h : In y′ x′) w Y → ∀ {t m} (T : Tg W′ t m) →
          In (yc (Run ac′ y′ q′ lW′ ll′ A₀′ (proj₁ (pos h w Y)) (proj₂ (pos h w Y))) T) (yc (Run ac′ x′ q′ lW′ ll′ A₀′ w Y) T)
  runIn here w Y T = here
  runIn (inL h) w Y T = inL (runIn h w Y T)
  runIn {x′ = a ⨾ b} (inR h) w Y T = inR (runIn h (w ⨾ nw q′ a) (Y ⊕⟨ lW′ ⟩ Run ac′ a q′ lW′ ll′ A₀′ w Y) T)
  runIn {x′ = nl e} (inE n h) w Y T = inE n (runIn h _ _ T)

  rptOK : ∀ (e : ℕ → D L′ V′) {w₀ : D L W} {Y₀ : St W} w Y → RelX⁺ L L′ lW lW′ w₀ w → J²⁺ lW lW′ Y₀ Y → ∀ n →
          RelX⁺ L L′ lW lW′ w₀ (proj₁ (Rpt ac′ e q′ lW′ ll′ A₀′ w Y n)) × J²⁺ lW lW′ Y₀ (proj₂ (Rpt ac′ e q′ lW′ ll′ A₀′ w Y n))
  rptOK e w Y hw hY zero = hw , hY
  rptOK e w Y hw hY (suc n) = pr⁺ (proj₁ (rptOK e w Y hw hY n)) , ext⁺ (proj₂ (rptOK e w Y hw hY n)) _

  posOK : ∀ {y′ x′ : D L′ V′} (h : In y′ x′) {w₀ : D L W} {Y₀ : St W} w Y → RelX⁺ L L′ lW lW′ w₀ w → J²⁺ lW lW′ Y₀ Y →
          RelX⁺ L L′ lW lW′ w₀ (proj₁ (pos h w Y)) × J²⁺ lW lW′ Y₀ (proj₂ (pos h w Y))
  posOK here w Y hw hY = hw , hY
  posOK (inL h) w Y hw hY = posOK h w Y hw hY
  posOK {x′ = a ⨾ b} (inR h) w Y hw hY = posOK h _ _ (pr⁺ hw) (ext⁺ hY _)
  posOK {x′ = nl e} (inE n h) w Y hw hY = posOK h _ _ (proj₁ (rptOK e w Y hw hY n)) (proj₂ (rptOK e w Y hw hY n))

sem-in : ∀ {L L′ V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {y′ x′ : D L′ V′} →
         SemX²⁺ L L′ lV lV′ x y′ → In y′ x′ → SemX²⁺ L L′ lV lV′ x x′
sem-in {L} {L′} sx h {W} {W′} lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ hY T T′ tx =
  in⁺ (sx lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w (proj₁ (R.pos h w′ Y′)) (proj₁ ok) Y (proj₂ (R.pos h w′ Y′)) (proj₂ ok) T T′ tx)
      (R.runIn h w′ Y′ T′)
  where
  module R = RunIn {L = L} {lW = lW} lW′ ac′ q′ ll′ A₀′
  ok = R.posOK h w′ Y′ hw hY
```

## 4 第 $0$ 层对第 $0$ 层: 无条件

```agda
semX00⁺ : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D hz V} {x′ : D hz V′} → RelX⁺ hz hz lV lV′ x x′ → SemX²⁺ hz hz lV lV′ x x′
semX00⁺ n0⁺ = sem-n0
semX00⁺ n1⁺ = sem-n1
semX00⁺ (⨾⁺ hx hy) = sem-⨾ hx (semX00⁺ hx) (semX00⁺ hy)
semX00⁺ (nl⁺ hd) = sem-nl hd (λ n → semX00⁺ (hd n))
semX00⁺ (pr⁺ hx) = sem-pr (semX00⁺ hx)
semX00⁺ (nw⁺ hp hx) = sem-nw hp (semX00⁺ hx)
semX00⁺ (ni⁺ {r = ()} _ _)
semX00⁺ (κ⁺ {zz = ()} _)
semX00⁺ (in⁺ hx h) = sem-in (semX00⁺ hx) h
semX00⁺ (rk⁺ r r′ lW lW′ ac ac₁ ac′ ac₁′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′ T T′ () pre tx eL eR)
semX00⁺ (nκ⁺ {r = ()} _)
```

## 5 左层为 $0$: 以 `RkSound₀` 为条件

```agda
module Zero⁺ (L′ : H) (rkS : RkSound₀ L′) where
  semX0⁺ : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D hz V} {x′ : D L′ V′} → RelX⁺ hz L′ lV lV′ x x′ → SemX²⁺ hz L′ lV lV′ x x′
  semX0⁺ n0⁺ = sem-n0
  semX0⁺ n1⁺ = sem-n1
  semX0⁺ (⨾⁺ hx hy) = sem-⨾ hx (semX0⁺ hx) (semX0⁺ hy)
  semX0⁺ (nl⁺ hd) = sem-nl hd (λ n → semX0⁺ (hd n))
  semX0⁺ (pr⁺ hx) = sem-pr (semX0⁺ hx)
  semX0⁺ (nw⁺ hp hx) = sem-nw hp (semX0⁺ hx)
  semX0⁺ (ni⁺ {r = ()} _ _)
  semX0⁺ (κ⁺ {zz = ()} _)
  semX0⁺ (in⁺ hx h) = sem-in (semX0⁺ hx) h
  semX0⁺ (rk⁺ r r′ lW lW′ ac ac₁ ac′ ac₁′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′ T T′ R′ pre tx eL eR) =
    rkS r r′ lW lW′ ac ac₁ ac′ ac₁′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′ T T′ R′ pre tx eL eR
  semX0⁺ (nκ⁺ {r = ()} _)
```
