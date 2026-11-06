# 结构关系, 第十九轮 (二): `RelX⁺⁺` 的状态律, 第 $0$ 层的语义 `SemS`, 有限 $\Lambda$ 上的 `Act`

> 不读记号. 入口 [StrRel19](StrRel19.lagda.md). 接口 [StrRel19If](StrRel19If.lagda.md) §2–§4. 把 `StrRel16Sem` 与 `StrRel16Fin` 里用到的部分搬到新关系 `RelX⁺⁺` 与带 `ActS`、带条件的语义 `SemS` 上; 证明逐条同原文, 构造子换成 `⁺⁺`.
>
> 1. **(定理) `law⊕⁺⁺`, `ext⁺⁺`**: `J⁺⁺` 对 `⊕` 封闭; 右边状态向右延长时 `J⁺⁺` 保持.
> 2. **(定理) `domZ⊕`, `domZR`**: 时间条件 `DomZ` 在两边都向右延长 (`⊕`) 与只延长右边时保持 (它只看右边状态的差与第 $0$ 层读数, 都是左前缀加长). 抽象成 `OkMono`.
> 3. **(定理) `semS00`: 两边都是第 $0$ 层时, `RelX⁺⁺ hz hz ⇒ SemS hz hz … Ok`, 对一切满足 `OkMono` 的条件 `Ok`.** 第 $0$ 层没有 `ni⁺⁺`, `κ⁺⁺`, `rk⁺⁺`, `nκ⁺⁺`, `up` (右边是第 $0$ 层时, 节点种类 `StH _ _ hz` 与 `NZ hz` 是空的).
> 4. **(定理) 有限 $\Lambda$ (`FinΛ⁺⁺`)**: `ΩRX⁺⁺`, `stepOA⁺⁺`, `hawAct⁺⁺`, `hawsAct` (`Act` 满足 `HAWS`), `hY₁⁺⁺` (`J⁺⁺ Y₁ Y₁`), `domZY₁` (`DomZ` 在 $(Y_1,Y_1)$ 上成立).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
module OCF.Align.StrRel19Sem (Λ : H) (lΛ : LgH Λ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (hz; hs; hself; ss; D; D₀; n0; n1; _⨾_; nl; nw; AccY; Ωd)
open import OCF.Align.StrRel11Rk Λ lΛ using (_⊑∞_; s∞; u∞; tr∞)
open import OCF.Align.StrRel12Al using (AP; CP; cp-top; cp-tr)
open import OCF.Align.StrRel12Sem Λ lΛ using (Top)
open import OCF.Align.StrRel14J Λ lΛ using (NE; ne⊕; rgt0) renaming (here to lfH)
open import OCF.Align.StrRel15If Λ lΛ using (TX)
open import OCF.Align.StrRel15Fin using (Fin; fin⊲)
open import OCF.Align.StrRel16If Λ lΛ using (module P; In; here; inL; inR; inE)
open import OCF.Align.StrRel17If Λ lΛ using (Cond)
open import OCF.Align.StrRel19If Λ lΛ

open P using (Tg; tg; wm; tm; lm; tg↑; τ₀; St; Df; yc; d; z; cv; _⊕⟨_⟩_; Run; Rpt; Ig; Ig↾; LW; Act; Step; Y₀)
```

## 1 状态律, 时间条件的单调

```agda
law⊕⁺⁺ : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} → Top lW lW′ → ∀ (Y : St W) (Y′ : St W′) (Δ : Df W) (Δ′ : Df W′) →
         J⁺⁺ lW lW′ Y Y′ → OA⁺⁺ lW lW′ Δ Δ′ → J⁺⁺ lW lW′ (Y ⊕⟨ lW ⟩ Δ) (Y′ ⊕⟨ lW′ ⟩ Δ′)
law⊕⁺⁺ {lW = lW} {lW′} tp Y Y′ Δ Δ′ ((r , rz) , (ne , ne′)) O =
  ((λ T T′ tx → ⨾⁺⁺ (r T T′ tx) (O T T′ tx)) , ⨾⁺⁺ rz (O (τ₀ lW) (τ₀ lW′) (tp , s∞))) ,
  (ne⊕ {lW = lW} Y Δ ne , ne⊕ {lW = lW′} Y′ Δ′ ne′)

ext⁺⁺ : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} {Y : St W} {Y′ : St W′} → J⁺⁺ lW lW′ Y Y′ → ∀ (Δ′ : Df W′) → J⁺⁺ lW lW′ Y (Y′ ⊕⟨ lW′ ⟩ Δ′)
ext⁺⁺ {lW′ = lW′} {Y′ = Y′} ((r , rz) , (ne , ne′)) Δ′ = ((λ T T′ tx → pr⁺⁺ (r T T′ tx)) , pr⁺⁺ rz) , (ne , ne⊕ {lW = lW′} Y′ Δ′ ne′)

OkMono : Cond → Set
OkMono Ok =
  (∀ {W W′} {lW : Lg W} {lW′ : Lg W′} (Y : St W) (Y′ : St W′) (Δ : Df W) (Δ′ : Df W′) →
     Ok lW lW′ Y Y′ → Ok lW lW′ (Y ⊕⟨ lW ⟩ Δ) (Y′ ⊕⟨ lW′ ⟩ Δ′)) ×
  (∀ {W W′} {lW : Lg W} {lW′ : Lg W′} (Y : St W) (Y′ : St W′) (Δ′ : Df W′) →
     Ok lW lW′ Y Y′ → Ok lW lW′ Y (Y′ ⊕⟨ lW′ ⟩ Δ′))

domZR : ∀ {W₀} (lW₀ : Lg W₀) (Y₀ : St W₀) {W W′} {lW : Lg W} {lW′ : Lg W′} (Y : St W) (Y′ : St W′) (Δ′ : Df W′) →
        DomZ lW₀ Y₀ lW lW′ Y Y′ → DomZ lW₀ Y₀ lW lW′ Y (Y′ ⊕⟨ lW′ ⟩ Δ′)
domZR lW₀ Y₀ {lW′ = lW′} Y Y′ Δ′ ((r , rz) , (ne , ne′)) =
  ((λ T T′ tx → pr⁺⁺ (r T T′ tx)) , pr⁺⁺ rz) , (ne , ne⊕ {lW = lW′} Y′ Δ′ ne′)

domZmono : ∀ {W₀} (lW₀ : Lg W₀) (Y₀ : St W₀) → OkMono (DomZ lW₀ Y₀)
domZmono lW₀ Y₀ =
  (λ {_} {_} {lW} {lW′} Y Y′ Δ Δ′ h → domZR lW₀ Y₀ {lW = lW} {lW′} (Y ⊕⟨ lW ⟩ Δ) Y′ Δ′ h) ,
  (λ {_} {_} {lW} {lW′} Y Y′ Δ′ h → domZR lW₀ Y₀ {lW = lW} {lW′} Y Y′ Δ′ h)
```

## 2 第 $0$ 层的语义 (条件 `Ok` 单调)

```agda
module Sem00 (Ok : Cond) (okm : OkMono Ok) where
  ok⊕ = proj₁ okm
  okR = proj₂ okm

  module Six {L L′ : H} where
    sem-n0 : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x′ : D L′ V′} → SemS L L′ lV lV′ Ok n0 x′
    sem-n0 lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r ok T T′ ta = n0⁺⁺

    sem-n1 : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} → SemS L L′ lV lV′ Ok n1 n1
    sem-n1 lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r ok = proj₁ ha C.self C.self lW lW′ (cp-top hq) w w′ hw Y Y′ r

    sem-⨾ : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x y : D L V} {x′ y′ : D L′ V′} →
            RelX⁺⁺ L L′ lV lV′ x x′ → SemS L L′ lV lV′ Ok x x′ → SemS L L′ lV lV′ Ok y y′ → SemS L L′ lV lV′ Ok (x ⨾ y) (x′ ⨾ y′)
    sem-⨾ {x = x} {x′ = x′} hx sx sy lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r ok T T′ ta =
      ⨾⁺⁺ (Ox T T′ ta)
         (sy lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha (w ⨾ nw q x) (w′ ⨾ nw q′ x′) (⨾⁺⁺ hw (nw⁺⁺ (proj₁ hq) hx))
             _ _ (law⊕⁺⁺ (cp-top hq) Y Y′ Δ Δ′ r Ox) (ok⊕ Y Y′ Δ Δ′ ok) T T′ ta)
      where
      Δ = Run ac x q lW ll A₀ w Y
      Δ′ = Run ac′ x′ q′ lW′ ll′ A₀′ w′ Y′
      Ox = sx lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r ok

    sem-nw : ∀ {V₀ V₀′ V V′} {lV₀ : Lg V₀} {lV₀′ : Lg V₀′} {lV : Lg V} {lV′ : Lg V′} {p : V₀ ⊲ V} {p′ : V₀′ ⊲ V′}
               {x : D L V₀} {x′ : D L′ V₀′} →
             AP lV₀ lV₀′ p lV p′ lV′ → SemS L L′ lV₀ lV₀′ Ok x x′ → SemS L L′ lV lV′ Ok (nw p x) (nw p′ x′)
    sem-nw hp sx lW lW′ ac ac′ ll ll′ q q′ hq = sx lW lW′ ac ac′ ll ll′ (⊲-tr _ q) (⊲-tr _ q′) (cp-tr hp hq)

    sem-pr : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {x′ y′ : D L′ V′} →
             SemS L L′ lV lV′ Ok x x′ → SemS L L′ lV lV′ Ok x (x′ ⨾ y′)
    sem-pr sx lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r ok T T′ ta =
      pr⁺⁺ (sx lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r ok T T′ ta)

    module NL {V V′} {lV : Lg V} {lV′ : Lg V′} {d₁ : ℕ → D L V} {d₁′ : ℕ → D L′ V′}
              (hd : ∀ n → RelX⁺⁺ L L′ lV lV′ (d₁ n) (d₁′ n)) (sd : ∀ n → SemS L L′ lV lV′ Ok (d₁ n) (d₁′ n))
              {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac′ : AccY L′) (ll : LW L W) (ll′ : LW L′ W′)
              (q : V ⊲ W) (q′ : V′ ⊲ W′) (hq : CP lV lV′ q lW q′ lW′)
              (A₀ : Ig L W) (A₀′ : Ig L′ W′) (ha : HAWS L L′ lW lW′ A₀ A₀′)
              (w : D L W) (w′ : D L′ W′) (hw : RelX⁺⁺ L L′ lW lW′ w w′) (Y : St W) (Y′ : St W′) (r : J⁺⁺ lW lW′ Y Y′)
              (ok : Ok lW lW′ Y Y′) where
      Pn : ℕ → D L W × St W
      Pn = Rpt ac d₁ q lW ll A₀ w Y
      Pn′ : ℕ → D L′ W′ × St W′
      Pn′ = Rpt ac′ d₁′ q′ lW′ ll′ A₀′ w′ Y′

      St′ : ℕ → Set
      St′ n = RelX⁺⁺ L L′ lW lW′ (proj₁ (Pn n)) (proj₁ (Pn′ n)) × (J⁺⁺ lW lW′ (proj₂ (Pn n)) (proj₂ (Pn′ n)) ×
              Ok lW lW′ (proj₂ (Pn n)) (proj₂ (Pn′ n)))

      out : ∀ n → St′ n → OA⁺⁺ lW lW′ (Run ac (d₁ n) q lW ll A₀ (proj₁ (Pn n)) (proj₂ (Pn n)))
                                       (Run ac′ (d₁′ n) q′ lW′ ll′ A₀′ (proj₁ (Pn′ n)) (proj₂ (Pn′ n)))
      out n (h , s , o) = sd n lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha _ _ h _ _ s o

      go : ∀ n → St′ n
      go zero = hw , r , ok
      go (suc n) = ⨾⁺⁺ (proj₁ (go n)) (nw⁺⁺ (proj₁ hq) (hd n)) ,
                   (law⊕⁺⁺ (cp-top hq) (proj₂ (Pn n)) (proj₂ (Pn′ n)) _ _ (proj₁ (proj₂ (go n))) (out n (go n)) ,
                    ok⊕ (proj₂ (Pn n)) (proj₂ (Pn′ n)) _ _ (proj₂ (proj₂ (go n))))

    sem-nl : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {d₁ : ℕ → D L V} {d₁′ : ℕ → D L′ V′} →
             (∀ n → RelX⁺⁺ L L′ lV lV′ (d₁ n) (d₁′ n)) → (∀ n → SemS L L′ lV lV′ Ok (d₁ n) (d₁′ n)) → SemS L L′ lV lV′ Ok (nl d₁) (nl d₁′)
    sem-nl hd sd lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r ok T T′ ta =
      nl⁺⁺ (λ n → N.out n (N.go n) T T′ ta)
      where module N = NL hd sd lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r ok

  open Six public

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

    Good : D L W → St W → D L′ W′ → St W′ → Set
    Good w₀ Y₀ w Y = RelX⁺⁺ L L′ lW lW′ w₀ w × (J⁺⁺ lW lW′ Y₀ Y × Ok lW lW′ Y₀ Y)

    rptOK : ∀ (e : ℕ → D L′ V′) {w₀ : D L W} {Y₀ : St W} w Y → Good w₀ Y₀ w Y → ∀ n →
            Good w₀ Y₀ (proj₁ (Rpt ac′ e q′ lW′ ll′ A₀′ w Y n)) (proj₂ (Rpt ac′ e q′ lW′ ll′ A₀′ w Y n))
    rptOK e w Y g zero = g
    rptOK e {Y₀ = Y₀} w Y g (suc n) with rptOK e w Y g n
    ... | (hw , hY , o) = pr⁺⁺ hw , (ext⁺⁺ hY _ , okR Y₀ _ _ o)

    posOK : ∀ {y′ x′ : D L′ V′} (h : In y′ x′) {w₀ : D L W} {Y₀ : St W} w Y → Good w₀ Y₀ w Y →
            Good w₀ Y₀ (proj₁ (pos h w Y)) (proj₂ (pos h w Y))
    posOK here w Y g = g
    posOK (inL h) w Y g = posOK h w Y g
    posOK {x′ = a ⨾ b} (inR h) {Y₀ = Y₀} w Y (hw , hY , o) = posOK h _ _ (pr⁺⁺ hw , (ext⁺⁺ hY _ , okR Y₀ _ _ o))
    posOK {x′ = nl e} (inE n h) w Y g = posOK h _ _ (rptOK e w Y g n)

  sem-in : ∀ {L L′ V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {y′ x′ : D L′ V′} →
           SemS L L′ lV lV′ Ok x y′ → In y′ x′ → SemS L L′ lV lV′ Ok x x′
  sem-in {L} {L′} sx h {W} {W′} lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ hY ok T T′ tx =
    in⁺⁺ (sx lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w (proj₁ (R.pos h w′ Y′)) (proj₁ g) Y (proj₂ (R.pos h w′ Y′))
            (proj₁ (proj₂ g)) (proj₂ (proj₂ g)) T T′ tx)
        (R.runIn h w′ Y′ T′)
    where
    module R = RunIn {L = L} {lW = lW} lW′ ac′ q′ ll′ A₀′
    g = R.posOK h w′ Y′ (hw , (hY , ok))

  semS00 : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D hz V} {x′ : D hz V′} → RelX⁺⁺ hz hz lV lV′ x x′ → SemS hz hz lV lV′ Ok x x′
  semS00 n0⁺⁺ = sem-n0
  semS00 n1⁺⁺ = sem-n1
  semS00 (⨾⁺⁺ hx hy) = sem-⨾ hx (semS00 hx) (semS00 hy)
  semS00 (nl⁺⁺ hd) = sem-nl hd (λ n → semS00 (hd n))
  semS00 (pr⁺⁺ hx) = sem-pr (semS00 hx)
  semS00 (nw⁺⁺ hp hx) = sem-nw hp (semS00 hx)
  semS00 (ni⁺⁺ {r = ()} _ _)
  semS00 (κ⁺⁺ {zz = ()} _)
  semS00 (in⁺⁺ hx h) = sem-in (semS00 hx) h
  semS00 (rk⁺⁺ r r′ lW lW′ ac ac₁ ac′ ac₁′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′ T T′ () pre tx eL eR)
  semS00 (nκ⁺⁺ {r = ()} _)
  semS00 (up r lW ac ac₁ q₀ ll A₀ w Y T T′ () s eL eR h)
```

## 3 有限 $\Lambda$: `Act`, $Y_1$, `DomZ` 在 $(Y_1,Y_1)$ 上

```agda
module FinΛ⁺⁺ (fΛ : Fin Λ) where
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

  hawAct⁺⁺ : ∀ L L′ {W W′} {lW : Lg W} {lW′ : Lg W′} → HAW⁺⁺ L L′ lW lW′ Act Act
  hawAct⁺⁺ L L′ p p′ l l′ cp w w′ hw Y Y′ hY = stepOA⁺⁺ hY

  hawsAct : ∀ L L′ {W W′} {lW : Lg W} {lW′ : Lg W′} → HAWS L L′ lW lW′ Act Act
  hawsAct L L′ = hawAct⁺⁺ L L′ , (sAct , sAct)

  Y₁ : ∀ {W} → Lg W → St W
  Y₁ lW = Y₀ ⊕⟨ lW ⟩ Step Y₀

  hY₁⁺⁺ : ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) → J⁺⁺ lW lW′ (Y₁ lW) (Y₁ lW′)
  hY₁⁺⁺ lW lW′ =
    ((λ T T′ tx → ⨾⁺⁺ n0⁺⁺ (nl⁺⁺ (λ _ → ⨾⁺⁺ (ΩRX⁺⁺ (fin⊲ (tm T) fΛ) (fin⊲ (tm T′) fΛ) (proj₂ tx)) n0⁺⁺))) ,
     ⨾⁺⁺ n0⁺⁺ (nl⁺⁺ (λ _ → ⨾⁺⁺ n1⁺⁺ n0⁺⁺))) ,
    ((λ T → n0 , rgt0 lfH) , (λ T → n0 , rgt0 lfH))

  -- 累计 n0 ⨾ ω⋅(1 ⨾ 0) 与第 0 层的读数 n0 ⨾ ω⋅(Ωd 0 ⨾ 0) 字面相同
  domZY₁ : ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) → DomZ lW (Y₁ lW) lW lW′ (Y₁ lW) (Y₁ lW′)
  domZY₁ lW lW′ = (proj₁ (proj₁ (hY₁⁺⁺ lW lW′)) , ⨾⁺⁺ n0⁺⁺ (nl⁺⁺ (λ _ → ⨾⁺⁺ n1⁺⁺ n0⁺⁺))) , proj₂ (hY₁⁺⁺ lW lW′)
```
