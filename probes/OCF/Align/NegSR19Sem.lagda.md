# 第十九轮的否定 (工具): 第 $0$ 层对第 $0$ 层, `RelX⁺⁺ ⇒ SemS … Any`

> 不读记号. 入口 [NegSR19](NegSR19.lagda.md). 对着接口 [StrRel19If](StrRel19If.lagda.md) (定稿 2026-11-05 16:01) §3–§4 的 `J⁺⁺`, `HAWS`, `SemS` 写. 一切 $\Lambda$. 把 `StrRel16Sem` 的 §1–§4 (`law⊕⁺`, 六条规则, `sem-in`, `semX00⁺`) 逐字搬到 `RelX⁺⁺` 与 `SemS` 上, 条件取恒真的 `Any`.
>
> **(定理) `semS00`**: 两边都是第 $0$ 层时, `RelX⁺⁺ hz hz ⇒ SemS hz hz … Any`. 这时 `rk⁺⁺` 与 `up` 都不出现 (右边是第 $0$ 层的节点, `StH _ _ hz` 是空的), `ni⁺⁺`, `κ⁺⁺`, `nκ⁺⁺` 也不出现 (左边是第 $0$ 层). 再折叠的动作前提 `HAWS` 只用到它的 `HAW⁺⁺` 一半.
>
> **用处.** `NegSR19Up` 要 `up` 的前提 `SemS x (上升输出)`, $x$ 是上升输出的一个第 $0$ 层的分量: 由本文的 `sem-in` 与 `semS00` 得到.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
module OCF.Align.NegSR19Sem (Λ : H) (lΛ : LgH Λ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (hz; D; n0; n1; _⨾_; nl; nw; AccY)
open import OCF.Align.StrRel11Rk Λ lΛ using (s∞)
open import OCF.Align.StrRel12Al using (AP; CP; cp-top; cp-tr)
open import OCF.Align.StrRel12Sem Λ lΛ using (Top)
open import OCF.Align.StrRel14J Λ lΛ using (ne⊕)
open import OCF.Align.StrRel16If Λ lΛ using (module P; In; here; inL; inR; inE)
open import OCF.Align.StrRel17If Λ lΛ using (Any)
open import OCF.Align.StrRel19If Λ lΛ

open P using (Tg; τ₀; St; Df; yc; d; z; _⊕⟨_⟩_; Run; Rpt; Ig; LW)
```

## 1 `⊕` 的律, 右边延长

```agda
law⊕⁺⁺ : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} → Top lW lW′ → ∀ (Y : St W) (Y′ : St W′) (Δ : Df W) (Δ′ : Df W′) →
         J⁺⁺ lW lW′ Y Y′ → OA⁺⁺ lW lW′ Δ Δ′ → J⁺⁺ lW lW′ (Y ⊕⟨ lW ⟩ Δ) (Y′ ⊕⟨ lW′ ⟩ Δ′)
law⊕⁺⁺ {lW = lW} {lW′} tp Y Y′ Δ Δ′ ((r , rz) , (ne , ne′)) O =
  ((λ T T′ tx → ⨾⁺⁺ (r T T′ tx) (O T T′ tx)) , ⨾⁺⁺ rz (O (τ₀ lW) (τ₀ lW′) (tp , s∞))) ,
  (ne⊕ {lW = lW} Y Δ ne , ne⊕ {lW = lW′} Y′ Δ′ ne′)

ext⁺⁺ : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} {Y : St W} {Y′ : St W′} → J⁺⁺ lW lW′ Y Y′ → ∀ (Δ′ : Df W′) → J⁺⁺ lW lW′ Y (Y′ ⊕⟨ lW′ ⟩ Δ′)
ext⁺⁺ {lW′ = lW′} {Y′ = Y′} ((r , rz) , (ne , ne′)) Δ′ = ((λ T T′ tx → pr⁺⁺ (r T T′ tx)) , pr⁺⁺ rz) , (ne , ne⊕ {lW = lW′} Y′ Δ′ ne′)
```

## 2 六条规则

```agda
module Six {L L′ : H} where
  sem-n0 : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x′ : D L′ V′} → SemS L L′ lV lV′ Any n0 x′
  sem-n0 lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r ok T T′ ta = n0⁺⁺

  sem-n1 : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} → SemS L L′ lV lV′ Any n1 n1
  sem-n1 lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r ok = proj₁ ha C.self C.self lW lW′ (cp-top hq) w w′ hw Y Y′ r

  sem-⨾ : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x y : D L V} {x′ y′ : D L′ V′} →
          RelX⁺⁺ L L′ lV lV′ x x′ → SemS L L′ lV lV′ Any x x′ → SemS L L′ lV lV′ Any y y′ → SemS L L′ lV lV′ Any (x ⨾ y) (x′ ⨾ y′)
  sem-⨾ {x = x} {x′ = x′} hx sx sy lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r ok T T′ ta =
    ⨾⁺⁺ (Ox T T′ ta)
       (sy lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha (w ⨾ nw q x) (w′ ⨾ nw q′ x′) (⨾⁺⁺ hw (nw⁺⁺ (proj₁ hq) hx))
           _ _ (law⊕⁺⁺ (cp-top hq) Y Y′ Δ Δ′ r Ox) tt T T′ ta)
    where
    Δ = Run ac x q lW ll A₀ w Y
    Δ′ = Run ac′ x′ q′ lW′ ll′ A₀′ w′ Y′
    Ox = sx lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r ok

  sem-nw : ∀ {V₀ V₀′ V V′} {lV₀ : Lg V₀} {lV₀′ : Lg V₀′} {lV : Lg V} {lV′ : Lg V′} {p : V₀ ⊲ V} {p′ : V₀′ ⊲ V′}
             {x : D L V₀} {x′ : D L′ V₀′} →
           AP lV₀ lV₀′ p lV p′ lV′ → SemS L L′ lV₀ lV₀′ Any x x′ → SemS L L′ lV lV′ Any (nw p x) (nw p′ x′)
  sem-nw hp sx lW lW′ ac ac′ ll ll′ q q′ hq = sx lW lW′ ac ac′ ll ll′ (⊲-tr _ q) (⊲-tr _ q′) (cp-tr hp hq)

  sem-pr : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {x′ y′ : D L′ V′} →
           SemS L L′ lV lV′ Any x x′ → SemS L L′ lV lV′ Any x (x′ ⨾ y′)
  sem-pr sx lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r ok T T′ ta =
    pr⁺⁺ (sx lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r ok T T′ ta)

  module NL {V V′} {lV : Lg V} {lV′ : Lg V′} {d₁ : ℕ → D L V} {d₁′ : ℕ → D L′ V′}
            (hd : ∀ n → RelX⁺⁺ L L′ lV lV′ (d₁ n) (d₁′ n)) (sd : ∀ n → SemS L L′ lV lV′ Any (d₁ n) (d₁′ n))
            {W W′} (lW : Lg W) (lW′ : Lg W′) (ac : AccY L) (ac′ : AccY L′) (ll : LW L W) (ll′ : LW L′ W′)
            (q : V ⊲ W) (q′ : V′ ⊲ W′) (hq : CP lV lV′ q lW q′ lW′)
            (A₀ : Ig L W) (A₀′ : Ig L′ W′) (ha : HAWS L L′ lW lW′ A₀ A₀′)
            (w : D L W) (w′ : D L′ W′) (hw : RelX⁺⁺ L L′ lW lW′ w w′) (Y : St W) (Y′ : St W′) (r : J⁺⁺ lW lW′ Y Y′) where
    Pn : ℕ → D L W × St W
    Pn = Rpt ac d₁ q lW ll A₀ w Y
    Pn′ : ℕ → D L′ W′ × St W′
    Pn′ = Rpt ac′ d₁′ q′ lW′ ll′ A₀′ w′ Y′

    St′ : ℕ → Set
    St′ n = RelX⁺⁺ L L′ lW lW′ (proj₁ (Pn n)) (proj₁ (Pn′ n)) × J⁺⁺ lW lW′ (proj₂ (Pn n)) (proj₂ (Pn′ n))

    out : ∀ n → St′ n → OA⁺⁺ lW lW′ (Run ac (d₁ n) q lW ll A₀ (proj₁ (Pn n)) (proj₂ (Pn n)))
                                    (Run ac′ (d₁′ n) q′ lW′ ll′ A₀′ (proj₁ (Pn′ n)) (proj₂ (Pn′ n)))
    out n (h , s) = sd n lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha _ _ h _ _ s tt

    go : ∀ n → St′ n
    go zero = hw , r
    go (suc n) = ⨾⁺⁺ (proj₁ (go n)) (nw⁺⁺ (proj₁ hq) (hd n)) ,
                 law⊕⁺⁺ (cp-top hq) (proj₂ (Pn n)) (proj₂ (Pn′ n)) _ _ (proj₂ (go n)) (out n (go n))

  sem-nl : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {d₁ : ℕ → D L V} {d₁′ : ℕ → D L′ V′} →
           (∀ n → RelX⁺⁺ L L′ lV lV′ (d₁ n) (d₁′ n)) → (∀ n → SemS L L′ lV lV′ Any (d₁ n) (d₁′ n)) → SemS L L′ lV lV′ Any (nl d₁) (nl d₁′)
  sem-nl hd sd lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r ok T T′ ta =
    nl⁺⁺ (λ n → N.out n (N.go n) T T′ ta)
    where module N = NL hd sd lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r

open Six public
```

## 3 `in⁺⁺`

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

  rptOK : ∀ (e : ℕ → D L′ V′) {w₀ : D L W} {Y₀ : St W} w Y → RelX⁺⁺ L L′ lW lW′ w₀ w → J⁺⁺ lW lW′ Y₀ Y → ∀ n →
          RelX⁺⁺ L L′ lW lW′ w₀ (proj₁ (Rpt ac′ e q′ lW′ ll′ A₀′ w Y n)) × J⁺⁺ lW lW′ Y₀ (proj₂ (Rpt ac′ e q′ lW′ ll′ A₀′ w Y n))
  rptOK e w Y hw hY zero = hw , hY
  rptOK e w Y hw hY (suc n) = pr⁺⁺ (proj₁ (rptOK e w Y hw hY n)) , ext⁺⁺ (proj₂ (rptOK e w Y hw hY n)) _

  posOK : ∀ {y′ x′ : D L′ V′} (h : In y′ x′) {w₀ : D L W} {Y₀ : St W} w Y → RelX⁺⁺ L L′ lW lW′ w₀ w → J⁺⁺ lW lW′ Y₀ Y →
          RelX⁺⁺ L L′ lW lW′ w₀ (proj₁ (pos h w Y)) × J⁺⁺ lW lW′ Y₀ (proj₂ (pos h w Y))
  posOK here w Y hw hY = hw , hY
  posOK (inL h) w Y hw hY = posOK h w Y hw hY
  posOK {x′ = a ⨾ b} (inR h) w Y hw hY = posOK h _ _ (pr⁺⁺ hw) (ext⁺⁺ hY _)
  posOK {x′ = nl e} (inE n h) w Y hw hY = posOK h _ _ (proj₁ (rptOK e w Y hw hY n)) (proj₂ (rptOK e w Y hw hY n))

sem-in : ∀ {L L′ V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {y′ x′ : D L′ V′} →
         SemS L L′ lV lV′ Any x y′ → In y′ x′ → SemS L L′ lV lV′ Any x x′
sem-in {L} {L′} sx h {W} {W′} lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ hY ok T T′ tx =
  in⁺⁺ (sx lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w (proj₁ (R.pos h w′ Y′)) (proj₁ okp) Y (proj₂ (R.pos h w′ Y′)) (proj₂ okp) tt T T′ tx)
       (R.runIn h w′ Y′ T′)
  where
  module R = RunIn {L = L} {lW = lW} lW′ ac′ q′ ll′ A₀′
  okp = R.posOK h w′ Y′ hw hY
```

## 4 第 $0$ 层对第 $0$ 层

```agda
semS00 : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D hz V} {x′ : D hz V′} → RelX⁺⁺ hz hz lV lV′ x x′ → SemS hz hz lV lV′ Any x x′
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
semS00 (up r lW ac ac₁ q₀ ll A₀ w Y T T′ () sA eL eR h)
```
