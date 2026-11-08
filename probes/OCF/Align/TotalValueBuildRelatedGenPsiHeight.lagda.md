# 原跨高度 Ψ 的获准生成保持

所有闭包更新使用原世界、cap 与 upd。较低反馈坐标仍由原 chainᵠ
产生，不加入未来域假设，也不改原程序。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildRelatedGenPsiHeight (𝕊 : HtB) where
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl; subst; sym)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level
open import OCF.Free.Tree using (Fl; dupr2)
open import OCF.Free.Floor using (Ev; _⊔_; fk; ∼ᶠ-refl; bound; Bd; evF; iF)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdRel 𝕊
open import OCF.Align.TotalValueBuildRelatedGenIf 𝕊
open import OCF.Align.TotalValueBuildRelatedGenUp 𝕊 using (C)
open import OCF.Align.TotalValueBuildRelatedGenFloor 𝕊 using (omega-gen)
open import OCF.Align.TotalValueBuildRelatedGenTransport 𝕊 using (transport-back)
open import OCF.Align.TotalValueBuildRelatedGenOps 𝕊 using (repeat-core; chain-gen)
open import OCF.Align.TotalValueBuildRelatedGenPsi 𝕊 using (psi-gen; self-feed; cl-head; cl-branch; unwk-left; unwk-right)

feed-down : ∀ {m a φ χ n k} {r : n <ᴸ m}
  {fe : ∀ {L} → Ev L φ → Ev L Fl} {ac : ∀ {L} → Ev L (χ n) → k <ᴵ L}
  {h : ∀ ξ ζ → Vs m r k ξ ζ → Q m a (ξ ⊔ φ) (lo n ζ ∪ χ)} →
  Gen m a (qΩ↓ r fe ac h) → ∀ ξ ζ (z : Q n k ξ ζ) → Gen n k z →
  Gen m a (h ξ ζ (intoV r z))
feed-down {m} {r = r} (rh , gh) ξ ζ z gz = self-feed rh ξ ζ z (proj₁ gz) ,
  gh ξ ζ (intoV r z)
    (subst (GHeight m r) (sym (out-intoV r z)) (height-in r gz))

feed-top : ∀ {m a φ χ k} {r : k <ᴵ a}
  {fe : ∀ {L} → Ev L φ → Ev L Fl}
  {h : ∀ ξ ζ → Us m k (<→◃ r) ξ ζ → Q m a (ξ ⊔ φ) (lo m ζ ∪ χ)} →
  Gen m a (qΩ fe r h) → ∀ ξ ζ (z : Q m k ξ ζ) → Gen m k z →
  Gen m a (h ξ ζ (intoU (<→◃ r) z))
feed-top {m} {r = r} (rΩ ek sf sc rh , gh) ξ ζ z gz =
  rh ξ ξ ζ ζ (∼ᶠ-refl ξ) (λ i p → ∼ᶠ-refl _) z z (intoRq (<→◃ r) (proj₁ gz)) ,
  gh ξ ζ (intoU (<→◃ r) z)
    (subst (Low m (GHeight m) _ (<→◃ r)) (sym (out-intoU (<→◃ r) z)) (low-in (<→◃ r) gz))

mutual
  height-gen : ∀ {H m a φ χ t w} (qH : H <ᴸ m) (ok : Ok w) (e : Eh H m w χ)
    (p : t <ᴵ w H) {x : Q m a φ χ} → Gen m a x → Gen H t (Ψ qH ok e p x)
  height-gen qH ok e p {x} (rx , gx) =
    R-Ψ qH ok e p ok e p (≅ᴵ-refl _) rx , height-core qH ok e p x rx gx

  height-core : ∀ {H m a φ χ t w} (qH : H <ᴸ m) (ok : Ok w) (e : Eh H m w χ)
    (p : t <ᴵ w H) (x : Q m a φ χ) → Rq m a a x x → C m a x → C H t (Ψ qH ok e p x)
  height-core {H} {t = t} qH ok e p q0 rx gx = proj₂ (omega-gen H t)
  height-core qH ok e p (qs x) (rs sf sc rx) gx = λ n → repeat-core (height-core qH ok e p x rx gx) n
  height-core qH ok e p (ql f) (rl rf) gf = λ i → height-core qH ok e p (f i) (rf i) (gf i)
  height-core qH ok e p (qi ac f) (ri ej rf) gf = λ x sx → height-core qH ok e p (f x) (rf x x sx) (gf x sx)
  height-core qH ok e p (qŝ c t g) (rŝ ec rt rg) (gt , gg) =
    height-core qH ok e p t rt gt , (λ η d → height-core qH ok e p (g η d) (rg η d η d (≅ᴵ-refl η)) (gg η d))
  height-core qH ok e p (qĉ c t g o h) (rĉ ec st sg ro rh) (st′ , sg′ , go , gh) =
    st′ , sg′ , height-core qH ok e p o ro go , (λ η d → height-core qH ok e p (h η d) (rh η d η d (≅ᴵ-refl η)) (gh η d))
  height-core qH ok e p (qclo t g) (rclo sf rt rg) (gt , gg) =
    height-core qH ok e p t rt gt , (λ η → height-core qH ok e p (g η) (rg η η (≅ᴵ-refl η)) (gg η))
  height-core qH ok e p (qwk le lc x) rx gx =
    height-core qH ok (λ i h r → lc i r (e i h r)) p x (unwk-right (unwk-left rx)) gx
  height-core qH ok e p (omk r z x) (rob ek rz′ rx) (gz , gx , rel) = height-core qH ok e p x rx gx
  height-core {H} {χ = χ} {w = w} qH ok e p (qcl {n = n} q ψ s x g) rx (gx , gg) with tri n H
  ... | tlt l = height-core qH ok e p x (cl-head rx) gx ,
    (λ η → height-core qH ok
      (λ i h r → subst (Ev _) (sym (upd-gt χ _ (Hi-gt l h))) (e i h r)) p
      (g η) (cl-branch rx η η (≅ᴵ-refl η)) (gg η))
  ... | teq refl = height-core qH ok e p x (cl-head rx) gx ,
    (λ η d → height-core qH
      (upd-ok n w ok (tt , λ q′ → lim 0 (proj₂ (evF B) q′)))
      (λ i h r → upd-ev n i w χ (evη ψ B η d) (e i h r))
      (subst (_ <ᴵ_) (sym (upd-self w n _)) (lim 0 (iF B)))
      (g η) (cl-branch rx η η (≅ᴵ-refl η)) (gg η))
    where B = bound (ψ ⊔ fk zero) (s (e n (inj₁ refl) q)) p
  ... | tgt l = height-core qH ok e p x (cl-head rx) gx ,
    (λ η d → height-core qH
      (upd-ok n w ok (tt , λ q′ → lim 0 (proj₂ (evF B) q′)))
      (λ i h r → upd-ev n i w χ (evη ψ B η d) (e i h r))
      (subst (_ <ᴵ_) (sym (upd-lt w _ l)) p)
      (g η) (cl-branch rx η η (≅ᴵ-refl η)) (gg η))
    where B = bound (ψ ⊔ fk zero) (s (e n (inj₂ l) q)) (zr ok n)
  height-core {H} {m} {φ = φ} {χ = χ} qH ok e p (qΩ↓ {n = n} {k = k} q fe ac h) rx gh with tri n H
  ... | tlt l = λ ξ ζ z gz →
    let fb = feed-down (rx , gh) ξ ζ (outV l z) (height-out l gz)
    in height-core qH ok (e-lo ζ (inj₂ l) e) p (h ξ ζ (intoV q (outV l z))) (proj₁ fb) (proj₂ fb)
  ... | teq refl with <ᴵ-dec (ac (e n (inj₁ refl) q)) p
  ...   | injᵃ (via d s) = λ ξ ζ z gz →
    let fb = feed-down (rx , gh) ξ ζ (tr⁻Q d (outU (<→◃ s) z)) (transport-back d (low-out (<→◃ s) gz))
    in height-core qH ok (e-lo ζ (inj₁ refl) e) p (h ξ ζ (intoV q (tr⁻Q d (outU (<→◃ s) z)))) (proj₁ fb) (proj₂ fb)
  ...   | injᵇ ee = λ i →
    let
      run : (z : Q n k (Fl ⊔ φ) (Z* χ)) → Gen n k z →
        Gen n k (qwk dupr2 (⇑ (cv* n)) (Ψ q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) (h (Fl ⊔ φ) (Z* χ) (intoV q z))))
      run z gz =
        let fb = feed-down (rx , gh) (Fl ⊔ φ) (Z* χ) z gz
            out = height-gen q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) fb
        in rwk (proj₁ out) , proj₂ out
      z = chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* n)) (Ψ q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) (h (Fl ⊔ φ) (Z* χ) (intoV q z)))) i
      gz = chain-gen proj₁ fc* _ run i
      fb = feed-down (rx , gh) (Fl ⊔ φ) (Z* χ) z gz
    in height-core qH ok (e⁺ H ok e) p (h (Fl ⊔ φ) (Z* χ) (intoV q z)) (proj₁ fb) (proj₂ fb)
  ...   | injᶜ ee = λ i →
    let
      run : (z : Q n k (Fl ⊔ φ) (Z* χ)) → Gen n k z →
        Gen n k (qwk dupr2 (⇑ (cv* n)) (Ψ q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) (h (Fl ⊔ φ) (Z* χ) (intoV q z))))
      run z gz =
        let fb = feed-down (rx , gh) (Fl ⊔ φ) (Z* χ) z gz
            out = height-gen q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) fb
        in rwk (proj₁ out) , proj₂ out
      z = chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* n)) (Ψ q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) (h (Fl ⊔ φ) (Z* χ) (intoV q z)))) i
      gz = chain-gen proj₁ fc* _ run i
      fb = feed-down (rx , gh) (Fl ⊔ φ) (Z* χ) z gz
    in height-core qH ok (e⁺ H ok e) p (h (Fl ⊔ φ) (Z* χ) (intoV q z)) (proj₁ fb) (proj₂ fb)
  height-core {H} {m} {φ = φ} {χ = χ} qH ok e p (qΩ↓ {n = n} {k = k} q fe ac h) rx gh | tgt l = λ i →
    let
      run : (z : Q n k (Fl ⊔ φ) (Z* χ)) → Gen n k z →
        Gen n k (qwk dupr2 (⇑ (cv* n)) (Ψ q ok (e⁺ n ok (e↑ l e)) (ac (e↑ l e n (inj₁ refl) q)) (h (Fl ⊔ φ) (Z* χ) (intoV q z))))
      run z gz =
        let fb = feed-down (rx , gh) (Fl ⊔ φ) (Z* χ) z gz
            out = height-gen q ok (e⁺ n ok (e↑ l e)) (ac (e↑ l e n (inj₁ refl) q)) fb
        in rwk (proj₁ out) , proj₂ out
      z = chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* n)) (Ψ q ok (e⁺ n ok (e↑ l e)) (ac (e↑ l e n (inj₁ refl) q)) (h (Fl ⊔ φ) (Z* χ) (intoV q z)))) i
      gz = chain-gen proj₁ fc* _ run i
      fb = feed-down (rx , gh) (Fl ⊔ φ) (Z* χ) z gz
    in height-core qH ok (e⁺ n ok e) p (h (Fl ⊔ φ) (Z* χ) (intoV q z)) (proj₁ fb) (proj₂ fb)
  height-core {H} {m} {φ = φ} {χ = χ} qH ok e p (qΩ fe r h) rx gh = λ i →
    let
      run : (z : Q m _ (Fl ⊔ φ) (Z* χ)) → Gen m _ z →
        Gen m _ (qwk dupr2 (⇑ (cv* m)) (ψᵠ r (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z))))
      run z gz =
        let out = psi-gen r (feed-top (rx , gh) (Fl ⊔ φ) (Z* χ) z gz)
        in rwk (proj₁ out) , proj₂ out
      z = chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* m)) (ψᵠ r (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z)))) i
      gz = chain-gen proj₁ fc* _ run i
      fb = feed-top (rx , gh) (Fl ⊔ φ) (Z* χ) z gz
    in height-core qH ok (e⁺ m ok e) p (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z)) (proj₁ fb) (proj₂ fb)
```
