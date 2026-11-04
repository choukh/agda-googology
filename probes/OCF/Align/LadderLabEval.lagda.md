> **机械改写, 验收用.** 由 `ScafLadderQEval` 经 `Survey/scripts/ladderlab/mk_class.py` 生成: 对高度结构 `HtS` 抽象, 记号前缀换成 `PxS` 的 `P`; 见 [LadderLab](LadderLab.lagda.md). 下面的文字来自原文件.

# 阶梯 (十二): 塔上的求值与标签

> 结论写在 [ScafLadder](ScafLadder.lagda.md). 与 [ScafLadderEval](ScafLadderEval.lagda.md) 同形, 对 $m$ 一致. `labelᵠ` 的前提只有 `NF₁ (ψ₀ u)`; `Ωᵉ` 的标准形是记号侧的每阶段输入, 见 [ScafLadderQTop](ScafLadderQTop.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase
open import OCF.Align.LadderLabBase
module OCF.Align.LadderLabEval (𝕊 : HtS) (𝕏 : PxS 𝕊) where

open PxS 𝕏
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.Level
open import OCF.Align.LadderLabZPrefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; NF₁-fsn; NF₁-pred)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.LadderLabZDecouple using (Idx; lvI; Lab0[])
open import OCF.Align.LadderLabZDecoupleBase using (ΩΩ)
open import OCF.Align.LadderLabZStage2Label using (one⁰)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.LadderLabZOmegaExpBase using (OccΣ; cofΣ; predΣ; πw; repW; ωW; γW; gtW; cofW)
open import OCF.Align.Closure using (cmpᵀ-refl) renaming (Pen to CPen)
open import OCF.Align.LadderLabZStandardOmega using ()
open import OCF.Align.LadderLabZGoodLBase
open import OCF.Align.LadderLabZUniformS
open import OCF.Align.LadderLabZUniform3Base hiding (_⊕_; Ψ; evη) renaming (FW to FW₀)
open import OCF.Align.LadderLabZUniform3Rel
open import OCF.Align.LadderLabZUniform3SqABase
open import OCF.Align.LadderLabZUniform3Hon
open import OCF.Align.LadderLabZUniform3Depth2Class
open import OCF.Align.LadderLabZUniform3Depth2W using (InpW; CH; FHν; fsTΩ)
open import OCF.Align.LadderLabZUniform3Depth2Fold using (Zc₀; Zc₀-of; InpO)
open import OCF.Align.LadderLabZUniform3Full using (FlrLab[]-up; LWʰ-up; FH-pred; pred-Pr; ∅ᴿ-goodʰ)
open import OCF.Align.LadderLabZUniform5Head
open import OCF.Align.LadderLabZUniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Align.LadderLabZUniform3SqA using (LW0→LW)
open GRᴬ
open import OCF.Align.LadderLabZUniform5Class using (Mode; hon; wkm; Fw; FlU; Cv; cv-h; cv-w; Cv-tr; Cv-refl; Fw-cv; FlU-cv; FlM; FlM-cv; FC)
open import OCF.Align.LadderLabZUniform5Eval using (OkW; Cv-of; Fw→[]; inp₀)
open import OCF.Align.LadderLabZInfWTree 𝕊
open import OCF.Align.LadderLabClass 𝕊 𝕏
open import OCF.Align.LadderLabPsi 𝕊 𝕏
open import OCF.Align.LadderLabRel 𝕊 𝕏
```

## §0 极限行

`LimRow` 对 $W$ 一致: 只要共尾度 $\Omega_{W+1}$ 的 $W$ 对可数项恒 `gt`.

```agda
module LimRowP {W : T} {ps : T} {y : PT} {ys : T} (cc : cof (y ∷ ys) ≡ cΩ W) (gtᵂ : ∀ {w} → Idx w → cmpᵀ (sucT W) w ≡ gt) where
  limμW : ∀ {c′ φ} {F : ℕ → Run φ} → (∀ n → LWʰ[ c′ ] (F n) (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) W n))) → LWʰ[ c′ ] (limA 0 F) (ps ++ (y ∷ ys))
  limμW {F = F} h {w = w} ev p Iw ei ki u =
    gl (trans (cofW w ps y ys) (trans (cong (E.cofA w) cc) (cong (E.cofψ₊ w W) (gtᵂ Iw))))
       (λ n → subst (LabL₊ _ Ll _) (sym (gtW w ps y ys W cc (gtᵂ Iw) n)) (proj₁ (h n ev p Iw ei ki u))) ,
    hl (NB-sum ps) (λ n → subst (Hn _) (sym (gtW w ps y ys W cc (gtᵂ Iw) n)) (proj₂ (h n ev p Iw ei ki u)))

  limμO : ∀ {φ} {F : ℕ → Run φ} → (∀ n → L0 (F n) (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) W n))) → L0 (limA 0 F) (ps ++ (y ∷ ys))
  limμO {F = F} h ev p nu =
    let cω′ = trans (cofW [] ps y ys) (trans (cong (E.cofA []) cc) (cong (E.cofψ₊ [] W) (gtᵂ I0))) in
    let Rn = λ n → h n ev p (subst NF₁ (gtW [] ps y ys W cc (gtᵂ I0) n) (NF₁-fsn nu cω′ n)) in
    limᴸ nu cω′ (λ n → proj₁ (Rn n)) (λ n → subst (Lab _) (sym (gtW [] ps y ys W cc (gtᵂ I0) n)) (proj₂ (Rn n)))
```

## §1 互模拟求值

```agda
R→Rdᵠ : ∀ {m a b φ χ ψ ρ w w′} {x : Q m a φ χ} {x′ : Q m b ψ ρ} → Rq m a b x x′ → (ok : Ok w) (e : Eh h₀ m w χ) (ok′ : Ok w′) (e′ : Eh h₀ m w′ ρ) → Rd 0 (ψ̄ᵠ ok e x) (ψ̄ᵠ ok′ e′ x′)
R→Rdᵠ rz ok e ok′ e′ = wkRd 0 _ _ (H→R 0 (proj₂ ∅ᴿ-goodʰ))
R→Rdᵠ (rs s c r) ok e ok′ e′ = sucRᴬ (R→Rdᵠ r ok e ok′ e′)
R→Rdᵠ (rl h) ok e ok′ e′ = limRd 0 (λ n → R→Rdᵠ (h n) ok e ok′ e′)
R→Rdᵠ (ri {ac = ac} {ac′ = ac′} {f = f} {f′ = f′} d h) ok e ok′ e′ = limᵢRd 0 {ac = ac} {ac′ = ac′} {H = λ x → ψ̄ᵠ ok e (f x)} {H′ = λ x → ψ̄ᵠ ok′ e′ (f′ x)} d (λ x y dd → R→Rdᵠ (h x y dd) ok e ok′ e′)
R→Rdᵠ (rŝ d r h) ok e ok′ e′ = ŝRd 0 d (R→Rdᵠ r ok e ok′ e′) (λ η ee η′ e₁ dd → R→Rdᵠ (h η ee η′ e₁ dd) ok e ok′ e′)
R→Rdᵠ (rĉ d dz dg r h) ok e ok′ e′ = ĉRd 0 d dz dg (R→Rdᵠ r ok e ok′ e′) (λ η ee η′ e₁ dd → R→Rdᵠ (h η ee η′ e₁ dd) ok e ok′ e′)
R→Rdᵠ (rclo {t = t} {t′} {g} {g′} s r h) ok e ok′ e′ = cloRd 0 {t = ψ̄ᵠ ok e t} {g = λ η → ψ̄ᵠ ok e (g η)} {t′ = ψ̄ᵠ ok′ e′ t′} {g′ = λ η → ψ̄ᵠ ok′ e′ (g′ η)} s (R→Rdᵠ r ok e ok′ e′) (λ η η′ d → R→Rdᵠ (h η η′ d) ok e ok′ e′)
R→Rdᵠ {χ = χ} {ρ = ρ} {w = w} {w′ = w′} (rcl {n = n} {κ₁ = κ₁} {κ₂ = κ₂} {q = q} {s = s₁} {s′ = s₂} same s r h) ok e ok′ e′ =
  ŝRd 0 (bound-≅ (⊔∼ s (fk∼ z≅)) _ (zr ok n) _ (zr ok′ n) z≅) (R→Rdᵠ r ok e ok′ e′)
      (λ η d η′ d′ eη → R→Rdᵠ (h η η′ eη)
         (upd-ok n w ok (tt , λ x → lim 0 (proj₂ (evF B₁) x))) (λ i k r₁ → upd-ev n i w χ (evη κ₁ B₁ η d) (e i k r₁))
         (upd-ok n w′ ok′ (tt , λ x → lim 0 (proj₂ (evF B₂) x))) (λ i k r₁ → upd-ev n i w′ ρ (evη κ₂ B₂ η′ d′) (e′ i k r₁)))
  where
  B₁ = bound (κ₁ ⊔ fk zero) (s₁ (e n (Hi-0 n) q)) (zr ok n)
  B₂ = bound (κ₂ ⊔ fk zero) (s₂ (e′ n (Hi-0 n) q)) (zr ok′ n)
R→Rdᵠ (rwk {le = le} {lc = lc} {le′ = le′} {lc′ = lc′} r) ok e ok′ e′ = wkRd 0 le le′ (R→Rdᵠ r ok (λ i h r₁ → lc i r₁ (e i h r₁)) ok′ (λ i h r₁ → lc′ i r₁ (e′ i h r₁)))
R→Rdᵠ (rob _ l r) ok e ok′ e′ = R→Rdᵠ r ok e ok′ e′
R→Rdᵠ (rΩ↓ {φ = φ} {χ} {ψ} {ρ} {n} {q = q} {fe = fe} {fe′} {ac} {ac′} {h} {h′} same ek s c f) ok e ok′ e′ =
  limRd 0 (λ i → wkRd 0 _ _ (R→Rdᵠ (f φ ψ (Z* χ) (Z* ρ) s (Z∼ (λ j r → c j (tr< r q))) (Z∼ (λ j r → c j (tr< r q))) _ _ (intoVH q (chRΨ q ok (e⁺ n ok (e↓ e)) (ac (e↓ e n (inj₁ refl) q)) ok′ (e⁺ n ok′ (e↓ e′)) (ac′ (e↓ e′ n (inj₁ refl) q)) {fe = fe} {fe′ = fe′} {a₁ = λ v → fe v , (v , v)} {a₂ = λ v → fe′ v , (v , v)} {h = h} {h′ = h′} ek s c f i))) ok (e⁺ n ok e) ok′ (e⁺ n ok′ e′)))
R→Rdᵠ {m} (rΩ {φ = φ} {χ} {ψ} {ρ} {fe = fe} {fe′} {r} {r′} {h} {h′} ek s c f) ok e ok′ e′ =
  limRd 0 (λ i → wkRd 0 _ _ (R→Rdᵠ (f φ ψ (Z* χ) (Z* ρ) s (Z∼ c) _ _ (intoRq (<→◃ r) (chRG {fe = fe} {fe′ = fe′} {a₁ = λ v → fe v , (v , v)} {a₂ = λ v → fe′ v , (v , v)} {r = r} {r′ = r′} {h = h} {h′ = h′} ek s c f i))) ok (e⁺ m ok e) ok′ (e⁺ m ok′ e′)))
```

## §2 $W$ 部分

```agda
pickF : ∀ {ψ ps y ys w₀ ℓ} → FW₀ (ψ ⊔ fk zero) ps y ys → (I₀ : Idx w₀) → zero ≼ lvI I₀ → Ob w₀ ps y ys → (B : Top zero ℓ (ψ ⊔ fk zero)) →
        Σ T λ w′ → Σ (Idx w′) λ Iw′ → (Bd B ⊑ᴵ suc (lvI Iw′)) × Ob w′ ps y ys
pickF {ψ} {ps} {y} {ys} fw I₀ z₀ o B = pickG {Θ = λ θ → ps ++ fsT (y ∷ ys) θ} fw (λ o′ → o′) I₀ z₀ o B

Lq→W : ∀ {m c′ c b mo φ χ w} {x : Q m c′ φ χ} {u} → OkW mo c → (ok : Ok w) (e : Eh h₀ m w χ) → Lq m c′ b mo x u → Wd c 0 (ψ̄ᵠ ok e x) u
Lq→W o ok e lz = wkW 0 _ (G→W 0 ∅ᴿ-goodʰ)
Lq→W o ok e (ls {ps = ps} {y} {ys} {a = a} cc F Fχ _ l) = sucWʰ {ps = ps} {y = y} {ys = ys} {R = ψ̄ᵠ ok e a} cc (Lq→W o ok e l)
Lq→W o ok e (ll {ps = ps} {y} {ys} {F} cc h) = limWd 0 {ps = ps} {y = y} {ys = ys} {F = λ n → ψ̄ᵠ ok e (F n)} cc (λ n → Lq→W o ok e (h n))
Lq→W {mo = mo} o ok e (li {ps = ps} {y} {ys} {ν} {j} {ac} {f} cc I d hP hI) =
  limᵢWd 0 {ps = ps} {y = y} {ys = ys} {ac = ac} {H = λ x → ψ̄ᵠ ok e (f x)} cc I d (InpW j) (inp₀ I d)
         (λ kj o′ → frL₊ kj (proj₁ o′) , λ _ → proj₂ o′ , FHν I d)
         (λ η x l {i} s ui → Lq→W {mo = wkm i} (≼-refl i) ok e (hP η x l s (Cv-of o ui)))
         (λ {η} {x} ix → Lq→W o ok e (hI η x ix))
Lq→W o ok e (lĉ {ps = ps} {y} {ys} {o₀ = o₀} {o = o₁} cc K h₀′ hk) =
  ĉWd 0 {ps = ps} {y = y} {ys = ys} {O₀ = ψ̄ᵠ ok e o₀} {O = λ η d → ψ̄ᵠ ok e (o₁ η d)} cc K (Lq→W o ok e h₀′) (λ k → Lq→W o ok e (hk k))
Lq→W o ok e (lŝ {ps = ps} {y} {ys} {t = t} {g} cc I b ob₁ h₀′ hg) =
  ŝWd 0 {ps = ps} {y = y} {ys = ys} {T₀ = ψ̄ᵠ ok e t} {G = λ η d → ψ̄ᵠ ok e (g η d)} cc I b ob₁ (Lq→W o ok e h₀′) (λ θ Y hY lY nθ lt d → Lq→W o ok e (hg θ Y hY lY nθ lt d))
Lq→W o ok e (lclo {ps = ps} {y} {ys} {t} {g} F cc h₀′ hg) =
  cloWd 0 {ps = ps} {y = y} {ys = ys} {t = ψ̄ᵠ ok e t} {g = λ η → ψ̄ᵠ ok e (g η)} (Fw→[] o F) cc (Lq→W o ok e h₀′) (λ θ Y hY lY nθ lt → Lq→W o ok e (hg θ Y hY lY nθ lt))
Lq→W {χ = χ} {w = w} o ok e (lcl {ps = ps} {y} {ys} {n = n} {ψ = ψ} {q = q} {s = s} {t = t} {g} G cc I₀ z₀ o₀ h₀′ hg) =
  ŝWd 0 {ps = ps} {y = y} {ys = ys} {T₀ = ψ̄ᵠ ok e t} {G = λ η d → ψ̄ᵠ (upd-ok n w ok (tt , λ q′ → lim 0 (proj₂ (evF B) q′))) (λ i h r → upd-ev n i w χ (evη ψ B η d) (e i h r)) (g η)} cc (proj₁ (proj₂ Pk)) (proj₁ (proj₂ (proj₂ Pk))) (proj₂ (proj₂ (proj₂ Pk)))
      (Lq→W o ok e h₀′) (λ θ Y hY lY nθ lt d → Lq→W o (upd-ok n w ok (tt , λ q′ → lim 0 (proj₂ (evF B) q′))) (λ i h r → upd-ev n i w χ (evη ψ B (toLevel Y hY) d) (e i h r)) (hg θ Y hY lY nθ lt))
  where
  B = bound (ψ ⊔ fk zero) (s (e n (Hi-0 n) q)) (zr ok n)
  Pk = pickF G I₀ z₀ o₀ B
Lq→W o ok e (lwk {le = le} {le′ = le′} l) = wkW 0 le (Lq→W o ok (λ i h r → le′ i r (e i h r)) l)
Lq→W o ok e (lob l x) = Lq→W o ok e x
Lq→W {mo = mo} o ok e (lΩ↓ {φ = φ} {χ} {ps} {y} {ys} {n} {k} {ν = ν} {q = q} {fe} {ac} {h} cc Iν ek f) =
  LimRowP.limμW {W = P n ν} {ps} {y} {ys} cc (P-gt n ν) {F = λ i → wk 0 (λ v → v , v) (ψ̄ᵠ ok (e⁺ n ok e) (h φ (Z* χ) (intoV q (chainᵠ fe fc* (λ z → qwk (λ v → fe v , (v , v)) (⇑ (cv* n)) (Ψ q ok (e⁺ n ok (e↓ e)) (ac (e↓ e n (inj₁ refl) q)) (h φ (Z* χ) (intoV q z)))) i))))}
    (λ i → wkW 0 (λ v → v , v) (Lq→W o ok (e⁺ n ok e) (f (Cv-refl mo) φ (Z* χ) _ _ (intoLV q (chainΨ {fe = fe} {a = λ v → fe v , (v , v)} q ok (e⁺ n ok (e↓ e)) (ac (e↓ e n (inj₁ refl) q)) {h = h} Iν ek f i)))))
Lq→W {m} {mo = mo} o ok e (lΩ {φ = φ} {χ} {ps} {y} {ys} {ν = ν} {fe} {r} {h} cc Iν ek f) =
  LimRowP.limμW {W = P m ν} {ps} {y} {ys} cc (P-gt m ν) {F = λ i → wk 0 (λ v → v , v) (ψ̄ᵠ ok (e⁺ m ok e) (h φ (Z* χ) (intoU (<→◃ r) (chainᵠ fe fc* (λ z → qwk (λ v → fe v , (v , v)) (⇑ (cv* m)) (ψᵠ r (h φ (Z* χ) (intoU (<→◃ r) z)))) i))))}
    (λ i → wkW 0 (λ v → v , v) (Lq→W o ok (e⁺ m ok e) (f (Cv-refl mo) φ (Z* χ) _ _ (intoL (<→◃ r) (chainG {fe = fe} {a = λ v → fe v , (v , v)} {r = r} {h = h} Iν ek f i)))))
```

## §3 $L_0$ 部分与主定理

```agda
Lq→O : ∀ {m c b φ χ w} {x : Q m c φ χ} {u} → Lq m c b hon x u → Rq m c c x x → (ok : Ok w) (e : Eh h₀ m w χ) → Od 0 (ψ̄ᵠ ok e x) u
Lq→O lz rz ok e = wkO 0 {X = ∅ᴿ} (λ _ → tt) (H→O 0 (proj₂ ∅ᴿ-goodʰ))
Lq→O (ls {ps = ps} {y} {ys} {a = a} cc F Fχ _ l) (rs s c r) ok e = suc0 {ps = ps} {y = y} {ys = ys} {R = ψ̄ᵠ ok e a} cc (Lq→O l r ok e)
Lq→O (ll {ps = ps} {y} {ys} {F} cc h) (rl h′) ok e = limOd 0 {ps = ps} {y = y} {ys = ys} {F = λ n → ψ̄ᵠ ok e (F n)} cc (λ n → Lq→O (h n) (h′ n) ok e)
Lq→O (li {ps = ps} {y} {ys} {ν} {j = zero} {ac} {f} cc I d hP hI) (ri e′ h′) ok e =
  limᵢOᴬ 0 {ps = ps} {y = y} {ys = ys} {ac = ac} {H = λ x → ψ̄ᵠ ok e (f x)} cc I d
         (λ η x l → Lq→W tt ok e (hI η x (l , λ ())))
         (λ η x l xx → Lq→O (hI η x (l , λ ())) (h′ x x xx) ok e , R→Rdᵠ (h′ x x xx) ok e ok e)
Lq→O (li {ps = ps} {y} {ys} {ν} {j = suc j} {ac} {f} cc I d hP hI) (ri e′ h′) ok e =
  limᵢOᴾ 0 {ps = ps} {y = y} {ys = ys} {ac = ac} {H = λ x → ψ̄ᵠ ok e (f x)} refl cc I d (InpO (suc j))
         (proj₁ (inp₀ I d) , Ωˢ-≅ᴬ (≅ᴵ-refl (suc j)) , proj₂ (inp₀ I d))
         (λ o xx → frL₊ refl (proj₁ o) , xx , λ _ → proj₂ o , FHν I d)
         (λ {η} {x} i → Lq→W tt ok e (hI η x (proj₁ i , proj₂ (proj₂ i))))
         (λ {η} {x} i → R→Rdᵠ (h′ x x (proj₁ (proj₂ i))) ok e ok e)
         (λ {η} {x} i → Lq→O (hI η x (proj₁ i , proj₂ (proj₂ i))) (h′ x x (proj₁ (proj₂ i))) ok e)
Lq→O (li {ps = ps} {y} {ys} {ν} {j = lim g s} {ac} {f} cc I d hP hI) (ri e′ h′) ok e =
  limᵢOᴾ 0 {ps = ps} {y = y} {ys = ys} {ac = ac} {H = λ x → ψ̄ᵠ ok e (f x)} refl cc I d (InpO (lim g s))
         (proj₁ (inp₀ I d) , Ωˢ-≅ᴬ (≅ᴵ-refl (lim g s)) , proj₂ (inp₀ I d))
         (λ o xx → frL₊ refl (proj₁ o) , xx , λ _ → proj₂ o , FHν I d)
         (λ {η} {x} i → Lq→W tt ok e (hI η x (proj₁ i , proj₂ (proj₂ i))))
         (λ {η} {x} i → R→Rdᵠ (h′ x x (proj₁ (proj₂ i))) ok e ok e)
         (λ {η} {x} i → Lq→O (hI η x (proj₁ i , proj₂ (proj₂ i))) (h′ x x (proj₁ (proj₂ i))) ok e)
Lq→O (lĉ {ps = ps} {y} {ys} {o₀ = o₀} {o} cc K h₀′ hk) (rĉ d dz dg r h′) ok e =
  ĉOd 0 {ps = ps} {y = y} {ys = ys} {O₀ = ψ̄ᵠ ok e o₀} {O = λ η d → ψ̄ᵠ ok e (o η d)} cc K (Lq→O h₀′ r ok e)
      (λ k → Lq→O (hk k) (h′ _ _ _ _ (≅ᴵ-refl _)) ok e)
Lq→O (lŝ {ps = ps} {y} {ys} {t = t} {g} cc I b o h₀′ hg) (rŝ d r h′) ok e =
  ŝOd 0 {ps = ps} {y = y} {ys = ys} {T₀ = ψ̄ᵠ ok e t} {G = λ η d → ψ̄ᵠ ok e (g η d)} cc I b o (Lq→O h₀′ r ok e)
      (λ θ Y hY lY nθ lt ee → Lq→O (hg θ Y hY lY nθ lt ee) (h′ _ _ _ _ (≅ᴵ-refl _)) ok e)
Lq→O (lclo {ps = ps} {y} {ys} {t} {g} F cc h₀′ hg) (rclo s r h′) ok e =
  cloOd 0 {ps = ps} {y = y} {ys = ys} {t = ψ̄ᵠ ok e t} {g = λ η → ψ̄ᵠ ok e (g η)} F cc (Lq→O h₀′ r ok e)
      (λ θ Y hY lY nθ lt → Lq→O (hg θ Y hY lY nθ lt) (h′ _ _ (≅ᴵ-refl _)) ok e)
Lq→O {χ = χ} {w = w} (lcl {ps = ps} {y} {ys} {n = n} {ψ = ψ} {q = q} {s = s} {t = t} {g} G cc I₀ z₀ o h₀′ hg) (rcl _ s′ r h′) ok e =
  ŝOd 0 {ps = ps} {y = y} {ys = ys} {T₀ = ψ̄ᵠ ok e t} {G = λ η d → ψ̄ᵠ (upd-ok n w ok (tt , λ q′ → lim 0 (proj₂ (evF B) q′))) (λ i h r → upd-ev n i w χ (evη ψ B η d) (e i h r)) (g η)} cc (proj₁ (proj₂ Pk)) (proj₁ (proj₂ (proj₂ Pk))) (proj₂ (proj₂ (proj₂ Pk)))
      (Lq→O h₀′ r ok e)
      (λ θ Y hY lY nθ lt d → Lq→O (hg θ Y hY lY nθ lt) (h′ _ _ (≅ᴵ-refl _)) (upd-ok n w ok (tt , λ q′ → lim 0 (proj₂ (evF B) q′))) (λ i h r → upd-ev n i w χ (evη ψ B (toLevel Y hY) d) (e i h r)))
  where
  B = bound (ψ ⊔ fk zero) (s (e n (Hi-0 n) q)) (zr ok n)
  Pk = pickF G I₀ z₀ o B
Lq→O (lwk {le = le} {le′ = le′} {x = x} l) (rwk r) ok e = wkO 0 {X = ψ̄ᵠ ok (λ i h r₁ → le′ i r₁ (e i h r₁)) x} le (Lq→O l r ok (λ i h r₁ → le′ i r₁ (e i h r₁)))
Lq→O (lob l x) (rob _ _ r) ok e = Lq→O x r ok e
Lq→O (lΩ↓ {φ = φ} {χ} {ps} {y} {ys} {n} {k} {ν = ν} {q = q} {fe} {ac} {h} cc Iν ek f) (rΩ↓ _ e′ s c f′) ok e =
  LimRowP.limμO {W = P n ν} {ps} {y} {ys} cc (P-gt n ν) {F = λ i → wk 0 (λ v → v , v) (ψ̄ᵠ ok (e⁺ n ok e) (h φ (Z* χ) (intoV q (chainᵠ fe fc* (λ z → qwk (λ v → fe v , (v , v)) (⇑ (cv* n)) (Ψ q ok (e⁺ n ok (e↓ e)) (ac (e↓ e n (inj₁ refl) q)) (h φ (Z* χ) (intoV q z)))) i))))}
    (λ i → wkO 0 {X = ψ̄ᵠ ok (e⁺ n ok e) (h φ (Z* χ) (intoV q (chainᵠ fe fc* (λ z → qwk (λ v → fe v , (v , v)) (⇑ (cv* n)) (Ψ q ok (e⁺ n ok (e↓ e)) (ac (e↓ e n (inj₁ refl) q)) (h φ (Z* χ) (intoV q z)))) i)))} (λ v → v , v)
       (Lq→O (f cv-h φ (Z* χ) _ _ (intoLV q (chainΨ {fe = fe} {a = λ v → fe v , (v , v)} q ok (e⁺ n ok (e↓ e)) (ac (e↓ e n (inj₁ refl) q)) {h = h} Iν ek f i)))
             (f′ φ φ (Z* χ) (Z* χ) s (Z∼ (λ j r → c j (tr< r q))) (Z∼ (λ j r → c j (tr< r q))) _ _ (intoVH q (chRΨ q ok (e⁺ n ok (e↓ e)) (ac (e↓ e n (inj₁ refl) q)) ok (e⁺ n ok (e↓ e)) (ac (e↓ e n (inj₁ refl) q)) {fe = fe} {fe′ = fe} {a₁ = λ v → fe v , (v , v)} {a₂ = λ v → fe v , (v , v)} {h = h} {h′ = h} e′ s c f′ i))) ok (e⁺ n ok e)))
Lq→O {m} (lΩ {φ = φ} {χ} {ps} {y} {ys} {ν = ν} {fe} {r} {h} cc Iν ek f) (rΩ e′ s c f′) ok e =
  LimRowP.limμO {W = P m ν} {ps} {y} {ys} cc (P-gt m ν) {F = λ i → wk 0 (λ v → v , v) (ψ̄ᵠ ok (e⁺ m ok e) (h φ (Z* χ) (intoU (<→◃ r) (chainᵠ fe fc* (λ z → qwk (λ v → fe v , (v , v)) (⇑ (cv* m)) (ψᵠ r (h φ (Z* χ) (intoU (<→◃ r) z)))) i))))}
    (λ i → wkO 0 {X = ψ̄ᵠ ok (e⁺ m ok e) (h φ (Z* χ) (intoU (<→◃ r) (chainᵠ fe fc* (λ z → qwk (λ v → fe v , (v , v)) (⇑ (cv* m)) (ψᵠ r (h φ (Z* χ) (intoU (<→◃ r) z)))) i)))} (λ v → v , v)
       (Lq→O (f cv-h φ (Z* χ) _ _ (intoL (<→◃ r) (chainG {fe = fe} {a = λ v → fe v , (v , v)} {r = r} {h = h} Iν ek f i)))
             (f′ φ φ (Z* χ) (Z* χ) s (Z∼ c) _ _ (intoRq (<→◃ r) (chRG {fe = fe} {fe′ = fe} {a₁ = λ v → fe v , (v , v)} {a₂ = λ v → fe v , (v , v)} {r = r} {r′ = r} {h = h} {h′ = h} e′ s c f′ i))) ok (e⁺ m ok e)))

labelᵠ : ∀ {m c b φ χ w} {x : Q m c φ χ} {u} → Lq m c b hon x u → Rq m c c x x → (ok : Ok w) (e : Eh h₀ m w χ) → NF₁ (ψ₀ᵗ u) → ∀ {ℓ} (ev : Ev ℓ φ) (p : zero <ᴵ ℓ) → Lab₀ (ψ̄ᵠ ok e x ev p) (ψ₀ᵗ u)
labelᵠ l r ok e nf ev p = Lq→O l r ok e ev p nf
```
