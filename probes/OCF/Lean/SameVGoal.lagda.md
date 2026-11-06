# SameV (五): 地板律, 地板的分支跨层单调, `P2`, `TX + 1 ≤ TU 1`

> 不含记号. 入口 [SameV](SameV.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延 (作为定义); 模块参数 `uipC` (`Cd` 上的 UIP, 由函数外延推出, `ValCUip.fe→uipC`, 条件). 实例 `I₁`. 只导入 stdlib, `OCF.Lean.CRw*`, `OCF.Lean.ValC*`, `OCF.Lean.ValX*`, `OCF.Lean.SameV*` (只用, 不改).
>
> 对任一推导 $p : a\le b$ (第 0 层), [SameVLeg](SameVLeg.lagda.md) 给出配对. 本篇对同一个 $p$ 逐构造子证:
>
> - **地板律 `tp`:** 配对的层的地板跨层相关. 这是 `crossΦ`, `crossX` 的前提, 不是假设.
> - **`gtP`:** 地板的分支跨层相关: $\mathrm{gt}(1\boxplus\mathrm{leg}\,a)\preceq_X\mathrm{gt}(1\boxplus\mathrm{leg}\,b)$. `floor-block` 说层反射的关系做不到; `_≼X_` 不层反射.
> - **`P2-thm`**, **`P2L-thm`:** ValXP1 的 `P2` 与它对 $k_L$ 的版本 (条件 UIP).
> - **`goal`:** $\mathrm{TX}+1\le\mathrm{TU}\,1$ (条件 UIP).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwBase using (Cd)
open import Relation.Binary.PropositionalEquality using (_≡_)
module OCF.Lean.SameVGoal (uipC : ∀ {x y : Cd} (e e′ : x ≡ y) → e ≡ e′) where

open import Data.Nat using (ℕ; zero; suc; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (<⇒<′)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (refl; subst; subst₂; sym; trans; cong)
open import OCF.Lean.CRwBase hiding (Pr)
open import OCF.Lean.CRw using (I₁; leg; Σ₀; W₀; TX; TU1; PH-topL)
open import OCF.Lean.CRwFold I₁
open import OCF.Lean.ValCRel I₁
open import OCF.Lean.ValCBase I₁ hiding (ap)
open import OCF.Lean.ValXRel I₁
open import OCF.Lean.ValXTm using (shLaw₁; sound₀)
open import OCF.Lean.ValXBase I₁ shLaw₁
open import OCF.Lean.ValXGoal using (κΩ; g₀; nd₀; kL; kR; Hyp)
open import OCF.Lean.ValCIf I₁ using (toA)
open import OCF.Lean.ValXP1 uipC using (U; MoX-U; MoX-gt; P2; goal-P2; pgL; P1)
open import OCF.Align.CumReadCF using (asuc)
import OCF.Align.TLRuleSpec as TL
open import OCF.Lean.SameVRel I₁ using (Match)
import OCF.Lean.SameVMono as SM
import OCF.Lean.SameVX as SX
open import OCF.Lean.SameVLeg
open ShLaw shLaw₁
```

## §1 第 0 层

```agda
module Core {a₀ b₀} (p₀ : LeAt hz a₀ b₀) where
  private
    Mt : Match
    Mt = M.match p₀
  open SM I₁ uipC Mt
  open SX I₁ uipC shLaw₁ Mt

  le← : ∀ {x y} → LE hz hz x y → LeAt hz x y
  le← R2.z≼ = Rel.z≤
  le← (R2.s≼s p) = Rel.s≤s (le← p)
  le← (R2.≼s p) = Rel.≤s (le← p)
  le← (R2.l≼l σ i h) = Rel.l≤l σ i (λ n → le← (h n))
  le← (R2.≼l n p) = Rel.≤l n (le← p)
  le← (R2.≼Ω {κ′ = ()} _ _ _ _)
  le← (R2.Ω≼Ω {κ′ = ()} _ _)

  le→ : ∀ {x y} → LeAt hz x y → LE hz hz x y
  le→ Rel.z≤ = R2.z≼
  le→ (Rel.s≤s p) = R2.s≼s (le→ p)
  le→ (Rel.≤s p) = R2.≼s (le→ p)
  le→ (Rel.l≤l σ i h) = R2.l≼l σ i (λ n → le→ (h n))
  le→ (Rel.≤l n p) = R2.≼l n (le→ p)
  le→ (Rel.≤Ω {κ = ()} _ _ _ _)
  le→ (Rel.Ω≤Ω {κ = ()} _ _)
```

## §2 嵌入

```agda
  upR : ∀ {x y} {a : H x} {b : H y} → LE x y a b → LE x (hs y) a (up b)
  upR R2.z≼ = R2.z≼
  upR (R2.s≼s p) = R2.s≼s (upR p)
  upR (R2.≼s p) = R2.≼s (upR p)
  upR (R2.l≼l σ i h) = R2.l≼l σ i (λ n → upR (h n))
  upR (R2.≼l n p) = R2.≼l n (upR p)
  upR (R2.≼Ω {κ′ = κ} c bd mc p) = R2.≼Ω {κ′ = inj₁ κ} c bd mc (upR p)
  upR (R2.Ω≼Ω {κ′ = κ} ev h) = R2.Ω≼Ω {κ′ = inj₁ κ} ev (λ d d′ md r → upR (h d d′ md r))

  up2 : ∀ {x y} {a : H x} {b : H y} → LE x y a b → LE (hs x) (hs y) (up a) (up b)
  up2 R2.z≼ = R2.z≼
  up2 (R2.s≼s p) = R2.s≼s (up2 p)
  up2 (R2.≼s p) = R2.≼s (up2 p)
  up2 (R2.l≼l σ i h) = R2.l≼l σ i (λ n → up2 (h n))
  up2 (R2.≼l n p) = R2.≼l n (up2 p)
  up2 (R2.≼Ω {κ′ = κ} c bd mc p) = R2.≼Ω {κ′ = inj₁ κ} c bd mc (up2 p)
  up2 (R2.Ω≼Ω {κ = κ} {κ′ = κ′} ev h) = R2.Ω≼Ω {κ = inj₁ κ} {κ′ = inj₁ κ′} ev (λ d d′ md r → up2 (h d d′ md r))

  ιR : ∀ {x} {f : ℕ → Cd} n {a : H x} {b : H (f n)} → LE x (f n) a b → LE x (hl f) a (ι n b)
  ιR n R2.z≼ = R2.z≼
  ιR n (R2.s≼s p) = R2.s≼s (ιR n p)
  ιR n (R2.≼s p) = R2.≼s (ιR n p)
  ιR n (R2.l≼l σ i h) = R2.l≼l σ i (λ k → ιR n (h k))
  ιR n (R2.≼l k p) = R2.≼l k (ιR n p)
  ιR n (R2.≼Ω {κ′ = κ} c bd mc p) = R2.≼Ω {κ′ = n , κ} c bd mc (ιR n p)
  ιR n (R2.Ω≼Ω {κ′ = κ} ev h) = R2.Ω≼Ω {κ′ = n , κ} ev (λ d d′ md r → ιR n (h d d′ md r))

  ι2 : ∀ {f g : ℕ → Cd} n m {a : H (f n)} {b : H (g m)} → LE (f n) (g m) a b → LE (hl f) (hl g) (ι n a) (ι m b)
  ι2 n m R2.z≼ = R2.z≼
  ι2 n m (R2.s≼s p) = R2.s≼s (ι2 n m p)
  ι2 n m (R2.≼s p) = R2.≼s (ι2 n m p)
  ι2 n m (R2.l≼l σ i h) = R2.l≼l σ i (λ k → ι2 n m (h k))
  ι2 n m (R2.≼l k p) = R2.≼l k (ι2 n m p)
  ι2 n m (R2.≼Ω {κ′ = κ} c bd mc p) = R2.≼Ω {κ′ = m , κ} c bd mc (ι2 n m p)
  ι2 n m (R2.Ω≼Ω {κ = κ} {κ′ = κ′} ev h) = R2.Ω≼Ω {κ = n , κ} {κ′ = m , κ′} ev (λ d d′ md r → ι2 n m (h d d′ md r))
```

## §3 地板律

```agda
  TP : Cd → Cd → Set
  TP x y = LE x y (top b⊥ x) (top b⊥ y)

  ΣT≡ : ∀ (f : ℕ → Cd) n → ΣT S⊥ hz f n ≡ Σ⁺ (λ k → ι k (top b⊥ (f k))) n
  ΣT≡ f zero = refl
  ΣT≡ f (suc n) = cong (λ z → z ⊞ ι (suc n) (top b⊥ (f (suc n)))) (ΣT≡ f n)

  ΣR : ∀ {x} (f : ℕ → Cd) n {a : H x} → LE x (hl f) a (ι n (top b⊥ (f n))) → LE x (hl f) a (ΣT S⊥ hz f n)
  ΣR f zero p = p
  ΣR {x} f (suc n) p = Lm.tr≼ x (hl f) p (L.≤⊞ˡ (hl f) (ΣT S⊥ hz f n) (ι (suc n) (top b⊥ (f (suc n)))))

  topR : ∀ {x u w} {a : H x} → LE x u a (top b⊥ u) → u ⊲ w → LE x w a (top b⊥ w)
  topR p hself = p
  topR {w = hs y} p (hsuc q) = R2.≼Ω {κ′ = inj₂ tt} (top b⊥ y) (L.≤-refl y _) (Mo-top y) (upR (topR p q))
  topR {w = hl f} p (hlim n q) = R2.≼l n (ΣR f n (ιR n (topR p q)))
  topR p (hLim {κ = ()} _ _)

  ez : hz ~ hz
  ez = M.z≈ p₀

  mutual
    TT : ∀ {a b} (p : LeAt hz a b) π₁ π₂ → TP (ap π₁ hz) (ap π₂ hz) → (∀ {u v} → Pr p π₁ π₂ u v → u ~ v) →
         TP (ap π₁ (leg a)) (ap π₂ (leg b)) × (∀ {u v} → Pr p π₁ π₂ u v → TP u v)
    TT {b = b} Rel.z≤ π₁ π₂ base inc = topR base (ap⊲ π₂ (z⊲ᴮ (leg b))) , λ ()
    TT (Rel.s≤s {a = a} {b = b} p) π₁ π₂ base inc =
      subst₂ TP (sym (ap-s π₁ (leg a))) (sym (ap-s π₂ (leg b)))
        (R2.Ω≼Ω {κ = inj₂ tt} {κ′ = inj₂ tt} (inc (inj₁ (refl , refl))) (λ d d′ md r → up2 r)) ,
      λ { (inj₁ (refl , refl)) → proj₁ (TT p π₁ π₂ base (λ r → inc (inj₂ r)))
        ; (inj₂ r) → proj₂ (TT p π₁ π₂ base (λ r → inc (inj₂ r))) r }
    TT (Rel.≤s {b = b} p) π₁ π₂ base inc =
      topR (proj₁ (TT p π₁ π₂ base inc)) (⊲-s π₂ hself) , proj₂ (TT p π₁ π₂ base inc)
    TT (Rel.≤l {g = g} n p) π₁ π₂ base inc =
      topR (proj₁ (TT p π₁ (pre π₂ (Fs g) n) (topR base (pre-lo π₂ (Fs g) n)) inc)) (⊲-L π₂ g n hself) ,
      proj₂ (TT p π₁ (pre π₂ (Fs g) n) (topR base (pre-lo π₂ (Fs g) n)) inc)
    TT (Rel.l≤l {f = f} {g = g} σ i h) π₁ π₂ base inc =
      subst₂ TP (sym (ap-l π₁ (Σ₀ (Fs f)))) (sym (ap-l π₂ (Σ₀ (Fs g))))
        (R2.l≼l σ i (λ n → subst₂ (LE _ _) (sym (ΣT≡ Ql n)) (sym (ΣT≡ Qr (σ n)))
           (Lm.Σ≼ (hl Ql) (hl Qr) (λ k → ι k (top b⊥ (Ql k))) (λ k → ι k (top b⊥ (Qr k))) σ i
              (λ k → ι2 {Ql} {Qr} k (σ k) (topAt σ i h π₁ π₂ base inc k)) n))) ,
      λ { (n , r) → proj₂ (TTn σ i h π₁ π₂ base inc n) r }
      where
      Ql Qr : ℕ → Cd
      Ql n = ap π₁ (Σ₀ (Fs f) n)
      Qr n = ap π₂ (Σ₀ (Fs g) n)
    TT (Rel.≤Ω {κ = ()} _ _ _ _)
    TT (Rel.Ω≤Ω {κ = ()} _ _)

    -- 第 n 段的下界相关
    TTb : ∀ {f g : ℕ → Cd} (σ : ℕ → ℕ) (i : Inc σ) (h : ∀ n → LeAt hz (f n) (g (σ n))) π₁ π₂ →
          TP (ap π₁ hz) (ap π₂ hz) → (∀ {u v} → Pr (Rel.l≤l σ i h) π₁ π₂ u v → u ~ v) → ∀ n →
          TP (ap (pre π₁ (Fs f) n) hz) (ap (pre π₂ (Fs g) (σ n)) hz)
    TTb {g = g} σ i h π₁ π₂ base inc zero = topR base (pre-lo π₂ (Fs g) (σ 0))
    TTb {g = g} σ i h π₁ π₂ base inc (suc n) = topR (topAt σ i h π₁ π₂ base inc n) (mon π₂ (Fs g) (<⇒<′ (i n)))

    TTn : ∀ {f g : ℕ → Cd} (σ : ℕ → ℕ) (i : Inc σ) (h : ∀ n → LeAt hz (f n) (g (σ n))) π₁ π₂ →
          TP (ap π₁ hz) (ap π₂ hz) → (∀ {u v} → Pr (Rel.l≤l σ i h) π₁ π₂ u v → u ~ v) → ∀ n →
          TP (ap (pre π₁ (Fs f) n) (leg (f n))) (ap (pre π₂ (Fs g) (σ n)) (leg (g (σ n)))) ×
          (∀ {u v} → Pr (h n) (pre π₁ (Fs f) n) (pre π₂ (Fs g) (σ n)) u v → TP u v)
    TTn σ i h π₁ π₂ base inc n = TT (h n) _ _ (TTb σ i h π₁ π₂ base inc n) (λ r → inc (n , r))

    topAt : ∀ {f g : ℕ → Cd} (σ : ℕ → ℕ) (i : Inc σ) (h : ∀ n → LeAt hz (f n) (g (σ n))) π₁ π₂ →
            TP (ap π₁ hz) (ap π₂ hz) → (∀ {u v} → Pr (Rel.l≤l σ i h) π₁ π₂ u v → u ~ v) → ∀ n →
            TP (ap π₁ (Σ₀ (Fs f) n)) (ap π₂ (Σ₀ (Fs g) (σ n)))
    topAt {f} {g} σ i h π₁ π₂ base inc n =
      subst₂ TP (pre-top π₁ (Fs f) n) (pre-top π₂ (Fs g) (σ n)) (proj₁ (TTn σ i h π₁ π₂ base inc n))

  T1 : TP (hs hz) (hs hz)
  T1 = R2.Ω≼Ω {κ = inj₂ tt} {κ′ = inj₂ tt} ez (λ d d′ md r → up2 r)

  tp : ∀ {k k′} → k ~ k′ → TP k k′
  tp (inj₁ (refl , refl)) = R2.z≼
  tp (inj₂ r) = proj₂ (TT p₀ π₀ π₀ T1 inj₂) r
```

## §4 地板的分支

```agda
  GP : Cd → Cd → Set
  GP x y = gt x ≼X gt y

  iu : ∀ c → H c → HX
  iu c x = ι {Cd} {λ c → Tw S⊥ (hs c)} c (up x)

  ιup : ∀ {L R} {d : H L} {d′ : H R} → LE L R d d′ → iu L d ≼X iu R d′
  ιup R2.z≼ = z≼
  ιup (R2.s≼s p) = s≼s (ιup p)
  ιup (R2.≼s p) = ≼s (ιup p)
  ιup (R2.l≼l σ i h) = l≼l σ i (λ n → ιup (h n))
  ιup (R2.≼l n p) = ≼l n (ιup p)
  ιup {R = R} (R2.≼Ω {κ′ = κ} c bd mc p) = ≼Ω {κ = R , inj₁ κ} c bd mc (λ B → ιup p)
  ιup {L} {R} (R2.Ω≼Ω {κ = κ} {κ′ = κ′} ev h) =
    Ω≼Ω {κ = L , inj₁ κ} {κ′ = R , inj₁ κ′} ev (λ l₁ l₂ w r → w)
      (λ d d′ md r B₁ B₂ w → ιup (h d d′ md (→ll L κ _ r)))

  nodeN : ∀ L R → hs hz ⊲ L → hs hz ⊲ R → L ~ R →
          ι {Cd} {λ c → Tw S⊥ (hs c)} L (topT S⊥ hz (hs L)) ≼X ι {Cd} {λ c → Tw S⊥ (hs c)} R (topT S⊥ hz (hs R))
  nodeN hz R () q ev
  nodeN (hΩ () _) R p q ev
  nodeN L hz p () ev
  nodeN L (hΩ () _) p q ev
  nodeN (hs x) (hs y) p q ev = Ω≼Ω ev (λ l₁ l₂ w r → w) (λ d d′ md r B₁ B₂ w → ιup r)
  nodeN (hs x) (hl g) p q ev = Ω≼Ω ev (λ l₁ l₂ w r → w) (λ d d′ md r B₁ B₂ w → ιup r)
  nodeN (hl f) (hs y) p q ev = Ω≼Ω ev (λ l₁ l₂ w r → w) (λ d d′ md r B₁ B₂ w → ιup r)
  nodeN (hl f) (hl g) p q ev = Ω≼Ω ev (λ l₁ l₂ w r → w) (λ d d′ md r B₁ B₂ w → ιup r)

  gtR : ∀ {a u w} → a ≼X gt u → u ⊲ w → a ≼X gt w
  gtR p hself = p
  gtR {w = hs y} p (hsuc q) = ≼X⊞ (gtR p q) _
  gtR {w = hl f} p (hlim n q) = ≼l n (gtR p q)
  gtR p (hLim {κ = ()} _ _)

  mutual
    GG : ∀ {a b} (p : LeAt hz a b) π₁ π₂ → hs hz ⊲ ap π₁ hz → hs hz ⊲ ap π₂ hz → GP (ap π₁ hz) (ap π₂ hz) →
         (∀ {u v} → Pr p π₁ π₂ u v → u ~ v) → GP (ap π₁ (leg a)) (ap π₂ (leg b))
    GG {b = b} Rel.z≤ π₁ π₂ o₁ o₂ base inc = gtR base (ap⊲ π₂ (z⊲ᴮ (leg b)))
    GG (Rel.s≤s {a = a} {b = b} p) π₁ π₂ o₁ o₂ base inc =
      subst₂ GP (sym (ap-s π₁ (leg a))) (sym (ap-s π₂ (leg b)))
        (⊞X (GG p π₁ π₂ o₁ o₂ base (λ r → inc (inj₂ r)))
            (nodeN (ap π₁ (leg a)) (ap π₂ (leg b)) (⊲ᴮ-tr o₁ (ap⊲ π₁ (z⊲ᴮ (leg a)))) (⊲ᴮ-tr o₂ (ap⊲ π₂ (z⊲ᴮ (leg b))))
               (inc (inj₁ (refl , refl)))))
    GG (Rel.≤s p) π₁ π₂ o₁ o₂ base inc = gtR (GG p π₁ π₂ o₁ o₂ base inc) (⊲-s π₂ hself)
    GG (Rel.≤l {g = g} n p) π₁ π₂ o₁ o₂ base inc =
      gtR (GG p π₁ (pre π₂ (Fs g) n) o₁ (⊲ᴮ-tr o₂ (pre-lo π₂ (Fs g) n)) (gtR base (pre-lo π₂ (Fs g) n)) inc) (⊲-L π₂ g n hself)
    GG (Rel.l≤l {f = f} {g = g} σ i h) π₁ π₂ o₁ o₂ base inc =
      subst₂ GP (sym (ap-l π₁ (Σ₀ (Fs f)))) (sym (ap-l π₂ (Σ₀ (Fs g))))
        (l≼l σ i (λ n → GGt σ i h π₁ π₂ o₁ o₂ base inc n))
    GG (Rel.≤Ω {κ = ()} _ _ _ _)
    GG (Rel.Ω≤Ω {κ = ()} _ _)

    GGb : ∀ {f g : ℕ → Cd} (σ : ℕ → ℕ) (i : Inc σ) (h : ∀ n → LeAt hz (f n) (g (σ n))) π₁ π₂ →
          hs hz ⊲ ap π₁ hz → hs hz ⊲ ap π₂ hz → GP (ap π₁ hz) (ap π₂ hz) →
          (∀ {u v} → Pr (Rel.l≤l σ i h) π₁ π₂ u v → u ~ v) → ∀ n →
          GP (ap (pre π₁ (Fs f) n) hz) (ap (pre π₂ (Fs g) (σ n)) hz)
    GGb {g = g} σ i h π₁ π₂ o₁ o₂ base inc zero = gtR base (pre-lo π₂ (Fs g) (σ 0))
    GGb {g = g} σ i h π₁ π₂ o₁ o₂ base inc (suc n) = gtR (GGt σ i h π₁ π₂ o₁ o₂ base inc n) (mon π₂ (Fs g) (<⇒<′ (i n)))

    GGt : ∀ {f g : ℕ → Cd} (σ : ℕ → ℕ) (i : Inc σ) (h : ∀ n → LeAt hz (f n) (g (σ n))) π₁ π₂ →
          hs hz ⊲ ap π₁ hz → hs hz ⊲ ap π₂ hz → GP (ap π₁ hz) (ap π₂ hz) →
          (∀ {u v} → Pr (Rel.l≤l σ i h) π₁ π₂ u v → u ~ v) → ∀ n →
          GP (ap π₁ (Σ₀ (Fs f) n)) (ap π₂ (Σ₀ (Fs g) (σ n)))
    GGt {f} {g} σ i h π₁ π₂ o₁ o₂ base inc n =
      subst₂ GP (pre-top π₁ (Fs f) n) (pre-top π₂ (Fs g) (σ n))
        (GG (h n) _ _ (⊲ᴮ-tr o₁ (pre-lo π₁ (Fs f) n)) (⊲ᴮ-tr o₂ (pre-lo π₂ (Fs g) (σ n)))
           (GGb σ i h π₁ π₂ o₁ o₂ base inc n) (λ r → inc (n , r)))

  G1 : GP (hs hz) (hs hz)
  G1 = Ω≼Ω {κ = κΩ} {κ′ = κΩ} ez (λ l₁ l₂ w r → nW-mono κΩ l₁ l₂ w (le← r))
         (λ d d′ md r B₁ B₂ w → ⊞X z≼ (ιup (le→ (shM w (le← r)))))

  gtP : gt (C a₀) ≼X gt (C b₀)
  gtP = GG p₀ π₀ π₀ hself hself G1 inj₂
```

## §5 嵌入一层再折回

```agda
  U-oneX : ∀ b y → hs hz ≼X U b y
  U-oneX b hz = s≼s z≼
  U-oneX b (hs y) = ≼l 0 (U-oneX b y)
  U-oneX b (hl f) = ≼l 0 (U-oneX b (f 0))
  U-oneX b (hΩ κ g) = ≼Ω hz Rel.z≤ tt (λ B → U-oneX b (g (psh (P κ) B (toX κ hz))))

  ≼X⊞ˡ : ∀ {a y} z → a ≼X y → a ≼X z ⊞ y
  ≼X⊞ˡ z z≼ = z≼
  ≼X⊞ˡ z (s≼s p) = s≼s (≼X⊞ˡ z p)
  ≼X⊞ˡ z (≼s p) = ≼s (≼X⊞ˡ z p)
  ≼X⊞ˡ z (l≼l σ i h) = l≼l σ i (λ n → ≼X⊞ˡ z (h n))
  ≼X⊞ˡ z (≼l n p) = ≼l n (≼X⊞ˡ z p)
  ≼X⊞ˡ z (≼Ω c bd mc p) = ≼Ω c bd mc (λ B → ≼X⊞ˡ z (p B))
  ≼X⊞ˡ z (Ω≼Ω ev wl h) = Ω≼Ω ev wl (λ d d′ md r B₁ B₂ w → ≼X⊞ˡ z (h d d′ md r B₁ B₂ w))

  mulX : ∀ {a a′} → a ≼X a′ → ∀ n → mul a n ≼X mul a′ n
  mulX p zero = p
  mulX p (suc n) = ⊞X (mulX p n) p

  Σge : ∀ {a} (G : ℕ → HX) n → a ≼X G n → a ≼X Σ⁺ G n
  Σge G zero p = p
  Σge G (suc n) p = ≼X⊞ˡ (Σ⁺ G n) p

  Σidx : ∀ {a} (G : ℕ → HX) {i j} → i ≤′ j → a ≼X Σ⁺ G i → a ≼X Σ⁺ G j
  Σidx G ≤′-refl p = p
  Σidx G (≤′-step q) p = ≼X⊞ (Σidx G q p) _

  Σstep : ∀ {a x} (G : ℕ → HX) {i j} → suc i ≤′ j → a ≼X Σ⁺ G i → x ≼X G j → a ⊞ x ≼X Σ⁺ G j
  Σstep G ≤′-refl p q = ⊞X p q
  Σstep G (≤′-step r) p q = ⊞X (Σidx G (lw′ r) p) q
    where
    lw′ : ∀ {i j} → suc i ≤′ j → i ≤′ j
    lw′ ≤′-refl = ≤′-step ≤′-refl
    lw′ (≤′-step p) = ≤′-step (lw′ p)

  Σ≼X : ∀ (F G : ℕ → HX) σ → Inc σ → (∀ n → F n ≼X G (σ n)) → ∀ n → Σ⁺ F n ≼X Σ⁺ G (σ n)
  Σ≼X F G σ i h zero = Σge G (σ 0) (h 0)
  Σ≼X F G σ i h (suc n) = Σstep G (<⇒<′ (i n)) (Σ≼X F G σ i h n) (h (suc n))

  UX : ∀ b {x y} → x ≼X y → U b x ≼X U b y
  UX b {y = y} z≼ = U-oneX b y
  UX b (s≼s p) = l≼l (λ n → n) idInc (mulX (UX b p))
  UX b (≼s p) = ≼l 0 (UX b p)
  UX b (l≼l σ i h) = l≼l σ i (Σ≼X _ _ σ i i′ )
    where i′ = λ n → UX b (h n)
  UX b {y = hl g} (≼l n p) = ≼l n (Σge (λ k → U b (g k)) n (UX b p))
  UX b (≼Ω c bd mc p) = ≼Ω c bd mc (λ B → UX b (p B))
  UX b (Ω≼Ω ev wl h) = Ω≼Ω ev wl (λ d d′ md r B₁ B₂ w → UX b (h d d′ md r B₁ B₂ w))
```

## §6 `P2`

$k_R\,b$ 是第 0 层目标, 界 $b$, 世界 $\mathrm{nxt}_0(W_0\boxplus\mathrm{leg}\,b)$, 输入 $U(\mathrm{gt}(W_0\boxplus\mathrm{leg}\,b))$.

```agda
  open ThmX tp

  Bz : ∀ {x y} → LeAt hz x y → Ch.Bx hz hz x y
  Bz {x} {y} p = moZ y , Rel.z≤ , le→ p

  kR≼ : LeAt hz (kR a₀) (kR b₀)
  kR≼ = le← (crossX (wf bX hz) (wf bX hz) {nW κΩ {W₀} tt a₀} {nW κΩ {W₀} tt b₀} (lgW κΩ {W₀} tt a₀) (lgW κΩ {W₀} tt b₀) (nW-mono κΩ {W₀} {W₀} tt tt (L.≤-refl hz W₀) p₀)
           (ptW κΩ {W₀} tt (z⊲ᴮ W₀) a₀) (ptW κΩ {W₀} tt (z⊲ᴮ W₀) b₀) ez (Bz p₀)
           (U topL (gt (C b₀))) (pgW κΩ {W₀} tt (proj₂ nd₀) a₀) (pgW κΩ {W₀} tt (proj₂ nd₀) b₀)
           (MoX-U topL (gt (C b₀)) (MoX-gt (C b₀))) (UX topL gtP))

  kL≼ : LeAt hz (kL a₀) (kL b₀)
  kL≼ = le← (crossX (wf bX hz) (wf bX hz) {nW κΩ {W₀} tt a₀} {nW κΩ {W₀} tt b₀} (lgW κΩ {W₀} tt a₀) (lgW κΩ {W₀} tt b₀) (nW-mono κΩ {W₀} {W₀} tt tt (L.≤-refl hz W₀) p₀)
           (ptW κΩ {W₀} tt (z⊲ᴮ W₀) a₀) (ptW κΩ {W₀} tt (z⊲ᴮ W₀) b₀) ez (Bz p₀)
           (gt (C b₀)) (pgW κΩ {W₀} tt pgL a₀) (pgW κΩ {W₀} tt pgL b₀)
           (MoX-gt (C b₀)) gtP)

P2-thm : P2
P2-thm b₁ b₂ p = Core.kR≼ p

P2L-thm : ∀ b₁ b₂ → LeAt hz b₁ b₂ → LeAt hz (kL b₁) (kL b₂)
P2L-thm b₁ b₂ p = Core.kL≼ p

goal : asuc (toA TX) TL.≤ toA TU1
goal = goal-P2 P2-thm
```

## 结论 (按档)

- **[条件定理, 条件: `Cd` 上的 UIP]** `Core.tp` (地板律), **`Core.gtP`** (地板的分支跨层相关), `Core.UX`; **`P2-thm`**: ValXP1 的 `P2`; **`P2L-thm`**; **`goal`**: $\mathrm{TX}+1\le\mathrm{TU}\,1$ (`TLRuleSpec._≤_`).
