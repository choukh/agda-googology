# 第 1 层的下界经层号嵌入 (搬到收缩见证的折叠)

验收文件. [YiL1Emb](YiL1Emb.lagda.md) 逐字搬到 [YiWitFold](YiWitFold.lagda.md): 只换模块名与导入, 链内模块换成 `YiWit` 的搬运件, 塔的 `Lw-tw`, `lgl→Lw`, `Tw`, `T⁺ʷ`, `TΛ` 取 `WF` (YiWitFold), 折叠 `W.Ψ` 仍是 YiDlFold 的 `Fold dl`. 定理与原文同名; 下文的讲解是原文.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWitL1Emb where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore hiding (Le)
open import OCF.Lean.YiNextBase
import OCF.Lean.YiLamFold as WL
import OCF.Lean.YiWitFold as WF
import OCF.Lean.YiNextAcc as NA
open NA using (_⊴_; z⊴; s⊴s; ⊴s; ⊴l; l⊴; ⊴b; nd; em⊴; u⊴)
open import OCF.Lean.YiWitVOne using (Ψ₀)
open import OCF.Lean.YiWitShpOne using (σA)
open import OCF.Lean.YiWitShpSq using (Bq)
open import OCF.Lean.YiWitShpEps using (Tψ; K₁; Xε≼Bq)
open import OCF.Lean.YiWitShpTwo using (σB)
open import OCF.Lean.YiWitL1Stmt using (F₁)
open import OCF.Lean.YiWitL1Read using (T₁; κ₁; foldM₁; R₁; lowR)
import OCF.Lean.YiLeanCore as M
import OCF.Lean.YiLeanValFin as MV
open import OCF.Lean.YiLeanValRel using
  ( Corr; cz; RelF; zr; ssr; sr; lr; llr; br; ndr; emr; tnr; tlr; ur; us )
open import OCF.Lean.YiNextValRel using (RR; rs; rl; rc; rt; read≅)
open import OCF.Lean.YiNextValFin using (toM; toM-R; toM-lgl; cp⊑ⁿ)
open import OCF.Align.YiLvValBase using (γ)
open import OCF.Align.YiLvVal2 using (ℓ₁)
open import OCF.Align.YiBtValBT using (module D)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; ⊑→≼; s≼s; ≼l; l≼)
open import OCF.Align.BTBOValAbsorb using (lim-≼⁻)
import OCF.Align.BTBOFullLe as BL
open BL using (cl0)
open import OCF.Align.BTBOFullEmb using (PEmb; module PE)
import OCF.Align.Stage2 as S2
```

## 1 参照一侧的比较连同主线的关系换成 `NA._⊴_`

`TB₁`: 参照 x ≤ y (`Le`, 对任一层号关系 E), y 与主线的树 t 相关 (`RelF 1`), t 与一致折叠的树 t′ 互模拟, 则 x ⊴ θ + t′. x 取第 0, 1 层 (`TB₀`, `TB₁`); `top` 落到 `topS` (`TBt`), 嵌入的第 0 层树 (`TBe`, `LeEm`).

```agda
module TBM (E : L.Ordᴵ → L.Ordᴵ → Set)
  (resp : ∀ {a b a′ b′} → E a b → a L.≅ᴵ a′ → b L.≅ᴵ b′ → E a′ b′) where
  open BL.LeE E resp ⊥

  refl₀ : ∀ (z : L.Ordᶜ L.zero) → Le z z
  refl₀ L.zero = Lz
  refl₀ (L.suc z) = Ls (refl₀ z)
  refl₀ (L.lim f) = Lll (λ n → Llr n (refl₀ (f n)))
  refl₀ (L.limᵢ () f)
  refl₀ (L.up () x)

  LeEm₀ : ∀ θ {x : L.Ordᶜ L.zero} {y b : L.Ordᶜ L.zero} → Le x y → y ≼ b → ∀ a → b ≡ NA.read a →
    x ⊴ plus (suc zero) θ (G.em tt a)
  LeEm₁ : ∀ θ {x : L.Ordᶜ ℓ₁} {y b : L.Ordᶜ L.zero} → Le x y → y ≼ b → ∀ a → b ≡ NA.read a →
    x ⊴ plus (suc zero) θ (G.em tt a)

  LeEm₀ θ Lz q a e = z⊴
  LeEm₀ θ (Lll h) q a e = l⊴ (λ n → LeEm₀ θ (h n) q a e)
  LeEm₀ θ (Ls d) (s≼s q) (G.suc a) refl = s⊴s (LeEm₀ θ d q a refl)
  LeEm₀ θ (Ls d) (s≼s q) G.top refl = s⊴s (LeEm₀ θ d q G.zero refl)
  LeEm₀ θ (Ls d) (≼l n q) (G.lim f) refl = ⊴l n (LeEm₀ θ (Ls d) q (f n) refl)
  LeEm₀ θ (Lsr d) (s≼s q) (G.suc a) refl = ⊴s (LeEm₀ θ d q a refl)
  LeEm₀ θ (Lsr d) (s≼s q) G.top refl = ⊴s (LeEm₀ θ d q G.zero refl)
  LeEm₀ θ (Lsr d) (≼l n q) (G.lim f) refl = ⊴l n (LeEm₀ θ (Lsr d) q (f n) refl)
  LeEm₀ θ (Llr n d) (l≼ h) a e = LeEm₀ θ d (h n) a e
  LeEm₀ θ (Llr n d) (≼l k q) (G.lim f) refl = ⊴l k (LeEm₀ θ (Llr n d) q (f k) refl)

  LeEm₁ θ Lz q a e = z⊴
  LeEm₁ θ (Lll h) q a e = l⊴ (λ n → LeEm₁ θ (h n) q a e)
  LeEm₁ θ (Lul {r = L.zero} d) q a e = u⊴ (LeEm₀ θ d q a e)
  LeEm₁ θ (Ls d) (s≼s q) (G.suc a) refl = s⊴s (LeEm₁ θ d q a refl)
  LeEm₁ θ (Ls d) (s≼s q) G.top refl = s⊴s (LeEm₁ θ d q G.zero refl)
  LeEm₁ θ (Ls d) (≼l n q) (G.lim f) refl = ⊴l n (LeEm₁ θ (Ls d) q (f n) refl)
  LeEm₁ θ (Lsr d) (s≼s q) (G.suc a) refl = ⊴s (LeEm₁ θ d q a refl)
  LeEm₁ θ (Lsr d) (s≼s q) G.top refl = ⊴s (LeEm₁ θ d q G.zero refl)
  LeEm₁ θ (Lsr d) (≼l n q) (G.lim f) refl = ⊴l n (LeEm₁ θ (Lsr d) q (f n) refl)
  LeEm₁ θ (Llr n d) (l≼ h) a e = LeEm₁ θ d (h n) a e
  LeEm₁ θ (Llr n d) (≼l k q) (G.lim f) refl = ⊴l k (LeEm₁ θ (Llr n d) q (f k) refl)

  TBe₀ : ∀ θ {k} {x : L.Ordᶜ L.zero} {y : L.Ordᶜ k} {a a′} → Le x y → RelF (M.suc M.zero) y (M.G.em tt a) →
    RR M.zero zero a a′ → x ⊴ plus (suc zero) θ (G.em tt a′)
  TBe₁ : ∀ θ {k} {x : L.Ordᶜ ℓ₁} {y : L.Ordᶜ k} {a a′} → Le x y → RelF (M.suc M.zero) y (M.G.em tt a) →
    RR M.zero zero a a′ → x ⊴ plus (suc zero) θ (G.em tt a′)

  TBe₀ θ {a′ = a′} e (emr {j = L.zero} p) rr = LeEm₀ θ e (≼-trans p (≅→≼ (read≅ rr))) a′ refl
  TBe₀ θ e (emr {j = L.suc _} ()) rr
  TBe₀ θ e (emr {j = L.lim _ _} ()) rr
  TBe₀ θ Lz d rr = z⊴
  TBe₀ θ (Lll h) d rr = l⊴ (λ n → TBe₀ θ (h n) d rr)
  TBe₀ θ (Llr n e) (llr h) rr = TBe₀ θ e (h n) rr
  TBe₀ θ (Lur {r = L.zero} e) (ur d) rr = TBe₀ θ e d rr
  TBe₀ θ (Lur {r = L.self n} e) (us d) rr = TBe₀ θ e d rr

  TBe₁ θ {a′ = a′} e (emr {j = L.zero} p) rr = LeEm₁ θ e (≼-trans p (≅→≼ (read≅ rr))) a′ refl
  TBe₁ θ e (emr {j = L.suc _} ()) rr
  TBe₁ θ e (emr {j = L.lim _ _} ()) rr
  TBe₁ θ Lz d rr = z⊴
  TBe₁ θ (Lll h) d rr = l⊴ (λ n → TBe₁ θ (h n) d rr)
  TBe₁ θ (Lul {r = L.zero} e) d rr = u⊴ (TBe₀ θ e d rr)
  TBe₁ θ (Llr n e) (llr h) rr = TBe₁ θ e (h n) rr
  TBe₁ θ (Lur {r = L.zero} e) (ur d) rr = TBe₁ θ e d rr
  TBe₁ θ (Lur {r = L.self n} e) (us d) rr = TBe₁ θ e d rr

  TBt₀ : ∀ θ {k} {x : L.Ordᶜ L.zero} {y : L.Ordᶜ k} → Le x y →
    RelF (M.suc M.zero) y (M.G.lc (inj₁ tt) (λ a → M.G.em tt a)) → x ⊴ plus (suc zero) θ G.top
  TBt₁ : ∀ θ {k} {x : L.Ordᶜ ℓ₁} {y : L.Ordᶜ k} → Le x y →
    RelF (M.suc M.zero) y (M.G.lc (inj₁ tt) (λ a → M.G.em tt a)) → x ⊴ plus (suc zero) θ G.top

  TBt₀ θ e (br d) = ⊴b (TBe₀ θ e d rt)
  TBt₀ θ Lz d = z⊴
  TBt₀ θ (Lll h) d = l⊴ (λ n → TBt₀ θ (h n) d)
  TBt₀ θ (Llr n e) (llr h) = TBt₀ θ e (h n)
  TBt₀ θ (Lir H) (ndr cz hy) = ⊴b (TBe₀ θ (H (L.Ω L.zero) cl0) (hy (L.Ω L.zero) M.G.top (≼-refl _)) rt)
  TBt₀ θ (Lb () k nz H) d
  TBt₀ θ (Lur {r = L.zero} e) (ur d) = TBt₀ θ e d
  TBt₀ θ (Lur {r = L.self n} e) (us d) = TBt₀ θ e d

  TBt₁ θ e (br d) = ⊴b (TBe₁ θ e d rt)
  TBt₁ θ Lz d = z⊴
  TBt₁ θ (Lll h) d = l⊴ (λ n → TBt₁ θ (h n) d)
  TBt₁ θ (Lul {r = L.zero} e) d = u⊴ (TBt₀ θ e d)
  TBt₁ θ (Llr n e) (llr h) = TBt₁ θ e (h n)
  TBt₁ θ (Lii {p = L.zero} ej h) (ndr cz hy) =
    nd (λ z a q → TBe₁ θ (h z z (Le→L _ (refl₀ z))) (hy z (toM a) (lowR a q)) (toM-R a))
  TBt₁ θ (Lii {p = L.suc ()} ej h) d
  TBt₁ θ (Lir H) (ndr cz hy) = ⊴b (TBe₁ θ (H (L.Ω L.zero) cl0) (hy (L.Ω L.zero) M.G.top (≼-refl _)) rt)
  TBt₁ θ (Lb () k nz H) d
  TBt₁ θ (Lur {r = L.zero} e) (ur d) = TBt₁ θ e d
  TBt₁ θ (Lur {r = L.self n} e) (us d) = TBt₁ θ e d

  TB₀ : ∀ θ {k} {x : L.Ordᶜ L.zero} {y : L.Ordᶜ k} {t t′} → Le x y → RelF (M.suc M.zero) y t →
    RR (M.suc M.zero) (suc zero) t t′ → x ⊴ plus (suc zero) θ t′
  TB₁ : ∀ θ {k} {x : L.Ordᶜ ℓ₁} {y : L.Ordᶜ k} {t t′} → Le x y → RelF (M.suc M.zero) y t →
    RR (M.suc M.zero) (suc zero) t t′ → x ⊴ plus (suc zero) θ t′

  TB₀ θ e (sr d) (rs rr) = ⊴s (TB₀ θ e d rr)
  TB₀ θ e (lr n d) (rl rr) = ⊴l n (TB₀ θ e d (rr n))
  TB₀ θ e (br {r = inj₁ _} d) (rc {r′ = inj₁ _} _ h) = ⊴b (TB₀ θ e d (h M.G.top G.top rt))
  TB₀ θ e (tnr tt d) rt = TBt₀ θ e d
  TB₀ θ e (tlr i () d) rr
  TB₀ θ e (emr d) ()
  TB₀ θ Lz d rr = z⊴
  TB₀ θ (Lll h) d rr = l⊴ (λ n → TB₀ θ (h n) d rr)
  TB₀ θ (Ls e) (ssr d) (rs rr) = s⊴s (TB₀ θ e d rr)
  TB₀ θ (Lsr e) (ssr d) (rs rr) = ⊴s (TB₀ θ e d rr)
  TB₀ θ (Llr n e) (llr h) rr = TB₀ θ e (h n) rr
  TB₀ θ (Lir H) (ndr {r = inj₁ _} cz hy) (rc {r′ = inj₁ _} _ hh) =
    ⊴b (TB₀ θ (H (L.Ω L.zero) cl0) (hy (L.Ω L.zero) M.G.top (≼-refl _)) (hh M.G.top G.top rt))
  TB₀ θ (Lb () k nz H) d rr
  TB₀ θ (Lur {r = L.zero} e) (ur d) rr = TB₀ θ e d rr
  TB₀ θ (Lur {r = L.self n} e) (us d) rr = TB₀ θ e d rr

  TB₁ θ e (sr d) (rs rr) = ⊴s (TB₁ θ e d rr)
  TB₁ θ e (lr n d) (rl rr) = ⊴l n (TB₁ θ e d (rr n))
  TB₁ θ e (br {r = inj₁ _} d) (rc {r′ = inj₁ _} _ h) = ⊴b (TB₁ θ e d (h M.G.top G.top rt))
  TB₁ θ e (tnr tt d) rt = TBt₁ θ e d
  TB₁ θ e (tlr i () d) rr
  TB₁ θ e (emr d) ()
  TB₁ θ Lz d rr = z⊴
  TB₁ θ (Lll h) d rr = l⊴ (λ n → TB₁ θ (h n) d rr)
  TB₁ θ (Lul {r = L.zero} e) d rr = u⊴ (TB₀ θ e d rr)
  TB₁ θ (Ls e) (ssr d) (rs rr) = s⊴s (TB₁ θ e d rr)
  TB₁ θ (Lsr e) (ssr d) (rs rr) = ⊴s (TB₁ θ e d rr)
  TB₁ θ (Llr n e) (llr h) rr = TB₁ θ e (h n) rr
  TB₁ θ (Lii {p = L.zero} ej h) (ndr {r = inj₁ _} cz hy) (rc {r′ = inj₁ _} _ hh) =
    nd (λ z a q → TB₁ θ (h z z (Le→L _ (refl₀ z))) (hy z (toM a) (lowR a q)) (hh (toM a) a (toM-R a)))
  TB₁ θ (Lii {p = L.suc ()} ej h) d rr
  TB₁ θ (Lir H) (ndr {r = inj₁ _} cz hy) (rc {r′ = inj₁ _} _ hh) =
    ⊴b (TB₁ θ (H (L.Ω L.zero) cl0) (hy (L.Ω L.zero) M.G.top (≼-refl _)) (hh M.G.top G.top rt))
  TB₁ θ (Lb () k nz H) d rr
  TB₁ θ (Lur {r = L.zero} e) (ur d) rr = TB₁ θ e d rr
  TB₁ θ (Lur {r = L.self n} e) (us d) rr = TB₁ θ e d rr
```

## 2 嵌入改成固定 0 与 1

```agda
Big : L.Ordᴵ → Set
Big c = (c L.≅ᴵ L.zero → ⊥) × (c L.≅ᴵ L.suc L.zero → ⊥)

data Sh : L.Ordᴵ → Set where
  s0 : Sh L.zero
  s1 : Sh (L.suc L.zero)
  sB : ∀ {c} → Big c → Sh c

sh : ∀ c → Sh c
sh L.zero = s0
sh (L.suc L.zero) = s1
sh (L.suc (L.suc c)) = sB ((λ ()) , λ { (L.s≅ ()) })
sh (L.suc (L.lim f s)) = sB ((λ ()) , λ { (L.s≅ ()) })
sh (L.lim f s) = sB ((λ ()) , (λ ()))

z≺1 : L.zero L.≺ᴵ L.suc L.zero
z≺1 = L.via L.z≅ L.zero

module Fix01 {a b : L.Ordᴵ} (P : PEmb a b)
  (h1 : ∀ {c} (r : c L.≺ᴵ a) → L.suc L.zero L.≺ᴵ PEmb.map P r) where
  mp : ∀ {c} → Sh c → c L.≺ᴵ a → L.Ordᴵ
  mp s0 r = L.zero
  mp s1 r = L.suc L.zero
  mp (sB _) r = PEmb.map P r

  map′ : ∀ {c} → c L.≺ᴵ a → L.Ordᴵ
  map′ {c} r = mp (sh c) r

  bnd′ : ∀ {c} (r : c L.≺ᴵ a) → map′ r L.≺ᴵ b
  bnd′ {c} r with sh c
  ... | s0 = L.≺ᴵ-trans z≺1 (L.≺ᴵ-trans (h1 r) (PEmb.bnd P r))
  ... | s1 = L.≺ᴵ-trans (h1 r) (PEmb.bnd P r)
  ... | sB _ = PEmb.bnd P r

  mono′ : ∀ {c d} (r : c L.≺ᴵ a) (s : d L.≺ᴵ a) → c L.≺ᴵ d → map′ r L.≺ᴵ map′ s
  mono′ {c} {d} r s lt with sh c | sh d
  ... | s0 | s0 = ⊥-elim (L.≺ᴵ-irrefl lt)
  ... | s0 | s1 = z≺1
  ... | s0 | sB _ = L.≺ᴵ-trans z≺1 (h1 s)
  ... | s1 | s0 = ⊥-elim (no0 lt)
    where no0 : ∀ {x} → x L.≺ᴵ L.zero → ⊥
          no0 (L.via e ())
  ... | s1 | s1 = ⊥-elim (L.≺ᴵ-irrefl lt)
  ... | s1 | sB _ = h1 s
  ... | sB bc | s0 = ⊥-elim (no0 lt)
    where no0 : ∀ {x} → x L.≺ᴵ L.zero → ⊥
          no0 (L.via e ())
  ... | sB bc | s1 = ⊥-elim (no1 lt)
    where no1 : c L.≺ᴵ L.suc L.zero → ⊥
          no1 (L.via e L.zero) = proj₁ bc e
          no1 (L.via e (L.suc ()))
  ... | sB _ | sB _ = PEmb.mono P r s lt

  coh′ : ∀ {c d} (r : c L.≺ᴵ a) (s : d L.≺ᴵ a) → c L.≅ᴵ d → map′ r L.≅ᴵ map′ s
  coh′ {c} {d} r s e with sh c | sh d
  ... | s0 | s0 = L.z≅
  ... | s0 | s1 = ⊥-elim (z≠1 e)
    where z≠1 : L.zero L.≅ᴵ L.suc L.zero → ⊥
          z≠1 ()
  ... | s0 | sB bd = ⊥-elim (proj₁ bd (L.≅ᴵ-sym e))
  ... | s1 | s0 = ⊥-elim (o≠0 e)
    where o≠0 : L.suc L.zero L.≅ᴵ L.zero → ⊥
          o≠0 ()
  ... | s1 | s1 = L.s≅ L.z≅
  ... | s1 | sB bd = ⊥-elim (proj₂ bd (L.≅ᴵ-sym e))
  ... | sB bc | s0 = ⊥-elim (proj₁ bc e)
  ... | sB bc | s1 = ⊥-elim (proj₂ bc e)
  ... | sB _ | sB _ = PEmb.coh P r s e

  P′ : PEmb a b
  P′ = record { map = map′ ; bnd = bnd′ ; mono = mono′ ; coh = coh′ }

  E11 : L.suc L.zero L.≺ᴵ a → PE.E P′ (L.suc L.zero) (L.suc L.zero)
  E11 r₁ = PE.sub r₁ (L.≅ᴵ-refl (L.suc L.zero))
```

## 3 目标层 1 上的下界经嵌入 (嵌入在 1 上取 1)

```agda
lit1 : ∀ {κ} → L.suc L.zero L.≺ᴵ κ → L.suc L.zero L.<ᴵ κ
lit1 (L.via (L.s≅ L.z≅) q) = q

lower₁ᴱ : ∀ a (l : Lgl zero a) {L₀} (P : PEmb L₀ (κ₁ a l)) (r₁ : L.suc L.zero L.≺ᴵ L₀) →
  PEmb.map P r₁ L.≅ᴵ L.suc L.zero →
  ∀ {a₀ ℓ} → a₀ L.≅ᴵ L₀ → ∀ (p : L.suc L.zero L.<ᴵ ℓ) (σ : L.Simᴵ a₀ ℓ) θ →
  L.ψ p σ (L.Ω a₀) ⊴ plus (suc zero) θ (T₁ a l)
lower₁ᴱ a l P r₁ e11 e p σ θ =
  T.TB₁ θ (LL.Le-ψ (PE.sub r₁ (L.≅ᴵ-sym e11)) p σ p′ (λ r → r) (LL.Le-Ω (PE.top e (L.≅ᴵ-refl _))))
    (foldM₁ (toM a) (toM-lgl a l) (MV.corr-read (toM a) (MV.HS-read (toM a) (toM-lgl a l))) p′ (λ r → r))
    (R₁ a l)
  where
  module LW = BL.LeE (PE.E P) (PE.E-resp P) ⊥
  module LL = LW.WithLaws (PE.ℒ P)
  module T = TBM (PE.E P) (PE.E-resp P)
  p′ : L.suc L.zero L.<ᴵ κ₁ a l
  p′ = lit1 (L.≺ᴵ-respˡ (L.≅ᴵ-sym e11) (PEmb.bnd P r₁))
```

## 4 `Base₁` 的第 0 项与部件

第 0 项由 [YiShpEps](YiShpEps.lagda.md) 的 `Xε≼Bq` (F₁ 0 与 γ 1 1 互模拟). 其余各项在 [YiL1Base](YiL1Base.lagda.md).

```agda
base₁-0 : ∀ ζ → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (F₁ 0)) ≼ NA.read (Ψ₀ (Bq ζ))
base₁-0 ζ = ≼-trans
  (≅→≼ (L.ψ⁰-≅ (L.add-≅ {σ = σA} {σ′ = σA} (L.Ω-refl S2.ℓ₀)
    (L.ψ-≅ {p = σB L.zero} {σ = λ q → L.lim 0 q} {p′ = L.zero} {σ′ = λ q → L.suc q}
      (L.≅ᴵ-refl (L.suc L.zero)) (L.Ω-refl (L.suc L.zero))))))
  (lim-≼⁻ (Xε≼Bq ζ) 1)

one≺ : ∀ a h → L.suc L.zero L.≺ᴵ L.toLevel (L.ψ⁰ (L.Ω a)) h
one≺ L.zero h = L.via (L.s≅ L.z≅) (L.lim 2 L.zero)
one≺ (L.suc a) h = L.≺-lim 0 (one≺ a _)
one≺ (L.lim f s) h = L.≺-lim 0 (one≺ (f 0) _)

⊴-cp : ∀ {k} {x : L.Ordᶜ k} {η η′} → x ⊴ η → Cp (suc zero) η η′ → x ⊴ η′
⊴-dn : ∀ {k} {x : L.Ordᶜ k} {η} η′ → x ⊴ η → Dn (suc zero) η η′ → x ⊴ η′
⊴-cp h (inj₁ refl) = h
⊴-cp h (inj₂ p) = ⊴-dn _ h p
⊴-dn (G.suc η′) h p = ⊴s (⊴-cp h p)
⊴-dn (G.lim f) h (n , p) = ⊴l n (⊴-cp h p)
⊴-dn (G.lc (inj₁ _) g) h p = ⊴b (⊴-cp h p)
⊴-dn (G.lc (inj₂ ()) g) h p
⊴-dn {η = G.em _ a} (G.em _ d) z⊴ (refl , p) = z⊴
⊴-dn {η = G.em _ a} (G.em _ d) (l⊴ h) (refl , p) = l⊴ (λ n → ⊴-dn (G.em tt d) (h n) (refl , p))
⊴-dn {η = G.em _ a} (G.em _ d) (em⊴ q) (refl , p) = em⊴ (≼-trans q (⊑→≼ (NA.read a) (cp⊑ⁿ a d (inj₂ p))))
⊴-dn {η = G.em _ a} (G.em _ d) (u⊴ h) (refl , p) = u⊴ (⊴-dn (G.em tt d) h (refl , p))

ℓ₀≅ : ∀ n → S2.ℓ₀ L.[ n ]ᴵ L.≅ᴵ D.L n
ℓ₀≅ n = L.≅ᴵ-refl _
```
