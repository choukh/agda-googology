# 紧的界: 落成字面闭包, 界的公式, 界的来源

> 不含记号. 结论写在 [GuardTight](GuardTight.lagda.md). 这是 [ScafLadderTop](ScafLadderTop.lagda.md) 的 `head-lit`, `bound-free` 在 `LG` 上的形式, 对**每一个位置**, 不只第一个闭包.
>
> - `land-tp`, `land-t0`, `head-goC`: 闭包在目标之下 (或目标 0), 证据齐全时, 折叠的头是字面的 `oŝ c₀`. $c_0=$ `cOf w`. 任何位置, 任何世界, 任何地板.
> - `cOf-ub`, `cOf-lb₁`, `cOf-lb₂`: $c_0$ 的公式. 模前序 $c_0=\sup(c_2,\{K+1\})$, $K$ 跑遍地板 $\varphi$.
> - `floors`: $\varphi$ 的项只有三个来源: 同键的活帧, 帧的节点自己路径上的同键分支, **目标路径上的同键分支**, 闭包自己路径上的同键分支. 地板是 `pr` 的像. 没有别的.
> - `nf-tail`, `tail-lb`, `tail-ub`, `bound-free`: $a+\eta$ 的闭包, 目标 $a+b$, 路径穿过任意分支 $\tau$: 规范化之后界模前序就是 $b+1$, 不看 $\tau$. **对一切 $\tau$, 对一切 $b$ 的定理**, 不是有限测试.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardTightBound where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.GuardTightCum using (Ordᴵ; _<ᴵ_; _⊑ᴵ_; _≺ᴵ_; _≅ᴵ_; via; Simᴵ; sim; Ordᶜ; add; ≅ᴵ-refl; ⊑ᴵ-trans; zero; suc; lim; z≅; s⊑; z⊑)
open import OCF.Free.Floor using (Flr; fz; fk; fb; _⊔_; Ev; InF; ink; inb; inl; inr; Dem; isB; bound; Bd; Fc; evF; iF; FM; ubd)
open import OCF.Align.GuardTightLv
open Lv Dom₀
open import OCF.Align.GuardTightTab Dom₀ using (kdec; _⊙_; adm⊙; Strict; stCp; st⊙; toCp)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTree
import OCF.Align.GuardTightUni as Uni
private module U = Uni Dom₀
open U using (rb₁; em)
open import OCF.Align.GuardTightRd
```

## §1 落成字面闭包 (每一个位置)

```agda
module Land (c : LG) (wf : WFˢ c) (sf : c ≈ c) (tc : Tc c) where
  open Fold c wf sf tc

  head-goC : ∀ {t π ρ c₁ t₁ g₁ c₂ t₂ g₂} (E : Ents) (T : Tg E t) (st : St E ρ π) (P : Cp (lc c₂ t₂ g₂) c) (k : Lk (lc c₂ t₂ g₂) (lc c₁ t₁ g₁)) (ap : AdmC (tab E) P)
             (x : O c π) (g : ∀ η e → O c (π ∪ tk (frm c₁ t₁ g₁ η e)))
             (SS : Sel.S P E ap (λ F → St F ρ π × (Tg F t × AdmC (tab F) P))) (w : Sel.Sl P E ap (Sel.φ SS)) →
             Σ (O t ρ) λ x′ → Σ ((η : Ordᴵ) → cOf w ⊑ᴵ η → O t ρ) λ g′ → goC E T st P k ap x g SS w ≡ oŝ (cOf w) x′ g′
  head-goC E T st P k ap x g SS (Sel.emp f) = _ , _ , refl
  head-goC E T st P k ap x g SS (Sel.sel ℓ K₀ a q y i dm) = _ , _ , refl

  -- 目标在闭包之下
  land-tp : ∀ {t π ρ c₁ t₁ g₁ c₂ t₂ g₂} (E : Ents) {q : t < c} {aq : Adm (tab E) q} (st : St E ρ π) (P : Cp (lc c₂ t₂ g₂) c) (k : Lk (lc c₂ t₂ g₂) (lc c₁ t₁ g₁)) (cv : AdmC (cov π) P) (ap : AdmC (tab E) P)
            (x : O c π) (g : ∀ η e → O c (π ∪ tk (frm c₁ t₁ g₁ η e))) →
            Vis.cmpK st wf sf P q cv aq ≡ Vis.kb → Vis.toTabC st P cv ≡ just ap →
            ψ E (tp q aq) st (ocl P k cv x g) ≡ goC E (tp q aq) st P k ap x g (SSc E (tp q aq) st P ap) (Sel.wit (SSc E (tp q aq) st P ap))
  land-tp E st P k cv ap x g e₁ e₂ rewrite e₁ | e₂ = refl

  -- 目标 0
  land-t0 : ∀ {π ρ c₁ t₁ g₁ c₂ t₂ g₂} (E : Ents) (st : St E ρ π) (P : Cp (lc c₂ t₂ g₂) c) (k : Lk (lc c₂ t₂ g₂) (lc c₁ t₁ g₁)) (cv : AdmC (cov π) P) (ap : AdmC (tab E) P)
            (x : O c π) (g : ∀ η e → O c (π ∪ tk (frm c₁ t₁ g₁ η e))) →
            Vis.toTabC st P cv ≡ just ap →
            ψ E t0 st (ocl P k cv x g) ≡ goC E t0 st P k ap x g (SSc E t0 st P ap) (Sel.wit (SSc E t0 st P ap))
  land-t0 E st P k cv ap x g e₂ rewrite e₂ = refl
```

## §2 $c_0$ 的公式

```agda
  evIn : ∀ {K φ ℓ} → Ev ℓ φ → (k : InF K φ) → isB k ≡ false → K <ᴵ ℓ
  evIn e ink r = e zero
  evIn e (inl k) r = evIn (proj₁ e) k r
  evIn e (inr k) r = evIn (proj₂ e) k r

  demS : ∀ {K φ η} (k : InF K φ) → K ≺ᴵ η → Dem η k
  demS ink s = inj₁ s
  demS inb s = ≺→⊑ᴵ s
  demS (inl k) s = demS k s
  demS (inr k) s = demS k s

  cOf-ub : ∀ {c₂ t₂ g₂} {P : Cp (lc c₂ t₂ g₂) c} {E ap φ} (w : Sel.Sl P E ap φ) {η} → c₂ ⊑ᴵ η → (∀ {K} → InF K φ → K ≺ᴵ η) → cOf w ⊑ᴵ η
  cOf-ub (Sel.emp f) d h = d
  cOf-ub {φ = φ} (Sel.sel ℓ K₀ a q y i dm) d h = ubd (bound φ y q) (h i) (λ k → demS k (h k))

  cOf-lb₁ : ∀ {c₂ t₂ g₂} {P : Cp (lc c₂ t₂ g₂) c} {E ap φ} (w : Sel.Sl P E ap φ) → c₂ ⊑ᴵ cOf w
  cOf-lb₁ {c₂ = c₂} (Sel.emp f) = ⊑ᴵ-refl′ c₂
    where
    open import OCF.Align.GuardTightCum using () renaming (⊑ᴵ-refl to ⊑ᴵ-refl″)
    ⊑ᴵ-refl′ : ∀ a → a ⊑ᴵ a
    ⊑ᴵ-refl′ a = ⊑ᴵ-refl″
  cOf-lb₁ {φ = φ} (Sel.sel ℓ K₀ a q y i dm) = ⊑ᴵ-trans (dm _ (evF (bound φ y q))) (FM (bound φ y q))

  cOf-lb₂ : ∀ {c₂ t₂ g₂} {P : Cp (lc c₂ t₂ g₂) c} {E ap φ} (w : Sel.Sl P E ap φ) {K} (k : InF K φ) → isB k ≡ false → K ≺ᴵ cOf w
  cOf-lb₂ (Sel.emp f) k r with evIn (f zero) k r
  ... | ()
  cOf-lb₂ {φ = φ} (Sel.sel ℓ K₀ a q y i dm) k r = sim (FM (bound φ y q)) (evIn (evF (bound φ y q)) k r)
```

## §3 地板的来源

`OccA y K r`: $K$ 是路径 $r$ 上某个 $\approx y$ 的闭包的分支值的 `pr`. `OccC`: 位置上的同一件事.

```agda
  data OccA (y : LG) (K : Ordᴵ) : ∀ {x a} → x < a → Set where
    oh : ∀ {c₃ t₃ g₃ x} (η : Ordᴵ) (e : c₃ ⊑ᴵ η) (r : x < g₃ η e) → lc c₃ t₃ g₃ ≈ y → K ≡ pr η → OccA y K (bra {c = c₃} {t = t₃} {g = g₃} η e r)
    ob : ∀ {c₃ t₃ g₃ x} (η : Ordᴵ) (e : c₃ ⊑ᴵ η) {r : x < g₃ η e} → OccA y K r → OccA y K (bra {c = c₃} {t = t₃} {g = g₃} η e r)
    os′ : ∀ {x b} {r : x < b} → OccA y K r → OccA y K (Lv.suc r)
    ol′ : ∀ {x f} n {r : x < f n} → OccA y K r → OccA y K (Lv.lim {f = f} n r)
    of′ : ∀ {c₃ t₃ g₃ x} {r : x < t₃} → OccA y K r → OccA y K (fst {c = c₃} {t = t₃} {g = g₃} r)

  data OccC (y : LG) (K : Ordᴵ) : ∀ {x a} → Cp x a → Set where
    oh : ∀ {c₃ t₃ g₃ x} (η : Ordᴵ) (e : c₃ ⊑ᴵ η) (r : Cp x (g₃ η e)) → lc c₃ t₃ g₃ ≈ y → K ≡ pr η → OccC y K (bra {c = c₃} {t = t₃} {g = g₃} η e r)
    ob : ∀ {c₃ t₃ g₃ x} (η : Ordᴵ) (e : c₃ ⊑ᴵ η) {r : Cp x (g₃ η e)} → OccC y K r → OccC y K (bra {c = c₃} {t = t₃} {g = g₃} η e r)
    os′ : ∀ {x b} {r : Cp x b} → OccC y K r → OccC y K (Lv.suc r)
    ol′ : ∀ {x f} n {r : Cp x (f n)} → OccC y K r → OccC y K (Lv.lim {f = f} n r)
    of′ : ∀ {c₃ t₃ g₃ x} {r : Cp x t₃} → OccC y K r → OccC y K (fst {c = c₃} {t = t₃} {g = g₃} r)

  module Occ {c₂ t₂ g₂} (P : Cp (lc c₂ t₂ g₂) c) (E : Ents) (ap : AdmC (tab E) P) where
    private module M = Sel P E ap
    κ₂ : LG
    κ₂ = lc c₂ t₂ g₂

    occP : ∀ {c₅ t₅ g₅} (Q : Cp (lc c₅ t₅ g₅) c) (aq : AdmC (tab E) Q) (η : Ordᴵ) (e : c₅ ⊑ᴵ η) (u : Bel′ E (lc c₅ t₅ g₅) η) {K} →
           InF K (M.φ (M.pick Q aq η e u)) → (lc c₅ t₅ g₅ ≈ κ₂) × (K ≡ pr η)
    occP Q aq η e (ℓ , a , q) i with kdec wf sf Q P E aq ap
    occP Q aq η e (ℓ , a , q) ink | inj₁ d = d , refl
    occP Q aq η e (ℓ , a , q) () | inj₂ n

    occW : ∀ {a x} (Q : Cp a c) (aq : AdmC (tab E) Q) (r : Cp x a) (ad : AdmC (tab E) r) {K} → InF K (M.φ (M.walk Q aq r ad)) → OccC κ₂ K r
    occW Q aq self _ ()
    occW Q aq (Lv.suc r) ad i = os′ (occW (Q ⊙ Lv.suc self) (adm⊙ {tab E} Q aq tt) r ad i)
    occW Q aq (Lv.lim n r) ad i = ol′ n (occW (Q ⊙ Lv.lim n self) (adm⊙ {tab E} Q aq tt) r ad i)
    occW Q aq (fst r) ad i = of′ (occW (Q ⊙ fst self) (adm⊙ {tab E} Q aq tt) r ad i)
    occW Q aq (bra η e r) (u , ad) (inl i) with occP Q aq η e u i
    ... | d , x = oh η e r d x
    occW Q aq (bra η e r) (u , ad) (inr i) = ob η e (occW (Q ⊙ bra η e self) (adm⊙ {tab E} Q aq (u , tt)) r ad i)

    occA : ∀ {a x} (Q : Cp a c) (aq : AdmC (tab E) Q) (r : x < a) (ad : Adm (tab E) r) {K} → InF K (M.φ (M.walkA Q aq r ad)) → OccA κ₂ K r
    occA Q aq zero _ ()
    occA Q aq (Lv.suc r) ad i = os′ (occA (Q ⊙ Lv.suc self) (adm⊙ {tab E} Q aq tt) r ad i)
    occA Q aq (Lv.lim n r) ad i = ol′ n (occA (Q ⊙ Lv.lim n self) (adm⊙ {tab E} Q aq tt) r ad i)
    occA Q aq (fst r) ad i = of′ (occA (Q ⊙ fst self) (adm⊙ {tab E} Q aq tt) r ad i)
    occA Q aq (bra η e r) (u , ad) (inl i) with occP Q aq η e u i
    ... | d , x = oh η e r d x
    occA Q aq (bra η e r) (u , ad) (inr i) = ob η e (occA (Q ⊙ bra η e self) (adm⊙ {tab E} Q aq (u , tt)) r ad i)

    -- 活帧: 帧的节点路径上的同键分支, 或这个帧自己
    data OccS (π : Fl) (K : Ordᴵ) : Set where
      sfr : ∀ {f} → Mem π f → κ f ≈ κ₂ → K ≡ pr (fη f) → OccS π K
      spf : ∀ {f c₃ t₃ g₃} (Pf : Cp (lc c₃ t₃ g₃) c) → Mem π f → OccC κ₂ K Pf → OccS π K

    occSel : ∀ {ρ} π (st : St E ρ π) {K} → InF K (M.φ (M.selSt π st)) → OccS π K
    occSel tz st ()
    occSel (tk f) st i with st hr
    occSel (tk f) st () | fs nothing a
    occSel (tk f) st (inl i) | fs (just (evd Pf adf lkf (ℓ , b , q))) a = spf Pf hr (occW self tt Pf adf i)
    occSel (tk f) st (inr i) | fs (just (evd Pf adf lkf (ℓ , b , q))) a with occP Pf adf (fη f) (conv (≅ᴰ-sym (oc≅ lkf)) (fe f)) (ℓ , at-resp {E} (≈-sym lkf) b , q) i
    ... | d , x = sfr hr (≈-trans (≈-sym lkf) d) x
    occSel (a ∪ b) st (inl i) with occSel a (λ m → st (ml m)) i
    ... | sfr m d x = sfr (ml m) d x
    ... | spf Pf m o = spf Pf (ml m) o
    occSel (a ∪ b) st (inr i) with occSel b (λ m → st (mr m)) i
    ... | sfr m d x = sfr (mr m) d x
    ... | spf Pf m o = spf Pf (mr m) o

  -- 定理: 地板只有四个来源
  data Src₄ {c₂ t₂ g₂} (P : Cp (lc c₂ t₂ g₂) c) (π : Fl) {t} (q : Maybe (t < c)) (E : Ents) (ap : AdmC (tab E) P) (K : Ordᴵ) : Set where
    fromSt  : Occ.OccS P E ap π K → Src₄ P π q E ap K
    fromTgt : ∀ {q′ : t < c} → q ≡ just q′ → OccA (lc c₂ t₂ g₂) K q′ → Src₄ P π q E ap K
    fromPos : OccC (lc c₂ t₂ g₂) K P → Src₄ P π q E ap K

  tgm : ∀ {E t} → Tg E t → Maybe (t < c)
  tgm t0 = nothing
  tgm (tp q _) = just q

  floors : ∀ {t π ρ c₂ t₂ g₂} (E : Ents) (T : Tg E t) (st : St E ρ π) (P : Cp (lc c₂ t₂ g₂) c) (ap : AdmC (tab E) P) {K} →
           InF K (Sel.φ (SSc E T st P ap)) → Src₄ P π (tgm T) E ap K
  floors {π = π} E T st P ap (inl i) = fromSt (Occ.occSel P E ap π st i)
  floors E t0 st P ap (inr (inl ()))
  floors E (tp q aq) st P ap (inr (inl i)) = fromTgt refl (Occ.occA P E ap self tt q aq i)
  floors E T st P ap (inr (inr i)) = fromPos (Occ.occW P E ap self tt P ap i)
```

## §4 $a+\eta$: 界不看穿过的分支

这是任务里 `c-bra*` 的定理形式. `Gp`: 字面的 $b<\eta$ 给字面的路径 $a+b<a+\eta$. `rec-exact`, `rdA-exact`: 读位置给的就是 $b+1$, **对一切 $\eta$, 含极限, 含极限的第 $n$ 项还是极限**. `nf-tail`: 目标规范化. `tail-ub`, `tail-lb`: 界模前序就是 $b+1$. `tail-free`: 两条路径的界互相 $\sqsubseteq$.

```agda
module TailThm (a : Ordᶜ (suc zero)) (σ : Simᴵ zero (suc zero)) (tca : Tc (rb₁ a)) where
  open RdAdd a σ tca using (Gₐ; I; vs; vl; rdA; Tc-top)
  open Tail I vs vl using (Rc; rB; rF; rC; rec; toRd)

  L : LG
  L = lc (suc zero) (suc (rb₁ a)) (λ η e → Gₐ η)

  Gp : ∀ {b x} → b <ᴵ x → Gₐ b < Gₐ x
  Gp zero      = Lv.zero
  Gp (suc q)   = Lv.suc (Gp q)
  Gp (lim n q) = Lv.lim n (Gp q)

  rec-exact : ∀ {b} η₀ z₀ x (q : b <ᴵ x) (σ′ : Simᴵ x η₀) l →
              Σ (suc zero ⊑ᴵ suc b) λ ea → Σ (suc b ⊲ η₀) λ m → Σ _ λ u →
              rec η₀ z₀ x (toCpS (Gp q)) σ′ l ≡ rB (suc b) ea m (inj₂ refl) self u
  rec-exact η₀ z₀ (suc b) zero σ′ l = _ , _ , _ , refl
  rec-exact η₀ z₀ (suc x) (suc q) σ′ l with rec η₀ z₀ x (toCpS (Gp q)) (λ r → σ′ (suc r)) (just (σ′ zero)) | rec-exact η₀ z₀ x q (λ r → σ′ (suc r)) (just (σ′ zero))
  ... | _ | ea , m , u , refl = ea , m , _ , refl
  rec-exact η₀ z₀ (lim f s) (lim n q) σ′ l with rec η₀ z₀ (f n) (toCpS (Gp q)) (λ r → σ′ (lim n r)) nothing | rec-exact η₀ z₀ (f n) q (λ r → σ′ (lim n r)) nothing
  ... | _ | ea , m , u , refl = ea , m , _ , refl

  rdA-exact : ∀ {b} η (e : suc zero ⊑ᴵ η) (q : b <ᴵ η) →
              Σ (suc zero ⊑ᴵ suc b) λ ea → Σ (suc b ⊲ η) λ m → Σ _ λ u →
              rdA η e (toCpS (Gp q)) ≡ rdB (suc b) ea m (inj₂ refl) self u
  rdA-exact (suc b) (s⊑ z≅ z₀) zero = _ , _ , _ , refl
  rdA-exact (suc x) (s⊑ z≅ z₀) (suc q) with rec (suc x) z₀ x (toCpS (Gp q)) (λ r → suc r) (just zero) | rec-exact (suc x) z₀ x q (λ r → suc r) (just zero)
  ... | _ | ea , m , u , refl = ea , m , _ , refl
  rdA-exact (lim f s) (s⊑ z≅ z₀) (lim n q) with rec (lim f s) z₀ (f n) (toCpS (Gp q)) (λ r → lim n r) nothing | rec-exact (lim f s) z₀ (f n) q (λ r → lim n r) nothing
  ... | _ | ea , m , u , refl = ea , m , _ , refl

  -- 目标的规范化
  nf-L : ∀ {b} τ (e : suc zero ⊑ᴵ τ) (q : b <ᴵ τ) →
         Σ (suc zero ⊑ᴵ suc b) λ ea → Σ _ λ t′ → Σ _ λ r′ →
         nfC L Tc-top (bra τ e (toCpS (Gp q))) ≡ nfc (inj₂ refl) (bra (suc b) ea self) t′ r′
  nf-L τ e q with rdA τ e (toCpS (Gp q)) | rdA-exact τ e q
  ... | _ | ea , m , u , refl = ea , _ , _ , refl

  nf-tail : ∀ {b} τ (e : suc zero ⊑ᴵ τ) (q : b <ᴵ τ) →
            Σ (suc zero ⊑ᴵ suc b) λ ea → Σ _ λ t′ →
            nfT (suc L) Tc-top (Lv.suc (bra τ e (Gp q))) ≡ nft (inj₂ refl) (Lv.suc (bra (suc b) ea Lv.zero)) t′
  nf-tail τ e q with nfC L Tc-top (bra τ e (toCpS (Gp q))) | nf-L τ e q
  ... | _ | ea , t′ , r′ , refl = ea , _ , refl

  -- 目标是规范的路径
  module Bd₁ (w₀ : WFˢ L) (s₀ : L ≈ L) where
    open Land (suc L) w₀ (s≈ s₀) Tc-top
    open Fold (suc L) w₀ (s≈ s₀) Tc-top

    pthₜ : ∀ {b} → suc zero ⊑ᴵ suc b → Gₐ b < suc L
    pthₜ ea = Lv.suc (bra _ ea Lv.zero)

    st₀ : ∀ {E ρ} → St E ρ tz
    st₀ ()

    module _ {b} (ea : suc zero ⊑ᴵ suc b) (E : Ents) (aq : Adm (tab E) (pthₜ ea)) where
      SS₀ = SSc {ρ = tz} E (tp (pthₜ ea) aq) (st₀ {E}) (Lv.suc self) tt
      w = Sel.wit SS₀

      only-b : ∀ {K} → InF K (Sel.φ SS₀) → K ≡ b
      only-b i with floors E (tp (pthₜ ea) aq) (st₀ {E}) (Lv.suc self) tt i
      ... | fromSt (Occ.sfr () _ _)
      ... | fromSt (Occ.spf _ () _)
      ... | fromTgt refl (os′ (oh _ _ _ _ refl)) = refl
      ... | fromTgt refl (os′ (ob _ _ ()))
      ... | fromPos (os′ ())

      in-b : InF b (Sel.φ SS₀)
      in-b = inr (inl (inl ink))

      tail-ub : cOf w ⊑ᴵ suc b
      tail-ub = cOf-ub w ea (λ i → sub (only-b i))
        where
        sub : ∀ {K} → K ≡ b → K ≺ᴵ suc b
        sub refl = via (≅ᴵ-refl b) zero

      tail-lb : suc b ⊑ᴵ cOf w
      tail-lb with cOf-lb₂ w in-b refl
      ... | via d r = s⊑ d r

      -- 头是字面的
      tail-head : ∀ (x : O (suc L) tz) (g : ∀ η e → O (suc L) (tz ∪ tk (frm (suc zero) (suc (rb₁ a)) (λ η e → Gₐ η) η e))) →
                  Σ _ λ x′ → Σ _ λ g′ → ψ {ρ = tz} E (tp (pthₜ ea) aq) (st₀ {E}) (ocl (Lv.suc self) (inj₂ refl) tt x g) ≡ oŝ (cOf w) x′ g′
      tail-head x g = head-goC E (tp (pthₜ ea) aq) (st₀ {E}) (Lv.suc self) (inj₂ refl) tt x g SS₀ w

    -- 界不看世界, 不看路径上曾经穿过什么
    tail-free : ∀ {b} (ea ea′ : suc zero ⊑ᴵ suc b) (E E′ : Ents) (aq : Adm (tab E) (pthₜ ea)) (aq′ : Adm (tab E′) (pthₜ ea′)) →
                cOf (w ea E aq) ⊑ᴵ cOf (w ea′ E′ aq′)
    tail-free ea ea′ E E′ aq aq′ = ⊑ᴵ-trans (tail-ub ea E aq) (tail-lb ea′ E′ aq′)
```

## §5 地板在下降时收紧: `omk` 的行

`ι-mark`: `ι` 读到记号时输出的形状: 外面一层 `ocv`, 里面的记号在规范的位置, 值是 $z$ 直接嵌到规范的位置. `mark-exact`, `mark-tail`: $a+\eta$ 的闭包, 分支 $\tau$ 里层 $a+(b+1)$ 的位置: 规范的分支是 $b+1$, 帧的分支值是 $b+1$, 地板是 `fk b`. **这是 [ScafLadderQ](ScafLadderQ.lagda.md) 的 `flo (suc b) = fk b`, 对一切 $\tau$, 不再有 $\tau$.**

```agda
module EmbThm (L : LG) (tc : Tc L) where
  open Emb L tc
  ι-mark : ∀ {a π ξ k} (P : Cp a L) (R : Strict k a) (lk : Wk ξ π) (ad : AdmC (cov π) (stCp R)) (z : Vs a R ξ) (x : O a π)
           {rep} (e₂ : Lk k rep) (pos : Strict rep L) (t : ∀ E → AdmC (tab E) (stCp (st⊙ P R)) → AdmC (tab E) (stCp pos))
           (r : ∀ ρ → AdmC (cov ρ) (stCp (st⊙ P R)) → AdmR ρ (stCp pos)) →
           nfS L tc (st⊙ P R) ≡ nfs e₂ pos t r →
           Σ (Cov (ξ ∪ pF (stCp pos)) (π ∪ pF P)) λ cv → Σ _ λ ad′ → Σ _ λ z′ →
           ι a P (inj₂ refl) (omk R lk ad z x) ≡ ocv cv (omk pos ml ad′ z′ (ιV a R (stCp pos) e₂ z))
  ι-mark P R lk ad z x e₂ pos t r eq rewrite eq = _ , _ , _ , refl

module MarkThm (a : Ordᶜ (suc zero)) (σ : Simᴵ zero (suc zero)) (tca : Tc (rb₁ a)) where
  open RdAdd a σ tca using (Gₐ; I; vs; vl; rdA; Tc-top)
  open Tail I vs vl using (Rc; rB; rF; rC; rec; toRd)
  open TailThm a σ tca using (L; Gp)

  toC : ∀ {b x} → b <ᴵ x → Cp (Gₐ b) (Gₐ x)
  toC q = toCp (Gp q)

  mark-exact : ∀ {b} η₀ z₀ x (q : suc b <ᴵ x) (σ′ : Simᴵ x η₀) l →
               Σ (suc zero ⊑ᴵ suc b) λ ea → Σ (suc b ⊲ η₀) λ m → Σ _ λ u →
               rec η₀ z₀ x (toC q) σ′ l ≡ rB (suc b) ea m (inj₂ refl) self u
  mark-exact η₀ z₀ (suc (suc b)) zero σ′ l = _ , _ , _ , refl
  mark-exact η₀ z₀ (suc x) (suc q) σ′ l with rec η₀ z₀ x (toC q) (λ r → σ′ (suc r)) (just (σ′ zero)) | mark-exact η₀ z₀ x q (λ r → σ′ (suc r)) (just (σ′ zero))
  ... | _ | ea , m , u , refl = ea , m , _ , refl
  mark-exact η₀ z₀ (lim f s) (lim n q) σ′ l with rec η₀ z₀ (f n) (toC q) (λ r → σ′ (lim n r)) nothing | mark-exact η₀ z₀ (f n) q (λ r → σ′ (lim n r)) nothing
  ... | _ | ea , m , u , refl = ea , m , _ , refl

  -- 分支 τ 里层 a+(b+1) 的位置, 规范化之后是分支 b+1 的顶
  mark-tail : ∀ {b} τ (e : suc zero ⊑ᴵ τ) (q : suc b <ᴵ τ) →
              Σ (suc zero ⊑ᴵ suc b) λ ea → Σ (suc b ⊲ τ) λ m → Σ _ λ u →
              rdA τ e (toC q) ≡ rdB (suc b) ea m (inj₂ refl) self u
  mark-tail (suc (suc b)) (s⊑ z≅ z₀) zero = _ , _ , _ , refl
  mark-tail (suc x) (s⊑ z≅ z₀) (suc q) with rec (suc x) z₀ x (toC q) (λ r → suc r) (just zero) | mark-exact (suc x) z₀ x q (λ r → suc r) (just zero)
  ... | _ | ea , m , u , refl = ea , m , _ , refl
  mark-tail (lim f s) (s⊑ z≅ z₀) (lim n q) with rec (lim f s) z₀ (f n) (toC q) (λ r → lim n r) nothing | mark-exact (lim f s) z₀ (f n) q (λ r → lim n r) nothing
  ... | _ | ea , m , u , refl = ea , m , _ , refl
```
