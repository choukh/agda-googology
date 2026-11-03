# 证书与阶段无关: 字面的目标 $L$ 与 $\omega$ 处的并 (底座)

> 底座, 不含记号. 结论写在 [LevelK](LevelK.lagda.md). `Cert-top`: 对任何阶段, 任何可取层号的目标 $L$ (`BL L`, 目标合法 `Ti L`, $L$ 自己是好层号), 任何合法模式, 折叠的输出有证书. `K-stage.Cert` 是它的实例. §2 把塔并到 $\omega$: 低层是全部自然数, 第 $m$ 层的地板就是第 $m+1$ 阶段的第 $m$ 层地板. §3 是 $L=\omega$ 的实例: $\psi_\omega(\Omega_n)$ 与 $\psi_\omega(\Omega_{\omega+1})$. 后者是字面的 "$\psi_L(\Omega_{L+1})$", 节点 $L$ 上升, 链的目标是 $L$ 自己. 这里的 `S` 都没有被问到.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LevelKOmega where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s; _+_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <⇒≤)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; at; Tree; limᵢ; up; Ω; toLv; Sim; σ-id; _∘σ_; ι; down; Dn)
open import OCF.Align.InaccFloorTree using (Sib; natL; Mode; bel; lt; fin; verdict; module PF)
open import OCF.Align.LevelKBase using (NoO; Fl; module Leaf; Stage; Ext; module Move)
open import OCF.Align.LevelKFin using (IsK; module Fin; noo-nat; at-nat; natL-inj)
open import OCF.Align.LevelKLvP using (module LvPs)
open import OCF.Align.LevelKTower
open import OCF.Align.LevelKWorld using (Ordᴵ; _<ᴵ_; suc; lim; zero; natᴵ; ωᴵ; em; E; W-ℓ; module W-ℓ₀)
```

## §1 字面目标的证书

```agda
module Top (S : Sib) (St : Stage) where
  open LvPs S St public

  Cert-top : ∀ {θ L} (m : Mode θ L) → BL L → Ti L → LvP L → OK θ m → LvP θ → WFᴬ (toLv (ψᵖ m (Ω θ)))
  Cert-top {θ} {L} m b ti pL ok p@(g , r , _) = wf b (Good-ψ m ok ti (Good-Ω L pL) (Good-Ω θ p) (Ω-self θ g r))

  -- `bel`: 树层在目标之下, 判决不被问到
  okB : ∀ k {i} (σ : Sim k i) → SD σ → OK k (bel σ)
  okB zero σ s = tt
  okB (suc k) σ s = (λ r d → cvp (proj₁ (σ r)) (proj₂ (σ r)) (s r d)) , okB k (_∘σ_ {b = suc k} σ (ι (suc k) tt)) (sd∘ι (suc k) tt σ s tt)
  okB (lim f) σ s =
    (λ r d → cvp (proj₁ (σ r)) (proj₂ (σ r)) (s r d)) , (λ n → okB (f n) (_∘σ_ {b = lim f} σ (ι (lim f) n)) (sd∘ι (lim f) n σ s tt))
  okB (limᴼ k g) σ s =
    (λ r d → cvp (proj₁ (σ r)) (proj₂ (σ r)) (s r d)) , (λ x b → okB (g x) (_∘σ_ {b = limᴼ k g} σ (ι (limᴼ k g) x)) (sd∘ι (limᴼ k g) x σ s b))
```

## §2 塔并到 $\omega$

`Flᴷ`: 第 $K$ 阶段. `ext-add`: 第 $K$ 阶段到第 $d+K$ 阶段是单步 `Ext` 的复合. `flω`: 地板读第 $m+1$ 阶段. 第 $m$ 层的地板与读它的阶段无关, 这正是 `Ext` 说的.

```agda
Ext∘ : ∀ {F G H} → Ext F G → Ext G H → Ext F H
Ext∘ X Y = record
  { low⊂ = λ l → Ext.low⊂ Y (Ext.low⊂ X l)
  ; A⊂ = λ a → Ext.A⊂ Y (Ext.A⊂ X a)
  ; A⊃ = λ l a → Ext.A⊃ X l (Ext.A⊃ Y (Ext.low⊂ X l) a)
  }

Ext-id : ∀ {F} → Ext F F
Ext-id = record { low⊂ = λ l → l ; A⊂ = λ a → a ; A⊃ = λ _ a → a }

module Union (W₀ : WorldK 0 St₀) (ch : Choice) where
  Sᴷ : ℕ → Stage
  Sᴷ K = proj₁ (tower W₀ ch K)

  Flᴷ : ℕ → Fl
  Flᴷ K = Stage.fl (Sᴷ K)

  isKᴷ : ∀ K → IsK K (Sᴷ K)
  isKᴷ K = proj₁ (proj₂ (tower W₀ ch K))

  ext-suc : ∀ K → Ext (Flᴷ K) (Flᴷ (suc K))
  ext-suc zero = Step.ext 0 St₀ isK₀ (λ _ ()) (λ _ ()) W₀
  ext-suc (suc k) =
    let t = tower W₀ ch (suc k)
    in Step.ext (suc k) (proj₁ t) (proj₁ (proj₂ t)) (proj₁ (proj₂ (proj₂ t))) (proj₂ (proj₂ (proj₂ t))) (ch k t)

  ext-add : ∀ K d → Ext (Flᴷ K) (Flᴷ (d + K))
  ext-add K zero    = Ext-id
  ext-add K (suc d) = Ext∘ (ext-add K d) (ext-suc (d + K))

  +s : ∀ a b → a + suc b ≡ suc (a + b)
  +s zero    b = refl
  +s (suc a) b = cong suc (+s a b)

  +0 : ∀ a → a + 0 ≡ a
  +0 zero    = refl
  +0 (suc a) = cong suc (+0 a)

  lt-add′ : ∀ m K → m < K → Σ ℕ λ d → K ≡ d + suc m
  lt-add′ zero    (suc K) (s≤s z≤n) = K , sym (trans (+s K 0) (cong suc (+0 K)))
  lt-add′ (suc m) (suc K) (s≤s p) with lt-add′ m K p
  ... | d , refl = d , sym (+s d (suc m))

  lt-add : ∀ {m K} → m < K → Σ ℕ λ d → K ≡ d + suc m
  lt-add {m} {K} = lt-add′ m K

  Lwᴷ : ℕ → Lv → Set
  Lwᴷ K = Fl.Lw (Flᴷ K)

  Aᴷ : ℕ → (j : Lv) → Ordᴸ j → Set
  Aᴷ K = Fl.A (Flᴷ K)

  lw-m : ∀ m → Lwᴷ (suc m) (natL m)
  lw-m m = IsK.⇐lw (isKᴷ (suc m)) m ≤-refl

  flω : Fl
  flω = record
    { Lw = λ j → Σ ℕ λ m → j ≡ natL m
    ; A = λ j x → Σ ℕ λ m → j ≡ natL m × Aᴷ (suc m) j x
    ; A→Lw = λ { k x (m , e , _) → m , e }
    ; low-noo = λ { j (m , refl) → noo-nat m }
    ; low-at = λ { j (m , refl) r → let n , _ , e = at-nat m r in n , e }
    ; low-lim = λ { f n (zero , ()) ; f n (suc m , ()) }
    }

  -- 第 K 阶段到并
  extω : ∀ K → Ext (Flᴷ K) flω
  extω K = record
    { low⊂ = λ l → let m , _ , e = IsK.lw⇒ (isKᴷ K) _ l in m , e
    ; A⊂ = A⊂′
    ; A⊃ = A⊃′
    }
    where
    A⊂′ : ∀ {j x} → Aᴷ K j x → Fl.A flω j x
    A⊂′ {j} {x} a with IsK.lw⇒ (isKᴷ K) j (Fl.A→Lw (Flᴷ K) j x a)
    ... | m , p , refl with lt-add p
    ...   | d , e = m , refl , Ext.A⊃ (ext-add (suc m) d) (lw-m m) (subst (λ u → Aᴷ u (natL m) x) e a)

    A⊃′ : ∀ {j x} → Lwᴷ K j → Fl.A flω j x → Aᴷ K j x
    A⊃′ {j} {x} l (m , refl , a) with IsK.lw⇒ (isKᴷ K) j l
    ... | m′ , p , e with natL-inj m m′ e
    ...   | refl with lt-add p
    ...     | d , e′ = subst (λ u → Aᴷ u (natL m) x) (sym e′) (Ext.A⊂ (ext-add (suc m) d) a)

  module Mω (K : ℕ) = Move (Flᴷ K) flω (extω K)
  open Leaf flω

  nat≈ : ∀ n {b} → natL n ≈ᴮ b → natL n ≡ b
  nat≈ zero z≈ = refl
  nat≈ (suc n) (s≈ e) = cong Lv.suc (nat≈ n e)

  nat-wf : ∀ n → WFᴬ (natL n)
  nat-wf zero    = tt
  nat-wf (suc n) = nat-wf n

  Stω : Stage
  Stω = record
    { fl = flω
    ; low-≈ = λ { (m , refl) _ e → nat≈ m e }
    ; low-wf = λ { j (m , refl) → nat-wf m }
    ; ΩA = λ { j (m , refl) → m , refl , Stage.ΩA (Sᴷ (suc m)) (natL m) (lw-m m) }
    ; pΩ = λ { j (m , refl) → Mω.≺↑ (suc m) (Stage.pΩ (Sᴷ (suc m)) (natL m) (lw-m m)) }
    ; cmpA = cmpω
    ; cxA = λ { j x (m , refl , a) →
        Mω.Cx↑ (suc m) (toLv x) (Fl.lo-toLv (Flᴷ (suc m)) (Fl.lw→bl (Flᴷ (suc m)) (lw-m m)) x)
          (Stage.cxA (Sᴷ (suc m)) (natL m) x a) }
    }
    where
    cmpω : ∀ j x y → Fl.A flω j x → Fl.A flω j y → Tri (toLv x) (toLv y)
    cmpω j x y (m , e , a) (m′ , e′ , a′) with natL-inj m m′ (trans (sym e) e′)
    ... | refl = Mω.Tri↑ (suc m) (Stage.cmpA (Sᴷ (suc m)) j x y a a′)
```

## §3 $L=\omega$

```agda
module Lω (S : Sib) (W₀ : WorldK 0 St₀) (ch : Choice) where
  open Union W₀ ch using (Stω)
  open Top S Stω

  ωL : Lv
  ωL = lim natL

  low-n : ∀ n → Lw (natL n)
  low-n n = n , refl

  low-at-ω : ∀ r → Lw (at ωL r)
  low-at-ω (n , r) with at-nat n r
  ... | m , _ , e = m , e

  bl-ω : BL ωL
  bl-ω = noo-nat , low-at-ω

  zt-ω : Zt ωL
  zt-ω j (m , refl) = (suc m , inj₁ tt) , tt , refl

  lvt-ω : LvT ωL
  lvt-ω = (λ r _ → inj₁ (low-at-ω r)) , (λ n → low→lvt (natL n) (low-n n))

  lvr-ω : LvR ωL
  lvr-ω = λ n → lvr-noo (natL n) (noo-nat n)

  ti-ω : Ti ωL
  ti-ω = lvt-ω , zt-ω , lvr-ω

  lvp-n : ∀ n → LvP (natL n)
  lvp-n n = lvp-low (natL n) (low-n n)

  step-Ω : ∀ n → Ω (natL n) ⊑ᵒ Ω (natL (suc n))
  step-Ω n = Ω-mono (natL n) (natL (suc n)) (low-wf _ (low-n n)) (low-wf _ (low-n (suc n)))
               (lo-par (low-n n)) (lo-par (low-n (suc n))) (lvp-n n) (lvp-n (suc n))
               (λ r d → viaᴬ (inj₂ r) d (≈ᴮ-refl _))

  lvp-ω : LvP ωL
  lvp-ω = (λ n → proj₁ (lvp-n n)) , lvr-ω , (λ n → proj₂ (proj₂ (lvp-n n))) , step-Ω

  -- ψ_ω(Ω_n): 判决不被问到
  σₙ : ∀ n → Sim (natL n) ωL
  σₙ n r = (n , r) , refl

  Cert-ωₙ : ∀ n → WFᴬ (toLv (ψᵖ (bel (σₙ n)) (Ω (natL n))))
  Cert-ωₙ n = Cert-top (bel (σₙ n)) bl-ω ti-ω lvp-ω (okB (natL n) (σₙ n) (λ r d → d)) (lvp-n n)

  -- ψ_ω(Ω_{ω+1}): L 上升, 链的目标是 L 自己
  nat≉ω : ∀ m → natL m ≈ᴮ ωL → ⊥
  nat≉ω zero ()
  nat≉ω (suc m) ()

  ≉≡ : ∀ {a} m → a ≡ natL m → a ≈ᴮ ωL → ⊥
  ≉≡ m refl e = nat≉ω m e

  mω : Mode (suc ωL) ωL
  mω = lt (inj₁ tt) refl

  ok-ω₊ : OK (suc ωL) mω
  ok-ω₊ = cvs , okB ωL (σ-id ωL) (λ r d → d)
    where
    cvs : ∀ r → AdmB (suc ωL) r → CV (verdict S mω r)
    cvs (inj₁ _) _ = cvr λ { (n , r) d e → let m , _ , q = at-nat n r in ≉≡ m q e }
    cvs (inj₂ r) d = cvp r refl d

  lvp-ω₊ : LvP (suc ωL)
  lvp-ω₊ = (inj₂ (ok-ω₊ , zt-ω) , lvt-ω) , lvr-ω , proj₂ (proj₂ lvp-ω)

  Cert-ω₊ : WFᴬ (toLv (ψᵖ mω (Ω (suc ωL))))
  Cert-ω₊ = Cert-top mω bl-ω ti-ω lvp-ω ok-ω₊ lvp-ω₊
```

## §4 $L=\omega+1$: 再加一层

`Next` 不要求新层是自然数: 地板的递归本来就是层号值的. 这里在 $\omega$ 处的并上再加第 $\omega$ 层. `pω` 说 $\omega$ 是 $\Omega_\omega$ 的字面前驱: 第 0 层的世界要超过 $\omega$ 才有 (`pω-ℓ`). 字面目标 $\psi_{\omega+1}(\Omega_{\omega+2})$ 有证书, `S` 没有被问到.

```agda
module Lω₁ (S : Sib) (W₀ : WorldK 0 St₀) (ch : Choice) (pω : Leaf._≺ᴬ_ (Stage.fl (Union.Stω W₀ ch)) (lim natL) (toLv (Ω (lim natL)))) where
  open Union W₀ ch using (Stω)
  private
    module T₀ = Top S Stω
    module O₀ = Lω S W₀ ch

  ωL : Lv
  ωL = lim natL

  nat≉ω′ : ∀ m → T₀._≈ᴮ_ ωL (natL m) → ⊥
  nat≉ω′ zero ()
  nat≉ω′ (suc m) ()

  N : NewLevel Stω ωL
  N = record
    { nw-noo = noo-nat
    ; nw-at = O₀.low-at-ω
    ; nw-lim = λ { f n refl → n , refl }
    ; nw-new = λ { (zero , ()) ; (suc m , ()) }
    ; nw-≉ = λ { (m , refl) e → nat≉ω′ m e }
    ; nw-wf = proj₁ (proj₁ (Cxω)) , proj₂ (proj₁ (Cxω))
    ; nw-pΩ = pω
    }
    where
    Cxω : T₀.Cx ωL
    Cxω = ((λ n r d → T₀.viaᴬ (inj₂ r) d (T₀.≈ᴮ-refl _)) , (λ n → T₀.low-wf _ (O₀.low-n n))) ,
          (λ n → T₀.noo→rp (natL n) (noo-nat n)) ,
          (λ n → T₀.noo→mn (natL n) (noo-nat n))

  Ωself : T₀.Eq ωL (Ω ωL) (Ω ωL)
  Ωself = T₀.Ω-self ωL (proj₁ O₀.lvp-ω) (proj₁ (proj₂ O₀.lvp-ω))

  W : World Stω ωL
  W = record
    { L = suc (toLv (Ω ωL))
    ; loL = T₀.lo-toLv O₀.bl-ω (Ω ωL)
    ; cxL = T₀.cx-tree O₀.bl-ω (T₀.Good-Ω ωL O₀.lvp-ω) Ωself
    ; hΩ = T₀.viaᴬ (inj₁ tt) tt (T₀.≈ᴮ-refl _)
    }

  St₊ : Stage
  St₊ = Next.St′ Stω ωL N W

  open Top S St₊

  low-ω : Lw ωL
  low-ω = inj₂ refl

  low-at-ω₁ : ∀ r → Lw (at (suc ωL) r)
  low-at-ω₁ (inj₁ _) = low-ω
  low-at-ω₁ (inj₂ r) = inj₁ (O₀.low-at-ω r)

  ω₁ : Lv
  ω₁ = suc ωL

  bl-ω₁ : BL ω₁
  bl-ω₁ = noo-nat , low-at-ω₁

  zt-ω₁ : Zt ω₁
  zt-ω₁ j (inj₂ refl) = inj₁ tt , tt , refl
  zt-ω₁ j (inj₁ (m , refl)) = inj₂ (suc m , inj₁ tt) , tt , refl

  lvt-ω₁ : LvT ω₁
  lvt-ω₁ = (λ r _ → inj₁ (low-at-ω₁ r)) , low→lvt ωL low-ω

  lvr-ω₁ : LvR ω₁
  lvr-ω₁ = lvr-noo ωL noo-nat

  ti-ω₁ : Ti ω₁
  ti-ω₁ = lvt-ω₁ , zt-ω₁ , lvr-ω₁

  lvp-ω₁ : LvP ω₁
  lvp-ω₁ = (inj₁ low-ω , low→lvt ωL low-ω) , lvr-ω₁ , glv-low ωL low-ω

  m₁ : Mode (suc ω₁) ω₁
  m₁ = lt (inj₁ tt) refl

  no≈ : ∀ {a} m → a ≡ natL m → a ≈ᴮ ω₁ → ⊥
  no≈ zero refl ()
  no≈ (suc zero) refl (s≈ ())
  no≈ (suc (suc m)) refl (s≈ ())

  ok-ω₂ : OK (suc ω₁) m₁
  ok-ω₂ = cvs , okB ω₁ (σ-id ω₁) (λ r d → d)
    where
    cvs : ∀ r → AdmB (suc ω₁) r → CV (verdict S m₁ r)
    cvs (inj₁ _) _ = cvr λ { (inj₁ _) _ () ; (inj₂ (n , s)) d e → let m , _ , q = at-nat n s in no≈ m q e }
    cvs (inj₂ r) d = cvp r refl d

  lvp-ω₂ : LvP (suc ω₁)
  lvp-ω₂ = (inj₂ (ok-ω₂ , zt-ω₁) , lvt-ω₁) , lvr-ω₁ , proj₂ (proj₂ lvp-ω₁)

  -- ψ_{ω+1}(Ω_{ω+2})
  Cert-ω₁ : WFᴬ (toLv (ψᵖ m₁ (Ω (suc ω₁))))
  Cert-ω₁ = Cert-top m₁ bl-ω₁ ti-ω₁ lvp-ω₁ ok-ω₂ lvp-ω₂

-- 第 0 层的世界 ℓ = ω + 2 给出 `pω`
module Pω-ℓ (S : Sib) (ch : Choice) where
  ℓ₂ : Ordᴵ
  ℓ₂ = suc (suc ωᴵ)

  h₂ : ∀ n → natᴵ n <ᴵ ℓ₂
  h₂ n = suc (suc (lim (suc n) zero))

  W₂ : WorldK 0 St₀
  W₂ = W-ℓ ℓ₂ h₂

  open Union W₂ ch using (Stω; flω)
  open Leaf flω

  ω≈E : lim natL ≈ᴮ E ωᴵ
  ω≈E = l≈ (λ n → ≡→≈′ (sym (W-ℓ₀.E-nat n)))

  pω-ℓ : lim natL ≺ᴬ toLv (Ω (lim natL))
  pω-ℓ = viaᴬ (1 , inj₂ (em (suc ωᴵ) , inj₁ tt)) ((0 , refl , inj₂ (refl , inj₁ tt , tt , Leaf.≈ᴮ-refl fl₀ _)) , tt) ω≈E

  open Lω₁ S W₂ ch pω-ℓ public using (Cert-ω₁)
```
