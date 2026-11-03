# 全部 $\theta$ 的证书: 第 5 站 (底座)

> 底座, 不含记号. 结论写在 [InaccTheta](InaccTheta.lagda.md). 第 5 站的层号 $\limᴼ\,0\,(x\mapsto\psi_1(\Omega_x))$ 就是 `toLv (F LΩ)`. 它的证书只差一件事: `S` 在 `Aℓ` 里每个层号的 $\Omega$ 节点要的链上正确 (`HE`). 世界 $\omega+1$ 里这是定理, 对一切 `S`, 对任何叶子 `B₀`. 嵌套的下标要叶子取 `B₀ = Aℓ` (`StA`).

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.InaccThetaStation where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; Low; Dn; DnT; at; down; outL; intoL; outD; intoD; Tree; limᵢ; up; Ω; toLv;
   Sim; σ-id; ι; _∘σ_)
open import OCF.Align.InaccFloorTree using (Sib; Mode; fin; bel; lt; upM; verdict; chM; natL; module PF)
open import OCF.Align.InaccFloorBase using (Aℓ; em)
open import OCF.Align.InaccThetaObs using (BL; b0; b1)
open import OCF.Align.InaccThetaMono using (module Mono)
open import OCF.Align.Level using (Ordᴵ; _<ᴵ_; zero; suc; lim; natᴵ; ωᴵ)
```

## §1 第 5 站

`g₅`: 第 5 站的分支. `lvp-E`: `Ordᴵ` 的层号, 只差 `LvG`. 这里的 `B₀` 任意, 因为 `Ordᴵ` 的层号里没有 `limᴼ`, 所以 `B₀ = ⊤` 时结论落在原来的 `Rel` 里. `Lv₅≡` 说第 5 站的层号**就是** `toLv (F LΩ)`, `refl`.

```agda
module St (S : Sib) (ℓ : Ordᴵ) (one : suc zero <ᴵ ℓ) (B₀ : Ordᴸ zero → Set) (a⊆b : ∀ x → Aℓ ℓ zero x → B₀ x) where
  open Mono S ℓ one B₀ a⊆b public

  E : Ordᴵ → Lv
  E a = toLv (em a)

  wf-E : ∀ a → WFᴬ (E a)
  wf-E a = wf b0 (em-good a)

  lvp-E : ∀ a → LvG (E a) → LvP (E a)
  lvp-E zero lg = tt , tt , tt
  lvp-E (suc a) lg with lvp-E a (t→g (E a) (proj₂ lg))
  ... | _ , r , v = lg , r , v
  lvp-E (lim f s) lg =
    let P = λ n → lvp-E (f n) (lg n)
    in lg , (λ n → proj₁ (proj₂ (P n))) , (λ n → proj₂ (proj₂ (P n))) ,
       (λ n → Ω-mono (E (f n)) (E (f (suc n))) (wf-E (f n)) (wf-E (f (suc n))) (P n) (P (suc n)) (em-mono (s n) (idO {b = b0} {b′ = b0})))

  HE : Set
  HE = ∀ x → A zero x → LvG (toLv x)

  LΩ : Lv
  LΩ = toLv (Ω (natL 1))

  g₅ : Ordᴸ zero → Lv
  g₅ x = toLv (F (toLv x))

  Lv₅ : Lv
  Lv₅ = toLv (F LΩ)

  Lv₅≡ : Lv₅ ≡ limᴼ zero g₅
  Lv₅≡ = refl

  lvp-A : HE → ∀ x → A zero x → LvP (toLv x)
  lvp-A he _ ax@(a , _ , refl) = lvp-E a (he _ ax)

  wf-A : ∀ x → A zero x → WFᴬ (toLv x)
  wf-A _ (a , _ , refl) = wf-E a

  mono₅ : HE → ∀ x z → A zero x → A zero z → x ⊑ᵒ z → g₅ x ⊑ᴬ g₅ z
  mono₅ he x z ax az p =
    F-mono (toLv x) (toLv z) (wf-A x ax) (wf-A z az) (lvp-A he x ax) (lvp-A he z az) (p (idO {b = b0} {b′ = b0}))

  Station5 : HE → WFᴬ Lv₅
  Station5 he =
    (λ x y ax ay → let z , az , px , py = A-dir x y ax ay in z , az , mono₅ he x z ax az px , mono₅ he y z ay az py) ,
    (Tree.suc Tree.zero , x₁ , zp-base b1 (ZpΨ {i = natL 1} (fin 1 refl) (Ω (toLv {zero} (Tree.suc Tree.zero))) zpI) , (λ ())) ,
    (λ x ax → Cert (toLv x) (lvp-A he x ax))

  cmp₅ : HE → (p q : Pre Lv₅) → Adm Lv₅ p → Adm Lv₅ q → Tri (at Lv₅ p) (at Lv₅ q)
  cmp₅ he = <-decᴬ Lv₅ (Station5 he)
```

## §2 $\omega$ 与 $\omega+1$: `S` 不被问到

`okBel`: 模式 `bel` 永远 `OK`. `okLtω`: $\omega+1$ 的链的模式 `lt` 不问 `S`: 路径比较全在字面的 `suc` 上. 这是 `fin` 以外的第一个实例, 说明 `LvG` 不只是有限层号的条件. 这里的 `S` 是任意的.

```agda
  okBel : ∀ k {i} (σ : Sim k i) → SD σ → OK k (bel σ)
  okBel zero       σ s = tt
  okBel (suc k)    σ s = (λ r d → cvp _ (proj₂ (σ r)) (s r d)) , okBel k _ (sd∘ι (suc k) tt σ s tt)
  okBel (lim f)    σ s = (λ r d → cvp _ (proj₂ (σ r)) (s r d)) , (λ n → okBel (f n) _ (sd∘ι (lim f) n σ s tt))
  okBel (limᴼ k g) σ s = (λ r d → cvp _ (proj₂ (σ r)) (s r d)) , (λ x b → okBel (g x) _ (sd∘ι (limᴼ k g) x σ s b))

  natL≉lim : ∀ m {f} → natL m ≈ᴮ lim f → ⊥
  natL≉lim zero ()
  natL≉lim (suc m) ()

  ω≉ : ∀ {c} m → c ≡ natL m → ∀ {f} → c ≈ᴮ lim f → ⊥
  ω≉ m refl e = natL≉lim m e

  okLtω : OK (suc Ωω) (lt (inj₁ tt) refl)
  okLtω = (λ { (inj₁ _) _ → cvr (λ { (n , r) _ e → ω≉ _ (proj₂ (fin-nat n r)) e })
             ; (inj₂ r) d → cvp r refl d })
        , okBel Ωω (σ-id Ωω) (sd-id {Ωω})

  fin-ω : FinAt Ωω
  fin-ω (n , r) = fin-nat n r

  LvTω : LvT Ωω
  LvTω = lvt-fin Ωω fin-ω

  Ztω : Zt Ωω
  Ztω = ((1 , inj₁ tt) , tt , refl) , zpL 0 (zpU zpZ)

  LvGω₊ : LvG (suc Ωω)
  LvGω₊ = inj₂ (okLtω , Ztω) , LvTω

  wf-nat : ∀ n → WFᴬ (natL n)
  wf-nat zero    = tt
  wf-nat (suc n) = wf-nat n

  step-nat : ∀ n → natL n ⊑ᴬ natL (suc n)
  step-nat n r d = viaᴬ (inj₂ r) d (≈ᴮ-refl _)

  lvpω : LvP Ωω
  lvpω = (λ n → proj₁ (lvp-nat n)) , lvr-nat , glv-nat ,
         (λ n → Ω-mono (natL n) (natL (suc n)) (wf-nat n) (wf-nat (suc n)) (lvp-nat n) (lvp-nat (suc n)) (step-nat n))

  lvpω₊ : LvP (suc Ωω)
  lvpω₊ = LvGω₊ , proj₁ (proj₂ lvpω) , proj₂ (proj₂ lvpω)

  Certω : WFᴬ (toLv (F Ωω))
  Certω = Cert Ωω lvpω

  Certω₊ : WFᴬ (toLv (F (suc Ωω)))
  Certω₊ = Cert (suc Ωω) lvpω₊
```

## §3 世界 $\omega+1$ 里第 5 站无条件

```agda
nat-eq : ∀ n → toLv (em (natᴵ n)) ≡ natL n
nat-eq zero    = refl
nat-eq (suc n) = cong Lv.suc (nat-eq n)

lt-nat : ∀ {a} m → a <ᴵ natᴵ m → Σ ℕ λ k → a ≡ natᴵ k
lt-nat (suc m) zero    = m , refl
lt-nat (suc m) (suc q) = lt-nat m q

one-ω : suc zero <ᴵ suc ωᴵ
one-ω = suc (lim 2 zero)

module Wω (S : Sib) (B₀ : Ordᴸ zero → Set) (a⊆b : ∀ x → Aℓ (suc ωᴵ) zero x → B₀ x) where
  open St S (suc ωᴵ) one-ω B₀ a⊆b public

  he-nat : ∀ n → LvG (toLv (em (natᴵ n)))
  he-nat n = subst LvG (sym (nat-eq n)) (proj₁ (lvp-nat n))

  HEω : HE
  HEω _ (a , zero , refl) = he-nat
  HEω _ (a , suc (lim m q) , refl) with lt-nat m q
  ... | k , refl = he-nat k

  Station5ω : WFᴬ Lv₅
  Station5ω = Station5 HEω
```

## §4 层号的闭包与嵌套: 叶子取 `Aℓ`

`lvp-lim`, `lvp-limᴼ`: 好层号对 `lim`, `limᴼ 0` 封闭, 条件都在层号上. `lvpΩΩ`: $\Omega_\Omega$ 的层号是好层号, 这要 `B₀ ⊆ Aℓ` (否则 `no-Ωᵀ`). `Tw`: 下标里任意嵌套 $\psi_1(\Omega_{\psi_1(\Omega_{\cdots})})$ 的塔.

```agda
module StA (S : Sib) (ℓ : Ordᴵ) (one : suc zero <ᴵ ℓ) where
  open St S ℓ one (Aℓ ℓ zero) (λ x a → a) public
  open Feed (λ x b → b) public

  lvp-lim : ∀ (h : ℕ → Lv) → (∀ n → LvP (h n)) → (∀ n → WFᴬ (h n)) → (∀ n → h n ⊑ᴬ h (suc n)) → LvP (lim h)
  lvp-lim h p w st =
    (λ n → proj₁ (p n)) , (λ n → proj₁ (proj₂ (p n))) , (λ n → proj₂ (proj₂ (p n))) ,
    (λ n → Ω-mono (h n) (h (suc n)) (w n) (w (suc n)) (p n) (p (suc n)) (st n))

  lvp-limᴼ : ∀ (g : Ordᴸ zero → Lv) →
             (∀ x → A zero x → LvP (g x)) → (∀ x → A zero x → WFᴬ (g x)) →
             (∀ x z → A zero x → A zero z → x ⊑ᵒ z → g x ⊑ᴬ g z) →
             (∀ z z′ → A zero z → A zero z′ → Eq zero z z′ → g z ≈ᴮ g z′) → LvP (limᴼ zero g)
  lvp-limᴼ g p w mo re =
    (inj₁ refl , tt , (λ x a → proj₁ (p x a))) ,
    (tt , (λ x a → proj₁ (proj₂ (p x a))) , re) ,
    (tt , (λ x a → proj₂ (proj₂ (p x a))) ,
     (λ z z′ a a′ q → Ω-mono (g z) (g z′) (w z a) (w z′ a′) (p z a) (p z′ a′) (mo z z′ a a′ q)))

  Ω₁≃ : Eq (natL 1) (Ω (natL 1)) (Ω (natL 1))
  Ω₁≃ = Ω-self (natL 1) (proj₁ (lvp-nat 1)) tt

  lvpΩΩ : HE → LvP LΩ
  lvpΩΩ he = lvp b1 GΩ₁ Ω₁≃ (inj₁ refl , tt , he)

  Station5′ : HE → WFᴬ Lv₅
  Station5′ he = Cert LΩ (lvpΩΩ he)

  Tw : ℕ → Lv
  Tw zero    = LΩ
  Tw (suc n) = toLv (F (Tw n))

  lvp-Tw : HE → (∀ n → LvG (Tw (suc n))) → ∀ n → LvP (Tw n)
  lvp-Tw he lg zero    = lvpΩΩ he
  lvp-Tw he lg (suc n) = lvp-F (Tw n) (lvp-Tw he lg n) (lg n)

  Cert-Tw : HE → (∀ n → LvG (Tw (suc n))) → ∀ n → WFᴬ (toLv (F (Tw n)))
  Cert-Tw he lg n = Cert (Tw n) (lvp-Tw he lg n)
```
