# 嵌入的 Ω 树折叠：源层与高两层的目标层
不读记号；编译定理，层号 A（无 Ω 形状）与嵌入深度 d 都是变量：源层 `Tw A d` 上 `ups A d`（Ω_A 经 d 次后继形状嵌入）的折叠，按 `N` 不高于目标层 `S2 (Tw A d)` 上 `ups′ A d` 的折叠（`E`），前提只有底按 `N` 拉回有序、目标底不低于标准 Ω 树、起点按 `N` 有序；目标路径的上两级可取 `inc` 或 `inu`（`wrap`）。
三种自身路径情形各一条引理：链（`chain`，起点义务 `YiRRThree.Obl3` 的一般形，用目标链第 1 项），两级上折（`upup`、`uu`），以及 `climb`（d = 0）。`Ladder2` 照 `YiRRUp.Ladder` 搬来，两侧底不同；`PsiLadder` 是同一梯子，把上折换成自身折叠。不用传递性，不读记号。
不否定什么；实例在 [YiPTThree](YiPTThree.lagda.md)。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPTLadder where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiVRRel using (NoΩ)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiLXClimb using (Dom)
open import OCF.Lean.YiOFPath using (pull-base)
open import OCF.Lean.YiTYPath using (pull-ok)
open import OCF.Lean.YiRRRel
open import OCF.Lean.YiRRFold using (_⊴ⁿ_; inflA)
open import OCF.Lean.YiRRClimb using (Fit; fself; fS; fSi; climb)
open import OCF.Lean.YiRRUp using (predN)
```

## 层号、嵌入、目标路径

```agda
S1 S2 : L → L
S1 X = nd sS (λ _ → X)
S2 X = nd sS (λ _ → nd sS (λ _ → X))

v2 : ∀ {X} → X ⊑ S2 X
v2 = inc tt (inc tt self)

Tw : L → ℕ → L
Tw A zero    = A
Tw A (suc d) = nd sS (λ _ → Tw A d)

ups : (A : L) (d : ℕ) → Tr⁺ (Tw A d)
ups A zero    = Ωt A
ups A (suc d) = upz tt (ups A d)

ups′ : (A : L) (d : ℕ) → Tr⁺ (S2 (Tw A d))
ups′ A zero    = Ωt (S2 A)
ups′ A (suc d) = upz tt (ups′ A d)

wrap : ∀ {j} {h : ⊤ → L} → Bool → j ≤ h tt → j ≤ nd sS h
wrap false w = inc tt w
wrap true  w = inu (λ _ → w)

fitW : ∀ {j X} (b₁ b₂ : Bool) (u : j ≤ X) → Fit v2 u (wrap b₁ (wrap b₂ u))
fitW false false u = fSi (fSi fself)
fitW false true  u = fSi (fS fself)
fitW true  false u = fS (fSi fself)
fitW true  true  u = fS (fS fself)

rowT : ∀ {h : ⊤ → L} (o : Ok (nd sS h)) (r : Rb (nd sS h)) (B : Base (nd sS h)) (j : L) (b : Bool) (w : j ≤ h tt)
  (β : Tr⁺ j) (y : Tr (h tt)) (e : h tt ⊢ zero ◃ y)
  → ψ (nd sS h) o r B j (wrap b w) β (up zero tt y e) ≡ ψ (h tt) (proj₂ o tt) (proj₂ r tt) (λ i u → B i (inc tt u)) j w β y
rowT o r B j false w β y e = refl
rowT o r B j true  w β y e = refl
```

## 两侧底不同的上折梯子

```agda
module Ladder2 {ℓ k : L} (νk : NoΩ k) (d : Dn ℓ (S1 k)) (b b′ : Tr⁺ ℓ) (hb : N ℓ (proj₁ b) (proj₁ b′)) where
  a : Tr ℓ
  a = proj₁ (Up k (down d tt) b (proj₁ (Ωt k)))

  rung : ∀ {y} {e} → N (S1 k) (up zero tt (suc (proj₁ (Ωt k))) e) y → N ℓ a (proj₁ (Up (S1 k) d b′ y))
  rung (≼s r) = ≼l 0 (rung r)
  rung (≼l n r) = ≼l n (rung r)
  rung {e = e} (≼w {p = p} {g = g} r) =
    ≼w (subst (λ t → N ℓ a (proj₁ (Up (S1 k) d b′ (g t)))) (sym (mvFirst d p)) (rung {e = e} r))
  rung {e = e} (≼W {p = p} z ez k′) = ≼W (mvBr⁻ d p z) (mvE d p ez) (λ u r → rung {e = e} (k′ _ (mvN⁻ d p r)))
  rung (≼u {x = x} {c = c} {y = y₁} r) = ≼Up k (down d c) (Up (S1 k) d b′ x) y₁ (rung r)
  rung (u≼u {x′ = x} dx dy) = Up≼ k (down d tt) b (Up (S1 k) d b′ x) (≼Up (S1 k) d b′ x hb) (predN dy)

  ladder : ∀ {y} → N (S1 k) (proj₁ (Ωt (S1 k))) y → N ℓ a (proj₁ (Up (S1 k) d b′ y))
  ladder (≼s r) = ≼l 0 (ladder r)
  ladder (≼l n r) = ≼l n (ladder r)
  ladder (≼w {p = p} {g = g} r) =
    ≼w (subst (λ t → N ℓ a (proj₁ (Up (S1 k) d b′ (g t)))) (sym (mvFirst d p)) (ladder r))
  ladder (≼W {p = p} z ez k′) = ≼W (mvBr⁻ d p z) (mvE d p ez) (λ u r → ladder (k′ _ (mvN⁻ d p r)))
  ladder (≼u {x = x} {c = c} {y = y₁} r) = ≼Up k (down d c) (Up (S1 k) d b′ x) y₁ (ladder r)
  ladder (w≼w {p = inj₂ (tt , inj₁ tt)} h) =
    ≼W (mvBr⁻ d (inj₂ (tt , inj₁ tt)) (proj₁ (Ωt k))) (mvE d (inj₂ (tt , inj₁ tt)) (entry k νk))
      (λ u r → rung (h (proj₁ (Ωt k)) _ (mvN⁻ d (inj₂ (tt , inj₁ tt)) r)))
```

## 自身折叠的梯子

起点 σ 不低于 β 时, 右边是 σ 上的自身折叠, 输入树不低于本层 Ω 树, 左边是 β 上折一级的 Ω 树.

```agda
module PsiLadder {k : L} (νk : NoΩ k) (o : Ok (S1 k)) (r : Rb (S1 k)) (B : Base (S1 k))
  (β σ : Tr⁺ (S1 k)) (hσ : N (S1 k) (proj₁ β) (proj₁ σ)) where
  a : Tr (S1 k)
  a = proj₁ (Up k (down stop tt) β (proj₁ (Ωt k)))
  F : Tr (S1 k) → Tr (S1 k)
  F y = proj₁ (ψ (S1 k) o r B (S1 k) self σ y)

  rung : ∀ {y} {e} → N (S1 k) (up zero tt (suc (proj₁ (Ωt k))) e) y → N (S1 k) a (F y)
  rung (≼s q) = ≼l 0 (rung q)
  rung (≼l n q) = ≼l n (rung q)
  rung {e = e} (≼w q) = ≼w (rung {e = e} q)
  rung {e = e} (≼W z ez k′) = ≼W z ez (λ u q → rung {e = e} (k′ u q))
  rung (≼u {x = x} {c = c} {y = y₁} q) = ≼Up k (down stop c) (ψ (S1 k) o r B (S1 k) self σ x) y₁ (rung q)
  rung (u≼u {x′ = x} dx dy) =
    Up≼ k (down stop tt) β (ψ (S1 k) o r B (S1 k) self σ x) (inflA (S1 k) o r B (S1 k) self σ x hσ) (predN dy)

  ladder : ∀ {y} → N (S1 k) (proj₁ (Ωt (S1 k))) y → N (S1 k) a (F y)
  ladder (≼s q) = ≼l 0 (ladder q)
  ladder (≼l n q) = ≼l n (ladder q)
  ladder (≼w q) = ≼w (ladder q)
  ladder (≼W z ez k′) = ≼W z ez (λ u q → ladder (k′ u q))
  ladder (≼u {x = x} {c = c} {y = y₁} q) = ≼Up k (down stop c) (ψ (S1 k) o r B (S1 k) self σ x) y₁ (ladder q)
  ladder (w≼w {p = inj₂ (tt , inj₁ tt)} h) =
    ≼W (proj₁ (Ωt k)) (entry k νk) (λ u q → rung (h (proj₁ (Ωt k)) u q))
```

## 三种自身路径情形

`chain`: 目标在高两层的 Ω 树上走链 (不保留), 取链的第 1 项; 那一项是起点 β′ 上的自身折叠, 输入以槽位层的底为起点, 由 `Dom` 不低于槽位层的 Ω 树. `upup`: 目标是同一层上高两级的上折.

```agda
chain : (A : L) → NoΩ A → (o : Ok (S2 A)) (r : Rb (S2 A)) (B : Base (S2 A)) (b : Bool)
  (β β′ : Tr⁺ (S1 A)) → N (S1 A) (proj₁ β) (proj₁ β′)
  → N (S1 A) (proj₁ (Ωt (S1 A))) (proj₁ (B (S1 A) (inc tt self)))
  → N (S1 A) (proj₁ (Up A (down stop tt) β (proj₁ (Ωt A))))
      (proj₁ (ψ (S2 A) o r B (S1 A) (wrap b self) β′ (proj₁ (Ωt (S2 A)))))
chain A νA o r B false β β′ hb hP = ≼l 1 (right-add (≼l 0 (≼l 0
  (PsiLadder.ladder νA (proj₂ o tt) (proj₂ r tt) (λ i u → B i (inc tt u)) β β′ hb hP))) _)
chain A νA o r B true β β′ hb hP = ≼l 1 (right-add (≼l 0 (≼l 0
  (PsiLadder.ladder νA (proj₂ o tt) (proj₂ r tt) (λ i u → B i (inc tt u)) β β′ hb hP))) _)

upup : (A : L) → NoΩ A → ∀ {ℓ} (D : Dn ℓ (S2 A)) (β β′ : Tr⁺ ℓ) → N ℓ (proj₁ β) (proj₁ β′)
     → N ℓ (proj₁ (Up A (down (down D tt) tt) β (proj₁ (Ωt A)))) (proj₁ (Up (S2 A) D β′ (proj₁ (Ωt (S2 A)))))
upup A νA D β β′ hb =
  ≼W (mvBr⁻ D (inj₂ (tt , inj₁ tt)) (proj₁ (Ωt (S1 A)))) (mvE D (inj₂ (tt , inj₁ tt)) (entry (S1 A) νA))
    (λ u q → ≼l 0 (Ladder2.ladder νA (down D tt) β β′ hb (mvN⁻ D (inj₂ (tt , inj₁ tt)) q)))

uu : (A : L) → NoΩ A → (e : ℕ) → ∀ {ℓ} (D : Dn ℓ (S2 (Tw A e))) (β β′ : Tr⁺ ℓ) → N ℓ (proj₁ β) (proj₁ β′)
   → N ℓ (proj₁ (Up (Tw A e) (down (down D tt) tt) β (proj₁ (ups A e)))) (proj₁ (Up (S2 (Tw A e)) D β′ (proj₁ (ups′ A e))))
uu A νA zero    D β β′ hb = upup A νA D β β′ hb
uu A νA (suc e) D β β′ hb = uu A νA e (down D tt) β β′ hb
```

## 一般形

对 d 归纳: d = 0 是 `climb`; 路径经孩子时两侧各剥一级 (目标剥 `wrap` 的外层), 底沿 `inc tt` 推进; 路径是 `self` 时按 d 分到 `chain` 与 `uu`.

```agda
E : (A : L) → NoΩ A → (d : ℕ) (o′ : Ok (S2 (Tw A d))) (r : Rb (Tw A d)) (r′ : Rb (S2 (Tw A d)))
  (B : Base (Tw A d)) (B′ : Base (S2 (Tw A d))) → B ⊴ⁿ pull-base v2 B′ → Dom B′
  → (i : L) (u : i ≤ Tw A d) (b₁ b₂ : Bool) (β β′ : Tr⁺ i) → N i (proj₁ β) (proj₁ β′)
  → N i (proj₁ (ψ (Tw A d) (pull-ok v2 o′) r B i u β (proj₁ (ups A d))))
        (proj₁ (ψ (S2 (Tw A d)) o′ r′ B′ i (wrap b₁ (wrap b₂ u)) β′ (proj₁ (ups′ A d))))
E A νA zero o′ r r′ B B′ hB dB i u b₁ b₂ β β′ hβ = climb v2 (fitW b₁ b₂ u) νA o′ r r′ B B′ hB dB β β′ hβ
E A νA (suc d) o′ r r′ B B′ hB dB i (inc tt w) b₁ b₂ β β′ hβ =
  subst (λ t → N i (proj₁ (ψ (Tw A d) (pull-ok v2 (proj₂ o′ tt)) (proj₂ r tt) (λ i u → B i (inc tt u)) i w β (proj₁ (ups A d)))) (proj₁ t))
    (sym (rowT o′ r′ B′ i b₁ (wrap b₂ (inc tt w)) β′ (proj₁ (ups′ A d)) (proj₂ (ups′ A d))))
    (E A νA d (proj₂ o′ tt) (proj₂ r tt) (proj₂ r′ tt) (λ i u → B i (inc tt u)) (λ i u → B′ i (inc tt u))
       (λ i u _ → hB i (inc tt u) tt) (λ i u _ → dB i (inc tt u) tt) i w b₂ false β β′ hβ)
E A νA (suc d) o′ r r′ B B′ hB dB i (inu vs) b₁ b₂ β β′ hβ =
  subst (λ t → N i (proj₁ (ψ (Tw A d) (pull-ok v2 (proj₂ o′ tt)) (proj₂ r tt) (λ i u → B i (inc tt u)) i (vs tt) β (proj₁ (ups A d)))) (proj₁ t))
    (sym (rowT o′ r′ B′ i b₁ (wrap b₂ (inu vs)) β′ (proj₁ (ups′ A d)) (proj₂ (ups′ A d))))
    (E A νA d (proj₂ o′ tt) (proj₂ r tt) (proj₂ r′ tt) (λ i u → B i (inc tt u)) (λ i u → B′ i (inc tt u))
       (λ i u _ → hB i (inc tt u) tt) (λ i u _ → dB i (inc tt u) tt) i (vs tt) b₂ true β β′ hβ)
E A νA (suc zero) o′ r r′ B B′ hB dB .(S1 A) self b₁ b₂ β β′ hβ =
  subst (λ t → N (S1 A) (proj₁ (Up A (down stop tt) β (proj₁ (Ωt A)))) (proj₁ t))
    (sym (rowT o′ r′ B′ (S1 A) b₁ (wrap b₂ self) β′ (proj₁ (Ωt (S2 A))) (proj₂ (Ωt (S2 A)))))
    (chain A νA (proj₂ o′ tt) (proj₂ r′ tt) (λ i u → B′ i (inc tt u)) b₂ β β′ hβ
       (le⊴ (Ωt≼ (S1 A) νA) (dB (S1 A) (inc tt (inc tt self)) tt)))
E A νA (suc (suc zero)) o′ r r′ B B′ hB dB .(S2 A) self b₁ b₂ β β′ hβ =
  subst (λ t → N (S2 A) (proj₁ (Up A (down (down stop tt) tt) β (proj₁ (Ωt A)))) (proj₁ t))
    (sym (rowT o′ r′ B′ (S2 A) b₁ (wrap b₂ self) β′ (proj₁ (ups′ A 1)) (proj₂ (ups′ A 1))))
    (subst (λ t → N (S2 A) (proj₁ (Up A (down (down stop tt) tt) β (proj₁ (Ωt A)))) (proj₁ t))
      (sym (rowT (proj₂ o′ tt) (proj₂ r′ tt) (λ i u → B′ i (inc tt u)) (S2 A) b₂ self β′ (proj₁ (Ωt (S2 A))) (proj₂ (Ωt (S2 A)))))
      (uu A νA zero stop β β′ hβ))
E A νA (suc (suc (suc e))) o′ r r′ B B′ hB dB .(S2 (Tw A (suc e))) self b₁ b₂ β β′ hβ =
  subst (λ t → N (S2 (Tw A (suc e))) (proj₁ (Up (Tw A (suc e)) (down (down stop tt) tt) β (proj₁ (ups A (suc e))))) (proj₁ t))
    (sym (rowT o′ r′ B′ (S2 (Tw A (suc e))) b₁ (wrap b₂ self) β′ (proj₁ (ups′ A (suc (suc e)))) (proj₂ (ups′ A (suc (suc e))))))
    (subst (λ t → N (S2 (Tw A (suc e))) (proj₁ (Up (Tw A (suc e)) (down (down stop tt) tt) β (proj₁ (ups A (suc e))))) (proj₁ t))
      (sym (rowT (proj₂ o′ tt) (proj₂ r′ tt) (λ i u → B′ i (inc tt u)) (S2 (Tw A (suc e))) b₂ self β′
         (proj₁ (ups′ A (suc e))) (proj₂ (ups′ A (suc e)))))
      (uu A νA (suc e) stop β β′ hβ))
```
