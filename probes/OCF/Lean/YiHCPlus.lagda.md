# 验收一侧: 孩子取 ω+1 (ℕ 极限层号之上的后继层), 折到有限层与折到 ω 层的保持, 判据

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提. 层 `ℓ₊ = Sᶜ Lω` 上的关系 `M₊` (ω 槽位的分支关系与孩子关系都是封闭族 `Mω`); `Mβ₊`: Ω 树对着 Ω_{ω+1}; `Fold₊.LFf`, `LFw`: `YiRBSib` 的折叠把 `M₊ a x` 送到 `M j (ψ_j(t₀ + a))` 与 `Mω (ψ_ω(t₀ + a))`, 对一切推导; 回灌链 `chainω` (第 0 步用 `leafω`).
> 判据 `crit₊`: 兄弟孩子写法在孩子 `suc ωᶜ` 处的那一支对着 ψ₂(Ω_{ω+1}), 陈述在封闭族 `M 2` 上. 未封闭的族上同一条证明路线的第 0 步被 `YiLRNeg.chain0₊` 否定; 这里的 `chain0₊` 是同一陈述在封闭族上的肯定.
> 来源: `LFf` 的各行照 `YiHCLim.Lim.Fold` (`LFω`, `LFΩ`, `LFΩ-lim`, `LFΩ-keep`, `chain`, `gbL`), 路径多一步 `inc tt`; ω 槽位与目标 ω 层的各行是新的. 量化域: 孩子是有限读回层号的 ℕ 极限层 (`Lim` 的参数), `k ≤ d k`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiHCPlus where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; node⁺)
open import OCF.Lean.YiRBSib
open import OCF.Lean.YiRBFam using (ψ-⊵)
open import OCF.Lean.YiRBCrit using (two; sh; gˢ; wˢ)
open import OCF.Lean.YiRLCrit using (ℓˢ; oˢ)
open import OCF.Lean.YiKVRel using (_⊴_; ⊴r; ++[])
open import OCF.Lean.YiKCStep using (⊴-trans)
open import OCF.Lean.YiHCRel using (Mᴴ; mz; m1; mL; mΩ; mU; mw; mc)
import OCF.Align.EboLeanDef as E
open E using (cof; cΩ; fsT; γT; natT; sucT; cmpᵀ; gt)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ; cofK; fsTK; cofG; fsnG)
open import OCF.Lean.YiDCRel using (app≤)
open import OCF.Lean.YiCLFam using (fn; levP)
open import OCF.Lean.YiCLLow using (Sb; s0; pth; penJ)
open import OCF.Lean.YiCLPhi using (ωᵀ)
open import OCF.Lean.YiCLCrit using (ωᶜ)
open import OCF.Lean.YiHCFam using (M; LwP; mwN; mcJ; zlJ; nextJ; cumJ; mLJ; mΩP; ΩJ)
open import OCF.Lean.YiLRBridge using (Sᶜ; NwB; τ; τ₂; comp)
open import OCF.Lean.YiHCBridge using (MB; LwB; kcaseB; kcaseB₂; feedB)
open import OCF.Lean.YiLRLow using (cWC; Gᶜ; eᶜ; Rᶜ; canRᶜ)
open import OCF.Lean.YiHCLim using (module Lim; hβ₂; atω)
open import OCF.Lean.YiHCOmega using (ψᵘ; appᵘ; gtω-nat; gtω-self; penB; module Tω)
```

## 层, 关系, Ω 树, 底的条件

```agda
gtN : ∀ j {ν} → ν ≡ ωᵀ → cmpᵀ (sucT ν) (natT j) ≡ gt
gtN j refl = gtω-nat j

gtS : ∀ {ν} → ν ≡ ωᵀ → cmpᵀ (sucT ν) ωᵀ ≡ gt
gtS refl = gtω-self

module Plus (G : ℕ → L) (d : ℕ → ℕ) (eG : ∀ n → G n ≡ fn (d n)) (R : (n : ℕ) → G n ≤ G (suc n))
            (canR : ∀ n → Σ (Sb (d (suc n)) (d n)) λ s → τ₂ (eG n) (eG (suc n)) (R n) ≡ pth s)
            (dk : ∀ k → k ≤ⁿ d k) (oc : (k : ℕ) → Ok (G k)) where
  open Lim G d eG R canR
  open Tω G d eG R canR using (ψω; leafω; module Gω; module Self)

  ℓ₊ : L
  ℓ₊ = Sᶜ Lω

  o₊ : Ok ℓ₊
  o₊ = tt , λ _ → (R , oc)

  Low₊ : (p : Pos ℓ₊) → E.T → Br ℓ₊ p → Set
  Low₊ (inj₁ ())
  Low₊ (inj₂ (tt , inj₁ tt)) = Mω
  Low₊ (inj₂ (tt , inj₂ p))  = Lowω p

  Nu₊ : Pos ℓ₊ → E.T → Set
  Nu₊ (inj₁ ())
  Nu₊ (inj₂ (tt , inj₁ tt)) ν = ν ≡ ωᵀ
  Nu₊ (inj₂ (tt , inj₂ p))  = Nuω p

  M₊ : E.T → Tr ℓ₊ → Set
  M₊ = Mᴴ (Sig ℓ₊) Low₊ (λ _ → Mω) Nu₊

  Mβ₊ : M₊ (E.Ωt (sucT ωᵀ)) (proj₁ (Ωt ℓ₊))
  Mβ₊ = mΩ refl refl (λ η c l → mU mz (mw l ◃s))

  record GB₊ (B : Base ℓ₊) (t₀ : E.T) : Set where
    constructor mkGB₊
    field
      fΩ : ∀ m {i} (si : Sb (d m) i) (u : fn i ≤ G m) → τ (eG m) u ≡ pth si
         → proj₁ (Ωt (fn i)) ⊴ proj₁ (B (fn i) (inc tt (inc m u)))
      fM : ∀ m {i} (si : Sb (d m) i) (u : fn i ≤ G m) → τ (eG m) u ≡ pth si
         → M i (ψᴺ i t₀) (proj₁ (B (fn i) (inc tt (inc m u))))
      ωΩ : proj₁ (Ωt Lω) ⊴ proj₁ (B Lω (inc tt self))
      ωM : Mω (ψω t₀) (proj₁ (B Lω (inc tt self)))
  open GB₊ public

  gb₊₀ : GB₊ (B₀ ℓ₊) []
  gb₊₀ = mkGB₊ (λ m si u q → ⊴r) (λ m {i} si u q → ΩJ i (Ωt (fn i)) ⊴r) ⊴r (leafω dk)
```

## 折叠的保持

`Ff`: 朝有限层 `fn j` (路径 `inc tt (inc n v)`, v 读成 `pth s`); `Fw`: 朝 ω 层 (路径 `inc tt self`). ω 槽位朝两个目标都不保留, 取回灌链 (`sω` 是回灌的函数: 折到 ω 层); 孩子 m 里的槽位朝有限层按 `kcaseB`, `kcaseB₂` 判定, 朝 ω 层保留. 嵌入一行: 朝有限层用 `Lim.Fold.LFω` (孩子的底满足 `GBω`, 即 `gbL`), 朝 ω 层用 `Tω.Self.PFω`.

```agda
  module Fold₊ (r : Rb ℓ₊) (B : Base ℓ₊) (t₀ : E.T) (gb : GB₊ B t₀) where

    Ff : ∀ {n j} → fn j ≤ G n → Tr⁺ (fn j) → Tr ℓ₊ → Tr⁺ (fn j)
    Ff {n} {j} v β x = ψ ℓ₊ o₊ r B (fn j) (inc tt (inc n v)) β x

    Fw : Tr⁺ Lω → Tr ℓ₊ → Tr⁺ Lω
    Fw β x = ψ ℓ₊ o₊ r B Lω (inc tt self) β x

    cb₊ : Tr ℓ₊ → Base Lω
    cb₊ x i u = ψ ℓ₊ o₊ r B i (inc tt u) (B i (inc tt u)) x

    sω : (Tr Lω → Tr ℓ₊) → Tr Lω → Tr Lω
    sω g z = proj₁ (Fw (B Lω (inc tt self)) (g z))

    sf : (m : ℕ) (t : Pos⁼ (G m)) → (Br⁼ (G m) t → Tr ℓ₊) → Br⁼ (G m) t → Br⁼ (G m) t
    sf m t g z = proj₂ (sl⁼ (G m) t)
      (proj₁ (ψ ℓ₊ o₊ r B (proj₁ (sl⁼ (G m) t)) (inc tt (inc m (posW⁼ (G m) t)))
                (B (proj₁ (sl⁼ (G m) t)) (inc tt (inc m (posW⁼ (G m) t)))) (g z)))

    mutual
      LFf : ∀ {n j} (v : fn j ≤ G n) (s : Sb (d n) j) → τ (eG n) v ≡ pth s
          → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
          → ∀ {a x} → M₊ a x → M j (ψᴺ j (t₀ ++ a)) (proj₁ (Ff v β x))
      LFf {n} {j} v s q β hβ (mz {x = x}) =
        ++[] (λ z → M j (ψᴺ j z) (proj₁ (Ff v β x))) t₀
          (zlJ j (λ y → proj₁ (Ff v β y)) (mono ℓ₊ o₊ r B (fn j) (inc tt (inc n v)) β) hβ x)
      LFf {n} {j} v s q β hβ (m1 {t = a} {x = x} e h) =
        nextJ j (Ff v β x) (cofψ1 (natT j) (t₀ ++ a) (cof++1 t₀ a e))
          (λ k → trans (fsnψ1 (natT j) (t₀ ++ a) k (cof++1 t₀ a e)) (cong (λ z → replicate k (E.ψ (natT j) z)) (pred++ t₀ a e)))
          (LFf v s q β hβ h)
      LFf {n} {j} v s q β hβ (mL {t = a} {x = x} e h) =
        mLJ j (cofψω (natT j) (t₀ ++ a) (cof++ω t₀ a e))
          (λ k → subst (λ z → M j z (proj₁ (Ff v β x)))
            (sym (trans (fsnψω (natT j) (t₀ ++ a) k (cof++ω t₀ a e)) (cong (ψᴺ j) (fsn++ t₀ a k e))))
            (LFf v s q β hβ (h k)))
      LFf v s q β hβ (mΩ {p = inj₁ ()} _ _ _)
      LFf v s q β hβ (mΩ {p = inj₂ (tt , inj₁ tt)} e nu h) = LFf-ω v s q β hβ e nu h
      LFf v s q β hβ (mΩ {p = inj₂ (tt , inj₂ (inj₁ ()))} _ _ _)
      LFf v s q β hβ (mΩ {p = inj₂ (tt , inj₂ (inj₂ (m , t)))} e nu h) = LFf-Ω v s q β hβ m t e nu h
      LFf {n} {j} v s q β hβ (mU {t = a} {s = s₁} {x = x} {y = y} h ch) =
        subst (λ z → M j (ψᴺ j z) (proj₁ (ψ Lω (R , oc) (proj₂ r tt) (cb₊ x) (fn j) (inc n v) (Ff v β x) y)))
          (++-assoc t₀ a s₁)
          (Fold.LFω oc (proj₂ r tt) (cb₊ x) (t₀ ++ a) (gbL h) v s q (Ff v β x) (LFf v s q β hβ h) ch)
      LFf {n} {j} v s q β hβ (mw h dd) = mwN j (LFf v s q β hβ h) (mono ℓ₊ o₊ r B (fn j) (inc tt (inc n v)) β dd)
      LFf {n} {j} v s q β hβ (mc le h) = mcJ j (app≤ j t₀ le) (LFf v s q β hβ h)

      gbL : ∀ {a x} → M₊ a x → GBω (cb₊ x) (t₀ ++ a)
      gbL {a} {x} h =
        mkGBω (λ m {i} si u qu → ⊴-trans (fΩ gb m si u qu)
                 (ψ-⊵ ℓ₊ o₊ r B (fn i) (inc tt (inc m u)) (B (fn i) (inc tt (inc m u))) x))
              (λ m {i} si u qu → LFf u si qu (B (fn i) (inc tt (inc m u))) (fM gb m si u qu) h)

      LFf-ω : ∀ {n j} (v : fn j ≤ G n) (s : Sb (d n) j) → τ (eG n) v ≡ pth s
            → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
            → ∀ {a ν} {g : Tr Lω → Tr ℓ₊} → cof a ≡ cΩ ν → ν ≡ ωᵀ → (∀ η c → Mω η c → M₊ (fsT a η) (g c))
            → M j (ψᴺ j (t₀ ++ a)) (proj₁ (limc⁺ (λ k → Ff v β (g (iter (sω g) zero k)))))
      LFf-ω {n} {j} v s q β hβ {a} {ν} {g} e nu h =
        mLJ j (cofG (natT j) (t₀ ++ a) (gtN j nu) (cof++Ω t₀ a e))
          (λ k → subst (λ z → M j z (proj₁ (limc⁺ (λ k′ → Ff v β (g (iter (sω g) zero k′))))))
            (sym (trans (fsnG (natT j) (t₀ ++ a) k (gtN j nu) (cof++Ω t₀ a e)) (cong (ψᴺ j) (fsT++ t₀ a (γT (t₀ ++ a) ν k) e))))
            (cumJ j (λ k′ → Ff v β (g (iter (sω g) zero k′))) (suc k)
              (LFf v s q β hβ (h (γT (t₀ ++ a) ν k) (iter (sω g) zero (suc k)) (chainω e nu h k)))))

      chainω : ∀ {a ν} {g : Tr Lω → Tr ℓ₊} → cof a ≡ cΩ ν → ν ≡ ωᵀ → (∀ η c → Mω η c → M₊ (fsT a η) (g c))
             → ∀ k → Mω (γT (t₀ ++ a) ν k) (iter (sω g) zero (suc k))
      chainω {g = g} e refl h zero =
        Gω.m⊴ (leafω dk) (⊴-trans (ωΩ gb) (ψ-⊵ ℓ₊ o₊ r B Lω (inc tt self) (B Lω (inc tt self)) (g zero)))
      chainω {a} {g = g} e refl h (suc k) =
        subst (λ z → Mω (ψω z) (sω g (iter (sω g) zero (suc k))))
          (sym (fsT++ t₀ a (γT (t₀ ++ a) ωᵀ k) e))
          (LFw (B Lω (inc tt self)) (ωM gb) (h (γT (t₀ ++ a) ωᵀ k) (iter (sω g) zero (suc k)) (chainω e refl h k)))

      LFf-Ω : ∀ {n j} (v : fn j ≤ G n) (s : Sb (d n) j) → τ (eG n) v ≡ pth s
            → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
            → (m : ℕ) (t : Pos⁼ (G m)) → ∀ {a ν} {g : Br⁼ (G m) t → Tr ℓ₊}
            → cof a ≡ cΩ ν → NwB (G m) (eG m) t ν → (∀ η c → LwB (G m) (eG m) t η c → M₊ (fsT a η) (g c))
            → M j (ψᴺ j (t₀ ++ a)) (proj₁ (Ff v β (Ω (inj₂ (tt , inj₂ (inj₂ (m , t)))) g)))
      LFf-Ω {n} {j} v s q β hβ m t {a} {ν} {g} e nu h =
        cWC (λ K → M j (ψᴺ j (t₀ ++ a)) (proj₁ (node⁺ K (λ z → Ff v β (g z)) (sf m t g)))) (way G R m n) (wc m n)
          (λ u c → kcaseB₂ (G m) (G n) (eG m) (eG n) (oc n) u (proj₁ c) (proj₂ c) t v s q nu
                     (λ K → M j (ψᴺ j (t₀ ++ a)) (proj₁ (node⁺ K (λ z → Ff v β (g z)) (sf m t g))))
                     (λ gtq → LFf-lim v s q β hβ m t e nu h gtq)
                     (λ qq cv eq nq lw → LFf-keep v s q β hβ m t e nu h qq cv eq nq lw))
          (λ u c → kcaseB (G m) (eG m) (oc m) t (v ∙ u) (comp (proj₁ c) s) (∙q q u c) nu
                     (λ K → M j (ψᴺ j (t₀ ++ a)) (proj₁ (node⁺ K (λ z → Ff v β (g z)) (sf m t g))))
                     (λ gtq → LFf-lim v s q β hβ m t e nu h gtq)
                     (λ qq cv eq nq lw → LFf-keep v s q β hβ m t e nu h qq cv eq nq lw))

      LFf-lim : ∀ {n j} (v : fn j ≤ G n) (s : Sb (d n) j) → τ (eG n) v ≡ pth s
              → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
              → (m : ℕ) (t : Pos⁼ (G m)) → ∀ {a ν} {g : Br⁼ (G m) t → Tr ℓ₊}
              → cof a ≡ cΩ ν → NwB (G m) (eG m) t ν → (∀ η c → LwB (G m) (eG m) t η c → M₊ (fsT a η) (g c))
              → cmpᵀ (sucT ν) (natT j) ≡ gt
              → M j (ψᴺ j (t₀ ++ a)) (proj₁ (limc⁺ (λ k → Ff v β (g (iter (sf m t g) (bz⁼ (G m) t) k)))))
      LFf-lim {n} {j} v s q β hβ m t {a} {ν} {g} e nu h gtq =
        mLJ j (cofG (natT j) (t₀ ++ a) gtq (cof++Ω t₀ a e))
          (λ k → subst (λ z → M j z (proj₁ (limc⁺ (λ k′ → Ff v β (g (iter (sf m t g) (bz⁼ (G m) t) k′))))))
            (sym (trans (fsnG (natT j) (t₀ ++ a) k gtq (cof++Ω t₀ a e)) (cong (ψᴺ j) (fsT++ t₀ a (γT (t₀ ++ a) ν k) e))))
            (cumJ j (λ k′ → Ff v β (g (iter (sf m t g) (bz⁼ (G m) t) k′))) (suc k)
              (LFf v s q β hβ (h (γT (t₀ ++ a) ν k) (iter (sf m t g) (bz⁼ (G m) t) (suc k)) (chainf m t e nu h k)))))

      LFf-keep : ∀ {n j} (v : fn j ≤ G n) (s : Sb (d n) j) → τ (eG n) v ≡ pth s
               → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
               → (m : ℕ) (t : Pos⁼ (G m)) → ∀ {a ν} {g : Br⁼ (G m) t → Tr ℓ₊}
               → cof a ≡ cΩ ν → NwB (G m) (eG m) t ν → (∀ η c → LwB (G m) (eG m) t η c → M₊ (fsT a η) (g c))
               → (qq : Pos (fn j)) (cv : Br (fn j) qq → Br⁼ (G m) t) (eq : cv (fromBr (fn j) qq zero) ≡ bz⁼ (G m) t)
               → ν ≡ natT (levP j qq) → (∀ η c → LwP j qq η c → LwB (G m) (eG m) t η (cv c))
               → M j (ψᴺ j (t₀ ++ a)) (Ω qq (λ z → proj₁ (Ff v β (g (cv z)))))
      LFf-keep {n} {j} v s q β hβ m t {a} {ν} {g} e nu h qq cv eq nq lw =
        mΩP j (cofK (natT j) (t₀ ++ a) (penJ j qq nq) (cof++Ω t₀ a e)) nq
          (λ η c l → subst (λ z → M j z (proj₁ (Ff v β (g (cv c)))))
            (sym (trans (fsTK (natT j) (t₀ ++ a) η (penJ j qq nq) (cof++Ω t₀ a e)) (cong (ψᴺ j) (fsT++ t₀ a η e))))
            (LFf v s q β hβ (h η (cv c) (lw η c l))))

      chainf : ∀ m (t : Pos⁼ (G m)) → ∀ {a ν} {g : Br⁼ (G m) t → Tr ℓ₊}
             → cof a ≡ cΩ ν → NwB (G m) (eG m) t ν → (∀ η c → LwB (G m) (eG m) t η c → M₊ (fsT a η) (g c))
             → ∀ k → LwB (G m) (eG m) t (γT (t₀ ++ a) ν k) (iter (sf m t g) (bz⁼ (G m) t) (suc k))
      chainf m t {a} {ν} {g} e nu h zero =
        feedB (G m) (eG m) t nu (γT (t₀ ++ a) ν zero)
          (λ k w → proj₁ (ψ ℓ₊ o₊ r B k (inc tt (inc m w)) (B k (inc tt (inc m w))) (g (bz⁼ (G m) t))))
          (λ {i} si u qu eqν → subst (λ μ → M i (E.Ωt μ) (proj₁ (ψ ℓ₊ o₊ r B (fn i) (inc tt (inc m u)) (B (fn i) (inc tt (inc m u))) (g (bz⁼ (G m) t)))))
             (sym eqν)
             (ΩJ i (ψ ℓ₊ o₊ r B (fn i) (inc tt (inc m u)) (B (fn i) (inc tt (inc m u))) (g (bz⁼ (G m) t)))
                (⊴-trans (fΩ gb m si u qu) (ψ-⊵ ℓ₊ o₊ r B (fn i) (inc tt (inc m u)) (B (fn i) (inc tt (inc m u))) (g (bz⁼ (G m) t))))))
      chainf m t {a} {ν} {g} e nu h (suc k) =
        feedB (G m) (eG m) t nu (γT (t₀ ++ a) ν (suc k))
          (λ k′ w → proj₁ (ψ ℓ₊ o₊ r B k′ (inc tt (inc m w)) (B k′ (inc tt (inc m w))) (g (iter (sf m t g) (bz⁼ (G m) t) (suc k)))))
          (λ {i} si u qu eqν →
             subst (λ μ → M i (E.ψ μ (fsT (t₀ ++ a) (γT (t₀ ++ a) ν k)) ∷ [])
                            (proj₁ (ψ ℓ₊ o₊ r B (fn i) (inc tt (inc m u)) (B (fn i) (inc tt (inc m u))) (g (iter (sf m t g) (bz⁼ (G m) t) (suc k))))))
               (sym eqν)
               (subst (λ z → M i (ψᴺ i z) (proj₁ (ψ ℓ₊ o₊ r B (fn i) (inc tt (inc m u)) (B (fn i) (inc tt (inc m u))) (g (iter (sf m t g) (bz⁼ (G m) t) (suc k))))))
                 (sym (fsT++ t₀ a (γT (t₀ ++ a) ν k) e))
                 (LFf u si qu (B (fn i) (inc tt (inc m u))) (fM gb m si u qu)
                   (h (γT (t₀ ++ a) ν k) (iter (sf m t g) (bz⁼ (G m) t) (suc k)) (chainf m t e nu h k)))))

      LFw : (β : Tr⁺ Lω) → Mω (ψω t₀) (proj₁ β)
          → ∀ {a x} → M₊ a x → Mω (ψω (t₀ ++ a)) (proj₁ (Fw β x))
      LFw β hβ (mz {x = x}) =
        ++[] (λ z → Mω (ψω z) (proj₁ (Fw β x))) t₀
          (Gω.m-zl (λ y → proj₁ (Fw β y)) (mono ℓ₊ o₊ r B Lω (inc tt self) β) hβ x)
      LFw β hβ (m1 {t = a} {x = x} e h) =
        Gω.m-next (Fw β x) (cofψ1 ωᵀ (t₀ ++ a) (cof++1 t₀ a e))
          (λ k → trans (fsnψ1 ωᵀ (t₀ ++ a) k (cof++1 t₀ a e)) (cong (λ z → replicate k (E.ψ ωᵀ z)) (pred++ t₀ a e)))
          (LFw β hβ h)
      LFw β hβ (mL {t = a} {x = x} e h) =
        mL (cofψω ωᵀ (t₀ ++ a) (cof++ω t₀ a e))
          (λ k → subst (λ z → Mω z (proj₁ (Fw β x)))
            (sym (trans (fsnψω ωᵀ (t₀ ++ a) k (cof++ω t₀ a e)) (cong ψω (fsn++ t₀ a k e))))
            (LFw β hβ (h k)))
      LFw β hβ (mΩ {p = inj₁ ()} _ _ _)
      LFw β hβ (mΩ {t = a} {ν = ν} {p = inj₂ (tt , inj₁ tt)} {g = g} e nu h) =
        mL (cofG ωᵀ (t₀ ++ a) (gtS nu) (cof++Ω t₀ a e))
          (λ k → subst (λ z → Mω z (proj₁ (limc⁺ (λ k′ → Fw β (g (iter (sω g) zero k′))))))
            (sym (trans (fsnG ωᵀ (t₀ ++ a) k (gtS nu) (cof++Ω t₀ a e)) (cong ψω (fsT++ t₀ a (γT (t₀ ++ a) ν k) e))))
            (Gω.m-cum (λ k′ → Fw β (g (iter (sω g) zero k′))) (suc k)
              (LFw β hβ (h (γT (t₀ ++ a) ν k) (iter (sω g) zero (suc k)) (chainω e nu h k)))))
      LFw β hβ (mΩ {p = inj₂ (tt , inj₂ (inj₁ ()))} _ _ _)
      LFw β hβ (mΩ {t = a} {p = inj₂ (tt , inj₂ (inj₂ (m , t)))} {g = g} e nu h) =
        mΩ (cofK ωᵀ (t₀ ++ a) (penB (G m) (eG m) t nu) (cof++Ω t₀ a e)) nu
          (λ η c l → subst (λ z → Mω z (proj₁ (Fw β (g c))))
            (sym (trans (fsTK ωᵀ (t₀ ++ a) η (penB (G m) (eG m) t nu) (cof++Ω t₀ a e)) (cong ψω (fsT++ t₀ a η e))))
            (LFw β hβ (h η c l)))
      LFw β hβ (mU {t = a} {s = s₁} {x = x} {y = y} h ch) =
        subst (λ z → Mω (ψω z) (Self.F oc (proj₂ r tt) (cb₊ x) (Fw β x) y)) (++-assoc t₀ a s₁)
          (Self.PFω oc (proj₂ r tt) (cb₊ x) (Fw β x) (LFw β hβ h) ch)
      LFw β hβ (mw h dd) = mw (LFw β hβ h) (mono ℓ₊ o₊ r B Lω (inc tt self) β dd)
      LFw β hβ (mc le h) = mc (appᵘ ωᵀ t₀ le) (LFw β hβ h)
```

## 实例: 孩子 `suc ωᶜ`, 判据

`chain0₊` 的陈述逐字是 `YiLRNeg.noFeedᶜ` 所否定的那一条, 关系换成封闭族.

```agda
le-sh : ∀ k → k ≤ⁿ sh k
le-sh zero    = z≤n
le-sh (suc k) = s≤s (le-sh k)

module P₊ = Plus Gᶜ sh eᶜ Rᶜ canRᶜ le-sh (proj₂ (oˢ ωᶜ))
module Wᶜ = Lim Gᶜ sh eᶜ Rᶜ canRᶜ
module Tᶜ = Tω Gᶜ sh eᶜ Rᶜ canRᶜ

lvl₊ : ℓˢ (suc ωᶜ) ≡ P₊.ℓ₊
lvl₊ = refl

ok₊ : oˢ (suc ωᶜ) ≡ P₊.o₊
ok₊ = refl

path₊ : wˢ (suc ωᶜ) ≡ inc tt (inc 0 self)
path₊ = refl

chain0₊ : Wᶜ.Mω (E.Ωt ωᵀ) (proj₁ (next⁺ (Ωt Wᶜ.Lω)))
chain0₊ = mw (Tᶜ.leafω le-sh) (◃l zero)

crit₊ : M 2 (ψᴺ 2 (E.Ωt (sucT ωᵀ))) (proj₁ (gˢ (suc ωᶜ)))
crit₊ = atω (suc ωᶜ)
  (P₊.Fold₊.LFf (rb-no P₊.ℓ₊) (B₀ P₊.ℓ₊) [] P₊.gb₊₀ {n = 0} {j = 2} self s0 refl (Ωt two) hβ₂ P₊.Mβ₊)
```
