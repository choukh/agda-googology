# 目标层上的一步接口: 替身在非零孩子处承载 ψ_ν(Ω_{ν+1})

> 验收文件 (读记号), 不进成品; 树、折叠、合法性不改. 判决: 编译定理, 前提是目标层 j 上的接口 (遗传封闭的关系 `Mj`, 读法 ν, 槽位读法低于 ν, Ω 树对着 Ω_ν, 折到自身的保持); 实例见 [YiSVOmega](YiSVOmega.lagda.md) (ω 层与有限层).
> 结论: j 之上的后继层朝 j 的折叠 (指定孩子路径 `LFw` 与一致路径 `LFu`) 把 `M₊ a x` 送到 `Mj (ψ_ν(t₀ + a))`; 所以 `seen` 在一切孩子处承载 ψ_ν(Ω_ν) (`seen-all`), 在一切非零孩子处承载 ψ_ν(Ω_{ν+1}) (`seen-nz`).
> 不给出什么: 再往上一层 (ψ_ν(Ω_{ν+2})) 要 j 之上后继层的同一接口, 没有做.
> 来源: `LFw`, `chain`, `LFu` 各行照 `YiHCPlus.Fold₊.LFw`, `chainω` (ω 层换成带接口的 j; `LFu` 是一致路径上的同一证明).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSVStep where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiRBSib using (Rb; rb-no; ψ; mono)
import OCF.Lean.YiKVRel as K
open import OCF.Lean.YiKVRel using (++[])
open import OCF.Lean.YiHCRel using (Mᴴ; mz; m1; mL; mΩ; mU; mw; mc; module Gen)
import OCF.Align.EboLeanDef as E
open E using (cof; cΩ; fsT; γT; sucT; cmpᵀ; gt)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiANFam using (Pen; cofK; fsTK; cofG; fsnG)
open import OCF.Lean.YiHCOmega using (ψᵘ; appᵘ)
open import OCF.Lean.YiBSBase using (seen)
open import OCF.Lean.YiSVMono

to : ∀ {ℓ} {x y : Tr ℓ} → x ⊴ y → x K.⊴ y
to ⊴r     = K.⊴r
to (⊴◃ d) = K.⊴◃ d

module Step (j : L) (oj : Ok j) (ν : E.T)
  (Low : (p : Pos j) → E.T → Br j p → Set) (Chd : (c : CH j) → E.T → ChT j c → Set) (Nu : Pos j → E.T → Set)
  (gtν : cmpᵀ (sucT ν) ν ≡ gt)
  (cofS : cof (E.Ωt (sucT ν)) ≡ cΩ ν)
  (fsS : ∀ η → fsT (E.Ωt (sucT ν)) η ≡ η)
  (pen : (p : Pos j) {ν′ : E.T} → Nu p ν′ → Pen (cmpᵀ (sucT ν′) ν))
  (leaf : Mᴴ (Sig j) Low Chd Nu (E.Ωt ν) (proj₁ (Ωt j)))
  (selfP : (r : Rb j) (B : Base j) (β : Tr⁺ j) {P₀ : E.T} → Mᴴ (Sig j) Low Chd Nu (ψᵘ ν P₀) (proj₁ β)
         → ∀ {a x} → Mᴴ (Sig j) Low Chd Nu a x → Mᴴ (Sig j) Low Chd Nu (ψᵘ ν (P₀ ++ a)) (proj₁ (ψ j oj r B j self β x)))
  where

  Mj : E.T → Tr j → Set
  Mj = Mᴴ (Sig j) Low Chd Nu

  module Gj = Gen {Sig j} {Low} {Chd} {Nu}

  ℓ₊ : L
  ℓ₊ = nd sS (λ _ → j)

  o₊ : Ok ℓ₊
  o₊ = tt , λ _ → oj

  Low₊ : (p : Pos ℓ₊) → E.T → Br ℓ₊ p → Set
  Low₊ (inj₁ ())
  Low₊ (inj₂ (tt , inj₁ tt)) = Mj
  Low₊ (inj₂ (tt , inj₂ p))  = Low p

  Nu₊ : Pos ℓ₊ → E.T → Set
  Nu₊ (inj₁ ())
  Nu₊ (inj₂ (tt , inj₁ tt)) ν′ = ν′ ≡ ν
  Nu₊ (inj₂ (tt , inj₂ p))     = Nu p

  M₊ : E.T → Tr ℓ₊ → Set
  M₊ = Mᴴ (Sig ℓ₊) Low₊ (λ _ → Mj) Nu₊

  Mβ₊ : M₊ (E.Ωt (sucT ν)) (proj₁ (Ωt ℓ₊))
  Mβ₊ = mΩ cofS refl (λ η c l → subst (λ s → M₊ s (up zero tt (suc c) (z◃ c ◃s))) (sym (fsS η)) (mU mz (mw l ◃s)))

  record GB₊ (B : Base ℓ₊) (t₀ : E.T) : Set where
    constructor mkGB₊
    field
      bΩ : proj₁ (Ωt j) K.⊴ proj₁ (B j (inc tt self))
      bM : Mj (ψᵘ ν t₀) (proj₁ (B j (inc tt self)))
  open GB₊ public

  good : (B : Base ℓ₊) → OKB B → GB₊ B []
  good B ok = mkGB₊ (to (ok j (inc tt self))) (Gj.m⊴ leaf (to (ok j (inc tt self))))

  module Fold₊ (r : Rb ℓ₊) (B : Base ℓ₊) (t₀ : E.T) (gb : GB₊ B t₀) where

    Fw Fu : Tr⁺ j → Tr ℓ₊ → Tr⁺ j
    Fw β x = ψ ℓ₊ o₊ r B j (inc tt self) β x
    Fu β x = ψ ℓ₊ o₊ r B j (inu (λ _ → self)) β x

    cb₊ : Tr ℓ₊ → Base j
    cb₊ x i u = ψ ℓ₊ o₊ r B i (inc tt u) (B i (inc tt u)) x

    sω : (Tr j → Tr ℓ₊) → Tr j → Tr j
    sω g z = proj₁ (Fw (B j (inc tt self)) (g z))

    ψ-⊵ᴷ : (β : Tr⁺ j) (x : Tr ℓ₊) → proj₁ β K.⊴ proj₁ (Fw β x)
    ψ-⊵ᴷ β x = to (ψ-⊵ ℓ₊ o₊ r B j (inc tt self) β x)

    ⊴t : {a b c : Tr j} → a K.⊴ b → b K.⊴ c → a K.⊴ c
    ⊴t p K.⊴r     = p
    ⊴t p (K.⊴◃ e) = K.⊴◃ (K.⊴-◃ p e)

    mutual
      LFw : (β : Tr⁺ j) → Mj (ψᵘ ν t₀) (proj₁ β) → ∀ {a x} → M₊ a x → Mj (ψᵘ ν (t₀ ++ a)) (proj₁ (Fw β x))
      LFw β hβ (mz {x = x}) =
        ++[] (λ z → Mj (ψᵘ ν z) (proj₁ (Fw β x))) t₀
          (Gj.m-zl (λ y → proj₁ (Fw β y)) (mono ℓ₊ o₊ r B j (inc tt self) β) hβ x)
      LFw β hβ (m1 {t = a} {x = x} e h) =
        Gj.m-next (Fw β x) (cofψ1 ν (t₀ ++ a) (cof++1 t₀ a e))
          (λ k → trans (fsnψ1 ν (t₀ ++ a) k (cof++1 t₀ a e)) (cong (λ z → replicate k (E.ψ ν z)) (pred++ t₀ a e)))
          (LFw β hβ h)
      LFw β hβ (mL {t = a} {x = x} e h) =
        mL (cofψω ν (t₀ ++ a) (cof++ω t₀ a e))
          (λ k → subst (λ z → Mj z (proj₁ (Fw β x)))
            (sym (trans (fsnψω ν (t₀ ++ a) k (cof++ω t₀ a e)) (cong (ψᵘ ν) (fsn++ t₀ a k e))))
            (LFw β hβ (h k)))
      LFw β hβ (mΩ {p = inj₁ ()} _ _ _)
      LFw β hβ (mΩ {t = a} {ν = ν′} {p = inj₂ (tt , inj₁ tt)} {g = g} e nu h) =
        mL (cofG ν (t₀ ++ a) (gt′ nu) (cof++Ω t₀ a e))
          (λ k → subst (λ z → Mj z (proj₁ (limc⁺ (λ k′ → Fw β (g (iter (sω g) zero k′))))))
            (sym (trans (fsnG ν (t₀ ++ a) k (gt′ nu) (cof++Ω t₀ a e)) (cong (ψᵘ ν) (fsT++ t₀ a (γT (t₀ ++ a) ν′ k) e))))
            (Gj.m-cum (λ k′ → Fw β (g (iter (sω g) zero k′))) (suc k)
              (LFw β hβ (h (γT (t₀ ++ a) ν′ k) (iter (sω g) zero (suc k)) (chain e nu h k)))))
      LFw β hβ (mΩ {t = a} {p = inj₂ (tt , inj₂ p)} {g = g} e nu h) =
        mΩ (cofK ν (t₀ ++ a) (pen p nu) (cof++Ω t₀ a e)) nu
          (λ η c l → subst (λ z → Mj z (proj₁ (Fw β (g c))))
            (sym (trans (fsTK ν (t₀ ++ a) η (pen p nu) (cof++Ω t₀ a e)) (cong (ψᵘ ν) (fsT++ t₀ a η e))))
            (LFw β hβ (h η c l)))
      LFw β hβ (mU {t = a} {s = s₁} {x = x} {y = y} h ch) =
        subst (λ z → Mj (ψᵘ ν z) (proj₁ (ψ j oj (proj₂ r tt) (cb₊ x) j self (Fw β x) y))) (++-assoc t₀ a s₁)
          (selfP (proj₂ r tt) (cb₊ x) (Fw β x) (LFw β hβ h) ch)
      LFw β hβ (mw h dd) = mw (LFw β hβ h) (mono ℓ₊ o₊ r B j (inc tt self) β dd)
      LFw β hβ (mc le h) = mc (appᵘ ν t₀ le) (LFw β hβ h)

      gt′ : ∀ {ν′} → ν′ ≡ ν → cmpᵀ (sucT ν′) ν ≡ gt
      gt′ refl = gtν

      chain : ∀ {a ν′} {g : Tr j → Tr ℓ₊} → cof a ≡ cΩ ν′ → ν′ ≡ ν → (∀ η c → Mj η c → M₊ (fsT a η) (g c))
            → ∀ k → Mj (γT (t₀ ++ a) ν′ k) (iter (sω g) zero (suc k))
      chain {g = g} e refl h zero =
        Gj.m⊴ leaf (⊴t (bΩ gb) (ψ-⊵ᴷ (B j (inc tt self)) (g zero)))
      chain {a} {g = g} e refl h (suc k) =
        subst (λ z → Mj (ψᵘ ν z) (sω g (iter (sω g) zero (suc k))))
          (sym (fsT++ t₀ a (γT (t₀ ++ a) ν k) e))
          (LFw (B j (inc tt self)) (bM gb) (h (γT (t₀ ++ a) ν k) (iter (sω g) zero (suc k)) (chain e refl h k)))

    LFu : (β : Tr⁺ j) → Mj (ψᵘ ν t₀) (proj₁ β) → ∀ {a x} → M₊ a x → Mj (ψᵘ ν (t₀ ++ a)) (proj₁ (Fu β x))
    LFu β hβ (mz {x = x}) =
      ++[] (λ z → Mj (ψᵘ ν z) (proj₁ (Fu β x))) t₀
        (Gj.m-zl (λ y → proj₁ (Fu β y)) (mono ℓ₊ o₊ r B j (inu (λ _ → self)) β) hβ x)
    LFu β hβ (m1 {t = a} {x = x} e h) =
      Gj.m-next (Fu β x) (cofψ1 ν (t₀ ++ a) (cof++1 t₀ a e))
        (λ k → trans (fsnψ1 ν (t₀ ++ a) k (cof++1 t₀ a e)) (cong (λ z → replicate k (E.ψ ν z)) (pred++ t₀ a e)))
        (LFu β hβ h)
    LFu β hβ (mL {t = a} {x = x} e h) =
      mL (cofψω ν (t₀ ++ a) (cof++ω t₀ a e))
        (λ k → subst (λ z → Mj z (proj₁ (Fu β x)))
          (sym (trans (fsnψω ν (t₀ ++ a) k (cof++ω t₀ a e)) (cong (ψᵘ ν) (fsn++ t₀ a k e))))
          (LFu β hβ (h k)))
    LFu β hβ (mΩ {p = inj₁ ()} _ _ _)
    LFu β hβ (mΩ {t = a} {ν = ν′} {p = inj₂ (tt , inj₁ tt)} {g = g} e nu h) =
      mL (cofG ν (t₀ ++ a) (gt′ nu) (cof++Ω t₀ a e))
        (λ k → subst (λ z → Mj z (proj₁ (limc⁺ (λ k′ → Fu β (g (iter (sω g) zero k′))))))
          (sym (trans (fsnG ν (t₀ ++ a) k (gt′ nu) (cof++Ω t₀ a e)) (cong (ψᵘ ν) (fsT++ t₀ a (γT (t₀ ++ a) ν′ k) e))))
          (Gj.m-cum (λ k′ → Fu β (g (iter (sω g) zero k′))) (suc k)
            (LFu β hβ (h (γT (t₀ ++ a) ν′ k) (iter (sω g) zero (suc k)) (chain e nu h k)))))
    LFu β hβ (mΩ {t = a} {p = inj₂ (tt , inj₂ p)} {g = g} e nu h) =
      mΩ (cofK ν (t₀ ++ a) (pen p nu) (cof++Ω t₀ a e)) nu
        (λ η c l → subst (λ z → Mj z (proj₁ (Fu β (g c))))
          (sym (trans (fsTK ν (t₀ ++ a) η (pen p nu) (cof++Ω t₀ a e)) (cong (ψᵘ ν) (fsT++ t₀ a η e))))
          (LFu β hβ (h η c l)))
    LFu β hβ (mU {t = a} {s = s₁} {x = x} {y = y} h ch) =
      subst (λ z → Mj (ψᵘ ν z) (proj₁ (ψ j oj (proj₂ r tt) (cb₊ x) j self (Fu β x) y))) (++-assoc t₀ a s₁)
        (selfP (proj₂ r tt) (cb₊ x) (Fu β x) (LFu β hβ h) ch)
    LFu β hβ (mw h dd) = mw (LFu β hβ h) (mono ℓ₊ o₊ r B j (inu (λ _ → self)) β dd)
    LFu β hβ (mc le h) = mc (appᵘ ν t₀ le) (LFu β hβ h)

  P₀ Q₀ Q₁ : Tr j → Set
  P₀ = Mj (ψᵘ ν [])
  Q₀ = Mj (ψᵘ ν (E.Ωt ν))
  Q₁ = Mj (ψᵘ ν (E.Ωt (sucT ν)))

  module C₀ = Mono j oj P₀ Q₀ mw mw (λ a → Gj.m-right a)
  module C₁ = Mono j oj P₀ Q₁ mw mw (λ a → Gj.m-right a)

  car₀ : C₀.Car zero
  car₀ ob r B β ok hβ = selfP r B β hβ leaf

  car₁ : C₁.Car (↑ zero (suc zero))
  car₁ ob r B β ok hβ = Fold₊.LFu r B [] (good B ok) β hβ Mβ₊

  seen-all : (c : Tr zero) (u : zero ≤ j) (β : Tr⁺ j) → P₀ (proj₁ β) → Q₀ (proj₁ (seen Sᶻ j oj u β c))
  seen-all c u β = C₀.seen-mono Sᶻ u β {c′ = zero} {c = c} (z⊑ (↑ zero c) (noΩ-↑ c)) (noΩ-↑ c) car₀

  seen-nz : (c : Tr zero) → zero ⊢ zero ◃ c → (u : zero ≤ j) (β : Tr⁺ j) → P₀ (proj₁ β) → Q₁ (proj₁ (seen Sᶻ j oj u β c))
  seen-nz c d u β = C₁.seen-mono Sᶻ u β {c′ = suc zero} {c = c} (one⊑ c d) (noΩ-↑ c) car₁
```
