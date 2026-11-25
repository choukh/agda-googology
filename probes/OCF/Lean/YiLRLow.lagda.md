# 验收 (换基): ℕ 极限读回层号上的关系族与折到有限层的保持

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 编译定理, 无前提. 层号 `nd sL G`, 孩子 `G n ≡ fn (d n)`, 相邻路径读成 `pth` (`Lim` 的参数); 关系 `Mω` 是 `Mᴰ` 在它上面的实例 (孩子 m 的关系与槽位读法经 `YiLRBridge` 读成 `M (d m)`). `LFω`: `YiRBSib` 的折叠沿 `inc n v` (v 读成 `pth s`) 把 `Mω a x` 送到 `M j (ψ_j(t₀ + a))`, 对一切推导.
> 实例: 兄弟孩子在 c = `ωᶜ`, `ωᵉ` 处折的层 (`lvlᶜ`, `lvlᵉ`, 证据的路线 `routeᶜ`, `routeᵉ`, 都是 `refl`); 检验 `valᶜ`, `valᵉ`: 那一支对着每个 ψ₂(Ω_{d n}). 量化域收窄在路径 (读成 `pth`), 底 (`GBω`, 标准底满足), 路线上, 不在树上.
> 来源: 照 `YiLMLow` (`LFω`, `LFU`, `gbL`, `LFΩω`, `chainω`) 在精简块与 `YiRBSib` 上重写; 有限层的保持引 `YiRBFam`. 不涉及一般的 `lim f a` (孩子不是有限读回层号的), ω 层作目标, 上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLRLow where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong; cong₂)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; node⁺)
open import OCF.Lean.YiRBSib
open import OCF.Lean.YiRBFam using (ψ-⊵)
open import OCF.Lean.YiRBCrit using (two; h₁; sh; gˢ; wˢ; hβ₂)
open import OCF.Lean.YiRLCrit using (ℓˢ; oˢ)
open import OCF.Lean.YiKVRel using (Mᴰ; mz; m1; mL; mΩ; mU; mw; _⊴_; ⊴r; +⊴; ++[])
open import OCF.Lean.YiKCStep using (⊴-trans)
import OCF.Align.EboLeanDef as E
open E using (cof; cΩ; fsT; γT; natT; sucT; cmpᵀ; gt)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ; cofK; fsTK; cofG; fsnG)
open import OCF.Lean.YiCLFam using (nat; fn; M; LwP; levP; mwN; m⊴N)
open import OCF.Lean.YiCLLow using (Sb; s0; ss; pth; zlJ; nextJ; cumJ; mLJ; mΩP; ΩJ; penJ)
open import OCF.Lean.YiCLCrit using (ωᶜ; ωᵉ; dbl)
open import OCF.Lean.YiLRBridge
```

## 两个孩子之间的路径

`way` 给出的路径都满足相邻路径满足的、对 `self` 与 `∙` 封闭的谓词 (`wayC`).

```agda
data WC (g : ℕ → L) (C : ∀ {a b} → g a ≤ g b → Set) (m n : ℕ) : (g m ≤ g n) ⊎ (g n ≤ g m) → Set where
  wf : ∀ {u} → C {m} {n} u → WC g C m n (inj₁ u)
  wb : ∀ {u} → C {n} {m} u → WC g C m n (inj₂ u)

from0C : (g : ℕ → L) (r : (n : ℕ) → g n ≤ g (suc n)) (C : ∀ {a b} → g a ≤ g b → Set)
       → (∀ {a} → C {a} {a} self) → (∀ a → C (r a))
       → (∀ {a b c} {u : g a ≤ g b} {u′ : g b ≤ g c} → C u → C u′ → C (u ∙ u′))
       → ∀ k → C {0} {k} (from0 g r k)
from0C g r C cs cr c∙ zero    = cs
from0C g r C cs cr c∙ (suc k) = c∙ (from0C g r C cs cr c∙ k) (cr k)

shiftWC : ∀ {g : ℕ → L} {C : ∀ {a b} → g a ≤ g b → Set} {m n W}
        → WC (λ i → g (suc i)) (λ {a} {b} u → C {suc a} {suc b} u) m n W → WC g C (suc m) (suc n) W
shiftWC (wf c) = wf c
shiftWC (wb c) = wb c

wayC : (g : ℕ → L) (r : (n : ℕ) → g n ≤ g (suc n)) (C : ∀ {a b} → g a ≤ g b → Set)
     → (∀ {a} → C {a} {a} self) → (∀ a → C (r a))
     → (∀ {a b c} {u : g a ≤ g b} {u′ : g b ≤ g c} → C u → C u′ → C (u ∙ u′))
     → ∀ m n → WC g C m n (way g r m n)
wayC g r C cs cr c∙ m       zero    = wb (from0C g r C cs cr c∙ m)
wayC g r C cs cr c∙ zero    (suc n) = wf (from0C g r C cs cr c∙ (suc n))
wayC g r C cs cr c∙ (suc m) (suc n) =
  shiftWC {g = g} {C = C} (wayC (λ i → g (suc i)) (λ i → r (suc i)) (λ {a} {b} u → C {suc a} {suc b} u)
    (λ {a} → cs {suc a}) (λ a → cr (suc a)) (λ {a} {b} {c} {u} {u′} → c∙ {suc a} {suc b} {suc c} {u} {u′}) m n)

cWC : ∀ {g : ℕ → L} {C : ∀ {a b} → g a ≤ g b → Set} {m n} {X : Set} (Q : X → Set) (W : (g m ≤ g n) ⊎ (g n ≤ g m))
    → WC g C m n W → {F : g m ≤ g n → X} {G : g n ≤ g m → X}
    → (∀ u → C {m} {n} u → Q (F u)) → (∀ u → C {n} {m} u → Q (G u)) → Q (cW W F G)
cWC Q _ (wf c) hF hG = hF _ c
cWC Q _ (wb c) hF hG = hG _ c
```

## 关系, 底的条件

```agda
module Lim (G : ℕ → L) (d : ℕ → ℕ) (eG : ∀ n → G n ≡ fn (d n)) (R : (n : ℕ) → G n ≤ G (suc n))
           (canR : ∀ n → Σ (Sb (d (suc n)) (d n)) λ s → τ₂ (eG n) (eG (suc n)) (R n) ≡ pth s) where

  Lω : L
  Lω = nd sL G

  CP : ∀ {a b} → G a ≤ G b → Set
  CP {a} {b} u = Σ (Sb (d b) (d a)) λ s′ → τ₂ (eG a) (eG b) u ≡ pth s′

  c∙ : ∀ {a b c} {u : G a ≤ G b} {u′ : G b ≤ G c} → CP u → CP u′ → CP (u ∙ u′)
  c∙ {a} {b} {c} {u} {u′} (s , q) (s′ , q′) =
    comp s′ s , trans (τ₂∙ (eG a) (eG b) (eG c) u u′) (trans (cong₂ _∙_ q q′) (∙pth s s′))

  wc : ∀ m n → WC G CP m n (way G R m n)
  wc = wayC G R CP (λ {a} → s0 , τ₂self (eG a)) canR c∙

  Lowω : (p : Pos Lω) → E.T → Br Lω p → Set
  Lowω (inj₁ ())
  Lowω (inj₂ (m , t)) = LwB (G m) (eG m) t

  Nuω : Pos Lω → E.T → Set
  Nuω (inj₁ ())
  Nuω (inj₂ (m , t)) = NwB (G m) (eG m) t

  Mω : E.T → Tr Lω → Set
  Mω = Mᴰ (Sig Lω) Lowω (λ m → MB (G m) (eG m)) Nuω

  record GBω (B : Base Lω) (t₀ : E.T) : Set where
    constructor mkGBω
    field
      wΩ : ∀ m {i} (si : Sb (d m) i) (u : fn i ≤ G m) → τ (eG m) u ≡ pth si → proj₁ (Ωt (fn i)) ⊴ proj₁ (B (fn i) (inc m u))
      wM : ∀ m {i} (si : Sb (d m) i) (u : fn i ≤ G m) → τ (eG m) u ≡ pth si → M i (ψᴺ i t₀) (proj₁ (B (fn i) (inc m u)))
  open GBω public

  gbω₀ : GBω (B₀ Lω) []
  gbω₀ = mkGBω (λ m si u q → ⊴r) (λ m {i} si u q → ΩJ i (Ωt (fn i)) ⊴r)

  ∙q : ∀ {n m j} {v : fn j ≤ G n} {s : Sb (d n) j} → τ (eG n) v ≡ pth s → (u : G n ≤ G m) (c : CP u)
     → τ (eG m) (v ∙ u) ≡ pth (comp (proj₁ c) s)
  ∙q {n} {m} {v = v} {s} q u c = trans (τ∙ (eG n) (eG m) v u) (trans (cong₂ _∙_ q (proj₂ c)) (∙pth s (proj₁ c)))
```

## 折到有限层

对 `Mω a x` 的推导归纳, 各行同 `YiRBFam.LF`; 嵌入一行按 `way` 落到孩子 n 或孩子 m, 再用 `LFAB`; 孩子层的底满足 `GBB` (`gbL`, 用到对 x 的归纳假设); 结点一行用 `kcaseB`, `kcaseB₂`, 回灌链用 `feedB`.

```agda
  module Fold (oc : (k : ℕ) → Ok (G k)) (r : Rb Lω) (B : Base Lω) (t₀ : E.T) (gb : GBω B t₀) where
    o : Ok Lω
    o = R , oc

    F : ∀ {j} → fn j ≤ Lω → Tr⁺ (fn j) → Tr Lω → Tr⁺ (fn j)
    F {j} w β x = ψ Lω o r B (fn j) w β x

    cb : (m : ℕ) → Tr Lω → Base (G m)
    cb m x i u = ψ Lω o r B i (inc m u) (B i (inc m u)) x

    sf : (m : ℕ) (t : Pos⁼ (G m)) → (Br⁼ (G m) t → Tr Lω) → Br⁼ (G m) t → Br⁼ (G m) t
    sf m t g z = proj₂ (sl⁼ (G m) t)
      (proj₁ (ψ Lω o r B (proj₁ (sl⁼ (G m) t)) (inc m (posW⁼ (G m) t)) (B (proj₁ (sl⁼ (G m) t)) (inc m (posW⁼ (G m) t))) (g z)))

    mutual
      LFω : ∀ {n j} (v : fn j ≤ G n) (s : Sb (d n) j) → τ (eG n) v ≡ pth s
          → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
          → ∀ {a x} → Mω a x → M j (ψᴺ j (t₀ ++ a)) (proj₁ (F (inc n v) β x))
      LFω {n} {j} v s q β hβ (mz {x = x}) =
        ++[] (λ z → M j (ψᴺ j z) (proj₁ (F (inc n v) β x))) t₀
          (zlJ j (λ y → proj₁ (F (inc n v) β y)) (mono Lω o r B (fn j) (inc n v) β) hβ x)
      LFω {n} {j} v s q β hβ (m1 {t = a} {x = x} e h) =
        nextJ j (F (inc n v) β x) (cofψ1 (natT j) (t₀ ++ a) (cof++1 t₀ a e))
          (λ k → trans (fsnψ1 (natT j) (t₀ ++ a) k (cof++1 t₀ a e)) (cong (λ z → replicate k (E.ψ (natT j) z)) (pred++ t₀ a e)))
          (LFω v s q β hβ h)
      LFω {n} {j} v s q β hβ (mL {t = a} {x = x} e h) =
        mLJ j (cofψω (natT j) (t₀ ++ a) (cof++ω t₀ a e))
          (λ k → subst (λ z → M j z (proj₁ (F (inc n v) β x)))
            (sym (trans (fsnψω (natT j) (t₀ ++ a) k (cof++ω t₀ a e)) (cong (ψᴺ j) (fsn++ t₀ a k e))))
            (LFω v s q β hβ (h k)))
      LFω v s q β hβ (mΩ {p = inj₁ ()} _ _ _)
      LFω v s q β hβ (mΩ {p = inj₂ (m , t)} e nu h) = LFΩ v s q β hβ m t e nu h
      LFω {n} {j} v s q β hβ (mU {t = a} {s = s₁} {x = x} {c = m} {y = y} {e = ey} h ch) =
        subst (λ z → M j (ψᴺ j z) (proj₁ (F (inc n v) β (up x m y ey)))) (++-assoc t₀ a s₁)
          (LFU v s q β hβ m y ey h ch (way G R m n) (wc m n))
      LFω {n} {j} v s q β hβ (mw h dd) = mwN j (LFω v s q β hβ h) (mono Lω o r B (fn j) (inc n v) β dd)

      LFU : ∀ {n j} (v : fn j ≤ G n) (s : Sb (d n) j) → τ (eG n) v ≡ pth s
          → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
          → ∀ {a s₁ x} (m : ℕ) (y : Tr (G m)) (ey : G m ⊢ zero ◃ y) → Mω a x → MB (G m) (eG m) s₁ y
          → (W : (G m ≤ G n) ⊎ (G n ≤ G m)) → WC G CP m n W
          → M j (ψᴺ j ((t₀ ++ a) ++ s₁)) (proj₁ (cW W
              (λ u → ψ (G n) (oc n) (proj₂ r n) (cb n x) (fn j) v (F (inc n v) β x) (proj₁ (emb (G n) (oc n) u (y , ey))))
              (λ u → ψ (G m) (oc m) (proj₂ r m) (cb m x) (fn j) (v ∙ u) (F (inc n v) β x) y)))
      LFU {n} {j} v s q β hβ {a} {s₁} {x} m y ey h ch W w =
        cWC (λ Z → M j (ψᴺ j ((t₀ ++ a) ++ s₁)) (proj₁ Z)) W w
          (λ u c → LFAB (G n) (eG n) (oc n) (proj₂ r n) (cb n x) v s q (t₀ ++ a) (gbL n h) (F (inc n v) β x)
                     (LFω v s q β hβ h) (embB (G m) (G n) (eG m) (eG n) (oc n) u (proj₁ c) (proj₂ c) y ey ch))
          (λ u c → LFAB (G m) (eG m) (oc m) (proj₂ r m) (cb m x) (v ∙ u) (comp (proj₁ c) s) (∙q q u c)
                     (t₀ ++ a) (gbL m h) (F (inc n v) β x) (LFω v s q β hβ h) ch)

      gbL : ∀ m {a x} → Mω a x → GBB (G m) (eG m) (cb m x) (t₀ ++ a)
      gbL m {a} {x} h =
        mkGBB (G m) (eG m) (cb m x) (t₀ ++ a)
          (λ {i} si u qu → ⊴-trans (wΩ gb m si u qu) (ψ-⊵ Lω o r B (fn i) (inc m u) (B (fn i) (inc m u)) x)
                         , LFω u si qu (B (fn i) (inc m u)) (wM gb m si u qu) h)

      LFΩ : ∀ {n j} (v : fn j ≤ G n) (s : Sb (d n) j) → τ (eG n) v ≡ pth s
          → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
          → (m : ℕ) (t : Pos⁼ (G m)) → ∀ {a ν} {g : Br⁼ (G m) t → Tr Lω}
          → cof a ≡ cΩ ν → NwB (G m) (eG m) t ν → (∀ η c → LwB (G m) (eG m) t η c → Mω (fsT a η) (g c))
          → M j (ψᴺ j (t₀ ++ a)) (proj₁ (F (inc n v) β (Ω (inj₂ (m , t)) g)))
      LFΩ {n} {j} v s q β hβ m t {a} {ν} {g} e nu h =
        cWC (λ K → M j (ψᴺ j (t₀ ++ a)) (proj₁ (node⁺ K (λ z → F (inc n v) β (g z)) (sf m t g)))) (way G R m n) (wc m n)
          (λ u c → kcaseB₂ (G m) (G n) (eG m) (eG n) (oc n) u (proj₁ c) (proj₂ c) t v s q nu
                     (λ K → M j (ψᴺ j (t₀ ++ a)) (proj₁ (node⁺ K (λ z → F (inc n v) β (g z)) (sf m t g))))
                     (λ gtq → LFΩ-lim v s q β hβ m t e nu h gtq)
                     (λ qq cv eq nq lw → LFΩ-keep v s q β hβ m t e nu h qq cv eq nq lw))
          (λ u c → kcaseB (G m) (eG m) (oc m) t (v ∙ u) (comp (proj₁ c) s) (∙q q u c) nu
                     (λ K → M j (ψᴺ j (t₀ ++ a)) (proj₁ (node⁺ K (λ z → F (inc n v) β (g z)) (sf m t g))))
                     (λ gtq → LFΩ-lim v s q β hβ m t e nu h gtq)
                     (λ qq cv eq nq lw → LFΩ-keep v s q β hβ m t e nu h qq cv eq nq lw))

      LFΩ-lim : ∀ {n j} (v : fn j ≤ G n) (s : Sb (d n) j) → τ (eG n) v ≡ pth s
              → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
              → (m : ℕ) (t : Pos⁼ (G m)) → ∀ {a ν} {g : Br⁼ (G m) t → Tr Lω}
              → cof a ≡ cΩ ν → NwB (G m) (eG m) t ν → (∀ η c → LwB (G m) (eG m) t η c → Mω (fsT a η) (g c))
              → cmpᵀ (sucT ν) (natT j) ≡ gt
              → M j (ψᴺ j (t₀ ++ a)) (proj₁ (limc⁺ (λ k → F (inc n v) β (g (iter (sf m t g) (bz⁼ (G m) t) k)))))
      LFΩ-lim {n} {j} v s q β hβ m t {a} {ν} {g} e nu h gtq =
        mLJ j (cofG (natT j) (t₀ ++ a) gtq (cof++Ω t₀ a e))
          (λ k → subst (λ z → M j z (proj₁ (limc⁺ (λ k′ → F (inc n v) β (g (iter (sf m t g) (bz⁼ (G m) t) k′))))))
            (sym (trans (fsnG (natT j) (t₀ ++ a) k gtq (cof++Ω t₀ a e)) (cong (ψᴺ j) (fsT++ t₀ a (γT (t₀ ++ a) ν k) e))))
            (cumJ j (λ k′ → F (inc n v) β (g (iter (sf m t g) (bz⁼ (G m) t) k′))) (suc k)
              (LFω v s q β hβ (h (γT (t₀ ++ a) ν k) (iter (sf m t g) (bz⁼ (G m) t) (suc k)) (chain m t e nu h k)))))

      LFΩ-keep : ∀ {n j} (v : fn j ≤ G n) (s : Sb (d n) j) → τ (eG n) v ≡ pth s
               → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
               → (m : ℕ) (t : Pos⁼ (G m)) → ∀ {a ν} {g : Br⁼ (G m) t → Tr Lω}
               → cof a ≡ cΩ ν → NwB (G m) (eG m) t ν → (∀ η c → LwB (G m) (eG m) t η c → Mω (fsT a η) (g c))
               → (qq : Pos (fn j)) (cv : Br (fn j) qq → Br⁼ (G m) t) (eq : cv (fromBr (fn j) qq zero) ≡ bz⁼ (G m) t)
               → ν ≡ natT (levP j qq) → (∀ η c → LwP j qq η c → LwB (G m) (eG m) t η (cv c))
               → M j (ψᴺ j (t₀ ++ a)) (Ω qq (λ z → proj₁ (F (inc n v) β (g (cv z)))))
      LFΩ-keep {n} {j} v s q β hβ m t {a} {ν} {g} e nu h qq cv eq nq lw =
        mΩP j (cofK (natT j) (t₀ ++ a) (penJ j qq nq) (cof++Ω t₀ a e)) nq
          (λ η c l → subst (λ z → M j z (proj₁ (F (inc n v) β (g (cv c)))))
            (sym (trans (fsTK (natT j) (t₀ ++ a) η (penJ j qq nq) (cof++Ω t₀ a e)) (cong (ψᴺ j) (fsT++ t₀ a η e))))
            (LFω v s q β hβ (h η (cv c) (lw η c l))))

      chain : ∀ m (t : Pos⁼ (G m)) → ∀ {a ν} {g : Br⁼ (G m) t → Tr Lω}
            → cof a ≡ cΩ ν → NwB (G m) (eG m) t ν → (∀ η c → LwB (G m) (eG m) t η c → Mω (fsT a η) (g c))
            → ∀ k → LwB (G m) (eG m) t (γT (t₀ ++ a) ν k) (iter (sf m t g) (bz⁼ (G m) t) (suc k))
      chain m t {a} {ν} {g} e nu h zero =
        feedB (G m) (eG m) t nu (γT (t₀ ++ a) ν zero)
          (λ k w → proj₁ (ψ Lω o r B k (inc m w) (B k (inc m w)) (g (bz⁼ (G m) t))))
          (λ {i} si u qu eqν → subst (λ μ → M i (E.Ωt μ) (proj₁ (ψ Lω o r B (fn i) (inc m u) (B (fn i) (inc m u)) (g (bz⁼ (G m) t)))))
             (sym eqν)
             (ΩJ i (ψ Lω o r B (fn i) (inc m u) (B (fn i) (inc m u)) (g (bz⁼ (G m) t)))
                (⊴-trans (wΩ gb m si u qu) (ψ-⊵ Lω o r B (fn i) (inc m u) (B (fn i) (inc m u)) (g (bz⁼ (G m) t))))))
      chain m t {a} {ν} {g} e nu h (suc k) =
        feedB (G m) (eG m) t nu (γT (t₀ ++ a) ν (suc k))
          (λ k′ w → proj₁ (ψ Lω o r B k′ (inc m w) (B k′ (inc m w)) (g (iter (sf m t g) (bz⁼ (G m) t) (suc k)))))
          (λ {i} si u qu eqν →
             subst (λ μ → M i (E.ψ μ (fsT (t₀ ++ a) (γT (t₀ ++ a) ν k)) ∷ [])
                            (proj₁ (ψ Lω o r B (fn i) (inc m u) (B (fn i) (inc m u)) (g (iter (sf m t g) (bz⁼ (G m) t) (suc k))))))
               (sym eqν)
               (subst (λ z → M i (ψᴺ i z) (proj₁ (ψ Lω o r B (fn i) (inc m u) (B (fn i) (inc m u)) (g (iter (sf m t g) (bz⁼ (G m) t) (suc k))))))
                 (sym (fsT++ t₀ a (γT (t₀ ++ a) ν k) e))
                 (LFω u si qu (B (fn i) (inc m u)) (wM gb m si u qu)
                   (h (γT (t₀ ++ a) ν k) (iter (sf m t g) (bz⁼ (G m) t) (suc k)) (chain m t e nu h k)))))
```

## 实例: c = `ωᶜ`, `ωᵉ`

```agda
Gᶜ : ℕ → L
Gᶜ n = h₁ (nat 2 + nat n)

eᶜ : ∀ n → Gᶜ n ≡ fn (sh n)
eᶜ zero    = refl
eᶜ (suc n) = cong Sᶜ (eᶜ n)

Rᶜ : (n : ℕ) → Gᶜ n ≤ Gᶜ (suc n)
Rᶜ n = inc tt self

canRᶜ : ∀ n → Σ (Sb (sh (suc n)) (sh n)) λ s → τ₂ (eᶜ n) (eᶜ (suc n)) (Rᶜ n) ≡ pth s
canRᶜ n = ss s0 , trans (τ₂S (eᶜ n) (eᶜ n) self) (cong (inc tt) (τ₂self (eᶜ n)))

module Wᶜ = Lim Gᶜ sh eᶜ Rᶜ canRᶜ

lvlᶜ : ℓˢ ωᶜ ≡ Wᶜ.Lω
lvlᶜ = refl

routeᶜ : proj₁ (oˢ ωᶜ) ≡ Rᶜ
routeᶜ = refl

dd : ℕ → ℕ
dd zero    = 2
dd (suc n) = suc (suc (dd n))

Gᵉ : ℕ → L
Gᵉ n = h₁ (nat 2 + dbl n)

eᵉ : ∀ n → Gᵉ n ≡ fn (dd n)
eᵉ zero    = refl
eᵉ (suc n) = cong (λ k → Sᶜ (Sᶜ k)) (eᵉ n)

Rᵉ : (n : ℕ) → Gᵉ n ≤ Gᵉ (suc n)
Rᵉ n = inc tt (inc tt self)

canRᵉ : ∀ n → Σ (Sb (dd (suc n)) (dd n)) λ s → τ₂ (eᵉ n) (eᵉ (suc n)) (Rᵉ n) ≡ pth s
canRᵉ n = ss (ss s0) , trans (τ₂SS (eᵉ n) (eᵉ n) self) (cong (λ w → inc tt (inc tt w)) (τ₂self (eᵉ n)))

module Wᵉ = Lim Gᵉ dd eᵉ Rᵉ canRᵉ

lvlᵉ : ℓˢ ωᵉ ≡ Wᵉ.Lω
lvlᵉ = refl

routeᵉ : proj₁ (oˢ ωᵉ) ≡ Rᵉ
routeᵉ = refl
```

检验: 兄弟孩子在 c = `ωᶜ` (`ωᵉ`) 处那一支对着 ψ₂(Ω_{n+2}) (ψ₂(Ω_{2n+2})). ω 层的 Ω 树第 n 个部分和的末项是孩子 n 的 Ω 树 (`MβB`), 再用 `LFω` (路径 `inc 0 self`, 标准底, 起点 Ω₂ 树).

```agda
atω : ∀ c {t} → M 2 t (proj₁ (ψ (ℓˢ c) (oˢ c) (rb-no _) (B₀ (ℓˢ c)) two (wˢ c) (Ωt two) (proj₁ (Ωt (ℓˢ c)))))
    → M 2 t (proj₁ (gˢ c))
atω c m = m⊴N 2 m (+⊴ _ _)

cumᶜ : ∀ n → Wᶜ.Mω (Ωᴺ (sh n)) (cum (λ k → proj₁ (upz {sL} {Gᶜ} k (Ωt (Gᶜ k)))) n)
cumᶜ zero    = mU mz (MβB (Gᶜ zero) (eᶜ zero))
cumᶜ (suc n) = mU mz (MβB (Gᶜ (suc n)) (eᶜ (suc n)))

valᶜ : ∀ n → M 2 (ψᴺ 2 (Ωᴺ (sh n))) (proj₁ (gˢ ωᶜ))
valᶜ n = atω ωᶜ (Wᶜ.Fold.LFω (proj₂ (oˢ ωᶜ)) (rb-no _) (B₀ Wᶜ.Lω) [] Wᶜ.gbω₀ {n = 0} {j = 2} self s0 refl (Ωt two) hβ₂
                  {x = proj₁ (Ωt Wᶜ.Lω)} (mw (cumᶜ n) (◃l n)))

cumᵉ : ∀ n → Wᵉ.Mω (Ωᴺ (dd n)) (cum (λ k → proj₁ (upz {sL} {Gᵉ} k (Ωt (Gᵉ k)))) n)
cumᵉ zero    = mU mz (MβB (Gᵉ zero) (eᵉ zero))
cumᵉ (suc n) = mU mz (MβB (Gᵉ (suc n)) (eᵉ (suc n)))

valᵉ : ∀ n → M 2 (ψᴺ 2 (Ωᴺ (dd n))) (proj₁ (gˢ ωᵉ))
valᵉ n = atω ωᵉ (Wᵉ.Fold.LFω (proj₂ (oˢ ωᵉ)) (rb-no _) (B₀ Wᵉ.Lω) [] Wᵉ.gbω₀ {n = 0} {j = 2} self s0 refl (Ωt two) hβ₂
                  {x = proj₁ (Ωt Wᵉ.Lω)} (mw (cumᵉ n) (◃l n)))
```
