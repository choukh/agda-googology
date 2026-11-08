# 富合法化保持原当前 Gd

直接证明原 legT，不改 Third 的折叠或坐标准入。关键不是跨世界迁证，
而是沿合法化已经使用的 Ctx 搬 Pos，并将输出节点的 AdT 坐标反向搬回
其原低层。到 Sb 底层时 Gd 对全部 raw 分支成立，不要求 Stable。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.CircuitLegalBuildNormal where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw; Pos)
open import OCF.Lean.ThirdTw using (Sb; FX)
open import OCF.Lean.LHRecLeg using (Ctx; here; viaS; viaL; ek; frC)
import OCF.Lean.ThirdFold as F
import OCF.Lean.ThirdRichLegIf as RI
import OCF.Lean.ThirdRichLegBuild as Rich

module At (N : ℕ) (w : Wd (Sb N)) (lw : LgW (Sb N) w) (M : HB (Sb N)) where
  U = Sb N
  T = Tw U M
  open F U w lw using (Gd; AdT; Gd-⊞)
  Q : HB T → Set
  Q = Gd M

  AllPos : ∀ {S} → Ctx T S → Set
  AllPos {S} c = ∀ κ → Pos U w M (ek c κ)

  all-new : ∀ {S} (c : Ctx T (step S)) (g : HB S → HB T) →
    AllPos c → (∀ e → Q (g e)) → ∀ d → Q (RI.New.θ c g d)
  all-new c g p h hz = h hz
  all-new c g p h (hs d) = Gd-⊞ _ _ (Gd-⊞ _ _ (all-new c g p h d) (h d)) (h (hs d))
  all-new c g p h (hl f) = λ n → all-new c g p h (f n)
  all-new c g p h (hΩ κ f) = p (inj₁ κ) , λ e _ → all-new c g p h (f (frC c (inj₁ κ) e))

  all-S : ∀ n (c : Ctx T (Sb n)) κ g → AllPos c →
    (∀ e → Q (g e)) → ∀ d → Q (Rich.θS n c κ g d)
  all-T : ∀ n i (c : Ctx T (Tw (Sb n) i)) κ g → AllPos c →
    (∀ e → Q (g e)) → ∀ d → Q (Rich.θT n i c κ g d)
  all-S zero c () g p h d
  all-S (suc n) c (inj₁ _ , inj₂ _) g p h d = all-new (viaL c (inj₁ tt)) g (λ κ → p (inj₁ tt , κ)) h d
  all-S (suc n) c (inj₁ _ , inj₁ κ) g p h d = all-S n (viaS (viaL c (inj₁ tt))) κ g (λ κ → p (inj₁ tt , inj₁ κ)) h d
  all-S (suc n) c (inj₂ e , κ) g p h d = all-T n (hs e) (viaL c (inj₂ e)) κ g (λ κ → p (inj₂ e , κ)) h d
  all-T n hz c κ g p h d = all-S n c κ g p h d
  all-T n (hs i) c (inj₂ _) g p h d = all-new c g p h d
  all-T n (hs i) c (inj₁ κ) g p h d = all-T n i (viaS c) κ g (λ κ → p (inj₁ κ)) h d
  all-T n (hl f) c (n′ , κ) g p h d = all-T n (f n′) (viaL c n′) κ g (λ κ → p (n′ , κ)) h d
  all-T n (hΩ κ₀ f) c (e , κ) g p h d = all-T n (f e) (viaL c e) κ g (λ κ → p (e , κ)) h d

  Map : (i : HB U) → Ctx T (Tw U i) → Set
  Map i c = (∀ κ → Pos U w i κ → Pos U w M (ek c κ)) ×
    (∀ κ e → AdT M (ek c κ) e → AdT i κ (frC c κ e))

  new-good : ∀ i (c : Ctx T (Tw U (hs i))) (g : HB (Tw U i) → HB T) → Map (hs i) c →
    (∀ d → Gd i d → Q (g d)) → ∀ d → Gd i d → Q (RI.New.θ c g d)
  new-good i c g p h hz d = h hz tt
  new-good i c g p h (hs a) d = Gd-⊞ _ _ (Gd-⊞ _ _ (new-good i c g p h a d) (h a d)) (h (hs a) d)
  new-good i c g p h (hl f) d = λ n → new-good i c g p h (f n) (d n)
  new-good i c g p h (hΩ κ f) (pos , branches) = proj₁ p (inj₁ κ) pos ,
    λ e ae → new-good i c g p h (f (frC c (inj₁ κ) e)) (branches _ (proj₂ p (inj₁ κ) e ae))

  theta-good : ∀ i (c : Ctx T (Tw U i)) κ g → Map i c → Pos U w i κ →
    (∀ e → AdT i κ e → Q (g e)) → ∀ e → AdT i κ e → Q (Rich.θT N i c κ g e)
  theta-good hz c κ g p pos h e a = all-S N c κ g (λ κ → proj₁ p κ tt) (λ e → h e tt) e
  theta-good (hs i) c (inj₂ _) g p pos h e a = new-good i c g p h e a
  theta-good (hs i) c (inj₁ κ) g p pos h e a = theta-good i (viaS c) κ g
    ((λ κ → proj₁ p (inj₁ κ)) , (λ κ → proj₂ p (inj₁ κ))) pos h e a
  theta-good (hl f) c (n , κ) g p pos h e a = theta-good (f n) (viaL c n) κ g
    ((λ κ → proj₁ p (n , κ)) , (λ κ → proj₂ p (n , κ))) pos h e a
  theta-good (hΩ κ₀ f) c (d , κ) g p (bd , pos) h e a = theta-good (f d) (viaL c d) κ g
    ((λ κ q → proj₁ p (d , κ) (bd , q)) , (λ κ → proj₂ p (d , κ))) pos h e a

  normal : ∀ h → Q h → Q (Rich.legT N M h)
  partial : ∀ f → (∀ n → Q (f n)) → ∀ n → Q (Rich.Complete.partial (Rich.allT N M) (λ n → Rich.legT N M (f n)) n)
  normal hz p = tt
  normal (hs h) p = normal h p
  normal (hl f) p = partial f p
  normal (hΩ κ g) (pos , p) = pos , λ e a →
    theta-good M here κ (λ d → Rich.legT N M (g d))
      ((λ κ p → p) , (λ κ e p → p)) pos (λ d ad → normal (g d) (p d ad)) e a
  partial f p zero = normal (f zero) (p zero)
  partial f p (suc n) = Gd-⊞ _ _ (partial f p n) (normal (f (suc n)) (p (suc n)))
```

原合同全 n、全高度与全部输入实填；证明实际不使用高度合法性，仍按
共享合同保留该参数，不因此修改接口。

```agda
open import OCF.Lean.CircuitLegalIf using (NormalGd)
normal-gd : NormalGd
normal-gd n w lw m lm = At.normal n w lw m
```
