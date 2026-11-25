# 候选折叠 (A)+(B)+(C)

> 定义候选, 未经作者采纳, 不进主线; 不读记号. 折叠逐行复制 `YiDXFold.Fold` (来源: 该文件第 81 至 189 行), 多带两个参数: 证据 `Pv` (进孩子时取孩子的分量) 与朝当前目标的来源表 `ot` (`ink` 行由 `dlg` 生成, 进孩子取分量, 换目标时清空). 取 `K = kpᶜ`、上折回退, 即 (A)+(B)+(C).
> 编译定理: 合法性是类型; 单调 `mono`、`monoˡ` 对一切 `K`、两种开关成立; 退路行两种写法的形状 (`row-fbᴾ`, `row-liftᴾ`), `ink` 行的形状 (`row-ink`). 闭项 `twᶜ`, `EBOᶜ` 用 `pvT`, `pvΛ`.
> 不否定什么. 测试在 [YiKFTest](YiKFTest.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKFFold where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; node⁺; nodeLe)
open import OCF.Lean.YiTBRow using (Rb; dW; dW-ind; dW-ind₂)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiDXFold using (sel; sel-ind; sel-ind₂)
open import OCF.Lean.YiKFKeep
```

## 折叠

```agda
module Fold (K : KeepFnᴾ) (lifted : Bool) where
  mutual
    ψ : (ℓ : L) → Ok ℓ → Rb ℓ → Pv ℓ → Base ℓ → (j : L) → j ≤ ℓ → Org j ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j
    ψ ℓ o r pv B j w ot β zero      = β
    ψ ℓ o r pv B j w ot β (suc x)   = next⁺ (ψ ℓ o r pv B j w ot β x)
    ψ ℓ o r pv B j w ot β (lim f a) = lim⁺ (λ n → ψ ℓ o r pv B j w ot β (f n)) (λ n → mono ℓ o r pv B j w ot β (a n))
    ψ ℓ o r pv B j w ot β (Ω p g)   = node⁺ (K ℓ o pv p w ot) (λ z → ψ ℓ o r pv B j w ot β (g z))
      (λ z → fromBr ℓ p (proj₁ (ψ ℓ o r pv B (at ℓ p) (posW ℓ p) (org-no _ _) (B (at ℓ p) (posW ℓ p)) (g z))))
    ψ (nd s h) o r pv B _ self ot β (up x c y e) = Up (h c) (down stop c) (ψ (nd s h) o r pv B _ self ot β x) y
    ψ (nd s h) o r pv B j (inu ws) ot β (up x c y e) =
      ψ (h c) (proj₂ o c) (proj₂ r c) (proj₂ pv c) (λ i u → ψ (nd s h) o r pv B i (inc c u) (org-no _ _) (B i (inc c u)) x) j (ws c) (proj₂ ot c) (ψ (nd s h) o r pv B j (inu ws) ot β x) y
    ψ (nd (sΩ k) h) o r pv B j (ink v) ot β (up x c y e) =
      ψ (h c) (proj₂ o c) (proj₂ r c) (proj₂ pv c) (λ i u → ψ (nd (sΩ k) h) o r pv B i (inc c u) (org-no _ _) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c) (dlg k h o pv v ot c)
        (ψ (nd (sΩ k) h) o r pv B j (ink v) ot β x) y
    ψ (nd sS h) o r pv B j (inc c′ v) ot β (up x c y e) =
      ψ (h c) (proj₂ o c) (proj₂ r c) (proj₂ pv c) (λ i u → ψ (nd sS h) o r pv B i (inc c u) (org-no _ _) (B i (inc c u)) x) j v (proj₂ ot c) (ψ (nd sS h) o r pv B j (inc c′ v) ot β x) y
    ψ (nd sL g) o r pv B j (inc n v) ot β (up x m y e) = cW (way g (proj₁ o) m n)
      (λ u → ψ (g n) (proj₂ o n) (proj₂ r n) (proj₂ pv n) (λ i u′ → ψ (nd sL g) o r pv B i (inc n u′) (org-no _ _) (B i (inc n u′)) x) j v (proj₂ ot n)
               (ψ (nd sL g) o r pv B j (inc n v) ot β x) (proj₁ (emb (g n) (proj₂ o n) u (y , e))))
      (λ u → ψ (g m) (proj₂ o m) (proj₂ r m) (proj₂ pv m) (λ i u′ → ψ (nd sL g) o r pv B i (inc m u′) (org-no _ _) (B i (inc m u′)) x) j (v ∙ u) (proj₂ ot m)
               (ψ (nd sL g) o r pv B j (inc n v) ot β x) y)
    ψ (nd (sΩ k) h) o r pv B j (inc c′ v) ot β (up x c y e) = dW (proj₁ r c c′)
      (λ u → ψ (h c) (proj₂ o c) (proj₂ r c) (proj₂ pv c) (λ i u′ → ψ (nd (sΩ k) h) o r pv B i (inc c u′) (org-no _ _) (B i (inc c u′)) x) j (v ∙ u) (proj₂ ot c)
               (ψ (nd (sΩ k) h) o r pv B j (inc c′ v) ot β x) y)
      (λ u → ψ (h c′) (proj₂ o c′) (proj₂ r c′) (proj₂ pv c′) (λ i u′ → ψ (nd (sΩ k) h) o r pv B i (inc c′ u′) (org-no _ _) (B i (inc c′ u′)) x) j v (proj₂ ot c′)
               (ψ (nd (sΩ k) h) o r pv B j (inc c′ v) ot β x) (proj₁ (emb (h c′) (proj₂ o c′) u (y , e))))
      (sel lifted (ψ (nd (sΩ k) h) o r pv B j (inc c′ v) ot β x ⊞ ψ (h c) (proj₂ o c) (proj₂ r c) (proj₂ pv c) (B₀ (h c)) zero (z≤ (h c)) (org-no _ _) (Ωt zero) y)
                  (ψˡ (nd (sΩ k) h) o pv (λ i u → ψ (nd (sΩ k) h) o r pv B i u (org-no _ _) (B i u) x) j (inc c′ v) ot
                     (ψ (nd (sΩ k) h) o r pv B j (inc c′ v) ot β x) (h c) (down stop c) y))

    ψˡ : (ℓ : L) → Ok ℓ → Pv ℓ → Base ℓ → (j : L) → j ≤ ℓ → Org j ℓ → Tr⁺ j → (a : L) → Dn ℓ a → Tr a → Tr⁺ j
    ψˡ ℓ o pv X j w ot β a d zero      = β
    ψˡ ℓ o pv X j w ot β a d (suc y)   = next⁺ (ψˡ ℓ o pv X j w ot β a d y)
    ψˡ ℓ o pv X j w ot β a d (lim f e) = lim⁺ (λ n → ψˡ ℓ o pv X j w ot β a d (f n)) (λ n → monoˡ ℓ o pv X j w ot β a d (e n))
    ψˡ ℓ o pv X j w ot β a d (Ω p g)   = node⁺ (K ℓ o pv (mv d p) w ot) (λ z → ψˡ ℓ o pv X j w ot β a d (g (mvBr d p z)))
      (λ z → fromBr ℓ (mv d p) (proj₁ (ψˡ ℓ o pv X (at ℓ (mv d p)) (posW ℓ (mv d p)) (org-no _ _) (X (at ℓ (mv d p)) (posW ℓ (mv d p)))
                                        a d (g (mvBr d p z)))))
    ψˡ ℓ o pv X j w ot β (nd s h) d (up y c y′ e) =
      ψˡ ℓ o pv (λ i u → ψˡ ℓ o pv X i u (org-no _ _) (X i u) (nd s h) d y) j w ot (ψˡ ℓ o pv X j w ot β (nd s h) d y) (h c) (down d c) y′

    monoˡ : (ℓ : L) (o : Ok ℓ) (pv : Pv ℓ) (X : Base ℓ) (j : L) (w : j ≤ ℓ) (ot : Org j ℓ) (β : Tr⁺ j) (a : L) (d : Dn ℓ a) {x y : Tr a}
          → a ⊢ x ◃ y → j ⊢ proj₁ (ψˡ ℓ o pv X j w ot β a d x) ◃ proj₁ (ψˡ ℓ o pv X j w ot β a d y)
    monoˡ ℓ o pv X j w ot β a d ◃s     = ◃l zero
    monoˡ ℓ o pv X j w ot β a d (◃l n) = ◃l n
    monoˡ ℓ o pv X j w ot β a d (◃w {p = p} {g = g}) =
      subst (λ t → j ⊢ proj₁ (ψˡ ℓ o pv X j w ot β a d (g t)) ◃ proj₁ (ψˡ ℓ o pv X j w ot β a d (Ω p g))) (mvFirst d p)
        (nodeLe (K ℓ o pv (mv d p) w ot) (λ z → ψˡ ℓ o pv X j w ot β a d (g (mvBr d p z)))
          (λ z → fromBr ℓ (mv d p) (proj₁ (ψˡ ℓ o pv X (at ℓ (mv d p)) (posW ℓ (mv d p)) (org-no _ _) (X (at ℓ (mv d p)) (posW ℓ (mv d p)))
                                             a d (g (mvBr d p z))))))
    monoˡ ℓ o pv X j w ot β (nd s h) d (◃u x c y e) =
      monoˡ ℓ o pv (λ i u → ψˡ ℓ o pv X i u (org-no _ _) (X i u) (nd s h) d x) j w ot (ψˡ ℓ o pv X j w ot β (nd s h) d x) (h c) (down d c) e
    monoˡ ℓ o pv X j w ot β (nd s h) d (◃c x c r) =
      monoˡ ℓ o pv (λ i u → ψˡ ℓ o pv X i u (org-no _ _) (X i u) (nd s h) d x) j w ot (ψˡ ℓ o pv X j w ot β (nd s h) d x) (h c) (down d c) r
    monoˡ ℓ o pv X j w ot β a d (◃t e f) = ◃t (monoˡ ℓ o pv X j w ot β a d e) (monoˡ ℓ o pv X j w ot β a d f)

    mono : (ℓ : L) (o : Ok ℓ) (r : Rb ℓ) (pv : Pv ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (ot : Org j ℓ) (β : Tr⁺ j) {x y : Tr ℓ}
         → ℓ ⊢ x ◃ y → j ⊢ proj₁ (ψ ℓ o r pv B j w ot β x) ◃ proj₁ (ψ ℓ o r pv B j w ot β y)
    mono ℓ o r pv B j w ot β ◃s           = ◃l zero
    mono ℓ o r pv B j w ot β (◃l n)       = ◃l n
    mono ℓ o r pv B j w ot β (◃w {p = p}) = nodeLe (K ℓ o pv p w ot) _ _
    mono (nd s h) o r pv B _ self ot β (◃u x c y e) = Upm (h c) (down stop c) (ψ (nd s h) o r pv B _ self ot β x) e
    mono (nd s h) o r pv B j (inu ws) ot β (◃u x c y e) =
      mono (h c) (proj₂ o c) (proj₂ r c) (proj₂ pv c) (λ i u → ψ (nd s h) o r pv B i (inc c u) (org-no _ _) (B i (inc c u)) x) j (ws c) (proj₂ ot c) (ψ (nd s h) o r pv B j (inu ws) ot β x) e
    mono (nd (sΩ k) h) o r pv B j (ink v) ot β (◃u x c y e) =
      mono (h c) (proj₂ o c) (proj₂ r c) (proj₂ pv c) (λ i u → ψ (nd (sΩ k) h) o r pv B i (inc c u) (org-no _ _) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c) (dlg k h o pv v ot c)
        (ψ (nd (sΩ k) h) o r pv B j (ink v) ot β x) e
    mono (nd sS h) o r pv B j (inc c′ v) ot β (◃u x c y e) =
      mono (h c) (proj₂ o c) (proj₂ r c) (proj₂ pv c) (λ i u → ψ (nd sS h) o r pv B i (inc c u) (org-no _ _) (B i (inc c u)) x) j v (proj₂ ot c) (ψ (nd sS h) o r pv B j (inc c′ v) ot β x) e
    mono (nd sL g) o r pv B j (inc n v) ot β (◃u x m y e) =
      cW-ind (λ Z → j ⊢ proj₁ (ψ (nd sL g) o r pv B j (inc n v) ot β x) ◃ proj₁ Z) (way g (proj₁ o) m n)
        (λ u → mono (g n) (proj₂ o n) (proj₂ r n) (proj₂ pv n) (λ i u′ → ψ (nd sL g) o r pv B i (inc n u′) (org-no _ _) (B i (inc n u′)) x) j v (proj₂ ot n)
                 (ψ (nd sL g) o r pv B j (inc n v) ot β x) (proj₂ (emb (g n) (proj₂ o n) u (y , e))))
        (λ u → mono (g m) (proj₂ o m) (proj₂ r m) (proj₂ pv m) (λ i u′ → ψ (nd sL g) o r pv B i (inc m u′) (org-no _ _) (B i (inc m u′)) x) j (v ∙ u) (proj₂ ot m)
                 (ψ (nd sL g) o r pv B j (inc n v) ot β x) e)
    mono (nd (sΩ k) h) o r pv B j (inc c′ v) ot β (◃u x c y e) =
      dW-ind (λ Z → j ⊢ proj₁ (ψ (nd (sΩ k) h) o r pv B j (inc c′ v) ot β x) ◃ proj₁ Z) (proj₁ r c c′)
        (λ u → mono (h c) (proj₂ o c) (proj₂ r c) (proj₂ pv c) (λ i u′ → ψ (nd (sΩ k) h) o r pv B i (inc c u′) (org-no _ _) (B i (inc c u′)) x) j (v ∙ u) (proj₂ ot c)
                 (ψ (nd (sΩ k) h) o r pv B j (inc c′ v) ot β x) e)
        (λ u → mono (h c′) (proj₂ o c′) (proj₂ r c′) (proj₂ pv c′) (λ i u′ → ψ (nd (sΩ k) h) o r pv B i (inc c′ u′) (org-no _ _) (B i (inc c′ u′)) x) j v (proj₂ ot c′)
                 (ψ (nd (sΩ k) h) o r pv B j (inc c′ v) ot β x) (proj₂ (emb (h c′) (proj₂ o c′) u (y , e))))
        (sel-ind (λ Z → j ⊢ proj₁ (ψ (nd (sΩ k) h) o r pv B j (inc c′ v) ot β x) ◃ proj₁ Z) lifted
          (+-mono _ (ι-mono j (proj₂ (ψ (h c) (proj₂ o c) (proj₂ r c) (proj₂ pv c) (B₀ (h c)) zero (z≤ (h c)) (org-no _ _) (Ωt zero) y))))
          (monoˡ (nd (sΩ k) h) o pv (λ i u → ψ (nd (sΩ k) h) o r pv B i u (org-no _ _) (B i u) x) j (inc c′ v) ot
            (ψ (nd (sΩ k) h) o r pv B j (inc c′ v) ot β x) (h c) (down stop c) e))
    mono (nd s h) o r pv B _ self ot β (◃c x c d) = Upm (h c) (down stop c) (ψ (nd s h) o r pv B _ self ot β x) d
    mono (nd s h) o r pv B j (inu ws) ot β (◃c x c d) =
      mono (h c) (proj₂ o c) (proj₂ r c) (proj₂ pv c) (λ i u → ψ (nd s h) o r pv B i (inc c u) (org-no _ _) (B i (inc c u)) x) j (ws c) (proj₂ ot c) (ψ (nd s h) o r pv B j (inu ws) ot β x) d
    mono (nd (sΩ k) h) o r pv B j (ink v) ot β (◃c x c d) =
      mono (h c) (proj₂ o c) (proj₂ r c) (proj₂ pv c) (λ i u → ψ (nd (sΩ k) h) o r pv B i (inc c u) (org-no _ _) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c) (dlg k h o pv v ot c)
        (ψ (nd (sΩ k) h) o r pv B j (ink v) ot β x) d
    mono (nd sS h) o r pv B j (inc c′ v) ot β (◃c x c d) =
      mono (h c) (proj₂ o c) (proj₂ r c) (proj₂ pv c) (λ i u → ψ (nd sS h) o r pv B i (inc c u) (org-no _ _) (B i (inc c u)) x) j v (proj₂ ot c) (ψ (nd sS h) o r pv B j (inc c′ v) ot β x) d
    mono (nd sL g) o r pv B j (inc n v) ot β (◃c x m d) =
      cW-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (way g (proj₁ o) m n)
        (λ u → mono (g n) (proj₂ o n) (proj₂ r n) (proj₂ pv n) (λ i u′ → ψ (nd sL g) o r pv B i (inc n u′) (org-no _ _) (B i (inc n u′)) x) j v (proj₂ ot n)
                 (ψ (nd sL g) o r pv B j (inc n v) ot β x) (emb-mono (g n) (proj₂ o n) u d))
        (λ u → mono (g m) (proj₂ o m) (proj₂ r m) (proj₂ pv m) (λ i u′ → ψ (nd sL g) o r pv B i (inc m u′) (org-no _ _) (B i (inc m u′)) x) j (v ∙ u) (proj₂ ot m)
                 (ψ (nd sL g) o r pv B j (inc n v) ot β x) d)
    mono (nd (sΩ k) h) o r pv B j (inc c′ v) ot β (◃c x c d) =
      dW-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (proj₁ r c c′)
        (λ u → mono (h c) (proj₂ o c) (proj₂ r c) (proj₂ pv c) (λ i u′ → ψ (nd (sΩ k) h) o r pv B i (inc c u′) (org-no _ _) (B i (inc c u′)) x) j (v ∙ u) (proj₂ ot c)
                 (ψ (nd (sΩ k) h) o r pv B j (inc c′ v) ot β x) d)
        (λ u → mono (h c′) (proj₂ o c′) (proj₂ r c′) (proj₂ pv c′) (λ i u′ → ψ (nd (sΩ k) h) o r pv B i (inc c′ u′) (org-no _ _) (B i (inc c′ u′)) x) j v (proj₂ ot c′)
                 (ψ (nd (sΩ k) h) o r pv B j (inc c′ v) ot β x) (emb-mono (h c′) (proj₂ o c′) u d))
        (sel-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) lifted
          (+-mono _ (ι-mono j (mono (h c) (proj₂ o c) (proj₂ r c) (proj₂ pv c) (B₀ (h c)) zero (z≤ (h c)) (org-no _ _) (Ωt zero) d)))
          (monoˡ (nd (sΩ k) h) o pv (λ i u → ψ (nd (sΩ k) h) o r pv B i u (org-no _ _) (B i u) x) j (inc c′ v) ot
            (ψ (nd (sΩ k) h) o r pv B j (inc c′ v) ot β x) (h c) (down stop c) d))
    mono ℓ o r pv B j w ot β (◃t d d′) = ◃t (mono ℓ o r pv B j w ot β d) (mono ℓ o r pv B j w ot β d′)
```

## 行的形状, 候选, 闭项

```agda
row-ink : ∀ (K : KeepFnᴾ) l k h (o : Ok (nd (sΩ k) h)) (r : Rb (nd (sΩ k) h)) (pv : Pv (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) j (v : j ≤ k) ot β x c y e
  → Fold.ψ K l (nd (sΩ k) h) o r pv B j (ink v) ot β (up x c y e)
  ≡ Fold.ψ K l (h c) (proj₂ o c) (proj₂ r c) (proj₂ pv c)
      (λ i u → Fold.ψ K l (nd (sΩ k) h) o r pv B i (inc c u) (org-no i (nd (sΩ k) h)) (B i (inc c u)) x)
      j (v ∙ proj₂ (proj₁ o) c) (dlg k h o pv v ot c) (Fold.ψ K l (nd (sΩ k) h) o r pv B j (ink v) ot β x) y
row-ink K l k h o r pv B j v ot β x c y e = refl

row-fbᴾ : ∀ (K : KeepFnᴾ) k h (o : Ok (nd (sΩ k) h)) (rc : (c : Tr k) → Rb (h c)) (pv : Pv (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) j c′ (v : j ≤ h c′) ot β x c y e
  → Fold.ψ K false (nd (sΩ k) h) o ((λ _ _ → nothing) , rc) pv B j (inc c′ v) ot β (up x c y e)
  ≡ Fold.ψ K false (nd (sΩ k) h) o ((λ _ _ → nothing) , rc) pv B j (inc c′ v) ot β x
    ⊞ Fold.ψ K false (h c) (proj₂ o c) (rc c) (proj₂ pv c) (B₀ (h c)) zero (z≤ (h c)) (org-no zero (h c)) (Ωt zero) y
row-fbᴾ K k h o rc pv B j c′ v ot β x c y e = refl

row-liftᴾ : ∀ (K : KeepFnᴾ) k h (o : Ok (nd (sΩ k) h)) (rc : (c : Tr k) → Rb (h c)) (pv : Pv (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) j c′ (v : j ≤ h c′) ot β x c y e
  → Fold.ψ K true (nd (sΩ k) h) o ((λ _ _ → nothing) , rc) pv B j (inc c′ v) ot β (up x c y e)
  ≡ Fold.ψˡ K true (nd (sΩ k) h) o pv
      (λ i u → Fold.ψ K true (nd (sΩ k) h) o ((λ _ _ → nothing) , rc) pv B i u (org-no i (nd (sΩ k) h)) (B i u) x) j (inc c′ v) ot
      (Fold.ψ K true (nd (sΩ k) h) o ((λ _ _ → nothing) , rc) pv B j (inc c′ v) ot β x) (h c) (down stop c) y
row-liftᴾ K k h o rc pv B j c′ v ot β x c y e = refl

module FC  = Fold kpᶜ true
module FC⁻ = Fold kpᶜ false

ψ₀ᶜ : (ℓ : L) → Ok ℓ → Pv ℓ → Tr ℓ → Tr⁺ zero
ψ₀ᶜ ℓ o pv = FC.ψ ℓ o (rbᶻ ℓ) pv (B₀ ℓ) zero (z≤ ℓ) (org-no zero ℓ) (Ωt zero)

twᶜ : ℕ → Tr zero
twᶜ n = proj₁ (ψ₀ᶜ (tw n) (Ok-tw n) (pvT n) (proj₁ (Ωt (tw n))))

EBOᶜ : Tr zero
EBOᶜ = proj₁ (ψ₀ᶜ Λ Ok-Λ pvΛ (proj₁ (Ωt Λ)))
```
