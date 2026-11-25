# FGH 式折叠 (原型): 后继是整族底的迭代, 不严格低于目标的分支在自己的层上取对角

> 判决: 候选原型 (折叠), 不替换主线. 树、层号、路径与证据沿用主线 (`YiRWBlock`, `YiRWOps`, `YiRWPath`), 保留判定沿用 `YiRWFold.kp`; 折叠 `Φ` 与严格膨胀 `infl`、单调 `mono` 互递归, 无前提.
> 做法: 零给 `suc β`; 后继对 (底族, 目标底) 整体迭代 (FGH 的 f_{a+1} = f_a^ω, 每一层都从当前累积的值出发); 结点只看槽位是否字面地严格低于目标: 是则保留, 否则在槽位自己的层上取对角, 下标是首分支折叠后的底族在该层的值 (以输出作下标). 链不在结点里, 由后继的迭代给出.
> 不否定什么. 坐标与回退两行照抄主线 (Ω 形状经指定孩子的路径仍回退, 见 `YiFGCheck`). 闭项 `twᶠ`, `EBOᶠ` 取 Ω 数加一 (FGH 的移位), 裸的 `twᶠ⁰` 作对照.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFGFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; kp)
```

## 结点

保留则在目标层的槽位上逐分支折叠, 否则取对角值 `D`. 两条引理给单调与膨胀用.

```agda
suc⁺ : ∀ {S : Sg} → T⁺ {S} → T⁺ {S}
suc⁺ (b , nb) = suc b , ◃t nb ◃s

nodeF : ∀ {j X x₀} → Keep j X x₀ → (X → Tr⁺ j) → Tr⁺ j → Tr⁺ j
nodeF (just (q , cv , _)) G D = Ω⁺ q (λ z → G (cv z))
nodeF nothing             G D = D

nodeLe : ∀ {j X x₀} (m : Keep j X x₀) (G : X → Tr⁺ j) (D : Tr⁺ j)
       → j ⊢ proj₁ (G x₀) ◃ proj₁ D → j ⊢ proj₁ (G x₀) ◃ proj₁ (nodeF m G D)
nodeLe {j} (just (q , cv , e)) G D d = subst (λ t → j ⊢ proj₁ (G t) ◃ Ω q (λ z → proj₁ (G (cv z)))) e ◃w
nodeLe nothing                 G D d = d

nodeIn : ∀ {j X x₀} (m : Keep j X x₀) (G : X → Tr⁺ j) (D : Tr⁺ j) {b : Tr j}
       → (∀ z → j ⊢ b ◃ proj₁ (G z)) → j ⊢ b ◃ proj₁ D → j ⊢ b ◃ proj₁ (nodeF m G D)
nodeIn {j} (just (q , cv , e)) G D h d = ◃t (h (cv (fromBr j q zero))) ◃w
nodeIn nothing                 G D h d = d
```

## 折叠, 膨胀, 单调

`jB x B`: 底族的每一层都折一次 x (一步作用在整族上); 后继迭代 (底族, 目标底) 这一对. 结点的对角: 首分支 `g b₀` 折完后的底族 `jB (g b₀) B` 在槽位自己的层 (路径 `posW`) 上的值作下标, 目标底取首分支的值.

```agda
mutual
  Φ : (ℓ : L) → Ok ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j
  Φ ℓ o B j w β zero      = suc⁺ β
  Φ ℓ o B j w β (suc x)   = lim⁺ (λ n → proj₂ (iter (λ P → jB ℓ o (proj₁ P) x , Φ ℓ o (proj₁ P) j w (proj₂ P) x) (B , β) n))
    (λ n → infl ℓ o (proj₁ (iter (λ P → jB ℓ o (proj₁ P) x , Φ ℓ o (proj₁ P) j w (proj₂ P) x) (B , β) n)) j w
                    (proj₂ (iter (λ P → jB ℓ o (proj₁ P) x , Φ ℓ o (proj₁ P) j w (proj₂ P) x) (B , β) n)) x)
  Φ ℓ o B j w β (lim f a) = lim⁺ (λ n → Φ ℓ o B j w β (f n)) (λ n → mono ℓ o B j w β (a n))
  Φ ℓ o B j w β (Ω p g)   = nodeF (kp ℓ o p w) (λ z → Φ ℓ o B j w β (g z))
    (Φ ℓ o (jB ℓ o B (g (fromBr ℓ p zero))) j w (Φ ℓ o B j w β (g (fromBr ℓ p zero)))
       (g (fromBr ℓ p (proj₁ (jB ℓ o B (g (fromBr ℓ p zero)) (at ℓ p) (posW ℓ p))))))
  Φ (nd s h) o B _ self β (up x c y e) = Up (h c) (down stop c) (Φ (nd s h) o B _ self β x) y
  Φ (nd s h) o B j (inu ws) β (up x c y e) =
    Φ (h c) (proj₂ o c) ((λ i u → Φ (nd s h) o B i (inc c u) (B i (inc c u)) x)) j (ws c) (Φ (nd s h) o B j (inu ws) β x) y
  Φ (nd (sΩ k) h) o B j (ink v) β (up x c y e) =
    Φ (h c) (proj₂ o c) ((λ i u → Φ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x)) j (v ∙ proj₂ (proj₁ o) c) (Φ (nd (sΩ k) h) o B j (ink v) β x) y
  Φ (nd sS h) o B j (inc c′ v) β (up x c y e) =
    Φ (h c) (proj₂ o c) ((λ i u → Φ (nd sS h) o B i (inc c u) (B i (inc c u)) x)) j v (Φ (nd sS h) o B j (inc c′ v) β x) y
  Φ (nd sL g) o B j (inc n v) β (up x m y e) = cW (way g (proj₁ o) m n)
    (λ u → Φ (g n) (proj₂ o n) ((λ i u → Φ (nd sL g) o B i (inc n u) (B i (inc n u)) x)) j v (Φ (nd sL g) o B j (inc n v) β x)
             (proj₁ (emb (g n) (proj₂ o n) u (y , e))))
    (λ u → Φ (g m) (proj₂ o m) ((λ i u → Φ (nd sL g) o B i (inc m u) (B i (inc m u)) x)) j (v ∙ u) (Φ (nd sL g) o B j (inc n v) β x) y)
  Φ (nd (sΩ k) h) o B j (inc c′ v) β (up x c y e) =
    Φ (nd (sΩ k) h) o B j (inc c′ v) β x ⊞ Φ (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y

  jB : (ℓ : L) → Ok ℓ → Base ℓ → Tr ℓ → Base ℓ
  jB ℓ o B x i u = Φ ℓ o B i u (B i u) x

  infl : (ℓ : L) (o : Ok ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) (x : Tr ℓ)
       → j ⊢ proj₁ β ◃ proj₁ (Φ ℓ o B j w β x)
  infl ℓ o B j w β zero      = ◃s
  infl ℓ o B j w β (suc x)   = ◃l zero
  infl ℓ o B j w β (lim f a) = ◃t (infl ℓ o B j w β (f zero)) (◃l zero)
  infl ℓ o B j w β (Ω p g)   = nodeIn (kp ℓ o p w) (λ z → Φ ℓ o B j w β (g z)) _
    (λ z → infl ℓ o B j w β (g z))
    (◃t (infl ℓ o B j w β (g (fromBr ℓ p zero)))
        (infl ℓ o (jB ℓ o B (g (fromBr ℓ p zero))) j w (Φ ℓ o B j w β (g (fromBr ℓ p zero)))
           (g (fromBr ℓ p (proj₁ (jB ℓ o B (g (fromBr ℓ p zero)) (at ℓ p) (posW ℓ p)))))))
  infl (nd s h) o B _ self β (up x c y e) =
    ◃t (infl (nd s h) o B _ self β x) (Upm (h c) (down stop c) (Φ (nd s h) o B _ self β x) e)
  infl (nd s h) o B j (inu ws) β (up x c y e) =
    ◃t (infl (nd s h) o B j (inu ws) β x)
       (infl (h c) (proj₂ o c) ((λ i u → Φ (nd s h) o B i (inc c u) (B i (inc c u)) x)) j (ws c) (Φ (nd s h) o B j (inu ws) β x) y)
  infl (nd (sΩ k) h) o B j (ink v) β (up x c y e) =
    ◃t (infl (nd (sΩ k) h) o B j (ink v) β x)
       (infl (h c) (proj₂ o c) ((λ i u → Φ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x)) j (v ∙ proj₂ (proj₁ o) c) (Φ (nd (sΩ k) h) o B j (ink v) β x) y)
  infl (nd sS h) o B j (inc c′ v) β (up x c y e) =
    ◃t (infl (nd sS h) o B j (inc c′ v) β x)
       (infl (h c) (proj₂ o c) ((λ i u → Φ (nd sS h) o B i (inc c u) (B i (inc c u)) x)) j v (Φ (nd sS h) o B j (inc c′ v) β x) y)
  infl (nd sL g) o B j (inc n v) β (up x m y e) =
    ◃t (infl (nd sL g) o B j (inc n v) β x)
       (cW-ind (λ Z → j ⊢ proj₁ (Φ (nd sL g) o B j (inc n v) β x) ◃ proj₁ Z) (way g (proj₁ o) m n)
         (λ u → infl (g n) (proj₂ o n) ((λ i u → Φ (nd sL g) o B i (inc n u) (B i (inc n u)) x)) j v (Φ (nd sL g) o B j (inc n v) β x)
                  (proj₁ (emb (g n) (proj₂ o n) u (y , e))))
         (λ u → infl (g m) (proj₂ o m) ((λ i u → Φ (nd sL g) o B i (inc m u) (B i (inc m u)) x)) j (v ∙ u) (Φ (nd sL g) o B j (inc n v) β x) y))
  infl (nd (sΩ k) h) o B j (inc c′ v) β (up x c y e) =
    ◃t (infl (nd (sΩ k) h) o B j (inc c′ v) β x)
       (+-mono _ (ι-mono j (proj₂ (Φ (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y))))

  mono : (ℓ : L) (o : Ok ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) {x y : Tr ℓ}
       → ℓ ⊢ x ◃ y → j ⊢ proj₁ (Φ ℓ o B j w β x) ◃ proj₁ (Φ ℓ o B j w β y)
  mono ℓ o B j w β ◃s                 = ◃l (suc zero)
  mono ℓ o B j w β (◃l n)             = ◃l n
  mono ℓ o B j w β (◃w {p = p} {g = g}) = nodeLe (kp ℓ o p w) (λ z → Φ ℓ o B j w β (g z)) _
    (infl ℓ o (jB ℓ o B (g (fromBr ℓ p zero))) j w (Φ ℓ o B j w β (g (fromBr ℓ p zero)))
       (g (fromBr ℓ p (proj₁ (jB ℓ o B (g (fromBr ℓ p zero)) (at ℓ p) (posW ℓ p))))))
  mono (nd s h) o B _ self β (◃u x c y e) = Upm (h c) (down stop c) (Φ (nd s h) o B _ self β x) e
  mono (nd s h) o B j (inu ws) β (◃u x c y e) =
    infl (h c) (proj₂ o c) ((λ i u → Φ (nd s h) o B i (inc c u) (B i (inc c u)) x)) j (ws c) (Φ (nd s h) o B j (inu ws) β x) y
  mono (nd (sΩ k) h) o B j (ink v) β (◃u x c y e) =
    infl (h c) (proj₂ o c) ((λ i u → Φ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x)) j (v ∙ proj₂ (proj₁ o) c) (Φ (nd (sΩ k) h) o B j (ink v) β x) y
  mono (nd sS h) o B j (inc c′ v) β (◃u x c y e) =
    infl (h c) (proj₂ o c) ((λ i u → Φ (nd sS h) o B i (inc c u) (B i (inc c u)) x)) j v (Φ (nd sS h) o B j (inc c′ v) β x) y
  mono (nd sL g) o B j (inc n v) β (◃u x m y e) =
    cW-ind (λ Z → j ⊢ proj₁ (Φ (nd sL g) o B j (inc n v) β x) ◃ proj₁ Z) (way g (proj₁ o) m n)
      (λ u → infl (g n) (proj₂ o n) ((λ i u → Φ (nd sL g) o B i (inc n u) (B i (inc n u)) x)) j v (Φ (nd sL g) o B j (inc n v) β x)
               (proj₁ (emb (g n) (proj₂ o n) u (y , e))))
      (λ u → infl (g m) (proj₂ o m) ((λ i u → Φ (nd sL g) o B i (inc m u) (B i (inc m u)) x)) j (v ∙ u) (Φ (nd sL g) o B j (inc n v) β x) y)
  mono (nd (sΩ k) h) o B j (inc c′ v) β (◃u x c y e) =
    +-mono _ (ι-mono j (proj₂ (Φ (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)))
  mono (nd s h) o B _ self β (◃c x c r) = Upm (h c) (down stop c) (Φ (nd s h) o B _ self β x) r
  mono (nd s h) o B j (inu ws) β (◃c x c r) =
    mono (h c) (proj₂ o c) ((λ i u → Φ (nd s h) o B i (inc c u) (B i (inc c u)) x)) j (ws c) (Φ (nd s h) o B j (inu ws) β x) r
  mono (nd (sΩ k) h) o B j (ink v) β (◃c x c r) =
    mono (h c) (proj₂ o c) ((λ i u → Φ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x)) j (v ∙ proj₂ (proj₁ o) c) (Φ (nd (sΩ k) h) o B j (ink v) β x) r
  mono (nd sS h) o B j (inc c′ v) β (◃c x c r) =
    mono (h c) (proj₂ o c) ((λ i u → Φ (nd sS h) o B i (inc c u) (B i (inc c u)) x)) j v (Φ (nd sS h) o B j (inc c′ v) β x) r
  mono (nd sL g) o B j (inc n v) β (◃c x m r) =
    cW-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (way g (proj₁ o) m n)
      (λ u → mono (g n) (proj₂ o n) ((λ i u → Φ (nd sL g) o B i (inc n u) (B i (inc n u)) x)) j v (Φ (nd sL g) o B j (inc n v) β x) (emb-mono (g n) (proj₂ o n) u r))
      (λ u → mono (g m) (proj₂ o m) ((λ i u → Φ (nd sL g) o B i (inc m u) (B i (inc m u)) x)) j (v ∙ u) (Φ (nd sL g) o B j (inc n v) β x) r)
  mono (nd (sΩ k) h) o B j (inc c′ v) β (◃c x c r) =
    +-mono _ (ι-mono j (mono (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) r))
  mono ℓ o B j w β (◃t d d′) = ◃t (mono ℓ o B j w β d) (mono ℓ o B j w β d′)
```

## 闭项

目标第 0 层, 一致路径, 默认底族 (每层是该层的 Ω 树), 目标底 `Ωt zero`. 塔与 Λ 取 Ω 数加一.

```agda
ψ₀ᶠ : (ℓ : L) → Ok ℓ → Tr ℓ → Tr⁺ zero
ψ₀ᶠ ℓ o = Φ ℓ o (B₀ ℓ) zero (z≤ ℓ) (Ωt zero)

twᶠ⁰ twᶠ : ℕ → Tr zero
twᶠ⁰ n = proj₁ (ψ₀ᶠ (tw n) (Ok-tw n) (proj₁ (Ωt (tw n))))
twᶠ  n = proj₁ (ψ₀ᶠ (tw n) (Ok-tw n) (suc (proj₁ (Ωt (tw n)))))

EBOᶠ : Tr zero
EBOᶠ = proj₁ (ψ₀ᶠ Λ Ok-Λ (suc (proj₁ (Ωt Λ))))
```
