# 同一合法Source输入的局部修复验收

仍使用NegOutput.input本身。Component是逐构造子的单分量视图证书，
没有假设任意Source分支属于某分量，也不借Funext把两个树当作相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeCtxRepair where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (lz; ls)
open import OCF.Lean.LHRecLeg using (ek)
open import OCF.Lean.LHRecFl using (Lg-flL; up-⊲)
open import OCF.Align.BoundedDescentValueBridge using (Native; Source)
open import OCF.Align.BoundedNativeCtxIf
open import OCF.Align.BoundedNativeCtxRun
import OCF.Align.BoundedNativeViewNegOutput as Old
open import OCF.Align.BoundedNativeViewNegCopies using (one; B; pc; W; D; one-to-D)

data Component (c : Cd) : HB (Native c) → HB Source → Set where
  cz : Component c hz hz
  cs : ∀ {a x} → Component c a x → Component c (hs a) (hs x)
  cl : ∀ {f g} → (∀ n → Component c (f n) (g n)) → Component c (hl f) (hl g)
  co : ∀ {κ f g} → (∀ e → Component c (f e) (g e)) →
    Component c (hΩ κ f) (hΩ (inj₂ c , κ) g)

repair : ∀ {c t a x} (q : c ⊲ t) → Component c a x → HB (Native t)
repair {a = a} q p = Keep.run q a
repair-legal : ∀ {c t a x} (q : c ⊲ t) → (p : Component c a x) → LgB a → LgB (repair q p)
repair-legal q p l = Keep.legal q _ l

original-component : ∀ a → Component one a (Old.put a)
original-component hz = cz
original-component (hs a) = cs (original-component a)
original-component (hl f) = cl (λ n → original-component (f n))
original-component (hΩ κ g) = co (λ e → original-component (g e))

repaired : HB (Native B)
repaired = repair {a = Old.floor} {x = Old.input} pc (original-component Old.floor)
legal-repaired : LgB repaired
legal-repaired = Keep.legal pc Old.floor (Lg-flL (ls (ls lz)))

-- 引发原反例的两个kind现在确实都选择第1拷贝。
selected-new : ek (context pc) (inj₂ tt) ≡ (1 , inj₂ tt)
selected-new = refl
selected-bottom : ek (context pc) (inj₁ (inj₂ tt)) ≡ (1 , inj₁ (inj₂ tt))
selected-bottom = refl

repaired-branch-path : Keep.run pc (up (hs hz)) ⊲[ W ] Keep.run pc (up D)
repaired-branch-path = Keep.position pc (up-⊲ one-to-D)
```

原输入合法性由Old.legal-input给出，原输出非法由Old.no-legal-output
给出；本篇对同一Source输入的真实单分量视图得到合法输出，并恢复原来
失败的分支位置。未修改旧定义。修复原因来自树侧合法性编译否定，
不是为了值验收方便。c>t及一般混合Source仍未在这里修复，值未断言。
