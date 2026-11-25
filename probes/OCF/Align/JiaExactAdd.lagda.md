# 逐项折叠的接线：原树加法与码列表连接

第四轮的辅助保持定理。原树加法对右树逐构造子递归，码侧取裸列表连接；
不做标准形正规化。ℕ 与 Ω 分支的基本列前缀律对一切非空右码成立。
关系的 Ω 子句只消费已有的低层相关输入，不给原始树补码。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaExactAdd where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans; sym; subst)
open import OCF.Align.EboLeanDef
  using (T; PT; ψ; sucT; cof; cω; cΩ; fsn; fsT)
open import OCF.Align.EboLeanView using (NE; ne)
open import OCF.Align.EboLean3Omega using (Acc′)
open import OCF.Align.JiaBase using (Tree; Low; module Layer)
open import OCF.Align.JiaRep using (Rep; module RelLayer)
open import OCF.Align.JiaExactFold using (copies)
open RelLayer using (rz; rs; rl; ro)

append-ne : ∀ A {B} → NE B → NE (A ++ B)
append-ne [] nB = nB
append-ne (x ∷ xs) nB = ne

cof-prepend : ∀ p {B} → NE B → cof (p ∷ B) ≡ cof B
cof-prepend p ne = refl

fsn-prepend : ∀ p {B} → NE B → ∀ n → fsn (p ∷ B) n ≡ p ∷ fsn B n
fsn-prepend p ne n = refl

fsT-prepend : ∀ p {B} → NE B → ∀ d → fsT (p ∷ B) d ≡ p ∷ fsT B d
fsT-prepend p ne d = refl

cof-append : ∀ A {B} → NE B → cof (A ++ B) ≡ cof B
cof-append [] nB = refl
cof-append (p ∷ A) nB = trans (cof-prepend p (append-ne A nB)) (cof-append A nB)

fsn-append : ∀ A {B} → NE B → ∀ n → fsn (A ++ B) n ≡ A ++ fsn B n
fsn-append [] nB n = refl
fsn-append (p ∷ A) nB n = trans (fsn-prepend p (append-ne A nB) n)
  (cong (p ∷_) (fsn-append A nB n))

fsT-append : ∀ A {B} → NE B → ∀ d → fsT (A ++ B) d ≡ A ++ fsT B d
fsT-append [] nB d = refl
fsT-append (p ∷ A) nB d = trans (fsT-prepend p (append-ne A nB) d)
  (cong (p ∷_) (fsT-append A nB d))

omega-ne : ∀ {B} → cof B ≡ cω → NE B
omega-ne {B = []} ()
omega-ne {B = p ∷ B} e = ne

Omega-ne : ∀ {B j} → cof B ≡ cΩ j → NE B
Omega-ne {B = []} ()
Omega-ne {B = p ∷ B} e = ne

module _ {ℓ : T} (a : Acc′ ℓ) where
  open Layer ℓ (Low ℓ a) using (_+_)

  rep-add : ∀ {x y A B} → Rep a x A → Rep a y B → Rep a (x + y) (A ++ B)
  rep-add {x} {A = A} rx rz = subst (Rep a x) (sym (++-identityʳ A)) rx
  rep-add {x} {A = A} rx (rs {x = y} {c = B} ry) =
    subst (Rep a (Layer.s (x + y))) (++-assoc A B (ψ [] [] ∷ []))
      (rs (rep-add rx ry))
  rep-add {x} {A = A} rx (rl {f = f} {c = B} e r) =
    rl (trans (cof-append A (omega-ne {B = B} e)) e)
      (λ n → subst (Rep a (x + f n)) (sym (fsn-append A (omega-ne {B = B} e) n))
        (rep-add rx (r n)))
  rep-add {x} {A = A} rx (ro {j} {p} {f} {c = B} e r) =
    ro (trans (cof-append A (Omega-ne {B = B} e)) e)
      (λ {y} {d} q → subst (Rep a (x + f y))
        (sym (fsT-append A (Omega-ne {B = B} e) d)) (rep-add rx (r q)))

  -- 新版 ψ 的后继行：n 份同一主项的原树，逐项对应 replicate n。
  rep-copies-single : ∀ {x p} → Rep a x (p ∷ []) →
    ∀ n → Rep a (copies {ℓ = ℓ} {a = a} x n) (replicate n p)
  rep-copies-single rx zero = rz
  rep-copies-single rx (suc n) = rep-add rx (rep-copies-single rx n)
```

`rep-add` 与 `rep-copies-single` 都对任意层号与可及证明成立，
没有阶段专属前提，也不假定 `Rep` 对所有原始树有实例。
它们是新版 ψ 后继情况的保持接线，尚不是 ψ 的完整保持定理。
