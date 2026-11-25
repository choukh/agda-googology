# 任意上下文中的零次回灌与有限分裂

第四层。每个后继步、每个普通极限分支以及规则 6 的第零枝，在任意嵌套位置均可由一次有限分裂执行。一次正迭代已能保持此编码完全相同。深度按起始有限项给定，以下动作均保持深度。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4CriticalFrames where

open import Data.Nat.Base using (ℕ; zero; suc; _⊔_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.List.Base using (List; []; _∷_; _++_; map; replicate)
import Data.List.Properties as LP
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.EboLeanDef hiding (lt; eq)
open import OCF.Align.EBO using (pred-suc)
open import OCF.Align.EboLeanView using (VΩ; ωs; ωr; ωl; ωp; Vω; ws; wl; w4; w5; w6; fω; fω-eq; fΩ; vω)
import Survey.W4CriticalDescent as C
import Survey.W4MultisetDescent as M
import W4Fold as Fold
open import WVOne using (read)
open import Data.List.Relation.Unary.All using ([]; _∷_)

data Edit : T → T → Set where
  erase : ∀ {x xs} → Edit (x ∷ xs) xs
  keep : ∀ {x a b} → Edit a b → Edit (x ∷ a) (x ∷ b)
  index : ∀ {u v a} → Edit u v → ∀ n → Edit (ψ u a ∷ []) (replicate n (ψ v a))
  arg : ∀ {u a b} → Edit a b → ∀ n → Edit (ψ u a ∷ []) (replicate n (ψ u b))

last-one : ∀ t → Edit (sucT t) t
last-one [] = erase
last-one (x ∷ xs) = keep (last-one xs)

predecessor : ∀ t → cof t ≡ c1 → Edit t (pred t)
predecessor t e = subst (λ s → Edit s (pred t)) (pred-suc t e) (last-one (pred t))

-- 零次迭代在唯一的规则叶把 Ω_(ν+1) 换为 Ω_ν。
leaf : ∀ {b ν} (v : VΩ b ν) → Edit b (fΩ v (Ωt ν))
leaf (ωs v) = keep (leaf v)
leaf (ωr {u} e) = index (predecessor u e) 1
leaf (ωl _ v) = index (leaf v) 1
leaf (ωp _ _ v) = arg (leaf v) 1

data Allowed : C.Kind → ℕ → Set where
  ordinary : ∀ {n} → Allowed C.plain n
  initial : Allowed C.feedback zero

compile : ∀ {t} (v : Vω t) n → Allowed (C.kind v) n → Edit t (fω v n)
compile (ws v) n a = keep (compile v n a)
compile (wl _ v) n a = index (compile v n a) 1
compile (w4 {b = b} e) n _ = arg (predecessor b e) n
compile (w5 _ v) n a = arg (compile v n a) 1
compile (w6 _ _ v) .zero initial = arg (leaf v) 1

actual-fs : ∀ t (e : cof t ≡ cω) n → Allowed (C.kind (vω t e)) n → Edit t (fsn t n)
actual-fs t e n a = subst (Edit t) (sym (fω-eq (vω t e) n)) (compile (vω t e) n a)

data Fits : ℕ → T → Set where
  nil : ∀ {d} → Fits d []
  cons : ∀ {d u a xs} → Fits d u → Fits d a → Fits (suc d) xs → Fits (suc d) (ψ u a ∷ xs)

widen : ∀ {d e t} → d ≤ e → Fits d t → Fits e t
widen h nil = nil
widen (s≤s h) (cons u a xs) = cons (widen h u) (widen h a) (widen (s≤s h) xs)

depth : T → ℕ
depth [] = 0
depth (ψ u a ∷ xs) = suc ((depth u ⊔ depth a) ⊔ depth xs)

fits : ∀ t → Fits (depth t) t
fits [] = nil
fits (ψ u a ∷ xs) = cons
  (widen (≤-trans (m≤m⊔n (depth u) (depth a)) (m≤m⊔n (depth u ⊔ depth a) (depth xs))) (fits u))
  (widen (≤-trans (m≤n⊔m (depth u) (depth a)) (m≤m⊔n (depth u ⊔ depth a) (depth xs))) (fits a))
  (widen (≤-trans (m≤n⊔m (depth u ⊔ depth a) (depth xs)) (Data.Nat.Properties.n≤1+n _)) (fits xs))

many : ∀ {d u a} → Fits d u → Fits d a → ∀ n → Fits (suc d) (replicate n (ψ u a))
many u a zero = nil
many u a (suc n) = cons u a (many u a n)

preserve : ∀ {d s t} → Edit s t → Fits d s → Fits d t
preserve erase (cons _ _ xs) = xs
preserve (keep e) (cons u a xs) = cons u a (preserve e xs)
preserve (index e n) (cons u a _) = many (preserve e u) a n
preserve (arg e n) (cons u a _) = many u (preserve e a) n

Y = read Fold.EBOᶜ
bag = M.State Y
move : ∀ d → bag d → bag d → Set
move = M.Move

combine : ∀ {X : Set} → (T → List X) → PT → List X
combine f (ψ u a) = f u ++ f a

code : ∀ d → T → bag (suc d)
code zero _ = []
code (suc d) t = map (combine (code d)) t

suffix : ∀ {X : Set} {R : X → X → Set} {a b} → M.Split R a b → ∀ xs →
  M.Split R (a ++ xs) (b ++ xs)
suffix (M.replace {xs = ys} {ys = zs} children) xs =
  subst (M.Split _ _) (sym (LP.++-assoc zs ys xs)) (M.replace children)
suffix (M.keep h) xs = M.keep (suffix h xs)

reps : ∀ {X Z : Set} (f : X → Z) n x → map f (replicate n x) ≡ replicate n (f x)
reps f zero x = refl
reps f (suc n) x = cong (f x ∷_) (reps f n x)

copy-step : ∀ d u a n {old : bag (suc d)} →
  move (suc d) old (code d u ++ code d a) →
  move (suc (suc d)) (old ∷ []) (code (suc d) (replicate n (ψ u a)))
copy-step d u a n {old} h = subst (move (suc (suc d)) (old ∷ [])) eq′
  (M.replace (M.copies {d = move (suc d)} {x = old} {y = code d u ++ code d a} h n))
  where
  eq′ = trans (LP.++-identityʳ (replicate n (code d u ++ code d a)))
    (sym (reps (combine (code d)) n (ψ u a)))

pay : ∀ {s t d} → Edit s t → Fits d s → move (suc d) (code d s) (code d t)
pay erase (cons _ _ _) = M.replace []
pay (keep e) (cons _ _ xs) = M.keep (pay e xs)
pay (index {v = v} {a} e n) (cons {d} u _ _) = copy-step d v a n (suffix (pay e u) (code d a))
pay (arg {u} {b = b} e n) (cons {d} _ a _) = copy-step d u b n (M.prefix (code d u) (pay e a))

-- 第一层正迭代把 Ω₁ 的下标一改放在参数处，合并两侧的编码辨认不出这一步。
first-positive : C.Edge C.feedback (C.epsilon ∷ []) (fsn (C.epsilon ∷ []) 1)
first-positive = C.at refl 1

collision : ∀ d → code d (C.epsilon ∷ []) ≡ code d (fsn (C.epsilon ∷ []) 1)
collision zero = refl
collision (suc zero) = refl
collision (suc (suc zero)) = refl
collision (suc (suc (suc d))) = refl
```
