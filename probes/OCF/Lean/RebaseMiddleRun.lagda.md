# 重定位后的实际Native运行吸收原动态中槽

联立证明目标输出的Seed0与原mid到目标输出的有向界。遇到中Ω，
新链第1项先覆盖原初界；随后每个旧步骤由一个新步骤覆盖。没有把
编码的膨胀定理直接当跨运行器模拟。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.RebaseMiddleRun where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (mul)
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunFloor using (legal-num)
open import OCF.Align.BoundedCompletionUniformIf
open import OCF.Align.BoundedCompletionUniformClosure using (add-rel; prefix-rel; right-rel)
import OCF.Align.BoundedCompletionUniformRun as Native
open import OCF.Align.BoundedWorldValueTwoSlot using (U; V; mid)
open import OCF.Align.BoundedWorldSeedIf
import OCF.Align.BoundedWorldSeedClosure as S
open import OCF.Align.BoundedWorldSeedCompose using (trans0)
import OCF.Align.BoundedWorldSeedMiddle as Old
open import OCF.Lean.TwoSlotValueRun using (middle; middle-positive)
open import OCF.Align.BoundedWorldRebaseIf using (enc)
import OCF.Align.BoundedWorldRebaseRun as Code
open import OCF.Lean.RebaseMiddleIf
import OCF.Lean.Fold1Fold as F

read-mono : ∀ {a b} → Value (hs hz) a b → Value hz (read a) (read b)
read-mono p = Native.compare 1 0 {B = num 1} {B′ = num 1}
  (legal-num 1) (legal-num 1) hself hself (hsuc hself) (hsuc hself) p
read-positive : ∀ a → Value hz (hs hz) (read a)
read-positive a = Native.positive 1 0 (legal-num 1) hself (hsuc hself) a
eval-self : ∀ b a → Seed0 b → Seed1 a → Value hz (eval b a) (eval b a)
eval-self b a sb sa = read-mono (Code.mono (S.self1 sa) (S.self0 sb))

one-seed : Seed0 (hs hz)
one-seed = vs vz , (vz , tt)

chain-seed : ∀ H → (∀ e → Seed0 e → Seed0 (H e)) → ∀ n → Seed0 (chain H n)
chain-seed H keep zero = one-seed
chain-seed H keep (suc n) = S.add0 (chain-seed H keep n) (keep _ (chain-seed H keep n))
partial-seed : ∀ H → (∀ e → Seed0 e → Seed0 (H e)) → ∀ n →
  Seed0 (Ops.partial U (λ j → H (chain H j)) n)
partial-seed H keep zero = keep _ one-seed
partial-seed H keep (suc n) = S.add0 (partial-seed H keep n) (keep _ (chain-seed H keep (suc n)))
constant-seed : ∀ a → Seed0 a → ∀ n → Seed0 (Ops.partial U (λ _ → a) n)
constant-seed a sa zero = sa
constant-seed a sa (suc n) = S.add0 (constant-seed a sa n) sa
mixed-repeat : ∀ {a b} → Value hz a b → ∀ n →
  Value hz (mul a n) (Ops.partial U (λ _ → b) n)
mixed-repeat p zero = p
mixed-repeat p (suc n) = add-rel (mixed-repeat p n) p

-- up输入的mid全保留；坐标回收直接按关系推导，不用任意Same同余。
recover-up : ∀ {a b} → Value hz a b → ∀ u → Value hz a (mid u (up b))
recover-up vz u = vz
recover-up {b = hs b} (vs p) u = vli 1 (add-rel (recover-up p u) (middle-positive u (up b)))
recover-up (vr p) u = vli 0 (recover-up p u)
recover-up (vl p) u = vl (λ n → recover-up (p n) u)
recover-up (vli n p) u = vli n (recover-up p u)
recover-up (vo {κ = inj₁ ()} p) u
recover-up (vo {κ = inj₂ _} p) u = vo (λ x y xy → recover-up (p x y xy) u)
recover-up (vor {κ = inj₁ ()} p) u
recover-up (vor {κ = inj₂ _} p) u = vor (λ c → recover-up (p c) u)

mutual
  native-seed : ∀ b a → Seed0 b → Seed1 a → Seed0 (eval b a)
  middle-bound : ∀ {a b u v} → Seed0 u → Seed0 v → Seed1 a → Seed1 b →
    Value (hs hz) a b → Value hz u v → Value hz (mid u a) (eval v b)

  native-seed b hz sb sa = one-seed
  native-seed b (hs a) sb sa = eval-self b (hs a) sb sa ,
    constant-seed (eval b a) (native-seed b a sb (proj₂ sa))
  native-seed b (hl f) sb sa = eval-self b (hl f) sb sa ,
    (λ n → native-seed b (f n) sb (proj₂ sa n))
  native-seed b (hΩ (inj₁ (inj₁ ())) g) sb sa
  native-seed b (hΩ (inj₁ (inj₂ _)) g) sb sa =
    eval-self b (hΩ (inj₁ (inj₂ tt)) g) sb sa ,
    (λ c → trans0 (Old.recover-pure b c)
      (middle-bound sb sb (S.up1 (S.up0 c)) (proj₂ (proj₂ sa) c)
        (proj₁ (proj₂ sa) c) (S.self0 sb))) ,
    (λ c → native-seed b (g c) sb (proj₂ (proj₂ sa) c))
  native-seed b (hΩ (inj₂ _) g) sb sa =
    eval-self b (hΩ (inj₂ tt) g) sb sa , partial-seed H keep
    where
    H : HB U → HB U
    H e = eval (b ⊞ e) (g (b ⊞ e))
    keep : ∀ e → Seed0 e → Seed0 (H e)
    keep e se = native-seed (b ⊞ e) (g (b ⊞ e)) (S.add0 sb se)
      (proj₂ (proj₂ sa) (b ⊞ e) (S.add0 sb se))

  middle-bound {b = b} {v = v} su sv sa sb vz uv = read-positive (enc v b)
  middle-bound su sv sa sb (vs p) uv = vl (λ n → vli n
    (mixed-repeat (middle-bound su sv (proj₂ sa) (proj₂ sb) p uv) n))
  middle-bound su sv sa sb (vr p) uv = vli 0 (middle-bound su sv sa (proj₂ sb) p uv)
  middle-bound su sv sa sb (vl p) uv = vl (λ n → middle-bound su sv (proj₂ sa n) sb (p n) uv)
  middle-bound su sv sa sb (vli n p) uv = vli n (middle-bound su sv sa (proj₂ sb n) p uv)
  middle-bound su sv sa sb (vo {κ = inj₁ (inj₁ ())} p) uv
  middle-bound su sv sa sb (vo {κ = inj₁ (inj₂ _)} p) uv = vo (λ x y xy →
    middle-bound su sv (proj₂ (proj₂ sa) x) (proj₂ (proj₂ sb) y) (p x y xy) uv)
  middle-bound {u = u} {v} su sv sa sb (vo {κ = inj₂ _} {f} {g} p) uv =
    vl (λ n → vli (suc n) (sums n))
    where
    module L = F.Col _⊞_ _⊞_ u u (λ _ e → e)
      (λ b e → mid b (f e)) (λ b e → mid b (f e))
    H : HB U → HB U
    H e = eval (v ⊞ e) (g (v ⊞ e))
    keep : ∀ e → Seed0 e → Seed0 (H e)
    keep e se = native-seed (v ⊞ e) (g (v ⊞ e)) (S.add0 sv se)
      (proj₂ (proj₂ sb) (v ⊞ e) (S.add0 sv se))
    captured : ∀ e → Seed0 e → Value hz (v ⊞ e) (H e)
    captured e se = trans0 (recover-up (S.self0 cap) (v ⊞ e))
      (middle-bound cap cap (S.up1 cap) (proj₂ (proj₂ sb) (v ⊞ e) cap)
        (proj₁ (proj₂ sb) (v ⊞ e) cap) (S.self0 cap))
      where cap = S.add0 sv se
    current : ∀ n → L.cw n ≡ L.ce n
    current zero = refl
    current (suc n) = refl
    old-coordinates : ∀ n → Seed0 (L.ce n)
    old-outputs : ∀ n → Seed0 (L.oo n)
    old-coordinates zero = su
    old-coordinates (suc n) = S.add0 (old-coordinates n) (old-outputs n)
    old-outputs n rewrite current n = Old.preserve (old-coordinates n)
      (proj₂ (proj₂ sa) (L.ce n) (old-coordinates n))
    coordinates : ∀ n → Value hz (L.ce n) (chain H (suc n))
    outputs : ∀ n → Value hz (L.oo n) (H (chain H (suc n)))
    coordinates zero = trans0 (prefix-rel uv (hs hz))
      (right-rel (hs hz) (captured (hs hz) one-seed))
    coordinates (suc n) = add-rel (coordinates n) (outputs n)
    outputs n rewrite current n = middle-bound
      (old-coordinates n) (S.add0 sv (chain-seed H keep (suc n)))
      (proj₂ (proj₂ sa) (L.ce n) (old-coordinates n))
      (proj₂ (proj₂ sb) (v ⊞ chain H (suc n)) (S.add0 sv (chain-seed H keep (suc n))))
      (p (L.ce n) (v ⊞ chain H (suc n)) (right-rel v (coordinates n)))
      (right-rel v (coordinates n))
    sums : ∀ n → Value hz (L.oO n) (Ops.partial U (λ j → H (chain H j)) (suc n))
    sums zero = right-rel (H (chain H zero)) (outputs zero)
    sums (suc n) = add-rel (sums n) (outputs (suc n))
  middle-bound su sv sa sb (vor {κ = inj₁ (inj₁ ())} p) uv
  middle-bound su sv sa sb (vor {κ = inj₁ (inj₂ _)} p) uv = vor (λ c →
    middle-bound su sv sa (proj₂ (proj₂ sb) c) (p c) uv)
  middle-bound {v = v} su sv sa sb (vor {κ = inj₂ _} p) uv = vli 0
    (middle-bound su cap sa (proj₂ (proj₂ sb) (v ⊞ hs hz) cap)
      (p (v ⊞ hs hz)) (prefix-rel uv (hs hz)))
    where cap = S.add0 sv one-seed

instance-middle : MiddleComparison
instance-middle = record { native-seed = native-seed ; middle-bound = middle-bound }
```

中Ω初界覆盖使用其实际坐标膨胀字段，旧第n个输出送入新第n+1项。
目标输出Seed0也按同一原运行器证明，未更改其固定种子1、基本分支
或回灌算法。本篇还没有low末段比较或原C的覆盖定理。
