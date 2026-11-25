# YiOmNeg 第 4 项 (续)：单个闭的目标，条件定理

**判决：条件定理，前提是第 0 层的值的序列上的函数外延 (`FunextR`)。** 目标固定为一个闭的位置 (第 `ω′+2` 支的根，层号 `ω′+1`)，树是 `top`：
各支的像满足保留律与折叠律 (`FixedBranch`，两条都只对与目标有路径相连的支要求)，则 WLPO。没有这个前提时，单个闭目标上推出什么没有判定。
`FixedBranch` 在排中律的实例 `HitDec` 下有模型。不否定目标层里没有极限层号位置的情形。主文 [YiOmNegBranch](YiOmNegBranch.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiOmNegBranchFixed where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
open import OCF.Align.YiLvIf
open import OCF.Align.YiRawIf using (IsLim)
open import OCF.Align.YiOmIf
open import OCF.Align.YiIrrNegWide using (seen; seen-mono; seen-hit)
open import OCF.Align.YiLvNegCompare
  using (At; onesᴰ; tickᴰ; tickᴰ-step; tickᴰ-lgl; betaᴰ; tick-flat; bodyᴸ)
open import OCF.Align.YiRawNegOmega
  using (K₂ω; br; Link; WLPO; read-shape; not-true; true≢false; placeᵒ; placeᵒ-kept)
```

## 1 目标与记录

目标层 `suc λ`，`λ = lim (1, 1, …)`：它的位置上的层号只有 `λ` 与 0。分支的像与保留律的写法同主文，目标不再变；
`Hit s`：第 `suc s` 支与目标有路径相连，并且它根上的层号在目标层的位置上。保留律在 `Hit` 时要求保留，折叠律在 `Hit` 不成立时要求输出是极限。

```agda
FunextR : Set
FunextR = ∀ (f g : ℕ → R) → (∀ n → f n ≡ g n) → f ≡ g

η_f : R
η_f = G.suc (G.suc onesᴰ)

e_f : Gd zero raw1 η_f
e_f = inj₂ (inj₂ (inj₂ (zero , inj₁ refl))) , ((λ _ → inj₁ refl) , (λ _ → tt)) , raw0-Nested η_f

q_f : Pre K₂ω
q_f = br η_f e_f (inj₁ tt)

q_f-level : lev K₂ω q_f ≡ suc (lim (λ _ → suc zero))
q_f-level = refl

Hit : R → Set
Hit s = (Cp zero (G.suc s) η_f ⊎ Cp zero η_f (G.suc s)) × At (lev K₂ω q_f) (read0 s)

hit-link : ∀ s (e : Gd zero raw1 (G.suc s)) →
  Hit s ≡ (Link (br (G.suc s) e (inj₁ tt)) q_f × At (lev K₂ω q_f) (read0 s))
hit-link s e = refl

record FixedBranch : Set where
  field
    branch : (η : R) → .(Gd zero raw1 η) → Raw (lev K₂ω q_f)
    branch-keep : ∀ s (e : Gd zero raw1 (G.suc s)) → Hit s →
      Kept (lev K₂ω q_f) (read0 s) (branch (G.suc s) e)
    branch-fold : ∀ s (e : Gd zero raw1 (G.suc s)) → (Hit s → ⊥) →
      IsLim (branch (G.suc s) e)
```

## 2 探针的一族分支

坐标 `suc (betaᴰ (seen α))`：`betaᴰ γ = lim (tickᴰ (γ m))`，假给 1，真给 `λ+1`。守卫对一切 `α` 有闭的相关证明。
它根上的层号 `read0 (betaᴰ (seen α))` 在目标层的位置上当且仅当它字面等于 `λ`；这推出 `α` 全假，反向要函数外延。

```agda
one-tick : ∀ x → Cp zero one (tickᴰ x)
one-tick false = inj₁ refl
one-tick true = inj₂ (inj₂ (zero , inj₁ refl))

guardᵇ : ∀ α → Gd zero raw1 (G.suc (betaᴰ (seen α)))
guardᵇ α =
  inj₂ (inj₂ (zero , one-tick (seen α zero))) ,
  ((λ m → tickᴰ-step (seen α m) (seen α (suc m)) (seen-mono α m)) ,
   (λ m → tickᴰ-lgl (seen α m))) ,
  raw0-Nested (G.suc (betaᴰ (seen α)))

at→false : ∀ α → At (lev K₂ω q_f) (read0 (betaᴰ (seen α))) → ∀ n → α n ≡ false
at→false α (inj₁ _ , e) n = not-true (α n) (λ p → true≢false
  (trans (sym (seen-hit α n p))
    (tick-flat (seen α n) _ (sym (cong (λ x → bodyᴸ x n) e)))))
at→false α (inj₂ (m , inj₁ _) , ()) n
at→false α (inj₂ (m , inj₂ ()) , e) n

seen-false : ∀ α → (∀ n → α n ≡ false) → ∀ m → seen α m ≡ false
seen-false α h zero = h zero
seen-false α h (suc m) = cong₂ _∨_ (seen-false α h m) (h (suc m))

false→flat : FunextR → ∀ α → (∀ n → α n ≡ false) → betaᴰ (seen α) ≡ onesᴰ
false→flat fe α h =
  cong G.lim (fe (λ m → tickᴰ (seen α m)) (λ _ → one) (λ m → cong tickᴰ (seen-false α h m)))

false→hit : FunextR → ∀ α → (∀ n → α n ≡ false) → Hit (betaᴰ (seen α))
false→hit fe α h =
  inj₁ (inj₂ (inj₁ (cong G.suc (false→flat fe α h)))) ,
  (inj₁ tt , cong read0 (sym (false→flat fe α h)))
```

## 3 条件定理与模型

```agda
fixed→wlpo : FunextR → FixedBranch → WLPO
fixed→wlpo fe F α
  with read-shape (branch (G.suc (betaᴰ (seen α))) (guardᵇ α))
         (branch-keep (betaᴰ (seen α)) (guardᵇ α))
         (branch-fold (betaᴰ (seen α)) (guardᵇ α))
  where open FixedBranch F
... | inj₁ no = inj₂ (λ h → no (false→hit fe α h))
... | inj₂ nn = inj₁ (λ n → not-true (α n) (λ p → nn (λ a →
    true≢false (trans (sym p) (at→false α (proj₂ a) n)))))

HitDec : Set
HitDec = ∀ s → Hit s ⊎ (Hit s → ⊥)

placeʰ : ∀ s → Hit s ⊎ (Hit s → ⊥) → Raw (lev K₂ω q_f)
placeʰ s (inj₁ (l , a)) = placeᵒ (lev K₂ω q_f) (read0 s) (inj₁ a)
placeʰ s (inj₂ no) = G.lim (λ _ → G.zero)

placeʰ-kept : ∀ s (o : Hit s ⊎ (Hit s → ⊥)) → Hit s →
  Kept (lev K₂ω q_f) (read0 s) (placeʰ s o)
placeʰ-kept s (inj₁ (l , a)) h = placeᵒ-kept (lev K₂ω q_f) (read0 s) (inj₁ a) a
placeʰ-kept s (inj₂ no) h = ⊥-elim (no h)

placeʰ-lim : ∀ s (o : Hit s ⊎ (Hit s → ⊥)) → (Hit s → ⊥) → IsLim (placeʰ s o)
placeʰ-lim s (inj₁ h) no = ⊥-elim (no h)
placeʰ-lim s (inj₂ _) no = tt

branchᶠ : HitDec → R → Raw (lev K₂ω q_f)
branchᶠ orc (G.suc s) = placeʰ s (orc s)
branchᶠ orc G.zero = G.zero
branchᶠ orc (G.lim f) = G.zero
branchᶠ orc (G.lc () c t g)
branchᶠ orc (G.em () T)
branchᶠ orc G.top = G.zero

oracle-fixed : HitDec → FixedBranch
oracle-fixed orc = record
  { branch = λ η e → branchᶠ orc η
  ; branch-keep = λ s e h → placeʰ-kept s (orc s) h
  ; branch-fold = λ s e no → placeʰ-lim s (orc s) no }
```

范围。目标位置的守卫是闭的相关证明；它是不是 `Ω₁⁺` 的规范的链走到的坐标，没有判定 (`ω′` 的各项相等，是合法但不严格增的极限)。
机制与主文不同：主文判定 "极限层号里有没有层号 1 的位置" (对下标的搜索)；这里判定 "一个极限层号是否字面等于目标层里的极限层号" (函数的相等)，所以要函数外延才能回到 WLPO。
