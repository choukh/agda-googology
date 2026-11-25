# φ 的配对否定: 按层号相等判 "能保留" 推出 LPO

> 验收文件 (否定). 判决: 编译定理, 前提是接口实例 I (`phi` 即是) 与加强 `FullSem I`. k 侧目标遇到孩子里的结点时, 若 "结点槽位的层号字面等于目标的某个槽位层号就保留, 且交出的槽位层号相同" (`FullSem`), 就推出 LPO (`fullSem→lpo`); `phi` 不满足它 (`phi-not-fullSem`).
> 探针不在规范域: 孩子层 `lim (gα α)` 不合法, 结点槽位不是顶槽位 (`R13Top.IsTop` 在 ℕ 极限层恒假). 读作 "按层号相等定义保留, 谓词太宽"; 机制与 `YiUniNegStep.step-full→lpo` 同 (保留可否是层号上的存在命题).
> 不否定什么: 按路径与证据定义的保留 (`YiPhiNegK.KAll`, `phi` 满足); 规范域内的任何加强.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPhiNegKSem where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (Ωt)
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiPhiIface using (Iface)
open import OCF.Lean.YiPhiCheck using (phi)
```

## 加强: 按层号相等的 "能保留处都保留"

对一切 `Ωₗ k h`, 目标 k (路径 `ink self`), 孩子 c 里的单个结点 `Ω t G`: 目标 k 有与 t 同层号的槽位, 输出就是以同层号槽位为根的结点.

```agda
FullSem : Iface → Set
FullSem I = (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (B : Base (Ωₗ k h)) (β : Tr k)
  (x : Tr (Ωₗ k h)) (c : Tr k) (t : Pos (h c)) (G : Br (h c) t → Tr (h c))
  → Σ (Pos k) (λ q → at k q ≡ at (h c) t)
  → Σ (Pos k) λ q → Σ (Br k q → Tr k) λ G′ →
      (Iface.ψs I (Ωₗ k h) ε B k (ink self) β (up x c (Ω t G)) ≡ Ω q G′) × (at k q ≡ at (h c) t)
```

## 探针

`Kα α` 的第 m 项在 α 于 m 之前有真值时是 2, 否则是 1; 它有层号 2 的槽位当且仅当 α 有真值. 孩子层的第 0 项是 `Kα α` (证据路径 `inl zero self`), 第 1 项是 2, 结点槽位取第 1 项自身.

```agda
Found : (ℕ → Bool) → Set
Found α = Σ ℕ λ n → α n ≡ true

LPO : Set
LPO = (α : ℕ → Bool) → Found α ⊎ (Found α → ⊥)

hit : (ℕ → Bool) → ℕ → Bool
hit α zero    = false
hit α (suc n) = α n ∨ hit α n

two : L
two = suc (suc zero)

pickL : Bool → L
pickL true  = two
pickL false = suc zero

Kα : (ℕ → Bool) → L
Kα α = lim (λ m → pickL (hit α m))

gα : (ℕ → Bool) → ℕ → L
gα α zero    = Kα α
gα α (suc _) = two

hα : (α : ℕ → Bool) → Tr (Kα α) → L
hα α _ = lim (gα α)

evP : (b : Bool) → Ev (pickL b)
evP true  = tt
evP false = tt

evG : (α : ℕ → Bool) (n : ℕ) → Ev (gα α n)
evG α zero    = λ m → evP (hit α m)
evG α (suc n) = tt

εα : (α : ℕ → Bool) → Ev (Ωₗ (Kα α) (hα α))
εα α = (λ m → evP (hit α m)) , λ c → inl zero self , evG α

t₂ : (α : ℕ → Bool) → Pos (lim (gα α))
t₂ α = suc zero , inj₁ tt

Oα : Iface → (α : ℕ → Bool) → Tr (Kα α)
Oα I α = Iface.ψs I (Ωₗ (Kα α) (hα α)) (εα α) (B₀ _) (Kα α) (ink self) zero
           (up zero zero (Ω (t₂ α) (λ _ → zero)))
```

## 层号 2 的槽位与 α 的真值

```agda
isTwo : L → Bool
isTwo (suc (suc zero)) = true
isTwo _                = false

or-l : ∀ a b → a ≡ true → (a ∨ b) ≡ true
or-l true b refl = refl

pick2 : (b : Bool) → b ≡ true → pickL b ≡ two
pick2 true refl = refl

found→slot : ∀ α → Found α → Σ (Pos (Kα α)) λ q → at (Kα α) q ≡ two
found→slot α (n , e) = (suc n , inj₁ tt) , pick2 (hit α (suc n)) (or-l (α n) (hit α n) e)

two→true : (b : Bool) (s : Pos⁼ (pickL b)) → isTwo (at⁼ (pickL b) s) ≡ true → b ≡ true
two→true true  s                  e = refl
two→true false (inj₁ tt)          ()
two→true false (inj₂ (inj₁ tt))   ()
two→true false (inj₂ (inj₂ ()))   e

hit-found : ∀ α n → hit α n ≡ true → Found α
hit-found α zero    ()
hit-found α (suc n) e with α n in q
... | true  = n , q
... | false = hit-found α n e

obs : (α : ℕ → Bool) → Tr (Kα α) → Bool
obs α (Ω q _) = isTwo (at (Kα α) q)
obs α _       = false

obs→found : ∀ α (o : Tr (Kα α)) → obs α o ≡ true → Found α
obs→found α (Ω (m , s) _) e = hit-found α m (two→true (hit α m) s e)
obs→found α zero       ()
obs→found α (suc _)    ()
obs→found α (lim _)    ()
obs→found α (up _ _ _) ()
```

## 否定

```agda
t≢f : true ≡ false → ⊥
t≢f ()

not-kept : (I : Iface) → FullSem I → ∀ α → obs α (Oα I α) ≡ false → Found α → ⊥
not-kept I F α e fd with F (Kα α) (hα α) (εα α) (B₀ _) zero zero zero (t₂ α) (λ _ → zero) (found→slot α fd)
... | q , G′ , eq , at≡ = t≢f (trans (sym (cong isTwo at≡)) (trans (sym (cong (obs α) eq)) e))

fullSem→lpo : (I : Iface) → FullSem I → LPO
fullSem→lpo I F α = go (obs α (Oα I α)) refl
  where
  go : (b : Bool) → obs α (Oα I α) ≡ b → Found α ⊎ (Found α → ⊥)
  go true  e = inj₁ (obs→found α (Oα I α) e)
  go false e = inj₂ (not-kept I F α e)
```

`phi` 在探针上走默认 (槽位在孩子层第 1 项, 证据路径在第 0 项, `eqℕ 1 0` 是 `nothing`), 所以不满足这一加强 (α 恒真时有真值).

```agda
phi-folds : obs (λ _ → true) (Oα phi (λ _ → true)) ≡ false
phi-folds = refl

phi-not-fullSem : FullSem phi → ⊥
phi-not-fullSem F = not-kept phi F (λ _ → true) phi-folds (zero , refl)
```
