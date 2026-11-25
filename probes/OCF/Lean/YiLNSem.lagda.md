# 冻结接口的配对否定 (四): 按层号字面相等的 "能保留处都保留"

> 验收文件 (否定), 编译定理. 候选字段 `FullSem` (k 侧目标遇到孩子里的结点时, 目标有同层号的槽位就以这样一个槽位为根保留) 对 `Iface` 的任何实例推出 LPO (`fullSem→lpo`, 经 `Slot.full→dec`); `legI` 不满足它 (`legI-not-fullSem`).
> `YiPhiNegKSem` 的探针 (孩子层 `lim (gα α)`) 在合法块里没有路线 (`ksem-no-route`); 这里孩子层换成 Ω 结点层号 `Mα α`, 两支分别是 2 与 `Kα α`, 证据与路线都是闭项 (`εα`, `ρα`). 探针不在规范域, 读作 "谓词太宽"; 机制是同层号的槽位在目标里的存在是 α 上的存在命题.
> 不否定什么: 按路径与 `InB` 见证的保留 (`kall`, `legI` 满足). 重推 `YiPhiNegKSem.fullSem→lpo` 到合法块与冻结接口.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLNSem where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps using (Ωt; Ωt-nz)
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold using (Base; B₀)
open import OCF.Lean.YiLPIface using (Iface)
open import OCF.Lean.YiLPInst using (legI)
open import OCF.Lean.YiAbsObs using (Found; LPO; module Slot)
```

## 候选字段

对一切 `Ωₗ k h`, 目标 k (路径 `ink self`), 孩子 c 里的单个结点 `Ω t G`.

```agda
FullSem : Iface → Set
FullSem I = (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (β : Tr k)
  (nβ : k ⊢ zero ◃ β) (x : Tr (Ωₗ k h)) (c : Tr k) (t : Pos (h c)) (G : Br (h c) t → Tr (h c))
  (e : h c ⊢ zero ◃ Ω t G)
  → Σ (Pos k) (λ q → at k q ≡ at (h c) t)
  → Σ (Pos k) λ q → Σ (Br k q → Tr k) λ G′ →
      (Iface.ψs I (Ωₗ k h) ε ρ B k (ink self) β nβ (up x c (Ω t G) e) ≡ Ω q G′) × (at k q ≡ at (h c) t)
```

## 探针

`Kα α` 的第 m 项在 α 于 m 之前有真值时是 2, 否则是 1, 相邻项有路径 (`adjP`). 孩子层 `Mα α` 是第 0 层下标的 Ω 结点层号: 分支 0 是 2 (结点槽位 `t₂` 在这里), 其余分支是 `Kα α` (证据路径 `inb 1 self`).

```agda
hit : (ℕ → Bool) → ℕ → Bool
hit α zero    = false
hit α (suc n) = α n ∨ hit α n

one two : L
one = suc zero
two = suc (suc zero)

pickL : Bool → L
pickL true  = two
pickL false = one

adjP : (a b : Bool) → pickL b ≤ pickL (a ∨ b)
adjP true  true  = self
adjP true  false = ins self
adjP false b     = self

Kα : (ℕ → Bool) → L
Kα α = lim (λ m → pickL (hit α m))

hh : (ℕ → Bool) → Tr zero → L
hh α zero          = two
hh α (suc _)       = Kα α
hh α (lim _ _)     = Kα α
hh α (Ω () _)
hh α (up _ () _ _)

Mα : (ℕ → Bool) → L
Mα α = Ωₗ zero (hh α)

hα : (α : ℕ → Bool) → Tr (Kα α) → L
hα α _ = Mα α

evP : (b : Bool) → Ev (pickL b)
evP true  = tt
evP false = tt

rtP : (b : Bool) → Rt (pickL b)
rtP true  = tt
rtP false = tt

evK : (α : ℕ → Bool) → Ev (Kα α)
evK α m = evP (hit α m)

rtK : (α : ℕ → Bool) → Rt (Kα α)
rtK α = (λ m → rtP (hit α m)) , (λ m → adjP (α m) (hit α m))

evhh : (α : ℕ → Bool) (c : Tr zero) → (zero ≤ hh α c) × Ev (hh α c)
evhh α zero          = ins (ins self) , tt
evhh α (suc _)       = inl zero (ins self) , evK α
evhh α (lim _ _)     = inl zero (ins self) , evK α
evhh α (Ω () _)
evhh α (up _ () _ _)

rthh : (α : ℕ → Bool) (c : Tr zero) → Rt (hh α c)
rthh α zero          = tt
rthh α (suc _)       = rtK α
rthh α (lim _ _)     = rtK α
rthh α (Ω () _)
rthh α (up _ () _ _)

εα : (α : ℕ → Bool) → Ev (Ωₗ (Kα α) (hα α))
εα α = evK α , λ c → inb (suc zero) self , tt , evhh α

ρα : (α : ℕ → Bool) → Rt (Ωₗ (Kα α) (hα α))
ρα α = rtK α , λ c → tt , rthh α

t₂ : (α : ℕ → Bool) → Pos (Mα α)
t₂ α = inj₂ (zero , inj₁ tt)

Oα : Iface → (α : ℕ → Bool) → Tr (Kα α)
Oα I α = Iface.ψs I (Ωₗ (Kα α) (hα α)) (εα α) (ρα α) (B₀ _) (Kα α) (ink self) (Ωt (Kα α)) (Ωt-nz (Kα α))
           (up zero zero (Ω (t₂ α) (λ _ → zero)) ◃w)
```

`YiPhiNegKSem` 的孩子层 `lim (gα α)` 的第 0 项是 `Kα α`, 第 1 项是 2; 相邻项之间没有路径, 所以没有路线.

```agda
gα : (ℕ → Bool) → ℕ → L
gα α zero    = Kα α
gα α (suc _) = two

ksem-no-route : (α : ℕ → Bool) → Rt (lim (gα α)) → ⊥
ksem-no-route α ρ = no (proj₂ ρ zero)
  where
  no : Kα α ≤ two → ⊥
  no (ins (ins ()))
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
two→true true  s                e = refl
two→true false (inj₁ tt)        ()
two→true false (inj₂ (inj₁ tt)) ()
two→true false (inj₂ (inj₂ ())) e

hit-found : ∀ α n → hit α n ≡ true → Found α
hit-found α zero    ()
hit-found α (suc n) e with α n in q
... | true  = n , q
... | false = hit-found α n e

rootT : ∀ {ℓ} → Tr ℓ → Maybe (Pos ℓ)
rootT (Ω q _) = just q
rootT _       = nothing
```

## 否定

```agda
fullSem→lpo : (I : Iface) → FullSem I → LPO
fullSem→lpo I F α = Slot.full→dec (at (Kα α)) two rootT isTwo refl (Oα I α) full (found→slot α) hp
  where
  full : Slot.Full (at (Kα α)) two rootT (Oα I α)
  full has with F (Kα α) (hα α) (εα α) (ρα α) (B₀ _) (Ωt (Kα α)) (Ωt-nz (Kα α)) zero zero (t₂ α) (λ _ → zero) ◃w has
  ... | q , G′ , oq , l = q , cong rootT oq , l
  hp : (q : Pos (Kα α)) → isTwo (at (Kα α) q) ≡ true → Found α
  hp (m , s) e = hit-found α m (two→true (hit α m) s e)
```

`legI` 在探针上走回退: 目标在 `Mα α` 的分支 1 里, 结点在分支 0 里 (Ω 结点层号上异支, 输出是 ℕ 极限).

```agda
αT : ℕ → Bool
αT _ = true

legI-not-fullSem : FullSem legI → ⊥
legI-not-fullSem F = no (F (Kα αT) (hα αT) (εα αT) (ρα αT) (B₀ _) (Ωt (Kα αT)) (Ωt-nz (Kα αT)) zero zero (t₂ αT)
                           (λ _ → zero) ◃w (found→slot αT (zero , refl)))
  where
  no : (Σ (Pos (Kα αT)) λ q → Σ (Br (Kα αT) q → Tr (Kα αT)) λ G′ → (Oα legI αT ≡ Ω q G′) × (at (Kα αT) q ≡ two)) → ⊥
  no (q , G′ , () , l)
```
