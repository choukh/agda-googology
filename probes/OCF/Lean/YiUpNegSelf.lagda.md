# 上折的配对否定: 自身行律与上折合法性的量化域

> 验收文件 (否定). 判决: 编译定理. 自身行律 `self-up` 对零偏移也陈述: 任一接口实例, 只要 x 对自身以零偏移折成零, 合法输入 `up x c (suc zero)` 的自身行输出就是常值极限, 不合法 (`self-zero`; `upI` 上 x = zero 即满足, `self-zero-up`); 旧自身行 (`YiPhiFold`) 在同一输入上合法 (`phi-legal`).
> 零偏移不是 "合法且非零" (`zero-not-LN`), 接口的 `press` 本来就要求偏移合法非零, 规范底都非零; 所以这是律在规范域外说话, 读作 "谓词太宽", 不读作数学障碍. 上折本身同理: 零底的后继给出不合法输出 (`up-zero-illegal`), 说明 `Up-LN` 的 "底非零" 前提不可去掉; 底取 Ωt 时前提满足 (`up-LN-inst`). `Up-mono` 无前提.
> 自身行律不读证据与底 (`self-indep`): 自身行的输出只由 x 的自身折叠与孩子 y 决定. 不否定什么: 不否定接口, 不否定 `upI`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUpNegSelf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (Ωt)
open import OCF.Lean.YiFreshLegal using (_⊢_◃_; ◃s; Leg; LN; Ωt-leg; Ωt-nz)
open import OCF.Lean.YiPhiBlock
import OCF.Lean.YiPhiFold as P
open import OCF.Lean.YiPhiNegB using (no-◃zero)
open import OCF.Lean.YiUpBlock using (Dn; stop; down; Up; Upc)
open import OCF.Lean.YiUpIface using (Iface)
import OCF.Lean.YiUpFold as F
open import OCF.Lean.YiUpLegal using (Up-mono; Up-LN)
open import OCF.Lean.YiUpCheck using (upI)
```

## 零底的上折

`Up j d zero (suc zero)` 是 `next zero`, 即各项都是零的极限.

```agda
up-zero-illegal : ∀ {ℓ} (j : L) (d : Dn ℓ j) → Leg ℓ (Up j d zero (suc zero)) → ⊥
up-zero-illegal j d (_ , adj) = no-◃zero (adj zero)

zero-not-LN : ∀ {j} → LN j zero → ⊥
zero-not-LN (_ , z) = no-◃zero z
```

## 自身行律在零偏移上

孩子取 `suc zero`. 输入合法 (`in-leg`).

```agda
sucCh : (ℓ : L) (c : Ch ℓ) → ChT ℓ c
sucCh (suc a)  c = suc zero
sucCh (lim g)  n = suc zero
sucCh (Ωₗ k h) c = suc zero

in-leg : (ℓ : L) (c : Ch ℓ) (x : Tr ℓ) → Leg ℓ x → Leg ℓ (up x c (sucCh ℓ c))
in-leg (suc a)  c x hx = hx , tt , ◃s
in-leg (lim g)  n x hx = hx , tt , ◃s
in-leg (Ωₗ k h) c x hx = hx , tt , ◃s

upc-zero-illegal : (ℓ : L) (c : Ch ℓ) → Leg ℓ (Upc ℓ c zero (sucCh ℓ c)) → ⊥
upc-zero-illegal (suc a)  c = up-zero-illegal a (down stop c)
upc-zero-illegal (lim g)  n = up-zero-illegal (g n) (down stop n)
upc-zero-illegal (Ωₗ k h) c = up-zero-illegal (h c) (down stop c)

self-zero : (I : Iface) (ℓ : L) (ε : Ev ℓ) (B : Base ℓ) (x : Tr ℓ) (c : Ch ℓ)
  → Iface.ψs I ℓ ε B ℓ self zero x ≡ zero
  → Leg ℓ (Iface.ψs I ℓ ε B ℓ self zero (up x c (sucCh ℓ c))) → ⊥
self-zero I ℓ ε B x c e h =
  upc-zero-illegal ℓ c
    (subst (Leg ℓ) (trans (Iface.self-up I ℓ ε B zero x c (sucCh ℓ c)) (cong (λ b → Upc ℓ c b (sucCh ℓ c)) e)) h)
```

前提的实例: `upI`, x = zero (零偏移下零的折叠是零). 对照: 旧自身行把孩子原样留下, 输出合法.

```agda
self-zero-up : (ℓ : L) (ε : Ev ℓ) (B : Base ℓ) (c : Ch ℓ)
  → Leg ℓ (up zero c (sucCh ℓ c)) × (Leg ℓ (F.ψs ℓ ε B ℓ self zero (up zero c (sucCh ℓ c))) → ⊥)
self-zero-up ℓ ε B c = in-leg ℓ c zero tt , self-zero upI ℓ ε B zero c refl

phi-legal : (ℓ : L) (ε : Ev ℓ) (B : Base ℓ) (c : Ch ℓ)
  → Leg ℓ (P.ψs ℓ ε B ℓ self zero (up zero c (sucCh ℓ c)))
phi-legal ℓ ε B c = in-leg ℓ c zero tt
```

## 自身行律不读证据与底

```agda
self-indep : (I : Iface) (ℓ : L) (ε ε′ : Ev ℓ) (B B′ : Base ℓ) (β β′ : Tr ℓ) (x x′ : Tr ℓ) (c : Ch ℓ) (y : ChT ℓ c)
  → Iface.ψs I ℓ ε B ℓ self β x ≡ Iface.ψs I ℓ ε′ B′ ℓ self β′ x′
  → Iface.ψs I ℓ ε B ℓ self β (up x c y) ≡ Iface.ψs I ℓ ε′ B′ ℓ self β′ (up x′ c y)
self-indep I ℓ ε ε′ B B′ β β′ x x′ c y e =
  trans (Iface.self-up I ℓ ε B β x c y)
        (trans (cong (λ b → Upc ℓ c b y) e) (sym (Iface.self-up I ℓ ε′ B′ β′ x′ c y)))
```

## `Up-mono`, `Up-LN` 的前提

`Up-mono` 只有序的前提 (例 `◃s`); `Up-LN` 的底取 Ωt ℓ 即满足.

```agda
up-mono-inst : ∀ {ℓ} (j : L) (d : Dn ℓ j) (b : Tr ℓ) → ℓ ⊢ Up j d b zero ◃ Up j d b (suc zero)
up-mono-inst j d b = Up-mono j d b ◃s

up-LN-inst : ∀ {ℓ} (j : L) (d : Dn ℓ j) (y : Tr j) → Leg j y → LN ℓ (Up j d (Ωt ℓ) y)
up-LN-inst {ℓ} j d y hy = Up-LN j d (Ωt ℓ) (Ωt-leg ℓ , Ωt-nz ℓ) y hy
```
