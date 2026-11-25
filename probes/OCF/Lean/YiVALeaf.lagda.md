# 塔第 1 项的叶子朝第 1 层折: 保留下来的每一支是 "起点加可数尾巴"

> 判决: 审核用的判定件 (编译定理, 都是 `refl`; 不读记号). 最小表下, `tw 1` 上经非零指定孩子的折叠遇到非零孩子的嵌入时, 输出逐字是 `折 x ⊞ ψ₀ᶻ y` (`fall`, 对一切证据, 底, 目标, 路径, 起点); 含孩子相同, 目标就是该孩子层号的情形 (`fall-diag`).
> 于是 `Ωt (tw 1)` 朝 `h₁ 1` (经孩子 2) 的折叠是下标槽位上保留的结点 (`leaf-node`), 它在每个非零 z 处的一支逐字是 `β ⊞ ψ₀ᶻ (Ωt (h₁ z))` (`leaf-branch`).
> 不否定什么: 只给出输出的形状, 没有值的上界, 不判定同步对象的值. 机制的另两件见 `YiTFTw1.kp-leaf`, `YiKTSlot`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVALeaf where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Maybe using (nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow using (ψ; h₁)
open import OCF.Lean.YiMTTab using (rbᶻ; ψ₀ᶻ; tbᶻ)
```

## 退路行

`NZ c`: c 的顶构造子不是 `zero`. 表 `tbᶻ` 只看两个孩子的顶构造子, 所以对变量 c, c′ 分四种情形都是 `refl`.

```agda
data NZ : Tr zero → Set where
  nzs : (c : Tr zero) → NZ (suc c)
  nzl : (f : ℕ → Tr zero) (a : (n : ℕ) → zero ⊢ f n ◃ f (suc n)) → NZ (lim f a)

ent : ∀ {c c′} → NZ c → NZ c′ → tbᶻ zero h₁ c c′ ≡ nothing
ent (nzs _)   (nzs _)   = refl
ent (nzs _)   (nzl _ _) = refl
ent (nzl _ _) (nzs _)   = refl
ent (nzl _ _) (nzl _ _) = refl

fall : ∀ {c c′} → NZ c → NZ c′ → (o : Ok (tw 1)) (B : Base (tw 1)) (j : L) (v : j ≤ h₁ c′) (β : Tr⁺ j)
  (x : Tr (tw 1)) (y : Tr (h₁ c)) (e : h₁ c ⊢ zero ◃ y)
  → ψ (tw 1) o (rbᶻ (tw 1)) B j (inc c′ v) β (up x c y e)
  ≡ ψ (tw 1) o (rbᶻ (tw 1)) B j (inc c′ v) β x ⊞ ψ₀ᶻ (h₁ c) (proj₂ o c) y
fall (nzs _)   (nzs _)   o B j v β x y e = refl
fall (nzs _)   (nzl _ _) o B j v β x y e = refl
fall (nzl _ _) (nzs _)   o B j v β x y e = refl
fall (nzl _ _) (nzl _ _) o B j v β x y e = refl
```

孩子相同, 目标就是该孩子的层号, 路径在孩子里是 `self`: y 已是目标层的树, 输出里只留下它折到第 0 层的值.

```agda
fall-diag : ∀ {c} → NZ c → (o : Ok (tw 1)) (B : Base (tw 1)) (β : Tr⁺ (h₁ c))
  (y : Tr (h₁ c)) (e : h₁ c ⊢ zero ◃ y)
  → ψ (tw 1) o (rbᶻ (tw 1)) B (h₁ c) (inc c self) β (up zero c y e)
  ≡ β ⊞ ψ₀ᶻ (h₁ c) (proj₂ o c) y
fall-diag nz o B β y e = fall nz nz o B _ self β zero y e
```

## 叶子 `Ωt (tw 1)` 朝第 1 层

目标 `h₁ 1`, 路径经孩子 2 (同步对象孩子 `a₁ 2` 的层号证据给出的那条, 见 `YiKTSlot`). 下标槽位被保留到目标层唯一的槽位 `q₁` 上.

```agda
one two : Tr zero
one = suc zero
two = suc one

w₁ : h₁ one ≤ tw 1
w₁ = inc two (inc tt self)

q₁ : Pos (h₁ one)
q₁ = inj₂ (tt , inj₁ tt)

leaf-node : (B : Base (tw 1)) (β : Tr⁺ (h₁ one))
  → ψ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) B (h₁ one) w₁ β (proj₁ (Ωt (tw 1)))
  ≡ Ω⁺ q₁ (λ z → ψ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) B (h₁ one) w₁ β (proj₁ (upz {s = sΩ zero} {h = h₁} z (Ωt (h₁ z)))))
leaf-node B β = refl

leaf-branch : ∀ {z} → NZ z → (B : Base (tw 1)) (β : Tr⁺ (h₁ one))
  → ψ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) B (h₁ one) w₁ β (proj₁ (upz {s = sΩ zero} {h = h₁} z (Ωt (h₁ z))))
  ≡ β ⊞ ψ₀ᶻ (h₁ z) (proj₂ (Ok-tw 1) z) (proj₁ (Ωt (h₁ z)))
leaf-branch nz B β = fall nz (nzs one) (Ok-tw 1) B (h₁ one) (inc tt self) β zero _ _
```
