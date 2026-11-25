# 候选原型的有限测试: 塔第 1 项前缀下的槽位与一行退路

> 有限测试, 不读记号; 不改树、折叠、合法性. 证据用 `Ok-tw 2` 在同步对象处的孩子 `oᵈ` (`YiKTSlot` 用的 `oᴱ` 见 `YiDXValue`). (A) 下 `p*` 由走链变保留, `p₀` 不变; d = 2 时下标层为第 1 层的槽位仍走链, 其中第 0 层的槽位保留.
> 同步对象孩子 `a₁ 2` 朝 `h₁ 1` 的一次折叠里, `p*` 型结点在原折叠下是 ℕ 极限, 在 (A) 下是 Ω 结点; `YiTFTw1` 那一行只有 (A)+(B) 让输出的第一项成为保留的 Ω 结点.
> 不给出值的定理. 同名对象是 `YiSYReduce`、`YiKTSlot`、`YiTFTw1` 里的逐字副本; (C) 的对应 (`at-q′`, `br-q′`) 只是检查, 本文件不实现 (C).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDXTest where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; Keep; kp; B₀)
open import OCF.Lean.YiTBRow using (Rb)
import OCF.Lean.YiTBRow as TB
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiDXFold
```

## 对象

```agda
h₁ : Tr zero → L
h₁ c = zero ⊕ ↑ zero c

a₁ : Tr zero → L
a₁ c = tw 1 ⊕ ↑ (tw 1) (proj₁ (upz {s = sΩ zero} {h = h₁} c (Ωt (h₁ c))))

hh : (d : Tr zero) → Tr (h₁ d) → L
hh d z = tw 1 ⊕ (zero ⊕ nd sS (λ _ → zero ⊕ ↑ (h₁ d) z))

oᵈ : Ok (nd (sΩ zero) a₁)
oᵈ = proj₂ (Ok-tw 2) (proj₁ (Ωt (tw 1)))

n1 n2 n3 : Tr zero
n1 = suc zero
n2 = suc n1
n3 = suc n2

a₁-2 : a₁ n2 ≡ nd (sΩ (h₁ n1)) (hh n1)
a₁-2 = refl

z* : Tr (h₁ n1)
z* = proj₁ (Ωt (h₁ n1))

p* p₀ : Pos (a₁ n2)
p* = inj₂ (z* , inj₂ (inj₂ (tt , inj₂ (inj₁ (inj₁ tt)))))
p₀ = inj₂ (z* , inj₂ (inj₂ (tt , inj₂ (inj₂ (zero , inj₂ (inj₂ (tt , inj₂ (inj₁ (inj₁ tt)))))))))

z₂ : Tr (h₁ n2)
z₂ = proj₁ (Ωt (h₁ n2))

p₂ p₂′ : Pos (a₁ n3)
p₂  = inj₂ (z₂ , inj₂ (inj₂ (tt , inj₂ (inj₁ (inj₁ tt)))))
p₂′ = inj₂ (z₂ , inj₂ (inj₂ (tt , inj₂ (inj₁ (inj₂ (inj₂ (tt , inj₁ tt)))))))

IsNothing IsJust : ∀ {j X x₀} → Keep j X x₀ → Set
IsNothing nothing  = ⊤
IsNothing (just _) = ⊥
IsJust nothing  = ⊥
IsJust (just _) = ⊤
```

## 保留判定

`p*`: 下标层为第 0 层的 Ω 形状层号的下标槽位; `p₀`: 前缀 `tw 1` 叶子的下标槽位. d = 2 时 `p₂` 的层号是 `h₁ 1` (低于目标 `h₁ 2`, 非零), `p₂′` 是它里面第 0 层的槽位.

```agda
kp*  : IsNothing (kp  (a₁ n2) (proj₂ oᵈ n2) p* (ink self))
kp*  = tt
kp*ᴬ : IsJust    (kpᴬ (a₁ n2) (proj₂ oᵈ n2) p* (ink self))
kp*ᴬ = tt
kp₀  : IsJust    (kp  (a₁ n2) (proj₂ oᵈ n2) p₀ (ink self))
kp₀  = tt
kp₀ᴬ : kpᴬ (a₁ n2) (proj₂ oᵈ n2) p₀ (ink self) ≡ kp (a₁ n2) (proj₂ oᵈ n2) p₀ (ink self)
kp₀ᴬ = refl

at-p₂ : at (a₁ n3) p₂ ≡ h₁ n1
at-p₂ = refl

kp₂ᴬ  : IsNothing (kpᴬ (a₁ n3) (proj₂ oᵈ n3) p₂ (ink self))
kp₂ᴬ  = tt
kp₂′  : IsNothing (kp  (a₁ n3) (proj₂ oᵈ n3) p₂′ (ink self))
kp₂′  = tt
kp₂′ᴬ : IsJust    (kpᴬ (a₁ n3) (proj₂ oᵈ n3) p₂′ (ink self))
kp₂′ᴬ = tt
```

`p₂` 的层号与分支类型就是目标层 `h₁ 2` 自己的槽位 `q′` 的 (读回 `↑` 把 `z₂` 在 `q′` 上的结点变成下标为 `at (h₁ 2) q′` 的 Ω 形状层号); 目标层在 `q′` 上保留. 这是 (C) "按读回的来源委托给下标层" 要用的对应, 本文件不实现 (C).

```agda
q′ : Pos (h₁ n2)
q′ = inj₂ (tt , inj₁ tt)

at-q′ : at (a₁ n3) p₂ ≡ at (h₁ n2) q′
at-q′ = refl

br-q′ : Br (a₁ n3) p₂ ≡ Br (h₁ n2) q′
br-q′ = refl

kp-q′ : IsJust (kp (h₁ n2) (proj₂ (Ok-tw 1) n2) q′ self)
kp-q′ = tt
```

最小表在塔第 1 项孩子 (2, 2) 上没有条目 (`YiTFTw1` 的退路), 对角上只有 (0, 0).

```agda
tb-22 : proj₁ (rbᶻ (tw 1)) n2 n2 ≡ nothing
tb-22 = refl
```

## 输出的形状

`el t n`: ℕ 极限的第 n 项 (别的构造子原样). 只算到弱头部.

```agda
el : ∀ {S} → T S → ℕ → T S
el (lim f _) n = f n
el t         n = t

HeadΩ HeadLim : ∀ {S} → T S → Set
HeadΩ (Ω _ _) = ⊤
HeadΩ _       = ⊥
HeadLim (lim _ _) = ⊤
HeadLim _         = ⊥

FirstLimΩ : ∀ {S} → T S → Set
FirstLimΩ {S} (Ω p g) = HeadLim (g (b₀ S p))
FirstLimΩ _           = ⊥
```

同步对象孩子 `a₁ 2` 的顶槽位回灌 (朝 `h₁ 1`, 路径 `ink self`, 标准底) 一棵分支 `g* z*`. 输出是链的部分和; 第 1 个部分和里第 1 个链点的折叠, 起头就是 `p*` 型结点.

```agda
g* : Tr (h₁ n1) → Tr (a₁ n2)
g* z = proj₁ (upz {s = sΩ (h₁ n1)} {h = hh n1} z (Ωt (hh n1 z)))

module Sync (ψˣ : (ℓ : L) → Ok ℓ → Rb ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j) where
  outS : Tr (h₁ n1)
  outS = proj₁ (ψˣ (a₁ n2) (proj₂ oᵈ n2) (rbᶻ (a₁ n2)) (B₀ (a₁ n2)) (h₁ n1) (ink self) (Ωt (h₁ n1)) (g* z*))

  probe : Tr (h₁ n1)
  probe = el (el (el outS 1) 0) 0

module S₀ = Sync TB.ψ
module Sᴬ = Sync FA.ψ

sync₀ : HeadLim S₀.probe
sync₀ = tt

syncᴬ : HeadΩ Sᴬ.probe
syncᴬ = tt
```

`YiTFTw1` 的那一处: 塔第 1 项孩子 2 里第 1 层的槽位 `p₁`, 分支是孩子 2 的直接嵌入 (表在 (2, 2) 缺项). 原折叠与 (A) 的输出第一项是 ℕ 极限 (Ω₁ 树加可数尾巴); (B) 下第一项是链 (ℕ 极限的部分和); (A)+(B) 下第一项是第 1 层上保留的 Ω 结点, 第一分支是 `next⁺` 的 ℕ 极限 (与基底 `Ωt` 不同, 后者的第一分支是嵌入).

```agda
c₂ : Tr zero
c₂ = suc (suc zero)

p₁ : Pos (tw 1)
p₁ = inj₂ (c₂ , inj₂ (inj₂ (tt , inj₁ tt)))

g₁ : Tr (h₁ n1) → Tr (tw 1)
g₁ c = up zero c₂ (up zero tt (suc c) (z◃ c ◃s)) (◃u zero tt (suc c) (z◃ c ◃s))

module Tw1 (ψˣ : (ℓ : L) → Ok ℓ → Rb ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j) where
  out₁ : Tr (at (tw 1) p₁)
  out₁ = proj₁ (ψˣ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) (B₀ (tw 1)) (at (tw 1) p₁) (posW (tw 1) p₁)
                  (B₀ (tw 1) (at (tw 1) p₁) (posW (tw 1) p₁)) (g₁ z*))

module T₀  = Tw1 TB.ψ
module Tᴬ  = Tw1 FA.ψ
module Tᴮ  = Tw1 FB.ψ
module Tᴬᴮ = Tw1 FAB.ψ

tw1₀ : HeadLim (el T₀.out₁ 0)
tw1₀ = tt

tw1ᴬ : HeadLim (el Tᴬ.out₁ 0)
tw1ᴬ = tt

tw1ᴮ : HeadLim (el Tᴮ.out₁ 0)
tw1ᴮ = tt

tw1ᴬᴮ : FirstLimΩ (el Tᴬᴮ.out₁ 0)
tw1ᴬᴮ = tt
```
