# 龙骨原型: 一步递归的塔

> 判决: 候选原型 (层号与闭项), 不替换主线. 龙骨塔 `κ`: 第 0 项是 `tw 1`, 下一项是 `rb ℓ = ℓ ⊕ ↑ ℓ (Ωt ℓ)` (本层 Ω 树读回成偏移, 加在本层上; `κ-step`, `refl`); 证据对一切层号一步成立 (`Ok-rb`), 所以 `Ok-κ`, `Ok-Λκ` 是闭项, 无前提.
> 编译定理 (对层号一般, `refl`): 下标层为第 0 层的 Ω 形状层号上, 沿路径 `zp` 的闭项是 "孩子层 Ω 树的第 0 层折叠" `Fc` 从零起迭代的部分和极限, 回灌与行是同一个值 (`keel-chain`); `rb` 把孩子族 h 送到 `ℓ ⊕ (zero ⊕ ↑ (Ωt (h z)))` (`rb-fam`), 地板是上一项 (`rb-flr`).
> 不否定什么; 不含值的定理. 折叠在 `YiKDFold`, 验收在 `YiKDStep`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKDKeel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKDPath
open import OCF.Lean.YiKDFold
open import OCF.Lean.YiCertFold using (B₀)
```

## 一步: 本层 Ω 树的读回加在本层上

`rb ℓ` 是 "以 ℓ 为下标层的 Ω 形状层号" `nx ℓ` 在孩子 `Ωt ℓ` 处的那一层; `tw (suc n)` 就是 `nx (tw n)`.

```agda
rb : L → L
rb ℓ = ℓ ⊕ ↑ ℓ (proj₁ (Ωt ℓ))

Ok-rb : (ℓ : L) → Ok ℓ → Ok (rb ℓ)
Ok-rb ℓ o = Ok⊕ ℓ (↑ ℓ (proj₁ (Ωt ℓ))) o (OkO↑ ℓ ℓ o self (proj₁ (Ωt ℓ)))

nx : L → L
nx ℓ = nd (sΩ ℓ) λ c → ℓ ⊕ ↑ ℓ c

_ : (n : ℕ) → tw (suc n) ≡ nx (tw n)
_ = λ n → refl

rb≤nx : (ℓ : L) → rb ℓ ≤ nx ℓ
rb≤nx ℓ = inc (proj₁ (Ωt ℓ)) self

≤rb : (ℓ : L) → ℓ ≤ rb ℓ
≤rb ℓ = lift ℓ (↑ ℓ (proj₁ (Ωt ℓ)))
```

Ω 形状层号上, `rb` 保住形状与下标层, 孩子族逐点换成 "前缀 ℓ, 再接孩子层 Ω 树的读回"; 地板是 ℓ 本身, 下标层到地板的路径经下标层侧.

```agda
rb-fam : (k : L) (h : Tr k → L)
       → rb (nd (sΩ k) h) ≡ nd (sΩ k) λ z → nd (sΩ k) h ⊕ (zero ⊕ ↑ (h z) (proj₁ (Ωt (h z))))
rb-fam k h = refl

rb-flr : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) → flr (Ok-rb (nd (sΩ k) h) o) ≡ nd (sΩ k) h
rb-flr k h o = refl

rb-kfl : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) → kfl (Ok-rb (nd (sΩ k) h) o) ≡ ink self ∙ self
rb-kfl k h o = refl
```

## 塔与 Λ

塔按孩子族写: `κ n` 是下标层为第 0 层的 Ω 形状层号, 孩子族 `θ n`; 下一项就是 `rb` (`κ-step`). `kl` 在前面补一个第 0 层, 使 `kl 1 = tw 1`.

```agda
θ : ℕ → Tr zero → L
κ : ℕ → L
κ n = nd (sΩ zero) (θ n)
θ zero    z = zero ⊕ ↑ zero z
θ (suc n) z = κ n ⊕ (zero ⊕ ↑ (θ n z) (proj₁ (Ωt (θ n z))))

_ : κ 0 ≡ tw 1
_ = refl

κ-step : (n : ℕ) → κ (suc n) ≡ rb (κ n)
κ-step n = refl

Ok-κ : (n : ℕ) → Ok (κ n)
Ok-κ zero    = Ok-tw 1
Ok-κ (suc n) = Ok-rb (κ n) (Ok-κ n)

kl : ℕ → L
kl zero    = zero
kl (suc n) = κ n

Ok-kl : (n : ℕ) → Ok (kl n)
Ok-kl zero    = tt
Ok-kl (suc n) = Ok-κ n

kl≤ : (n : ℕ) → kl n ≤ kl (suc n)
kl≤ zero    = z≤ (tw 1)
kl≤ (suc n) = ≤rb (κ n)

Λκ : L
Λκ = nd sL kl

Ok-Λκ : Ok Λκ
Ok-Λκ = kl≤ , Ok-kl
```

## 闭项

路径 `zp`: 到第 0 层, Ω 形状上经下标层侧. 闭项 `ψ₀ᵏ` 取默认底, 路径 `zp`, 起点 `Ωt zero`. 终点两种: `EBOκ` 是 Λκ 上 Ω 树的折叠; `klᴸ` (与塔 `tw` 的 `twᴸ`) 是各项的部分和极限.

```agda
zp : (ℓ : L) → zero ≤ ℓ
zp zero          = self
zp (nd sS h)     = inu λ _ → zp (h tt)
zp (nd sL g)     = inu λ n → zp (g n)
zp (nd (sΩ k) h) = ink (zp k)

ψ₀ᵏ : (ℓ : L) → Ok ℓ → Tr ℓ → Tr⁺ zero
ψ₀ᵏ ℓ o = ψ ℓ o (B₀ ℓ) zero (zp ℓ) (Ωt zero)

klᶜ⁺ : ℕ → Tr⁺ zero
klᶜ⁺ n = ψ₀ᵏ (kl n) (Ok-kl n) (proj₁ (Ωt (kl n)))

klᶜ : ℕ → Tr zero
klᶜ n = proj₁ (klᶜ⁺ n)

EBOκ : Tr zero
EBOκ = proj₁ (ψ₀ᵏ Λκ Ok-Λκ (proj₁ (Ωt Λκ)))

klᴸ : Tr zero
klᴸ = proj₁ (limc⁺ klᶜ⁺)

twᴸ : Tr zero
twᴸ = proj₁ (limc⁺ λ n → ψ₀ (tw n) (Ok-tw n) (proj₁ (Ωt (tw n))))
```

## 一步的形状: 闭项是孩子层折叠的迭代

`Fc o z`: 孩子 z 那一层的 Ω 树折到第 0 层, 路径是 "到地板, 再沿 z 的证书上去". 下标层为第 0 层时, 结点朝第 0 层不保留, 链的回灌与行都是 `Fc`.

```agda
Fc : ∀ {h : Tr zero → L} (o : Ok (nd (sΩ zero) h)) → Tr zero → Tr⁺ zero
Fc {h} o z = ψ (h z) (proj₂ o z) (λ i u → Ωt i) zero (self ∙ kh o z) (Ωt zero) (proj₁ (Ωt (h z)))

keel-chain : (h : Tr zero → L) (o : Ok (nd (sΩ zero) h))
           → ψ₀ᵏ (nd (sΩ zero) h) o (proj₁ (Ωt (nd (sΩ zero) h)))
           ≡ limc⁺ (λ m → Fc o (iter (λ z → proj₁ (Fc o z)) zero m))
keel-chain h o = refl

itκ : (n : ℕ) → ℕ → Tr zero
itκ n = iter (λ z → proj₁ (Fc (Ok-κ n) z)) zero

kl-chain : (n : ℕ) → klᶜ⁺ (suc n) ≡ limc⁺ (λ m → Fc (Ok-κ n) (itκ n m))
kl-chain n = refl
```

后继孩子处的层号 (`refl`): 下标层是层号 `θ 0 z` 的 Ω 形状, 孩子是后继层号. 它的 Ω 树朝第 0 层的链在 `Tr (θ 0 z)` 里回灌 (验收的第一个障碍在这里, 见 `YiKDStep.Blk`).

```agda
θ1-suc : (z : Tr zero)
       → θ 1 (suc z) ≡ nd (sΩ (θ 0 z)) (λ c → nd sS (λ _ → κ 0 ⊕ (zero ⊕ (zero ⊕ ↑ (θ 0 z) c))))
θ1-suc z = refl
```
