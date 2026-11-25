# 龙骨原型的验收: K(1), 行到项的归约, 步骤的陈述

> 验收文件 (读记号), 不进成品. 编译定理, 无前提: `k1 : K 1`, `kκ1 : Kκ 1` (塔 `tw` 与龙骨塔第 1 项 ≥ ψ₀(Ω_Ω) 的参照); 条件定理: 孩子族在迭代点上的下界 `Famᴵ n` 推出龙骨塔第 n+1 项的行 (`Chain.fam→Kκ`, 记号一侧共尾度与两条基本列等式作前提, n = 0, 1, 2 处是 `refl`: `fam→Kκ1`, `fam→Kκ2`, `fam→Kκ3`); 一切 n ≥ 2 的 K 推出部分和终点 ≥ EBO 参照 (`end-tw`, `end-κ`).
> 未证: `K 2`, `Kκ 2`, `Fam n`, `Famᴵ n`, 步骤 `FamStep n = Fam n → Fam (suc n)` (只是 `Set`). 不否定什么, 不涉及上界.
> `Fam n` 的读法 (ψ₀(Ω 的 n+1 重下标)) 来自记号项; 树侧 `Fc` 的读法是判断.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKDStep where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKDPath
open import OCF.Lean.YiKDFold
open import OCF.Lean.YiKDKeel
open import OCF.Lean.YiKDTw1 using (btbo-tw1ᴰ; btbo-kl1)
open import OCF.Lean.YiBRValue using (readRW)
open import OCF.Lean.YiEXRow using (row₂-btbo; down₀; down₁)
open import OCF.Lean.YiRefTw2 using (Rt; hω-inv; tree-≼; endpoint)
import OCF.Align.EboLeanDef as E
open E using (HC; h0; h1; hω; cof; cω; fsn; EBOψ; natT)
open import OCF.Align.EboLeanTree using (hc-tower; EBO-tree′)
open import OCF.Lean.YiMonoExit using (toL)
import OCF.Align.Level as O
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≼-suc)

T₀ : Set
T₀ = O.Ordᶜ O.zero
```

## 读回的三条小引理

```agda
plusᴿ : (a b : Tr zero) → readRW b ≼ readRW (a + b)
plusᴿ a zero      = z≼
plusᴿ a (suc b)   = s≼s (plusᴿ a b)
plusᴿ a (lim f _) = l≼ (λ n → ≼l n (plusᴿ a (f n)))

item≼ : (F : ℕ → Tr⁺ zero) (n : ℕ) → readRW (proj₁ (F n)) ≼ readRW (proj₁ (limc⁺ F))
item≼ F zero    = ≼l zero (≼-refl _)
item≼ F (suc n) = ≼l (suc n) (plusᴿ (cum (λ i → proj₁ (F i)) n) (proj₁ (F (suc n))))

◃s≼ : {x y : Tr zero} → zero ⊢ x ◃ y → O.suc (readRW x) ≼ readRW y
◃s≼ ◃s             = ≼-refl _
◃s≼ (◃l {a = a} n) = ≼l (suc n) (◃s≼ (a n))
◃s≼ (◃w {p = ()})
◃s≼ (◃u x () y e)
◃s≼ (◃c x () r)
◃s≼ (◃t d e)       = ≼-trans (◃s≼ d) (≼-trans (≼-suc (≼-refl _)) (◃s≼ e))

lim-inv : ∀ {t} (h : HC t) (w : cof t ≡ cω) (Y : T₀) → (∀ n → Rt (hω-inv h w n) ≼ Y) → Rt h ≼ Y
lim-inv (h0 e)   w Y q with trans (sym e) w
... | ()
lim-inv (h1 e _) w Y q with trans (sym e) w
... | ()
lim-inv (hω _ h) w Y q = l≼ q
```

## K(n) 与 K(1)

```agda
K Kκ : ℕ → Set
K  n = Rt (hc-tower (suc n)) ≼ readRW (twᶜ n)
Kκ n = Rt (hc-tower (suc n)) ≼ readRW (klᶜ n)

k1 : K 1
k1 = ≼-trans row₂-btbo btbo-tw1ᴰ

kκ1 : Kκ 1
kκ1 = ≼-trans row₂-btbo btbo-kl1
```

## 部分和终点: 一切项的 K 推出终点 ≥ EBO 的参照

```agda
end-κ : (∀ n → Kκ (suc (suc n))) → toL EBO-tree′ ≼ readRW klᴸ
end-κ r = endpoint (readRW klᴸ) go
  where
  r2 : Rt (hc-tower 2) ≼ readRW klᴸ
  r2 = ≼-trans kκ1 (item≼ klᶜ⁺ 1)
  go : ∀ k → Rt (hc-tower k) ≼ readRW klᴸ
  go zero                = ≼-trans down₀ (≼-trans down₁ r2)
  go (suc zero)          = ≼-trans down₁ r2
  go (suc (suc zero))    = r2
  go (suc (suc (suc n))) = ≼-trans (r n) (item≼ klᶜ⁺ (suc (suc n)))

end-tw : (∀ n → K (suc (suc n))) → toL EBO-tree′ ≼ readRW twᴸ
end-tw r = endpoint (readRW twᴸ) go
  where
  F : ℕ → Tr⁺ zero
  F n = ψ₀ (tw n) (Ok-tw n) (proj₁ (Ωt (tw n)))
  r2 : Rt (hc-tower 2) ≼ readRW twᴸ
  r2 = ≼-trans k1 (item≼ F 1)
  go : ∀ k → Rt (hc-tower k) ≼ readRW twᴸ
  go zero                = ≼-trans down₀ (≼-trans down₁ r2)
  go (suc zero)          = ≼-trans down₁ r2
  go (suc (suc zero))    = r2
  go (suc (suc (suc n))) = ≼-trans (r n) (item≼ F (suc (suc n)))
```

## 孩子族的下界推出一行

记号一侧: 第 n+2 行 ψ₀(Ω 塔) 的第 m 项是 `fκ n γₘ`, γ₀ = 1, γₘ₊₁ 是第 m 项 (下面作前提 `r0`, `rs`). 树一侧: `klᶜ (suc n)` 是 `Fc` 从零起迭代的部分和 (`kl-chain`). `Fam n`: 层号参数 z 的读回不低于 γ 的参照时, 孩子 z 的折叠不低于 `fκ n γ` 的参照.

```agda
Ωn : ℕ → E.T → E.T
Ωn zero    γ = γ
Ωn (suc n) γ = E.Ωt (Ωn n γ)

fκ : ℕ → E.T → E.T
fκ n γ = E.ψ [] (Ωn (suc n) γ) ∷ []

Fam : ℕ → Set
Fam n = ∀ {γ} (hγ : HC γ) (hf : HC (fκ n γ)) (z : Tr zero)
      → Rt hγ ≼ readRW z → Rt hf ≼ readRW (proj₁ (Fc (Ok-κ n) z))

FamStep : ℕ → Set
FamStep n = Fam n → Fam (suc n)

-- 链只用到 z 取迭代点的情形
Famᴵ : ℕ → Set
Famᴵ n = ∀ m {γ} (hγ : HC γ) (hf : HC (fκ n γ))
       → Rt hγ ≼ readRW (itκ n m) → Rt hf ≼ readRW (itκ n (suc m))

fam→ᴵ : ∀ n → Fam n → Famᴵ n
fam→ᴵ n F m hγ hf = F hγ hf (itκ n m)

h𝟏 : HC (natT 1)
h𝟏 = h1 refl (h0 refl)

module Chain (n : ℕ) (w : cof (EBOψ (suc (suc n))) ≡ cω)
             (r0 : fsn (EBOψ (suc (suc n))) 0 ≡ fκ n (natT 1))
             (rs : ∀ m → fsn (EBOψ (suc (suc n))) (suc m) ≡ fκ n (fsn (EBOψ (suc (suc n))) m))
             (fam : Famᴵ n) where

  hr : ∀ m → HC (fsn (EBOψ (suc (suc n))) m)
  hr = hω-inv (hc-tower (suc (suc n))) w

  row : ∀ m → Rt (hr m) ≼ readRW (itκ n (suc (suc m)))
  row zero    = ≼-trans (tree-≼ r0 (hr 0) (subst HC r0 (hr 0)))
    (fam 1 h𝟏 (subst HC r0 (hr 0)) (◃s≼ (proj₂ (Fc (Ok-κ n) zero))))
  row (suc m) = ≼-trans (tree-≼ (rs m) (hr (suc m)) (subst HC (rs m) (hr (suc m))))
    (fam (suc (suc m)) (hr m) (subst HC (rs m) (hr (suc m))) (row m))

  fam→Kκ : Kκ (suc n)
  fam→Kκ = lim-inv (hc-tower (suc (suc n))) w (readRW (klᶜ (suc n)))
    (λ m → ≼-trans (row m) (item≼ (λ i → Fc (Ok-κ n) (itκ n i)) (suc m)))

fam→Kκ1 : Famᴵ 0 → Kκ 1
fam→Kκ1 = Chain.fam→Kκ 0 refl refl (λ m → refl)

fam→Kκ2 : Famᴵ 1 → Kκ 2
fam→Kκ2 = Chain.fam→Kκ 1 refl refl (λ m → refl)

fam→Kκ3 : Famᴵ 2 → Kκ 3
fam→Kκ3 = Chain.fam→Kκ 2 refl refl (λ m → refl)
```

## 记号一侧的两条等式对一切 n 成立

Ω 塔第 k+1 项的共尾度是 Ω₁ (`cofT`), 它在 η 处的 Ω-基本列值是 η 外面套 k 重 Ω 下标 (`fsT-T`); 于是第 n+2 行的第 m 项是 `fκ n` 作用在 γ-链上 (`rowE`), 上面的前提 `w`, `r0`, `rs` 都可填出.

```agda
cofT : ∀ k → cof (E.ΩTower (suc k)) ≡ E.cΩ []
cofT zero    = refl
cofT (suc k) = cong (E.cofψ0 (E.ΩTower (suc k))) (cofT k)

fsT-T : ∀ k η → E.fsT (E.ΩTower (suc k)) η ≡ Ωn k η
fsT-T zero    η = refl
fsT-T (suc k) η = trans (cong (λ c → E.fsT0 (E.ΩTower (suc k)) c η) (cofT k)) (cong E.Ωt (fsT-T k η))

module Rows (n : ℕ) where
  b : E.T
  b = E.ΩTower (suc (suc n))

  wT : cof (EBOψ (suc (suc n))) ≡ cω
  wT = cong (E.cofA []) (cofT (suc n))

  rowC : ∀ m → fsn (EBOψ (suc (suc n))) m ≡ E.ψ [] (E.fsT b (E.γT b [] m)) ∷ []
  rowC m = cong (λ c → E.fsn₊ [] b c m) (cofT (suc n))

  rowE : ∀ m → fsn (EBOψ (suc (suc n))) m ≡ fκ n (E.γT b [] m)
  rowE m = trans (rowC m) (cong (λ x → E.ψ [] x ∷ []) (fsT-T (suc n) (E.γT b [] m)))

  rsT : ∀ m → fsn (EBOψ (suc (suc n))) (suc m) ≡ fκ n (fsn (EBOψ (suc (suc n))) m)
  rsT m = trans (rowE (suc m)) (cong (fκ n) (sym (rowC m)))

famᴵ→Kκ : ∀ n → Famᴵ n → Kκ (suc n)
famᴵ→Kκ n = Chain.fam→Kκ n (Rows.wT n) (Rows.rowE n 0) (Rows.rsT n)

end-fam : (∀ n → Famᴵ n) → toL EBO-tree′ ≼ readRW klᴸ
end-fam F = end-κ (λ n → famᴵ→Kκ (suc n) (F (suc n)))
```

## 第一个障碍的陈述 (未证)

`Fam 1` 在后继参数处: 层号 `θ 1 (suc z)` 是以 `θ 0 z` 为下标层的 Ω 形状 (`YiKDKeel.θ1-suc`), 记号一侧 ψ₀(Ω_{Ω_{γ+1}}) 的基本列走 ψ_γ 的链. 两边要对上, 需要层号 `θ 0 z` 上的树与记号项的关系, 本文没有.

```agda
Blk : Set
Blk = ∀ {γ} (hγ : HC γ) (hf : HC (fκ 1 (E.sucT γ))) (z : Tr zero)
    → Rt hγ ≼ readRW z → Rt hf ≼ readRW (proj₁ (Fc (Ok-κ 1) (suc z)))
```
