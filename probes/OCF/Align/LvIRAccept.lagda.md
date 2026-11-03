# 归纳-递归块: 验收 (有限检查)

> **验收节.** 记号只在本文件. 结论写在 [LvIR](LvIR.lagda.md). 全部是**有限检查** (宽度、深度、路径都是有限的), 不是定理.
>
> **块里的闭项.** 块只定义了 $x_0,x_1$ (`b0`, `b1`), 对 `EBOψ 0`, `EBOψ 1` 无偏离. 对照 `c0`, `c1`: 换一个序数比较确实给出偏离路径, 所以比较器不是空的. $x_2,x_3,x_4$ 在块里**没有定义** (`¬Good-L₂`), 所以块上没有它们的检查, 也就谈不上值对不对.
>
> **裸层号上的路径, 判决取 `ver`** (这些不是块的闭项, 只是确认 [LvIRReach](LvIRReach.lagda.md) 走到的确实是记号的那一站): $x_2,x_3,x_4$ 在宽 3 深 5–6 内无偏离 (`e2`, `e3`, `e4`); 路径 `hard-tm` 上记号的项正是 $\psi_0(\psi_{\Omega}(\psi_{\omega+1}(\Omega_\Omega)))$ (`refl`, 这是这一节最强的证据), 树与项在宽 3 深 4 内无偏离 (`hard-ok`). **这个比较器在这个深度内分不开 $\omega+1$ 与 $\omega+2$ (`hard-blind`, 深度加到 6 也一样, 临时文件), 所以 `hard-ok` 是弱证据**; 对照 `hard-ctrl`: 换成 1 有偏离. 通过 $W$ 的路径: 记号走到 `W` (`W-tm`), 这条路径的前四步正是到 $\psi_0(\Omega_{\Omega_2})$ (`W-head`), 树与项无偏离到宽 3 深 4 (`W-ok`), 对照 `W-ctrl`. **`ver` 不声称正确**, 这里只说它在这些点上碰巧对.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvIRAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_; take)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.InaccTreeBase using (ver; Ordᴸ; zero)
open import OCF.Align.EBOTopRaw hiding (natT; cof)
import OCF.Align.EBO as E
open E using (fsn; cof; c0; c1; cω; pred) renaming (T to Tm; ψ to ψᵗ)
open import OCF.Align.InaccTreeAccept using (diff; walkB)
open import OCF.Align.Uniform5Wall using (p₁; p₂; W)
open import OCF.Align.EBOTopStage using (O₀)
open import OCF.Align.LvIRBlock using (x₀; x₁)
```

## §1 块里的闭项

```agda
diff₀  : ℕ → ℕ → Tm → O₀ → Maybe (List ℕ)
diffs₀ : ℕ → ℕ → ℕ → Tm → (ℕ → O₀) → Maybe (List ℕ)
diff₀ zero w t x = nothing
diff₀ (suc d) w t x with cof t | x
... | c0 | O₀.zero  = nothing
... | c1 | O₀.suc a = diff₀ d w (pred t) a
... | cω | O₀.lim f = diffs₀ w d w t f
... | _  | _        = just []
diffs₀ zero d w t f = nothing
diffs₀ (suc n) d w t f with diff₀ d w (fsn t n) (f n)
... | just p  = just (n ∷ p)
... | nothing = diffs₀ n d w t f

b0 : diff₀ 6 3 (E.EBOψ 0) x₀ ≡ nothing
b0 = refl

b1 : diff₀ 6 3 (E.EBOψ 1) x₁ ≡ nothing
b1 = refl

-- 对照: 比较器不是空的
c0ctl : Σ (List ℕ) λ q → diff₀ 4 3 (E.EBOψ 1) x₀ ≡ just q
c0ctl = _ , refl

c1ctl : Σ (List ℕ) λ q → diff₀ 4 3 (E.EBOψ 0) x₁ ≡ just q
c1ctl = _ , refl
```

## §2 裸层号上的路径

```agda
open Raw ver

e2 : diff 6 3 (E.EBOψ 2) (x 2) ≡ nothing
e2 = refl
e3 : diff 5 3 (E.EBOψ 3) (x 3) ≡ nothing
e3 = refl
e4 : diff 5 2 (E.EBOψ 4) (x 4) ≡ nothing
e4 = refl

ψ₀t : Tm → Tm
ψ₀t a = ψᵗ [] a ∷ []

one ω-t Ωt₁ ΩΩ : Tm
one  = ψ₀t []
ω-t  = ψ₀t one
Ωt₁  = ψᵗ one [] ∷ []
ΩΩ   = ψᵗ Ωt₁ [] ∷ []

-- ω + 1, ω + 2
ω+1 ω+2 : Tm
ω+1 = ω-t ++ one
ω+2 = ω-t ++ (one ++ one)

pth : List ℕ
pth = (1 ∷ 0 ∷ 0 ∷ 2 ∷ []) ++ (1 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ []) ++ (1 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 1 ∷ 2 ∷ 2 ∷ 2 ∷ []) ++ (1 ∷ 0 ∷ 0 ∷ 1 ∷ [])

tmA : Tm
tmA = proj₁ (walkB pth (E.EBOψ 3) (x 3))

trA : Ordᴸ zero
trA = proj₂ (walkB pth (E.EBOψ 3) (x 3))

-- 记号走到的站点: ψ₀(ψ_Ω(ψ_{ω+1}(Ω_Ω)))
hard-tm : tmA ≡ ψ₀t (ψᵗ Ωt₁ (ψᵗ ω+1 ΩΩ ∷ []) ∷ [])
hard-tm = refl

hard-ok : diff 4 3 tmA trA ≡ nothing
hard-ok = refl

-- 这个比较器分不开 ω+1 与 ω+2 (这个深度内没有走到那个差别): 所以 hard-ok 只是弱证据
hard-blind : diff 4 3 (ψ₀t (ψᵗ Ωt₁ (ψᵗ ω+2 ΩΩ ∷ []) ∷ [])) trA ≡ nothing
hard-blind = refl

-- 对照: 换成一个小得多的序数就有偏离
hard-ctrl : Σ (List ℕ) λ q → diff 4 3 one trA ≡ just q
hard-ctrl = _ , refl
```

## §3 通过 $W$

```agda
wTm : Tm
wTm = proj₁ (walkB (p₁ ++ p₂) (E.EBOψ 3) (x 3))

wTr : Ordᴸ zero
wTr = proj₂ (walkB (p₁ ++ p₂) (E.EBOψ 3) (x 3))

W-tm : wTm ≡ W
W-tm = refl

W-head : take 4 (p₁ ++ p₂) ≡ (1 ∷ 0 ∷ 0 ∷ 2 ∷ [])
W-head = refl

W-ok : diff 4 3 wTm wTr ≡ nothing
W-ok = refl

W-ctrl : Σ (List ℕ) λ q → diff 4 3 one wTr ≡ just q
W-ctrl = _ , refl
```
