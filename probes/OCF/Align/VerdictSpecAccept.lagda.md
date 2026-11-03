# 判决的规格: 验收 (与 EBO 比较)

> **验收节.** 记号只在本文件, 用来检验判据, 判据不读它. 结论写在 [VerdictSpec](VerdictSpec.lagda.md). 全部是有限测试, 只比种类, 宽度与深度有限.
>
> - **`S₁` (只在 $(\Omega,\Omega+1)$ 上穿透) 修好了 `Zero.dev`** (`dev-fixed`), 并走过第 30 步与 $W$.
> - **这段路径上 `S` 只被问到两种形状** (`Asked`, 其余是变量, `refl` 通过). 脚本探针读出的就是 $(\Omega,\Omega+1)$ 与 $(\Omega,\Omega)$.
> - **压力测试 `Sₕ`:** 下标对 $\Omega+u$, $\Omega+v$ 的十种组合, 判决由有限深度的比较给出, 全部与 EBO 一致.
> - **反面:** `PW` (判决全对, 链丢掉) 确实与 EBO 不符 (`wrong-is-wrong`); `PF` 在帧塔出错的 $\psi_0(\psi_{\Omega+1}(\Omega_{\Omega+1}))$ 与旧地板出错的 $\psi_0(\Omega_\Omega^2)$ 上与 EBO 一致 (`spec-frame`, `spec-floor`).
> - **没有找到判决正确而与记号不一致的树.** 这是有限测试, 不是定理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.VerdictSpecAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_; take)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.InaccTreeBase as B using (Lv; Ordᴸ; Pre; at; Ω; toLv; rise; pen; Verdict; Tree; up; _+_; limᴼ; lim; limᵢ)
open import OCF.Align.InaccFloorTree using (Sib; natL; fin; bel; sib; module PF)
open import OCF.Align.InaccFloorAccept using (module AllS; module Zero; S₀)
open import OCF.Align.InaccTreeAccept using (diff)
open import OCF.Align.Uniform5Wall using (tΩΩ; W; p₁; p₂)
open import OCF.Align.Uniform4Head using (Ωp)
open import OCF.Align.Uniform4Expt using () renaming (ψ₁ to ψ₊₁)
open import OCF.Align.OmegaPlus1Base using (Ω⁺¹)
open import OCF.Align.OmegaKBase using (tΩ2)
open import OCF.Align.Uniform3Base using (ψ₀ᵗ)
import OCF.Align.EBO as E
open E using (T; Ωt; natT) renaming (ψ to ψᵗ)
open import OCF.Align.VerdictSpecBase using (coe⁺)
open import OCF.Align.VerdictSpecReject using (S₁; module PW; path₂)
open import OCF.Align.VerdictSpecFrame using (module Spec)
```

## §1 `S₁`

$p_1,p_2$ 的第 40 步是 $W$. `Zero.dev` 说 `S₀ = rise` 在 $W[0]$ 之下深度 10 错. 换成 `S₁` 不错了 (`dev-fixed`).

```agda
pw2 pw : List ℕ
pw2 = p₁ ++ p₂
pw  = pw2 ++ (0 ∷ [])

module One where
  open AllS S₁ using (tmAt; dfP)

  reach-W : tmAt pw2 ≡ W
  reach-W = refl

  step30 : dfP (take 30 pw2) 5 3 ≡ nothing
  step30 = refl

  at-W : dfP pw2 6 3 ≡ nothing
  at-W = refl

  dev-fixed : dfP pw 10 2 ≡ nothing
  dev-fixed = refl

  below-W1 : dfP (pw2 ++ (1 ∷ [])) 7 2 ≡ nothing
  below-W1 = refl

  below-W2 : dfP (pw2 ++ (2 ∷ [])) 7 2 ≡ nothing
  below-W2 = refl
```

## §2 这段路径上只问到两种形状

`Sₐ Sv` 在 $(\mathtt{lim}^\mathsf{O}\,0\,\_,\ \mathtt{lim}^\mathsf{O}\,0\,\_+1)$ 与 $(\mathtt{lim}^\mathsf{O}\,0\,\_,\ \mathtt{lim}^\mathsf{O}\,0\,\_)$ 上答得与 `S₁` 相同, 其余问变量 `Sv`. `refl` 通过, 所以其余的层号对没有被问到. (脚本探针把这两种形状读成 $(\Omega,\Omega+1)$, $(\Omega,\Omega)$; 第 0 层的节点走 `zv`, 不问 `S`.)

```agda
Sₐ : Sib → Sib
Sₐ Sv j@(limᴼ B.zero _) (B.suc i@(limᴼ B.zero _)) = pen (inj₁ tt) (coe⁺ i j)
Sₐ Sv (limᴼ B.zero _) (limᴼ B.zero _) = rise
Sₐ Sv j i = Sv j i

module Asked (Sv : Sib) where
  open AllS (Sₐ Sv) using (dfP)

  q-dev : dfP pw 10 2 ≡ nothing
  q-dev = refl

  q-W1 : dfP (pw2 ++ (1 ∷ [])) 7 2 ≡ nothing
  q-W1 = refl
```

## §3 压力测试: 下标对 $\Omega+u$, $\Omega+v$

`Sₕ` 是测试用的判决: 有限深度比较层号, 搜索路径, 搬运用 `coe⁺`. 它不是定理, 只是手给的判决. `ck` 比较 $\psi_0(\psi_{\Omega+u}(\Omega_{\Omega+v}))$. 这些对都不是字面路径的目标与节点 (模式是 `sib`).

```agda
eqL : ℕ → Lv → Lv → Bool
eqL zero _ _ = true
eqL (suc d) B.zero B.zero = true
eqL (suc d) (B.suc a) (B.suc b) = eqL d a b
eqL (suc d) (lim f) (lim g) = eqL d (f 0) (g 0) ∧ (eqL d (f 1) (g 1) ∧ eqL d (f 2) (g 2))
eqL (suc d) (limᴼ k g) (limᴼ k′ g′) = eqL d k k′ ∧ (eqL d (g Tree.zero) (g′ Tree.zero) ∧ eqL d (g (Tree.suc Tree.zero)) (g′ (Tree.suc Tree.zero)))
eqL (suc d) _ _ = false

find : ℕ → ℕ → (j i : Lv) → Maybe (Pre i)
find d zero j i = nothing
find d (suc w) j B.zero = nothing
find d (suc w) j (B.suc k) with eqL d j k
... | true = just (inj₁ tt)
... | false with find d w j k
...   | just r = just (inj₂ r)
...   | nothing = nothing
find d (suc w) j (lim f) = go 3 where
  go : ℕ → Maybe (Pre (lim f))
  go zero = nothing
  go (suc n) with find d w j (f n)
  ... | just r = just (n , r)
  ... | nothing = go n
find d (suc w) j (limᴼ k g) with eqL d j k
... | true = just (inj₁ (inj₁ tt))
... | false with find d w j k
...   | just r = just (inj₁ (inj₂ r))
...   | nothing with find d w j (g (Tree.suc Tree.zero))
...     | just r = just (inj₂ (Tree.suc Tree.zero , r))
...     | nothing = nothing

Sₕ : Sib
Sₕ j i with find 7 7 j i
... | just r = pen r (coe⁺ (at i r) j)
... | nothing = rise

module Stress where
  open PF Sₕ using (ψᵖ; ψⁿ)

  Ω₁ : Ordᴸ (natL 1)
  Ω₁ = Ω (natL 1)

  lv : Ordᴸ B.zero → Lv
  lv t = toLv (Ω₁ + up tt t)

  ω̂ ω̂₂ ε̂ : Ordᴸ B.zero
  ω̂  = ψⁿ 0 {B.zero} (Tree.suc Tree.zero)
  ω̂₂ = ψⁿ 0 {B.zero} (Tree.suc (Tree.suc Tree.zero))
  ε̂  = ψⁿ 0 (Ω (natL 1))

  tω tω₂ tε : T
  tω  = ψ₀ᵗ (natT 1)
  tω₂ = ψ₀ᵗ (natT 2)
  tε  = ψ₀ᵗ (Ωp ∷ [])

  n̂ : ℕ → Ordᴸ B.zero
  n̂ zero    = Tree.zero
  n̂ (suc n) = Tree.suc (n̂ n)

  tU : T → T → T
  tU u v = ψ₀ᵗ (ψᵗ (Ωp ∷ u) (Ωt (Ωp ∷ v)) ∷ [])

  tree : Ordᴸ B.zero → Ordᴸ B.zero → Ordᴸ B.zero
  tree u v = ψᵖ (fin 0 refl) (ψᵖ {k = lv v} {i = lv u} sib (Ω (lv v)))

  ck : T → T → Ordᴸ B.zero → Ordᴸ B.zero → Maybe (List ℕ)
  ck a b u v = diff 6 2 (tU a b) (tree u v)

  r₁ : ck (natT 1) (natT 2) (n̂ 1) (n̂ 2) ≡ nothing     -- 节点 Ω+1 = 目标
  r₁ = refl
  r₂ : ck (natT 1) (natT 3) (n̂ 1) (n̂ 3) ≡ nothing     -- 节点 Ω+2 > 目标
  r₂ = refl
  r₃ : ck (natT 2) (natT 2) (n̂ 2) (n̂ 2) ≡ nothing     -- 节点 Ω+1 < 目标
  r₃ = refl
  r₄ : ck tω (natT 2) ω̂ (n̂ 2) ≡ nothing               -- 目标 Ω+ω, 路径经过 lim
  r₄ = refl
  r₅ : ck (natT 1) tω (n̂ 1) ω̂ ≡ nothing               -- 节点在 Ω_{Ω+ω} 的 lim 里
  r₅ = refl
  r₆ : ck tω (tω ++ natT 1) ω̂ (Tree.suc ω̂) ≡ nothing  -- 节点 Ω+ω = 目标
  r₆ = refl
  r₇ : ck (tω ++ natT 1) tω₂ (Tree.suc ω̂) ω̂₂ ≡ nothing
  r₇ = refl
  r₈ : ck tε (natT 2) ε̂ (n̂ 2) ≡ nothing               -- 目标 Ω+ε
  r₈ = refl
  r₉ : ck tω tε ω̂ ε̂ ≡ nothing
  r₉ = refl
  r₁₀ : ck tε (tε ++ natT 1) ε̂ (Tree.suc ε̂) ≡ nothing -- 节点 Ω+ε = 目标
  r₁₀ = refl
```

## §4 判据之外的反例与它们的对照

`spec-frame`: `PF` 在帧塔出错的项上与 EBO 一致, 路径 `fp` 在范围内. `spec-floor`: 旧地板的目标 $\psi_0(\Omega_\Omega^2)$, `PF` 没有地板, 一致. `wrong-is-wrong`: `PW` 判决全对, 与 EBO 不符, 这是 `wrong-fold` 的正对照.

```agda
module Controls (S : Sib) where
  open Spec S using (Tˢ)
  open PF S using (ψᵖ)

  tF : T
  tF = ψ₀ᵗ (ψ₊₁ (Ω⁺¹ ∷ []))

  spec-frame : diff 9 2 tF Tˢ ≡ nothing
  spec-frame = refl

  LΩ : Lv
  LΩ = toLv (Ω (natL 1))

  Tq : Ordᴸ B.zero
  Tq = ψᵖ (fin 0 refl) (ψᵖ (bel (λ r → r , refl)) (Ω LΩ))

  spec-floor : diff 8 2 tΩ2 Tq ≡ nothing
  spec-floor = refl

  wrong-is-wrong : diff 5 2 (ψ₀ᵗ (Ωt (natT 2))) (PW.Tʷ S (natL 2)) ≡ just (1 ∷ 1 ∷ 1 ∷ [])
  wrong-is-wrong = refl

  right-is-right : diff 5 2 (ψ₀ᵗ (Ωt (natT 2))) (PF.T S (natL 2)) ≡ nothing
  right-is-right = refl
```
