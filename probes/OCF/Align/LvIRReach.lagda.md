# 归纳-递归块: $\psi_0(\Omega_{\Omega_2})$ 字面地走到目标 $\omega+1$, 分支是全部第 0 层输入

> 不含记号. 结论写在 [LvIR](LvIR.lagda.md). 世界是 [EBOTopRaw](EBOTopRaw.lagda.md) 的裸层号与 `Raw S`. 全部是 `refl` 的有限路径, 不是全称定理, 但每一步都编译过.
>
> **结论.** `T₁ 2 = ψ₀(Ω_{Ω₂})` 沿路径 $(1,0,0,2,0)$ 走到 $\psi_0(\Omega_{\Omega+1})$ (`reach-sucL₂`, 对一切 `S`), 再沿 $(1,1,0,1,0,1,2,2,2)$ 走到 $\psi_0(\psi^{\mathsf{bel}}_{\Omega}(\Omega_{\omega+2}))$ (`reach-node`, 对一切 `S`). 取 `S = ver`, 再沿 $(1,0,0,1)$ 走到 $\psi_0(\psi^{\mathsf{bel}}_{\Omega}(\psi_{\omega+1}(\Omega_\Omega)))$ (`reach-hard`). 而 $\psi_{\omega+1}(\Omega_\Omega)$ 的头是穿透到第 0 层, 分支是**每一个**第 0 层的输入 $v$, 第 $v$ 枝是 $\psi_{\omega+1}(\Omega_v)$ (`hard`). 所以**第一个具体站点 $\psi_0(\Omega_{\Omega_2})$ 已经要求目标 $\omega+1$ 对全部好输入有判决**. [LvIRNeg](LvIRNeg.lagda.md) 的 `no-read` 说: 这个判决只要好输入含反例族就是 WLPO.
>
> [EBOTop](EBOTop.lagda.md) 把非自然数目标记在 $x_3$ 名下, 把 `HS (T₁ (natT 2))` 当作第一步. 实测这一步里就有非自然数目标, 而且它不全是 `sib` 丢路径造成的假问题: §2 的第一问 (节点 $\omega$, 目标 $\omega+1$, 同一枝) 是假问题, 第二问 (`hard`, 全部 $v$) 不是.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvIRReach where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.InaccTreeBase
open import OCF.Align.InaccFloorTree using (Sib; Mode; fin; lt; sib; bel; upM; verdict; chM; natL; Sz; module PF)
open import OCF.Align.EBOTopRaw
import OCF.Align.EBOTopStage as St
open import OCF.Align.LvIRNeg as N using (natO)
```

## §1 对一切 `S`

```agda
module AllS (S : Sib) where
  open Raw S
  open PF S using (ψᵖ)

  T2 : Ordᴸ zero
  T2 = T₁ (suc (suc zero))

  L₂ : Lv
  L₂ = limᴼ zero toLv

  -- ψ₀(Ω_{Ω+1}): 层号是 L₂ 的后继, 节点层是 L₂ 自己
  reach-sucL₂ : walkT (1 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ []) T2 ≡ X (suc L₂)
  reach-sucL₂ = refl

  Lj : Lv
  Lj = suc (suc (toLv ω′))

  -- 第 0 层的链点 c₁ 沿 (0,1,0,1,2,2,2) 走到 ω+2. 这个 Ω 在第 c₁ 枝里
  reach-node : Σ (Sim Lj L₂) λ σ →
    walkT (1 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 1 ∷ 2 ∷ 2 ∷ 2 ∷ []) (X (suc L₂)) ≡ ψ₀ (ψᵖ (bel σ) (Ω Lj))
  reach-node = _ , refl
```

## §2 第一问是假问题, 第二问不是

取 `S = ver`. 这一支的链目标是 `j` $=\omega+1$, 字面地在 $L_2$ 的第 $c_1$ 枝里, 路径是 `p`. 第一问比节点 $\omega$ 与目标 $\omega+1$: 它们在**同一枝**, 只是 [InaccFloorTree](InaccFloorTree.lagda.md) 的 `lit` 在 `limᴼ` 的 `inj₂` 上不看 $x$ 是否相同 (由 `lit` 的定义读出, 这里没有写成等式). 第二问在 $\Omega_\Omega$ 上: 头穿透, 分支是全部 $v$ (`hard`), 第 $v$ 枝的节点是 $v$ 的前驱 (`ask`).

```agda
module Ver where
  open Raw ver
  open PF ver using (ψᵖ)
  open AllS ver using (L₂; Lj; reach-node; reach-sucL₂; T2) public

  σ : Sim Lj L₂
  σ = proj₁ reach-node

  p : Pre L₂
  p = proj₁ (σ (inj₁ tt))

  j : Lv
  j = at L₂ p

  j-is : j ≡ suc (toLv ω′)
  j-is = refl

  ΩL : Ordᴸ L₂
  ΩL = Ω L₂

  reach-hard : Σ (Sim j L₂) λ τ →
    walkT (1 ∷ 0 ∷ 0 ∷ 1 ∷ []) (ψ₀ (ψᵖ (bel σ) (Ω Lj))) ≡ ψ₀ (ψᵖ (bel τ) (ψᵖ (lt p refl) ΩL))
  reach-hard = _ , refl

  r₀ : Pre j
  r₀ = inj₂ (1 , inj₁ tt)

  -- 头穿透到第 0 层, 分支是全部第 0 层的输入, 第 v 枝是 ψ_{ω+1}(Ω_v)
  hard : ψᵖ (lt p refl) ΩL ≡ limᵢ r₀ (λ v → ψᵖ sib (Ω (toLv {zero} v)))
  hard = refl

  -- 第 v = a+1 枝问的是: a 与 ω+1 比
  ask : ∀ (a : Ordᴸ zero) → verdict ver (sib {suc (toLv a)} {j}) (inj₁ tt) ≡ Sz ver (toLv a) j
  ask a = refl
```

## §3 这里的 $\omega$ 就是反例族比较的 $\omega$

`no-read` 的 $\omega$ 是 `lim natO`, 这里的目标是 $\omega'+1$. 它们 $\cong^0$. 所以 `ask` 的问题对 $a$ 取反例族的值就是 `no-read` 的问题 (判断: 从层号的判决读到 `O₀` 上的 `Dec` 这一步没有写成映射, 因为判决的语义本身就是由 $\prec^0$ 规定的, 见 [VerdictSpecEvid](VerdictSpecEvid.lagda.md)).

```agda
module Link (S : Sib) where
  open Raw S

  natT≅ : ∀ k → rd (natT k) St.≅⁰ natO k
  natT≅ zero    = St.z≅
  natT≅ (suc k) = St.s≅ (natT≅ k)

  ω′≅ω : rd ω′ St.≅⁰ N.ω
  ω′≅ω = St.l≅ go where
    add-nat : ∀ m → natT 1 + natT m ≡ natT (suc m)
    add-nat zero    = refl
    add-nat (suc m) = cong suc (add-nat m)
    eqn : ∀ k → iter (natT 1 +_) zero k ≡ natT k
    eqn zero    = refl
    eqn (suc k) rewrite eqn k = add-nat k
    go : ∀ k → rd (iter (natT 1 +_) zero k) St.≅⁰ natO k
    go k rewrite eqn k = natT≅ k
```
