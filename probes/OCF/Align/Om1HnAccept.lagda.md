# 验收: $\psi_0(\Omega_{\Omega+1})$ 不累加这一路

> **验收文件.** 只有本文件读记号 (`Lab`, `BTBO-label`). 判决: **序数值验收在 Ω+1 未走通**, 没有否定定理. 这里拿到的:
>
> | 定理 | 档 |
> |---|---|
> | `same-T⁰ : fr (force (G-p₀ 1)) ≅ fr T⁰`, 新证书对 $\psi_0(\Omega_\Omega)$ 这一站不变 | 基本列验收, 定理 (经 `any-cert`) |
> | `term₀ : ∀ d → fr (T₁ 的第 0 项) ≅ BTBOᴵ` | 第 0 项过基本列验收, 对任何证书 |
> | `label-term₀` | `Lab` 探路 |
> | `low : ∀ d → BTBOᴵ ⊑⁰ fr (force d)` | 非严格下界, 对任何证书 (`G₁` 是一个), 定理; 严格性未证 (判断: 成立) |
>
> **第一个障碍 (读源码, 判断, 没有编译的否定).** `NoCumW.add⁰` 在第 $(0,0)$ 层对闭包的写法是 `oc (W⊕x) (λ v → W⊕h v)`, 计值时链点读 **`W⊕x` 的输出**. `OCF.Free.Prefix.addˢ {k = zero}` 在第 0 层写成 `ĉᴸ c (toZ t₀) (toZ ∘ g) (a+t₀) (a+g)`, 链点读 **没加 $a$ 的 $t_0, g$**. 这个差在 $\psi_0(\Omega_{\Omega+1})$ 第 1 项里就出现: $\psi_0(\mathrm{os}\,\Omega_\Omega)=\lim\mathrm{rep}(a)$, $a=\psi_0(\Omega_\Omega)$, 第 2 项 $a\oplus a$ 是第 $(0,0)$ 层的闭包. 这里它的链点高于 $a$, (这一半是定理: `Om1HnNeg.shift`), 所以 $a\oplus a$ 的值判断为下一个不动点, 不是 $a\cdot2$. 所以判断: `T₁` 与 `GᴺΩ̇ 1` 的树**基本列不一致, 也不 $\cong$**, 只能指望序数值相等 (吸收), 不是模拟能给的. 这是 "不累加" 的 (p, a) 世界里残留的一处等效累加: 根上没有前缀, 但加法把 $W$ 带进了链点. $\psi_0(\Omega_\Omega)$ 这一站看不到它, 因为高度 0 的项没有闭包.
>
> 全文 `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Om1HnAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import OCF.Align.Level
import OCF.Align.NoCumsum as N
open N using (BTBOᴵ)
import OCF.Align.EBO as E
open import OCF.Align.Correspond using (Lab; Lab-≅)
open import OCF.Align.Label using (BTBO-label)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (azero; A; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumUpAcceptSim using (fr)
open import OCF.Align.NoCumLit using (z≈; ≈ᴬ-refl)
open import OCF.Align.NoCumW using (one; g₀; pos; lgw; Tᴰ; Ω̇; Ω̇at; ψ; oe; es)
open import OCF.Align.NoCumEq using (Ω≈)
open import OCF.Align.NoCumPsi using (ψQ)
open import OCF.Align.NoCumForce using (G; gw; gl; force; fo≅)
open import OCF.Align.NoCumOmega using (T⁰)
open import OCF.Align.NoCumAcceptOmega using (T⁰≅)
open import OCF.Align.NoCumHnAccept using (any-cert; fr≅)
open import OCF.Align.Om1HnMain using (G-p₀; G₁)

d₀ : G (Tᴰ 1 azero one g₀ (z⊲ one))
d₀ = G-p₀ 1

same-T⁰ : fr (force d₀) ≅ fr T⁰
same-T⁰ = ≅-trans (any-cert d₀) (≅-sym T⁰≅)

-- 第 n 项
tm : (d : G (Tᴰ 1 one one g₀ C.self)) → ℕ → FL.Ordᶜ FL.zero
tm (gw (gl Gs st)) n = force (Gs n)

term₀ : ∀ d → fr (tm d 0) ≅ BTBOᴵ
term₀ (gw (gl Gs st)) =
  ≅-trans (fr≅ (fo≅ (Gs 0) d₀ (ψQ (oe es (Ω̇at 1 azero g₀)) (Ω̇ 1 azero) g₀ g₀ one g₀ C.self _ _ one g₀ (pos g₀) (z⊲ one) (z⊲ one) (≈ᴬ-refl azero) (Ω≈ 1 z≈))))
          (any-cert d₀)

label-term₀ : ∀ d → Lab (fr (tm d 0)) (E.EBOψ 2)
label-term₀ d = Lab-≅ (term₀ d) BTBO-label

low : (d : G (Tᴰ 1 one one g₀ C.self)) → BTBOᴵ ⊑⁰ fr (force d)
low (gw (gl Gs st)) c = ≺l 0 (≅→⊑ (≅-sym (term₀ (gw (gl Gs st)))) c)

low-T₁ : BTBOᴵ ⊑⁰ fr (force G₁)
low-T₁ = low G₁

```
