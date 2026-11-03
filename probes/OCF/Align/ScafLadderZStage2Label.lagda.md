> **机械克隆.** 由 `Stage2Label` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# $\psi^P$ 的闭包定理与 $\psi_0(\Omega_\Omega+\Omega_2)$ 的计值树

> 接 [Prefix](Prefix.lagda.md) §8 与 [UniformS](UniformS.lagda.md). UniformS 把 Uniform 移植到新族; 本文在其上证明 `Goodᶻ` 对 $\psi^P$ 的输出封闭 (界 $\le2$ 的闭包), 构造 $\psi_0(\Omega_\Omega+\Omega_2)$ 的计值树, 并做标签检验.
>
> 结论先说:
>
> 1. **严格性引理 (§4).** `Strict₀`: 空栈、目标 0 的 $\psi$ 输出 (任意尾巴, 任意证书) 的层号 $\sqsupseteq^\mathsf I1$. **`Strict₁`: 单 $\hat\Omega$ 栈、目标 0 的输出, 对任意自反尾巴与任意证书, 层号 $\sqsupseteq^\mathsf I2$**, 即输出 $\succ1$. 证明不经 $\sqsubseteq^\mathsf o$ 的后继同余 (Level 的 $\sqsubseteq$ 对 `suc` 不单调): 先对栈的弹出证 $\psi^{[\hat\Omega]}_0(0)\succ1$ (它的第 0 个链点 $\psi^{[]}_0(\Omega_1)$ 已 $\succ1$, `one≺`, 这一步也用观测证明, 因为对 `<ᴵ-dec` 的 `with` 抽象不合法, 报错见 §4), 再用带栈的链起点 `B1₁` 推到任意尾巴. 由此得到界 $\le2$ 的闭包的 `d₀`/`dE`: 弹栈处 (`popDom`), 与非零层的 `ŝ` 被单 $\hat\Omega$ 栈的 $\psi_0$ 映到第 0 层处 (`Dom-ψ1`).
> 2. **闭包定理 (§3, §5).** `Good-ψ0 : Good x → x ≅ˢ x → Ok i x → Good (ψᴾ 0 p σ [] x)`, 其中 `Ok zero x` = $x$ 无符号 (与 Level 的某棵树异族互模拟 `_~_`), 非零目标层无条件. **`Good-ψ1 : ℓ ⊑ᴵ 2 → Good x → x ≅ˢ x → Good (ψᴾ 1 p σ (fΩ̂ z ∷ []) x)`**: 单个 $\hat\Omega$ 帧, 环境层号 $\le2$, 任意目标层、任意 `Sim`、任意好输入. 前提 $\ell\sqsubseteq^\mathsf I2$ 恰用两次, 都在支配字段.
> 3. **检验 1 的计值树 (§6).** **`GX₂ : Goodᶻ (toZ X₂ˢ)`, `X₂ᶠ = force (toZ X₂ˢ) GX₂`** ($\psi_0(\Omega_\Omega+\Omega_2)$, 环境层号 2). 沿 Symbolic 的 `PB` (静态树在此走到 `zero`, `B0-unlabel`) 计值树非零 (`refl`): 闭包在折叠内部计值.
> 4. **标签 (§7–§8).** `pop0≅`: 目标 0 的弹栈闭包在**任意**环境层号、任意证书下计值 $\cong$ `BTBOᴵ` (Prefix `βˢ≅` 的一般形). `fadd`: 计值与加法交换. **静态前缀桥 `brg`**: 第 0 层 (可数) 尾巴上, 符号前缀的计值 $\cong$ Stage2 的静态前缀 $\psi^0(\Omega_{\ell_0}+\cdot)$, 推论 `Ctxˢ` (Stage2 `Ctx₀` 在新树上). 于是新树上 **`tsˢ-label` ($\psi_0(\Omega_\Omega+1)$)、`χ1ˢ-label` ($\psi_0(\Omega_\Omega+\Omega)$) 与 `X₂-0 : Lab (sq X₂ᶠ 0) (fsn X₂ᵗ 0)`** 是定理.
> 5. **$\psi_0(\Omega_\Omega+\Omega_2)$ 的完整标签未得 (§9).** `X₂-reduce` 把它归约为各项; 第 0 项已证, **第一个未证的是第 1 项** $X_2[1]=\psi_0(\Omega_\Omega+\psi_1(\Omega_\Omega+\Omega_1))$: 尾巴在第 1 层 (共尾度 $\Omega_1$, `refl`), `brg`/`Ctx₀` 都只管可数尾巴. 它的后代 $A[1]=\psi_0(\Omega_\Omega+\psi_1(\Omega_{\eta_1}))$ 以阶段 2 的项 $\eta_1=A[0]$ 为 $\Omega$-下标, 所以缺的引理是带前缀的 `Generic` (阶段 2 的下标系统沿 $A$ 的链逐阶段生成), 不再是证书问题.
> 6. **序的对应可从标签读出 (§10).** `Lab-oc : Lab X u → NF₁ u → Lab Y v → NF₁ v → v <ᵀ u → Y ≺ X`, 对一切 `NF₁` 项 (用 `cofin₁` 与离散性), 不需要 `Generic` 的 `corr`. 实例 `BTBO≺χ1ˢ`. 这是步骤 2 的同时归纳里 "标签 ⟹ 支配" 那一半.
> 7. **步骤 2 的停点 (§11).** $\psi_0(\Omega_\Omega\cdot2)$ 的第 1 个链点 $\gamma'_2$ 内部有 $X_3=\psi_0(\Omega_\Omega+\Omega_3)$ (Symbolic 的 `t2-to-X₃`), 其中出现界为 3 的闭包 (`refl`), `Good-ψ1` 的前提 $\ell\sqsubseteq^\mathsf I2$ 不成立; 一般的界 $j+1$ 跑遍 $\mathtt{lvl}\,\gamma'_1$ 的子层号, 需要 "$\psi^{[\hat\Omega]}_0(\Omega_j)$ 的层号 $\sqsupseteq j+1$", 它对 $j$ 本身的大小有要求 (只在 $j<\psi_0(\Omega_\Omega\cdot2)$ 时为真), 必须来自标签 (`Lab-oc`), 而这些标签 (含 $X_2$) 正是第 5 条的缺口.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块 (与 UniformS), 不改任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderZStage2Label where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Vec using (Vec; []; _∷_)
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Ctx; Pt; pt; lvP; Γᶜ; Mlev; σ1; X₂ᵗ)
open import OCF.Align.ScafLadderZPrefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; fΩ̂; ψᴾ;
  trˢ; tr⁻ˢ; outs; Goodᶻ; force; force-HS; _~_; H₊; Rh→~; ~→Rh; ψ~; Ω~; z<suc; empty-agree; X₂ˢ; z2; z1; kind; Kind; kc; walkˢ)
import OCF.Align.NoCumsum as N
import OCF.Align.EBO as E
open E using (T; natT; fsn; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne)
open import OCF.Align.Label using (BTBO-label)
open import OCF.Align.Bachmann using (<sucT)
open import OCF.Align.Closure using (lt→<)
open import OCF.Align.Standard using () renaming (d₀ to d₀ᴰ)
open import OCF.Align.ScafLadderZStandardOmega using (NF₁; NF₁-pred; NF₁-fsn; cofin₁; γ′-NF; diag₁-desc-NF; walkD)
open import OCF.Align.Stage2 using (≺→⊑; ℓ₀; Ctx₀; ctx; ts; lab-χ0; γ′ᴱ; b′; fs-χ1; sq; walk; Lab-uniq; Ωᵗ)
open import OCF.Align.ScafLadderZUniformS
```

## §1 无符号输入与 `Ok`

空栈、目标 0 的折叠不产生新的界, 但若它的尾巴里有非零层的 `ŝ` (界 2), 输出是第 0 层的链, 支配要求 "$\psi^{[]}_0$ 的输出 $\succ1$": 对非零尾巴这在序数上成立, 在树上却要 $X\sqsupseteq1\Rightarrow X+X\sqsupseteq2$ 一类的后继同余, 不成立 (Prefix §8 的纸面反例). 所以空栈、目标 0 的折叠只用于**无符号**输入. 无符号就用 Prefix §5 的异族互模拟表达: $x$ 与 Level 族的某棵树 `~` 相关 (`Pl`). 它对后继、极限、`up` 下降, 对 `ŝ`/`ĉᴸ` 不成立, 对折叠的链点保持 (链点与 Level 族的链点由 `ψ~` 逐个相关, `~chain`).

```agda
Pl : ∀ {k} → Ordˢ k → Set
Pl x = Σ Ordᴵ λ ℓ′ → Σ (Ordᶜ ℓ′) λ y → x ~ y

~suc : ∀ {k ℓ′} {a : Ordˢ k} {y : Ordᶜ ℓ′} → Ord₊ˢ.suc a ~ y → Pl a
~suc (H₊.s~ d)              = _ , _ , d
~suc (H₊.upʳ {r = zero} d)   = ~suc d
~suc (H₊.upʳ {r = self n} d) = ~suc d

~lim : ∀ {k ℓ′} {f : ℕ → Ordˢ k} {y : Ordᶜ ℓ′} → Ord₊ˢ.lim f ~ y → ∀ n → Pl (f n)
~lim (H₊.l~ h) n              = _ , _ , h n
~lim (H₊.upʳ {r = zero} d) n   = ~lim d n
~lim (H₊.upʳ {r = self m} d) n = ~lim d n

~up : ∀ {k ℓ ℓ′} (r : k ◃₁ ℓ) {x : Uˢ k (◃₁→◃ r)} {y : Ordᶜ ℓ′} → Ord₊ˢ.up r x ~ y → Pl (outˢ (◃₁→◃ r) x)
~up zero     (H₊.upˡ d)              = _ , _ , d
~up (self n) (H₊.upˡ d)              = _ , _ , d
~up r        (H₊.upʳ {r = zero} d)   = ~up r d
~up r        (H₊.upʳ {r = self n} d) = ~up r d

~ŝ : ∀ {k ℓ′ c t₀ g} {y : Ordᶜ ℓ′} → Ord₊ˢ.ŝ {ℓ = k} c t₀ g ~ y → ⊥
~ŝ (H₊.upʳ {r = zero} d)   = ~ŝ d
~ŝ (H₊.upʳ {r = self n} d) = ~ŝ d

~ĉ : ∀ {k ℓ′ c t₀ g o₀ o} {y : Ordᶜ ℓ′} → Ord₊ˢ.ĉᴸ {ℓ = k} c t₀ g o₀ o ~ y → ⊥
~ĉ (H₊.upʳ {r = zero} d)   = ~ĉ d
~ĉ (H₊.upʳ {r = self n} d) = ~ĉ d

chain0 : ∀ {j k ℓ} (σ : Simᴵ k ℓ) (q : j <ᴵ k) (f : Uˢ j (<→◃ q) → Ordˢ k) → ℕ → Ordˢ j
chain0 {j} σ q f = iter (λ x → ψ0 (σ q) σ (f (intoˢ (<→◃ q) x))) (Ωˢ j)

chain1 : ∀ {j k ℓ} (σ : Simᴵ k ℓ) (z : zero <ᴵ ℓ) (q : j <ᴵ k) (f : Uˢ j (<→◃ q) → Ordˢ k) → ℕ → Ordˢ j
chain1 {j} σ z q f = iter (λ x → ψ1 (σ q) σ z (f (intoˢ (<→◃ q) x))) (Ωˢ j)

~chain : ∀ {j k ℓ ℓ′} (σ : Simᴵ k ℓ) {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} {y : Ordᶜ ℓ′} →
         Ord₊ˢ.limᵢ q f ~ y → ∀ n → Pl (f (intoˢ (<→◃ q) (chain0 σ q f n)))
~chain σ {q = q} {f = f} (H₊.lᵢ~ {q = q′} {g = g} e h) n = _ , _ , h _ _ (~→Rh (<→◃ q) (ch n))
  where
  ch = iter-R _~_ {G = λ x → ψ0 (σ q) σ (f (intoˢ (<→◃ q) x))} {G′ = λ y → ψ q′ (λ r → r) (g (into (<→◃ q′) y))}
              (λ d → ψ~ {p = σ q} {σ = σ} {p′ = q′} {σ′ = λ r → r} e (h _ _ (~→Rh (<→◃ q) d))) (Ω~ e)
~chain σ (H₊.upʳ {r = zero} d)   n = ~chain σ d n
~chain σ (H₊.upʳ {r = self m} d) n = ~chain σ d n

Pl-Ω : ∀ a → Pl (Ωˢ a)
Pl-Ω a = _ , Ω a , Ω~ (≅ᴵ-refl a)
```

`Ok i x`: 目标层为 0 时 $x$ 无符号, 否则无条件. 派发的折叠分支 (`injᵇ`: $i\prec j$, `injᶜ`: $j\cong i$) 下, 链点的 `Ok` 由 `Ok-col` 给出: 目标 0 时链点无符号 (`~chain`); 目标非零时节点层 $j$ 也非零 ($j=0$ 会给出 $i\prec0$ 或 $0\cong i$, 后者迫使 $i$ 字面为 `zero`).

```agda
Ok : (i : Ordᴵ) → ∀ {k} → Ordˢ k → Set
Ok zero      x = Pl x
Ok (suc _)   x = ⊤
Ok (lim _ _) x = ⊤

Ok-Pl : ∀ i {k} {x : Ordˢ k} → Pl x → Ok i x
Ok-Pl zero      h = h
Ok-Pl (suc _)   h = tt
Ok-Pl (lim _ _) h = tt

Ok-suc : ∀ i {k} {a : Ordˢ k} → Ok i (Ord₊ˢ.suc a) → Ok i a
Ok-suc zero      (_ , _ , d) = ~suc d
Ok-suc (suc _)   _ = tt
Ok-suc (lim _ _) _ = tt

Ok-lim : ∀ i {k} {f : ℕ → Ordˢ k} → Ok i (Ord₊ˢ.lim f) → ∀ n → Ok i (f n)
Ok-lim zero      (_ , _ , d) n = ~lim d n
Ok-lim (suc _)   _ n = tt
Ok-lim (lim _ _) _ n = tt

Ok-up : ∀ i {k ℓ} (r : k ◃₁ ℓ) {x : Uˢ k (◃₁→◃ r)} → Ok i (Ord₊ˢ.up r x) → Ok i (outˢ (◃₁→◃ r) x)
Ok-up zero      r (_ , _ , d) = ~up r d
Ok-up (suc _)   r _ = tt
Ok-up (lim _ _) r _ = tt

Ok-col : ∀ {i j k ℓ} (σ : Simᴵ k ℓ) {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
         (i ≺ᴵ j ⊎ j ≅ᴵ i) → Ok i (Ord₊ˢ.limᵢ q f) →
         ∀ n → Ok j (f (intoˢ (<→◃ q) (chain0 σ q f n))) × Ok i (f (intoˢ (<→◃ q) (chain0 σ q f n)))
Ok-col {i = zero}    {j} σ c (_ , _ , d) n = Ok-Pl j (~chain σ d n) , ~chain σ d n
Ok-col {i = suc _}   {j = zero}    σ (inj₁ (via e ())) ok n
Ok-col {i = suc _}   {j = zero}    σ (inj₂ ()) ok n
Ok-col {i = suc _}   {j = suc _}   σ c ok n = tt , tt
Ok-col {i = suc _}   {j = lim _ _} σ c ok n = tt , tt
Ok-col {i = lim _ _} {j = zero}    σ (inj₁ (via e ())) ok n
Ok-col {i = lim _ _} {j = zero}    σ (inj₂ ()) ok n
Ok-col {i = lim _ _} {j = suc _}   σ c ok n = tt , tt
Ok-col {i = lim _ _} {j = lim _ _} σ c ok n = tt , tt
```

## §2 规则 6 的链

链点是 $\psi^P_{\sigma q}(f\,x)$, 带同一个栈 (Prefix §3). 自反 (`chain0-≅`/`chain1-≅`) 与步进同 Uniform 的 `chain-≅`/`chain-step`. 单 $\hat\Omega$ 栈的步进第 0 步要 $\Omega_j\sqsubseteq^\mathsf o\psi^{[\hat\Omega]}_j(f\,\Omega_j)$; 经 `B1₁` 只需 $\Omega_j\sqsubseteq^\mathsf o\psi^{[\hat\Omega]}_j(0)$, 它是弹栈闭包, 第 0 点 $\psi^{[]}_j(\Omega_1)\sqsupseteq^\mathsf o\Omega_j$ (`B1₀`), 再 `ŝ-r` (`Ω⊑pop`; 即 $\psi_j(\Omega_\Omega)\ge\psi_j(\Omega_1)\ge\Omega_j$).

```agda
chain0-≅ : ∀ {j k k′ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} {b : Ordˢ k′} →
           Ord₊ˢ.limᵢ q f ≅ˢ b → ∀ n → chain0 σ q f n ≅ˢ chain0 σ q f n
chain0-≅ {j} e zero    = Ωˢ-refl j
chain0-≅ {j} e (suc n) = ψ0-≅ (≅ᴵ-refl j) (i-respˢ e (chain0-≅ e n))

chain1-≅ : ∀ {j k k′ ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} {b : Ordˢ k′} →
           Ord₊ˢ.limᵢ q f ≅ˢ b → ∀ n → chain1 σ z q f n ≅ˢ chain1 σ z q f n
chain1-≅ {j} e zero    = Ωˢ-refl j
chain1-≅ {j} e (suc n) = ψ1-≅ (≅ᴵ-refl j) (i-respˢ e (chain1-≅ e n))

chain0-step : ∀ {j k k′ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} {b : Ordˢ k′} → Ord₊ˢ.limᵢ q f ≅ˢ b →
              (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ q) z) ⊑ᵒ f (intoˢ (<→◃ q) z′)) →
              ∀ n → chain0 σ q f n ⊑ᵒ chain0 σ q f (suc n)
chain0-step {j} {σ = σ} {q = q} {f = f} e hm zero =
  B1₀ {q = σ q} {σ = σ} (≅→⊑ᵒ (Ωˢ-refl j)) (f (intoˢ (<→◃ q) (Ωˢ j))) (i-respˢ e (Ωˢ-refl j))
chain0-step e hm (suc n) = ψ0-cong (hm (chain0-step e hm n))

Ω⊑pop : ∀ {j k ℓ} (t : j <ᴵ ℓ) (σ : Simᴵ k ℓ) (z : zero <ᴵ ℓ) → Ωˢ j ⊑ᵒ ψ1 t σ z Ord₊ˢ.zero
Ω⊑pop {j} t σ z = ŝ-r (B1₀ (≅→⊑ᵒ (Ωˢ-refl j)) (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)))

chain1-step : ∀ {j k k′ ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} {b : Ordˢ k′} →
              Ord₊ˢ.limᵢ q f ≅ˢ b →
              (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ q) z) ⊑ᵒ f (intoˢ (<→◃ q) z′)) →
              ∀ n → chain1 σ z q f n ⊑ᵒ chain1 σ z q f (suc n)
chain1-step {j} {σ = σ} {z = z} {q = q} {f = f} e hm zero =
  B1₁ {q = σ q} {σ = σ} {z₁ = z} (Ω⊑pop (σ q) σ z) (f (intoˢ (<→◃ q) (Ωˢ j))) (i-respˢ e (Ωˢ-refl j))
chain1-step e hm (suc n) = ψ1-cong (hm (chain1-step e hm n))
```

## §3 空栈的闭包定理

`mkĉ`: 第 0 层的 `ŝ` 被映成 `ĉᴸ` 时 (尾巴在第 0 层), 链的证书由 `Good→Goodᶻ`, 支配与单调在这些证书处实例化 (这一步不需要新的支配: 链就是原来的链). `Good-ψ0` 与 Uniform 的 `Good-ψ` 同形, `chain0-good` 互递归; 新情况:

- 尾巴 `ŝ`/`ĉᴸ`, 目标 0: 由 `Ok` (无符号) 排除.
- 尾巴第 0 层的 `ŝ`, 目标非零: 输出 `ĉᴸ` (`mkĉ`).
- 尾巴非零层的 `ŝ`, 目标非零: 输出目标层的 `ŝ`, 支配 $c\sqsubseteq^\mathsf I2$ 原样 (目标层与尾巴层的种类都是 `false`).

```agda
mkĉ : ∀ {ℓ c} {t₀ : Ordˢ zero} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ zero} {o₀ : Ordˢ ℓ} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} →
      Good t₀ → (∀ η e → Good (g η e)) → (∀ η e → t₀ ⊑ᵒ g η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → g η e ⊑ᵒ g η′ e′) →
      Dom zero c t₀ g → Good o₀ → (∀ η e → Good (o η e)) →
      (∀ η e → o₀ ⊑ᵒ o η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → o η e ⊑ᵒ o η′ e′) →
      Good (Ord₊ˢ.ĉᴸ c (toZ t₀) (λ η e → toZ (g η e)) o₀ o)
mkĉ g0 gg m mm (d₀ , dE) go gO mo mO =
  bĉ G₀ Gg (d₀ G₀) (λ η e → dE η e (Gg η e))
     (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
     go gO mo mO
  where
  G₀ = Good→Goodᶻ g0
  Gg = λ η e → Good→Goodᶻ (gg η e)

Ok-pen : ∀ {i j k} {x : Ordˢ k} → j <ᴵ i → Ok i x
Ok-pen {i = suc _}   r = tt
Ok-pen {i = lim _ _} r = tt

Good-ψ0 : ∀ {i k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {x : Ordˢ k} → Good x → x ≅ˢ x → Ok i x → Good (ψ0 p σ x)
chain0-good : ∀ {j k ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
              (∀ (z : Ordˢ j) → z ≅ˢ z → Gd j (<→◃ q) (intoˢ (<→◃ q) z) → Good (f (intoˢ (<→◃ q) z))) →
              Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → (∀ n → Ok j (f (intoˢ (<→◃ q) (chain0 σ q f n)))) →
              ∀ n → Good (chain0 σ q f n)
chain0-good {j} hb e ok zero = Good-Ω j
chain0-good {σ = σ} {q = q} {f = f} hb e ok (suc n) =
  Good-ψ0 (hb (chain0 σ q f n) (chain0-≅ e n) (Good→Gd (<→◃ q) (chain0-good hb e ok n))) (i-respˢ e (chain0-≅ e n)) (ok n)

Good-ψ0 {i} bz ex ok = Good-Ω i
Good-ψ0 {i} {p = p} {σ = σ} (bs g) ex ok = bl (Good-iter (Good-ψ0 g ea (Ok-suc i ok)) eψ) (rule4ᵒ eψ)
  where ea = s-invˢ ex
        eψ = ψ0-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} (≅ᴵ-refl i) ea
Good-ψ0 {i} (bl hg st) ex ok = bl (λ n → Good-ψ0 (hg n) (l-invˢ ex n) (Ok-lim i ok n)) (λ n → ψ0-cong (st n))
Good-ψ0 {i} {p = p} {σ = σ} (bi {j = j} {p = q} {f = f} hb hm) ex ok with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = bi
  (λ z ez g → subst (λ u → Good (ψ0 p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))))) (sym (out-intoˢ (<→◃ r) z))
                    (Good-ψ0 (hb (tr⁻ˢ e z) (self-tr⁻ˢ e ez) (Good→Gd (<→◃ q) (Good-tr⁻ e (Gd→Good (<→◃ r) g))))
                             (i-respˢ ex (self-tr⁻ˢ e ez)) (Ok-pen r)))
  (λ {z} {z′} h → subst₂ (λ u v → ψ0 p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ⊑ᵒ ψ0 p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e v))))
                         (sym (out-intoˢ (<→◃ r) z)) (sym (out-intoˢ (<→◃ r) z′)) (ψ0-cong (hm (tr⁻-cong h))))
... | injᵇ c = bl (λ n → Good-ψ0 (hb (chain0 σ q f n) (chain0-≅ ex n)
                                       (Good→Gd (<→◃ q) (chain0-good hb ex (λ m → proj₁ (Ok-col σ (inj₁ c) ok m)) n)))
                                  (i-respˢ ex (chain0-≅ ex n)) (proj₂ (Ok-col σ (inj₁ c) ok n)))
                  (λ n → ψ0-cong (hm (chain0-step ex hm n)))
... | injᶜ c = bl (λ n → Good-ψ0 (hb (chain0 σ q f n) (chain0-≅ ex n)
                                       (Good→Gd (<→◃ q) (chain0-good hb ex (λ m → proj₁ (Ok-col σ (inj₂ c) ok m)) n)))
                                  (i-respˢ ex (chain0-≅ ex n)) (proj₂ (Ok-col σ (inj₂ c) ok n)))
                  (λ n → ψ0-cong (hm (chain0-step ex hm n)))
Good-ψ0 {i} (bu {r = zero} g) ex ok   = Good-ψ0 g (u-reflˢ zero ex) (Ok-up i zero ok)
Good-ψ0 {i} (bu {r = self n} g) ex ok = Good-ψ0 g (u-reflˢ (self n) ex) (Ok-up i (self n) ok)
Good-ψ0 {i = zero} (bŝ g0 gg et eg m mm dm) ex (_ , _ , d) = ⊥-elim (~ŝ d)
Good-ψ0 {i = suc _} {k = zero} (bŝ g0 gg et eg m mm dm) ex ok =
  mkĉ g0 gg m mm dm (Good-ψ0 g0 et tt) (λ η e → Good-ψ0 (gg η e) (eg η e η e (≅ᴵ-refl η)) tt)
      (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h))
Good-ψ0 {i = lim _ _} {k = zero} (bŝ g0 gg et eg m mm dm) ex ok =
  mkĉ g0 gg m mm dm (Good-ψ0 g0 et tt) (λ η e → Good-ψ0 (gg η e) (eg η e η e (≅ᴵ-refl η)) tt)
      (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h))
Good-ψ0 {i = suc _} {k = suc _} (bŝ g0 gg et eg m mm dm) ex ok =
  bŝ (Good-ψ0 g0 et tt) (λ η e → Good-ψ0 (gg η e) (eg η e η e (≅ᴵ-refl η)) tt)
     (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h)) dm
Good-ψ0 {i = suc _} {k = lim _ _} (bŝ g0 gg et eg m mm dm) ex ok =
  bŝ (Good-ψ0 g0 et tt) (λ η e → Good-ψ0 (gg η e) (eg η e η e (≅ᴵ-refl η)) tt)
     (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h)) dm
Good-ψ0 {i = lim _ _} {k = suc _} (bŝ g0 gg et eg m mm dm) ex ok =
  bŝ (Good-ψ0 g0 et tt) (λ η e → Good-ψ0 (gg η e) (eg η e η e (≅ᴵ-refl η)) tt)
     (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h)) dm
Good-ψ0 {i = lim _ _} {k = lim _ _} (bŝ g0 gg et eg m mm dm) ex ok =
  bŝ (Good-ψ0 g0 et tt) (λ η e → Good-ψ0 (gg η e) (eg η e η e (≅ᴵ-refl η)) tt)
     (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h)) dm
Good-ψ0 {i = zero} (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex (_ , _ , d) = ⊥-elim (~ĉ d)
Good-ψ0 {i = suc _} (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex ok =
  bĉ G₀ Gg d₀ dE m₀ mE (Good-ψ0 go (ĉ-refl₀ ex) tt) (λ η e → Good-ψ0 (gO η e) (ĉ-reflg ex η e) tt)
     (λ η e → ψ0-cong (mo η e)) (λ η e η′ e′ h → ψ0-cong (mO η e η′ e′ h))
Good-ψ0 {i = lim _ _} (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex ok =
  bĉ G₀ Gg d₀ dE m₀ mE (Good-ψ0 go (ĉ-refl₀ ex) tt) (λ η e → Good-ψ0 (gO η e) (ĉ-reflg ex η e) tt)
     (λ η e → ψ0-cong (mo η e)) (λ η e η′ e′ h → ψ0-cong (mO η e η′ e′ h))
```

**读法.** 停机: 对 `Good` 推导结构递归, `chain0-good` 只把 `hb` (推导的字段) 用在链点上, 与 Uniform 同, 一次通过.

## §4 严格性引理

**`Strict₀`.** 空栈、目标 0: `B1₀` 在观测 `idO` 下给出 $1=\Omega_0\sqsubseteq\psi^{[]}_0(y)$ 的计值, `toLevel-⊑` 变成层号.

**弹栈闭包.** 目标层 $i$、单 $\hat\Omega$ 帧、尾巴 0 的折叠字面就是 `ŝ (suc i) (t₀pop p z) (gpop p z)` (`refl`): 第 0 点 $\psi^{[]}_i(\Omega_1)$ (在 $i+1$ 上), 在 $\eta$ 处 $\psi^{[]}_i(\Omega_\eta)$ (在 `Mlev (suc i) η e` 上). `popGood`: 好性由 `Good-ψ0` (输入 $\Omega$ 无符号), 单调由 `Ω-monoᵒ` ($1\sqsubseteq^\mathsf I i+1$ 用 `z<suc` 给的字面证明, 不能假设 $0<^\mathsf I i$), 支配 `popDom`: $i=0$ 时由 `Strict₀` (界 1), $i\ne0$ 时由 $i<^\mathsf I\ell\sqsubseteq^\mathsf I2$ 得 $i+1\sqsubseteq^\mathsf I2$ (**前提 $\ell\sqsubseteq^\mathsf I2$ 的第一处用法**).

```agda
Strict₀ : ∀ {L k} {p : zero <ᴵ L} {σ : Simᴵ k L} (y : Ordˢ k) → y ≅ˢ y → (G : Goodᶻ (toZ (ψ0 p σ y))) →
          suc zero ⊑ᴵ toLevel (force _ G) (force-HS _ G)
Strict₀ {p = p} {σ = σ} y ey G =
  toLevel-⊑ (hs hz) (force-HS _ G) (B1₀ {q = p} {σ = σ} (≅→⊑ᵒ (Ωˢ-refl zero)) y ey idO (Goodᶻ.gs Goodᶻ.gz) G)

t₀pop : ∀ {i ℓ} → i <ᴵ ℓ → zero <ᴵ ℓ → Ordˢ i
t₀pop {i} p z = ψ0 {ℓ = suc i} zero (σ1 (z<suc z p)) (Ωˢ (suc zero))

gpop : ∀ {i ℓ} → i <ᴵ ℓ → zero <ᴵ ℓ → (η : Ordᴵ) → suc i ⊑ᴵ η → Ordˢ i
gpop {i} p z η e = ψ0 {ℓ = Mlev (suc i) η e} (lim 0 zero) (λ q → lim 1 q) (Ωˢ η)

_ : ∀ {i k ℓ} (p : i <ᴵ ℓ) (σ : Simᴵ k ℓ) (z : zero <ᴵ ℓ) → ψ1 p σ z Ord₊ˢ.zero ≡ Ord₊ˢ.ŝ (suc i) (t₀pop p z) (gpop p z)
_ = λ p σ z → refl

popGood : ∀ {i k ℓ} (p : i <ᴵ ℓ) (σ : Simᴵ k ℓ) (z : zero <ᴵ ℓ) → Dom i (suc i) (t₀pop p z) (gpop p z) →
          Good (ψ1 p σ z Ord₊ˢ.zero)
popGood {i} p σ z dm =
  bŝ (Good-ψ0 (Good-Ω (suc zero)) (Ωˢ-refl (suc zero)) (Ok-Pl i (Pl-Ω (suc zero))))
     (λ η e → Good-ψ0 (Good-Ω η) (Ωˢ-refl η) (Ok-Pl i (Pl-Ω η)))
     (ψ0-≅ (≅ᴵ-refl i) (Ωˢ-refl (suc zero))) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl i) (Ωˢ-≅ eη))
     (λ η e → ψ0-cong (Ω-monoᵒ (⊑ᴵ-trans (s⊑ z≅ (z<suc z p)) e))) (λ η e η′ e′ h → ψ0-cong (Ω-monoᵒ h)) dm

popDom₀ : ∀ {ℓ} (p : zero <ᴵ ℓ) (z : zero <ᴵ ℓ) → Dom zero (suc zero) (t₀pop p z) (gpop p z)
popDom₀ p z = (λ G → Strict₀ (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)) G) , (λ η e G → Strict₀ (Ωˢ η) (Ωˢ-refl η) G)

popDom : ∀ {i ℓ} (p : i <ᴵ ℓ) (z : zero <ᴵ ℓ) → ℓ ⊑ᴵ two → Dom i (suc i) (t₀pop p z) (gpop p z)
popDom {i = zero}    p z h = popDom₀ p z
popDom {i = suc _}   p z h = s⊑′ (sim h p)
popDom {i = lim _ _} p z h = s⊑′ (sim h p)
```

**`Strict₁`.** 单 $\hat\Omega$ 栈、目标 0, 任意自反尾巴 $y$、任意证书: 层号 $\sqsupseteq^\mathsf I2$. 步骤:

1. `one≺`: $\psi^{[]}_0(\Omega_1)$ 在任意证书下计值 $\succ1$. 观测证明: `up zero 1` $\sqsubseteq^\mathsf o\Omega_1$ (`limᵢ-r`), 经观测 $\psi_0$ 得 $\psi_0(1)$ 的计值 $\sqsubseteq$ 目标, 而 $\psi_0(1)=\lim(0,1,2,\ldots)$ 的第 2 项是 `suc (suc zero)` (`one≺ω`).
2. `onepop`: 弹栈闭包的计值是 $\lim$ `outs`, 第 0 项是上面的 $\psi^{[]}_0(\Omega_1)$.
3. `B1₁` (假设由 `ψ1-≅` 给出) 把弹栈闭包推到任意尾巴, `two⊑` 把 $1\prec X$ 变成 $2\sqsubseteq X$ (`≺→⊑` 处理 $c\prec1$).

**否定 (编译报错).** 第 1 步最初直接对派发 `with <ᴵ-dec (σ zero) p` 再匹配证书, 报

    [UnequalTerms] w != <ᴵ-dec (σ zero) p of type zero ≺ᴵ zero ⊎ zero ≺ᴵ zero ⊎ zero ≅ᴵ zero
    when checking that the type … (G : Goodᶻ (toZ (ψᴾ 0 p σ [] (Ord₊ˢ.limᵢ zero (Ord₊ˢ.up zero)) | w))) → …
    of the generated with function is well-formed

(Prefix 的 `ψᴾ` 的 `with` 辅助函数不能在这里被抽象), 改为上面的观测证明. 另一个工程注记: `suc zero ≺ X` 的左端层号不定, 报 `[SplitError.UnificationStuck] … {ℓ₂} ≟ {_ℓ₁_13990}`, 用标注了层号的 `one⁰`/`two⁰` 即过.

```agda
one⁰ two⁰ : Ordᶜ zero
one⁰ = suc zero
two⁰ = suc one⁰

two⊑ : ∀ {X : Ordᶜ zero} → one⁰ ≺ X → two⁰ ⊑ X
two⊑ h (≺z e)  = ≺-respˡ (≅-sym e) h
two⊑ h (≺s h′) = ≺→⊑ h h′

h2 : (G : Goodᶻ (Z.suc (Z.suc Z.zero))) → one⁰ ≺ force _ G
h2 (Goodᶻ.gs (Goodᶻ.gs Goodᶻ.gz)) = ≺z (s≅ z≅)

one≺ω : (G : Goodᶻ (toZ {- ψ₀(1) -} (Ord₊ˢ.lim (iter (Ord₊ˢ.suc Ord₊ˢ.zero +ˢ_) Ord₊ˢ.zero)))) → one⁰ ≺ force _ G
one≺ω (Goodᶻ.gl Gs st) = ≺l 2 (h2 (Gs 2))

lim0≺ : ∀ {F : ℕ → Ordˢ zero} → (∀ (G : Goodᶻ (toZ (F 0))) → one⁰ ≺ force _ G) →
        (G : Goodᶻ (toZ (Ord₊ˢ.lim F))) → one⁰ ≺ force _ G
lim0≺ h (Goodᶻ.gl Gs st) = ≺l 0 (h (Gs 0))

one≺ : ∀ {L} {p : zero <ᴵ L} (σ : Simᴵ (suc zero) L) (G : Goodᶻ (toZ (ψ0 p σ (Ωˢ (suc zero))))) → one⁰ ≺ force _ G
one≺ {p = p} σ G = le idO G₁ G (one≺ω G₁)
  where
  u : Ordˢ (suc zero)
  u = Ord₊ˢ.up zero (Ord₊ˢ.suc Ord₊ˢ.zero)
  u⊑ : u ⊑ᵒ Ωˢ (suc zero)
  u⊑ = limᵢ-r (λ z d → up-l {r = zero} (up-r {r = zero} {y = z} (≅→⊑ᵒ (≅ˢ-sym d))))
  le : ψ0 p σ u ⊑ᵒ ψ0 p σ (Ωˢ (suc zero))
  le = ψ0-cong {p = p} {p′ = p} {σ = σ} {σ′ = σ} u⊑
  G₁ : Goodᶻ (toZ (ψ0 p σ u))
  G₁ = Good→Goodᶻ (Good-ψ0 (bu (bs bz)) (upˡ (upʳ (s≅ z≅))) (zero , one⁰ , H₊.upˡ (H₊.s~ H₊.z~)))

onepop : ∀ {L k} (p : zero <ᴵ L) (σ : Simᴵ k L) (z : zero <ᴵ L) (G : Goodᶻ (toZ (ψ1 p σ z Ord₊ˢ.zero))) → one⁰ ≺ force _ G
onepop p σ z (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) = ≺l 0 (one≺ (σ1 (z<suc z p)) Go₀)

Strict₁ : ∀ {L k} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} (y : Ordˢ k) → y ≅ˢ y → (G : Goodᶻ (toZ (ψ1 p σ z y))) →
          two ⊑ᴵ toLevel (force _ G) (force-HS _ G)
Strict₁ {k = k} {p = p} {σ = σ} {z = z} y ey G =
  toLevel-⊑ (hs (hs hz)) (force-HS _ G)
            (two⊑ (B1₁ {q = p} {σ = σ} {z₁ = z} {x = ψ1 p σ z (𝟎ˢ {k})}
                       (≅→⊑ᵒ (ψ1-≅ {k₁ = k} {k₂ = k} {p = p} {σ = σ} {p′ = p} {σ′ = σ} {z = z} {z′ = z} (≅ᴵ-refl zero) z≅))
                       y ey idO G₀ G (onepop p σ z G₀)))
  where G₀ = Good→Goodᶻ (popGood p σ z (popDom₀ p z))
```

## §5 单 $\hat\Omega$ 栈的闭包定理

`Dom-ψ1`: 非零层的 `ŝ` (界 $c\sqsubseteq^\mathsf I2$) 被单 $\hat\Omega$ 栈、目标 0 的折叠映到第 0 层, 新链的链点是 $\psi^{[\hat\Omega]}_0(t_0)$ 与 $\psi^{[\hat\Omega]}_0(g\,\eta\,e)$, 支配由 `Strict₁` 与 $c\sqsubseteq^\mathsf I2$ 复合 (**前提 $\ell\sqsubseteq^\mathsf I2$ 的第二处用法**, 经输入的 `Dom`). 这就是 Prefix §8 (b) 要的 "$\psi_\delta$ 出现在链点里 $\Rightarrow\delta\prec^\mathsf I$ 链点的层号", 在 $\delta\le1$ 时的树版本.

**定理 `Good-ψ1`.** 前提: 环境层号 $\ell\sqsubseteq^\mathsf I2$; 输入好且自反. 结论: $\psi^{[\hat\Omega]}_i(x)$ 好, 对任意目标层 $i<^\mathsf I\ell$、任意 `Sim`、任意帧证据 $z:0<^\mathsf I\ell$. 情况: 弹栈 (`popGood`/`popDom`); 后继/极限/`up`/穿透/折叠同 `Good-ψ0` (折叠的链点带同一个栈, `chain1-good` 互递归); 尾巴 `ŝ`: 第 0 层 → `mkĉ`, 非零层且目标 0 → `Dom-ψ1`, 非零层且目标非零 → 支配原样; 尾巴 `ĉᴸ` → 输出逐点. 弹栈的两个递归调用落在 `Good-ψ0` (栈已空, 输入 $\Omega_1$, $\Omega_\eta$ 无符号), 所以长度 1 的栈不需要关于 `Mlev` 的任何前提.

```agda
Dom-ψ1 : ∀ {L k c} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} →
         c ⊑ᴵ two → t₀ ≅ˢ t₀ → (∀ η e → g η e ≅ˢ g η e) →
         Dom zero c (ψ1 p σ z t₀) (λ η e → ψ1 p σ z (g η e))
Dom-ψ1 {t₀ = t₀} {g = g} dm et eg =
  (λ G → ⊑ᴵ-trans dm (Strict₁ t₀ et G)) , (λ η e G → ⊑ᴵ-trans dm (Strict₁ (g η e) (eg η e) G))

Good-ψ1 : ∀ {i k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {x : Ordˢ k} → ℓ ⊑ᴵ two → Good x → x ≅ˢ x →
          Good (ψ1 p σ z x)
chain1-good : ∀ {j k ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} → ℓ ⊑ᴵ two →
              (∀ (y : Ordˢ j) → y ≅ˢ y → Gd j (<→◃ q) (intoˢ (<→◃ q) y) → Good (f (intoˢ (<→◃ q) y))) →
              Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → ∀ n → Good (chain1 σ z q f n)
chain1-good {j} h hb e zero = Good-Ω j
chain1-good {σ = σ} {z = z} {q = q} {f = f} h hb e (suc n) =
  Good-ψ1 h (hb (chain1 σ z q f n) (chain1-≅ e n) (Good→Gd (<→◃ q) (chain1-good h hb e n))) (i-respˢ e (chain1-≅ e n))

Good-ψ1 {p = p} {σ = σ} {z = z} h bz ex = popGood p σ z (popDom p z h)
Good-ψ1 {i} {p = p} {σ = σ} {z = z} h (bs g) ex = bl (Good-iter (Good-ψ1 h g ea) eψ) (rule4ᵒ eψ)
  where ea = s-invˢ ex
        eψ = ψ1-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} {z = z} {z′ = z} (≅ᴵ-refl i) ea
Good-ψ1 h (bl hg st) ex = bl (λ n → Good-ψ1 h (hg n) (l-invˢ ex n)) (λ n → ψ1-cong (st n))
Good-ψ1 {p = p} {σ = σ} {z = z} h (bi {j = j} {p = q} {f = f} hb hm) ex with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = bi
  (λ y ey g → subst (λ u → Good (ψ1 p σ z (f (intoˢ (<→◃ q) (tr⁻ˢ e u))))) (sym (out-intoˢ (<→◃ r) y))
                    (Good-ψ1 h (hb (tr⁻ˢ e y) (self-tr⁻ˢ e ey) (Good→Gd (<→◃ q) (Good-tr⁻ e (Gd→Good (<→◃ r) g))))
                               (i-respˢ ex (self-tr⁻ˢ e ey))))
  (λ {y} {y′} hy → subst₂ (λ u v → ψ1 p σ z (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ⊑ᵒ ψ1 p σ z (f (intoˢ (<→◃ q) (tr⁻ˢ e v))))
                          (sym (out-intoˢ (<→◃ r) y)) (sym (out-intoˢ (<→◃ r) y′)) (ψ1-cong (hm (tr⁻-cong hy))))
... | injᵇ _ = bl (λ n → Good-ψ1 h (hb (chain1 σ z q f n) (chain1-≅ ex n) (Good→Gd (<→◃ q) (chain1-good h hb ex n)))
                                    (i-respˢ ex (chain1-≅ ex n)))
                  (λ n → ψ1-cong (hm (chain1-step ex hm n)))
... | injᶜ _ = bl (λ n → Good-ψ1 h (hb (chain1 σ z q f n) (chain1-≅ ex n) (Good→Gd (<→◃ q) (chain1-good h hb ex n)))
                                    (i-respˢ ex (chain1-≅ ex n)))
                  (λ n → ψ1-cong (hm (chain1-step ex hm n)))
Good-ψ1 h (bu {r = zero} g) ex   = Good-ψ1 h g (u-reflˢ zero ex)
Good-ψ1 h (bu {r = self n} g) ex = Good-ψ1 h g (u-reflˢ (self n) ex)
Good-ψ1 {i = zero} {k = zero} h (bŝ g0 gg et eg m mm dm) ex =
  mkĉ g0 gg m mm dm (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
      (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh))
Good-ψ1 {i = suc _} {k = zero} h (bŝ g0 gg et eg m mm dm) ex =
  mkĉ g0 gg m mm dm (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
      (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh))
Good-ψ1 {i = lim _ _} {k = zero} h (bŝ g0 gg et eg m mm dm) ex =
  mkĉ g0 gg m mm dm (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
      (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh))
Good-ψ1 {i = zero} {k = suc _} h (bŝ g0 gg et eg m mm dm) ex =
  bŝ (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh))
     (Dom-ψ1 dm et (λ η e → eg η e η e (≅ᴵ-refl η)))
Good-ψ1 {i = zero} {k = lim _ _} h (bŝ g0 gg et eg m mm dm) ex =
  bŝ (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh))
     (Dom-ψ1 dm et (λ η e → eg η e η e (≅ᴵ-refl η)))
Good-ψ1 {i = suc _} {k = suc _} h (bŝ g0 gg et eg m mm dm) ex =
  bŝ (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh)) dm
Good-ψ1 {i = suc _} {k = lim _ _} h (bŝ g0 gg et eg m mm dm) ex =
  bŝ (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh)) dm
Good-ψ1 {i = lim _ _} {k = suc _} h (bŝ g0 gg et eg m mm dm) ex =
  bŝ (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh)) dm
Good-ψ1 {i = lim _ _} {k = lim _ _} h (bŝ g0 gg et eg m mm dm) ex =
  bŝ (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh)) dm
Good-ψ1 h (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex =
  bĉ G₀ Gg d₀ dE m₀ mE (Good-ψ1 h go (ĉ-refl₀ ex)) (λ η e → Good-ψ1 h (gO η e) (ĉ-reflg ex η e))
     (λ η e → ψ1-cong (mo η e)) (λ η e η′ e′ hh → ψ1-cong (mO η e η′ e′ hh))
```

## §6 检验 1: $\psi_0(\Omega_\Omega+\Omega_2)$ 的计值树

$X_2$ = `ψᴾ 1 z2 id (fΩ̂ z2 ∷ []) (Ωˢ 2)` (Prefix 的 `X₂ˢ`, 环境层号 2). 证书由 `Good-ψ1` (前提 `⊑ᴵ-refl`) 与 `Good→Goodᶻ` 给出.

```agda
X₂-good : Good X₂ˢ
X₂-good = Good-ψ1 {p = z2} {σ = λ q → q} {z = z2} ⊑ᴵ-refl (Good-Ω two) (Ωˢ-refl two)

GX₂ : Goodᶻ (toZ X₂ˢ)
GX₂ = Good→Goodᶻ X₂-good

X₂ᶠ : Ordᶜ zero
X₂ᶠ = force (toZ X₂ˢ) GX₂

isZ : Ordᶜ zero → Bool
isZ zero = true
isZ _    = false

-- Symbolic: walk B0t PB ≡ zero (静态前缀); 同一路径在计值树上非零
_ : isZ (walk X₂ᶠ (2 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ [])) ≡ false
_ = refl
```

**读法.** `GX₂` 是 Prefix §8 缺的 "第一个实例" (含 $A$ 的闭包, 界 2) 及其全部后代的证书. 路径 `2 ∷ 0 ∷ 1 ∷ 0 ∷ PB` 是 Symbolic 的 `B0-unlabel` 的路径 ($B=X_2[2][0][1]$, $B[0]$, 再走 `PB`): 静态前缀的树在终点是 `zero`; 计值树在 $B[0][0][0]$ 处是界为 2 的待计值链 (Prefix `kind … ≡ kc two`), 它的第 1 项是在第 0 个链点的层号处计值的分支, 终点非零 (`refl`, 约 4 秒). 记号侧的终点是 $\psi_0(\Omega_\Omega)$ (Symbolic `A-end`); 计值树的终点是一个目标 0 的弹栈闭包, 由 §7 的 `pop0≅` 它 $\cong$ BTBO, 但 "终点字面是哪一个弹栈闭包" 要写出它所在的环境层号与 `Sim`, 本文没有写, 只编译了非零性.

## §7 计值与加法、目标 0 的弹栈闭包

**`fadd`.** 第 0 层的好树 $a,b$: `force (toZ (a +ˢ b)) G ≅ force a + force b` (证书任意; 右端用 `Good→Goodᶻ` 的证书). 尾巴是 `ŝ`/`ĉᴸ` 时左边是以 $a+o$ 为输出的链, 右边是 $a$ 加上链的极限; 两条链的证书不同, 链点由 `chain≅` 对上 (`outsMap`: 输出逐项与 $F(\text{另一组输出})$ 相关).

```agda
outsMap : (C C′ : Ctx) → Ctx.t₀ C ≅ Ctx.t₀ C′ → (∀ η e η′ e′ → η ≅ᴵ η′ → Ctx.E C η e ≅ Ctx.E C′ η′ e′) →
          ∀ {O₀ O} {P₀ : Ordᶜ zero} {P : (η : Ordᴵ) → Ctx.c C′ ⊑ᴵ η → Ordᶜ zero} (F : Ordᶜ zero → Ordᶜ zero) →
          O₀ ≅ F P₀ → (∀ η e η′ e′ → η ≅ᴵ η′ → O η e ≅ F (P η′ e′)) →
          ∀ n → outs C O₀ O n ≅ F (outs C′ P₀ P n)
outsMap C C′ h₀ hE F o₀ hO zero    = o₀
outsMap C C′ h₀ hE F o₀ hO (suc k) =
  hO _ _ _ _ (toLevel-≅ (Pt.hx (Γᶜ C k)) (Pt.hx (Γᶜ C′ k)) (chain≅ C C′ h₀ hE k))

fadd : ∀ {a b : Ordˢ zero} (ga : Good a) → a ≅ˢ a → (gb : Good b) → b ≅ˢ b → (G : Goodᶻ (toZ (a +ˢ b))) →
       force _ G ≅ force _ (Good→Goodᶻ ga) + force _ (Good→Goodᶻ gb)
fadd ga ea bz eb G = force-≅ (toZ-≅ ea) G (Good→Goodᶻ ga)
fadd ga ea (bs gb) eb (Goodᶻ.gs G) = s≅ (fadd ga ea gb (s-invˢ eb) G)
fadd ga ea (bl hg st) eb (Goodᶻ.gl G _) = l≅ (λ n → fadd ga ea (hg n) (l-invˢ eb n) (G n))
fadd ga ea (bi {p = ()} hb hm) eb G
fadd ga ea (bu {r = ()} g) eb G
fadd {a = a} ga ea (bŝ {c = c} {t₀ = t₀} {g = g} g0 gg et eg m mm (d₀ , dE)) eb
     (Goodᶻ.gc G₀ Gg d₀′ dE′ m₀′ mE′ Go₀ Go mo₀ mo) =
  l≅ (outsMap C C′ (force-≅ (toZ-≅ et) G₀ (Good→Goodᶻ g0))
              (λ η e η′ e′ eη → force-≅ (toZ-≅ (eg η e η′ e′ eη)) (Gg η e) (Good→Goodᶻ (gg η′ e′)))
              (λ X → force _ (Good→Goodᶻ ga) + X)
              (fadd ga ea g0 et Go₀)
              (λ η e η′ e′ eη → ≅-trans (fadd ga ea (gg η e) (eg η e η e (≅ᴵ-refl η)) (Go η e))
                                        (add-≅ (≅-refl⁰ _) (force-≅ (toZ-≅ (eg η e η′ e′ eη)) (Good→Goodᶻ (gg η e)) (Good→Goodᶻ (gg η′ e′))))))
  where
  C : Ctx
  C = record { c = c ; t₀ = force (toZ t₀) G₀ ; E = λ η e → force (toZ (g η e)) (Gg η e)
             ; h₀ = force-HS _ G₀ ; hE = λ η e → force-HS _ (Gg η e) ; d₀ = d₀′ ; dE = dE′ ; m₀ = m₀′ ; mE = mE′ }
  G₀′ = Good→Goodᶻ g0
  Gg′ = λ η e → Good→Goodᶻ (gg η e)
  C′ : Ctx
  C′ = record { c = c ; t₀ = force (toZ t₀) G₀′ ; E = λ η e → force (toZ (g η e)) (Gg′ η e)
              ; h₀ = force-HS _ G₀′ ; hE = λ η e → force-HS _ (Gg′ η e) ; d₀ = d₀ G₀′ ; dE = λ η e → dE η e (Gg′ η e)
              ; m₀ = λ η e → m η e idO G₀′ (Gg′ η e) ; mE = λ η e η′ e′ h → mm η e η′ e′ h idO (Gg′ η e) (Gg′ η′ e′) }
fadd {a = a} ga ea (bĉ {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} G₀ Gg d₀ dE m₀ mE go gO mo mO) eb
     (Goodᶻ.gc G₀′ Gg′ d₀′ dE′ m₀′ mE′ Go₀ Go mo₀ mo′) =
  l≅ (outsMap C′ C (force-≅ (≅ᶻ-refl₀ eb) G₀′ G₀)
              (λ η e η′ e′ eη → force-≅ (≅ᶻ-reflg eb η e η′ e′ eη) (Gg′ η e) (Gg η′ e′))
              (λ X → force _ (Good→Goodᶻ ga) + X)
              (fadd ga ea go (ĉ-refl₀ eb) Go₀)
              (λ η e η′ e′ eη → ≅-trans (fadd ga ea (gO η e) (ĉ-reflg eb η e) (Go η e))
                                        (add-≅ (≅-refl⁰ _) (force-≅ (toZ-≅ (ĉ-reflO eb η e η′ e′ eη)) (Good→Goodᶻ (gO η e)) (Good→Goodᶻ (gO η′ e′))))))
  where
  C : Ctx
  C = record { c = c ; t₀ = force t₀ G₀ ; E = λ η e → force (g η e) (Gg η e)
             ; h₀ = force-HS _ G₀ ; hE = λ η e → force-HS _ (Gg η e) ; d₀ = d₀ ; dE = dE ; m₀ = m₀ ; mE = mE }
  C′ : Ctx
  C′ = record { c = c ; t₀ = force t₀ G₀′ ; E = λ η e → force (g η e) (Gg′ η e)
              ; h₀ = force-HS _ G₀′ ; hE = λ η e → force-HS _ (Gg′ η e) ; d₀ = d₀′ ; dE = dE′ ; m₀ = m₀′ ; mE = mE′ }
```

**`pop0≅`.** 目标 0、单 $\hat\Omega$ 帧、尾巴 0 的折叠, 在**任意**环境层号、任意 `Sim`、任意证书下计值 $\cong$ `BTBOᴵ`. 证明照 Prefix 的 `βˢ≅` (那里只对环境层号 2 的 `β₀`): 链点经 `empty-agree` 化为 $\psi^0(\Omega_\eta)$, 层号经 `toLevel-≅` 与 NoCumsum 的 $\gamma$ 对上.

```agda
pop0≅ : ∀ {L k} (p : zero <ᴵ L) (σ : Simᴵ k L) (z : zero <ᴵ L) (G : Goodᶻ (toZ (ψ1 p σ z Ord₊ˢ.zero))) →
        force _ G ≅ N.BTBOᴵ
pop0≅ p σ z (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) = l≅ outs≅′
  where
  C : Ctx
  C = record { c = suc zero ; t₀ = force (toZ (t₀pop p z)) G₀ ; E = λ η e → force (toZ (gpop p z η e)) (Gg η e)
             ; h₀ = force-HS _ G₀ ; hE = λ η e → force-HS _ (Gg η e) ; d₀ = d₀ ; dE = dE ; m₀ = m₀ ; mE = mE }
  ag₀ : ∀ G → force (toZ (t₀pop p z)) G ≅ ψ⁰ (Ω (suc zero))
  ag₀ G = empty-agree zero (σ1 (z<suc z p)) G
  agβ : ∀ η e G → force (toZ (gpop p z η e)) G ≅ ψ⁰ (Ω η)
  agβ η e G = empty-agree (lim 0 zero) (λ q → lim 1 q) G
  pts : ∀ k → Pt.x (Γᶜ C k) ≅ N.γ (suc k)
  pts zero    = ag₀ G₀
  pts (suc k) = ≅-trans (agβ _ _ (Gg _ _)) (ψ⁰-≅ (Ω-≅ (toLevel-≅ (Pt.hx (Γᶜ C k)) (N.cert (suc k)) (pts k))))
  outs≅′ : ∀ n → outs C (force (toZ (t₀pop p z)) Go₀) (λ η e → force (toZ (gpop p z η e)) (Go η e)) n ≅ N.γ (suc n)
  outs≅′ zero    = ag₀ Go₀
  outs≅′ (suc k) = ≅-trans (agβ _ _ (Go _ _)) (ψ⁰-≅ (Ω-≅ (toLevel-≅ (Pt.hx (Γᶜ C k)) (N.cert (suc k)) (pts k))))

pop0-label : ∀ {L k} (p : zero <ᴵ L) (σ : Simᴵ k L) (z : zero <ᴵ L) (G : Goodᶻ (toZ (ψ1 p σ z Ord₊ˢ.zero))) →
             Lab (force _ G) (E.EBOψ 2)
pop0-label p σ z G = Lab-≅ (pop0≅ p σ z G) BTBO-label
```

## §8 静态前缀桥与新树上的标签

**`brg`.** 尾巴 $Y$ 在第 0 层 (可数) 时, 符号前缀的计值与 Stage2 的静态前缀一致:

$$\mathtt{force}(\psi^{[\hat\Omega]}_0(Y))\cong\psi^0(\Omega_{\ell_0}+\mathtt{force}(Y)).$$

对 $Y$ 的 `Good` 推导归纳: 尾巴 0 是 `pop0≅` (右端 $\psi^0(\Omega_{\ell_0})$ 字面就是 `BTBOᴵ`); 后继经 `fadd` 与迭代 (`iter≅`); 极限逐项; `ŝ`/`ĉᴸ` 时两边都是同一条链 (证书不同, `outsMap`). 前提 $L\sqsubseteq^\mathsf I2$ 只为后继情况里 `Good-ψ1` 的调用. 这说明 Stage2 的静态替身在可数尾巴上本来就对, 失败只发生在前缀于 $\psi_\delta$ ($\delta\ge1$) 之下暴露的地方 (Stage2 `X₂-unlabel`).

```agda
σ₀ : Simᴵ zero ℓ₀
σ₀ ()

iter≅ : ∀ {X : Ordˢ zero} {X′ : Ordᶜ zero} → Good X → X ≅ˢ X → (∀ G → force (toZ X) G ≅ X′) →
        ∀ n (G : Goodᶻ (toZ (iter (X +ˢ_) Ord₊ˢ.zero n))) → force _ G ≅ iter (X′ +_) zero n
iter≅ gX eX hX zero    Goodᶻ.gz = z≅
iter≅ {X = X} gX eX hX (suc n) G =
  ≅-trans (fadd gX eX (Good-iter gX eX n) (iter-R _≅ˢ_ {G = X +ˢ_} {G′ = X +ˢ_} (addˢ-≅ refl eX) z≅ n) G)
          (add-≅ (hX (Good→Goodᶻ gX)) (iter≅ gX eX hX n (Good→Goodᶻ (Good-iter gX eX n))))

brg : ∀ {L} {p : zero <ᴵ L} {σ : Simᴵ zero L} {z : zero <ᴵ L} → L ⊑ᴵ two →
      {Y : Ordˢ zero} (gY : Good Y) → Y ≅ˢ Y → (G : Goodᶻ (toZ (ψ1 p σ z Y))) →
      force _ G ≅ ψ⁰ (add (Ω ℓ₀) σ₀ (force _ (Good→Goodᶻ gY)))
brg {p = p} {σ = σ} {z = z} h bz eY G = pop0≅ p σ z G
brg {p = p} {σ = σ} {z = z} h (bs {a = Y′} g) eY (Goodᶻ.gl Gs st) =
  l≅ (λ n → iter≅ (Good-ψ1 h g (s-invˢ eY)) (ψ1-≅ (≅ᴵ-refl zero) (s-invˢ eY)) (λ G → brg h g (s-invˢ eY) G) n (Gs n))
brg h (bl hg st) eY (Goodᶻ.gl Gs _) = l≅ (λ n → brg h (hg n) (l-invˢ eY n) (Gs n))
brg h (bi {p = ()} hb hm) eY G
brg h (bu {r = ()} g) eY G
brg {p = p} {σ = σ} {z = z} h (bŝ {c = c} {t₀ = t₀} {g = g} g0 gg et eg m mm (d₀ , dE)) eY
    (Goodᶻ.gc G₀ Gg d₀′ dE′ m₀′ mE′ Go₀ Go mo₀ mo) =
  l≅ (outsMap C C′ (force-≅ (toZ-≅ et) G₀ G₀′)
              (λ η e η′ e′ eη → force-≅ (toZ-≅ (eg η e η′ e′ eη)) (Gg η e) (Gg′ η′ e′))
              (λ X → ψ⁰ (add (Ω ℓ₀) σ₀ X))
              (brg h g0 et Go₀)
              (λ η e η′ e′ eη → ≅-trans (brg h (gg η e) (eg η e η e (≅ᴵ-refl η)) (Go η e))
                                        (ψ⁰-≅ (add-≅ (Ω-refl ℓ₀) (force-≅ (toZ-≅ (eg η e η′ e′ eη)) (Gg′ η e) (Gg′ η′ e′))))))
  where
  C : Ctx
  C = record { c = c ; t₀ = force (toZ t₀) G₀ ; E = λ η e → force (toZ (g η e)) (Gg η e)
             ; h₀ = force-HS _ G₀ ; hE = λ η e → force-HS _ (Gg η e) ; d₀ = d₀′ ; dE = dE′ ; m₀ = m₀′ ; mE = mE′ }
  G₀′ = Good→Goodᶻ g0
  Gg′ = λ η e → Good→Goodᶻ (gg η e)
  C′ : Ctx
  C′ = record { c = c ; t₀ = force (toZ t₀) G₀′ ; E = λ η e → force (toZ (g η e)) (Gg′ η e)
              ; h₀ = force-HS _ G₀′ ; hE = λ η e → force-HS _ (Gg′ η e) ; d₀ = d₀ G₀′ ; dE = λ η e → dE η e (Gg′ η e)
              ; m₀ = λ η e → m η e idO G₀′ (Gg′ η e) ; mE = λ η e η′ e′ hh → mm η e η′ e′ hh idO (Gg′ η e) (Gg′ η′ e′) }
brg {p = p} {σ = σ} {z = z} h (bĉ {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} G₀ Gg d₀ dE m₀ mE go gO mo mO) eY
    (Goodᶻ.gc G₀′ Gg′ d₀′ dE′ m₀′ mE′ Go₀ Go mo₀ mo′) =
  l≅ (outsMap C′ C (force-≅ (≅ᶻ-refl₀ eY) G₀′ G₀)
              (λ η e η′ e′ eη → force-≅ (≅ᶻ-reflg eY η e η′ e′ eη) (Gg′ η e) (Gg η′ e′))
              (λ X → ψ⁰ (add (Ω ℓ₀) σ₀ X))
              (brg h go (ĉ-refl₀ eY) Go₀)
              (λ η e η′ e′ eη → ≅-trans (brg h (gO η e) (ĉ-reflg eY η e) (Go η e))
                                        (ψ⁰-≅ (add-≅ (Ω-refl ℓ₀) (force-≅ (toZ-≅ (ĉ-reflO eY η e η′ e′ eη))
                                                                           (Good→Goodᶻ (gO η e)) (Good→Goodᶻ (gO η′ e′)))))))
  where
  C : Ctx
  C = record { c = c ; t₀ = force t₀ G₀ ; E = λ η e → force (g η e) (Gg η e)
             ; h₀ = force-HS _ G₀ ; hE = λ η e → force-HS _ (Gg η e) ; d₀ = d₀ ; dE = dE ; m₀ = m₀ ; mE = mE }
  C′ : Ctx
  C′ = record { c = c ; t₀ = force t₀ G₀′ ; E = λ η e → force (g η e) (Gg′ η e)
              ; h₀ = force-HS _ G₀′ ; hE = λ η e → force-HS _ (Gg′ η e) ; d₀ = d₀′ ; dE = dE′ ; m₀ = m₀′ ; mE = mE′ }

Ctxˢ : ∀ {L} {p : zero <ᴵ L} {σ : Simᴵ zero L} {z : zero <ᴵ L} → L ⊑ᴵ two →
       {Y : Ordˢ zero} (gY : Good Y) → Y ≅ˢ Y → ∀ {y} → Lab (force _ (Good→Goodᶻ gY)) y →
       (G : Goodᶻ (toZ (ψ1 p σ z Y))) → Lab (force _ G) (ctx y)
Ctxˢ h gY eY l G = Lab-≅ (brg h gY eY G) (Ctx₀ σ₀ l)
```

**检验 1 的后两项, 在新树上.** $\psi_0(\Omega_\Omega+1)$: `Ctxˢ` 加 Stage2 的 `lab-χ0`. $\psi_0(\Omega_\Omega+\Omega)$: 树在第 0 层节点处折叠, 链点 $\chi_{m+1}=\psi^{[\hat\Omega]}_0(\chi_m)$ 都有可数尾巴, 逐个由 `Ctxˢ` 得到标签 `γT b′ [] m` (`Chain0.chLab`), 外层由 Stage2 的 `fs-χ1` 对齐 (`χ1core`). `χ1core` 对任意环境层号 $\le2$ 与任意 `Sim` 陈述, 所以同一个引理也给出 $X_2$ 的第 0 项 (§9).

```agda
σ00 : Simᴵ zero two
σ00 ()

tsˢ : Ordˢ zero
tsˢ = ψ1 z2 σ00 z2 (Ord₊ˢ.suc Ord₊ˢ.zero)

_ : ctx (natT 1) ≡ ts
_ = refl

tsˢ-good : Goodᶻ (toZ tsˢ)
tsˢ-good = Good→Goodᶻ (Good-ψ1 {p = z2} {σ = σ00} {z = z2} ⊑ᴵ-refl (bs bz) (s≅ z≅))

tsˢ-label : (G : Goodᶻ (toZ tsˢ)) → Lab (force _ G) ts
tsˢ-label G = Ctxˢ ⊑ᴵ-refl (bs bz) (s≅ z≅) lab-χ0 G

module Chain0 {L} (σ : Simᴵ (suc zero) L) (z : zero <ᴵ L) (h : L ⊑ᴵ two) where
  ch : ℕ → Ordˢ zero
  ch = chain1 σ z zero (Ord₊ˢ.up zero)

  eΩ : Ωˢ (suc zero) ≅ˢ Ωˢ (suc zero)
  eΩ = Ωˢ-refl (suc zero)

  gch : ∀ m → Good (ch m)
  gch = chain1-good h (λ y ey g → bu g) eΩ

  ech : ∀ m → ch m ≅ˢ ch m
  ech = chain1-≅ eΩ

  chLab : ∀ m (G : Goodᶻ (toZ (ch m))) → Lab (force _ G) (E.γT b′ [] m)
  chLab zero    (Goodᶻ.gs Goodᶻ.gz) = lab-χ0
  chLab (suc m) G = Ctxˢ h (gch m) (ech m) (chLab m (Good→Goodᶻ (gch m))) G

  χ1core : ∀ (p : zero <ᴵ L) →
           (G : Goodᶻ (toZ (Ord₊ˢ.lim (λ m → ψ1 p σ z (Ord₊ˢ.up zero (ch m)))))) → Lab (force _ G) (γ′ᴱ 1)
  χ1core p (Goodᶻ.gl Gs st) =
    lω refl (l≅ (λ m → ≅-refl⁰ _))
       (λ m → subst (Lab _) (sym (fs-χ1 m)) (Ctxˢ h (gch m) (ech m) (chLab m (Good→Goodᶻ (gch m))) (Gs m)))

one⊑two : suc zero ⊑ᴵ two
one⊑two = s⊑ z≅ (suc zero)

χ1ˢ : Ordˢ zero
χ1ˢ = ψ1 z1 (λ q → q) z1 (Ωˢ (suc zero))

χ1ˢ-label : (G : Goodᶻ (toZ χ1ˢ)) → Lab (force _ G) (γ′ᴱ 1)
χ1ˢ-label G = Chain0.χ1core (λ q → q) z1 one⊑two z1 G
```

**读法.** 两个标签都对**任意**证书成立, 恢复了 Stage2 的 `ts-label`/`χ1-label` (那里是静态前缀的旧树), 但树现在由 $\psi^P$ 产生, 闭包在折叠内部.

## §9 $\psi_0(\Omega_\Omega+\Omega_2)$ 的标签: 第 0 项与停点

证书的投影 `certL` 与 `sq-force` 让我们在不展开 `GX₂` 的情况下谈计值树的基本列. $X_2[0]=\psi_0(\Omega_\Omega+\Omega_1)=\gamma'_1$ (`refl`), 计值树的第 0 项由 `χ1core` 给出标签.

```agda
certL : ∀ {f : ℕ → Z} → Goodᶻ (Z.lim f) → ∀ n → Goodᶻ (f n)
certL (Goodᶻ.gl G st) = G

sq-force : ∀ {f : ℕ → Z} (G : Goodᶻ (Z.lim f)) n → sq (force (Z.lim f) G) n ≡ force (f n) (certL G n)
sq-force (Goodᶻ.gl G st) n = refl

_ : fsn X₂ᵗ 0 ≡ γ′ᴱ 1
_ = refl

X₂-0 : Lab (sq X₂ᶠ 0) (fsn X₂ᵗ 0)
X₂-0 = subst (λ X → Lab X (γ′ᴱ 1)) (sym (sq-force GX₂ 0))
             (Chain0.χ1core (λ q → suc q) z2 ⊑ᴵ-refl z2 (certL GX₂ 0))

force-lim : ∀ {f : ℕ → Z} (G : Goodᶻ (Z.lim f)) → force (Z.lim f) G ≅ lim (λ n → force (f n) (certL G n))
force-lim (Goodᶻ.gl G st) = l≅ (λ n → ≅-refl⁰ _)

X₂-reduce : (∀ n → Lab (sq X₂ᶠ n) (fsn X₂ᵗ n)) → Lab X₂ᶠ X₂ᵗ
X₂-reduce h = lω refl (force-lim GX₂) (λ n → subst (λ X → Lab X (fsn X₂ᵗ n)) (sq-force GX₂ n) (h n))
```

**停点.** `X₂-reduce`: $X_2$ 的标签 ⟸ 一切 $n$ 的第 $n$ 项标签. $n=0$ 是 `X₂-0`. **$n=1$ 未证**, 它是第一个缺口:

```agda
_ : fsn X₂ᵗ 1 ≡ ctx (ψᵗ (natT 1) (ψᵗ Ωᵗ [] ∷ Ωt (natT 1)) ∷ [])
_ = refl

_ : cof (ψᵗ (natT 1) (ψᵗ Ωᵗ [] ∷ Ωt (natT 1)) ∷ []) ≡ cΩ []
_ = refl
```

$X_2[1]=\psi_0(\Omega_\Omega+\psi_1(\Omega_\Omega+\Omega_1))$ 的尾巴在第 1 层, 共尾度 $\Omega_1$ (H1 的穿透): `brg` 与 `Ctx₀` 都只管第 0 层尾巴. 它的后代 (Symbolic `X₂-at-A`: $X_2[1][0][1]=A$) 有

- $A[0]=\eta_1=\psi_0(\Omega_\Omega+\psi_1(\Omega_1))$ (Prefix `A0≡η₁`): 尾巴仍在第 1 层, 下标只有 $0,1$ 与阶段 1 的下标 (经 $\psi_0(\Omega_\Omega)$ = BTBO 的后代);
- $A[1]=\psi_0(\Omega_\Omega+\psi_1(\Omega_{\eta_1}))$ (Symbolic `A-fs1`): 阶段 2 的项 $\eta_1$ 成了 $\Omega$-下标, 其后 $\psi_1(\Omega_{\eta_1})$ 沿 $\eta_1$ 的基本列下降, 节点 $\psi_\delta$ 的 $\delta$ 跑遍 $\eta_1$ 的后代; $A[k+1]$ 以 $A[k]$ 为下标.

所以 $X_2$ 的标签要两件 `Generic` 级的东西: (i) **带前缀的 `Generic`**: 类里多一种主项 $\psi_0(\Omega_\Omega+a)$ ($a$ 不可数), 翻译是 `ψᴾ 1`, 形状定理要在 `ŝ`/`ĉᴸ` 处读计值后的形状 (第一实例 $\eta_1$, 下标系统 = $\{0,1\}$ ∪ 阶段 1); (ii) **沿 $A$ 的链逐阶段生成下标系统** (Label 的 `St k` 的阶段 2 版本; 第 $k+1$ 阶段的下标包含 $A[k]$ 及其后代), 每一阶段的 `Slt`/`Seq` 由 §10 的 `Lab-oc` 从上一阶段的标签读出. 证书一侧已无缺口: 这些树都在 `GX₂` 之下.

一个有界的数值观察 (Python 模拟器 `ebo.py`, 宽度 3、深度 14 的基本列搜索, 约 111 万个 $X_2$ 的后代, 不进本文): 没有遇到两个**不同的**、都含 $\Omega_\Omega$ 的可数下标之间严格的派发比较 (只有 `eq`, 例如 $\psi_0(\Omega_\Omega)+1$ 对自己). 这提示 (i) 的派发对阶段 2 的下标也许只需要相等的情形, 但这是有界搜索, 不是定理.

## §10 序的对应来自标签

Label 的 `oc` 从上一阶段 `Generic` 的形状定理 (`corr`) 读出序的对应. 其实只要有标签就够: 对 $X$ 的标签归纳, 后继用离散性 `<sucT` 与 `Lab-uniq`, 极限用 `cofin₁` (StandardOmega, 对一切 `NF₁`).

```agda
Lab-oc : ∀ {X Y : Ordᶜ zero} {u v : T} → Lab X u → NF₁ u → Lab Y v → NF₁ v → v <ᵀ u → Y ≺ X
Lab-oc {u = []} (l0 c e) nu lY nv ()
Lab-oc {u = x ∷ xs} (l0 c e) nu lY nv p = ⊥-elim (cof-ne x xs c)
Lab-oc {u = u} {v = v} (l1 c e l) nu lY nv p with <sucT (pred u) (subst (v <ᵀ_) (sym (E.pred-suc u c)) p)
... | inj₁ q    = ≺-respʳ (≺s (Lab-oc l (NF₁-pred nu c) lY nv q)) (≅-sym e)
... | inj₂ refl = ≺-respʳ (≺z (Lab-uniq lY l)) (≅-sym e)
Lab-oc (lω c e h) nu lY nv p with cofin₁ nu c nv p
... | n , q = ≺-respʳ (≺l n (Lab-oc (h n) (NF₁-fsn nu c n) lY nv q)) (≅-sym e)

BTBO-NF : NF₁ (E.EBOψ 2)
BTBO-NF = diag₁-desc-NF (walkD d₀ᴰ (0 ∷ 0 ∷ 1 ∷ []) (refl , refl , refl , tt))

BTBO≺χ1ˢ : (G : Goodᶻ (toZ χ1ˢ)) → N.BTBOᴵ ≺ force _ G
BTBO≺χ1ˢ G = Lab-oc (χ1ˢ-label G) (γ′-NF 1) BTBO-label BTBO-NF (lt→< (E.EBOψ 2) (γ′ᴱ 1) refl)
```

**读法.** `Lab-oc` 对一切带标签的 `NF₁` 项给出树的 $\prec$, 经 `toLevel-≺` 就是层号的 $\prec^\mathsf I$, 即阶段 2 下标系统的 `Slt`. `BTBO≺χ1ˢ` 是它在 $\psi_0(\Omega_\Omega)<\psi_0(\Omega_\Omega+\Omega)$ 上的实例 (Stage2 的 `BTBO≺χ1` 是旧树上手写的 `≺l` 链).

## §11 步骤 2 ($\psi_0(\Omega_\Omega\cdot2)$) 的停点

$t_2$ 的树是 `ψᴾ 2 … (fΩ̂ ∷ fΩ̂ ∷ []) zero` (Prefix `t2ˢ-shape`): 弹出一个 $\hat\Omega$ 后, 链的第 0 点 $\psi^{[\hat\Omega]}_0(\Omega_1)$ 在环境层号 1 上, `Good-ψ1` 直接给证书, 其计值就是 $\gamma'_1$ 的标签 `χ1ˢ-label` 的那棵树. 第 $k+1$ 点是 $g\,\eta\,e=\psi^{[\hat\Omega]}_0(\Omega_\eta)$ 在 `Mlev 1 η e` 上, $\eta=\mathtt{lvl}\,\chi_k$. 环境层号不再 $\le2$: 例如 $\gamma'_2$ 内部有 $X_3=\psi_0(\Omega_\Omega+\Omega_3)$ (Symbolic `t2-to-X₃`), 它沿 Symbolic 的 `N3-path` 有界为 3 的闭包 (下面先在环境层号 3 上算 `X₃ˢ`, 再在受支配的层号 `Mlev 3 η e` 内部对抽象的 $\eta$ 重算 `X₃ᴹ`: 紧的界不随环境层号变化, 同 Prefix 的 `X₂ᴹ`):

```agda
three : Ordᴵ
three = suc two

z3 : zero <ᴵ three
z3 = suc (suc zero)

X₃ˢ : Ordˢ zero
X₃ˢ = ψ1 z3 (λ q → q) z3 (Ωˢ three)

_ : kind (walkˢ X₃ˢ (1 ∷ 1 ∷ 0 ∷ 2 ∷ [])) ≡ kc three
_ = refl

-- 在受支配的层号 Mlev 3 η e 内部 (η 抽象) 重算, 同一处的界仍是 3
module _ (η : Ordᴵ) (e : three ⊑ᴵ η) where
  X₃ᴹ : Ordˢ zero
  X₃ᴹ = ψᴾ 1 {ℓ = Mlev three η e} (lim 0 z3) (λ q → lim 0 q) (fΩ̂ (lim 0 z3) ∷ []) (Ωˢ three)

  _ : kind (walkˢ X₃ᴹ (1 ∷ 1 ∷ 0 ∷ 2 ∷ [])) ≡ kc three
  _ = refl
```

**精确的停点.**

- 链指标 $k=1$ (第一个非平凡的计值点 $\gamma'_2=\psi_0(\Omega_\Omega+\Omega_{\gamma'_1})$), 项 $X_3$ (基本列路径 `1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 3` 自 $t_2$), 界为 3 的闭包在 $X_3$ 的 `1 ∷ 1 ∷ 0 ∷ 2` 处 (上面的 `refl`). `Good-ψ1` 的前提 $\ell\sqsubseteq^\mathsf I2$ 在这里不成立; 单看有限的界, 修补是把 2 换成 3, 证 `Strict` 的 3 版本 ($\psi^{[\hat\Omega]}_0(0)$ = BTBO $\succ2$), 与本文同法.
- 但 $\gamma'_2$ 的计值里, 弹栈的目标层 $j$ 跑遍 $\eta=\mathtt{lvl}\,\gamma'_1$ 的子层号 (例如 $\mathtt{lvl}$ BTBO, $\mathtt{lvl}(\mathrm{BTBO}\cdot\omega)$), 支配要 "$j+1\sqsubseteq^\mathsf I$ 新链点的层号". 新链点 $\sqsupseteq^\mathsf o\psi^{[\hat\Omega]}_0(\Omega_j)$, 所以缺的引理是 **`Strictⱼ`: $\mathtt{lvl}(\psi^{[\hat\Omega]}_0(\Omega_j))\sqsupseteq^\mathsf Ij+1$ 对 $j\prec^\mathsf I\mathtt{lvl}\,\gamma'_k$**. 它不是一致的树事实 ($j\ge\psi_0(\Omega_\Omega\cdot2)$ 时为假), 只能来自 $j$ 的标签与新链点的标签经 `Lab-oc`; 而新链点 (如 $\psi_0(\Omega_\Omega+\Omega_\iota)$, $\iota<\gamma'_1$) 的标签与 §9 的 $X_2$ 是同一类缺口 ($X_2$ 就是 $\iota=2$). 所以步骤 2 的同时归纳在 $k=1$ 处就需要 §9 的 (i)(ii); 本文停在这里.

## §12 对比表

| | Prefix (§8 的计划) | 本文 |
|---|---|---|
| Uniform 的移植 | 计划 (a) | UniformS: 完成; 新增 `force-≅`/`Goodᶻ-tr`/`kd`/`Lv`/`B1` 假设形式 |
| `ŝ≅` 的传递性 | "要求紧的界" | 编译过: 用 $c\cong^\mathsf Ic'$ (`⊑ᴵ-≅ˡ ec`) |
| 严格性 ($\delta\le1$) | "初等, 但要 $\prec$ 的严格性" | `Strict₀`/`Strict₁`, 经观测与 `B1₁`, 不用后继同余 |
| `Goodᶻ` 闭包 | 缺 | `Good-ψ0` (`Ok`), **`Good-ψ1` ($\ell\sqsubseteq^\mathsf I2$)** |
| $\psi_0(\Omega_\Omega+\Omega_2)$ 的计值树 | 无法构造 | **`GX₂`, `X₂ᶠ`**; `PB` 上非零 |
| $\psi_0(\Omega_\Omega)$ 标签 | `βˢ-label` (环境层号 2) | `pop0-label` (任意环境层号) |
| $\psi_0(\Omega_\Omega+1)$, $+\Omega$ | 沿用 Stage2 的静态树 | `tsˢ-label`, `χ1ˢ-label` (新树, 任意证书), 经 `brg` |
| $\psi_0(\Omega_\Omega+\Omega_2)$ 标签 | 未得 | 第 0 项 `X₂-0`; 第 1 项起缺带前缀的 `Generic` |
| 序的对应 | "阶段 2 的 `oc`/`Slt`, 来自标签" | `Lab-oc` (对一切 `NF₁`, 只要标签) |
| $\psi_0(\Omega_\Omega\cdot2)$ | `C2-unlabel` | 停在 $k=1$: 界 3 的闭包 (`refl`), `Strictⱼ` 需要标签 |

## §13 结论与边界

**字面成立 (`refl`):** 弹栈闭包的形状 `ψ1 p σ z zero ≡ ŝ (suc i) (t₀pop p z) (gpop p z)`; `ctx (natT 1) ≡ ts`; `fsn X₂ᵗ 0 ≡ γ′ᴱ 1`; `fsn X₂ᵗ 1` 的形状与它的尾巴的共尾度 `cΩ []`; `PB` 上计值树非零; $X_3$ 里界为 3 的闭包 (环境层号 3 与抽象 $\eta$ 的 `Mlev 3 η e` 两处).

**定理 (模 $\cong$; 标签按 Correspond 的 `Lab`):**

1. 严格性: `Strict₀`, `Strict₁`, `one≺`, `onepop`.
2. 闭包: `Good-ψ0` (前提 `Ok`), `Good-ψ1` (前提 $\ell\sqsubseteq^\mathsf I2$), `popGood`, `Dom-ψ1`.
3. 检验 1: **`GX₂ : Goodᶻ (toZ X₂ˢ)`**, 计值树 `X₂ᶠ`.
4. 计值: `fadd`, `pop0≅`, `pop0-label`; 桥 `brg`, `Ctxˢ`.
5. 标签: `tsˢ-label : ∀ G → Lab (force (toZ tsˢ) G) ts`, `χ1ˢ-label : ∀ G → Lab (force (toZ χ1ˢ) G) (γ′ᴱ 1)`, **`X₂-0 : Lab (sq X₂ᶠ 0) (fsn X₂ᵗ 0)`**, `X₂-reduce`.
6. 序的对应: `Lab-oc`, 实例 `BTBO≺χ1ˢ`.

**标签状态.** $\psi_0(\Omega_\Omega)$: 定理 (任意环境层号, `pop0-label`). $\psi_0(\Omega_\Omega+1)$, $\psi_0(\Omega_\Omega+\Omega)$: 定理 (新树). $\psi_0(\Omega_\Omega+\Omega_2)$: **计值树与证书是定理, 遗传标签未得**; 已证到第 0 项, 第 1 项 $\psi_0(\Omega_\Omega+\psi_1(\Omega_\Omega+\Omega_1))$ 起缺带前缀的 `Generic` 与沿 $A$ 的链的阶段归纳 (§9). Symbolic 的 `PB` 在计值树上非零 (`refl`), 终点 $\cong$ BTBO 只是纸面的 (经 `pop0≅`). $\psi_0(\Omega_\Omega\cdot2)$: 未得, 停在链指标 1 (§11). `C2-unlabel` 与 Stage2 的 `Q′` 未解除.

**边界.**

- 闭包定理只对长度 $\le1$ 的纯 $\hat\Omega$ 栈、环境层号 $\le2$. 这正好覆盖 $\psi_0(\Omega_\Omega+\Omega_2)$; 长度 2 的栈与更大的环境层号见 §11.
- 空栈、目标 0 的折叠要求无符号输入 (`Ok`); 不加这个前提时, 尾巴里界为 2 的 `ŝ` 被映到第 0 层, 支配要 "$\psi^{[]}_0$ 的输出 $\succ1$", 由于 Level 的 $\sqsubseteq$ 对 `suc` 不单调, 本文没有证出 (纸面; 在 $X_2$ 的计值中不出现这种情形).
- `brg` 只对第 0 层尾巴; 第 1 层尾巴 (无论是否含 $\Omega_\Omega$) 的桥没有写, 而且即使有也只把问题移到静态前缀的旧树, 那里同样没有标签定理.
- §9 的 Python 搜索是有界的数值观察, 不进本文, 不作为定理.
- 不改 `src/`、`archive/` 与已有的 Align 文件, README 未改.
