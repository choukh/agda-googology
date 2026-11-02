# 依目标的互模拟与地板见证 (一): (b′) 与 (a′)

> 接 [Uniform2](Uniform2.lagda.md) §6. 本文是 [Relative](Relative.lagda.md) 的前半: 任务 1 (依目标的互模拟, Uniform2 所说的 (b′)) 与任务 2 (依目标的地板见证, (a′)). `BranchΩ` 与 $\psi_0(\Omega_\Omega^2)$ 的结论在 Relative.
>
> 结论先说:
>
> 1. **(b′) 在 "目标高于尾巴的一切地板" 时是定理, 对一切底.** 依目标下界 $c$ 的地板关系 `_∼[_]_` (只在 $\preceq c$ 的项上可以不同)、运行的互模拟 `_≈[_]_` (只比较目标 $\succeq c$ 处的输出)、导出上的层对齐 `AlignT c`; 深度 0 与 1 的折叠都尊重它 (`fold-≅0ᵗ`, `fold-≅1ᵗ`). 当两侧尾巴的层号 $\sqsubseteq c+1$、根地板可忽略时, **任意** $\cong^\mathsf s$ 导出都层对齐 (`alignHigh`: "$\cong^\mathsf s$ 蕴含 $\cong^\mathsf t$"). 于是 `bRᵗ`: 对一切 $\eta\cong\eta'$ 与一切 $c$ ($\eta\sqsubseteq c+2$), 分支帧 $\psi_\Omega(\Omega_\eta)$ 的深度 1 折叠在目标 $\succeq c$ 处互模拟, 对**一切** $\approx_{[c]}$ 相关的底, 无标签前提. $\eta=3$ 时 $c=1$ 成立 (`AlignΩ₃ᵗ`), $c=0$ 不成立 (`¬AlignΩ₃⁰`, 即 Uniform2 的 `¬AlignΩ₃`).
> 2. **但 $c=0$ 处缺的不是量化范围.** Relative §1 编译证明 Uniform2 的 `BranchΩ (Ω̂A 0) []` **无居留**: 折叠情形的链点在**更高**的目标 (节点层) 上算出, 随后作为指数尾巴在**更低**的目标上重新折叠, 底在高目标处输出的 `up`-结构于是在低目标处被读到. "派发只升目标" 对一次计值成立, 链点却把高目标的树带回低目标. (b′) 在低目标处的正确形式是对**底**的层对齐要求, 不是对目标的相对化 (Relative §2–§3).
> 3. **(a′) 是定理, 且确实只在 $\eta\ge4$ 才需要.** `FlrLab[ c ]`/`FW[ c ]` (只有 $\succ$ 目标的地板项要见证), 弹栈行 `cloWᵗ`, 闭包定理 `goodΩ̂0Wᵗ` (深度 0, 目标非零部分). 三种地板 (§8): 第 2 层的地板 `fk 1` 总被 $\Omega=\Omega_1$ 里的 $1$ 见证 (`FL-Ω₁`, 对一切帧标签); 首项为 $\psi_w(\cdot)$ 的标签 (链点) 见证一切 $\preceq\mathtt{lvl}\,w$ 的地板 (`FL-head`); 第 3 层的伪输入 (树 `suc zero`, 标签 $1$) 的地板 `fk 2` 在目标无关的形式下没有见证 (`¬FL₄`, 编译), 依目标的形式在一切 $\succeq2$ 的目标处平凡成立 (`FL₄[]`), 而 $\Omega_4$ 的伪输入只在穿透目标 ($\succ3$) 处被计值.
> 4. **`up (self n)` 下的地板紧性: 否定 (§9).** 极限层的地板在 `up (self n)` 下保持为父层的 `fk (lim …)`. $\psi_0(\psi_\Omega(\Omega_\omega))$ 的第 0 支 (尾巴 $1$, 地板 `fk ω`) 的第 2 份副本里弹栈的界字面是 $\omega+1$ (`up-self-bound`, `refl`; 紧的界是 $1$), 而帧标签 $\psi_\Omega(1)$ 里没有能见证 $\omega$ 的下标 (`¬FLω`, 编译). 这一点不在 $\psi_0(\Omega_\Omega^2)$ 的目标 0 计值里出现 (Relative §4), 但它使 `BranchΩ` 的 `bW` 在 $\theta=\omega$、目标 $1\le i<\omega$ 处不能由 `gŝ` 行给出.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件; Uniform2Base 的定义凡要相对化的都以新名字 (后缀 `ᵗ` 或 `[ c ]`) 复制在本文, 证明与原版逐行对应, 只多一个目标下界参数.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RelativeBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Ord₊ˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; tr⁻ˢ; H1-pen; Kind; kind; kl; walkˢ)
open import OCF.Align.Prefix using () renaming (kc to kcˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsT; cof; cΩ; Ωt; _<ᵀ_; cofA; []<) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω)
open import OCF.Align.StandardOmega using (NF₁; NF₁-fsn)
open import OCF.Align.SystemOmega using (Occ; oh; od; os; ot)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.Stage2Label using (one⁰)
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.Decouple using (Idx; lvI; Ieq)
open import OCF.Align.GoodLBase
open import OCF.Align.OmegaExpBase using (cofW; H1W; gtW; ne-w; 1<γ)
open import OCF.Align.NonTightBase using (I₁)
open import OCF.Align.UniformS
open import OCF.Align.Uniform2Base
open import OCF.Align.Uniform2Depth1 using (_≈₁_; AlignD)
```
## §1 目标下界与可忽略的地板项

`Up c i`: 目标 $i\succeq c$. 计值中的一切目标都 $\succeq$ 起点目标 (派发只升目标: 穿透保持 $i$, 折叠的链在节点层 $j\succeq i$ 上算), 所以一个目标下界沿整个计值保持. `Ign c K`: 地板项 $K$ 平凡 ($\cong0$) 或 $\preceq c$. 关键观察 `ign-no`: 在目标 $i\succeq c$ 的弹栈里, `bound` 的当前最大者 $M\succeq i$ (`iM≼`), 可忽略的项永远不会严格超过它, 于是 `<ᴵ-dec` 永不走 "换最大者" 的分支.

```agda
Up : Ordᴵ → Ordᴵ → Set
Up c i = (c ≺ᴵ i) ⊎ (c ≅ᴵ i)

≺≼ : ∀ {a b d} → a ≺ᴵ b → (b ≺ᴵ d) ⊎ (b ≅ᴵ d) → a ≺ᴵ d
≺≼ s (inj₁ s′) = ≺ᴵ-trans s s′
≺≼ s (inj₂ e)  = ≺ᴵ-respʳ s e

≼≺ : ∀ {a b d} → (a ≺ᴵ b) ⊎ (a ≅ᴵ b) → b ≺ᴵ d → a ≺ᴵ d
≼≺ (inj₁ s) s′ = ≺ᴵ-trans s s′
≼≺ (inj₂ e) s′ = ≺ᴵ-respˡ e s′

Up-≅ : ∀ {c i i′} → Up c i → i ≅ᴵ i′ → Up c i′
Up-≅ (inj₁ s)  e = inj₁ (≺ᴵ-respʳ s e)
Up-≅ (inj₂ e′) e = inj₂ (≅ᴵ-trans e′ e)

Up-≺ : ∀ {c i j} → Up c i → i ≺ᴵ j → Up c j
Up-≺ u s = inj₁ (≼≺ u s)

Ign : Ordᴵ → Ordᴵ → Set
Ign c K = (K ≅ᴵ zero) ⊎ ((K ≺ᴵ c) ⊎ (K ≅ᴵ c))

ign-no : ∀ {c i M K} → Ign c K → Up c i → (i ≺ᴵ M) ⊎ (i ≅ᴵ M) → M ≺ᴵ K → ⊥
ign-no (inj₁ k0) u im s = ≺0 s k0
ign-no (inj₂ kc) u im s = ≺ᴵ-irrefl (≺≼ (≺≼ (≺≼ s kc) u) im)
```
**依目标的地板关系.** 与 Uniform2Base 的 `_∼ᶠ_` 相同, 只是 "平凡项可与空位对应" 推广为 "可忽略项 (对 $c$) 可与空位或任何可忽略项对应". `∼→∼[]`: 原关系是 $c$ 任意时的特例.

```agda
infix 4 _∼[_]_
data _∼[_]_ : Flr → Ordᴵ → Flr → Set where
  fz∼ : ∀ {c} → fz ∼[ c ] fz
  fk∼ : ∀ {c K K′} → K ≅ᴵ K′ → fk K ∼[ c ] fk K′
  kk∼ : ∀ {c K K′} → Ign c K → Ign c K′ → fk K ∼[ c ] fk K′
  zk∼ : ∀ {c K′} → Ign c K′ → fz ∼[ c ] fk K′
  kz∼ : ∀ {c K} → Ign c K → fk K ∼[ c ] fz
  ⊔∼  : ∀ {c a a′ b b′} → a ∼[ c ] a′ → b ∼[ c ] b′ → a ⊔ b ∼[ c ] a′ ⊔ b′

∼→∼[] : ∀ {c φ φ′} → φ ∼ᶠ φ′ → φ ∼[ c ] φ′
∼→∼[] fz∼ = fz∼
∼→∼[] (fk∼ e) = fk∼ e
∼→∼[] (zk∼ e) = zk∼ (inj₁ e)
∼→∼[] (kz∼ e) = kz∼ (inj₁ e)
∼→∼[] (⊔∼ a b) = ⊔∼ (∼→∼[] a) (∼→∼[] b)

∼[]-refl : ∀ {c} φ → φ ∼[ c ] φ
∼[]-refl φ = ∼→∼[] (∼ᶠ-refl φ)
```
## §2 界的依目标互模拟

`insT′`: 可忽略项不改最大者 (Uniform2Base `insT` 的推广). `accMᵗ`/`bound-≅ᵗ`: 两侧地板 $\sim_{[c]}$、目标 $\cong$ 且 $\succeq c$ 时, 两次 `bound` 的最大者 $\cong$. 证明与 `accM` 逐项相同, 新的三个子句由 `insT′` 两侧化.

```agda
insT′ : ∀ {c i ℓ φ K} (t : Top i ℓ φ) (ek : Simᴵ (suc K) ℓ) → Ign c K → Up c i → Mx (ins t ek) ≡ Mx t
insT′ t ek g u with <ᴵ-dec (ek zero) (mx t)
... | injᵃ (via _ _) = refl
... | injᶜ _ = refl
... | injᵇ s = ⊥-elim (ign-no g u (iM≼ (src t)) s)

accMᵗ : ∀ {c i i′ ℓ ℓ′ φ₁ φ₁′ φ₂ φ₂′} (t : Top i ℓ φ₁) (t′ : Top i′ ℓ′ φ₁′) → Up c i → Up c i′ → φ₂ ∼[ c ] φ₂′ →
        (ev : Ev ℓ φ₂) (ev′ : Ev ℓ′ φ₂′) → Mx t ≅ᴵ Mx t′ → Mx (accT t φ₂ ev) ≅ᴵ Mx (accT t′ φ₂′ ev′)
accMᵗ t t′ u u′ fz∼ ev ev′ eM = eM
accMᵗ t t′ u u′ (fk∼ eK) ev ev′ eM = insM t t′ ev ev′ eM eK
accMᵗ t t′ u u′ (kk∼ g g′) ev ev′ eM = subst₂ _≅ᴵ_ (sym (insT′ t ev g u)) (sym (insT′ t′ ev′ g′ u′)) eM
accMᵗ t t′ u u′ (zk∼ g′) ev ev′ eM = subst (λ M → Mx t ≅ᴵ M) (sym (insT′ t′ ev′ g′ u′)) eM
accMᵗ t t′ u u′ (kz∼ g) ev ev′ eM = subst (λ M → M ≅ᴵ Mx t′) (sym (insT′ t ev g u)) eM
accMᵗ t t′ u u′ (⊔∼ a b) (x , y) (x′ , y′) eM = accMᵗ (accT t _ x) (accT t′ _ x′) u u′ b y y′ (accMᵗ t t′ u u′ a x x′ eM)

bound-≅ᵗ : ∀ {c i i′ ℓ ℓ′ φ φ′} → φ ∼[ c ] φ′ → (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (ev′ : Ev ℓ′ φ′) (p′ : i′ <ᴵ ℓ′) →
           i ≅ᴵ i′ → Up c i → Mx (bound φ ev p) ≅ᴵ Mx (bound φ′ ev′ p′)
bound-≅ᵗ s ev p ev′ p′ ei u = accMᵗ (top₀ p) (top₀ p′) u (Up-≅ u ei) s ev ev′ ei
```
**读法.** 这就是 Uniform2 §6 所说的 "$\preceq$ 目标的地板项从不被读到" 的精确形式: 被读到的只有最大者, 可忽略项不会成为最大者. 下面把它沿运行与折叠传播.

## §3 深度 0 的依目标互模拟

`R ≈[ c ] R′`: 一切 $\cong$ 的目标对 $(i,i')$ 且 $i\succeq c$ 处输出 $\cong^\mathsf s$. 行引理与 Uniform2Base §7 的 `…R` 逐字对应; 唯一的新内容在 `limᵢRᵗ` 的折叠情形: 链在节点层 $j$ 上算, 需要 `Up c j`, 由派发结果给出 (`injᵇ s`: $i\prec j$; `injᶜ`: $j\cong i$). 穿透情形目标不变.

```agda
infix 4 _≈[_]_
_≈[_]_ : ∀ {φ ψ} → Run φ → Ordᴵ → Run ψ → Set
_≈[_]_ {φ} {ψ} R c R′ = ∀ {i i′ ℓ ℓ′} (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (ev′ : Ev ℓ′ ψ) (p′ : i′ <ᴵ ℓ′) → i ≅ᴵ i′ → Up c i →
                        R ev p ≅ˢ R′ ev′ p′

≈→≈[] : ∀ {c φ ψ} {R : Run φ} {R′ : Run ψ} → R ≈ᴿ R′ → R ≈[ c ] R′
≈→≈[] h ev p ev′ p′ ei u = h ev p ev′ p′ ei

limRᵗ : ∀ {c φ ψ} {F : ℕ → Run φ} {G : ℕ → Run ψ} → (∀ n → F n ≈[ c ] G n) → limA 0 F ≈[ c ] limA 0 G
limRᵗ h ev p ev′ p′ ei u = l≅ (λ n → h n ev p ev′ p′ ei u)

sucRᵗ : ∀ {c φ ψ} {R : Run φ} {R′ : Run ψ} → R ≈[ c ] R′ → sucRun R ≈[ c ] sucRun R′
sucRᵗ h ev p ev′ p′ ei u = l≅ (iter-R _≅ˢ_ (λ e′ → addˢ-≅ (kd-≅ ei) (h ev p ev′ p′ ei u) e′) z≅)

limᵢRᵗ : ∀ {c φ ψ j j′} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → j′ <ᴵ L}
         {H : Ordˢ j → Run φ} {H′ : Ordˢ j′ → Run ψ} →
         j ≅ᴵ j′ → (∀ x y → x ≅ˢ y → H x ≈[ c ] H′ y) → limᵢA 0 ac H ≈[ c ] limᵢA 0 ac′ H′
limᵢRᵗ {ac = ac} {ac′ = ac′} {H = H} {H′ = H′} e h ev p ev′ p′ ei u with <ᴵ-dec (ac ev) p | <ᴵ-dec (ac′ ev′) p′
... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) = lᵢ≅ (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans e e₂)) λ x y d →
  subst₂ (λ a b → H (tr⁻ˢ e₁ a) ev p ≅ˢ H′ (tr⁻ˢ e₂ b) ev′ p′)
         (sym (out-intoˢ (<→◃ r₁) x)) (sym (out-intoˢ (<→◃ r₂) y))
         (h _ _ (tr⁻ˢ-≅ e₁ (≅-tr⁻ˢ e₂ (R→≅ˢ (<→◃ r₁) d))) ev p ev′ p′ ei u)
... | injᵃ r | injᵇ s  = ⊥-elim (clash₁ e ei r s)
... | injᵃ r | injᶜ c′ = ⊥-elim (clash₂ e ei r c′)
... | injᵇ s | injᵃ r  = ⊥-elim (clash₁ (≅ᴵ-sym e) (≅ᴵ-sym ei) r s)
... | injᶜ c′ | injᵃ r = ⊥-elim (clash₂ (≅ᴵ-sym e) (≅ᴵ-sym ei) r c′)
... | injᵇ s | injᵇ _  = l≅ (λ m → h _ _ (iter-R _≅ˢ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e (Up-≺ u s)) (Ωˢ-≅ e) m) ev p ev′ p′ ei u)
... | injᵇ s | injᶜ _  = l≅ (λ m → h _ _ (iter-R _≅ˢ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e (Up-≺ u s)) (Ωˢ-≅ e) m) ev p ev′ p′ ei u)
... | injᶜ c′ | injᵇ _ = l≅ (λ m → h _ _ (iter-R _≅ˢ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e (Up-≅ u (≅ᴵ-sym c′))) (Ωˢ-≅ e) m) ev p ev′ p′ ei u)
... | injᶜ c′ | injᶜ _ = l≅ (λ m → h _ _ (iter-R _≅ˢ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e (Up-≅ u (≅ᴵ-sym c′))) (Ωˢ-≅ e) m) ev p ev′ p′ ei u)

ĉRᵗ : ∀ {c₀ φ ψ c c′ t₀ t₀′} {g : (η : Ordᴵ) → c ⊑ᴵ η → _} {g′ : (η : Ordᴵ) → c′ ⊑ᴵ η → _}
      {O₀ : Run φ} {O : (η : Ordᴵ) → c ⊑ᴵ η → Run φ} {O₀′ : Run ψ} {O′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Run ψ} →
      c ≅ᴵ c′ → t₀ ≅ᶻ t₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ᶻ g′ η′ e′) →
      O₀ ≈[ c₀ ] O₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → O η e ≈[ c₀ ] O′ η′ e′) → ĉA 0 c t₀ g O₀ O ≈[ c₀ ] ĉA 0 c′ t₀′ g′ O₀′ O′
ĉRᵗ ec dt dg h₀ h ev p ev′ p′ ei u = ĉ≅ ec dt dg (h₀ ev p ev′ p′ ei u) (λ η e η′ e′ eη → h η e η′ e′ eη ev p ev′ p′ ei u)

ŝRᵗ : ∀ {c₀ φ ψ c c′} {T₀ : Run φ} {G : (η : Ordᴵ) → c ⊑ᴵ η → Run φ} {T₀′ : Run ψ} {G′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Run ψ} →
      c ≅ᴵ c′ → T₀ ≈[ c₀ ] T₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → G η e ≈[ c₀ ] G′ η′ e′) → ŝA 0 c T₀ G ≈[ c₀ ] ŝA 0 c′ T₀′ G′
ŝRᵗ ec h₀ h ev p ev′ p′ ei u = ŝ≅ (kd-≅ ei) ec (h₀ ev p ev′ p′ ei u) (λ η e η′ e′ eη → h η e η′ e′ eη ev p ev′ p′ ei u)

wkRᵗ : ∀ {c φ φ′ ψ ψ′} {R : Run φ} {R′ : Run φ′} (le : ∀ {L} → Ev L ψ → Ev L φ) (le′ : ∀ {L} → Ev L ψ′ → Ev L φ′) →
       R ≈[ c ] R′ → wk 0 le R ≈[ c ] wk 0 le′ R′
wkRᵗ le le′ h ev p ev′ p′ ei u = h (le ev) p (le′ ev′) p′ ei u

cloRᵗ : ∀ {c φ φ′} {t : Run (φ ⊔ fk zero)} {g : (η : Ordᴵ) → Run (φ ⊔ fk η)}
        {t′ : Run (φ′ ⊔ fk zero)} {g′ : (η : Ordᴵ) → Run (φ′ ⊔ fk η)} → φ ∼[ c ] φ′ →
        t ≈[ c ] t′ → (∀ η η′ → η ≅ᴵ η′ → g η ≈[ c ] g′ η′) → cloA 0 t g ≈[ c ] cloA 0 t′ g′
cloRᵗ {φ = φ} {φ′} s ht hg ev p ev′ p′ ei u =
  ŝ≅ (kd-≅ ei) (s≅ (bound-≅ᵗ (⊔∼ s (fk∼ z≅)) ev p ev′ p′ ei u)) (ht ev p ev′ p′ ei u)
     (λ η e η′ e′ eη → hg η η′ eη _ (lim 0 (iF (bound (φ ⊔ fk zero) ev p))) _ (lim 0 (iF (bound (φ′ ⊔ fk zero) ev′ p′))) ei u)
```
`fold-≅0ᵗ`: Uniform2Base `fold-≅0` 的相对版, 对 $\cong^\mathsf s$ 推导递归, 各行交给上面的 `…Rᵗ`. 深度 0 的尾巴里没有弹栈, 尾巴地板不影响值, 对任意两个地板成立.

```agda
fold-≅0ᵗ : ∀ {c fl fl′ φ φ′ k₁ k₂} {cv : ∀ {L} → Ev L φ → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k₂ L}
           {P : Run fl} {P′ : Run fl′} {a : Ordˢ k₁} {b : Ordˢ k₂} →
           P ≈[ c ] P′ → a ≅ˢ b → fold 0 φ cv P a ≈[ c ] fold 0 φ′ cv′ P′ b
fold-≅0ᵗ H z≅ ev p ev′ p′ ei u = H (proj₁ ev) p (proj₁ ev′) p′ ei u
fold-≅0ᵗ H (s≅ e) = sucRᵗ (fold-≅0ᵗ H e)
fold-≅0ᵗ H (l≅ h) = limRᵗ (λ n → fold-≅0ᵗ H (h n))
fold-≅0ᵗ {k₁ = suc k′} {cv = cv} {cv′ = cv′} H (upˡ {r = zero} e) =
  wkRᵗ (λ ev → proj₁ ev , toFlo k′ (cv (proj₂ ev))) (λ ev → ev) (fold-≅0ᵗ H e)
fold-≅0ᵗ H (upˡ {r = self n} e) = fold-≅0ᵗ H e
fold-≅0ᵗ {k₂ = suc k′} {cv = cv} {cv′ = cv′} H (upʳ {r = zero} e) =
  wkRᵗ (λ ev → ev) (λ ev → proj₁ ev , toFlo k′ (cv′ (proj₂ ev))) (fold-≅0ᵗ H e)
fold-≅0ᵗ H (upʳ {r = self n} e) = fold-≅0ᵗ H e
fold-≅0ᵗ {k₁ = zero} {k₂ = zero} H (ŝ≅ k ec et eg) =
  ĉRᵗ ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη)) (fold-≅0ᵗ H et) (λ η e η′ e′ eη → fold-≅0ᵗ H (eg η e η′ e′ eη))
fold-≅0ᵗ {k₁ = zero} {k₂ = suc _}   H (ŝ≅ k ec et eg) = ⊥-elim (tf k)
fold-≅0ᵗ {k₁ = zero} {k₂ = lim _ _} H (ŝ≅ k ec et eg) = ⊥-elim (tf k)
fold-≅0ᵗ {k₁ = suc _}   {k₂ = zero} H (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
fold-≅0ᵗ {k₁ = lim _ _} {k₂ = zero} H (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
fold-≅0ᵗ {k₁ = suc _}   {k₂ = suc _}   H (ŝ≅ k ec et eg) = ŝRᵗ ec (fold-≅0ᵗ H et) (λ η e η′ e′ eη → fold-≅0ᵗ H (eg η e η′ e′ eη))
fold-≅0ᵗ {k₁ = suc _}   {k₂ = lim _ _} H (ŝ≅ k ec et eg) = ŝRᵗ ec (fold-≅0ᵗ H et) (λ η e η′ e′ eη → fold-≅0ᵗ H (eg η e η′ e′ eη))
fold-≅0ᵗ {k₁ = lim _ _} {k₂ = suc _}   H (ŝ≅ k ec et eg) = ŝRᵗ ec (fold-≅0ᵗ H et) (λ η e η′ e′ eη → fold-≅0ᵗ H (eg η e η′ e′ eη))
fold-≅0ᵗ {k₁ = lim _ _} {k₂ = lim _ _} H (ŝ≅ k ec et eg) = ŝRᵗ ec (fold-≅0ᵗ H et) (λ η e η′ e′ eη → fold-≅0ᵗ H (eg η e η′ e′ eη))
fold-≅0ᵗ H (ĉ≅ ec dt dg eo eO) = ĉRᵗ ec dt dg (fold-≅0ᵗ H eo) (λ η e η′ e′ eη → fold-≅0ᵗ H (eO η e η′ e′ eη))
fold-≅0ᵗ H (lᵢ≅ {p = q} e h) = limᵢRᵗ e (λ x y d → fold-≅0ᵗ H (h x y (≅→Rˢ (<→◃ q) d)))
```
## §4 深度 1: 依目标的层对齐互模拟

`E ≈₁[ c ] E′`: 底的地板 $\sim_{[c]}$、底 $\approx_{[c]}$ 则输出 $\approx_{[c]}$. `AlignT c φ φ′ d`: Uniform2Depth1 的 `AlignD`, 只把后继步的 `φ ∼ᶠ φ′` 换成 `φ ∼[ c ] φ′`. 这就是任务 1 要的 $\cong^\mathsf t$: 一对 $\cong^\mathsf s$ 相关的尾巴, 在后继步上地板只在 $\preceq c$ 的项上不同, 即**只在目标以下不同**.

```agda
infix 4 _≈₁[_]_
_≈₁[_]_ : ∀ {φ ψ} → A 1 φ → Ordᴵ → A 1 ψ → Set
E ≈₁[ c ] E′ = ∀ {fl fl′} {P : Run fl} {P′ : Run fl′} → fl ∼[ c ] fl′ → P ≈[ c ] P′ → E P ≈[ c ] E′ P′

AlignT : ∀ {k₁ k₂} (c : Ordᴵ) (φ φ′ : Flr) {a : Ordˢ k₁} {b : Ordˢ k₂} → a ≅ˢ b → Set
AlignT c φ φ′ z≅ = ⊤
AlignT c φ φ′ (s≅ e) = (φ ∼[ c ] φ′) × AlignT c φ φ′ e
AlignT c φ φ′ (l≅ h) = ∀ n → AlignT c φ φ′ (h n)
AlignT c φ φ′ (lᵢ≅ e h) = ∀ x y r → AlignT c φ φ′ (h x y r)
AlignT c φ φ′ (upˡ {k = k′} {r = zero} e) = AlignT c (flo k′) φ′ e
AlignT c φ φ′ (upˡ {r = self n} e) = AlignT c φ φ′ e
AlignT c φ φ′ (upʳ {k = k′} {r = zero} e) = AlignT c φ (flo k′) e
AlignT c φ φ′ (upʳ {r = self n} e) = AlignT c φ φ′ e
AlignT c φ φ′ (ŝ≅ k ec et eg) = AlignT c φ φ′ et × (∀ η e η′ e′ eη → AlignT c φ φ′ (eg η e η′ e′ eη))
AlignT c φ φ′ (ĉ≅ ec dt dg eo eO) = AlignT c φ φ′ eo × (∀ η e η′ e′ eη → AlignT c φ φ′ (eO η e η′ e′ eη))
```
`fold-≅1ᵗ` (任务 1 的 `fold-≅ᵗ`): 指数前缀 $\approx_{1[c]}$、尾巴推导 `AlignT c`, 则深度 1 的折叠 $\approx_{1[c]}$. 与 `fold-≅1` 逐子句对应; 后继行的副本由 `repRᵗ` (底的地板 `fl ⊔ (flE ⊔ φ)` 由 `⊔∼` 与后继步的 $\sim_{[c]}$ 拼出). `selfΩ̂0ᵗ`: $\Omega_\Omega$ 闭包对一切 $c$ 是 $\approx_{1[c]}$ 的.

```agda
repRᵗ : ∀ {c fl fl′ ψ ψ′} {Q : Run fl} {Q′ : Run fl′} {fr : A 1 ψ} {fr′ : A 1 ψ′} →
        fl ∼[ c ] fl′ → ψ ∼[ c ] ψ′ → Q ≈[ c ] Q′ → fr ≈₁[ c ] fr′ → ∀ m → repA 0 Q fr m ≈[ c ] repA 0 Q′ fr′ m
repRᵗ s sψ H F zero          = wkRᵗ proj₁ proj₁ H
repRᵗ s sψ H F (suc zero)    = F s H
repRᵗ s sψ H F (suc (suc m)) = wkRᵗ _ _ (F (⊔∼ s sψ) (repRᵗ s sψ H F (suc m)))

fold-≅1ᵗ : ∀ {c flE flE′ φ φ′ k₁ k₂} {cv : ∀ {L} → Ev L φ → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k₂ L}
           {E : A 1 flE} {E′ : A 1 flE′} {a : Ordˢ k₁} {b : Ordˢ k₂} →
           flE ∼[ c ] flE′ → E ≈₁[ c ] E′ → (d : a ≅ˢ b) → AlignT c φ φ′ d → fold 1 φ cv E a ≈₁[ c ] fold 1 φ′ cv′ E′ b
fold-≅1ᵗ sE HE z≅ al s H = wkRᵗ _ _ (HE s H)
fold-≅1ᵗ sE HE (s≅ e) (sφ , al) s H = limRᵗ (λ m → repRᵗ s (⊔∼ sE sφ) H (fold-≅1ᵗ sE HE e al) m)
fold-≅1ᵗ sE HE (l≅ h) al s H = limRᵗ (λ n → fold-≅1ᵗ sE HE (h n) (al n) s H)
fold-≅1ᵗ sE HE (lᵢ≅ {p = q} e h) al s H =
  limᵢRᵗ e (λ x y d → fold-≅1ᵗ sE HE (h x y (≅→Rˢ (<→◃ q) d)) (al x y (≅→Rˢ (<→◃ q) d)) s H)
fold-≅1ᵗ {k₁ = suc k′} {cv = cv} sE HE (upˡ {r = zero} e) al s H =
  wkRᵗ (λ { (u , (w , v)) → u , (w , toFlo k′ (cv v)) }) (λ ev → ev) (fold-≅1ᵗ sE HE e al s H)
fold-≅1ᵗ sE HE (upˡ {r = self n} e) al s H = fold-≅1ᵗ sE HE e al s H
fold-≅1ᵗ {k₂ = suc k′} {cv′ = cv′} sE HE (upʳ {r = zero} e) al s H =
  wkRᵗ (λ ev → ev) (λ { (u , (w , v)) → u , (w , toFlo k′ (cv′ v)) }) (fold-≅1ᵗ sE HE e al s H)
fold-≅1ᵗ sE HE (upʳ {r = self n} e) al s H = fold-≅1ᵗ sE HE e al s H
fold-≅1ᵗ {k₁ = zero} {k₂ = zero} sE HE (ŝ≅ k ec et eg) (al₀ , al) s H =
  ĉRᵗ ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη)) (fold-≅1ᵗ sE HE et al₀ s H)
      (λ η e η′ e′ eη → fold-≅1ᵗ sE HE (eg η e η′ e′ eη) (al η e η′ e′ eη) s H)
fold-≅1ᵗ {k₁ = zero} {k₂ = suc _}   sE HE (ŝ≅ k ec et eg) al s H = ⊥-elim (tf k)
fold-≅1ᵗ {k₁ = zero} {k₂ = lim _ _} sE HE (ŝ≅ k ec et eg) al s H = ⊥-elim (tf k)
fold-≅1ᵗ {k₁ = suc _}   {k₂ = zero} sE HE (ŝ≅ k ec et eg) al s H = ⊥-elim (tf (sym k))
fold-≅1ᵗ {k₁ = lim _ _} {k₂ = zero} sE HE (ŝ≅ k ec et eg) al s H = ⊥-elim (tf (sym k))
fold-≅1ᵗ {k₁ = suc _} {k₂ = suc _} sE HE (ŝ≅ k ec et eg) (al₀ , al) s H =
  ŝRᵗ ec (fold-≅1ᵗ sE HE et al₀ s H) (λ η e η′ e′ eη → fold-≅1ᵗ sE HE (eg η e η′ e′ eη) (al η e η′ e′ eη) s H)
fold-≅1ᵗ {k₁ = suc _} {k₂ = lim _ _} sE HE (ŝ≅ k ec et eg) (al₀ , al) s H =
  ŝRᵗ ec (fold-≅1ᵗ sE HE et al₀ s H) (λ η e η′ e′ eη → fold-≅1ᵗ sE HE (eg η e η′ e′ eη) (al η e η′ e′ eη) s H)
fold-≅1ᵗ {k₁ = lim _ _} {k₂ = suc _} sE HE (ŝ≅ k ec et eg) (al₀ , al) s H =
  ŝRᵗ ec (fold-≅1ᵗ sE HE et al₀ s H) (λ η e η′ e′ eη → fold-≅1ᵗ sE HE (eg η e η′ e′ eη) (al η e η′ e′ eη) s H)
fold-≅1ᵗ {k₁ = lim _ _} {k₂ = lim _ _} sE HE (ŝ≅ k ec et eg) (al₀ , al) s H =
  ŝRᵗ ec (fold-≅1ᵗ sE HE et al₀ s H) (λ η e η′ e′ eη → fold-≅1ᵗ sE HE (eg η e η′ e′ eη) (al η e η′ e′ eη) s H)
fold-≅1ᵗ sE HE (ĉ≅ ec dt dg eo eO) (al₀ , al) s H =
  ĉRᵗ ec dt dg (fold-≅1ᵗ sE HE eo al₀ s H) (λ η e η′ e′ eη → fold-≅1ᵗ sE HE (eO η e η′ e′ eη) (al η e η′ e′ eη) s H)

selfΩ̂0ᵗ : ∀ {c} → Ω̂A 0 ≈₁[ c ] Ω̂A 0
selfΩ̂0ᵗ {P = P} {P′ = P′} s H =
  cloRᵗ {t = fold 0 (fk zero) (λ e → e) P (Ωˢ (suc zero))} {g = λ η → fold 0 (fk η) (λ e q → e (suc q)) P (Ωˢ η)}
        {t′ = fold 0 (fk zero) (λ e → e) P′ (Ωˢ (suc zero))} {g′ = λ η → fold 0 (fk η) (λ e q → e (suc q)) P′ (Ωˢ η)}
        s (fold-≅0ᵗ H (Ωˢ-refl (suc zero))) (λ η η′ eη → fold-≅0ᵗ H (Ωˢ-≅ eη))
```
## §5 由 $\cong^\mathsf s$ 推出: 目标高于尾巴的一切地板时

`alignHigh`: 两侧的根地板可忽略 (`IgnL c`: 空或单项可忽略), 两侧树的层号 $\sqsubseteq c+1$, 则**任意** $\cong^\mathsf s$ 推导都 `AlignT c`. 证明对推导递归, 维持不变量: `up zero` 处层号 $k'+1\sqsubseteq c+1$ 给出 $k'\preceq c$ (`s⊑s→≼`), 新地板 `flo k′` 可忽略 (`floIgn`), 子树层号 $\sqsubseteq c+1$; `up (self n)` 处地板不变, $f\,n\sqsubseteq\lim f$. 层号的界用 $\sqsubseteq$ 而不用 $\preceq$: 后者对 `up (self n)` 不下传 (常数列 `Z⁰` 的项 $0\not\preceq$ `Z⁰`).

```agda
IgnL : Ordᴵ → Flr → Set
IgnL c φ = (φ ≡ fz) ⊎ Σ Ordᴵ λ K → (φ ≡ fk K) × Ign c K

ign∼ : ∀ {c φ φ′} → IgnL c φ → IgnL c φ′ → φ ∼[ c ] φ′
ign∼ (inj₁ refl) (inj₁ refl) = fz∼
ign∼ (inj₁ refl) (inj₂ (K′ , refl , g′)) = zk∼ g′
ign∼ (inj₂ (K , refl , g)) (inj₁ refl) = kz∼ g
ign∼ (inj₂ (K , refl , g)) (inj₂ (K′ , refl , g′)) = kk∼ g g′

s⊑s→≼ : ∀ {a c} → suc a ⊑ᴵ suc c → (a ≺ᴵ c) ⊎ (a ≅ᴵ c)
s⊑s→≼ (s⊑ e zero)    = inj₂ e
s⊑s→≼ (s⊑ e (suc q)) = inj₁ (via e q)

≼→⊑ : ∀ {a b} → (a ≺ᴵ b) ⊎ (a ≅ᴵ b) → a ⊑ᴵ b
≼→⊑ (inj₁ (via e q)) = ⊑ᴵ-trans (≅ᴵ→⊑ᴵ e) (Sim→⊑ᴵ (λ q′ → <ᴵ-trans q′ q))
≼→⊑ (inj₂ e) = ≅ᴵ→⊑ᴵ e

≼-suc : ∀ {a c} → (a ≺ᴵ c) ⊎ (a ≅ᴵ c) → (a ≺ᴵ suc c) ⊎ (a ≅ᴵ suc c)
≼-suc (inj₁ s) = inj₁ (≺-suc s)
≼-suc (inj₂ e) = inj₁ (via e zero)

floIgn : ∀ {c} k′ → (k′ ≺ᴵ c) ⊎ (k′ ≅ᴵ c) → IgnL c (flo k′)
floIgn zero      h = inj₁ refl
floIgn (suc k″)  h = inj₂ (k″ , refl , inj₂ (inj₁ (≺≼ (via (≅ᴵ-refl k″) zero) h)))
floIgn (lim f s) h = inj₂ (lim f s , refl , inj₂ h)

alignHigh : ∀ {c k₁ k₂ φ φ′} {a : Ordˢ k₁} {b : Ordˢ k₂} → IgnL c φ → IgnL c φ′ → k₁ ⊑ᴵ suc c → k₂ ⊑ᴵ suc c →
            (d : a ≅ˢ b) → AlignT c φ φ′ d
alignHigh g g′ l₁ l₂ z≅ = tt
alignHigh g g′ l₁ l₂ (s≅ e) = ign∼ g g′ , alignHigh g g′ l₁ l₂ e
alignHigh g g′ l₁ l₂ (l≅ h) = λ n → alignHigh g g′ l₁ l₂ (h n)
alignHigh g g′ l₁ l₂ (lᵢ≅ e h) = λ x y r → alignHigh g g′ l₁ l₂ (h x y r)
alignHigh {k₁ = suc k′} g g′ l₁ l₂ (upˡ {r = zero} e) =
  alignHigh (floIgn k′ (s⊑s→≼ l₁)) g′ (≼→⊑ (≼-suc (s⊑s→≼ l₁))) l₂ e
alignHigh {k₁ = lim f s} g g′ l₁ l₂ (upˡ {r = self n} e) = alignHigh g g′ (⊑ᴵ-trans (Sim→⊑ᴵ (lim n)) l₁) l₂ e
alignHigh {k₂ = suc k′} g g′ l₁ l₂ (upʳ {r = zero} e) =
  alignHigh g (floIgn k′ (s⊑s→≼ l₂)) l₁ (≼→⊑ (≼-suc (s⊑s→≼ l₂))) e
alignHigh {k₂ = lim f s} g g′ l₁ l₂ (upʳ {r = self n} e) = alignHigh g g′ l₁ (⊑ᴵ-trans (Sim→⊑ᴵ (lim n)) l₂) e
alignHigh g g′ l₁ l₂ (ŝ≅ k ec et eg) = alignHigh g g′ l₁ l₂ et , (λ η e η′ e′ eη → alignHigh g g′ l₁ l₂ (eg η e η′ e′ eη))
alignHigh g g′ l₁ l₂ (ĉ≅ ec dt dg eo eO) = alignHigh g g′ l₁ l₂ eo , (λ η e η′ e′ eη → alignHigh g g′ l₁ l₂ (eO η e η′ e′ eη))
```
**$\Omega_\eta$ 的对齐与分支的互模拟.** `AlignΩᵗ`: `Ωˢ-≅ e` 的推导在 $\eta\sqsubseteq c+2$ 时 `AlignT c` (根地板只在 $\Omega_0=1$ 的后继步被比较, 两侧都是 `fk`, $\cong$; 分支经 `up zero` 后进入 `alignHigh`). **`bRᵗ`**: 对一切 $\eta\cong\eta'$ 与 $c$ ($\eta\sqsubseteq c+2$), Uniform2 `BranchΩ` 的 `bR` 字段在目标 $\succeq c$ 处成立, 对**一切** $\approx_{[c]}$ 相关的底, 不要标签.

```agda
≼s→IgnL : ∀ {c} a → (a ≺ᴵ suc c) ⊎ (a ≅ᴵ suc c) → IgnL c (flo a)
≼s→IgnL zero h = inj₁ refl
≼s→IgnL (suc a′) (inj₁ (via (s≅ e) zero)) = inj₂ (a′ , refl , inj₂ (inj₁ (via e zero)))
≼s→IgnL (suc a′) (inj₁ (via (s≅ e) (suc q))) = inj₂ (a′ , refl , inj₂ (inj₁ (via e (<ᴵ-trans zero q))))
≼s→IgnL (suc a′) (inj₂ (s≅ e)) = inj₂ (a′ , refl , inj₂ (inj₂ e))
≼s→IgnL (lim f s) (inj₁ (via e zero)) = inj₂ (lim f s , refl , inj₂ (inj₂ e))
≼s→IgnL (lim f s) (inj₁ (via e (suc q))) = inj₂ (lim f s , refl , inj₂ (inj₁ (via e q)))
≼s→IgnL (lim f s) (inj₂ ())

AlignΩᵗ : ∀ {c η η′ K K′} (e : η ≅ᴵ η′) → η ⊑ᴵ suc (suc c) → K ≅ᴵ K′ → AlignT c (fk K) (fk K′) (Ωˢ-≅ e)
AlignΩᵗ z≅ le eK = fk∼ eK , tt
AlignΩᵗ {c} {suc a} {suc a′} (s≅ e) le eK = λ x y r →
  alignHigh (≼s→IgnL a (s⊑s→≼ le)) (≼s→IgnL a′ (s⊑s→≼ le′)) (≼→⊑ (s⊑s→≼ le)) (≼→⊑ (s⊑s→≼ le′)) r
  where le′ : suc a′ ⊑ᴵ suc (suc c)
        le′ = ⊑ᴵ-trans (≅ᴵ→⊑ᴵ (s≅ (≅ᴵ-sym e))) le
AlignΩᵗ (l≅ h) (l⊑ hh) eK = λ n → AlignΩᵗ (h n) (hh n) eK

bRᵗ : ∀ {c η η′} (e : η ≅ᴵ η′) → η ⊑ᴵ suc (suc c) →
      fold 1 (fk η) (λ e q → e (suc q)) (Ω̂A 0) (Ωˢ η) ≈₁[ c ] fold 1 (fk η′) (λ e q → e (suc q)) (Ω̂A 0) (Ωˢ η′)
bRᵗ e le = fold-≅1ᵗ (fk∼ z≅) selfΩ̂0ᵗ (Ωˢ-≅ e) (AlignΩᵗ e le e)
```
**读法.** `bRᵗ` 的条件 $\eta\sqsubseteq c+2$ 正是 "尾巴 $\Omega_\eta$ 的一切内部地板 ($\preceq\eta-2$) 都 $\preceq$ 目标". 不满足时 (目标低于内部地板) 只剩折叠情形 (节点层 $\eta-1\succ$ 目标): 分支只在链点处计值, 而链点是底在节点层上的输出, 见 Relative §1.

## §6 $\eta=3$ 的 `gi` 行

Uniform2 的失败点: 深度 1、尾巴 $\Omega_3$、节点层 2 的 `gi` 行、分支路径 `up zero x`、输入对 $x=1$ (第 2 层自带后继) 与 $y=$ `up zero (up zero 1)`. 依目标的形式: $c=1$ 时成立 (`AlignΩ₃ᵗ`, 因为两侧的地板 `fk 1`、`fz` 都 $\preceq1$); $c=0$ 时与 Uniform2 的 `¬AlignΩ₃` 相同 (`¬AlignΩ₃⁰`: `fk 1 ∼[ zero ] fz` 无居留).

```agda
one three : Ordᴵ
one = suc zero
three = suc two

AlignΩ₃ᵗ : AlignT one (fk three) (fk three) (Ωˢ-refl three)
AlignΩ₃ᵗ = AlignΩᵗ (≅ᴵ-refl three) ⊑ᴵ-refl (≅ᴵ-refl three)

no1z : fk one ∼[ zero ] fz → ⊥
no1z (kz∼ (inj₁ ()))
no1z (kz∼ (inj₂ (inj₁ (via e ()))))
no1z (kz∼ (inj₂ (inj₂ ())))

x₃ y₃ : Ordˢ two
x₃ = Ord₊ˢ.suc Ord₊ˢ.zero
y₃ = Ord₊ˢ.up zero (Ord₊ˢ.up zero (Ord₊ˢ.suc Ord₊ˢ.zero))

r₃ : x₃ ≅ˢ y₃
r₃ = upʳ (upʳ (s≅ z≅))

¬AlignΩ₃⁰ : AlignT zero (fk three) (fk three) (Ωˢ-refl three) → ⊥
¬AlignΩ₃⁰ al = no1z (proj₁ (al x₃ y₃ r₃))
```
**读法.** 目标 $\succeq1$ 处 `gi` 行 (节点层 2) 的伪输入只在穿透 ($i\succ2$) 时出现, 输入里的地板 $\preceq1\prec i$, 读不到: 这一半与 Uniform2 §6 的设想一致. 目标 0 处节点层 2 走折叠, 分支只在链点上计值, 链点不是伪输入, 但链点之间的关系不由尾巴的推导给出, 而由**底**在目标 2 处的输出给出: 那里 Uniform2 的设想不成立 (Relative §1 的编译反例正是在这一行、这一路径上).

## §7 (a′) 依目标的地板见证

`FW[ c ]`/`FlrLab[ c ]`: 只有 $\succ c$ 的地板项要见证 (平凡或被前缀里出现的带 `Idx` 的下标支配). 理由与 §1 相同: 弹栈的界的来源 `src` 若是地板项 $K$, 则 $i\prec K$ (`pickW` 只读这样的项), 而 $c\preceq i$. `LW[ c ]`: 只在目标 $\succeq c$ 处要求带标签.

```agda
LW[_] : ∀ {φ} → Ordᴵ → Run φ → T → Set
LW[_] {φ} c R u = ∀ {i ℓ w} (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → Up c i →
                  LabL₊ i Ll (R ev p) (ψᵗ w u ∷ [])

LW→LW[] : ∀ {c φ} {R : Run φ} {u} → LW R u → LW[ c ] R u
LW→LW[] h ev p Iw ei ki u = h ev p Iw ei ki

FW[_] : Ordᴵ → Flr → T → PT → T → Set
FW[ c ] φ ps y ys = ∀ {K} → InF K φ → c ≺ᴵ K →
                    (K ≅ᴵ zero) ⊎ Σ T λ w → Σ (Idx w) λ Iw → ((K ≺ᴵ lvI Iw) ⊎ (K ≅ᴵ lvI Iw)) × Ob w ps y ys

FW→FW[] : ∀ {c φ ps y ys} → FW φ ps y ys → FW[ c ] φ ps y ys
FW→FW[] F k s = F k

FlrLab[_] : Ordᴵ → Flr → T → Set
FlrLab[ c ] φ ps = ∀ {K} → InF K φ → c ≺ᴵ K →
                   (K ≅ᴵ zero) ⊎ Σ T λ w → Σ (Idx w) λ Iw → ((K ≺ᴵ lvI Iw) ⊎ (K ≅ᴵ lvI Iw)) × Occ w ps

FlrLab→[] : ∀ {c φ ps} → FlrLab φ ps → FlrLab[ c ] φ ps
FlrLab→[] F k s = F k

FlrLab[]-ign : ∀ {c φ ps} → (∀ {K} → InF K φ → Ign c K) → FlrLab[ c ] φ ps
FlrLab[]-ign G k s with G k
... | inj₁ k0 = inj₁ k0
... | inj₂ kc = ⊥-elim (≺ᴵ-irrefl (≺≼ s kc))

FW-popᵗ : ∀ {c fl π} → FlrLab[ c ] fl π → FW[ c ] (fl ⊔ fk zero) π ΩΩ []
FW-popᵗ F (inr ink) s = inj₁ z≅
FW-popᵗ F (inl k) s with F k s
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → OccPre _ o)
```
**弹栈行与闭包定理.** `cloWᵗ` 与 Uniform2Base `cloW` 逐字, 只把 `pickW` 换成 `pickWᵗ` (多一个 `Up c i`, 地板项的见证由 `fw k (≼≺ u s)` 取). `goodΩ̂0Wᵗ`: 依目标的地板标签加尾巴的 `LW`, 则 $P+\Omega_\Omega$ 在目标 $\succeq c$ 处带标签 (Uniform2Depth1 `gwΩ̂0` 的相对版).

```agda
module _ {c φ} {ps : T} {y : PT} {ys : T} {t : Run (φ ⊔ fk zero)} {g : (η : Ordᴵ) → Run (φ ⊔ fk η)}
         (fw : FW[ c ] (φ ⊔ fk zero) ps y ys) (cs : cof (y ∷ ys) ≡ cΩ []) where

  pickWᵗ : ∀ {i M w} → Up c i → (Iw : Idx w) → i ≅ᴵ lvI Iw → (M ≡ i) ⊎ ((i ≺ᴵ M) × Σ Ordᴵ λ K → InF K (φ ⊔ fk zero) × (M ≡ K)) →
           Σ T λ w′ → Σ (Idx w′) λ Iw′ → (suc M ⊑ᴵ suc (lvI Iw′)) × (∀ θ → Occ w′ (ψᵗ w (ps ++ fsT (y ∷ ys) θ) ∷ []))
  pickWᵗ {w = w} u Iw ei (inj₁ refl) = w , Iw , sB (inj₂ ei) , (λ θ → oh)
  pickWᵗ u Iw ei (inj₂ (s , K , k , refl)) with fw k (≼≺ u s)
  ... | inj₁ k0 = ⊥-elim (≺0 s k0)
  ... | inj₂ (w′ , Iw′ , kw , ob′) = w′ , Iw′ , sB kw , (λ θ → od (ob′ θ))

  cloWᵗ : LW[ c ] t (ps ++ fsT (y ∷ ys) (natT 1)) →
          (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → LW[ c ] (g (toLevel Y hY)) (ps ++ fsT (y ∷ ys) θ)) →
          LW[ c ] (cloA 0 t g) (ps ++ (y ∷ ys))
  cloWᵗ h₀ hg {w = []} ev p Iw ei ki u = ⊥-elim (ne-w Iw ei ki refl)
  cloWᵗ h₀ hg {w = x ∷ xs} ev p Iw ei ki u =
    gŝ ki (trans (cofW (x ∷ xs) ps y ys) (trans (cong (cofA (x ∷ xs)) cs) (H1-pen x xs)))
       (proj₁ (proj₂ Pk)) (proj₁ (proj₂ (proj₂ Pk)))
       (λ θ → subst (Occ _) (sym (H1W x xs ps y ys cs θ)) (proj₂ (proj₂ (proj₂ Pk)) θ))
       (subst (LabL₊ _ Ll _) (sym (H1W x xs ps y ys cs (natT 1))) (h₀ ev p Iw ei ki u))
       (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (H1W x xs ps y ys cs θ))
            (hg θ Y hY lY nθ lt (evη φ B (toLevel Y hY) e) (lim 0 (iF B)) Iw ei ki u))
    where
    B = bound (φ ⊔ fk zero) ev p
    Pk = pickWᵗ u Iw ei (src B)

goodΩ̂0Wᵗ : ∀ {c fl} {P : Run fl} {π} → FlrLab[ c ] fl π → LW P π → LW[ c ] (Ω̂A 0 P) (π ++ ΩΩ ∷ [])
goodΩ̂0Wᵗ {fl = fl} {P} {π} F hP =
  cloWᵗ {t = fold 0 (fk zero) (λ e → e) P (Ωˢ (suc zero))} {g = λ η → fold 0 (fk η) (λ e q → e (suc q)) P (Ωˢ η)}
        (FW-popᵗ F) refl
        (LW→LW[] {R = fold 0 (fk zero) (λ e → e) P (Ωˢ (suc zero))}
                 (TlW.tlWV hP {φ = fk zero} {cv = λ e → e} {t = Ωˢ (suc zero)} (LabL-Ω one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _))))
        (λ θ Y hY lY nθ lt → LW→LW[] {R = fold 0 (fk (toLevel Y hY)) (λ e q → e (suc q)) P (Ωˢ (toLevel Y hY))}
                 (TlW.tlWV hP {φ = fk (toLevel Y hY)} {cv = λ e q → e (suc q)} {t = Ωˢ (toLevel Y hY)} (LabL-Ω Y hY lY nθ (≅ᴵ-refl _))))
```
**读法.** 目标 0 的部分 (`clo0`) 不需要单独的相对版: 目标 0 时要见证的是一切 $\succ0$ 的地板项, 与目标无关的 `FW` 只差 "既不 $\succ0$ 也不 $\cong0$" 的退化项 (如 `Z⁰`). 所以 (a′) 的内容全在目标非零处, 而深度 1 的 `GW1` 正是对一切非零带标签目标量化的.

## §8 三种地板与 $\eta=4$

深度 1 的后继行把尾巴的当前地板放进副本的底 (`FL-rep` 的位置). 帧标签是 $\psi_\Omega(\zeta+\mathrm{pred}\,y)$. 三种情形:

- 第 2 层的尾巴 (地板 `fk 1`): 帧标签的下标 $\Omega=\Omega_1$ 本身含 $1$ (`os oh`), 永远见证 (`FL-Ω₁`, 对一切 $b$). 这就是 Uniform2 §6 所说 "层 2 地板总由 Ω₁ 里的 1 见证", 也是 $\eta\le3$ 不需要 (a′) 的原因.
- 链点 (标签首项为 $\psi_w(\cdot)$, $w$ 带 `Idx`): 见证一切 $\preceq\mathtt{lvl}\,w$ 的地板 (`FL-head`). 节点层 $j$ 上的链点标签首项下标的层号 $\cong j$, 所以链点作为第 $j$ 层输入时它的一切地板 ($\prec j$) 都有见证.
- 伪输入 (第 3 层的树 `suc zero`, 标签 $1$, 地板 `fk 2`): 帧标签 $\psi_\Omega(1)$ 里出现的下标只有 $\Omega$ (无 `Idx`, `noIdxΩ`)、$1$ ($\mathtt{lvl}\cong1$) 与 $0$, 都不能支配 $2$ (`¬FL₄`, 编译). 依目标的形式在一切目标 $\succeq2$ 处平凡成立 (`FL₄[]`); 而 $\Omega_4$ 的 `gi` 行 (节点层 3) 只在穿透目标 $\succ3$ 处对任意输入计值.

```agda
ψΩᵗ′ : T → T
ψΩᵗ′ b = ψᵗ Ωᵗ b ∷ []

FL-Ω₁ : ∀ b → FlrLab (fk one) (ψΩᵗ′ b)
FL-Ω₁ b ink = inj₂ (natT 1 , I₁ , inj₂ (≅ᴵ-refl _) , os oh)

FL-head : ∀ {K w u ys} (Iw : Idx w) → (K ≺ᴵ lvI Iw) ⊎ (K ≅ᴵ lvI Iw) → FlrLab (fk K) (ψΩᵗ′ (ψᵗ w u ∷ ys))
FL-head Iw kw ink = inj₂ (_ , Iw , kw , od oh)
```
```agda
noIdxΩ : Idx Ωᵗ → ⊥
noIdxΩ (Y , hY , l0 () e , nY)
noIdxΩ (Y , hY , l1 () e l , nY)
noIdxΩ (Y , hY , lω () e h , nY)

occ1′ : ∀ {w} → Occ w (natT 1) → w ≡ []
occ1′ oh = refl
occ1′ (od ())
occ1′ (os ())
occ1′ (ot ())

lvl-small : ∀ {w} (Iw : Idx w) → Occ w (ψΩᵗ′ (natT 1)) → (lvI Iw ≅ᴵ zero) ⊎ (lvI Iw ≅ᴵ one)
lvl-small Iw oh = ⊥-elim (noIdxΩ Iw)
lvl-small Iw (od o) with occ1′ o
lvl-small (Y , hY , lY , nY) (od o) | refl = inj₁ (lab[]≅0 hY lY)
lvl-small Iw (os oh) = inj₂ (Ieq Iw I₁)
lvl-small Iw (os (od ()))
lvl-small Iw (os (os o)) with occ1′ o
lvl-small (Y , hY , lY , nY) (os (os o)) | refl = inj₁ (lab[]≅0 hY lY)
lvl-small Iw (os (ot ()))
lvl-small Iw (ot ())

-- a floor item K above 1 has no witness in the frame label ψ_Ω(1)
small-≼ : ∀ {K L} → one ≺ᴵ K → (L ≅ᴵ zero) ⊎ (L ≅ᴵ one) → (K ≺ᴵ L) ⊎ (K ≅ᴵ L) → ⊥
small-≼ s (inj₁ e0) kw = ≺0 (≺≼ s kw) e0
small-≼ s (inj₂ e1) kw = ≺ᴵ-irrefl (≺ᴵ-respʳ (≺≼ s kw) e1)

¬FL-fake : ∀ {K} → one ≺ᴵ K → FlrLab (fk K) (ψΩᵗ′ (natT 1)) → ⊥
¬FL-fake s F with F ink
... | inj₁ k0 = ≺0 s k0

... | inj₂ (w , Iw , kw , o) = small-≼ s (lvl-small Iw o) kw

¬FL₄ : FlrLab (fk two) (ψΩᵗ′ (natT 1)) → ⊥
¬FL₄ = ¬FL-fake (via (≅ᴵ-refl _) zero)

FL₄[] : ∀ {c ps} → Up two c → FlrLab[ c ] (fk two) ps
FL₄[] u = FlrLab[]-ign (λ { ink → inj₂ u })
```
**读法.** `¬FL-fake` 对一切 $K\succ1$ 成立: 这是 TopDown `noExpected` 的同一现象 (标签小、层号高的树) 在深度 1 帧标签上的形式. 它说明目标无关的 `FlrLab` 对 $\eta\ge4$ 的分支确实不够, 而依目标的形式 (`FL₄[]`) 恰好覆盖伪输入出现的目标.

## §9 `up (self n)` 下的地板

`fold` 的 `up (self n)` 子句保持父层的地板. 父层为极限层 $L$ 时地板是 `flo L = fk L`, 子树在层 $f\,n\prec L$ 上, 它自己的后继步 (在下一个 `up zero` 之前) 以 `fk L` 为地板. 第一个例子: $\psi_0(\psi_\Omega(\Omega_\omega))$, 尾巴 $\Omega_\omega=\lim_n$ `up (self n)` $\Omega_n$, 第 0 支 $\Omega_0=1$ 是地板 `fk ω` 下的后继. 下面在目标 0、底 $\varnothing$ 上计值: 第 0 支的第 2 份副本 ($\psi_0(\Omega_\Omega\cdot2)$ 的位置) 弹栈的界字面是 $\omega+1$; 同一位置的紧界是 $1$ (Uniform2 §5 `T2ᵀ` 的 `kc one`). 帧标签 $\psi_\Omega(1)$ 不见证 $\omega$ (`¬FLω`); 依目标的形式只在目标 $\succeq\omega$ 处成立 (`FLω[]`).

```agda
ℓω : Ordᴵ
ℓω = suc ωᴵ

Bω : A 1 (fk zero ⊔ fk ωᴵ)
Bω = fold 1 (fk ωᴵ) (λ e q → e (suc q)) (Ω̂A 0) (Ωˢ ωᴵ)

evω : Ev ℓω (fz ⊔ (fk zero ⊔ fk ωᴵ))
evω = tt , ((λ { zero → suc (lim 1 zero) }) , (λ q → q))

pω : zero <ᴵ ℓω
pω = suc (lim 1 zero)

Tω : Ordˢ zero
Tω = Bω ∅ᴿ evω pω

up-self-bound : kind (walkˢ Tω (0 ∷ 2 ∷ [])) ≡ kcˢ (suc ωᴵ)
up-self-bound = refl

1≺ω : one ≺ᴵ ωᴵ
1≺ω = via (≅ᴵ-refl one) (lim 2 zero)

¬FLω : FlrLab (fk ωᴵ) (ψΩᵗ′ (natT 1)) → ⊥
¬FLω = ¬FL-fake 1≺ω

FLω[] : ∀ {c ps} → Up ωᴵ c → FlrLab[ c ] (fk ωᴵ) ps
FLω[] u = FlrLab[]-ign (λ { ink → inj₂ u })
```
**读法.** 与 §8 的伪输入不同, 这个位置在**一切**目标处都被计值 (它在 `lim` 之下, 不在 `limᵢ` 之下), 所以依目标的见证覆盖不了它. 目标 0 时链点的层号远大于 $\omega+1$ (链点是 $\psi_0(\Omega_\Omega+\cdots)$), 支配可以按值 (经 `Lab-oc`) 而不是按出现的下标证出, 标签仍可能成立; 目标 $1\le i<\omega$ 时 `gŝ` 行要求一个出现在每个点标签里、层号 $\succeq\omega$ 的下标, 而点标签 $\psi_i(\Omega_\Omega+\Omega_\theta)$ (底为 $\varnothing$) 里没有, 所以这里的树与 EBO 的基本列不能由 `LabL₊` 对上 (分析, 未编译成否定). 这是定义层面的偏差 (紧的做法是 `up (self n)` 处把地板换成 `flo (f n)`), 不是证明的量化问题. 它不影响 $\psi_0(\Omega_\Omega^2)$ 在目标 0 的计值 (Relative §4), 但影响 `BranchΩ` 的 `bW` 字段在 $\theta=\omega$ 的实例.

## §10 对比表: 目标无关与依目标

| 内容 | 目标无关 (Uniform2Base/Depth1) | 依目标 (本文) | 状态 |
|---|---|---|---|
| 地板关系 | `_∼ᶠ_` (平凡项可对空位) | `_∼[ c ]_` (可忽略项 $\preceq c$ 可对空位或彼此) | 定义 |
| 界 | `bound-≅` | `bound-≅ᵗ` (目标 $\succeq c$) | 定理 |
| 运行互模拟 | `_≈ᴿ_` (一切目标) | `_≈[ c ]_` (目标 $\succeq c$) | 定义; `≈→≈[]` |
| 深度 0 折叠 | `fold-≅0` | `fold-≅0ᵗ` | 定理 |
| 层对齐 | `AlignD` | `AlignT c` | 定义 |
| 深度 1 折叠 | `fold-≅1` | `fold-≅1ᵗ` | 定理 |
| $\cong^\mathsf s\Rightarrow$ 对齐 | 只对第 0、1 层 (`lowA`) | 层号 $\sqsubseteq c+1$ 的一切推导 (`alignHigh`) | 定理 |
| `BranchΩ.bR` | 假设 (实际**假**, Relative §1) | `bRᵗ`: 目标 $\succeq\eta-2$ 处对一切底 | 定理 |
| $\eta=3$ 的 `gi` 行 | `¬AlignΩ₃` | `AlignΩ₃ᵗ` ($c=1$), `¬AlignΩ₃⁰` ($c=0$) | 定理 / 否定 |
| 地板见证 | `FlrLab`, `FW` (一切项) | `FlrLab[ c ]`, `FW[ c ]` (只 $\succ c$ 的项) | 定义; `FlrLab→[]`, `FW→FW[]` |
| 弹栈行 | `cloW` | `cloWᵗ` | 定理 |
| $\Omega_\Omega$ 闭包 (目标非零) | `gwΩ̂0` | `goodΩ̂0Wᵗ` | 定理 |
| 第 2 层地板 | `fl₂`/`FL₂` (逐例) | `FL-Ω₁` (一切帧标签) | 定理 |
| 第 3 层伪输入 ($\eta=4$) | `¬FL₄` | `FL₄[]` (目标 $\succeq2$) | 否定 / 定理 |
| `up (self n)` | 未查 | `up-self-bound` (`refl`), `¬FLω`, `FLω[]` | 否定 (定义偏差) |

## §11 结论与边界

**(b′) 证得的部分.** 依目标的互模拟 (`_∼[_]_`, `_≈[_]_`, `_≈₁[_]_`, `AlignT`) 与它的折叠定理 (`fold-≅0ᵗ`, `fold-≅1ᵗ`) 都是无条件定理; "由 $\cong^\mathsf s$ 推出" 在目标高于尾巴的一切地板时成立 (`alignHigh`); 分支 $\Omega_\eta$ 的互模拟在目标 $\succeq\eta-2$ 处对一切底成立 (`bRᵗ`), $\eta=3$ 的 `gi` 行在 $c=1$ 处对齐 (`AlignΩ₃ᵗ`). **未证、且不能这样证的部分**: 目标 $\prec\eta-2$ 处 (折叠情形). 那里分支只在链点上计值, 链点之间的关系来自底在节点层上的输出; 对任意 $\cong^\mathsf s$ 相关的底它不层对齐, `BranchΩ (Ω̂A 0) []` 因此是假的 (Relative §1, 编译). 所以 Uniform2 §6 对 (b′) 的表述 ("派发只升目标, ≼ 目标的地板项从不被读到, 只改量化范围") 只对了一半: 对一次计值内部正确 (§1–§5), 对链点不正确.

**(a′) 证得的部分.** 依目标的地板见证 (`FlrLab[ c ]`, `FW[ c ]`) 与弹栈行 `cloWᵗ`、闭包 `goodΩ̂0Wᵗ` 是定理. $\eta\le3$ 不需要它 (`FL-Ω₁`), $\eta=4$ 的伪输入需要且被它覆盖 (`¬FL₄` 与 `FL₄[]`), 链点总有见证 (`FL-head`). 一般深度 1 尾巴的 W 定理 (把 Uniform2Depth1 `W1₁` 推广到任意层并改用 `FlrLab[ c ]`) **未写**: 它要对尾巴推导做 "遗传的、在 `gi` 输入处分两半" 的前提 (穿透处对一切输入以抬高的目标下界, 折叠处只对链点), 而链点的见证要从 `LW` 的输出标签读出 (`FL-head`), 这需要 `LW` 输出 "首项下标" 的形状引理.

**`up (self n)`.** 否定: 极限层地板在 `up (self n)` 下不紧 (`up-self-bound`), 帧标签不见证它 (`¬FLω`), 依目标的见证覆盖不了 (位置在一切目标处计值). 定义层面的偏差, 不是 (a′) 能解决的.

**字面与模 $\cong$.** `refl`: `up-self-bound`. 其余都是对一切环境与证据的定理或否定.

**工程注记 (编译失败的写法).**

1. `≼s→IgnL` 的后继情形 `(inj₁ (via (s≅ e) zero))` 最初写成 `inj₂ (inj₂ e)`: 这里 $a'+1\cong c$ 而不是 $\cong c+1$, 应为 $a'\prec c$:

        error: [UnequalTerms]
        b != (suc b) of type Ordᴵ
        when checking that the expression e has type a′ ≅ᴵ suc b

2. `AlignΩᵗ` 的极限情形最初把根地板换成 `fk (lim f s)`: `up (self n)` 不换地板, 两侧仍是最初的 `fk K`、`fk K′`:

        error: [UnequalTerms]
        lim (λ z → f z) _s_3512 != K of type Ordᴵ

3. `goodΩ̂0Wᵗ` 里 `LW→LW[] (TlW.tlWV hP …)` 不给出 `tlWV` 的 `φ`/`cv`/`t` 时报 `[UnsolvedConstraints]` (合一器要从 `fold 0 … ev p` 反解运行), 一律显式给出 (Uniform2Base §12 第 4 条的同一现象).
4. 从 Prefix 导入 `kc` 与本文的变量名 `kc` (`Ign c K` 的第二支) 冲突: `[ConstructorPatternInWrongDatatype] kc is not a constructor of the datatype _⊎_`. 改为 `renaming (kc to kcˢ)`.
