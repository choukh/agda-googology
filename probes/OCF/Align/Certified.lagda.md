# 认证层号: ⊑-步进能否越过 ψ₀ 片段

> [Cumsum](Cumsum.lagda.md) §7 第 3 条与 §8 留下的开放问题: 消去 `cumsum` 的认证层号能否越过 $\psi_0$ 片段 ($\varepsilon_0$). Cumsum 推荐的下标类型 `Ordʷ` 的 `lim` 只要求相邻两项**前驱包含** $\sqsubseteq$ (非严格). 本文检验的假设是: 严格单调的反例 (`ψᴱ-not-mono`, 两棵树的 $\psi_0$ 像相同) 对非严格的 $\sqsubseteq$ 无害, 所以在树族上定义遗传的 $\sqsubseteq$ 与步进谓词 `Step` 后, 加法、提升、$\Omega$ 与忠实折叠 $\psi$ 都保持它们, 于是对角线的每一棵树都自带层号证据, 安全路径引理不再需要.
>
> 结论先说:
>
> 1. **假设不成立, 在 $\psi$ 处.** $\psi$ 不保持 $\sqsubseteq$, 第 1 层就有编译过的反例 (`ψ-not-⊑mono`): $\mathrm{suc}\,a_1\sqsubseteq\Omega_1$, 但 $\psi_0(\mathrm{suc}\,a_1)\not\sqsubseteq\psi_0(\Omega_1)$. 原因是 $\sqsubseteq$ 在后继上就是严格序 ($\mathrm{suc}\,a\sqsubseteq b\iff a\prec b$), 而规则 4 把 $\psi(a)$ 复制成 $\psi(a)\cdot n$; 于是 "$\psi$ 保持 $\sqsubseteq$" 蕴含 "$\psi$ 保持 $\prec$" (`mono⇒strict`), Cumsum §2.4 的严格反例经规则 4 原样回来. 遗传步进谓词对 $\psi$ 不封闭 (`ψ-breaks-Stepᴴ`). 就 $\psi$ 而言, 候选 B 没有减轻候选 A 的负担.
> 2. **安全路径引理的充分性一半已证.** 对目标层 $i$ 的折叠 $\psi_p$, 只沿它自己会走的分支 (下标 $j<i$ 的 `limᵢ` 走全部分支, 其余只走 $\gamma$-链分支) 定义结构序 $\prec_p$ 与前驱包含 $\sqsubseteq_p$, 则 $\psi_p$ 把 $\sqsubseteq_p$ 送到 $\sqsubseteq$, 不需要任何前提 (`ψ-⊑ₚ`). 无 `limᵢ` 的输入上 $\sqsubseteq$ 蕴含 $\sqsubseteq_p$ (`⊑→⊑ₚ`); 规则 6 的链在 "$f$ 把 $\sqsubseteq$ 送到 $\sqsubseteq_q$" 下是 $\sqsubseteq$-递增的 (`rule6-chain`).
> 3. **第二个障碍, 与规则 6 无关: 层号证明是相关的.** $\Omega$ 在极限层的第 $n$ 项用证明 `lim n` 提升, 这个证明被写进每个 `limᵢ` 节点. 结构序要求前驱字面相等, 于是 $\Omega_\omega$ 的相邻两项不 $\sqsubseteq$ (`Ω-not-step`), 对角线实际用到的 $\Omega_{\varepsilon_0}$ 也一样 (`Ωε₀-not-step`). 加法、提升、零层与后继层的 $\Omega$ 保持 $\sqsubseteq$ 与遗传步进 (已证).
> 4. **认证层号要原生构造, 不能从树上读.** 树上的遗传谓词不能喂给 `toLevel`: 同一棵子树经不同路径得到的证据不同, 而 `Ordʷ` 的 $\sqsubseteq^\mathsf{w}$ 对证据敏感 (§7). 可用的 `Step` 是归纳-递归的证书, `lim` 的证据直接是层号之间的 $\sqsubseteq^\mathsf{w}$; `toLevel` 与基本列逐项交换 (`toLevel-lim`, `Ω-exact`, 都是 `refl`), 每个 `Ordʷ` 的遗忘像都有典范证书 (`cert`). $\psi_0$ 片段在 `Ordʷ` 上原生认证 (`ψ⁰ʷ`), 给出无累积和的层号 $\varepsilon_0$, 其 $\Omega$-基本列逐项是 $\Omega_{x_2[n]}$ (`refl`), 遗忘后与忠实折叠的 $x_2$ 外延相等 (`x₂-link`).
> 5. **对角线: 认证到 $x_2=\varepsilon_0$ 为止.** $x_3=\psi_0(\Omega_{\varepsilon_0})$ 用无累积和的层号定义, `FGHʷ x₃ 99` 是闭项; $x_3$ 自己的层号未能认证. 条件包 `CertDiag`/`Diagonal` 在 "每一步的层号存在" 的前提下组装出带证书的 `BTBOʷ` (无累积和, $\Omega$-基本列逐项精确, FGH 是闭项), 其第 0 步已兑现 (`prefix`). 缺口精确在第 1 步: 找 $L_2$ 使 $\varepsilon_0^\mathsf{w}\sqsubseteq^\mathsf{w}L_2$ 且 `forget L₂ ≈ x₃`. §10 说明这一步被内涵性挡住, 修复需要商化的 $\sqsubseteq$ 或函数外延性, 不是再证一条关于规则 6 的引理就够的.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. `Ordʷ`、树族与 `ψʷ` 从 Cumsum 的模块 `W` 导入, 没有复制任何定义, `W` 也不缺东西; 对 `W` 的补充只有 `coe` 的合成引理 `coe-coe₀`、`<ʷ` 的无自反与一个与 `Ωʷ` 里的 `lim n` $\eta$-等价的提升证据 `limS`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Certified where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Cumsum using (module W)
open W
```

约定: `_<ʷ_`/`_⊑ʷ_` 是下标 `Ordʷ` 上的结构序与前驱包含 (Cumsum §3.1); `_≺_`/`_⊑_` 是本文在树族 `Ordᵂ ℓ` 上新定义的同名关系; `_+ʷ_`, `↑ʷ`, `Ωʷ`, `ψʷ` 是 `W` 里的树运算, `ψʷ` 就是 [Finite](Finite.lagda.md) §3 的忠实折叠 $\psi^\mathsf{E}$ (BTBOFix 的直接折叠加 $\Omega_0=1$ 与链起点 $\Omega_j$).

## §0 两条下标引理

`<ʷ` 良基, 所以无自反; `ψʷ` 的 `<ʷ-dec` 派发中互相矛盾的分支靠它排除. 搬运合成 `coe-coe₀` 与 [FiniteAll](FiniteAll.lagda.md) §2 逐字相同, 只换了下标类型.

```agda
data Accʷ (a : Ordʷ) : Set where
  acc : (∀ {b} → b <ʷ a → Accʷ b) → Accʷ a

accʷ : ∀ a {b} → b <ʷ a → Accʷ b
accʷ (suc a)   zero      = acc (accʷ a)
accʷ (suc a)   (suc p)   = accʷ a p
accʷ (lim f s) (lim n p) = accʷ (f n) p

<ʷ-irrefl : ∀ {a} → a <ʷ a → ⊥
<ʷ-irrefl {a} = go (acc (accʷ a)) where
  go : ∀ {a} → Accʷ a → a <ʷ a → ⊥
  go (acc h) p = go (h p) p

coe-coe₀ : ∀ {j ℓ₁ ℓ₂} (r : j <ʷ ℓ₁) (q : j <ʷ ℓ₂) (x : Ordᵂ j) →
           coeʷ {p = r} {q = q} (coe₀ʷ {p = r} x) ≡ coe₀ʷ {p = q} x
coe-coe₀ zero      q         x = refl
coe-coe₀ (suc r)   zero      x = coe-coe₀ r zero x
coe-coe₀ (suc r)   (suc q)   x = coe-coe₀ (suc r) q x
coe-coe₀ (suc r)   (lim n q) x = coe-coe₀ (suc r) q x
coe-coe₀ (lim m r) zero      x = coe-coe₀ r zero x
coe-coe₀ (lim m r) (suc q)   x = coe-coe₀ (lim m r) q x
coe-coe₀ (lim m r) (lim n q) x = coe-coe₀ (lim m r) q x
```

## §1 树族上的结构序与前驱包含

把 Cumsum §2.1 的 $\prec$ 搬到 `Ordᵂ ℓ`. `limᵢ` 的分支用 `coe₀ʷ x` ($x$ 是第 $j$ 层的树) 索引, 这样所有关于 `coe` 的事实都只需要 `coe-coe₀`. 前驱包含 $\sqsubseteq$ 是归纳定义的 (严格正), 与语义版 `Sim` ("$a$ 的每个前驱都是 $b$ 的前驱") 等价; 自反、传递对**一切**树成立, 不需要任何步进前提.

```agda
infix 4 _≺_ _⊑_

data _≺_ {ℓ} : Ordᵂ ℓ → Ordᵂ ℓ → Set where
  ≺z : ∀ {a} → a ≺ suc a
  ≺s : ∀ {a b} → a ≺ b → a ≺ suc b
  ≺l : ∀ {a} {f : ℕ → Ordᵂ ℓ} n → a ≺ f n → a ≺ lim f
  ≺i : ∀ {a j} {p : j <ʷ ℓ} {f : Ord<ʷ j p → Ordᵂ ℓ} (x : Ordᵂ j) → a ≺ f (coe₀ʷ x) → a ≺ limᵢ p f

data _⊑_ {ℓ} : Ordᵂ ℓ → Ordᵂ ℓ → Set where
  z⊑ : ∀ {b} → zero ⊑ b
  s⊑ : ∀ {a b} → a ≺ b → suc a ⊑ b
  l⊑ : ∀ {f : ℕ → Ordᵂ ℓ} {b} → (∀ n → f n ⊑ b) → lim f ⊑ b
  i⊑ : ∀ {j} {p : j <ʷ ℓ} {f : Ord<ʷ j p → Ordᵂ ℓ} {b} → (∀ x → f (coe₀ʷ x) ⊑ b) → limᵢ p f ⊑ b

Sim : ∀ {ℓ} → Ordᵂ ℓ → Ordᵂ ℓ → Set
Sim a b = ∀ {c} → c ≺ a → c ≺ b

≺-trans : ∀ {ℓ} {a b c : Ordᵂ ℓ} → a ≺ b → b ≺ c → a ≺ c
≺-trans p ≺z       = ≺s p
≺-trans p (≺s q)   = ≺s (≺-trans p q)
≺-trans p (≺l n q) = ≺l n (≺-trans p q)
≺-trans p (≺i x q) = ≺i x (≺-trans p q)

⊑→Sim : ∀ {ℓ} {a b : Ordᵂ ℓ} → a ⊑ b → Sim a b
⊑→Sim (s⊑ p) ≺z       = p
⊑→Sim (s⊑ p) (≺s q)   = ≺-trans q p
⊑→Sim (l⊑ h) (≺l n q) = ⊑→Sim (h n) q
⊑→Sim (i⊑ h) (≺i x q) = ⊑→Sim (h x) q

Sim→⊑ : ∀ {ℓ} {a b : Ordᵂ ℓ} → Sim a b → a ⊑ b
Sim→⊑ {a = zero}     s = z⊑
Sim→⊑ {a = suc a}    s = s⊑ (s ≺z)
Sim→⊑ {a = lim f}    s = l⊑ (λ n → Sim→⊑ (λ q → s (≺l n q)))
Sim→⊑ {a = limᵢ p f} s = i⊑ (λ x → Sim→⊑ (λ q → s (≺i x q)))

⊑-refl : ∀ {ℓ} {a : Ordᵂ ℓ} → a ⊑ a
⊑-refl = Sim→⊑ (λ q → q)

⊑-trans : ∀ {ℓ} {a b c : Ordᵂ ℓ} → a ⊑ b → b ⊑ c → a ⊑ c
⊑-trans p q = Sim→⊑ (λ r → ⊑→Sim q (⊑→Sim p r))

≺→⊑ : ∀ {ℓ} {a b : Ordᵂ ℓ} → a ≺ b → a ⊑ b
≺→⊑ p = Sim→⊑ (λ q → ≺-trans q p)

⊑-≺ : ∀ {ℓ} {a b c : Ordᵂ ℓ} → a ⊑ b → b ≺ c → a ⊑ c
⊑-≺ p q = Sim→⊑ (λ r → ≺-trans (⊑→Sim p r) q)

⊑-lim : ∀ {ℓ} {a : Ordᵂ ℓ} {f : ℕ → Ordᵂ ℓ} n → a ⊑ f n → a ⊑ lim f
⊑-lim n p = Sim→⊑ (λ r → ≺l n (⊑→Sim p r))

⊑-limᵢ : ∀ {ℓ j} {p : j <ʷ ℓ} {f : Ord<ʷ j p → Ordᵂ ℓ} {a} x → a ⊑ f (coe₀ʷ x) → a ⊑ limᵢ p f
⊑-limᵢ x p = Sim→⊑ (λ r → ≺i x (⊑→Sim p r))

data Acc≺ {ℓ} (a : Ordᵂ ℓ) : Set where
  acc : (∀ {b} → b ≺ a → Acc≺ b) → Acc≺ a

acc≺ : ∀ {ℓ} (a : Ordᵂ ℓ) {b} → b ≺ a → Acc≺ b
acc≺ (suc a)    ≺z       = acc (acc≺ a)
acc≺ (suc a)    (≺s p)   = acc≺ a p
acc≺ (lim f)    (≺l n p) = acc≺ (f n) p
acc≺ (limᵢ q f) (≺i x p) = acc≺ (f (coe₀ʷ x)) p

≺-irrefl : ∀ {ℓ} {a : Ordᵂ ℓ} → ¬ (a ≺ a)
≺-irrefl {a = a} = go (acc (acc≺ a)) where
  go : ∀ {ℓ} {a : Ordᵂ ℓ} → Acc≺ a → ¬ (a ≺ a)
  go (acc h) p = go (h p) p
```

**$\sqsubseteq$ 是字面的.** 在后继上它就是严格序, 前驱必须字面相等. 这一条贯穿全文: 两棵外延相等而表示不同的树之间, $\sqsubseteq$ 一般无从证明.

```agda
⊑-literal : ∀ {ℓ} {a b : Ordᵂ ℓ} → suc a ⊑ suc b → a ≡ b ⊎ a ≺ b
⊑-literal (s⊑ ≺z)     = inj₁ refl
⊑-literal (s⊑ (≺s q)) = inj₂ q
```

## §2 保持 $\sqsubseteq$ 的运算: 加法、提升、规则 4

**加法** 对右加数保持 $\prec$ 与 $\sqsubseteq$, 且 $a\sqsubseteq a+b$, 全部无前提 (Cumsum 的 `+-mono≺` 加上 `limᵢ` 情况). 规则 4 的序列 $\psi(a)\cdot n$ 因此**总是** $\sqsubseteq$-步进的, 不需要 Cumsum `rule4ʳ` 的 $0\prec c$.

```agda
+-mono≺ : ∀ {ℓ} {a b c : Ordᵂ ℓ} → b ≺ c → a +ʷ b ≺ a +ʷ c
+-mono≺ ≺z       = ≺z
+-mono≺ (≺s q)   = ≺s (+-mono≺ q)
+-mono≺ (≺l n q) = ≺l n (+-mono≺ q)
+-mono≺ (≺i x q) = ≺i x (+-mono≺ q)

⊑+ : ∀ {ℓ} {a : Ordᵂ ℓ} b → a ⊑ a +ʷ b
⊑+ zero       = ⊑-refl
⊑+ (suc b)    = ⊑-≺ (⊑+ b) ≺z
⊑+ (lim f)    = ⊑-lim 0 (⊑+ (f 0))
⊑+ (limᵢ p f) = ⊑-limᵢ zero (⊑+ (f (coe₀ʷ zero)))

+-mono⊑ : ∀ {ℓ} {a b c : Ordᵂ ℓ} → b ⊑ c → a +ʷ b ⊑ a +ʷ c
+-mono⊑ {c = c} z⊑ = ⊑+ c
+-mono⊑ (s⊑ p)     = s⊑ (+-mono≺ p)
+-mono⊑ (l⊑ h)     = l⊑ (λ n → +-mono⊑ (h n))
+-mono⊑ (i⊑ h)     = i⊑ (λ x → +-mono⊑ (h x))

rule4 : ∀ {ℓ} (c : Ordᵂ ℓ) n → iter (c +ʷ_) zero n ⊑ iter (c +ʷ_) zero (suc n)
rule4 c zero    = z⊑
rule4 c (suc n) = +-mono⊑ (rule4 c n)
```

**提升** `↑ʷ s` 对任意 `Simʷ` 证据保持 $\prec$ 与 $\sqsubseteq$; `limᵢ` 情况只用 `coe-coe₀`.

```agda
↑-mono≺ : ∀ {ℓ₁ ℓ₂} {s : Simʷ ℓ₁ ℓ₂} {a b : Ordᵂ ℓ₁} → a ≺ b → ↑ʷ s a ≺ ↑ʷ s b
↑-mono≺ ≺z       = ≺z
↑-mono≺ (≺s q)   = ≺s (↑-mono≺ q)
↑-mono≺ (≺l n q) = ≺l n (↑-mono≺ q)
↑-mono≺ {s = s} {a = a} (≺i {p = p} {f = f} x q) =
  ≺i x (subst (λ z → ↑ʷ s a ≺ ↑ʷ s (f z)) (sym (coe-coe₀ (s p) p x)) (↑-mono≺ q))

↑-mono⊑ : ∀ {ℓ₁ ℓ₂} {s : Simʷ ℓ₁ ℓ₂} {a b : Ordᵂ ℓ₁} → a ⊑ b → ↑ʷ s a ⊑ ↑ʷ s b
↑-mono⊑ z⊑     = z⊑
↑-mono⊑ (s⊑ p) = s⊑ (↑-mono≺ p)
↑-mono⊑ (l⊑ h) = l⊑ (λ n → ↑-mono⊑ (h n))
↑-mono⊑ {s = s} {b = b} (i⊑ {p = p} {f = f} h) =
  i⊑ (λ x → subst (λ z → ↑ʷ s (f z) ⊑ ↑ʷ s b) (sym (coe-coe₀ (s p) p x)) (↑-mono⊑ (h x)))
```

**$\Omega_i\sqsubseteq\psi_p(b)$ 对一切 $b$**, 以及 $0\prec\Omega_\ell$. 前者是规则 6 的链的种子一步: $\gamma_0=\Omega_j=\psi_q(0)\sqsubseteq\psi_q(f\,\gamma_0)=\gamma_1$, 无前提. 后面的 `chain-step` 把 "种子一步 + 迭代函数单调" 变成整条链递增.

```agda
Ω⊑ψ : ∀ {i ℓ} (p : i <ʷ ℓ) (b : Ordᵂ ℓ) → Ωʷ i ⊑ ψʷ p b
Ω⊑ψ p zero    = ⊑-refl
Ω⊑ψ p (suc a) = ⊑-lim 1 (Ω⊑ψ p a)
Ω⊑ψ p (lim f) = ⊑-lim 0 (Ω⊑ψ p (f 0))
Ω⊑ψ p (limᵢ q f) with <ʷ-dec q p
... | injᵃ r = ⊑-limᵢ zero (Ω⊑ψ p (f (coeʷ (coe₀ʷ zero))))
... | injᵇ r = ⊑-lim 0 (Ω⊑ψ p _)
... | injᶜ r = ⊑-lim 0 (Ω⊑ψ p _)

z≺Ω : ∀ ℓ → zero ≺ Ωʷ ℓ
z≺Ω zero      = ≺z
z≺Ω (suc ℓ)   = ≺i (suc zero) ≺z
z≺Ω (lim f s) = ≺l 0 (↑-mono≺ (z≺Ω (f 0)))

chain-step : ∀ {j} (g : Ordᵂ j → Ordᵂ j) → (∀ {x y} → x ⊑ y → g x ⊑ g y) →
             Ωʷ j ⊑ g (Ωʷ j) → ∀ n → iter g (Ωʷ j) n ⊑ iter g (Ωʷ j) (suc n)
chain-step g m h zero    = h
chain-step g m h (suc n) = m (chain-step g m h n)
```

## §3 关键观察不成立: $\psi$ 不保持 $\sqsubseteq$

**$\sqsubseteq$-单调蕴含严格单调.** 若 $\psi_p$ 保持 $\sqsubseteq$, 由 $a\prec b$ 得 $\mathrm{suc}\,a\sqsubseteq b$, 于是 $\psi(\mathrm{suc}\,a)=\lim_n\psi(a)\cdot n\sqsubseteq\psi(b)$; 而 $\psi(a)\prec\psi(a)+\psi(a)$ (右加数 $0\prec\psi(a)$, 由 `Ω⊑ψ` 与 `z≺Ω`), 所以 $\psi(a)\prec\psi(b)$. 证明对任意目标层成立.

```agda
mono⇒strict : ∀ {i ℓ} (p : i <ʷ ℓ) → (∀ {a b} → a ⊑ b → ψʷ p a ⊑ ψʷ p b) →
              ∀ {a b} → a ≺ b → ψʷ p a ≺ ψʷ p b
mono⇒strict {i} p m {a} h = ⊑→Sim (m (s⊑ h)) (≺l 2 (+-mono≺ (⊑→Sim (Ω⊑ψ p a) (z≺Ω i))))
```

所以 Cumsum §2.4 的严格反例必然以 $\sqsubseteq$ 的形式重现. 直接构造: 第 1 层 $\Omega_1$, $\gamma$-链 $G$ ($G\,0=1$, $G(k+1)=\psi_0(\uparrow G\,k)$), $E=\lim(G\circ\mathrm{suc})=\psi_0(\Omega_1)$ (`refl`). $a_1=\uparrow(\lim G)$ 是 $\varepsilon_0$ 的另一个表示, $a_1\prec\Omega_1$ (经分支 $(\lim G)+1$), 且 $\psi_0(a_1)$ 与 $\psi_0(\Omega_1)$ 定义性相等. 于是 $\mathrm{suc}\,a_1\sqsubseteq\Omega_1$; 但 $\psi_0(\mathrm{suc}\,a_1)$ 的第 2 项是 $E+E$, 它以 $E$ 为前驱 ($E+E$ 的第 0 项是 $E+G\,1$, 其第 1 项是 $E+1$), 而 $E\not\prec E$.

```agda
Ω₁ : Ordᵂ (suc zero)
Ω₁ = Ωʷ (suc zero)

ψ₀ : Ordᵂ (suc zero) → Ordᵂ zero
ψ₀ = ψʷ zero

G : ℕ → Ordᵂ zero
G = iter (λ x → ψ₀ (↑ʷ suc x)) (suc zero)

E : Ordᵂ zero
E = lim (G ∘ suc)

_ : ψ₀ Ω₁ ≡ E
_ = refl

a₁ : Ordᵂ (suc zero)
a₁ = ↑ʷ suc (lim G)

_ : ψ₀ a₁ ≡ E
_ = refl

a₁≺Ω₁ : a₁ ≺ Ω₁
a₁≺Ω₁ = ≺i (suc (lim G)) ≺z

E≺ : E ≺ ψ₀ (suc a₁)
E≺ = ≺l 2 (≺l 0 (≺l 1 ≺z))

ψ-not-⊑mono : suc a₁ ⊑ Ω₁ × ¬ (ψ₀ (suc a₁) ⊑ ψ₀ Ω₁)
ψ-not-⊑mono = s⊑ a₁≺Ω₁ , λ h → ≺-irrefl (⊑→Sim h E≺)
```

题设的论证 "$\gamma_0\sqsubseteq\gamma_1$ 因为 $0\sqsubseteq f\,\gamma_0$ 且 $\psi_j$ 保持 $\sqsubseteq$" 的第一步是对的 (`Ω⊑ψ`, 不需要单调性), 归纳步需要的 "$\psi_j$ 保持 $\sqsubseteq$" 是错的. 同一反例给出: 一个 `lim` 的两项 $\mathrm{suc}\,a_1\sqsubseteq\Omega_1$ 是合法的 $\sqsubseteq$-步, 规则 5ω 把它送成 $\psi_0(\mathrm{suc}\,a_1),\psi_0(\Omega_1)$, 不再是步 (§6 `ψ-breaks-Stepᴴ`).

## §4 修复: 沿折叠自己的路径定义 $\sqsubseteq_p$

最弱的结构修复是只要求 $\psi_p$ 真正经过的分支. `limᵢ q f` ($q:j<\ell$) 上, $j<i$ 时 $\psi_p$ 穿透 (规则 5Ω), 用到全部分支; 否则 (规则 6) 只用到 $f(\gamma_n)$, $\gamma$ 是 $\psi_q$ 的链 `γʷ q f`, 与 $p$ 无关. 于是:

- $\prec_p$: 在 `limᵢ` 上只能经 `≺chain` (任意 $j$) 或 `≺pass` ($j<i$) 下降;
- $\sqsubseteq_p$: `limᵢ q f` $\sqsubseteq_p b$ 要么全部分支都 $\sqsubseteq_p b$ (`⊑pass`, 总可用), 要么 $\neg(j<i)$ 且链分支都 $\sqsubseteq_p b$ (`⊑chain`).

**定理 (安全折叠).** $a\sqsubseteq_p b\Rightarrow\psi_p(a)\sqsubseteq\psi_p(b)$, 无前提. 证明对 $\sqsubseteq_p$/$\prec_p$ 的推导归纳, 在 `limᵢ` 处与 `ψʷ` 对同一个 `<ʷ-dec q p` 分情况; 矛盾的组合由 `<ʷ-irrefl` 排除.

```agda
γʷ : ∀ {j ℓ} (q : j <ʷ ℓ) (f : Ord<ʷ j q → Ordᵂ ℓ) → ℕ → Ordᵂ j
γʷ {j} q f = iter (ψʷ q ∘ f ∘ coe₀ʷ) (Ωʷ j)

module Safe {i ℓ} (p : i <ʷ ℓ) where
  infix 4 _≺ₚ_ _⊑ₚ_
  data _≺ₚ_ : Ordᵂ ℓ → Ordᵂ ℓ → Set where
    ≺z    : ∀ {a} → a ≺ₚ suc a
    ≺s    : ∀ {a b} → a ≺ₚ b → a ≺ₚ suc b
    ≺l    : ∀ {a} {f : ℕ → Ordᵂ ℓ} n → a ≺ₚ f n → a ≺ₚ lim f
    ≺pass : ∀ {a j} {q : j <ʷ ℓ} {f : Ord<ʷ j q → Ordᵂ ℓ} → j <ʷ i →
            (x : Ordᵂ j) → a ≺ₚ f (coe₀ʷ x) → a ≺ₚ limᵢ q f
    ≺chain : ∀ {a j} {q : j <ʷ ℓ} {f : Ord<ʷ j q → Ordᵂ ℓ} →
            (n : ℕ) → a ≺ₚ f (coe₀ʷ (γʷ q f n)) → a ≺ₚ limᵢ q f

  data _⊑ₚ_ : Ordᵂ ℓ → Ordᵂ ℓ → Set where
    z⊑ : ∀ {b} → zero ⊑ₚ b
    s⊑ : ∀ {a b} → a ≺ₚ b → suc a ⊑ₚ b
    l⊑ : ∀ {f : ℕ → Ordᵂ ℓ} {b} → (∀ n → f n ⊑ₚ b) → lim f ⊑ₚ b
    ⊑pass  : ∀ {j} {q : j <ʷ ℓ} {f : Ord<ʷ j q → Ordᵂ ℓ} {b} →
             (∀ x → f (coe₀ʷ x) ⊑ₚ b) → limᵢ q f ⊑ₚ b
    ⊑chain : ∀ {j} {q : j <ʷ ℓ} {f : Ord<ʷ j q → Ordᵂ ℓ} {b} → ¬ (j <ʷ i) →
             (∀ n → f (coe₀ʷ (γʷ q f n)) ⊑ₚ b) → limᵢ q f ⊑ₚ b

  ψ-≺ₚ : ∀ {a b} → a ≺ₚ b → ψʷ p (suc a) ⊑ ψʷ p b
  ψ-≺ₚ ≺z         = ⊑-refl
  ψ-≺ₚ {b = suc b} (≺s h) = ⊑-trans (ψ-≺ₚ h) (⊑-lim 1 ⊑-refl)
  ψ-≺ₚ (≺l n h)   = ⊑-lim n (ψ-≺ₚ h)
  ψ-≺ₚ {a} (≺pass {j = j} {q = q} {f = f} r x h) with <ʷ-dec q p
  ... | injᵃ r′ = ⊑-limᵢ x (subst (λ z → ψʷ p (suc a) ⊑ ψʷ p (f z)) (sym (coe-coe₀ r′ q x)) (ψ-≺ₚ h))
  ... | injᵇ s  = ⊥-elim (<ʷ-irrefl (<ʷ-trans r s))
  ... | injᶜ e  = ⊥-elim (<ʷ-irrefl (subst (j <ʷ_) (sym e) r))
  ψ-≺ₚ {a} (≺chain {q = q} {f = f} n h) with <ʷ-dec q p
  ... | injᵃ r′ = ⊑-limᵢ (γʷ q f n)
                    (subst (λ z → ψʷ p (suc a) ⊑ ψʷ p (f z)) (sym (coe-coe₀ r′ q _)) (ψ-≺ₚ h))
  ... | injᵇ _  = ⊑-lim n (ψ-≺ₚ h)
  ... | injᶜ _  = ⊑-lim n (ψ-≺ₚ h)

  ψ-⊑ₚ : ∀ {a b} → a ⊑ₚ b → ψʷ p a ⊑ ψʷ p b
  ψ-⊑ₚ {b = b} z⊑ = Ω⊑ψ p b
  ψ-⊑ₚ (s⊑ h)     = ψ-≺ₚ h
  ψ-⊑ₚ (l⊑ h)     = l⊑ (λ n → ψ-⊑ₚ (h n))
  ψ-⊑ₚ {b = b} (⊑pass {q = q} {f = f} h) with <ʷ-dec q p
  ... | injᵃ r′ = i⊑ (λ x → subst (λ z → ψʷ p (f z) ⊑ ψʷ p b) (sym (coe-coe₀ r′ q x)) (ψ-⊑ₚ (h x)))
  ... | injᵇ _  = l⊑ (λ n → ψ-⊑ₚ (h _))
  ... | injᶜ _  = l⊑ (λ n → ψ-⊑ₚ (h _))
  ψ-⊑ₚ (⊑chain {q = q} ¬r h) with <ʷ-dec q p
  ... | injᵃ r′ = ⊥-elim (¬r r′)
  ... | injᵇ _  = l⊑ (λ n → ψ-⊑ₚ (h n))
  ... | injᶜ _  = l⊑ (λ n → ψ-⊑ₚ (h n))
```

$\prec_p\subseteq\prec$, 所以 $\sqsubseteq_p$ 是 "安全路径" 的精确形式: Cumsum §7 第 3 条说 "相邻项之间的结构路径在每个 $j\ge i$ 的 `limᵢ` 节点上都分叉于 $\gamma$-链之下", 这里就是 `≺chain`/`⊑chain`. `ψ-not-⊑mono` 的 $\mathrm{suc}\,a_1\sqsubseteq\Omega_1$ 经过非链分支 $(\lim G)+1$, 所以不是 $\sqsubseteq_p$.

**规则 6 的链.** 若 $f$ 把 $\sqsubseteq$ 送到 $\sqsubseteq_q$, 则 $\gamma$-链 $\sqsubseteq$-递增. 种子一步无前提.

```agda
rule6-chain : ∀ {j ℓ} (q : j <ʷ ℓ) (f : Ord<ʷ j q → Ordᵂ ℓ) →
              (∀ {x y} → x ⊑ y → Safe._⊑ₚ_ q (f (coe₀ʷ x)) (f (coe₀ʷ y))) →
              ∀ n → γʷ q f n ⊑ γʷ q f (suc n)
rule6-chain q f h = chain-step (ψʷ q ∘ f ∘ coe₀ʷ) (λ le → Safe.ψ-⊑ₚ q (h le)) (Ω⊑ψ q _)
```

**无 `limᵢ` 的情形.** 若 $b$ 没有 `limᵢ` 节点, 则 $\prec$ 到 $b$ 的路径都是安全的, $a\sqsubseteq b\Rightarrow a\sqsubseteq_p b$ (对 $a$ 不加条件: $a$ 的 `limᵢ` 用 `⊑pass`). 第 0 层的树与它们的提升都没有 `limᵢ`; 由此 $G$ 是 $\sqsubseteq$-递增的, 这是 Cumsum `γᴰ-step` 在树上的版本.

```agda
data NoLᵢ {ℓ} : Ordᵂ ℓ → Set where
  nz : NoLᵢ zero
  ns : ∀ {a} → NoLᵢ a → NoLᵢ (suc a)
  nl : ∀ {f : ℕ → Ordᵂ ℓ} → (∀ n → NoLᵢ (f n)) → NoLᵢ (lim f)

noLᵢ₀ : (x : Ordᵂ zero) → NoLᵢ x
noLᵢ₀ zero    = nz
noLᵢ₀ (suc x) = ns (noLᵢ₀ x)
noLᵢ₀ (lim f) = nl (λ n → noLᵢ₀ (f n))

noLᵢ-↑ : ∀ {ℓ₁ ℓ₂} {s : Simʷ ℓ₁ ℓ₂} {x : Ordᵂ ℓ₁} → NoLᵢ x → NoLᵢ (↑ʷ s x)
noLᵢ-↑ nz     = nz
noLᵢ-↑ (ns h) = ns (noLᵢ-↑ h)
noLᵢ-↑ (nl h) = nl (λ n → noLᵢ-↑ (h n))

module _ {i ℓ} (p : i <ʷ ℓ) where
  open Safe p

  ≺→≺ₚ : ∀ {a b : Ordᵂ ℓ} → NoLᵢ b → a ≺ b → a ≺ₚ b
  ≺→≺ₚ (ns h) ≺z       = ≺z
  ≺→≺ₚ (ns h) (≺s q)   = ≺s (≺→≺ₚ h q)
  ≺→≺ₚ (nl h) (≺l n q) = ≺l n (≺→≺ₚ (h n) q)

  ⊑→⊑ₚ : ∀ {a b : Ordᵂ ℓ} → NoLᵢ b → a ⊑ b → a ⊑ₚ b
  ⊑→⊑ₚ h z⊑     = z⊑
  ⊑→⊑ₚ h (s⊑ q) = s⊑ (≺→≺ₚ h q)
  ⊑→⊑ₚ h (l⊑ k) = l⊑ (λ n → ⊑→⊑ₚ h (k n))
  ⊑→⊑ₚ h (i⊑ k) = ⊑pass (λ x → ⊑→⊑ₚ h (k x))

  ψ-mono-NoLᵢ : ∀ {a b : Ordᵂ ℓ} → NoLᵢ b → a ⊑ b → ψʷ p a ⊑ ψʷ p b
  ψ-mono-NoLᵢ h q = ψ-⊑ₚ (⊑→⊑ₚ h q)

G-step : ∀ n → G n ⊑ G (suc n)
G-step zero    = Ω⊑ψ zero (↑ʷ suc (G 0))
G-step (suc n) = ψ-mono-NoLᵢ zero (noLᵢ-↑ (noLᵢ₀ _)) (↑-mono⊑ (G-step n))
```

## §5 第二个障碍: 层号证明写进了树

$\Omega$ 在极限层 $\lim f$ 的第 $n$ 项是 $\uparrow_{\mathtt{lim}\,n}\Omega_{f\,n}$: 提升证据 `lim n` 被 `↑ʷ` 写进每个 `limᵢ` 节点的证明字段 (`↑ʷ s (limᵢ q g) = limᵢ (s q) …`). 于是第 $n$ 项的 `limᵢ` 前驱都带标签 $n$, 第 $n+1$ 项的都带 $n+1$, 两者不可能字面相同. 下面在 $\omega$ 层编译出这一点: `tag` 读出 `limᵢ (lim n _) _` 的 $n+1$; `tag-↑` 说 $\uparrow_{\mathtt{lim}\,n}t$ 的前驱的标签只能是 $0$ 或 $n+1$; $\Omega_2$ 的前驱 $\uparrow_{\mathtt{suc}}\Omega_1$ 提升后标签是 $3$, 不是 $\uparrow_{\mathtt{lim}\,3}\Omega_3$ 的前驱.

```agda
natʷ : ℕ → Ordʷ
natʷ zero    = zero
natʷ (suc n) = suc (natʷ n)

natʷ-step : ∀ n → natʷ n ⊑ʷ natʷ (suc n)
natʷ-step n = Sim→⊑ʷ suc

ωʷ : Ordʷ
ωʷ = lim natʷ natʷ-step

limS : ∀ {g : ℕ → Ordʷ} {s : ∀ n → g n ⊑ʷ g (suc n)} n → Simʷ (g n) (lim g s)
limS n q = lim n q

T : ∀ n → Ordᵂ ωʷ
T n = ↑ʷ (limS n) (Ωʷ (natʷ n))

_ : Ωʷ ωʷ ≡ lim T
_ = refl

tag : ∀ {ℓ} → Ordᵂ ℓ → ℕ
tag (limᵢ (lim n _) _) = suc n
tag _                  = zero

module _ {g : ℕ → Ordʷ} {s : ∀ n → g n ⊑ʷ g (suc n)} {n : ℕ} where
  tag-node : (t : Ordᵂ (g n)) → tag (↑ʷ (limS {g} {s} n) t) ≡ 0 ⊎ tag (↑ʷ (limS {g} {s} n) t) ≡ suc n
  tag-node zero       = inj₁ refl
  tag-node (suc t)    = inj₁ refl
  tag-node (lim f)    = inj₁ refl
  tag-node (limᵢ q f) = inj₂ refl

  tag-↑ : (t : Ordᵂ (g n)) {d : Ordᵂ (lim g s)} → d ≺ ↑ʷ (limS {g} {s} n) t → tag d ≡ 0 ⊎ tag d ≡ suc n
  tag-↑ (suc t)    ≺z       = tag-node t
  tag-↑ (suc t)    (≺s h)   = tag-↑ t h
  tag-↑ (lim f)    (≺l m h) = tag-↑ (f m) h
  tag-↑ (limᵢ q f) (≺i x h) = tag-↑ (f (coeʷ (coe₀ʷ x))) h

c₂ : Ordᵂ ωʷ
c₂ = ↑ʷ (limS 2) (↑ʷ suc (Ωʷ (natʷ 1)))

_ : tag c₂ ≡ 3
_ = refl

c₂≺T₂ : c₂ ≺ T 2
c₂≺T₂ = ≺i (suc (Ωʷ (natʷ 1))) ≺z

Ω-not-step : ¬ (T 2 ⊑ T 3)
Ω-not-step h with tag-↑ {g = natʷ} {s = natʷ-step} {n = 3} (Ωʷ (natʷ 3)) (⊑→Sim h c₂≺T₂)
... | inj₁ ()
... | inj₂ ()
```

值层面 $\Omega_2<\Omega_3$, 前驱集合也包含; 结构上不包含, 只因为两边的子树带着不同的证明项. 这与规则 6、与 $\psi$ 都无关, 是 "下标序是子项序 + 证明相关的层号 + 字面的 $\sqsubseteq$" 三者合起来的代价. 换别的提升证据也一样: 只要第 $n$ 项与第 $n+1$ 项经过不同的 `Simʷ` 提升, 它们的 `limᵢ` 子树就字面不同.

## §6 遗传步进 `Stepᴴ`: 什么封闭, 什么不封闭

题设的遗传谓词: 每个 `lim f` 有 $f\,n\sqsubseteq f(n+1)$; 每个 `limᵢ p f` 在较低层满足 `Stepᴴ` 的定义域上把 $\sqsubseteq$ 送到 $\sqsubseteq$. 较低层的谓词作参数 `S<` 传入, 再对证明 $p:j<\ell$ 递归定义成第 $j$ 层的 `Stepᴴ`, 与 BTBO 的 `Ord<`、FiniteAll 的 `R<` 同一个模式 (停机检查器看到隐式层级递降).

```agda
module _ (ℓ : Ordʷ) (S< : (j : Ordʷ) → j <ʷ ℓ → Ordᵂ j → Set) where
  data Stepᴴ₊ : Ordᵂ ℓ → Set where
    hz : Stepᴴ₊ zero
    hs : ∀ {a} → Stepᴴ₊ a → Stepᴴ₊ (suc a)
    hl : ∀ {f : ℕ → Ordᵂ ℓ} → (∀ n → Stepᴴ₊ (f n)) → (∀ n → f n ⊑ f (suc n)) → Stepᴴ₊ (lim f)
    hi : ∀ {j} {p : j <ʷ ℓ} {f : Ord<ʷ j p → Ordᵂ ℓ} →
         (∀ x → S< j p x → Stepᴴ₊ (f (coe₀ʷ x))) →
         (∀ x y → S< j p x → S< j p y → x ⊑ y → f (coe₀ʷ x) ⊑ f (coe₀ʷ y)) → Stepᴴ₊ (limᵢ p f)

S<ᴴ : ∀ {ℓ} (j : Ordʷ) → j <ʷ ℓ → Ordᵂ j → Set
S<ᴴ j zero      = Stepᴴ₊ j S<ᴴ
S<ᴴ j (suc p)   = S<ᴴ j p
S<ᴴ j (lim n p) = S<ᴴ j p

Stepᴴ : ∀ {ℓ} → Ordᵂ ℓ → Set
Stepᴴ {ℓ} = Stepᴴ₊ ℓ S<ᴴ

S<-conv : ∀ {j ℓ₁ ℓ₂} (p : j <ʷ ℓ₁) (q : j <ʷ ℓ₂) {x} → S<ᴴ j p x → S<ᴴ j q x
S<-conv zero      zero      r = r
S<-conv zero      (suc q)   r = S<-conv zero q r
S<-conv zero      (lim n q) r = S<-conv zero q r
S<-conv (suc p)   q         r = S<-conv p q r
S<-conv (lim n p) q         r = S<-conv p q r
```

**封闭的:** 加法、提升 (任意证据)、$\Omega$ 在零层与后继层.

```agda
+-Stepᴴ : ∀ {ℓ} {a b : Ordᵂ ℓ} → Stepᴴ a → Stepᴴ b → Stepᴴ (a +ʷ b)
+-Stepᴴ ha hz          = ha
+-Stepᴴ ha (hs hb)     = hs (+-Stepᴴ ha hb)
+-Stepᴴ ha (hl hb st)  = hl (λ n → +-Stepᴴ ha (hb n)) (λ n → +-mono⊑ (st n))
+-Stepᴴ ha (hi hb mo)  = hi (λ x sx → +-Stepᴴ ha (hb x sx)) (λ x y sx sy le → +-mono⊑ (mo x y sx sy le))

↑-Stepᴴ : ∀ {ℓ₁ ℓ₂} {s : Simʷ ℓ₁ ℓ₂} {a : Ordᵂ ℓ₁} → Stepᴴ a → Stepᴴ (↑ʷ s a)
↑-Stepᴴ hz          = hz
↑-Stepᴴ (hs h)      = hs (↑-Stepᴴ h)
↑-Stepᴴ (hl h st)   = hl (λ n → ↑-Stepᴴ (h n)) (λ n → ↑-mono⊑ (st n))
↑-Stepᴴ {s = σ} (hi {p = q} {f = f} h mo) =
  hi (λ x sx → subst (λ z → Stepᴴ (↑ʷ σ (f z))) (sym (coe-coe₀ (σ q) q x))
                     (↑-Stepᴴ (h x (S<-conv (σ q) q sx))))
     (λ x y sx sy le → subst (λ z → ↑ʷ σ (f z) ⊑ ↑ʷ σ (f (coeʷ (coe₀ʷ y)))) (sym (coe-coe₀ (σ q) q x))
                         (subst (λ z → ↑ʷ σ (f (coe₀ʷ x)) ⊑ ↑ʷ σ (f z)) (sym (coe-coe₀ (σ q) q y))
                           (↑-mono⊑ (mo x y (S<-conv (σ q) q sx) (S<-conv (σ q) q sy) le))))

Ω-zero-Stepᴴ : Stepᴴ (Ωʷ zero)
Ω-zero-Stepᴴ = hs hz

Ω-suc-Stepᴴ : ∀ ℓ → Stepᴴ (Ωʷ (suc ℓ))
Ω-suc-Stepᴴ ℓ = hi (λ x sx → ↑-Stepᴴ sx) (λ x y _ _ le → ↑-mono⊑ le)

iter-Stepᴴ : ∀ {ℓ} {c : Ordᵂ ℓ} → Stepᴴ c → ∀ n → Stepᴴ (iter (c +ʷ_) zero n)
iter-Stepᴴ h zero    = hz
iter-Stepᴴ h (suc n) = +-Stepᴴ h (iter-Stepᴴ h n)
```

**$\psi$ 在无 `limᵢ` 的输入上封闭** (只要 $\Omega_i$ 是步进的). 由此第 0 层的链 $G$ 与 $E=\psi_0(\Omega_1)$ 都是遗传步进的.

```agda
ψ-Stepᴴ-NoLᵢ : ∀ {i ℓ} (p : i <ʷ ℓ) → Stepᴴ (Ωʷ i) → ∀ {a} → NoLᵢ a → Stepᴴ a → Stepᴴ (ψʷ p a)
ψ-Stepᴴ-NoLᵢ p hΩ nz      hz        = hΩ
ψ-Stepᴴ-NoLᵢ p hΩ (ns na) (hs h)    = hl (iter-Stepᴴ (ψ-Stepᴴ-NoLᵢ p hΩ na h)) (rule4 _)
ψ-Stepᴴ-NoLᵢ p hΩ (nl na) (hl h st) =
  hl (λ n → ψ-Stepᴴ-NoLᵢ p hΩ (na n) (h n)) (λ n → ψ-mono-NoLᵢ p (na (suc n)) (st n))

G-Stepᴴ : ∀ n → Stepᴴ (G n)
G-Stepᴴ zero    = hs hz
G-Stepᴴ (suc n) = ψ-Stepᴴ-NoLᵢ zero Ω-zero-Stepᴴ (noLᵢ-↑ (noLᵢ₀ _)) (↑-Stepᴴ (G-Stepᴴ n))

E-Stepᴴ : Stepᴴ E
E-Stepᴴ = hl (λ n → G-Stepᴴ (suc n)) (λ n → G-step (suc n))
```

**不封闭的:** $\Omega$ 在极限层 (§5), 以及一般的 $\psi$ (§3). 后者的见证是第 1 层的遗传步进树 $\lim(\mathrm{suc}\,a_1,\Omega_1,\Omega_1,\ldots)$.

```agda
Ω-lim-not-Stepᴴ : ¬ Stepᴴ (Ωʷ ωʷ)
Ω-lim-not-Stepᴴ (hl _ st) = Ω-not-step (st 2)

hh : ℕ → Ordᵂ (suc zero)
hh zero    = suc a₁
hh (suc _) = Ω₁

hh-Stepᴴ : Stepᴴ (lim hh)
hh-Stepᴴ = hl comp st where
  comp : ∀ n → Stepᴴ (hh n)
  comp zero    = hs (↑-Stepᴴ (hl G-Stepᴴ G-step))
  comp (suc _) = Ω-suc-Stepᴴ zero
  st : ∀ n → hh n ⊑ hh (suc n)
  st zero    = s⊑ a₁≺Ω₁
  st (suc _) = ⊑-refl

ψ-breaks-Stepᴴ : Stepᴴ (lim hh) × ¬ Stepᴴ (ψ₀ (lim hh))
ψ-breaks-Stepᴴ = hh-Stepᴴ , λ { (hl _ st) → proj₂ ψ-not-⊑mono (st 0) }
```

所以 "`Step` 对生成对角线的运算 (零、$\Omega$、加法、$\psi$、步进序列的极限) 封闭" 不成立: 对 $+$、`↑` 与非极限层的 $\Omega$ 成立, 对 $\psi$ 只在安全 ($\sqsubseteq_p$) 的输入上成立, 对极限层的 $\Omega$ 不成立.

## §7 认证层号: `Step` 与 `toLevel`

**为什么不能从 `Stepᴴ` 读层号.** 设 `toLevel` 把带 `Stepᴴ` 证明的第 0 层树转成 `Ordʷ`, `lim` 的证据由 $f\,n\sqsubseteq f(n+1)$ 换来. 这需要 "$a\sqsubseteq b\Rightarrow$ `toLevel a` $\sqsubseteq^\mathsf{w}$ `toLevel b`": $a$ 的前驱 $c$ 的层号是 `toLevel c` (取 $a$ 的证明在 $c$ 处的限制), 它必须**字面地**是 `toLevel b` 的前驱, 而后者是 `toLevel c` (取 $b$ 的证明在 $c$ 处的限制). 两个限制是同一命题的两个证明, `Ordʷ` 的 `lim` 把证据存成函数, 证明不同则层号不同 (要判定它们相等还需函数外延性). `Stepᴴ` 不是命题 ($\prec$ 的推导不唯一), 所以这条路不通.

**归纳-递归的证书.** 把证据直接放在层号上: `l` 要求各项的证书, 以及**像之间**的 $\sqsubseteq^\mathsf{w}$. `toLevel` 与 `Step` 同时定义, `lim` 的证据就是证书里的那一份, 没有填充. 层号的第 $n$ 项定义性地是第 $n$ 项的层号 (`toLevel-lim`), 于是 $\Omega$ 的第 $n$ 项定义性地是 $\Omega_{\mathtt{toLevel}(f\,n)}$ (`Ω-exact`), 这就是 Cumsum `exact` 的格式, 且这里是 `refl`. 遗忘回树与原树外延相等 (`forget-toLevel`).

```agda
forget : Ordʷ → Ordᵂ zero
forget zero      = zero
forget (suc a)   = suc (forget a)
forget (lim f _) = lim (forget ∘ f)

data Step : Ordᵂ zero → Set
toLevel : (x : Ordᵂ zero) → Step x → Ordʷ

data Step where
  z : Step zero
  s : ∀ {a} → Step a → Step (suc a)
  l : ∀ {f : ℕ → Ordᵂ zero} (h : ∀ n → Step (f n)) →
      (∀ n → toLevel (f n) (h n) ⊑ʷ toLevel (f (suc n)) (h (suc n))) → Step (lim f)

toLevel _ z       = zero
toLevel _ (s h)   = suc (toLevel _ h)
toLevel _ (l h e) = lim (λ n → toLevel _ (h n)) e

toLevel-lim : ∀ {f} (h : ∀ n → Step (f n)) e → toLevel (lim f) (l h e) ≡ lim (λ n → toLevel (f n) (h n)) e
toLevel-lim h e = refl

Ω-exact : ∀ {f} (h : ∀ n → Step (f n)) e →
          Ωʷ (toLevel (lim f) (l h e)) ≡ lim (λ n → ↑ʷ (limS n) (Ωʷ (toLevel (f n) (h n))))
Ω-exact h e = refl

infix 4 _≈_
data _≈_ : Ordᵂ zero → Ordᵂ zero → Set where
  z≈ : zero ≈ zero
  s≈ : ∀ {a b} → a ≈ b → suc a ≈ suc b
  l≈ : ∀ {f g : ℕ → Ordᵂ zero} → (∀ n → f n ≈ g n) → lim f ≈ lim g

≈-refl : ∀ x → x ≈ x
≈-refl zero       = z≈
≈-refl (suc x)    = s≈ (≈-refl x)
≈-refl (lim f)    = l≈ (λ n → ≈-refl (f n))
≈-refl (limᵢ () f)

≈-trans : ∀ {a b c} → a ≈ b → b ≈ c → a ≈ c
≈-trans z≈     z≈      = z≈
≈-trans (s≈ e) (s≈ e′) = s≈ (≈-trans e e′)
≈-trans (l≈ h) (l≈ h′) = l≈ (λ n → ≈-trans (h n) (h′ n))

forget-toLevel : ∀ x (h : Step x) → forget (toLevel x h) ≈ x
forget-toLevel _ z       = z≈
forget-toLevel _ (s h)   = s≈ (forget-toLevel _ h)
forget-toLevel _ (l h e) = l≈ (λ n → forget-toLevel _ (h n))
```

**典范证书.** 每个下标 $L$ 的遗忘像都有证书, 证据由 $L$ 自己的证据经单调的往返 $\lceil L\rceil$ 搬过来. 这里没有一致性问题, 因为证书是 $L$ 的函数, 同一个子项总拿到同一份证书. 换言之: **由 `Ordʷ` 原生构造的层号, 其遗忘像自动带证书**; 难的是让忠实折叠的输出落在这样的像里.

```agda
cert : (L : Ordʷ) → Step (forget L)
⌈_⌉ : Ordʷ → Ordʷ
⌈⌉-mono< : ∀ {a b} → a <ʷ b → ⌈ a ⌉ <ʷ ⌈ b ⌉
⌈⌉-mono⊑ : ∀ {a b} → a ⊑ʷ b → ⌈ a ⌉ ⊑ʷ ⌈ b ⌉

⌈ L ⌉ = toLevel (forget L) (cert L)

cert zero      = z
cert (suc a)   = s (cert a)
cert (lim f e) = l (cert ∘ f) (λ n → ⌈⌉-mono⊑ (e n))

⌈⌉-mono< zero      = zero
⌈⌉-mono< (suc p)   = suc (⌈⌉-mono< p)
⌈⌉-mono< (lim n p) = lim n (⌈⌉-mono< p)

⌈⌉-mono⊑ z⊑     = z⊑
⌈⌉-mono⊑ (s⊑ p) = s⊑ (⌈⌉-mono< p)
⌈⌉-mono⊑ (l⊑ h) = l⊑ (λ n → ⌈⌉-mono⊑ (h n))
```

## §8 $\psi_0$ 片段的原生认证: 层号 $\varepsilon_0$

Cumsum 的 `ψ⁰ᴰ` 搬到 `Ordʷ`: 加法 `⊕` 与它的单调性互递归, $\psi_0$ 与它的单调性互递归, 每个 `lim` 的证据现场给出. 与 `Ordᴰ` 版相比, 证据只要 $\sqsubseteq^\mathsf{w}$, 所以规则 4 的证据不再需要 $0<c$ (`rule4ʷ`), 种子 $\Omega_0$ 也不必严格小于下一项.

```agda
infixl 6 _⊕_
_⊕_ : Ordʷ → Ordʷ → Ordʷ
⊕-mono< : ∀ {a b c} → b <ʷ c → a ⊕ b <ʷ a ⊕ c
⊕-mono⊑ : ∀ {a b c} → b ⊑ʷ c → a ⊕ b ⊑ʷ a ⊕ c
⊑⊕ : ∀ {a} c → a ⊑ʷ a ⊕ c

a ⊕ zero    = a
a ⊕ suc b   = suc (a ⊕ b)
a ⊕ lim f e = lim (λ n → a ⊕ f n) (λ n → ⊕-mono⊑ (e n))

⊕-mono< zero      = zero
⊕-mono< (suc p)   = suc (⊕-mono< p)
⊕-mono< (lim n p) = lim n (⊕-mono< p)

⊕-mono⊑ {c = c} z⊑ = ⊑⊕ c
⊕-mono⊑ (s⊑ p)     = s⊑ (⊕-mono< p)
⊕-mono⊑ (l⊑ h)     = l⊑ (λ n → ⊕-mono⊑ (h n))

⊑⊕ zero      = ⊑ʷ-refl
⊑⊕ (suc c)   = ⊑ʷ-trans (⊑⊕ c) (Sim→⊑ʷ suc)
⊑⊕ (lim f e) = ⊑ʷ-trans (⊑⊕ (f 0)) (Sim→⊑ʷ (lim 0))

rule4ʷ : ∀ c n → iter (c ⊕_) zero n ⊑ʷ iter (c ⊕_) zero (suc n)
rule4ʷ c zero    = z⊑
rule4ʷ c (suc n) = ⊕-mono⊑ (rule4ʷ c n)

ψ⁰ʷ : Ordʷ → Ordʷ
z<ψ⁰ʷ : ∀ a → zero <ʷ ψ⁰ʷ a
ψ⁰ʷ-mono< : ∀ {a b} → a <ʷ b → ψ⁰ʷ (suc a) ⊑ʷ ψ⁰ʷ b
ψ⁰ʷ-mono⊑ : ∀ {a b} → a ⊑ʷ b → ψ⁰ʷ a ⊑ʷ ψ⁰ʷ b

ψ⁰ʷ zero      = suc zero
ψ⁰ʷ (suc a)   = lim (iter (ψ⁰ʷ a ⊕_) zero) (rule4ʷ (ψ⁰ʷ a))
ψ⁰ʷ (lim f e) = lim (ψ⁰ʷ ∘ f) (λ n → ψ⁰ʷ-mono⊑ (e n))

z<ψ⁰ʷ zero      = zero
z<ψ⁰ʷ (suc a)   = lim 1 (z<ψ⁰ʷ a)
z<ψ⁰ʷ (lim f e) = lim 0 (z<ψ⁰ʷ (f 0))

ψ⁰ʷ-mono< zero                = ⊑ʷ-refl
ψ⁰ʷ-mono< {b = suc b} (suc p) = ⊑ʷ-trans (ψ⁰ʷ-mono< p) (Sim→⊑ʷ (lim 1))
ψ⁰ʷ-mono< (lim n p)           = ⊑ʷ-trans (ψ⁰ʷ-mono< p) (Sim→⊑ʷ (lim n))

ψ⁰ʷ-mono⊑ {b = b} z⊑ = s⊑ (z<ψ⁰ʷ b)
ψ⁰ʷ-mono⊑ (s⊑ p)     = ψ⁰ʷ-mono< p
ψ⁰ʷ-mono⊑ (l⊑ h)     = l⊑ (λ n → ψ⁰ʷ-mono⊑ (h n))
```

$\gamma$-链与层号 $\varepsilon_0^\mathsf{w}=\lim(\gamma\circ\mathrm{suc})$. 它的 $\Omega$-基本列逐项是 $\Omega_{\gamma(n+1)}$; 第 0 项 $\gamma_1=\omega$ 的 $\Omega$-基本列逐项是 $\Omega_n$ (Cumsum §0 里 `ordᴰ` 给的是 $\Omega_0,\Omega_2,\Omega_5,\ldots$).

```agda
γᴺ : ℕ → Ordʷ
γᴺ = iter ψ⁰ʷ (suc zero)

γᴺ-step : ∀ n → γᴺ n ⊑ʷ γᴺ (suc n)
γᴺ-step zero    = ψ⁰ʷ-mono⊑ {a = zero} {b = suc zero} z⊑
γᴺ-step (suc n) = ψ⁰ʷ-mono⊑ (γᴺ-step n)

ε₀ʷ : Ordʷ
ε₀ʷ = lim (γᴺ ∘ suc) (γᴺ-step ∘ suc)

_ : Ωʷ ε₀ʷ ≡ lim (λ n → ↑ʷ (limS n) (Ωʷ (γᴺ (suc n))))
_ = refl

_ : Ωʷ (γᴺ 1) ≡ lim (λ m → ↑ʷ (limS m) (Ωʷ (iter (suc zero ⊕_) zero m)))
_ = refl

_ : iter (suc zero ⊕_) zero 2 ≡ natʷ 2
_ = refl
```

**与忠实折叠的对应.** 遗忘后, `ψ⁰ʷ` 就是 `ψʷ` 从第 1 层折到第 0 层 (先提升), 在 $\approx$ 下 (`forget-ψ`); 于是链 $\gamma^\mathsf{N}$ 对应 §3 的 $G$, 层号 $\varepsilon_0^\mathsf{w}$ 对应 $x_2=\psi_0(\Omega_1)$ (`x₂-link`).

```agda
+-≈ : ∀ {a b c d} → a ≈ b → c ≈ d → a +ʷ c ≈ b +ʷ d
+-≈ e z≈      = e
+-≈ e (s≈ e′) = s≈ (+-≈ e e′)
+-≈ e (l≈ h)  = l≈ (λ n → +-≈ e (h n))

forget-⊕ : ∀ a b → forget (a ⊕ b) ≈ forget a +ʷ forget b
forget-⊕ a zero      = ≈-refl (forget a)
forget-⊕ a (suc b)   = s≈ (forget-⊕ a b)
forget-⊕ a (lim f e) = l≈ (λ n → forget-⊕ a (f n))

ψ₀↑ : Ordᵂ zero → Ordᵂ zero
ψ₀↑ x = ψ₀ (↑ʷ suc x)

forget-ψ : ∀ a → forget (ψ⁰ʷ a) ≈ ψ₀↑ (forget a)
forget-ψ zero      = s≈ z≈
forget-ψ (suc a)   = l≈ go where
  go : ∀ n → forget (iter (ψ⁰ʷ a ⊕_) zero n) ≈ iter (ψ₀↑ (forget a) +ʷ_) zero n
  go zero    = z≈
  go (suc n) = ≈-trans (forget-⊕ (ψ⁰ʷ a) _) (+-≈ (forget-ψ a) (go n))
forget-ψ (lim f e) = l≈ (λ n → forget-ψ (f n))

ψ₀↑-≈ : ∀ {x y} → x ≈ y → ψ₀↑ x ≈ ψ₀↑ y
ψ₀↑-≈ z≈     = s≈ z≈
ψ₀↑-≈ (s≈ e) = l≈ go where
  go : ∀ n → iter (ψ₀↑ _ +ʷ_) zero n ≈ iter (ψ₀↑ _ +ʷ_) zero n
  go zero    = z≈
  go (suc n) = +-≈ (ψ₀↑-≈ e) (go n)
ψ₀↑-≈ (l≈ h) = l≈ (λ n → ψ₀↑-≈ (h n))

γ-link : ∀ n → forget (γᴺ n) ≈ G n
γ-link zero    = s≈ z≈
γ-link (suc n) = ≈-trans (forget-ψ (γᴺ n)) (ψ₀↑-≈ (γ-link n))

x₂-link : forget ε₀ʷ ≈ ψ₀ Ω₁
x₂-link = l≈ (λ n → γ-link (suc n))
```

## §9 对角线

**约定.** BTBOFix 的 $\psi_0$ 在第 0 层是恒等, 所以 $x_1=\psi_0(\Omega_0)=\Omega_0=1$ (`Ωʷ zero = suc zero`), 对角线依次是 $0,1,\varepsilon_0,\psi_0(\Omega_{\varepsilon_0}),\ldots$ (BTBOSemantics §9). $x_{k+1}=\psi_{0<\ell_k}(\Omega_{\ell_k})$, $\ell_k$ 是 $x_k$ 的认证层号; $k\ge1$ 时 $0<\ell_k$.

**无条件的部分.** 层号 $\ell_0=0$, $\ell_1=1$, $\ell_2=\varepsilon_0^\mathsf{w}$ 已认证 (§8); 于是 $x_3$ 可以用**无累积和**的层号定义, 它的参数 $\Omega_{\varepsilon_0}$ 的第 $n$ 项定义性地是 $\uparrow\Omega_{\gamma(n+1)}$, 与 EBO 的 $\Omega_u[n]=\Omega_{u[n]}$ 逐项一致. `FGHʷ x₃ 99` 是闭项 (只做类型检查, 不归约).

```agda
FGHʷ : Ordᵂ zero → ℕ → ℕ
FGHʷ zero        n = suc n
FGHʷ (suc a)     n = iter (FGHʷ a) n n
FGHʷ (lim f)     n = FGHʷ (f n) n
FGHʷ (limᵢ () f) n

z<ε₀ʷ : zero <ʷ ε₀ʷ
z<ε₀ʷ = lim 0 (z<ψ⁰ʷ (suc zero))

T′ : ∀ n → Ordᵂ ε₀ʷ
T′ n = ↑ʷ (limS n) (Ωʷ (γᴺ (suc n)))

_ : Ωʷ ε₀ʷ ≡ lim T′
_ = refl

x₃ : Ordᵂ zero
x₃ = ψʷ z<ε₀ʷ (Ωʷ ε₀ʷ)

_ : x₃ ≡ lim (λ n → ψʷ z<ε₀ʷ (T′ n))
_ = refl

_ : ℕ
_ = FGHʷ x₃ 99
```

**$x_3$ 的参数不是步进的.** §5 的标签论证原样适用于对角线真正用到的层: $\Omega_{\varepsilon_0}$ 的第 0 项与第 1 项之间没有 $\sqsubseteq$. 见证 $c'=\uparrow_{\mathtt{lim}\,0}\uparrow_{\mathtt{lim}\,2}\uparrow_{\mathtt{suc}}\Omega_1$ (标签 1) 是第 0 项的前驱, 第 1 项的 `limᵢ` 前驱标签只能是 2.

```agda
c′ : Ordᵂ ε₀ʷ
c′ = ↑ʷ (limS 0) (↑ʷ (limS 2) (↑ʷ suc (Ωʷ (natʷ 1))))

_ : tag c′ ≡ 1
_ = refl

c′≺T′₀ : c′ ≺ T′ 0
c′≺T′₀ = ≺l 2 (↑-mono≺ (≺i (suc (Ωʷ (natʷ 1))) ≺z))

Ωε₀-not-step : ¬ (T′ 0 ⊑ T′ 1)
Ωε₀-not-step h with tag-↑ {g = γᴺ ∘ suc} {s = γᴺ-step ∘ suc} {n = 1} (Ωʷ (γᴺ 2)) (⊑→Sim h c′≺T′₀)
... | inj₁ ()
... | inj₂ ()

x₃-arg-not-Stepᴴ : ¬ Stepᴴ (Ωʷ ε₀ʷ)
x₃-arg-not-Stepᴴ (hl _ st) = Ωε₀-not-step (st 0)
```

**条件包.** 假定每一步都有认证层号: 序列 $L_k$ (即 $x_{k+1}$ 的层号), $L_0=1$, $0<L_k$, $L_k\sqsubseteq^\mathsf{w}L_{k+1}$, 且 $L_{k+1}$ 遗忘后外延等于忠实折叠 $\psi_{0<L_k}(\Omega_{L_k})$. 那么对角线的每一项都是带证书的第 0 层树 (`ψⁿʷ`), `BTBOʷ` 的树是它们的极限 (`refl`), 层号 `BTBOˡ` 的 $\Omega$-基本列逐项是 $\Omega_{x_n}$ (`refl`), FGH 是闭项. 整个包里没有 `cumsum`, 也没有填充: 证据全部来自前提 `infl`.

```agda
record CertDiag : Set where
  field
    L     : ℕ → Ordʷ
    L₀    : L 0 ≡ suc zero
    pos   : ∀ k → zero <ʷ L k
    infl  : ∀ k → L k ⊑ʷ L (suc k)
    faith : ∀ k → forget (L (suc k)) ≈ ψʷ (pos k) (Ωʷ (L k))

module Diagonal (D : CertDiag) where
  open CertDiag D

  lvl : ℕ → Ordʷ
  lvl zero    = zero
  lvl (suc k) = L k

  lvl-step : ∀ n → lvl n ⊑ʷ lvl (suc n)
  lvl-step zero    = z⊑
  lvl-step (suc k) = infl k

  BTBOˡ : Ordʷ
  BTBOˡ = lim lvl lvl-step

  ψⁿʷ : ℕ → Σ (Ordᵂ zero) Step
  ψⁿʷ k = forget (lvl k) , cert (lvl k)

  BTBOʷ : Σ (Ordᵂ zero) Step
  BTBOʷ = forget BTBOˡ , cert BTBOˡ

  _ : proj₁ (ψⁿʷ 0) ≡ zero
  _ = refl

  ψⁿʷ-1 : proj₁ (ψⁿʷ 1) ≡ suc zero
  ψⁿʷ-1 = cong forget L₀

  _ : proj₁ BTBOʷ ≡ lim (proj₁ ∘ ψⁿʷ)
  _ = refl

  _ : Ωʷ BTBOˡ ≡ lim (λ n → ↑ʷ (limS n) (Ωʷ (lvl n)))
  _ = refl

  faithful : ∀ k → proj₁ (ψⁿʷ (suc (suc k))) ≈ ψʷ (pos k) (Ωʷ (lvl (suc k)))
  faithful = faith

  big : ℕ
  big = FGHʷ (proj₁ BTBOʷ) 99
```

第 0 步的前提已兑现 ($L_0=1$, $L_1=\varepsilon_0^\mathsf{w}$):

```agda
prefix : Σ[ p ∈ zero <ʷ suc zero ] (suc zero ⊑ʷ ε₀ʷ) × (forget ε₀ʷ ≈ ψʷ p (Ωʷ (suc zero)))
prefix = zero , s⊑ z<ε₀ʷ , x₂-link
```

第 1 步的前提就是缺口: 一个 $L_2:\mathsf{Ord}^\mathsf{w}$ 使 $\varepsilon_0^\mathsf{w}\sqsubseteq^\mathsf{w}L_2$ 且 `forget L₂ ≈ x₃`. `CertDiag` 是否可被满足, 是本文留下的开放问题.

## §10 缺口的精确位置

第 1 步卡在哪里, 分三层.

1. **树的层面 (已编译的否定).** $x_3$ 的参数 $\Omega_{\varepsilon_0}$ 不是步进的 (`Ωε₀-not-step`), 所以 "参数步进 $\Rightarrow$ 输出步进" 这条路在第一步就断了, 与 $\psi$ 是否单调无关.
2. **第 0 层 (未编译, 元理论的说明).** 证明项的标签在 $\psi_0$ 的输出里不再出现在节点上, 但留在闭包里: $\psi_p(T'_n)$ 的规则 6 链经过 $\psi_q$, $q$ 是带 `lim n` 的节点证明, 提升函数 `↑ʷ (limS n)` 也留在 `lim` 的闭包 $\lambda m.\,\uparrow(\cdots)$ 里. `⊑-literal` 说 $\sqsubseteq$ 的每个推导都落到某个 `≺z`, 即前驱与对方子树字面相等; $x_3$ 的步进因此要求 $\psi_p(T'_0)$ 的深层子树与 $\psi_p(T'_1)$ 的子树定义性相等, 而两者的闭包分别含 $\mathtt{limS}\,0$ 与 $\mathtt{limS}\,1$. 由 `--without-K` 的典范性, 这样的闭等式若有证明, 证明会归约到 `refl`, 两边须定义性相等; 我们据此判断它没有证明 (未逐项核对正规形). 两边逐点外延相等 (FiniteAll `ψᴱ-≈` 的类比, 本文未对 `ψʷ` 重证), 所以函数外延性能把它们等同; 剩下的才是真正的数学内容, 即对这些标准项的安全路径包含.
3. **证书层面.** 即使树上有了 `Stepᴴ`, 也要再造证书 (§7 第一段的一致性问题). 原生构造 (§8) 没有这个问题, 但把它推到 $\psi_0(\Omega_L)$ ($L$ 为极限) 要一个从第 $L$ 层树到 `Ordʷ` 的认证折叠, 它的单调性要比较经过不同提升的两棵树, 回到第 2 条.

所以 Cumsum §7 第 3 条的安全路径引理**仍然必要** (`ψ-not-⊑mono`, 弱化到 $\sqsubseteq$ 不能绕开它), 它的充分性一半已证 (`ψ-⊑ₚ`), 但它**不够**: 在当前的树族上, 即使对标准项证出它, 对角线也过不了 $x_2$, 障碍是内涵性 (证明相关的层号 + 字面的 $\sqsubseteq$), 不是规则 6. 可能的出路, 按改动大小:

- **商化的前驱包含.** 把树与下标上的 $\sqsubseteq$ 都改成 "前驱在 $\approx$ 下包含". 代价: `<ʷ-dec` 只能给出 "在 $\approx$ 下三歧", 树族 `Ord<ʷ i p` 必须沿下标的 $\approx$ 搬运, 等于重写 `W`.
- **累积的树族.** 若 `↑` 是恒等 (层号成员关系证明无关), 标签消失. FiniteAll §1 说明在严格正性约束下, 定义域总要经由对层号或其证明的递归算出, 证明无关的写法目前没有.
- **由表记生成层号** (Cumsum D2): 层号是项的函数, 子项共享是定义性的; 需要 Bachmann 性质与 `Acc` 证书, 循环.
- **保留 `cumsum`** (现状): 它从不比较两条不同路径上的树, 所以绕开了上述一切, 代价是 Cumsum §0 的偏移.

## §11 结论与边界

已形式化 (全部 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示; `Ordʷ`、树族、`ψʷ` 从 Cumsum 的 `W` 导入, 无复制):

1. 树族上的 $\prec$, $\sqsubseteq$ 与 `Sim` 等价; $\sqsubseteq$ 对**一切**树自反、传递; $\prec$ 无自反. $\sqsubseteq$ 在后继上是字面的 (`⊑-literal`).
2. 加法 (`+-mono≺`, `+-mono⊑`, `⊑+`)、提升 (`↑-mono≺`, `↑-mono⊑`, 任意 `Simʷ` 证据) 无条件保持 $\prec$ 与 $\sqsubseteq$; 规则 4 的序列无条件 $\sqsubseteq$-步进 (`rule4`); $\Omega_i\sqsubseteq\psi_p(b)$ 对一切 $b$ (`Ω⊑ψ`), 即规则 6 链的种子一步无条件成立.
3. $\psi$ 不保持 $\sqsubseteq$ (`ψ-not-⊑mono`, 第 1 层, 定义性计算); 且 $\sqsubseteq$-单调蕴含严格单调 (`mono⇒strict`). 题设的关键观察不成立.
4. 安全折叠定理: $a\sqsubseteq_p b\Rightarrow\psi_p(a)\sqsubseteq\psi_p(b)$ (`ψ-⊑ₚ`), 无前提; 无 `limᵢ` 时 $\sqsubseteq\Rightarrow\sqsubseteq_p$ (`⊑→⊑ₚ`, `ψ-mono-NoLᵢ`); 规则 6 链在 "$f$ 把 $\sqsubseteq$ 送到 $\sqsubseteq_q$" 下递增 (`rule6-chain`), $G$ 递增 (`G-step`).
5. 遗传步进 `Stepᴴ`: 对加法、提升、零层与后继层的 $\Omega$ 封闭; $\psi$ 在无 `limᵢ` 的输入上封闭 (`ψ-Stepᴴ-NoLᵢ`); 对极限层的 $\Omega$ 不封闭 (`Ω-lim-not-Stepᴴ`, `x₃-arg-not-Stepᴴ`), 对一般 $\psi$ 不封闭 (`ψ-breaks-Stepᴴ`). 不封闭的两处原因不同: 前者是证明标签 (`Ω-not-step`, `Ωε₀-not-step`), 后者是规则 6 经规则 4 的回归.
6. 认证层号: 归纳-递归的 `Step` 与 `toLevel`, 基本列逐项交换 (`toLevel-lim`, `Ω-exact`, `refl`), `forget-toLevel`; 每个 `Ordʷ` 的遗忘像有典范证书 (`cert`).
7. $\psi_0$ 片段在 `Ordʷ` 上原生认证 (`ψ⁰ʷ`, 无填充, 规则 4 不需要严格性), 层号 $\varepsilon_0^\mathsf{w}$ 的 $\Omega$-基本列逐项是 $\Omega_{x_2[n]}$, $\Omega_\omega$ 的是 $\Omega_n$ (`refl`); 遗忘后与忠实折叠外延相等 (`forget-ψ`, `γ-link`, `x₂-link`).
8. 对角线: $x_0,x_1,x_2$ 全程无累积和认证; $x_3$ 用无累积和的层号定义, `FGHʷ x₃ 99` 是闭项; 条件包 `CertDiag`/`Diagonal` 给出带证书的 `BTBOʷ` 与 `big = FGHʷ (proj₁ BTBOʷ) 99`, 第 0 步前提已兑现 (`prefix`).

边界与未做:

- **对角线没有全程认证.** 认证止于 $x_2=\varepsilon_0$, 与 Cumsum 候选 A 的边界相同. 第 1 步 ($x_3$ 的层号) 的缺口在 §9 末精确陈述; §10 第 2 条关于第 0 层的论证是元理论的说明, 未编译. `CertDiag` 是否可满足未知.
- `Step` (证书) 对哪些树成立: 恰是 `Ordʷ` 原生构造的遗忘像 (`cert`), 以及与它们逐项同构的树; 忠实折叠 `ψʷ` 的输出只与它们外延相等 ($\approx$), 不字面相等. `Stepᴴ` (树上的遗传谓词) 对 $x_0,x_1,x_2$ (即 $E$) 成立 (`E-Stepᴴ`), 对生成对角线的运算整体不封闭.
- "精确" 在两个意义下: 层号与树的基本列逐项对应是定义性的 (`toLevel-lim`); 层号与忠实折叠的对应在 $\approx$ 下 (`x₂-link`).
- $x_2$ 的序数标签 $\varepsilon_0$ 依赖 $\psi_0$ 片段的标准识别 (Cumsum §2.3、Finite 对 $\psi^\mathsf{E}$ 的对齐; `ψʷ` 是 $\psi^\mathsf{E}$ 换下标类型的逐字搬运, 本文未对 `ψʷ` 重做对齐). 条件包中 `BTBOʷ` 的序数标签仍是估计: 扩展 Buchholz 记号的 $\psi_0(\Omega_\Omega)$, 即 $\alpha\mapsto\psi_0(\Omega_\alpha)$ 的最小不动点 (BTBOSemantics §9).
- 本文不改 `src/`、`archive/` 与已有的 Align 文件.
