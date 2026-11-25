# K4 (三): 第 0 层就是值序; 阶段无关的单调引理; 实例与边界

> 入口 [K4Mono](K4Mono.lagda.md). 第 4 层 (验收侧), 不进成品. 导入 [Value](Value.lagda.md) (值前序 `_≼_`) 与 [RR4MonoFragment](RR4MonoFragment.lagda.md) (第 1 层的结点与两条已有结果), 不改任何已有文件. `importclosure.py OCF.Align.K4MonoValue`: 禁用表命中 18, 全部经 `Value` 进来 (`Value` 自己导入 `EBO`, `Correspond`, `Stage2`, `GoodL`); 本文只用 `Value` 里不含记号的部分 (`_≼_` 及其引理, `Ω₁′`, `ψ⁰-not-cong`).
>
> **定理 (都已编译).**
>
> 1. **第 0 层上 `⊑ᵖ` 与 `≼` 相同** (`⊑ᵖ→≼`, `≼→⊑ᵖ`), 关系的两个版本都如此.
> 2. **阶段无关的单调引理 `ψ⁰-monoᵖ`:** 对任意两层的树, `a ⊑ᵖ b → ψ⁰ a ≼ ψ⁰ b`. 这是 [K4MonoFold](K4MonoFold.lagda.md) 的 `ψ⁰-⊑` 接第 1 条.
> 3. **实例.**
>    - `pointwise-mono₁′`: 与 `RR4MonoFragment.Pointwise.pointwise-mono₁` 同一陈述, 没有附加前提, 由第 2 条一行得到 (用不带合法性的版本). 第 1 层上关系的刻画 `node-char`: `node h ⊑ᵖ node h′` 当且仅当 `∀ {x y} → x ≼ y → h x ≼ h′ y`.
>    - `pointwise-mono`: 同一条对一切分支层 $j$ (结点在第 $j+1$ 层, 分支吃第 $j$ 层的树).
>    - `Ω-prefix`: 对一切 $j$ 与第 $j$ 层的 $A$, $\psi^0(\Omega_{j+1})\preccurlyeq\psi^0(\text{分支为 }x\mapsto A+x\text{ 的结点})$. $j=0$ 时是 `RR4MonoFragment.Prefix.fold-below`.
>    - `fb₂`: 第 2 层的一个例子, 分支里对输入再做一次目标层 1 的折叠 (回灌的形状).
> 4. **边界.**
>    - `no-below`: 第 1 层上任何让 $\psi^0$ 落进 `≼` 的关系, 都不能把一切第 0 层的树放在 $\Omega_1$ 之下. 所以 Ω-结点处不能有 "在某一支之下" 的规则 (值序的 `≼i`). 由它一行重新得到 "值序下折叠不单调" (`≼-not-fold-mono`).
>    - `Ω₁′-legal-≅`, `Ω₁′-not-legal`: `Value` 的 $\Omega_1'$ 满足 $\Omega_1'\cong\Omega_1'$, 但不满足 $\Omega_1'\sqsubseteq\Omega_1'$. 本文的 "合法" 与 `_≅_` 的定义域是两个不同的谓词.
>    - `Ω₁ˣ⋢Ω₁`, `Ω₁⋢Ω₁′`: 两条已有的否定 (`mono-fragment-not-cong`, `ψ⁰-not-cong`) 经第 2 条的逆否, 说明这两对不在关系里. 另一个方向在关系里 (`Ω₁⊑Ω₁ˣ`; `Ω₁′⊑Ω₁` 只在不带合法性的版本里).
>    - `finer`: 第 1 层上 `⊑ᵖ` 严格细于 `≼`.
>
> **没有证的.** 高层上 `⊑ᵖ` 是否推出 `≼`: `≼` 的 Ω-结点规则对 $x\cong x$ 的输入取上确界, 那些输入不一定 `⊑ᵖ`-合法, 本文没有比较. 关系是不是 "被折叠保持的最宽关系": 没有证, 也不这样声称.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.K4MonoValue where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Level
open import OCF.Align.Value
  using (_≼_; _≈ᵛ_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼; ≼-refl; ≼-trans; ≼-suc; s≼0; 𝟏; Ω₁; Ω₁′; ψ⁰-not-cong)
  renaming (g to g₁)
open import OCF.Align.RR4MonoFragment using (Br; node; x≼ψ⁰; irr; X; Ω₁ˣ; mono-fragment-not-cong)
open import OCF.Align.K4MonoFold using (module Fold)
```

## §1 第 0 层

第 0 层没有 Ω-结点与提升. `⊑ᵖ` 剩下 `z≤`, `s≤`, `≤s`, `≤l`, `l≤`; `≼` 剩下 `z≼`, `s≼s`, `≼l`, `l≼`. `≤s` 在 `≼` 里可导出 (`Value.≼-suc`), 零在一切树之下在 `⊑ᵖ` 里可导出 (`zero⊑`).

```agda
module Val (M : Set) where
  open Fold M public

  ⊑ᵖ→≼ : ∀ {a b : Ordᶜ zero} → a ⊑ᵖ b → a ≼ b
  ⊑ᵖ→≼ z≤       = z≼
  ⊑ᵖ→≼ (s≤ d)   = s≼s (⊑ᵖ→≼ d)
  ⊑ᵖ→≼ (≤s d)   = ≼-suc (⊑ᵖ→≼ d)
  ⊑ᵖ→≼ (≤l n d) = ≼l n (⊑ᵖ→≼ d)
  ⊑ᵖ→≼ (l≤ h)   = l≼ (λ n → ⊑ᵖ→≼ (h n))
  ⊑ᵖ→≼ (i≤ {p = ()} e m h)
  ⊑ᵖ→≼ (≤i {q = ()} h)
  ⊑ᵖ→≼ (u≤ {r = ()} d)
  ⊑ᵖ→≼ (≤u {r = ()} d)

  ≼→⊑ᵖ : ∀ {a b : Ordᶜ zero} → a ≼ b → a ⊑ᵖ b
  ≼→⊑ᵖ {b = b} z≼ = zero⊑ b
  ≼→⊑ᵖ (s≼s e)  = s≤ (≼→⊑ᵖ e)
  ≼→⊑ᵖ (≼l n e) = ≤l n (≼→⊑ᵖ e)
  ≼→⊑ᵖ (l≼ h)   = l≤ (λ n → ≼→⊑ᵖ (h n))
  ≼→⊑ᵖ (≼i {p = ()} x ex e)
  ≼→⊑ᵖ (i≼ {p = ()} h)
  ≼→⊑ᵖ (≼u {r = ()} e)
  ≼→⊑ᵖ (u≼ {r = ()} e)
```

## §2 阶段无关的单调引理

输入在任意两层, 输出在第 0 层, 结论是值序. 没有合法性前提, 没有对层号的假设.

```agda
  ψ⁰-monoᵖ : ∀ {k₁ k₂} {a : Ordᶜ k₁} {b : Ordᶜ k₂} → a ⊑ᵖ b → ψ⁰ a ≼ ψ⁰ b
  ψ⁰-monoᵖ d = ⊑ᵖ→≼ (ψ⁰-⊑ d)

  -- 互相 ⊑ᵖ 的两棵树折叠后同值 (比 ≅ 宽, 比 ≈ᵛ 窄的一个同余)
  ψ⁰-congᵖ : ∀ {k₁ k₂} {a : Ordᶜ k₁} {b : Ordᶜ k₂} → a ⊑ᵖ b → b ⊑ᵖ a → ψ⁰ a ≈ᵛ ψ⁰ b
  ψ⁰-congᵖ d e = ψ⁰-monoᵖ d , ψ⁰-monoᵖ e

  -- 中间先折到任意目标层, 再折到第 0 层
  ψψ⁰-monoᵖ : ∀ {i i′ k₁ ℓ₁ k₂ ℓ₂} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂}
              {a : Ordᶜ k₁} {b : Ordᶜ k₂} → i ≅ᴵ i′ → a ⊑ᵖ b → ψ⁰ (ψ p σ a) ≼ ψ⁰ (ψ p′ σ′ b)
  ψψ⁰-monoᵖ ei d = ψ⁰-monoᵖ (ψ-⊑ ei d)
```

## §3 实例: 一切层的 `pointwise-mono`

`nodeʲ F` 是第 $j+1$ 层的结点, 分支 $x\mapsto F\,x$ 吃第 $j$ 层的树. $j=0$ 时就是 `RR4MonoFragment.node`; `nodeʲ (λ x → x)` 就是 $\Omega_{j+1}$.

```agda
  nodeʲ : ∀ {j} → (Ordᶜ j → Ordᶜ j) → Ordᶜ (suc j)
  nodeʲ F = limᵢ zero (λ x → up zero (F x))

  nodeʲ-⊑ : ∀ {j} {F G : Ordᶜ j → Ordᶜ j} → (M → ∀ x y → x ⊑ᵖ y → F x ⊑ᵖ F y) → (∀ x y → x ⊑ᵖ y → F x ⊑ᵖ G y) →
            nodeʲ F ⊑ᵖ nodeʲ G
  nodeʲ-⊑ {j = j} m h = node-⊑ (≅ᴵ-refl j) (λ μ x y d → u≤ (≤u (m μ x y d))) (λ x y d → u≤ (≤u (h x y d)))

  pointwise-mono : ∀ {j} {F G : Ordᶜ j → Ordᶜ j} → (M → ∀ x y → x ⊑ᵖ y → F x ⊑ᵖ F y) → (∀ x y → x ⊑ᵖ y → F x ⊑ᵖ G y) →
                   ψ⁰ (nodeʲ F) ≼ ψ⁰ (nodeʲ G)
  pointwise-mono m h = ψ⁰-monoᵖ (nodeʲ-⊑ m h)

  _ : ∀ {j} → nodeʲ {j} (λ x → x) ≡ Ω (suc j)
  _ = refl

  _ : ∀ (h : Br) → nodeʲ {zero} h ≡ node h
  _ = λ h → refl
```

前缀: 分支 $x\mapsto A+x$ 逐点高于恒等 (`K4MonoFold.⊑-addˡ`), 所以折叠值不低. `RR4MonoFragment.Prefix.fold-below` 是 $j=0$ 的情形.

```agda
  Ω-prefix : ∀ {j} (A : Ordᶜ j) → ψ⁰ (Ω (suc j)) ≼ ψ⁰ (nodeʲ (A +_))
  Ω-prefix A = pointwise-mono {F = λ x → x} (λ μ x y d → d) (λ x y d → ⊑-addˡ A d)

  Ω-prefix-⊑ : ∀ {j} (A : Ordᶜ j) → Ω (suc j) ⊑ᵖ nodeʲ (A +_)
  Ω-prefix-⊑ A = nodeʲ-⊑ {F = λ x → x} (λ μ x y d → d) (λ x y d → ⊑-addˡ A d)
```

第 2 层的一个例子. 分支吃第 1 层的 $x$, 先提升到第 2 层, 取后继, 再折回第 1 层 (目标层 1 的 `ψ`); 右边多取一次后继. 分支里的折叠由 `ψ-⊑` 自己处理, 不需要另外的引理.

```agda
  F₂ G₂ : Ordᶜ (suc zero) → Ordᶜ (suc zero)
  F₂ x = ψ {i = suc zero} {k = suc (suc zero)} {ℓ = suc (suc zero)} zero (λ r → r) (suc (up zero x))
  G₂ x = ψ {i = suc zero} {k = suc (suc zero)} {ℓ = suc (suc zero)} zero (λ r → r) (suc (suc (up zero x)))

  fb₂-⊑ : nodeʲ F₂ ⊑ᵖ nodeʲ G₂
  fb₂-⊑ = nodeʲ-⊑ (λ μ x y d → ψ-⊑ (s≅ z≅) (s≤ (u≤ (≤u d)))) (λ x y d → ψ-⊑ (s≅ z≅) (s≤ (≤s (u≤ (≤u d)))))

  fb₂ : ψ⁰ (nodeʲ F₂) ≼ ψ⁰ (nodeʲ G₂)
  fb₂ = ψ⁰-monoᵖ fb₂-⊑
```

## §4 第 1 层上关系的刻画

两个第 1 层的结点相关, 要么来自逐点规则 `i≤`, 要么来自 `≤i` (左结点在右结点的每一支之下). 后一种在第 1 层不可能: 右结点的分支是第 0 层的树, Ω-结点不在任何第 0 层的树之下 (`¬limᵢ⊑⁰`).

```agda
  ¬limᵢ⊑⁰ : ∀ {ℓ j} {p : j <ᴵ ℓ} {f : U j (<→◃ p) → Ordᶜ ℓ} {b : Ordᶜ zero} → limᵢ p f ⊑ᵖ b → ⊥
  ¬limᵢ⊑⁰ (≤s d)   = ¬limᵢ⊑⁰ d
  ¬limᵢ⊑⁰ (≤l n d) = ¬limᵢ⊑⁰ d
  ¬limᵢ⊑⁰ (i≤ {q = ()} e m h)
  ¬limᵢ⊑⁰ (≤i {q = ()} h)
  ¬limᵢ⊑⁰ (≤u {r = ()} d)

  node-inv₁ : ∀ {h h′ : Br} → node h ⊑ᵖ node h′ → ∀ {x y} → x ≼ y → h x ≼ h′ y
  node-inv₁ (i≤ e m k) {x} {y} xy = ⊑ᵖ→≼ (≤u⁻ (u≤⁻ (k x y (≼→⊑ᵖ xy))))
  node-inv₁ (≤i k)             xy = ⊥-elim (¬limᵢ⊑⁰ (≤u⁻ (k zero)))

  node-intro₁ : ∀ {h h′ : Br} → (M → ∀ {x y} → x ≼ y → h x ≼ h y) → (∀ {x y} → x ≼ y → h x ≼ h′ y) → node h ⊑ᵖ node h′
  node-intro₁ m r = nodeʲ-⊑ (λ μ x y d → ≼→⊑ᵖ (m μ (⊑ᵖ→≼ d))) (λ x y d → ≼→⊑ᵖ (r (⊑ᵖ→≼ d)))
```

## §5 边界: 哪些对不在关系里

`Value` 的 $\Omega_1'$ (分支 $g$ 把 $1$ 改成 $0$) 不合法: $g$ 对值序不单调 ($\lim(1,1,\dots)\preccurlyeq1$, 而 $g$ 把左边留着, 把右边变成 $0$).

```agda
  Ω₁′-not-legal : ¬ (Ω₁′ ⊑ᵖ Ω₁′)
  Ω₁′-not-legal d = bad (node-inv₁ {h = g₁} {h′ = g₁} d {x = lim (λ _ → 𝟏)} {y = 𝟏} (l≼ (λ _ → ≼-refl 𝟏)))
    where
    bad : lim (λ _ → 𝟏) ≼ 𝟎 {zero} → ⊥
    bad (l≼ k) = s≼0 (k 0)
```

两条已有的否定经 `ψ⁰-monoᵖ` 的逆否: 这两对不在关系里. 另一个方向在.

```agda
  Ω₁ˣ⋢Ω₁ : ¬ (Ω₁ˣ ⊑ᵖ Ω₁)
  Ω₁ˣ⋢Ω₁ d = proj₂ mono-fragment-not-cong (ψ⁰-monoᵖ d)

  Ω₁⋢Ω₁′ : ¬ (Ω₁ ⊑ᵖ Ω₁′)
  Ω₁⋢Ω₁′ d = proj₂ ψ⁰-not-cong (ψ⁰-monoᵖ d)

  Ω₁⊑Ω₁ˣ : Ω₁ ⊑ᵖ Ω₁ˣ
  Ω₁⊑Ω₁ˣ = Ω-prefix-⊑ X

  -- 第 1 层上关系严格细于值序: 值上 Ω₁ˣ ≼ Ω₁, 关系里没有
  finer : (Ω₁ˣ ≼ Ω₁) × ¬ (Ω₁ˣ ⊑ᵖ Ω₁)
  finer = proj₂ (proj₁ mono-fragment-not-cong) , Ω₁ˣ⋢Ω₁
```

## §6 两个版本的实例

```agda
module W = Val ⊥   -- 不带合法性
module L = Val ⊤   -- 带左合法性, 传递

-- RR4MonoFragment.Pointwise.pointwise-mono₁ 的陈述, 原样, 没有附加前提
pointwise-mono₁′ : ∀ (h h′ : Br) → (∀ {x y} → x ≼ y → h x ≼ h′ y) → ψ⁰ (node h) ≼ ψ⁰ (node h′)
pointwise-mono₁′ h h′ r = W.ψ⁰-monoᵖ (W.node-intro₁ (λ ()) r)

-- 第 1 层: 不带合法性的关系恰好是 pointwise-mono₁ 的前提
node-char : ∀ (h h′ : Br) →
            (node h W.⊑ᵖ node h′ → ∀ {x y} → x ≼ y → h x ≼ h′ y) ×
            ((∀ {x y} → x ≼ y → h x ≼ h′ y) → node h W.⊑ᵖ node h′)
node-char h h′ = W.node-inv₁ , W.node-intro₁ (λ ())

-- 带合法性的版本: 多要 h 自己单调; 换来传递与左自反
node-charᴸ : ∀ (h h′ : Br) →
             (node h L.⊑ᵖ node h′ → (∀ {x y} → x ≼ y → h x ≼ h y) × (∀ {x y} → x ≼ y → h x ≼ h′ y)) ×
             ((∀ {x y} → x ≼ y → h x ≼ h y) → (∀ {x y} → x ≼ y → h x ≼ h′ y) → node h L.⊑ᵖ node h′)
node-charᴸ h h′ = (λ d → L.node-inv₁ (L.⊑ᵖ-reflˡ tt d) , L.node-inv₁ d) , (λ m r → L.node-intro₁ (λ _ → m) r)

⊑ᴸ-trans : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} {c : Ordᶜ ℓ₃} → a L.⊑ᵖ b → b L.⊑ᵖ c → a L.⊑ᵖ c
⊑ᴸ-trans = L.⊑ᵖ-trans tt

⊑ᴸ-reflˡ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a L.⊑ᵖ b → a L.⊑ᵖ a
⊑ᴸ-reflˡ = L.⊑ᵖ-reflˡ tt
```

$\Omega_1'$ 在 `_≅_` 的定义域里 ($g$ 尊重 `≅`), 却不 `⊑ᵖ`-合法 (上面的 `Ω₁′-not-legal`, 两个版本都成立). 不带合法性的版本仍把它放在 $\Omega_1$ 之下 ($g\,x\preccurlyeq x$), 于是 $\psi^0(\Omega_1')\preccurlyeq\psi^0(\Omega_1)$; 反方向由 `Ω₁⋢Ω₁′` 排除.

```agda
g-≅ : ∀ {x y : Ordᶜ zero} → x ≅ y → g₁ x ≅ g₁ y
g-≅ z≅              = z≅
g-≅ (s≅ z≅)         = z≅
g-≅ (s≅ (s≅ e))     = s≅ (s≅ e)
g-≅ (s≅ (l≅ h))     = s≅ (l≅ h)
g-≅ (s≅ (lᵢ≅ {p = ()} e h))
g-≅ (s≅ (upˡ {r = ()} e))
g-≅ (s≅ (upʳ {r = ()} e))
g-≅ (l≅ h)          = l≅ h
g-≅ (lᵢ≅ {p = ()} e h)
g-≅ (upˡ {r = ()} e)
g-≅ (upʳ {r = ()} e)

Ω₁′-legal-≅ : Ω₁′ ≅ Ω₁′
Ω₁′-legal-≅ = lᵢ≅ z≅ (λ x y d → upˡ (upʳ (g-≅ d)))

g-defl : ∀ (x : Ordᶜ zero) → g₁ x ≼ x
g-defl zero                = z≼
g-defl (suc zero)          = z≼
g-defl (suc (suc x))       = ≼-refl _
g-defl (suc (lim f))       = ≼-refl _
g-defl (suc (limᵢ () f))
g-defl (suc (up () x))
g-defl (lim f)             = ≼-refl _
g-defl (limᵢ () f)
g-defl (up () x)

Ω₁′⊑Ω₁ : Ω₁′ W.⊑ᵖ Ω₁
Ω₁′⊑Ω₁ = W.node-intro₁ {h = g₁} {h′ = λ x → x} (λ ()) (λ {x} e → ≼-trans (g-defl x) e)

ψ⁰Ω₁′≼ψ⁰Ω₁ : ψ⁰ Ω₁′ ≼ ψ⁰ Ω₁
ψ⁰Ω₁′≼ψ⁰Ω₁ = W.ψ⁰-monoᵖ Ω₁′⊑Ω₁

≅-legal-not-⊑-legal : (Ω₁′ ≅ Ω₁′) × ¬ (Ω₁′ W.⊑ᵖ Ω₁′) × ¬ (Ω₁′ L.⊑ᵖ Ω₁′)
≅-legal-not-⊑-legal = Ω₁′-legal-≅ , W.Ω₁′-not-legal , L.Ω₁′-not-legal
```

## §7 边界: Ω-结点处不能有 "在某一支之下"

对第 1 层上的任意关系陈述. 取 $X=\psi^0(\Omega_1)$. 若一切第 0 层的 $x$ 都有 $\uparrow x$ 在 $\Omega_1$ 之下, 且关系被 $\psi^0$ 送进值序, 则 $\psi^0(X+1)\preccurlyeq X$; 而 $X+1\preccurlyeq\psi^0(X+1)$ (`RR4MonoFragment.x≼ψ⁰`), 矛盾.

```agda
no-below : (Rel : Ordᶜ (suc zero) → Ordᶜ (suc zero) → Set) →
           (∀ {a b} → Rel a b → ψ⁰ a ≼ ψ⁰ b) →
           ¬ (∀ (x : Ordᶜ zero) → Rel (up zero x) Ω₁)
no-below Rel snd bel = irr X (≼-trans (x≼ψ⁰ (suc X)) (snd (bel (suc X))))
```

两个前提各自可满足. 第一个: 本文的关系 (`W.ψ⁰-monoᵖ`), 于是它不含 "一切 $\uparrow x$ 在 $\Omega_1$ 之下". 第二个: 值序 (`≼-below`, 用的正是 `≼i`), 于是值序下折叠不单调; 这是 `TpPort2Tab.no-valmonoT⁺` 与 `Certified.ψ-not-⊑mono` 在 `Level` 族上的同一件事.

```agda
⊑ᵖ-no-below : ¬ (∀ (x : Ordᶜ zero) → up zero x W.⊑ᵖ Ω₁)
⊑ᵖ-no-below = no-below (λ a b → a W.⊑ᵖ b) W.ψ⁰-monoᵖ

≼-below : ∀ (x : Ordᶜ zero) → up zero x ≼ Ω₁
≼-below x = ≼i x (≅-refl⁰ x) (≼-refl (up zero x))

≼-not-fold-mono : ¬ (∀ {a b : Ordᶜ (suc zero)} → a ≼ b → ψ⁰ a ≼ ψ⁰ b)
≼-not-fold-mono m = no-below (λ a b → a ≼ b) m ≼-below
```

"在全部分支之下" 则可以: 规则 `≤i` 在定义里, 折叠保持它. 一个看得见的后果是零在一切树之下 (`zero⊑`), 而 "某一支" 的版本连 $\uparrow(X+1)$ 都放不进去.

## §8 小结

- 第 0 层: `⊑ᵖ` 就是 `≼`. 高层: Ω-结点逐点, 或左边在右结点的全部分支之下.
- `ψ⁰-monoᵖ` 对任意两层的输入成立, 一条引理.
- `pointwise-mono₁` 是它在第 1 层的实例, 陈述原样.
- 已知的两条否定都落在关系之外, 与定理不冲突.
