# X₁ 上叠层, 否定一路 (三): 同层的链从零起步时, 输出没有 Ω-结点

> 不含记号. 入口 [NegX1Up](NegX1Up.lagda.md). 本篇**不依赖**构造一路的接口; 对 [TySupFold](TySupFold.lagda.md) 的 `Φ` 与 [PathOutFold](PathOutFold.lagda.md) 的 `Ψ` (只读导入) 写. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题 (任务第 1 条的第三问).** 叠层时累加会不会让读法塌回? 本篇找到的塌缩点不在部分和本身, 在 "同层" 链的起点: `TySupFold.Φ` 的 `same` 分支是 `hl (chain b (λ b′ → Φ (g (to b′))))`, 链从**当前界** $b$ 起步. 可数层号的闭项 (`TySupSum.TCΣ`) 的目标总是第 0 层, 界从 $0$ 起步正对; 非零目标层上的 `same` 只在 "在上" 之后出现, 那时链从 `top i` 起步. 叠层后, 若上层折叠以 $X_1$ (非零层号) 为目标、界取 $0$, 而 $\Omega_{X_1+1}$-结点的分支是 `up` 形 (地板 `topC (hs x) = hΩ (inj₂ tt) up` 的形状), 链的每一项都不含 $\Omega$-结点.
>
> **结果.**
>
> 1. **`NoΩ`, `noΩ-⊞`, `FoldΦ.nmul`, `nchain`, `nΣ` (定理, 对一切种类结构).** "不含 $\Omega$-结点" 对 $\boxplus$, `mul`, `chain`, `Σ⁺` 封闭 (`chain` 要起点与每一步都保持).
> 2. **`Φ-noΩ` (定理, 对一切实例 `R`), `Ψ-noΩ` (定理, 对一切实例 `P`).** 输入不含 $\Omega$-结点, 输出也不含; 证明不经 `dec` (输入没有结点, 折叠的结点子句从不被用到).
> 3. **`same-noΩ` (定理, 对一切实例 `R`).** 若某次决定是 `same to`, 界 $b$ 不含 $\Omega$-结点, 且分支 $g\circ$`to` 把不含结点的坐标送到不含结点的树, 则这一步的输出 (`Φ` 的结点子句的值) 不含 $\Omega$-结点.
> 4. **`up-noΩ` (定理).** `up` 形的分支满足 3 的条件: `up c` 不含结点当且仅当 $c$ 不含 (`noΩ-up`, `up-noΩ⁻`).
> 5. **`flat-at-X₁` (定理, 对一切实例 `R` 与层号 $X$).** 把 1-4 合起来: 对输入 `hΩ κ up` (κ 是新种类), 若 `dec` 在目标 $t$ 上给 `same to` 且 `to` 是恒等搬运 (`to c ≡ c`), 从界 $b=0$ 起步, `Φ` 的输出不含 $\Omega$-结点. 前提实例: TySupC 的实例 `ICd`, 层号 $2$, 目标 $1$, 种类 `inj₂ tt` (层号 $1$): `dec` 给 `same` (`same-ICd`, refl), 结论 `flat-ICd`.
>
> **前提实例.** 1, 2, 4: 无前提. 3, 5: `flat-ICd` (可数层号上的实例, 与叠层无关, 说明前提可满足; 叠层的实例等构造一路的接口).
>
> **只否定什么.** 只说: 同层的链从零起步、分支是 `up` 形时, 这一步的输出没有 $\Omega$-结点; 之后再折到第 0 层 (PathOut 的 `Ψ`) 时不经 `dec` (2). **不否定**: 链从 `top X` 起步的写法 (那里起点有结点, 本篇不适用); 经 "在上" 到达非零层号的写法 (TySup 的写法); 部分和本身. 读法 "塌到 ε₀ 一档" 是判断 (没有值的定理); 定理档只到 "没有 $\Omega$-结点" 与 "不经 `dec`". 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegX1UpFlat where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥)
open import OCF.Align.TySupIf
open import OCF.Align.TySupC using (Cd; LC; ICd; _⊑ᶜ_)
import OCF.Align.TySupFold as TF
open import OCF.Align.PathOutIf using (PathOutIf; module PathOutIf)
import OCF.Align.PathOutFold as PF
```

## §1 不含 $\Omega$-结点

```agda
module _ {S : KS} where
  NoΩ : HB S → Set
  NoΩ hz = ⊤
  NoΩ (hs h) = NoΩ h
  NoΩ (hl f) = ∀ n → NoΩ (f n)
  NoΩ (hΩ _ _) = ⊥

  noΩ-⊞ : ∀ a b → NoΩ a → NoΩ b → NoΩ (a ⊞ b)
  noΩ-⊞ a hz na nb = na
  noΩ-⊞ a (hs b) na nb = noΩ-⊞ a b na nb
  noΩ-⊞ a (hl f) na nb = λ n → noΩ-⊞ a (f n) na (nb n)
  noΩ-⊞ a (hΩ _ _) na ()
```

## §2 折叠保 "不含结点" (对一切实例)

```agda
module FoldΦ (R : TySupIf) where
  open TySupIf R
  open TF R using (mul; chain; Σ⁺; Φ; caseDc)

  nmul : ∀ {S} (x : HB S) → NoΩ x → ∀ n → NoΩ (mul x n)
  nmul x nx zero = nx
  nmul x nx (suc n) = noΩ-⊞ (mul x n) x (nmul x nx n) nx

  nchain : ∀ {S} (b : HB S) k → NoΩ b → (∀ c → NoΩ c → NoΩ (k c)) → ∀ n → NoΩ (chain b k n)
  nchain b k nb nk zero = nk b nb
  nchain b k nb nk (suc n) = noΩ-⊞ _ _ (nchain b k nb nk n) (nk _ (noΩ-⊞ b _ nb (nchain b k nb nk n)))

  nΣ : ∀ {S} (f : ℕ → HB S) → (∀ n → NoΩ (f n)) → ∀ n → NoΩ (Σ⁺ f n)
  nΣ f nf zero = nf 0
  nΣ f nf (suc n) = noΩ-⊞ _ _ (nΣ f nf n) (nf (suc n))

  Φ-noΩ : ∀ X a lX t pt b h → NoΩ h → NoΩ (Φ X a lX t pt b h)
  Φ-noΩ X (acc rs) lX t pt b hz nh = tt
  Φ-noΩ X (acc rs) lX t pt b (hs h) nh = nmul _ (Φ-noΩ X (acc rs) lX t pt b h nh)
  Φ-noΩ X (acc rs) lX t pt b (hl f) nh = nΣ _ (λ n → Φ-noΩ X (acc rs) lX t pt b (f n) (nh n))
  Φ-noΩ X (acc rs) lX t pt b (hΩ κ g) ()
```

**同层一步.** `Φ` 在结点 `hΩ κ g` 上, 决定是 `same to` 时, 值就是 `hl (chain b (λ b′ → Φ … b′ (g (to b′))))` (定义展开, `same-val`).

```agda
  same-val : ∀ X a lX t pt b κ g to → dec X t pt lX κ ≡ same to →
    Φ X a lX t pt b (hΩ κ g) ≡ hl (chain b (λ b′ → Φ X a lX t pt b′ (g (to b′))))
  same-val X (acc rs) lX t pt b κ g to e rewrite e = refl

  same-noΩ : ∀ X a lX t pt b κ g to → dec X t pt lX κ ≡ same to → NoΩ b →
    (∀ c → NoΩ c → NoΩ (g (to c))) → NoΩ (Φ X a lX t pt b (hΩ κ g))
  same-noΩ X a lX t pt b κ g to e nb ng =
    subst NoΩ (sym′ (same-val X a lX t pt b κ g to e))
      (λ n → nchain b _ nb (λ c nc → Φ-noΩ X a lX t pt c (g (to c)) (ng c nc)) n)
    where
    sym′ : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    sym′ refl = refl
```

## §3 `up` 形的分支

```agda
noΩ-up : ∀ {S} (c : HB S) → NoΩ c → NoΩ (up c)
noΩ-up hz _ = tt
noΩ-up (hs c) n = noΩ-up c n
noΩ-up (hl f) n = λ m → noΩ-up (f m) (n m)
noΩ-up (hΩ _ _) ()

up-noΩ⁻ : ∀ {S} (c : HB S) → NoΩ (up c) → NoΩ c
up-noΩ⁻ hz _ = tt
up-noΩ⁻ (hs c) n = up-noΩ⁻ c n
up-noΩ⁻ (hl f) n = λ m → up-noΩ⁻ (f m) (n m)
up-noΩ⁻ (hΩ _ _) ()
```

**`flat-at-X₁`.** 层号 $X$ 的种类结构是 `step S` 一类 (新种类的坐标是 `HB S`, 分支 `up`), 只要求: 坐标类型就是 `HB S`, 搬运 `to` 是恒等. 这里对一般实例写成: 分支 $g$ 与 `to` 的复合是 `up`.

```agda
module Flat (R : TySupIf) where
  open TySupIf R
  open TF R using (Φ)
  open FoldΦ R

  flat-at-X₁ : ∀ X a lX t pt κ (g : E (L X) κ → HB (L X)) (to : HB (L t) → E (L X) κ) →
    dec X t pt lX κ ≡ same to →
    (∀ c → NoΩ c → NoΩ (g (to c))) →
    NoΩ (Φ X a lX t pt hz (hΩ κ g))
  flat-at-X₁ X a lX t pt κ g to e ng = same-noΩ X a lX t pt hz κ g to e tt ng
```

## §4 前提实例 (可数层号上)

`ICd`, 层号 $X=2$, 目标 $t=1$, 种类 `inj₂ tt` (第 2 层的新种类, 层号 $1$, 坐标是第 1 层的值). `decC` 给 `same` (refl). 分支 `up`, 搬运恒等.

```agda
one₁ two₁ : Cd
one₁ = hs hz
two₁ = hs one₁

pt₁₂ : one₁ ⊑ᶜ two₁
pt₁₂ = hsuc hself

κ₂ : K (LC two₁)
κ₂ = inj₂ tt

same-ICd : TySupIf.dec ICd two₁ one₁ pt₁₂ tt κ₂ ≡ same (λ c → c)
same-ICd = refl

flat-ICd : NoΩ (TF.Φ ICd two₁ (TySupIf.wf ICd two₁) tt one₁ pt₁₂ hz (hΩ κ₂ up))
flat-ICd = Flat.flat-at-X₁ ICd two₁ (TySupIf.wf ICd two₁) tt one₁ pt₁₂ κ₂ up (λ c → c) same-ICd (λ c nc → noΩ-up c nc)
```

## §5 PathOut 的 `Ψ` 也保 "不含结点" (对一切实例)

```agda
module FoldΨ (P : PathOutIf) where
  open PathOutIf P
  open PF P using (Ψ; PH)
  open FoldΦ R using (nmul; nΣ)

  Ψ-noΩ : ∀ W lW t pt b h ph → NoΩ h → NoΩ (Ψ W lW t pt b h ph)
  Ψ-noΩ W lW t pt b hz ph nh = tt
  Ψ-noΩ W lW t pt b (hs h) ph nh = nmul _ (Ψ-noΩ W lW t pt b h ph nh)
  Ψ-noΩ W lW t pt b (hl f) ph nh = nΣ _ (λ n → Ψ-noΩ W lW t pt b (f n) (ph n) (nh n))
  Ψ-noΩ W lW t pt b (hΩ κ g) ph ()
```

## 结论 (按档)

- **[定理]** `NoΩ`, `noΩ-⊞`; `FoldΦ.nmul`, `nchain`, `nΣ`, **`FoldΦ.Φ-noΩ`** (对一切 `R`), `same-val`, **`same-noΩ`**; `noΩ-up`, `up-noΩ⁻`; **`Flat.flat-at-X₁`**; `same-ICd`, **`flat-ICd`** (前提实例); **`FoldΨ.Ψ-noΩ`** (对一切 `P`).
- **[判断]** 读法塌到 ε₀ 一档 (没有值的定理); 构造一路是否落在本篇的前提里, 要看它的接口与闭项 (接口定稿后在实例检查里查).
