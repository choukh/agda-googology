# `tH` 实验 (三): 原则版的值, 定理

> 入口 [TLOne](TLOne.lagda.md). **判决: HOLDS (编译过, 无条件).** 只说原则版与 `T⊤`, 与它们自己的关系. 不读记号.
>
> | 定理 | 陈述 | 读法 (判断, 另写) |
> | --- | --- | --- |
> | `above-α` | `suc lv⊤ ≼ lv (Tᵖ M p (suc lv⊤))`, 一切 $M$, $p$ | 字面的 `Ω̇ (suc lv⊤)` 严格过了 `T⊤` |
> | `above-h` | `suc lv⊤ ≼ lv Tᴮ` | 高度槽也过了 |
> | `above-ν`, `next≻` | `suc lv⊤ ≼ lvᶜ′ lv⊤`; 迭代严格升 | 闭包严格升 |
> | `T⊤≺T̃ᴬ`, `T⊤≺T̃ᴰ` | 字面 $\prec$ | 回灌闭包在 `T⊤` 之上 |
> | `Tᶜ≼T̃ᴰ` | $x$ 在链上时 `lvᶜ′ x ≼ lv T̃ᴰ` | |
> | `below-chain` | 链上任何世界任何位置的第 0 行 $\prec$ `νT 𝒯 M₀` | 第 0 行落在闭包点之下 |
> | `dom-row` | 任何一行 (任何 $\alpha$) 的层号 $\preceq$ 把它喂给高度之后的第 0 行 | $\alpha$ 槽没有带来高度槽之外的东西 |
> | `fixᶜ-*` | `Fix` 在 `cs ⌈x⌉` 起点的实例: 输出与高度互相共尾 | `Tᶜ` 是一个闭包点, 就是 "下一个不动点" |
> | `clo-up`, `clo-dn` | `T̃ᴬ` 的链点与分支互相控制 | 同上 |
> | `no-world` | 没有码 $M$ 使一切 `C 𝒩 M₀ n ⊂ M` | 闭包点不是任何一个世界的行 |
> | `no-lift` | $M\subset M'$ 而 $M$ `ᶜ+ ⌈η⌉` $\not\subset M'$ `ᶜ+ ⌈η⌉` | 绑定的分支只按 $\eta$ 索引时上移写不出来, Kripke 分支是树逼的 |
> | `leaf-ψ`, `leaf-Ψ`, `top-new` | 折叠的叶子就是本世界的 `Ω̇`; 新世界的顶高于旧世界的像 | 折叠不出世界 |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLOneThm where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; n≤1+n)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Free.Level hiding (up)
open import OCF.Free.Prefix using (Z; toZ)
open import OCF.Free.Floor using (Ev)
open import OCF.Free.Force using (Goodᴺ; forceᴺ; forceᴺ-HS)
open import OCF.Free.Class using (lvG)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode using (⌈_⌉; _ᶜ+_; ωᶜ; _≼_; z≼; s≼; s≼ʳ; l≼; l≼ʳ; ≼-trans; ≼-refl; dom₀)
open import OCF.Align.LadderOrdStr using (≅→≼; ≺→s≼)
open import OCF.Align.LadderOrdCert using (ev₀; Tᵖ; Gᵖ)
open import OCF.Align.CrossMUp using (_⊂_; ⊂r; es; el; ⊂+; up)
open import OCF.Align.CrossMUpTree using (up≺; step≺)
open import OCF.Align.CrossMNode using (Node; node; ≺→⊑; C; νZ; Gν; νT; νlv; yv; ly; val-next; module Fix)
open import OCF.Free.Force using (gs)
open import OCF.Align.CrossMInst using (𝒯; val≼T; module Fixᵗ)
open import OCF.Align.CrossMClosed using (T⊤; HS⊤; lv⊤)
open import OCF.Align.CrossNextSum using (lvG-≼; module Sum; G-ofZ)
open import OCF.Align.TLOneDef
import OCF.Align.TLOneV as TV
import OCF.Align.LadderOrdTree
```

## §1 过了 `T⊤`

**$\alpha$ 槽.** `dom-α`: 第 $\alpha$ 行的值不低于 $\alpha$. 所以 `Ω̇ (suc lv⊤)` 折叠之后不低于 `suc lv⊤`, 对一切世界. 这里 `lv⊤` 不必在任何闭包里: 它字面地决定了层, 折叠的 $\alpha$ 是参数, 不是闭包里的项.

```agda
≼-≅ᵣ : ∀ {a b c} → a ≼ b → c ≅ᴵ b → a ≼ c
≼-≅ᵣ h e = ≼-trans h (≅→≼ (≅ᴵ-sym e))

module Vᴹ (M : Code) = TV (HB M)

dom-row-α : ∀ M (p : Pos (cs M)) α → α ≼ lvG (Gᵖ M p α)
dom-row-α M p α = ≼-≅ᵣ (Vᴹ.dom-α M p α) (Vᴹ.Lv≅lvG M p α ev₀ (Gᵖ M p α))

above-α : ∀ M (p : Pos (cs M)) → suc lv⊤ ≼ lvG (Gᵖ M p (suc lv⊤))
above-α M p = dom-row-α M p (suc lv⊤)
```

**高度槽.** 已有的 `val≼T` 加 `dom₀`, 对变量 $x$. 全文的定理都对变量证: 闭合世界上比较 `forceᴺ` 的不同写法要化简证书, 直接写闭项 12G 堆内没有结果 (第一版的 `above-ν = l≼ʳ 0 above-h`, 这不是否定, 只是写法).

```agda
above-h′ : ∀ x → suc x ≼ lvG (Gᵖ (cs ⌈ x ⌉) end zero)
above-h′ x = ≼-trans (s≼ (dom₀ x)) (val≼T (cs ⌈ x ⌉))

above-h : suc lv⊤ ≼ lvG (Gᵖ (cs ⌈ lv⊤ ⌉) end zero)
above-h = above-h′ lv⊤
```

**闭包.** 第 0 项不低于高度的值. 对抽象的节点证, 不展开 `𝒯`.

```agda
module AbsN (𝒩 : Node) where
  first-above : ∀ M₀ {y} → y ≼ ly 𝒩 M₀ → y ≼ νlv 𝒩 M₀
  first-above M₀ h = l≼ʳ 0 h

  in-chain : ∀ M₀ n {c : Ordᶜ zero} → c ≺ yv 𝒩 (C 𝒩 M₀ n) → c ≺ νT 𝒩 M₀
  in-chain M₀ n r = ≺l n r

val≼𝒯 : ∀ M → val M ≼ ly 𝒯 M
val≼𝒯 = val≼T

above-ν′ : ∀ x → suc x ≼ lvᶜ′ x
above-ν′ x = AbsN.first-above 𝒯 (cs ⌈ x ⌉) (≼-trans (s≼ (dom₀ x)) (val≼𝒯 (cs ⌈ x ⌉)))

above-ν : suc lv⊤ ≼ lvᶜ′ lv⊤
above-ν = above-ν′ lv⊤

-- 迭代严格升: 对 k 一致
next≻ : ∀ x k → suc (itᶜ x k) ≼ lvᶜ′ (itᶜ x k)
next≻ x k = above-ν′ (itᶜ x k)
```

**回灌闭包 (`Sum`).** 对任何分支族证: 链的第 1 点字面地以第 0 点为前缀; 分支的层号不超过闭包.

```agda
module AbsS (b : Ordᴵ → Z) (G : ∀ η → Goodᴺ (b η)) {t₀ : Z} (G₀ : Goodᴺ t₀) where
  open Sum b G G₀

  t₀≺ : forceᴺ _ G₀ ≺ T̃
  t₀≺ = ≺l 1 (pre≺ (ys 0) (hy 0))

  br≼ : ∀ k → lvG (G (η k)) ≼ lvG ĜS
  br≼ k = l≼ʳ (suc k) (lvG-≼ (gs (G-ofZ (η k))) (G (η k)))

Gbᴬ : ∀ η → Goodᴺ (bᴬ η)
Gbᴬ η = Gᵖ ωᶜ end (suc η)

Gbᴰ : ∀ η → Goodᴺ (bᴰ η)
Gbᴰ η = Gν 𝒯 (cs ⌈ η ⌉)

module Aᴬ = AbsS bᴬ Gbᴬ (Gν 𝒯 ωᶜ)
module Aᴰ = AbsS bᴰ Gbᴰ (Gν 𝒯 ωᶜ)
module Sᴬ = Sum bᴬ Gbᴬ (Gν 𝒯 ωᶜ)
module Sᴰ = Sum bᴰ Gbᴰ (Gν 𝒯 ωᶜ)

T⊤≺T̃ᴬ : T⊤ ≺ Sᴬ.T̃
T⊤≺T̃ᴬ = Aᴬ.t₀≺

T⊤≺T̃ᴰ : T⊤ ≺ Sᴰ.T̃
T⊤≺T̃ᴰ = Aᴰ.t₀≺

-- T̃ᴰ 的分支就是 "从链点起的下一个闭包点"
Tᶜ≼T̃ᴰ : ∀ k → lvᶜ′ (Sᴰ.η k) ≼ lvG Sᴰ.ĜS
Tᶜ≼T̃ᴰ = Aᴰ.br≼
```

## §2 第 0 行落在闭包点之下

`below-chain`: 链上任何世界 $C_n$ 的任何位置, 第 0 行严格低于闭包点. 比较在 $C_{n+1}$ 这个字面的公共上界里. $\alpha\ne0$ 的行不在这条定理里: 见 `above-α`.

```agda
module AbsL (b : Code → Z) (G : ∀ M → Goodᴺ (b M)) (u : ∀ M N → forceᴺ _ (G M) ⊑⁰ forceᴺ _ (G (M ᶜ+ cs N)))
  (low : ∀ A N (p : Pos (cs A)) → forceᴺ _ (Gᵖ A p zero) ≺ forceᴺ _ (G (A ᶜ+ cs N))) where
  𝒩ᴸ : Node
  𝒩ᴸ = node b G u

  below : ∀ M₀ n (p : Pos (cs (C 𝒩ᴸ M₀ n))) → forceᴺ _ (Gᵖ (C 𝒩ᴸ M₀ n) p zero) ≺ νT 𝒩ᴸ M₀
  below M₀ n p = ≺l (suc n) (low (C 𝒩ᴸ M₀ n) ⌈ ly 𝒩ᴸ (C 𝒩ᴸ M₀ n) ⌉ p)

below-chain : ∀ M₀ n (p : Pos (cs (C 𝒯 M₀ n))) → forceᴺ _ (Gᵖ (C 𝒯 M₀ n) p zero) ≺ νT 𝒯 M₀
below-chain = AbsL.below (λ M → toZ (Tᵖ M end zero ev₀ zero)) (λ M → Gᵖ M end zero) (λ M N → ≺→⊑ (step≺ M N)) (λ A N p → up≺ (⊂+ A (cs N)) p end tt)
```

**$\alpha$ 槽不带来高度槽之外的东西.** 任何一行喂给高度之后的第 0 行不低于它. 所以把 "行" 换成 "第 0 行" 不丢高度: 原则版的族与 `M ↦ Tᵖ M end 0` 互相控制.

```agda
dom-row : ∀ M (p : Pos (cs M)) α → lvG (Gᵖ M p α) ≼ lvG (Gᵖ (M ᶜ+ cs ⌈ lvG (Gᵖ M p α) ⌉) end zero)
dom-row M p α = ≼-trans (val-next M (lvG (Gᵖ M p α))) (val≼T (M ᶜ+ cs ⌈ lvG (Gᵖ M p α) ⌉))
```

## §3 "下一个不动点"

`Fix` 对一切起点是定理. 在 `cs ⌈x⌉` 上: 输出的层号与高度的值互相共尾. 在字面的这个意义下, `Tᶜ′ x` 是 $x$ 之上的闭包点; 最小性没有编译 (它是 $\preceq$ 下的陈述, 要折叠对值单调, `ψ⁰-not-cong` 一带已知不便宜).

```agda
module Fᶜ (x : Ordᴵ) = Fixᵗ (cs ⌈ x ⌉)

-- 记号: Fix 的节点与 𝒯 是同一个构造, 陈述直接用 Fix 的
fixᶜ-up : ∀ x n → ly (Fᶜ.𝒩 x) (Fᶜ.Cₜ x n) ≼ val (Fᶜ.Cₜ x (suc n))
fixᶜ-up x = Fᶜ.feed-up x

fixᶜ-dn : ∀ x n → val (Fᶜ.Cₜ x n) ≼ ly (Fᶜ.𝒩 x) (Fᶜ.Cₜ x n)
fixᶜ-dn x = Fᶜ.feed-dn x

fixᶜ-out : ∀ x n → val (Fᶜ.Cₜ x n) ≼ νlv (Fᶜ.𝒩 x) (cs ⌈ x ⌉)
fixᶜ-out x = Fᶜ.cof-out x

fixᶜ-ht : ∀ x {y} → y ≺ᴵ νlv (Fᶜ.𝒩 x) (cs ⌈ x ⌉) → Σ ℕ λ n → y ≼ val (Fᶜ.Cₜ x (suc n))
fixᶜ-ht x = Fᶜ.cof-ht x
```

`T̃ᴬ`: 分支 $b(\eta_k)$ 的层号不超过闭包, 链点严格地爬. 所以 $\alpha\mapsto$ `Tᵖ ωᶜ end (suc α)` 沿链封闭.

```agda
clo-up : ∀ k → lvG (Gbᴬ (Sᴬ.η k)) ≼ lvG Sᴬ.ĜS
clo-up = Aᴬ.br≼

clo-dn : ∀ k → suc (Sᴬ.η k) ≼ lvG Sᴬ.ĜS
clo-dn k = ≼-trans (dom-row-α ωᶜ end (suc (Sᴬ.η k))) (clo-up k)
```

## §4 闭包点不是任何一个世界的行

`hgt`: 码沿第 0 块的深度. `⊂` 不降深度, 链每一步升深度. 所以一个码只含链的有限段.

```agda
hgt : Code → ℕ
hgt cz = 0
hgt (cs c) = suc (hgt c)
hgt (cl g) = suc (hgt (g 0))

⊂-hgt : ∀ {A B} → A ⊂ B → hgt A ≤ hgt B
⊂-hgt ⊂r = ≤-refl
⊂-hgt (es e) = ≤-trans (⊂-hgt e) (n≤1+n _)
⊂-hgt (el e) = ≤-trans (⊂-hgt e) (n≤1+n _)

C-hgt : ∀ (𝒩 : Node) M₀ n → n ≤ hgt (C 𝒩 M₀ n)
C-hgt 𝒩 M₀ zero = z≤n
C-hgt 𝒩 M₀ (suc n) = s≤s (≤-trans (C-hgt 𝒩 M₀ n) (⊂-hgt (⊂+ (C 𝒩 M₀ n) ⌈ ly 𝒩 (C 𝒩 M₀ n) ⌉)))

no-world : ∀ (𝒩 : Node) M₀ M → (∀ n → C 𝒩 M₀ n ⊂ M) → ⊥
no-world 𝒩 M₀ M f = absurd (≤-trans (C-hgt 𝒩 M₀ (suc (hgt M))) (⊂-hgt (f (suc (hgt M)))))
  where
  absurd : ∀ {n} → suc n ≤ n → ⊥
  absurd {suc n} (s≤s h) = absurd h
```

**把全部世界放进一个 `HtB`.** 这是 "凡下标都可作层" 最字面的读法: 一个高度结构含一切下标, 闭包点就是它的一行, 不用新绑定. 这条已被否定 (`LadderOrdNeg`, 不是这里证的): `no-all-Ord` (字面忠实, 矛盾), `all-Ord→LPO` (忠实到值, LPO), `no-tri-code` (跨码三歧假), `no-cofinal` (单个 $M$ 的秩穷尽不了 `Ordᴵ`). 前提可满足性见那个文件的表.

## §5 绑定的分支为什么是 Kripke 的

只按 $\eta$ 索引的分支 `∀ η → T (M ᶜ+ ⌈η⌉)`, 上移算子过不去: 要把 `T (M ᶜ+ ⌈η⌉)` 变成 `T (M′ ᶜ+ ⌈η⌉)`, 而这两个码之间可以没有 `⊂`. 这条只否定那个索引方式, 反例是 $M=0$, $M'=1$, $\eta=\omega$.

```agda
hd : Code → Code
hd (cl g) = g 0
hd c = c

Xᶜ Yᶜ : Code
Xᶜ = cz ᶜ+ ⌈ ωᴵ ⌉
Yᶜ = cs cz ᶜ+ ⌈ ωᴵ ⌉

no₀ : ∀ {D} → Xᶜ ⊂ D → D ≡ cz → ⊥
no₀ ⊂r ()
no₀ (es x) ()
no₀ (el x) ()

no₁ : ∀ {D} → Xᶜ ⊂ D → D ≡ cs cz → ⊥
no₁ ⊂r ()
no₁ (es x) refl = no₀ x refl
no₁ (el x) ()

no₂ : ∀ {D} → Xᶜ ⊂ D → D ≡ Yᶜ → ⊥
no₂ ⊂r e with cong hd e
... | ()
no₂ (es x) ()
no₂ (el x) e = no₁ x (cong hd e)

no-lift : Σ Code λ M → Σ Code λ M′ → Σ Ordᴵ λ η → (M ⊂ M′) × ((M ᶜ+ ⌈ η ⌉ ⊂ M′ ᶜ+ ⌈ η ⌉) → ⊥)
no-lift = cz , cs cz , ωᴵ , es ⊂r , (λ x → no₂ x refl)
```

## §6 折叠不出世界

`leaf-ψ`, `leaf-Ψ`: 叶子是本世界的 $\dot\Omega$. `top-new`: 接上去一段后, 新的顶严格高于旧世界的一切位置的像, 所以新世界顶上的第 0 行不是任何旧高度上的项 (`↓ᴾ` 下不来).

```agda
top-new : ∀ M N (p : Pos (cs M)) → up (⊂+ M (cs N)) p <ᴾ end
top-new M N p = tt

module Lf (M : Code) where
  open OCF.Align.LadderOrdTree (HB M)

  leaf-ψ : ∀ {m α t φ χ} (q : t <ᴵ α) → ψᵠ {m} q {φ} {χ} q0 ≡ qwk proj₁ fc* (Ω̇ m t)
  leaf-ψ q = refl

  leaf-Ψ : ∀ {H m α φ χ t w} (qH : H <ᴸ m) (ok : Ok w) (e : Eh H m w χ) (p : t <ᴵ w H) → Ψ {α = α} {φ = φ} qH ok e p q0 ≡ qwk proj₁ fc* (Ω̇ H t)
  leaf-Ψ qH ok e p = refl
```
