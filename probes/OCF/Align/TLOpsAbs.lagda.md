# 树的算子语言 (九): 一条迭代定理的四个实例

> 不含记号. 入口 [TLOps](TLOps.lagda.md). `Iter`: **单调迭代.** 载体 $X$ 上有预序 $\rightsquigarrow$, 一步 `step` 保序, 起点 $x_0\rightsquigarrow\mathrm{step}\,x_0$, 输出 `out` 保序, 则 $\mathrm{out}(x_n)\rightsquigarrow'\mathrm{out}(x_{n+1})$. 证明两行. 下面四个实例的载体不同, 这就是 "回灌闭包" 这个词的全部内容:
>
> | 实例 | 载体 $X$ | 一步 | 输出 | 来自 |
> |---|---|---|---|---|
> | `inst-feed` | `Ordᴵ`, $\sqsubseteq^{\mathsf I}$ | $\eta\mapsto\mathrm{lv}(g\,\eta)$ | $g\,\eta$ | `TreeLangFeed.Clo`, 即 `Goodᴺ.gc` 的计值 |
> | `inst-ν` | `Code`, 初始段 | $M\mapsto M$ `ᶜ+ cs` $\lceil\mathrm{ly}\,M\rceil$ | 分支 | `CrossMNode.Gν`, `refl` |
> | `inst-γ` | 层 $k$ 的元素, $\trianglelefteq$ | $z\mapsto\psi_k(h\,z)$ | $z\mapsto\psi_\tau(h\,z)$ | `ψᵒ` 的 `injᵇ` 行, $\gamma$-链 |
> | `inst-cell` | `Clo.Cell`, $\trianglelefteq_0$ | 回灌 | 输出 | [TLOpsClo](TLOpsClo.lagda.md) |
>
> **$\gamma$-链不是新算子, 也不是从记号抄的规则的残余: 它是载体为层 $k$ 的回灌闭包.** "同一闭包在不同目标下算两次" 就是 step 用目标 $k$, out 用目标 $\tau$. 这条定理很浅, 深的部分是各个实例的前提, 见 [TLOps](TLOps.lagda.md): `inst-γ` 的前提由 `ψL′`, `hMi`, `Ωfst` 对一切项给出, `inst-feed` 的前提要 `g` 对 $\sqsubseteq^{\mathsf I}$ 单调.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLOpsAbs where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import OCF.Free.Level using (Ordᴵ; Ordᶜ; _⊑ᴵ_; _⊑⁰_; _≅_; l≅; ≅-refl⁰; HS; hl; toLevel; toLevel-⊑)
import OCF.Free.Level as FL
open import OCF.Free.Force using (forceᴺ; forceᴺ-HS)
open import OCF.Align.TreeLangFeed using (module Clo)
open import OCF.Align.CumReadCF using (A; _≪_; _⊲_; ≪⊲; ⊲-tr; ≪S)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit using (Ord₀; _⊴₀_; ⊴₀→⊑⁰; Lit₀; HS₀)
open import OCF.Align.LadderOrdPos using (Code; cs)
open import OCF.Align.LadderOrdCode using (⌈_⌉; _ᶜ+_)
open import OCF.Align.CrossMNode using (Node; C; νT; νHS; ly; yv; Gbr; ↑br)
open import OCF.Align.TLOpsW
open import OCF.Align.TLOpsLe
open import OCF.Align.TLOpsMain
import OCF.Align.TLOpsClo as K
```

## §1 单调迭代

```agda
module Iter {X Y : Set} (_⇝_ : X → X → Set) (_⇝′_ : Y → Y → Set) (s : X → X) (out : X → Y)
            (x₀ : X) (inf : x₀ ⇝ s x₀) (sm : ∀ {x y} → x ⇝ y → s x ⇝ s y) (om : ∀ {x y} → x ⇝ y → out x ⇝′ out y) where
  it : ℕ → X
  it zero = x₀
  it (suc n) = s (it n)

  it-up : ∀ n → it n ⇝ it (suc n)
  it-up zero = inf
  it-up (suc n) = sm (it-up n)

  out-up : ∀ n → out (it n) ⇝′ out (it (suc n))
  out-up n = om (it-up n)
```

## §2 累积形 (一步总往上)

`Code` 的链不是单调迭代: 每一步都接在自己上面, 与上一步是否保序无关. 取 `sm` 的位置换成 `up`. 这是同一条定理的退化情形: `it-up` 不再需要归纳.

```agda
module IterUp {X Y : Set} (_⇝_ : X → X → Set) (_⇝′_ : Y → Y → Set) (s : X → X) (out : X → Y) (x₀ : X)
              (up : ∀ x → x ⇝ s x) (om : ∀ {x y} → x ⇝ y → out x ⇝′ out y) where
  it : ℕ → X
  it zero = x₀
  it (suc n) = s (it n)

  out-up : ∀ n → out (it n) ⇝′ out (it (suc n))
  out-up n = om (up (it n))
```

## §3 实例

`inst-feed`: `TreeLangFeed.Clo` 的 `HS-clo` 要的 `st`, 由 $g$ 的单调给出. 这正是 `OCF/Free/Main` 的 `TopClo` 里 `mF` 的用处.

```agda
module inst-feed (t₀ : Ordᶜ FL.zero) (h₀ : HS t₀) (g : Ordᴵ → Ordᶜ FL.zero) (hg : ∀ η → HS (g η))
                 (mono : ∀ {η η′} → η ⊑ᴵ η′ → g η ⊑⁰ g η′)
                 (first : t₀ ⊑⁰ g (toLevel t₀ h₀)) where
  open Clo t₀ h₀ g hg (FL.suc t₀) g using (lv; ch)

  x₀ : Ordᴵ
  x₀ = toLevel t₀ h₀

  sf : Ordᴵ → Ordᴵ
  sf η = toLevel (g η) (hg η)

  private module I = Iter _⊑ᴵ_ _⊑⁰_ sf g x₀
                          (toLevel-⊑ h₀ (hg x₀) first)
                          (λ d → toLevel-⊑ (hg _) (hg _) (mono d)) mono

  outs : ℕ → Ordᶜ FL.zero
  outs n = g (I.it n)

  HS-outs : HS (FL.lim outs)
  HS-outs = hl (λ n → hg (I.it n)) I.out-up

-- CrossMNode.Gν: 分支对一切码, 链累积, 字面就是这个形状
module inst-ν (𝒩 : Node) (M₀ : Code) where
  _⇝_ : Code → Code → Set
  M ⇝ M′ = Σ Code λ N → M′ ≡ M ᶜ+ cs N

  sf : Code → Code
  sf M = M ᶜ+ cs ⌈ ly 𝒩 M ⌉

  om : ∀ {M M′} → M ⇝ M′ → yv 𝒩 M ⊑⁰ yv 𝒩 M′
  om {M} (N , refl) = ↑br 𝒩 M N

  private module I = IterUp _⇝_ _⊑⁰_ sf (yv 𝒩) M₀ (λ M → _ , refl) om

  chain≡ : ∀ n → I.it n ≡ C 𝒩 M₀ n
  chain≡ zero = refl
  chain≡ (suc n) = cong sf (chain≡ n)

  -- 与 νT 逐项是同一棵树, 步进证据也来自这里
  T≅ : FL.lim (λ n → yv 𝒩 (I.it n)) ≅ νT 𝒩 M₀
  T≅ = l≅ (λ n → subst (λ M → yv 𝒩 (I.it n) ≅ yv 𝒩 M) (chain≡ n) (≅-refl⁰ _))

  HS≡ : HS (FL.lim (λ n → yv 𝒩 (I.it n)))
  HS≡ = hl (λ n → forceᴺ-HS _ (Gbr 𝒩 (I.it n))) I.out-up

-- ψ 的上升行: 载体是层 k 的元素. 前提都来自闭包定理的通用引理, 不看 h 的形状.
module inst-γ {p a u m k q t} (H : Hk p q) {r : k ≪ a}
              {f : ∀ {v} → u ⊲ v → Gw v → Vs p a (≪S r) v → 𝓞 p a v} (w : WF (oi r f))
              (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) where
  km : k ⊲ m
  km = ⊲-tr (≪⊲ r) am

  body : 𝓞 p k m → 𝓞 p a m
  body z = f um gm (inS (≪S r) z)

  sf : 𝓞 p k m → 𝓞 p k m
  sf z = ψ p k (hkR H) (body z) gm m gm C.self km am

  out : 𝓞 p k m → 𝓞 q t m
  out z = ψ q t H (body z) gm m gm C.self tm am

  sm : ∀ {x y} → x ⊴ y → sf x ⊴ sf y
  sm d = ψL′ p k (hkR H) (hkR H) (hMi {r = r} w um gm d) gm gm m gm C.self km am m gm C.self km am

  om : ∀ {x y} → x ⊴ y → out x ⊴ out y
  om d = ψL′ q t H H (hMi {r = r} w um gm d) gm gm m gm C.self tm am m gm C.self tm am

  private module I = Iter _⊴_ _⊴_ sf out (Ω̇at p k gm) (Ωfst p k (hkR H) (body (Ω̇at p k gm)) gm m gm C.self km am) sm om

  -- 与 ψᵒ 的上升行逐字同形
  chain≡ : ∀ n → I.it n ≡ chainᵒ gm sf n
  chain≡ zero = refl
  chain≡ (suc n) = cong sf (chain≡ n)

  γ-up : ∀ n → out (I.it n) ⊴ out (I.it (suc n))
  γ-up = I.out-up

-- 顶层闭包: 载体是 Cell
module inst-cell (F : K.Fam) where
  open K.Clo F

  private module I = IterUp (λ c c′ → Cell.y c ⊴₀ Cell.y c′) (λ a b → a ⊑⁰ b) step Cell.y start
                            (λ c → Cell.mono c) ⊴₀→⊑⁰

  cell≡ : ∀ n → I.it n ≡ cell n
  cell≡ zero = refl
  cell≡ (suc n) = cong step (cell≡ n)

  up′ : ∀ n → Cell.y (I.it n) ⊑⁰ Cell.y (I.it (suc n))
  up′ = I.out-up
```
