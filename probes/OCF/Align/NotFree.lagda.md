# 记号无关的证书 `Goodᴺ`: 可行性研究

> 接 [GoodLBase](GoodLBase.lagda.md) §1 与 [Omega2](Omega2.lagda.md) §4–§5. 纲领要求树的**定义**独立于 EBO 记号, 记号只作事后验收的尺子. BTBO 阶段如此 (`Uniform : ∀ a → HS (ψ⁰ (Ω a))` 是纯树侧定理); EBO 阶段自 GoodLBase 起, 证书 `Goodᴸ` 把记号项的标签列 $\gamma:\mathbb N\to T$ 当字段, 可容许的计值点是 "带标签 $\gamma_m$ 的树的层号", 单调与支配都从标签得来. 计值 `forceᴸ` 不读标签, 所以树的**计算**与记号无关, 但闭项的**可定义性**以记号为证明见证. 本文研究: 能否在不改计值树 (模 $\cong$) 的前提下把证书做成记号无关的.
>
> 结论先说:
>
> 1. **记号无关的证书类型存在且好用 (§1–§2).** `Goodᴺ` 把可容许点取为闭包**自己的链点**: `gc` 带一个树序列 `ys` (链的 "预言"), 分支证书只在 `ys m` 的层号处给出, 约束 `l₀ : force t₀ ≅ ys 0`、`lE m : force (g (lvl ys m)) ≅ ys (m+1)` 让 `ys` 模 $\cong$ 就是链. 没有 `T`, 没有 `Set₁`, 正性与停机一次通过. 链在类型里字面迭代的余归纳写法 (`Goodᶜ`, §1′) 也可行, 对结论无影响. 计值与证书无关 (`forceᴺ-≅`), 所以 "标签层只做验收" 在类型层面成立: 一个记号无关的 $t_2$ 证书一旦存在, 它的树自动 $\cong$ `T2ᴸ` 并带标签 $t_2$ (`any-T2`, `any-T2-label`).
> 2. **桥 (§3).** `ofZ : Goodᶻ x → Goodᴺ x` (Prefix 的 "一切 $\eta$" 证书限制到链点) 与 `ofL : Goodᴸ x → Goodᴺ x` (遗忘标签), 计值都不变 (`ofZ-≅`, `ofL-≅`). 前者把已有的**记号无关**证书全部搬过来; 后者给出 `Goodᴺ` 在 $t_2$、$\psi_0(\Omega_\Omega\cdot k)$、$\psi_0(\Omega_\Omega\cdot\Omega_2)$ 等处的居留, 但构造仍经过标签 (不是纲领要的答案, 只说明 `Goodᴺ` 不比 `Goodᴸ` 窄).
> 3. **决定性检验 (§4–§5).** (b) $\psi_0(\Omega_\Omega+\Omega_2)$: **通过**, `GᴺX₂ = ofZ GX₂`, 构造只用观测前序 (UniformS/Stage2Label), `forceᴺ … GᴺX₂ ≅ X₂ᶠ` 与标签 `X₂-label` 都是验收; $X_3$、BTBO、$t_2$ 的第 0 个链点 $\gamma'_1$ 同样通过. (a) $\psi_0(\Omega_\Omega\cdot2)$: **未通过**, 停在链指标 $k=1$: 需要 $\gamma'_2=\psi_0(\Omega_\Omega+\Omega_{\gamma'_1})$ 的计值树的记号无关证书 (`NextN` 的第 0 项). 外层的障碍 (Omega2 §5: `Goodᶻ` 要求一切 $\eta$) 被 `Goodᴺ` 消除了 (`Gᴺ₂-of`: 只要链点处的证书), 剩下的全是 $\gamma'_2$ **内部**闭包的支配: 只要 $\gamma'_2$ 的计值树有一个 Prefix 证书, 这一步的支配与单调都记号无关地得出 (`step₀`). (c) $\psi_0(\Omega_\Omega\cdot\Omega_2)$: 只有经标签的居留.
> 4. **支配为什么不能从观测前序得到 (§6).** 内部闭包的支配 "$w+1\sqsubseteq\mathtt{lvl}$ 链点" 不是单调性的推论: 闭包在被 $\psi^{[\hat\Omega]}_0$ 计值之前会被更低目标的 $\psi_j$ ($j<w$) 逐点映射, 观测前序只给链点 $\sqsupseteq\psi^{[\hat\Omega]}_0(\cdots\psi_j(\cdots\Omega_j))$, 层号 $\succ j$, 不到 $w$. 全局界 (Omega2Base `Strictᵝ`) 被 `no-Bound` 排除, 值序 `≼` 被 `shift≈` 排除 (不动点处严格增长为假). 缺的是**树侧的出现性不变量** (SystemOmega `occ<` 的树版: "链点的计值树里出现层号 $\succeq w$ 的子树"), 是证明技术上的缺口, 不是假命题 (标签路线证明了每个出现的闭包都被支配).
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NotFree where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Level
open import OCF.Align.Symbolic using (Ctx; Pt; lvP; Γᶜ; χᶜ-step)
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Ordˢ; toZ; Goodᶻ; force; force-HS; outs; t2ˢ; X₂ˢ)
open import OCF.Align.UniformS using (_≅ᶻ_; zᶻ; sᶻ; lᶻ; ĉᶻ; toZ-≅)
import OCF.Align.GoodLBase as GL
open GL using (Goodᴸ; forceᴸ; forceᴸ-HS; Ptᴸ; ptsᴸ; lvᴸ)
```

## §1 `Goodᴺ`: 链点由预言序列给出

**设计.** `Goodᴸ` 的标签列 $\gamma$ 有两个作用: (i) 给可容许点一个**外部**的名字 ("带标签 $\gamma_m$"), 打破 "分支证书的定义域依赖分支证书本身" 的循环; (ii) 提供单调与支配. 记号无关的证书只需要 (i) 的替身. 最直接的候选是让链点**在类型内部**由分支证书迭代生成, 可容许点 = "可达的点". 作为一个字段的谓词写不出来: "可达" 要提到正在定义的字段 `Gg` (`Gg` 的定义域是 `Reach`, `Reach` 的后继子句要 `force (Gg …)`), 而构造子的字段只能依赖前面的字段. 有两种写法可行 (都已编译): (1) **余归纳的链证书** (§1′, `Goodᶜ`): `record Chainᶜ … Y where coinductive; field G : Goodᶜ (g (lvl Y)); d : 支配; next : Chainᶜ … (forceᶜ G)`, 链字面在类型里迭代; 计值仍对 `Z` 结构递归 (`nthᶜ` 对 $k$ 递归, 回到 `forceᶜ` 时 `Z` 的下标是 `g η`, 小于 `ĉᴸ c t₀ g …`), 停机检查通过; 需要 `--guardedness` (仓库的 `agda-lib` 对全部文件都开着). (2) **预言序列** (本节, `Goodᴺ`): 替身取**数据**, 一个树序列 `ys`, 由约束钉成链 (模 $\cong$):

$$\mathtt{ys}\,0\cong\mathtt{force}\,t_0,\qquad \mathtt{ys}\,(m{+}1)\cong\mathtt{force}\,(g\,(\mathtt{lvl}\,\mathtt{ys}\,m)).$$

分支证书 `Gg m` 只在 `ys m` 的层号处给出, 支配 `dy m` 是每个链点的字段, 输出证书 `Go k` 与输出单调同 `Goodᴸ`. 与 `Goodᴸ` 相比, 这里的 "标签" 就是链点自己 (自标签), 可容许点恰好是链点而不是 "一切带同一标签的树"; 后者在 `Goodᴸ` 里由 `Lab-uniq` 塌缩成 $\cong$, 这里直接是 $\cong$.

```agda
outsᴺ : Ordᶜ zero → (ℕ → Ordᶜ zero) → ℕ → Ordᶜ zero
outsᴺ O₀ O zero    = O₀
outsᴺ O₀ O (suc k) = O k

outsᴺ-HS : ∀ {O₀ O} → HS O₀ → (∀ k → HS (O k)) → ∀ n → HS (outsᴺ O₀ O n)
outsᴺ-HS h₀ h zero    = h₀
outsᴺ-HS h₀ h (suc k) = h k

outsᴺ-step : ∀ {O₀ O} → O₀ ⊑⁰ O 0 → (∀ k → O k ⊑⁰ O (suc k)) → ∀ n → outsᴺ O₀ O n ⊑⁰ outsᴺ O₀ O (suc n)
outsᴺ-step m₀ m zero    = m₀
outsᴺ-step m₀ m (suc k) = m k

outsᴺ-≅ : ∀ {O₀ O₀′ O O′} → O₀ ≅ O₀′ → (∀ k → O k ≅ O′ k) → ∀ n → outsᴺ O₀ O n ≅ outsᴺ O₀′ O′ n
outsᴺ-≅ e₀ e zero    = e₀
outsᴺ-≅ e₀ e (suc k) = e k
```


```agda
data Goodᴺ : Z → Set
forceᴺ    : (x : Z) → Goodᴺ x → Ordᶜ zero
forceᴺ-HS : (x : Z) (G : Goodᴺ x) → HS (forceᴺ x G)

data Goodᴺ where
  gz : Goodᴺ Z.zero
  gs : ∀ {x} → Goodᴺ x → Goodᴺ (Z.suc x)
  gl : ∀ {f : ℕ → Z} (G : ∀ n → Goodᴺ (f n)) →
       (∀ n → forceᴺ (f n) (G n) ⊑⁰ forceᴺ (f (suc n)) (G (suc n))) → Goodᴺ (Z.lim f)
  gc : ∀ {c t₀ o₀} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z}
       (ys : ℕ → Ordᶜ zero) (hy : ∀ m → HS (ys m)) (dy : ∀ m → c ⊑ᴵ toLevel (ys m) (hy m))
       (G₀ : Goodᴺ t₀) (l₀ : forceᴺ t₀ G₀ ≅ ys 0)
       (Gg : ∀ m → Goodᴺ (g (toLevel (ys m) (hy m)) (dy m)))
       (lE : ∀ m → forceᴺ _ (Gg m) ≅ ys (suc m))
       (Go₀ : Goodᴺ o₀) (Go : ∀ k → Goodᴺ (o (toLevel (ys k) (hy k)) (dy k))) →
       forceᴺ o₀ Go₀ ⊑⁰ forceᴺ _ (Go 0) →
       (∀ k → forceᴺ _ (Go k) ⊑⁰ forceᴺ _ (Go (suc k))) →
       Goodᴺ (ĉᴸ c t₀ g o₀ o)

forceᴺ Z.zero    gz        = zero
forceᴺ (Z.suc x) (gs G)    = suc (forceᴺ x G)
forceᴺ (Z.lim f) (gl G st) = lim (λ n → forceᴺ (f n) (G n))
forceᴺ (ĉᴸ c t₀ g o₀ o) (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = lim (outsᴺ (forceᴺ o₀ Go₀) (λ k → forceᴺ _ (Go k)))

forceᴺ-HS Z.zero    gz        = hz
forceᴺ-HS (Z.suc x) (gs G)    = hs (forceᴺ-HS x G)
forceᴺ-HS (Z.lim f) (gl G st) = hl (λ n → forceᴺ-HS (f n) (G n)) st
forceᴺ-HS (ĉᴸ c t₀ g o₀ o) (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) =
  hl (outsᴺ-HS (forceᴺ-HS o₀ Go₀) (λ k → forceᴺ-HS _ (Go k))) (outsᴺ-step mo₀ mo)
```


**读法.** 类型里只有 `Ordᴵ`、`Ordᶜ zero`、`HS`、$\sqsubseteq^\mathsf I$、$\cong$、$\sqsubseteq^0$, 全部来自 Level; `Z`/`ĉᴸ` 来自 Prefix (定义不涉及记号). `forceᴺ` 在 `gc` 处与 `forceᴸ` 同形: 第 0 项 $o_0$, 第 $k+1$ 项是 $o$ 在第 $k$ 个链点的层号处的值. 链点的计算方式在构造证书时体现: §4 的构造里 `ys (suc m)` 字面就取 `forceᴺ _ (Gg m)`, `lE` 是自反性, 所以计值确实是 "从第 0 点出发迭代分支", 预言只是让类型写得出来的名字.

**§1′ 余归纳的写法.** 下面是 (1) 的完整定义, 只为说明它可行; 本文其余部分用 `Goodᴺ`, 因为两个桥 (§3) 与无关性 (§2) 对它只要普通归纳, 而对 `Goodᶜ` 要余递归地造链 (`ofZ` 的 `gc` 情形变成 "对 `Goodᶻ` 递归 + 对链余递归" 的互递归, 支配字段还要在余递归里搬运 `ofZ-≅`). 从 `Goodᶜ` 到 `Goodᴺ` 是直接的 (取 `ys k = nthᶜ K k`), 反方向要把 `Gg m` 沿 `lE m` 的 $\cong$ 搬到字面的计值点上 (证书沿 `≅ᶻ` 的搬运, 未写).

```agda
data Goodᶜ : Z → Set
forceᶜ    : (x : Z) → Goodᶜ x → Ordᶜ zero
forceᶜ-HS : (x : Z) (G : Goodᶜ x) → HS (forceᶜ x G)
record Chainᶜ (c : Ordᴵ) (g : (η : Ordᴵ) → c ⊑ᴵ η → Z) (Y : Ordᶜ zero) (hY : HS Y) (e : c ⊑ᴵ toLevel Y hY) : Set
nthᶜ    : ∀ {c g Y hY e} → Chainᶜ c g Y hY e → ℕ → Ordᶜ zero
nthᶜ-HS : ∀ {c g Y hY e} (K : Chainᶜ c g Y hY e) n → HS (nthᶜ K n)

record Chainᶜ c g Y hY e where
  coinductive
  field
    G    : Goodᶜ (g (toLevel Y hY) e)
    d    : c ⊑ᴵ toLevel (forceᶜ _ G) (forceᶜ-HS _ G)
    next : Chainᶜ c g (forceᶜ _ G) (forceᶜ-HS _ G) d

data Goodᶜ where
  gzᶜ : Goodᶜ Z.zero
  gsᶜ : ∀ {x} → Goodᶜ x → Goodᶜ (Z.suc x)
  glᶜ : ∀ {f : ℕ → Z} (G : ∀ n → Goodᶜ (f n)) →
        (∀ n → forceᶜ (f n) (G n) ⊑⁰ forceᶜ (f (suc n)) (G (suc n))) → Goodᶜ (Z.lim f)
  gcᶜ : ∀ {c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} (G₀ : Goodᶜ t₀) (d₀ : c ⊑ᴵ toLevel (forceᶜ t₀ G₀) (forceᶜ-HS t₀ G₀)) →
        (K : Chainᶜ c g (forceᶜ t₀ G₀) (forceᶜ-HS t₀ G₀) d₀) →
        forceᶜ t₀ G₀ ⊑⁰ nthᶜ K 0 → (∀ k → nthᶜ K k ⊑⁰ nthᶜ K (suc k)) → Goodᶜ (ĉᴸ c t₀ g t₀ g)

nthᶜ K zero    = forceᶜ _ (Chainᶜ.G K)
nthᶜ K (suc k) = nthᶜ (Chainᶜ.next K) k

nthᶜ-HS K zero    = forceᶜ-HS _ (Chainᶜ.G K)
nthᶜ-HS K (suc k) = nthᶜ-HS (Chainᶜ.next K) k

forceᶜ Z.zero    gzᶜ        = zero
forceᶜ (Z.suc x) (gsᶜ G)    = suc (forceᶜ x G)
forceᶜ (Z.lim f) (glᶜ G st) = lim (λ n → forceᶜ (f n) (G n))
forceᶜ (ĉᴸ c t₀ g o₀ o) (gcᶜ G₀ d₀ K m₀ m) = lim (outsᴺ (forceᶜ t₀ G₀) (nthᶜ K))

forceᶜ-HS Z.zero    gzᶜ        = hz
forceᶜ-HS (Z.suc x) (gsᶜ G)    = hs (forceᶜ-HS x G)
forceᶜ-HS (Z.lim f) (glᶜ G st) = hl (λ n → forceᶜ-HS (f n) (G n)) st
forceᶜ-HS (ĉᴸ c t₀ g o₀ o) (gcᶜ G₀ d₀ K m₀ m) = hl (outsᴺ-HS (forceᶜ-HS t₀ G₀) (nthᶜ-HS K)) (outsᴺ-step m₀ m)
```

这里只写了输出即链的闭包 (`ĉᴸ c t₀ g t₀ g`, 即 `toZ (ŝ …)`); 一般的输出 $o$ 要在链里多带一个输出证书, 同形.


## §2 计值与证书无关

两个证书的预言序列逐点 $\cong$ (对 $m$ 归纳: 第 0 点经 `l₀`, 后继经 `lE` 与分支在 $\cong^\mathsf I$ 层号处的互模拟), 于是输出逐点 $\cong$. 递归调用写在传给 `ys-≅` 的 $\lambda$ 里 (`Gg m` 是 `gc` 的字段, 结构变小), 停机一次通过.

```agda
ys-≅ : ∀ {ys ys′ : ℕ → Ordᶜ zero} → ys 0 ≅ ys′ 0 → (∀ m → ys m ≅ ys′ m → ys (suc m) ≅ ys′ (suc m)) → ∀ m → ys m ≅ ys′ m
ys-≅ e₀ eS zero    = e₀
ys-≅ e₀ eS (suc m) = eS m (ys-≅ e₀ eS m)

forceᴺ-≅ : ∀ {x y} → x ≅ᶻ y → (G : Goodᴺ x) (G′ : Goodᴺ y) → forceᴺ x G ≅ forceᴺ y G′
forceᴺ-≅ zᶻ     gz gz = z≅
forceᴺ-≅ (sᶻ d) (gs G) (gs G′) = s≅ (forceᴺ-≅ d G G′)
forceᴺ-≅ (lᶻ h) (gl G _) (gl G′ _) = l≅ (λ n → forceᴺ-≅ (h n) (G n) (G′ n))
forceᴺ-≅ (ĉᶻ ec dt dg dp dO) (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) (gc ys′ hy′ dy′ G₀′ l₀′ Gg′ lE′ Go₀′ Go′ mo₀′ mo′) =
  l≅ (outsᴺ-≅ (forceᴺ-≅ dp Go₀ Go₀′)
              (λ k → forceᴺ-≅ (dO _ _ _ _ (toLevel-≅ (hy k) (hy′ k) (eY k))) (Go k) (Go′ k)))
  where
  eY : ∀ m → ys m ≅ ys′ m
  eY = ys-≅ (≅-trans (≅-sym l₀) (≅-trans (forceᴺ-≅ dt G₀ G₀′) l₀′))
            (λ m e → ≅-trans (≅-sym (lE m))
                     (≅-trans (forceᴺ-≅ (dg _ _ _ _ (toLevel-≅ (hy m) (hy′ m) e)) (Gg m) (Gg′ m)) (lE′ m)))
```

**读法.** `forceᴺ-≅` 是 "标签层只做验收" 在类型层面的形式: 同一棵符号树 (自互模拟) 的任意两个 `Goodᴺ` 证书计值出 $\cong$ 的树. 所以只要某一个证书的树带标签, 一切证书 (包括将来记号无关地造出的) 的树都带同一标签 (`Lab-≅`), 不需要对新证书重做任何标签证明.

## §3 桥: 从 Prefix 的证书与从 `Goodᴸ`

**`ofZ`.** Prefix 的 `Goodᶻ` 对一切 $\eta\sqsupseteq c$ 给分支证书并要求链单调 (`m₀`/`mE`); 限制到链点即得 `Goodᴺ`. 预言取 Symbolic 的链点 `Γᶜ` (其后继字面是 `E` 在上一点处的值, Symbolic 的 `Tᶜ-suc` 是 `refl`), 所以 `l₀`/`lE` 只是 `ofZ-≅`. 输出单调用 `Goodᶻ` 的 "一切 $\eta\sqsubseteq\eta'$" 字段在相邻链点处的实例, 链点层号单调由 `χᶜ-step` 与 `toLevel-⊑`. 不需要自互模拟.

```agda
ofZ   : ∀ {x} → Goodᶻ x → Goodᴺ x
ofZ-≅ : ∀ {x} (G : Goodᶻ x) → forceᴺ x (ofZ G) ≅ force x G

ofZ Goodᶻ.gz = gz
ofZ (Goodᶻ.gs G) = gs (ofZ G)
ofZ (Goodᶻ.gl G st) = gl (λ n → ofZ (G n))
  (λ n → ⊑-trans (≅→⊑ (ofZ-≅ (G n))) (⊑-trans (st n) (≅→⊑ (≅-sym (ofZ-≅ (G (suc n)))))))
ofZ {ĉᴸ c t₀ g o₀ o} (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) =
  gc (λ m → Pt.x (P m)) (λ m → Pt.hx (P m)) (λ m → Pt.dx (P m))
     (ofZ G₀) (ofZ-≅ G₀) (λ m → ofZ (Gg _ _)) (λ m → ofZ-≅ (Gg _ _))
     (ofZ Go₀) (λ k → ofZ (Go _ _))
     (⊑-trans (≅→⊑ (ofZ-≅ Go₀)) (⊑-trans (mo₀ _ _) (≅→⊑ (≅-sym (ofZ-≅ (Go _ _))))))
     (λ k → ⊑-trans (≅→⊑ (ofZ-≅ (Go _ _)))
            (⊑-trans (mo _ _ _ _ (toLevel-⊑ (Pt.hx (P k)) (Pt.hx (P (suc k))) (χᶜ-step C k)))
                     (≅→⊑ (≅-sym (ofZ-≅ (Go _ _))))))
  where
  C : Ctx
  C = record { c = c ; t₀ = force t₀ G₀ ; E = λ η e → force (g η e) (Gg η e)
             ; h₀ = force-HS t₀ G₀ ; hE = λ η e → force-HS (g η e) (Gg η e)
             ; d₀ = d₀ ; dE = dE ; m₀ = m₀ ; mE = mE }
  P : ℕ → Pt C
  P = Γᶜ C

ofZ-≅ Goodᶻ.gz = z≅
ofZ-≅ (Goodᶻ.gs G) = s≅ (ofZ-≅ G)
ofZ-≅ (Goodᶻ.gl G st) = l≅ (λ n → ofZ-≅ (G n))
ofZ-≅ (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) = l≅ eo
  where
  eo : ∀ n → _
  eo zero    = ofZ-≅ Go₀
  eo (suc k) = ofZ-≅ (Go _ _)
```

**`ofL`.** 遗忘标签: 预言取 `Goodᴸ` 的链点 `ptsᴸ`, 分支证书取它在链点处的值. 与 `ofZ` 同形; `ptsᴸ` 的后继子句字面是上一点处的计值, 所以 `lE` 仍是 `ofL-≅`.

```agda
ofL   : ∀ {x} → Goodᴸ x → Goodᴺ x
ofL-≅ : ∀ {x} (G : Goodᴸ x) → forceᴺ x (ofL G) ≅ forceᴸ x G

ofL GL.gz = gz
ofL (GL.gs G) = gs (ofL G)
ofL (GL.gl G st) = gl (λ n → ofL (G n))
  (λ n → ⊑-trans (≅→⊑ (ofL-≅ (G n))) (⊑-trans (st n) (≅→⊑ (≅-sym (ofL-≅ (G (suc n)))))))
ofL {ĉᴸ c t₀ g o₀ o} (GL.gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) =
  gc (λ m → Ptᴸ.x (P m)) (λ m → Ptᴸ.hx (P m)) (λ m → Ptᴸ.dx (P m))
     (ofL G₀) (ofL-≅ G₀) (λ m → ofL (Gm m)) (λ m → ofL-≅ (Gm m))
     (ofL Go₀) (λ k → ofL (Go k))
     (⊑-trans (≅→⊑ (ofL-≅ Go₀)) (⊑-trans mo₀ (≅→⊑ (≅-sym (ofL-≅ (Go 0))))))
     (λ k → ⊑-trans (≅→⊑ (ofL-≅ (Go k))) (⊑-trans (mo k) (≅→⊑ (≅-sym (ofL-≅ (Go (suc k)))))))
  where
  P : ∀ k → Ptᴸ c γ k
  P = ptsᴸ (forceᴸ t₀ G₀) (forceᴸ-HS t₀ G₀) l₀ d₀ (λ m Y hY lY e → forceᴸ _ (Gg m Y hY lY e))
           (λ m Y hY lY e → forceᴸ-HS _ (Gg m Y hY lY e)) lE dE
  Gm : ∀ m → Goodᴸ (g (lvᴸ (P m)) (Ptᴸ.dx (P m)))
  Gm m = Gg m (Ptᴸ.x (P m)) (Ptᴸ.hx (P m)) (Ptᴸ.lx (P m)) (Ptᴸ.dx (P m))

ofL-≅ GL.gz = z≅
ofL-≅ (GL.gs G) = s≅ (ofL-≅ G)
ofL-≅ (GL.gl G st) = l≅ (λ n → ofL-≅ (G n))
ofL-≅ (GL.gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) = l≅ eo
  where
  eo : ∀ n → _
  eo zero    = ofL-≅ Go₀
  eo (suc k) = ofL-≅ (Go k)
```

**读法.** 两个桥都只是遗忘: `ofZ` 忘掉 "非链点处的分支证书" 与链单调, `ofL` 忘掉标签. 反方向都不成立 (Omega2 §5: $t_2$ 的外层闭包在非链点 $\eta$ 处的分支里有不受支配的闭包, 所以 `toZ t2ˢ` 不大可能有 `Goodᶻ`; 而 `Goodᴺ` 的链点没有标签). `Goodᴺ` 是三者里最弱的, 恰好是 `forceᴺ` 用得到的那部分.

## §4 检验 (b) 与第 0 个链点: 记号无关的证书

下面四个证书都经 `ofZ` 从已有的 Prefix 证书得来, 而那些证书 (Stage2Label `GX₂`/`popGood`、Omega2Base `GX₃`、Omega2 `G₀ᵗ`) 的构造只用观测前序、`Strict₀`/`Strict₁`/`StrictN` 与 `Good-ψ1`/`Good-ψ0`, 不读任何记号项: **它们的可定义性与记号无关**. 记号只出现在本节的验收行 (`…-label`) 里. 验收用的模块单独导入:

```agda
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import OCF.Align.Symbolic using (σ1; X₂ᵗ; X₃ᵗ)
open import OCF.Align.Prefix using (Ωˢ)
open import OCF.Align.UniformS using (Ωˢ-refl; ψ1; ⊑ᴵ-≅ʳ)
import OCF.Align.NoCumsum as N
import OCF.Align.EBO as E
open E using (T; _<ᵀ_; []<; cmpᵀ; lt; natT; Ωt) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; Lab-≅)
open import OCF.Align.Stage2 using (Lab-uniq; γ′ᴱ; t2; ctx; ≺→⊑)
open import OCF.Align.StandardOmega using (γ′-NF; γ′-mono)
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.Stage2Label using (GX₂; X₂ᶠ; pop0≅; Lab-oc)
open import OCF.Align.Decouple using (X₂-label)
open import OCF.Align.Omega2Base using (GX₃; X₃ᶠ; X₃-label; popG; module Bound)
open import OCF.Align.Stage2Label using (X₃ˢ)
import OCF.Align.Omega2 as O2
open O2 using (t₀ᵗ; gᵗ; G₀ᵗ; dom1; lab-t₀)
open import OCF.Align.GoodL using (G2; T2ᴸ; T2-label; t2-refl; lab-gᴸ)
```

**$\psi_0(\Omega_\Omega)$ (任意环境、任意证据).** 弹栈闭包 `ψ1 p σ z 0`, 计值 $\cong$ `BTBOᴵ` (Stage2Label 的 `pop0≅`, 树侧). 工程注记: `BTBOᴺ-≅` 的类型若写成 `forceᴺ _ (GᴺBTBO p σ z) ≅ …`, 检查器为展开 `GᴺBTBO` 而把两边化到弱头范式, 在 300 s 内不结束 (二分定位, 临时文件); 直接写 `ofZ (popG p σ z)` 一秒内通过.

```agda
GᴺBTBO : ∀ {L k} (p : zero <ᴵ L) (σ : Simᴵ k L) (z : zero <ᴵ L) → Goodᴺ (toZ (ψ1 p σ z Ord₊ˢ.zero))
GᴺBTBO p σ z = ofZ (popG p σ z)

BTBOᴺ-≅ : ∀ {L k} (p : zero <ᴵ L) (σ : Simᴵ k L) (z : zero <ᴵ L) →
          forceᴺ (toZ (ψ1 p σ z Ord₊ˢ.zero)) (ofZ (popG p σ z)) ≅ N.BTBOᴵ
BTBOᴺ-≅ p σ z = ≅-trans (ofZ-≅ (popG p σ z)) (pop0≅ p σ z (popG p σ z))
```

**检验 (b): $X_2=\psi_0(\Omega_\Omega+\Omega_2)$.** 这是 Prefix 的检验 2 最初失败的项 (Prefix §7: 缺 `Goodᶻ (toZ X₂ˢ)`, 第一个缺的是 $A=X_2[1][0][1]$ 的闭包). 证书 `GᴺX₂`, 计值 $\cong$ Stage2Label 的 `X₂ᶠ`, 标签是验收. 同法 $X_3=\psi_0(\Omega_\Omega+\Omega_3)$.

```agda
GᴺX₂ : Goodᴺ (toZ X₂ˢ)
GᴺX₂ = ofZ GX₂

X₂ᴺ-≅ : forceᴺ _ GᴺX₂ ≅ X₂ᶠ
X₂ᴺ-≅ = ofZ-≅ GX₂

X₂ᴺ-label : Lab (forceᴺ _ GᴺX₂) X₂ᵗ
X₂ᴺ-label = Lab-≅ X₂ᴺ-≅ X₂-label

GᴺX₃ : Goodᴺ (toZ X₃ˢ)
GᴺX₃ = ofZ GX₃

X₃ᴺ-label : Lab (forceᴺ _ GᴺX₃) X₃ᵗ
X₃ᴺ-label = Lab-≅ (ofZ-≅ GX₃) X₃-label
```

**$t_2$ 的第 0 个链点 $\gamma'_1=\psi_0(\Omega_\Omega+\Omega_1)$.** 证书 `ofZ G₀ᵗ`, 支配 $1\sqsubseteq^\mathsf I$ 层号由 Omega2 的 `dom1` (即 Stage2Label 的 `Strict₁`, 观测证明) 沿 `ofZ-≅` 搬过来. 这三项都不读记号.

```agda
G₀ᴺ : Goodᴺ (toZ t₀ᵗ)
G₀ᴺ = ofZ G₀ᵗ

χ₀ : Ordᶜ zero
χ₀ = forceᴺ _ G₀ᴺ

hχ₀ : HS χ₀
hχ₀ = forceᴺ-HS _ G₀ᴺ

dχ₀ : suc zero ⊑ᴵ toLevel χ₀ hχ₀
dχ₀ = ⊑ᴵ-≅ʳ (dom1 {p = zero} {σ = σ1 zero} {z = zero} (Ωˢ-refl (suc zero)) G₀ᵗ)
            (toLevel-≅ (force-HS _ G₀ᵗ) hχ₀ (≅-sym (ofZ-≅ G₀ᵗ)))

χ₀-label : Lab χ₀ (γ′ᴱ 1)
χ₀-label = Lab-≅ (ofZ-≅ G₀ᵗ) (lab-t₀ G₀ᵗ)
```

## §5 检验 (a): $t_2=\psi_0(\Omega_\Omega\cdot2)$

**验收层.** 由 `forceᴺ-≅` 与一个经标签的证书 `ofL G2`, 任意 `Goodᴺ` 证书 (不论怎么造的) 的计值树都 $\cong$ GoodL 的 `T2ᴸ`, 并带标签 $t_2$. 这就是 "记号只作验收尺" 的形式: 新证书不需要任何新的标签证明.

```agda
any-T2 : (G : Goodᴺ (toZ t2ˢ)) → forceᴺ _ G ≅ T2ᴸ
any-T2 G = ≅-trans (forceᴺ-≅ (toZ-≅ t2-refl) G (ofL G2)) (ofL-≅ G2)

any-T2-label : (G : Goodᴺ (toZ t2ˢ)) → Lab (forceᴺ _ G) t2
any-T2-label G = Lab-≅ (any-T2 G) T2-label
```

**记号无关的链骨架.** `t2ˢ` 字面是第 0 层闭包 `ŝ 1 t₀ᵗ gᵗ` (Omega2 §1), `toZ` 后输出就是链本身. 下面的 `Gᴺ₂-of` 把一个链点 oracle 变成 `Goodᴺ (toZ t2ˢ)`. oracle 的类型 `NextN` 不含记号: 一个对链指标与树的**任意**不变量 `Inv` (记号无关的实例要由使用者给出), 第 0 点满足它, 且对满足它的点 $Y$ 给出下一个计值点 $\psi^{[\hat\Omega]}_0(\Omega_{\mathtt{lvl}\,Y})$ 的 `Goodᴺ` 证书、不变量、支配与单调. 骨架本身 (预言序列、`lE` 取自反、输出即链) 不读 `Inv` 的内容.

```agda
record NextN : Set₁ where
  field
    Inv  : ℕ → Ordᶜ zero → Set
    inv₀ : Inv 0 χ₀
    step : ∀ k Y (hY : HS Y) (e : suc zero ⊑ᴵ toLevel Y hY) → Inv k Y →
           Σ (Goodᴺ (toZ (gᵗ (toLevel Y hY) e))) λ G →
             Inv (suc k) (forceᴺ _ G) × Σ (suc zero ⊑ᴵ toLevel (forceᴺ _ G) (forceᴺ-HS _ G)) λ _ → Y ⊑⁰ forceᴺ _ G

record Pkᴺ (Iv : ℕ → Ordᶜ zero → Set) (k : ℕ) : Set where
  constructor pkᴺ
  field
    Y  : Ordᶜ zero
    hY : HS Y
    dY : suc zero ⊑ᴵ toLevel Y hY
    iY : Iv k Y

module ChainN (X : NextN) where
  open NextN X
  open Pkᴺ

  nx : ∀ k (P : Pkᴺ Inv k) → _
  nx k P = step k (Y P) (hY P) (dY P) (iY P)

  pk : ∀ k → Pkᴺ Inv k
  pk zero    = pkᴺ χ₀ hχ₀ dχ₀ inv₀
  pk (suc k) = pkᴺ (forceᴺ _ (proj₁ (nx k (pk k)))) (forceᴺ-HS _ _) (proj₁ (proj₂ (proj₂ (nx k (pk k)))))
                   (proj₁ (proj₂ (nx k (pk k))))

  Gk : ∀ k → Goodᴺ (toZ (gᵗ (toLevel (Y (pk k)) (hY (pk k))) (dY (pk k))))
  Gk k = proj₁ (nx k (pk k))

  mk : ∀ k → Y (pk k) ⊑⁰ forceᴺ _ (Gk k)
  mk k = proj₂ (proj₂ (proj₂ (nx k (pk k))))

  Gᴺ₂ : Goodᴺ (toZ t2ˢ)
  Gᴺ₂ = gc (λ k → Y (pk k)) (λ k → hY (pk k)) (λ k → dY (pk k))
           G₀ᴺ (≅-refl⁰ _) Gk (λ k → ≅-refl⁰ _)
           G₀ᴺ Gk (mk 0) (λ k → mk (suc k))

  Gᴺ₂-T2 : forceᴺ _ Gᴺ₂ ≅ T2ᴸ
  Gᴺ₂-T2 = any-T2 Gᴺ₂

Gᴺ₂-of : NextN → Goodᴺ (toZ t2ˢ)
Gᴺ₂-of X = ChainN.Gᴺ₂ X
```

**读法.** 外层闭包的困难 (Omega2 §5: Prefix 的 `gc` 要求**一切** $\eta\sqsupseteq1$ 处的分支证书, 非链点处弹出不受支配的闭包, 全局界 `no-Bound`) 在这里**完全消失**: `Gᴺ₂-of` 只在链点处要证书. 剩下的只有 `NextN`. 它是可满足的 (下面的 `labelNext`, 不变量取 "带标签 $\gamma'_{k+1}$"), 但那个实例经标签: 证书来自 GoodL 的 `lab-gᴸ` (经 `ofL`), 支配来自 `one⊑lab`, 单调来自 `Lab-oc` + `γ′-mono`. 这把记号依赖**精确定位**到 `NextN.step` 的三个分量.

```agda
labelNext : NextN
labelNext = record
  { Inv  = λ k Y → Lab Y (γ′ᴱ (suc k))
  ; inv₀ = χ₀-label
  ; step = λ k Y hY e lY →
      let L = lab-gᴸ k Y hY lY e
          G = ofL (proj₁ L)
          l : Lab (forceᴺ _ G) (γ′ᴱ (suc (suc k)))
          l = Lab-≅ (ofL-≅ (proj₁ L)) (proj₂ L)
      in G , l , GL.one⊑lab (forceᴺ-HS _ G) l (γ′-NF (suc (suc k))) []<
           , ≺→⊑ (Lab-oc l (γ′-NF (suc (suc k))) lY (γ′-NF (suc k)) (γ′-mono (suc k)))
  }

Gᴸᴺ₂ : Goodᴺ (toZ t2ˢ)
Gᴸᴺ₂ = Gᴺ₂-of labelNext
```

## §6 支配: 缺的是什么

`NextN.step` 的三个分量里, 支配 ($1\sqsubseteq^\mathsf I$ 层号) 与单调 ($Y\sqsubseteq^0$ 下一点) 在**有** Prefix 证书时都是记号无关的: Stage2Label 的 `Strict₁` 与观测前序的 `ψ1-cong (Ω-monoᵒ …)` (Omega2 `G₀ᵗ`/`dom1` 就是这样做的). 所以 $k=0$ 的真正缺口只是证书: $\gamma'_2$ 的计值树 `gᵗ (lvl χ₀) dχ₀` 的记号无关证书, 而这棵树内部有大量闭包 (Omega2 §4 的 `first-wall`: 目标 BTBO, 界 $\mathtt{lvl}\,\mathrm{BTBO}+1$; `second-wall`: 目标 BTBO$+1$), 每个都要支配字段. 下面三条编译过的事实说明这些支配不能从已有的记号无关工具得到.

**只差证书 ($k=0$ 的形式).** 给定 $\gamma'_2$ 的计值树的任意 Prefix 证书, `NextN.step 0` 在 $\chi_0$ 处的三个分量都记号无关地得出: 证书经 `ofZ`, 支配经 `dom1`, 单调经观测前序 (`ψ1-cong (Ω-monoᵒ dχ₀)` 在恒等观测下比较 $\psi^{[\hat\Omega]}_0(\Omega_1)$ 与 $\psi^{[\hat\Omega]}_0(\Omega_{\mathtt{lvl}\,\chi_0})$). 对一般的 $k$ 同形 (不变量取 "是上一个 Prefix 证书的计值且层号单调"), 这里只编译 $k=0$:

```agda
open import OCF.Align.UniformS using (ψ1-cong; Ω-monoᵒ; idO)
open import OCF.Align.Symbolic using (Mlev)

step₀ : (G : Goodᶻ (toZ (gᵗ (toLevel χ₀ hχ₀) dχ₀))) →
        Σ (Goodᴺ (toZ (gᵗ (toLevel χ₀ hχ₀) dχ₀))) λ G′ →
          Σ (suc zero ⊑ᴵ toLevel (forceᴺ _ G′) (forceᴺ-HS _ G′)) λ _ → χ₀ ⊑⁰ forceᴺ _ G′
step₀ G = ofZ G
        , ⊑ᴵ-≅ʳ (dom1 {L = Mlev (suc zero) (toLevel χ₀ hχ₀) dχ₀} {k = toLevel χ₀ hχ₀} {p = lim 0 zero} {σ = λ q → lim 1 q}
                      {z = lim 0 zero} {y = Ωˢ (toLevel χ₀ hχ₀)} (Ωˢ-refl (toLevel χ₀ hχ₀)) G)
                (toLevel-≅ (force-HS _ G) (forceᴺ-HS _ (ofZ G)) (≅-sym (ofZ-≅ G)))
        , ⊑-trans (≅→⊑ (ofZ-≅ G₀ᵗ)) (⊑-trans (mono idO G₀ᵗ G) (≅→⊑ (≅-sym (ofZ-≅ G))))
  where
  mono = ψ1-cong {ℓ = suc zero} {ℓ′ = Mlev (suc zero) (toLevel χ₀ hχ₀) dχ₀}
                 {p = zero} {p′ = lim 0 zero} {σ = σ1 zero} {σ′ = λ q → lim 1 q} {z = zero} {z′ = lim 0 zero}
                 {x = Ωˢ (suc zero)} {y = Ωˢ (toLevel χ₀ hχ₀)} (Ω-monoᵒ dχ₀)
```

所以 (a) 的缺口精确地是: **`Goodᶻ (toZ (gᵗ (toLevel χ₀ hχ₀) dχ₀))` 的记号无关构造** (以及沿链的同类陈述). 注意这里要的是 Prefix 的 "一切 $\eta$" 证书, 但只对**链点处的分支树** $\gamma'_{k+2}$, 不对 `t2ˢ` 本身: 后者的分支在任意 $\eta$ 处计值, 前者内部闭包的分支只在 $\gamma'_{k+2}$ 的子层号范围内弹栈 (闭包在目标 $j$ 处弹出后栈已空, 分支 $\psi^{[]}_j(\Omega_{\eta'})$ 不再弹栈, 外层 $\psi^{[\hat\Omega]}$ 只在层号 $\preceq j$ 处折叠它), 所以不受 Omega2 §5 的 "无标签 $\eta$" 问题影响; 问题只剩支配字段.

**(i) 全局界不行 (Omega2 `no-Bound`).** 对 $\gamma'_2$ 的环境层号之上的一切 $\beta$, Omega2Base 的 `Strictᵝ β` 为假. 这里只是把它对 `G₀ᵗ` 实例化:

```agda
open import Data.List using ([]; _∷_)
open import OCF.Align.Value using (_≼_; s≼s; ≼l; ≼-refl; ≼-trans; s≼s⁻; s≼0; ≼lim⁻; ≺→s≼; shift≈)
open import OCF.Align.SystemOmega using (Occ; oh; od; ot)

bound-closed : (e : suc zero ⊑ᴵ toLevel (force _ G₀ᵗ) (force-HS _ G₀ᵗ)) →
               ∀ β → Mlev (suc zero) (toLevel (force _ G₀ᵗ) (force-HS _ G₀ᵗ)) e ⊑ᴵ β → ¬ Bound.Strictᵝ β
bound-closed = O2.no-Bound G₀ᵗ
```

**(ii) 值序不行: 不动点处严格增长为假.** "下一个链点严格高于上一个" 的全局形式是 $x\prec\psi(\Omega_{\mathtt{lvl}\,x})$. 用 Value 的 `shift≈` ($\psi^0(\Omega_{\mathrm{BTBO}^\mathsf L})\approx^\mathsf v\mathrm{BTBO}$) 与值序的反自反 (`s⋠`, 对第 0 层的树归纳), 它在 $x=\mathrm{BTBO}$ 处为假, 即使只要求值的严格 (`≺→s≼`). 所以严格性只能 "在不动点之下" 成立, 是相对于链的, 不是 $\psi$ 的性质; $\preccurlyeq$ 本身也只给非严格比较, 而 `toLevel` 吃的是结构的 $\sqsubseteq^\mathsf I$ (Value §4: 值序不进入任何定义).

```agda
s⋠ : (a : Ordᶜ zero) → ¬ (suc a ≼ a)
s⋠ zero    p = s≼0 p
s⋠ (suc a) p = s⋠ a (s≼s⁻ p)
s⋠ (lim f) p with ≼lim⁻ p
... | n , q = s⋠ (f n) (≼-trans (s≼s (≼l n (≼-refl (f n)))) q)
s⋠ (limᵢ () f) p
s⋠ (up () x) p

fix-not-strict : ¬ (N.BTBOᴵ ≺ ψ⁰ (Ω N.BTBOᴸ))
fix-not-strict h = s⋠ N.BTBOᴵ (≼-trans (≺→s≼ h) (proj₁ shift≈))
```

**(iii) 观测前序不行: 上下文会把闭包压到它的目标之下.** 观测前序 $\sqsubseteq^\mathsf o$ 对一切相似的观测栈量化, 所以 "闭包的第 0 点 $\sqsupseteq^\mathsf o\Omega_w$" 只能推出 "链点 $\sqsupseteq\psi^{[\hat\Omega]}_0(C[\Omega_w])$", 而 $C$ 可以经过目标低于 $w$ 的 $\psi_j$. 记号侧的例子 (`refl`): $A=\psi_0(\Omega_\Omega+\psi_1(\Omega_\Omega+\Omega_{\gamma'_2}))$ 里出现下标 $\gamma'_2$ (`dip-occ`), 但 $A<\gamma'_2$ (`dip`). 树侧的 $\psi^{[\hat\Omega]}_0(\psi^{[\hat\Omega]}_1(\Omega_{\mathtt{lvl}\,\gamma'_2}))$ 有定义 (环境层号取 $\mathtt{lvl}\,\gamma'_2+1$ 以上即可), 它在目标 $1$ 处折叠 $\Omega_{\gamma'_2}$ 时沿 $\gamma'_2$ 的子层号逐个弹栈, 产生界直到 $\gamma'_2$ 附近的闭包, 而这些闭包的链点都 $\le A<\gamma'_2$: **支配为假, 这棵树没有任何 `Goodᴺ` 证书** (按值对应, 纸面). 所以任何 "对一切好尾巴封闭" 的记号无关闭包定理都必须排除这样的尾巴, 排除的条件是 "尾巴里出现的层号小于它自己被 $\psi^{[\hat\Omega]}_0$ 折叠后的值", 即标准形的 $G$-条件; `occ<` (SystemOmega) 是它在记号侧的形式, GoodLBase 的 `domᴸ` 正是经 `occ<` + `Lab-oc` 得到支配的.

```agda
A-dip : T
A-dip = ctx (ψᵗ (natT 1) (ΩΩ ∷ Ωt (γ′ᴱ 2)) ∷ [])

dip : cmpᵀ A-dip (γ′ᴱ 2) ≡ lt
dip = refl

dip-occ : Occ (γ′ᴱ 2) A-dip
dip-occ = od (ot (od (ot oh)))
```

**读法.** (i)–(iii) 合起来: 支配既不是全局的 (i), 也不是 $\psi$ 的单调/增长性质 (ii), 也不能只看闭包自己与观测上下文 (iii); 它是**出现性**的: 闭包的目标 $w$ 必须作为层号 "出现" 在最终链点的计值树里, 并且计值树的值大于其中出现的一切层号. 在可达的树上这是真的 (标签路线证明了 $t_2$ 的每个链点里每个闭包都被支配, GoodLBase `domᴸ`), 所以缺口是**证明技术**的, 不是数学的: 需要一个树侧的标准形谓词 (SystemOmega 的 `Bnd₁`/`occ<` 搬到树上: "尾巴里出现的层号 $\prec$ 它的 $\psi^{[\hat\Omega]}_0$-折叠的层号", 对子树遗传), 证明它沿折叠与沿 $t_2$ 的链保持, 再把 Omega2Base 的 `Bound β` (全局 `Strictᵝ`) 换成 "带地板" 的版本, 在 `Dom-ψ1` 处用这个谓词代替 `Sβ`.

## §7 检验 (c) 与统一形的树

**(c) $\psi_0(\Omega_\Omega\cdot\Omega_2)$, 以及统一形上的 $t_2$.** Uniform2 的标签定理在统一折叠的树上造出 `Goodᴸ` 证书; 经 `ofL` 它们都是 `Goodᴺ` 证书, 所以 `Goodᴺ` 在统一形的这些树上有居留. 但构造经过标签 (Uniform2 的 `label` 对 `Rep` 的推导递归), 不是纲领要的答案. 统一折叠 (Uniform2Base 的前缀塔、`bound`、`cloA`、`repA`) 上**没有**任何记号无关的好性理论 (观测前序只移植到了 Prefix 的 `ψᴾ`, 栈 `[]` 与 `[Ω̂]`), 所以在统一形上连 (b) 也只有经标签的居留; 记号无关的 `GᴺX₂` 在 Prefix 的树上, 它与统一形的树计值 $\cong$ (`X₂-uniform`, 验收: 同一标签).

```agda
open import OCF.Align.Uniform2Base using (ψᵀ; Ψ; tlᵀ; flo; cvFlo; _⊕_)
open import OCF.Align.Uniform2 using (Ω̂ᵀ; T2-label′; TΩ₂-label′; pΩ₂-label)
open import OCF.Align.UniformS using (two)

GᴸᴺT2ᵀ : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψᵀ (Ω̂ᵀ ⊕ Ω̂ᵀ) ev z))
GᴸᴺT2ᵀ ev z = ofL (proj₁ (T2-label′ ev z))

GᴸᴺTΩ₂ : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψᵀ (Ψ (tlᵀ (flo two) (cvFlo two) (Ωˢ two))) ev z))
GᴸᴺTΩ₂ ev z = ofL (proj₁ (TΩ₂-label′ ev z))

X₂-uniform : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → forceᴺ _ GᴺX₂ ≅ forceᴸ _ (proj₁ (pΩ₂-label ev z))
X₂-uniform ev z = Lab-uniq X₂ᴺ-label (proj₂ (pΩ₂-label ev z))
```

## §8 对比表: 标签式与记号无关

| | 标签式 (`Goodᴸ`, GoodLBase 起) | 记号无关 (`Goodᴺ`, 本文) |
|---|---|---|
| 可容许的计值点 | 带标签 $\gamma_m$ 的一切树的层号 ($\gamma:\mathbb N\to T$ 是字段) | 闭包自己的链点 (预言 `ys`, 由 `l₀`/`lE` 钉成链, 模 $\cong$) |
| 类型里出现的记号 | `T`, `Lab` | 无 |
| 计值 | `forceᴸ`: 链点处的输出 | `forceᴺ`: 同形; 两者经 `ofL-≅` 一致 |
| 计值与证书无关 | `forceᴸ-≅` (链点经 `Lab-uniq`) | `forceᴺ-≅` (链点经对 $m$ 归纳) |
| 链单调 | 不要求 (输出相邻单调) | 同左 |
| 输出单调 | `mono-lab` (`Lab-oc` + `fs-mono₁`) | 字段; 有 Prefix 证书时由观测前序 (`ofZ`) |
| 支配 | `domᴸ` (`occ<` + `Lab-oc`) | 字段; 有 Prefix 证书时由 `Strict₁`/`StrictN`/`Strict-BTBO` |
| $\psi_0(\Omega_\Omega)$, $\gamma'_1$, $X_2$, $X_3$ | 定理 | **定理, 记号无关** (`GᴺBTBO`, `G₀ᴺ`, `GᴺX₂`, `GᴺX₃`) |
| $t_2$ 外层闭包 | `G2` (GoodL) | **骨架记号无关** (`Gᴺ₂-of`), 只差链点 oracle `NextN` |
| $t_2$ 的链点 $\gamma'_{k+2}$ ($k\ge0$) | `lab-gᴸ` | **未得**; 经标签的实例 `labelNext` |
| $\psi_0(\Omega_\Omega\cdot k)$, $\cdot\omega$, $\cdot\Omega_2$ … | Uniform2 九条校准 | 只有经标签的居留 (`ofL`) |
| 标签层 | 与证书由同一递归造出 (层 3 与层 4 合并) | 纯验收: `forceᴺ-≅` + 一个带标签的证书 (`any-T2-label`) |

## §9 结论与边界

**定义 (记号无关, 已编译).** `Goodᴺ`/`forceᴺ`/`forceᴺ-HS` (§1): `gc` 的可容许点是闭包自己的链点, 以树序列 `ys` 为名, 约束 `l₀ : forceᴺ t₀ G₀ ≅ ys 0`、`lE m : forceᴺ _ (Gg m) ≅ ys (suc m)`; 分支与输出证书只在 `ys m` 的层号处给出; 支配 `dy m` 与输出单调是字段. 在 `Set` 里, 正性与停机一次通过. "可达点" 作为字段谓词写不出来 (要提到正在定义的字段); 链在类型内部字面迭代的写法用余归纳记录可行 (§1′ `Goodᶜ`/`Chainᶜ`, 计值对 `Z` 结构递归, 已编译), 预言序列是它的归纳式替身, 构造时 `ys (suc m)` 字面取 `forceᴺ _ (Gg m)` (`ChainN.pk`), 所以计值仍是 "从第 0 点迭代分支". 两种写法对本文的结论没有区别: 缺口在内部闭包的支配, 不在可容许点的表述.

**定理 (已编译).**

1. `forceᴺ-≅`: 计值与证书无关 (模 $\cong$).
2. `ofZ`/`ofZ-≅`, `ofL`/`ofL-≅`: Prefix 证书与 `Goodᴸ` 证书都遗忘为 `Goodᴺ`, 计值不变.
3. 记号无关的证书: `GᴺBTBO` (任意环境, `BTBOᴺ-≅`), `G₀ᴺ` ($\gamma'_1$, 支配 `dχ₀`), **`GᴺX₂` (检验 b)**, `GᴺX₃`; 验收 `X₂ᴺ-label`, `X₃ᴺ-label`, `χ₀-label`, `X₂-uniform`.
4. $t_2$: `any-T2`/`any-T2-label` (任意 `Goodᴺ` 证书 $\cong$ `T2ᴸ` 且带标签 $t_2$); `NextN`/`ChainN`/`Gᴺ₂-of` (记号无关的骨架: 外层闭包只要链点处的证书); `labelNext` (经标签的 oracle 实例), `Gᴸᴺ₂ = Gᴺ₂-of labelNext`; `step₀` (只要 $\gamma'_2$ 的计值树有 Prefix 证书, `NextN.step 0` 的支配与单调都记号无关地得出: `Strict₁`, `ψ1-cong (Ω-monoᵒ …)`).
5. 余归纳写法 `Goodᶜ`/`Chainᶜ`/`forceᶜ`/`nthᶜ` (§1′): 链在类型里字面迭代, 也通过正性与停机检查.
6. (c) 与统一形: `GᴸᴺT2ᵀ`, `GᴸᴺTΩ₂` (经标签).
7. 否定与侦察: `bound-closed` (全局界, 即 Omega2 `no-Bound`), `s⋠`/`fix-not-strict` (BTBO 处 $x\prec\psi^0(\Omega_{\mathtt{lvl}\,x})$ 为假, 连值的严格也不成立), `dip`/`dip-occ` (记号侧: 出现下标 $\gamma'_2$ 的项 $\psi_0(\Omega_\Omega+\psi_1(\Omega_\Omega+\Omega_{\gamma'_2}))<\gamma'_2$, `refl`).

**三个检验.**

- **(b) $\psi_0(\Omega_\Omega+\Omega_2)$: 通过 (Prefix 的树), 模 $\cong$ 与标签树一致** (`X₂ᴺ-≅` 到 `X₂ᶠ` 是 $\cong$; `X₂ᶠ` 本身就是 Prefix 证书的计值, 所以与 Decouple 的标签树字面同一; 与统一形的树 $\cong$ 经验收 `X₂-uniform`). 统一形上的记号无关证书没有, 因为统一折叠上没有记号无关的好性理论.
- **(a) $\psi_0(\Omega_\Omega\cdot2)$: 未通过.** 停点: 链指标 $k=1$, 即 `NextN.step 0 χ₀ hχ₀ dχ₀ _` 的证书分量, 项 $\gamma'_2=\psi_0(\Omega_\Omega+\Omega_{\gamma'_1})$, 符号树 `gᵗ (toLevel χ₀ hχ₀) dχ₀` (Omega2 的 `CertOracle 0` 的记号无关版). 外层闭包已无障碍 (`Gᴺ₂-of`); 第 0 点与它的支配记号无关 (`G₀ᴺ`, `dχ₀`). 缺的引理: $\gamma'_2$ 的计值树**内部**闭包的支配 (第一处: Omega2 `first-wall`, $t_2$ 沿 `1 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 1 ∷ 1`, 目标 BTBO, 界 $\mathtt{lvl}\,\mathrm{BTBO}+1$; 下一处 `second-wall`, 目标 BTBO$+1$). 一旦这些树有 Prefix 证书, `NextN` 的支配与单调分量都由已有的记号无关引理给出 (`Strict₁`, 观测前序), 所以缺口**只有一条**: 一个 "带地板" 的闭包定理, 其中 Omega2Base 的全局 `Strictᵝ β` 换成树侧的出现性 (标准形) 谓词.
- **(c) $\psi_0(\Omega_\Omega\cdot\Omega_2)$: 未通过** (只有经标签的居留 `GᴸᴺTΩ₂`); 它在 (a) 之后, 且还需要统一折叠上的记号无关理论.

**失败的性质: 证明技术, 不是数学.** 每个在 $t_2$ 的链点里出现的闭包都被支配 (标签路线的 `domᴸ` 是定理), 所以没有假命题挡路. 但支配不能从已有的记号无关工具推出: (i) 全局界在 BTBO 处到头 (`bound-closed`); (ii) 严格增长不是 $\psi$ 的性质, 在不动点处为假 (`fix-not-strict`), 值序 `≼` 也给不出 (它只给非严格比较, 且不进入 `toLevel`); (iii) 观测前序对上下文是盲的: 闭包在被 $\psi^{[\hat\Omega]}_0$ 计值之前可能被目标更低的 $\psi_j$ 映射, $\sqsubseteq^\mathsf o$ 只给链点 $\succ j$, 而目标 $w>j$; 一般的 "好尾巴" 里甚至有支配为假的树 (`dip`: 出现下标 $\gamma'_2$ 而值 $<\gamma'_2$). 所以记号无关的闭包定理必须把尾巴限制在 "出现的层号小于它自己的折叠值" 的类里, 即**树侧的标准形**, 这正是 `occ<` (SystemOmega) 与 `NF₁` 的 $G$-条件在树上的对应物.

**代价估计 (纸面).** 恢复纲领要求 EBO 阶段的层 3 (证书) 重新独立于层 4 (标签):

| 部分 | 依据 | 估计 (代码行) |
|---|---|---|
| `Goodᴺ` + 无关性 + 两个桥 | 本文 §1–§3 | ≈150 (已完成) |
| 观测前序移植到统一折叠 (前缀塔、`bound`、`cloA`、`repA`、深度 $d$) | UniformS 920 行代码 (只有 `ψᴾ` 的栈 `[]`/`[Ω̂]`) | 1500–2500 |
| 树侧标准形谓词与 `occ<` 的树版, 沿折叠与沿链保持 | StandardOmega 943 + SystemOmega 195 行代码的相应部分 | 800–1200 |
| 带地板的闭包定理 (`Bound` 的 `Dom-ψ1` 用标准形谓词代替 `Strictᵝ`), 链上的严格增长 | Omega2Base §1–§3 + Stage2Label §3–§5 (531 行代码) | 500–800 |
| 每个阶段的实例 ($t_2$, $\cdot k$, $\cdot\omega^\eta$, $\cdot\Omega_2$, …) | 本文 §5 的骨架 | 每个 30–80 |
| 标签层 | 现有的统一 ≈1010 行原样保留, 经 `ofL` + `forceᴺ-≅` 验收 | +30 |

合计层 3 约 3000–4500 行, 相对现在合并的 ≈1010 行 (层 3 与层 4 一起) 是 3–4 倍; 标签层不变, 变成纯验收 (与 BTBO 阶段 `Uniform` + `Label` 的分工相同). 风险集中在第三行: 树侧标准形要对**树** (不是记号项) 陈述 "出现的层号 $\prec$ 折叠值", 而折叠值要证书才算得出, 所以谓词与证书要沿链交错归纳 (Omega2 `Chain` 的良基序列的记号无关版).

**边界.**

- 只导入已有模块, 不改任何已有文件; README 未改. 所有 `Goodᴺ` 证书都在 Prefix 的 `Z` 上 (统一折叠的输出也是 `Z`, 所以 `GᴸᴺT2ᵀ` 等同一类型).
- "记号无关" 指证明项与类型不引用 `T`/`Lab`; 被引用的 Prefix 证书 (`GX₂`, `GX₃`, `popG`, `G₀ᵗ`) 所在模块导入了记号模块, 但这些定义本身只用观测前序与树侧严格性引理.
- §6 (iii) 中 "该树没有 `Goodᴺ` 证书" 是按值对应的纸面论证; 编译的只是记号侧的 `dip`/`dip-occ`.
- 工程注记: `step₀` 里 `dom1` 与 `ψ1-cong` 的隐式参数 (`L`/`k`/`p`/`σ`/`z`/`y`, 以及 `ℓ`/`ℓ′`/`x`/`y`) 不写时报 `[UnsolvedConstraints] ψᴾ 1 (lim 0 zero) (lim 1) (fΩ̂ (lim 0 zero) ∷ []) (Ωˢ (_f_1115 1)) = Ord₊ˢ.lim (λ m → …)`: 检查器把 `χ₀` 的层号化开成 `lim`, 再去猜 `Ωˢ ?` 的参数; 写出即过 (README 记的 "折叠引理的隐式参数要写出" 的又一例). 定义成别名的证书在等式类型里出现 (`forceᴺ _ (GᴺBTBO p σ z)`) 会让检查器为展开别名把两边化到弱头范式, 超过 300 s; 类型里直接写 `ofZ (popG p σ z)` 即过. `ofL-≅` 的 `gc` 情形不能用 `outsᴺ-≅` (两边的输出列一个是 `outsᴺ`, 一个是 GoodLBase 的 `outsᴸ`), 改为逐项.
