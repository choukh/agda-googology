# 内层对应: 可数下标的 EBO 片段与证据模 ≅ 的树族

> 接 [Level](Level.lagda.md), [Uniform](Uniform.lagda.md), [Diagonal](Diagonal.lagda.md), [NoCumsum](NoCumsum.lagda.md) 与参照记号 [EBO](EBO.lagda.md). NoCumsum 给出了闭合、带证书、无 `cumsum` 的 `BTBOᴵ`, 它的外层基本列与 EBO 的 $\psi_0(\Omega_\Omega)$ 的规则 6 链同形 (`refl`), 但标签 $\psi_0(\Omega_\Omega)$ 仍是估计: 每个 $\gamma_k$ 的内部与 EBO 的 $\gamma_k$ 的基本列一致没有证. 依 [probes/README](../../README.md), 标签只有在 "树的 FGH 满足表记的递归方程" 证成后才算定理. 本文是 [FiniteAll](FiniteAll.lagda.md)/[Translate](Translate.lagda.md) 在 "下标是可数项, 层号由 `toLevel` 从树造出" 时的推广, 能做到哪里就做到哪里, 并把做不到的地方精确地标出来.
>
> 结论先说:
>
> 1. **片段与翻译 (§1–§2).** 片段 $\mathbb G$ 是 EBO 项上的归纳谓词: $0$, 和, $\psi_0(a)$ ($a\in\mathbb G$), $\psi_0(\Omega_u)$ ($u\in\mathbb G$, 任意可数项, 包括 $u=0$), 以及只为容纳 $\gamma$-链结果的 $\psi_0(h)$, $h\in H_\nu$ ($H_\nu::=\Omega_\nu\mid\psi_\nu(H_\nu)$, $\nu\in\mathbb G$). 翻译 `⟦_⟧ : 𝔾 t → Ordᶜ zero` 对推导递归; 下标 $u$ 变成层号 `lvl g = toLevel ⟦ g ⟧ (Good→HS (good g))`, 证书由 `Good` 对推导**归纳**得到 (`good`, 只用 Uniform 的 `Good-add`/`Good-ψ⁰`/`Good-Ω`/`Good-ψ`, 不用 `Uniform` 定理本身). 不需要标准形或任何别的前提.
> 2. **形状定理 (§5) 全部子句已证.** `corr : ∀ (g : 𝔾 t) → Pure g → Shape g` ("纯" = 不含 $H$-构造子): `cof t` 为 $0$ 时 `⟦g⟧ ≅ 0`; 为后继时 `⟦g⟧ ≅ suc ⟦g′⟧`, $g'$ 是 `pred t` 的纯推导; 为 $\omega$ 时 `⟦g⟧ ≅ lim F` 且对每个 $n$ 有 `fsn t n` 的推导 $g_n$ 使 `F n ≅ ⟦g_n⟧`; 为 $\Omega_{\mu+1}$ 的情况不出现 (可数项). 下标层面的 $\Omega$-子句 (`Ω-shape1`, `Ω-shapeω`, §9): $u$ 后继时 $\Omega_{\mathtt{lvl}\,u}\cong\Omega_{\mathrm{suc}\,L'}=$ `limᵢ zero (up zero)`, 指标层 $L'$ 满足 `lvl g ≅ᴵ suc L′`, 分支在 $x$ 处就是 $x$, 与 EBO 的 $\Omega_u[\eta]=\eta$ 一致; $u$ 极限时 $\Omega$ 的第 $n$ 项是 $\Omega_{\mathtt{toLevel}(F\,n)}$, `F n ≅ ⟦u[n]⟧`. **$\gamma$-链子句**: 树在 `limᵢ` 节点上的链 `iter (λ x → ψ zero id (up zero x)) (Ω L′)` 逐项 $\cong$ EBO 的 `γT` 链在 $H$-翻译下的像 (`γᶜ≅`, `γT-ch`, 用在 `corrΩ` 的后继分支). 全部只模 $\cong$.
> 3. **对角线 (§7).** 对一切 $k$, `N.γ k ≅ ⟦ gγ k ⟧`, $\gamma^\mathsf E_k$ 是 EBO 规则 6 给 $\psi_0(\Omega_\Omega)$ 的链 (`diag-fs : fsn (EBOψ 2) n ≡ γᴱ (suc n)`, 由 `fsT↓-trm`/`γ↓-trm` 化到裸值). 于是 `BTBOᴵ` 与 $\psi_0(\Omega_\Omega)$ 的外层基本列逐项匹配 (`BTBO-shape`), 每个 $\gamma_k$ 的一步形状由 `corr` 给出 (`γ-shape`), `FGH BTBOᴵ n ≡ FGH ⟦γᴱ(n+1)⟧ n`.
> 4. **遗传标签 (§8).** 定义 `Lab X t` ("树 $X$ 的基本列遗传地与 $t$ 的一致", 归纳; 由它直接读出 FGH 的三条 EBO 递归方程 `FGH-Lab0`/`FGH-Lab1`/`FGH-Labω`). 对 $\varepsilon_0$ 片段 $\mathbb E$ (由 $0$, 和, $\psi_0(a)$, $\psi_0(\Omega_1)$ 生成, 对 `pred`/`fsn` 封闭) 证了 `Lab ⟦ g ⟧ t` (对树结构递归, 不需要表记侧的 `Acc`), 特别是 **`ε₀-label : Lab (N.γ 1) (γᴱ 1)`: 新树族上 $\gamma_1=\psi_0(\Omega_1)$ 的标签是定理.** 对角线: `diag-label : (∀ k → Lab (N.γ (suc k)) (γᴱ (suc k))) → Lab BTBOᴵ (EBOψ 2)`, 即 BTBO 的标签**恰好**归约为内层的 $\gamma_{k+1}$ ($k\ge1$) 的遗传标签.
> 5. **阶段 2 没有一般地完成 (§9–§10).** 纯片段对 `fsn` 不封闭: 唯一的出口是某处的 $\psi_0(\Omega_{\nu+1})$, $\nu\ne0$, 它的基本列是 $\psi_0(\psi_\nu(\cdots\Omega_\nu))$; 而 $\gamma^\mathsf E_2$ 的基本列四步之后就走到这里 (`refl`: $\gamma^\mathsf E_2[1][2][2][1]=\psi_0(\Omega_{\omega+1})$, 再一步是 $\psi_0(\psi_\omega(\Omega_\omega))$, 再一步是 $\psi_0(\psi_\omega(\Omega_2))$). 在后继层的穿透是结构的且 `refl` 可见 (`pen`, 分支经 `tr⁻ (≅ᴵ-refl M)`, 模 $\cong$ 透明 `pen-branch`, 对应规则 5Ω $\psi_{\mu+1}(\Omega_{\mu+1})[\eta]=\psi_{\mu+1}(\eta)$). 一般情形缺的是**序的对应**: 把 $\Omega_v$ ($v<u$) 放进 $\psi_u$ 的参数层要 `lvl v ≺ᴵ lvl u` 的证据, 而 `<ᴵ-dec` 的派发与 `cmpᵀ (ν+1) u` 一致要 "标准形上 $v<^\mathsf T u\Rightarrow\llbracket v\rrbracket\prec\llbracket u\rrbracket$", 这需要 EBO 的标准形理论 (EBO §9 明说未做), 对非标准项还是假的. **所以 BTBO 的标签 $\psi_0(\Omega_\Omega)$ 仍是估计**; 已是定理的是: 外层一致、每个 $\gamma_k$ 的一步一致、$\gamma_1=\varepsilon_0$ 的遗传一致, 以及 "标签 ⟸ 内层遗传一致" 这条归约.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改动任何已有文件 (没有需要复制的私有定义).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Correspond where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Uniform using (Good; Good-add; Good-ψ; Good-ψ⁰; Good-Ω; Good→HS; gz; γᶜ; s-inv; l-inv; ≅-reflˡ)
import OCF.Align.NoCumsum as N
import OCF.Align.EBO as E
open E using (T; PT; Cof; c0; c1; cω; cΩ; Cmp; lt; eq; gt; cmpᵀ; cof; cofP; cofA; cofψ0; cofψ₊;
              pred; sucT; Ωt; natT; fsn; fsT; fsT0; γT; trm; dec)
       renaming (ψ to ψᵗ)
```

## §1 片段 $\mathbb G$ 与链项 $H_\nu$

EBO 的项是 `List PT`, 主项 `ψᵗ u a` $=\psi_u(a)$ (本文把 EBO 的构造子 `ψ` 改名为 `ψᵗ`, 避免与树侧的折叠 `ψ` 冲突). 片段 $\mathbb G$ 只有目标层 $0$ 的折叠, 下标只以 $\psi_0(\Omega_u)$ 的整体参数出现. `gΩ` 对 $u=[\,]$ 也允许 ($\psi_0(\Omega_0)=\psi_0(1)=\omega$, 与 `gψ` 的推导重叠, 两者的翻译字面相同, §5). $H_\nu$ 是规则 6 在第 $\nu$ 层的 $\gamma$-链所用的项 ($\gamma_0=\Omega_\nu$, $\gamma_{k+1}=\psi_\nu(\gamma_k)$), `gH` 只为了让链的结果 $\psi_0(\gamma_k)$ 有推导; 形状定理不对含 `gH` 的推导陈述.

```agda
data H (ν : T) : T → Set where
  hΩ : H ν (ψᵗ ν [] ∷ [])
  hψ : ∀ {h} → H ν h → H ν (ψᵗ ν h ∷ [])

data 𝔾  : T → Set
data 𝔾ᴾ : PT → Set
data 𝔾 where
  g[] : 𝔾 []
  g∷  : ∀ {x xs} → 𝔾ᴾ x → 𝔾 xs → 𝔾 (x ∷ xs)
data 𝔾ᴾ where
  gψ : ∀ {a} → 𝔾 a → 𝔾ᴾ (ψᵗ [] a)
  gΩ : ∀ {u} → 𝔾 u → 𝔾ᴾ (ψᵗ [] (ψᵗ u [] ∷ []))
  gH : ∀ {ν h} → 𝔾 ν → H ν h → 𝔾ᴾ (ψᵗ [] h)
```

## §2 翻译、证书与层号

$H_\nu$ 在给定层号 $L$ (就是 $\nu$ 的层号) 上的翻译: $\Omega_\nu\mapsto\Omega_L$, $\psi_\nu(h)\mapsto\psi_{L}(\mathsf{up}\;h)$ (参数在第 $L+1$ 层, `up zero` 嵌入). 注意 `ψ p σ (up zero x)` 定义性地归约成 `ψ p (λ q → σ (suc q)) x`, 所以关于它的引理要直接用 `σ = λ q → suc q` 陈述. 第一次照常写成 `ψ-≅ {σ = λ r → r} … (upˡ (upʳ …))` 时报 `[UnsolvedMetaVariables]` (约束 `ψ zero (λ r → r) (up _r_76 _x_77) = ψ zero suc (⟦ d ⟧ᴴ L)` 卡在 `_r_76` 上).

```agda
⟦_⟧ᴴ : ∀ {ν h} → H ν h → (L : Ordᴵ) → Ordᶜ L
⟦ hΩ ⟧ᴴ   L = Ω L
⟦ hψ d ⟧ᴴ L = ψ zero (λ r → r) (up zero (⟦ d ⟧ᴴ L))

reflH : ∀ {ν h} (d : H ν h) L → ⟦ d ⟧ᴴ L ≅ ⟦ d ⟧ᴴ L
reflH hΩ     L = Ω-refl L
reflH (hψ d) L = ψ-≅ {p = zero} {σ = λ q → suc q} {p′ = zero} {σ′ = λ q → suc q} (≅ᴵ-refl L) (reflH d L)

goodH : ∀ {ν h} (d : H ν h) L → Good (⟦ d ⟧ᴴ L)
goodH hΩ     L = Good-Ω L
goodH (hψ d) L = Good-ψ {p = zero} {σ = λ q → suc q} (goodH d L) (reflH d L)
```

主翻译对推导递归; 和是右结合的 `_+_`, 于是单元素和 $x+0$ 定义性地就是 `⟦x⟧` (`add a σ zero = a`). $\psi_0(\Omega_u)$ 的翻译是 `ψ⁰ (Ω (lvl u))`, 层号 `lvl` 是 Level 的 `toLevel` 作用在 $u$ 的翻译与它的证书上. 证书 `good` 与翻译互递归: 每个构造子对应 Uniform §7 的一条封闭性引理, 第 0 层的自反 $\cong$ 由 `≅-refl⁰` 白给. **`Good` 对翻译确实可以对项归纳得到**, 不需要 `Uniform` 这条定理 (它只是 `Good-ψ⁰ (Good-Ω a) (Ω-refl a)` 的特例, 这里正是 `goodᴾ (gΩ u)` 那一行).

```agda
⟦_⟧   : ∀ {t} → 𝔾 t → Ordᶜ zero
⟦_⟧ᴾ  : ∀ {x} → 𝔾ᴾ x → Ordᶜ zero
good  : ∀ {t} (g : 𝔾 t) → Good ⟦ g ⟧
goodᴾ : ∀ {x} (g : 𝔾ᴾ x) → Good ⟦ g ⟧ᴾ
lvl   : ∀ {t} → 𝔾 t → Ordᴵ

⟦ g[] ⟧      = zero
⟦ g∷ x xs ⟧  = ⟦ x ⟧ᴾ + ⟦ xs ⟧
⟦ gψ a ⟧ᴾ    = ψ⁰ ⟦ a ⟧
⟦ gΩ u ⟧ᴾ    = ψ⁰ (Ω (lvl u))
⟦ gH g d ⟧ᴾ  = ψ⁰ (⟦ d ⟧ᴴ (lvl g))
good g[]       = gz
good (g∷ x xs) = Good-add (goodᴾ x) (≅-refl⁰ _) (good xs)
goodᴾ (gψ a)   = Good-ψ⁰ (good a) (≅-refl⁰ _)
goodᴾ (gΩ u)   = Good-ψ⁰ (Good-Ω (lvl u)) (Ω-refl (lvl u))
goodᴾ (gH g d) = Good-ψ⁰ (goodH d (lvl g)) (reflH d (lvl g))
lvl g = toLevel ⟦ g ⟧ (Good→HS (good g))

cert : ∀ {t} (g : 𝔾 t) → HS ⟦ g ⟧
cert g = Good→HS (good g)
```

## §3 纯推导、匹配与形状的陈述

`Pure` 排除 `gH`. `Match s X` 说 "第 0 层的树 $X$ 与项 $s$ 的某个推导的翻译 $\cong$". 形状 `Sh X c t` 按共尾度 $c$ 分四行 (与 FiniteAll §6 同形, 只是 $\Omega$ 行在可数片段里不可能, 写作 $\bot$):

| `cof t` | `Sh X (cof t) t` |
|---|---|
| `c0` | $X\cong 0$ |
| `c1` | 有 `pred t` 的纯推导 $g'$ 使 $X\cong\mathrm{suc}\llbracket g'\rrbracket$ |
| `cω` | 有 $F$ 使 $X\cong\lim F$, 且每个 $n$ 有 `fsn t n` 的推导 $g_n$ 使 $F\,n\cong\llbracket g_n\rrbracket$ |
| `cΩ μ` | $\bot$ |

`HS-≅` (第 0 层的遗传步进沿 $\cong$ 搬运) 是下面 `toLevel-≅` 的前提要用的: 形状定理给出的 `lim F` 只与翻译 $\cong$, 它的证书要从翻译的证书搬过来.

```agda
Pure  : ∀ {t} → 𝔾 t → Set
Pureᴾ : ∀ {x} → 𝔾ᴾ x → Set
Pure g[]        = ⊤
Pure (g∷ x xs)  = Pureᴾ x × Pure xs
Pureᴾ (gψ a)    = Pure a
Pureᴾ (gΩ u)    = Pure u
Pureᴾ (gH _ _)  = ⊥

𝟘 : Ordᶜ zero
𝟘 = zero

Match : T → Ordᶜ zero → Set
Match s X = Σ (𝔾 s) λ g → X ≅ ⟦ g ⟧

Match-≡ : ∀ {s s′ X} → s ≡ s′ → Match s′ X → Match s X
Match-≡ refl m = m

Sh : Ordᶜ zero → Cof → T → Set
Sh X c0     t = X ≅ 𝟘
Sh X c1     t = Σ (𝔾 (pred t)) λ g → Pure g × (X ≅ suc ⟦ g ⟧)
Sh X cω     t = Σ (ℕ → Ordᶜ zero) λ F → (X ≅ lim F) × (∀ n → Match (fsn t n) (F n))
Sh X (cΩ μ) t = ⊥

Shape : ∀ {t} → 𝔾 t → Set
Shape {t} g = Sh ⟦ g ⟧ (cof t) t

HS-≅ : ∀ {x y : Ordᶜ zero} → x ≅ y → HS x → HS y
HS-≅ z≅     hz        = hz
HS-≅ (s≅ e) (hs h)    = hs (HS-≅ e h)
HS-≅ (l≅ k) (hl h st) = hl (λ n → HS-≅ (k n) (h n))
                           (λ n → ⊑-trans (≅→⊑ (≅-sym (k n))) (⊑-trans (st n) (≅→⊑ (k (suc n)))))
HS-≅ (lᵢ≅ {p = ()} _ _) _
HS-≅ (upˡ {r = ()} _)   _
HS-≅ (upʳ {r = ()} _)   _
```

## §4 记号侧: 规则的裸值形式

EBO 的 `fsn` 内部按 `cof` 的**计算值**派发, 证明侧只有命题等式; 与 FiniteAll 一样用 EBO §6 的 J-对齐引理 (`fsn₊-eq`, `fsn0-eq`, `fsT↓-trm`, `γ↓-trm`, `rep-trm`) 把每条规则化成裸值等式. `ch ν k` 是第 $\nu$ 层的规则 6 链 ($\Omega_\nu$, $\psi_\nu(\Omega_\nu)$, …), `hch` 是它的 $H_\nu$ 推导. `cmp-suc[]`: $\nu+1>0$, 所以 $\psi_0$ 的参数共尾度为 $\Omega_{\nu+1}$ 时总走规则 6 (对变量 $\nu$, `sucT ν = ν ++ [1]` 不归约, 要对 $\nu$ 分情况).

```agda
ch : T → ℕ → T
ch ν zero    = ψᵗ ν [] ∷ []
ch ν (suc k) = ψᵗ ν (ch ν k) ∷ []

hch : ∀ ν k → H ν (ch ν k)
hch ν zero    = hΩ
hch ν (suc k) = hψ (hch ν k)

cmp-suc[] : ∀ ν → cmpᵀ (sucT ν) [] ≡ gt
cmp-suc[] []       = refl
cmp-suc[] (x ∷ xs) = refl
```

`cof-ne`: 非空项的共尾度不是 $0$ (对一切 EBO 项, 不限片段).

```agda
cof-ne   : ∀ x xs → cof (x ∷ xs) ≡ c0 → ⊥
cofA-ne  : ∀ u c → cofA u c ≡ c0 → ⊥
cofψ0-ne : ∀ w ws c → cof (w ∷ ws) ≡ c → cofψ0 (w ∷ ws) c ≡ c0 → ⊥
cofψ₊-ne : ∀ u μ m → cofψ₊ u μ m ≡ c0 → ⊥
cof-ne x (y ∷ ys) e               = cof-ne y ys e
cof-ne (ψᵗ u (y ∷ ys)) [] e       = cofA-ne u (cof (y ∷ ys)) e
cof-ne (ψᵗ (w ∷ ws) []) [] e      = cofψ0-ne w ws (cof (w ∷ ws)) refl e
cof-ne (ψᵗ [] []) [] ()
cofA-ne u c0 ()
cofA-ne u c1 ()
cofA-ne u cω ()
cofA-ne u (cΩ μ) e = cofψ₊-ne u μ (cmpᵀ (sucT μ) u) e
cofψ₊-ne u μ lt ()
cofψ₊-ne u μ eq ()
cofψ₊-ne u μ gt ()
cofψ0-ne w ws c0 ce _ = cof-ne w ws ce
cofψ0-ne w ws c1 ce ()
cofψ0-ne w ws cω ce ()
cofψ0-ne w ws (cΩ μ) ce ()
```

四条规则的裸值形式: 规则 4 (`fs-rep`: $\psi_u(b+1)[n]=\psi_u(b)\cdot n$), 规则 5ω (`fs-ω`), 奇异 $\Omega$ 的下标基本列 (`fs-Ωω`: $u$ 极限时 $\psi_0(\Omega_u)[n]=\psi_0(\Omega_{u[n]})$), 规则 6 (`fs-Ω1`: $u=\nu+1$ 时 $\psi_0(\Omega_u)[n]=\psi_0(\gamma_n)$, $\gamma$ 是第 $\nu$ 层的链 `ch ν`). 最后一条要三次对齐: `cmpᵀ (sucT ν) []` 化成 `gt` (`fsn↓c-gt`), `fsT (Ωt u) η = fsT0 u (cof u) η` 化成 $\eta$ (`fsT-c1`, 即 $\Omega_{\nu+1}[\eta]=\eta$), 以及 `γT` 化成 `ch` (`γT-ch`).

```agda
fs-rep : ∀ u y ys → cof (y ∷ ys) ≡ c1 → ∀ n → fsn (ψᵗ u (y ∷ ys) ∷ []) n ≡ replicate n (ψᵗ u (pred (y ∷ ys)))
fs-rep u y ys e n = trans (E.fsn₊-eq u y ys n e) (E.rep-trm u (E.pred-< (y ∷ ys) e) n)

fs-ω : ∀ u y ys → cof (y ∷ ys) ≡ cω → ∀ n → fsn (ψᵗ u (y ∷ ys) ∷ []) n ≡ ψᵗ u (fsn (y ∷ ys) n) ∷ []
fs-ω u y ys e n = E.fsn₊-eq u y ys n e

fs-Ωω : ∀ w ws → cof (w ∷ ws) ≡ cω → ∀ n → fsn (ψᵗ [] (Ωt (w ∷ ws)) ∷ []) n ≡ ψᵗ [] (Ωt (fsn (w ∷ ws) n)) ∷ []
fs-Ωω w ws e n = trans (E.fsn₊-eq [] (ψᵗ (w ∷ ws) []) [] n (cong (cofψ0 (w ∷ ws)) e))
                       (cong (λ z → ψᵗ [] z ∷ []) (E.fsn0-eq w ws n e))

fsT-c1 : ∀ u c → c ≡ c1 → ∀ η → fsT0 u c η ≡ η
fsT-c1 u .c1 refl η = refl

fsn↓c-gt : ∀ u y ys ν be m → m ≡ gt → ∀ n → trm (E.fsn↓c u y ys ν be m n) ≡ trm (E.fsn↓c u y ys ν be gt n)
fsn↓c-gt u y ys ν be .gt refl n = refl

γT-ch : ∀ w ws → cof (w ∷ ws) ≡ c1 → ∀ ν k → γT (Ωt (w ∷ ws)) ν k ≡ ch ν k
γT-ch w ws e ν zero    = refl
γT-ch w ws e ν (suc k) = cong (λ z → ψᵗ ν z ∷ []) (trans (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) e _) (γT-ch w ws e ν k))

fs-Ω1 : ∀ w ws → cof (w ∷ ws) ≡ c1 → ∀ n → fsn (ψᵗ [] (Ωt (w ∷ ws)) ∷ []) n ≡ ψᵗ [] (ch (pred (w ∷ ws)) n) ∷ []
fs-Ω1 w ws e n =
  trans (E.fsn₊-eq [] (ψᵗ u []) [] n be)
  (trans (fsn↓c-gt [] (ψᵗ u []) [] ν be (cmpᵀ (sucT ν) []) (cmp-suc[] ν) n)
         (cong (λ z → ψᵗ [] z ∷ [])
               (trans (E.fsT↓-trm (Ωt u) be (dec g))
               (trans (fsT-c1 u (cof u) e _)
               (trans (E.γ↓-trm (Ωt u) ν be n) (γT-ch w ws e ν n))))))
  where
  u = w ∷ ws
  ν = pred u
  be : cof (Ωt u) ≡ cΩ ν
  be = cong (cofψ0 u) e
  g = E.γ↓ (Ωt u) ν be n
```

## §5 对应定理

树侧的辅助. `rep-≅`: 规则 4 的树 `iter (c +_) zero n` 与 `replicate n` 的翻译 $\cong$. `γᶜ≅`: 树在 $\Omega_{\mathrm{suc}\,L}$ 节点上的链 (Uniform 的 `γᶜ L`, 与 `ψ⁰` 在 `limᵢ` 上的展开定义性一致) 逐项 $\cong$ `ch ν` 的 $H$-翻译, 这就是 **$\gamma$-链子句**; `chainMatch` 把它包成 `Match`. `ΩMatch`: 树 $X\cong\llbracket u'\rrbracket$ 时 $\psi^0(\Omega_{\mathtt{toLevel}\,X})$ 匹配 $\psi_0(\Omega_{u'})$, 经 `toLevel-≅` 与 `Ω-≅`.

```agda
gRep : ∀ {b} → 𝔾 b → ∀ n → 𝔾 (replicate n (ψᵗ [] b))
gRep gb zero    = g[]
gRep gb (suc n) = g∷ (gψ gb) (gRep gb n)

rep-≅ : ∀ {b} (gb : 𝔾 b) n → iter (ψ⁰ ⟦ gb ⟧ +_) zero n ≅ ⟦ gRep gb n ⟧
rep-≅ gb zero    = z≅
rep-≅ gb (suc n) = add-≅ (≅-refl⁰ _) (rep-≅ gb n)

γᶜ≅ : ∀ ν L n → γᶜ L n ≅ ⟦ hch ν n ⟧ᴴ L
γᶜ≅ ν L zero    = Ω-refl L
γᶜ≅ ν L (suc n) = ψ-≅ {p = zero} {σ = λ q → suc q} {p′ = zero} {σ′ = λ q → suc q} (≅ᴵ-refl L) (γᶜ≅ ν L n)

chainMatch : ∀ {ν} (g : 𝔾 ν) n → Match (ψᵗ [] (ch ν n) ∷ []) (ψ⁰ (γᶜ (lvl g) n))
chainMatch {ν} g n = g∷ (gH g (hch ν n)) g[] , ψ⁰-≅ (γᶜ≅ ν (lvl g) n)

ΩMatch : ∀ {s} (g : 𝔾 s) {X} (hX : HS X) → X ≅ ⟦ g ⟧ → Match (ψᵗ [] (Ωt s) ∷ []) (ψ⁰ (Ω (toLevel X hX)))
ΩMatch g hX e = g∷ (gΩ g) g[] , ψ⁰-≅ (Ω-≅ (toLevel-≅ hX (cert g) e))
```

主项与和. `corrψ` 处理 $\psi_0(a)$, $a\ne0$: 后继走规则 4, $\omega$ 走规则 5ω. `corrΩ` 处理 $\psi_0(\Omega_u)$, $u\ne0$: $u$ 后继时先由 $u$ 的形状得 $\llbracket u\rrbracket\cong\mathrm{suc}\llbracket u'\rrbracket$, 于是 `lvl u ≅ᴵ suc (lvl u′)` (`toLevel-≅`; 右边定义性地是 `suc (lvl u′)`, 因为 `toLevel (suc a) (hs h) = suc (toLevel a h)`), 树经 `Ω-≅` 换到 $\Omega_{\mathrm{suc}\,L'}$ = `limᵢ zero (up zero)`, `ψ⁰` 在它上面定义性地展开成链 `γᶜ L′`, 记号侧是 `fs-Ω1`, 两边经 `chainMatch` 接上; $u$ 极限时树换到 `toLevel (lim F) _` (证书经 `HS-≅` 从 `cert u` 搬来), $\Omega$ 定义性地逐项展开, 记号侧是 `fs-Ωω`, 两边经 `ΩMatch` 接上. `sum` 是规则 1. 一切 $\Omega_{\mu+1}$ 行都由归纳假设的 $\bot$ 排除, `c0` 行由 `cof-ne` 排除. `corrᴾ (gΩ g[])` 不递归 (直接用 `corrψ` 在 $1$ 的形状上), 否则过不了停机检查.

```agda
corrψ : ∀ {y ys} (ga : 𝔾 (y ∷ ys)) → ∀ c → cof (y ∷ ys) ≡ c → Sh ⟦ ga ⟧ c (y ∷ ys) →
        Sh (ψ⁰ ⟦ ga ⟧) (cofA [] c) (ψᵗ [] (y ∷ ys) ∷ [])
corrψ {y} {ys} ga c0 e sh = ⊥-elim (cof-ne y ys e)
corrψ {y} {ys} ga c1 e (g′ , _ , eg) =
  iter (ψ⁰ ⟦ g′ ⟧ +_) zero , ψ⁰-≅ eg , λ n → Match-≡ (fs-rep [] y ys e n) (gRep g′ n , rep-≅ g′ n)
corrψ {y} {ys} ga cω e (F , eF , hF) =
  ψ⁰ ∘ F , ψ⁰-≅ eF , λ n → Match-≡ (fs-ω [] y ys e n) (g∷ (gψ (proj₁ (hF n))) g[] , ψ⁰-≅ (proj₂ (hF n)))
corrψ ga (cΩ μ) e ()

corrΩ : ∀ {w ws} (gv : 𝔾 (w ∷ ws)) → ∀ c → cof (w ∷ ws) ≡ c → Sh ⟦ gv ⟧ c (w ∷ ws) →
        Sh (ψ⁰ (Ω (lvl gv))) (cofA [] (cofψ0 (w ∷ ws) c)) (ψᵗ [] (Ωt (w ∷ ws)) ∷ [])
corrΩ {w} {ws} gv c0 e sh = ⊥-elim (cof-ne w ws e)
corrΩ {w} {ws} gv c1 e (g′ , _ , eg) =
  subst (λ m → Sh (ψ⁰ (Ω (lvl gv))) (cofψ₊ [] (pred (w ∷ ws)) m) (ψᵗ [] (Ωt (w ∷ ws)) ∷ []))
        (sym (cmp-suc[] (pred (w ∷ ws))))
        ((λ n → ψ⁰ (γᶜ (lvl g′) n)) , ψ⁰-≅ (Ω-≅ (toLevel-≅ (cert gv) (hs (cert g′)) eg)) ,
         λ n → Match-≡ (fs-Ω1 w ws e n) (chainMatch g′ n))
corrΩ {w} {ws} gv cω e (F , eF , hF) =
  (λ n → ψ⁰ (Ω (toLevel (F n) (hl₁ hF′ n)))) , ψ⁰-≅ (Ω-≅ (toLevel-≅ (cert gv) hF′ eF)) ,
  λ n → Match-≡ (fs-Ωω w ws e n) (ΩMatch (proj₁ (hF n)) (hl₁ hF′ n) (proj₂ (hF n)))
  where
  hF′ : HS (lim F)
  hF′ = HS-≅ eF (cert gv)
corrΩ gv (cΩ μ) e ()

sum : ∀ {x y ys} (gx : 𝔾ᴾ x) → Pureᴾ gx → (gys : 𝔾 (y ∷ ys)) → ∀ c → cof (y ∷ ys) ≡ c → Sh ⟦ gys ⟧ c (y ∷ ys) →
      Sh (⟦ gx ⟧ᴾ + ⟦ gys ⟧) c (x ∷ y ∷ ys)
sum {y = y} {ys} gx px gys c0 e _ = ⊥-elim (cof-ne y ys e)
sum gx px gys c1 e (g′ , p′ , eg) = g∷ gx g′ , (px , p′) , add-≅ (≅-refl⁰ _) eg
sum gx px gys cω e (F , eF , hF) =
  (λ n → ⟦ gx ⟧ᴾ + F n) , add-≅ (≅-refl⁰ _) eF ,
  λ n → g∷ gx (proj₁ (hF n)) , add-≅ (≅-refl⁰ _) (proj₂ (hF n))
sum gx px gys (cΩ μ) e ()

corr  : ∀ {t} (g : 𝔾 t) → Pure g → Shape g
corrᴾ : ∀ {x} (g : 𝔾ᴾ x) → Pureᴾ g → Sh ⟦ g ⟧ᴾ (cofP x) (x ∷ [])
corr g[] _ = z≅
corr (g∷ gx g[]) (px , _) = corrᴾ gx px
corr (g∷ gx (g∷ {x = y} {xs = ys} gy gys)) (px , p) = sum gx px (g∷ gy gys) (cof (y ∷ ys)) refl (corr (g∷ gy gys) p)
corrᴾ (gψ g[]) _ = g[] , tt , s≅ z≅
corrᴾ (gψ (g∷ {x = y} {xs = ys} gy gys)) p = corrψ (g∷ gy gys) (cof (y ∷ ys)) refl (corr (g∷ gy gys) p)
corrᴾ (gΩ g[]) _ = corrψ (g∷ (gψ g[]) g[]) c1 refl (g[] , tt , s≅ z≅)
corrᴾ (gΩ (g∷ {x = w} {xs = ws} gw gws)) p = corrΩ (g∷ gw gws) (cof (w ∷ ws)) refl (corr (g∷ gw gws) p)
corrᴾ (gH _ _) ()
```

**陈述.** 对每个纯推导 $g:\mathbb G\,t$ (任意可数下标, 不要求标准形), `Shape g`. 没有遗漏的子句: $0$、后继、$\omega$ 三行都是构造性的证明, $\Omega$ 行在片段内不可能. 后继行的 `pred t` 推导仍是纯的; $\omega$ 行的 `fsn t n` 推导可能含 `gH` (只由 `chainMatch` 产生, 见 §9).

## §6 FGH 的一步递归方程

由形状定理与 Level 的 `FGH-≅` 直接得到: 树 `⟦g⟧` 的 FGH 满足 EBO FGH 的三条递归方程, 每条一步 ($t=0$: $n+1$; $t$ 后继: $f_{t-1}^n(n)$; $t$ 为 $\omega$-共尾: $f_{t[n]}(n)$), 右边的项 `pred t`/`fsn t n` 以某个推导的翻译出现.

```agda
FGH-c0 : ∀ {t} (g : 𝔾 t) → Pure g → cof t ≡ c0 → ∀ n → FGH ⟦ g ⟧ n ≡ suc n
FGH-c0 {t} g p e = FGH-≅ (subst (λ c → Sh ⟦ g ⟧ c t) e (corr g p))

FGH-c1 : ∀ {t} (g : 𝔾 t) → Pure g → cof t ≡ c1 →
         Σ (𝔾 (pred t)) λ g′ → Pure g′ × (∀ n → FGH ⟦ g ⟧ n ≡ iter (FGH ⟦ g′ ⟧) n n)
FGH-c1 {t} g p e with subst (λ c → Sh ⟦ g ⟧ c t) e (corr g p)
... | g′ , p′ , eg = g′ , p′ , FGH-≅ eg

FGH-cω : ∀ {t} (g : 𝔾 t) → Pure g → cof t ≡ cω → ∀ n → Σ (𝔾 (fsn t n)) λ g′ → FGH ⟦ g ⟧ n ≡ FGH ⟦ g′ ⟧ n
FGH-cω {t} g p e n with subst (λ c → Sh ⟦ g ⟧ c t) e (corr g p)
... | F , eF , hF = proj₁ (hF n) , trans (FGH-≅ eF n) (FGH-≅ (proj₂ (hF n)) n)
```

## §7 对角线

EBO 的 $\psi_0(\Omega_\Omega)$ (`EBOψ 2`) 的规则 6 链: $\gamma^\mathsf E_0=1$, $\gamma^\mathsf E_{k+1}=\psi_0(\Omega_{\gamma^\mathsf E_k})$. `diag-fs` 把 `fsn (EBOψ 2) n` 经 `fsT↓-trm`/`γ↓-trm` 化到裸值; 其中 `fsT βᴱ η ≡ Ωt η` 是定义性的 ($\Omega_\Omega[\eta]=\Omega_\eta$, 正规叶 $\Omega_1$ 给出 $\eta$). 每个 $\gamma^\mathsf E_k$ 都在纯片段里 (`gγ`, `pγ`, 全用 `gΩ`). 树侧 `N.γ` 是 NoCumsum 的闭项. `diag-≅` 对 $k$ 归纳: 两边的下一项都是 $\psi^0(\Omega_{\mathtt{toLevel}(\cdot)})$, 层号经 `toLevel-≅` (两边证书不同: 一边是 `Uniform (L k)`, 一边是 `good` 的归纳证书) 相关.

```agda
γᴱ : ℕ → T
γᴱ zero    = ψᵗ [] [] ∷ []
γᴱ (suc k) = ψᵗ [] (Ωt (γᴱ k)) ∷ []

gγ : ∀ k → 𝔾 (γᴱ k)
gγ zero    = g∷ (gψ g[]) g[]
gγ (suc k) = g∷ (gΩ (gγ k)) g[]

pγ : ∀ k → Pure (gγ k)
pγ zero    = tt , tt
pγ (suc k) = pγ k , tt

βᴱ : T
βᴱ = Ωt (Ωt (natT 1))

_ : E.EBOψ 2 ≡ ψᵗ [] βᴱ ∷ []
_ = refl

_ : ∀ η → fsT βᴱ η ≡ Ωt η
_ = λ η → refl

_ : cof (E.EBOψ 2) ≡ cω
_ = refl

γT-γᴱ : ∀ k → γT βᴱ [] k ≡ γᴱ k
γT-γᴱ zero    = refl
γT-γᴱ (suc k) = cong (λ z → ψᵗ [] (Ωt z) ∷ []) (γT-γᴱ k)

diag-fs : ∀ n → fsn (E.EBOψ 2) n ≡ γᴱ (suc n)
diag-fs n = cong (λ z → ψᵗ [] z ∷ [])
  (trans (E.fsT↓-trm βᴱ refl (dec (E.γ↓ βᴱ [] refl n))) (cong (fsT βᴱ) (trans (E.γ↓-trm βᴱ [] refl n) (γT-γᴱ n))))

diag-≅ : ∀ k → N.γ k ≅ ⟦ gγ k ⟧
diag-≅ zero    = s≅ z≅
diag-≅ (suc k) = ψ⁰-≅ (Ω-≅ (toLevel-≅ (N.cert k) (cert (gγ k)) (diag-≅ k)))

BTBO-shape : Sh N.BTBOᴵ (cof (E.EBOψ 2)) (E.EBOψ 2)
BTBO-shape = N.γ ∘ suc , l≅ (λ n → ≅-refl⁰ _) , λ n → Match-≡ (diag-fs n) (gγ (suc n) , diag-≅ (suc n))

FGH-BTBO : ∀ n → FGH N.BTBOᴵ n ≡ FGH ⟦ gγ (suc n) ⟧ n
FGH-BTBO n = FGH-≅ (diag-≅ (suc n)) n

γ-shape : ∀ k → Shape (gγ k)
γ-shape k = corr (gγ k) (pγ k)
```

`BTBO-shape` 是 `BTBOᴵ` 对 $\psi_0(\Omega_\Omega)$ 的 $\omega$ 行 (即使 $\psi_0(\Omega_\Omega)$ 的下标 $\Omega$ 不可数、不在 $\mathbb G$ 里): `BTBOᴵ ≅ lim (γ ∘ suc)`, 第 $n$ 项匹配 `fsn (EBOψ 2) n`. `γ-shape k` 是每个 $\gamma^\mathsf E_k$ 的一步形状.

## §8 遗传标签

`Lab X t` 是 README 认证标准的直接形式化: 归纳地, $X$ 的形状由 `cof t` 决定, 且前驱/各项又带 `pred t`/`fsn t n` 的标签. 只要 `Lab X t`, 树的 FGH 就满足 EBO 的 FGH 沿 $t$ 的**全部**递归方程 (`FGH-Lab0`/`FGH-Lab1`/`FGH-Labω` 逐层读出, 可以一直用下去). `Lab` 在 $\cong$ 下不变 (`Lab-≅`).

```agda
data Lab : Ordᶜ zero → T → Set where
  l0 : ∀ {X t} → cof t ≡ c0 → X ≅ 𝟘 → Lab X t
  l1 : ∀ {X Y t} → cof t ≡ c1 → X ≅ suc Y → Lab Y (pred t) → Lab X t
  lω : ∀ {X t} {F : ℕ → Ordᶜ zero} → cof t ≡ cω → X ≅ lim F → (∀ n → Lab (F n) (fsn t n)) → Lab X t

Lab-≅ : ∀ {X X′ t} → X′ ≅ X → Lab X t → Lab X′ t
Lab-≅ d (l0 c e)     = l0 c (≅-trans d e)
Lab-≅ d (l1 c e l)   = l1 c (≅-trans d e) l
Lab-≅ d (lω c e h)   = lω c (≅-trans d e) h

FGH-Lab0 : ∀ {X t} → Lab X t → cof t ≡ c0 → ∀ n → FGH X n ≡ suc n
FGH-Lab0 (l0 _ e) _ = FGH-≅ e
FGH-Lab0 (l1 c _ _) c′ = ⊥-elim (c0≢c1 (trans (sym c′) c)) where
  c0≢c1 : c0 ≡ c1 → ⊥
  c0≢c1 ()
FGH-Lab0 (lω c _ _) c′ = ⊥-elim (c0≢cω (trans (sym c′) c)) where
  c0≢cω : c0 ≡ cω → ⊥
  c0≢cω ()
```

**$\varepsilon_0$ 片段.** $\mathbb E$: $0$, 和, $\psi_0(a)$, 以及唯一的 $\Omega$-项 $\psi_0(\Omega_1)$. 它对 `pred`、`fsn` 封闭: 规则 4、5ω、1 保持 $\mathbb E$; $\psi_0(\Omega_1)$ 的链在第 0 层 ($\nu=0$), $\gamma_k=\psi_0^k(1)$ (`pch`) 都在 $\mathbb E$ 里. 树侧第 0 层的链 `γᶜ zero` 用 Level 的 `ψ⁰≅ψ` 与 `ψ⁰` 对上 (`pch-≅`). `corrE` 与 `corr` 同构, 只是匹配的推导留在 $\mathbb E$ 里; $\psi_0(\Omega_1)$ 的情况完全定义性 (`lvl 1` 字面上是 `suc zero`).

```agda
data 𝔼  : T → Set
data 𝔼ᴾ : PT → Set
data 𝔼 where
  e[] : 𝔼 []
  e∷  : ∀ {x xs} → 𝔼ᴾ x → 𝔼 xs → 𝔼 (x ∷ xs)
data 𝔼ᴾ where
  eψ  : ∀ {a} → 𝔼 a → 𝔼ᴾ (ψᵗ [] a)
  eΩ₁ : 𝔼ᴾ (ψᵗ [] (Ωt (natT 1)))

emb  : ∀ {t} → 𝔼 t → 𝔾 t
embᴾ : ∀ {x} → 𝔼ᴾ x → 𝔾ᴾ x
emb e[]        = g[]
emb (e∷ x xs)  = g∷ (embᴾ x) (emb xs)
embᴾ (eψ a)    = gψ (emb a)
embᴾ eΩ₁       = gΩ (g∷ (gψ g[]) g[])

MatchE : T → Ordᶜ zero → Set
MatchE s X = Σ (𝔼 s) λ g → X ≅ ⟦ emb g ⟧

MatchE-≡ : ∀ {s s′ X} → s ≡ s′ → MatchE s′ X → MatchE s X
MatchE-≡ refl m = m

ShE : Ordᶜ zero → Cof → T → Set
ShE X c0     t = X ≅ 𝟘
ShE X c1     t = Σ (𝔼 (pred t)) λ g → X ≅ suc ⟦ emb g ⟧
ShE X cω     t = Σ (ℕ → Ordᶜ zero) λ F → (X ≅ lim F) × (∀ n → MatchE (fsn t n) (F n))
ShE X (cΩ μ) t = ⊥

eRep : ∀ {b} → 𝔼 b → ∀ n → 𝔼 (replicate n (ψᵗ [] b))
eRep gb zero    = e[]
eRep gb (suc n) = e∷ (eψ gb) (eRep gb n)

eRep-≅ : ∀ {b} (gb : 𝔼 b) n → iter (ψ⁰ ⟦ emb gb ⟧ +_) zero n ≅ ⟦ emb (eRep gb n) ⟧
eRep-≅ gb zero    = z≅
eRep-≅ gb (suc n) = add-≅ (≅-refl⁰ _) (eRep-≅ gb n)

pch : ∀ k → 𝔼 (ch [] k)
pch zero    = e∷ (eψ e[]) e[]
pch (suc k) = e∷ (eψ (pch k)) e[]

pch-≅ : ∀ k → γᶜ zero k ≅ ⟦ emb (pch k) ⟧
pch-≅ zero    = s≅ z≅
pch-≅ (suc k) = ≅-sym (ψ⁰≅ψ {p = zero} {σ = λ q → suc q} (≅-sym (pch-≅ k)))

corrψE : ∀ {y ys} (ga : 𝔼 (y ∷ ys)) → ∀ c → cof (y ∷ ys) ≡ c → ShE ⟦ emb ga ⟧ c (y ∷ ys) →
         ShE (ψ⁰ ⟦ emb ga ⟧) (cofA [] c) (ψᵗ [] (y ∷ ys) ∷ [])
corrψE {y} {ys} ga c0 e sh = ⊥-elim (cof-ne y ys e)
corrψE {y} {ys} ga c1 e (g′ , eg) =
  iter (ψ⁰ ⟦ emb g′ ⟧ +_) zero , ψ⁰-≅ eg , λ n → MatchE-≡ (fs-rep [] y ys e n) (eRep g′ n , eRep-≅ g′ n)
corrψE {y} {ys} ga cω e (F , eF , hF) =
  ψ⁰ ∘ F , ψ⁰-≅ eF , λ n → MatchE-≡ (fs-ω [] y ys e n) (e∷ (eψ (proj₁ (hF n))) e[] , ψ⁰-≅ (proj₂ (hF n)))
corrψE ga (cΩ μ) e ()

sumE : ∀ {x y ys} (gx : 𝔼ᴾ x) (gys : 𝔼 (y ∷ ys)) → ∀ c → cof (y ∷ ys) ≡ c → ShE ⟦ emb gys ⟧ c (y ∷ ys) →
       ShE (⟦ embᴾ gx ⟧ᴾ + ⟦ emb gys ⟧) c (x ∷ y ∷ ys)
sumE {y = y} {ys} gx gys c0 e _ = ⊥-elim (cof-ne y ys e)
sumE gx gys c1 e (g′ , eg) = e∷ gx g′ , add-≅ (≅-refl⁰ _) eg
sumE gx gys cω e (F , eF , hF) =
  (λ n → ⟦ embᴾ gx ⟧ᴾ + F n) , add-≅ (≅-refl⁰ _) eF ,
  λ n → e∷ gx (proj₁ (hF n)) , add-≅ (≅-refl⁰ _) (proj₂ (hF n))
sumE gx gys (cΩ μ) e ()

corrE  : ∀ {t} (g : 𝔼 t) → ShE ⟦ emb g ⟧ (cof t) t
corrEᴾ : ∀ {x} (g : 𝔼ᴾ x) → ShE ⟦ embᴾ g ⟧ᴾ (cofP x) (x ∷ [])
corrE e[] = z≅
corrE (e∷ gx e[]) = corrEᴾ gx
corrE (e∷ gx (e∷ {x = y} {xs = ys} gy gys)) = sumE gx (e∷ gy gys) (cof (y ∷ ys)) refl (corrE (e∷ gy gys))
corrEᴾ (eψ e[]) = e[] , s≅ z≅
corrEᴾ (eψ (e∷ {x = y} {xs = ys} gy gys)) = corrψE (e∷ gy gys) (cof (y ∷ ys)) refl (corrE (e∷ gy gys))
corrEᴾ eΩ₁ = (λ n → ψ⁰ (γᶜ zero n)) , ≅-refl⁰ _ ,
  λ n → MatchE-≡ (fs-Ω1 (ψᵗ [] []) [] refl n) (e∷ (eψ (pch n)) e[] , ψ⁰-≅ (pch-≅ n))
```

**由形状到遗传标签: 对树递归.** 表记侧没有 `Acc` (EBO §9: `_<ᵀ_` 在一般项上不良基), 但不需要: `lab X g` 对第 0 层的树 $X$ 结构递归, $X\cong\mathrm{suc}\,\llbracket g'\rrbracket$ 迫使 $X=\mathrm{suc}\,Y$, $X\cong\lim F$ 迫使 $X=\lim F'$, 递归到 $Y$ 与 $F'\,n$. 这是 "树这边良基免费" 的字面实现 (EBO §9 的设想).

```agda
z≇s : ∀ {b : Ordᶜ zero} → 𝟘 ≅ suc b → ⊥
z≇s ()
l≇s : ∀ {f : ℕ → Ordᶜ zero} {b : Ordᶜ zero} → lim f ≅ suc b → ⊥
l≇s ()
z≇l : ∀ {f : ℕ → Ordᶜ zero} → 𝟘 ≅ lim f → ⊥
z≇l ()
s≇l : ∀ {a : Ordᶜ zero} {f : ℕ → Ordᶜ zero} → suc a ≅ lim f → ⊥
s≇l ()

lab   : ∀ (X : Ordᶜ zero) {t} (g : 𝔼 t) → X ≅ ⟦ emb g ⟧ → Lab X t
labSh : ∀ (X : Ordᶜ zero) {t} (g : 𝔼 t) c → cof t ≡ c → ShE ⟦ emb g ⟧ c t → X ≅ ⟦ emb g ⟧ → Lab X t
lab X {t} g d = labSh X g (cof t) refl (corrE g) d
labSh X g c0 ce sh d = l0 ce (≅-trans d sh)
labSh zero    g c1 ce (g′ , eg) d = ⊥-elim (z≇s (≅-trans d eg))
labSh (lim F) g c1 ce (g′ , eg) d = ⊥-elim (l≇s (≅-trans d eg))
labSh (suc Y) g c1 ce (g′ , eg) d = l1 ce (s≅ (≅-reflˡ e′)) (lab Y g′ e′)
  where e′ = s-inv (≅-trans d eg)
labSh zero    g cω ce (F , eF , hF) d = ⊥-elim (z≇l (≅-trans d eF))
labSh (suc Y) g cω ce (F , eF , hF) d = ⊥-elim (s≇l (≅-trans d eF))
labSh (lim F′) g cω ce (F , eF , hF) d =
  lω ce (l≅ (λ n → ≅-reflˡ (h n))) (λ n → lab (F′ n) (proj₁ (hF n)) (≅-trans (h n) (proj₂ (hF n))))
  where h = l-inv (≅-trans d eF)
labSh (limᵢ () f) g _ _ _ _
labSh (up () x)   g _ _ _ _

ε₀-label : Lab (N.γ 1) (γᴱ 1)
ε₀-label = lab (N.γ 1) (e∷ eΩ₁ e[]) (≅-refl⁰ _)

diag-label : (∀ k → Lab (N.γ (suc k)) (γᴱ (suc k))) → Lab N.BTBOᴵ (E.EBOψ 2)
diag-label h = lω refl (l≅ (λ n → ≅-refl⁰ _)) (λ n → subst (Lab (N.γ (suc n))) (sym (diag-fs n)) (h n))

FGH-Lab1 : ∀ {X t} → Lab X t → cof t ≡ c1 → Σ (Ordᶜ zero) λ Y → Lab Y (pred t) × (∀ n → FGH X n ≡ iter (FGH Y) n n)
FGH-Lab1 (l0 c _)   c′ = ⊥-elim (c0≢c1 (trans (sym c) c′)) where
  c0≢c1 : c0 ≡ c1 → ⊥
  c0≢c1 ()
FGH-Lab1 (l1 c e l) c′ = _ , l , FGH-≅ e
FGH-Lab1 (lω c _ _) c′ = ⊥-elim (cω≢c1 (trans (sym c) c′)) where
  cω≢c1 : cω ≡ c1 → ⊥
  cω≢c1 ()

FGH-Labω : ∀ {X t} → Lab X t → cof t ≡ cω →
           Σ (ℕ → Ordᶜ zero) λ F → (∀ n → Lab (F n) (fsn t n)) × (∀ n → FGH X n ≡ FGH (F n) n)
FGH-Labω (l0 c _)   c′ = ⊥-elim (c0≢cω (trans (sym c) c′)) where
  c0≢cω : c0 ≡ cω → ⊥
  c0≢cω ()
FGH-Labω (l1 c _ _) c′ = ⊥-elim (c1≢cω (trans (sym c) c′)) where
  c1≢cω : c1 ≡ cω → ⊥
  c1≢cω ()
FGH-Labω (lω {F = F} c e h) c′ = F , h , FGH-≅ e
```

## §9 下标的 $\Omega$-子句与穿透

下标的两种 $\Omega$ 形状 (形状定理的推论). `Ω-shape1`: $u$ 后继时 $\Omega$ 节点的指标层 $\cong^\mathsf I$ `lvl (pred u)`, $\Omega_{\mathrm{suc}\,L}$ 定义性地是 `limᵢ zero (up zero)` (分支在 $x$ 处是 $x$ 本身), 记号侧 $\Omega_u[\eta]=\eta$. `Ω-shapeω`: $u$ 极限时 $\Omega_{\mathtt{lvl}\,u}\cong\Omega_{\mathtt{toLevel}(\lim F)}$, 后者定义性地是 $\lim_n\Omega_{\mathtt{toLevel}(F\,n)}$, `F n` 匹配 $u[n]$, 记号侧 $\Omega_u[n]=\Omega_{u[n]}$.

```agda
Ω-shape1 : ∀ {w ws} (g : 𝔾 (w ∷ ws)) → Pure g → cof (w ∷ ws) ≡ c1 →
           Σ (𝔾 (pred (w ∷ ws))) λ g′ → Pure g′ × (lvl g ≅ᴵ suc (lvl g′)) × (Ω (lvl g) ≅ Ω (suc (lvl g′)))
           × (∀ η → fsT (Ωt (w ∷ ws)) η ≡ η)
Ω-shape1 {w} {ws} g p e with subst (λ c → Sh ⟦ g ⟧ c (w ∷ ws)) e (corr g p)
... | g′ , p′ , eg = g′ , p′ , eL , Ω-≅ eL , fsT-c1 (w ∷ ws) (cof (w ∷ ws)) e
  where eL = toLevel-≅ (cert g) (hs (cert g′)) eg

_ : ∀ L → Ω (suc L) ≡ limᵢ zero (up zero)
_ = λ L → refl

Ω-shapeω : ∀ {w ws} (g : 𝔾 (w ∷ ws)) → Pure g → cof (w ∷ ws) ≡ cω →
           Σ (ℕ → Ordᶜ zero) λ F → Σ (HS (lim F)) λ hF → (lvl g ≅ᴵ toLevel (lim F) hF)
           × (∀ n → Match (fsn (w ∷ ws) n) (F n)) × (∀ n → fsn (Ωt (w ∷ ws)) n ≡ Ωt (fsn (w ∷ ws) n))
Ω-shapeω {w} {ws} g p e with subst (λ c → Sh ⟦ g ⟧ c (w ∷ ws)) e (corr g p)
... | F , eF , hF = F , HS-≅ eF (cert g) , toLevel-≅ (cert g) (HS-≅ eF (cert g)) eF , hF , λ n → E.fsn0-eq w ws n e
```

**穿透 (阶段 2 的入口).** 在后继层 $M+1$ 上, $\psi_{M+1}(\Omega_{M+1})$ 的树定义性地是一个穿透节点 (`<ᴵ-dec (suc zero) zero` 字面地给出 `injᵃ (via (≅ᴵ-refl M) zero)`), 分支经 `tr⁻ (≅ᴵ-refl M)` 搬回第 $M$ 层再折叠 (`pen`, `refl`). 这一次搬运模 $\cong$ 不可见 (`pen-branch`, 由 Level 的 `tr⁻-≅`), 于是分支在 $x$ 处 $\cong\psi_{M+1}(x)$, 正是 EBO 的规则 5Ω $\psi_{\mu+1}(\Omega_{\mu+1})[\eta]=\psi_{\mu+1}(\eta)$. `Sim` 累加器在这里是 `λ q → suc (suc q)`: 两次 `up zero` 被 `ψ` 吸收进 `σ`.

```agda
pen : ∀ (M : Ordᴵ) → ψ {i = suc M} zero (λ q → suc q) (Ω (suc M))
                     ≡ limᵢ zero (λ y → ψ zero (λ q → suc (suc q)) (tr⁻ (≅ᴵ-refl M) y))
pen M = refl

pen-branch : ∀ {M} (x : Ordᶜ M) → x ≅ x →
             ψ {i = suc M} zero (λ q → suc (suc q)) (tr⁻ (≅ᴵ-refl M) x) ≅ ψ {i = suc M} zero (λ q → suc (suc q)) x
pen-branch {M} x d = ψ-≅ {p = zero} {σ = λ q → suc (suc q)} {p′ = zero} {σ′ = λ q → suc (suc q)} (≅ᴵ-refl (suc M)) (tr⁻-≅ (≅ᴵ-refl M) d)
```

## §10 样例与出口

`refl` 核对: $\gamma^\mathsf E_2[0]=\psi_0(\Omega_\omega)$; $\psi_0(\Omega_2)[1]=\psi_0(\psi_1(\Omega_1))$ (这一项由 `chainMatch` 匹配, 推导是 `gH`); FGH 小值与 NoCumsum 一致.

```agda
_ : fsn (γᴱ 2) 0 ≡ ψᵗ [] (Ωt (ψᵗ [] (ψᵗ [] [] ∷ []) ∷ [])) ∷ []
_ = refl

_ : fsn (ψᵗ [] (Ωt (natT 2)) ∷ []) 1 ≡ ψᵗ [] (ψᵗ (natT 1) (Ωt (natT 1)) ∷ []) ∷ []
_ = refl

_ : FGH (N.γ 1) 1 ≡ 2
_ = refl

_ : FGH ⟦ gγ 2 ⟧ 1 ≡ 2
_ = refl
```

**出口.** 纯片段在 `fsn` 下唯一的出口是 $\psi_0(\Omega_{\nu+1})$, $\nu\ne0$ (由代码可见: `gH` 只由 `chainMatch` 产生, 它只在 `corrΩ` 的后继分支被调用; 未形式化成一条定理). 对角线的第二项就走到它: 下面三条 `refl` 依次是 $\gamma^\mathsf E_2[1][2][2][1]=\psi_0(\Omega_{\omega+1})$ (路径 $\varepsilon_0\to\omega^\omega\to\omega^2\to\omega\cdot2\to\omega+1$ 在下标里), $\psi_0(\Omega_{\omega+1})[1]=\psi_0(\psi_\omega(\Omega_\omega))$, $\psi_0(\psi_\omega(\Omega_\omega))[2]=\psi_0(\psi_\omega(\Omega_2))$. 最后一项的参数 $\psi_\omega(\Omega_2)$ 把第 2 层的 $\Omega_2$ 放进 $\psi_\omega$ 的参数层: 树侧这要 `lvl 2 ≺ᴵ lvl ω` 的证据才能 `lift`; 而 `lvl ω` 的第 2 项是 `toLevel (iter (1 +_) 0 2) _`, 对具体的 2 恰好字面等于 `lvl 2` 的值, 对变量 $n$ 只 $\cong^\mathsf I$.

```agda
ωᵗ : T
ωᵗ = ψᵗ [] (ψᵗ [] [] ∷ []) ∷ []

_ : fsn (fsn (fsn (fsn (γᴱ 2) 1) 2) 2) 1 ≡ ψᵗ [] (Ωt (ψᵗ [] (ψᵗ [] [] ∷ []) ∷ ψᵗ [] [] ∷ [])) ∷ []
_ = refl

_ : fsn (ψᵗ [] (Ωt (ψᵗ [] (ψᵗ [] [] ∷ []) ∷ ψᵗ [] [] ∷ [])) ∷ []) 1 ≡ ψᵗ [] (ψᵗ ωᵗ (Ωt ωᵗ) ∷ []) ∷ []
_ = refl

_ : fsn (ψᵗ [] (ψᵗ ωᵗ (Ωt ωᵗ) ∷ []) ∷ []) 2 ≡ ψᵗ [] (ψᵗ ωᵗ (Ωt (natT 2)) ∷ []) ∷ []
_ = refl
```

## §11 对比表

| | FiniteAll (BTBO 的 `Ord (nat n)`) | 本文 (Level 的 `Ordᶜ`, 下标 `Ordᴵ`) |
|---|---|---|
| 下标 | 自然数 $\nu$, 层号 `nat ν` | 可数项 $u\in\mathbb G$, 层号 `toLevel ⟦u⟧ (cert u)` |
| 片段 | 一切镜像项 (下标 ℕ), 无前提 | $\psi_0$ 片段, 下标任意可数项; 前提 `Pure` (不含链项构造子) |
| 证书 | 不需要 | `good` 对推导归纳 (Uniform §7 的封闭性), 不用 `Uniform` 定理 |
| 形状定理 | `corr : ∀ t → Shape t`, 四行 | `corr : ∀ g → Pure g → Shape g`, 三行 + $\Omega$ 行不可能 |
| $\Omega$-基本列子句 | `Ω-corr`, 任意 $\mu$ | 下标的 $\Omega$: `Ω-shape1` (后继, `limᵢ`, 指标层 $\cong^\mathsf I$ `lvl (pred u)`), `Ω-shapeω` (极限) |
| $\gamma$-链 | `chain` 逐项 $\approx$ | `γᶜ≅` + `γT-ch`, 第 $\nu$ 层的链与 `ch ν` 的 $H$-翻译 $\cong$ |
| 穿透 | `pen` (派发引理), 一般 $\nu<u$ | 只有后继层的结构穿透 (`pen`, `pen-branch`); 一般 $\nu<u$ 未做 |
| 对 `fsn` 封闭 | 是 (定理无前提) | 否: 出口 $\psi_0(\Omega_{\nu+1})$, $\nu\ne0$; $\varepsilon_0$ 片段 $\mathbb E$ 封闭 |
| 遗传标签 | `FGH-c1`/`FGH-cω` 沿 `Top₀` 一路可用 | `Lab` (归纳, 对树递归证); $\mathbb E$ 全体, 特别是 $\gamma_1=\varepsilon_0$ |
| 相等的种类 | 异层 $\approx$ | 跨层 $\cong$ (Level), 层号 $\cong^\mathsf I$ |

## §12 结论与边界

**字面成立 (`refl` 或定义性):** `fsT βᴱ η ≡ Ωt η`; `cof (EBOψ 2) ≡ cω`; `EBOψ 2 ≡ ψ₀(βᴱ)`; `Ω (suc L) ≡ limᵢ zero (up zero)`; `pen` (后继层穿透节点的形状); `⟦gΩ g[]⟧` 与 `⟦gψ 1⟧` 是同一棵树; $\psi_0(\Omega_1)$ 的树就是 `N.γ 1`; 记号侧的规则化简 (`fs-rep`, `fs-ω`, `fs-Ωω`, `fs-Ω1`, `diag-fs`) 是命题等式, 但只用 J-对齐, 无函数外延; 样例与 FGH 小值.

**模 $\cong$ 成立 (定理):**

1. 形状定理 `corr` (纯片段 $\mathbb G$, 任意可数下标, 无标准形前提), 一步 FGH 方程 `FGH-c0`/`FGH-c1`/`FGH-cω`, 下标 $\Omega$-子句 `Ω-shape1`/`Ω-shapeω`, $\gamma$-链子句 `γᶜ≅`/`chainMatch`.
2. 对角线: `diag-≅ : ∀ k → N.γ k ≅ ⟦ gγ k ⟧`, `BTBO-shape`, `FGH-BTBO`, `γ-shape`.
3. 遗传: `lab` (每个 $\mathbb E$ 项), **`ε₀-label : Lab (N.γ 1) (γᴱ 1)`**, 以及归约 `diag-label`.
4. 穿透的不可见性 `pen-branch`.

字面相等做不到的原因与 SafePath §12、Level §2 相同: 层号的步进证据来自不同证书 (`Uniform (L k)` 对 `good`), `toLevel` 的结果只 $\cong^\mathsf I$; 穿透里的 `tr⁻` 字面地改写树.

**关于标签 $\psi_0(\Omega_\Omega)$, 证了什么:** (i) `BTBOᴵ` 的基本列逐项 $\cong$ EBO 的 $\psi_0(\Omega_\Omega)[n]=\gamma^\mathsf E_{n+1}$ 的翻译; (ii) 每个 $\gamma_k$ 的第一步基本列与 EBO 一致; (iii) $\gamma_1=\psi_0(\Omega_1)=\varepsilon_0$ 的标签是定理 (FGH 满足 EBO 沿 $\varepsilon_0$ 的全部递归方程); (iv) `BTBOᴵ` 的标签 $\psi_0(\Omega_\Omega)$ **等价于** 对一切 $k\ge1$ 的 `Lab (N.γ (suc k)) (γᴱ (suc k))` ($k=0$ 就是 `ε₀-label`; 充分性是 `diag-label`, 必要性由 `Lab` 的反演、`l-inv` 与 `Lab-≅` 即得, 纸面, 未编译).

**没有证的:** $k\ge1$ 时 $\gamma_{k+1}$ 的遗传标签, 所以 **BTBO $=\psi_0(\Omega_\Omega)$ 仍是估计.** 缺口精确地是阶段 2: 一般的 $\psi_u$ ($u$ 可数) 的参数里会出现 $\Omega_v$ ($v<u$), 例如 $\gamma^\mathsf E_2$ 的基本列四步后到达的 $\psi_0(\psi_\omega(\Omega_2))$. 翻译它要 (a) 公共的参数层: `lift` 要字面的 $\triangleleft$ 或 `lvl v ≺ᴵ lvl u` 的证据 (经 `tr` 再 `lift`); (b) 派发一致: 树按 `<ᴵ-dec` 在层号上派发, 记号按 `cmpᵀ (ν+1) u` 在项上派发, 二者一致需要 "标准形上 $v<^\mathsf T u\Rightarrow\llbracket v\rrbracket\prec\llbracket u\rrbracket$" (序的对应). 后者是 EBO 标准形理论的核心 (标准形谓词、`fsn` 保持标准形、序的比较引理), EBO §9 明说没做; 而对非标准项它是假的 (树侧的实例是 Uniform 的 `ψ-not-⊑mono`). 只当 $v$ 是 $u$ 的基本列后代时, 证据可以从 $u$ 的形状定理现场造出 (如 $\Omega_{\omega[n]}$ 从 `Ω-shapeω`), 这提示阶段 2 的一条可能的路: 不按语法片段而按 "基本列闭包" 归纳, 证据随形状一起传递; 本文没有走到.

**其他边界.**

- 翻译依赖推导; 同一项的两个纯推导的翻译 $\cong$ (例如 `gΩ g[]` 与 `gψ 1` 字面相同) 只在用到处核对, 没有证一般的唯一性引理.
- 出口刻画 ("纯片段的 `fsn` 只经 `chainMatch` 离开纯片段") 是读代码的结论, 未形式化.
- 本文不改 `src/`、`archive/` 与已有的 Align 文件.
