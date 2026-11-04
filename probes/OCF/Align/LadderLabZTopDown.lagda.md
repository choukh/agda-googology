> **机械克隆, 验收用.** 由 `ScafLadderZTopDown` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.

> **机械克隆.** 由 `TopDown` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 自上而下: 从 EBO 的文法读出统一的符号前缀 (设计草案)

> 自下而上的路线 (Symbolic → Prefix → … → OmegaSq, 约十轮) 每轮修补上一轮的表示, 到 $\psi_0(\Omega_\Omega\cdot\omega^\eta)$ 与 $\psi_0(\Omega_\Omega\cdot\Omega_2)$ 为止, 停在 OmegaSqBase 的 `noSim21`/`low-unlab`. 本文反过来: 从 [EBO](EBO.lagda.md) 的文法 (项 = 主项 $\psi_u(a)$ 之和) 与已编译的全部否定出发, 写出 "成品定义应当长什么样", 并让它通过决定性检验. 这是设计草案: 定义全部编译, 证书与标签只给类型, 期望的定理收在记录 `Expected` 的字段里 (无公设).
>
> 结论先说:
>
> 1. **一种帧.** 自下而上的三种帧 `▹Ω̂` ($\Omega_\Omega=\psi_\Omega(0)$)、`▹ω X` ($\Omega_\Omega\cdot\omega^X=\psi_\Omega(X)$)、`▹Ω̂²` ($\psi_\Omega(\Omega_\Omega)$) 是同一个帧 `Ψ Y` $=\psi_\Omega(Y)$ 的三个实例: `Ψ ∅ᵀ`、`Ψ (tlᵀ … X)`、`Ψ (Ψ ∅ᵀ)` (§5). 指数 $Y$ 本身是符号项, 可任意嵌套.
> 2. **前缀塔 (§2).** 符号项不是数据, 是对一切深度 $d$ 的作用 `Sym φ = ∀ d → A (suc d) φ`, 其中 `A 0 φ = Run φ` 是 OmegaExpBase 的续延栈 `Stk` (加上地板 $\varphi$), `A (d+1) φ` 把深度 $d$ 的前缀映到前缀. 深度 $d+1$ 的前缀就是 "一个 $\psi_\Omega$ 的指数前缀", 它作用于深度 $d$ 的前缀即压入 $\psi_\Omega(\cdot)$. 于是 $\psi_\Omega(Y)$ 在深度 $d$ 上 `= Y (suc d) (Ω̂A d)`: 指数 $Y$ 作用于 "指数为 0 的前缀" $\Omega_\Omega$, 一行, 无特例.
> 3. **地板与非紧的界 (§1, §3).** 每个前缀的类型带地板 `φ : Flr` (它的可数数据所在层号的语法和), 证据是 "每个地板 $K$ 模 $\cong$ 是环境层号的字面子项", 值为带回搬的嵌入 `Emb` (Restrˢ 值的 Sim). 弹出 $\Omega_\Omega$ 时, 闭包的界由**当前环境层号内**的有界三歧逐个比较目标与地板得出: 地板 $\preceq$ 目标时字面就是紧界 $i+1$ (Prefix 的 `rebase`), 否则是 `Mlev (i+1) (M+1)`, 步进证据正是比较结果. 这就是交替不变量: 被比较的下标 (目标与地板) 在环境层号 $\ell$ 内有公共上界, $\ell$ 由链逐步现造.
> 4. **一个折叠 (§4).** `fold d φ cv P t` $=P+t$ (深度 $d$, 尾巴 $t$ 为第 $k$ 层树): 深度 0 是尾巴折叠 (旧 `ψˢ`), 深度 $\ge1$ 是指数折叠 (旧 `ψᵉ′`), 只有后继子句按深度分两种 (输出重复 / 压 $m$ 帧), 不按层号分: 无占位. 停机度量: 只对尾巴树结构递归, 无互递归; 栈、帧、深度都是参数.
> 5. **决定性检验全部 `refl` (§7).** $\psi_0(\Omega_\Omega\cdot2)$ 与 $\psi_0(\Omega_\Omega^2)$ 的前几项与 EBO 的 `walk` 同形; `pathLow ++ [2,0,0]` 处树是 `kl` 而非占位 (`low-tree′`); `low-pop` 处闭包的界是 `Mlev 1 2`, 首点在其中计算第 2 层的帧, 无 `noSim21` 障碍; 单帧与 Prefix 的 `β₀`、`X₂ˢ` 在所有已有的 `kind` 检验点上一致.
> 6. **证书与标签 (§6).** `Goodᴸ`/`forceᴸ`/`LabL` 原样; 新的只有 "好前缀塔" `GoodA d` 与 `GoodSym`. 第 1 阶段的标签定理由两条引理组成: 各深度的 $\Omega_\Omega$ 闭包定理 `goodΩ̂` 与折叠定理 `goodTl` (加上统一支配引理 `dom`); `goodΨ`、`rep→good`、主定理 `label` 在本文中由它们**证明** (§6 `Derived`).
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLabZTopDown where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev)
open import OCF.Align.LadderLabZPrefix using (Z; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; toZ; Ωˢ; _+ˢ_; tr⁻ˢ;
  Restrˢ; restrˢ; resˢ; kind; kl; kc; walkˢ; β₀; X₂ˢ; two)
open Restrˢ
import OCF.Align.EBO as E
open E using (T; natT; fsT; cof; cω; Ωt; 𝟏) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; walk)
open import OCF.Align.LadderLabZSystemOmega using (Occ)
open import OCF.Align.Stage2 using (Ωᵗ; t2; tO)
open import OCF.Align.LadderLabZUniformS using (kd)
open import OCF.Align.LadderLabZDecoupleBase using (ΩΩ)
open import OCF.Align.LadderLabZDecouple using (Idx; lvI)
open import OCF.Align.LadderLabZGoodLBase using (Goodᴸ; forceᴸ; LabL; LabL₊; Ll)
open import OCF.Align.LadderLabZOmegaKBase using (tΩ2)
open import OCF.Align.LadderLabZOmegaExp using (ψΩ₀; tΩ1)
open import OCF.Align.LadderLabZOmegaSqBase using (ψ₂1ˢ; three; Ω₂)
```

## §0 出发点: EBO 的文法与三种旧帧

EBO 的项是主项之和, 主项只有一种 $\psi_u(a)$, $u$ 与 $a$ 都是项. 在 $\psi_0(\Omega_{\Omega+1})$ 之下, 不可数的下标只有 $\Omega$ ($=\Omega_1$), 所以前缀里的每个被加数都是 $\psi_\Omega(\zeta)$, $\zeta<\Omega_{\Omega+1}$ 又是同样形状的项. 自下而上的三种帧都在这里:

| 旧帧 (文件) | EBO 主项 | 指数 $\zeta$ | 本文 |
|---|---|---|---|
| `▹Ω̂` (OmegaExpBase, Prefix 的 `fΩ̂`) | $\Omega_\Omega=\psi_\Omega(0)$ | $0$ | `Ψ ∅ᵀ` |
| `▹ω X`, `▹[ s ] X` (OmegaExpBase, OmegaSqBase) | $\Omega_\Omega\cdot\omega^X=\psi_\Omega(X)$ | 可数树 $X$ | `Ψ (tlᵀ φ cv X)` |
| `▹Ω̂²` (OmegaExpBase) | $\Omega_\Omega\cdot\Omega_\Omega=\psi_\Omega(\Omega_\Omega)$ | $\psi_\Omega(0)$ | `Ψ (Ψ ∅ᵀ)` |

旧路线把三者写成三个特例, 是因为它的栈只有一层: 指数是可数树时用 `ψᵉ` 对树递归, 指数是 $\Omega_\Omega$ 时只在栈顶特殊处理. 一旦指数本身含 $\psi_\Omega$ (例如 $\psi_\Omega(\psi_\Omega(\psi_\Omega(0)))$, 仍在 $\psi_0(\Omega_{\Omega+1})$ 之下), 就需要 "指数的指数" 的栈. 下面的前缀塔把这件事一次做完.

## §1 嵌入与地板

**嵌入.** 旧折叠的 `Simᴵ k ℓ` 把第 $k$ 层的字面子项映到 $\ell$ 的字面子项. 非紧的界要比较目标与地板, 比较结果只给出 $K\cong K'<^\mathsf I\ell$ (Level §2 `lit→ext`: 不能要求字面), 所以嵌入的值改为 `Restrˢ c ℓ`: 代表 $c'\cong c$、$c'<^\mathsf I\ell$ 与回搬 `Ordˢ c′ → Ordˢ c`. 旧的 `Sim` 经 `simE` 嵌入, 回搬是恒等. `mkE e r` 由 $K\cong K'<^\mathsf I c$ 造出整个 $\{\le K\}$ 的嵌入 (回搬用 Prefix 的 `tr⁻ˢ`/`resˢ`).

```agda
Emb : Ordᴵ → Ordᴵ → Set
Emb k ℓ = ∀ {c} → c <ᴵ k → Restrˢ c ℓ

simE : ∀ {k ℓ} → Simᴵ k ℓ → Emb k ℓ
simE σ q = restrˢ (≅ᴵ-refl _) (σ q) (λ x → x)

_∘ᴱ_ : ∀ {a b c} → Emb a b → Emb b c → Emb a c
(σ ∘ᴱ τ) q = restrˢ (≅ᴵ-trans (eqˢ (σ q)) (eqˢ (τ (ltˢ (σ q))))) (ltˢ (τ (ltˢ (σ q))))
                    (λ x → backˢ (σ q) (backˢ (τ (ltˢ (σ q))) x))

mkE : ∀ {K K′ c} → K ≅ᴵ K′ → K′ <ᴵ c → Emb (suc K) c
mkE e r zero    = restrˢ e r (tr⁻ˢ e)
mkE e r (suc q) = restrˢ (eqˢ (resˢ q e)) (<ᴵ-trans (ltˢ (resˢ q e)) r) (backˢ (resˢ q e))
```

**地板.** 前缀里的可数数据 (指数树、尾巴树) 只在被计值时需要嵌入环境层号; 但弹出 $\Omega_\Omega$ 时要知道它们的层号, 才能定闭包的界. 地板是层号的**语法和** `Flr`: 两个地板在压栈时不比较 (那时没有环境层号), 比较推迟到弹栈, 在当时的环境层号内做. 证据 `Ev ℓ φ`: 每个地板项 $K$ 给 `Emb (suc K) ℓ`, 即 $K$ 模 $\cong$ 在 $\ell$ 之下. `_≤ᶠ_` 是语义包含 (证据的反向转换), `liftEv` 沿嵌入搬运证据.

```agda
infixl 5 _⊔_
data Flr : Set where
  fz  : Flr
  fk  : Ordᴵ → Flr
  _⊔_ : Flr → Flr → Flr

Ev : Ordᴵ → Flr → Set
Ev ℓ fz      = ⊤
Ev ℓ (fk K)  = Emb (suc K) ℓ
Ev ℓ (a ⊔ b) = Ev ℓ a × Ev ℓ b

_≤ᶠ_ : Flr → Flr → Set
a ≤ᶠ b = ∀ {ℓ} → Ev ℓ b → Ev ℓ a

liftEv : ∀ {ℓ ℓ′} (φ : Flr) → Emb ℓ ℓ′ → Ev ℓ φ → Ev ℓ′ φ
liftEv fz      τ _       = tt
liftEv (fk K)  τ e       = e ∘ᴱ τ
liftEv (a ⊔ b) τ (x , y) = liftEv a τ x , liftEv b τ y
```

**读法.** 旧设计的帧证据 $z:0<^\mathsf I\ell$ 就是地板 `fk zero` 的字面特例 (`Emb 1 ℓ`); 第 1 层的 `σ1 z` 也落在 `fk zero` 里; `noSim2`/`noSim21` 说的正是 "第 2 层的帧要地板 `fk 1`, 而紧界闭包的环境层号里没有它".

## §2 前缀塔

`Run φ` 是 OmegaExpBase 的 `Stk` 加地板: 前缀在尾巴 $0$ 处、对一切目标 $i$ 与环境层号 $\ell$ 的值 $\psi_i(P+0)$. `A (suc d) φ` 是深度 $d+1$ 的前缀: 作用于任意地板 $fl$ 的深度 $d$ 前缀, 地板增加 $\varphi$. 读法: 深度 $d+1$ 的前缀 $E$ 代表一个 $\psi_\Omega$ 的指数前缀 $\zeta$, $E\,P=P+\psi_\Omega(\zeta)$. 这是按 $d$ 递归的普通函数, 不是数据类型, 没有正性问题.

```agda
Run : Flr → Set
Run φ = ∀ {i ℓ} → Ev ℓ φ → i <ᴵ ℓ → Ordˢ i

A : ℕ → Flr → Set
A zero    φ = Run φ
A (suc d) φ = ∀ {fl} → A d fl → A d (fl ⊔ φ)

wk : ∀ d {φ ψ} → φ ≤ᶠ ψ → A d φ → A d ψ
wk zero    le x ev p = x (le ev) p
wk (suc d) le x P    = wk d (λ { (u , v) → u , le v }) (x P)
```

**构造器.** 折叠的结果在每个深度上要能做四件事: $\mathbb N$-极限、$\Omega_{j+1}$-共尾 (`limᵢ`)、第 $\ge1$ 层的符号闭包 (`ŝ`)、第 0 层的待计值链 (`ĉᴸ`). 深度 $d+1$ 一律逐点 (对作用的对象), 深度 0 才真正造树. `limᵢA` 的深度 0 子句就是旧折叠的派发: 在**环境层号 $\ell$ 内**比较节点层号的代表与目标 (`<ᴵ-dec`), 穿透或沿第 $j'$ 层的链折叠, 链点 `h x ev (ltˢ R)` 是同一前缀在目标 $j'$ 处的值 (规则 6, EBO 的 $b[\gamma_k]$ 含整个前缀). 深度 $\ge1$ 不派发: $\psi_\Omega$ 之下可数的 $j+1<\Omega$ 总是穿透, 派发推迟到最终在深度 0 计值时.

```agda
limA : ∀ d {φ} → (ℕ → A d φ) → A d φ
limA zero    F ev p = Ord₊ˢ.lim (λ m → F m ev p)
limA (suc d) F P    = limA d (λ m → F m P)

limᵢA : ∀ d {φ j} → (∀ {ℓ} → Ev ℓ φ → Restrˢ j ℓ) → (Ordˢ j → A d φ) → A d φ
limᵢA zero ac h ev p with <ᴵ-dec (ltˢ (ac ev)) p
... | injᵃ (via e r) = Ord₊ˢ.limᵢ r (λ y → h (backˢ (ac ev) (tr⁻ˢ e (outˢ (<→◃ r) y))) ev p)
... | injᵇ _ = Ord₊ˢ.lim (λ m → h (backˢ (ac ev) (iter (λ x → h (backˢ (ac ev) x) ev (ltˢ (ac ev))) (Ωˢ _) m)) ev p)
... | injᶜ _ = Ord₊ˢ.lim (λ m → h (backˢ (ac ev) (iter (λ x → h (backˢ (ac ev) x) ev (ltˢ (ac ev))) (Ωˢ _) m)) ev p)
limᵢA (suc d) ac h P = limᵢA d (λ ev → ac (proj₂ ev)) (λ x → h x P)

ŝA : ∀ d {φ} (c : Ordᴵ) → A d φ → ((η : Ordᴵ) → c ⊑ᴵ η → A d φ) → A d φ
ŝA zero    c t g ev p = Ord₊ˢ.ŝ c (t ev p) (λ η e → g η e ev p)
ŝA (suc d) c t g P    = ŝA d c (t P) (λ η e → g η e P)

ĉA : ∀ d {φ} (c : Ordᴵ) → Z → ((η : Ordᴵ) → c ⊑ᴵ η → Z) → A d φ → ((η : Ordᴵ) → c ⊑ᴵ η → A d φ) → A d φ
ĉA zero    c t₀ g o₀ o ev p = Ord₊ˢ.ĉᴸ c t₀ g (o₀ ev p) (λ η e → o η e ev p)
ĉA (suc d) c t₀ g o₀ o P    = ĉA d c t₀ g (o₀ P) (λ η e → o η e P)
```

## §3 闭包与非紧的界

**界.** 弹出 $\Omega_\Omega$ 的闭包要一个界 $c$: 目标 $i$ 字面地在 $c$ 之下 (`tg`), 地板整体嵌入 $c$ (`evc`). `Top` 记录目标与已看过的地板中的大者: `here` (大者就是目标, 字面), `above` (大者 $M$ 是某个地板在 $\ell$ 内的字面代表, $i\prec^\mathsf I M$). `ins` 把一个地板 $K$ 并进来: 在 $\ell$ 内用 `<ᴵ-dec` 比较 $K$ 的代表与当前大者, 两者都是 $\ell$ 的字面子项. 这里是交替不变量被兑现的地方: 被比较的只有目标与地板, 它们的公共上界就是当前的环境层号 $\ell$, 而 $\ell$ 由上层的闭包 (分支在 `Mlev c (suc η) e`, $\eta$ 是证书给的链点层号) 现造. 符号下标 $\Omega$ 从不参与比较.

```agda
data Top (i ℓ : Ordᴵ) (φ : Flr) : Set where
  here  : Ev (suc i) φ → Top i ℓ φ
  above : ∀ {M} → M <ᴵ ℓ → i ≺ᴵ M → Ev (suc M) φ → Top i ℓ φ

mapTop : ∀ {i ℓ φ ψ} → ψ ≤ᶠ φ → Top i ℓ φ → Top i ℓ ψ
mapTop f (here ev)       = here (f ev)
mapTop f (above m im ev) = above m im (f ev)

ins : ∀ {i ℓ φ K} → i <ᴵ ℓ → Top i ℓ φ → Emb (suc K) ℓ → Top i ℓ (φ ⊔ fk K)
ins {φ = φ} p (here ev) ek with <ᴵ-dec (ltˢ (ek zero)) p
... | injᵃ (via e r) = here (ev , mkE (≅ᴵ-trans (eqˢ (ek zero)) e) (suc r))
... | injᵇ (via e r) = above (ltˢ (ek zero)) (via e r) (liftEv φ (mkE e (suc r)) ev , mkE (eqˢ (ek zero)) zero)
... | injᶜ e         = here (ev , mkE (≅ᴵ-trans (eqˢ (ek zero)) e) zero)
ins {φ = φ} p (above m im ev) ek with <ᴵ-dec (ltˢ (ek zero)) m
... | injᵃ (via e r) = above m im (ev , mkE (≅ᴵ-trans (eqˢ (ek zero)) e) (suc r))
... | injᵇ (via e r) = above (ltˢ (ek zero)) (≺ᴵ-trans im (via e r)) (liftEv φ (mkE e (suc r)) ev , mkE (eqˢ (ek zero)) zero)
... | injᶜ e         = above m im (ev , mkE (≅ᴵ-trans (eqˢ (ek zero)) e) zero)

accT : ∀ {i ℓ φ₁} → i <ᴵ ℓ → Top i ℓ φ₁ → (φ₂ : Flr) → Ev ℓ φ₂ → Top i ℓ (φ₁ ⊔ φ₂)
accT p t fz      _       = mapTop (λ x → x , tt) t
accT p t (fk K)  ek      = ins p t ek
accT p t (a ⊔ b) (x , y) = mapTop (λ { ((u , v) , w) → u , (v , w) }) (accT p (accT p t a x) b y)

record Bnd (i : Ordᴵ) (φ : Flr) : Set where
  constructor bnd
  field
    c   : Ordᴵ
    tg  : i <ᴵ c
    evc : Ev c φ
open Bnd

toBnd : ∀ {i ℓ φ} → Top i ℓ φ → Bnd i φ
toBnd {i} (here ev) = bnd (suc i) zero ev
toBnd {i} {φ = φ} (above {M} m (via e r) ev) =
  bnd (Mlev (suc i) (suc M) (s⊑ e (suc r))) (lim 0 zero) (liftEv φ (simE (λ q → lim 1 q)) ev)

bound : ∀ {i ℓ} (φ : Flr) → Ev ℓ φ → i <ᴵ ℓ → Bnd i φ
bound φ ev p = toBnd (mapTop proj₂ (accT p (here tt) φ ev))
```

**读法.** 界是 $\max(i,F)+1$: `here` 时字面为 `suc i`, 与 Prefix `rebase` 的紧界逐字相同 (所以纯 $\Omega_\Omega$ 栈的闭包与旧的同界, §7); `above` 时为 `Mlev (suc i) (suc M) _`, 即 $\lim[i+1, M+1, M+1,\dots]$, 步进 $i+1\sqsubseteq M+1$ 就是比较结果 $i\prec M$. 目标经第 0 项、地板经第 1 项字面地进入; 不需要对输出做 `tr⁻ˢ`. 不比较极限层号本身 (那是 [Barrier](../Barrier.lagda.md) 与 Stage2 `dec→WLPO` 的领地): 只比较 $\ell$ 的两个字面子项.

**闭包.** `cloA d first branch` $=P+\Omega_\Omega$ 的弹出: 深度 0 造 `ŝ c t₀ g`, $t_0$ 是 `first` 在界 $c$ 上的值, $g\,\eta\,e$ 是 `branch η` 在 `Mlev c (suc η) _` 上的值; 深度 $\ge1$ 逐点 (地板经结合律搬运). 分支的环境层号取 $\eta+1$ 而不是旧的 $\eta$: 分支尾巴 $\Omega_\eta$ 的地板是 $\eta$ 本身, 要 $\eta\prec^\mathsf I$ 环境层号; `Mlev c η e` 里 $\eta$ 只是 $\triangleleft$-前驱, 不是字面子项.

```agda
⊑suc : ∀ {c η} → c ⊑ᴵ η → c ⊑ᴵ suc η
⊑suc e = ⊑ᴵ-trans e (Sim→⊑ᴵ (λ q → suc q))

cloA : ∀ d {φ} → A d (φ ⊔ fk zero) → ((η : Ordᴵ) → A d (φ ⊔ fk η)) → A d (φ ⊔ fk zero)
cloA zero {φ} t g {i} ev p =
  Ord₊ˢ.ŝ (c B) (t (evc B) (tg B))
          (λ η e → g η {ℓ = Mlev (c B) (suc η) (⊑suc e)}
                     (liftEv φ (simE (λ q → lim 0 q)) (proj₁ (evc B)) , simE (λ q → lim 1 q)) (lim 0 (tg B)))
  where B = bound (φ ⊔ fk zero) ev p
cloA (suc d) {φ} t g {fl} P =
  wk d (λ { (u , (v , w)) → (u , v) , w })
       (cloA d {fl ⊔ φ} (wk d (λ { ((u , v) , w) → u , (v , w) }) (t P))
                        (λ η → wk d (λ { ((u , v) , w) → u , (v , w) }) (g η P)))
```

## §4 统一折叠

`fold d φ cv P t` 表示 $P+t$: $P$ 是深度 $d$ 的前缀 (地板 $fl$), $t$ 是第 $k$ 层的树, 其数据由地板 $\varphi$ 经 `cv` 嵌入. 子句:

- $t=0$: $P$ 本身.
- $t=a+1$: 深度 0 是 $\psi_i(P+a+1)[m]=\psi_i(P+a)\cdot m$ (输出重复); 深度 $d+1$ 是 $\psi_\Omega(\zeta+a+1)[m]=\psi_\Omega(\zeta+a)\cdot m$, 即在深度 $d$ 的前缀 $Q$ 上压 $m$ 个帧 `fold (suc d) φ cv P a` (`repA`). **不按层号 $k$ 分情况**: 第 0、1、2、… 层的后继同一行 (旧 `ψᵉ′` 在第 $\ge2$ 层是占位).
- `lim`/`limᵢ`/`ŝ`/`ĉᴸ`: 交给 §2 的构造器; `limᵢ` 的嵌入由地板证据给出.
- `up zero x` ($k=k'+1$): 地板收紧为 `fk k′` (证据就是 `cv`), 结果再放宽回 $\varphi$. 于是在 $x$ 内压的帧带紧地板 $k'$ (OmegaSq 的 `TΩ₂` 中第 1 层的帧带地板 0, 与旧的 `σ1` 同). `up (self n) x`: 极限父层, 地板不变 (极限层号无法收紧: 它不是环境层号的字面子项).

停机: `fold` 只对尾巴树结构递归; `repA` 是先定义的独立函数, `fold (suc d) φ cv P a` 作为值传给它 (旧 `ψᵉ → rep → ψᵉ` 的环在这里不出现在调用图里). 无互递归, 检查器一次通过. 栈、帧、深度 $d$ 都只是参数.

```agda
repA : ∀ d {fl ψ} → A d fl → A (suc d) ψ → ℕ → A d (fl ⊔ ψ)
repA d Q fr zero    = wk d proj₁ Q
repA d Q fr (suc m) = wk d (λ { (u , v) → (u , v) , v }) (fr (repA d Q fr m))

fold : ∀ d {fl k} (φ : Flr) → (∀ {ℓ} → Ev ℓ φ → Emb k ℓ) → A d fl → Ordˢ k → A d (fl ⊔ φ)
fold d φ cv P Ord₊ˢ.zero = wk d proj₁ P
fold zero    φ cv P (Ord₊ˢ.suc a) ev p = Ord₊ˢ.lim (iter (fold zero φ cv P a ev p +ˢ_) Ord₊ˢ.zero)
fold (suc d) φ cv P (Ord₊ˢ.suc a) Q    = limA d (λ m → repA d Q (fold (suc d) φ cv P a) m)
fold d φ cv P (Ord₊ˢ.lim f) = limA d (λ m → fold d φ cv P (f m))
fold d φ cv P (Ord₊ˢ.limᵢ q f) = limᵢA d (λ ev → cv (proj₂ ev) q) (λ x → fold d φ cv P (f (intoˢ (<→◃ q) x)))
fold d φ cv P (Ord₊ˢ.up zero x) = wk d (λ { (u , v) → u , cv v }) (fold d (fk _) (λ e q → e (suc q)) P x)
fold d φ cv P (Ord₊ˢ.up (self n) x) = fold d φ (λ e q → cv e (lim n q)) P x
fold d {k = zero}    φ cv P (Ord₊ˢ.ŝ c t₀ g) =
  ĉA d c (toZ t₀) (λ η e → toZ (g η e)) (fold d φ cv P t₀) (λ η e → fold d φ cv P (g η e))
fold d {k = suc _}   φ cv P (Ord₊ˢ.ŝ c t₀ g) = ŝA d c (fold d φ cv P t₀) (λ η e → fold d φ cv P (g η e))
fold d {k = lim _ _} φ cv P (Ord₊ˢ.ŝ c t₀ g) = ŝA d c (fold d φ cv P t₀) (λ η e → fold d φ cv P (g η e))
fold d φ cv P (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) = ĉA d c t₀ g (fold d φ cv P o₀) (λ η e → fold d φ cv P (o η e))
```

**$\Omega_\Omega$ 在一切深度.** `Ω̂A d P` $=P+\Omega_\Omega$: 闭包, 第 0 点是 $P+\Omega_1$ (尾巴 $\Omega_1$, 地板 `fk 0`), 在 $\eta$ 处是 $P+\Omega_\eta$ (地板 `fk η`). 深度 0 是旧的 `▹Ω̂`; 深度 1 (指数前缀上加 $\Omega_\Omega$) 是旧的 `▹Ω̂²` 的弹出; 深度 $\ge2$ 旧路线没有.

```agda
Ω̂A : ∀ d → A (suc d) (fk zero)
Ω̂A d {fl} P = cloA d {fl} (fold d (fk zero) (λ e → e) P (Ωˢ (suc zero)))
                         (λ η → fold d (fk η) (λ e q → e (suc q)) P (Ωˢ η))
```

## §5 符号项与统一的帧

**符号项.** `Sym φ` 对一切深度给出作用. 四个构造: 零 `∅ᵀ`, 可数尾巴 `tlᵀ`, 和 `_⊕_` (作用的复合), 与唯一的帧 `Ψ`. `Ψ Y d P = Y (suc d) (Ω̂A d) P`: 在深度 $d+1$ 上, $Y$ 作用于 "指数为 0 的前缀" $\Omega_\Omega$ (`Ω̂A d`), 得到 "指数为 $Y$ 的前缀", 再作用于 $P$. 这是 "符号下标的折叠" 的全部: 指数里的 $\psi_\Omega$ 让深度加一, 深度只出现在类型里, 不出现在任何递归里. 计值: `ψᵀ X` 把 $X$ 作用于空前缀 (`∅ᴿ`: $\psi_i(0)=\Omega_i$).

```agda
Sym : Flr → Set
Sym φ = ∀ d → A (suc d) φ

∅ᵀ : Sym fz
∅ᵀ d P = wk d proj₁ P

tlᵀ : ∀ {k} (φ : Flr) → (∀ {ℓ} → Ev ℓ φ → Emb k ℓ) → Ordˢ k → Sym φ
tlᵀ φ cv t d P = fold d φ cv P t

Ψ : ∀ {φ} → Sym φ → Sym (fk zero ⊔ φ)
Ψ Y d P = Y (suc d) (Ω̂A d) P

infixl 6 _⊕_
_⊕_ : ∀ {φ ψ} → Sym φ → Sym ψ → Sym (φ ⊔ ψ)
(X ⊕ Y) d P = wk d (λ { (u , (v , w)) → (u , v) , w }) (Y d (X d P))

∅ᴿ : Run fz
∅ᴿ {i} _ p = Ωˢ i

ψᵀ : ∀ {φ} → Sym φ → Run (fz ⊔ φ)
ψᵀ X = X zero ∅ᴿ
```

**文法 (数据).** 符号项的语法 `Syn` 逐字是 EBO 的文法: 零、可数尾巴 (任意层 $k$ 的树)、主项帧 `ψ̇ u ζ` $=\psi_u(\zeta)$、和. 下标宇宙 `Sub` 在第 1 阶段只有 `Ω̇`; §9 说明后续阶段加什么. 可数尾巴的地板由层号读出 (`flo`: 后继层 $k+1$ 的地板是 $k$, 紧; 极限层是自身). 解释 `⟦_⟧` 是对语法的结构递归, 三种旧帧是 `ψ̇ Ω̇ 0̇`、`ψ̇ Ω̇ (tl X)`、`ψ̇ Ω̇ (ψ̇ Ω̇ 0̇)`.

```agda
data Sub : Set where
  Ω̇ : Sub

infixl 6 _⊹_
data Syn : Set where
  0̇   : Syn
  tl  : ∀ {k} → Ordˢ k → Syn
  ψ̇   : Sub → Syn → Syn
  _⊹_ : Syn → Syn → Syn

flo : Ordᴵ → Flr
flo zero      = fz
flo (suc k)   = fk k
flo (lim f s) = fk (lim f s)

cvFlo : ∀ k {ℓ} → Ev ℓ (flo k) → Emb k ℓ
cvFlo zero      _ ()
cvFlo (suc k)   e q = e q
cvFlo (lim f s) e q = e (suc q)

⟦_⟧ : Syn → Σ Flr Sym
⟦ 0̇ ⟧        = fz , ∅ᵀ
⟦ tl {k} t ⟧ = flo k , tlᵀ (flo k) (cvFlo k) t
⟦ ψ̇ Ω̇ Y ⟧    = fk zero ⊔ proj₁ ⟦ Y ⟧ , Ψ (proj₂ ⟦ Y ⟧)
⟦ X ⊹ Y ⟧    = proj₁ ⟦ X ⟧ ⊔ proj₁ ⟦ Y ⟧ , proj₂ ⟦ X ⟧ ⊕ proj₂ ⟦ Y ⟧
```

## §6 证书与标签的类型, 期望的定理

**不变的部分.** 证书 `Goodᴸ` (只在带标签的计值点量化, 标签列是字段)、`forceᴸ`、关系式标签 `LabL` (带 `Idx`, 比较经 `Lab-oc`/`Lab-uniq` 现场做) 原样使用: 折叠的输出仍是 `Ordˢ zero`, 经 `toZ` 交给 `Goodᴸ`. `Rep X x` 把符号项与 EBO 项对上 (尾巴由 `LabL` 标记).

```agda
ψΩᵗ : T → T
ψΩᵗ ζ = ψᵗ Ωᵗ ζ ∷ []

ψ₀ᵗ : T → T
ψ₀ᵗ x = ψᵗ [] x ∷ []

Lab₀ : Ordˢ zero → T → Set
Lab₀ x t = Σ (Goodᴸ (toZ x)) λ G → Lab (forceᴸ _ G) t

data Rep : ∀ {φ} → Sym φ → T → Set where
  r∅  : Rep ∅ᵀ []
  rΨ  : ∀ {φ} {Y : Sym φ} {y} → Rep Y y → Rep (Ψ Y) (ψΩᵗ y)
  r⊕  : ∀ {φ ψ} {X : Sym φ} {Y : Sym ψ} {x y} → Rep X x → Rep Y y → Rep (X ⊕ Y) (x ++ y)
  rtl : ∀ {k} {t : Ordˢ k} {y} → LabL t y → Rep (tlᵀ (flo k) (cvFlo k) t) y
```

**好前缀塔.** 深度 0: `GoodR P ps` 是 OmegaExpBase `Goodˢ` 的 `HypW`/`Hyp0` (前缀 $ps$, 任意带标签目标), 外加地板的标签 `FlrLab`: 每个地板项被某个在 $ps$ 中出现的下标 $w$ 支配 ($K\sqsubseteq^\mathsf I$ `lvI Iw`). 深度 $d+1$: $E$ 好且指数为 $\zeta$, 指它把每个好的深度 $d$ 前缀 $(P,\pi)$ 变成好的 $(E\,P,\ \pi+\psi_\Omega(\zeta))$. `GoodSym X x`: 在每个深度上把 $(P,\pi)$ 变成 $(X\,d\,P,\ \pi+x)$.

```agda
data InF (K : Ordᴵ) : Flr → Set where
  ink : InF K (fk K)
  inl : ∀ {a b} → InF K a → InF K (a ⊔ b)
  inr : ∀ {a b} → InF K b → InF K (a ⊔ b)

FlrLab : Flr → T → Set
FlrLab φ ps = ∀ {K} → InF K φ → Σ T λ w → Σ (Idx w) λ Iw → (K ⊑ᴵ lvI Iw) × Occ w ps

record GoodR {φ} (P : Run φ) (ps : T) : Set where
  field
    fl : FlrLab φ ps
    hW : ∀ {i ℓ w} (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
         LabL₊ i Ll (P ev p) (ψᵗ w ps ∷ [])
    h0 : ∀ {ℓ} (ev : Ev ℓ φ) (p : zero <ᴵ ℓ) → NF₁ (ψ₀ᵗ ps) → Lab₀ (P ev p) (ψ₀ᵗ ps)

GoodA : ∀ d {φ} → A d φ → T → Set
GoodA zero    P ps = GoodR P ps
GoodA (suc d) E ζ  = ∀ {fl} {P : A d fl} {π} → GoodA d P π → GoodA d (E P) (π ++ ψΩᵗ ζ)

GoodSym : ∀ {φ} → Sym φ → T → Set
GoodSym X x = ∀ d {fl} {P : A d fl} {π} → GoodA d P π → GoodA d (X d P) (π ++ x)
```

**期望的定理.** 第 1 阶段 ($\psi_0(\Omega_{\Omega+1})$ 之下) 的全部内容是下面七个字段. $\psi_0(\Omega_{\Omega+1})$ 本身的树 `TOᵀ` 是 §9 的对角线, 要用到 §7 的常量, 所以记录写成以它为参数的模块 `Stage1`, 在 §9 末尾实例化.

- `good∅ᴿ`: 空前缀 ($\psi_i(0)=\Omega_i$) 好. 已有: GoodLBase §4 `emptyᴸ` 与 OmegaExpBase `Good∅`.
- `good∅`, `good⊕`: 零与和. 纯搬运 (`wk` 与 `++` 的结合律).
- **`goodΩ̂ d`** (闭包定理, 每个深度一条, 对一切帧统一): $P$ 好 ⟹ $P+\Omega_\Omega$ 好. 深度 0 是 GoodLBase 的 `popL`/`pop0ᴸ` 与 OmegaExpBase 的 `GoodΩ`, 但界换成 §3 的 `bound`; 深度 1 是 OmegaExpBase/OmegaSq 的 `▹Ω̂²` 情形 (缺的 `BranchΩ` 正是它的分支字段); 深度 $\ge2$ 新.
- **`goodTl`** (折叠定理): `LabL t y` ⟹ `tlᵀ … t` 好. 深度 0 是 `PreW`/`Pre0` (`PreS₊`/`Pre0S₊`), 深度 1 是 `WE₀`/`WE₁`/`ZE₀`/`ZE₁` 与 `GoodE₀`/`GoodE₁` 的合并, 对一切层号的指数.
- **`dom`** (统一支配引理): 目标带标签 ($i\cong$ `lvI I₀`)、地板带标签时, `bound` 给出的界被某个出现在前缀里 (或就是目标下标) 的 $w$ 支配: $c\sqsubseteq^\mathsf I$ `suc (lvI Iw)`. 这正是 `LabL` 的 `gŝ` 行要的地板字段, 也是 `domS` (地板只有 $0$ 时) 的推广.
- `topO`: $\psi_0(\Omega_{\Omega+1})$ 的标签.

```agda
module Stage1 (TOᵀ : Ordˢ zero) where

  record Expected : Set₁ where
    field
      good∅ᴿ : GoodR ∅ᴿ []
      good∅  : GoodSym ∅ᵀ []
      good⊕  : ∀ {φ ψ} {X : Sym φ} {Y : Sym ψ} {x y} → GoodSym X x → GoodSym Y y → GoodSym (X ⊕ Y) (x ++ y)
      goodΩ̂  : ∀ d → GoodA (suc d) (Ω̂A d) []
      goodTl : ∀ {k} {t : Ordˢ k} {y} → LabL t y → GoodSym (tlᵀ (flo k) (cvFlo k) t) y
      dom    : ∀ {φ ps i ℓ w₀} (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (I₀ : Idx w₀) → i ≅ᴵ lvI I₀ → FlrLab φ ps →
               Σ T λ w → Σ (Idx w) λ Iw → (c (bound φ ev p) ⊑ᴵ suc (lvI Iw)) × (Occ w ps ⊎ w ≡ w₀)
      topO   : Lab₀ TOᵀ tO
```

**由期望的定理证明的部分.** 帧的闭包定理不是新字段: `goodΨ` 一行由 `goodΩ̂` 得到 (帧的定义就是 "指数作用于 $\Omega_\Omega$", 闭包定理随之是 "指数的好性作用于 $\Omega_\Omega$ 的好性"). 主标签定理 `label`: 对一切表示 EBO 项 $x$ 的符号项, $\psi_0(x)$ 的计值树带遗传标签 (在 `NF₁` 下), 对一切环境层号与地板证据. 证明是对 `Rep` 的结构递归, 再取深度 0 的 `h0`; `[] ++ x` 定义性地是 $x$.

```agda
  module Derived (Ex : Expected) where
    open Expected Ex

    goodΨ : ∀ {φ} {Y : Sym φ} {y} → GoodSym Y y → GoodSym (Ψ Y) (ψΩᵗ y)
    goodΨ GY d GP = GY (suc d) (goodΩ̂ d) GP

    rep→good : ∀ {φ} {X : Sym φ} {x} → Rep X x → GoodSym X x
    rep→good r∅        = good∅
    rep→good (rΨ r)    = goodΨ (rep→good r)
    rep→good (r⊕ r r′) = good⊕ (rep→good r) (rep→good r′)
    rep→good (rtl l)   = goodTl l

    label : ∀ {φ} {X : Sym φ} {x} → Rep X x → NF₁ (ψ₀ᵗ x) → ∀ {ℓ} (ev : Ev ℓ (fz ⊔ φ)) (z : zero <ᴵ ℓ) →
            Lab₀ (ψᵀ X ev z) (ψ₀ᵗ x)
    label r nf ev z = GoodR.h0 (rep→good r zero good∅ᴿ) ev z nf
```

**读法.** 自下而上的定理清单 (`Tk-label`, `Tω-label`, `Tη-label`, `TΩ₂-label`, `TΩ2-cond`) 都是 `label` 对特定 `Rep` 的实例; `TΩ2-cond` 的前提 `BranchΩ` 是 `goodΩ̂ 1` 的分支字段. `GoodR` 不含旧 `Goodˢ` 的自互模拟 `S ≈ˢ S`: 那是证明里搬运 `Lab-uniq` 用的辅助, 在关系式标签下可由标签推出, 不必是定义的一部分 (见 §11 边界).

## §7 决定性检验

**常量.** 环境层号与嵌入. `e11` 等是字面 `Sim` 的嵌入.

```agda
one : Ordᴵ
one = suc zero

e11 : Emb one one
e11 = simE (λ q → q)

e12 : Emb one two
e12 = simE (λ q → suc q)

e22 : Emb two two
e22 = simE (λ q → q)

e13 : Emb one three
e13 = simE (λ q → suc (suc q))

e23 : Emb two three
e23 = simE (λ q → suc q)

bndOf : Ordˢ zero → Ordᴵ
bndOf (Ord₊ˢ.ŝ c _ _) = c
bndOf _               = zero

term : Ordᴵ → ℕ → Ordᴵ
term (lim f s) n = f n
term x         n = x
```

**检验 1: $\psi_0(\Omega_\Omega\cdot2)$.** 树 `ψᵀ (Ψ ∅ᵀ ⊕ Ψ ∅ᵀ)`, 环境层号 1. 顶层是界 1 的闭包 (Stage2 的规则 6 外层: 链点由证书给); 第 0 点与 EBO 的 `fsn t2 0` $=\psi_0(\Omega_\Omega+\Omega_1)$ 同为 $\omega$-共尾, 再下一步 $\psi_0(\Omega_\Omega+1)$, 再 $[1]$ 是 $\psi_0(\Omega_\Omega)$, 即又一个界 1 的闭包. Stage2 的 `diag2-fs` (链 $\gamma'$) 的第 $n\ge1$ 项要强制计值, 是证书的事 (GoodL 的 `T2-label`).

```agda
T2ᵀ : Ordˢ zero
T2ᵀ = ψᵀ (Ψ ∅ᵀ ⊕ Ψ ∅ᵀ) (tt , ((e11 , tt) , (e11 , tt))) zero

_ : kind T2ᵀ ≡ kc one
_ = refl
_ : walk t2 (0 ∷ []) ≡ ψᵗ [] (ΩΩ ∷ Ωt (natT 1)) ∷ []
_ = refl
_ : cof (walk t2 (0 ∷ [])) ≡ cω
_ = refl
_ : kind (walkˢ T2ᵀ (0 ∷ [])) ≡ kl
_ = refl
_ : walk t2 (0 ∷ 0 ∷ []) ≡ ψᵗ [] (ΩΩ ∷ 𝟏 ∷ []) ∷ []
_ = refl
_ : kind (walkˢ T2ᵀ (0 ∷ 0 ∷ [])) ≡ kl
_ = refl
_ : walk t2 (0 ∷ 0 ∷ 1 ∷ []) ≡ ψᵗ [] (ΩΩ ∷ []) ∷ []
_ = refl
_ : kind (walkˢ T2ᵀ (0 ∷ 0 ∷ 1 ∷ [])) ≡ kc one
_ = refl
```

**检验 2: $\psi_0(\Omega_\Omega^2)=\psi_0(\psi_\Omega(\Omega_\Omega))$.** 树 `ψᵀ (Ψ (Ψ ∅ᵀ))`: 指数是符号项 $\Omega_\Omega$, 深度 2 的作用, 无 `▹Ω̂²` 特例. 顶层闭包 (界 1), 第 0 点 $t_{\Omega1}=\psi_0(\psi_\Omega(\Omega_1))$ 是 $\omega$-共尾, $[0][0]$ 是 $\psi_0(\psi_\Omega(1))$, 再 $[1]$/$[2]$ 是 $\psi_0(\Omega_\Omega)$/$\psi_0(\Omega_\Omega\cdot2)$, 都是界 1 的闭包, 与 EBO 逐项同形.

```agda
TΩ2ᵀ : Ordˢ zero
TΩ2ᵀ = ψᵀ (Ψ (Ψ ∅ᵀ)) (tt , (e11 , (e11 , tt))) zero

_ : kind TΩ2ᵀ ≡ kc one
_ = refl
_ : walk tΩ2 (0 ∷ []) ≡ tΩ1
_ = refl
_ : cof tΩ1 ≡ cω
_ = refl
_ : kind (walkˢ TΩ2ᵀ (0 ∷ [])) ≡ kl
_ = refl
_ : walk tΩ2 (0 ∷ 0 ∷ []) ≡ ψΩ₀ (natT 1)
_ = refl
_ : kind (walkˢ TΩ2ᵀ (0 ∷ 0 ∷ [])) ≡ kl
_ = refl
_ : walk tΩ2 (0 ∷ 0 ∷ 1 ∷ []) ≡ ψᵗ [] (ΩΩ ∷ []) ∷ []
_ = refl
_ : kind (walkˢ TΩ2ᵀ (0 ∷ 0 ∷ 1 ∷ [])) ≡ kc one
_ = refl
_ : walk tΩ2 (0 ∷ 0 ∷ 2 ∷ []) ≡ ψᵗ [] (ΩΩ ∷ ΩΩ ∷ []) ∷ []
_ = refl
_ : kind (walkˢ TΩ2ᵀ (0 ∷ 0 ∷ 2 ∷ [])) ≡ kc one
_ = refl
```

**检验 3: 低目标帧 (`pathLow ++ [2,0,0]`).** OmegaSqBase §1: $t_{\Omega2}$ 沿 `pathLow` 到 $\psi_0(\psi_\Omega(\psi_2(1)))$ (经过第 1 个链点, 要强制计值), 所以与 OmegaSqBase §3 一样直接造这一点的树: 指数是 OmegaSqBase 的 `ψ₂1ˢ` (第 2 层的树), 地板 `fk 1`, 环境层号 3. 再走 $[2,0,0]$ 到 $\psi_0(\psi_\Omega(\Omega_2+1))$: 旧折叠在这里是占位 $0$ (`low-tree : … ≡ kz`), 统一折叠是 $\omega$-共尾的极限 (规则 4: 压 $m$ 个第 2 层指数的帧), 与 EBO 的 `low-cof` 一致.

```agda
lowᵀ : Ordˢ zero
lowᵀ = ψᵀ (Ψ (tlᵀ (fk one) (λ e → e) ψ₂1ˢ)) (tt , (e13 , e23)) (suc (suc zero))

_ : kind (walkˢ lowᵀ (2 ∷ [])) ≡ kl
_ = refl
_ : kind (walkˢ lowᵀ (2 ∷ 0 ∷ [])) ≡ kl
_ = refl

low-tree′ : kind (walkˢ lowᵀ (2 ∷ 0 ∷ 0 ∷ [])) ≡ kl
low-tree′ = refl
```

**检验 4: `low-pop` 处的闭包.** 再走 $[2,0,0,1]$ 到 $\psi_0(\psi_\Omega(\Omega_2)+\Omega_\Omega)$ (OmegaSqBase 的 `low-pop`): 第 2 层指数的帧之上弹出 $\Omega_\Omega$. 闭包的界是 `Mlev 1 2 _` (`term` 读出第 0、1 项: 目标 0 经 $1$ 进入, 地板 1 经 $2$ 进入), 即 $\max(0,1)+1$; 紧界会是 1, 那里要 `Simᴵ 2 1` (`noSim21`). 首点 $\psi_0(\psi_\Omega(\Omega_2)+\Omega_1)$ 在这个界上计算, 再走 $[0]$、$[1]$ 弹出第 2 层的帧 $\psi_0(\psi_\Omega(\Omega_2))$, 它的 $\Omega_2$ 沿第 1 层的链折叠 (链点目标 1 $<^\mathsf I$ 界), 再 $[0]$ 是 $\psi_0(\psi_\Omega(\Omega_1))$: 全部非占位, 与 EBO 侧逐项同形. `sim2` 说明界里放得下第 2 层.

```agda
popᵀ : Ordˢ zero
popᵀ = walkˢ lowᵀ (2 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 1 ∷ [])

lpᵗ : T
lpᵗ = ψᵗ [] (ψᵗ Ωᵗ Ω₂ ∷ ΩΩ ∷ []) ∷ []

_ : term (bndOf popᵀ) 0 ≡ one
_ = refl
_ : term (bndOf popᵀ) 1 ≡ two
_ = refl

sim2 : ∀ {s} → Simᴵ two (Mlev one two s)
sim2 q = lim 1 q

_ : walk lpᵗ (0 ∷ []) ≡ ψᵗ [] (ψᵗ Ωᵗ Ω₂ ∷ ψᵗ (natT 1) [] ∷ []) ∷ []
_ = refl
_ : kind (walkˢ popᵀ (0 ∷ [])) ≡ kl
_ = refl
_ : walk lpᵗ (0 ∷ 0 ∷ []) ≡ ψᵗ [] (ψᵗ Ωᵗ Ω₂ ∷ 𝟏 ∷ []) ∷ []
_ = refl
_ : kind (walkˢ popᵀ (0 ∷ 0 ∷ [])) ≡ kl
_ = refl
_ : walk lpᵗ (0 ∷ 0 ∷ 1 ∷ []) ≡ ψᵗ [] (ψᵗ Ωᵗ Ω₂ ∷ []) ∷ []
_ = refl
_ : cof (walk lpᵗ (0 ∷ 0 ∷ 1 ∷ [])) ≡ cω
_ = refl
_ : kind (walkˢ popᵀ (0 ∷ 0 ∷ 1 ∷ [])) ≡ kl
_ = refl
_ : walk lpᵗ (0 ∷ 0 ∷ 1 ∷ 0 ∷ []) ≡ ψᵗ [] (ψᵗ Ωᵗ (Ωt (natT 1)) ∷ []) ∷ []
_ = refl
_ : kind (walkˢ popᵀ (0 ∷ 0 ∷ 1 ∷ 0 ∷ [])) ≡ kl
_ = refl
```

**检验 5: 单帧与 Prefix 一致.** 字面 `refl` 在闭包层面不可能: 闭包的分支在抽象的 $\eta$ 下停在各自折叠函数的调用上 (`ψᴾ 0 … (Ωˢ η)` 对 `fold 0 … (Ωˢ η)`), 两个不同的函数名不会定义性相等; 链的第 0 点在抽象的 $m$ 下停在 `iter` 上, 同理. 可比的是逐点的观测: 在 Prefix 的全部 `kind` 检验点上两者 `refl` 相同, 且纯 $\Omega_\Omega$ 栈的界字面相同 (`kc one`、`kc two`: `bound` 的 `here` 分支就是 `rebase` 的紧界). 下面 $\beta$ 是 $\psi_0(\Omega_\Omega)$ (环境层号 2), $X_2=\psi_0(\Omega_\Omega+\Omega_2)$ (Prefix §7, 路径 $A$、$B$、$B[0][0][0]$).

```agda
βᵀ : Ordˢ zero
βᵀ = ψᵀ (Ψ ∅ᵀ) (tt , (e12 , tt)) (suc zero)

_ : kind βᵀ ≡ kind β₀
_ = refl
_ : kind (walkˢ βᵀ (0 ∷ [])) ≡ kind (walkˢ β₀ (0 ∷ []))
_ = refl
_ : kind (walkˢ βᵀ (0 ∷ 0 ∷ [])) ≡ kind (walkˢ β₀ (0 ∷ 0 ∷ []))
_ = refl
_ : kind (walkˢ βᵀ (0 ∷ 3 ∷ 1 ∷ [])) ≡ kind (walkˢ β₀ (0 ∷ 3 ∷ 1 ∷ []))
_ = refl

X₂ᵀ : Ordˢ zero
X₂ᵀ = ψᵀ (Ψ ∅ᵀ ⊕ tlᵀ (fk one) (λ e → e) (Ωˢ two)) (tt , ((e12 , tt) , e22)) (suc zero)

_ : kind X₂ᵀ ≡ kind X₂ˢ
_ = refl
_ : kind (walkˢ X₂ᵀ (1 ∷ 0 ∷ 1 ∷ [])) ≡ kind (walkˢ X₂ˢ (1 ∷ 0 ∷ 1 ∷ []))
_ = refl
_ : kind (walkˢ X₂ᵀ (1 ∷ 0 ∷ 1 ∷ [])) ≡ kc two
_ = refl
_ : kind (walkˢ X₂ᵀ (2 ∷ 0 ∷ 1 ∷ [])) ≡ kind (walkˢ X₂ˢ (2 ∷ 0 ∷ 1 ∷ []))
_ = refl
_ : kind (walkˢ X₂ᵀ (2 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ [])) ≡ kind (walkˢ X₂ˢ (2 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ []))
_ = refl
_ : kind (walkˢ X₂ᵀ (2 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ [])) ≡ kc two
_ = refl
```

**结果.** 五组检验全部 `refl`. $A=\psi_0(\Omega_\Omega+\psi_1(\Omega_\Omega))$ 处的界 2 来自 `bound` 的 `here` 分支 (地板 0 $\prec$ 目标 1, 字面 `suc 1`), 与 Prefix 的紧界相同; `low-pop` 处的界 `Mlev 1 2` 来自 `above` 分支 (目标 0 $\prec$ 地板 1). 同一个子句, 两种情形.

## §8 约束表

| 编译的否定 (文件: 名字) | 内容 | 本设计如何满足 |
|---|---|---|
| Barrier: `barrier` | 精确 $\Omega$-扩张 + 有界三歧 ⟹ LPO | 下标层仍是 `Ordᴵ`, 无 $\Omega$-共尾元; 符号下标 $\Omega$ 只出现在深度里, 从不被比较; `<ᴵ-dec` 只用于同一 $\ell$ 的两个字面子项 (`limᵢA`, `ins`) |
| Level §2: `lit→ext` | 字面三歧 ⟹ funext | 嵌入值是 `Restrˢ` (模 $\cong$ 的代表 + 回搬); `Mlev` 的步进 `s⊑ e (suc r)` 用 $\cong$ |
| Stage2: `dec→WLPO` | 全分支的第二层要 WLPO | 闭包定义域仍是 $c\sqsubseteq^\mathsf I\eta$; 分支只在 `Goodᴸ` 的带标签点计值 (证书不变) |
| Stage2: `naive-unlabel` | 静态 $\Omega_\ell$ 替身在 $\psi_0(\Omega_\Omega\cdot2)$ 断 | $\Omega_\Omega$ 是 `Ω̂A` 的闭包, 点由上下文链给; 检验 1 |
| Symbolic: `Toy.loop` | $\hat\Omega$ 不能是可数层的构造子 | `Ω̂A` 是前缀塔上的函数, 树族 `Ordˢ` 原样 |
| Symbolic: `N3-path` | 更高层前缀出现 | `Run` 对目标多态, 帧在任意目标弹出; 检验 5 的 $A$ ($\psi_1$ 下的闭包) |
| Prefix §3: `List` 栈 `TerminationIssue` | 提升后的栈不是子项 | 栈是函数; `fold` 只对尾巴树递归 |
| Prefix §7: 紧界 | 用环境层号作界则 `d₀` 不可能 | 地板 $\preceq$ 目标时界字面是 `suc i` (检验 5 的 `kc two`) |
| Omega2: `no-Bound` | 无全局界 | 界在每次弹栈时于当前 $\ell$ 内现造, 无全局 $\beta$ |
| Omega2 §5 | 对一切 $\eta$ 量化的证书在无标签点失败 | 证书仍是 `Goodᴸ` (只在带标签点); `GoodR.h0` 产出它 |
| OmegaK §4: `Vec` 栈 | 弹一帧生 $m$ 帧时栈长不降 | `repA` 对 $m$ 递归是独立函数, `fold` 只把帧当值传入 |
| OmegaExp: `noSim2` | 紧界闭包分支放不下第 2 层帧 | 非紧界; 分支环境 `Mlev c (suc η) _` 字面含 $\eta$ |
| OmegaSqBase: `low-term`/`low-unlab` | 低目标帧真实出现, 占位无标签 | 后继子句不分层号, 无占位; `low-tree′ : … ≡ kl` |
| OmegaSqBase: `noSim21` | `Simᴵ 2 1` 不存在 | 界 `Mlev 1 2` (`term` 检验), `sim2` |
| SystemOmega: `prev-fails`/`cur-holds` | 界必须是当前链点 | 分支环境的 $\eta$ 是证书给的当前链点层号; `dom` 的结论对每个弹栈点陈述 |
| StandardOmega: `NF₁`, `Vis₁` 的 `vs`, `cofin₁` | 标签侧需要的标准形 | 第 1 阶段原样使用 (`label` 的前提 `NF₁`); 后续阶段要把 `Sb` 从 "可数或 $\Omega+c$" 推广到符号下标 (§9), `vs`/`cofin` 同步推广 |

## §9 后续阶段

**$\psi_0(\Omega_{\Omega+1})$ 本身.** $\Omega_{\Omega+1}$ 正规, $\psi_0(\Omega_{\Omega+1})[n]=\psi_0(\gamma_n)$, $\gamma_0=\Omega_\Omega$, $\gamma_{k+1}=\psi_\Omega(\gamma_k)$: 第 $\Omega$ 层的规则 6 链. 在本设计里链点就是 `Ψ` 的迭代 (符号项, 不被比较), 对角线是它们在深度 0 的计值之 $\mathbb N$-极限: 交替原则的 "$\Omega$ 只作对象层的对角 $\mathbb N$-极限". 不需要任何新构造. 第 $n$ 项的地板与证据随 $n$ 现造.

```agda
Ψit : ℕ → Σ Flr Sym
Ψit zero    = fz , ∅ᵀ
Ψit (suc n) = fk zero ⊔ proj₁ (Ψit n) , Ψ (proj₂ (Ψit n))

evΨ : ∀ {ℓ} → Emb one ℓ → ∀ n → Ev ℓ (proj₁ (Ψit n))
evΨ e zero    = tt
evΨ e (suc n) = e , evΨ e n

TOᵀ : Ordˢ zero
TOᵀ = Ord₊ˢ.lim (λ n → ψᵀ (proj₂ (Ψit (suc n))) (tt , evΨ e11 (suc n)) zero)

_ : kind (walkˢ TOᵀ (0 ∷ [])) ≡ kc one
_ = refl
_ : walk tO (1 ∷ []) ≡ tΩ2
_ = refl
_ : walkˢ TOᵀ (1 ∷ []) ≡ TΩ2ᵀ
_ = refl

open Stage1 TOᵀ public
```

`walkˢ TOᵀ [1] ≡ TΩ2ᵀ` 是字面的: 对角线的第 1 项就是检验 2 的树, 与 EBO 的 `tΩ2-walk` 对应.

**$\psi_0(\Omega_{\Omega+2})$, …, $\psi_0(\Omega_{\Omega\cdot2})$: 新符号 $\Omega+\alpha$.** 帧 $\psi_{\Omega+\alpha}(\zeta)$, $\alpha$ 可数. 在可数目标处弹出 $\Omega_{\Omega+\alpha+1}$ (正规) 时, 规则 6 的链在第 $\Omega+\alpha$ 层: $\gamma_{k+1}=\psi_{\Omega+\alpha}(P+\gamma_k)$, 链点含**整个前缀** $P$. 这是本设计唯一需要改的地方: 帧的作用不能只拿到深度 $d$ 的值 $P\in$ `A d fl`, 它要在更深处重放 $P$, 即前缀要以 `Sym` 的形式给出. 所以下一阶段的塔以上一阶段的符号项为底: `A⁺ 0 = Sym` 的 (带地板的) 版本, `A⁺ (suc d) = A⁺ d → A⁺ d`, 第 2 阶段的符号项 `Sym⁺ = ∀ d → A⁺ (suc d) _`; 第 1 阶段的项经 "右作用" 嵌入. 下标宇宙 `Sub` 加构造子 `Ω̇+ : Ordᴵ → Sub` ($\Omega+\alpha$); 两个这种下标的比较 ($\nu+1$ 对 $u$, 规则 5/6 的分界) 化为 $\alpha$ 与 $\beta$ 的比较, 它们是可数层号, 在**当前环境层号**内用 `<ᴵ-dec` (§3 的同一机制). `fold`、`limᵢA` 的派发、`cloA`/`bound`、`Goodᴸ`、`LabL` 不变; 新增的是第 $\Omega+\alpha$ 层的符号闭包 (定义域是符号点 $\eta<\Omega_{\Omega+\alpha+1}$, 由链给, 不比较) 与它的闭包定理 `goodΩ̂⁺`. 记号侧: `NF₁` 的 `Sb` 换成 "可数, 或 $\Omega+c$ 且 $c$ 可数" 的推广 (`Sb` 已含 $\Omega+c$, StandardOmega §1), 所以 $\psi_0(\Omega_{\Omega\cdot2})$ 之下的标准形已有.

**$\psi_0(\Omega_{\Omega_\Omega})$: 下标本身是符号项.** 下标 $u<\Omega_\Omega$ 是第 1 阶段的符号项 ($\Omega\cdot\alpha+\beta$, $\Omega^\alpha$, $\psi_\Omega(\cdots)$, …). 规则 5/6 要比较两个符号下标: 它们是函数, 不能直接比较, 要比较它们的**语法** (`Syn`, 叶子是可数树), 即 EBO 的 `cmpᵀ` 的字典序, 叶子在当前环境层号内比较. 这是交替不变量在符号层的形式: 两个被比较的符号下标的全部可数叶子必须在同一个环境层号之下. `Sub` 成为 `Syn` 本身 (`ψ̇ (sym X) ζ`), 下标宇宙与项宇宙相同, 如 EBO. 预期改动: 比较函数 `cmpˢ : Syn → Syn → …` (对语法结构递归, 叶子用 `<ᴵ-dec`); 帧的作用以下标的 `Syn` 为参数. 折叠与证书仍不变.

**$\psi_0(\Lambda)$: 阶段对角线.** 第 $s$ 阶段的符号项类型 `Sym⟨ s ⟩` 对 $s$ 递归定义 (每个都在 `Set` 里), 第 $s$ 阶段的顶 $\psi_0(\Omega\text{-塔}_s)$ (EBO 的 `EBOψ s`) 是它的对角线 (像 `TOᵀ`). $\mathrm{EBO}=\psi_0(\Lambda)=\lim_s$ 第 $s$ 阶段的顶: 又一个对象层的 $\mathbb N$-极限, 阶段号从不被比较. 交替不变量在每一阶段都在同一处兑现: 弹栈的 `bound` 与派发 `limᵢA`, 比较的永远是当前环境层号的两个字面子项, 环境层号由上一层闭包的分支 (`Mlev c (suc η) _`, $\eta$ 来自证书的带标签链点) 现造.

**哪些部分随阶段变.** 不变: `Ordᴵ`、`Ordˢ`、`Emb`/`Flr`/`Ev`、构造器、`bound`/`cloA`、`fold`、`Goodᴸ`/`forceᴸ`/`LabL`、`Rep`/`GoodA` 的形状. 每阶段新增: 一个下标构造子、一层塔 (底换成上一阶段的符号项)、该层的闭包定理与支配引理. 记号侧: 标准形的下标条件 `Sb`.

## §10 校准: 与自下而上的栈对照

| 自下而上的部件 | 文件 | 在本设计中 |
|---|---|---|
| `Ordᴵ`, `<ᴵ-dec`, `≅ᴵ`, `⊑ᴵ`, `Mlev` | Level, Symbolic | 原样 |
| `Ordˢ`/`Uˢ`/`Z`/`ĉᴸ`/`toZ`/`trˢ`/`tr⁻ˢ`/`resˢ`/`Ωˢ`/`+ˢ` | Prefix §2 | 原样 |
| `Goodᴸ`/`forceᴸ`/`CCᴸ`/`LabL`/`Lab-oc`/`Lab-uniq`/`fs-mono₁` | GoodLBase, Decouple | 原样 |
| `domS` | OmegaExpBase | `dom` 在地板只有 0 时的特例 |
| `Stk` | OmegaExpBase | `Run φ` = `A 0 φ` (加地板) |
| `ψˢ` | OmegaExpBase | `fold 0` |
| `ψᵉ`, `ψᵉ′`, `rep`, `repᴷ` | OmegaExpBase, OmegaSqBase | `fold 1` 于 `Ω̂A 0`, `repA` |
| `▹Ω̂`, `▹ω X`/`▹[ s ] X`, `▹Ω̂²` | OmegaExpBase, OmegaSqBase | `Ψ ∅ᵀ`, `Ψ (tlᵀ …)`, `Ψ (Ψ ∅ᵀ)` |
| `rebase`, `z<suc`, `σ1`, `s₀`, `σ⊥` | Prefix, OmegaSqBase | `bound` 的 `here` 分支; 地板 `fk zero`, `fz` |
| `Goodˢ` = `HypW` × `Hyp0` × `≈ˢ` | OmegaExpBase | `GoodR` (+ `FlrLab`) 与塔 `GoodA` |
| `PreW`/`Pre0`, `WE₀/₁`, `ZE₀/₁`, `GoodE`, `GoodE₀/₁`, `repGood₀/₁` | OmegaExpBase, OmegaSqBase | 合并为一条 `goodTl` |
| `popL`/`pop0ᴸ`, `GoodΩ`, `BranchΩ` | GoodLBase, OmegaExpBase, OmegaSq | 合并为 `goodΩ̂ d` (各深度一条) |
| `ψᴾ`, `Frame`, `Vec` 栈, `Base` | Prefix | 死 |
| `ψ²` 计数器, `ψᵛ` | OmegaK | 死 |
| 第 $\ge1$/$\ge2$ 层后继的占位, `Lo` | OmegaExpBase, OmegaSqBase | 死 |
| `Bound`/`Strictᵝ`, 观测前序, `Goodᶻ` | Omega2Base, UniformS, Prefix | 死 (GoodL 时已不用) |

**行数估计** (代码行, 不含空行与散文). 按 README "成品去向" 的三层: (1) 下标层、树族与层号: Level §1/§4–§9 约 610 (README 的数), 加 Prefix §2 的符号构造子与搬运 103 行, 不变; (2) 折叠: 本文 §1–§5 共 147 行 (含 `Syn`/`⟦_⟧`), 取代 Prefix §3 (50)、OmegaExpBase §2 (49)、OmegaSqBase §2 (29) 共 128 行, 多出的 19 行是地板与界, 换来对一切第 1 阶段的项无占位; (3) 证书: Uniform §0–§9 约 370、GoodLBase §1–§2 151、Diagonal §1–2 约 35, 不变. 第 1 阶段的成品定义约 $610+103+147+370+151+35\approx1400$ 行, 证书与标签的类型 (§6) 另加约 50 行. 每个后续阶段估计加 100–150 行 (一个下标构造子、一层塔、一个符号闭包与比较), 阶段递归写一次后到 $\psi_0(\Lambda)$ 约 1600–1800 行. 不含标签证明 (自下而上的经验: 证明是定义的 3–5 倍).

**判断.** 自下而上的树族、证书与标签机器全部保留; 被取代的只是折叠与栈 (约十轮里每轮修补的正是它们). 三种旧帧与两种指数折叠都是一个帧与一个折叠的实例, 两条编译的障碍 (`noSim21`、`low-unlab`) 在定义层面消失. 剩下的数学集中在两条引理: 各深度的闭包定理 `goodΩ̂` (其深度 0、1 的部分已在 GoodL/OmegaExp/OmegaSq 中逐例证过, 只是界换成 `bound`) 与统一支配引理 `dom` (由 `Lab-oc` 与 `occ<`, 形状同 `domS`).

## §11 结论与边界

**字面成立 (`refl`):** 检验 1–5 的全部 `kind`/`walk`/`cof` 等式; `term (bndOf popᵀ) 0 ≡ one`、`… 1 ≡ two`; `walkˢ TOᵀ [1] ≡ TΩ2ᵀ`; `walk tO [1] ≡ tΩ2`.

**编译的构造:** 嵌入 `Emb`/`simE`/`_∘ᴱ_`/`mkE`; 地板 `Flr`/`Ev`/`liftEv`; 前缀塔 `Run`/`A`/`wk` 与构造器 `limA`/`limᵢA`/`ŝA`/`ĉA`; 界 `Top`/`ins`/`accT`/`Bnd`/`bound` 与闭包 `cloA`; 折叠 `repA`/`fold`/`Ω̂A`; 符号项 `Sym`/`∅ᵀ`/`tlᵀ`/`Ψ`/`_⊕_`/`ψᵀ`; 文法 `Sub`/`Syn`/`⟦_⟧`; 证书与标签类型 `Rep`/`Lab₀`/`FlrLab`/`GoodR`/`GoodA`/`GoodSym`; 期望的定理 `Expected`; 由它们证明的 `goodΨ`/`rep→good`/`label`; 对角线 `TOᵀ`.

**未做 (设计草案的边界):**

1. `Expected` 的七个字段都未证. 深度 0、1 的 `goodΩ̂`/`goodTl` 是旧证明在新界下的移植; 深度 $\ge2$ 的 `goodΩ̂` 与 `dom` 是新数学 (`dom` 的形状已由 `domS` 证过一个特例).
2. `dom` 要的 `FlrLab` 要求地板紧: 在 `up zero` 处收紧保证了后继父层; 极限父层 (`up (self n)`) 保留父地板, 是否总被某个出现的下标支配, 未核实 (极限层号的数据在已有检验中未出现).
3. `GoodR` 不含自互模拟 (`≈ˢ`); 若 `goodTl` 的证明像 OmegaExpBase 那样需要它, 要补一个 `A d` 上的互模拟塔.
4. 分支环境由 `Mlev c η e` 改为 `Mlev c (suc η) _`; 所有标签与证书只看 `toZ` 后的树与带标签的链点, 不受影响, 但旧树与新树只在观测上一致 (检验 5), 不是 `≅ˢ` (未证).
5. §9 的后续阶段只有 $\psi_0(\Omega_{\Omega+1})$ 本身编译; $\Omega+\alpha$ 与符号下标的塔是纸面设计.
