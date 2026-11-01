# 一致引理: 安全路径引理移植到证据模 ≅ 的层号上

> 接 [SafePath](SafePath.lagda.md) 与 [Level](Level.lagda.md). SafePath 在旧族 (Cumulative 的 `Ordᶜ`, 下标 `Ordʷ`) 上证了 `HS-diag : ∀ a → HS (ψ⁰ (Ω a))`; [Diagonal](Diagonal.lagda.md) 需要的恰是它在 Level 的族 (下标 `Ordᴵ`) 上的版本, 并把它当作模块参数 `Uniform`. 本文把 SafePath §4–§10 移植过来, 兑现这个参数.
>
> 结论先说:
>
> 1. **`Uniform : ∀ (a : Ordᴵ) → HS (ψ⁰ (Ω a))` 已证, 无前提** (§9). `HS` 是 Level 的 `HS` (同一个数据类型, 没有第二份). `lim` 情况的步进证据直接取层号自带的 `t n : g n ⊑ᴵ g (suc n)`, 经 `Ω-monoᵒ` 变成 $\Omega_{g\,n}\sqsubseteq^\mathsf{o}\Omega_{g(n+1)}$.
> 2. **观测必须包含搬运.** Level 的 $\psi$ 在穿透分支把输入经 `tr⁻ e` 从目标层的代表元 $j'$ 搬回节点的层 $j$. 于是 `Good-ψ` 在穿透处要两件事: `Good (tr⁻ e z)` 与 "`tr⁻ e` 对 $\sqsubseteq^\mathsf{o}$ 单调". 后者在 SafePath 的观测下看不出怎么证 (纸面论证, §6): 要把第 $j$ 层上的观测换成第 $j'$ 层上的, 而 `Sim` 证据是字面的 (`c <ᴵ j′` 经 `<-≅` 只给出 $c\cong^\mathsf{I}c'<^\mathsf{I}j$, 不给出字面的 `c <ᴵ ℓ`). 修复是把两种搬运也算作观测 (`tro`, `tr⁻o`, §1): 单调性随即是一行 (`tr-cong`, `tr⁻-cong`), `Good` 对搬运封闭 (`Good-tr`/`Good-tr⁻`, 与 Level 的 `tr`/`tr⁻`/`res`/`res⁻` 同构的四重互递归).
> 3. **相似关系不需要 $\cong^\mathsf{I}$-相关的目标层.** `ψo` 两侧仍要求同一个目标层 $i$ (SafePath 的选择), `Sim` 证据与外层层号任意; 新增的 `tro`/`tr⁻o` 两侧都必须是搬运, 搬运证据任意. 所有层号上的 $\cong^\mathsf{I}$ 都被搬运观测吸收, 没有一处要 "$i\cong^\mathsf{I}i'$ 的两个 $\psi$ 观测相似".
> 4. **`tr⁻` 进入 `limᵢ` 上界引理的方式.** SafePath 的 `limᵢ-r` 只要 $x\cong g(\Omega_j)$. 穿透后新节点的起点分支是 $\psi(g(\mathtt{tr}^{-}_e\,\Omega_{j'}))$, 它的参数不再字面地是 $\Omega_j$. 所以假设改为对**一切** $z\cong\Omega_j$ 都有 $x\sqsubseteq^\mathsf{o}g(z)$ (§3); 穿透时取 $z:=\mathtt{tr}^{-}_e\,z'$, 由 `tr⁻-≅` 与 `Ω-≅` 得 $\mathtt{tr}^{-}_e\,z'\cong\Omega_j$. 搬运观测的情况同理, 用 `back-≅`/`back⁻-≅`. 假设同时从 $\cong$ 放宽为 $\sqsubseteq^\mathsf{o}$, 于是上界引理直接吸收传递性, SafePath 的 `⊑ᵒ-trans◃`/`retarget` 不再需要.
> 5. **检验全部移植** (§10): `chain-step`, `row4` (任意 $c$), `HS-x₃` (层号 $\varepsilon_0$ 由 `toLevel` 从 $\psi_0(\Omega_1)$ 造出), `⊑ᵒ-rejects` (反例对在本族上重述并被拒).
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入 Level, 不改动任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open Restr
```

## §0 记号与几条 $\cong$ 的小引理

记号全部沿用 Level: 下标 `Ordᴵ` (字面子项序 $<^\mathsf{I}$, 结构互模拟 $\cong^\mathsf{I}$, 前驱包含 $\sqsubseteq^\mathsf{I}$), 树族 `Ordᶜ`, 搬运 `tr`/`tr⁻` (及 `res`/`res⁻`/`back`), 忠实折叠 `ψ`, 目标层 0 的 `ψ⁰`, 互模拟 $\cong$, 叶子为 $\cong$ 的 $\prec/\sqsubseteq$. Level 没有导出 $\cong$ 的左右自反 (Cumulative 有), 这里补上; 再加上 SafePath §7 的反演. `limᵢ` 的反演写成 "相关输入给出相关输出" (`i-resp`): Level 的 `lᵢ≅` 两边节点可在不同的层 $j\cong^\mathsf{I}j'$, 所以不能像 SafePath 那样把同一个 $z$ 喂给两边, 而是两边都对到右边的 `tr e z′`. 右边保持任意 (`limᵢ p f ≅ b`), 避开 `UnificationStuck`.

```agda
≅-reflˡ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≅ b → a ≅ a
≅-reflˡ e = ≅-trans e (≅-sym e)

≅-reflʳ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≅ b → b ≅ b
≅-reflʳ e = ≅-trans (≅-sym e) e

self-tr : ∀ {a b} (e : a ≅ᴵ b) {x : Ordᶜ a} → x ≅ x → tr e x ≅ tr e x
self-tr e d = ≅-reflˡ (tr-≅ e d)

self-tr⁻ : ∀ {a b} (e : a ≅ᴵ b) {x : Ordᶜ b} → x ≅ x → tr⁻ e x ≅ tr⁻ e x
self-tr⁻ e d = ≅-reflˡ (tr⁻-≅ e d)

s-inv : ∀ {k k′} {a : Ordᶜ k} {b : Ordᶜ k′} → suc a ≅ suc b → a ≅ b
s-inv (s≅ e) = e

l-inv : ∀ {k k′} {f : ℕ → Ordᶜ k} {g : ℕ → Ordᶜ k′} → lim f ≅ lim g → ∀ n → f n ≅ g n
l-inv (l≅ h) = h

i-resp : ∀ {k k′ j} {p : j <ᴵ k} {f : U j (<→◃ p) → Ordᶜ k} {b : Ordᶜ k′} → limᵢ p f ≅ b →
         ∀ {z z′ : Ordᶜ j} → z ≅ z′ → f (into (<→◃ p) z) ≅ f (into (<→◃ p) z′)
i-resp {p = p} (lᵢ≅ e h) {z} {z′} d =
  ≅-trans (h z (tr e z′) (≅→R (<→◃ p) (≅-tr e d)))
          (≅-sym (h z′ (tr e z′) (≅→R (<→◃ p) (≅-tr e (≅-reflʳ d)))))
i-resp (upʳ {r = zero} e)   = i-resp e
i-resp (upʳ {r = self n} e) = i-resp e

u-inv : ∀ {k ℓ ℓ′} (r : k ◃₁ ℓ) {x : U k (◃₁→◃ r)} {b : Ordᶜ ℓ′} → up r x ≅ b → out (◃₁→◃ r) x ≅ b
u-inv zero     (upˡ e)              = e
u-inv zero     (upʳ {r = zero} e)   = upʳ (u-inv zero e)
u-inv zero     (upʳ {r = self n} e) = upʳ (u-inv zero e)
u-inv (self m) (upˡ e)              = e
u-inv (self m) (upʳ {r = zero} e)   = upʳ (u-inv (self m) e)
u-inv (self m) (upʳ {r = self n} e) = upʳ (u-inv (self m) e)

u-refl : ∀ {k ℓ} (r : k ◃₁ ℓ) {x : U k (◃₁→◃ r)} → up r x ≅ up r x → out (◃₁→◃ r) x ≅ out (◃₁→◃ r) x
u-refl r e = ≅-reflˡ (u-inv r e)
```

## §1 观测与观测前序 (SafePath §4, 加上搬运)

**观测.** SafePath 的四种 (`idO`, `ψ⁰o`, `ψo`, `addo`) 之外加两种: `tro O e` 先做 `tr e` 再做 `O`, `tr⁻o O e` 先做 `tr⁻ e`. 为什么必须加, 见 §6 开头; 这里先说它们的代价: 每条对观测归纳的引理多两个情况, 每个情况要求搬运与该引理关心的首构造子交换. `tr`/`tr⁻` 对 `zero`/`suc`/`lim` 逐字交换, 对 `limᵢ` 交换成另一个 `limᵢ` 节点 (下标换成代表元, 分支经 `back`), 对 `up` 在 $\cong^\mathsf{I}$ 的证明拆开一层后交换. 这正是上界引理需要的全部.

**相似.** `ψo` 两侧同一个目标层 $i$, 目标证明 $p,p'$、`Sim` 证据与外层层号任意 (同 SafePath). `tro`/`tr⁻o` 两侧都是搬运, 两侧的 $\cong^\mathsf{I}$ 证据任意. 没有放宽到 $\cong^\mathsf{I}$-相关的目标层: 下面没有一处需要它 (Level 的 `ψ-≅` 允许, 但对角线上的观测都是同目标层的; 层号的 $\cong^\mathsf{I}$ 全部出现在节点的下标上, 由搬运观测处理). `run-≅`: 相似观测把 $\cong$ 送到 $\cong$, 搬运情况用 `tr-≅`/`≅-tr`.

```agda
data Obs : Ordᴵ → Set where
  idO  : Obs zero
  ψ⁰o  : ∀ {k} → Obs zero → Obs k
  ψo   : ∀ {i k ℓ} → Obs i → i <ᴵ ℓ → Simᴵ k ℓ → Obs k
  addo : ∀ {k ℓ} → Obs ℓ → Ordᶜ ℓ → Simᴵ k ℓ → Obs k
  tro  : ∀ {a b} → Obs b → a ≅ᴵ b → Obs a
  tr⁻o : ∀ {a b} → Obs a → a ≅ᴵ b → Obs b

run : ∀ {k} → Obs k → Ordᶜ k → Ordᶜ zero
run idO          x = x
run (ψ⁰o O)      x = run O (ψ⁰ x)
run (ψo O p σ)   x = run O (ψ p σ x)
run (addo O a σ) x = run O (add a σ x)
run (tro O e)    x = run O (tr e x)
run (tr⁻o O e)   x = run O (tr⁻ e x)

infix 4 _≈ᵒ_ _⊑ᵒ_
data _≈ᵒ_ : ∀ {k k′} → Obs k → Obs k′ → Set where
  idO  : idO ≈ᵒ idO
  ψ⁰o  : ∀ {k k′} {O O′ : Obs zero} → O ≈ᵒ O′ → ψ⁰o {k} O ≈ᵒ ψ⁰o {k′} O′
  ψo   : ∀ {i k k′ ℓ ℓ′} {O O′ : Obs i} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} →
         O ≈ᵒ O′ → ψo O p σ ≈ᵒ ψo O′ p′ σ′
  addo : ∀ {k k′ ℓ ℓ′} {O : Obs ℓ} {O′ : Obs ℓ′} {a : Ordᶜ ℓ} {a′ : Ordᶜ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} →
         O ≈ᵒ O′ → a ≅ a′ → addo O a σ ≈ᵒ addo O′ a′ σ′
  tro  : ∀ {a a′ b b′} {O : Obs b} {O′ : Obs b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} →
         O ≈ᵒ O′ → tro O e ≈ᵒ tro O′ e′
  tr⁻o : ∀ {a a′ b b′} {O : Obs a} {O′ : Obs a′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} →
         O ≈ᵒ O′ → tr⁻o O e ≈ᵒ tr⁻o O′ e′

≈ᵒ-reflˡ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → O ≈ᵒ O
≈ᵒ-reflˡ idO        = idO
≈ᵒ-reflˡ (ψ⁰o o)    = ψ⁰o (≈ᵒ-reflˡ o)
≈ᵒ-reflˡ (ψo o)     = ψo (≈ᵒ-reflˡ o)
≈ᵒ-reflˡ (addo o e) = addo (≈ᵒ-reflˡ o) (≅-reflˡ e)
≈ᵒ-reflˡ (tro o)    = tro (≈ᵒ-reflˡ o)
≈ᵒ-reflˡ (tr⁻o o)   = tr⁻o (≈ᵒ-reflˡ o)

≈ᵒ-reflʳ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → O′ ≈ᵒ O′
≈ᵒ-reflʳ idO        = idO
≈ᵒ-reflʳ (ψ⁰o o)    = ψ⁰o (≈ᵒ-reflʳ o)
≈ᵒ-reflʳ (ψo o)     = ψo (≈ᵒ-reflʳ o)
≈ᵒ-reflʳ (addo o e) = addo (≈ᵒ-reflʳ o) (≅-reflʳ e)
≈ᵒ-reflʳ (tro o)    = tro (≈ᵒ-reflʳ o)
≈ᵒ-reflʳ (tr⁻o o)   = tr⁻o (≈ᵒ-reflʳ o)

run-≅ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} {x : Ordᶜ k} {x′ : Ordᶜ k′} → O ≈ᵒ O′ → x ≅ x′ → run O x ≅ run O′ x′
run-≅ idO        d = d
run-≅ (ψ⁰o o)    d = run-≅ o (ψ⁰-≅ d)
run-≅ (ψo o)     d = run-≅ o (ψ-≅ (≅ᴵ-refl _) d)
run-≅ (addo o a) d = run-≅ o (add-≅ a d)
run-≅ (tro {e = e} {e′ = e′} o)  d = run-≅ o (tr-≅ e (≅-tr e′ d))
run-≅ (tr⁻o {e = e} {e′ = e′} o) d = run-≅ o (tr⁻-≅ e (≅-tr⁻ e′ d))

_⊑ᵒ_ : ∀ {k k′} → Ordᶜ k → Ordᶜ k′ → Set
_⊑ᵒ_ {k} {k′} x y = ∀ {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → run O x ⊑ run O′ y

≅→⊑ᵒ : ∀ {k k′} {x : Ordᶜ k} {y : Ordᶜ k′} → x ≅ y → x ⊑ᵒ y
≅→⊑ᵒ e o = ≅→⊑ (run-≅ o e)

⊑ᵒ-≅ʳ : ∀ {k k′} {x : Ordᶜ k} {y y′ : Ordᶜ k′} → x ⊑ᵒ y → y ≅ y′ → x ⊑ᵒ y′
⊑ᵒ-≅ʳ h e o = ⊑-trans (h o) (≅→⊑ (run-≅ (≈ᵒ-reflʳ o) e))
```

`≅→⊑ᵒ` 是跨层的 ($x,y$ 的层号任意), 因为 `run-≅` 对任意相似观测成立. `⊑ᵒ-≅ʳ` 只在同一层换右端. 一般的跨层传递性没有, 也不需要 (§3 的上界引理把它吸收了).

## §2 同余

与 SafePath §5 相同, 多两条搬运同余. 透过提升节点 (`up-l`/`up-r`) 在搬运观测下要先拆 $\cong^\mathsf{I}$ 的证明: `tr (s≅ e) (up zero x) = up zero (tr e x)`, `tr (l≅ h) (up (self n) x) = up (self n) (tr (h n) x)`; 拆开后对内层观测递归, 并把搬运推进假设.

```agda
ψ-cong : ∀ {i k k′ ℓ ℓ′} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} {x : Ordᶜ k} {y : Ordᶜ k′} →
         x ⊑ᵒ y → ψ p σ x ⊑ᵒ ψ p′ σ′ y
ψ-cong h o = h (ψo o)

ψ⁰-cong : ∀ {k k′} {x : Ordᶜ k} {y : Ordᶜ k′} → x ⊑ᵒ y → ψ⁰ x ⊑ᵒ ψ⁰ y
ψ⁰-cong h o = h (ψ⁰o o)

add-cong : ∀ {k k′ ℓ ℓ′} {a : Ordᶜ ℓ} {a′ : Ordᶜ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} {x : Ordᶜ k} {y : Ordᶜ k′} →
           a ≅ a′ → x ⊑ᵒ y → add a σ x ⊑ᵒ add a′ σ′ y
add-cong e h o = h (addo o e)

tr-cong : ∀ {a a′ b b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} {x : Ordᶜ a} {y : Ordᶜ a′} → x ⊑ᵒ y → tr e x ⊑ᵒ tr e′ y
tr-cong h o = h (tro o)

tr⁻-cong : ∀ {a a′ b b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} {x : Ordᶜ b} {y : Ordᶜ b′} → x ⊑ᵒ y → tr⁻ e x ⊑ᵒ tr⁻ e′ y
tr⁻-cong h o = h (tr⁻o o)

up-l : ∀ {k ℓ ℓ′} {r : k ◃₁ ℓ} {x : U k (◃₁→◃ r)} {y : Ordᶜ ℓ′} → out (◃₁→◃ r) x ⊑ᵒ y → up r x ⊑ᵒ y
up-l {r = zero}   h (ψ⁰o o)    = h (ψ⁰o o)
up-l {r = zero}   h (ψo o)     = h (ψo o)
up-l {r = zero}   h (addo o e) = h (addo o e)
up-l {r = zero}   h (tro {e = s≅ e} o)  = up-l {r = zero} (λ o′ → h (tro o′)) o
up-l {r = zero}   h (tr⁻o {e = s≅ e} o) = up-l {r = zero} (λ o′ → h (tr⁻o o′)) o
up-l {r = self n} h (ψ⁰o o)    = h (ψ⁰o o)
up-l {r = self n} h (ψo o)     = h (ψo o)
up-l {r = self n} h (addo o e) = h (addo o e)
up-l {r = self n} h (tro {e = l≅ f} o)  = up-l {r = self n} (λ o′ → h (tro o′)) o
up-l {r = self n} h (tr⁻o {e = l≅ f} o) = up-l {r = self n} (λ o′ → h (tr⁻o o′)) o

up-r : ∀ {k ℓ ℓ′} {r : k ◃₁ ℓ} {y : U k (◃₁→◃ r)} {x : Ordᶜ ℓ′} → x ⊑ᵒ out (◃₁→◃ r) y → x ⊑ᵒ up r y
up-r {r = zero}   h (ψ⁰o o)    = h (ψ⁰o o)
up-r {r = zero}   h (ψo o)     = h (ψo o)
up-r {r = zero}   h (addo o e) = h (addo o e)
up-r {r = zero}   h (tro {e′ = s≅ e} o)  = up-r {r = zero} (λ o′ → h (tro o′)) o
up-r {r = zero}   h (tr⁻o {e′ = s≅ e} o) = up-r {r = zero} (λ o′ → h (tr⁻o o′)) o
up-r {r = self n} h (ψ⁰o o)    = h (ψ⁰o o)
up-r {r = self n} h (ψo o)     = h (ψo o)
up-r {r = self n} h (addo o e) = h (addo o e)
up-r {r = self n} h (tro {e′ = l≅ f} o)  = up-r {r = self n} (λ o′ → h (tro o′)) o
up-r {r = self n} h (tr⁻o {e′ = l≅ f} o) = up-r {r = self n} (λ o′ → h (tr⁻o o′)) o
```

## §3 上界引理

SafePath §6 的上界引理以 $\cong$ 为假设 ($x\cong h\,n\Rightarrow x\sqsubseteq^\mathsf{o}\lim h$), 再用传递性串起来. 这里直接以 $\sqsubseteq^\mathsf{o}$ 为假设 ($x\sqsubseteq^\mathsf{o}h\,n\Rightarrow x\sqsubseteq^\mathsf{o}\lim h$): 证明照旧是对观测归纳, 每一步把运算同时推进左边的 $x$ (用同余) 与右边的节点 (运算与首构造子交换), 到 `idO` 时用第 0 层的 $\sqsubseteq$. 这样做省掉了 SafePath 的三种传递与 `retarget` (后者在搬运观测下要沿 $\cong^\mathsf{I}$ 搬 $\triangleleft$ 证明).

- `lim-r`: $x\sqsubseteq^\mathsf{o}h\,n\Rightarrow x\sqsubseteq^\mathsf{o}\lim h$;
- `lim-l`: $(\forall n.\,h\,n\sqsubseteq^\mathsf{o}y)\Rightarrow\lim h\sqsubseteq^\mathsf{o}y$;
- `suc-r`: $x\sqsubseteq^\mathsf{o}y\Rightarrow x\sqsubseteq^\mathsf{o}\mathrm{suc}\,y$ ($\psi$ 与 $\psi^0$ 观测下走规则 4 的第 1 项).

```agda
lim-r : ∀ {k k′} {x : Ordᶜ k} {h : ℕ → Ordᶜ k′} n → x ⊑ᵒ h n → x ⊑ᵒ lim h
lim-r n p idO        = ⊑-lim n (p idO)
lim-r n p (ψ⁰o o)    = lim-r n (ψ⁰-cong p) o
lim-r n p (ψo o)     = lim-r n (ψ-cong p) o
lim-r n p (addo o a) = lim-r n (add-cong a p) o
lim-r n p (tro o)    = lim-r n (tr-cong p) o
lim-r n p (tr⁻o o)   = lim-r n (tr⁻-cong p) o

lim-l : ∀ {k k′} {h : ℕ → Ordᶜ k} {y : Ordᶜ k′} → (∀ n → h n ⊑ᵒ y) → lim h ⊑ᵒ y
lim-l K idO        = lim-⊑ (λ n → K n idO)
lim-l K (ψ⁰o o)    = lim-l (λ n o′ → K n (ψ⁰o o′)) o
lim-l K (ψo o)     = lim-l (λ n o′ → K n (ψo o′)) o
lim-l K (addo o a) = lim-l (λ n o′ → K n (addo o′ a)) o
lim-l K (tro o)    = lim-l (λ n o′ → K n (tro o′)) o
lim-l K (tr⁻o o)   = lim-l (λ n o′ → K n (tr⁻o o′)) o

suc-r : ∀ {k k′} {x : Ordᶜ k} {y : Ordᶜ k′} → x ⊑ᵒ y → x ⊑ᵒ suc y
suc-r p idO        = λ h → ≺s (p idO h)
suc-r p (ψ⁰o o)    = lim-r 1 (ψ⁰-cong p) o
suc-r p (ψo o)     = lim-r 1 (ψ-cong p) o
suc-r p (addo o a) = suc-r (add-cong a p) o
suc-r p (tro o)    = suc-r (tr-cong p) o
suc-r p (tr⁻o o)   = suc-r (tr⁻-cong p) o
```

**`limᵢ-r`: 起点分支在节点之下, 以及 `tr⁻` 怎样进来.** SafePath 的陈述是 $x\cong g(\Omega_j)\Rightarrow x\sqsubseteq^\mathsf{o}\lim_j g$, 证明的穿透情况把观测推进节点后, 新节点的起点分支是 $\psi(g(\Omega_j))$, 字面地还是 $g$ 在 $\Omega_j$ 处的值. 在 Level 的族上穿透输出是

    limᵢ r (λ y → ψ p σ (g (into (<→◃ q) (tr⁻ e (out (<→◃ r) y)))))      -- e : j ≅ᴵ j′, r : j′ <ᴵ i

它的起点分支 ($y$ 取 $\Omega_{j'}$) 是 $\psi(g(\mathtt{tr}^{-}_e\,\Omega_{j'}))$: $g$ 的参数只 $\cong\Omega_j$, 不再字面地是 $\Omega_j$. 所以假设必须对**一切** $z\cong\Omega_j$ 成立:

$$(\forall z\cong\Omega_j.\ x\sqsubseteq^\mathsf{o}g(z))\ \Rightarrow\ x\sqsubseteq^\mathsf{o}\textstyle\lim_j g.$$

穿透情况的新假设取 $z:=\mathtt{tr}^{-}_e\,z'$ ($z'\cong\Omega_{j'}$): `tr⁻-≅ e` 给出 $\mathtt{tr}^{-}_e\,z'\cong z'$, 再接 $\Omega_{j'}\cong\Omega_j$ (`Ω-≅ (≅ᴵ-sym e)`), 然后用原假设与 `ψ-cong`. 这是 `tr⁻` 进入证明的唯一方式: 只经 `tr⁻-≅` (搬运在 $\cong$ 下不可见), 不需要 `tr⁻` 的任何单调性. 两种搬运观测的情况结构相同, 节点被搬到代表元 `rep (res q e′)` 上, 分支经 `back`, 用 `back-≅` (或 `back⁻-≅`) 与 `Ω-≅ (≅ᴵ-sym (eq …))`. 折叠情况 (`ψ⁰o`, 以及 `ψo` 的第二、三种派发) 取 $z:=\Omega_j$ 与 `lim-r 0`, 与 SafePath 相同.

```agda
limᵢ-r : ∀ {k k′ j} {x : Ordᶜ k} {q : j <ᴵ k′} {g : U j (<→◃ q) → Ordᶜ k′} →
         (∀ z → z ≅ Ω j → x ⊑ᵒ g (into (<→◃ q) z)) → x ⊑ᵒ limᵢ q g
limᵢ-r {q = ()} H idO
limᵢ-r {j = j} H (ψ⁰o o) = lim-r 0 (ψ⁰-cong (H (Ω j) (Ω-refl j))) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} H (ψo {p = p} {p′ = p′} {σ = σ} {σ′ = σ′} o) with <ᴵ-dec (σ′ q) p′
... | injᵃ (via e r) = limᵢ-r (λ z d →
        subst (λ u → ψ p σ x ⊑ᵒ ψ p′ σ′ (g (into (<→◃ q) (tr⁻ e u)))) (sym (out-into (<→◃ r) z))
              (ψ-cong (H (tr⁻ e z) (tr⁻-≅ e (≅-trans d (Ω-≅ (≅ᴵ-sym e))))))) o
... | injᵇ _ = lim-r 0 (ψ-cong (H (Ω j) (Ω-refl j))) o
... | injᶜ _ = lim-r 0 (ψ-cong (H (Ω j) (Ω-refl j))) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} H (addo {a = a} {a′ = a′} {σ = σ} {σ′ = σ′} o ea) = limᵢ-r (λ z d →
  subst (λ u → add a σ x ⊑ᵒ add a′ σ′ (g (into (<→◃ q) u))) (sym (out-into (<→◃ (σ′ q)) z))
        (add-cong ea (H z d))) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} H (tro {e = e} {e′ = e′} o) = limᵢ-r (λ z d →
  subst (λ u → tr e x ⊑ᵒ tr e′ (g (into (<→◃ q) (back (res q e′) u)))) (sym (out-into (<→◃ (lt (res q e′))) z))
        (tr-cong (H (back (res q e′) z) (≅-trans (back-≅ q e′ d) (Ω-≅ (≅ᴵ-sym (eq (res q e′)))))))) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} H (tr⁻o {e = e} {e′ = e′} o) = limᵢ-r (λ z d →
  subst (λ u → tr⁻ e x ⊑ᵒ tr⁻ e′ (g (into (<→◃ q) (back (res⁻ q e′) u)))) (sym (out-into (<→◃ (lt (res⁻ q e′))) z))
        (tr⁻-cong (H (back (res⁻ q e′) z) (≅-trans (back⁻-≅ q e′ d) (Ω-≅ (≅ᴵ-sym (eq (res⁻ q e′)))))))) o
```

## §4 链的起点 $\Omega_j\sqsubseteq^\mathsf{o}\psi_q z$ (SafePath §7)

`B1`, `B1⁰`, `add-r`, `zero-l` 的陈述与 SafePath 相同. 证明因上界引理以 $\sqsubseteq^\mathsf{o}$ 为假设而变短 (不再先证起点分支再传递): 后继与 `lim` 直接是 `lim-r 1`/`lim-r 0` 作用于递归结果. 穿透情况 (`<ᴵ-dec` 给出 `via e₁ r`) 对新节点用 `limᵢ-r`, 在每个 $z$ 上对 $g(\mathtt{tr}^{-}_{e_1}z)$ 递归 (这是结构递归: 它是 $g$ 的一个值); 只需要 $g$ 在这个点上自反 (`i-resp` 加 `self-tr⁻`). `zero-l` 的搬运情况就是对搬运后的右端递归 (`tr e zero = zero`).

```agda
B1 : ∀ {j ℓ k} {q : j <ᴵ ℓ} {σ : Simᴵ k ℓ} (z : Ordᶜ k) → z ≅ z → Ω j ⊑ᵒ ψ q σ z
B1 zero e = ≅→⊑ᵒ (Ω-refl _)
B1 {q = q} {σ = σ} (suc a) e = lim-r 1 (B1 {q = q} {σ = σ} a (s-inv e))
B1 {q = q} {σ = σ} (lim h) e = lim-r 0 (B1 {q = q} {σ = σ} (h 0) (l-inv e 0))
B1 {j = j} {q = q} {σ = σ} (limᵢ {i = j′} q′ g) e with <ᴵ-dec (σ q′) q
... | injᵃ (via e₁ r) = limᵢ-r (λ z d →
        subst (λ u → Ω j ⊑ᵒ ψ q σ (g (into (<→◃ q′) (tr⁻ e₁ u)))) (sym (out-into (<→◃ r) z))
              (B1 {q = q} {σ = σ} (g (into (<→◃ q′) (tr⁻ e₁ z))) (i-resp e (self-tr⁻ e₁ (≅-reflˡ d)))))
... | injᵇ _ = lim-r 0 (B1 {q = q} {σ = σ} (g (into (<→◃ q′) (Ω j′))) (i-resp e (Ω-refl j′)))
... | injᶜ _ = lim-r 0 (B1 {q = q} {σ = σ} (g (into (<→◃ q′) (Ω j′))) (i-resp e (Ω-refl j′)))
B1 (up zero x) e     = B1 x (u-refl zero e)
B1 (up (self n) x) e = B1 x (u-refl (self n) e)

B1⁰ : ∀ {k} (z : Ordᶜ k) → z ≅ z → Ω zero ⊑ᵒ ψ⁰ z
B1⁰ zero e    = ≅→⊑ᵒ (Ω-refl zero)
B1⁰ (suc a) e = lim-r 1 (B1⁰ a (s-inv e))
B1⁰ (lim h) e = lim-r 0 (B1⁰ (h 0) (l-inv e 0))
B1⁰ (limᵢ {i = j′} q′ g) e = lim-r 0 (B1⁰ (g (into (<→◃ q′) (Ω j′))) (i-resp e (Ω-refl j′)))
B1⁰ (up zero x) e     = B1⁰ x (u-refl zero e)
B1⁰ (up (self n) x) e = B1⁰ x (u-refl (self n) e)

add-r : ∀ {k ℓ ℓ′} {a : Ordᶜ ℓ} {a′ : Ordᶜ ℓ′} {σ : Simᴵ k ℓ′} (b : Ordᶜ k) → a ≅ a′ → b ≅ b → a ⊑ᵒ add a′ σ b
add-r zero ea eb = ≅→⊑ᵒ ea
add-r {σ = σ} (suc b) ea eb = suc-r (add-r {σ = σ} b ea (s-inv eb))
add-r {σ = σ} (lim h) ea eb = lim-r 0 (add-r {σ = σ} (h 0) ea (l-inv eb 0))
add-r {a = a} {a′ = a′} {σ = σ} (limᵢ q g) ea eb = limᵢ-r (λ z d →
  subst (λ u → a ⊑ᵒ add a′ σ (g (into (<→◃ q) u))) (sym (out-into (<→◃ (σ q)) z))
        (add-r {σ = σ} (g (into (<→◃ q) z)) ea (i-resp eb (≅-reflˡ d))))
add-r (up zero x)     ea eb = add-r x ea (u-refl zero eb)
add-r (up (self n) x) ea eb = add-r x ea (u-refl (self n) eb)

zero-l : ∀ {k k′} {y : Ordᶜ k′} → y ≅ y → 𝟎 {k} ⊑ᵒ y
zero-l ey idO         = λ ()
zero-l ey (ψ⁰o o)     = B1⁰ _ ey o
zero-l ey (ψo o)      = B1 _ ey o
zero-l ey (addo o ea) = add-r _ ea ey o
zero-l ey (tro {e′ = e′} o)  = zero-l (self-tr e′ ey) o
zero-l ey (tr⁻o {e′ = e′} o) = zero-l (self-tr⁻ e′ ey) o
```

## §5 $\Omega$ 的单调性 (观测版)

`Ω-monoᵒ : a ⊑ᴵ b → Ω a ⊑ᵒ Ω b`, 对 Level 的 $\sqsubseteq^\mathsf{I}$ 的三个构造子. 与 SafePath §8 的差别:

- `s⊑ e q` 现在给出 $a\cong^\mathsf{I}a'<^\mathsf{I}b$. `Ω<` 带着 $e$ 走 $q$, 在底部 ($b=\mathrm{suc}\,a'$) 用 `Ω-≅ (s≅ e)` 与跨层的 `≅→⊑ᵒ` 换代表元, 这就是 Level 的 `Ω-mono` 在 `s⊑` 情况的做法.
- 后继一步不再写成 "$\Omega_c\sqsubseteq^\mathsf{o}\Omega_{c+1}$ 再传递", 而是直接对 $\Omega_{c+1}=\lim_c\mathtt{up}$ 用 `limᵢ-r`: 对每个 $z\cong\Omega_c$, 递归结果经 `⊑ᵒ-≅ʳ` (同层换右端) 与 `up-r` 落到分支 `up zero z` 上. 于是不需要 SafePath 的 `⊑ᵒ-trans◃`.

```agda
Ω0 : ∀ b → Ω zero ⊑ᵒ Ω b
Ω0 zero      = ≅→⊑ᵒ (Ω-refl zero)
Ω0 (suc b)   = limᵢ-r (λ z d → up-r (⊑ᵒ-≅ʳ (Ω0 b) (≅-sym d)))
Ω0 (lim g s) = lim-r 0 (up-r (Ω0 (g 0)))

Ω< : ∀ {a a′ b} → a ≅ᴵ a′ → a′ <ᴵ b → Ω (suc a) ⊑ᵒ Ω b
Ω< e zero      = ≅→⊑ᵒ (Ω-≅ (s≅ e))
Ω< e (suc q)   = limᵢ-r (λ z d → up-r (⊑ᵒ-≅ʳ (Ω< e q) (≅-sym d)))
Ω< e (lim n q) = lim-r n (up-r (Ω< e q))

Ω-monoᵒ : ∀ {a b} → a ⊑ᴵ b → Ω a ⊑ᵒ Ω b
Ω-monoᵒ {b = b} z⊑ = Ω0 b
Ω-monoᵒ (s⊑ e q)   = Ω< e q
Ω-monoᵒ (l⊑ k)     = lim-l (λ n → up-l (Ω-monoᵒ (k n)))
```

## §6 遗传好树 `Good` 与搬运

`Good` 与 SafePath §9 逐字 (对 $\triangleleft$ 的证明递归定义 `Gd`).

```agda
module _ (ℓ : Ordᴵ) (G< : (i : Ordᴵ) (r : i ◃ ℓ) → U i r → Set) where
  data Good₊ : Ordᶜ ℓ → Set where
    gz : Good₊ zero
    gs : ∀ {a} → Good₊ a → Good₊ (suc a)
    gl : ∀ {h : ℕ → Ordᶜ ℓ} → (∀ n → Good₊ (h n)) → (∀ n → h n ⊑ᵒ h (suc n)) → Good₊ (lim h)
    gi : ∀ {j} {p : j <ᴵ ℓ} {f : U j (<→◃ p) → Ordᶜ ℓ} →
         (∀ (z : Ordᶜ j) → z ≅ z → G< j (<→◃ p) (into (<→◃ p) z) → Good₊ (f (into (<→◃ p) z))) →
         (∀ {z z′ : Ordᶜ j} → z ⊑ᵒ z′ → f (into (<→◃ p) z) ⊑ᵒ f (into (<→◃ p) z′)) →
         Good₊ (limᵢ p f)
    gu : ∀ {k} {r : k ◃₁ ℓ} {x : U k (◃₁→◃ r)} → G< k (◃₁→◃ r) x → Good₊ (up r x)

Gd : ∀ {ℓ} (i : Ordᴵ) (r : i ◃ ℓ) → U i r → Set
Gd i zero         x = Good₊ i Gd x
Gd i (suc r)      x = Gd i r x
Gd _ (self {f} n) x = Good₊ (f n) Gd x
Gd i (lim n r)    x = Gd i r x

Good : ∀ {ℓ} → Ordᶜ ℓ → Set
Good {ℓ} = Good₊ ℓ Gd

Gd→Good : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordᶜ i} → Gd i r (into r x) → Good x
Gd→Good zero      g = g
Gd→Good (suc r)   g = Gd→Good r g
Gd→Good (self n)  g = g
Gd→Good (lim n r) g = Gd→Good r g

Good→Gd : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordᶜ i} → Good x → Gd i r (into r x)
Good→Gd zero      g = g
Good→Gd (suc r)   g = Good→Gd r g
Good→Gd (self n)  g = g
Good→Gd (lim n r) g = Good→Gd r g

Gd-conv : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) (r′ : i ◃ ℓ′) {x : Ordᶜ i} → Gd i r (into r x) → Gd i r′ (into r′ x)
Gd-conv r r′ g = Good→Gd r′ (Gd→Good r g)
```

**为什么观测里要有搬运.** `Good-ψ` (§7) 在穿透分支要证新节点的分支函数 $z'\mapsto\psi(f(\mathtt{tr}^{-}_e z'))$ 好且单调. "好" 要 `Good (tr⁻ e z′)` (喂给 $f$ 的好性条件); "单调" 要从 $z'\sqsubseteq^\mathsf{o}z''$ 推出 $\mathtt{tr}^{-}_e z'\sqsubseteq^\mathsf{o}\mathtt{tr}^{-}_e z''$. 在只有 SafePath 四种观测时后者等于说: 第 $j$ 层上的每对相似观测都能换成第 $j'$ 层上的一对, 结果在 $\cong$ 下不变. `ψo O p σ` 的 `σ : Simᴵ j ℓ` 要换成 `Simᴵ j′ ℓ′`, 但 $c<^\mathsf{I}j'$ 经 `<-≅` 只给出 $c\cong^\mathsf{I}c'<^\mathsf{I}j$, 推不出字面的 $c<^\mathsf{I}\ell$; 而 `ψ` 的类型要字面的 `Sim`. 也试过把 `gi` 的条件改成对 $\cong$ 饱和 (对一切 $z\cong w$, $z'\cong w'$, $w\sqsubseteq^\mathsf{o}w'$), 结果在 `Good-Ω (suc c)` 处要的正是同一个跨层不变性, 绕了一圈 (纸面, 未编译). 把搬运本身算作观测后, 单调性是定义 (`tr-cong`/`tr⁻-cong`), 代价只是 §1–§3 每条归纳多两个情况.

**`Good` 对搬运封闭.** `Good-tr`/`Good-tr⁻`/`Good-back`/`Good-back⁻` 四重互递归, 递归结构与 Level 的 `tr`/`tr⁻`/`res`/`res⁻` 一一对应: `limᵢ` 节点被搬到代表元上, 新分支是 $\mathtt{tr}_e\circ f\circ\mathtt{back}$, 好性由 `Good-back` 与对 `hb` 的应用递归得到, 单调性由 `back-mono` (底部是 `tr⁻-cong` 或 `tr-cong`) 与 `hm`、`tr-cong` 复合. 停机度量是 ($\cong^\mathsf{I}$ 的证明, 好性推导) 的字典序, 与 Level 的 `tr` 相同.

```agda
back-mono : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u u′ : Ordᶜ (rep (res q e))} → u ⊑ᵒ u′ → back (res q e) u ⊑ᵒ back (res q e) u′
back-mono zero      (s≅ e) h = tr⁻-cong h
back-mono (suc q)   (s≅ e) h = back-mono q e h
back-mono (lim n q) (l≅ f) h = back-mono q (f n) h

back⁻-mono : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u u′ : Ordᶜ (rep (res⁻ q e))} → u ⊑ᵒ u′ → back (res⁻ q e) u ⊑ᵒ back (res⁻ q e) u′
back⁻-mono zero      (s≅ e) h = tr-cong h
back⁻-mono (suc q)   (s≅ e) h = back⁻-mono q e h
back⁻-mono (lim n q) (l≅ f) h = back⁻-mono q (f n) h

self-back : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res q e))} → u ≅ u → back (res q e) u ≅ back (res q e) u
self-back q e d = ≅-reflˡ (back-≅ q e d)

self-back⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res⁻ q e))} → u ≅ u → back (res⁻ q e) u ≅ back (res⁻ q e) u
self-back⁻ q e d = ≅-reflˡ (back⁻-≅ q e d)

Good-tr    : ∀ {a b} (e : a ≅ᴵ b) {x : Ordᶜ a} → Good x → Good (tr e x)
Good-tr⁻   : ∀ {a b} (e : a ≅ᴵ b) {x : Ordᶜ b} → Good x → Good (tr⁻ e x)
Good-back  : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res q e))} → Good u → Good (back (res q e) u)
Good-back⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res⁻ q e))} → Good u → Good (back (res⁻ q e) u)

Good-tr e gz         = gz
Good-tr e (gs g)     = gs (Good-tr e g)
Good-tr e (gl hg st) = gl (λ n → Good-tr e (hg n)) (λ n → tr-cong (st n))
Good-tr e (gi {p = q} {f = f} hb hm) = gi
  (λ z ez g → subst (λ w → Good (tr e (f (into (<→◃ q) (back (res q e) w))))) (sym (out-into (<→◃ (lt (res q e))) z))
                    (Good-tr e (hb (back (res q e) z) (self-back q e ez)
                                   (Good→Gd (<→◃ q) (Good-back q e (Gd→Good (<→◃ (lt (res q e))) g))))))
  (λ {z} {z′} h → subst₂ (λ w w′ → tr e (f (into (<→◃ q) (back (res q e) w))) ⊑ᵒ tr e (f (into (<→◃ q) (back (res q e) w′))))
                         (sym (out-into (<→◃ (lt (res q e))) z)) (sym (out-into (<→◃ (lt (res q e))) z′))
                         (tr-cong (hm (back-mono q e h))))
Good-tr (s≅ e) (gu {r = zero} g)   = gu (Good-tr e g)
Good-tr (l≅ f) (gu {r = self n} g) = gu (Good-tr (f n) g)

Good-tr⁻ e gz         = gz
Good-tr⁻ e (gs g)     = gs (Good-tr⁻ e g)
Good-tr⁻ e (gl hg st) = gl (λ n → Good-tr⁻ e (hg n)) (λ n → tr⁻-cong (st n))
Good-tr⁻ e (gi {p = q} {f = f} hb hm) = gi
  (λ z ez g → subst (λ w → Good (tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) w))))) (sym (out-into (<→◃ (lt (res⁻ q e))) z))
                    (Good-tr⁻ e (hb (back (res⁻ q e) z) (self-back⁻ q e ez)
                                    (Good→Gd (<→◃ q) (Good-back⁻ q e (Gd→Good (<→◃ (lt (res⁻ q e))) g))))))
  (λ {z} {z′} h → subst₂ (λ w w′ → tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) w))) ⊑ᵒ tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) w′))))
                         (sym (out-into (<→◃ (lt (res⁻ q e))) z)) (sym (out-into (<→◃ (lt (res⁻ q e))) z′))
                         (tr⁻-cong (hm (back⁻-mono q e h))))
Good-tr⁻ (s≅ e) (gu {r = zero} g)   = gu (Good-tr⁻ e g)
Good-tr⁻ (l≅ f) (gu {r = self n} g) = gu (Good-tr⁻ (f n) g)

Good-back zero      (s≅ e) g = Good-tr⁻ e g
Good-back (suc q)   (s≅ e) g = Good-back q e g
Good-back (lim n q) (l≅ f) g = Good-back q (f n) g

Good-back⁻ zero      (s≅ e) g = Good-tr e g
Good-back⁻ (suc q)   (s≅ e) g = Good-back⁻ q e g
Good-back⁻ (lim n q) (l≅ f) g = Good-back⁻ q (f n) g
```

## §7 封闭性

`Good-Ω`, `Good-add`, `Good-iter`, `rule4ᵒ`, `chain-step`, `Good-ψ`, `Good-ψ⁰` 的陈述与 SafePath §9 相同. 改动:

- `Good-Ω (lim g s)` 的步进取层号自带的证据 `s n : g n ⊑ᴵ g (suc n)` (模 $\cong^\mathsf{I}$), 经 `Ω-monoᵒ`. 这就是 SafePath 的 `ΩStep-all` 在 `Ordᴵ` 上的形状: 不需要另一个前提, 因为 `Ω-monoᵒ` 吃的正是模 $\cong^\mathsf{I}$ 的证据.
- `Good-ψ` 的穿透分支: 新分支是 $\psi\circ f\circ\mathtt{tr}^{-}_e$, 好性用 `Good-tr⁻`, 自反用 `self-tr⁻` 与 `i-resp`, 单调用 `tr⁻-cong`. 链分支 (第二、三种派发) 与 SafePath 逐字, 只是 `ψ-≅` 多一个 `≅ᴵ-refl`.
- `chain-≅`, `chain-step` 用 `i-resp` 代替 `i-inv`.

```agda
Good-Ω : ∀ a → Good (Ω a)
Good-Ω zero      = gs gz
Good-Ω (suc c)   = gi (λ z ez g → gu g) (λ h → up-l (up-r h))
Good-Ω (lim g s) = gl (λ n → gu (Good-Ω (g n))) (λ n → up-l (up-r (Ω-monoᵒ (s n))))

Good-add : ∀ {k ℓ} {a : Ordᶜ ℓ} {σ : Simᴵ k ℓ} {b : Ordᶜ k} → Good a → a ≅ a → Good b → Good (add a σ b)
Good-add ga ea gz          = ga
Good-add ga ea (gs g)      = gs (Good-add ga ea g)
Good-add ga ea (gl hg st)  = gl (λ n → Good-add ga ea (hg n)) (λ n → add-cong ea (st n))
Good-add {a = a} {σ = σ} ga ea (gi {p = q} {f = f} hb hm) = gi
  (λ z ez g → subst (λ u → Good (add a σ (f (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ q)) z))
                    (Good-add ga ea (hb z ez (Gd-conv (<→◃ (σ q)) (<→◃ q) g))))
  (λ {z} {z′} h → subst₂ (λ u v → add a σ (f (into (<→◃ q) u)) ⊑ᵒ add a σ (f (into (<→◃ q) v)))
                         (sym (out-into (<→◃ (σ q)) z)) (sym (out-into (<→◃ (σ q)) z′)) (add-cong ea (hm h)))
Good-add ga ea (gu {r = zero} g)   = Good-add ga ea g
Good-add ga ea (gu {r = self n} g) = Good-add ga ea g

Good-iter : ∀ {ℓ} {c : Ordᶜ ℓ} → Good c → c ≅ c → ∀ n → Good (iter (c +_) zero n)
Good-iter gc ec zero    = gz
Good-iter gc ec (suc n) = Good-add gc ec (Good-iter gc ec n)

rule4ᵒ : ∀ {ℓ} {c : Ordᶜ ℓ} → c ≅ c → ∀ n → iter (c +_) zero n ⊑ᵒ iter (c +_) zero (suc n)
rule4ᵒ ec zero    = zero-l ec
rule4ᵒ ec (suc n) = add-cong ec (rule4ᵒ ec n)

chain : ∀ {j k} (q : j <ᴵ k) (f : U j (<→◃ q) → Ordᶜ k) → ℕ → Ordᶜ j
chain {j} q f = iter (λ x → ψ q (λ r → r) (f (into (<→◃ q) x))) (Ω j)

chain-≅ : ∀ {j k k′} {q : j <ᴵ k} {f : U j (<→◃ q) → Ordᶜ k} {b : Ordᶜ k′} → limᵢ q f ≅ b → ∀ n → chain q f n ≅ chain q f n
chain-≅ {j} e zero    = Ω-refl j
chain-≅ {j} {q = q} e (suc n) = ψ-≅ {p = q} {σ = λ r → r} {p′ = q} {σ′ = λ r → r} (≅ᴵ-refl j) (i-resp e (chain-≅ e n))

chain-step : ∀ {j k k′} {q : j <ᴵ k} {f : U j (<→◃ q) → Ordᶜ k} {b : Ordᶜ k′} → limᵢ q f ≅ b →
             (∀ {z z′ : Ordᶜ j} → z ⊑ᵒ z′ → f (into (<→◃ q) z) ⊑ᵒ f (into (<→◃ q) z′)) →
             ∀ n → chain q f n ⊑ᵒ chain q f (suc n)
chain-step {j} {q = q} {f = f} e hm zero = B1 {q = q} {σ = λ r → r} (f (into (<→◃ q) (Ω j))) (i-resp e (Ω-refl j))
chain-step e hm (suc n) = ψ-cong (hm (chain-step e hm n))

Good-ψ : ∀ {i k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {x : Ordᶜ k} → Good x → x ≅ x → Good (ψ p σ x)
chain-good : ∀ {j k} {q : j <ᴵ k} {f : U j (<→◃ q) → Ordᶜ k} →
             (∀ (z : Ordᶜ j) → z ≅ z → Gd j (<→◃ q) (into (<→◃ q) z) → Good (f (into (<→◃ q) z))) →
             limᵢ q f ≅ limᵢ q f → ∀ n → Good (chain q f n)
chain-good {j} hb e zero = Good-Ω j
chain-good {q = q} {f = f} hb e (suc n) =
  Good-ψ (hb (chain q f n) (chain-≅ e n) (Good→Gd (<→◃ q) (chain-good hb e n))) (i-resp e (chain-≅ e n))

Good-ψ {i} gz ex = Good-Ω i
Good-ψ {i} {p = p} {σ = σ} (gs {a} g) ex = gl (Good-iter (Good-ψ g ea) eψ) (rule4ᵒ eψ)
  where ea = s-inv ex
        eψ = ψ-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} (≅ᴵ-refl i) ea
Good-ψ (gl hg st) ex = gl (λ n → Good-ψ (hg n) (l-inv ex n)) (λ n → ψ-cong (st n))
Good-ψ {p = p} {σ = σ} (gi {j = j} {p = q} {f = f} hb hm) ex with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = gi
  (λ z ez g → subst (λ u → Good (ψ p σ (f (into (<→◃ q) (tr⁻ e u))))) (sym (out-into (<→◃ r) z))
                    (Good-ψ (hb (tr⁻ e z) (self-tr⁻ e ez) (Good→Gd (<→◃ q) (Good-tr⁻ e (Gd→Good (<→◃ r) g))))
                            (i-resp ex (self-tr⁻ e ez))))
  (λ {z} {z′} h → subst₂ (λ u v → ψ p σ (f (into (<→◃ q) (tr⁻ e u))) ⊑ᵒ ψ p σ (f (into (<→◃ q) (tr⁻ e v))))
                         (sym (out-into (<→◃ r) z)) (sym (out-into (<→◃ r) z′)) (ψ-cong (hm (tr⁻-cong h))))
... | injᵇ _ = gl (λ n → Good-ψ (hb (chain q f n) (chain-≅ ex n) (Good→Gd (<→◃ q) (chain-good hb ex n)))
                                (i-resp ex (chain-≅ ex n)))
                  (λ n → ψ-cong (hm (chain-step ex hm n)))
... | injᶜ _ = gl (λ n → Good-ψ (hb (chain q f n) (chain-≅ ex n) (Good→Gd (<→◃ q) (chain-good hb ex n)))
                                (i-resp ex (chain-≅ ex n)))
                  (λ n → ψ-cong (hm (chain-step ex hm n)))
Good-ψ (gu {r = zero} g) ex   = Good-ψ g (u-refl zero ex)
Good-ψ (gu {r = self n} g) ex = Good-ψ g (u-refl (self n) ex)

Good-ψ⁰ : ∀ {k} {x : Ordᶜ k} → Good x → x ≅ x → Good (ψ⁰ x)
Good-ψ⁰ gz ex = gs gz
Good-ψ⁰ (gs {a} g) ex = gl (Good-iter (Good-ψ⁰ g ea) (ψ⁰-≅ ea)) (rule4ᵒ (ψ⁰-≅ ea))
  where ea = s-inv ex
Good-ψ⁰ (gl hg st) ex = gl (λ n → Good-ψ⁰ (hg n) (l-inv ex n)) (λ n → ψ⁰-cong (st n))
Good-ψ⁰ (gi {p = q} {f = f} hb hm) ex =
  gl (λ n → Good-ψ⁰ (hb (chain q f n) (chain-≅ ex n) (Good→Gd (<→◃ q) (chain-good hb ex n))) (i-resp ex (chain-≅ ex n)))
     (λ n → ψ⁰-cong (hm (chain-step ex hm n)))
Good-ψ⁰ (gu {r = zero} g) ex   = Good-ψ⁰ g (u-refl zero ex)
Good-ψ⁰ (gu {r = self n} g) ex = Good-ψ⁰ g (u-refl (self n) ex)
```

## §8 第 0 层: 好树遗传步进

`HS` 是 Level §9 的数据类型 (步进关系 `_⊑⁰_`, 即 Level 的 $\sqsubseteq$ 在第 0 层的实例, 叶子 $\cong$). SafePath 自己定义了一个同形的 `HS`, 这里不再定义: 恒等观测 `idO` 下 $\sqsubseteq^\mathsf{o}$ 的定义展开就是 `_⊑⁰_`, `Good→HS` 直接落在 Level 的 `HS` 上.

```agda
Good→HS : ∀ {x : Ordᶜ zero} → Good x → HS x
Good→HS gz         = hz
Good→HS (gs g)     = hs (Good→HS g)
Good→HS (gl hg st) = hl (λ n → Good→HS (hg n)) (λ n → st n idO)
Good→HS (gi {p = ()} hb hm)
Good→HS (gu {r = ()} g)
```

## §9 一致引理

```agda
Uniform : ∀ (a : Ordᴵ) → HS (ψ⁰ (Ω a))
Uniform a = Good→HS (Good-ψ⁰ (Good-Ω a) (Ω-refl a))
```

这是 Diagonal 的模块参数的类型, 逐字相同. 依赖链: `Good-Ω a` (层号 $a$ 的每个极限步经 `Ω-monoᵒ`) → `Good-ψ⁰` (规则 4 经 `rule4ᵒ`, 规则 6 经 `chain-step`, 链上各点的好性经 `chain-good`/`Good-ψ`, 穿透经 `Good-tr⁻`) → `Good→HS` (观测取 `idO`).

**精确接口 `ΩStep`.** 与 SafePath 相同, `Uniform` 只用到 `Good (Ω a)`, 而这只依赖极限脊上的观测步进. 对 `Ordᴵ` 它总成立 (`ΩStep-all`), 证据就是层号的 `lim` 自带的 $t\,n:g\,n\sqsubseteq^\mathsf{I}g(n+1)$ 经 `Ω-monoᵒ`.

```agda
data ΩStep : Ordᴵ → Set where
  z : ΩStep zero
  s : ∀ {c} → ΩStep (suc c)
  l : ∀ {g : ℕ → Ordᴵ} {t : ∀ n → g n ⊑ᴵ g (suc n)} →
      (∀ n → ΩStep (g n)) → (∀ n → Ω (g n) ⊑ᵒ Ω (g (suc n))) → ΩStep (lim g t)

Good-Ωˢ : ∀ {a} → ΩStep a → Good (Ω a)
Good-Ωˢ z        = gs gz
Good-Ωˢ (s {c})  = Good-Ω (suc c)
Good-Ωˢ (l h st) = gl (λ n → gu (Good-Ωˢ (h n))) (λ n → up-l (up-r (st n)))

ΩStep-all : ∀ a → ΩStep a
ΩStep-all zero      = z
ΩStep-all (suc c)   = s
ΩStep-all (lim g t) = l (λ n → ΩStep-all (g n)) (λ n → Ω-monoᵒ (t n))

Uniformˢ : ∀ {a} → ΩStep a → HS (ψ⁰ (Ω a))
Uniformˢ {a} h = Good→HS (Good-ψ⁰ (Good-Ωˢ h) (Ω-refl a))
```

## §10 检验

**第四行 (SafePath 检验 1、2).** $\Omega_{c+1}$ 的 $\psi_c$-链 $\gamma^c$ 与 `ψ⁰` 的展开 `refl` 一致; 链步进的第 0 步是 `B1` 作用于 `up zero (Ω c)`, 其后是 `ψ-cong`. 用观测 `ψ⁰o idO` 得到第 0 层的 $\sqsubseteq$, 对任意层号 $c$.

```agda
γᶜ : ∀ c → ℕ → Ordᶜ c
γᶜ c = iter (λ x → ψ zero (λ r → r) (up zero x)) (Ω c)

_ : ∀ c → ψ⁰ (Ω (suc c)) ≡ lim (λ n → ψ⁰ (γᶜ c n))
_ = λ c → refl

γᶜ-step : ∀ c n → γᶜ c n ⊑ᵒ γᶜ c (suc n)
γᶜ-step c zero    = B1 {q = zero} {σ = λ r → r} (up zero (Ω c)) (upˡ (upʳ (Ω-refl c)))
γᶜ-step c (suc n) = ψ-cong {p = zero} {p′ = zero} {σ = λ r → suc r} {σ′ = λ r → suc r} (γᶜ-step c n)

row4 : ∀ c n → ψ⁰ (γᶜ c n) ⊑ ψ⁰ (γᶜ c (suc n))
row4 c n = γᶜ-step c n (ψ⁰o idO)
```

**$x_3$ (SafePath 检验 3).** Level 没有 $\varepsilon_0$ 的层号 (Cumulative 的 `ε₀ʷ` 是 `Ordʷ` 上用 `ψ⁰ʷ` 造的). 在本族上它的自然来源是 `toLevel`: $x_2=\psi^0(\Omega_1)$ 是第 0 层的树 (EBO 的 $\varepsilon_0=\psi_0(\Omega_1)$, 基本列是第 0 层的链 $\psi^0(G_n)$), `Uniform 1` 给它发证书, `toLevel` 把它变成层号. 这也正是 Diagonal 的 `L 1`. $x_3=\psi^0(\Omega_{\varepsilon_0})$ 的遗传步进是 `Uniform` 的特例; 它的基本列逐项是 $\psi^0(\Omega_{\mathtt{toLevel}(\psi^0(G_n))})$ (`refl`).

```agda
Ω₁ : Ordᶜ (suc zero)
Ω₁ = Ω (suc zero)

ψ₀ : Ordᶜ (suc zero) → Ordᶜ zero
ψ₀ = ψ zero (λ q → q)

G : ℕ → Ordᶜ zero
G = iter (λ x → ψ₀ (up zero x)) (suc zero)

x₂ : Ordᶜ zero
x₂ = ψ⁰ Ω₁

_ : x₂ ≡ lim (λ n → ψ⁰ (G n))
_ = refl

ε₀ᴵ : Ordᴵ
ε₀ᴵ = toLevel x₂ (Uniform (suc zero))

_ : ∀ n → ε₀ᴵ [ n ]ᴵ ≡ toLevel (ψ⁰ (G n)) (hl₁ (Uniform (suc zero)) n)
_ = λ n → refl

x₃ : Ordᶜ zero
x₃ = ψ⁰ (Ω ε₀ᴵ)

_ : x₃ ≡ lim (λ n → ψ⁰ (Ω (toLevel (ψ⁰ (G n)) (hl₁ (Uniform (suc zero)) n))))
_ = refl

HS-x₃ : HS x₃
HS-x₃ = Uniform ε₀ᴵ
```

**反例对被拒绝 (SafePath 检验 5).** Level 没有移植 `ψ-not-⊑mono` (Level §10 末: "原样成立"); 这里在本族上重述 (定义与 Cumulative §10 逐字, `ψ-≅` 多一个 `≅ᴵ-refl`) 并编译. $\mathrm{suc}\,a_1\sqsubseteq\Omega_1$, 但 $\psi_0(\mathrm{suc}\,a_1)\not\sqsubseteq\psi_0(\Omega_1)$; $\psi_0$ 是观测 `ψo idO zero id`, 所以 $\mathrm{suc}\,a_1\not\sqsubseteq^\mathsf{o}\Omega_1$. 加入搬运观测只让 $\sqsubseteq^\mathsf{o}$ 更强 (要对更多观测对成立), 拒绝自然保持.

```agda
E : Ordᶜ zero
E = lim (G ∘ suc)

_ : ψ₀ Ω₁ ≡ E
_ = refl

a₁ : Ordᶜ (suc zero)
a₁ = up zero (lim G)

_ : ψ₀ a₁ ≡ E
_ = refl

G-refl : ∀ n → G n ≅ G n
G-refl zero    = s≅ z≅
G-refl (suc n) = ψ-≅ {p = zero} {σ = λ q → suc q} {p′ = zero} {σ′ = λ q → suc q} (≅ᴵ-refl zero) (G-refl n)

lG : lim G ≅ lim G
lG = l≅ G-refl

E≅E : E ≅ E
E≅E = l≅ (λ n → G-refl (suc n))

suca₁⊑Ω₁ : suc a₁ ⊑ Ω₁
suca₁⊑Ω₁ (≺z e)      = ≺i (suc (lim G)) (s≅ lG) (≺u (≺z (≅-trans e (upˡ lG))))
suca₁⊑Ω₁ (≺s (≺u h)) = ≺i (suc (lim G)) (s≅ lG) (≺u (≺s h))

E≺ : E ≺ ψ₀ (suc a₁)
E≺ = ≺l 2 (≺l 0 (≺l 1 (≺z E≅E)))

ψ-not-⊑mono : (suc a₁ ⊑ Ω₁) × ¬ (ψ₀ (suc a₁) ⊑ ψ₀ Ω₁)
ψ-not-⊑mono = suca₁⊑Ω₁ , λ h → ≺-irrefl (h E≺)

⊑ᵒ-rejects : ¬ (suc a₁ ⊑ᵒ Ω₁)
⊑ᵒ-rejects h = proj₂ ψ-not-⊑mono (h (ψo {p = zero} {p′ = zero} {σ = λ q → q} {σ′ = λ q → q} idO))
```

SafePath §1 的 C1 反例对 ($\uparrow^2\Omega_1$ 对 $\uparrow^2\varepsilon_0$) 仍只是纸面论证, 未编译.

## §11 移植清单

相对 [SafePath](SafePath.lagda.md) (族 Cumulative → Level, 下标 `Ordʷ` → `Ordᴵ`):

| 名字 | 状态 | 说明 |
|---|---|---|
| `Obs`, `run`, `≈ᵒ` | 加两个构造子 | `tro`/`tr⁻o` (搬运观测); `ψo` 仍同目标层 |
| `≈ᵒ-reflˡ/ʳ`, `run-≅`, `≅→⊑ᵒ` | 多两个情况 | `run-≅` 的 `ψo` 情况 `ψ-≅ (≅ᴵ-refl _)`; 搬运情况 `tr-≅`/`≅-tr` |
| `⊑ᵒ-trans`, `⊑ᵒ-transˡ`, `⊑ᵒ-trans◃`, `retarget`, `◃→Sim` | 删去 | 上界引理改以 $\sqsubseteq^\mathsf{o}$ 为假设后不需要; 只留同层换右端 `⊑ᵒ-≅ʳ` |
| `ψ-cong`, `ψ⁰-cong`, `add-cong` | 逐字 | |
| `tr-cong`, `tr⁻-cong` | 新 | 一行 |
| `up-l`, `up-r` | 多四个情况 | 搬运观测下先拆 $\cong^\mathsf{I}$ 证明 |
| `lim-r`, `suc-r` | 假设 $\cong$ → $\sqsubseteq^\mathsf{o}$ | 更强, 证明同形 |
| `lim-l` | 多两个情况 | |
| `limᵢ-r` | 假设改为 "对一切 $z\cong\Omega_j$, $x\sqsubseteq^\mathsf{o}g(z)$" | 穿透经 `tr⁻-≅`; 搬运观测经 `back-≅`/`back⁻-≅` |
| `B1`, `B1⁰`, `add-r`, `zero-l` | 陈述逐字, 证明变短 | 不再经传递 |
| `s-inv`, `l-inv`, `u-inv`, `u-refl` | 逐字 | |
| `i-inv` | 换成 `i-resp` | 相关输入给出相关输出 (`lᵢ≅` 两边可在不同层) |
| `Ω-suc`, `Ω0`, `Ω<`, `Ω-monoᵒ` | `Ω-suc` 并入; `Ω<` 带 $a\cong^\mathsf{I}a'$ | `s⊑ e q` 经 `Ω-≅ (s≅ e)` 换代表元 |
| `Good₊`, `Gd`, `Good`, 转换 | 逐字 | |
| `Good-tr`, `Good-tr⁻`, `Good-back`, `Good-back⁻`, `back-mono`, `back⁻-mono` | 新 | 搬运保持好性 |
| `Good-Ω`, `Good-add`, `Good-iter`, `rule4ᵒ`, `Good-ψ⁰` | 逐字 (`ψ⁰≅` → Level 的 `ψ⁰-≅`) | |
| `Good-ψ` | 改穿透分支 | `Good-tr⁻`, `tr⁻-cong` |
| `chain`, `chain-≅`, `chain-good`, `chain-step` | 几乎逐字 | `i-resp` |
| `HS` | 不再定义 | 用 Level 的 `HS` |
| `Good→HS` | 逐字 | |
| `HS-diag` → `Uniform`, `ΩStep`, `ΩStep-all`, `HS-diagˢ` → `Uniformˢ` | 陈述逐字 (下标换成 `Ordᴵ`) | |
| `γᶜ`, `γᶜ-step`, `row4` | 逐字 | |
| `HS-x₃` | 层号换成 `toLevel` 造的 `ε₀ᴵ` | Level 无 `ε₀ʷ` 对应物 |
| `Ω₁`, `ψ₀`, `G`, `E`, `a₁`, `ψ-not-⊑mono`, `⊑ᵒ-rejects` | 在本族重述 | Level 未移植反例 |

没有移植失败的定理. SafePath 的 `row4-c1` 是 `row4 (suc zero)`, 不另列.

## §12 结论与边界

**已证** (`--safe --without-K`, 无公设、无洞、无编译指示):

1. `Uniform : ∀ (a : Ordᴵ) → HS (ψ⁰ (Ω a))`, 无前提, `HS` 为 Level 的 `HS`. Diagonal 的模块参数由此兑现 (见 [NoCumsum](NoCumsum.lagda.md)).
2. 带搬运的观测前序 $\sqsubseteq^\mathsf{o}$: 同余 (含 `tr-cong`/`tr⁻-cong`)、上界 (`lim-r`, `lim-l`, `suc-r`, `limᵢ-r`, `add-r`, `zero-l`)、链起点 (`B1`, `B1⁰`)、`Ω-monoᵒ`.
3. `Good` 对 $\Omega$, 加法, $\psi_p\sigma$, `ψ⁰`, `tr`, `tr⁻` 封闭; `chain-step`.
4. 检验: `row4` (任意 $c$), `HS-x₃`, `⊑ᵒ-rejects`.

**边界.**

- 步进仍是模 $\cong$ 的 ($\sqsubseteq$ 的叶子是 $\cong$), 与 Level 的 `HS` 一致; 这正是 Level 的 `toLevel` 吃的形式, 所以不再是缺口.
- 观测前序比 SafePath 的强 (多了搬运观测), 这是被迫的: 没有它 `Good-ψ` 的穿透分支要的 "`tr⁻` 单调" 证不出 (§6 开头的论证是纸面的; 编译过的是带搬运的版本).
- 相似关系没有放宽到 $\cong^\mathsf{I}$-相关的目标层; 是否可以放宽 (`run-≅` 有 `ψ-≅ ei` 可用) 没有试, 因为没有用处.
- 本文不改 `src/`、`archive/` 与已有的 Align 文件.
