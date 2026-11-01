# 无 cumsum 的 BTBO: 闭合的对角线

> 接 [Level](Level.lagda.md), [Diagonal](Diagonal.lagda.md), [Uniform](Uniform.lagda.md). Diagonal 以 `Uniform : ∀ (a : Ordᴵ) → HS (ψ⁰ (Ω a))` 为模块参数组装了扩展 Buchholz 记号 (EBO) 的 $\psi_0(\Omega_\Omega)$ 的规则 6 链; Uniform 证出了这条引理. 本文把二者接上, 得到一个**闭合的、带证书的、不用 `cumsum`/`ordᴰ` 的 BTBO 定义**, 并把完整定义集中列在一处 (§3), 供决定是否进入 `src/` 时阅读.
>
> 结论先说:
>
> 1. **闭项.** `BTBOᴵ : Ordᶜ zero`, 证书 `BTBO-HS : HS BTBOᴵ`, 它作为层号 `BTBOᴸ : Ordᴵ`, 以及 `big = FGH BTBOᴵ 99`, 都是闭项, 不依赖任何假设 (§1). 全部依赖链: Level (下标类型、树族、折叠、证书) → Uniform (安全路径引理) → Diagonal (对角线) → 本文.
> 2. **规则 6 的形状仍是 `refl`.** Diagonal §1 的六条事实在 `Uniform` 具体化之后逐条以 `refl` 重新检查通过 (§1): `γ 0 ≡ suc zero`, `γ (suc n) ≡ ψ⁰ (Ω (L n))`, `BTBOᴵ ≡ lim (γ ∘ suc)`, `γ 1 ≡ lim (ψ⁰ ∘ G)`, `L 1 [ n ]ᴵ ≡ toLevel (ψ⁰ (G n)) _`, `Ω BTBOᴸ ≡ lim (λ n → up (self n) (Ω (L (suc n))))`. 这是预期的: 它们在参数抽象时已经是定义性的, 代入具体证明不会破坏定义性相等; `toLevel` 对树递归, 层号的骨架不读证书.
> 3. **值不依赖 `Uniform` 的证明 (模 $\cong$).** 字面的树 `BTBOᴵ` 依赖证书的证明项: 层号 `lim` 的步进证据来自证书, 而 $\psi$ 的派发 `<ᴵ-dec` 在 `lim`/`lim` 且下标不同时读这个证据, 决定穿透输出挂在哪个代表元上. 但对**任意**另一个证明 `U′`, 两条对角线逐项 $\cong$ (`γ-indep`), 极限 $\cong$, FGH 逐点相等 (`FGH-indep`), 层号 $\cong^\mathsf{I}$ (`BTBOᴸ-indep`). 所以 "BTBO 的值" 是良定义的, 只是 "BTBO 的那棵树" 依赖证明, 精确到 $\cong$.
> 4. **FGH (§2).** 参数为 1 的全部 `refl` 且瞬时: $\gamma_1,\ldots,\gamma_4$, `BTBOᴵ`, 下一阶段的第一项 $\psi^0(\Omega_{\mathtt{BTBO}^\mathsf{L}})$, 都给 2. 参数为 2 的只到 $\gamma_0$ ($f_1(2)=4$) 与 $\psi^0(\Omega_0)=\omega$ ($f_\omega(2)=8$); $\gamma_1$ 起在 60 秒内算不完 (记录在 §2). src 的 BTBO 一侧情况相同 (Diagonal §3 的结论在具体 `Uniform` 下不变).
> 5. **标签仍是估计.** 外层规则 6 的形状与 EBO 的 $\psi_0(\Omega_\Omega)$ 一致 (`refl`); 每个 $\gamma_k$ 的内部与 EBO 的 $\gamma_k$ 的基本列一致性没有证, 所以 "BTBOᴵ $=\psi_0(\Omega_\Omega)$" 是估计 (§4).
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只读引用 src 的 BTBO.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoCumsum where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.BTBO using (module Ord-Ord)
module Src = Ord-Ord
open import OCF.Align.Level
open import OCF.Align.Diagonal using (module Diagonal)
open import OCF.Align.Uniform using (Uniform; ε₀ᴵ)
```

## §1 闭合的对角线

把 Uniform 的定理代入 Diagonal 的参数. 下面的名字都是闭项 (模块实例化之后再取出, 类型写全, 便于独立阅读).

```agda
module D = Diagonal Uniform

γ : ℕ → Ordᶜ zero
γ = D.γ

cert : ∀ n → HS (γ n)
cert = D.cert

L : ℕ → Ordᴵ
L = D.L

BTBOᴵ : Ordᶜ zero
BTBOᴵ = D.BTBOᴵ

BTBO-HS : HS BTBOᴵ
BTBO-HS = D.BTBO-HS

BTBOᴸ : Ordᴵ
BTBOᴸ = D.BTBOᴸ

big : ℕ
big = FGH BTBOᴵ 99
```

**规则 6 的形状 (Diagonal §1–§2, 具体 `Uniform` 下重新检查).** 起点 $\gamma_0=\Omega_0=1$, 层号 $L_0=1$; $\gamma_{n+1}=\psi_0(\Omega_{L_n})$; 对角线是 $\gamma\circ\mathrm{suc}$ 的极限; $\gamma_1=\psi_0(\Omega_1)$ 内部是第 0 层的链 $G$; $L_1$ 逐项是 $\psi_0(G_n)$ 的层号; 极限的 $\Omega$ 是对角 $\mathbb{N}$-极限. 另加三条只在具体化之后才能陈述的: $\gamma_1$ 的证书就是 `Uniform 1`, 它的层号就是 Uniform §10 的 $\varepsilon_0$ 层号 `ε₀ᴵ`, 每个 $L_{n+1}$ 的证书是 `Uniform (L n)`.

```agda
_ : γ 0 ≡ suc zero
_ = refl

_ : L 0 ≡ suc zero
_ = refl

_ : ∀ n → γ (suc n) ≡ ψ⁰ (Ω (L n))
_ = λ n → refl

_ : BTBOᴵ ≡ lim (γ ∘ suc)
_ = refl

_ : γ 1 ≡ lim (ψ⁰ ∘ D.G)
_ = refl

_ : ∀ n → L 1 [ n ]ᴵ ≡ toLevel (ψ⁰ (D.G n)) _
_ = λ n → refl

_ : Ω BTBOᴸ ≡ lim (λ n → up (self n) (Ω (L (suc n))))
_ = refl

_ : BTBOᴸ [ 0 ]ᴵ ≡ L 1
_ = refl

_ : cert 1 ≡ Uniform (suc zero)
_ = refl

_ : L 1 ≡ ε₀ᴵ
_ = refl

_ : ∀ n → cert (suc n) ≡ Uniform (L n)
_ = λ n → refl
```

`L 1 [ n ]ᴵ` 那一行的下划线由合一解出 (Diagonal 写的是 `hl₁ (cert 1) n`). 全部都是 `refl`: 这些相等在 Diagonal 里对抽象的 `Uniform` 已经成立, 定义性相等对代换封闭; 具体化唯一可能的影响是让检查器多做归约, 实测没有 (本文件单独检查约 2 秒).

**值不依赖 `Uniform` 的证明.** 对任意另一个证明 `U′` (例如把 Uniform 里的某个引理换一种证法), 对角线逐项 $\cong$: $\gamma_0$ 两边相同; 由 $\gamma_n\cong\gamma'_n$ 得层号 $L_n\cong^\mathsf{I}L'_n$ (Level 的 `toLevel-≅`, 两边证书任意), 再经 `Ω-≅` 与 `ψ⁰-≅`. FGH 在 $\cong$ 下不变 (`FGH-≅`).

```agda
module _ (U′ : ∀ (a : Ordᴵ) → HS (ψ⁰ (Ω a))) where
  module D′ = Diagonal U′

  γ-indep : ∀ n → γ n ≅ D′.γ n
  γ-indep zero    = s≅ z≅
  γ-indep (suc n) = ψ⁰-≅ (Ω-≅ (toLevel-≅ (cert n) (D′.cert n) (γ-indep n)))

  BTBO-indep : BTBOᴵ ≅ D′.BTBOᴵ
  BTBO-indep = l≅ (λ n → γ-indep (suc n))

  FGH-indep : ∀ n → FGH BTBOᴵ n ≡ FGH D′.BTBOᴵ n
  FGH-indep = FGH-≅ BTBO-indep

  BTBOᴸ-indep : BTBOᴸ ≅ᴵ D′.BTBOᴸ
  BTBOᴸ-indep = toLevel-≅ BTBO-HS D′.BTBO-HS BTBO-indep
```

## §2 FGH 测试

每个测试先在临时文件里单独以 `timeout 60` 检查 (墙钟时间含加载接口, 加载本身约 2.1 秒); 算完的写成下面的 `refl`, 算不完的只记录.

| 测试 | 结果 | 墙钟 |
|---|---|---|
| `FGH (γ 0) 2` | 4 ($f_1(2)$) | 2.1 s |
| `FGH (γ 0) 10` | 20 | 2.5 s |
| `FGH (ψ⁰ (Ω zero)) 2` | 8 ($f_\omega(2)$) | 2.5 s |
| `FGH (γ 1) 1` | 2 | 2.5 s |
| `FGH (γ 2) 1` | 2 | 2.5 s |
| `FGH (γ 3) 1` | 2 | 2.5 s |
| `FGH (γ 4) 1` | 2 | 2.5 s |
| `FGH BTBOᴵ 1` | 2 | 2.5 s |
| `FGH (ψ⁰ (Ω (suc (suc zero)))) 1` | 2 | 2.5 s |
| `FGH (ψ⁰ (Ω BTBOᴸ)) 1` | 2 (下一阶段的第一项) | 2.6 s |
| `Src.FGH (Src.ψⁿ 1) 2` | 8 | 2.6 s |
| `Src.FGH (Src.ψⁿ 2) 1` | 2 | 2.6 s |
| `Src.FGH Src.BTBO 1` | 2 | 2.6 s |
| `FGH (ψ⁰ (Ω zero)) 3` | 超时 (60 s, 退出码 124) | — |
| `FGH (γ 1) 2` | 超时 | — |
| `FGH (ψ⁰ (Ω (suc zero))) 2` | 超时 (同上, $\gamma_1$ 的另一写法) | — |
| `FGH BTBOᴵ 2` | 超时 | — |
| `Src.FGH (Src.ψⁿ 2) 2` | 超时 | — |

```agda
_ : FGH (γ 0) 2 ≡ 4
_ = refl

_ : FGH (γ 0) 10 ≡ 20
_ = refl

_ : FGH (ψ⁰ (Ω zero)) 2 ≡ 8
_ = refl

_ : FGH (γ 1) 1 ≡ 2
_ = refl

_ : FGH (γ 2) 1 ≡ 2
_ = refl

_ : FGH (γ 3) 1 ≡ 2
_ = refl

_ : FGH (γ 4) 1 ≡ 2
_ = refl

_ : FGH BTBOᴵ 1 ≡ 2
_ = refl

_ : FGH (ψ⁰ (Ω (suc (suc zero)))) 1 ≡ 2
_ = refl

_ : FGH (ψ⁰ (Ω BTBOᴸ)) 1 ≡ 2
_ = refl

_ : Src.FGH (Src.ψⁿ 1) 2 ≡ 8
_ = refl

_ : Src.FGH (Src.ψⁿ 2) 1 ≡ 2
_ = refl

_ : Src.FGH Src.BTBO 1 ≡ 2
_ = refl
```

**读法.** 参数为 1 的测试沿基本列 $[1]$ 一路下降到 0, 值恒为 2; 它们说明的是计算路径通畅: 具体证书没有拖慢任何一步 (Diagonal §3 的说明: 这条路径不读步进证据, 而且 Agda 的归约是惰性的). 参数为 2 的比较只到 $\gamma_0=1$ 与 $\psi^0(\Omega_0)=\omega$, 与 src 的 $\psi^n\,1=\omega$ 同值 8; 从 $\gamma_1=\varepsilon_0$ 与 src 的 $\psi^n\,2$ 起, 一进制自然数写不下结果 ($f_{\varepsilon_0}(2)$ 下降到 $f_{\omega+1}(2)=f_\omega(8)=f_8(8)$ 一类的值). 与 src 的逐项对照表 (起点、$\Omega_0$、链起点、层号、提升、下标类型) 在 Diagonal §3, 具体化不改变其中任何一行. 两条对角线的值交错, 极限都是估计的 $\psi_0(\Omega_\Omega)$.

## §3 定义一览

完整的无 cumsum 定义, 按依赖顺序. 每项只给读者需要的几行代码 (不参与编译), 并指向证明或完整定义所在处. 读者可以只读这一节.

**1. 下标类型 (Level §1).** 四个类型归纳-归纳地同时定义. `lim` 的证据是**模互模拟**的前驱包含: $\mathrm{suc}\,a\sqsubseteq^\mathsf{I}b$ 当且仅当 $a\cong^\mathsf{I}a'<^\mathsf{I}b$.

    data Ordᴵ where
      zero : Ordᴵ
      suc  : Ordᴵ → Ordᴵ
      lim  : (f : ℕ → Ordᴵ) (s : ∀ n → f n ⊑ᴵ f (suc n)) → Ordᴵ
    data _<ᴵ_ where          -- 字面子项序
      zero : a <ᴵ suc a
      suc  : a <ᴵ b → a <ᴵ suc b
      lim  : ∀ n → a <ᴵ f n → a <ᴵ lim f s
    data _≅ᴵ_ where          -- 结构互模拟, 不看步进证据
      z≅ : zero ≅ᴵ zero
      s≅ : a ≅ᴵ b → suc a ≅ᴵ suc b
      l≅ : (∀ n → f n ≅ᴵ g n) → lim f s ≅ᴵ lim g t
    data _⊑ᴵ_ where          -- 前驱包含, 叶子模 ≅ᴵ
      z⊑ : zero ⊑ᴵ b
      s⊑ : a ≅ᴵ a′ → a′ <ᴵ b → suc a ⊑ᴵ b
      l⊑ : (∀ n → f n ⊑ᴵ b) → lim f s ⊑ᴵ b

有界三歧性 (三种情况都只模 $\cong^\mathsf{I}$; 第一种不能是字面的, 否则推出函数外延性的实例, Level §2 `lit→ext`):

    <ᴵ-dec : a <ᴵ c → b <ᴵ c → a ≺ᴵ b ⊎ b ≺ᴵ a ⊎ a ≅ᴵ b      -- a ≺ᴵ b := Σ a′. a ≅ᴵ a′ × a′ <ᴵ b

**2. 树族 (Level §4).** 以 `Ordᴵ` 为层号的归纳-递归族. `limᵢ` 是以较低层 $i$ 的树为参数的极限 (共尾度 $\Omega_i$), `up` 把直接结构前驱层的树定义性地嵌入. `U` 对 $\triangleleft$ 的证明递归, `into`/`out` 每步恒等.

    data Ord₊ (ℓ) (U) where
      zero : Ord₊
      suc  : Ord₊ → Ord₊
      lim  : (ℕ → Ord₊) → Ord₊
      limᵢ : (p : i <ᴵ ℓ) → (U i (<→◃ p) → Ord₊) → Ord₊
      up   : (r : k ◃₁ ℓ) → U k (◃₁→◃ r) → Ord₊
    U i zero = Ord₊ i U ;  U i (suc r) = U i r ;  U _ (self {f} n) = Ord₊ (f n) U ;  U i (lim n r) = U i r
    Ordᶜ ℓ = Ord₊ ℓ U

**3. 层间搬运 (Level §4).** 三歧性的第一种情况只给出代表元 $j\cong^\mathsf{I}j'<^\mathsf{I}i$, 所以穿透要把第 $j'$ 层的输入搬回第 $j$ 层. 结构搬运, 对 $\cong^\mathsf{I}$ 的证明与树同时递归, 在 $\cong$ 下不可见 (`tr-≅`, `tr⁻-≅`).

    tr  : a ≅ᴵ b → Ordᶜ a → Ordᶜ b
    tr⁻ : a ≅ᴵ b → Ordᶜ b → Ordᶜ a

**4. $\Omega$, 加法, 折叠 (Level §4).** $\Omega_0=1$ (EBO 的约定), 后继层 $\Omega_{c+1}=\lim_c\mathtt{up}$, 极限层是对角 $\mathbb{N}$-极限.

    Ω zero      = suc zero
    Ω (suc ℓ)   = limᵢ zero (up zero)
    Ω (lim f s) = lim (λ n → up (self n) (Ω (f n)))

    add a σ zero = a ;  add a σ (suc b) = suc (add a σ b) ;  add a σ (lim f) = lim (λ n → add a σ (f n))
    add a σ (limᵢ q f) = limᵢ (σ q) (λ y → add a σ (f (coe _ _ y)))
    add a σ (up zero x) = add a (σ ∘ suc) x ;  add a σ (up (self n) x) = add a (σ ∘ lim n) x

忠实折叠 $\psi_i$ (`p : i <ᴵ ℓ`, `σ : Simᴵ k ℓ` 把输入层的字面子项送到 $\ell$ 的字面子项): 规则 4 (后继: $\psi(a)\cdot n$), 5ω (`lim` 逐项), 5Ω (穿透, 唯一用搬运处), 6 (折叠: 节点自己的 $\gamma$-链, 起点 $\Omega_j$).

    ψ p σ zero    = Ω _
    ψ p σ (suc a) = lim (iter (ψ p σ a +_) zero)
    ψ p σ (lim f) = lim (λ n → ψ p σ (f n))
    ψ p σ (limᵢ {i = j} q f) with <ᴵ-dec (σ q) p
    ... | injᵃ (via e r) = limᵢ r (λ y → ψ p σ (f (into _ (tr⁻ e (out _ y)))))
    ... | injᵇ _ = lim (λ n → ψ p σ (f (into _ (iter (λ x → ψ q id (f (into _ x))) (Ω j) n))))
    ... | injᶜ _ = (同上)
    ψ p σ (up zero x)     = ψ p (σ ∘ suc) x
    ψ p σ (up (self n) x) = ψ p (σ ∘ lim n) x

目标层 0 的无证明折叠 (没有穿透, 永远走规则 6) 与 FGH:

    ψ⁰ zero    = suc zero
    ψ⁰ (suc a) = lim (iter (ψ⁰ a +_) zero)
    ψ⁰ (lim f) = lim (ψ⁰ ∘ f)
    ψ⁰ (limᵢ {i = j} q f) = lim (λ n → ψ⁰ (f (into _ (iter (λ x → ψ q id (f (into _ x))) (Ω j) n))))
    ψ⁰ (up _ x) = ψ⁰ x

    FGH zero n = suc n ;  FGH (suc a) n = iter (FGH a) n n ;  FGH (lim f) n = FGH (f n) n

**5. 比较关系 (Level §5, §7).** 跨层结构互模拟 $\cong$ (PER; `limᵢ` 节点可在 $\cong^\mathsf{I}$-相关的层; 透视 `up`), 叶子为 $\cong$ 的结构序 $\prec$, 前驱包含 $a\sqsubseteq b:=\forall c.\,c\prec a\to c\prec b$. 只用于证书, 不参与上面任何定义.

**6. 证书与层号 (Level §9).** 第 0 层的遗传步进; 层号由树直接构造 (对树递归, 证书只提供 `lim` 的步进证据), 无填充.

    data HS : Ordᶜ zero → Set where
      hz : HS zero
      hs : HS a → HS (suc a)
      hl : (∀ n → HS (f n)) → (∀ n → f n ⊑ f (suc n)) → HS (lim f)

    toLevel : (x : Ordᶜ zero) → HS x → Ordᴵ
    toLevel zero    h = zero
    toLevel (suc a) h = suc (toLevel a (hs⁻ h))
    toLevel (lim f) h = lim (λ n → toLevel (f n) (hl₁ h n)) (λ n → toLevel-⊑ (hl₁ h n) (hl₁ h (suc n)) (hl₂ h n))

**7. 一致引理 (Uniform §9).** 定理, 无前提:

    Uniform : ∀ (a : Ordᴵ) → HS (ψ⁰ (Ω a))
    Uniform a = Good→HS (Good-ψ⁰ (Good-Ω a) (Ω-refl a))

证明: 观测前序 $\sqsubseteq^\mathsf{o}$ (观测 = 作用到第 0 层的运算栈: $\psi_p\sigma$, $\psi^0$, $a+\_$, 两种搬运; Uniform §1), 遗传好树 `Good` (`lim` 相邻项 $\sqsubseteq^\mathsf{o}$-步进, `limᵢ` 分支函数 $\sqsubseteq^\mathsf{o}$-单调; Uniform §6), `Good` 对 $\Omega$/加法/$\psi$/`ψ⁰`/搬运封闭 (Uniform §6–§7), 第 0 层好树遗传步进 (Uniform §8). 数学核心是 `limᵢ-r` (节点在它的起点分支之上) 与 `B1` (链起点 $\Omega_j\sqsubseteq^\mathsf{o}\psi_q z$), 来自 SafePath.

**8. 对角线 (Diagonal §1–§2, 本文 §1).**

    next (x , h) = ψ⁰ (Ω (toLevel x h)) , Uniform (toLevel x h)
    Γ = iter next (Ω zero , hs hz)                     -- γ₀ = Ω₀ = 1
    γ n = proj₁ (Γ n) ;  cert n = proj₂ (Γ n) ;  L n = toLevel (γ n) (cert n)
    BTBOᴵ = lim (λ n → ψ⁰ (Ω (L n)))                   -- = lim (γ ∘ suc)
    BTBO-HS = hl (cert ∘ suc) (diag-step ∘ suc)        -- diag-step 由 Ψ⁰-mono 与 toLevel-⊑ 归纳
    BTBOᴸ = toLevel BTBOᴵ BTBO-HS                      -- 对角对象回灌下标层

**依赖.** 定义 `BTBOᴵ` 需要 1–4、6、7、8: 证书出现在定义里 (`next` 要 `Uniform` 给出下一层号的步进证据), 所以 5 与 Uniform 的整个证明都是定义的一部分, 不只是元定理. 这是 "带证书" 的代价. 值只模 $\cong$ 依赖这个证明 (§1 `γ-indep`).

## §4 结论与边界

**已形式化** (`--safe --without-K`, 无公设、无洞、无编译指示):

1. 闭项 `BTBOᴵ`, `BTBO-HS`, `BTBOᴸ`, `big`; 无 `cumsum`/`ordᴰ`, 层号全部由 `toLevel` 逐项构造.
2. Diagonal §1–§2 的规则 6 形状事实在具体 `Uniform` 下全部 `refl`, 外加 `cert 1 ≡ Uniform 1`, `L 1 ≡ ε₀ᴵ`, `cert (n+1) ≡ Uniform (L n)`.
3. 证明无关性 (模 $\cong$): `γ-indep`, `BTBO-indep`, `FGH-indep`, `BTBOᴸ-indep`, 对 `Uniform` 的任意证明.
4. FGH: 参数 1 到 $\gamma_4$、`BTBOᴵ` 与下一阶段第一项; 参数 2 到 $\gamma_0$ 与 $\omega$; 与 src 的对应项一致 (§2).

**什么是字面的, 什么是模 $\cong$ 的.**

- 字面 (`≡`/`refl`): 对角线的外层规则 6 形状; 层号逐项是树的逐项 (`toLevel-lim`); $\Omega$ 在层号上的基本列 (`Ω-exact`); FGH 测试值.
- 模 $\cong$: 证书里的步进 (`HS` 的 $\sqsubseteq$ 叶子是 $\cong$); 层号 `lim` 的证据 (模 $\cong^\mathsf{I}$); 三歧性的三种情况; 树对 `Uniform` 证明项的依赖; `forget ∘ toLevel` (Level §9). 字面版本要函数外延性 (Level §2) 或会被内涵性挡住 (SafePath §12), 不是数学缺口.

**什么是估计.**

- 标签 $\psi_0(\Omega_\Omega)$: 外层是定理 (每项 $\gamma_{n+1}=\psi_0(\Omega_{\gamma_n})$, 起点 $\Omega_0=1$, 与 EBO `fsn (EBOψ 2)` 前三项同形, Diagonal §1). 内层没有证: 每个 $\gamma_k$ (作为树) 的基本列是否与 EBO 的 $\gamma_k$ (作为记号) 的基本列处处一致. 对第 0 层的 $\psi_0$-片段 ($\gamma_1=\varepsilon_0$) 这是 [FiniteAll](FiniteAll.lagda.md)/[Translate](Translate.lagda.md) 一类定理在下标为树时的推广, 本文与前几篇都没有做. 所以按 probes/README 的认证规则, "BTBOᴵ $=\psi_0(\Omega_\Omega)$" 仍是估计.
- 两条对角线的值交错 (Diagonal §3), 纸面论证.

**下一阶段 (EBO 的下一个规则 6 链, Diagonal §5) 需要的.**

1. 种子一步 $x\sqsubseteq^0\psi^0(\Omega_{\mathtt{toLevel}\,x})$ 对一般的 $x$ (对角线若从 `BTBOᴵ` 再起, $x=$ `BTBOᴵ`); `diag-step zero` 只对 $x=1$ 证了. `next` 与 `Uniform` 可原样使用, `FGH (ψ⁰ (Ω BTBOᴸ)) 1` 已算通.
2. 对新的运算 (例如 $a\mapsto\psi^0(\Omega_{\Omega_a})$ 的对角对象代表) 的一致引理: `Good` 的封闭性对 $\Omega$/加法/$\psi$/`ψ⁰`/搬运已有, 新运算若由这些复合而成, 证书可由同样的 `Good→HS` 得到; 选哪个对角对象代表不可数下标是缺的设计.
3. 内层对应定理 (上面 "估计" 一条), 把标签从估计升为定理.
4. `Ordᴵ`/`Ordᶜ`/`ψ`/`Uniform` 本身不需要改.

**是否进入 src.** 本文只把定义集中在 §3 供作者判断. 若进入, 需要搬的是 Level (除 §2、§3 的否定实验与 §9 的对照测试)、Uniform (除 §10 的检验)、Diagonal §1–§2 与本文 §1. 本文不改 `src/`、`archive/` 与已有的 Align 文件.
