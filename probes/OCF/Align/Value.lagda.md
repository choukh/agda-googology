# 值相等作为认证: 树侧的外延值前序与它的代价

> 侦察稿. 现行认证准则 (README, 形式化为 [Correspond](Correspond.lagda.md) 的 `Lab`) 要求树的基本列与 EBO 记号的基本列**逐项**一致, 由此 FGH 满足记号的递归方程. 这部分 (README 行数表第 4 层) 已花去定义本体的 3–5 倍. 作者问: 能否让树侧换一个更简单、基本列**不**逐项一致的定义, 只证明**序数值**相等? 本文回答三件事: (1) 在 `--safe --without-K`、无商、无函数外延的约束下, "值" 能否成为一个可用的关系; (2) 在 [Stage2](Stage2.lagda.md) 的现成样例上试一次; (3) 以值相等作认证会省掉什么、新增什么.
>
> 结论先说:
>
> 1. **载体存在, 是 KNFX 式的归纳值前序 `_≼_` (§1).** 构造子 `z≼`/`s≼s`/`≼l`/`l≼` 与 `src/WellFormed/CrossTree` 的 $\preccurlyeq$ 相同, 另加 `limᵢ` 两条 (分支只在 PER 定义域 $x\cong x$ 上取上确界, 与 Level §7 的 `≺i` 一致) 与 `up` 两条 (提升透明). 跨层号, 对**一切**树自反 (`≼-refl`), 传递 (`≼-trans`), 故 $\approx^\mathsf v$ 是等价关系 (而 $\cong$ 在高层只是 PER). 包含结构关系: `≅→≼` (跨层), `⊑→≼` (第 0 层), 于是 $\cong\subseteq\approx^\mathsf v$, 互为 $\sqsubseteq$ $\subseteq\approx^\mathsf v$. 两个包含都严格: $\omega$ 与 $\omega^+=\lim(n+1)$ 互为 $\sqsubseteq$ 且 $\approx^\mathsf v$, 但 `¬ ωᶜ ≅ ω⁺`, 而且**互为 $\sqsubseteq$ 不是后继同余** (`⊑-not-suc`: $\mathrm{suc}\,\omega\not\sqsubseteq\mathrm{suc}\,\omega^+$), $\approx^\mathsf v$ 是 (§2).
> 2. **同余范围 (§3).** 第 0 层上 `suc`/`lim`/`+` (两个参数)/`iter` 与 $\psi^0$ 都尊重 $\preccurlyeq$ (`+-mono`, `ψ⁰-mono⁰`); 对任意层的 $a,b$, $\psi^0(\mathrm{suc}\,a)$ 只依赖 $\psi^0 a$ 的值 (`ψ⁰-suc-≼`). **对第 $\ge1$ 层的参数 $\psi^0$ 不是 $\approx^\mathsf v$-同余** (`ψ⁰-not-cong`, 已编译): $\Omega_1$ 与把分支在 $1$ 处改成 $0$ 的 $\Omega_1'$ 值相等, 而 $\psi^0(\Omega_1)\ge 2$, $\psi^0(\Omega_1')\preccurlyeq1$ (链在 $1$ 处停滞). 折叠只看分支在链点上的取值, 值只看上确界; 要同余必须限制到"分支对值单调"的正规片段, 那是一套新的、Uniform 量级的理论.
> 3. **不恢复三歧性 (§4).** `dec≈→LPO : (∀ a b → Dec (a ≈ᵛ b)) → LPO` 已编译 (第 0 层就够). 这与壁垒定理不冲突: 壁垒约束的是下标类型 `<ᴵ-dec` 的派发; $\approx^\mathsf v$ 只出现在定理的陈述里, 从不被派发读取. 反过来, $\approx^\mathsf v$ **不能**下放到下标层 (把 `Ordᴵ` 的步进证据或 `<ᴵ-dec` 改成模值), 那正是 de Jong 等人的 Brw 三歧 $\Leftrightarrow$ LPO.
> 4. **样例通过, 很便宜 (§5).** `shift≈ : ψ⁰ (Ω BTBOᴸ) ≈ᵛ BTBOᴵ` (平移的对角线与对角线), **`ts≈tbs : ψ⁰ (suc (Ω BTBOᴸ)) ≈ᵛ ψ⁰ (suc (Ω ℓ₀))`**; 两棵树的标签分别是 $\psi_0(\Omega_{\psi_0(\Omega_\Omega)}+1)$ 与 $\psi_0(\Omega_\Omega+1)$, 前者不带后者的标签 (`shift-unlabel`), 记号的句法比较给 `lt` (`cmp-tbs-ts`, `refl`), 两树也不 $\cong$ (`ts≇tbs`). 证明 8 行, 因为 Stage2 已有 `seed`/`seed⁻` (互为 $\sqsubseteq$) 而外层只有 `lim`. 值标签 `VLab X t = Σ Y. Lab Y t × X ≈ᵛ Y` 给出 `ts-vlab : VLab (ψ⁰ (suc (Ω BTBOᴸ))) ts`. 代价: FGH 不随值走 (`FGH ωᶜ 2 ≡ 8`, `FGH ω⁺ 2 ≡ 2048`).
> 5. **作为认证准则不省钱 (§7).** 值标签在已有带标签的树旁边证一个变体, 便宜; 但要用它**取代** `Lab`, 必须有一个与记号值相等的参照物: 要么仍是带 `Lab` 的树 (逐项一致的成本一分不少), 要么是记号自身的值语义 (记号侧第 3 层的良基性未做, 外加"标准形项的基本列极限等于其值", 也未做), 再加上折叠在正规片段上的值同余 (§3 的反例说明它不免费). EBO 阶段还有一层: `Goodᴸ` 证书 (第 3 层) 的单调性与支配**来自标签** (`mono-lab`, `Lab-oc`), 去掉标签就要另造证书理论. 估计第 4 层树侧 (BTBO ≈1850, EBO 阶段 ≈2250) 不会降; 新增载体理论 ≈150 行 (本文 §1–§3) 加正规片段的折叠同余 (估计 Uniform 量级, ≈700) 加记号值语义.
> 6. **优雅性检验: 符号替身机器是定义所需, 不是匹配所需 (§8).** 因放弃逐项一致而能删的只有表面选择 ($\Omega_0=1$、链起点 $\Omega_j$、`ℓ₀` 对 `BTBOᴸ`); 上下文计值的闭包、栈与帧、非紧界都在为**值**或为**类型**服务: EBO 的 $\psi_\delta(\Omega_\Omega+\cdots)$ ($\delta\ge1$) 是 $\Omega_1$-共尾的, 以固定可数层号作前缀的树在那里是 $\omega$-共尾的 $\mathbb N$-极限, 各项都更小, 值严格更小 (纸面, 依据: 共尾度是值不变量). 接口草图 `ValueRoute` 与开放命题 `D3-question` (Stage2 的 D3 树与 GoodL 的带标签树是否值相等) 只给类型; 已证的部分: 第 0 项 $\cong$ (`D3-first`), 第 1 项不 $\cong$ (`D3-second`), 值未定.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Value where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
open import Data.Sum using (inj₁; inj₂)

open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Barrier using (LPO; any; any-witness; true→any)
open import OCF.Align.Level
import OCF.Align.NoCumsum as N
import OCF.Align.EBO as E
open import OCF.Align.Correspond using (Lab; Lab-≅)
open import OCF.Align.Stage2
  using (ℓ₀; seed; seed⁻; ts; tbs; ts-label; shift-unlabel; Lab-uniq; T₂; T₂-0; sq; sqLab; diag2-fs; χ2-unlabel)
open import OCF.Align.GoodL using (T2ᴸ; T2-label)
```

## §1 载体: 外延值前序 $\preccurlyeq$

候选 (a). `src/WellFormed/CrossTree` 定义 2-3-0 的 $\preccurlyeq$ 有四个构造子: $0\preccurlyeq a$; 后继保持; 极限是各项的上界 (`≼l`); 极限是各项的上确界 (`l≼`). 那里是 cubical 的单层树; 这里推广到 Level 的跨层族 `Ordᶜ`:

- `limᵢ p f` 的值是分支 $f(x)$ 的上确界, $x$ 只取 PER 定义域 ($x\cong x$) 里的树. 这与 Level §7 结构序 `≺i` 的约定相同; 定义域外的树在 $\cong$ 下本来就不算合法输入. 不加这一限制, `≅→≼` 在 `lᵢ≅` 处证不出 (那里两边的分支只在 $\cong$-相关的输入上相关).
- `up r y` 的值就是 $y$ 的值 (提升透明).

$\preccurlyeq$ 是普通的归纳族, 严格正 (`i≼` 的前提 `∀ x → x ≅ x → …` 里 $\preccurlyeq$ 只在箭头右边), 不需要商, 也不需要函数外延.

```agda
infix 4 _≼_ _≈ᵛ_

data _≼_ : ∀ {ℓ₁ ℓ₂} → Ordᶜ ℓ₁ → Ordᶜ ℓ₂ → Set where
  z≼  : ∀ {ℓ₁ ℓ₂} {b : Ordᶜ ℓ₂} → 𝟎 {ℓ₁} ≼ b
  s≼s : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≼ b → suc a ≼ suc b
  ≼l  : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {f : ℕ → Ordᶜ ℓ₂} n → a ≼ f n → a ≼ lim f
  l≼  : ∀ {ℓ₁ ℓ₂} {f : ℕ → Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → (∀ n → f n ≼ b) → lim f ≼ b
  ≼i  : ∀ {ℓ₁ ℓ₂ j} {a : Ordᶜ ℓ₁} {p : j <ᴵ ℓ₂} {f : U j (<→◃ p) → Ordᶜ ℓ₂}
        (x : Ordᶜ j) → x ≅ x → a ≼ f (into (<→◃ p) x) → a ≼ limᵢ p f
  i≼  : ∀ {ℓ₁ ℓ₂ j} {p : j <ᴵ ℓ₁} {f : U j (<→◃ p) → Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} →
        (∀ (x : Ordᶜ j) → x ≅ x → f (into (<→◃ p) x) ≼ b) → limᵢ p f ≼ b
  ≼u  : ∀ {ℓ₁ ℓ₂ k} {a : Ordᶜ ℓ₁} {r : k ◃₁ ℓ₂} {y : U k (◃₁→◃ r)} → a ≼ out (◃₁→◃ r) y → a ≼ up r y
  u≼  : ∀ {ℓ₁ ℓ₂ k} {r : k ◃₁ ℓ₁} {y : U k (◃₁→◃ r)} {b : Ordᶜ ℓ₂} → out (◃₁→◃ r) y ≼ b → up r y ≼ b
```

**自反与传递.** 自反对树递归, 对**一切**树成立 (不需要 $x\cong x$): `limᵢ` 情况在每个输入处用同一个 $x$. 传递与 CrossTree 定理 2-3-6 同形, 多出 `limᵢ`/`up` 的两对 (`≼i` 接 `i≼`, `≼u` 接 `u≼`); 每次递归至少一个推导结构下降, 停机检查直接通过.

```agda
≼-refl : ∀ {ℓ} (a : Ordᶜ ℓ) → a ≼ a
≼-refl zero            = z≼
≼-refl (suc a)         = s≼s (≼-refl a)
≼-refl (lim f)         = l≼ (λ n → ≼l n (≼-refl (f n)))
≼-refl (limᵢ p f)      = i≼ (λ x ex → ≼i x ex (≼-refl (f (into (<→◃ p) x))))
≼-refl (up zero y)     = u≼ (≼u (≼-refl y))
≼-refl (up (self n) y) = u≼ (≼u (≼-refl y))

≼-trans : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} {c : Ordᶜ ℓ₃} → a ≼ b → b ≼ c → a ≼ c
≼-trans z≼          q           = z≼
≼-trans p           (≼l n q)    = ≼l n (≼-trans p q)
≼-trans p           (≼i x ex q) = ≼i x ex (≼-trans p q)
≼-trans p           (≼u q)      = ≼u (≼-trans p q)
≼-trans (l≼ p)      q           = l≼ (λ n → ≼-trans (p n) q)
≼-trans (i≼ p)      q           = i≼ (λ x ex → ≼-trans (p x ex) q)
≼-trans (u≼ p)      q           = u≼ (≼-trans p q)
≼-trans (s≼s p)     (s≼s q)     = s≼s (≼-trans p q)
≼-trans (≼l n p)    (l≼ q)      = ≼-trans p (q n)
≼-trans (≼i x ex p) (i≼ q)      = ≼-trans p (q x ex)
≼-trans (≼u p)      (u≼ q)      = ≼-trans p q

_≈ᵛ_ : ∀ {ℓ₁ ℓ₂} → Ordᶜ ℓ₁ → Ordᶜ ℓ₂ → Set
a ≈ᵛ b = a ≼ b × b ≼ a

≈ᵛ-refl : ∀ {ℓ} (a : Ordᶜ ℓ) → a ≈ᵛ a
≈ᵛ-refl a = ≼-refl a , ≼-refl a

≈ᵛ-sym : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≈ᵛ b → b ≈ᵛ a
≈ᵛ-sym (p , q) = q , p

≈ᵛ-trans : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} {c : Ordᶜ ℓ₃} → a ≈ᵛ b → b ≈ᵛ c → a ≈ᵛ c
≈ᵛ-trans (p , q) (p′ , q′) = ≼-trans p p′ , ≼-trans q′ q
```

**后继单调与反演.** `≼-suc` 即 CrossTree 引理 2-3-8. 反演只用三条: 后继对后继只能来自 `s≼s`; 后继不 $\preccurlyeq 0$; 后继 $\preccurlyeq$ 极限只能经某一项.

```agda
≼-suc : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≼ b → a ≼ suc b
≼-suc z≼                          = z≼
≼-suc (s≼s p)                     = s≼s (≼-suc p)
≼-suc (≼l {f = f} n p)            = ≼-trans (≼-suc p) (s≼s (≼l n (≼-refl (f n))))
≼-suc (l≼ p)                      = l≼ (λ n → ≼-suc (p n))
≼-suc (≼i {p = q} {f = f} x ex p) = ≼-trans (≼-suc p) (s≼s (≼i x ex (≼-refl (f (into (<→◃ q) x)))))
≼-suc (i≼ p)                      = i≼ (λ x ex → ≼-suc (p x ex))
≼-suc (≼u {r = r} {y = y} p)      = ≼-trans (≼-suc p) (s≼s (≼u (≼-refl (out (◃₁→◃ r) y))))
≼-suc (u≼ p)                      = u≼ (≼-suc p)

s≼s⁻ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → suc a ≼ suc b → a ≼ b
s≼s⁻ (s≼s p) = p

s≼0 : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} → ¬ (suc a ≼ 𝟎 {ℓ₂})
s≼0 ()

≼lim⁻ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {f : ℕ → Ordᶜ ℓ₂} → suc a ≼ lim f → Σ ℕ (λ n → suc a ≼ f n)
≼lim⁻ (≼l n p) = n , p
```

## §2 与结构关系的比较

**$\cong\subseteq\approx^\mathsf v$, 跨层.** 对 $\cong$ 的推导递归. `lᵢ≅` 情况: 对左边定义域里的 $x$ ($x\cong x$), 右边取 `tr e x` (Level §7 `≺-respʳ` 的同一手法), 它也在定义域里, 两分支 $\cong$, 递归.

```agda
≅→≼ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≅ b → a ≼ b
≅→≼ z≅      = z≼
≅→≼ (s≅ e)  = s≼s (≅→≼ e)
≅→≼ (l≅ h)  = l≼ (λ n → ≼l n (≅→≼ (h n)))
≅→≼ (lᵢ≅ {p = p} e h) =
  i≼ (λ x ex → ≼i (tr e x) (tr-≅ e (≅-tr e ex)) (≅→≼ (h x (tr e x) (≅→R (<→◃ p) (≅-tr e ex)))))
≅→≼ (upˡ {r = zero} e)   = u≼ (≅→≼ e)
≅→≼ (upˡ {r = self n} e) = u≼ (≅→≼ e)
≅→≼ (upʳ {r = zero} e)   = ≼u (≅→≼ e)
≅→≼ (upʳ {r = self n} e) = ≼u (≅→≼ e)

≅→≈ᵛ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≅ b → a ≈ᵛ b
≅→≈ᵛ e = ≅→≼ e , ≅→≼ (≅-sym e)
```

**$\sqsubseteq\subseteq\preccurlyeq$ (第 0 层).** 结构序的一步 $c\prec b$ 给出 $c+1\preccurlyeq b$ (`≺→s≼`, 跨层); 于是前驱包含 $a\sqsubseteq b$ 对 $a$ 递归给出 $a\preccurlyeq b$. 后继情况要把 $a_0\prec\mathrm{suc}\,a_0$ 喂进去, 需要 $a_0\cong a_0$: 第 0 层自动成立 (`≅-refl⁰`), 高层要另带 PER 前提, 本文用不到.

```agda
≺→s≼ : ∀ {ℓ₁ ℓ₂} {c : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → c ≺ b → suc c ≼ b
≺→s≼ (≺z e)      = s≼s (≅→≼ e)
≺→s≼ (≺s h)      = ≼-suc (≺→s≼ h)
≺→s≼ (≺l n h)    = ≼l n (≺→s≼ h)
≺→s≼ (≺i x ex h) = ≼i x ex (≺→s≼ h)
≺→s≼ (≺u h)      = ≼u (≺→s≼ h)

⊑→≼ : ∀ {ℓ₂} (a : Ordᶜ zero) {b : Ordᶜ ℓ₂} → a ⊑ b → a ≼ b
⊑→≼ zero        k = z≼
⊑→≼ (suc a)     k = ≺→s≼ (k (≺z (≅-refl⁰ a)))
⊑→≼ (lim f)     k = l≼ (λ n → ⊑→≼ (f n) (λ h → k (≺l n h)))
⊑→≼ (limᵢ () f) k
⊑→≼ (up () x)   k

⊑⊒→≈ᵛ : ∀ {a b : Ordᶜ zero} → a ⊑ b → b ⊑ a → a ≈ᵛ b
⊑⊒→≈ᵛ {a} {b} p q = ⊑→≼ a p , ⊑→≼ b q
```

**两个包含都严格, 且互为 $\sqsubseteq$ 不是同余.** 取 $\omega^+=\lim_n(n+1)$. 它与 $\omega$ 互为 $\sqsubseteq$ (于是值相等), 但不 $\cong$ (第 0 项 $0$ 对 $1$). 后继之后 $\sqsubseteq$ 断了: $\omega\prec\mathrm{suc}\,\omega$, 而 $\omega\not\prec\mathrm{suc}\,\omega^+$, 因为 $\prec$ 的叶子要求 $\cong$. 这是 Prefix §8 所记 "Level 的 $\sqsubseteq$ 对 suc 不单调" 的最小实例. 所以 Stage2 的 `seed`/`seed⁻` (互为 $\sqsubseteq$) 本身还不是值相等的载体, 经 `⊑→≼` 才是.

```agda
ω⁺ : Ordᶜ zero
ω⁺ = lim (natᶜ ∘ suc)

ω⊑ω⁺ : ωᶜ ⊑ ω⁺
ω⊑ω⁺ (≺l n h) = ≺l n (≺s h)

ω⁺⊑ω : ω⁺ ⊑ ωᶜ
ω⁺⊑ω (≺l n h) = ≺l (suc n) h

ω≈ω⁺ : ωᶜ ≈ᵛ ω⁺
ω≈ω⁺ = ⊑⊒→≈ᵛ ω⊑ω⁺ ω⁺⊑ω

ω≇ω⁺ : ¬ (ωᶜ ≅ ω⁺)
ω≇ω⁺ (l≅ h) with h 0
... | ()

ω≇nat : ∀ m → ¬ (ωᶜ ≅ natᶜ m)
ω≇nat zero    ()
ω≇nat (suc m) ()

ω⊀nat : ∀ m → ¬ (ωᶜ ≺ natᶜ m)
ω⊀nat zero    ()
ω⊀nat (suc m) (≺z e) = ω≇nat m e
ω⊀nat (suc m) (≺s h) = ω⊀nat m h

⊑-not-suc : ¬ (suc ωᶜ ⊑ suc ω⁺)
⊑-not-suc k with k (≺z (≅-refl⁰ ωᶜ))
... | ≺z e        = ω≇ω⁺ e
... | ≺s (≺l n h) = ω⊀nat (suc n) h

suc-ω≈ : suc ωᶜ ≈ᵛ suc ω⁺
suc-ω≈ = s≼s (proj₁ ω≈ω⁺) , s≼s (proj₂ ω≈ω⁺)
```

## §3 同余: 第 0 层的运算与 $\psi^0$ 的边界

**和与迭代.** 第 0 层的 `_+_` 对右参数按结构递归 (`add a σ (suc b) = suc (add a σ b)`, `lim` 逐项), 所以两个参数上的单调性对右参数的 $\preccurlyeq$ 推导递归即得; `z≼` 情况要 $a'\preccurlyeq a'+b'$ (`≼-+ʳ`). 高层构造子 `≼i`/`i≼`/`≼u`/`u≼` 在第 0 层不可能出现 (没有 $j<^\mathsf I0$, 也没有 $k\triangleleft_1 0$), 以荒谬模式排除.

```agda
≼-+ʳ : ∀ (a b : Ordᶜ zero) → a ≼ a + b
≼-+ʳ a zero        = ≼-refl a
≼-+ʳ a (suc b)     = ≼-suc (≼-+ʳ a b)
≼-+ʳ a (lim f)     = ≼l 0 (≼-+ʳ a (f 0))
≼-+ʳ a (limᵢ () f)
≼-+ʳ a (up () x)

+-mono : ∀ {a a′ b b′ : Ordᶜ zero} → a ≼ a′ → b ≼ b′ → a + b ≼ a′ + b′
+-mono {a′ = a′} {b′ = b′} pa z≼ = ≼-trans pa (≼-+ʳ a′ b′)
+-mono pa (s≼s q)  = s≼s (+-mono pa q)
+-mono pa (≼l n q) = ≼l n (+-mono pa q)
+-mono pa (l≼ h)   = l≼ (λ n → +-mono pa (h n))
+-mono pa (≼i {p = ()} x ex q)
+-mono pa (i≼ {p = ()} h)
+-mono pa (≼u {r = ()} q)
+-mono pa (u≼ {r = ()} q)

iter-≼ : ∀ {A B : Ordᶜ zero} → A ≼ B → ∀ n → iter (A +_) zero n ≼ iter (B +_) zero n
iter-≼ e zero    = z≼
iter-≼ e (suc n) = +-mono e (iter-≼ e n)
```

**$\psi^0$ 的后继情况只依赖 $\psi^0 a$ 的值, 任意层.** $\psi^0(\mathrm{suc}\,a)$ 定义性地是 $\lim_n(\psi^0a)\cdot n$. 由此第 0 层参数的 $\psi^0$ 单调 (`ψ⁰-mono⁰`, 对推导递归; `z≼` 情况用 Level 的 `z≺ψ⁰`: 任何 $\psi^0$ 输出 $\ge 1$).

```agda
ψ⁰-suc-≼ : ∀ {k k′} {a : Ordᶜ k} {b : Ordᶜ k′} → ψ⁰ a ≼ ψ⁰ b → ψ⁰ (suc a) ≼ ψ⁰ (suc b)
ψ⁰-suc-≼ e = l≼ (λ n → ≼l n (iter-≼ e n))

ψ⁰-suc-≈ : ∀ {k k′} {a : Ordᶜ k} {b : Ordᶜ k′} → ψ⁰ a ≈ᵛ ψ⁰ b → ψ⁰ (suc a) ≈ᵛ ψ⁰ (suc b)
ψ⁰-suc-≈ (p , q) = ψ⁰-suc-≼ p , ψ⁰-suc-≼ q

1≼ψ⁰ : ∀ {k} (y : Ordᶜ k) → suc (𝟎 {zero}) ≼ ψ⁰ y
1≼ψ⁰ y = ≺→s≼ (z≺ψ⁰ {ℓ₀ = zero} y)

ψ⁰-mono⁰ : ∀ {a b : Ordᶜ zero} → a ≼ b → ψ⁰ a ≼ ψ⁰ b
ψ⁰-mono⁰ {b = b} z≼ = 1≼ψ⁰ b
ψ⁰-mono⁰ (s≼s e)   = ψ⁰-suc-≼ (ψ⁰-mono⁰ e)
ψ⁰-mono⁰ (≼l n e)  = ≼l n (ψ⁰-mono⁰ e)
ψ⁰-mono⁰ (l≼ h)    = l≼ (λ n → ψ⁰-mono⁰ (h n))
ψ⁰-mono⁰ (≼i {p = ()} x ex e)
ψ⁰-mono⁰ (i≼ {p = ()} h)
ψ⁰-mono⁰ (≼u {r = ()} e)
ψ⁰-mono⁰ (u≼ {r = ()} e)
```

**高层参数: $\psi^0$ 不是同余.** $\Omega_1$ 即 `limᵢ zero (up zero)`. $\Omega_1'$ 的分支先过 $g$: $g(1)=0$, 其余恒等. 两者分支的上确界相同 (对 $x$ 取 $x+2$ 即可越过), 所以 $\Omega_1\approx^\mathsf v\Omega_1'$. 但规则 6 的链从 $\Omega_0=1$ 起: $\Omega_1'$ 的链 $1\mapsto\psi_0(g(1))=\psi_0(0)=1$ 停滞 (`stall`), $\psi^0(\Omega_1')$ 每一项都是 $\psi^0(0)=1$; 而 $\psi^0(\Omega_1)$ 沿路径 $[1][2][1][2]$ 就到 $2$ (`two≼`, 全靠归约).

```agda
𝟏 𝟐 : Ordᶜ zero
𝟏 = suc zero
𝟐 = suc 𝟏

g : Ordᶜ zero → Ordᶜ zero
g (suc zero) = zero
g x          = x

Ω₁ Ω₁′ : Ordᶜ (suc zero)
Ω₁  = Ω (suc zero)
Ω₁′ = limᵢ zero (λ x → up zero (g x))

Ω₁≈Ω₁′ : Ω₁ ≈ᵛ Ω₁′
Ω₁≈Ω₁′ = i≼ (λ x ex → ≼i (suc (suc x)) (≅-refl⁰ _) (u≼ (≼u (≼-suc (≼-suc (≼-refl x))))))
        , i≼ (λ x ex → ≼i (g x) (≅-refl⁰ (g x)) (≼-refl (up zero (g x))))

STEP : Ordᶜ zero → Ordᶜ zero
STEP x = ψ {i = zero} {k = suc zero} {ℓ = suc zero} zero (λ r → r) (up zero (g x))

stall : ∀ n → iter STEP 𝟏 n ≡ 𝟏
stall zero    = refl
stall (suc n) = cong STEP (stall n)

ψΩ₁′≼1 : ψ⁰ Ω₁′ ≼ 𝟏
ψΩ₁′≼1 = l≼ (λ n → subst (λ w → ψ⁰ (g w) ≼ 𝟏) (sym (stall n)) (≼-refl 𝟏))

two≼ : 𝟐 ≼ ψ⁰ Ω₁
two≼ = ≼l 1 (≼l 2 (≼l 1 (≼l 2 (≼-refl 𝟐))))

ψ⁰-not-cong : Ω₁ ≈ᵛ Ω₁′ × ¬ (ψ⁰ Ω₁ ≼ ψ⁰ Ω₁′)
ψ⁰-not-cong = Ω₁≈Ω₁′ , λ e → s≼0 (s≼s⁻ (≼-trans two≼ (≼-trans e ψΩ₁′≼1)))
```

**读法.** 折叠只在规则 6 的链点上读分支, 值只看分支的上确界, 两者之间没有一般的联系. $\Omega_1'$ 不是任何折叠的输出, 但它说明 "$\psi$ 尊重 $\approx^\mathsf v$" 只能在**分支对值单调**的片段上成立 (分支 $f$ 满足 $x\preccurlyeq y\Rightarrow f\,x\preccurlyeq f\,y$, 并且这一性质要对折叠输出封闭). 这是 Uniform 的观测前序 `⊑ᵒ` 的值版本; Certified 的 `ψ-not-⊑mono` 已说明结构版本在一般树上不成立; 值版本在 `Good` 片段上是否成立未查, 估计是 Uniform 量级 (≈700 行) 的新理论.

## §4 不恢复三歧性

二进制序列 $\alpha$ 的树 $t_\alpha=\lim_n[\mathsf{any}_\alpha(n)]$ (每项 $0$ 或 $1$) 的值是 $1$ 当且仅当 $\alpha$ 有真值. 于是 $\approx^\mathsf v$ 的判定 (只在第 0 层、只对 $b=1$) 就给出 LPO: `yes` 给出 $1\preccurlyeq t_\alpha$, 反演出见证; `no` 时若某个 $\alpha(k)$ 为真则 $t_\alpha\approx^\mathsf v1$, 矛盾.

```agda
bit : Bool → Ordᶜ zero
bit true  = 𝟏
bit false = zero

tα : (ℕ → Bool) → Ordᶜ zero
tα α = lim (λ n → bit (any α n))

bit≼1 : ∀ b → bit b ≼ 𝟏
bit≼1 true  = ≼-refl 𝟏
bit≼1 false = z≼

1≼bit : ∀ b → 𝟏 ≼ bit b → b ≡ true
1≼bit true  _ = refl
1≼bit false ()

dec≈→LPO : (∀ (a b : Ordᶜ zero) → Dec (a ≈ᵛ b)) → LPO
dec≈→LPO d α with d (tα α) 𝟏
... | yes (_ , q) with ≼lim⁻ q
...   | n , r = inj₁ (any-witness n (1≼bit (any α n) r))
dec≈→LPO d α | no ¬e = inj₂ ff where
  ff : ∀ k → α k ≡ false
  ff k with α k in eq
  ... | false = refl
  ... | true  = ⊥-elim (¬e (l≼ (λ n → bit≼1 (any α n))
                          , ≼l k (subst (λ b → 𝟏 ≼ bit b) (sym (true→any k eq)) (≼-refl 𝟏))))
```

**与壁垒的关系.** [Barrier](../Barrier.lagda.md) 的定理 1 约束的是**下标类型**: 用来派发 `ψ` 的有界三歧性. $\approx^\mathsf v$ 不进入任何定义, 只出现在定理的陈述里, 所以它不可判定没有坏处 (结构的 $\cong$ 本来也不可判定: 要逐点比较 $\mathbb N\to$ 树). 反方向的限制是实质的: 若把下标层 `lim` 的步进证据或 `<ᴵ-dec` 的第三支改成模 $\approx^\mathsf v$, 派发就要判定值的序, 那是 Brw 的三歧 ($\Leftrightarrow$ LPO, de Jong 等 Thm 53) 或 CuST 的商序数 ($\Leftrightarrow$ LEM). 所以值相等只能是**对象层的认证关系**, 层号证书 `HS` 必须继续是结构的 $\sqsubseteq$ (叶子 $\cong$). 这也说明值认证不会减轻第 3 层 (回灌证书) 的成本.

## §5 样例: 平移的对角线

Stage2 §1 的两个对角层号: `ℓ₀` (含 $\gamma_0$) 与 `BTBOᴸ` (从 $L_1$ 起). $\psi^0(\Omega_{\ell_0})$ 字面上是 `BTBOᴵ`, $\psi^0(\Omega_{\mathtt{BTBO}^\mathsf L})$ 是对角线平移一位, 二者互为 $\sqsubseteq$ (`seed`/`seed⁻`). 经规则 4 得 Stage2 §3 的两棵树: 标签 $\psi_0(\Omega_\Omega+1)$ (`ts-label`) 与 $\psi_0(\Omega_{\psi_0(\Omega_\Omega)}+1)$ (`tbs-label`), 前者**不**带后者的标签 (`shift-unlabel`). 它们值相等:

```agda
γ-mono : ∀ n → N.γ n ≼ N.γ (suc n)
γ-mono n = ⊑→≼ (N.γ n) (N.D.diag-step n)

shift≈ : ψ⁰ (Ω N.BTBOᴸ) ≈ᵛ N.BTBOᴵ
shift≈ = ⊑→≼ _ seed⁻ , ⊑→≼ _ seed

ts≈tbs : ψ⁰ (suc (Ω N.BTBOᴸ)) ≈ᵛ ψ⁰ (suc (Ω ℓ₀))
ts≈tbs = ψ⁰-suc-≈ shift≈

ts≇tbs : ¬ (ψ⁰ (suc (Ω N.BTBOᴸ)) ≅ ψ⁰ (suc (Ω ℓ₀)))
ts≇tbs e = shift-unlabel (Lab-≅ e ts-label)
```

`ts≈tbs` 的右边是 $\psi^0(\mathrm{suc}\,\Omega_{\ell_0})$, 而 `shift≈` 的右边是 `BTBOᴵ`; 二者经 Stage2 的 `ψ⁰ (Ω ℓ₀) ≡ BTBOᴵ` (`refl`) 定义性相等, 合一器自己看出. `ts≇tbs` 说这一对在结构上**不** $\cong$ (否则标签可沿 $\cong$ 搬过去, 与 `shift-unlabel` 矛盾): 它恰是 $\approx^\mathsf v$ 比 $\cong$ 宽的那一类. 样例本身 8 行, 工作量全在已有的 `seed`/`seed⁻` 与 §1–§3 的通用引理.

**记号侧.** 两个标签项按 Buchholz 的值相等, 但 EBO 的 `cmpᵀ` 是句法字典序, 对非标准项 `tbs` 给 `lt`. 所以候选 (c) "经记号 `cmpᵀ` 的值相等" 在这一对上直接失效; 要它工作, 得先有把 `tbs` 化成 `ts` 的保值正规化 (StandardOmega 的 `NF₁` 只刻画标准形, 不提供正规化).

```agda
cmp-tbs-ts : E.cmpᵀ tbs ts ≡ E.lt
cmp-tbs-ts = refl
```

**值标签.** 把认证准则放宽为 "与某棵带标签的树值相等":

```agda
VLab : Ordᶜ zero → E.T → Set
VLab X t = Σ (Ordᶜ zero) (λ Y → Lab Y t × X ≈ᵛ Y)

Lab→VLab : ∀ {X t} → Lab X t → VLab X t
Lab→VLab {X} l = X , l , ≈ᵛ-refl X

VLab-≈ : ∀ {X X′ t} → X′ ≈ᵛ X → VLab X t → VLab X′ t
VLab-≈ e (Y , l , e′) = Y , l , ≈ᵛ-trans e e′

VLab-val : ∀ {X X′ t} → VLab X t → VLab X′ t → X ≈ᵛ X′
VLab-val (Y , l , e) (Y′ , l′ , e′) = ≈ᵛ-trans e (≈ᵛ-trans (≅→≈ᵛ (Lab-uniq l l′)) (≈ᵛ-sym e′))

ts-vlab : VLab (ψ⁰ (suc (Ω N.BTBOᴸ))) ts
ts-vlab = VLab-≈ ts≈tbs (Lab→VLab ts-label)

value-not-label : VLab (ψ⁰ (suc (Ω N.BTBOᴸ))) ts × ¬ Lab (ψ⁰ (suc (Ω N.BTBOᴸ))) ts
value-not-label = ts-vlab , shift-unlabel
```

`VLab-val`: 值标签决定值 (经 `Lab-uniq`, 同标签的树 $\cong$). 它不给 FGH 的递归方程.

## §6 FGH 不随值走

$\omega$ 与 $\omega^+$ 值相等 (`ω≈ω⁺`), FGH 在 2 处分别是 $f_2(2)=8$ 与 $f_3(2)=2048$. 一般地, 基本列可以在任意长的前缀上停在 $0$: 值相等, 而 FGH 在任何可计算的范围内都小得多. 所以值标签只认证 "序数强度", 不认证 "这棵树的 FGH 就是 EBO 的 $f_\alpha$".

```agda
_ : FGH ωᶜ 2 ≡ 8
_ = refl

_ : FGH ω⁺ 2 ≡ 2048
_ = refl
```

## §7 候选载体对比与替代认证准则

| 载体 | 定义方式 | 等价关系? | 含 $\cong$ | 同余 | 可判定 | 本文结果 |
|---|---|---|---|---|---|---|
| $\cong$ (Level §5) | 结构互模拟 | 高层只是 PER | — | suc/lim/+/ψ/ψ⁰ 全部 (`ψ-≅`) | 否 | 太细: `ω≇ω⁺` |
| 互为 $\sqsubseteq$ (Level §7) | 前驱包含, 叶子 $\cong$ | 是 | 是 | **不是 suc 同余** (`⊑-not-suc`) | 否 | 介于两者之间, 不能当值 |
| (a) $\approx^\mathsf v$ (本文 §1) | KNFX 归纳 $\preccurlyeq$, 分支取 PER 定义域 | 是, 一切层 | 是 (`≅→≈ᵛ`) | 第 0 层 suc/lim/+/iter/ψ⁰; ψ⁰∘suc 任意层; **高层 ψ⁰ 否** (`ψ⁰-not-cong`) | 否, 判定即 LPO (`dec≈→LPO`) | **采用** |
| (b) setoid 良序解释 (DecZero `funTreeRepresentative` 式) | 每棵树给一个带序的位置类型, 等价 = 序同构 | 是 | 需证 | 同 (a), 另需显式构造同构 | 否 | 未编译: `lim` 的位置类型 $\Sigma_n\mathrm{Pos}(f\,n)$ 上的序要比较不同项里的位置, 只能借 (a) 的 $\preccurlyeq$; 于是 (b) = (a) + 显式同构见证, 更贵而不更强. DecZero 也只证了单向 (结构序 ⟹ 语义序) |
| (c) 经记号 (`cmpᵀ` 相等) | 两侧各有带标签的树, 标签项比较相等 | 只在标准形上有意义 | 是 | 依赖记号 | 句法上可判定 | 句法 `cmpᵀ` 在非标准项上不是值 (`cmp-tbs-ts`); 在标准形上 `cmpᵀ ≡ eq` 即同一项, 退化为 `Lab-uniq`; 要它比 `Lab` 宽, 需记号的值语义 (未有) |

**替代准则.** 两种表述:

- **V1 (值标签, 本文 `VLab`):** $X$ 与某棵带 `Lab … t` 的树值相等. 保证: $X$ 的序数值就是那棵带标签的树的值 (README 意义下即 $t$ 的强度). 不保证: $X$ 的基本列、$X$ 的 FGH. 成本 = 参照树的 `Lab` (原样) + 一个 $\approx^\mathsf v$ 证明. **它不省钱**, 只是把已有的标签转移给值相等的变体 (如 `ts-vlab`).
- **V2 (直接对记号的值):** $X$ 与标准形项 $t$ 的序数值相等. 要求: (i) 标准形上 `<ᵀ` 的良基性 (行数表第 3 层记号列, 未做); (ii) 标准形项的基本列极限等于其值 (完全的 Bachmann 性质与 `cofin`; Standard/StandardOmega 的约 1900 行是其中的序对应部分); (iii) 树侧折叠在正规片段上的值同余与单调 (§3 说明必须限制片段; 估计 Uniform 量级); (iv) 每个阶段对 $X$ 证上下两个方向的界. 第 (iv) 步对每个 $\psi$-子树都要给上界与下界, 而目前唯一能算这些树的值的办法是沿基本列展开, 即逐项匹配换一种记账方式.

**成本估计 (README 四层口径).**

| | 现行 (逐项一致) | V2 (值相等) |
|---|---|---|
| 载体理论 | 0 (`≅`、`Lab` 已有) | 本文 §1–§3 约 150 行 + 正规片段的折叠值同余 ≈700 (估计) |
| 记号侧 | 第 4 层 ≈2250 (Standard/StandardOmega/SystemOmega/fs-mono₁) | 仍需其中的序对应 (≈1900) + 第 3 层良基性 (未做, Buchholz 良序证明量级) + 值语义 |
| 树侧第 4 层 | BTBO ≈1850, EBO 阶段 ≈2250 | 每阶段的上下界证明; 无理由比逐项匹配短 (上界要穷举一切前驱, 下界要为每个记号前驱找到树前驱, 恰是 `Lab` 的两个方向) |
| 树侧第 3 层 | EBO 阶段的 `Goodᴸ` 用标签 (`mono-lab`, `Lab-oc`) 证单调与支配 | 去掉标签要另造; Omega2 的 `no-Bound` 说明不带标签的全局界不存在 |

结论: 以值相等**取代**逐项一致, 第 4 层不会降, 第 3 层反而失去现成的证明途径; 以值相等**补充** (V1) 很便宜, 适合给变体树转移强度.

## §8 优雅性检验: 哪些机器只为逐项匹配存在

若不要求逐项一致, 树侧定义能简化多少? 逐项核对现有构件 (出处见 README):

| 构件 | 用途 | 放弃逐项一致后 |
|---|---|---|
| $\Omega_0=1$, 链起点 $\Omega_j$, $\psi^0$ 在第 0 层也折叠 (Diagonal §3 表) | 匹配 EBO 的规则 | 可换 (src 的 $\Omega_0=\omega$、起点 0 给同一不动点, 纸面); 每处一两行 |
| `ℓ₀` 对 `BTBOᴸ` (Stage2 §1) | 匹配 $\Omega_\Omega$ 的链 | 可换 (`ts≈tbs`); 零行差别 |
| 无 cumsum 的 `toLevel` (Level, Cumsum) | 值: cumsum 改值 (`overshoot`) | **不可去** |
| `Ordᴵ` 模 $\cong$ 的步进与 `tr⁻` (Level §2) | 派发 (有界三歧) | **不可去**; 值相等不能下放到下标层 (§4) |
| 上下文计值的闭包 `ŝ`/`ĉᴸ`、函数式栈 `Stk` 与帧 (Symbolic … OmegaExp) | $\Omega_\Omega$ 在 $\psi_\delta$ ($\delta\ge1$) 下是 $\Omega_1$-共尾的, 由上下文的链计值 | **值所需**: 静态可数前缀 (D3) 在那里是 $\omega$-共尾的 $\mathbb N$-极限, 各项 $\psi_\delta(\Omega_{L_m}+\cdots)<\psi_\delta(\Omega_\Omega+\cdots)$, 共尾度不同的两序数不相等, 树值严格更小 (纸面) |
| 非紧闭包的界 $\max(i,F)+1$ (NonTight) | 类型: 闭包环境要放得下高层帧 (`noSim21`) | **定义所需**: 不然树造不出来, 与是否匹配无关 |
| `Goodᴸ` 只在带标签点量化, 单调性来自 `mono-lab` | 第 3 层证书 | 依赖标签; 放弃标签要另造 (`no-Bound`) |
| `Lab`/`LabL`/`Pre*`/`WE`/`ZE` | 第 4 层 | 被值的上下界证明替换, 不是删除 |

下面把值路线 V2 需要的接口写成类型 (只有字段), 并把最直接的简化候选写成一个命题: Stage2 的 D3 树 `T₂` (上下文对角线, 静态前缀 $\Omega_{\ell_0}$, 定义约 130 行) 与 GoodL 的带标签树 `T2ᴸ` (符号替身族) 是否值相等. 若成立, src 可以用 D3 代替符号替身族到达 $\psi_0(\Omega_\Omega\cdot2)$; 上表第 5 行的纸面论证预期它**不**成立 (D3 在 `X₂-unlabel` 的暴露点给出 $\omega$-共尾的子树).

```agda
record ValueRoute : Set₁ where
  field
    Norm     : ∀ {ℓ} → Ordᶜ ℓ → Set
    Norm-Ω   : ∀ a → Norm (Ω a)
    Norm-ψ⁰  : ∀ {k} {x : Ordᶜ k} → Norm x → Norm (ψ⁰ x)
    ψ⁰-cong  : ∀ {k k′} {x : Ordᶜ k} {y : Ordᶜ k′} → Norm x → Norm y → x ≈ᵛ y → ψ⁰ x ≈ᵛ ψ⁰ y
    Ω-cong   : ∀ {a b} → forget a ≈ᵛ forget b → Ω a ≈ᵛ Ω b
    Val      : Ordᶜ zero → E.T → Set
    Val-Lab  : ∀ {X t} → Lab X t → Val X t
    Val-≈    : ∀ {X Y t} → X ≈ᵛ Y → Val Y t → Val X t
    Val-uniq : ∀ {X Y t} → Val X t → Val Y t → X ≈ᵛ Y

D3-question : Set
D3-question = T₂ ≈ᵛ T2ᴸ

D3-first : sq T₂ 0 ≈ᵛ sq T2ᴸ 0
D3-first = ≅→≈ᵛ (Lab-uniq T₂-0 (sqLab T2-label refl 0))

D3-second : ¬ (sq T₂ 1 ≅ sq T2ᴸ 1)
D3-second e = χ2-unlabel (Lab-≅ e (subst (Lab _) (diag2-fs 1) (sqLab T2-label refl 1)))
```

`D3-question` 的现状: 第 0 项两棵树带同一标签 $\psi_0(\Omega_\Omega+\Omega)$, 由 `Lab-uniq` 甚至 $\cong$ (`D3-first`); 第 1 项 D3 的 $\chi_2$ 无标签而 `T2ᴸ` 的第 1 项有, 故二者不 $\cong$ (`D3-second`). 它们的**值**是否相等, 本文无法判定: 证"是"要 $\chi_2$ 的值的上界, 证"否"要高层值的共尾度理论, 两者都要求 V2 的 `ψ⁰-cong` 一类工具.

`Val` 只能以谓词出现: 值的载体是树, 记号没有到树的典范映射 (那正是标签要造的东西). `Val-Lab` 把现行准则嵌进来, `Val-≈`/`Val-uniq` 是 V1 的公理化; V2 的全部新数学在 `Norm`/`ψ⁰-cong`/`Ω-cong` 三个字段与 `Val` 的独立定义里.

## §9 结论与边界

**已形式化:**

1. 外延值前序 `_≼_` (跨层, 分支取 PER 定义域, `up` 透明); `≼-refl` (一切树)、`≼-trans`, `≈ᵛ` 是等价关系; `≼-suc` 与三条反演.
2. 结构到值: `≅→≼`/`≅→≈ᵛ` (跨层), `≺→s≼`, `⊑→≼` 与 `⊑⊒→≈ᵛ` (第 0 层). 严格性: `ω≈ω⁺`, `ω≇ω⁺`, `⊑-not-suc`, `suc-ω≈`.
3. 同余: `+-mono`, `iter-≼`, `ψ⁰-suc-≼`/`ψ⁰-suc-≈` (任意层), `ψ⁰-mono⁰` (第 0 层); 反例 `ψ⁰-not-cong` (第 1 层).
4. `dec≈→LPO`.
5. 样例: `γ-mono`, `shift≈`, **`ts≈tbs`**, `cmp-tbs-ts`, `VLab`/`Lab→VLab`/`VLab-≈`/`VLab-val`, `ts-vlab`, `value-not-label`; FGH 对照 8 与 2048.
6. 类型草图 `ValueRoute` 与命题 `D3-question` (未证); 其部分事实 `D3-first` (第 0 项 $\cong$) 与 `D3-second` (第 1 项不 $\cong$); 样例对不 $\cong$ (`ts≇tbs`).

**边界与开放:**

- 高层的 `⊑→≼` 要 PER 前提, 未写. 正规片段上 $\psi$ 的值同余未尝试; 它是 V2 路线的第一块砖, 也决定 `D3-question` 能否形式化地否定.
- `D3-question` 的否定只有纸面论证 (共尾度); 形式化需要高层树的值的共尾度不变量.
- 值标签 `VLab` 不给 FGH 方程. 若采用, README 的认证准则要分成 "FGH 标签" (现行 `Lab`) 与 "值标签" (`VLab`) 两种, 后者只认证序数强度. 本文不改 README.
- 不改 `src/`、`archive/` 与任何已有文件; 未触及 TopDown/Uniform2 的主题.
