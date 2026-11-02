# 不可达层 I 的可行性侦察: 层号宇宙、以层号为输出的折叠、Λ 的位置与序对应的代价

> 侦察稿, 不建理论. 五个问题各以编译过的探针 (正面构造或否定) 作答, 结论先说:
>
> 1. **"I 层 = 对层号类型取极限" 有两种读法, 只有一种有内容 (§1–§2).** 读法 A (第二梯级 `Lv₂ = Ordᴵ ⊎ {I+n}`, 树在 I 层对整个 `Ordᴵ` 分支) 编译无碍: 严格正、全在 `Set`、`--without-K` 下无事, 壁垒定理不咬它 (`Ω_I` 是对已定义类型 `Ordᴵ` 的 W-型分支, 不是可数层的 Ω̂). 但它是空心的: `Lv₂` 在 `Ordᴵ` 与 I 之间没有任何层号 (`no-middle`), 所以 ψ_I 的输出 (Ω-不动点 Λ 等, 不可数而 < I) 无处安放; 而且它以 I 为界的"有界三歧"就是 `Ordᴵ` 上的无界三歧, 推出 WLPO (`Trich₂→WLPO`, 壁垒在此处的形态). 读法 B 才是 Setzer 的 I: **层号类型本身是归纳-递归的宇宙** `Lv`, 多一个构造子 `limᴼ : (k : Lv) → (Ordᴸ k → Lv) → Lv` (对第 k 层的树取上确界), 树族 `Ordᴸ : Lv → Set` 与 `Lv` 同时定义. 这在 `--safe --without-K` 下编译通过 (§2): 正性无碍 (`Lv` 不以类型身份出现在 `Ordᴸ` 的展开里), 宇宙层级仍是 `Set`; 停机检查要把 "路径处的树类型" 写成对 ℓ 递归的 `Low` 而不是 `Ordᴸ (at ℓ r)`. I 层的树 `OrdI′` 对 `Σ Lv Ordᴸ` 分支, `Ωᴵ`、`Ωᴵ+1` 是普通树, 不需要替身.
> 2. **ψ_I 以层号为输出可以直接写出, 不自指 (§3).** `ψᴵ : OrdI′ → Lv`: 零 ↦ Λ, 后继 ↦ 下一个 Ω-不动点, `limᵢ` 分支 (层 ℓ < I) ↦ `limᴼ ℓ`, I-共尾分支 ↦ 对角 ℕ-极限, 对角线的回灌是 "层号 L ↦ 树 `Ω L` 于层 L" (`reseed`), 折叠本身不参与归纳-递归; IR 只在层号类型里. 层 3 的 "折叠结果可当下标" 在这里是**定义性的** (`Lv` 是宇宙, 任何树的 `toLv` 都是层号, 不要证书), 代价转移到两处: 有界三歧 (派发) 与 "输出是 Ω-不动点" (回灌的值正确性, `ΩL-Λ` 只差一位).
> 3. **Λ 在 I 之前, 而且与 I 层无关 (§2 末).** Λ = `lim (λ n → iter ΩL zero n)` 是 `Lv` 的一个普通 ℕ-极限层号, 只用到 Ω-封闭 (`limᴼ`), 不用到 I 层的树; EBO = ψ₀(Λ) 的树是 `ψ⁰ (Ω Λ)` 的形状. 所以 **I 层不是替身机制的替代品, Ω-封闭的层号类型才是**; 而它把替身的代价搬到了派发: `Ordᴸ` 上的一般 ψ 要在 `Lv` 上做有界三歧, 而 `limᴼ` 层号作界时三歧要分支族的有向性证据 (§4, 只编译类型 `Lv⁺`), 于是 `toLv` 不再免费 (每个 `limᵢ` 节点的分支函数都要单调证书), 这正是现有 `HS`/`Good` 证书在全部层上的推广. **结论: 搬家, 不是省掉.**
> 4. **序对应的后一半已经在仓库里 (§5).** Stage2Label 的 `Lab-oc : Lab X u → NF₁ u → Lab Y v → NF₁ v → v <ᵀ u → Y ≺ X` 正是 "项序 ⟹ 树序", 树序 `≺` 对一切树良基 (Level `acc≺`). 本文补上**转移定理** `Transfer.accP`: 任何向下封闭、全体带标签的 `NF₁` 项类, 其每个项都 `Acc` (15 行). 所以 "从树得到记号的 Acc" 只剩一件事: **类内每个项都有带标签的树** (不是沿基本列路径的标签, 是类内全部项). 以 ψ₀(Ω_Ω+Ω₂) 之下的 `NF₁` 项为校准: 转移 15 行 + 翻译 ≈300 + 类范围标签定理 ≈1000–1500 (带前缀的 `Generic`, Stage2Label §9 (i)(ii)), 合计 ≈1300–1800 行, 全部在层 4.
> 5. **代价估计 (§6).** 四层口径: (a) EBO = ψ₀(Λ): 层 1 ≈400, 层 2 +250, 层 3 +1200–1800, 层 4 +2000–3000; (b) ψ_{Ω₁}(I): +80 / +60 / +600 / +1500; (c) ψ_{Ω₁}(Ω_{I+ω}): +60 / +100 / +400 / +1500. 与归档记号侧 I 层 (≈510 / ≈585 / ≈7565, 标签 n/a) 相比: 层 1–2 同量级, 层 3 树侧便宜 (良基性免费, 付的是派发证据), 层 4 记号侧 n/a 而树侧不可免.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示; 不导入归档的 Mahlo 代码 (只读). 脚手架与内容的区分在 §7.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccScout where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Stage2 using (WLPO; dec→WLPO)
import OCF.Align.EBO as E
open E using (T; _<ᵀ_)
open import OCF.Align.Correspond using (Lab)
open import OCF.Align.StandardOmega using (NF₁)
open import OCF.Align.Stage2Label using (Lab-oc)
```

## §1 读法 A: 第二梯级 `Ordᴵ ⊎ {I+n}`

问题 1 的字面提议: 在现有层号类型 `Ordᴵ` 之上加第二梯级 I, I+1, …, I 层的树对整个 `Ordᴵ` 分支. 先把它造出来.

```agda
data Lv₂ : Set where
  ι  : Ordᴵ → Lv₂
  I₊ : ℕ → Lv₂

data _<ᴺ_ : ℕ → ℕ → Set where
  z< : ∀ {n} → zero <ᴺ suc n
  s< : ∀ {m n} → m <ᴺ n → suc m <ᴺ suc n

data _<₂_ : Lv₂ → Lv₂ → Set where
  ιι : ∀ {a b} → a ≺ᴵ b → ι a <₂ ι b
  ιI : ∀ {a n} → ι a <₂ I₊ n
  II : ∀ {m n} → m <ᴺ n → I₊ m <₂ I₊ n
```

I 层的树: 对 `Ordᴵ` 分支 (`limᴸ`), 对某可数层的树分支 (`limᵢ`), 对下一梯级的树分支 (`limᴵ⁺`), 两种嵌入. 参数 `B` 是下一梯级的树类型, I 层取 `⊥`.

```agda
data OrdI (B : Set) : Set where
  zero  : OrdI B
  suc   : OrdI B → OrdI B
  lim   : (ℕ → OrdI B) → OrdI B
  limᴸ  : (Ordᴵ → OrdI B) → OrdI B
  limᵢ  : (ℓ : Ordᴵ) → (Ordᶜ ℓ → OrdI B) → OrdI B
  limᴵ⁺ : (B → OrdI B) → OrdI B
  upᶜ   : (ℓ : Ordᴵ) → Ordᶜ ℓ → OrdI B
  up    : B → OrdI B

OrdI₊ : ℕ → Set
OrdI₊ zero    = OrdI ⊥
OrdI₊ (suc n) = OrdI (OrdI₊ n)

Ω_I : OrdI₊ zero
Ω_I = limᴸ (λ ℓ → upᶜ ℓ (Ω ℓ))

Ω_I+1 : OrdI₊ (suc zero)
Ω_I+1 = limᴵ⁺ up
```

编译通过, 全在 `Set` (`Ordᴵ : Set`, `Ordᶜ ℓ : Set`, 对它们分支的 W-型仍在 `Set`), 严格正 (分支类型都是已定义好的类型, 不是互递归的), `--without-K` 无事. 壁垒定理 (Barrier) 不咬这里: 它的前提是 "可数层的下标类型有精确的 Ω-共尾元且有界三歧", 而 `Ω_I` 是更高梯级的一棵树, 不是 `Ordᴵ` 的元素.

但读法 A 是空心的, 两条编译的否定.

**否定 1: 中间没有层号.** `Lv₂` 里 I 之下的层号全是 `ι ℓ`, 可数. ψ_I 的输出 (Λ = ψ_I(0), 以及一切 Ω-不动点) 不可数而 < I, 在 `Lv₂` 里无处安放; "`toLevel` 式地把 I 层的树映回层号" 只能映到 `I₊` 梯级, 即把 Λ 与 I 混同.

```agda
no-middle : ∀ L → (∀ ℓ → ι ℓ <₂ L) → L <₂ I₊ zero → ⊥
no-middle (ι a)  h ιI with h a
... | ιι p = ≺ᴵ-irrefl p
no-middle (I₊ n) h (II ())
```

**否定 2: 界 I 处的三歧就是无界三歧, 推出 WLPO.** 交替路线的派发靠有界三歧 `<ᴵ-dec` (两个层号在公共上界之下才比较). 在 `Lv₂` 里以 `I₊ 0` 为界的三歧, 限制到 `ι` 上就是 `Ordᴵ` 的**无界**三歧; 由 Stage2 的 `dec→WLPO` (任意 a 与固定的 ω+1 比较可判定 ⟹ WLPO) 立得. 这是壁垒定理在第二梯级的形态: 不是 "下标类型有 Ω-共尾元", 而是 "以 I 为界的比较没有可数的公共上界".

```agda
Trich₂ : Set
Trich₂ = ∀ {a b} → a <₂ I₊ zero → b <₂ I₊ zero → a <₂ b ⊎ b <₂ a ⊎ a ≡ b

trich→WLPO : (∀ a b → a ≺ᴵ b ⊎ b ≺ᴵ a ⊎ a ≅ᴵ b) → WLPO
trich→WLPO tri = dec→WLPO dec where
  dec : ∀ a → Dec (a ≺ᴵ suc ωᴵ)
  dec a with tri a (suc ωᴵ)
  ... | inj₁ p        = yes p
  ... | inj₂ (inj₁ q) = no (λ p → ≺ᴵ-irrefl (≺ᴵ-trans p q))
  ... | inj₂ (inj₂ e) = no (λ p → ≺ᴵ-irrefl (≺ᴵ-respˡ (≅ᴵ-sym e) p))

Trich₂→WLPO : Trich₂ → WLPO
Trich₂→WLPO tri = trich→WLPO tri′ where
  tri′ : ∀ a b → a ≺ᴵ b ⊎ b ≺ᴵ a ⊎ a ≅ᴵ b
  tri′ a b with tri {ι a} {ι b} ιI ιI
  ... | inj₁ (ιι p)        = inj₁ p
  ... | inj₂ (inj₁ (ιι q)) = inj₂ (inj₁ q)
  ... | inj₂ (inj₂ refl)   = inj₂ (inj₂ (≅ᴵ-refl a))
```

所以 I 层的折叠 ψ_δ (δ 可数, ≥ 1) 作用于对 `Ordᴵ` 全分支的 `Ω_I` 节点时, 忠实派发要拿每个分支层号去和 δ 比, 正是 Stage2 的 D1 (`dec→WLPO`). 目标 δ = 0 (`ψ⁰`) 与目标 I 自身 (§3) 不比较, 不受影响; 中间目标全部受影响. 这与交替路线 "Ω_Ω 只作参数层前缀, 由上下文链计值" 的现状一致: 读法 A 没有提供新的东西.

## §2 读法 B: 层号宇宙 `Lv` (归纳-递归), Ω-封闭

Setzer 的 I 对应 ML₁W 的宇宙: 层号的类型要对 "第 k 层的树取上确界" 封闭 (`limᴼ`), 这样 Ω_{k+1} 本身才是层号, Ω-不动点才是层号. 树族 `Ordᴸ : Lv → Set` 必须与 `Lv` 同时定义 (构造子 `limᴼ` 的分支类型是 `Ordᴸ k`), 即归纳-递归. 为了让正性检查通过, 树类型取为**参数化的**一般树 `Tree P Br C` (预先定义, 不提 `Lv`): `P` 是前驱路径的类型, `Br r` 是路径 `r` 处的树类型, `C` 是本层的共尾类型 (只有 `limᴼ` 层非空).

```agda
data Tree (P : Set) (Br : P → Set) (C : Set) : Set where
  zero : Tree P Br C
  suc  : Tree P Br C → Tree P Br C
  lim  : (ℕ → Tree P Br C) → Tree P Br C
  limᵢ : (r : P) → (Br r → Tree P Br C) → Tree P Br C
  limᶜ : (C → Tree P Br C) → Tree P Br C
  up   : (r : P) → Br r → Tree P Br C
```

层号宇宙. `Pre ℓ` 是 ℓ 的结构前驱路径 (取代 Level 的 `_◃_` 数据类型: 互递归的数据类型会在 `limᴼ` 的定义域里负出现), `Low ℓ r` 是路径 `r` 处的树类型 (对 ℓ 结构递归; 若写成 `Ordᴸ (at ℓ r)` 停机检查不过, 因为 `at ℓ r` 不是 ℓ 的子项 —— 这是 Level 用 `U i (r : i ◃ ℓ)` 对证明递归的同一个坎, 这里改为对 ℓ 递归, 把 `at` 与 `low-at : Low ℓ r ≡ Ordᴸ (at ℓ r)` 放在后面), `Cof` 是共尾类型.

```agda
data Lv : Set
Pre  : Lv → Set
Low  : (ℓ : Lv) → Pre ℓ → Set
Cof  : Lv → Set
Ordᴸ : Lv → Set

data Lv where
  zero : Lv
  suc  : Lv → Lv
  lim  : (ℕ → Lv) → Lv
  limᴼ : (k : Lv) → (Ordᴸ k → Lv) → Lv

Pre zero       = ⊥
Pre (suc k)    = ⊤ ⊎ Pre k
Pre (lim f)    = Σ ℕ λ n → ⊤ ⊎ Pre (f n)
Pre (limᴼ k g) = Σ (Ordᴸ k) λ x → ⊤ ⊎ Pre (g x)

Low (suc k)    (inj₁ _)     = Ordᴸ k
Low (suc k)    (inj₂ r)     = Low k r
Low (lim f)    (n , inj₁ _) = Ordᴸ (f n)
Low (lim f)    (n , inj₂ r) = Low (f n) r
Low (limᴼ k g) (x , inj₁ _) = Ordᴸ (g x)
Low (limᴼ k g) (x , inj₂ r) = Low (g x) r

Cof (limᴼ k g) = Ordᴸ k
Cof _          = ⊥

Ordᴸ ℓ = Tree (Pre ℓ) (Low ℓ) (Cof ℓ)

at : (ℓ : Lv) → Pre ℓ → Lv
at (suc k)    (inj₁ _)     = k
at (suc k)    (inj₂ r)     = at k r
at (lim f)    (n , inj₁ _) = f n
at (lim f)    (n , inj₂ r) = at (f n) r
at (limᴼ k g) (x , inj₁ _) = g x
at (limᴼ k g) (x , inj₂ r) = at (g x) r

low-at : ∀ ℓ r → Low ℓ r ≡ Ordᴸ (at ℓ r)
low-at (suc k)    (inj₁ _)     = refl
low-at (suc k)    (inj₂ r)     = low-at k r
low-at (lim f)    (n , inj₁ _) = refl
low-at (lim f)    (n , inj₂ r) = low-at (f n) r
low-at (limᴼ k g) (x , inj₁ _) = refl
low-at (limᴼ k g) (x , inj₂ r) = low-at (g x) r

coeᴸ : ∀ ℓ r → Ordᴸ (at ℓ r) → Low ℓ r
coeᴸ ℓ r = subst (λ A → A) (sym (low-at ℓ r))
```

编译通过: 正性检查无异议 (在 `limᴼ` 的定义域 `Ordᴸ k` 的展开中, `Lv` 只以元素 `k`、`g x` 的身份出现, 类型 `Lv` 与任何互递归数据类型都不出现), 宇宙层级 `Lv : Set`、`Ordᴸ ℓ : Set`, 停机检查对 `Pre`/`Low`/`Cof`/`Ordᴸ` 都是对 `Lv` 的结构递归 (`Ordᴸ ℓ → Low ℓ` 同参数, `Low → Ordᴸ` 严格下降, 环路有下降), `--without-K` 无事. 这回答了问题 1 的 "是否要 `Set₁`" (否) 与 "IR 是否需要" (是, 但只在层号类型里).

Ω 与总的 `toLv` (本文的 Ω、toLevel 为避免与 Level 的同名者冲突, 写作 `Ωᴸ`、`toLv`). 关键差别: 在现有的 Level 里 `toLevel` 只对第 0 层带 `HS` 证书的树定义, 因为 `Ordᴵ.lim` 要单调证据; 这里 `Lv` 的 `lim`/`limᴼ` 不带证据, 于是**任何层的任何树**都有层号, 不要证书. 嵌入节点 `up r x` 的 `x : Low ℓ r` 要沿路径 `r` 走回 `Ordᴸ` (`toLvL`), 否则停机检查看不见 `subst` 下的下降; `limᶜ` 节点只在 `limᴼ` 层有分支 (`cofLv`, 其余层 `Cof = ⊥`, 节点是空极限, 取 0).

```agda
Ωᴸ : (ℓ : Lv) → Ordᴸ ℓ
Ωᴸ zero       = suc zero
Ωᴸ (suc k)    = limᵢ (inj₁ tt) (up (inj₁ tt))
Ωᴸ (lim f)    = lim (λ n → up (n , inj₁ tt) (Ωᴸ (f n)))
Ωᴸ (limᴼ k g) = limᶜ (λ x → up (x , inj₁ tt) (Ωᴸ (g x)))

cofLv : ∀ ℓ → (Cof ℓ → Lv) → Lv
cofLv (limᴼ k g) h = limᴼ k h
cofLv zero       h = zero
cofLv (suc _)    h = zero
cofLv (lim _)    h = zero

toLv  : ∀ {ℓ} → Ordᴸ ℓ → Lv
toLvL : ∀ ℓ (r : Pre ℓ) → Low ℓ r → Lv

toLv zero                   = zero
toLv (suc x)                = suc (toLv x)
toLv (lim f)                = lim (λ n → toLv (f n))
toLv {ℓ} (limᵢ r f)         = limᴼ (at ℓ r) (λ y → toLv (f (coeᴸ ℓ r y)))
toLv {ℓ} (limᶜ f)           = cofLv ℓ (λ x → toLv (f x))
toLv {ℓ} (up r x)           = toLvL ℓ r x

toLvL (suc k)    (inj₁ _)     x = toLv x
toLvL (suc k)    (inj₂ r)     x = toLvL k r x
toLvL (lim f)    (n , inj₁ _) x = toLv x
toLvL (lim f)    (n , inj₂ r) x = toLvL (f n) r x
toLvL (limᴼ k g) (y , inj₁ _) x = toLv x
toLvL (limᴼ k g) (y , inj₂ r) x = toLvL (g y) r x

ΩL : Lv → Lv
ΩL ℓ = toLv (Ωᴸ ℓ)

_ : ∀ k → ΩL (suc k) ≡ limᴼ k (λ x → toLv x)
_ = λ k → refl
```

`ΩL (suc k)` 字面上就是 "第 k 层全部树的层号的上确界", 即 Ω_{k+1} 作为层号. 于是 Λ (最小 Ω-不动点) 是一个普通的 ℕ-极限层号, 它的 Ω 只差一位 (与 README 记的 `shift-unlabel` 同型: 值是不动点, 字面是平移), EBO 的树是 `ψ⁰ (Ωᴸ Λ)` 的形状 (`ψ⁰` 本身要一般的 ψ, 见 §4):

```agda
Λ : Lv
Λ = lim (λ n → iter ΩL zero n)

ΩL-Λ : ΩL Λ ≡ lim (λ n → iter ΩL zero (suc n))
ΩL-Λ = refl

ΩᴸΛ : Ordᴸ Λ
ΩᴸΛ = Ωᴸ Λ
```

**问题 3 的回答.** Λ 在这里完全不需要 I 层: 它只用到 `limᴼ` (Ω-封闭) 与 ℕ-极限. 现有路线用替身 ℓ₀ 的原因是 `Ordᴵ` 没有 `limᴼ`, 不是没有 I. 所以 "I 层让替身机制变得不必要" 的说法要修正为 "**Ω-封闭的层号类型**让替身作为类型变得不必要", 而代价搬到了 `Lv` 上的派发与证书 (§4).

## §3 I 层的树与以层号为输出的折叠 ψ_I

I 层的树对全部 `(ℓ , x)` 分支 (`Σ Lv Ordᴸ`, 即 I 的共尾类型), 每个层号 ℓ 都是前驱. I+1 层多一个前驱 (I 本身), 共尾类型空.

```agda
OrdI′ : Set
OrdI′ = Tree Lv Ordᴸ (Σ Lv Ordᴸ)

Ωᴵ-child : Σ Lv Ordᴸ → OrdI′
Ωᴵ-child (ℓ , x) = up ℓ x

Ωᴵ : OrdI′
Ωᴵ = limᶜ Ωᴵ-child

BrI : ⊤ ⊎ Lv → Set
BrI (inj₁ _) = OrdI′
BrI (inj₂ ℓ) = Ordᴸ ℓ

OrdI′+1 : Set
OrdI′+1 = Tree (⊤ ⊎ Lv) BrI ⊥

Ωᴵ+1 : OrdI′+1
Ωᴵ+1 = limᵢ (inj₁ tt) (up (inj₁ tt))
```

ψ_I 的类型是 `OrdI′ → Lv`: 输出是层号. 各子句按 Level 的 ψ 逐条翻译, 目标是 I 自身, 所以 **从不派发** (一切分支层号 ℓ ∈ `Lv` 都 < I, 一切 I-共尾分支 ≥ I): 零 ↦ Λ (目标的 "Ω", 即最小 Ω-不动点); 后继 ↦ 下一个 Ω-不动点; `limᵢ ℓ` ↦ `limᴼ ℓ` (分支层在目标之下, 保留为层号的上确界, 这正是 `Lv` 要 `limᴼ` 的第二个理由); `limᶜ` (I-共尾) ↦ 对角 ℕ-极限, 回灌 `reseed : Lv → Σ Lv Ordᴸ` 把输出层号 L 变回树 `Ωᴸ L` 于层 L (ψ_I 的输出是 Ω-不动点, 所以 `Ωᴸ L` 的值就是 L, 这是回灌的值正确性, 本文不证); `up ℓ x` ↦ 对低层树继续折叠 (`ψᴸ`, 同一套子句, 目标仍是 I).

```agda
nextFix : Lv → Lv
nextFix L = lim (λ n → iter ΩL (suc L) n)

ψᴸ  : ∀ {ℓ} → Ordᴸ ℓ → Lv
ψᴸL : ∀ ℓ (r : Pre ℓ) → Low ℓ r → Lv

ψᴸ zero                = Λ
ψᴸ (suc a)             = nextFix (ψᴸ a)
ψᴸ (lim f)             = lim (λ n → ψᴸ (f n))
ψᴸ {ℓ} (limᵢ r f)      = limᴼ (at ℓ r) (λ y → ψᴸ (f (coeᴸ ℓ r y)))
ψᴸ {ℓ} (limᶜ f)        = cofLv ℓ (λ x → ψᴸ (f x))
ψᴸ {ℓ} (up r x)        = ψᴸL ℓ r x

ψᴸL (suc k)    (inj₁ _)     x = ψᴸ x
ψᴸL (suc k)    (inj₂ r)     x = ψᴸL k r x
ψᴸL (lim f)    (n , inj₁ _) x = ψᴸ x
ψᴸL (lim f)    (n , inj₂ r) x = ψᴸL (f n) r x
ψᴸL (limᴼ k g) (y , inj₁ _) x = ψᴸ x
ψᴸL (limᴼ k g) (y , inj₂ r) x = ψᴸL (g y) r x

reseed : Lv → Σ Lv Ordᴸ
reseed L = L , Ωᴸ L

ψᴵ : OrdI′ → Lv
ψᴵ zero       = Λ
ψᴵ (suc a)    = nextFix (ψᴵ a)
ψᴵ (lim f)    = lim (λ n → ψᴵ (f n))
ψᴵ (limᵢ ℓ f) = limᴼ ℓ (λ y → ψᴵ (f y))
ψᴵ (limᶜ f)   = lim (λ n → ψᴵ (f (iter (λ s → reseed (ψᴵ (f s))) (reseed Λ) n)))
ψᴵ (up ℓ x)   = ψᴸ x

ψᴵ-Ωᴵ : ψᴵ Ωᴵ ≡ lim (λ n → ψᴵ (Ωᴵ-child (iter (λ s → reseed (ψᴵ (Ωᴵ-child s))) (reseed Λ) n)))
ψᴵ-Ωᴵ = refl

ψᴵ-Λ : ψᴵ (up Λ ΩᴸΛ) ≡ lim (λ n → ψᴸ (Ωᴸ (iter ΩL zero n)))
ψᴵ-Λ = refl
```

**问题 2 的回答.** (i) 类型 `ψᴵ : OrdI′ → Lv` 可以直接写, 折叠的输出类型 `Lv` 不提折叠自身, 折叠不参与归纳-递归; IR 只在 `Lv`/`Ordᴸ` 这一对里, `--safe --without-K` 接受. (ii) "折叠结果可当下标" (层 3) 在这个设计下是定义性的: `ψᴵ` 的输出就是层号, `toLv` 对一切树都有定义. 但这不是白得的: 层 3 的内容搬到 (a) 回灌的**值**正确性 (`reseed` 假定输出是 Ω-不动点; `ΩL-Λ` 显示连 Λ 也只在模平移下成立, 所以要 "模 ≅ 的 Ω-不动点" 引理), (b) 可数目标的派发 (§4). (iii) ψ_I(0) = Λ 的玩具实例是上面的 `Λ`、`ψᴸ zero`、`ψᴵ zero`; 对角 ℕ-极限的形状由 `ψᴵ-Ωᴵ` (refl) 给出; `ψᴵ-Λ` (refl): ψ_I(Λ) = sup_n ψ_I(Ω^n(0)), 嵌入的低层树沿 `ψᴸL` 回到 `ψᴸ`.

`ψᴵ` 的语义本文不认证 (没有对 OT_I 的标签), 它是 "类型能写出、停机检查通过、对角线形状正确" 的证据, 不是定理.

## §4 代价搬到哪里: `Lv` 上的有界三歧

`Ordᴸ` 上一般的 ψ (可数目标 i, 环境 ℓ) 的 `limᵢ` 子句要比较分支层号 j 与目标 i (都 < ℓ), 这是 Level 的 `<ᴵ-dec`. 它对界 ℓ 结构归纳: 界是 `lim f s` 时取两个前驱 `f n`, `f m` 的公共上界 `f (max n m)`, 用的是 `lim` 携带的单调证据 `s`. 界是 `limᴼ k g` 时, 两个前驱是 `g x`, `g y`, 公共上界要 **分支族的有向性**: `∀ x y → Σ z. g x ⊑ g z × g y ⊑ g z`. 所以 `Lv` 若要有有界三歧, `limᴼ` 必须像 `Ordᴵ.lim` 那样携带证据, 而证据的类型 `⊑` 又是与 `Lv` 互递归的数据类型 —— 与 IR 的 `Ordᴸ` 混在同一个互递归块里. 下面只编译**类型** (`Lv⁺` 与三个序关系), 检验 Agda 是否接受这种组合; `<-dec` 本身不写.

```agda
infix 4 _<⁺_ _≅⁺_ _⊑⁺_

data Lv⁺ : Set
data _<⁺_ : Lv⁺ → Lv⁺ → Set
data _≅⁺_ : Lv⁺ → Lv⁺ → Set
data _⊑⁺_ : Lv⁺ → Lv⁺ → Set
Pre⁺  : Lv⁺ → Set
Low⁺  : (ℓ : Lv⁺) → Pre⁺ ℓ → Set
Cof⁺  : Lv⁺ → Set
Ordᴸ⁺ : Lv⁺ → Set

Dir : ∀ {A : Set} → (A → Lv⁺) → Set
Dir {A} g = ∀ x y → Σ A λ z → g x ⊑⁺ g z × g y ⊑⁺ g z

data Lv⁺ where
  zero : Lv⁺
  suc  : Lv⁺ → Lv⁺
  lim  : (f : ℕ → Lv⁺) → (∀ n → f n ⊑⁺ f (suc n)) → Lv⁺
  limᴼ : (k : Lv⁺) (g : Ordᴸ⁺ k → Lv⁺) → Dir g → Lv⁺

data _<⁺_ where
  zero : ∀ {a} → a <⁺ suc a
  suc  : ∀ {a b} → a <⁺ b → a <⁺ suc b
  lim  : ∀ {a f s} n → a <⁺ f n → a <⁺ lim f s
  limᴼ : ∀ {a k g d} x → a <⁺ g x → a <⁺ limᴼ k g d

data _≅⁺_ where
  z≅ : zero ≅⁺ zero
  s≅ : ∀ {a b} → a ≅⁺ b → suc a ≅⁺ suc b
  l≅ : ∀ {f g s t} → (∀ n → f n ≅⁺ g n) → lim f s ≅⁺ lim g t
  o≅ : ∀ {k g g′ d d′} → (∀ x → g x ≅⁺ g′ x) → limᴼ k g d ≅⁺ limᴼ k g′ d′

data _⊑⁺_ where
  z⊑ : ∀ {b} → zero ⊑⁺ b
  s⊑ : ∀ {a a′ b} → a ≅⁺ a′ → a′ <⁺ b → suc a ⊑⁺ b
  l⊑ : ∀ {f s b} → (∀ n → f n ⊑⁺ b) → lim f s ⊑⁺ b
  o⊑ : ∀ {k g d b} → (∀ x → g x ⊑⁺ b) → limᴼ k g d ⊑⁺ b

Pre⁺ zero         = ⊥
Pre⁺ (suc k)      = ⊤ ⊎ Pre⁺ k
Pre⁺ (lim f _)    = Σ ℕ λ n → ⊤ ⊎ Pre⁺ (f n)
Pre⁺ (limᴼ k g _) = Σ (Ordᴸ⁺ k) λ x → ⊤ ⊎ Pre⁺ (g x)

Low⁺ (suc k)      (inj₁ _)     = Ordᴸ⁺ k
Low⁺ (suc k)      (inj₂ r)     = Low⁺ k r
Low⁺ (lim f _)    (n , inj₁ _) = Ordᴸ⁺ (f n)
Low⁺ (lim f _)    (n , inj₂ r) = Low⁺ (f n) r
Low⁺ (limᴼ k g _) (x , inj₁ _) = Ordᴸ⁺ (g x)
Low⁺ (limᴼ k g _) (x , inj₂ r) = Low⁺ (g x) r

Cof⁺ (limᴼ k g _) = Ordᴸ⁺ k
Cof⁺ _            = ⊥

Ordᴸ⁺ ℓ = Tree (Pre⁺ ℓ) (Low⁺ ℓ) (Cof⁺ ℓ)
```

编译通过: 四个数据类型 + 四个递归函数的归纳-递归块被接受, 有向性证据 `Dir g` 对 `Ordᴸ⁺ k` 的元素量化, `⊑⁺` 正出现. 这说明 "Ω-封闭 + 带证据的层号类型" 在 `--safe --without-K` 下是可以**定义**的. 代价在定义之后:

- `o≅` 只允许同一个 `k` (不同的 `k ≅⁺ k′` 要把 `x : Ordᴸ⁺ k` 搬到 `Ordᴸ⁺ k′`, 即 Level 的 `tr`, 它是对 `≅` 证明递归的函数, 要再进互递归块一次; 本文未试).
- `toLv` 不再是总函数: `limᵢ r f` 节点要 `Dir (toLv ∘ f)`, 即分支函数 `f` 在 `⊑` 下单调且 `Ordᴸ⁺ (at ℓ r)` 有向 (`x ⊑ x + y` 类的引理). 这是现有 `HS`/`Good` 证书推广到全部层与全部 `limᵢ` 节点, 规模与 Level + Uniform 的证书部分同量级或更大 —— 这就是 "搬家" 的具体内容.
- 派发 `<-dec` 的 `limᴼ` 情形: 公共上界 `g z` 结构上更小 (`g z` 是 `limᴼ k g d` 的子项), 归纳能走; 但 `Ordᴵ` 版本的后继情形依赖 `s⊑` 的 `≅` 搬运, `limᴼ` 版本同样要 `tr`.

## §5 序对应: 转移定理

问题 4. 仓库里已有的: Level 的 `acc≺` (树序 `≺` 对一切树良基, 不要证书), Stage2Label 的 `Lab-oc` (两个带标签的 `NF₁` 项, 项序给树序). 缺的是把它们接成记号侧 `Acc` 的一条定理, 下面补上: 对任意向下封闭、全体带标签的 `NF₁` 项类 `P`, 类内每个项都 `Acc`. 证明对标签树的 `Acc≺` 归纳.

```agda
module Transfer
  (P      : T → Set)
  (P-NF   : ∀ {t} → P t → NF₁ t)
  (P-down : ∀ {s t} → s <ᵀ t → P t → P s)
  (P-lab  : ∀ {t} → P t → Σ (Ordᶜ zero) λ X → Lab X t)
  where

  go : ∀ {X t} → Acc≺ X → Lab X t → P t → E.Acc t
  go (acc h) lX pt = E.acc λ {s} s<t →
    let ps = P-down s<t pt
        Y , lY = P-lab ps
    in go (h (Lab-oc lX (P-NF pt) lY (P-NF ps) s<t)) lY ps

  accP : ∀ {t} → P t → E.Acc t
  accP pt with P-lab pt
  ... | X , lX = go (acc (acc≺ X)) lX pt

  FGH-P : ∀ t → P t → ℕ → ℕ
  FGH-P t pt = E.FGH t (accP pt)
```

**读法.** 树侧的良基性是免费的 (`acc≺` 对一切树, 连 `HS` 都不要); 项序到树序由标签给出 (`Lab-oc`, 8 行); 转移 15 行. 于是 "树交付记号的 Acc" 的全部代价集中在一个前提: **`P-lab`, 类内每一个项都有带标签的树**. 这与现有标签定理的形状不同: 现有的是沿基本列路径的标签 (链点 γ′_k、X₂、T_ω 等) 与参数化的形状定理 (`Tη-label′`: 尾巴带标签则 ψ₀(Ω_Ω+Ω_η) 带标签); `P-lab` 要的是类内全部项, 包括不在任何基本列路径上的项. 这就是 Stage2Label §9 的 "带前缀的 `Generic`" + "逐阶段生成的下标系统".

**校准: ψ₀(Ω_Ω+Ω₂) 之下的 `NF₁` 项的 Acc.** 取 `P t = NF₁ t × t <ᵀ X₂ᵗ`: `P-NF` 平凡, `P-down` 由 `<ᵀ` 的传递性 (Bachmann/Closure 已有), 缺 `P-lab`. 估计:

| 部件 | 行数 | 状态 |
|---|---|---|
| 树序良基 `acc≺` | 0 | 已有 (Level) |
| `Lab-oc` | 0 | 已有 (Stage2Label) |
| 转移 `Transfer` | 15 | 本文 |
| 翻译 `⟦_⟧ : NF₁ ∩ (< X₂) → Ordˢ` (下标 ≤ Ω+c 到层号, 要 `cert`/`toLevel`) | ≈300 | 未做 |
| 类范围标签定理 (带前缀的 `Generic`, 阶段 2 下标系统沿 A 的链生成) | ≈1000–1500 | 未做 (Stage2Label §9 (i)(ii)) |
| 合计 | ≈1300–1800 | 全在层 4 |

对照: 记号侧直接证同一片段的良基性 (Setzer 式 §4–§5 对 I 系统是 ≈7000 行; 对 ψ₀(Ω_Ω+Ω₂) 这一小段没有现成数字, 但 Bachmann 的 `cofin`/`oc` 经验是每个下标阶段几百行). 树侧的优势是良基性免费, 劣势是要先有全类标签, 而全类标签又正是层 4 的全部内容, 所以 "从树得 Acc" 不比 "从标签得 FGH 方程" 多花钱, 也不少花: 它是层 4 的推论.

## §6 四层口径的代价估计

按 feedback-loc-conventions 的四层 (累计; 层 1 定义本体, 层 2 + 折叠, 层 3 + 折叠输出可回灌的证明, 层 4 + 对 OT_I/EBO 的标签). 以 §2–§4 的 `Lv⁺` 设计为底, 不是以现有 `Ordᴵ` + 替身为底 (两者不能叠加, 见 §7).

| | (a) EBO = ψ₀(Λ) | (b) ψ_{Ω₁}(I) | (c) ψ_{Ω₁}(Ω_{I+ω}) | 归档记号侧 I 层 |
|---|---|---|---|---|
| 层 1 | ≈400 (`Lv⁺` 宇宙 + `Tree` 族 + 提升/嵌入 + Ω + toLevel 子句 + 加法) | +80 (I 层树族、`Ωᴵ`、`reseed`) | +60 (I+n 梯级, 本文 `OrdI′+1` 的推广) | ≈510 |
| 层 2 | +250 (一般 ψ 含 `limᴼ` 情形的派发; `ψ⁰`) | +60 (`ψᴵ`, 本文已写 25 行) | +100 (I+n 目标的 ψ_{I+k}, 派发在 ℕ 梯级) | ≈585 |
| 层 3 | +1200–1800 (`<-dec` 的 `limᴼ` 情形含 `tr`; `Dir` 证据的全层 `Good`; `Ψ-mono` 推广; Λ 之下折叠输出的层号证书) | +600 (ψ_I 输出模 ≅ 是 Ω-不动点; 回灌值正确) | +400 (I+k 目标输出可当 I+j 下标) | ≈7565 (Theorem 4.41 到端点) |
| 层 4 | +2000–3000 (Λ 之下的 EBO 标签: 第一阶段 Ω_Ω 用了 1430, Λ 之下有 ω 个阶段 Ω_Ω, Ω_{Ω_Ω}, …, 每阶段的下标系统换一次) | +1500 (对 OT_I 的 ψ_I 项标签, 新的记号侧 NF/cofin 对 I) | +1500 (Ω_{I+n} 的标签) | n/a |

读法: 层 1–2 两边同量级 (与 BTBO 的表一致: "树比记号复杂" 不成立). 层 3 树侧估计是记号侧的 1/4–1/6, 因为树侧的良基性免费, 付的只是派发证据 (`Dir`) 与回灌值正确性; 但这一层是**新数学** (现有 Level/Uniform 的证书都只对 ℕ-极限层号). 层 4 记号侧 n/a (Setzer 的记号系统就是标准), 树侧不可免且是最大项. 数字的不确定度: 层 1–2 ±30%, 层 3–4 一个因子 2.

## §7 脚手架与内容

- **内容 (可直接引用的编译事实):** `no-middle`、`trich→WLPO`、`Trich₂→WLPO` (读法 A 的两条否定); `Lv`/`Ordᴸ` 归纳-递归宇宙编译通过, `Ωᴸ`/`toLv` 总函数, `ΩL (suc k) ≡ limᴼ k toLv` 与 `ΩL-Λ` 字面成立; `ψᴵ : OrdI′ → Lv` 过停机检查, 对角线形状 `ψᴵ-Ωᴵ`、`ψᴵ-Λ` refl; `Lv⁺` 带证据版本的互递归块编译通过; `Transfer.accP`.
- **脚手架 (只为让上面的东西能写, 本身无主张):** `OrdI`/`OrdI₊`/`Ω_I`/`Ω_I+1` (读法 A 的树, 只用来展示 "编译无碍"), `Tree` 的 `up` 允许任意前驱 (Level 只允许直接前驱 `◃₁`, 这里不做规范形), `Cof` 作为单独的递归函数 (也可并入 `Pre`), `at`/`low-at`/`coeᴸ` (若把 `limᴼ` 的第一个参数改为路径就可省掉), `_<ᴺ_`.
- **未做而且不该在侦察里做:** `Lv⁺` 上的 `<-dec`、`tr`; `Ordᴸ` 上一般的 ψ 与 `ψ⁰`; `ψᴵ` 对 OT_I 的任何标签; `P-lab` 的任何实例.
- **与现有路线的关系:** `Lv⁺` 不是 `Ordᴵ` 的扩展而是替换 (`Ordᴵ.lim` 的证据形状保留, 加 `limᴼ`); Level 的 1043 行里 `Ordᴵ` 部分 (≈300) 要重写, 树族/Ω/ψ 部分可逐字搬 (`Tree` 与 `Ord₊` 同构, `Pre`/`Low` 取代 `◃`/`U`), Uniform2 栈的前缀塔/地板/`Ψ` 帧在 `Lv⁺` 上失去 "符号前缀" 的理由 (Ω_Ω 是真层号 `ΩL (suc zero)`), 但 "上下文链计值" 的内容变成 "`limᴼ` 层号之下的派发", 没有消失.
