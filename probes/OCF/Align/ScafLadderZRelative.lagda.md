> **机械克隆.** 由 `Relative` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 依目标的互模拟与地板见证 (二): `BranchΩ` 无居留、层对齐的互模拟与 $\psi_0(\Omega_\Omega^2)$

> 接 [RelativeBase](RelativeBase.lagda.md) (任务 1–2). 本文是任务 3–4: `BranchΩ (Ω̂A 0) []` 的状态, $\psi_0(\Omega_\Omega^2)$ 的标签状态, 与深度 $\ge2$、$\psi_0(\Omega_{\Omega+1})$ 的展望.
>
> 结论先说:
>
> 1. **`BranchΩ (Ω̂A 0) []` 无居留 (`¬BranchΩ`, 编译).** Uniform2 的 `TΩ2-cond : BranchΩ (Ω̂A 0) [] → …` 是前提为假的条件定理. 反例在它的 `bR` 字段: $\eta=3$, 两个底 `PL`/`PR` 只在目标 2 处不同 (`suc zero` 对 `up zero (up zero 1)`, $\cong^\mathsf s$ 相关, `PL≈PR`), 目标 0 处分支树沿路径 `[1,0,0,1,0,0,1,2]` 到达两个闭包, 界字面分别是 $2$ 与 $1$ (`bndL`/`bndR`, `refl`), 而 `ŝ≅` 要求界 $\cong^\mathsf I$. 路径正是 Uniform2 §6 的失败点 (深度 1、尾巴 $\Omega_3$、节点层 2 的 `gi` 行、分支 `up zero x`), 但输入不是伪输入, 而是**链点**: 目标 2 上算出的链点含底在目标 2 处的输出, 随后在目标 0 被重新折叠. 同一论证: Uniform2Depth1 的 `GA1` 对分支帧 $\psi_\Omega(\Omega_3)$ 无居留 (`¬GA1-Ω₃`).
> 2. **依目标能救回的部分是定理 (RelativeBase `bRᵗ`):** 分支互模拟在目标 $\succeq\eta-2$ 处对一切底成立. 反例的目标 $0\prec1=\eta-2$.
> 3. **(b′) 的正确形式: 层对齐的互模拟 $\cong^\mathsf A$ (§2–§3).** 只允许成对的 `up` (同种类, `self` 同下标), 其余构造与 $\cong^\mathsf s$ 相同. 深度 0、1 的折叠尊重它, **不要任何对齐前提** (`fold-≅1ᴬ`: 两侧层号 $\cong^\mathsf I$、根地板 $\sim$ 即可; `AlignD`/`lowA`/`AlignT` 都不再需要). **`bRᴬ`: 对一切 $\eta\cong\eta'$, 分支 $\psi_\Omega(\Omega_\eta)$ 的深度 1 折叠在一切目标处互模拟, 只要底层对齐**; 空前缀是层对齐的 (`∅ᴿ-ᴬ`). `¬AlignΩ₃` 的输入对不层对齐 (`¬x₃y₃`), 反例的底也不 (`¬PLᴬPR`).
> 4. **`TΩ2-label` 未得.** `BranchΩ` 的互模拟部分在层对齐的形式下是定理 (`bR-free`), 剩下的是标签部分: 一般层号尾巴的深度 1 折叠定理, 带层对齐的自互模拟与依目标的 "诚实" 前提 (§4, 精确列出). $\psi_0(\psi_\Omega(\Omega_3))$、$\psi_0(\psi_\Omega(\Omega_4))$ 的标签也未得 (同一定理的 $\eta=3,4$ 实例).
> 5. **展望 (§5, 只给类型):** 层对齐的好性记录 `GRᴬ`/`GA0ᴬ`/`GA1ᴬ`, 修正的前提 `BranchΩᴬ` 与目标 `TΩ2-target`, 一般尾巴定理的类型 `FullTlᴬ`, 深度 2 的 `GA2ᴬ`/`goodΩ̂₂-type`, $\psi_0(\Omega_{\Omega+1})$ 的 `topO-type`.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 不改任何已有文件. Uniform2Base 的互模拟引理凡要改成层对齐的, 都以新名字 (后缀 `ᴬ`) 复制在本文.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderZRelative where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.ScafLadderZPrefix using (Z; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; trˢ; tr⁻ˢ; addˢ;
  Restrˢ; resˢ; res⁻ˢ; sqˢ; walkˢ)
open Restrˢ using (repˢ; backˢ; ltˢ; eqˢ)
import OCF.Align.EBO as E
open E using (T; natT; Ωt) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab)
open import OCF.Align.ScafLadderZStandardOmega using (NF₁)
open import OCF.Align.Stage2 using (tO)
open import OCF.Align.ScafLadderZOmegaKBase using (tΩ2)
open import OCF.Align.ScafLadderZGoodLBase using (LabL)
open import OCF.Align.ScafLadderZUniformS
import OCF.Align.ScafLadderZTopDown as TD
open import OCF.Align.ScafLadderZUniform2Base
open import OCF.Align.ScafLadderZUniform2Depth1 using (_≈₁_; GA1; gr1)
open import OCF.Align.ScafLadderZUniform2 using (BranchΩ; bR; good∅ᴿ)
open import OCF.Align.ScafLadderZRelativeBase using (Up; _≈₁[_]_; bRᵗ; AlignΩ₃ᵗ; ¬AlignΩ₃⁰; one; three; LW[_]; FlrLab[_])
```
## §1 `BranchΩ (Ω̂A 0) []` 无居留

**两个底.** `PL`/`PR` 只在目标字面为 $2$ 处不同: `PL` 输出第 2 层自带的后继 `suc zero`, `PR` 输出 `up zero (up zero (suc zero))` (Uniform2 §6 的 $x$ 与 $y$). 其余目标都输出 $\Omega_i$. 分支取 $\eta=3$, 地板证据取环境层号 $4$ 上的字面证据, 目标 $0$.

```agda
four : Ordᴵ
four = suc three

pickL : (i : Ordᴵ) → Ordˢ i
pickL zero = Ωˢ zero
pickL (suc zero) = Ωˢ (suc zero)
pickL (suc (suc zero)) = Ord₊ˢ.suc Ord₊ˢ.zero
pickL (suc (suc (suc i))) = Ωˢ _
pickL (suc (suc (lim f s))) = Ωˢ _
pickL (suc (lim f s)) = Ωˢ _
pickL (lim f s) = Ωˢ _

pickR : (i : Ordᴵ) → Ordˢ i
pickR zero = Ωˢ zero
pickR (suc zero) = Ωˢ (suc zero)
pickR (suc (suc zero)) = Ord₊ˢ.up zero (Ord₊ˢ.up zero (Ord₊ˢ.suc Ord₊ˢ.zero))
pickR (suc (suc (suc i))) = Ωˢ _
pickR (suc (suc (lim f s))) = Ωˢ _
pickR (suc (lim f s)) = Ωˢ _
pickR (lim f s) = Ωˢ _

PL PR : Run fz
PL {i} _ _ = pickL i
PR {i} _ _ = pickR i

Rb : A 1 (fk zero ⊔ fk three)
Rb = fold 1 (fk three) (λ e q → e (suc q)) (Ω̂A 0) (Ωˢ three)

ev : Ev four (fz ⊔ (fk zero ⊔ fk three))
ev = tt , ((λ q → suc (suc (suc q))) , (λ q → q))

p0 : zero <ᴵ four
p0 = suc (suc (suc zero))

TL TR : Ordˢ zero
TL = Rb PL ev p0
TR = Rb PR ev p0

path : List ℕ
path = 1 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 2 ∷ []

bndL : TD.bndOf (walkˢ TL path) ≡ suc (suc zero)
bndL = refl

bndR : TD.bndOf (walkˢ TR path) ≡ suc zero
bndR = refl
```
**读法 (路径).** 目标 0 处 $\Omega_3$ (节点层 2) 走折叠: 输出是 $\lim_m H(c_m)$, 链 $c_{m+1}=H(c_m)$ 在目标 2 上算. 路径第 1 步取 $m=1$: $c_1=H(\Omega_2)$ 在目标 2 处是穿透输出 $\mathrm{limᵢ}$ (节点层 1), 其分支含 `Ω̂A 0` 作用于底, 而底在目标 2 处的输出 (`PL`: `suc zero`) 就在里面. 之后在目标 0 折叠 $c_1$: 节点层 1、0 都走折叠 (第 2、3 步取链点 0), 第 4 步取第 1 份副本 (目标 2 上的 `Ω̂A 0` 闭包, `kc 3`), 第 5 步取它的第 0 点, 第 6 步取节点层 0 的链点 0, 第 7 步取底输出所在的项, 第 8 步取底输出 (第 2 层后继, 地板 `fk 1`) 的第 2 份副本: 那里 `Ω̂A 0` 在目标 0 处弹栈, 左侧的底地板含 `fk 1`, 界 `suc 1`; 右侧底输出是 `up zero (up zero 1)`, 地板降为 `fz`, 界 `suc 0`. 这一组 `kind` 是用交互式计值逐步核对过的 (`kl kl kl (kc 3) kl kl kl (kc 2)` 对 `kc 1`).

**两个底互模拟.** 对一切 $\cong^\mathsf I$ 的目标对: 字面 $2$ 处由两次 `upʳ`, 其余处由 `Ωˢ-≅`.

```agda
PL≈PR : PL ≈ᴿ PR
PL≈PR ev p ev′ p′ z≅ = Ωˢ-≅ z≅
PL≈PR ev p ev′ p′ (s≅ z≅) = Ωˢ-≅ (s≅ z≅)
PL≈PR ev p ev′ p′ (s≅ (s≅ z≅)) = upʳ (upʳ (s≅ z≅))
PL≈PR ev p ev′ p′ (s≅ (s≅ (s≅ e))) = Ωˢ-≅ (s≅ (s≅ (s≅ e)))
PL≈PR ev p ev′ p′ (s≅ (s≅ (l≅ h))) = Ωˢ-≅ (s≅ (s≅ (l≅ h)))
PL≈PR ev p ev′ p′ (s≅ (l≅ h)) = Ωˢ-≅ (s≅ (l≅ h))
PL≈PR ev p ev′ p′ (l≅ h) = Ωˢ-≅ (l≅ h)
```
**第 0 层树的反演.** 第 0 层没有 `limᵢ` 与 `up`, $\cong^\mathsf s$ 的推导由两棵树的首构造子决定, 于是 `walkˢ` 的每一步与界 `bndOf` 都尊重 $\cong^\mathsf s$. 这里没有 Uniform2Base §12 所说的 "两侧反演 `lim`/`ŝ` 卡住" 的问题: 反演的是推导而不是树的等式.

```agda
sq-≅ : ∀ {x y : Ordˢ zero} n → x ≅ˢ y → sqˢ x n ≅ˢ sqˢ y n
sq-≅ n z≅ = z≅
sq-≅ n (s≅ d) = s≅ d
sq-≅ n (l≅ h) = h n
sq-≅ n (lᵢ≅ {p = ()} e h)
sq-≅ n (upˡ {r = ()} d)
sq-≅ n (upʳ {r = ()} d)
sq-≅ zero (ŝ≅ k ec et eg) = et
sq-≅ (suc n) (ŝ≅ k ec et eg) = ŝ≅ k ec et eg
sq-≅ zero (ĉ≅ ec dt dg eo eO) = eo
sq-≅ (suc n) (ĉ≅ ec dt dg eo eO) = ĉ≅ ec dt dg eo eO

walk-≅ : ∀ {x y : Ordˢ zero} ps → x ≅ˢ y → walkˢ x ps ≅ˢ walkˢ y ps
walk-≅ [] d = d
walk-≅ (n ∷ ps) d = walk-≅ ps (sq-≅ n d)

bnd-≅ : ∀ {x y : Ordˢ zero} → x ≅ˢ y → TD.bndOf x ≅ᴵ TD.bndOf y
bnd-≅ z≅ = z≅
bnd-≅ (s≅ d) = z≅
bnd-≅ (l≅ h) = z≅
bnd-≅ (lᵢ≅ {p = ()} e h)
bnd-≅ (upˡ {r = ()} d)
bnd-≅ (upʳ {r = ()} d)
bnd-≅ (ŝ≅ k ec et eg) = ec
bnd-≅ (ĉ≅ ec dt dg eo eO) = z≅

no21 : suc (suc zero) ≅ᴵ suc zero → ⊥
no21 (s≅ ())
```
**否定.**

```agda
¬bR : (∀ η η′ → η ≅ᴵ η′ → fold 1 (fk η) (λ e q → e (suc q)) (Ω̂A 0) (Ωˢ η) ≈₁ fold 1 (fk η′) (λ e q → e (suc q)) (Ω̂A 0) (Ωˢ η′)) → ⊥
¬bR br = no21 (bnd-≅ (walk-≅ path (br three three (≅ᴵ-refl three) fz∼ PL≈PR ev p0 ev p0 z≅)))

¬BranchΩ : BranchΩ (Ω̂A 0) [] → ⊥
¬BranchΩ Br = ¬bR (bR Br)

¬GA1-Ω₃ : ∀ {ζ} → GA1 (fold 1 (fk three) (λ e q → e (suc q)) (Ω̂A 0) (Ωˢ three)) ζ → ⊥
¬GA1-Ω₃ G = no21 (bnd-≅ (walk-≅ path (gr1 G fz∼ PL≈PR ev p0 ev p0 z≅)))
```
**读法.** `¬bR` 只用 `bR` 在 $\eta=\eta'=3$ 的一个实例与一对不带标签的底. Uniform2 §6 的诊断 ("派发只升目标, $\preceq$ 目标的地板项从不被读到, 假输入只在穿透分支出现; 只改证明的量化范围") 对一次计值是对的 (RelativeBase §1–§6), 但 **链点把高目标处算出的树带回低目标**: 折叠情形下 $c_m$ 在节点层上算, 然后作为指数尾巴在原目标上重新折叠, 底在节点层上的输出的 `up`-结构在原目标处决定弹栈的界. 所以缺的不是 "依目标的互模拟", 而是 **底的层对齐**; 一旦 `≈₁` 对一切 $\cong^\mathsf s$ 相关的底量化, `bR` 就是假的. 同一论证给出 `¬GA1-Ω₃`: Uniform2Depth1 的好帧记录 `GA1` 对分支帧 $\psi_\Omega(\Omega_3)$ (对任何 $\zeta$) 无居留, 因为它的 `gr1` 字段就是 `bR` 的这个实例. 也就是说, Uniform2 的 `FullΩ₂` 式定理在第 3 层不可能存在, 不论地板见证怎样处理; `goodΩ̂₀` 的 `selfΩ̂0` 成立是因为 `Ω̂A 0` 是深度 0 的闭包, 底的输出不进入任何深度 $\ge1$ 的尾巴.

## §2 层对齐的互模拟 $\cong^\mathsf A$

`Eqᴬ`/`Rᴬ`/`_≅ᴬ_`: UniformS 的 `Eq₊ˢ`/`Rˢ`/`_≅ˢ_` 去掉单侧的 `upˡ`/`upʳ`, 换成成对的 `uᴬ` (两侧同为 `up zero`, 或同为 `up (self n)` 且 $n$ 相同, `UpK`). `limᵢ` 的输入关系也是 $\cong^\mathsf A$ (嵌套的 `Rᴬ`, 与 `Rˢ` 同构造). 两侧层号 $\cong^\mathsf I$ 时, 层对齐的推导在每个后继步上两侧的地板自动 $\sim$ (`up zero` 两侧都换成 `flo` 于 $\cong^\mathsf I$ 的层号, `up (self n)` 两侧都不换), 这就是 "层对齐" 的含义.

```agda
data UpK : ∀ {k k′ ℓ ℓ′} → k ◃₁ ℓ → k′ ◃₁ ℓ′ → Set where
  uz : ∀ {k k′} → UpK (zero {k}) (zero {k′})
  us : ∀ {f g : ℕ → Ordᴵ} {s t} n → UpK (self {f} {s} n) (self {g} {t} n)

module _ (ℓ : Ordᴵ) (R : (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → ∀ {ℓ′} → Ordˢ ℓ′ → Set) where
  data Eqᴬ : ∀ {ℓ′} → Ordˢ ℓ → Ordˢ ℓ′ → Set where
    zᴬ  : ∀ {ℓ′} → Eqᴬ {ℓ′} Ord₊ˢ.zero Ord₊ˢ.zero
    sᴬ  : ∀ {ℓ′} {a : Ordˢ ℓ} {b : Ordˢ ℓ′} → Eqᴬ a b → Eqᴬ (Ord₊ˢ.suc a) (Ord₊ˢ.suc b)
    lᴬ  : ∀ {ℓ′} {f : ℕ → Ordˢ ℓ} {g : ℕ → Ordˢ ℓ′} → (∀ n → Eqᴬ (f n) (g n)) → Eqᴬ (Ord₊ˢ.lim f) (Ord₊ˢ.lim g)
    lᵢᴬ : ∀ {ℓ′ j j′} {p : j <ᴵ ℓ} {q : j′ <ᴵ ℓ′} {f : Uˢ j (<→◃ p) → Ordˢ ℓ} {g : Uˢ j′ (<→◃ q) → Ordˢ ℓ′} →
          j ≅ᴵ j′ →
          (∀ (x : Ordˢ j) (y : Ordˢ j′) → R j (<→◃ p) (intoˢ (<→◃ p) x) y → Eqᴬ (f (intoˢ (<→◃ p) x)) (g (intoˢ (<→◃ q) y))) →
          Eqᴬ (Ord₊ˢ.limᵢ p f) (Ord₊ˢ.limᵢ q g)
    uᴬ  : ∀ {ℓ′ k k′} {r : k ◃₁ ℓ} {r′ : k′ ◃₁ ℓ′} {x : Uˢ k (◃₁→◃ r)} {y : Uˢ k′ (◃₁→◃ r′)} →
          UpK r r′ → R k (◃₁→◃ r) x (outˢ (◃₁→◃ r′) y) → Eqᴬ (Ord₊ˢ.up r x) (Ord₊ˢ.up r′ y)
    ŝᴬ  : ∀ {ℓ′ c c′} {t₀ : Ordˢ ℓ} {t₀′ : Ordˢ ℓ′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} {g′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Ordˢ ℓ′} →
          kd ℓ ≡ kd ℓ′ → c ≅ᴵ c′ → Eqᴬ t₀ t₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → Eqᴬ (g η e) (g′ η′ e′)) →
          Eqᴬ (Ord₊ˢ.ŝ c t₀ g) (Ord₊ˢ.ŝ c′ t₀′ g′)
    ĉᴬ  : ∀ {ℓ′ c c′ t₀ t₀′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {g′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Z}
          {o₀ : Ordˢ ℓ} {o₀′ : Ordˢ ℓ′} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} {o′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Ordˢ ℓ′} →
          c ≅ᴵ c′ → t₀ ≅ᶻ t₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ᶻ g′ η′ e′) →
          Eqᴬ o₀ o₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → Eqᴬ (o η e) (o′ η′ e′)) →
          Eqᴬ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) (Ord₊ˢ.ĉᴸ c′ t₀′ g′ o₀′ o′)

Rᴬ : ∀ {ℓ} (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → ∀ {ℓ′} → Ordˢ ℓ′ → Set
Rᴬ i zero         x b = Eqᴬ i Rᴬ x b
Rᴬ i (suc r)      x b = Rᴬ i r x b
Rᴬ _ (self {f} n) x b = Eqᴬ (f n) Rᴬ x b
Rᴬ i (lim n r)    x b = Rᴬ i r x b

infix 4 _≅ᴬ_
_≅ᴬ_ : ∀ {ℓ₁ ℓ₂} → Ordˢ ℓ₁ → Ordˢ ℓ₂ → Set
_≅ᴬ_ {ℓ₁} = Eqᴬ ℓ₁ Rᴬ

R→≅ᴬ : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) {x : Ordˢ i} {b : Ordˢ ℓ′} → Rᴬ i r (intoˢ r x) b → x ≅ᴬ b
R→≅ᴬ zero      e = e
R→≅ᴬ (suc r)   e = R→≅ᴬ r e
R→≅ᴬ (self n)  e = e
R→≅ᴬ (lim n r) e = R→≅ᴬ r e

≅→Rᴬ : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) {x : Ordˢ i} {b : Ordˢ ℓ′} → x ≅ᴬ b → Rᴬ i r (intoˢ r x) b
≅→Rᴬ zero      e = e
≅→Rᴬ (suc r)   e = ≅→Rᴬ r e
≅→Rᴬ (self n)  e = e
≅→Rᴬ (lim n r) e = ≅→Rᴬ r e
```
**对称、第 0 层与 $\cong^\mathsf s$ 一致.** 对称与 UniformS 的 `≅ˢ-sym`/`R-flipˢ`/`flipRˢ` 同构造 (把 `R-flipᴬ` 写成 `≅→Rᴬ ∘ ≅ᴬ-sym ∘ R→≅ᴬ` 时停机检查失败, 见 §6 注记). 第 0 层没有 `up` 与 `limᵢ`, $\cong^\mathsf A$ 蕴含 $\cong^\mathsf s$ (`≅ᴬ→≅ˢ₀`; 链原子与 `toZ-≅` 只在第 0 层用到 $\cong^\mathsf s$).

```agda
UpK-sym : ∀ {k k′ ℓ ℓ′} {r : k ◃₁ ℓ} {r′ : k′ ◃₁ ℓ′} → UpK r r′ → UpK r′ r
UpK-sym uz = uz
UpK-sym (us n) = us n

≅ᴬ-sym  : ∀ {ℓ₁ ℓ₂} {a : Ordˢ ℓ₁} {b : Ordˢ ℓ₂} → a ≅ᴬ b → b ≅ᴬ a
R-flipᴬ : ∀ {j j′ ℓ₁ ℓ₂} (r : j ◃ ℓ₁) (r′ : j′ ◃ ℓ₂) {x : Ordˢ j} {y : Ordˢ j′} → Rᴬ j r (intoˢ r x) y → Rᴬ j′ r′ (intoˢ r′ y) x
flipRᴬ  : ∀ {j j′ ℓ₂} (r′ : j′ ◃ ℓ₂) {x : Ordˢ j} {y : Ordˢ j′} → x ≅ᴬ y → Rᴬ j′ r′ (intoˢ r′ y) x
≅ᴬ-sym zᴬ = zᴬ
≅ᴬ-sym (sᴬ d) = sᴬ (≅ᴬ-sym d)
≅ᴬ-sym (lᴬ h) = lᴬ (λ n → ≅ᴬ-sym (h n))
≅ᴬ-sym (lᵢᴬ {p = p} {q = q} e h) = lᵢᴬ (≅ᴵ-sym e) (λ y x d → ≅ᴬ-sym (h x y (R-flipᴬ (<→◃ q) (<→◃ p) d)))
≅ᴬ-sym (uᴬ uz d) = uᴬ uz (≅ᴬ-sym d)
≅ᴬ-sym (uᴬ (us n) d) = uᴬ (us n) (≅ᴬ-sym d)
≅ᴬ-sym (ŝᴬ k ec et eg) = ŝᴬ (sym k) (≅ᴵ-sym ec) (≅ᴬ-sym et) (λ η e η′ e′ eη → ≅ᴬ-sym (eg η′ e′ η e (≅ᴵ-sym eη)))
≅ᴬ-sym (ĉᴬ ec dt dg eo eO) = ĉᴬ (≅ᴵ-sym ec) (≅ᶻ-sym dt) (λ η e η′ e′ eη → ≅ᶻ-sym (dg η′ e′ η e (≅ᴵ-sym eη)))
                               (≅ᴬ-sym eo) (λ η e η′ e′ eη → ≅ᴬ-sym (eO η′ e′ η e (≅ᴵ-sym eη)))
R-flipᴬ zero      r′ e = flipRᴬ r′ e
R-flipᴬ (suc r)   r′ e = R-flipᴬ r r′ e
R-flipᴬ (self n)  r′ e = flipRᴬ r′ e
R-flipᴬ (lim n r) r′ e = R-flipᴬ r r′ e
flipRᴬ zero       e = ≅ᴬ-sym e
flipRᴬ (suc r′)   e = flipRᴬ r′ e
flipRᴬ (self n)   e = ≅ᴬ-sym e
flipRᴬ (lim n r′) e = flipRᴬ r′ e

≅ᴬ→≅ˢ₀ : ∀ {ℓ′} {x : Ordˢ zero} {y : Ordˢ ℓ′} → x ≅ᴬ y → x ≅ˢ y
≅ᴬ→≅ˢ₀ zᴬ = z≅
≅ᴬ→≅ˢ₀ (sᴬ d) = s≅ (≅ᴬ→≅ˢ₀ d)
≅ᴬ→≅ˢ₀ (lᴬ h) = l≅ (λ n → ≅ᴬ→≅ˢ₀ (h n))
≅ᴬ→≅ˢ₀ (lᵢᴬ {p = ()} e h)
≅ᴬ→≅ˢ₀ (uᴬ {r = ()} k d)
≅ᴬ→≅ˢ₀ (ŝᴬ k ec et eg) = ŝ≅ k ec (≅ᴬ→≅ˢ₀ et) (λ η e η′ e′ eη → ≅ᴬ→≅ˢ₀ (eg η e η′ e′ eη))
≅ᴬ→≅ˢ₀ (ĉᴬ ec dt dg eo eO) = ĉ≅ ec dt dg (≅ᴬ→≅ˢ₀ eo) (λ η e η′ e′ eη → ≅ᴬ→≅ˢ₀ (eO η e η′ e′ eη))
```
**搬运与 $\Omega$.** UniformS 的 `trˢ-≅` 组逐字 (`up` 子句成对), `Ωˢ-≅ᴬ` 的 `up` 本来就是成对的.

```agda
trˢ-≅ᴬ    : ∀ {a b ℓ′} (e : a ≅ᴵ b) {x : Ordˢ a} {y : Ordˢ ℓ′} → x ≅ᴬ y → trˢ e x ≅ᴬ y
tr⁻ˢ-≅ᴬ   : ∀ {a b ℓ′} (e : a ≅ᴵ b) {x : Ordˢ b} {y : Ordˢ ℓ′} → x ≅ᴬ y → tr⁻ˢ e x ≅ᴬ y
backˢ-≅ᴬ  : ∀ {j a b ℓ′} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} {v : Ordˢ ℓ′} → u ≅ᴬ v → backˢ (resˢ q e) u ≅ᴬ v
back⁻ˢ-≅ᴬ : ∀ {j a b ℓ′} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} {v : Ordˢ ℓ′} → u ≅ᴬ v → backˢ (res⁻ˢ q e) u ≅ᴬ v

trˢ-≅ᴬ e zᴬ = zᴬ
trˢ-≅ᴬ e (sᴬ d) = sᴬ (trˢ-≅ᴬ e d)
trˢ-≅ᴬ e (lᴬ h) = lᴬ (λ n → trˢ-≅ᴬ e (h n))
trˢ-≅ᴬ e (lᵢᴬ {p = q} {q = q₂} {f = f} {g = g} ej h) =
  lᵢᴬ (≅ᴵ-trans (≅ᴵ-sym (eqˢ (resˢ q e))) ej) λ u v d →
    subst (λ w → trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w))) ≅ᴬ g (intoˢ (<→◃ q₂) v))
          (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) u))
          (trˢ-≅ᴬ e (h _ v (≅→Rᴬ (<→◃ q) (backˢ-≅ᴬ q e (R→≅ᴬ (<→◃ (ltˢ (resˢ q e))) d)))))
trˢ-≅ᴬ (s≅ e) (uᴬ uz d) = uᴬ uz (trˢ-≅ᴬ e d)
trˢ-≅ᴬ (l≅ h) (uᴬ (us n) d) = uᴬ (us n) (trˢ-≅ᴬ (h n) d)
trˢ-≅ᴬ e (ŝᴬ k ec et eg) = ŝᴬ (trans (sym (kd-≅ e)) k) ec (trˢ-≅ᴬ e et) (λ η d η′ d′ eη → trˢ-≅ᴬ e (eg η d η′ d′ eη))
trˢ-≅ᴬ e (ĉᴬ ec dt dg eo eO) = ĉᴬ ec dt dg (trˢ-≅ᴬ e eo) (λ η d η′ d′ eη → trˢ-≅ᴬ e (eO η d η′ d′ eη))

tr⁻ˢ-≅ᴬ e zᴬ = zᴬ
tr⁻ˢ-≅ᴬ e (sᴬ d) = sᴬ (tr⁻ˢ-≅ᴬ e d)
tr⁻ˢ-≅ᴬ e (lᴬ h) = lᴬ (λ n → tr⁻ˢ-≅ᴬ e (h n))
tr⁻ˢ-≅ᴬ e (lᵢᴬ {p = q} {q = q₂} {f = f} {g = g} ej h) =
  lᵢᴬ (≅ᴵ-trans (≅ᴵ-sym (eqˢ (res⁻ˢ q e))) ej) λ u v d →
    subst (λ w → tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w))) ≅ᴬ g (intoˢ (<→◃ q₂) v))
          (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) u))
          (tr⁻ˢ-≅ᴬ e (h _ v (≅→Rᴬ (<→◃ q) (back⁻ˢ-≅ᴬ q e (R→≅ᴬ (<→◃ (ltˢ (res⁻ˢ q e))) d)))))
tr⁻ˢ-≅ᴬ (s≅ e) (uᴬ uz d) = uᴬ uz (tr⁻ˢ-≅ᴬ e d)
tr⁻ˢ-≅ᴬ (l≅ h) (uᴬ (us n) d) = uᴬ (us n) (tr⁻ˢ-≅ᴬ (h n) d)
tr⁻ˢ-≅ᴬ e (ŝᴬ k ec et eg) = ŝᴬ (trans (kd-≅ e) k) ec (tr⁻ˢ-≅ᴬ e et) (λ η d η′ d′ eη → tr⁻ˢ-≅ᴬ e (eg η d η′ d′ eη))
tr⁻ˢ-≅ᴬ e (ĉᴬ ec dt dg eo eO) = ĉᴬ ec dt dg (tr⁻ˢ-≅ᴬ e eo) (λ η d η′ d′ eη → tr⁻ˢ-≅ᴬ e (eO η d η′ d′ eη))

backˢ-≅ᴬ zero      (s≅ e) d = tr⁻ˢ-≅ᴬ e d
backˢ-≅ᴬ (suc q)   (s≅ e) d = backˢ-≅ᴬ q e d
backˢ-≅ᴬ (lim n q) (l≅ h) d = backˢ-≅ᴬ q (h n) d

back⁻ˢ-≅ᴬ zero      (s≅ e) d = trˢ-≅ᴬ e d
back⁻ˢ-≅ᴬ (suc q)   (s≅ e) d = back⁻ˢ-≅ᴬ q e d
back⁻ˢ-≅ᴬ (lim n q) (l≅ h) d = back⁻ˢ-≅ᴬ q (h n) d

≅ᴬ-tr⁻ˢ : ∀ {a b ℓ′} (e : a ≅ᴵ b) {y : Ordˢ ℓ′} {x : Ordˢ b} → y ≅ᴬ x → y ≅ᴬ tr⁻ˢ e x
≅ᴬ-tr⁻ˢ e d = ≅ᴬ-sym (tr⁻ˢ-≅ᴬ e (≅ᴬ-sym d))

Ωˢ-≅ᴬ : ∀ {a b} → a ≅ᴵ b → Ωˢ a ≅ᴬ Ωˢ b
Ωˢ-≅ᴬ z≅     = sᴬ zᴬ
Ωˢ-≅ᴬ (s≅ e) = lᵢᴬ e (λ x y d → uᴬ uz d)
Ωˢ-≅ᴬ (l≅ h) = lᴬ (λ n → uᴬ (us n) (Ωˢ-≅ᴬ (h n)))
```
**加法.** `addˢ` 把尾巴的 `up` 消掉 (尾巴的后继被放到被加数的层上), 所以 `addˢ-≅ᴬ` 与 `addˢ-≅` 同形; 尾巴需要 $\cong^\mathsf A$ 只是因为输出的 `limᵢ` 的输入关系是 $\cong^\mathsf A$.

```agda
R-convᴬ : ∀ {j ℓ₁ ℓ₂ ℓ′} (r : j ◃ ℓ₁) (r′ : j ◃ ℓ₂) {x : Ordˢ j} {b : Ordˢ ℓ′} → Rᴬ j r (intoˢ r x) b → Rᴬ j r′ (intoˢ r′ x) b
R-convᴬ r r′ e = ≅→Rᴬ r′ (R→≅ᴬ r e)

addˢ-≅ᴬ : ∀ {k₁ ℓ₁ k₂ ℓ₂} {σ : Simᴵ k₁ ℓ₁} {σ′ : Simᴵ k₂ ℓ₂} {a : Ordˢ ℓ₁} {a′ : Ordˢ ℓ₂} {b : Ordˢ k₁} {b′ : Ordˢ k₂} →
          kd ℓ₁ ≡ kd ℓ₂ → a ≅ᴬ a′ → b ≅ᴬ b′ → addˢ a σ b ≅ᴬ addˢ a′ σ′ b′
addˢ-≅ᴬ kℓ ea zᴬ     = ea
addˢ-≅ᴬ kℓ ea (sᴬ e) = sᴬ (addˢ-≅ᴬ kℓ ea e)
addˢ-≅ᴬ kℓ ea (lᴬ h) = lᴬ (λ n → addˢ-≅ᴬ kℓ ea (h n))
addˢ-≅ᴬ kℓ ea (uᴬ uz e)     = addˢ-≅ᴬ kℓ ea e
addˢ-≅ᴬ kℓ ea (uᴬ (us n) e) = addˢ-≅ᴬ kℓ ea e
addˢ-≅ᴬ {σ = σ} {σ′ = σ′} {a = a} {a′ = a′} kℓ ea (lᵢᴬ {p = q} {q = q′} {f = f} {g = g} e h) = lᵢᴬ e λ x y d →
  subst₂ (λ u v → addˢ a σ (f (intoˢ (<→◃ q) u)) ≅ᴬ addˢ a′ σ′ (g (intoˢ (<→◃ q′) v)))
         (sym (out-intoˢ (<→◃ (σ q)) x)) (sym (out-intoˢ (<→◃ (σ′ q′)) y))
         (addˢ-≅ᴬ kℓ ea (h x y (R-convᴬ (<→◃ (σ q)) (<→◃ q) d)))
addˢ-≅ᴬ {k₁ = zero}    {k₂ = zero}    kℓ ea (ŝᴬ k ec et eg) =
  ĉᴬ ec (toZ-≅ (≅ᴬ→≅ˢ₀ et)) (λ η e η′ e′ eη → toZ-≅ (≅ᴬ→≅ˢ₀ (eg η e η′ e′ eη))) (addˢ-≅ᴬ kℓ ea et)
     (λ η e η′ e′ eη → addˢ-≅ᴬ kℓ ea (eg η e η′ e′ eη))
addˢ-≅ᴬ {k₁ = zero}    {k₂ = suc _}   kℓ ea (ŝᴬ k ec et eg) = ⊥-elim (tf k)
addˢ-≅ᴬ {k₁ = zero}    {k₂ = lim _ _} kℓ ea (ŝᴬ k ec et eg) = ⊥-elim (tf k)
addˢ-≅ᴬ {k₁ = suc _}   {k₂ = zero}    kℓ ea (ŝᴬ k ec et eg) = ⊥-elim (tf (sym k))
addˢ-≅ᴬ {k₁ = lim _ _} {k₂ = zero}    kℓ ea (ŝᴬ k ec et eg) = ⊥-elim (tf (sym k))
addˢ-≅ᴬ {k₁ = suc _}   {k₂ = suc _}   kℓ ea (ŝᴬ k ec et eg) = ŝᴬ kℓ ec (addˢ-≅ᴬ kℓ ea et) (λ η e η′ e′ eη → addˢ-≅ᴬ kℓ ea (eg η e η′ e′ eη))
addˢ-≅ᴬ {k₁ = suc _}   {k₂ = lim _ _} kℓ ea (ŝᴬ k ec et eg) = ŝᴬ kℓ ec (addˢ-≅ᴬ kℓ ea et) (λ η e η′ e′ eη → addˢ-≅ᴬ kℓ ea (eg η e η′ e′ eη))
addˢ-≅ᴬ {k₁ = lim _ _} {k₂ = suc _}   kℓ ea (ŝᴬ k ec et eg) = ŝᴬ kℓ ec (addˢ-≅ᴬ kℓ ea et) (λ η e η′ e′ eη → addˢ-≅ᴬ kℓ ea (eg η e η′ e′ eη))
addˢ-≅ᴬ {k₁ = lim _ _} {k₂ = lim _ _} kℓ ea (ŝᴬ k ec et eg) = ŝᴬ kℓ ec (addˢ-≅ᴬ kℓ ea et) (λ η e η′ e′ eη → addˢ-≅ᴬ kℓ ea (eg η e η′ e′ eη))
addˢ-≅ᴬ kℓ ea (ĉᴬ ec dt dg eo eO) = ĉᴬ ec dt dg (addˢ-≅ᴬ kℓ ea eo) (λ η e η′ e′ eη → addˢ-≅ᴬ kℓ ea (eO η e η′ e′ eη))
```
## §3 折叠尊重 $\cong^\mathsf A$; 分支的互模拟

运行的层对齐互模拟 `_≈ᴬ_` 与行引理: Uniform2Base §7 的 `…R` 逐字, 只把 $\cong^\mathsf s$ 换成 $\cong^\mathsf A$. `limᵢRᴬ` 的折叠情形里链点经 `iter-R _≅ᴬ_` 层对齐地相关, 这正是 §1 缺的那一条.

```agda
infix 4 _≈ᴬ_
_≈ᴬ_ : ∀ {φ ψ} → Run φ → Run ψ → Set
_≈ᴬ_ {φ} {ψ} R R′ = ∀ {i i′ ℓ ℓ′} (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (ev′ : Ev ℓ′ ψ) (p′ : i′ <ᴵ ℓ′) → i ≅ᴵ i′ → R ev p ≅ᴬ R′ ev′ p′

limRᴬ : ∀ {φ ψ} {F : ℕ → Run φ} {G : ℕ → Run ψ} → (∀ n → F n ≈ᴬ G n) → limA 0 F ≈ᴬ limA 0 G
limRᴬ h ev p ev′ p′ ei = lᴬ (λ n → h n ev p ev′ p′ ei)

sucRᴬ : ∀ {φ ψ} {R : Run φ} {R′ : Run ψ} → R ≈ᴬ R′ → sucRun R ≈ᴬ sucRun R′
sucRᴬ h ev p ev′ p′ ei = lᴬ (iter-R _≅ᴬ_ (λ e′ → addˢ-≅ᴬ (kd-≅ ei) (h ev p ev′ p′ ei) e′) zᴬ)

limᵢRᴬ : ∀ {φ ψ j j′} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → j′ <ᴵ L}
         {H : Ordˢ j → Run φ} {H′ : Ordˢ j′ → Run ψ} →
         j ≅ᴵ j′ → (∀ x y → x ≅ᴬ y → H x ≈ᴬ H′ y) → limᵢA 0 ac H ≈ᴬ limᵢA 0 ac′ H′
limᵢRᴬ {ac = ac} {ac′ = ac′} {H = H} {H′ = H′} e h ev p ev′ p′ ei with <ᴵ-dec (ac ev) p | <ᴵ-dec (ac′ ev′) p′
... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) = lᵢᴬ (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans e e₂)) λ x y d →
  subst₂ (λ a b → H (tr⁻ˢ e₁ a) ev p ≅ᴬ H′ (tr⁻ˢ e₂ b) ev′ p′)
         (sym (out-intoˢ (<→◃ r₁) x)) (sym (out-intoˢ (<→◃ r₂) y))
         (h _ _ (tr⁻ˢ-≅ᴬ e₁ (≅ᴬ-tr⁻ˢ e₂ (R→≅ᴬ (<→◃ r₁) d))) ev p ev′ p′ ei)
... | injᵃ r | injᵇ s  = ⊥-elim (clash₁ e ei r s)
... | injᵃ r | injᶜ c′ = ⊥-elim (clash₂ e ei r c′)
... | injᵇ s | injᵃ r  = ⊥-elim (clash₁ (≅ᴵ-sym e) (≅ᴵ-sym ei) r s)
... | injᶜ c′ | injᵃ r = ⊥-elim (clash₂ (≅ᴵ-sym e) (≅ᴵ-sym ei) r c′)
... | injᵇ _ | injᵇ _  = lᴬ (λ m → h _ _ (iter-R _≅ᴬ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≅ᴬ e) m) ev p ev′ p′ ei)
... | injᵇ _ | injᶜ _  = lᴬ (λ m → h _ _ (iter-R _≅ᴬ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≅ᴬ e) m) ev p ev′ p′ ei)
... | injᶜ _ | injᵇ _  = lᴬ (λ m → h _ _ (iter-R _≅ᴬ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≅ᴬ e) m) ev p ev′ p′ ei)
... | injᶜ _ | injᶜ _  = lᴬ (λ m → h _ _ (iter-R _≅ᴬ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≅ᴬ e) m) ev p ev′ p′ ei)

ĉRᴬ : ∀ {φ ψ c c′ t₀ t₀′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {g′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Z}
      {O₀ : Run φ} {O : (η : Ordᴵ) → c ⊑ᴵ η → Run φ} {O₀′ : Run ψ} {O′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Run ψ} →
      c ≅ᴵ c′ → t₀ ≅ᶻ t₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ᶻ g′ η′ e′) →
      O₀ ≈ᴬ O₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → O η e ≈ᴬ O′ η′ e′) → ĉA 0 c t₀ g O₀ O ≈ᴬ ĉA 0 c′ t₀′ g′ O₀′ O′
ĉRᴬ ec dt dg h₀ h ev p ev′ p′ ei = ĉᴬ ec dt dg (h₀ ev p ev′ p′ ei) (λ η e η′ e′ eη → h η e η′ e′ eη ev p ev′ p′ ei)

ŝRᴬ : ∀ {φ ψ c c′} {T₀ : Run φ} {G : (η : Ordᴵ) → c ⊑ᴵ η → Run φ} {T₀′ : Run ψ} {G′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Run ψ} →
      c ≅ᴵ c′ → T₀ ≈ᴬ T₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → G η e ≈ᴬ G′ η′ e′) → ŝA 0 c T₀ G ≈ᴬ ŝA 0 c′ T₀′ G′
ŝRᴬ ec h₀ h ev p ev′ p′ ei = ŝᴬ (kd-≅ ei) ec (h₀ ev p ev′ p′ ei) (λ η e η′ e′ eη → h η e η′ e′ eη ev p ev′ p′ ei)

wkRᴬ : ∀ {φ φ′ ψ ψ′} {R : Run φ} {R′ : Run φ′} (le : ∀ {L} → Ev L ψ → Ev L φ) (le′ : ∀ {L} → Ev L ψ′ → Ev L φ′) →
       R ≈ᴬ R′ → wk 0 le R ≈ᴬ wk 0 le′ R′
wkRᴬ le le′ h ev p ev′ p′ ei = h (le ev) p (le′ ev′) p′ ei

cloRᴬ : ∀ {φ φ′} {t : Run (φ ⊔ fk zero)} {g : (η : Ordᴵ) → Run (φ ⊔ fk η)}
        {t′ : Run (φ′ ⊔ fk zero)} {g′ : (η : Ordᴵ) → Run (φ′ ⊔ fk η)} → φ ∼ᶠ φ′ →
        t ≈ᴬ t′ → (∀ η η′ → η ≅ᴵ η′ → g η ≈ᴬ g′ η′) → cloA 0 t g ≈ᴬ cloA 0 t′ g′
cloRᴬ {φ} {φ′} s ht hg ev p ev′ p′ ei =
  ŝᴬ (kd-≅ ei) (s≅ (bound-≅ (⊔∼ s (fk∼ z≅)) ev p ev′ p′ ei)) (ht ev p ev′ p′ ei)
     (λ η e η′ e′ eη → hg η η′ eη _ (lim 0 (iF (bound (φ ⊔ fk zero) ev p))) _ (lim 0 (iF (bound (φ′ ⊔ fk zero) ev′ p′))) ei)
```
`fold-≅0ᴬ`: 深度 0 的折叠 (`up zero` 子句两侧都弱化证据).

```agda
fold-≅0ᴬ : ∀ {fl fl′ φ φ′ k₁ k₂} {cv : ∀ {L} → Ev L φ → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k₂ L}
           {P : Run fl} {P′ : Run fl′} {a : Ordˢ k₁} {b : Ordˢ k₂} →
           P ≈ᴬ P′ → a ≅ᴬ b → fold 0 φ cv P a ≈ᴬ fold 0 φ′ cv′ P′ b
fold-≅0ᴬ H zᴬ ev p ev′ p′ ei = H (proj₁ ev) p (proj₁ ev′) p′ ei
fold-≅0ᴬ H (sᴬ e) = sucRᴬ (fold-≅0ᴬ H e)
fold-≅0ᴬ H (lᴬ h) = limRᴬ (λ n → fold-≅0ᴬ H (h n))
fold-≅0ᴬ {k₁ = suc k′} {k₂ = suc k″} {cv = cv} {cv′ = cv′} H (uᴬ uz e) =
  wkRᴬ (λ ev → proj₁ ev , toFlo k′ (cv (proj₂ ev))) (λ ev → proj₁ ev , toFlo k″ (cv′ (proj₂ ev))) (fold-≅0ᴬ H e)
fold-≅0ᴬ H (uᴬ (us n) e) = fold-≅0ᴬ H e
fold-≅0ᴬ {k₁ = zero} {k₂ = zero} H (ŝᴬ k ec et eg) =
  ĉRᴬ ec (toZ-≅ (≅ᴬ→≅ˢ₀ et)) (λ η e η′ e′ eη → toZ-≅ (≅ᴬ→≅ˢ₀ (eg η e η′ e′ eη))) (fold-≅0ᴬ H et)
      (λ η e η′ e′ eη → fold-≅0ᴬ H (eg η e η′ e′ eη))
fold-≅0ᴬ {k₁ = zero} {k₂ = suc _}   H (ŝᴬ k ec et eg) = ⊥-elim (tf k)
fold-≅0ᴬ {k₁ = zero} {k₂ = lim _ _} H (ŝᴬ k ec et eg) = ⊥-elim (tf k)
fold-≅0ᴬ {k₁ = suc _}   {k₂ = zero} H (ŝᴬ k ec et eg) = ⊥-elim (tf (sym k))
fold-≅0ᴬ {k₁ = lim _ _} {k₂ = zero} H (ŝᴬ k ec et eg) = ⊥-elim (tf (sym k))
fold-≅0ᴬ {k₁ = suc _}   {k₂ = suc _}   H (ŝᴬ k ec et eg) = ŝRᴬ ec (fold-≅0ᴬ H et) (λ η e η′ e′ eη → fold-≅0ᴬ H (eg η e η′ e′ eη))
fold-≅0ᴬ {k₁ = suc _}   {k₂ = lim _ _} H (ŝᴬ k ec et eg) = ŝRᴬ ec (fold-≅0ᴬ H et) (λ η e η′ e′ eη → fold-≅0ᴬ H (eg η e η′ e′ eη))
fold-≅0ᴬ {k₁ = lim _ _} {k₂ = suc _}   H (ŝᴬ k ec et eg) = ŝRᴬ ec (fold-≅0ᴬ H et) (λ η e η′ e′ eη → fold-≅0ᴬ H (eg η e η′ e′ eη))
fold-≅0ᴬ {k₁ = lim _ _} {k₂ = lim _ _} H (ŝᴬ k ec et eg) = ŝRᴬ ec (fold-≅0ᴬ H et) (λ η e η′ e′ eη → fold-≅0ᴬ H (eg η e η′ e′ eη))
fold-≅0ᴬ H (ĉᴬ ec dt dg eo eO) = ĉRᴬ ec dt dg (fold-≅0ᴬ H eo) (λ η e η′ e′ eη → fold-≅0ᴬ H (eO η e η′ e′ eη))
fold-≅0ᴬ H (lᵢᴬ {p = q} e h) = limᵢRᴬ e (λ x y d → fold-≅0ᴬ H (h x y (≅→Rᴬ (<→◃ q) d)))
```
**深度 1.** `fold-≅1ᴬ` 的前提只有: 指数前缀的地板 $\sim$、指数前缀 $\approx^\mathsf A_1$、两侧尾巴层号 $\cong^\mathsf I$、根地板 $\sim$、尾巴 $\cong^\mathsf A$. 后继步的地板对齐不再是前提: `up zero` 处由 `flo-∼` 从层号 $\cong^\mathsf I$ 得到, `up (self n)` 处由 `l≅` 的第 $n$ 项. 与 Uniform2Depth1 的 `fold-≅1` 相比少了 `AlignD`, 与 RelativeBase 的 `fold-≅1ᵗ` 相比少了目标下界.

```agda
infix 4 _≈₁ᴬ_
_≈₁ᴬ_ : ∀ {φ ψ} → A 1 φ → A 1 ψ → Set
E ≈₁ᴬ E′ = ∀ {fl fl′} {P : Run fl} {P′ : Run fl′} → fl ∼ᶠ fl′ → P ≈ᴬ P′ → E P ≈ᴬ E′ P′

flo-∼ : ∀ {k k′} → k ≅ᴵ k′ → flo k ∼ᶠ flo k′
flo-∼ z≅     = fz∼
flo-∼ (s≅ e) = fk∼ e
flo-∼ (l≅ h) = fk∼ (l≅ h)

repRᴬ : ∀ {fl fl′ ψ ψ′} {Q : Run fl} {Q′ : Run fl′} {fr : A 1 ψ} {fr′ : A 1 ψ′} →
        fl ∼ᶠ fl′ → ψ ∼ᶠ ψ′ → Q ≈ᴬ Q′ → fr ≈₁ᴬ fr′ → ∀ m → repA 0 Q fr m ≈ᴬ repA 0 Q′ fr′ m
repRᴬ s sψ H F zero          = wkRᴬ proj₁ proj₁ H
repRᴬ s sψ H F (suc zero)    = F s H
repRᴬ s sψ H F (suc (suc m)) = wkRᴬ _ _ (F (⊔∼ s sψ) (repRᴬ s sψ H F (suc m)))

fold-≅1ᴬ : ∀ {flE flE′ φ φ′ k₁ k₂} {cv : ∀ {L} → Ev L φ → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k₂ L}
           {E : A 1 flE} {E′ : A 1 flE′} {a : Ordˢ k₁} {b : Ordˢ k₂} →
           flE ∼ᶠ flE′ → E ≈₁ᴬ E′ → k₁ ≅ᴵ k₂ → φ ∼ᶠ φ′ → a ≅ᴬ b → fold 1 φ cv E a ≈₁ᴬ fold 1 φ′ cv′ E′ b
fold-≅1ᴬ sE HE ek sφ zᴬ s H = wkRᴬ _ _ (HE s H)
fold-≅1ᴬ sE HE ek sφ (sᴬ e) s H = limRᴬ (λ m → repRᴬ s (⊔∼ sE sφ) H (fold-≅1ᴬ sE HE ek sφ e) m)
fold-≅1ᴬ sE HE ek sφ (lᴬ h) s H = limRᴬ (λ n → fold-≅1ᴬ sE HE ek sφ (h n) s H)
fold-≅1ᴬ sE HE ek sφ (lᵢᴬ {p = q} e h) s H =
  limᵢRᴬ e (λ x y d → fold-≅1ᴬ sE HE ek sφ (h x y (≅→Rᴬ (<→◃ q) d)) s H)
fold-≅1ᴬ {k₁ = suc k′} {k₂ = suc k″} {cv = cv} {cv′ = cv′} sE HE (s≅ ek) sφ (uᴬ uz d) s H =
  wkRᴬ (λ { (u , (w , v)) → u , (w , toFlo k′ (cv v)) }) (λ { (u , (w , v)) → u , (w , toFlo k″ (cv′ v)) })
       (fold-≅1ᴬ sE HE ek (flo-∼ ek) d s H)
fold-≅1ᴬ sE HE (l≅ hh) sφ (uᴬ (us n) d) s H = fold-≅1ᴬ sE HE (hh n) sφ d s H
fold-≅1ᴬ {k₁ = zero} {k₂ = zero} sE HE ek sφ (ŝᴬ k ec et eg) s H =
  ĉRᴬ ec (toZ-≅ (≅ᴬ→≅ˢ₀ et)) (λ η e η′ e′ eη → toZ-≅ (≅ᴬ→≅ˢ₀ (eg η e η′ e′ eη))) (fold-≅1ᴬ sE HE ek sφ et s H)
      (λ η e η′ e′ eη → fold-≅1ᴬ sE HE ek sφ (eg η e η′ e′ eη) s H)
fold-≅1ᴬ {k₁ = zero} {k₂ = suc _}   sE HE ek sφ (ŝᴬ k ec et eg) s H = ⊥-elim (tf k)
fold-≅1ᴬ {k₁ = zero} {k₂ = lim _ _} sE HE ek sφ (ŝᴬ k ec et eg) s H = ⊥-elim (tf k)
fold-≅1ᴬ {k₁ = suc _}   {k₂ = zero} sE HE ek sφ (ŝᴬ k ec et eg) s H = ⊥-elim (tf (sym k))
fold-≅1ᴬ {k₁ = lim _ _} {k₂ = zero} sE HE ek sφ (ŝᴬ k ec et eg) s H = ⊥-elim (tf (sym k))
fold-≅1ᴬ {k₁ = suc _} {k₂ = suc _} sE HE ek sφ (ŝᴬ k ec et eg) s H =
  ŝRᴬ ec (fold-≅1ᴬ sE HE ek sφ et s H) (λ η e η′ e′ eη → fold-≅1ᴬ sE HE ek sφ (eg η e η′ e′ eη) s H)
fold-≅1ᴬ {k₁ = suc _} {k₂ = lim _ _} sE HE ek sφ (ŝᴬ k ec et eg) s H =
  ŝRᴬ ec (fold-≅1ᴬ sE HE ek sφ et s H) (λ η e η′ e′ eη → fold-≅1ᴬ sE HE ek sφ (eg η e η′ e′ eη) s H)
fold-≅1ᴬ {k₁ = lim _ _} {k₂ = suc _} sE HE ek sφ (ŝᴬ k ec et eg) s H =
  ŝRᴬ ec (fold-≅1ᴬ sE HE ek sφ et s H) (λ η e η′ e′ eη → fold-≅1ᴬ sE HE ek sφ (eg η e η′ e′ eη) s H)
fold-≅1ᴬ {k₁ = lim _ _} {k₂ = lim _ _} sE HE ek sφ (ŝᴬ k ec et eg) s H =
  ŝRᴬ ec (fold-≅1ᴬ sE HE ek sφ et s H) (λ η e η′ e′ eη → fold-≅1ᴬ sE HE ek sφ (eg η e η′ e′ eη) s H)
fold-≅1ᴬ sE HE ek sφ (ĉᴬ ec dt dg eo eO) s H =
  ĉRᴬ ec dt dg (fold-≅1ᴬ sE HE ek sφ eo s H) (λ η e η′ e′ eη → fold-≅1ᴬ sE HE ek sφ (eO η e η′ e′ eη) s H)
```
**分支.** `selfΩ̂0ᴬ`: `Ω̂A 0` 是 $\approx^\mathsf A_1$ 的; `∅ᴿ-ᴬ`: 空前缀层对齐; **`bRᴬ`**: Uniform2 `BranchΩ.bR` 的层对齐形式, 对一切 $\eta\cong\eta'$ (不要标签、不要目标下界). `¬x₃y₃`: Uniform2 `¬AlignΩ₃` 的输入对不层对齐, 所以 $\Omega_3$ 的自互模拟 `Ωˢ-≅ᴬ` 根本不关联它们; `¬PLᴬPR`: §1 的反例的底不层对齐.

```agda
selfΩ̂0ᴬ : Ω̂A 0 ≈₁ᴬ Ω̂A 0
selfΩ̂0ᴬ {P = P} {P′ = P′} s H =
  cloRᴬ {t = fold 0 (fk zero) (λ e → e) P (Ωˢ (suc zero))} {g = λ η → fold 0 (fk η) (λ e q → e (suc q)) P (Ωˢ η)}
        {t′ = fold 0 (fk zero) (λ e → e) P′ (Ωˢ (suc zero))} {g′ = λ η → fold 0 (fk η) (λ e q → e (suc q)) P′ (Ωˢ η)}
        s (fold-≅0ᴬ H (Ωˢ-≅ᴬ (≅ᴵ-refl (suc zero)))) (λ η η′ eη → fold-≅0ᴬ H (Ωˢ-≅ᴬ eη))

∅ᴿ-ᴬ : ∅ᴿ ≈ᴬ ∅ᴿ
∅ᴿ-ᴬ ev p ev′ p′ ei = Ωˢ-≅ᴬ ei

bRᴬ : ∀ {η η′} (e : η ≅ᴵ η′) →
      fold 1 (fk η) (λ e q → e (suc q)) (Ω̂A 0) (Ωˢ η) ≈₁ᴬ fold 1 (fk η′) (λ e q → e (suc q)) (Ω̂A 0) (Ωˢ η′)
bRᴬ e = fold-≅1ᴬ (fk∼ z≅) selfΩ̂0ᴬ e (fk∼ e) (Ωˢ-≅ᴬ e)

¬x₃y₃ : Ord₊ˢ.suc {ℓ = suc (suc zero)} Ord₊ˢ.zero ≅ᴬ Ord₊ˢ.up {ℓ = suc (suc zero)} zero (Ord₊ˢ.up zero (Ord₊ˢ.suc Ord₊ˢ.zero)) → ⊥
¬x₃y₃ ()

¬PLᴬPR : PL ≈ᴬ PR → ⊥
¬PLᴬPR h with h tt (zero {suc (suc zero)}) tt zero (≅ᴵ-refl _)
... | ()
```
**读法.** (b′) 在两种意义下证成: 目标 $\succeq\eta-2$ 处对一切底 (RelativeBase `bRᵗ`), 一切目标处对层对齐的底 (`bRᴬ`). 第一种是 Uniform2 §6 设想的 "依目标" 形式, 它不能延伸到更低的目标 (§1); 第二种是真正需要的形式. 二者的分界正是链点: 目标 $\succeq\eta-2$ 时链点的一切地板都可忽略.

## §4 $\psi_0(\Omega_\Omega^2)$ 的状态

**未得.** 精确状态:

- `BranchΩ (Ω̂A 0) []` 是假的 (`¬BranchΩ`), 所以 `TΩ2-cond` 不能给出标签; 它的证明结构 (`goodΩ̂₁` 对一切好指数前缀) 必须改到层对齐的好性上: `GR.gR`、`GA1.gr1`、`GV1` 的互模拟部分都换成 $\approx^\mathsf A$ (§5 的 `GRᴬ`/`GA1ᴬ`). 互模拟部分换了之后, `bR` 是定理 (`bRᴬ`), `AlignD`/`lowA`/`alΩ₂` 不再需要.
- 剩下的是**标签**部分: 分支 $\psi_\Omega(\Omega_\eta)$ 对一切带标签链点层号 $\eta$ 的深度 1 折叠定理 (`W` 与目标 0 两半). 它要一般层号尾巴的 `Full₁` (Uniform2Depth1 只到第 0、1 层, Uniform2 §1 只到 $\Omega_2$、$\Omega_2+1$). 第 $\eta$ 层尾巴 $\Omega_\eta$ 的 `gi` 行 (节点层 $\eta-1$): 穿透目标 ($\succ\eta-1$) 处对任意带标签输入, 输入的一切地板可忽略 (RelativeBase `alignHigh` 的标签版, 用 `FlrLab[ c ]`); 折叠目标处只对链点, 链点的地板由它标签的首项下标见证 (RelativeBase `FL-head`). 所以一般尾巴定理需要的前提是对尾巴推导的**遗传、在 `gi` 输入处分两半**的 "诚实" 谓词 (§5 `Outlook.Hon`), 外加一条形状引理: `LW` 在目标 $j$ 处输出的标签 $\psi_w(\cdot)$ ($\mathtt{lvl}\,w\cong j$) 沿推导的每个后继行都含 $w$ (`FL-head` 的前提). 两者都未写.
- 第一个未带标签的实例: $\psi_0(\psi_\Omega(\Omega_3))$ (即 $\psi_0(\Omega_\Omega\cdot\Omega_3)$). 它的地板见证不需要 (a′) (第 2 层输入的地板总被 $\Omega_1$ 见证, RelativeBase `FL-Ω₁`), 缺的只是第 2 层一般尾巴的 `Full₂`, 带层对齐自互模拟 (任意带标签的第 2 层尾巴的 $\cong^\mathsf s$ 自互模拟可以在不同输入的分支之间把后继对到 `up`-下降的后继, 层对齐不能从 $\cong^\mathsf s$ 推出). $\psi_0(\psi_\Omega(\Omega_4))$ 另外需要 (a′) 的依目标形式 (RelativeBase `¬FL₄`/`FL₄[]`).
- `TΩ2-step` (`refl`) 与和 NonTight `TΩ2ᶠˢ` 的一致: 没有标签, 只能比较树; 两树族不同 (非紧地板记录对语法地板和), 字面 `refl` 不可能 (TopDown §7 检验 5 的理由), 未做.

**不在目标 0 计值里出现的问题.** RelativeBase §9 的 `up (self n)` 地板偏差只出现在尾巴的第 0 支是 $\Omega_0=1$ 的极限层 $\eta$ (例如 $\theta=\omega$). $\psi_0(\Omega_\Omega^2)$ 在目标 0 处只在外层闭包的链点 $\theta_k$ 上计值分支; 链点的树沿第 0 项下降最终到 $1=$ `suc zero` (底 $\varnothing$ 在目标 0 处的输出 $\Omega_0$), 所以 $\mathtt{toLevel}\,\theta_k$ 的第 0 项链最终是后继层号, $\Omega_{\mathtt{lvl}\,\theta_k}$ 的极限层分支里不出现地板为 `fk η` 的后继. 但它使 Uniform2 `BranchΩ.bW` (对一切 $\theta>1$ 与一切非零目标) 在 $\theta=\omega$、目标 $1\le i<\omega$ 处不能由 `gŝ` 行给出, 所以修正的前提 `BranchΩᴬ` 里的 `W` 部分只在目标 $\succeq\eta$ 处要求 (`bW₀` 的目标下界是 `toLevel Y hY`).

## §5 展望 (只给类型)

**层对齐的好性.** `GRᴬ` = Uniform2Base `GR` 的互模拟换成 $\approx^\mathsf A$; `∅ᴿ-good` 说明空前缀满足它 (由 Uniform2 `good∅ᴿ` 的两半与 `∅ᴿ-ᴬ`). `GA1ᴬ`: 静态地板标签, 依目标的 `W` (RelativeBase `LW[ c ]`, 地板标签也依目标), 目标 0 的标签对层对齐的好底, 帧互模拟 $\approx^\mathsf A_1$.

**修正的前提与目标.** `BranchΩᴬ`: 分支在目标 $\succeq\eta$ 处的 `W` (那里尾巴的一切地板可忽略) 与目标 0 处的标签; 互模拟部分是定理 `bR-free` (= `bRᴬ`). `TΩ2-target`: 由 `BranchΩᴬ` 推出 $\psi_0(\Omega_\Omega^2)$ 的标签 (类型; 证明要 Uniform2 §6 `DepthOneΩ` 在 `GA1ᴬ` 上的移植, 与 `clo0` 只在链点上用分支 (`Rg`) 这一事实).

**一般尾巴定理.** `Outlook.FullTlᴬ`: 对任意层号 $k$ 的带标签、层对齐自互模拟、诚实 (`Hon`) 的尾巴, 深度 1 折叠保持 `GA1ᴬ`. `BranchΩᴬ` 是它在 $t=\Omega_\eta$ 的实例 (加上 $\Omega_\eta$ 的诚实性). `Hon` 的内容见 §4.

**深度 $\ge2$ 与 $\psi_0(\Omega_{\Omega+1})$.** 深度 2 的帧互模拟 `_≈₂ᴬ_` (作用于 $\approx^\mathsf A_1$ 相关的指数前缀) 与好性 `GA2ᴬ`; `goodΩ̂₂-type`: $\Omega_\Omega$ 闭包在深度 2 是好的 (即 $\psi_\Omega(\psi_\Omega(\cdots+\Omega_\Omega))$ 的那一层); 它要深度 2 的 `fold` 在层对齐的尾巴上的互模拟 (`fold-≅1ᴬ` 的深度 2 版, 证明是同一递归套一层 `repA 1`) 与深度 2 的诚实谓词 (深度 2 的后继行把 `A 1` 前缀放进底, 底的地板含指数尾巴的地板). `topO-type`: $\psi_0(\Omega_{\Omega+1})$ 的标签等价于它的一切基本列项 $\psi_0(\psi_\Omega^{\,n+1}(0)\ldots)$ = `ψᵀ (Ψ^(n+1) ∅ᵀ)` 的标签 (TopDown 的 `TOᵀ` 是这些项的极限); 每个 $n$ 要深度 $n$ 的 `goodΩ̂`, 所以 `topO` 要对深度归纳的 `GAᵈᴬ` 与 `goodΩ̂ d`.

```agda
record GRᴬ {φ} (R : Run φ) (u : T) : Set where
  constructor grᴬ
  field
    gWᴬ : LW R u
    g0ᴬ : L0 R u
    gRᴬ : R ≈ᴬ R

GA0ᴬ : ∀ {fl} → Run fl → T → Set
GA0ᴬ {fl} P π = FlrLab fl π × GRᴬ P π

∅ᴿ-good : GA0ᴬ ∅ᴿ []
∅ᴿ-good = FlrLab-fz , grᴬ (gW (proj₂ good∅ᴿ)) (g0 (proj₂ good∅ᴿ)) ∅ᴿ-ᴬ

record GA1ᴬ {φ} (E : A 1 φ) (ζ : T) : Set where
  field
    fl1ᴬ : FlrLab φ ζ
    gw1ᴬ : ∀ {c fl} {P : Run fl} {π} → FlrLab[ c ] fl π → LW P π → LW[ c ] (E P) (π ++ ψΩᵗ ζ)
    g01ᴬ : ∀ {fl} {P : Run fl} {π} → GA0ᴬ P π → L0 (E P) (π ++ ψΩᵗ ζ)
    gr1ᴬ : E ≈₁ᴬ E

Branch : (η : Ordᴵ) → A 1 (fk zero ⊔ fk η)
Branch η = fold 1 (fk η) (λ e q → e (suc q)) (Ω̂A 0) (Ωˢ η)

record BranchΩᴬ : Set where
  field
    bW₀ : ∀ θ Y (hY : HS Y) → Lab Y θ → NF₁ θ → ∀ {fl} {P : Run fl} {π} → FlrLab[ toLevel Y hY ] fl π → LW P π →
          LW[ toLevel Y hY ] (Branch (toLevel Y hY) P) (π ++ ψΩᵗ (Ωt θ))
    bV₀ : ∀ θ Y (hY : HS Y) → Lab Y θ → NF₁ θ → ∀ {fl} {P : Run fl} {π} → GA0ᴬ P π →
          L0 (Branch (toLevel Y hY) P) (π ++ ψΩᵗ (Ωt θ))

bR-free : ∀ {η η′} → η ≅ᴵ η′ → Branch η ≈₁ᴬ Branch η′
bR-free = bRᴬ

TΩ2-target : Set
TΩ2-target = BranchΩᴬ → ∀ {ℓ} (ev : Ev ℓ (fz ⊔ (fk zero ⊔ (fk zero ⊔ fz)))) (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (Ψ (Ψ ∅ᵀ)) ev z) tΩ2

module Outlook (Hon : ∀ {k} → Ordˢ k → T → Set) where
  FullTlᴬ : Set
  FullTlᴬ = ∀ {flE} {E : A 1 flE} {ζ} → GA1ᴬ E ζ → ∀ {k} {t : Ordˢ k} {y} → LabL t y → t ≅ᴬ t → Hon t y →
            GA1ᴬ (fold 1 (flo k) (cvFlo k) E t) (ζ ++ y)

infix 4 _≈₂ᴬ_
_≈₂ᴬ_ : ∀ {φ ψ} → A 2 φ → A 2 ψ → Set
E ≈₂ᴬ E′ = ∀ {fl fl′} {F : A 1 fl} {F′ : A 1 fl′} → fl ∼ᶠ fl′ → F ≈₁ᴬ F′ → E F ≈₁ᴬ E′ F′

record GA2ᴬ {φ} (E : A 2 φ) (ζ : T) : Set where
  field
    fl2ᴬ : FlrLab φ ζ
    gv2ᴬ : ∀ {fl} {F : A 1 fl} {ζ′} → GA1ᴬ F ζ′ → GA1ᴬ (E F) (ζ′ ++ ψΩᵗ ζ)
    gr2ᴬ : E ≈₂ᴬ E

goodΩ̂₂-type : Set
goodΩ̂₂-type = GA2ᴬ (Ω̂A 1) []

Ψⁿ : ℕ → Σ Flr Sym
Ψⁿ zero    = fz , ∅ᵀ
Ψⁿ (suc n) = fk zero ⊔ proj₁ (Ψⁿ n) , Ψ (proj₂ (Ψⁿ n))

topO-type : Set
topO-type = ∀ n {ℓ} (ev : Ev ℓ (fz ⊔ proj₁ (Ψⁿ (suc n)))) (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (proj₂ (Ψⁿ (suc n))) ev z) (E.fsn tO (suc n))
```
## §6 结论与边界

**`BranchΩ`.** 未能解除, 并且被否定: `¬BranchΩ : BranchΩ (Ω̂A 0) [] → ⊥` (编译). 精确失败点: $\eta=3$, 目标 0, 分支 $\psi_0(\psi_\Omega(\Omega_3))$ 的 `gi` 行 (节点层 2) 的**折叠**情形, 链点 $c_1$ (目标 2 上算出) 里底在目标 2 处的输出; fs 路径 `[1,0,0,1,0,0,1,2]`; 那一行是底输出的后继行的第 2 份副本里 `Ω̂A 0` 的弹栈, 界 $2$ 对 $1$. 缺的引理: **底的层对齐** (不是目标相对化). 其层对齐形式 `bRᴬ` 是定理.

**`TΩ2-label`.** 未得 (没有名为 `TΩ2-label` 的定理). 能说的最强的: `TΩ2-target` 的类型是修正后的条件定理的类型, 它的前提 `BranchΩᴬ` 只含标签部分; 互模拟部分是定理.

**对比表 (本文与 RelativeBase 合起来).**

| | 目标无关 (Uniform2) | 依目标 (RelativeBase) | 层对齐 (本文) |
|---|---|---|---|
| 尾巴关系 | $\cong^\mathsf s$ + `AlignD` | $\cong^\mathsf s$ + `AlignT c` | $\cong^\mathsf A$ (无附加前提) |
| 底的关系 | $\approx^\mathsf R$ (一切目标) | $\approx_{[c]}$ (目标 $\succeq c$) | $\approx^\mathsf A$ (一切目标) |
| 深度 1 折叠 | `fold-≅1` (要 `AlignD`) | `fold-≅1ᵗ` (要 `AlignT c`) | `fold-≅1ᴬ` |
| $\cong^\mathsf s\Rightarrow$ | 第 0、1 层 (`lowA`) | 层号 $\sqsubseteq c+1$ (`alignHigh`) | 不蕴含 (`¬x₃y₃`); 反向在第 0 层 (`≅ᴬ→≅ˢ₀`) |
| `bR` | 假设, 假 (`¬BranchΩ`) | 目标 $\succeq\eta-2$ (`bRᵗ`) | 一切目标 (`bRᴬ`) |
| $\eta=3$ 的 `gi` 行 | `¬AlignΩ₃` | $c=1$ 成立, $c=0$ 否 | 伪输入对不在关系内 |
| 地板见证 | `FlrLab` (一切项) | `FlrLab[ c ]` (只 $\succ c$) | 同依目标 |

**字面与模 $\cong$.** 字面 (`refl`): `bndL`/`bndR` (两棵树在路径末端的界), RelativeBase `up-self-bound`. 其余: 对一切环境与证据的定理或否定. 标签 (`Lab`) 本身是模 $\cong$ 的, 本文没有新标签.

**边界.** 本文没有证明任何新的序数标签. 新增的定理是互模拟层面的 (`bRᵗ`, `bRᴬ`, `fold-≅1ᵗ`, `fold-≅1ᴬ`) 与地板见证层面的 (`cloWᵗ`, `goodΩ̂0Wᵗ`); 新增的否定是 `¬BranchΩ` (Uniform2 的条件定理为空)、`¬GA1-Ω₃` (第 3 层分支帧无 Uniform2 意义的好帧)、`¬AlignΩ₃⁰`、`¬FL₄`、`¬FLω`、`¬x₃y₃`、`¬PLᴬPR`. 不改 `src/`、`archive/` 与任何已有文件.

**工程注记.**

1. `R-flipᴬ r r′ d = ≅→Rᴬ r′ (≅ᴬ-sym (R→≅ᴬ r d))` (经转换函数) 停机检查失败:

        error: [TerminationIssue]
        Termination checking failed for the following functions:
          ≅ᴬ-sym, R-flipᴬ
        Problematic calls:
          R-flipᴬ (<→◃ q) (<→◃ p) d
          ≅ᴬ-sym (R→≅ᴬ r d)

   改为 UniformS 的写法: `R-flipᴬ` 对第一个 `◃` 证明递归、`flipRᴬ` 对第二个递归, 在 `zero`/`self n` 处直接调用 `≅ᴬ-sym` (那里 `Rᴬ` 定义性地就是 `Eqᴬ`).
2. `Restrˢ` 的字段 (`repˢ`/`backˢ`/`ltˢ`/`eqˢ`) 不能从 Prefix 的 `using` 列表导入 (`-W[no]ModuleDoesntExport`, 随后 `[NotInScope] repˢ`), 要 `open Restrˢ using (…)`.
3. §1 的路径是用交互式 `Cmd_compute_toplevel` 逐步计值 `kind (walkˢ TL …)` 找到的; 整条路径的 `bndOf` 在类型检查时定义性地归约 (`bndL`/`bndR` 是 `refl`), `¬bR` 里 `no21` 的参数类型由归约得到, 编译时间与 Uniform2 §5 的检验同量级.
