# CRw 上底做成递归, 否定一路 (三): 对构造一路折叠与实例的检查

> 不含记号. 入口 [NegRecB](NegRecB.lagda.md). 只读导入构造一路的 [RecBIf](RecBIf.lagda.md), [RecBFold](RecBFold.lagda.md), [RecBPath](RecBPath.lagda.md), [RecB](RecB.lagda.md) 与它们导入的 `CRw*`, 以及 NegCRw 的 [NegCRwInst](NegCRwInst.lagda.md) (都不改). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **主审续派的五件事, 结果.**
>
> 1. **一个定义覆盖一切 $n$ (正面, 定理).** 底 `Sb (suc n)` 字面就是 `XSof (Sb n)` (`Sb-step`, 对一切 $n$, refl). 跨底折叠 `ΦX n` 是一个对 $n$ 参数化的函数, 只在指标种类的决定 `dcI` 上分 $n=0$ 与 $n\geq1$ 两种: $n\geq1$ 时一律留, 嵌成第 $n$ 个底的指标种类, 坐标原样 (`dcI-suc`, `frE-ιK`, 对一切 $n$, refl); $n=0$ 时与目标比较. 下降 `desc` 对 $n$ 递归. 所以不是逐站拼接. **但**底的下标是 $\mathbb N$, 不是层号 `LH` (构造一路自述; 本路读类型确认): 这不是作者原话 "让底对层号 LH 递归".
> 2. **读法是否高于 `TU2` (形状定理; 读法本身仍是判断).** **`root-keep`** (对一切 $n$, 一切世界与分支): 从第 $n+2$ 个底往第 $n+1$ 个底的跨底折叠, 把根上的指标结点原样留成指标结点 (分支仍是跨底折叠). **`root-collapse₀`**: 第 1 个底往第 0 个底时, 指标结点 (世界 $1$) 被坍缩成 ℕ-极限. 所以 `TN (n+1) m` 的下降, 在到第 0 个底之前, 每过一个底都留下一层指标结点; `TD 0` (与 CRw 的 `TU2` 在深度 4 有界展开相同, `RecBCmp`) 的下降只有最后这一步. 这是 "多一层" 的形状事实, 不是读法的定理. **有限测试** (`RecBCmp` 已有): 深度 4, 5 的结点数分不开 `TD 0` 与 `TD 1`; 本路没有找到能在 6G 内分开它们的测试, 没有做.
> 3. **证书 (定理).** `LgB-Tω` 的类型就是 `CRwBase.LgB Tω`, 标准 `LgB` (`cert-std`, 读类型). 中间层: **`kept-not-LgB₁`**: 第 1 个底上第 1 层里合法的输入 (`Lg-inΩ`) 经同底折叠 `ΦS` 折到第 0 层, 留下指标结点, 输出**不满足 `LgB`**. **`ΦS-acc`**, **`ΦX-acc`** (对一切 $n$, 一切底与目标): 两个折叠都不保第一位置 ($1\lhd\lim(0,1,1,\dots)$, 像不是). 同 CRw (`NegCRwInst.Φ-acc-sm`, `Φ-acc-cx`, `kept-not-LgB-X`).
> 4. **决定 (定理).** **`ok-dcxR`**: 分量里的新种类按 `pick` 的读法正确 (对一切底, 一切 `B`); 底种类一行是 $\top$ (盲, 一律留). **`ok-dcI₀`**: 第 0 个底上指标种类的决定正确. **`dcI-suc-not-local`**: $n\geq1$ 时指标种类一律留, CRw 的局部判据 `OkAt` (要 $j+1\lhd t$, 这里 $j=0$) 在目标 $t=0$ 时**不成立**; 留是否正确要看层号 $(n,t)$ 读 $\Omega\cdot n+t\geq\Omega$ 之上 (判断: 正确), 局部判据不适用.
> 5. **"每个底必须有自己的 $\Omega_1$ 指标种类, 否则跨底路径搬运方向相反" (否定定理).** **`liftM`**: 把 `RecBPath.lift` 里指标分量上的平凡结构 `triv` 换成**也移动下层世界**的结构 `PSι` (可入 $W\lhd e$ 且 $e$ 合法, 进入后 $e+1$, 同 `I₁` 的 `Adm₀`/`nxt₀`): 即 "移动上层世界的种类同时在下层结构里不平凡". **`ΦX↓M-fails`**: 对 $Q=$ `PSX 0` ($n=0$, 满足 `Down` 的两个前提, `ok-Q₀`), `PH-ΦX↓` 把 `lift` 换成 `liftM` 后的陈述**不成立**. 反例 (`hM`, 世界 $W=1$): 输入在世界 $1$ 里带 `liftM` 路径 (`in-M`) 与跨底折叠自己的路径 (`nd-M`), 下层地板带路径; 输出的指标结点在坐标 $1$ 处进入下层世界 $2$, 但那一支是输入在回灌后的坐标 $1\boxplus\mathrm{leg}\,1=2$ 处的分支, 它的种类要 $3\lhd2$ (`out-fails`). 方向: 输出要的世界是 $c+1$, 输入给的是 $(B\boxplus\mathrm{leg}\,c)+1$, 更大, 而路径只能往大搬 (`PH-mono`). 对照: 同一输入在 RecB 的 `lift` 下**不**带路径 (`no-lift`), 所以与 `PH-ΦX↓` 不矛盾.
>
> **前提实例.** 2: 世界 $1$ 与证据写出. 3: `Lg-inΩ` (输入合法), `lg-w₁` (世界合法), `Lg-fI`, `one⊲fI`. 5: `ok-Q₀` (`Down` 的两个前提对 `PSX 0` 成立), `in-M`, `nd-M`, `fl-Q₀` (结论的三个前提都成立).
>
> **只否定什么.** 3: 只否定中间输出满足 `LgB` 与折叠保第一位置; **不否定** `LgB-Tω` (它对). 4: `dcI-suc-not-local` 只说 CRw 的局部判据不适用于 $n\geq1$ 的指标种类, 不说决定错. 5: 只否定 "指标分量在下层结构里按 `PSι` (同 `I₁` 的规则) 移动下层世界" 时 `PH-ΦX↓` 的结论; **不否定** RecB 的 `lift` (指标分量平凡) 与 `PH-ΦX↓` (都对), 也不否定别的下层移动规则 (例如不动世界的 `stayOf` 式规则, 那就是 `triv` 的情形). 1, 2 是正面与形状定理, 不否定任何东西. 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegRecBInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.RecBIf
open import OCF.Lean.CRw using (I₁)
open import OCF.Lean.RecB using (J₁; PH-fl; Tω; LgB-Tω)
open import OCF.Lean.CRwFold I₁ using (Tw; PS; module PS; PH; Dc; keep; same; above; Cl; bas; nw; cl; pick; mul; Σ⁺; emb; frE)
open import OCF.Lean.CRwPath I₁ using (psSup)
open import OCF.Lean.RecBFold J₁
open import OCF.Lean.RecBPath J₁ using (PSL; lift; triv; FQ)
open import OCF.Lean.NegCRwInst using (module AccNMᶜ; fI; Lg-fI; one⊲fI; num; module ForI)
open ForI I₁ using (OkAt; ok-pick; OkCl; wT; lgT)
```

## §1 一个定义覆盖一切 $n$

```agda
Sb-step : ∀ n → Sb (suc n) ≡ XSof (Sb n)
Sb-step n = refl

dcI-suc : ∀ n {B t} (lB : LgB B) (pt : t ⊲ B) (o : hs hz ⊲ B) →
  dcI (suc n) lB pt o ≡ keep (emb {S = Sb (suc n)} t (ιK {Sb n})) (frE {S = Sb (suc n)} t (ιK {Sb n}))
dcI-suc n lB pt o = refl

-- 留下的指标种类的坐标原样 (都是 Cd)
frE-ιK : ∀ n (c : Cd) → frE {S = Sb (suc n)} hz (ιK {Sb n}) c ≡ c
frE-ιK n c = refl
```

## §2 形状: 跨底折叠在 $n\geq1$ 留指标结点, 在 $n=0$ 坍缩

```agda
data IsNode {S : KS} (κ : K S) : HB S → Set where
  node : ∀ {g} → IsNode κ (hΩ κ g)

data IsLim {S : KS} : HB S → Set where
  lim : ∀ {f} → IsLim (hl f)

root-keep : ∀ n B lB pt b (g : Cd → HB (Sb (suc (suc n)))) o pg →
  IsNode (ιK {Sb n}) (ΦX (suc n) hz B lB pt b (hΩ (ιK {Sb (suc n)}) g) (o , pg))
root-keep n B lB pt b g o pg = node

W₁ : Cd
W₁ = hs hz

root-collapse₀ : ∀ b (g : Cd → HB (Sb 1)) pg →
  IsLim (ΦX 0 hz W₁ tt (z⊲ᴮ W₁) b (hΩ (ιK {S⊥}) g) (hself , pg))
root-collapse₀ b g pg = lim
```

## §3 证书与中间层

`cert-std`: 证书的类型就是 `CRwBase.LgB` (读类型).

```agda
cert-std : LgB Tω
cert-std = LgB-Tω

mulC : ∀ {S : KS} n → mul {S} (hs hz) n ≡ num (suc n)
mulC zero = refl
mulC (suc n) = cong hs (mulC n)

ΦS-acc : ∀ S fb m a lm t (pt : t ⊲ m) b {w : Wd (Tw S t)} →
  ¬ (ΦS S fb m a lm t pt b (hs hz) ⊲[ w ] ΦS S fb m a lm t pt b (hl fI))
ΦS-acc S fb m a lm t pt b =
  AccNMᶜ.acc-not-mono _ _ _ (mul (hs hz)) (Σ⁺ (λ n → ΦS S fb m a lm t pt b (fI n)))
    refl refl mulC refl refl (λ n → refl)

phI : ∀ n B k → PH (PSX n) B (fI k)
phI n B zero = tt
phI n B (suc k) = tt

ΦX-acc : ∀ n t B lB (pt : t ⊲ B) b {w : Wd (Tw (Sb n) t)} →
  ¬ (ΦX n t B lB pt b (hs hz) tt ⊲[ w ] ΦX n t B lB pt b (hl fI) (phI n B))
ΦX-acc n t B lB pt b =
  AccNMᶜ.acc-not-mono _ _ _ (mul (hs hz)) (Σ⁺ (λ k → ΦX n t B lB pt b (fI k) (phI n B k)))
    refl refl mulC refl refl (λ k → refl)
```

**中间层不合法.** 第 1 个底 (`Sb 1`) 上第 1 层 (`step (Sb 1)`) 里, 底种类 (指标种类) 的结点, 分支在坐标 $c$ 处是 $c$ 自己. 合法. 同底折叠到第 0 层: 留下指标结点, 分支 $c\mapsto\Phi(\mathrm{lift}\,c)$, 在 $1\lhd\lim(0,1,1,\dots)$ 处不单调.

```agda
S₁ : KS
S₁ = Sb 1

liftC : Cd → HB (step S₁)
liftC hz = hz
liftC (hs c) = hs (liftC c)
liftC (hl f) = hl (λ n → liftC (f n))
liftC (hΩ () _)

liftC-⊲ : ∀ {c c′ : Cd} {w} → c ⊲ c′ → liftC c ⊲[ w ] liftC c′
liftC-⊲ hself = hself
liftC-⊲ (hsuc p) = hsuc (liftC-⊲ p)
liftC-⊲ (hlim n p) = hlim n (liftC-⊲ p)
liftC-⊲ (hLim {κ = ()} _ _)

Lg-liftC : ∀ c → LgB c → LgB (liftC c)
Lg-liftC hz l = tt
Lg-liftC (hs c) l = Lg-liftC c l
Lg-liftC (hl f) (st , l) = (λ n → liftC-⊲ (st {tt} n)) , (λ n → Lg-liftC (f n) (l n))
Lg-liftC (hΩ () _) l

inΩ : HB (Tw S₁ (hs hz))
inΩ = hΩ (inj₁ (ιK {S⊥})) liftC

Lg-inΩ : LgB inΩ
Lg-inΩ = (λ lw e e′ p → liftC-⊲ p) , (λ {w} {c} lw e → Lg-liftC c (lgB⊲ e tt (proj₂ (proj₁ lw ix))))

outΩ : HB S₁ → HB S₁
outΩ b = ΦS S₁ (fl 1) (hs hz) (wfC (hs hz)) tt hz (z⊲ᴮ (hs hz)) b inΩ

outΩ-kept : ∀ b → outΩ b ≡ hΩ (ιK {S⊥}) (λ c → ΦS S₁ (fl 1) (hs hz) (wfC (hs hz)) tt hz (z⊲ᴮ (hs hz)) b (liftC c))
outΩ-kept b = refl

-- 合法的世界: 指标分量的界是 lim(0,1,1,…)
w₁ : Wd S₁
w₁ ix = tt , hl fI
w₁ (cp c) = wT (hs c)

lg-w₁ : LgW S₁ w₁
lg-w₁ ix = tt , Lg-fI
lg-w₁ (cp c) = lgT (hs c)

kept-not-LgB₁ : ∀ b → ¬ LgB (outΩ b)
kept-not-LgB₁ b (mo , _) =
  AccNMᶜ.acc-not-mono _ _ _ (mul (hs hz))
    (Σ⁺ (λ n → ΦS S₁ (fl 1) (hs hz) (wfC (hs hz)) tt hz (z⊲ᴮ (hs hz)) b (liftC (fI n))))
    refl refl mulC refl refl (λ n → refl)
    (mo {w = w₁} {c = hs hz} {c′ = hl fI} lg-w₁ one⊲fI hself one⊲fI)
```

## §4 决定

```agda
ok-dcxR : ∀ {S B t c} {κ : K (Tw S (hs c))} (lB : LgB B) (pt : t ⊲ B) (ev : hs c ⊲ B) (k : Cl {S} (hs c) κ) →
          OkCl {S} {hs c} {B} k (dcx lB pt ev k)
ok-dcxR lB pt ev (bas κ₀ to) = tt
ok-dcxR {S} lB pt ev (nw j pj to) = ok-pick S to (⊲ᴮ-tr pj ev) (cmpB (⊲ᴮ-tr pj ev) pt tt lB)

ok-dcI₀ : ∀ {B t} (lB : LgB B) (pt : t ⊲ B) (o : hs hz ⊲ B) → OkAt {Tw S⊥} {B} {t} hz (dcI zero lB pt o)
ok-dcI₀ lB pt o = ok-pick S⊥ (λ c → c) o (cmpB o pt tt lB)

dcI-suc-not-local : ∀ n → ¬ OkAt {Tw (Sb (suc n))} {W₁} {hz} hz (dcI (suc n) {W₁} {hz} tt (z⊲ᴮ W₁) hself)
dcI-suc-not-local n ()
```

## §5 指标分量在下层也移动世界: `PH-ΦX↓` 不成立

`PSι`: `step S⊥` (指标分量) 上移动世界的结构, 规则同 `I₁` (可入 $W\lhd e$ 且 $e$ 合法, 进入后 $e+1$). `liftM Q`: 与 `RecBPath.lift` 只差指标分量 (`triv` 换成 `PSι`).

```agda
PSι : PS (step S⊥)
PSι = record { Ev = Ev′ ; Ad = Ad′ ; nx = nx′ ; ev↑ = λ q {κ} e → ev↑′ q κ e ; ad↓ = λ q {κ} {e} a → ad↓′ q κ e a ; nx↑ = λ {B} {κ} {e} a → nx↑′ B κ e a }
  where
  Ev′ : Cd → K (step S⊥) → Set
  Ev′ W (inj₁ ())
  Ev′ W (inj₂ _) = ⊤
  Ad′ : Cd → (κ : K (step S⊥)) → E (step S⊥) κ → Set
  Ad′ W (inj₁ ()) e
  Ad′ W (inj₂ _) e = (W ⊲ e) × LgB e
  nx′ : (W : Cd) (κ : K (step S⊥)) (e : E (step S⊥) κ) → Ad′ W κ e → Cd
  nx′ W (inj₁ ()) e a
  nx′ W (inj₂ _) e a = hs e
  ev↑′ : ∀ {B B′} → B ⊲ B′ → ∀ κ → Ev′ B κ → Ev′ B′ κ
  ev↑′ q (inj₁ ()) e
  ev↑′ q (inj₂ _) e = tt
  ad↓′ : ∀ {B B′} → B ⊲ B′ → ∀ κ e (a′ : Ad′ B′ κ e) → Σ (Ad′ B κ e) (λ a → nx′ B κ e a ⊲ nx′ B′ κ e a′)
  ad↓′ q (inj₁ ()) e a′
  ad↓′ q (inj₂ _) e (w , l) = (⊲ᴮ-tr q w , l) , hself
  nx↑′ : ∀ B κ e (a : Ad′ B κ e) → B ⊲ nx′ B κ e a
  nx↑′ B (inj₁ ()) e a
  nx↑′ B (inj₂ _) e (w , l) = ⊲ᴮ-tr w (hsuc hself)

FQM : ∀ {S} → PS S → (i : Ix) → PS (FX S i)
FQM Q ix = PSι
FQM Q (cp c) = PSL Q (hs c)

liftM : ∀ {S} → PS S → PS (XSof S)
liftM {S} Q = psSup {Ix} {FX S} (FQM Q)
```

**反例.** $Q_0=$ `PSX 0` (第 1 个底自己的结构). 输入 $h$ 是第 2 个底的指标结点, 分支 $e\mapsto$ 第 0 个分量里, 第 1 个底的种类 $(e, \Omega_{e+1})$ 的结点 (分支都是 $0$). 这个种类在 $Q_0$ 里的证据是 $e+1\lhd W$.

```agda
Q₀ : PS S₁
Q₀ = PSX 0

yE : (e : Cd) → HB (Tw S⊥ (hs e))
yE e = hΩ (inj₂ tt) (λ _ → hz)

xE : Cd → HB S₁
xE e = ι {Ix} {FX S⊥} (cp e) (yE e)

gM : Cd → HB (Sb 2)
gM e = ι {Ix} {FX S₁} (cp hz) (up (xE e))

hM : HB (Sb 2)
hM = hΩ (ιK {S₁}) gM

-- 跨底折叠自己的路径 (世界 1)
nd-M : PH (PSX 1) W₁ hM
nd-M = hself , λ e a → hsuc (proj₁ a) , λ _ _ → tt

-- 输入在世界 1 里带 liftM 路径: 分支 e 进入下层世界 e+1, 证据 e+1 ⊲ e+1
in-M : PH (liftM Q₀) W₁ hM
in-M = tt , λ e a → hself , λ _ _ → tt

-- 下层地板带路径; Down 的两个前提对 Q₀ 成立
fl-Q₀ : PH (PSL Q₀ hz) W₁ (fl 1)
fl-Q₀ = PH-fl 0 W₁ hself

ok-Q₀ : (∀ W → hs hz ⊲ W → PS.Ev Q₀ W (ιK {S⊥})) × (∀ B → hs hz ⊲ B → PH Q₀ B (fl 1))
ok-Q₀ = (λ W o → o) , PH-fl 0

three two : Cd
two = hs (hs hz)
three = hs two

no32 : ¬ (three ⊲ two)
no32 (hsuc (hsuc ()))

outM : HB S₁
outM = ΦX 1 hz W₁ tt (z⊲ᴮ W₁) (fl 1) hM nd-M

-- 输出的指标结点在坐标 1 处 (可入: 1 ⊲ 1) 进入世界 2; 那一支是输入在 1 ⊞ leg 1 = 2 处的分支, 证据要 3 ⊲ 2
out-fails : ¬ PH (PSL Q₀ hz) W₁ outM
out-fails p = no32 (proj₁ (proj₂ p (hs hz) (hself , tt)))

ΦX↓M-fails : ¬ (∀ t B lB pt b h nd W → hs hz ⊲ W → PH (PSL Q₀ t) W b → PH (liftM Q₀) W h →
                 PH (PSL Q₀ t) W (ΦX 1 t B lB pt b h nd))
ΦX↓M-fails all = out-fails (all hz W₁ tt (z⊲ᴮ W₁) (fl 1) hM nd-M W₁ hself fl-Q₀ in-M)

-- 对照: 同一输入在 RecB 的 lift (指标分量平凡) 下不带路径, 与 PH-ΦX↓ 不矛盾
no21 : ¬ (two ⊲ W₁)
no21 (hsuc ())

no-lift : ¬ PH (lift Q₀) W₁ hM
no-lift p = no21 (proj₁ (proj₂ p (hs hz) tt))
```

## 结论 (按档)

- **[定理, 正面]** `Sb-step`, `dcI-suc`, `frE-ιK` (一个定义覆盖一切 $n$); `ok-dcxR`, `ok-dcI₀` (决定正确; 底种类一行盲); `cert-std` (证书是标准 `LgB`).
- **[定理, 形状]** `root-keep` (对一切 $n$), `root-collapse₀`.
- **[定理, 否定]** `ΦS-acc`, `ΦX-acc` (不保第一位置); **`kept-not-LgB₁`** (中间层不合法); `dcI-suc-not-local` (局部判据不适用); **`ΦX↓M-fails`** (指标分量在下层也移动世界时 `PH-ΦX↓` 不成立), 反例 `out-fails`, 前提 `in-M`, `nd-M`, `fl-Q₀`, `ok-Q₀`; 对照 `no-lift`.
- **[判断]** 读法 (`TD 1` ψ₀(Ω_{Ω·3}), `Tω` ψ₀(Ω_{Ω·ω})) 没有定理; `root-keep` 只说每过一个底留一层指标结点. $n\geq1$ 时 "留" 正确是按层号 $\Omega\cdot n+t$ 的判断.
