# 第三种组织, 否定一路 (一): 接口之前 (内层指标, 留下带回灌, 写回, 分类, 对角)

> 不含记号. 入口 [NegThird](NegThird.lagda.md). 本篇**不依赖**构造一路 Third 的接口 (接口定稿之前写的部分). 只读导入 [CRwBase](CRwBase.lagda.md), `LHRec*`, `CRwFold`/`CRwPath` (路径记录 `PS`, `PH`), [NegRecBPre](NegRecBPre.lagda.md) (都不改). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP. 函数外延只在 `upd→WLPO` 作前提 (`FE`, 只对 $\mathbb N\to$ `Cd`), 那条结论标 "条件".
>
> **问题** (作者本轮选定 "攻: LHRec 的第三种组织"). `LHRec` §4 的设计: 底对 $n$ 递归, $x_0=0$, $x_{n+1}=$ `lΩ xₙ (c ↦ xₙ ⊕L ls (upL xₙ c))` (`xb`, `cH`), 分量共享低层世界 $w$, 内层指标 "在上层路径里移动 $w$ 的那一部分, 在下层路径里平凡, 折叠时总是留, 嵌成底种类", 并判断: 留下后两个作用不在同一个世界里, 所以 `ΦX↓M-fails` 的方向问题不出现.
>
> **注.** 本篇写在 `LHRec` §4 的设计上 (层号 `LH`, 内层指标种类). 构造一路的接口 `ThirdIf` 改用塔 `Tw`, 没有内层指标种类; 它的闭项里指标分量的旧种类不留 (`NegThirdInst.G.old-pk`), 所以 §3, §4 的 `Keep.Kp` 前提在它的闭项路径上不成立: 这两节说明的是**为什么要绕开**, 不是对它的闭项的否定.
>
> **对象 (都是 `refl` 算出来的).** $X_1=x_1$; `th₁` 是 `flL X₁` 的分支 (第 $d$ 项之前的分量地板的和); $Y=X_1\oplus$ `upL X₁ (flL X₁)` 就是分量高度 `flL X₁` 下的层号 (`Y≡`), 地板 `flL Y` 的根是内层指标 (`flY≡`). **`rootY`** (对变量 $d$): `θY (d+2)` 的根种类是 `κY d` $=$ (内层分量 $d+1$, 它的指标), 它来自 $X_1$ 的底种类 (分量 $d$, 新种类) (`thRoot`). 所以真实的地板里, 内层指标的第 $d+2$ 个分支含一个结点, 留下后是底种类 (分量 $d$), 下层的证据是 $d+1\lhd W$ (这是 RecB 的 `ev`, `dcx` 拿它做公共上界的那个证据; `Sound` 只要求这一条).
>
> **结果.**
>
> 1. **内层指标在下层路径里不能平凡 (§3).** **`floor-forces`**: 任一路径结构 `P`, 若内层种类的 `Ev` 推出 $d+1\lhd W$, 且真实地板在 $W$ 里带路径, 则内层指标在坐标 $d+2$ 处的新世界必须 $\rhd d+1$. 推论 **`floor-no-stay`**: 不动世界的 `P` 不带路径. 三种情形: **`case-triv`** (全平凡: 地板带路径, 但留下的结点没有下层证据), **`case-stay`** (`Ev` 抄自下层, 不动世界: 地板不带路径), **`case-move`** (`Ev` 抄自下层, 按下层规则移动: 对一切 $W$ 带路径, 正面). 这回答 `NegLHRecInst` 留下的判断 (b): 第三种组织里, 留下的内层指标在下层路径里**不平凡**. RecB 的 `no-lift` 对照: RecB 的真实地板带 `lift` 路径, 这里不带, 差别在分量高度含 $\Omega$-结点.
> 2. **留下带回灌, 方向问题还在, 而且与下层规则无关 (§4).** **`keep-req`**: 留下的结点在坐标 $y$ 处的分支是 $\Phi(g(\mathrm{sh}\,B\,y))$, 且那一支的根留下时, 下层新世界必须 $\rhd$ 回灌后的坐标减一. **`real-keep-fails`**: 标准规则 `Q₁`, 世界对 (上层 $3$, 下层 $2$) (从 $(1,1)$ 过坐标 $1$ 到达: `reachB`, `reachV`), 坐标 $2$: 要 $4\lhd3$. **`init-keep-fails`**: 标准规则在初始世界对 $(1,1)$, 坐标 $\omega+2$ 就失败. **`no-lower-rule`** (核心): **任何**下层路径结构 `Q` (`Sound`, 新世界合法, 记录 `PS` 自带的单调 `ad↓`) 都不能同时让世界对 $(1,1)$ 与 $(3,V_2)$ ($1\lhd V_2$; 含 $V_2=3$, 即上下层世界相等的不变量) 带路径: 回灌后的 $(1\boxplus\omega')+1$ 与 $(3\boxplus\omega')+1$ 都要在同一棵合法树的第一位置里 (`ad↓`), 而它们不可比 (`inc`, 即 `NegNoAccX.⊞-not-monoˡ` 的形状). 所以 `LHRec` §4 的判断 "不是同一个世界, 方向问题不出现" 在这个形状下**不成立**.
> 3. **`Φ`-无关.** 2 里的折叠是任意函数 `Φ`, 只要求 "这一支的根留下成底种类" (`Keep.Kp`, 设计的 "总是留"); 回灌是 `J₁` 的 $B\boxplus\mathrm{leg}\,y$ (接口定稿后对接口重写).
> 4. **写回 (§5, 条件).** 内层结点的种类在 $x_n$ 的分量 $c_0$ 里时 (`thRoot`: 真实地板有这种结点), 走进内层分量要移动世界 $w$ 在 $c_0$ 处的值 (`bdK`: 界读 `wlK`). **`WB.weak-eq`** (无条件): 精确写回 (`Upd`: $c_0$ 处换新值, 字面不等于 $c_0$ 的下标处不动) 给出分量下标的弱判等 $\neg\neg(c=c_0)\lor\neg(c=c_0)$. **`upd→WLPO`** (条件: `FE`): 推出 WLPO.
> 5. **"分量在界内" 不能判定 (§6).** **`bd-dec→LPO`**: 对一切合法的界判定 $1\lhd B$ 就是 LPO. 所以塔的种类分类不能先判 "这个分量在不在世界里", 证据必须来自路径.
> 6. **分类良定义, 搬运不是 `refl` 但不是墙 (§7, 正面).** **`clT`**: 塔的一切种类按 (底 / 塔 / 内层指标 / 内层旧种类) 分类, 对层号递归, 变量 $x$ 上不用搬运. **`node-form`**, **`lvl-E`**, **`toE`**, **`wlK`**, **`bdK`**: 变量层号上结点是 `lΩ (lvl k κ)`, 坐标类型与界都对上, 都是对 $k$ 归纳, 每个归纳步 `refl`. [有限测试] 变量 $n$ 上 `node (xb n) κ h` 不是 `lΩ` 头, 直接 `refl` 编译失败 (scratch `T1.agda`, 退出码 42, `UnequalTerms`), 所以要 `node-form`. **`upL-collide`**: `upL` 不单射 (同 `lvl` 的两个种类), 所以 "留成哪个底种类" 要读值 $c$, 不能读层号.
> 7. **对角到 $\Lambda$ (§8).** **`xb-naive`**: 各站在 `ll xb` 各自分量里写的对角不合法 (`sup-diag-illegal`); **`xb-acc`**: 累加合法 (`Lg-flL`).
>
> **前提实例.** 1: `case-move` 给出满足 `floor-forces` 前提的 `P`; `case-stay` 的 `PYs` 满足 `floor-no-stay` 的三条前提; `case-triv` 不满足 Ev 前提 (这是它的内容). 2: `Φ-ex`, `kp-ex` (留下的前提); `no-lower-rule` 的前提两两相容: `Qb b` 是 `PS`, `Sound` (`Qb-sound`), 新世界合法 (`lg-ex`), 可入 (`a₂-ex₁`, `a₂-ex₃`), `Φr` 满足留下的前提 (`kpr`), $b=1$ 时第一个世界对带路径 (`p₁-ex`), $b=3$ 时第二个世界对带路径 (`p₃-ex`). 4: `Upd` 的前提 (`FE`) 在函数外延成立的模型里成立; `Upd` 本身是被否定的对象. 5: `Lg-Bα`. 7: `wx`.
>
> **只否定什么.** 1 只否定: 内层指标在下层路径里不动世界而又要真实地板带路径与留下的结点有证据; **不否定**内层指标在下层路径里移动世界 (`case-move` 是正面). 2 只否定: 分支形状 $\Phi(g(\mathrm{sh}\,B\,y))$, 留下的种类的分量序号就是输入的序号, 下层路径记录是 `PS` (世界是一棵可数树, 带 `ad↓`), 回灌是 $B\boxplus\mathrm{leg}\,y$. **不否定**: 留下时把分量序号重新索引; 输出分支不是输入在回灌坐标处的分支; 下层世界不是一棵树 (例如带上层的界); 不要 `ad↓` 的下层路径; 下层折叠不用这个证据做公共上界; 别的回灌. 4 只否定字面的精确写回; **不否定**别处也变的抬升, 不写回的世界 (例如不用 `Wd (Lv xₙ)` 的 Π). 5 只否定判定, 不否定带路径证据的分类. 7 只否定各站各写的对角. 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegThirdPre where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool; true; false; if_then_else_; _∨_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecIf
open import OCF.Lean.LHRecLeg using (J₁; leg; Lg-leg; Σᴸ; module New; rfL; w₀L; lw₀L)
open import OCF.Lean.LHRecLay using (lvl; node; upL; _⊕L_)
open import OCF.Lean.LHRecFl using (flL; ΣF; Lg-flL; gcF; ixK; cxI)
open import OCF.Lean.CRw using (I₁)
open import OCF.Lean.CRwFold I₁ using (PS; module PS; PH)
open import OCF.Lean.CRwPath I₁ using (PH-⊞)
open import OCF.Lean.NegRecBPre using (sup-diag-illegal; here)
open LHRecIf
```

## §1 序列

```agda
cH : (x : LH) → HB (Lv x) → LH
cH x c = x ⊕L ls (upL x c)

xb : ℕ → LH
xb zero = lz
xb (suc n) = lΩ (xb n) (cH (xb n))

X₁ : LH
X₁ = xb 1

gX₁ : Cd → LH
gX₁ = cH lz

th₁ : Cd → HB (Lv X₁)
th₁ = New.θ (cxI lz gX₁) (gcF (λ d → ι {IxL lz} {FXL lz gX₁} (inj₂ d) (flL (gX₁ d))))

Y : LH
Y = X₁ ⊕L upL X₁ (flL X₁)

gY : Cd → LH
gY c = X₁ ⊕L upL X₁ (th₁ c)

Y≡ : Y ≡ lΩ lz gY
Y≡ = refl

θY : Cd → HB (Lv Y)
θY = New.θ (cxI lz gY) (gcF (λ d → ι {IxL lz} {FXL lz gY} (inj₂ d) (flL (gY d))))

flY≡ : flL Y ≡ hΩ ixK θY
flY≡ = refl

data IsNode {S : KS} (κ : K S) : HB S → Set where
  isn : ∀ {g} → IsNode κ (hΩ κ g)

κY : Cd → K (Lv Y)
κY d = inj₂ (hs d) , inj₁ tt , inj₂ tt

rootY : ∀ d → IsNode (κY d) (θY (hs (hs d)))
rootY d = isn
```

## §2 路径结构

```agda
num : ∀ {S} → ℕ → HB S
num zero = hz
num (suc n) = hs (num n)

ixY : K (Lv Y)
ixY = ixK

ixX : K (Lv X₁)
ixX = ixK

-- 平凡
trivP : PS (Lv Y)
trivP = record { Ev = λ _ _ → ⊤ ; Ad = λ _ _ _ → ⊤ ; nx = λ B _ _ _ → B
               ; ev↑ = λ _ _ → tt ; ad↓ = λ q _ → tt , q ; nx↑ = λ _ → hself }

PH-triv : ∀ W h → PH trivP W h
PH-triv W hz = tt
PH-triv W (hs h) = PH-triv W h
PH-triv W (hl f) = λ n → PH-triv W (f n)
PH-triv W (hΩ κ g) = tt , λ e a → PH-triv W (g e)

-- 下层的路径结构 (第 1 个底): 指标种类移动世界, 分量的种类读世界
EvQ : Cd → K (Lv X₁) → Set
EvQ B (inj₁ _ , _) = hs hz ⊲ B
EvQ B (inj₂ c , _) = hs c ⊲ B

AdQ : Cd → (κ : K (Lv X₁)) → E (Lv X₁) κ → Set
AdQ B (inj₁ _ , inj₁ ()) e
AdQ B (inj₁ _ , inj₂ _) e = (B ⊲ e) × LgB e
AdQ B (inj₂ c , κ) e = ⊤

nxQ : (B : Cd) (κ : K (Lv X₁)) (e : E (Lv X₁) κ) → AdQ B κ e → Cd
nxQ B (inj₁ _ , inj₁ ()) e a
nxQ B (inj₁ _ , inj₂ _) e a = hs e
nxQ B (inj₂ c , κ) e a = B

Q₁ : PS (Lv X₁)
Q₁ = record { Ev = EvQ ; Ad = AdQ ; nx = nxQ ; ev↑ = ev↑′ ; ad↓ = ad↓′ ; nx↑ = nx↑′ }
  where
  ev↑′ : ∀ {B B′} → B ⊲ B′ → ∀ {κ} → EvQ B κ → EvQ B′ κ
  ev↑′ q {inj₁ _ , _} ev = ⊲ᴮ-tr ev q
  ev↑′ q {inj₂ _ , _} ev = ⊲ᴮ-tr ev q
  ad↓′ : ∀ {B B′} → B ⊲ B′ → ∀ {κ e} (a′ : AdQ B′ κ e) → Σ (AdQ B κ e) (λ a → nxQ B κ e a ⊲ nxQ B′ κ e a′)
  ad↓′ q {inj₁ _ , inj₁ ()} a′
  ad↓′ q {inj₁ _ , inj₂ _} (w , l) = (⊲ᴮ-tr q w , l) , hself
  ad↓′ q {inj₂ _ , _} a′ = tt , q
  nx↑′ : ∀ {B κ e} (a : AdQ B κ e) → B ⊲ nxQ B κ e a
  nx↑′ {κ = inj₁ _ , inj₁ ()} a
  nx↑′ {κ = inj₁ _ , inj₂ _} (w , l) = ⊲ᴮ-tr w (hsuc hself)
  nx↑′ {κ = inj₂ _ , _} a = hself

Sound : PS (Lv X₁) → Set
Sound Q = ∀ W d κ → PS.Ev Q W (inj₂ d , κ) → hs d ⊲ W

Q₁-sound : Sound Q₁
Q₁-sound W d κ e = e

-- 内层: Ev 抄自下层 (分量 d 读 d ⊲ W), 内层指标按 stay 或 move
EvI : Cd → K (Lv Y) → Set
EvI B (inj₁ _ , _) = ⊤
EvI B (inj₂ d , _) = d ⊲ B

AdM : Cd → (κ : K (Lv Y)) → E (Lv Y) κ → Set
AdM B (inj₁ _ , inj₁ ()) e
AdM B (inj₁ _ , inj₂ _) e = (B ⊲ e) × LgB e
AdM B (inj₂ c , κ) e = ⊤

nxM : (B : Cd) (κ : K (Lv Y)) (e : E (Lv Y) κ) → AdM B κ e → Cd
nxM B (inj₁ _ , inj₁ ()) e a
nxM B (inj₁ _ , inj₂ _) e a = hs e
nxM B (inj₂ c , κ) e a = B

evI↑ : ∀ {B B′} → B ⊲ B′ → ∀ {κ} → EvI B κ → EvI B′ κ
evI↑ q {inj₁ _ , _} ev = tt
evI↑ q {inj₂ _ , _} ev = ⊲ᴮ-tr ev q

PYm : PS (Lv Y)
PYm = record { Ev = EvI ; Ad = AdM ; nx = nxM ; ev↑ = evI↑ ; ad↓ = ad↓′ ; nx↑ = nx↑′ }
  where
  ad↓′ : ∀ {B B′} → B ⊲ B′ → ∀ {κ e} (a′ : AdM B′ κ e) → Σ (AdM B κ e) (λ a → nxM B κ e a ⊲ nxM B′ κ e a′)
  ad↓′ q {inj₁ _ , inj₁ ()} a′
  ad↓′ q {inj₁ _ , inj₂ _} (w , l) = (⊲ᴮ-tr q w , l) , hself
  ad↓′ q {inj₂ _ , _} a′ = tt , q
  nx↑′ : ∀ {B κ e} (a : AdM B κ e) → B ⊲ nxM B κ e a
  nx↑′ {κ = inj₁ _ , inj₁ ()} a
  nx↑′ {κ = inj₁ _ , inj₂ _} (w , l) = ⊲ᴮ-tr w (hsuc hself)
  nx↑′ {κ = inj₂ _ , _} a = hself

-- Ev 抄下来, 内层指标不动世界
PYs : PS (Lv Y)
PYs = record { Ev = EvI ; Ad = λ _ _ _ → ⊤ ; nx = λ B _ _ _ → B
             ; ev↑ = evI↑ ; ad↓ = λ q _ → tt , q ; nx↑ = λ _ → hself }
```

## §3 内层指标在下层路径里不平凡: 真实地板

```agda
evOf : ∀ {T : KS} (P : PS T) {W κ x} → IsNode κ x → PH P W x → PS.Ev P W κ
evOf P isn p = proj₁ p

-- 真实的地板带路径, 且内层种类的 Ev 读世界时, 内层指标必须把世界移到坐标之上
floor-forces : (P : PS (Lv Y)) → (∀ W d → PS.Ev P W (κY d) → hs d ⊲ W) →
  ∀ {W} → PH P W (flL Y) → ∀ d (a : PS.Ad P W ixY (hs (hs d))) → hs d ⊲ PS.nx P W ixY (hs (hs d)) a
floor-forces P snd p d a = snd _ d (evOf P (rootY d) (proj₂ p (hs (hs d)) a))

no12 : ¬ (num {S⊥} 2 ⊲ num 1)
no12 (hsuc ())

-- 不动世界 + Ev 读世界: 真实地板不带路径
floor-no-stay : (P : PS (Lv Y)) → (∀ W d → PS.Ev P W (κY d) → hs d ⊲ W) →
  (∀ W e a → PS.nx P W ixY e a ≡ W) → PS.Ad P (num 1) ixY (num 3) → ¬ PH P (num 1) (flL Y)
floor-no-stay P snd st a p =
  no12 (subst (λ z → num 2 ⊲ z) (st (num 1) (num 3) a) (floor-forces P snd p (num 1) a))

-- 三种情形
-- (A) 平凡: 真实地板带路径, 但 Ev 不读世界 (留下的结点没有证据)
case-triv : PH trivP (num 1) (flL Y) × PS.Ev trivP (num 1) (κY (num 1)) × ¬ PS.Ev Q₁ (num 1) (inj₂ (num 1) , inj₂ tt)
case-triv = PH-triv (num 1) (flL Y) , tt , no12

-- (B) Ev 抄下来, 不动世界: 真实地板不带路径
case-stay : ¬ PH PYs (num 1) (flL Y)
case-stay = floor-no-stay PYs (λ W d e → e) (λ W e a → refl) tt

-- (C) Ev 抄下来, 按下层的规则移动: 真实地板带路径
PH-comp : ∀ W d → d ⊲ W → (t : HB (FXL lz gY (inj₂ d))) → PH PYm W (ι {IxL lz} {FXL lz gY} (inj₂ d) t)
PH-comp W d b hz = tt
PH-comp W d b (hs t) = PH-comp W d b t
PH-comp W d b (hl f) = λ n → PH-comp W d b (f n)
PH-comp W d b (hΩ κ g) = b , λ e a → PH-comp W d b (g e)

PH-θY : ∀ e W → e ⊲ W → PH PYm W (θY e)
PH-θY hz W b = tt
PH-θY (hs d) W b =
  PH-⊞ PYm (θY d) _ (PH-θY d W (⊲ᴮ-tr (hsuc hself) b)) (PH-comp W d (⊲ᴮ-tr (hsuc hself) b) (flL (gY d)))
PH-θY (hl f) W b = λ n → PH-θY (f n) W (⊲ᴮ-tr (hlim n hself) b)
PH-θY (hΩ () _) W b

case-move : ∀ W → PH PYm W (flL Y)
case-move W = tt , λ e a → PH-θY e (hs e) (hsuc hself)
```

## §4 留下带回灌: 任何下层规则都对不上

```agda
shB : Cd → Cd → Cd
shB B y = sh J₁ lz (tt , B) y

module Keep (Q : PS (Lv X₁)) (snd : Sound Q) (Φ : Cd → HB (Lv Y) → HB (Lv X₁)) where
  Out : (Cd → Cd) → HB (Lv X₁)
  Out sf = hΩ ixX (λ y → Φ y (θY (sf y)))

  Kp : Cd → Cd → Set
  Kp y d = IsNode {Lv X₁} (inj₂ d , inj₂ tt) (Φ y (θY (hs (hs d))))

  keep-req : ∀ sf V y (a : PS.Ad Q V ixX y) d → sf y ≡ hs (hs d) → Kp y d → PH Q V (Out sf) → hs d ⊲ PS.nx Q V ixX y a
  keep-req sf V y a d eq kp p =
    snd _ d (inj₂ tt) (evOf Q kp (subst (λ z → PH Q (PS.nx Q V ixX y a) (Φ y (θY z))) eq (proj₂ p y a)))
```

**真实的世界对.** 从 $(B, V)=(1,1)$ 过一个留下的结点 (坐标 $1$) 到 $(3, 2)$.

```agda
reachB : proj₂ (nxt J₁ lz (tt , num 1) (shB (num 1) (num 1)) (adm-sh J₁ lz (num 1) (tt , tt))) ≡ num 3
reachB = refl

reachV : ∀ (a : AdQ (num 1) ixX (num 1)) → nxQ (num 1) ixX (num 1) a ≡ num 2
reachV a = refl

no43 : ¬ (num {S⊥} 4 ⊲ num 3)
no43 (hsuc (hsuc (hsuc ())))

-- Q₁: 世界对 (3, 2), 坐标 2 可入, 回灌到 5, 那一支的种类要 4 ⊲ 3
real-keep-fails : (Φ : Cd → HB (Lv Y) → HB (Lv X₁)) → Keep.Kp Q₁ Q₁-sound Φ (num 2) (num 3) →
  ¬ PH Q₁ (num 2) (Keep.Out Q₁ Q₁-sound Φ (shB (num 3)))
real-keep-fails Φ kp p = no43 (Keep.keep-req Q₁ Q₁-sound Φ (shB (num 3)) (num 2) (num 2) (hself , tt) (num 3) refl kp p)

-- 前提实例
Φ-ex : Cd → HB (Lv Y) → HB (Lv X₁)
Φ-ex y t = hΩ (inj₂ (num 3) , inj₂ tt) (λ _ → hz)

kp-ex : Keep.Kp Q₁ Q₁-sound Φ-ex (num 2) (num 3)
kp-ex = isn
```

**对任何下层规则.** 换掉下层的新世界 (`nx`) 也不行: `PS` 要求 `nx` 随世界单调 (`ad↓`), 世界要合法才能比较; 两个世界对的回灌坐标 $1\boxplus\omega'$, $3\boxplus\omega'$ 没有合法的公共上界.

```agda
module _ {S : KS} where
  at : HB S → ℕ → HB S
  at (hl f) n = f n
  at x n = x

NoL : Cd → Set
NoL hz = ⊤
NoL (hs x) = NoL x
NoL (hl f) = ⊥
NoL (hΩ () _)

NoL⊲ : ∀ {a b} → a ⊲ b → NoL b → NoL a
NoL⊲ hself n = n
NoL⊲ (hsuc p) n = NoL⊲ p n
NoL⊲ (hlim k p) ()
NoL⊲ (hLim {κ = ()} _ _) n

NoL-⊞ : ∀ a b → NoL a → NoL b → NoL (a ⊞ b)
NoL-⊞ a hz na nb = na
NoL-⊞ a (hs b) na nb = NoL-⊞ a b na nb
NoL-⊞ a (hΩ () _) na nb

NoL-num : ∀ n → NoL (num n)
NoL-num zero = tt
NoL-num (suc n) = NoL-num n

ω̂ : Cd
ω̂ = hl num

L̂ : Cd
L̂ = leg lz ω̂

NoL-legn : ∀ n → NoL (leg lz (num n))
NoL-legn zero = tt
NoL-legn (suc n) = NoL-legn n

NoL-Σ : ∀ n → NoL (Σᴸ lz (λ m → leg lz (num m)) n)
NoL-Σ zero = tt
NoL-Σ (suc n) = NoL-⊞ _ (leg lz (num (suc n))) (NoL-Σ n) (NoL-legn (suc n))

inc : ∀ {B B′} → NoL B′ → ¬ (B ≡ B′) → ¬ (hs (B ⊞ L̂) ⊲ hs (B′ ⊞ L̂))
inc {B} {B′} nb ne p = go p refl
  where
  go : ∀ {b} → hs (B ⊞ L̂) ⊲ b → b ≡ hs (B′ ⊞ L̂) → ⊥
  go hself e = ne (cong (λ z → at (pr z) 0) e)
    where pr : Cd → Cd
          pr (hs x) = x
          pr x = x
  go (hsuc (hlim n q)) refl = NoL⊲ q (NoL-⊞ B′ _ nb (NoL-Σ n))

y₀ : Cd
y₀ = hs (hs ω̂)

no13 : ¬ (num {S⊥} 1 ≡ num 3)
no13 ()

no31 : ¬ (num {S⊥} 3 ≡ num 1)
no31 ()

no-lower-rule : (Q : PS (Lv X₁)) (snd : Sound Q) (Φ : Cd → HB (Lv Y) → HB (Lv X₁)) →
  (V₂ : Cd) → num 1 ⊲ V₂ →
  (a₂ : PS.Ad Q V₂ ixX y₀) → LgB (PS.nx Q V₂ ixX y₀ a₂) →
  Keep.Kp Q snd Φ y₀ (num 1 ⊞ L̂) → Keep.Kp Q snd Φ y₀ (num 3 ⊞ L̂) →
  PH Q (num 1) (Keep.Out Q snd Φ (shB (num 1))) → PH Q V₂ (Keep.Out Q snd Φ (shB (num 3))) → ⊥
no-lower-rule Q snd Φ V₂ q₂ a₂ lg k₁ k₃ p₁ p₃ with PS.ad↓ Q {num 1} {V₂} q₂ {ixX} {y₀} a₂
... | a₁ , m with cmpB (⊲ᴮ-tr (Keep.keep-req Q snd Φ (shB (num 1)) (num 1) y₀ a₁ _ refl k₁ p₁) m)
                      (Keep.keep-req Q snd Φ (shB (num 3)) V₂ y₀ a₂ _ refl k₃ p₃) tt lg
...   | inj₁ q = inc tt no31 q
...   | inj₂ q = inc tt no13 q
```

**初始世界就不够 (`Q₁`).** $(B,V)=(1,1)$, 坐标 $\omega+2$: 回灌到 $(1\boxplus\omega')+2$, 要 $(1\boxplus\omega')+1\lhd\omega+3$.

```agda
no-d₁ : ¬ (hs (num 1 ⊞ L̂) ⊲ hs (hs (hs ω̂)))
no-d₁ (hsuc (hsuc p)) = go p refl
  where
  go : ∀ {b} → hs (num 1 ⊞ L̂) ⊲ b → b ≡ hs ω̂ → ⊥
  go hself e = no-z (cong (λ z → at (pr z) 0) e)
    where pr : Cd → Cd
          pr (hs x) = x
          pr x = x
          no-z : ¬ (num {S⊥} 1 ≡ hz)
          no-z ()
  go (hsuc (hlim n q)) refl = NoL⊲ q (NoL-num n)

Lg-num : ∀ n → LgB (num {S⊥} n)
Lg-num zero = tt
Lg-num (suc n) = Lg-num n

init-keep-fails : (Φ : Cd → HB (Lv Y) → HB (Lv X₁)) → Keep.Kp Q₁ Q₁-sound Φ y₀ (num 1 ⊞ L̂) →
  ¬ PH Q₁ (num 1) (Keep.Out Q₁ Q₁-sound Φ (shB (num 1)))
init-keep-fails Φ kp p =
  no-d₁ (Keep.keep-req Q₁ Q₁-sound Φ (shB (num 1)) (num 1) y₀ (hsuc (hsuc (hlim 1 hself)) , (λ n → hsuc hself) , Lg-num) _ refl kp p)
```

**前提可满足.** `no-lower-rule` 的前提两两相容: `Qb b` 的新世界是 $(b\boxplus\mathrm{leg}\,e)+2$, 与下层世界无关, 是 `PS`, `Sound`, 合法; `b = 1` 时第一个世界对的路径成立 (`p₁-ex`), `b = 3` 时第二个世界对的路径成立 (`p₃-ex`). `Φr` 把根上的内层种类留下 (`Kp` 成立).

```agda
nb : Cd → Cd → Cd
nb b e = hs (hs (b ⊞ leg lz e))

AdB : Cd → Cd → (κ : K (Lv X₁)) → E (Lv X₁) κ → Set
AdB b B (inj₁ _ , inj₁ ()) e
AdB b B (inj₁ _ , inj₂ _) e = B ⊲ nb b e
AdB b B (inj₂ c , κ) e = ⊤

nxB : (b B : Cd) (κ : K (Lv X₁)) (e : E (Lv X₁) κ) → AdB b B κ e → Cd
nxB b B (inj₁ _ , inj₁ ()) e a
nxB b B (inj₁ _ , inj₂ _) e a = nb b e
nxB b B (inj₂ c , κ) e a = B

Qb : Cd → PS (Lv X₁)
Qb b = record { Ev = EvQ ; Ad = AdB b ; nx = nxB b ; ev↑ = ev↑′ ; ad↓ = ad↓′ ; nx↑ = nx↑′ }
  where
  ev↑′ : ∀ {B B′} → B ⊲ B′ → ∀ {κ} → EvQ B κ → EvQ B′ κ
  ev↑′ q {inj₁ _ , _} ev = ⊲ᴮ-tr ev q
  ev↑′ q {inj₂ _ , _} ev = ⊲ᴮ-tr ev q
  ad↓′ : ∀ {B B′} → B ⊲ B′ → ∀ {κ e} (a′ : AdB b B′ κ e) → Σ (AdB b B κ e) (λ a → nxB b B κ e a ⊲ nxB b B′ κ e a′)
  ad↓′ q {inj₁ _ , inj₁ ()} a′
  ad↓′ q {inj₁ _ , inj₂ _} w = ⊲ᴮ-tr q w , hself
  ad↓′ q {inj₂ _ , _} a′ = tt , q
  nx↑′ : ∀ {B κ e} (a : AdB b B κ e) → B ⊲ nxB b B κ e a
  nx↑′ {κ = inj₁ _ , inj₁ ()} a
  nx↑′ {κ = inj₁ _ , inj₂ _} w = w
  nx↑′ {κ = inj₂ _ , _} a = hself

Qb-sound : ∀ b → Sound (Qb b)
Qb-sound b W d κ e = e

Φr : Cd → HB (Lv Y) → HB (Lv X₁)
Φr y (hΩ (inj₂ (hs d) , κ) g) = hΩ (inj₂ d , inj₂ tt) (λ _ → hz)
Φr y _ = hz

kpr : ∀ b y d → Keep.Kp (Qb b) (Qb-sound b) Φr y d
kpr b y d = isn

PH-Φr : ∀ b y x → PH (Qb b) (hs (hs x)) (Φr y (θY x))
PH-Φr b y hz = tt
PH-Φr b y (hs hz) = tt
PH-Φr b y (hs (hs d)) = hsuc (hsuc (hsuc hself)) , λ e a → tt
PH-Φr b y (hs (hl f)) = tt
PH-Φr b y (hs (hΩ () _))
PH-Φr b y (hl f) = tt
PH-Φr b y (hΩ () _)

Lg-nb : ∀ b → LgB b → ∀ e → LgB (nb b e)
Lg-nb b lb e = Lg-⊞ b (leg lz e) lb (Lg-leg lz e)

p₁-ex : PH (Qb (num 1)) (num 1) (Keep.Out (Qb (num 1)) (Qb-sound (num 1)) Φr (shB (num 1)))
p₁-ex = hself , λ e a → PH-Φr (num 1) e (num 1 ⊞ leg lz e)

p₃-ex : PH (Qb (num 3)) (num 2) (Keep.Out (Qb (num 3)) (Qb-sound (num 3)) Φr (shB (num 3)))
p₃-ex = hsuc hself , λ e a → PH-Φr (num 3) e (num 3 ⊞ leg lz e)

-- 新世界合法, 且 y₀ 在世界 2 里可入
a₂-ex₁ : PS.Ad (Qb (num 1)) (num 2) ixX y₀
a₂-ex₁ = hsuc (hsuc (hsuc (hsuc (hlim 1 hself))))

a₂-ex₃ : PS.Ad (Qb (num 3)) (num 2) ixX y₀
a₂-ex₃ = hsuc (hsuc (hsuc (hsuc (hlim 0 (hsuc hself)))))

lg-ex : ∀ b → LgB b → ∀ a → LgB (PS.nx (Qb b) (num 2) ixX y₀ a)
lg-ex b lb a = Lg-nb b lb y₀
```

## §5 上层: 分量的世界不能写回

```agda
Wc : Cd → Set
Wc c = Wd (Lv (gX₁ c))

u₀ : Wd (Lv X₁)
u₀ = w₀L X₁

V₀ : (c : Cd) → Wc c
V₀ c = w₀L (lz ⊕L upL lz c) , hs hz

record Upd : Set where
  field
    upd   : (c₀ : Cd) → Wc c₀ → Wd (Lv X₁) → Wd (Lv X₁)
    here′ : ∀ c₀ V u → upd c₀ V u (inj₂ c₀) ≡ V
    there : ∀ c₀ c V u → ¬ (c ≡ c₀) → upd c₀ V u (inj₂ c) ≡ u (inj₂ c)

module _ {S : KS} where
  hd : HB S → Bool
  hd hz = true
  hd _ = false

module WB (U : Upd) where
  open Upd U
  rd : ∀ c c₀ → Bool
  rd c c₀ = hd (proj₂ (upd c₀ (V₀ c₀) u₀ (inj₂ c)))

  weak-eq : ∀ c c₀ → ¬ ¬ (c ≡ c₀) ⊎ ¬ (c ≡ c₀)
  weak-eq c c₀ with rd c c₀ in eq
  ... | true = inj₂ λ { refl → f (trans (sym eq) (cong (λ V → hd (proj₂ V)) (here′ c₀ (V₀ c₀) u₀))) }
    where f : ¬ (true ≡ false)
          f ()
  ... | false = inj₁ λ ne → f (trans (sym eq) (cong (λ V → hd (proj₂ V)) (there c₀ c (V₀ c₀) u₀ ne)))
    where f : ¬ (false ≡ true)
          f ()

FE : Set
FE = ∀ (f g : ℕ → Cd) → (∀ n → f n ≡ g n) → f ≡ g

WLPO : Set
WLPO = ∀ (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ ¬ (∀ n → α n ≡ false)

cα : (ℕ → Bool) → ℕ → Cd
cα α n = if α n then hs hz else hz

nz : ∀ b → (if b then hs {S⊥} hz else hz) ≡ hz → b ≡ false
nz false e = refl
nz true ()

ptw : ∀ α → hl (cα α) ≡ hl (λ _ → hz) → ∀ n → α n ≡ false
ptw α e n = nz (α n) (cong (λ z → at z n) e)

bf : ∀ b → ¬ ¬ (b ≡ false) → b ≡ false
bf false k = refl
bf true k = ⊥-elim (k (λ ()))

upd→WLPO : FE → Upd → WLPO
upd→WLPO fe U α with WB.weak-eq U (hl (cα α)) (hl (λ _ → hz))
... | inj₁ k = inj₁ (λ n → bf (α n) (λ ne → k (λ e → ne (ptw α e n))))
... | inj₂ ne = inj₂ (λ all → ne (cong hl (fe (cα α) (λ _ → hz) (λ n → cong (λ b → if b then hs hz else hz) (all n)))))
```

**第一位置读分量的世界.** 高度 $c=$ `th₁ (hs d)` 的根是种类 (分量 $d$, 新); 过它的第一位置要分量 $d$ 的界. 所以走进内层分量要动世界在**分量** $d$ 处的部分.

```agda
thRoot : ∀ d → IsNode {Lv X₁} (inj₂ d , inj₂ tt) (th₁ (hs d))
thRoot d = isn
```

## §6 判定 "分量在界内" 是 LPO

```agda
LPO : Set
LPO = ∀ (α : ℕ → Bool) → Σ ℕ (λ n → α n ≡ true) ⊎ (∀ n → α n ≡ false)

hit : (ℕ → Bool) → ℕ → Bool
hit α zero = α zero
hit α (suc n) = hit α n ∨ α (suc n)

bα : (ℕ → Bool) → ℕ → Cd
bα α n = if hit α n then hs hz else hz

Bα : (ℕ → Bool) → Cd
Bα α = hl (bα α)

Lg-Bα : ∀ α → LgB (Bα α)
Lg-Bα α = st , (λ n → go n (hit α n))
  where
  go : ∀ n (b : Bool) → LgB (if b then hs {S⊥} hz else hz)
  go n true = tt
  go n false = tt
  st′ : ∀ {w} (x y : Bool) → (if x then hs {S⊥} hz else hz) ⊲[ w ] (if (x ∨ y) then hs hz else hz)
  st′ true y = hself
  st′ false true = hsuc hself
  st′ false false = hself
  st : ∀ {w} n → bα α n ⊲[ w ] bα α (suc n)
  st n = st′ (hit α n) (α (suc n))

hit→ : ∀ α n → hit α n ≡ true → Σ ℕ (λ m → α m ≡ true)
hit→ α zero e = zero , e
hit→ α (suc n) e with hit α n in h
... | true = hit→ α n h
... | false = suc n , e

→hit : ∀ α n → α n ≡ true → hit α n ≡ true
→hit α zero e = e
→hit α (suc n) e with hit α n
... | true = refl
... | false = e

one⊲→ : ∀ α → hs hz ⊲ Bα α → Σ ℕ (λ m → α m ≡ true)
one⊲→ α (hlim n p) = hit→ α n (go (hit α n) p)
  where
  go : ∀ b → hs {S⊥} hz ⊲ (if b then hs hz else hz) → b ≡ true
  go true p = refl
  go false ()

→one⊲ : ∀ α n → α n ≡ true → hs hz ⊲ Bα α
→one⊲ α n e = hlim n (go (hit α n) (→hit α n e))
  where
  go : ∀ b → b ≡ true → hs {S⊥} hz ⊲ (if b then hs hz else hz)
  go true r = hself

Dec₀ : Set → Set
Dec₀ A = A ⊎ ¬ A

bd-dec→LPO : (∀ B → LgB B → Dec₀ (hs hz ⊲ B)) → LPO
bd-dec→LPO d α with d (Bα α) (Lg-Bα α)
... | inj₁ p = inj₁ (one⊲→ α p)
... | inj₂ n = inj₂ (λ m → nb′ (α m) (λ e → n (→one⊲ α m e)))
  where
  nb′ : ∀ b → ¬ (b ≡ true) → b ≡ false
  nb′ false k = refl
  nb′ true k = ⊥-elim (k refl)
```

## §7 分类: 一切种类, 不用搬运

```agda
data Tag (x : LH) : Set where
  bas : K (Lv x) → Tag x
  twr : LH → Tag x
  inI : LH → Tag x
  inO : (k : LH) → K (Lv k) → Tag x

clT : ∀ x y → K (Lv (x ⊕L y)) → Tag x
clT x lz κ = bas κ
clT x (ls y) (inj₁ κ) = clT x y κ
clT x (ls y) (inj₂ _) = twr (x ⊕L y)
clT x (ll f) (n , κ) = clT x (f n) κ
clT x (lΩ k g) (inj₁ _ , inj₁ κ) = inO k κ
clT x (lΩ k g) (inj₁ _ , inj₂ _) = inI k
clT x (lΩ k g) (inj₂ c , κ) = clT x (g c) κ

toE : ∀ k κ → HB (Lv (lvl k κ)) → E (Lv k) κ
toE lz ()
toE (ls x) (inj₁ κ) c = toE x κ c
toE (ls x) (inj₂ _) c = c
toE (ll f) (n , κ) c = toE (f n) κ c
toE (lΩ k g) (inj₁ _ , inj₁ κ) c = toE k κ c
toE (lΩ k g) (inj₁ _ , inj₂ _) c = c
toE (lΩ k g) (inj₂ d , κ) c = toE (g d) κ c

node-form : ∀ k κ h → node k κ h ≡ lΩ (lvl k κ) (λ c → h (toE k κ c))
node-form lz ()
node-form (ls x) (inj₁ κ) h = node-form x κ h
node-form (ls x) (inj₂ _) h = refl
node-form (ll f) (n , κ) h = node-form (f n) κ h
node-form (lΩ k g) (inj₁ _ , inj₁ κ) h = node-form k κ h
node-form (lΩ k g) (inj₁ _ , inj₂ _) h = refl
node-form (lΩ k g) (inj₂ d , κ) h = node-form (g d) κ h

lvl-E : ∀ k κ → E (Lv k) κ ≡ HB (Lv (lvl k κ))
lvl-E lz ()
lvl-E (ls x) (inj₁ κ) = lvl-E x κ
lvl-E (ls x) (inj₂ _) = refl
lvl-E (ll f) (n , κ) = lvl-E (f n) κ
lvl-E (lΩ k g) (inj₁ _ , inj₁ κ) = lvl-E k κ
lvl-E (lΩ k g) (inj₁ _ , inj₂ _) = refl
lvl-E (lΩ k g) (inj₂ d , κ) = lvl-E (g d) κ

-- 种类的世界的一层
wlK : ∀ k κ → Wd (Lv k) → WL (lvl k κ)
wlK lz ()
wlK (ls x) (inj₁ κ) u = wlK x κ (proj₁ u)
wlK (ls x) (inj₂ _) u = u
wlK (ll f) (n , κ) u = wlK (f n) κ (u n)
wlK (lΩ k g) (inj₁ _ , inj₁ κ) u = wlK k κ (proj₁ (u (inj₁ tt)))
wlK (lΩ k g) (inj₁ _ , inj₂ _) u = u (inj₁ tt)
wlK (lΩ k g) (inj₂ d , κ) u = wlK (g d) κ (u (inj₂ d))

bdK : ∀ k κ (e : HB (Lv (lvl k κ))) (u : Wd (Lv k)) →
      Bd (Lv k) κ (toE k κ e) u ≡ (e ⊲[ proj₁ (wlK k κ u) ] proj₂ (wlK k κ u))
bdK lz ()
bdK (ls x) (inj₁ κ) e u = bdK x κ e (proj₁ u)
bdK (ls x) (inj₂ _) e u = refl
bdK (ll f) (n , κ) e u = bdK (f n) κ e (u n)
bdK (lΩ k g) (inj₁ _ , inj₁ κ) e u = bdK k κ e (proj₁ (u (inj₁ tt)))
bdK (lΩ k g) (inj₁ _ , inj₂ _) e u = refl
bdK (lΩ k g) (inj₂ d , κ) e u = bdK (g d) κ e (u (inj₂ d))

-- 层号忘了种类
upL-collide : upL X₁ (hΩ ixX (λ _ → hz)) ≡ upL X₁ (hΩ (inj₂ hz , inj₂ tt) (λ _ → hz)) ×
              ¬ (hΩ {Lv X₁} ixX (λ _ → hz) ≡ hΩ (inj₂ hz , inj₂ tt) (λ _ → hz))
upL-collide = refl , λ ()
```

## §8 对角到 $\Lambda$

```agda
Fx : ℕ → KS
Fx n = Lv (xb n)

wx : Wd (sup ℕ Fx)
wx n = w₀L (xb n)

one≢two : ¬ (1 ≡ 2)
one≢two ()

xb-naive : ¬ LgB {Lv (ll xb)} (hl (λ n → ι {ℕ} {Fx} (suc n) (flL (xb (suc n)))))
xb-naive = sup-diag-illegal {ℕ} {Fx} suc (λ n → flL (xb (suc n))) wx here one≢two

xb-acc : LgB (flL (ll xb))
xb-acc = Lg-flL (ll xb)

xb-acc-shape : flL (ll xb) ≡ hl (ΣF xb)
xb-acc-shape = refl
```

## 结论 (按档)

- **[定理, 否定]** **`floor-forces`**, **`floor-no-stay`**, `case-stay`, `case-triv`; `keep-req`, `real-keep-fails`, `init-keep-fails`, **`no-lower-rule`**; `WB.weak-eq`; `bd-dec→LPO`; `xb-naive`; `upL-collide`.
- **[定理, 条件]** **`upd→WLPO`** (前提 `FE`).
- **[定理, 正面]** `rootY`, `thRoot`, `Y≡`, `flY≡`, `case-move`, `PH-θY`; `clT`, `toE`, `node-form`, `lvl-E`, `wlK`, `bdK`; `xb-acc`, `xb-acc-shape`; 实例 `Qb`, `p₁-ex`, `p₃-ex`.
- **[有限测试]** 变量 $n$ 上 `node (xb n) κ h` 的 `refl` 编译失败 (退出码 42).
- **[判断]** 下层折叠必须用证据 $d+1\lhd W$ 做公共上界 (RecB 的 `dcx` 如此; `Sound` 把它写成前提); "留下" 的形状以 `LHRec` §4 为准; 否定只对写明的形状.
