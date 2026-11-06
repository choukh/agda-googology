# 树的语言, 否定一路 (一): 接口定稿之前, 今天的否定性判据给不出正面指引

> 不含记号. 入口 [NegTreeLang](NegTreeLang.lagda.md). 本篇**不依赖**构造一路的接口 `TreeLangIf` (接口定稿之前写的部分), 只读导入今天的判据来源 ([HtTowerNeg](HtTowerNeg.lagda.md), [NegSlotPre](NegSlotPre.lagda.md), [NegSlotWall](NegSlotWall.lagda.md)) 与对象 ([HtTowerTy](HtTowerTy.lagda.md), [LFReTy](LFReTy.lagda.md), [FabLFReGen](FabLFReGen.lagda.md)). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延 `FEL` (只对 $\mathbb N\to$ `LH`) 只在一条条件定理 (`pt-SL→WLPO`) 里作前提, 标 "条件".
>
> **问题.** 构造一路要 "只用判据推出下一步定义". 今天的否定性判据是: `no-retract` (没有种类的坐标收缩到全部高度), `no-inflate` (经一个坐标绕一圈不能膨胀), `lv-not-self` / `no-total` (没有种类的坐标类型就是本级的高度类型), `slot-ret` / `no-slot-adj` (共享槽逼成员两两互为收缩, 相邻两级不能同槽), 分离子一族 (`upd₁-sep`, `updT-sep`, `updD-sep`, ...: "升一份, 留别份" 的点更新推出分离子). 本篇问: 它们合起来能不能挑出一个定义?
>
> **结果.**
>
> 1. **`crit₄` (定理, 对一切 `T`).** 前四条写成种类结构 `T` 上的谓词 `Crit₄ T`, 对**一切** `T` 成立 (就是那四条定理本身). 作为对定义的筛子, 它们**一个定义也不排除**; 它们排除的是规格 (想要的性质: 收缩的槽, 膨胀的绕圈, 相邻两级同槽, 坐标就是本级高度).
> 2. **`pt-wdec` (定理, 对一切 `T`, 新的一般形).** 分离子一族的共同形状: 一族种类 $\kappa_j$ ($j:J$) 各有精确升界 (`RsK`), 且升 $\kappa_j$ 时别的 $\kappa_{j'}$ ($j'\ne j$) 的顶不动 (`keep`), 再加一个可判定的 "标记" (`Mk`: 某个坐标值与基世界的顶可以分开), 就推出 $J$ 上相等的弱判定 (`WDec J`). $J$ 能编码 $\mathbb N\to$ `Bool` (`Code`) 时推出分离子 (`wdec→sepC`); 加外延得 WLPO (条件). 只用 `rs-top` 与 `keep`, 不用 `rs≤`, `rsLg`, 世界的形状.
> 3. **`pt-SL-sep` (定理) / `pt-SL→WLPO` (条件 `FEL`).** 在一次封闭的层号结构 `SL` ([LFReTy](LFReTy.lagda.md)) 上: 若一切层 $k$ 的新种类 `νL k` 都有精确升界且 "升一份留别份", 则分离子. 这把 [FabLFReGen](FabLFReGen.lagda.md) §4 的判断 ("C6 在 `SL` 上落在 `upd₁-sep` 一族的定义域里") 写成了定理. 前提可满足的部分: 下标可判定的子族 (`lz`, `ls lz`) 上, `RsK` 与 `keep` 同时成立 (`ptB`), 标记有实例 (`mkNew`).
> 4. **盲 (`blind⊥`, `blind1`, `blindSL`, 定理).** 第五条判据写成对候选 (种类结构 + 每个种类的升界或有损) 的筛子 `NoPt` (候选的升界不是编码族上的 "升一份留别份"). 三个候选都满足全部五条: **(a)** `S⊥` (没有种类, 高度就是第 0 层的可数树: `frE⊥`, `toE⊥` 双向保第一位置); **(b)** `step S⊥` (只有一个种类, 精确升界); **(c)** `SL` 配 `FabLFReGen.GL` 的顶坐标, 一切种类有损 (今天候选闭项 `TΛ` 所用的回灌, 读法远低于 ψ₀Λ, 判断). 更一般: 对一切 `T`, 全有损的候选满足全部五条 (`null-crit`). 判据分不开 "没有 Ω" (a) 与 "每一层 $k$ 都有坐标为 `HB (Lv k)` 的种类" (c, `coord-stage`).
>
> **只否定什么.** 只否定推断 "满足今天的否定性判据, 所以定义被确定 / 被推向更强". 不否定任何构造, 不否定任何判据 (它们都对), 不否定 "判据→定义" 这条路线: 缺的是**正面的** (向上封闭的) 判据, 本篇 §5 只给判断. `pt-SL-sep` 只否定 `SL` 上对**一切**层号一致的 "精确 + 留别份"; **不否定**: 只精确不留 (未构造, 未否定), 有界升界 (`RsOwnIf.RsBd`), 下标可判定的子族 (`ptB` 正是实例).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegTreeLangPre where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerNeg using (no-retract)
open import OCF.Align.NegSlotPre using (_◁_; s; p; ps; no-inflate)
import OCF.Align.NegSlotWall as NSW
open import OCF.Align.SlotIf using (Slot)
open import OCF.Align.RsOwnIf using (RsK; rs; rs≤; rsLg; rs-top)
open import OCF.Align.GenFoldIf using (TopG; top; topBd; tpK; w₀)
open import OCF.Align.GenFoldTree using (topStepG)
open import OCF.Align.ColimWNeg using (WLPO)
open import OCF.Align.LFReTy using (LH; lz; ls; ll; lΩ; Lv; S⊥; FL; SL; νL; ofHB)
open import OCF.Align.LFReTower using (tw)
open import OCF.Align.FabLFReGen using (GL; top⊥; frE⊥; frE⊥-⊲; frE⊥-lg; coord-stage)
```

## §1 前四条判据: 对一切种类结构成立

`Crit₄ T` 的四个字段就是今天的四条否定, 写成 `T` 上的谓词. `na` 对 `T` 上的**一切**共享槽量化.

```agda
record Crit₄ (T : KS) : Set₁ where
  field
    nr : ∀ κ → ¬ (HB T ◁ E T κ)
    ni : ∀ κ (d : HB T → E T κ) (u : E T κ → HB T) → ¬ (∀ x → Σ (Wd T) (λ w → x ⊲[ w ] u (d x)))
    ns : ∀ κ → ¬ (E T κ ≡ HB T)
    na : ∀ {tp J κJ Q tq κ₀} (S : Slot T tp J κJ Q tq κ₀) jL jH {S′ : KS} (κ : K S′) →
         E T (κJ jH) ≡ HB S′ → E S′ κ ≡ E T (κJ jL) → ¬ NSW.SL.Reach S jH
open Crit₄ public

crit₄ : ∀ T → Crit₄ T
crit₄ T = record
  { nr = λ κ R → no-retract κ (s R) (p R) (ps R)
  ; ni = no-inflate
  ; ns = λ κ e → no-retract κ (λ x → subst (λ Z → Z) (sym e) x) (λ y → subst (λ Z → Z) e y) (λ x → sr e x)
  ; na = λ S jL jH κ eH eL R → NSW.SL.no-slot-adj S jL jH κ eH eL R }
  where
  sr : ∀ {X Y : Set} (e : X ≡ Y) (x : Y) → subst (λ Z → Z) e (subst (λ Z → Z) (sym e) x) ≡ x
  sr refl x = refl
```

## §2 分离子一族的一般形: "升一份留别份" 推出弱判定

`PtFam tp J κJ`: 一族种类各有精确升界 (`RsK`, 只用到 `rs-top`), 升 $\kappa_j$ 时别的成员的顶不动 (`keep`; 比较的是两个**裸下标** $j,j'$, 没有公共上界, 手册 §3.1 的律的定义域). `Mk`: 一个基世界, 每个成员一个标记坐标与一个可判定的谓词 $D_j$, 标记满足 $D_j$, 基世界的顶不满足.

```agda
record PtFam {T : KS} (tp : TopG T) (J : Set) (κJ : J → K T) : Set where
  field
    R    : ∀ j → RsK T tp (κJ j)
    keep : ∀ j j′ w v → ¬ (j′ ≡ j) → top tp (κJ j′) (rs (R j) w v) ≡ top tp (κJ j′) w
open PtFam public

record Mk {T : KS} (tp : TopG T) (J : Set) (κJ : J → K T) : Set₁ where
  field
    wb  : Wd T
    mk  : ∀ j → E T (κJ j)
    D   : ∀ j → E T (κJ j) → Set
    dD  : ∀ j e → D j e ⊎ ¬ D j e
    Dmk : ∀ j → D j (mk j)
    nD0 : ∀ j → ¬ D j (top tp (κJ j) wb)
open Mk public

WDec : Set → Set
WDec J = ∀ (j j′ : J) → ¬ (j′ ≡ j) ⊎ ¬ ¬ (j′ ≡ j)

pt-wdec : ∀ {T tp J κJ} → PtFam {T} tp J κJ → Mk tp J κJ → WDec J
pt-wdec {T} {tp} {J} {κJ} P M j j′ with dD M j′ (top tp (κJ j′) (rs (R P j) (wb M) (mk M j)))
... | inj₁ d = inj₂ (λ ne → nD0 M j′ (subst (D M j′) (keep P j j′ (wb M) (mk M j) ne) d))
... | inj₂ nd = inj₁ (λ e → nd (h e))
  where
  h : j′ ≡ j → D M j′ (top tp (κJ j′) (rs (R P j) (wb M) (mk M j)))
  h e = subst (λ x → D M x (top tp (κJ x) (rs (R P j) (wb M) (mk M j)))) (sym e)
          (subst (D M j) (sym (rs-top (R P j))) (Dmk M j))
```

**编码与分离子.** `Code J`: 把 $\alpha:\mathbb N\to$ `Bool` 编进 $J$, 与全假的编码相等时 $\alpha$ 全假. 弱判定推出分离子 `SepC`; 加 "全假时编码相等" (外延的形状) 得 WLPO.

```agda
record Code (J : Set) : Set where
  field
    code   : (ℕ → Bool) → J
    code-F : ∀ α → code α ≡ code (λ _ → false) → ∀ n → α n ≡ false
open Code public

SepC : ∀ {J} → Code J → Set
SepC C = ∀ α → (∀ n → α n ≡ false) ⊎ ¬ (code C α ≡ code C (λ _ → false))

nnB : ∀ b → ¬ ¬ (b ≡ false) → b ≡ false
nnB false _ = refl
nnB true nn = ⊥-elim (nn (λ ()))

wdec→sepC : ∀ {J} (C : Code J) → WDec J → SepC C
wdec→sepC C Dc α with Dc (code C (λ _ → false)) (code C α)
... | inj₁ ne = inj₂ ne
... | inj₂ nn = inj₁ (λ n → nnB (α n) (λ k → nn (λ e → k (code-F C α e n))))

sepC→WLPO : ∀ {J} (C : Code J) → (∀ α → (∀ n → α n ≡ false) → code C α ≡ code C (λ _ → false)) → SepC C → WLPO
sepC→WLPO C ext S α with S α
... | inj₁ h = inj₁ h
... | inj₂ ne = inj₂ (λ h → ne (ext α h))
```

## §3 在 `SL` 上: 一切层的新种类 "升一份留别份" 推出分离子

`SL = sup LH FL`, 种类 `νL k = (k , inj₂ tt)` 的坐标是 `HB (Lv k)`, 顶是世界第 $k$ 个分量的第二分量. 顶坐标取 `FabLFReGen.GL` 的 (`tpL`), 基世界 `w₀ GL` 里每个新种类的顶是 $0$ (`refl`).

```agda
tpL : TopG SL
tpL = tpK GL

top-νL : ∀ k w → top tpL (νL k) w ≡ proj₂ (w k)
top-νL k w = refl

isZ : ∀ {T : KS} (x : HB T) → (x ≡ hz) ⊎ ¬ (x ≡ hz)
isZ hz = inj₁ refl
isZ (hs x) = inj₂ (λ ())
isZ (hl f) = inj₂ (λ ())
isZ (hΩ κ g) = inj₂ (λ ())

-- 标记: 坐标 1, 谓词 "不是 0"
mkNew : (J : Set) (ix : J → LH) → Mk tpL J (λ j → νL (ix j))
mkNew J ix = record
  { wb = w₀ GL ; mk = λ j → hs hz ; D = λ j e → ¬ (e ≡ hz)
  ; dD = λ j e → dz e ; Dmk = λ j () ; nD0 = λ j d → d refl }
  where
  dz : ∀ {T : KS} (e : HB T) → ¬ (e ≡ hz) ⊎ ¬ ¬ (e ≡ hz)
  dz e with isZ e
  ... | inj₁ z = inj₂ (λ d → d z)
  ... | inj₂ nz = inj₁ nz
```

层号的编码: $\alpha\mapsto$ `ll (n ↦ bit (α n))`, `bit true = ls lz`, `bit false = lz`.

```agda
bitL : Bool → LH
bitL true = ls lz
bitL false = lz

unll : LH → ℕ → LH
unll (ll f) = f
unll _ = λ _ → lz

bitL≡ : ∀ b → bitL b ≡ lz → b ≡ false
bitL≡ false _ = refl
bitL≡ true ()

codeL : Code LH
codeL = record
  { code = λ α → ll (λ n → bitL (α n))
  ; code-F = λ α e n → bitL≡ (α n) (cong (λ x → unll x n) e) }

pt-SL-sep : PtFam tpL LH νL → SepC codeL
pt-SL-sep P = wdec→sepC codeL (pt-wdec P (mkNew LH (λ k → k)))

-- 外延只对 ℕ → LH, 只作前提
FEL : Set
FEL = ∀ (f g : ℕ → LH) → (∀ n → f n ≡ g n) → f ≡ g

pt-SL→WLPO : FEL → PtFam tpL LH νL → WLPO
pt-SL→WLPO fe P = sepC→WLPO codeL (λ α h → cong ll (fe _ _ (λ n → cong bitL (h n)))) (pt-SL-sep P)
```

**分量上的 "留" 推出顶上的 "留".** `RsOwnIf.PW.Keep` 的形状 (别的分量逐字不动) 在 `SL` 上推出本篇的 `keep`.

```agda
keep-comp : ∀ {k} (R : RsK SL tpL (νL k)) → (∀ w v k′ → ¬ (k′ ≡ k) → rs R w v k′ ≡ w k′) →
  ∀ k′ w v → ¬ (k′ ≡ k) → top tpL (νL k′) (rs R w v) ≡ top tpL (νL k′) w
keep-comp R kp k′ w v ne = cong proj₂ (kp w v k′ ne)
```

**前提实例: 下标可判定的子族.** `lz` 与 `ls lz` 不含函数, 按构造子判定; 两份点更新各自满足 `RsK`, 合起来满足 `keep`. 所以 `PtFam` 与 `Mk` 的前提同时可满足; `pt-SL-sep` 否定的只是对**一切**层号 (含函数) 一致.

```agda
upd0 : Wd SL → HB (Lv lz) → Wd SL
upd0 w v lz = proj₁ (w lz) , v
upd0 w v (ls k) = w (ls k)
upd0 w v (ll f) = w (ll f)
upd0 w v (lΩ k g) = w (lΩ k g)

upd0≤ : ∀ w v → proj₂ (w lz) ⊲[ proj₁ (w lz) ] v → _≤w_ SL w (upd0 w v)
upd0≤ w v q lz = ≤w-rf (Lv lz) , q
upd0≤ w v q (ls k) = ≤w-rf (FL (ls k))
upd0≤ w v q (ll f) = ≤w-rf (FL (ll f))
upd0≤ w v q (lΩ k g) = ≤w-rf (FL (lΩ k g))

upd0Lg : ∀ w v → LgW SL w → LgB v → LgW SL (upd0 w v)
upd0Lg w v lw lv lz = proj₁ (lw lz) , lv
upd0Lg w v lw lv (ls k) = lw (ls k)
upd0Lg w v lw lv (ll f) = lw (ll f)
upd0Lg w v lw lv (lΩ k g) = lw (lΩ k g)

R0 : RsK SL tpL (νL lz)
R0 = record { rs = upd0 ; rs≤ = λ {w} {v} q → upd0≤ w v q ; rsLg = λ {w} {v} lw lv → upd0Lg w v lw lv ; rs-top = refl }

upd1 : Wd SL → HB (Lv (ls lz)) → Wd SL
upd1 w v lz = w lz
upd1 w v (ls lz) = proj₁ (w (ls lz)) , v
upd1 w v (ls (ls k)) = w (ls (ls k))
upd1 w v (ls (ll f)) = w (ls (ll f))
upd1 w v (ls (lΩ k g)) = w (ls (lΩ k g))
upd1 w v (ll f) = w (ll f)
upd1 w v (lΩ k g) = w (lΩ k g)

upd1≤ : ∀ w v → proj₂ (w (ls lz)) ⊲[ proj₁ (w (ls lz)) ] v → _≤w_ SL w (upd1 w v)
upd1≤ w v q lz = ≤w-rf (FL lz)
upd1≤ w v q (ls lz) = ≤w-rf (Lv (ls lz)) , q
upd1≤ w v q (ls (ls k)) = ≤w-rf (FL (ls (ls k)))
upd1≤ w v q (ls (ll f)) = ≤w-rf (FL (ls (ll f)))
upd1≤ w v q (ls (lΩ k g)) = ≤w-rf (FL (ls (lΩ k g)))
upd1≤ w v q (ll f) = ≤w-rf (FL (ll f))
upd1≤ w v q (lΩ k g) = ≤w-rf (FL (lΩ k g))

upd1Lg : ∀ w v → LgW SL w → LgB v → LgW SL (upd1 w v)
upd1Lg w v lw lv lz = lw lz
upd1Lg w v lw lv (ls lz) = proj₁ (lw (ls lz)) , lv
upd1Lg w v lw lv (ls (ls k)) = lw (ls (ls k))
upd1Lg w v lw lv (ls (ll f)) = lw (ls (ll f))
upd1Lg w v lw lv (ls (lΩ k g)) = lw (ls (lΩ k g))
upd1Lg w v lw lv (ll f) = lw (ll f)
upd1Lg w v lw lv (lΩ k g) = lw (lΩ k g)

R1 : RsK SL tpL (νL (ls lz))
R1 = record { rs = upd1 ; rs≤ = λ {w} {v} q → upd1≤ w v q ; rsLg = λ {w} {v} lw lv → upd1Lg w v lw lv ; rs-top = refl }

ixB : Bool → LH
ixB true = lz
ixB false = ls lz

RB : ∀ b → RsK SL tpL (νL (ixB b))
RB true = R0
RB false = R1

keepB : ∀ j j′ w v → ¬ (j′ ≡ j) → top tpL (νL (ixB j′)) (rs (RB j) w v) ≡ top tpL (νL (ixB j′)) w
keepB true true w v ne = ⊥-elim (ne refl)
keepB true false w v ne = refl
keepB false true w v ne = refl
keepB false false w v ne = ⊥-elim (ne refl)

ptB : PtFam tpL Bool (λ b → νL (ixB b))
ptB = record { R = RB ; keep = keepB }

-- 前提齐全时结论确实成立 (Bool 上相等可判定, 与 pt-wdec 一致)
ptB-wdec : WDec Bool
ptB-wdec = pt-wdec ptB (mkNew Bool ixB)
```

## §4 第五条判据作为筛子, 与盲

候选: 种类结构 `T`, 顶坐标, 每个种类给出精确升界或有损. 第五条判据 `NoPt`: 候选的升界不在任何编码族上构成 "升一份留别份". 与 §1 的四条不同, 它不是对一切候选成立的定理 (候选可以在编码族上精确, 那时 `pt-wdec` 给出分离子).

```agda
Fb : (T : KS) → TopG T → Set
Fb T tp = (κ : K T) → RsK T tp κ ⊎ ⊤

NoPt : ∀ {T} (tp : TopG T) → Fb T tp → Set₁
NoPt {T} tp fb = ∀ (J : Set) (κJ : J → K T) (C : Code J) (P : PtFam tp J κJ) → (∀ j → fb (κJ j) ≡ inj₁ (R P j)) → ⊥

Crit : ∀ (T : KS) (tp : TopG T) → Fb T tp → Set₁
Crit T tp fb = Crit₄ T × NoPt tp fb

-- 违反 NoPt 的候选给出分离子 (只要有标记)
¬NoPt→sep : ∀ {T tp J κJ} (C : Code J) → PtFam {T} tp J κJ → Mk tp J κJ → SepC C
¬NoPt→sep C P M = wdec→sepC C (pt-wdec P M)
```

**全有损的候选对一切 `T` 满足全部判据.**

```agda
null : ∀ {T} (tp : TopG T) → Fb T tp
null tp κ = inj₂ tt

null-noPt : ∀ {T} (tp : TopG T) → NoPt tp (null tp)
null-noPt tp J κJ C P eq with eq (code C (λ _ → false))
... | ()

null-crit : ∀ (T : KS) (tp : TopG T) → Crit T tp (null tp)
null-crit T tp = crit₄ T , null-noPt tp
```

**(a) `S⊥`: 没有种类.** 高度只有 $0$, 后继, $\mathbb N$-极限, 与第 0 层的可数树 `A` 双向保第一位置 (`frE⊥-⊲` 来自 `FabLFReGen`, `toE⊥-⊲` 在这里).

```agda
fb⊥ : Fb S⊥ top⊥
fb⊥ ()

blind⊥ : Crit S⊥ top⊥ fb⊥
blind⊥ = crit₄ S⊥ , (λ J κJ C P eq → κ⊥ (κJ (code C (λ _ → false))))
  where
  κ⊥ : K S⊥ → ⊥
  κ⊥ ()

toE⊥ : A → HB S⊥
toE⊥ azero = hz
toE⊥ (asuc a) = hs (toE⊥ a)
toE⊥ (alim f) = hl (λ n → toE⊥ (f n))

toE⊥-⊲ : ∀ {a b} → a ⊲ b → toE⊥ a ⊲[ tt ] toE⊥ b
toE⊥-⊲ C.self = hself
toE⊥-⊲ (C.suc q) = hsuc (toE⊥-⊲ q)
toE⊥-⊲ (C.lim n q) = hlim n (toE⊥-⊲ q)

-- S⊥ 的高度就是可数树: 两个方向都保第一位置, frE⊥ 保合法
low⊥ : (∀ {a b} {w : Wd S⊥} → a ⊲[ w ] b → frE⊥ a ⊲ frE⊥ b) × (∀ {a b} → a ⊲ b → toE⊥ a ⊲[ tt ] toE⊥ b) ×
       (∀ a → LgB {S⊥} a → Lg (frE⊥ a))
low⊥ = frE⊥-⊲ , toE⊥-⊲ , frE⊥-lg
```

**(b) `step S⊥`: 一个种类, 精确升界.** 它也满足 `NoPt`: 编码族的两个不同成员落在同一个种类上, "留" 与 `rs-top` 冲突 (`same-kind`).

```agda
T1 : KS
T1 = step S⊥

tp1 : TopG T1
tp1 = topStepG top⊥

R1x : RsK T1 tp1 (inj₂ tt)
R1x = record { rs = λ w v → proj₁ w , v ; rs≤ = λ q → tt , q ; rsLg = λ lw lv → proj₁ lw , lv ; rs-top = refl }

fb1 : Fb T1 tp1
fb1 (inj₁ ())
fb1 (inj₂ tt) = inj₁ R1x

same-kind : ∀ {T} (tp : TopG T) {κ} (R : RsK T tp κ) κ′ → κ′ ≡ κ → ∀ w v →
  top tp κ′ (rs R w v) ≡ top tp κ′ w → v ≡ top tp κ w
same-kind tp R κ′ refl w v h = trans (sym (rs-top R)) h

allEq1 : (κ κ′ : K T1) → κ′ ≡ κ
allEq1 (inj₁ ()) κ′
allEq1 (inj₂ tt) (inj₁ ())
allEq1 (inj₂ tt) (inj₂ tt) = refl

t≢f : ¬ (true ≡ false)
t≢f ()

one≢z : ∀ {T : KS} → ¬ (hs {T} hz ≡ hz)
one≢z ()

blind1 : Crit T1 tp1 fb1
blind1 = crit₄ T1 , np
  where
  -- 坐标类型里有两个不同的值, 不能都等于同一个顶
  two : ∀ κ (c : E T1 κ) → (∀ v → v ≡ c) → ⊥
  two (inj₁ ()) c h
  two (inj₂ tt) c h = one≢z (trans (h (hs hz)) (sym (h hz)))
  np : NoPt tp1 fb1
  np J κJ C P eq = two (κJ j0) (top tp1 (κJ j0) (tt , hz))
                     (λ v → same-kind tp1 (R P j0) (κJ j1) (allEq1 (κJ j0) (κJ j1)) (tt , hz) v (keep P j0 j1 (tt , hz) v ne))
    where
    j0 = code C (λ _ → false)
    j1 = code C (λ _ → true)
    ne : ¬ (j1 ≡ j0)
    ne e = t≢f (code-F C (λ _ → true) e 0)
```

**(c) `SL` 与今天的候选闭项的回灌.** `FabLFReGen.GL` 一切种类有损 (`fb-lossy`); 它的候选就是 `null tpL`. 它与 (a), (b) 一样满足全部判据, 但它的种类结构里每一站都有坐标为本层值的种类 (`coord-stage`).

```agda
blindSL : Crit SL tpL (null tpL)
blindSL = null-crit SL tpL

blind-pair : Crit S⊥ top⊥ fb⊥ × Crit T1 tp1 fb1 × Crit SL tpL (null tpL) ×
             (K S⊥ → ⊥) × (∀ n → E SL (νL (ofHB (tw n))) ≡ HB (Lv (ofHB (tw n))))
blind-pair = blind⊥ , blind1 , blindSL , (λ ()) , coord-stage
```

## §5 结论 (按档)

- **[定理]** **`crit₄`**: 今天的四条否定 (`no-retract`, `no-inflate`, `lv-not-self`/`no-total` 的一般形 `ns`, `no-slot-adj`) 写成 `T` 上的谓词, 对一切 `T` 成立.
- **[定理]** **`pt-wdec`** (一般形: "精确 + 留别份" + 标记 ⇒ 弱判定), `wdec→sepC`; **`pt-SL-sep`** (`SL` 的一切新种类); `keep-comp`. **[条件 `FEL`]** `pt-SL→WLPO`, `sepC→WLPO` (条件是 "全假时编码相等").
- **[定理, 前提实例]** `mkNew` (标记), `R0`, `R1`, **`ptB`** (可判定子族上 `PtFam` 成立), `ptB-wdec`.
- **[定理, 盲]** **`null-crit`** (对一切 `T`, 全有损满足全部五条), **`blind⊥`**, **`blind1`**, **`blindSL`**, **`blind-pair`**; `low⊥` (`S⊥` 的高度与 `A` 双向保第一位置).
- **[判断]** (1) 今天的否定性判据都是 "向下封闭" 的: 做得更少 (有损, 不共享, 没有种类) 永远不违反它们 (`null-crit`). 所以它们只能划出 "不能要求什么", 不能单独推出下一步定义; 下一步定义要一条**向上封闭**的正面判据 (例如 "某一族种类非有损", 或序数值下界), 而最自然的那条 ("一切层的新种类精确且留别份") 在 `SL` 上推出分离子 (`pt-SL-sep`). (2) 剩下未定的正面形状: 只精确不留 (`RsK` 对一切 `νL k`, 不要 `keep`; 未构造, 未否定), 带字面公共上界的有界升界. (3) 穷尽是判断.
