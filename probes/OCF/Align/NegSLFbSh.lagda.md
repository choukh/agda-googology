# `SL` 上带证据的回灌, 否定一路 (二): "同级同界" 的世界证据

> 不含记号. 入口 [NegSLFb](NegSLFb.lagda.md). 本篇**不依赖**构造一路的接口 `SLFbIf` (接口定稿之前写的部分). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** 给 `SL` 的世界加证据 "所有同级种类同界", 让坐标是高度的种类也能回灌. `SL` 里种类 $\kappa$ 的级是 `rbl κ` (`LFReTy`), 坐标类型是 `HB (Lv (rbl κ))` (`E-rbl`, 随级变). 问: (a) 这份证据可满足还是推出矛盾? (b) 在这样的世界里 "一起抬高" 是否让读回失去信息? (c) 证据能否躲开 [NegSLFbSep](NegSLFbSep.lagda.md) 的分离子?
>
> **回答 (都是定理).**
>
> - **(a) 可满足, 而且就是 "以层号为下标的截面".** `ShL w`: 有截面 $G : (x : \mathrm{LH})\to$ `HB (Lv x)`, 每个种类 $\kappa$ 的顶 (经 `E-rbl` 读成 `HB (Lv (rbl κ))`) 等于 $G\,(\mathrm{rbl}\,\kappa)$. 对一切截面 $G$, 世界 `wG G` (每个 `step` 节点在级 $x$ 处放 $G\,x$) 满足它 (`shL-wG`); 基世界满足它 (`shL-wb`). 它与两两的写法 "级相同的两个种类, 顶沿级的路径运输后相等" 等价 (`sh→pair`, `pair→sh`). 坐标类型随级变不造成矛盾: 运输只沿 `rbl κ ≡ rbl κ′`, 由 J 消去.
> - **(b) 同级的种类分不开; 回灌一个就是回灌整级.** `νL k` (分量 $k$ 的新种类) 与 `cpL k` (分量 `ls k` 里级为 $k$ 的那份拷贝) 是可判定地不同的两个种类 (`νL≢cp`), 但在一切 `ShL` 世界里界相同 (`sh-νcp`). 任何在 `ShL` 上精确置 `νL s` 的 `RsInv` 同时精确置了一切级为 $s$ 的种类 (`sh-moves`, `sh-moves-cp`); 从 `νL s` 回灌与从 `cpL s` 回灌, 级 $s$ 上读出的顶相同 (`fed-indist`). 回灌的内容只是截面在 $s$ 处的一个值 (`inv→ext`: 每个这样的 `RsInv` 给出一个截面 $G'$ 使 $G'\,s\equiv v$).
> - **(c) 证据躲不开分离子, 而且让 "留别的分量" 直接矛盾.** 只要证据类含基世界, `NegSLFbSep.updP-sep` 照样适用 (`sh-upd-sep`). 更强: 在任一含于 `ShL` 的世界类上, 精确置 `νL s` 的 `RsInv` 与 "别的分量原样" (`KeepC`) 合起来推出 $\bot$, 对一切 $s$, 包括可判定的 $s=$ `lz` (`no-inv-keep`): 分量 `ls s` 里的拷贝 `cpL s` 必须跟着变.
> - **前提实例.** 在可判定的层号 `lz` 上, 带证据 "世界是某截面的 `wG`" (`Pw`) 的 `RsInv` 存在 (`rsLz`, 构造: 截面在 `lz` 处换成 $v$), 它把每个分量里级为 `lz` 的拷贝都改了 (`rsLz-moves`). `KeepC` 由不动的操作满足 (`stayKeep`).
>
> **只否定什么.** 只否定: `ShL` 类世界上 "精确置一个 + 别的分量原样" (`no-inv-keep`, $\bot$); 含基世界的证据类上 "升 `νL s` + 不升别的级的新种类" ($s$ 的头是 `lΩ` 时, 分离子). **不否定**: `ShL` 本身 (可满足); `ShL` 上的 `RsInv` (在 `lz` 有实例; 在含函数的层号上**未写出, 未否定**, 卡点见 §5 的判断); "一起抬高" (只是读回分不开同级的种类, 这是盲, 不是矛盾).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSLFbSh where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy
open import OCF.Align.FabLFReGen using (GL; topLv; w₀Lv)
open import OCF.Align.GenFoldIf using (TopG; top; tpK; w₀)
open import OCF.Align.RsOwnIf using (RsInv; rsᴵ; rsᴵ-P; rsᴵ≤; rsᴵLg; rsᴵ-top)
open import OCF.Align.NegSLFbSep using (wb; SepAt; PtUpdP; updP-sep)
```

## §1 截面与它的世界

```agda
Sec : Set
Sec = (x : LH) → HB (Lv x)

wLv : Sec → (k : LH) → Wd (Lv k)
wLv G lz = tt
wLv G (ls x) = wLv G x , G x
wLv G (ll f) n = wLv G (f n)
wLv G (lΩ k g) (inj₁ _) = wLv G k , G k
wLv G (lΩ k g) (inj₂ c) = wLv G (g c)

wG : Sec → Wd SL
wG G k = wLv G k , G k

tpL : TopG SL
tpL = tpK GL

-- 种类的顶, 经 E-rbl 读成它的级的值
top′ : (κ : K SL) → Wd SL → HB (Lv (rbl κ))
top′ κ w = subst (λ X → X) (E-rbl κ) (top tpL κ w)
```

**截面世界的顶就是截面.** 对 $(k,\kappa)$ 递归, 每一步 `refl` 或递归调用 (与 `FabLFReGen.top-base-Lv` 同形).

```agda
top-wLv : ∀ G k κ → subst (λ X → X) (E-lvl k κ) (top (topLv k) κ (wLv G k)) ≡ G (lvl k κ)
top-wLv G lz ()
top-wLv G (ls x) (inj₁ κ) = top-wLv G x κ
top-wLv G (ls x) (inj₂ _) = refl
top-wLv G (ll f) (n , κ) = top-wLv G (f n) κ
top-wLv G (lΩ k g) (inj₁ _ , inj₁ κ) = top-wLv G k κ
top-wLv G (lΩ k g) (inj₁ _ , inj₂ _) = refl
top-wLv G (lΩ k g) (inj₂ c , κ) = top-wLv G (g c) κ

top-wG : ∀ G κ → top′ κ (wG G) ≡ G (rbl κ)
top-wG G (k , inj₂ _) = refl
top-wG G (k , inj₁ κ) = top-wLv G k κ

top-w₀Lv : ∀ k κ → subst (λ X → X) (E-lvl k κ) (top (topLv k) κ (w₀Lv k)) ≡ hz
top-w₀Lv lz ()
top-w₀Lv (ls x) (inj₁ κ) = top-w₀Lv x κ
top-w₀Lv (ls x) (inj₂ _) = refl
top-w₀Lv (ll f) (n , κ) = top-w₀Lv (f n) κ
top-w₀Lv (lΩ k g) (inj₁ _ , inj₁ κ) = top-w₀Lv k κ
top-w₀Lv (lΩ k g) (inj₁ _ , inj₂ _) = refl
top-w₀Lv (lΩ k g) (inj₂ c , κ) = top-w₀Lv (g c) κ

top-wb : ∀ κ → top′ κ wb ≡ hz
top-wb (k , inj₂ _) = refl
top-wb (k , inj₁ κ) = top-w₀Lv k κ
```

## §2 "同级同界" 的证据: 可满足, 两种写法等价

```agda
ShL : Wd SL → Set
ShL w = Σ Sec (λ G → ∀ κ → top′ κ w ≡ G (rbl κ))

shL-wG : ∀ G → ShL (wG G)
shL-wG G = G , top-wG G

shL-wb : ShL wb
shL-wb = (λ _ → hz) , top-wb

-- 两两的写法: 级相同的两个种类, 顶沿级的路径运输后相等
ShPair : Wd SL → Set
ShPair w = ∀ κ κ′ (e : rbl κ ≡ rbl κ′) → subst (λ x → HB (Lv x)) e (top′ κ w) ≡ top′ κ′ w

substSec : ∀ (G : Sec) {x y} (e : x ≡ y) → subst (λ z → HB (Lv z)) e (G x) ≡ G y
substSec G refl = refl

sh→pair : ∀ {w} → ShL w → ShPair w
sh→pair (G , h) κ κ′ e =
  trans (cong (subst (λ x → HB (Lv x)) e) (h κ)) (trans (substSec G e) (sym (h κ′)))

pair→sh : ∀ {w} → ShPair w → ShL w
pair→sh {w} P = (λ x → top′ (νL x) w) , (λ κ → P κ (νL (rbl κ)) refl)
```

## §3 同级的种类分不开

`cpL k`: 分量 `ls k` (种类结构 `step (Lv (ls k)) = step (step (Lv k))`) 的旧种类里, `step (Lv k)` 的新种类; 级是 $k$, 坐标字面是 `HB (Lv k)`. 它与 `νL k` 是不同的种类 (第一分量 `ls k` 与 $k$ 不同, `ls` 没有不动点), 判定它们不同不需要比较含函数的东西.

```agda
cpL : LH → K SL
cpL k = ls k , inj₁ (inj₂ tt)

rbl-cp : ∀ k → rbl (cpL k) ≡ k
rbl-cp k = refl

ls-nofix : ∀ y → ¬ (ls y ≡ y)
ls-nofix lz ()
ls-nofix (ls y) e = ls-nofix y (cong unls e)
  where unls : LH → LH
        unls (ls z) = z
        unls z = z
ls-nofix (ll f) ()
ls-nofix (lΩ k g) ()

νL≢cp : ∀ k → ¬ (νL k ≡ cpL k)
νL≢cp k e = ls-nofix k (sym (cong proj₁ e))

sh-νcp : ∀ {w} → ShL w → ∀ k → top tpL (νL k) w ≡ top tpL (cpL k) w
sh-νcp (G , h) k = trans (h (νL k)) (sym (h (cpL k)))
```

**回灌一个就是回灌整级.** `RsInv SL P tpL (νL s)` (接口 `RsOwnIf`: 升界读证据, 保证据, `rs-top` 精确) 在一切含于 `ShL` 的证据类上, 同时精确置了每个级为 $s$ 的种类.

```agda
module _ {P : Wd SL → Set} (sh : ∀ {w} → P w → ShL w) where

  sh-moves-cp : ∀ s (R : RsInv SL P tpL (νL s)) {w} (p : P w) v → top tpL (cpL s) (rsᴵ R w p v) ≡ v
  sh-moves-cp s R p v = trans (sym (sh-νcp (sh (rsᴵ-P R p v)) s)) (rsᴵ-top R p)

  sh-moves : ∀ s (R : RsInv SL P tpL (νL s)) {w} (p : P w) v κ (e : s ≡ rbl κ) →
    subst (λ x → HB (Lv x)) e v ≡ top′ κ (rsᴵ R w p v)
  sh-moves s R {w} p v κ e =
    trans (cong (subst (λ x → HB (Lv x)) e) (sym (rsᴵ-top R p))) (sh→pair (sh (rsᴵ-P R p v)) (νL s) κ e)

  -- 从 νL s 回灌与从 cpL s 回灌, 级 s 上的一切顶相同
  fed-indist : ∀ s (R₁ : RsInv SL P tpL (νL s)) (R₂ : RsInv SL P tpL (cpL s)) {w} (p : P w) v κ (e : s ≡ rbl κ) →
    top′ κ (rsᴵ R₁ w p v) ≡ top′ κ (rsᴵ R₂ w p v)
  fed-indist s R₁ R₂ {w} p v κ e =
    trans (sym (sh-moves s R₁ p v κ e))
      (trans (cong (subst (λ x → HB (Lv x)) e) (sym (rsᴵ-top R₂ p)))
        (sh→pair (sh (rsᴵ-P R₂ p v)) (cpL s) κ e))

  -- 回灌的内容: 一个截面, 在 s 处是 v
  inv→ext : ∀ s (R : RsInv SL P tpL (νL s)) {w} (p : P w) v → Σ Sec (λ G′ → G′ s ≡ v)
  inv→ext s R p v = proj₁ (sh (rsᴵ-P R p v)) , trans (sym (proj₂ (sh (rsᴵ-P R p v)) (νL s))) (rsᴵ-top R p)
```

## §4 边界: "别的分量原样" 在同界世界里是 $\bot$; 留别的级仍是分离子

`KeepC R`: 升界之后, 下标不同的分量原样 (接口 `RsOwnIf.PW.Keep` 的形状, 对 `SL`).

```agda
KeepC : ∀ {P s} → RsInv SL P tpL (νL s) → Set
KeepC {P} {s} R = ∀ w (p : P w) v k → ¬ (k ≡ s) → rsᴵ R w p v k ≡ w k

hs-nofix : ∀ {S : KS} (x : HB S) → ¬ (hs x ≡ x)
hs-nofix hz ()
hs-nofix (hs x) e = hs-nofix x (cong unhs e)
  where unhs : HB _ → HB _
        unhs (hs z) = z
        unhs z = z
hs-nofix (hl f) ()
hs-nofix (hΩ κ g) ()

no-inv-keep : ∀ s {P : Wd SL → Set} → (∀ {w} → P w → ShL w) → ∀ {w₁} → P w₁ →
  (R : RsInv SL P tpL (νL s)) → KeepC R → ⊥
no-inv-keep s {P} sh {w₁} p₁ R kp = hs-nofix t (trans (sym e₁) (trans e₂ (sym e₃)))
  where
  t : HB (Lv s)
  t = top tpL (νL s) w₁
  W = rsᴵ R w₁ p₁ (hs t)
  -- cpL s 在新世界里的顶是 hs t (同界)
  e₁ : top tpL (cpL s) W ≡ hs t
  e₁ = sh-moves-cp sh s R p₁ (hs t)
  -- 分量 ls s 原样, 所以 cpL s 的顶不变
  e₂ : top tpL (cpL s) W ≡ top tpL (cpL s) w₁
  e₂ = cong (λ c → top (topLv (ls s)) (inj₂ tt) (proj₁ c)) (kp w₁ p₁ (hs t) (ls s) (ls-nofix s))
  -- 旧世界里 cpL s 与 νL s 同界
  e₃ : t ≡ top tpL (cpL s) w₁
  e₃ = sh-νcp (sh p₁) s
```

**留别的级, 证据躲不开分离子.** 基世界在 `ShL` 里, 所以 `NegSLFbSep.updP-sep` 直接适用.

```agda
sh-upd-sep : ∀ k g → PtUpdP (lΩ k g) ShL → SepAt k g
sh-upd-sep k g U = updP-sep k g shL-wb U
```

## §5 前提实例: 可判定层号 `lz` 上带截面证据的 `RsInv`

`Pw w`: $w$ 字面是某个截面的世界. `setLz G v`: 截面在 `lz` 处换成 $v$, 别处不变 (按模式, 不判定含函数的东西). 升界 = `wG (setLz G v)`.

```agda
Pw : Wd SL → Set
Pw w = Σ Sec (λ G → w ≡ wG G)

Pw→ShL : ∀ {w} → Pw w → ShL w
Pw→ShL (G , e) = subst ShL (sym e) (shL-wG G)

setLz : Sec → HB (Lv lz) → Sec
setLz G v lz = v
setLz G v (ls x) = G (ls x)
setLz G v (ll f) = G (ll f)
setLz G v (lΩ k g) = G (lΩ k g)

module LzLe (G : Sec) (v : HB (Lv lz)) (pre : G lz ⊲[ tt ] v) where
  G′ = setLz G v

  top-le : ∀ x → G x ⊲[ wLv G′ x ] G′ x
  top-le lz = pre
  top-le (ls x) = hself
  top-le (ll f) = hself
  top-le (lΩ k g) = hself

  le-wLv : ∀ k → _≤w_ (Lv k) (wLv G k) (wLv G′ k)
  le-wLv lz = tt
  le-wLv (ls x) = le-wLv x , top-le x
  le-wLv (ll f) n = le-wLv (f n)
  le-wLv (lΩ k g) (inj₁ _) = le-wLv k , top-le k
  le-wLv (lΩ k g) (inj₂ c) = le-wLv (g c)

  le-wG : _≤w_ SL (wG G) (wG G′)
  le-wG k = le-wLv k , top-le k

lg-wLv : ∀ (G : Sec) → (∀ x → LgB (G x)) → ∀ k → LgW (Lv k) (wLv G k)
lg-wLv G L lz = tt
lg-wLv G L (ls x) = lg-wLv G L x , L x
lg-wLv G L (ll f) n = lg-wLv G L (f n)
lg-wLv G L (lΩ k g) (inj₁ _) = lg-wLv G L k , L k
lg-wLv G L (lΩ k g) (inj₂ c) = lg-wLv G L (g c)

lgSet : ∀ (G : Sec) v → LgW SL (wG G) → LgB v → ∀ x → LgB (setLz G v x)
lgSet G v lw lv lz = lv
lgSet G v lw lv (ls x) = proj₂ (lw (ls x))
lgSet G v lw lv (ll f) = proj₂ (lw (ll f))
lgSet G v lw lv (lΩ k g) = proj₂ (lw (lΩ k g))

rsLz : RsInv SL Pw tpL (νL lz)
rsLz = record
  { rsᴵ = λ w p v → wG (setLz (proj₁ p) v)
  ; rsᴵ-P = λ p v → setLz (proj₁ p) v , refl
  ; rsᴵ≤ = λ {w} {v} p pre → le w p v pre
  ; rsᴵLg = λ {w} {v} p lw lv → lg w p v lw lv
  ; rsᴵ-top = λ p → refl }
  where
  le : ∀ w (p : Pw w) v → Pr SL (νL lz) w (top tpL (νL lz) w) v → _≤w_ SL w (wG (setLz (proj₁ p) v))
  le w (G , refl) v pre = LzLe.le-wG G v pre
  lg : ∀ w (p : Pw w) v → LgW SL w → LgB v → LgW SL (wG (setLz (proj₁ p) v))
  lg w (G , refl) v lw lv k = lg-wLv (setLz G v) (lgSet G v lw lv) k , lgSet G v lw lv k

-- 前提实例: Pw 含于 ShL, 且非空
pw-inst : Pw (wG (λ _ → hz))
pw-inst = (λ _ → hz) , refl

-- 一起抬高: rsLz 改了分量 ls lz 里级为 lz 的拷贝
rsLz-moves : ∀ G v → top tpL (cpL lz) (rsᴵ rsLz (wG G) (G , refl) v) ≡ v
rsLz-moves G v = refl

-- KeepC 单独可满足: 不动的操作 (它不满足 rs-top)
stayKeep : ∀ (w : Wd SL) k → w k ≡ w k
stayKeep w k = refl

-- 推论 (检查前提可满足): rsLz 与 KeepC 不相容
rsLz-no-keep : KeepC rsLz → ⊥
rsLz-no-keep kp = no-inv-keep lz Pw→ShL pw-inst rsLz kp
```

**判断 (未否定, 卡点).** 在含函数的层号 $s$ (第 $n\ge2$ 站) 上, `ShL` 类世界的 `RsInv` 等于造截面的延拓: 给截面 $G$ 与 $v$ : `HB (Lv s)` ($G\,s\lhd v$), 造截面 $G'$ 使 $G'\,s\equiv v$, 且世界变大 (`inv→ext` 是这一方向的定理; 反方向在 `lz` 上就是 `rsLz`). `setLz` 的写法要对 $x$ 判定 "是不是 $s$", 在含函数的 $s$ 上就是 `NegSLFbSep` 的分离子. 不判定的写法要一个对一切 $x$ 的 $G'\,x$, 在 $s$ 处字面等于任意给定的 $v$: 一条候选是逐结构的搬运 `HB (Lv s) → HB (Lv x)` (种类按层号的形状对应, 坐标反向搬运), 它在 $x\equiv s$ 时把 $v$ 搬回 $v$ 要在 $\Omega$-节点上用函数外延 (分支 $h$ 与 $h\circ\mathrm{back}$ 逐点相等); 而且 "在别的级上不低于 $G\,x$ 又在 $s$ 处恰为 $v$" 是一个并, `HtTowerNeg.no-joinᴮ` 说一般没有字面的并. 两件都没有写成定理, 不算否定.

## §6 结论 (按档)

- **[定理]** `top-wLv`, `top-wG`, `top-w₀Lv`, `top-wb`; **`shL-wG`**, **`shL-wb`** (同级同界的证据对一切截面可满足); **`sh→pair`**, **`pair→sh`** (两种写法等价); `rbl-cp`, `ls-nofix`, `νL≢cp`, **`sh-νcp`** (同级的不同种类同界).
- **[定理, 盲]** **`sh-moves`**, **`sh-moves-cp`** (精确置 `νL s` 就精确置了整级), **`fed-indist`** (回灌哪个同级种类, 读出的级 $s$ 的顶相同), **`inv→ext`** (回灌的内容是一个截面值).
- **[定理, 否定]** **`no-inv-keep`** (含于 `ShL` 的证据类上, 精确置 `νL s` + 别的分量原样 ⇒ $\bot$, 对一切 $s$); **`sh-upd-sep`** ($s$ 的头是 `lΩ` 时, `ShL` 上留别的级的新种类 ⇒ 分离子).
- **[定理, 前提实例]** `Pw`, `Pw→ShL`, `pw-inst`, **`rsLz`** (`lz` 上带截面证据的 `RsInv`, 构造), `rsLz-moves`, `stayKeep`, `rsLz-no-keep`.
- **[判断]** §5 末: 含函数的层号上 `ShL` 的 `RsInv` 未写出, 卡在截面延拓; 未否定.
