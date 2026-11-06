# 补四条正面判据, 否定一路 (三): 判据 (ii)–(iv) 约束框架, 不约束候选

> 不含记号. 入口 [NegTL2](NegTL2.lagda.md). 对着接口 [TL2If](TL2If.lagda.md) §2–§4 ("接口定稿 2026-11-05 21:12 (首次编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 只读导入构造一路上一对的 [TreeLangRaise](TreeLangRaise.lagda.md) (`Pos`, `supF`, `sup-bare→Sep`) 与上一对否定一路的 [NegTreeLangRaise](NegTreeLangRaise.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> **结果.**
>
> 1. **(ii) `Cross F H` 取决于 `H` (`diag-cross`, `diag-not-cross-id`, `blind-ii`, 定理).** 上一对的 "一起升" 框架 `supD` (`Lev` 的裸坐标积世界, 定义域只含同一成员, 有升界 `diag-raise` 且它把**一切**成员改成 $v$): 键按恒等读成高度 (`idH`) 时不满足 `Cross`; 但换一个合法的 `HKey` (`tagH`: 键 $k$ 读成 $\mathrm{h\Omega}\,(k,\ast)\,(\lambda\_.0)$, 单射, 有合法世界与合法高度, 前提非空 `tag-inst`), 两个不同的键永远没有合法的公共上界, `Cross` 只要求同键的对, `supD` 就满足. 接口让框架自己选 `HKey`, 所以 (ii) 单独不排除 "一起升".
> 2. **(iii) 序由框架自选 (`trivO`, `triv-grow`, `raise→up`, `triv-lowers`, 定理).** 平凡的序 (一切 $\le$ 都是 `⊤`) 是合法的 `OrdFrame`; 在它下面任一合法升界都满足 `Grow`, 都给出 `RaiseUp`; 上一对的 `any-lowers` 框架上的升界在 `RaiseUp` 里仍把读数从 $1$ 降到 $0$. 用真的序 (读数 $\mathbb N$ 的 $\le$, 世界逐点) 时 `Pos` 的升界满足 `Grow` (`grow-pos`).
> 3. **(ii)–(iv) 不提候选: 一个框架服务一切候选 (`all4`, `all-Lev`, `all-Pz`, `all-D`, 定理).** 把四条判据与上一对的 `LvCrit`, `LvUpper` 合成一个记录 `All4 R` (只是接口记录的合取). 任一满足 `LvCrit`, `LvUpper`, `OrdCrit` 的 `R` 都有 `All4 R`, 框架部分用同一组实例 (`Pos` 框架, 真的序, 恒等的键, 截面升界), 非平凡. 所以 `Lev`, 在第一位置上塌缩的 `LevP Pz` ([NegTL2Ord](NegTL2Ord.lagda.md) `blind-i`), 重数为 2 的 `LevD`, **同时满足全部判据**.
> 4. **把 (iii) 绑到候选自己的世界上, 就分开了 (`lev-own-up`, `pz-own-no-up`, `pn-own-no-up`, 定理).** 框架取候选第 1 层的世界, 读数取世界的高度分量, 序取种类结构自己的 `≤w` 与 `⊲`: `Lev` (与 `LevD`, 世界类型相同) 有 `RaiseUp`; `LevP Pz`, `LevP Pn` 没有. 这条 "自己的框架" 不在接口里.
> 5. **(iv) 截面升界的边界 (定理).**
>    - `adj-ok`: 相邻两级 (读数 `HB S₀` 与 `HB (step S₀)`, 后者的新种类坐标正是前者) 同在一个 `DFrame` 里, 有 `DRaise`. 上一对的 `raise-adj` 在 (iv) 下不再成立.
>    - `d-ret`, **`d-adj`**: 成员 $j$ 的定义域含自身对且有一个在 $j$ 处取 $v$ 的截面扩张时, 读数类型 $V_j$ 是世界的收缩; 所以若 $V_{j}$ 是 `HB S′`, 世界又收缩到 `S′` 的某个种类的坐标, 则矛盾 (`no-retract`). 世界必须比最高一级的读数大; 不能把世界放进低一级的坐标 (共享槽的形状, 对照 `NegSlotWall.slot-ret`).
>    - `d-nocopy`, `copies-split`: 截面升界禁止 "真拷贝" (同键, 读数相同的两个成员): 有一个分开它们的截面就矛盾. 同一个框架上 `Raise` 存在. 所以 (iv) 比上一对的 `Raise` 多要求同键成员各有自己的槽.
>    - `draise→raise`, `dsup-bare→Sep`: 读数不变时 `DRaise` 推出 `Raise`; 所以 `Lev` 的裸坐标积世界上的截面升界也推出分离子.
>
> **只否定什么.** 只否定推断 "(ii)–(iv) 加进来后, 判据确定了候选的定义 (或排除了 Ω-结点塌缩的候选, 或排除了一起升)". 接口里的框架与 `LvRule` 之间没有字段相连, 所以这些判据约束的是框架, 对候选是盲的 (`all4`). **不否定**: 构造一路的任何定理 (Cross 下的唯一性, `supD` 对恒等键不满足 Cross, 截面升界的实例等); 判据本身; 给接口加 "框架由候选的世界给出, 键由候选的高度给出, 序由种类结构给出" 之后的结果 (§4 只对第 1 层的一个分量做了检查).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegTL2Raise where

open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (H₀)
open import OCF.Align.HtTowerNeg using (no-retract; NatH; evᴴ)
open import OCF.Align.NegGenFoldUpd using (Sep)
open import OCF.Align.NegSlotPre using (_◁_; s; p; ps; ◁-rf)
open import OCF.Align.StallDxBdec using (bdec)
open import OCF.Align.TreeLangIf
open import OCF.Align.TreeLangLv using (LevR; LevC; LevU)
import OCF.Align.TreeLangRaise as TR
open import OCF.Align.NegTreeLangRaise using (supD; diag-raise; diag-moves; F₀; w1; j₀)
open import OCF.Align.TL2If
open import OCF.Align.NegTL2Pre using (stepP; Pz; Pn; ⊲hz; LevP; RP; CP; UP; RD; CD; UD; stepD)
open import OCF.Align.NegTL2Ord using (ordP; ordLev; ordD)
```

## §1 (ii): `Cross` 取决于框架自选的 `HKey`

`Stag`: 以键为下标的并, 每个分量是 `S₀`. 键 $k$ 读成 $\mathrm{h\Omega}\,(k,\ast)\,(\lambda\_.0)$; 读回 `untag` 是定义上的左逆, 所以单射不用函数外延.

```agda
Stag : KS
Stag = sup H₀ (λ _ → S₀)

hkT : H₀ → HB Stag
hkT k = hΩ (k , tt) (λ _ → hz)

untag : HB Stag → H₀
untag (hΩ (k , _) _) = k
untag _ = hz

tagH : HKey H₀
tagH = record { Sk = Stag ; hk = hkT ; hk-inj = λ e → cong untag e }

idH : HKey H₀
idH = record { Sk = S₀ ; hk = λ k → k ; hk-inj = λ e → e }

-- 第一位置是 hkT k 的, 要么就是它, 要么是 0
tagged⊲ : ∀ {w} {x y : HB Stag} {k} → x ⊲[ w ] y → y ≡ hkT k → (x ≡ y) ⊎ (x ≡ hz)
tagged⊲ hself e = inj₁ refl
tagged⊲ (hsuc q) ()
tagged⊲ (hlim n q) ()
tagged⊲ (hLim b q) refl = inj₂ (⊲hz q)

private
  side : ∀ {w} {k k′} → hkT k′ ⊲[ w ] hkT k → k′ ≡ k
  side r with tagged⊲ r refl
  ... | inj₁ e = cong untag e
  ... | inj₂ ()

-- 共界的两个带标签的键相等
tag-key : ∀ {ω Lb k k′} → LgW Stag ω → LgB Lb → hkT k ⊲[ ω ] Lb → hkT k′ ⊲[ ω ] Lb → k′ ≡ k
tag-key lω lL q q′ with cmpB q q′ lω lL
... | inj₁ r = side r
... | inj₂ r = sym (side r)

diag-cross : Cross supD tagH
diag-cross w lω lL j j′ q q′ = tag-key lω lL q q′

z≢1 : ∀ {S : KS} → ¬ (hz {S} ≡ hs hz)
z≢1 ()

1≢z : ∀ {S : KS} → ¬ (hs (hz {S}) ≡ hz)
1≢z ()

diag-not-cross-id : ¬ Cross supD idH
diag-not-cross-id c = z≢1 (c (λ x → TR.zW x) {azero} {hs hz} tt tt (hs hz) hz hself (hsuc hself))

-- 前提非空: 合法世界, 合法高度, 同键的对在共界之下
tag-inst : ∀ k → LgW Stag (λ _ → azero) × LgB (hkT k) × (hkT k ⊲[ (λ _ → azero) ] hkT k)
tag-inst k = (λ _ → tt) , ((λ _ _ _ _ → hself) , (λ _ _ → tt)) , hself

blind-ii : (Raise supD × Cross supD tagH) × ¬ Cross supD idH ×
           (∀ w j j′ v → obs supD j′ (rs diag-raise w j v) ≡ v)
blind-ii = (diag-raise , diag-cross) , diag-not-cross-id , diag-moves
```

## §2 (iii): 序由框架自选

```agda
trivO : ∀ F → OrdFrame F
trivO F = record { _≤W_ = λ _ _ → ⊤ ; ≤R = λ _ _ _ _ → ⊤ ; obs-mono = λ _ _ → tt }

triv-grow : ∀ F (R : Raise F) → Grow (trivO F) R
triv-grow F R v a = tt

raise→up : ∀ F (O : OrdFrame F) (R : Raise F) → Grow O R → RaiseUp F O
raise→up F O R g = record
  { rsU = λ w j v _ → rs R w j v
  ; setU = λ {w} {j} {j′} {v} a ev k → set R v ev k
  ; keepU = λ {w} {j} {j′} {v} a ev nk → keep R v ev nk
  ; growU = λ {w} {j} {v} a → g v a }

-- 上一对 any-lowers 的框架: 平凡的序下 RaiseUp 仍把 1 降到 0
triv-lowers : Σ (RaiseUp F₀ (trivO F₀)) (λ U →
  (obs F₀ j₀ (rsU U w1 j₀ 0 (λ _ _ _ → tt)) ≡ 0) × (obs F₀ j₀ w1 ≡ 1))
triv-lowers = U , setU U {w1} {j₀} {j₀} {0} (λ _ _ _ → tt) tt refl , refl
  where U = raise→up F₀ (trivO F₀) TR.posInst (triv-grow F₀ TR.posInst)
```

**真的序.** `Pos` 框架 (读数 $\mathbb N$): 世界逐点 $\le$, 读数 $\le$. 按判定的点更新满足 `Grow`.

```agda
module PosN = TR.Pos {S₀} {azero} {hz} tt tt ℕ
open PosN using (PJ; posF; rsP; posR)

pick-≤ : ∀ {X : Set} (d : X ⊎ ¬ X) {a b : ℕ} → (X → b ≤ a) → b ≤ TR.pick d a b
pick-≤ (inj₁ x) h = h x
pick-≤ (inj₂ _) h = ≤-refl

pick-yes : ∀ {X Y : Set} (d : X ⊎ ¬ X) {a b : Y} → X → TR.pick d a b ≡ a
pick-yes (inj₁ _) _ = refl
pick-yes (inj₂ n) x = ⊥-elim (n x)

pick-no : ∀ {X Y : Set} (d : X ⊎ ¬ X) {a b : Y} → ¬ X → TR.pick d a b ≡ b
pick-no (inj₁ x) n = ⊥-elim (n x)
pick-no (inj₂ _) _ = refl

ordN : OrdFrame posF
ordN = record
  { _≤W_ = λ w w′ → ∀ b q → w b q ≤ w′ b q
  ; ≤R = λ _ _ → _≤_
  ; obs-mono = λ j q → q (proj₁ j) (proj₂ j) }

grow-pos : Grow ordN posR
grow-pos {w} {a , p₀} v ab b q = pick-≤ (bdec q p₀ tt tt) (λ k → ab (b , q) tt k)

upPos : RaiseUp posF ordN
upPos = raise→up posF ordN posR grow-pos

idHK : HKey (HB S₀)
idHK = record { Sk = S₀ ; hk = λ k → k ; hk-inj = λ e → e }

crossPos : Cross posF idHK
crossPos _ _ _ _ _ _ _ = tt
```

**截面升界 (iv) 在同一框架上.**

```agda
DP : DFrame
DP = constD posF

drsP : Wᴰ DP → Jᴰ DP → ((j : Jᴰ DP) → Vᴰ DP j) → Wᴰ DP
drsP w (a , p₀) vs b q = TR.pick (bdec q p₀ tt tt) (vs (b , q)) (w b q)

dposR : DRaise DP
dposR = record
  { rsᴰ = drsP
  ; setᴰ = λ {w} {j} {j′} vs ev k → pick-yes (bdec (proj₂ j′) (proj₂ j) tt tt) k
  ; keepᴰ = λ {w} {j} {j′} vs ev nk → pick-no (bdec (proj₂ j′) (proj₂ j) tt tt) nk }

ordD′ : DOrd DP
ordD′ = record
  { _≤Wᴰ_ = λ w w′ → ∀ b q → w b q ≤ w′ b q
  ; ≤Rᴰ = λ _ _ → _≤_
  ; obs-monoᴰ = λ j q → q (proj₁ j) (proj₂ j) }

dgrow-pos : DGrow ordD′ dposR
dgrow-pos {w} {a , p₀} vs ab b q = pick-≤ (bdec q p₀ tt tt) (λ k → ab (b , q) tt k)

dcrossPos : DCross DP idHK
dcrossPos _ _ _ _ _ _ _ = tt
```

## §3 全部判据合起来: 一个框架服务一切候选

`All4 R`: 上一对的 `LvCrit`, `LvUpper`, 加本对的四条 (只是接口记录的合取, 不是新接口).

```agda
record All4 {S : KS} {B : Set} (R : LvRule S B) : Set₁ where
  field
    lc : LvCrit R
    lu : LvUpper R
    oc : OrdCrit R
    F  : RaiseFrame
    HF : HKey (Key F)
    OF : OrdFrame F
    ra : Raise F
    cr : Cross F HF
    gr : Grow OF ra
    ru : RaiseUp F OF
    D  : DFrame
    HD : HKey (Keyᴰ D)
    OD : DOrd D
    dr : DRaise D
    dc : DCross D HD
    dg : DGrow OD dr

all4 : ∀ {S : KS} {B : Set} (R : LvRule S B) → LvCrit R → LvUpper R → OrdCrit R → All4 R
all4 R c u o = record
  { lc = c ; lu = u ; oc = o
  ; F = posF ; HF = idHK ; OF = ordN ; ra = posR ; cr = crossPos ; gr = grow-pos ; ru = upPos
  ; D = DP ; HD = idHK ; OD = ordD′ ; dr = dposR ; dc = dcrossPos ; dg = dgrow-pos }

all-Lev : All4 (LevR {S₀})
all-Lev = all4 LevR LevC LevU ordLev

all-Pz : All4 (RP Pz {S₀})
all-Pz = all4 (RP Pz) (CP Pz) (UP Pz) (ordP Pz)

all-Pn : All4 (RP Pn {S₀})
all-Pn = all4 (RP Pn) (CP Pn) (UP Pn) (ordP Pn)

all-D : All4 (RD {S₀})
all-D = all4 RD CD UD ordD
```

## §4 把 (iii) 绑到候选自己的世界上

框架: 世界是候选第 1 层 (后继一步) 的世界, 一个成员, 读数是世界的高度分量, 序取种类结构自己的 `≤w` 与 `⊲`. `Lev` (`step`) 有 `RaiseUp`; `LevD` 的世界类型与 `step` 相同 (`levD-same-W`), 同一个证明; `LevP Pz`, `LevP Pn` 没有.

```agda
ownL : (S : KS) → RaiseFrame
ownL S = record { W = Wd (step S) ; J = ⊤ ; Key = ⊤ ; V = HB S ; key = λ _ → tt ; obs = λ _ w → proj₂ w ; Ev = λ _ _ _ → ⊤ }

ownLO : (S : KS) → OrdFrame (ownL S)
ownLO S = record { _≤W_ = _≤w_ (step S) ; ≤R = λ w _ a b → a ⊲[ proj₁ w ] b ; obs-mono = λ _ q → proj₂ q }

lev-own-up : ∀ S → RaiseUp (ownL S) (ownLO S)
lev-own-up S = record
  { rsU = λ w _ v _ → proj₁ w , v
  ; setU = λ _ _ _ → refl
  ; keepU = λ _ _ nk → ⊥-elim (nk refl)
  ; growU = λ {w} a → ≤w-rf S , a tt tt refl }

levD-same-W : ∀ S → Wd (stepD S) ≡ Wd (step S)
levD-same-W S = refl

ownP : ∀ {S : KS} (P : HB S → Set) → RaiseFrame
ownP {S} P = record { W = Wd (stepP S P) ; J = ⊤ ; Key = ⊤ ; V = HB S ; key = λ _ → tt
                    ; obs = λ _ w → proj₁ (proj₂ w) ; Ev = λ _ _ _ → ⊤ }

ownPO : ∀ {S : KS} (P : HB S → Set) → OrdFrame (ownP P)
ownPO {S} P = record { _≤W_ = _≤w_ (stepP S P) ; ≤R = λ w _ a b → a ⊲[ proj₁ w ] b ; obs-mono = λ _ q → proj₂ q }

pz-own-no-up : ¬ RaiseUp (ownP {S₀} (Pz S₀)) (ownPO (Pz S₀))
pz-own-no-up U = 1≢z (trans (sym st) (proj₂ (proj₂ r)))
  where
  w₀ : W (ownP {S₀} (Pz S₀))
  w₀ = azero , (hz , refl)
  ab : Above (ownPO {S₀} (Pz S₀)) w₀ tt (hs hz)
  ab _ _ _ = hsuc hself
  r = rsU U w₀ tt (hs hz) ab
  st : proj₁ (proj₂ r) ≡ hs hz
  st = setU U {w₀} {tt} {tt} {hs hz} ab tt refl

pn-own-no-up : ¬ RaiseUp (ownP {S₀} (Pn S₀)) (ownPO (Pn S₀))
pn-own-no-up U = subst NatH st (proj₂ (proj₂ r))
  where
  w₀ : W (ownP {S₀} (Pn S₀))
  w₀ = azero , (hz , tt)
  ab : Above (ownPO {S₀} (Pn S₀)) w₀ tt (hl evᴴ)
  ab _ _ _ = z⊲ᴮ (hl evᴴ)
  r = rsU U w₀ tt (hl evᴴ) ab
  st : proj₁ (proj₂ r) ≡ hl evᴴ
  st = setU U {w₀} {tt} {tt} {hl evᴴ} ab tt refl
```

## §5 (iv) 截面升界的边界

**相邻两级同在一个框架.** 成员 `true` 读 `HB S₀` (= `step S₀` 的新种类的坐标), 成员 `false` 读 `HB (step S₀)`. 上一对 `raise-adj` 说单一读数类型的框架装不下这一对; 截面升界装得下.

```agda
Fadj : DFrame
Fadj = record
  { Wᴰ = HB S₀ × HB (step S₀) ; Jᴰ = Bool ; Keyᴰ = Bool ; keyᴰ = λ b → b
  ; Vᴰ = λ { true → HB S₀ ; false → HB (step S₀) }
  ; obsᴰ = λ { true w → proj₁ w ; false w → proj₂ w }
  ; Evᴰ = λ _ _ _ → ⊤ }

rsAdj : Wᴰ Fadj → Jᴰ Fadj → ((j : Jᴰ Fadj) → Vᴰ Fadj j) → Wᴰ Fadj
rsAdj w true vs = vs true , proj₂ w
rsAdj w false vs = proj₁ w , vs false

setAdj : ∀ {w} j j′ vs → j′ ≡ j → obsᴰ Fadj j′ (rsAdj w j vs) ≡ vs j′
setAdj true .true vs refl = refl
setAdj false .false vs refl = refl

keepAdj : ∀ {w} j j′ vs → ¬ (j′ ≡ j) → obsᴰ Fadj j′ (rsAdj w j vs) ≡ obsᴰ Fadj j′ w
keepAdj true true vs nk = ⊥-elim (nk refl)
keepAdj true false vs nk = refl
keepAdj false true vs nk = refl
keepAdj false false vs nk = ⊥-elim (nk refl)

adj-ok : DRaise Fadj × (Vᴰ Fadj true ≡ E (step S₀) (inj₂ tt)) × (Vᴰ Fadj false ≡ HB (step S₀))
adj-ok = record
  { rsᴰ = rsAdj
  ; setᴰ = λ {w} {j} {j′} vs ev k → setAdj {w} j j′ vs k
  ; keepᴰ = λ {w} {j} {j′} vs ev nk → keepAdj {w} j j′ vs nk } , refl , refl
```

**读数是世界的收缩; 世界不能放进低一级的坐标.**

```agda
◁-tr : ∀ {X Y Z : Set} → X ◁ Y → Y ◁ Z → X ◁ Z
◁-tr R R′ = record { s = λ x → s R′ (s R x) ; p = λ z → p R (p R′ z)
                   ; ps = λ x → trans (cong (p R) (ps R′ (s R x))) (ps R x) }

≡◁′ : ∀ {X Y Z : Set} → X ≡ Y → Y ◁ Z → X ◁ Z
≡◁′ refl R = R

module _ {F : DFrame} (R : DRaise F) where
  dset-onto : ∀ {w j} → Evᴰ F w j j → ∀ vs → obsᴰ F j (rsᴰ R w j vs) ≡ vs j
  dset-onto ev vs = setᴰ R vs ev refl

  d-ret : ∀ {w j} → Evᴰ F w j j → (ext : Vᴰ F j → (j′ : Jᴰ F) → Vᴰ F j′) → (∀ v → ext v j ≡ v) → Vᴰ F j ◁ Wᴰ F
  d-ret {w} {j} ev ext pt = record
    { s = λ v → rsᴰ R w j (ext v) ; p = obsᴰ F j ; ps = λ v → trans (setᴰ R (ext v) ev refl) (pt v) }

  d-adj : ∀ {w j} → Evᴰ F w j j → (ext : Vᴰ F j → (j′ : Jᴰ F) → Vᴰ F j′) → (∀ v → ext v j ≡ v) →
          ∀ {S′ : KS} (κ : K S′) → Vᴰ F j ≡ HB S′ → Wᴰ F ◁ E S′ κ → ⊥
  d-adj ev ext pt κ eV WR = no-retract κ (s R′) (p R′) (ps R′)
    where R′ = ≡◁′ (sym eV) (◁-tr (d-ret ev ext pt) WR)

  -- 真拷贝 (同键, 读数相同) 与一个分开它们的截面不相容
  d-nocopy : ∀ {w j j₁ j₂} → Evᴰ F w j j₁ → Evᴰ F w j j₂ → keyᴰ F j₁ ≡ keyᴰ F j → keyᴰ F j₂ ≡ keyᴰ F j →
             (eV : Vᴰ F j₁ ≡ Vᴰ F j₂) → (∀ w′ → subst (λ X → X) eV (obsᴰ F j₁ w′) ≡ obsᴰ F j₂ w′) →
             (vs : (j′ : Jᴰ F) → Vᴰ F j′) → ¬ (subst (λ X → X) eV (vs j₁) ≡ vs j₂) → ⊥
  d-nocopy {w} {j} e₁ e₂ k₁ k₂ eV cp vs ne =
    ne (trans (cong (subst (λ X → X) eV) (sym (setᴰ R vs e₁ k₁))) (trans (cp _) (setᴰ R vs e₂ k₂)))
```

**前提实例.** `d-adj`: `Fadj` 的成员 `false` 给出 `DRaise`, 定义域含自身对, 扩张 (`extF`), $V\equiv$ `HB (step S₀)`; "世界收缩到低一级的坐标" 在另一个框架 (`F1`: 世界就是 `HB S₀` 一个槽) 上成立, 它也有 `DRaise`. 两半各自可满足, 合起来正是被否定的.

```agda
extF : Vᴰ Fadj false → (j′ : Jᴰ Fadj) → Vᴰ Fadj j′
extF v true = hz
extF v false = v

adj-half : (Vᴰ Fadj false ◁ Wᴰ Fadj)
adj-half = d-ret (proj₁ adj-ok) {hz , hz} {false} tt extF (λ v → refl)

F1 : DFrame
F1 = record { Wᴰ = HB S₀ ; Jᴰ = ⊤ ; Keyᴰ = ⊤ ; keyᴰ = λ _ → tt ; Vᴰ = λ _ → HB S₀ ; obsᴰ = λ _ w → w ; Evᴰ = λ _ _ _ → ⊤ }

slot-half : DRaise F1 × (Wᴰ F1 ◁ E (step S₀) (inj₂ tt))
slot-half = record { rsᴰ = λ w _ vs → vs tt ; setᴰ = λ vs ev k → refl ; keepᴰ = λ vs ev nk → ⊥-elim (nk refl) } , ◁-rf
```

**真拷贝: `Raise` 有, `DRaise` 没有.** 两个成员 (`Bool`), 同一个键, 同一个读数 (世界 $\mathbb N$ 本身).

```agda
Fc : RaiseFrame
Fc = record { W = ℕ ; J = Bool ; Key = ⊤ ; V = ℕ ; key = λ _ → tt ; obs = λ _ w → w ; Ev = λ _ _ _ → ⊤ }

copies-split : Raise Fc × ¬ DRaise (constD Fc)
copies-split =
  record { rs = λ w j v → v ; set = λ v ev k → refl ; keep = λ v ev nk → ⊥-elim (nk refl) } ,
  (λ R → d-nocopy R {0} {true} {true} {false} tt tt refl refl refl (λ _ → refl)
           (λ { true → 0 ; false → 1 }) (λ ()))
```

**读数不变时 `DRaise` 推出 `Raise`.** 所以 `Lev` 的裸坐标积世界上的截面升界也推出分离子.

```agda
draise→raise : ∀ {F : RaiseFrame} → DRaise (constD F) → Raise F
draise→raise D = record
  { rs = λ w j v → rsᴰ D w j (λ _ → v)
  ; set = λ v ev k → setᴰ D (λ _ → v) ev k
  ; keep = λ v ev nk → keepᴰ D (λ _ → v) ev nk }

dsup-bare→Sep : DRaise (constD TR.supF) → Sep
dsup-bare→Sep D = TR.sup-bare→Sep (draise→raise D)
```

## §6 结论 (按档)

- **[定理, 盲 (ii)]** `tagH` (合法 `HKey`), `tag-key`, **`diag-cross`**, `diag-not-cross-id`, `tag-inst` (前提非空), **`blind-ii`**.
- **[定理, 盲 (iii)]** `trivO`, `triv-grow`, `raise→up`, **`triv-lowers`**; 真的序下的实例 `ordN`, `grow-pos`, `upPos`.
- **[定理, 盲 (ii)–(iv) 对候选]** `All4`, **`all4`**, **`all-Lev`**, **`all-Pz`**, `all-Pn`, `all-D` (框架部分非平凡: `posR`, `grow-pos`, `dposR`, `dgrow-pos`).
- **[定理, 绑定后分开]** **`lev-own-up`**, `levD-same-W`, **`pz-own-no-up`**, **`pn-own-no-up`**.
- **[定理, 边界 (iv)]** **`adj-ok`** (相邻两级可同框), `dset-onto`, `d-ret`, **`d-adj`**, **`d-nocopy`**, **`copies-split`**, `draise→raise`, `dsup-bare→Sep`; 前提实例 `adj-half`, `slot-half`, `extF`.
- **[判断]** (1) 接口的 `RaiseFrame`/`DFrame`/`HKey`/`OrdFrame` 都由框架自选, 与 `LvRule` 之间没有字段相连; 所以 (ii)–(iv) 对候选是盲的, 这是结构上的 (`all4` 的证明不看 `R`). 要让它们约束候选, 需要一条 "框架由候选给出" 的字段 (世界取候选的世界, 键取候选的高度, 序取种类结构的 `≤w` 与 `⊲`); §4 显示这样绑定后, (iii) 就等于 "界够多" (`NegTL2Pre.Rich`), 排除 `LevP Pz`, `LevP Pn`, 不排除 `LevD`. (2) (iv) 把 `raise-adj` 换成了 `d-adj`: 跨级族的世界必须收缩到每一级的读数, 所以世界不能是低级坐标里的一个槽 (`NegSlotWall` 的共享槽正是被排除的形状); 积世界可以. (3) `d-nocopy`: 截面升界要求同键的成员各有槽; 当成员是 "同一高度的不同第一位置证明" 时, 世界必须按证明分槽, 不能按高度分槽 (判断: 本篇只在 `Fc` 上写成定理). (4) 穷尽是判断.
