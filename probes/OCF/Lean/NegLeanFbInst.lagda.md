# 级回灌参数 `Fb`, 否定一路 (四): 对构造一路实例 `TF` 的检查

> 不含记号. 入口 [NegLeanFb](NegLeanFb.lagda.md). 只读导入构造一路的 [LeanFbSt](LeanFbSt.lagda.md), [LeanFbSlot](LeanFbSlot.lagda.md), [LeanFbRd](LeanFbRd.lagda.md), [LeanFbTm](LeanFbTm.lagda.md) (21:3x 的编译版), 不改它们. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延.
>
> **三个检查.**
>
> 1. **回灌是否真被执行.** 构造一路的 `LeanFbShape.exec-head` 是一步的局部定理 (`RunC` 在头种类上走到 `RKa`), 与 [NegLeanFbPre](NegLeanFbPre.lagda.md) 的 `exec-old` 同档; `LeanFbTest` 的 `a1`, `a2` 是有限测试, 而且在那两个深度上 `TF` 与全有损的 `TL` 的指纹**相同**, 没有分辨力. 本篇给闭项本身的定理: **`exec-TF0`, `exec-TF1`, `exec-TF2`** (`refl`): 沿一条显式路径 (`nav`) 取 `ΨF` (闭项 `TF = sum hz ΨF` 的第 0 层数据) 的子项, 字面地等于 `RKa _ (fb (νS n)) …`, $n=0,1,2$; 而 `fb (νS n)` 是 `inj₁ (toFb …)` (`fb-head0`, `fb-head1`, `fb-head2`). 所以三种回灌 (`slotUp 0` + `sum`, `slotUp 1` + `rdX newAK`, `headUp 2` + `rdX (find0 …)`) 都出现在闭项的计算里.
> 2. **新种类的回灌 (底种类 `bkS`) 不执行.** **`TF-old`** (定理): `TF` 的折叠的输入与每个目标上的输出里, 闭包结点都是旧种类 (`ΛF = up Λs` 只有旧种类, [NegLeanFbKD](NegLeanFbKD.lagda.md) 的 `kd-Run`). 读法 (一行, 同 `NegLeanFbKD`): 新种类的回灌 `κc₁` 与它用的 `rd₁`, `bkS` 在 `TF` 上不执行. 构造一路 `bk-merge` 说底种类 `νS 0` 与级 0 的拷贝同槽; 底种类作为 **`BotK`** (新种类回灌的读回目标) 在 `TF` 里闲着; 作为 `SLs` 的种类 `νS 0` 它是级 0 槽的成员, 由 `feed0` 回灌.
> 3. **剩下多少有损种类; 共享界是否退化.**
>    - **`lossy-hl`** (定理, 对一切 $f$): 第 3 站里坐标 $1+\mathrm{hl}\,f$ 的分量的新种类 (级是 `kc (hl f)` = `ll …`, 含函数) 有损. 这一族以 `HB S⊥` 的 `hl` 为下标, 两两级不同 (见 `NegLeanFbPre.kc-hl`); 与构造一路的 `lv2-lossy`, `cp2-lossy` 合起来: 有损种类不止有限个, 也包括含函数下标的整族.
>    - **`lossy-hl-target`** (定理): 这些种类都是 $\Lambda_F$ 在某个从基世界升上来的合法世界里的目标层的头 (在第 4 站的坐标 $c$ = 一个以它为头的高度处). 所以不是 "不出现所以无所谓": 它们出现在层里, 回灌行在它们上面是有损的那一行 (`exec-old`). 这一步之后的 "在 `TF` 的计算里被走到" 未证 (判断: 要走到, 第 3 站头的界里要有这个种类的 Ω-结点; 下一条说明经回灌升上来的界里没有).
>    - **`rdX-one-kind`** (定理, 对一切 $X$, `AK0 a`): 级 1 式读回 `rdX a` 的输出里一切 $\Omega$-结点的种类都是 `aK a`. 对第 $n\ge2$ 站的头, `a = find0 (st n)` 是 `Lv (st n)` 里一个级为 `lz` 的种类 (坐标读成 `HB S⊥`): **头 $n\ge2$ 的界只按一个级 0 种类的 Ω-结点增长**. 读回不在自己的级上 (构造一路已在 `LeanFbRd` 头说明), 这里是定理.
>    - **共享界**: 不退化的一面 (每次调用确实给每个成员加读回, `rz-top`, 构造一路 `cp1-moves`, `head1-moves`); 退化的一面是 [NegLeanFbBlind](NegLeanFbBlind.lagda.md) 的 `same-iter`: 同一个 `slotUp j` 的成员在读数相同的世界里经它的任意次升界后读数仍相同. 本篇加 **`slot0-start`**, **`slot1-start`** (定理): 基世界里 `slotUp 0`, `slotUp 1` 的一切成员读数都是 $0$ (前提实例), 所以只经各自的槽升界时, 同级拷贝 (含第 3 站里第 1 站头的拷贝 `cp1`) 与头**读数恒等**.
>
> **只说什么.** `exec-TF*` 说回灌行在闭项的计算里出现 (有被执行的分支); 不说回灌升出的界让值变大 (值的比较没做). `TF-old` 只说新种类的回灌不执行. `lossy-hl*`, `rdX-one-kind` 是对实例的形状定理, 不否定计划, 不否定路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLeanFbInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanTTree
open import OCF.Lean.LeanFbIf
open import OCF.Lean.LeanFbSt renaming (st to stL)
open import OCF.Lean.LeanFbSlot
open import OCF.Lean.LeanFbRd
open import OCF.Lean.LeanFbTm using (bkS; plan; toFb; fb; Act; ΨF; feed0; feed1; feedH)
import OCF.Lean.LeanTFold as Fold
open import OCF.Lean.LeanT using (Old; old-up)
open import OCF.Lean.NegLeanFbPre using (AllK; allK-⊲)
open import OCF.Lean.NegLeanFbKD using (OldK; old→all; module KDM; module KDRun)
open import OCF.Lean.NegLeanFbBlind using (rzN; same-iter)
open Tree SLs
open FoldTy SLs ΛF
open Fold SLs bkS ΛF lΛF oneF fb
```

## §1 回灌在闭项的计算里出现

`nav`: 沿路径取第 0 层数据的子项 (`dL`, `dR`: `⨾` 的左右; `dN n`: `nl` 的第 $n$ 项; 不匹配时取 $0$).

```agda
data Dir : Set where
  dL dR : Dir
  dN : ℕ → Dir

nav : ∀ {W} → List Dir → D hz W → D hz W
nav [] x = x
nav (dL ∷ p) (x ⨾ y) = nav p x
nav (dR ∷ p) (x ⨾ y) = nav p y
nav (dN n ∷ p) (nl d) = nav p (d n)
nav (_ ∷ p) _ = n0

fb-head0 : fb (νS 0) ≡ inj₁ (toFb (feed0 ((0 , inj₁ refl) , refl)))
fb-head0 = refl

fb-head1 : fb (νS 1) ≡ inj₁ (toFb (feed1 ((1 , inj₁ refl) , refl)))
fb-head1 = refl

fb-head2 : Σ (AK0 (Lv (stL 2))) (λ a → fb (νS 2) ≡ inj₁ (toFb (feedH 2 a)))
fb-head2 = _ , refl
```

**路径.** `ΨF = n1 ⨾ out`; `out` 的右半是 $\Omega_{\Lambda_F}$ 的 $\mathbb N$-极限部分; 第 $n+1$ 项是结点 (第 $n$ 站的层 `up (1 ⊞ tws (n+1))`), 在第 0 层目标上上升 (`rise`); 链的第 0 项折叠状态在这一层上的数据, 其中有 "当前状态的一步" 发出的 $\Omega_k$, 它的头是旧种类 `inj₁ (νS n)`, 走到 `RKa`.

```agda
exec-TF0 : (Tq : Tg _ hz (w₀ L₀)) → nav (dR ∷ dR ∷ dN 1 ∷ dN 0 ∷ dL ∷ dR ∷ dN 0 ∷ dL ∷ dR ∷ []) ΨF ≡ RKa _ (fb (νS 0)) _ _ _ _ _ _ _ Tq
exec-TF0 Tq = refl

exec-TF1 : (Tq : Tg _ hz (w₀ L₀)) → nav (dR ∷ dR ∷ dN 2 ∷ dN 0 ∷ dL ∷ dL ∷ dR ∷ dN 0 ∷ dL ∷ dR ∷ []) ΨF ≡ RKa _ (fb (νS 1)) _ _ _ _ _ _ _ Tq
exec-TF1 Tq = refl

exec-TF2 : (Tq : Tg _ hz (w₀ L₀)) → nav (dR ∷ dR ∷ dN 3 ∷ dN 0 ∷ dL ∷ dL ∷ dL ∷ dR ∷ dN 0 ∷ dL ∷ dR ∷ []) ΨF ≡ RKa _ (fb (νS 2)) _ _ _ _ _ _ _ Tq
exec-TF2 Tq = refl
```

**对照: 同一路径在全有损的折叠上.** 同一个折叠, 参数取一切有损 (`LeanFbTest.TL` 的写法): 同一条路径走到同一行, 种类取有损的那一支: 子项是常值序列 `nl (λ _ → x)` (有损行 `ω⋅` 的形状). 所以 `exec-TF*` 里那一行的输出由 `fb` 决定.

```agda
module FL = Fold SLs bkS ΛF lΛF oneF (λ _ → inj₂ tt)

ΨL : D hz (w₀ L₀)
ΨL = n1 ⨾ yc (FL.Run accᴸ (Ωd ΛF) ≤rf (lw₀ L₀) hself (λ p lW′ _ Y → FL.Stp Y) n0 (st FL.zeroD n0 n0)) (FL.τ₀ (lw₀ L₀))

ctrl-TL0 : Σ (D hz (w₀ L₀)) (λ x → nav (dR ∷ dR ∷ dN 1 ∷ dN 0 ∷ dL ∷ dR ∷ dN 0 ∷ dL ∷ dR ∷ []) ΨL ≡ nl (λ _ → x))
ctrl-TL0 = _ , refl
```

## §2 新种类的回灌在 `TF` 上不执行

```agda
module TFOld where
  open KDM SLs (OldK {SLs})
  open KDRun SLs bkS ΛF lΛF oneF fb (OldK {SLs}) (old→all {SLs} ΛF (old-up {SLs} Λs))

  kd-Act : ∀ {ly W} → KDI (Act {ly} {W})
  kd-Act p lW′ v Y′ kv kY′ = kd-Stp {Y = Y′} kY′

  Y₀ : St (w₀ L₀)
  Y₀ = st zeroD n0 n0

  TF-old : KDf (Run (accᴸ {S = L₀} {L = ΛF}) (Ωd ΛF) ≤rf (lw₀ L₀) hself (Act {ΛF} {w₀ L₀}) n0 Y₀)
  TF-old = kd-Run (accᴸ {S = L₀} {L = ΛF}) (Ωd ΛF) ≤rf (lw₀ L₀) hself (Act {ΛF} {w₀ L₀}) n0 Y₀
             (kd-Ωd ΛF (old→all {SLs} ΛF (old-up {SLs} Λs))) kd-Act tt ((λ Tq → tt) , tt)
```

## §3 剩下的有损种类

**含函数下标的一族.** 第 3 站, 坐标分量 $1+\mathrm{hl}\,f$, 左分量的新种类 (与构造一路的 `cp1` 同一位置, 只是坐标 $1$ 换成 $1+\mathrm{hl}\,f$; 级是 `ll …`).

```agda
κq : (ℕ → HB S⊥) → K (Lv (stL 3))
κq f = inj₂ (hs (hl f)) , inj₁ tt , inj₂ tt

κH : (ℕ → HB S⊥) → K SLs
κH f = 3 , inj₁ (κq f)

lossy-hl : ∀ f → plan (κH f) ≡ inj₂ tt
lossy-hl f = refl

lossy-hl-fb : ∀ f → fb (κH f) ≡ inj₂ tt
lossy-hl-fb f = refl
```

**它们是目标层的头.** 世界 `mH f`: 从基世界经第 3 站头的 `Up` (`headUp 3`) 把界升到 $c_0$ = 以 `κq f` 为头的高度; 在第 4 站的坐标 $c_0$ 处, 层的头就是 `inj₁ (κH f)`.

```agda
c₀ : (ℕ → HB S⊥) → HB (Lv (stL 3))
c₀ f = hΩ (κq f) (λ _ → hz)

lc₀ : ∀ f → LgB (c₀ f)
lc₀ f = (λ _ _ _ _ → hself) , (λ _ _ → tt)

mH : (ℕ → HB S⊥) → Wd SLs
mH f = rz (headUp 3) (c₀ f) (w₀ SLs)

lossy-hl-target : ∀ f → Σ (E L₀ (inj₁ (κH f)) → HB L₀) (λ g → Tg (w₀ L₀) (hΩ (inj₁ (κH f)) g) (mH f , hz))
lossy-hl-target f =
  _ , tg (rz≤ (headUp 3) (c₀ f) (w₀ SLs) , hself)
         (hlim 4 (hLim {κ = inj₁ (νS 3)} {c = c₀ f} hself hself))
         (rzLg (headUp 3) (lc₀ f) (lw₀ SLs) , tt)
```

**级 1 式读回只产出一个种类的 Ω-结点.** 对一切 $X$ 与 `a : AK0 X`, 起点满足时, `rdX a` 的输出的一切 $\Omega$-结点的种类都是 `aK a`.

```agda
module OneKind {X : KS} (a : AK0 X) where
  P1 : K X → Set
  P1 κ = κ ≡ aK a

  one-nbA : ∀ b (s : HB S⊥ → HB X → HB X) → AllK P1 b → (∀ c h → AllK P1 h → AllK P1 (s c h)) → ∀ c → AllK P1 (NbA.nbA b s c)
  one-nbA b s ab as hz = ab
  one-nbA b s ab as (hs c) = as c _ (one-nbA b s ab as c)
  one-nbA b s ab as (hl f) = λ n → one-nbA b s ab as (f n)
  one-nbA b s ab as (hΩ (() , _) g)

  one-rdX : ∀ {W} (lW : LgW L₀ W) b (x : D (hs hz) W) → AllK P1 b → AllK P1 (rdX a lW b x)
  one-rdp : ∀ {W} (lW : LgW L₀ W) b (d : ℕ → D (hs hz) W) → AllK P1 b → ∀ n → AllK P1 (rdpX a lW b d n)
  one-rdX lW b n0 ab = ab
  one-rdX lW b n1 ab = ab
  one-rdX lW b (x ⨾ y) ab = one-rdX lW (rdX a lW b x) y (one-rdX lW b x ab)
  one-rdX lW b (nl d) ab = λ n → one-rdp lW b d ab n
  one-rdX lW b (ni (ss hself) u) ab =
    refl , λ e → one-nbA b (λ c h → rdX a lW h (u ≤rf lW (toD₀ c))) ab (λ c h ah → one-rdX lW h (u ≤rf lW (toD₀ c)) ah) (fr a e)
  one-rdX lW b (nc (inj₁ κ) z u) ab = one-rdX lW b (u ≤rf lW) ab
  one-rdX lW b (nc (inj₂ _) () u) ab
  one-rdX lW b (nw p x) ab = one-rdX (lgDn L₀ p lW) b x ab
  one-rdp lW b d ab zero = ab
  one-rdp lW b d ab (suc n) = one-rdX lW (rdpX a lW b d n) (d n) (one-rdp lW b d ab n)

  -- 读回的增量 (起点 0)
  rdX-one-kind : ∀ {W} (lW : LgW L₀ W) (x : D (hs hz) W) → AllK P1 (LvRd.δ (RX a) lW x)
  rdX-one-kind lW x = one-rdX lW hz x tt
```

## §4 槽的成员在基世界里读数都是 $0$

对一切 $j$: `slotUp j` 的每个成员在基世界里的读数是 $0$. 与 `NegLeanFbBlind.same-iter` 合起来 (`slot-merge`): 只经 `slotUp j` 升界时, 成员读数恒相等.

```agda
module Start (j : ℕ) where
  open Pos j

  uncast-hz : ∀ {x} (e : num j ≡ x) → uncast e hz ≡ hz
  uncast-hz refl = refl

  top₀N  : ∀ k (p : PosN k) → coN k p (top (Lv k) (kN k p) (w₀ (Lv k))) ≡ hz
  top₀St : ∀ x (p : PosSt x) → coSt x p (top (step (Lv x)) (kSt x p) (w₀ (step (Lv x)))) ≡ hz
  top₀St x (inj₁ e) = uncast-hz e
  top₀St x (inj₂ p) = top₀N x p
  top₀N lz ()
  top₀N (ls x) p = top₀St x p
  top₀N (ll f) (i , p) = top₀N (f i) p
  top₀N (lΩ k g) (inj₁ p) = top₀St k p
  top₀N (lΩ k g) (inj₂ (c , p)) = top₀N (g c) p

  slot-start : ∀ i → co (slotUp j) i (top SLs (κJ (slotUp j) i) (w₀ SLs)) ≡ hz
  slot-start (m , p) = top₀St (stL m) p

  slot-merge : ∀ i i′ (ds : ℕ → HB (Lv (num j))) n →
    co (slotUp j) i (top SLs (κJ (slotUp j) i) (rzN (slotUp j) ds n (w₀ SLs)))
      ≡ co (slotUp j) i′ (top SLs (κJ (slotUp j) i′) (rzN (slotUp j) ds n (w₀ SLs)))
  slot-merge i i′ ds n = same-iter (slotUp j) i i′ ds (w₀ SLs) (trans (slot-start i) (sym (slot-start i′))) n
```

## §5 结论 (按档)

- **[定理, 闭项]** **`exec-TF0`, `exec-TF1`, `exec-TF2`** (`refl`; `TF` 的第 0 层数据沿显式路径的子项字面地是 `RKa _ (fb (νS n)) …`, $n=0,1,2$); `fb-head0`, `fb-head1`, `fb-head2` (这三处 `fb` 是回灌); 对照 **`ctrl-TL0`** (同一路径在全有损的折叠上是常值序列 `nl (λ _ → x)`, 有损行的形状; 不说 `TF` 那一处不是常值序列, 那要比较值, 未做).
- **[定理]** **`TF-old`** (`TF` 的折叠里闭包结点都是旧种类). **[判断, 一行读法]** 新种类的回灌 `κc₁` 与 `rd₁`, `bkS` 在 `TF` 上不执行.
- **[定理, 有损]** **`lossy-hl`**, `lossy-hl-fb` (对一切 $f$), **`lossy-hl-target`** (对一切 $f$, 它们是从基世界经 `headUp 3` 升上来的合法世界里的目标层的头). **[判断]** 这些目标在 `TF` 的计算里是否被走到: 未证; 由 `rdX-one-kind`, 经回灌升上来的第 3 站头的界只有一个级 0 种类的 Ω-结点, 所以 (判断) 沿回灌走到的世界里第 3 站头的坐标不以 `κq f` 为头.
- **[定理, 读回]** **`rdX-one-kind`** (对一切 $X$, `a`): 级 1 式读回的增量只含 `aK a` 的 Ω-结点. 对头 $n\ge2$ (`feedH n a`, `a` 来自 `find0`), 这是一个级为 `lz` 的种类.
- **[定理, 共享界]** **`slot-start`** (对一切 $j$, 基世界里 `slotUp j` 的成员读数都是 $0$), **`slot-merge`** (只经 `slotUp j` 升界, 成员读数恒相等).
