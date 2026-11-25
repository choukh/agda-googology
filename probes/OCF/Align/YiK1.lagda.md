# K1：原块上第三项塔的正则性

**结论（编译定理）：`tw3-reg : Reg (V.tw 3)`。** 原块上第三项塔的
派发证据完整，不需要加严格性或修改守卫。另证层参数为 Ω₁ 时，
全部原合法守卫坐标的读回满足 `Reg`。本篇没有折叠或新序数值界。

只用原 `LevelFixCore` / `LevelFixVal` 与第十轮冻结的 `Reg`。
先逐层展开目标，再检查全部原守卫坐标。全塔归纳的一次尝试止于
“坐标读回再取 Ω”这个字段，未得到全 `n` 定理；不是该字段的否定。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiK1 where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.LevelFixCore using (LF; Raw; Gd; Cp; Lgl; Pre; Low; GdL)
import OCF.Align.LevelFixCore as F
open F using (module G)
import OCF.Align.LevelFixVal as V
open import OCF.Align.YiDispBase
  using (Below; one; more; e-suc; e-lim; e-first; e-branch; below-trans)
open import OCF.Align.YiRegBase using (Reg)
import OCF.Align.RR4RegOmega2 as R
import OCF.Align.RR4CoordRoot as C
```

## 1. 目标的字面展开与坐标域

`tw 0 = 0`，`tw 1 = 1`，`tw 2 = Ω̂ 1 = Ω₁`，
`tw 3 = Ω̂ Ω₁`。这里的 Ω₂ 专指 `Ω̂ 2`，不是 `tw 3`。
记 `raw1 = suc zero : Raw 0`。第三项的外层展开为

```agda
tw3-form : V.tw 3 ≡
  F.lc F.zero (G.suc G.zero) (V.Ω̂ (F.suc F.zero))
    (λ η e → V.Ω̂ (V.up F.zero η))
tw3-form = refl

Tw3Expanded : Set
Tw3Expanded =
  Below (F.suc F.zero) (V.tw 3) ×
  Reg F.zero ×
  Reg (V.Ω̂ (F.suc F.zero)) ×
  (∀ η (e : Gd F.zero (V.cO F.zero) η) → Reg (V.Ω̂ (V.up F.zero η)))

expand-reg : Reg (V.tw 3) → Tw3Expanded
expand-reg r = r

pack-reg : Tw3Expanded → Reg (V.tw 3)
pack-reg r = r
```

因此须区分两种“层号 Ω₁ 处的坐标”：`Ω₁` 这个结点的分支坐标是
`Raw 0`，守卫为 `Cp 0 raw1 η × Lgl 0 η`；类型 `Raw Ω₁` 则是
**以 Ω₁ 为 Raw 的层参数**，两者不是同一类型。按原定义逐层展开
`Reg (tw 3)`，外层量化前者；后者不是这里的外层守卫域。
下面的通用引理仍量化任意层号的全部 `Raw`，包括 `Raw Ω₁`，不删退化坐标。

若 `η = suc a`，最后一项继续展开为
`Below (suc (up 0 a)) (Ω̂ (suc (up 0 a)))`、`Reg (up 0 a)`、
`Reg (Ω̂ (up 0 a))`，以及对所有
`ζ : Raw (up 0 a)`、`d : Gd (up 0 a) (cO (up 0 a)) ζ`
的 `Reg (up (up 0 a) ζ)`。若 `η = lim f`，则是逐项的同一义务。
这些量词保留常列、常值 Ω 分支、`top` 和 `em`，只要求原 `Lgl`。

## 2. 从已有位置路径取正则性

第一位置 `CP` 可以自反，`Below` 是至少一步的路径。二者都把目标的
`Reg` 传给来源；这里不需要在裸下标上比较。

```agda
cp-reg : ∀ {a b} → V.CP a b → Reg b → Reg a
cp-reg V.self r = r
cp-reg (V.suc p) r = cp-reg p r
cp-reg (V.lim n p) r = cp-reg p (r n)
cp-reg (V.fst p) (bound , rk , rt , rg) = cp-reg p rt

upN-reg : ∀ y → Reg y → (r : Pre y) (c : Low y r)
  (t : LF) (g : (η : Low y r) → GdL y r c η → LF) →
  Below y t → Reg t → (∀ η e → Reg (g η e)) → Reg (V.upN y r c t g)
upN-reg F.zero ry ()
upN-reg (F.suc y) ry (inj₁ _) c t g p rt rg =
  more p e-first , ry , rt , rg
upN-reg (F.suc y) ry (inj₂ r) c t g p rt rg =
  upN-reg y ry r c t g (below-trans (one e-suc) p) rt rg
upN-reg (F.lim f) rf (n , r) c t g p rt rg =
  upN-reg (f n) (rf n) r c t g (below-trans (one (e-lim n)) p) rt rg
upN-reg (F.lc k c₀ t₀ g₀) (bound , rk , rt₀ , rg₀)
  (inj₁ (inj₁ _)) c t g p rt rg =
  more (below-trans bound p) e-first , rk , rt , rg
upN-reg (F.lc k c₀ t₀ g₀) (bound , rk , rt₀ , rg₀)
  (inj₁ (inj₂ r)) c t g p rt rg =
  upN-reg k rk r c t g (below-trans (below-trans (one e-suc) bound) p) rt rg
upN-reg (F.lc k c₀ t₀ g₀) (bound , rk , rt₀ , rg₀)
  (inj₂ (inj₁ r)) c t g p rt rg =
  upN-reg t₀ rt₀ r c t g (below-trans (one e-first) p) rt rg
upN-reg (F.lc k c₀ t₀ g₀) (bound , rk , rt₀ , rg₀)
  (inj₂ (inj₂ (η , e , r))) c t g p rt rg =
  upN-reg (g₀ η e) (rg₀ η e) r c t g
    (below-trans (one (e-branch η e)) p) rt rg
```

`upN-reg` 的前提是已有的 `Reg y` 与字面路径 `Below y t`。
在槽位沿 `lc.k` 下降时，用 `Reg y` 的第一个字段
`Below (suc k) y`，而不是把下标字段本身当作值的子树。

## 3. 任意层上，带三份外部证据的坐标读回

以下引理的三份证据都在块外：`Reg y`、`Below y (Ω̂ y)`、
`Reg (Ω̂ y)`。没有把它们放进 `Gd`。
`top` 下方的 `em` 不再逐形状枚举：读回的 `CP` 直接从
`Reg (Ω̂ y)` 取出其正则性。

```agda
up-to : ∀ y (f : ℕ → Raw y) → (∀ n → Cp y (f n) (f (suc n))) →
  ∀ k m → Cp y (f m) (f (k + m))
up-to y f st zero m = inj₁ refl
up-to y f st (suc k) m = F.Cp-tr y (up-to y f st k m) (st (k + m))

top-read-reg : ∀ y → Reg y → Below y (V.Ω̂ y) → Reg (V.Ω̂ y) →
  ∀ (η : Raw y) → Lgl y η → Cp y G.top η → Reg (V.up y η)
top-read-reg y ry root ro G.zero l (inj₁ ())
top-read-reg y ry root ro G.zero l (inj₂ ())
top-read-reg y ry root ro (G.suc a) l (inj₁ ())
top-read-reg y ry root ro (G.suc a) l (inj₂ p) =
  top-read-reg y ry root ro a l p
top-read-reg y ry root ro (G.lim f) (st , lw) (inj₁ ())
top-read-reg y ry root ro (G.lim f) (st , lw) (inj₂ (n , p)) = term
  where
  term : ∀ m → Reg (V.up y (f m))
  term m with F.cmpC y (f (m + n))
    (subst (λ z → Cp y (f m) (f z)) (+-comm n m) (up-to y f st n m))
    (F.Cp-tr y p (up-to y f st m n)) (lw (m + n))
  ... | inj₁ below-top = cp-reg (V.cp→CP y below-top) ro
  ... | inj₂ above-top = top-read-reg y ry root ro (f m) (lw m) above-top
top-read-reg y ry root ro (G.lc r c t g) (tg , mono , irr , lt , lg) (inj₁ ())
top-read-reg y ry root ro (G.lc r c t g) (tg , mono , irr , lt , lg) (inj₂ p) =
  upN-reg y ry r c (V.up y t) (λ η e → V.up y (g η e))
    (R.below-cp root (V.cp→CP y p))
    (top-read-reg y ry root ro t lt p)
    (λ η e → top-read-reg y ry root ro (g η e) (lg η e) (F.Cp-tr y p (tg η e)))
top-read-reg y ry root ro (G.em i t) l (inj₁ ())
top-read-reg y ry root ro (G.em i t) l (inj₂ ())
top-read-reg y ry root ro G.top l p = ro

guard-read-reg : ∀ y → Reg y → Below y (V.Ω̂ y) → Reg (V.Ω̂ y) →
  ∀ η → Gd y (V.cO y) η → Reg (V.up y η)
guard-read-reg F.zero ry root ro η e = R.read0-reg η
guard-read-reg (F.suc y) ry root ro η e =
  top-read-reg (F.suc y) ry root ro η (proj₂ e) (proj₁ e)
guard-read-reg (F.lim f) ry root ro η e =
  top-read-reg (F.lim f) ry root ro η (proj₂ e) (proj₁ e)
guard-read-reg (F.lc k c t g) ry root ro η e =
  top-read-reg (F.lc k c t g) ry root ro η (proj₂ e) (proj₁ e)
```

极限行里比较的两个坐标都携带到同一项 `f (m + n)` 的字面路径，
其合法性来自 `Lgl`，没有全局比较。该引理有闭实例：取 `y = 0`，
三份证据依次是 `tt`、`one e-suc`、`tt`。

## 4. 第 0 层守卫读回的 Ω 保持

对坐标本身结构递归。后继行新用通用的 `guard-read-reg`，从而覆盖
`Raw (up 0 a)` 的全部守卫分支；根路径由旧的 `coordinate-root` 给出。
极限中的早项若在 `raw1` 之下，只可能是字面的 0 或 1。

```agda
under-one-omega : ∀ (a : Raw F.zero) → Cp F.zero a R.raw1 →
  Reg (V.Ω̂ (V.up F.zero a))
under-one-omega a (inj₁ refl) = R.Ω₁-reg
under-one-omega a (inj₂ (inj₁ refl)) = tt
under-one-omega a (inj₂ (inj₂ ()))

coordinate-omega-reg : ∀ (η : Raw F.zero) → Lgl F.zero η →
  Cp F.zero R.raw1 η → Reg (V.Ω̂ (V.up F.zero η))
coordinate-omega-reg G.zero l (inj₁ ())
coordinate-omega-reg G.zero l (inj₂ ())
coordinate-omega-reg (G.suc a) l (inj₁ refl) = R.Ω₁-reg
coordinate-omega-reg (G.suc a) l (inj₂ p) =
    C.reg-root-suc a (inj₂ p , l)
  , R.read0-reg a
  , coordinate-omega-reg a l p
  , (λ ζ d → guard-read-reg (V.up F.zero a) (R.read0-reg a)
      (C.coordinate-root (a , (p , l))) (coordinate-omega-reg a l p) ζ d)
coordinate-omega-reg (G.lim f) (st , lw) (inj₁ ())
coordinate-omega-reg (G.lim f) (st , lw) (inj₂ (n , p)) = term
  where
  term : ∀ m → Reg (V.Ω̂ (V.up F.zero (f m)))
  term m with F.cmpC F.zero (f (m + n))
    (subst (λ z → Cp F.zero (f m) (f z)) (+-comm n m) (up-to F.zero f st n m))
    (F.Cp-tr F.zero p (up-to F.zero f st m n)) (lw (m + n))
  ... | inj₁ below-one = under-one-omega (f m) below-one
  ... | inj₂ above-one = coordinate-omega-reg (f m) (lw m) above-one
coordinate-omega-reg (G.lc () c t g) l p
coordinate-omega-reg (G.em () t) l p
coordinate-omega-reg G.top l (inj₁ ())
coordinate-omega-reg G.top l (inj₂ ())

tw3-reg : Reg (V.tw 3)
tw3-reg =
    more R.one-below-Ω₁ e-first
  , tt
  , R.Ω₁-reg
  , (λ η e → coordinate-omega-reg η (proj₂ e) (proj₁ e))

tw3-legal : V.Legal (V.tw 3)
tw3-legal = V.Legal-tw 3
```

`tw3-reg` 是完整 `Reg`，`tw3-legal` 是原块的合法闭项证书；二者
都没有外部前提。没有折叠或序数值比较，因此没有新增强度界。

## 5. 层参数确为 Ω₁ 的全部坐标

为避免把前述两种坐标域混用，这里另外实填 `Raw Ω₁` 的结论。
其守卫确为 `Cp Ω₁ top η × Lgl Ω₁ η`，原下界等号保留。
它是通用引理在 `tw 2` 的实例，用到刚证得的 `Reg (tw 3)`。

```agda
omega1-coordinate-reg : ∀ (η : Raw (V.tw 2)) →
  Gd (V.tw 2) (V.cO (V.tw 2)) η → Reg (V.up (V.tw 2) η)
omega1-coordinate-reg = guard-read-reg (V.tw 2) R.Ω₁-reg (one e-first) tw3-reg
```

常值 Ω 分支给一个非空的退化实例。坐标本身位于 `Raw Ω₁`，
根槽位取 Ω₁ 结点的层号 0；第一支和全部分支都是同一个 `top`。
原 `Lgl` 的第一支、单调性均用自反位置，未要求严格增长。

```agda
omega1-junk : Raw (V.tw 2)
omega1-junk = G.lc (inj₁ (inj₁ tt)) R.raw1 G.top (λ _ _ → G.top)

omega1-junk-lgl : Lgl (V.tw 2) omega1-junk
omega1-junk-lgl =
  (λ _ _ → inj₁ refl) , (λ _ _ _ _ _ → inj₁ refl) ,
  (λ _ _ _ → refl) , tt , (λ _ _ → tt)

omega1-junk-guard : Gd (V.tw 2) (V.cO (V.tw 2)) omega1-junk
omega1-junk-guard = inj₂ (inj₁ refl) , omega1-junk-lgl

omega1-junk-read : V.up (V.tw 2) omega1-junk ≡
  F.lc F.zero R.raw1 (V.tw 3) (λ _ _ → V.tw 3)
omega1-junk-read = refl

omega1-junk-reg : Reg (V.up (V.tw 2) omega1-junk)
omega1-junk-reg = omega1-coordinate-reg omega1-junk omega1-junk-guard
```

## 6. 全塔归纳尝试的停止点

**判断／未完成的证明义务。** 试把 `tw3-reg` 的证明提升为相邻两项
`Reg (tw n)`、`Reg (tw (suc n))` 的归纳不变量。直接套
`guard-read-reg` 只能得到坐标读回的 `Reg`；下一次取 Ω，结点的
最后一个字段变为“每个坐标读回再取 Ω 后仍 `Reg`”。这正是下面的类型：

```agda
NextCoordinateField : Set
NextCoordinateField = ∀ (η : Raw F.zero) →
  Gd F.zero (V.cO F.zero) η → Reg (V.Ω̂ (V.Ω̂ (V.up F.zero η)))

next-field-at-one : Reg (V.Ω̂ (V.Ω̂ (V.up F.zero R.raw1)))
next-field-at-one = tw3-reg
```

继续对 `η = suc a` 展开后，其中一项是
`∀ ζ (d : Gd (up 0 a) (cO (up 0 a)) ζ) → Reg (Ω̂ (up (up 0 a) ζ))`。
本篇的 `guard-read-reg` 给的是去掉这次 Ω 的结论；仅有相邻塔两项的
`Reg` 不能直接把这个字段填上。没有写出一次封闭的全 `n` 归纳，
按任务约定停在 `tw 3`，不继续扩建归纳不变量，不把这个卡点说成否定。
`next-field-at-one` 仅实填单个坐标，不是全域或有限测试代替证明。

## 7. 与 Ω₂ 证明的差、翻译账与范围

`RR4RegOmega2.Ω₂-reg` 在 `Raw 1` 中只有一个有效 Ω 槽位，
根字段的下标是 0；它用“`top` 之下只有 `top` 与 `em top₀`”枚举。
这里的后继行须处理 `Raw (up 0 a)` 的任意槽位。新用到的实质字段是
**槽位沿下标继续下降时，`Reg (lc k …)` 自带的
`Below (suc k) (lc k …)`**：`upN-reg` 把它接到读回结点的第一支。
同时递归读取 `Reg` 的层号、第一支、全部守卫分支三个子字段，
所以 `Raw Ω₁` 的 `Pre` 中每个原槽位都覆盖；没有把 `lc.k` 当作值边。

新增的是对结构参数的一步定理 `top-read-reg` / `guard-read-reg`，
不按塔的站数定制槽位，也不从记号基本列新增节点或字段。
根路径借用 `coordinate-root`，极限比较照原块的字面公共界进行；
`Reg`、`Gd`、`Lgl`、`Legal` 及树、折叠均未改，证据始终在块外。
导入闭包无记号、无 C 线；这说明无引用，不声称整套定义已树自足。

**判断。** 本站不需要“证据进 Gd”，没有测试新的归纳–递归块。
若以后确要把证据放进守卫，`Reg` 的位置路径索引含 `LF`，而 `Gd`
出现在 `lc` 分支函数的定义域；可能重新形成 `LF` 经证据类型到负位置的
路径。`LevelFixCore` 开头 P1 的报错记录了相等类型造成的同类路径，
但不是对这个尚未写出的改法的正性否定，也不是本轮编译事实。

定理档只有上述完整类型检查的结论；本轮不以有限样本支持全域声称。
`tw3-legal` 交付合法闭项，`tw3-reg` 交付本任务指定的派发性质，
没有 ψ、γ、FGH 比较或 EBO 下界；既有值前沿不变。

## 8. 冷编与审计清单

- 本轮新模块仅 `OCF.Align.YiK1`。删它自己的字面 `.agdai` 后，
  从仓库根单路以 `+RTS -M6G -RTS` 冷编，退出码 0，有 `Checking` 行；
  依赖用缓存，不声称冷编了整个导入闭包。
- 文件选项 `--safe --without-K --lossy-unification`，代码无公设、洞、
  不检查停机／正性指示、信任相等或函数外延前提。无本机绝对路径、尾随空白。
- `importclosure.py` 的 `--only` 白名单为 `OCF.Align.Yi`、
  `OCF.Align.RR4CoordRoot`、`OCF.Align.RR4RegOmega2`、
  `OCF.Align.LevelFix`、`OCF.Free.Level`、`OCF.BTBO`：
  本地 19 模块、库叶 19，禁用表及白名单外均为 0。
  `agda --dependency-graph` 的本地集合与源码闭包逐一相同，无记号或 C 线。
- 成功生成 HTML 后切片：`tw3-reg` 87 块、`guard-read-reg` 68 块、
  `omega1-coordinate-reg` 88 块、`omega1-junk-reg` 92 块；
  四者记号模块块数与其它模块记号词命中均为 0。
  另以单路 6G 成功生成 `EboLean3Lab` 的 HTML 作正对照，
  `ebo-lab″` 为 352／33／36。正对照不在本篇导入闭包内。
  切片是语法近似，只认证所述无引用范围。

复现命令（`<库文件>` 含 stdlib 与 cubical 的库路径）：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiK1.lagda.md +RTS -M6G -RTS
```

没有提交或推送；README 当前阶段、翻译账与 LOG 同步补记。
