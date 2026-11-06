# 一般种类结构的折叠, 否定一路 (二): 接口的回灌律不看种类, 钩子不看读回

> 不含记号. 入口 [NegGenFold](NegGenFold.lagda.md). 对着接口 [GenFoldIf](GenFoldIf.lagda.md) ("接口定稿 2026-11-05 16:59 (首次编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> 接口 §3 的 `FBA S κ` 是 "种类 $\kappa$ 的 A-回灌", `GenK.fbA κ : FBA K κ ⊎ ⊤` 给每个种类一个可选的回灌; 接口文件头说: 并的分量的下标是坐标时, 这些种类 "只能有损地回灌 (`fbA κ = inj₂ tt`)". 本篇:
>
> 1. **`FBA` 的律不提 $\kappa$ (定理, `fba-swap`).** 记录 `FBA S κ` 的五个字段都不出现 $\kappa$, 所以一个种类的回灌就是一切种类的回灌. 在 `K₁` 上, 用可判定的旧站分量 `inj₁ tt` 的点更新 ([NegGenFoldUpd](NegGenFoldUpd.lagda.md) 的 `upd∘`) 得到 `FBA K₁ κ` 对**一切** $\kappa$ (`fba₁`), 包括读回分量里下标是高度的种类 `κ₁ f` (接口说只能有损的那些). 由它得到 `GenK K₁` 的实例 `genK₁`, 其中**每个种类都有回灌** (`fed-all`). 但这回灌升高的是 `inj₁ tt` 分量的界, `κ₁ f` 自己的分量原样不动 (`fba₁-misses`). 所以接口的律区分不了 "有内容的回灌" 与 "把别的种类的界升了": `fbA κ = inj₁ _` 不说明 $\kappa$ 的界被回灌.
> 2. **钩子是盲的 (定理).** `EvGenTy K` 对一切 $K$ 有常数实例, 连 `Dat` 取接口自己的数据树 `DK K` 时也有 (`evGenD`: 一切数据树求值为 $2$); `FoldTy.RunTy` 对一切 $K$, $\Lambda$ 有实例 (`runC`: 一切目标给 `n0`); `DnGenTy` 有实例 (`dnGenC`, 就是 `NegDnFoldBlind.dnC`, 每站回灌输出是 $2$, `HsGen`). 接口文件头 "接口不管什么 (盲)" 已经自述了第一条; 这里写成定理, 并补上后两条.
> 3. **`GenK (Lev x)` 对一切 $x$ 有实例 (定理, `genLev`; 嫌疑 iv 的回答之一).** 对高度 $x$ 结构递归 (与 `Lev` 同形): 顶坐标 `NegKcFoldDec.topLev`, 基世界 `LvKtCode.w0 (cdLev x)`, 底种类 `aL x` (沿 `inj₁`, 第 0 个分量, 底坐标 `bot` 走到 `Lev hz = S₀`), `frE` 就是那一份底拷贝的坐标 (`A`). 没有停机或正性问题, 不用编译指示. 所以 `DnGenTy` 的前提 `∀ x → GenK (Lev x)` 可满足 (`genAll`), 由它给出的 `DnTower` 若只用这条前提, 仍可以是常数 (第 2 条).
>
> **"读回进了闭项" 的陈述.** 简报说接口会有它的非盲陈述; 定稿的接口 (16:59 版) **没有**这样的陈述 (§5 只有 `EvGenTy`, `DnGenTy` 两个类型与 `K₁`). 所以本篇没有对象可以否定; 第 2 条说明现有的钩子不能承担这个说法 (手册 §3.3, §3.7).
>
> **只否定什么.** 第 1 条否定一个推断: "`fbA κ = inj₁ _` 说明种类 $\kappa$ 的界被有内容地回灌". 第 2 条否定: "有 `EvGenTy`/`RunTy`/`DnGenTy` 的实例就说明读回进了闭项". **不否定** 接口的任何记录与定义 (都有实例), 不否定有内容的折叠存在 (那要值的陈述).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegGenFoldBlind where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (Ht; H₀)
open import OCF.Align.LvKtCode using (w0; lw0; cdLev)
open import OCF.Align.LvKtIf using (Kc; FN; ckc)
open import OCF.Align.KcFoldIf using (LayK; DnTower; DnK)
open import OCF.Align.KcFoldTower using (module KD)
open import OCF.Align.DnFoldIf using (EvSys; EvSysK)
open import OCF.Align.NegKcFoldDec using (TopK; topLev; topKc)
open import OCF.Align.NegDnFoldBlind using (dnC; dnLC; HsC)
open import OCF.Align.GenFoldIf
open import OCF.Align.NegGenFoldUpd using (upd∘; κ₁; jx)
```

## §1 `FBA` 不看种类

```agda
fba-swap : ∀ {S : KS} {κ κ′ : K S} → FBA S κ → FBA S κ′
fba-swap F = record { tpA = tpA F ; rsA = rsA F ; rs≤ = rs≤ F ; rsLg = rsLg F ; tp-rs = tp-rs F }
```

`K₁` 上的一个 `FBA`: 读旧站分量 `inj₁ tt` 的界, 只升它 (点更新在可判定的下标上).

```agda
rs≤₁ : ∀ {w : Wd K₁} {v} → w (inj₁ tt) ⊲ v → _≤w_ K₁ w (upd∘ w v)
rs≤₁ p (inj₁ tt) = p
rs≤₁ {w} p (inj₂ c) = ≤w-rf (Lev c)

rsLg₁ : ∀ {w : Wd K₁} {v} → LgW K₁ w → Lg v → LgW K₁ (upd∘ w v)
rsLg₁ lw lv (inj₁ tt) = lv
rsLg₁ lw lv (inj₂ c) = lw (inj₂ c)

fba₀ : FBA K₁ (inj₁ tt , tt)
fba₀ = record { tpA = λ w → w (inj₁ tt) ; rsA = upd∘ ; rs≤ = rs≤₁ ; rsLg = rsLg₁ ; tp-rs = C.self }

fba₁ : ∀ κ → FBA K₁ κ
fba₁ κ = fba-swap fba₀

-- 读回分量里下标为高度的底拷贝 κ₁ f: 它的 "回灌" 不碰它自己的分量
fba₁-misses : ∀ f w v → rsA (fba₁ (κ₁ f)) w v (inj₂ (jx f)) ≡ w (inj₂ (jx f))
fba₁-misses f w v = refl
```

`GenK K₁`, 每个种类都有回灌.

```agda
toG : ∀ {S : KS} → TopK S → TopG S
toG T = record { top = TopK.top T ; topBd = TopK.topBd T }

genK₁ : GenK K₁
genK₁ = record
  { tpK = toG (topKc 1) ; w₀ = w0 (ckc 1) ; lw₀ = lw0 (ckc 1)
  ; aK = inj₁ tt , tt ; frE = λ e → e ; frE-lg = λ l → l ; frE-mono = λ lw b b′ p → p
  ; fbA = λ κ → inj₁ (fba₁ κ) }

fed-all : ∀ κ → Σ (FBA K₁ κ) (λ F → fbA genK₁ κ ≡ inj₁ F)
fed-all κ = fba₁ κ , refl

-- 接口 §2: 闭包结点的分支在世界 W′ 里的坐标是 top κ W′. 对 κ₁ f, 回灌后的世界里这个坐标不动
fba₁-top-fixed : ∀ f w v → top (tpK genK₁) (κ₁ f) (rsA (fba₁ (κ₁ f)) w v) ≡ top (tpK genK₁) (κ₁ f) w
fba₁-top-fixed f w v = refl
```

接口 §6, §7 (只增) 的结构在 `genK₁` 上也成立: 回灌的顶坐标合法 (`fbLg₁`), 合法向下封闭 (`ldK₁`; 对一切 `Lev x`, `ldLev`). 所以 `genK₁` 可以作构造一路 `GenFoldRun` 的模块参数 `(G, Ld, fl)`.

```agda
fbLg₁ : FbLg genK₁
fbLg₁ κ lw = lw (inj₁ tt)

ldLev : ∀ {S : KS} (x : HB S) → LgDn (Lev x)
ldLev hz = record { lgDn = λ p l → lg⊲ p l }
ldLev (hs x) = record { lgDn = λ p l → lgDn (ldLev x) (proj₁ p) (proj₁ l) , lgB⊲ (proj₂ p) (proj₁ l) (proj₂ l) }
ldLev (hl f) = record { lgDn = λ p l n → lgDn (ldLev (f n)) (p n) (l n) }
ldLev (hΩ κ g) = record { lgDn = λ p l e → lgDn (ldLev (g e)) (p e) (l e) }

ldK₁ : LgDn K₁
ldK₁ = record { lgDn = ld }
  where
  ld : ∀ {u v} → _≤w_ K₁ u v → LgW K₁ v → LgW K₁ u
  ld p l (inj₁ tt) = lg⊲ (p (inj₁ tt)) (l (inj₁ tt))
  ld p l (inj₂ c) = lgDn (ldLev c) (p (inj₂ c)) (l (inj₂ c))
```

## §2 钩子是盲的

```agda
evGenC : ∀ (T : KS) → EvGenTy T
evGenC T g = record
  { Lay = LayK T ; Wor = ⊤ ; LgWo = λ _ → ⊤ ; Dat = λ _ _ → ⊤ ; Ok = λ _ _ → ⊤
  ; evH = λ _ _ _ → hs (hs hz) ; lgEv = λ _ _ _ → tt } , refl

-- 数据取接口自己的数据树 DK T, 世界取 Wd (step T): 仍可以一切求值为 2
evGenD : ∀ (T : KS) → EvGenTy T
evGenD T g = record
  { Lay = LayK T ; Wor = Wd (step T) ; LgWo = LgW (step T) ; Dat = DK T ; Ok = λ _ _ → ⊤
  ; evH = λ _ _ _ → hs (hs hz) ; lgEv = λ _ _ _ → tt } , refl

evGenD-const : ∀ (T : KS) (g : GenK T) {L W} (X : DK T L W) (lW : LgW (step T) W) →
  EvSys.evH (proj₁ (evGenD T g)) {L} {W} tt lW X ≡ hs (hs hz)
evGenD-const T g X lW = refl

runC : ∀ (T : KS) (Λ : HB (step T)) → FoldTy.RunTy T Λ
runC T Λ ac X q lW ll ig w s = FoldTy.df (λ _ → n0)

dnGenC : DnGenTy
dnGenC _ = dnC
```

## §3 `GenK (Lev x)` 对一切 $x$: 对高度结构递归

底种类沿 `inj₁` (后继), 第 0 个分量 (ℕ-极限), 底坐标 `bot` 那个分量 ($\Omega$-结点) 走到 `Lev hz = S₀`.

```agda
aL : ∀ {S : KS} (x : HB S) → K (Lev x)
aL hz = tt
aL (hs x) = inj₁ (aL x)
aL (hl f) = 0 , aL (f 0)
aL {S} (hΩ κ g) = bot S κ , aL (g (bot S κ))

frL : ∀ {S : KS} (x : HB S) → E (Lev x) (aL x) → A
frL hz e = e
frL (hs x) e = frL x e
frL (hl f) e = frL (f 0) e
frL {S} (hΩ κ g) e = frL (g (bot S κ)) e

frL-lg : ∀ {S : KS} (x : HB S) {e} → LgE (Lev x) (aL x) e → Lg (frL x e)
frL-lg hz l = l
frL-lg (hs x) l = frL-lg x l
frL-lg (hl f) l = frL-lg (f 0) l
frL-lg {S} (hΩ κ g) l = frL-lg (g (bot S κ)) l

frL-mono : ∀ {S : KS} (x : HB S) {w e e′} → LgW (Lev x) w → Bd (Lev x) (aL x) e w → Bd (Lev x) (aL x) e′ w →
  Pr (Lev x) (aL x) w e e′ → frL x e ⊲ frL x e′
frL-mono hz lw b b′ p = p
frL-mono (hs x) lw b b′ p = frL-mono x (proj₁ lw) b b′ p
frL-mono (hl f) lw b b′ p = frL-mono (f 0) (lw 0) b b′ p
frL-mono {S} (hΩ κ g) lw b b′ p = frL-mono (g (bot S κ)) (lw (bot S κ)) b b′ p

genLev : ∀ {S : KS} (x : HB S) → GenK (Lev x)
genLev x = record
  { tpK = toG (topLev x) ; w₀ = w0 (cdLev x) ; lw₀ = lw0 (cdLev x)
  ; aK = aL x ; frE = frL x ; frE-lg = frL-lg x ; frE-mono = frL-mono x
  ; fbA = λ _ → inj₂ tt }

-- DnGenTy 的前提可满足; 由它给出的塔仍可以是常数
genAll : ∀ {S : KS} (x : HB S) → GenK (Lev x)
genAll = genLev

module KG = KD (dnGenC genAll) dnLC

HsGen : ∀ s → KG.Hs s ≡ hs (hs hz)
HsGen = HsC
```

## §4 结论 (按档)

- **[定理]** **`fba-swap`** (`FBA S κ` 不看 $\kappa$); `fba₀`, `fba₁`, **`genK₁`**, **`fed-all`** (`K₁` 上每个种类都有回灌); **`fba₁-misses`**, **`fba₁-top-fixed`** (对 `κ₁ f`, 回灌不碰它自己的分量, 闭包分支的坐标 `top κ W′` 不动); `fbLg₁`, `ldK₁`, `ldLev` (接口 §6, §7 的结构也成立).
- **[定理]** **`evGenC`**, **`evGenD`**, `evGenD-const` (`EvGenTy` 的常数实例, 数据取 `DK` 时也是); **`runC`** (`RunTy` 的平凡实例); **`dnGenC`**, **`HsGen`** (`DnGenTy` 的实例, 每站回灌输出是 $2$).
- **[定理, 前提实例]** **`genLev`** / `genAll` (一切 $x$ 的 `GenK (Lev x)`, 对 $x$ 结构递归, 无编译指示), `aL`, `frL`, `frL-lg`, `frL-mono`.
- **[判断]** 要让 `fbA κ = inj₁ _` 说出 "$\kappa$ 的界被回灌", `FBA` 至少要把 `tpA` 绑到 $\kappa$ 的界上 (例如对坐标为 `A` 的种类 `tpA w ≡ top κ w`, 或 `Bd κ c w` ⇔ `c ⊲ tpA w`). 绑上之后, 若再要求 "别的分量不升" 就是 [NegGenFoldUpd](NegGenFoldUpd.lagda.md) 的分离子; 只绑不留, 本路没有找到否定, 也没有找到下标为高度的分量上的构造 (判断: 统一的升法要 `A` 上的字面公共上界, 例如 $1$ 与 $\omega$ 的 $1\oplus v$ 不以 $\omega$ 为第一位置; 未编译).
