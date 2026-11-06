# 读回包 + 第 ω+1 级折叠, 否定一路 (二): 层号的读法, Ω-极限层, 混合高度的拷贝

> 不含记号. 入口 [NegLvRd](NegLvRd.lagda.md). 对着接口 [LvRdIf](LvRdIf.lagda.md) ("接口定稿 2026-11-05 14:28 (编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示; 函数外延 `FEA` (只对 $\mathbb N\to A$) 只在 §2 作前提, 用到它的结论标 "条件".
>
> 1. **嫌疑 (iv): 层号的读法不能忠实 (定理).** `no-faithful`: 对**任一** `σ-of : Ht → HB S₀`, 没有 $d$ 使 $d\circ\sigma\text{-of}=\mathrm{id}$. 这是 `HtTowerNeg.no-retract` 在 `S₁` 的新种类 (坐标 `HB S₀`) 上的实例. 推论 `no-faithful-shape`: 对任一 `LvShape`, 层号 (外层界的增量) 记不住回灌的输出. 前提 `LvShape` 可满足 (`lvShape`, 对任意读法与输出). **只否定**: "层号由回灌给出" 读成 "层号忠实地编码输出" (新一级的种类以输出本身为坐标, 再从层号读回输出). **不否定**: 接口 §8 的 `LvShape` (它只要求层号是输出的函数); 层号与壁垒: `Stages` 的码都在字面的界 `B (s+1)` 之下, 判定都是码的数据判定 (判断, 见入口).
> 2. **嫌疑 (i): Ω-极限层上没有与世界无关的层证据 (定理); 按可入性对一切分支给值撞 WLPO (条件).** 有限级与 ω 级的读回包 (`FamFoldRead.trK`, 接口 `PkgΩ`) 把旧种类交给低层时, 用的是**对一切世界**成立的层证据 `Q : ∀ {W} → ly m ⊲[ W ] L′` (层是有限高度或 ℕ-极限, `hlim` 证据与世界无关). 若层号由回灌给出, 层可以是 Ω-极限 (`A`-分支). `no-unifΩ`: 对合法的 Ω-极限层 $L=\mathrm{h\Omega}\,\kappa_A\,h_A$ (`Lg-LΩ`), 分支 $h_A(1)$ 没有对一切世界的证据; 只有世界的 `A`-分量在 $1$ 之上时才有 (`acc-ev`). 所以在 Ω-极限层, 读回包对分支给的值必须读世界 (同第 0 级的闭包 `nκ`), 不能像 `trK` 那样对一切分支一致地给. 若改为 "可入就照常翻译, 否则给缺省值", 就要对**裸**分支判定可入: `decAcc-sep` (无条件分离子), `decAcc→WLPO` (条件 `FEA`). **只否定**: 与世界无关的层证据 (Ω-极限层的非底分支); 对裸 `A`-元素判定在 $\omega$ 之下. **不否定**: 接口 `PkgΩ` (只到 $\omega$, $\omega+1$, 都是后继或 ℕ-极限); 读世界的闭包式翻译; 带公共上界的可入判定 (`cmpF`, 那是可判定的).
> 3. **嫌疑 (iii): 混合高度的级数是数据, 不用判定; 墙在拷贝 (定理).** `Gω = sup ℕ Sk` 的种类是 $(n,\kappa)$, 级数 `lvl = proj₁` (定义, 不判定任何高度). `no-wmatch-ω`: 种类 $(1,\mathrm{new})$ 与 $(2,\text{旧}(\mathrm{new}))$ (同一个第 1 级新种类的两份拷贝) 在 `Sk 2` 里是同一个种类, 在 `Gω` 的世界里却各读各的分量; 没有 `Gω` 到 `Sk 2` 的世界映射同时保两份的界 (`HtTowerNStage.no-wmatch` 在接口的 `Gω` 上的版本). 两个前提各自可满足 (`sat-1`, `sat-2`). **只否定**: 把混合高度的世界折成某一级的世界而两份拷贝的界同时保持. **不否定**: 接口 §3 的 `Dn Gω` (下降是对结点的折叠, 不需要世界映射; 判断); 逐级的截断在 "只含 $\le N$ 级种类" 的高度上 (方向 `Sk N` 的世界 → `Gω` 的世界, 判断: 可写).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegLvRdLay where

open import Data.Nat using (ℕ; zero; suc)
import Data.Nat as N
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (S₁; Ht; Wd₂; κA; n0)
open import OCF.Align.HtTowerNeg using (no-retract)
open import OCF.Align.FamFoldIf using (Sk)
open import OCF.Align.LvFbCode using (Code; cd; cd-tgt)
open import OCF.Align.ColimWNeg using (WLPO; or; or-in; or-false)
open import OCF.Align.LvRdIf
```

## §1 嫌疑 (iv): 层号的读法不能忠实

`S₁` 的新种类 `inj₂ tt` 的坐标是 `HB S₀`. 若某个读法 `σ-of : Ht → HB S₀` 有左逆, 它就是 `HB S₁` 到这个坐标类型的收缩, 与 `no-retract` 矛盾.

```agda
no-faithful : ∀ (σ-of : Ht → HB S₀) (d : HB S₀ → Ht) → ¬ (∀ x → d (σ-of x) ≡ x)
no-faithful σ-of d = no-retract {S = S₁} (inj₂ tt) σ-of d

no-faithful-shape : ∀ {a} (L : LvShape a) (d : HB S₀ → Ht) → ¬ (∀ x → d (LvShape.σ-of L x) ≡ x)
no-faithful-shape L d = no-faithful (LvShape.σ-of L) d
```

**前提实例.** 对任意读法与任意输出 (读出的增量合法), `LvShape` 都有: 外层界取部分和, 第 $s+1$ 站回灌的码取 "旧界经 `⊞-fst`" 的码.

```agda
module Shape (a : A) (σ-of : Ht → HB S₀) (out : ℕ → Ht) (lσ : ∀ s → LgB (σ-of (out s))) where
  Bs : ℕ → HB S₀
  Bs zero = hz
  Bs (suc s) = Bs s ⊞ σ-of (out s)

  st : Stages a
  st = record
    { B = Bs ; σ = λ s → σ-of (out s) ; lgσ = lσ ; B-s = λ s → refl
    ; κ = λ s → cd (⊞-fst {w = a} (Bs s) (σ-of (out s)))
    ; κ-tgt = λ s → cd-tgt (⊞-fst {w = a} (Bs s) (σ-of (out s))) }

  lvShape : LvShape a
  lvShape = record { St = st ; out = out ; σ-of = σ-of ; σ-is = λ s → refl }

-- 具体的: 读法取常值 1
lvShape₁ : LvShape azero
lvShape₁ = Shape.lvShape azero (λ _ → hs hz) (λ _ → hz) (λ _ → tt)
```

## §2 嫌疑 (i): Ω-极限层上没有与世界无关的层证据

`hA` 把 `A` 的元素读成 `Ht` 里的同形高度; Ω-极限层 $L = \mathrm{h\Omega}\,\kappa_A\,h_A$ (种类 $\kappa_A$ 的坐标是 `A`, 界在世界的 `A`-分量里). $L$ 合法.

```agda
hA : A → Ht
hA azero = hz
hA (asuc a) = hs (hA a)
hA (alim f) = hl (λ n → hA (f n))

hA-mono : ∀ {c c′ : A} {W : Wd₂} → c ⊲ c′ → hA c ⊲[ W ] hA c′
hA-mono C.self = hself
hA-mono (C.suc p) = hsuc (hA-mono p)
hA-mono (C.lim n p) = hlim n (hA-mono p)

lg-hA : ∀ c → Lg c → LgB (hA c)
lg-hA azero l = tt
lg-hA (asuc c) l = lg-hA c l
lg-hA (alim f) (st , l) = (λ n → hA-mono (st n)) , (λ n → lg-hA (f n) (l n))

LΩ : Ht
LΩ = hΩ κA hA

Lg-LΩ : LgB LΩ
Lg-LΩ = (λ lw e e′ pr → hA-mono pr) , (λ c lc → lg-hA c lc)

-- 分支 1 没有对一切世界的证据
no-unifΩ : ¬ (∀ {W : Wd₂} → hs hz ⊲[ W ] LΩ)
no-unifΩ u = h (u {azero , hz})
  where
  bad : ∀ {c} → c ⊲ azero → hs hz ⊲[ azero , hz ] hA c → ⊥
  bad C.self ()
  h : hs hz ⊲[ azero , hz ] LΩ → ⊥
  h (hLim e q) = bad e q

-- 世界的 A-分量在 1 之上时有
acc-ev : ∀ {W : Wd₂} → asuc azero ⊲ proj₁ W → hs hz ⊲[ W ] LΩ
acc-ev e = hLim {κ = κA} {c = asuc azero} e hself
```

**按可入性给值要判定裸分支.** `ωA` 是 `A` 里的 $\omega$. `xα α` 是合法的 `A`-极限: $\alpha$ 尚未为真时第 $n$ 项是 $n$, 之后是 $n+1$. 若对一切合法的 `A`-元素可判定 "在 $\omega$ 之下" (即世界的 `A`-分量取 $\omega$ 时的可入性), 就得到分离子; 有 $\mathbb N\to A$ 的外延时得到 WLPO.

```agda
finA : ℕ → A
finA zero = azero
finA (suc n) = asuc (finA n)

ωA : A
ωA = alim finA

pk : Bool → ℕ → A
pk false n = finA n
pk true n = finA (suc n)

xh : (ℕ → Bool) → ℕ → A
xh α n = pk (or α n) n

xα : (ℕ → Bool) → A
xα α = alim (xh α)

lg-finA : ∀ n → Lg (finA n)
lg-finA zero = tt
lg-finA (suc n) = lg-finA n

stp : ∀ b c n → pk b n ⊲ pk (Data.Bool._∨_ b c) (suc n)
stp true c n = C.suc C.self
stp false false n = C.suc C.self
stp false true n = C.suc (C.suc C.self)

lgp : ∀ b n → Lg (pk b n)
lgp false n = lg-finA n
lgp true n = lg-finA (suc n)

Lg-xα : ∀ α → Lg (xα α)
Lg-xα α = (λ n → stp (or α n) (α (suc n)) n) , (λ n → lgp (or α n) n)

Lg-ωA : Lg ωA
Lg-ωA = (λ n → C.suc C.self) , lg-finA

-- 极限不在有限之下
IsFin : A → Set
IsFin azero = ⊤
IsFin (asuc a) = IsFin a
IsFin (alim _) = ⊥

isFin : ∀ n → IsFin (finA n)
isFin zero = tt
isFin (suc n) = isFin n

noLimFin : ∀ {g x} → alim g ⊲ x → IsFin x → ⊥
noLimFin C.self ()
noLimFin (C.suc p) f = noLimFin p f
noLimFin (C.lim n p) ()

unlim : A → ℕ → A
unlim (alim f) = f
unlim _ = λ _ → azero

unsucA : A → A
unsucA (asuc a) = a
unsucA a = a

fs≢ : ∀ n → ¬ (finA (suc n) ≡ finA n)
fs≢ zero ()
fs≢ (suc n) e = fs≢ n (cong unsucA e)

-- xα ⊲ ωA 只能是 self, 于是逐项相等
lem : ∀ α {x y} → x ⊲ y → y ≡ ωA → x ≡ xα α → ∀ n → xh α n ≡ finA n
lem α C.self ey ex n = cong (λ t → unlim t n) (trans (sym ex) ey)
lem α (C.suc p) () ex n
lem α (C.lim {f = f} m p) ey ex n =
  ⊥-elim (noLimFin (subst (λ t → t ⊲ f m) ex p) (subst IsFin (sym (cong (λ t → unlim t m) ey)) (isFin m)))

allF : ∀ α → (∀ n → xh α n ≡ finA n) → ∀ n → α n ≡ false
allF α h n with α n in eq
... | false = refl
... | true = ⊥-elim (fs≢ n (trans (sym (cong (λ b → pk b n) (or-in α n eq))) (h n)))

decAcc-sep : (∀ a → Lg a → Dec (a ⊲ ωA)) → ∀ α → (∀ n → α n ≡ false) ⊎ ¬ (xα α ≡ ωA)
decAcc-sep D α with D (xα α) (Lg-xα α)
... | yes p = inj₁ (allF α (lem α p refl refl))
... | no np = inj₂ (λ e → np (subst (λ t → xα α ⊲ t) e C.self))

FEA : Set
FEA = ∀ (f g : ℕ → A) → (∀ n → f n ≡ g n) → f ≡ g

xα≡ : FEA → ∀ α → (∀ n → α n ≡ false) → xα α ≡ ωA
xα≡ fe α h = cong alim (fe (xh α) finA (λ n → cong (λ b → pk b n) (or-false α h n)))

decAcc→WLPO : FEA → (∀ a → Lg a → Dec (a ⊲ ωA)) → WLPO
decAcc→WLPO fe D α with decAcc-sep D α
... | inj₁ h = inj₁ h
... | inj₂ ne = inj₂ (λ h → ne (xα≡ fe α h))
```

## §3 嫌疑 (iii): 混合高度的级数是数据; 拷贝的界不能折到一级

```agda
lvl : K Gω → ℕ
lvl = proj₁

κ1 κ2 : K Gω
κ1 = 1 , inj₂ tt
κ2 = 2 , inj₁ (inj₂ tt)

K₂ : K (Sk 2)
K₂ = inj₁ (inj₂ tt)

-- 每一级的一个世界 (最小的分量)
wd : ∀ n → Wd (Sk n)
wd zero = azero
wd (suc n) = wd n , hz

-- Gω 的世界: 第 1 份拷贝的界是 0, 第 2 份拷贝的界是 1
w⋆ : Wd Gω
w⋆ zero = azero
w⋆ (suc zero) = azero , hz
w⋆ (suc (suc zero)) = (azero , hs hz) , hz
w⋆ (suc (suc (suc n))) = wd (suc (suc (suc n)))

no-wmatch-ω : ∀ (wm : Wd Gω → Wd (Sk 2)) →
  (∀ {c w} → Bd Gω κ2 c w → Bd (Sk 2) K₂ c (wm w)) →
  (∀ {c w} → Bd (Sk 2) K₂ c (wm w) → Bd Gω κ1 c w) → ⊥
no-wmatch-ω wm h2 h1 with h1 {hs hz} {w⋆} (h2 {hs hz} {w⋆} hself)
... | ()

-- 两个前提各自可满足: 只保一份拷贝时, 世界映射取那一个分量
sat-2 : Σ (Wd Gω → Wd (Sk 2)) (λ wm → (∀ {c w} → Bd Gω κ2 c w → Bd (Sk 2) K₂ c (wm w)) × (∀ {c w} → Bd (Sk 2) K₂ c (wm w) → Bd Gω κ2 c w))
sat-2 = (λ w → w 2) , (λ e → e) , (λ e → e)

sat-1 : Σ (Wd Gω → Wd (Sk 2)) (λ wm → (∀ {c w} → Bd Gω κ1 c w → Bd (Sk 2) K₂ c (wm w)) × (∀ {c w} → Bd (Sk 2) K₂ c (wm w) → Bd Gω κ1 c w))
sat-1 = (λ w → (w 1 , hz)) , (λ e → e) , (λ e → e)
```

**记录本身平凡可满足.** 接口的 `RdC` 与 `Dn` 作为类型不空: 读回取恒等 (底是第一位置, 合法保持), 翻译取 `n0`; 下降取常值 $0$. 有信息的是构造一路选的具体读回, 不是记录.

```agda
rdcTriv : ∀ T L → RdC T L
rdcTriv T L = record { rdr = λ lW b x → b ; fst = λ lW b x → hself ; lgr = λ lW b x l → l ; tr = λ x → n0 }

dnTriv : ∀ T → Dn T
dnTriv T = (λ _ → hz) , (λ x l → tt)
```

## §4 结论 (按档)

- **[定理]** **`no-faithful`**, `no-faithful-shape` (对一切读法); 前提实例 `Shape.lvShape`, `lvShape₁`.
- **[定理]** `Lg-LΩ`, **`no-unifΩ`**, `acc-ev`: Ω-极限层的非底分支没有与世界无关的证据, 世界够大时有.
- **[定理]** `Lg-xα`, `Lg-ωA`, **`decAcc-sep`** (分离子); **[定理, 条件 `FEA`]** **`decAcc→WLPO`**.
- **[定理]** `lvl` (定义), **`no-wmatch-ω`**, `sat-1`, `sat-2`.
- **[定理]** `rdcTriv`, `dnTriv`: 记录 `RdC`, `Dn` 平凡可满足.
- **[判断]** `no-unifΩ` 落在 "读回包对高度递归" 的下一步上: 接口 `PkgΩ` 只到 $\omega+1$, 层是后继与 ℕ-极限, `trK` 的证据形状够用; 层号由回灌给出之后, 层里会出现 `A`-分支的 Ω-极限 (`σ-of` 的值域是一般的 `HB S₀`), 那里翻译旧种类要读世界, `D` 现有的读世界的结点只有第 0, 1 级的闭包 `nκ`, `nμ`.
