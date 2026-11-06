# 最高层含与站层号同形的层, 否定一路 (一): 接口之前

> 不含记号. 入口 [NegLamIso](NegLamIso.lagda.md). 本篇**不依赖**构造一路的接口 `LamIsoIf` (接口定稿之前写的部分). 只导入 [LeanTBase](LeanTBase.lagda.md), [LeanTLv](LeanTLv.lagda.md), [LeanFbIf](LeanFbIf.lagda.md), [LeanFbSt](LeanFbSt.lagda.md), 已定稿的 [LeanLvIf](LeanLvIf.lagda.md) §6 (`Sim⁺`), 与否定一路旧文件 [NegLeanLvPre](NegLeanLvPre.lagda.md) 的规范读法 `ofL`, `_≈_` (都不改). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延 (连前提也没有).
>
> **问题** (作者本轮选定 "②: 最高层 Λ 含与站层号同形的层"). 构造一路要写新的最高层 $\Lambda'$, 对一切世界字面地含与每一站层号 `st n` 同形 (`Sim⁺`) 的层 $L_n$. `LeanLv` 接手清单第 1 条的难点判断: "$L_n$ 的 $\Omega$-结点要用站 $n-1$ 的种类; 按在 `st (n-1)` 里的路径选拷贝时, `hΩ` 处不同分支用不同分量的拷贝, 分支间不再是第一位置". 本篇:
>
> 1. **难点写成定理 (§1, §3).** **`path-illegal`** (对一切种类结构): $\Omega$-结点在某个合法世界里有界内的一对 $c\lhd c'$, 若分支 $g\,c$ 含某类种类的结点而 $g\,c'$ 不含, 则这个结点不合法. 原因只有一条: 第一位置继承种类 (**`has⊲`**). 实例 **`pathcopy-illegal`** (第 3 站): 顶种类为头 0 的层, 若第 $e$ 支只用第 2 站分量 `inj₂ e` 的拷贝 ("按路径选拷贝"), 且第 $1$ 支确实用了分量 `inj₂ 1` 的拷贝, 则不合法. 前提实例 **`Lpath`**: 字面上与 `st 3` 有 `Sim⁺` (`sim-Lpath`) 且满足两条前提. 对照 **`Lone`**: 同样的分支, 一切分支都用同一个分量的拷贝, 合法 (`Lg-Lone`) 且与 `st 3` 有 `Sim⁺` (`sim-Lone`).
> 2. **对角 (§2, §4).** **`diag-illegal`**: $\mathbb N$-极限的相邻两项若种类不继承, 不合法. **`station-diag-illegal`** (`no-naive-diag` 的站版): 第 $n$ 项只用第 $\sigma\,n$ 站的种类, 第 $n$ 项确有第 $\sigma\,n$ 站的结点, $\sigma\,n\ne\sigma(n+1)$, 则对角不合法. 实例 **`indep-col-illegal`**: 每一项单独合法 (`Lg-col`), 与 `st k` 有 `Sim⁺` (`col-sim`), 只用第 $\sigma\,k$ 站的头作种类; 只要某处 $\sigma(2+n)\ne\sigma(3+n)$ (例如 $\sigma=$ 恒等, 或 "站 $k-1$"), 对角不合法. 所以 $\Lambda'$ 里的同形层若在对角上排, 种类必须逐项继承 (**`has-chain`**).
> 3. **盲: `Sim⁺` 这个判据本身挡不住退化的 $\Lambda'$ (§5).** **`ΛC`** (对任一种类 $\kappa_0$): 把 `tw n` 的每个 $\Omega$-结点换成 $\kappa_0$ 的常值结点 (分支取原来的底坐标处) 得到 `col (tw n)`; 对角 `ΛC` **合法** (`Lg-ΛC`), 对一切世界字面地含每一个 `col (tw n)` (`ΛC-fst`), 且 `col (tw n)` 与 `st n` 有 `Sim⁺` (`ΛC-sim`, 坐标映射是常值). 整棵 $\Lambda_C$ 只用一个种类 (`col-kind`). 所以 "对一切世界字面含与 `st n` 同形的层" 若只按 `LeanLvIf` 的 `Sim⁺` (坐标映射任意) 验, 对一切 $n$ 都能用一个种类满足, 与合法性、`no-naive-diag` 都不冲突; 它不说明读回能按自己的级读出任何种类. 规范读法分得开: **`col3-not-own`**: `ofL (col (tw 3))` 与 `st 3` 不外延相等 (取 $\kappa_0$ = 头 0).
>
> **只否定什么.** `path-illegal`, `pathcopy-illegal` 只否定: $\Omega$-结点的两个可比分支所含种类不继承 (具体: 各分支只用 "按路径" 的分量的拷贝). **不否定**: 按 "级" 全局一致地选拷贝 (例如分支 $c'$ 把分支 $c$ 原样接在前面, 再在后面用新的拷贝, $\hat\Omega$ 式的 $\boxplus$); `Lone` 说明只要不按路径换分量, 同样的骨架合法. `station-diag-illegal` 只否定对角的相邻项种类不继承, **不否定**累加 ($P_{n+1}=P_n\boxplus\cdots$) 或逐项继承的链 ($L_n\lhd L_{n+1}$). `ΛC` 是盲定理, 不否定任何路线, 只说明 `Sim⁺` (任意坐标映射) 不足以当 "按自己的级" 的判据. 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLamIsoPre where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanFbIf
open import OCF.Lean.LeanFbSt renaming (st to stL)
open import OCF.Lean.LeanLvIf using (Sim⁺; sz⁺; ss⁺; sl⁺; sΩ⁺)
open import OCF.Lean.NegLeanLvPre using (ofL; _≈_; ≈-≡; ⊲hz; tw-shape)
```

## §1 第一位置继承种类; 分支间不继承就不合法

`HasP P x`: $x$ 里有一个种类满足 $P$ 的 $\Omega$-结点 (同 `LeanLvIf.HasK`, 换成谓词).

```agda
module _ {S : KS} (P : K S → Set) where
  data HasP : HB S → Set where
    here : ∀ {κ g} → P κ → HasP (hΩ κ g)
    inS  : ∀ {a} → HasP a → HasP (hs a)
    inL  : ∀ {f} n → HasP (f n) → HasP (hl f)
    inΩ  : ∀ {κ g} c → HasP (g c) → HasP (hΩ κ g)

  has⊲ : ∀ {a b w} → HasP a → a ⊲[ w ] b → HasP b
  has⊲ h hself = h
  has⊲ h (hsuc p) = inS (has⊲ h p)
  has⊲ h (hlim n p) = inL n (has⊲ h p)
  has⊲ h (hLim e p) = inΩ _ (has⊲ h p)

  no-fst : ∀ {a b w} → HasP a → ¬ HasP b → ¬ (a ⊲[ w ] b)
  no-fst h nh p = nh (has⊲ h p)

  -- Ω-结点: 界内可比的两支, 前一支有而后一支没有 ⟹ 不合法
  path-illegal : ∀ {κ g w c c′} → LgW S w → Bd S κ c w → Bd S κ c′ w → Pr S κ w c c′ →
                 HasP (g c) → ¬ HasP (g c′) → ¬ LgB (hΩ κ g)
  path-illegal lw e e′ p h nh (mo , _) = no-fst h nh (mo lw e e′ p)
```

## §2 $\mathbb N$-极限: 相邻项不继承就不合法; 合法的对角逐项继承

```agda
  diag-illegal : ∀ {f : ℕ → HB S} n → HasP (f n) → ¬ HasP (f (suc n)) → ¬ LgB (hl f)
  diag-illegal n h nh (st , _) = no-fst h nh (st {w₀ S} n)

  has-chain : ∀ {f : ℕ → HB S} {w} → (∀ n → f n ⊲[ w ] f (suc n)) → ∀ k n → HasP (f n) → HasP (f (k + n))
  has-chain s zero n h = h
  has-chain s (suc k) n h = has⊲ (has-chain s k n h) (s (k + n))
```

## §3 第 3 站: 按路径选拷贝的层不合法

层在 `L₀ = step SLs`. 第 2 站的种类 `K (FS 2)` 的旧种类 `inj₁ (i , κ)` 落在 `Lv (st 2) = Lv (lΩ lz g₂)` 的分量 $i$ : `⊤ ⊎ HB S⊥` 里. `InC2 i`: 种类是第 2 站分量 $i$ 里的拷贝.

```agda
L₀ : KS
L₀ = step SLs

g₂ : HB S⊥ → LH
g₂ c = ofHB (hs hz ⊞ ι {LH} {FL} lz (up c))

g₃ : HB S⊥ → LH
g₃ c = ofHB (Ω̂ (hs hz ⊞ ι {LH} {FL} lz (up c)))

st3-shape : stL 3 ≡ lΩ lz g₃
st3-shape = refl

Ix2 : Set
Ix2 = ⊤ ⊎ HB S⊥

InC2 : Ix2 → K L₀ → Set
InC2 i (inj₁ (suc (suc zero) , inj₁ (i′ , _))) = i′ ≡ i
InC2 i _ = ⊥

-- 每个分量里取一个种类
anyK : (c : HB S⊥) → K (Lv (g₂ c))
anyK hz = inj₂ tt
anyK (hs c) = inj₂ tt
anyK (hl f) = 0 , anyK (f 0)
anyK (hΩ (() , _) g)

kC : Ix2 → K L₀
kC (inj₁ tt) = inj₁ (2 , inj₁ (inj₁ tt , inj₂ tt))
kC (inj₂ c) = inj₁ (2 , inj₁ (inj₂ c , anyK c))

kC-in : ∀ i i′ → InC2 i′ (kC i) → i ≡ i′
kC-in (inj₁ tt) i′ p = p
kC-in (inj₂ c) i′ p = p

-- 头 0 的种类 (坐标 HB S⊥)
kν0 : K L₀
kν0 = inj₁ (νS 0)
```

**分支 `B i e`.** 只用分量 $i$ 的拷贝, 与 `g₃ e` 有 `Sim⁺` (内层坐标映射取常值 $0$).

```agda
B : Ix2 → HB S⊥ → HB L₀
B i hz = hΩ (kC i) (λ _ → hs hz)
B i (hs j) = hΩ (kC i) (λ _ → B i j)
B i (hl f) = hl (λ n → B i (f n))
B i (hΩ (() , _) g)

simB : ∀ i e → Sim⁺ SLs (B i e) (g₃ e)
simB i hz = sΩ⁺ (λ _ → hz) (λ _ → ss⁺ sz⁺) (λ _ → inj₂ tt)
simB i (hs j) = sΩ⁺ (λ _ → hz) (λ _ → simB i j) (λ _ → inj₂ tt)
simB i (hl f) = sl⁺ (λ n → simB i (f n)) (λ _ → inj₂ tt)
simB i (hΩ (() , _) g)

onlyB : ∀ i i′ e → HasP (InC2 i′) (B i e) → i ≡ i′
onlyB i i′ hz (here p) = kC-in i i′ p
onlyB i i′ hz (inΩ c (inS ()))
onlyB i i′ (hs j) (here p) = kC-in i i′ p
onlyB i i′ (hs j) (inΩ c h) = onlyB i i′ j h
onlyB i i′ (hl f) (inL n h) = onlyB i i′ (f n) h
onlyB i i′ (hΩ (() , _) g) h
```

**合法世界.** 头 0 的界升到 $2$ (`headUp 0`); 坐标 $1\lhd 2$ 都在界内.

```agda
W2 : Wd L₀
W2 = bumpH 0 (hs (hs hz)) (w₀ SLs) , hz

lW2 : LgW L₀ W2
lW2 = rzLg (headUp 0) {δ = hs (hs hz)} {w = w₀ SLs} tt (lw₀ SLs) , tt

two≢one : ¬ (_≡_ {A = Ix2} (inj₂ (hs (hs hz))) (inj₂ (hs hz)))
two≢one ()
```

**定理 `pathcopy-illegal`.** 顶是头 0 的 $\Omega$-结点; 第 $e$ 支只用分量 `inj₂ e` 的拷贝; 第 $1$ 支确有分量 `inj₂ 1` 的拷贝 ⟹ 不合法.

```agda
pathcopy-illegal : ∀ (g : HB S⊥ → HB L₀) →
  HasP (InC2 (inj₂ (hs hz))) (g (hs hz)) →
  (∀ e i → HasP (InC2 i) (g e) → inj₂ e ≡ i) →
  ¬ LgB (hΩ kν0 g)
pathcopy-illegal g h only =
  path-illegal (InC2 (inj₂ (hs hz))) {κ = kν0} {g = g} {w = W2} {c = hs hz} {c′ = hs (hs hz)}
    lW2 (hsuc hself) hself (hsuc hself) h (λ h′ → two≢one (only (hs (hs hz)) (inj₂ (hs hz)) h′))
```

**前提实例 `Lpath`.** 第 $e$ 支取 `B (inj₂ e) e`. 与 `st 3` 有 `Sim⁺` (顶的坐标映射是恒等).

```agda
Lpath : HB L₀
Lpath = hΩ kν0 (λ e → B (inj₂ e) e)

sim-Lpath : Sim⁺ SLs Lpath (stL 3)
sim-Lpath = sΩ⁺ (λ e → e) (λ e → simB (inj₂ e) e) (λ _ → inj₂ tt)

Lpath-illegal : ¬ LgB Lpath
Lpath-illegal = pathcopy-illegal (λ e → B (inj₂ e) e) (here refl) (λ e i h → onlyB (inj₂ e) i e h)
```

**对照 `Lone`.** 一切分支用同一个分量 $i_0$ 的拷贝: 合法, 同形.

```agda
B-step : ∀ i j {w} → B i j ⊲[ w ] B i (hs j)
B-step i j {w} = hLim (botBd L₀ (kC i) w) hself

B-mono : ∀ i {v e e′} → e ⊲[ v ] e′ → ∀ {w} → B i e ⊲[ w ] B i e′
B-mono i hself = hself
B-mono i (hsuc p) = ⊲ᴮ-tr (B-mono i p) (B-step i _)
B-mono i (hlim n p) = hlim n (B-mono i p)
B-mono i (hLim {κ = () , _} e p)

Lg-B : ∀ i e → LgB e → LgB (B i e)
Lg-B i hz _ = (λ _ _ _ _ → hself) , (λ _ _ → tt)
Lg-B i (hs j) l = (λ _ _ _ _ → hself) , (λ _ _ → Lg-B i j l)
Lg-B i (hl f) (st , l) = (λ n → B-mono i (st {w₀ S⊥} n)) , (λ n → Lg-B i (f n) (l n))
Lg-B i (hΩ (() , _) g) l

Lone : Ix2 → HB L₀
Lone i₀ = hΩ kν0 (λ e → B i₀ e)

Lg-Lone : ∀ i₀ → LgB (Lone i₀)
Lg-Lone i₀ =
  (λ lw e e′ p → B-mono i₀ p) ,
  (λ {W} {c} lw e → Lg-B i₀ c (lgB⊲ e (proj₁ (proj₁ lw 0)) (proj₂ (proj₁ lw 0))))

sim-Lone : ∀ i₀ → Sim⁺ SLs (Lone i₀) (stL 3)
sim-Lone i₀ = sΩ⁺ (λ e → e) (λ e → simB i₀ e) (λ _ → inj₂ tt)
```

## §4 站版的 `no-naive-diag`

`InSt m`: 种类是第 $m$ 站的 (头或旧种类).

```agda
InSt : ℕ → K L₀ → Set
InSt m (inj₁ (m′ , _)) = m′ ≡ m
InSt m (inj₂ _) = ⊥

station-diag-illegal : ∀ (f : ℕ → HB L₀) (σ : ℕ → ℕ) n →
  HasP (InSt (σ n)) (f n) →
  (∀ m → HasP (InSt m) (f (suc n)) → m ≡ σ (suc n)) →
  ¬ (σ n ≡ σ (suc n)) → ¬ LgB (hl f)
station-diag-illegal f σ n h only ne =
  diag-illegal (InSt (σ n)) {f = f} n h (λ h′ → ne (only (σ n) h′))
```

前提实例在 §5 之后 (`indep-col-illegal`).

## §5 盲: 一个种类的 $\Lambda_C$

**底世界的界只有底坐标** (`BaseBot`): 对 `Lv k`, `SL`, `SLs`, `L₀` 都成立. 由此 "对一切世界是第一位置" 只能沿底坐标走 (同 `NegLeanLvPre.lvl-cases` 的原因).

```agda
BaseBot : KS → Set
BaseBot S = ∀ κ {c} → Bd S κ c (w₀ S) → c ≡ bot S κ

bb-step : ∀ {S} → BaseBot S → BaseBot (step S)
bb-step b (inj₁ κ) e = b κ e
bb-step b (inj₂ _) e = ⊲hz e

bb-Lv : ∀ k → BaseBot (Lv k)
bb-Lv lz (() , _) e
bb-Lv (ls x) κ e = bb-step (bb-Lv x) κ e
bb-Lv (ll f) (n , κ) e = bb-Lv (f n) κ e
bb-Lv (lΩ k g) (inj₁ _ , κ) e = bb-step (bb-Lv k) κ e
bb-Lv (lΩ k g) (inj₂ c , κ) e = bb-Lv (g c) κ e

bb-SL : BaseBot SL
bb-SL (k , κ) e = bb-step (bb-Lv k) κ e

bb-SLs : BaseBot SLs
bb-SLs (m , κ) e = bb-step (bb-Lv (stL m)) κ e

bb-L₀ : BaseBot L₀
bb-L₀ = bb-step bb-SLs
```

**塌缩 `col κ₀`.** `HB SL` 的高度, 每个 $\Omega$-结点换成种类 $\kappa_0$ 的常值结点, 值取原来底坐标处的分支.

```agda
module Col (κ₀ : K L₀) where
  col : HB SL → HB L₀
  col hz = hz
  col (hs a) = hs (col a)
  col (hl f) = hl (λ n → col (f n))
  col (hΩ κ g) = hΩ κ₀ (λ _ → col (g (bot SL κ)))

  col-⊲  : ∀ {a b} → a ⊲[ w₀ SL ] b → ∀ {W} → col a ⊲[ W ] col b
  col-⊲′ : ∀ {a κ} {g : E SL κ → HB SL} {c} → c ≡ bot SL κ → a ⊲[ w₀ SL ] g c → ∀ {W} → col a ⊲[ W ] col (g (bot SL κ))
  col-⊲ hself = hself
  col-⊲ (hsuc p) = hsuc (col-⊲ p)
  col-⊲ (hlim n p) = hlim n (col-⊲ p)
  col-⊲ (hLim {κ = κ} e p) {W} = hLim (botBd L₀ κ₀ W) (col-⊲′ (bb-SL κ e) p)
  col-⊲′ refl p = col-⊲ p

  Lg-col : ∀ a → LgB a → LgB (col a)
  Lg-col hz l = tt
  Lg-col (hs a) l = Lg-col a l
  Lg-col (hl f) (st , l) = (λ n → col-⊲ (st {w₀ SL} n)) , (λ n → Lg-col (f n) (l n))
  Lg-col (hΩ κ g) (mo , l) =
    (λ _ _ _ _ → hself) , (λ _ _ → Lg-col (g (bot SL κ)) (l (lw₀ SL) (botBd SL κ (w₀ SL))))

  -- 只用一个种类
  col-kind : ∀ a {P : K L₀ → Set} → HasP P (col a) → P κ₀
  col-kind hz ()
  col-kind (hs a) (inS h) = col-kind a h
  col-kind (hl f) (inL n h) = col-kind (f n) h
  col-kind (hΩ κ g) (here p) = p
  col-kind (hΩ κ g) (inΩ c h) = col-kind (g (bot SL κ)) h
```

**同形.** `col a` 与 `ofHB a` 有 `Sim⁺` (坐标映射取常值 $0$, 不带后继种类). 旧种类的结点经 `node` 下降, 对 `node` 的同一递归.

```agda
  simNode : ∀ k κ (h : E (Lv k) κ → LH) {x} → Sim⁺ SLs x (h (bot (Lv k) κ)) → Sim⁺ SLs (hΩ κ₀ (λ _ → x)) (node k κ h)
  simNode lz (() , _) h s
  simNode (ls y) (inj₁ κ) h s = simNode y κ h s
  simNode (ls y) (inj₂ _) h s = sΩ⁺ (λ _ → hz) (λ _ → s) (λ _ → inj₂ tt)
  simNode (ll f) (n , κ) h s = simNode (f n) κ h s
  simNode (lΩ k g) (inj₁ _ , inj₁ κ) h s = simNode k κ h s
  simNode (lΩ k g) (inj₁ _ , inj₂ _) h s = sΩ⁺ (λ _ → hz) (λ _ → s) (λ _ → inj₂ tt)
  simNode (lΩ k g) (inj₂ c , κ) h s = simNode (g c) κ h s

  col-sim : ∀ a → Sim⁺ SLs (col a) (ofHB a)
  col-sim hz = sz⁺
  col-sim (hs a) = ss⁺ (col-sim a)
  col-sim (hl f) = sl⁺ (λ n → col-sim (f n)) (λ _ → inj₂ tt)
  col-sim (hΩ (k , inj₂ _) g) = sΩ⁺ (λ _ → hz) (λ _ → col-sim (g hz)) (λ _ → inj₂ tt)
  col-sim (hΩ (k , inj₁ κ) g) = simNode k κ (λ c → ofHB (g c)) (col-sim (g (bot (Lv k) κ)))
```

**$\Lambda_C$.** 合法, 对一切世界字面含每个 `col (tw n)`, 后者与 `st n` 同形.

```agda
  ΛC : HB L₀
  ΛC = hl (λ n → col (tw n))

  Lg-ΛC : LgB ΛC
  Lg-ΛC = (λ n → col-⊲ (tw-st {w₀ SL} n)) , (λ n → Lg-col (tw n) (Lg-tw n))

  ΛC-fst : ∀ n {w} → col (tw n) ⊲[ w ] ΛC
  ΛC-fst n = hlim n hself

  ΛC-sim : ∀ n → Sim⁺ SLs (col (tw n)) (stL n)
  ΛC-sim n = col-sim (tw n)
```

**前提实例 (§4): 各站各写一层, 对角不合法.** 第 $k$ 项是 `col (νS (σ k)) (tw k)`: 单独合法, 与 `st k` 同形, 只用第 $\sigma\,k$ 站的头.

```agda
open Col using (col; col-kind; Lg-col; col-sim)

col-has : ∀ κ₀ m → HasP (λ κ → κ ≡ κ₀) (col κ₀ (tw (suc (suc m))))
col-has κ₀ m = subst (λ t → HasP (λ κ → κ ≡ κ₀) (col κ₀ t)) (sym (proj₁ (proj₂ (tw-shape m)))) (here refl)

has-map : ∀ {S : KS} {P Q : K S → Set} → (∀ κ → P κ → Q κ) → ∀ {x : HB S} → HasP {S} P x → HasP {S} Q x
has-map {S} {P} {Q} pq (here p) = here (pq _ p)
has-map {S} {P} {Q} pq (inS h) = inS (has-map {S} {P} {Q} pq h)
has-map {S} {P} {Q} pq (inL n h) = inL n (has-map {S} {P} {Q} pq h)
has-map {S} {P} {Q} pq (inΩ c h) = inΩ c (has-map {S} {P} {Q} pq h)

indep-col-illegal : ∀ (σ : ℕ → ℕ) n → ¬ (σ (2 + n) ≡ σ (3 + n)) →
  ¬ LgB (hl (λ k → col (inj₁ (νS (σ k))) (tw k)))
indep-col-illegal σ n ne =
  station-diag-illegal (λ k → col (inj₁ (νS (σ k))) (tw k)) σ (2 + n)
    (has-map {L₀} {λ κ → κ ≡ inj₁ (νS (σ (2 + n)))} {InSt (σ (2 + n))} (λ { κ refl → refl }) (col-has (inj₁ (νS (σ (2 + n)))) n))
    (λ m h → sym (col-kind (inj₁ (νS (σ (3 + n)))) (tw (3 + n)) {P = InSt m} h))
    ne

-- 每一项单独合法, 同形
indep-col-each : ∀ (σ : ℕ → ℕ) k → LgB (col (inj₁ (νS (σ k))) (tw k)) × Sim⁺ SLs (col (inj₁ (νS (σ k))) (tw k)) (stL k)
indep-col-each σ k = Lg-col (inj₁ (νS (σ k))) (tw k) (Lg-tw k) , col-sim (inj₁ (νS (σ k))) (tw k)

-- 两个 σ 的实例: 恒等, 与 "站 k-1"
pred′ : ℕ → ℕ
pred′ zero = zero
pred′ (suc k) = k

indep-id : ¬ LgB (hl (λ k → col (inj₁ (νS k)) (tw k)))
indep-id = indep-col-illegal (λ k → k) 0 (λ ())

indep-pred : ¬ LgB (hl (λ k → col (inj₁ (νS (pred′ k))) (tw k)))
indep-pred = indep-col-illegal pred′ 0 (λ ())
```

## §6 规范读法分得开 `col` 与 `st 3`

`lz ≡ lz` 的证明都是 `refl` (编码-解码, 不用 K).

```agda
Code : LH → Set
Code lz = ⊤
Code (ls _) = ⊥
Code (ll _) = ⊥
Code (lΩ _ _) = ⊥

dec : ∀ y → Code y → lz ≡ y
dec lz _ = refl
dec (ls _) ()
dec (ll _) ()
dec (lΩ _ _) ()

de : ∀ {y} (e : lz ≡ y) → dec y (subst Code e tt) ≡ e
de refl = refl

lz-refl : (e : lz ≡ lz) → e ≡ refl
lz-refl e = sym (de e)

subst-id : (e : lz ≡ lz) (c : HB S⊥) → subst (λ x → HB (Lv x)) e c ≡ c
subst-id e c = cong (λ e′ → subst (λ x → HB (Lv x)) e′ c) (lz-refl e)

col3-not-own : ¬ (ofL (col kν0 (tw 3)) ≈ stL 3)
col3-not-own (e , q) = bad (≈-≡ _ (q (hs (hs hz))) (cong g₃ (subst-id e (hs (hs hz)))))
  where
  bad : ¬ (lΩ lz (λ _ → ls lz) ≈ g₃ (hs (hs hz)))
  bad (() , _)
```

**前提实例.** `col3-not-own` 无前提. 对照: `ΛC-sim 3` 给出同一个 `col kν0 (tw 3)` 与 `st 3` 的 `Sim⁺`. 所以 `Sim⁺` (坐标映射任意) 比规范读法的外延相等弱, 后者要求每个 $\Omega$-结点的种类的级与层号的首项一致.

## §7 结论 (按档)

- **[定理, 一般]** `has⊲`, `no-fst`, **`path-illegal`**, **`diag-illegal`**, `has-chain`, `BaseBot` 与 `bb-L₀` (底世界里界只有底坐标).
- **[定理, 否定, 实例]** **`pathcopy-illegal`** (第 3 站按路径选第 2 站分量的拷贝: 不合法), 前提实例 `Lpath` (`sim-Lpath`: 与 `st 3` 有 `Sim⁺`; `Lpath-illegal`). **`station-diag-illegal`**, **`indep-col-illegal`**, `indep-id`, `indep-pred` (各站各写同形层再取对角: 不合法; 每项单独合法且同形: `indep-col-each`).
- **[定理, 正面对照]** `Lone`, `Lg-Lone`, `sim-Lone` (同一骨架用同一分量: 合法, 同形).
- **[定理, 盲]** **`ΛC`**, `Lg-ΛC`, `ΛC-fst`, `ΛC-sim`, `col-kind`: 对任一种类 $\kappa_0$, 有合法的 $\Lambda_C$ 对一切世界字面含与每个 `st n` 有 `Sim⁺` 的层, 且只用 $\kappa_0$ 一个种类. **`col3-not-own`**: 规范读法不认它.
- **[判断]** (i) "按级全局一致地选拷贝" 对一般的 $n$ 是否可写, 本篇没有定理; `Lone` 只说明第 3 站的骨架在不换分量时合法. (ii) `ΛC` 说明构造一路的接口若只要 `Sim⁺`, 应另加对坐标映射的要求 (例如坐标映射是种类坐标的嵌入, 或规范读法的外延相等), 否则 "同形" 不约束读回; 这是给接口的建议, 不是定理.
