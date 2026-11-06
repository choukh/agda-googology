# X₂ 与往 `tw n`, 否定一路 (二): $X_2$ 的种类, 决定要的界, 叠层结构的搬运

> 不含记号. 入口 [NegX2](NegX2.lagda.md). 本篇**不依赖**构造一路的接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延 `FE₁` 只在标 "条件" 的定理里作前提.
>
> **问题.** $X_2=$ `lΩ lz (λ c → ls (ofU c))` (`ofU c` 是 $X_1\oplus c$, [NegX1UpEmb](NegX1UpEmb.lagda.md)). 它的分支 $c$ 是第 $X_1\oplus c+1$ 层, 里面有 $X_1$ 的种类 (底种类的拷贝) 与叠层的新种类 (层号 $X_1\oplus j$, $j\le c$). 构造一路要把可数折叠推广到带底种类 (`X1UpFold.ΦU` 的形状), 在 $X_2$ 的折叠 "在上" 之后调用. 本篇问: 在 $X_2$ 里各类种类对目标的决定要什么界; `X1UpFold` 的叠层结构 `LS` 与 `Lv ∘ ofU` 之间是否要搬运.
>
> **结果.**
>
> 1. **`no-exact-base-X₂` (定理, 对一切 $c$).** $X_2$ 的分支 $c$ 里 $X_1$ 的种类 $\kappa(c_1)$ 的拷贝, 对可数目标 $t_1$ **没有**精确的决定 (由 `exact→cmp`, `incomp-lim`, `lvl-emb`). 所以 $X_2$ 的折叠折到可数目标时, $X_1$ 内部的比较 (PathOut 的世界与证据) 要在 $X_2$ 的每个分支里再做一次; 拷贝的证据要按 $c$ 递归读出 (同 `NegX1UpEmb.EvU`).
> 2. **`no-exact-new-X₂` (定理).** $X_2$ 的两个叠层新种类来自不同的 `lΩ` 坐标 ($\lim\mathrm{od}$ 的第 $X_1\oplus\lim\mathrm{od}$ 层新种类, 对目标 $X_1\oplus\lim\mathrm{ev}$): **没有**精确的决定. **`no-fixed-m` (定理).** 没有一个可数 $m$ 让一切坐标 $c$ 都有 $c+1\lhd m$. 合起来: `X1UpFold.decU` 用的公共上界 (折叠所在的叠层层号 $m$) 在 $X_2$ 里不存在, 新种类之间的比较也要 `lΩ` 坐标上的世界 (PathOut 式的界 $B$, $c+1\lhd B$); 有合法的公共上界时比较是构造 (`NegX1UpCmp.cmp-new`).
> 3. **`ofU⊏X₂`, `X₁⊏X₂` (定理).** 一切 $X_1\oplus c$ 字面严格在 $X_2$ 之下 (2 的目标是合法的子层号).
> 4. **叠层结构的搬运.** `X1UpFold` 对一般的底 `XS` 写叠层 `LS`; $X_2$ 的分支用 `Lv (ofU c)`. 二者逐子句同式, 但是两个函数:
>    - **`LS≡LU` (定理, 条件 `FE₁`).** 有函数外延时对一切 $c$ 相等; ℕ-极限一步要外延.
>    - **`toU`, `toS`, `kU`, `kS` (构造), `kS-kU`, `kU-kS` (定理, 无条件).** 不用外延的搬运: 树与种类按 $c$ 与树互递归地搬, 种类往返恒等 (命题等式, 对 $c$ 归纳). 每个子句的类型字面对上, 不用 `subst`.
>    - **[测试, 元层]** 有限的 $c$ 上 `LS c` 与 `Lv (ofU c)` 字面相同 (`LS≡LU-3`, `refl`); 对**闭的** $\omega=\lim_n n$, `refl` 不通过 (草稿 `scratch/negx2/OmegaRefl.agda`, 报 `UnequalTerms`): `LS (hl f)` 展开到 `sup ℕ (λ n → LS (f n))`, 分量里的 `f n` 对变量 $n$ 卡住. 所以 "搬运不是 refl" 不只发生在变量层号上, 在闭的 ℕ-极限偏移上就发生. 这一条是关于 Agda 定义等同的元层事实, 不能写成对象层的定理.
>
> **前提实例.** 1: 对一切 $c$ (例如 $c=0$); `Lg-c₁`, `Lg-t₀` (坐标合法, `NegPathOutCmp`). 2: `nat-od`, `nat-ev` (`HtTowerNeg`); `hl odᴴ`, `hl evᴴ` 都合法 (`Lg-od`, `Lg-ev`). 4: `FE₁` 是函数外延的一个实例, 与本系统相容 (有外延的模型里成立).
>
> **只否定什么.** 1, 2 只否定**精确** (蕴含字面可比) 的决定在没有公共上界的种类与目标对上; `no-fixed-m` 只否定 "一个固定的可数界盖住 $X_2$ 的一切坐标". **不否定**: 带世界证据的决定 (PathOut 的 `correct₁` 是同一类构造); 在合法公共上界之下的比较 (`cmp-new`); 用 `toU`/`toS` 把 `ΦU` 接到 $X_2$ 上 (4 是构造, 要不要还取决于构造一路的写法). 本篇没有关闭任何路线.
>
> **对构造一路 (判断, 依据 1-4).** $X_2$ 的折叠 (折到可数目标) 要的东西是: PathOut 的世界 (界 $B$) 盖住 `lΩ` 坐标 $c$, 用它比较叠层新种类 (2) 与 $X_1$ 拷贝里的种类 (1); "在上" 到第 $X_1\oplus j$ 层之后, 从 $X_1\oplus j$ 折到可数目标要经 $X_1$ (底种类全留, 再交给 `PathOutFold.Ψ`), 后者要输入带路径. 所以 "去掉 `noK` 的可数折叠" 若要在 "在上" 之后折到**可数**目标, 自己就要带路径 (由 `NegX1UpCmp.no-exact-up`: 叠层上底种类对可数目标无精确决定); 若只折到叠层目标 (`ΦU` 的做法), 要在外面再接 `Ψ`. 若构造一路把 $X_2$ 的分支结构写成 `Lv ∘ ofU` 而折叠写在 `LS` 上, 就要 4 的搬运, 路径 (`PSL`) 也要跟着搬.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegX2Lv where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥; LH; lz; ls; ll; lΩ; Lv; lvl)
open import OCF.Align.TySupIf using (Dc)
open import OCF.Align.TySupC using (Cd; ofC)
open import OCF.Align.HtTowerNeg using (evᴴ; odᴴ; nat-ev; nat-od)
open import OCF.Align.Fab4LOm using (_⊑ᴸ_; _⊏ᴸ_; ⊑self; ⊑suc; ⊑lim; ⊑om; ⊑ᴸ-tr; Exact; κ; t₁; irr)
open import OCF.Align.NegPathOutCmp using (CmpL; exact→cmp; incomp-lim; u₁; v₁; c₁; s≢z; ofC-mono)
open import OCF.Align.PathOutX1 using (X₁; XS₁)
open import OCF.Align.NegX1UpEmb using (ofU; LU; embB; lvl-emb)
open import OCF.Align.NegX1UpCmp using (incomp-new-od-ev; X₁⊑U)
open import OCF.Align.X1Up using (IU)
import OCF.Align.X1UpFold as UF
open UF IU using (LS)
```

## §1 层号 $X_2$

```agda
X₂ : LH
X₂ = lΩ lz (λ c → ls (ofU c))

XS₂ : KS
XS₂ = Lv X₂

ofU⊏X₂ : ∀ c → ofU c ⊏ᴸ X₂
ofU⊏X₂ c = ⊑om c ⊑self

X₁⊏X₂ : X₁ ⊏ᴸ X₂
X₁⊏X₂ = ⊑om hz ⊑self
```

## §2 $X_1$ 的拷贝: 对可数目标没有精确的决定

`κb c`: $X_2$ 的分支 $c$ 里, $X_1$ 的种类 $\kappa(c_1)$ 的拷贝 (经 `embB c`).

```agda
κb : HB S⊥ → K XS₂
κb c = inj₂ c , inj₁ (embB c (κ c₁))

no-exact-base-X₂ : ∀ c (d : Dc Lv _⊏ᴸ_ _⊑ᴸ_ X₂ t₁ (κb c)) → ¬ Exact (κb c) d
no-exact-base-X₂ c d ex =
  incomp-lim u₁ v₁ (λ _ → tt) (λ _ → tt) s≢z
    (subst (λ w → CmpL w t₁) (lvl-emb c (κ c₁)) (exact→cmp {X₂} d ex))
```

## §3 叠层新种类: 没有固定的公共上界

`κn c`: $X_2$ 的分支 $c$ 的顶种类 (第 $X_1\oplus c$ 层的新种类, 层号字面是 `ofU c`).

```agda
κn : HB S⊥ → K XS₂
κn c = inj₂ c , inj₂ tt

lvl-κn : ∀ c → lvl X₂ (κn c) ≡ ofU c
lvl-κn c = refl

no-exact-new-X₂ : (d : Dc Lv _⊏ᴸ_ _⊑ᴸ_ X₂ (ofU (hl evᴴ)) (κn (hl odᴴ))) → ¬ Exact (κn (hl odᴴ)) d
no-exact-new-X₂ d ex = incomp-new-od-ev (exact→cmp {X₂} d ex)

-- 目标是 X₂ 的合法子层号
pt-ev : ofU (hl evᴴ) ⊑ᴸ X₂
pt-ev = ⊑ᴸ-tr (⊑suc ⊑self) (ofU⊏X₂ (hl evᴴ))

no-fixed-m : ∀ (m : HB S⊥) → ¬ (∀ c → hs c ⊲[ tt ] m)
no-fixed-m m all = irr (ofC m) (ofC-mono (all m))
```

## §4 叠层结构: `LS` 与 `Lv ∘ ofU`

**条件定理.** `FE₁`: 以 `ℕ` 为定义域、值在 `KS` 的函数外延.

```agda
FE₁ : Set₁
FE₁ = ∀ {F G : ℕ → KS} → (∀ n → F n ≡ G n) → F ≡ G

module _ (fe : FE₁) where
  LS≡LU : ∀ c → LS c ≡ LU c
  LS≡LU hz = refl
  LS≡LU (hs x) = cong step (LS≡LU x)
  LS≡LU (hl f) = cong (sup ℕ) (fe (λ n → LS≡LU (f n)))
  LS≡LU (hΩ () _)
```

**测试 (有限层号).** `refl`.

```agda
three : Cd
three = hs (hs (hs hz))

LS≡LU-3 : LS three ≡ LU three
LS≡LU-3 = refl
```

**不用外延的搬运 (构造).** 树按 $c$ 与树互递归; 进入新种类的分支时坐标往反方向搬 (`eS`, `eU`).

```agda
kU : ∀ c → K (LS c) → K (LU c)
kS : ∀ c → K (LU c) → K (LS c)
toU : ∀ c → HB (LS c) → HB (LU c)
toS : ∀ c → HB (LU c) → HB (LS c)
eS : ∀ c κ → E (LU c) (kU c κ) → E (LS c) κ
eU : ∀ c κ → E (LS c) (kS c κ) → E (LU c) κ

kU hz κ = κ
kU (hs x) (inj₁ κ) = inj₁ (kU x κ)
kU (hs x) (inj₂ _) = inj₂ tt
kU (hl f) (n , κ) = n , kU (f n) κ
kU (hΩ () _) _

kS hz κ = κ
kS (hs x) (inj₁ κ) = inj₁ (kS x κ)
kS (hs x) (inj₂ _) = inj₂ tt
kS (hl f) (n , κ) = n , kS (f n) κ
kS (hΩ () _) _

toU c hz = hz
toU c (hs h) = hs (toU c h)
toU c (hl f) = hl (λ n → toU c (f n))
toU c (hΩ κ g) = hΩ (kU c κ) (λ e → toU c (g (eS c κ e)))

toS c hz = hz
toS c (hs h) = hs (toS c h)
toS c (hl f) = hl (λ n → toS c (f n))
toS c (hΩ κ g) = hΩ (kS c κ) (λ e → toS c (g (eU c κ e)))

eS hz κ e = e
eS (hs x) (inj₁ κ) e = eS x κ e
eS (hs x) (inj₂ _) e = toS x e
eS (hl f) (n , κ) e = eS (f n) κ e
eS (hΩ () _) _ _

eU hz κ e = e
eU (hs x) (inj₁ κ) e = eU x κ e
eU (hs x) (inj₂ _) e = toU x e
eU (hl f) (n , κ) e = eU (f n) κ e
eU (hΩ () _) _ _
```

**种类往返恒等 (定理, 无条件).** 对 $c$ 归纳.

```agda
kS-kU : ∀ c κ → kS c (kU c κ) ≡ κ
kS-kU hz κ = refl
kS-kU (hs x) (inj₁ κ) = cong inj₁ (kS-kU x κ)
kS-kU (hs x) (inj₂ _) = refl
kS-kU (hl f) (n , κ) = cong (λ z → n , z) (kS-kU (f n) κ)
kS-kU (hΩ () _) _

kU-kS : ∀ c κ → kU c (kS c κ) ≡ κ
kU-kS hz κ = refl
kU-kS (hs x) (inj₁ κ) = cong inj₁ (kU-kS x κ)
kU-kS (hs x) (inj₂ _) = refl
kU-kS (hl f) (n , κ) = cong (λ z → n , z) (kU-kS (f n) κ)
kU-kS (hΩ () _) _
```

## 结论 (按档)

- **[定理]** `X₂`, `XS₂`, `ofU⊏X₂`, `X₁⊏X₂`; `κb`, **`no-exact-base-X₂`**; `κn`, `lvl-κn`, **`no-exact-new-X₂`**, `pt-ev`, **`no-fixed-m`**; `kU`, `kS`, `toU`, `toS`, `eS`, `eU` (构造), **`kS-kU`**, **`kU-kS`**.
- **[条件]** **`LS≡LU`** (条件 `FE₁`).
- **[测试]** `LS≡LU-3` (有限层号, `refl`); 草稿 `OmegaRefl.agda`: 闭的 $\omega$ 上 `refl` 不通过 (元层).
- **[判断]** 文件头 "对构造一路" 一段.
