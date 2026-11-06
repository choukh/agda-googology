# 路径记在折叠输出上, 否定一路 (一): Fab4LOm §5 的三条判断写成定理

> 不含记号. 入口 [NegPathOut](NegPathOut.lagda.md). 本篇**不依赖**构造一路的接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** [Fab4LOm](Fab4LOm.lagda.md) §5 对 "lΩ 层号上坐标要带路径" 列了三种写法, 都标为判断 (未走通): (1) 层号带界, 共尾度变了; (2) 高度带 "在世界里" 的谓词, 与 "链要越过界" 冲突; (3) 分支依赖证据, 链要把输入搬到更大的世界. 本篇把能写成定理的部分写成定理.
>
> **结果.**
>
> 1. **`escape` (定理, 对一切种类结构 `S`, 一切世界).** $d\neq0$ (`NZ d`) 时 $b\boxplus d$ 不是 $b$ 的第一位置. 推论 **`fab3-escape`**: [Fab3Typed](Fab3Typed.lagda.md) 的链在世界 $(w,b)$ 里用的第 $n+1$ 个坐标 $b\boxplus d_n$ **不在这个世界的界之下** (`¬ Bd (step T) (inj₂ tt) _ (w , b)`), 对一切 `T`, $w$, $b$, 分支, $n$. 这是 §5 三条共同的起点, 现在是定理.
> 2. **第 2 条 (高度带 "在世界里" 谓词), 三种读法各一条定理.** 层号取 `lΩ lz G` ($G$ 任意). 一个高度 "在界 $b$ 里", 指它的每个种类 $(\mathrm{inj}_2\,c',\kappa)$ 有 $c'\lhd b$.
>    - **`inWA-out` (否定).** 谓词对 $\Omega_1$-结点的**一切**分支遗传 (`InWᴬ`): 只要某个分支 $g\,c$ 提到自己的坐标 $c$ 且 $c\not\lhd b$, 谓词就不成立; 于是 "分支在 $c$ 处提到坐标 $c$" 的结点 (例如 `D κ`, 读 $\sup_c\Omega_{c+1}$ 的形状, 判断) 对**任何**界都不在世界里 (`inWA-D`).
>    - **`inWB-D` (构造) 与 `inWB-chain-out` (否定).** 谓词只对界之下的分支遗传 (`InWᴮ`): `D κ` 对任何界都满足; 但链在界 $b$ 下要递归的分支 $g\,(b\boxplus d)$ 不满足 (由 `escape`). "对界外的分支无话可说" 是定理.
>    - **`no-grow` (否定) 与 `inWC-D` (构造).** 谓词让分支换一个**更大的合法界** (`InWᴳ`: 分支 $c$ 处给出合法的 $B$, $b\lhd B$, 分支在 $B$ 里): 只要 $b=\lim\mathrm{ev}$ 且分支在 $\lim\mathrm{od}$ 处提到坐标 $\lim\mathrm{od}$, 就推出 $\lim\mathrm{ev}$, $\lim\mathrm{od}$ 有合法的字面公共上界, 与 `HtTowerNeg.no-joinᴮ` 矛盾. 反过来, 只对**链的坐标** $b\boxplus d$ 换界 (`InWᶜ`, 新界就是 $b\boxplus d$ 自己) 时 `D κ` 满足 (`inWC-D`): 这就是 Fab4LOm 说的出口 "让链点自带路径", 现在是一条构造.
> 3. **第 1 条 (层号带界) 的结构对照 (定理, 平凡).** 坐标限制在界 $b$ 之下 (非严格, 同 `step` 的 `Bd⁺`) 且分支单调时, 分支在 $b$ 处取到最大 (`bd-max`); 而无界的 `lΩ lz G` (Fab4LOm 的 $G\,c=c+1$) 没有最大分支 (`unbd-no-max`). 这说的是 "有最大元" 与 "没有", 不是序数值的定理; "值变了" 仍是判断.
> 4. **第 3 条 (分支依赖证据).** 以世界为下标的结点只在 $c\lhd b$ 的坐标上有分支; 链要的坐标 $b\boxplus d$ 不在其中, 就是 `escape`. "更大的世界的分支小世界的树给不出" 的其余部分 (扩张不唯一) 本篇没有写成定理 (要函数外延才能陈述两个扩张相等的限制), 仍是判断.
>
> **前提实例.** `escape` 的 `NZ`: Fab3Typed 的 `Ψ` 从不输出 $0$ (`Ψ-NZ`), 链点也不 (`chain-NZ`). `inWA-out`, `inWB-chain-out`, `no-grow` 的 "分支提到坐标": 实例 `D κ₁` (`G₁ c = c+1` 即 Fab4LOm 的 `G`, `κ₁ c = inj₂ tt`, `ment-D`). `no-grow` 的界 $\lim\mathrm{ev}$ 合法 (`Lg-ev`). `bd-max` 的单调: 常值分支 (`bd-max-inst`).
>
> **只否定什么.** 只否定: (a) 对 $\Omega_1$-结点的一切分支在同一界下遗传的 "在世界里" 谓词, 用在分支提到自己坐标的高度上; (b) 只对界下分支遗传的谓词能覆盖链的分支; (c) 分支处换成任意更大合法界的谓词, 用在 $\lim\mathrm{ev}$ 与 $\lim\mathrm{od}$ 这一对上. **不否定**: 只对链坐标换界的谓词 (`inWC-D` 是构造); 谓词与 `InWᴮ` 合用 (界下分支用旧界, 链坐标用新界); 不按谓词组织的折叠. 本篇没有关闭任何路线.
>
> **对纲领与目标.** 纲领 3: `no-grow` 是壁垒的又一个影子: 想让每个分支都有一个同时盖住旧界与新坐标的合法界, 就是要字面的并. 目标: 这几条把 Fab4LOm 的判断换成 "树自己说的" 定理: 链的坐标越过界 (`escape`), 越过之后只有链坐标自己能当新界 (`inWC-D`). 它们不涉及记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegPathOutWorld where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥; LH; lz; ls; ll; lΩ; Lv)
open import OCF.Align.StallDxBdec using (_<ᴮ_; <s₀; <s; <l₀; <l; <Ω₀; <Ω; wf; irr; toLt; lt→≢)
open import OCF.Align.NegTySupSel using (lt-tr)
open import OCF.Align.HtTowerNeg using (evᴴ; odᴴ; Lg-ev; Lg-od; no-joinᴮ)
open import OCF.Align.Fab3Typed using (module Fold)
open import OCF.Align.TySupC using (ofC)
open import OCF.Align.Fab4LOm using (_⊑ᴸ_; _⊏ᴸ_; ⊑self; ⊑suc) renaming (irr to irrᴸ)
```

## §1 链的坐标越过界

`NZ d`: $d$ 不是 $0$. `fst≤`: $b$ 是 $b\boxplus d$ 本身或它的严格子项 (不要世界). `⊞-strict`: $d\neq0$ 时严格.

```agda
module _ {S : KS} where
  infix 4 _≺_
  _≺_ : HB S → HB S → Set
  _≺_ = _<ᴮ_ {S}

  NZ : HB S → Set
  NZ hz = ⊥
  NZ (hs _) = ⊤
  NZ (hl _) = ⊤
  NZ (hΩ _ _) = ⊤

  NZ-⊞ : ∀ a b → NZ b → NZ (a ⊞ b)
  NZ-⊞ a (hs b) _ = tt
  NZ-⊞ a (hl f) _ = tt
  NZ-⊞ a (hΩ κ g) _ = tt

  fst≤ : ∀ b d → (b ≡ b ⊞ d) ⊎ (b ≺ b ⊞ d)
  fst≤ b hz = inj₁ refl
  fst≤ b (hs d) with fst≤ b d
  ... | inj₁ e = inj₂ (subst (λ z → b ≺ hs z) e <s₀)
  ... | inj₂ q = inj₂ (<s q)
  fst≤ b (hl f) with fst≤ b (f 0)
  ... | inj₁ e = inj₂ (subst (λ z → z ≺ hl (λ n → b ⊞ f n)) (sym e) (<l₀ 0))
  ... | inj₂ q = inj₂ (<l 0 q)
  fst≤ b (hΩ κ g) with fst≤ b (g (bot S κ))
  ... | inj₁ e = inj₂ (subst (λ z → z ≺ hΩ κ (λ c → b ⊞ g c)) (sym e) (<Ω₀ (bot S κ)))
  ... | inj₂ q = inj₂ (<Ω (bot S κ) q)

  ⊞-strict : ∀ b d → NZ d → b ≺ b ⊞ d
  ⊞-strict b (hs d) _ with fst≤ b d
  ... | inj₁ e = subst (λ z → b ≺ hs z) e <s₀
  ... | inj₂ q = <s q
  ⊞-strict b (hl f) _ with fst≤ b (f 0)
  ... | inj₁ e = subst (λ z → z ≺ hl (λ n → b ⊞ f n)) (sym e) (<l₀ 0)
  ... | inj₂ q = <l 0 q
  ⊞-strict b (hΩ κ g) _ with fst≤ b (g (bot S κ))
  ... | inj₁ e = subst (λ z → z ≺ hΩ κ (λ c → b ⊞ g c)) (sym e) (<Ω₀ (bot S κ))
  ... | inj₂ q = <Ω (bot S κ) q
```

**定理 `escape`.** $d\neq0$ 时 $b\boxplus d\not\lhd b$ (任一世界). 证明: 第一位置要么相等要么严格子项 (`toLt`), 两种都与 $b<b\boxplus d$ 矛盾 (子项关系良基).

```agda
  escape : ∀ {w} b d → NZ d → ¬ (b ⊞ d ⊲[ w ] b)
  escape b d nz p with toLt p
  ... | inj₁ e = lt→≢ {S} (⊞-strict b d nz) (sym e)
  ... | inj₂ q = irr {S} (wf {S} _) (lt-tr {S} q (⊞-strict b d nz))
```

**Fab3Typed 的链.** `Ψ` 从不输出 $0$, 所以链点都不是 $0$; 链的第 $n+1$ 个坐标 $b\boxplus d_n$ 不在世界 $(w,b)$ 的新种类界之下.

```agda
module Fab3Esc (T : KS) where
  open Fold T using (Ψ; chain; L)

  Ψ-NZ : ∀ W h → NZ (Ψ W h)
  Ψ-NZ W hz = tt
  Ψ-NZ W (hs h) = tt
  Ψ-NZ W (hl f) = tt
  Ψ-NZ W (hΩ (inj₁ κ) g) = tt
  Ψ-NZ W (hΩ (inj₂ _) g) = tt

  chain-NZ : ∀ w b (g : HB T → HB L) n → NZ (chain w b (λ W′ c → Ψ W′ (g c)) n)
  chain-NZ w b g zero = Ψ-NZ _ _
  chain-NZ w b g (suc n) = NZ-⊞ _ _ (Ψ-NZ _ _)

  fab3-escape : ∀ w b (g : HB T → HB L) n →
                ¬ Bd L (inj₂ tt) (b ⊞ chain w b (λ W′ c → Ψ W′ (g c)) n) (w , b)
  fab3-escape w b g n = escape b _ (chain-NZ w b g n)
```

## §2 "在世界里的高度": 三种读法

层号 `X = lΩ lz G`. 它的种类: $\Omega_1$ (`Ω₁ = (inj₁ tt , inj₂ tt)`, 坐标是可数高度) 与 $(\mathrm{inj}_2\,c',\kappa)$ (第 $c'$ 个分量 `Lv (G c′)` 的种类, 以坐标 $c'$ 为下标). `Ment c h`: $h$ 里有一个下标为 $c$ 的种类的结点 (沿后继, ℕ-极限的某项, 任一分支). `Ment⁰`: 同上但不经 $\Omega_1$-结点.

```agda
module LOm (G : HB S⊥ → LH) where
  X : LH
  X = lΩ lz G

  SX : KS
  SX = Lv X

  Ω₁ : K SX
  Ω₁ = inj₁ tt , inj₂ tt

  Ment : HB S⊥ → HB SX → Set
  Ment c hz = ⊥
  Ment c (hs h) = Ment c h
  Ment c (hl f) = Σ ℕ (λ n → Ment c (f n))
  Ment c (hΩ (inj₁ _ , inj₁ ()) g)
  Ment c (hΩ (inj₁ _ , inj₂ _) g) = Σ (HB S⊥) (λ e → Ment c (g e))
  Ment c (hΩ (inj₂ c′ , κ) g) = (c′ ≡ c) ⊎ Σ (E (Lv (G c′)) κ) (λ e → Ment c (g e))

  Ment⁰ : HB S⊥ → HB SX → Set
  Ment⁰ c hz = ⊥
  Ment⁰ c (hs h) = Ment⁰ c h
  Ment⁰ c (hl f) = Σ ℕ (λ n → Ment⁰ c (f n))
  Ment⁰ c (hΩ (inj₁ _ , inj₁ ()) g)
  Ment⁰ c (hΩ (inj₁ _ , inj₂ _) g) = ⊥
  Ment⁰ c (hΩ (inj₂ c′ , κ) g) = (c′ ≡ c) ⊎ Σ (E (Lv (G c′)) κ) (λ e → Ment⁰ c (g e))
```

**读法 A: 对一切分支在同一界下遗传.**

```agda
  InWᴬ : HB S⊥ → HB SX → Set
  InWᴬ b hz = ⊤
  InWᴬ b (hs h) = InWᴬ b h
  InWᴬ b (hl f) = ∀ n → InWᴬ b (f n)
  InWᴬ b (hΩ (inj₁ _ , inj₁ ()) g)
  InWᴬ b (hΩ (inj₁ _ , inj₂ _) g) = ∀ e → InWᴬ b (g e)
  InWᴬ b (hΩ (inj₂ c′ , κ) g) = (c′ ⊲[ tt ] b) × (∀ e → InWᴬ b (g e))

  mentA : ∀ {b c} h → Ment c h → InWᴬ b h → c ⊲[ tt ] b
  mentA hz () i
  mentA (hs h) m i = mentA h m i
  mentA (hl f) (n , m) i = mentA (f n) m (i n)
  mentA (hΩ (inj₁ _ , inj₁ ()) g) m i
  mentA (hΩ (inj₁ _ , inj₂ _) g) (e , m) i = mentA (g e) m (i e)
  mentA (hΩ (inj₂ c′ , κ) g) (inj₁ refl) i = proj₁ i
  mentA (hΩ (inj₂ c′ , κ) g) (inj₂ (e , m)) i = mentA (g e) m (proj₂ i e)

  inWA-out : ∀ b c (g : HB S⊥ → HB SX) → ¬ (c ⊲[ tt ] b) → Ment c (g c) → ¬ InWᴬ b (hΩ Ω₁ g)
  inWA-out b c g nc m i = nc (mentA (g c) m (i c))
```

**读法 B: 只对界之下的分支遗传.**

```agda
  InWᴮ : HB S⊥ → HB SX → Set
  InWᴮ b hz = ⊤
  InWᴮ b (hs h) = InWᴮ b h
  InWᴮ b (hl f) = ∀ n → InWᴮ b (f n)
  InWᴮ b (hΩ (inj₁ _ , inj₁ ()) g)
  InWᴮ b (hΩ (inj₁ _ , inj₂ _) g) = ∀ e → e ⊲[ tt ] b → InWᴮ b (g e)
  InWᴮ b (hΩ (inj₂ c′ , κ) g) = (c′ ⊲[ tt ] b) × (∀ e → InWᴮ b (g e))

  mentB : ∀ {b c} h → Ment⁰ c h → InWᴮ b h → c ⊲[ tt ] b
  mentB hz () i
  mentB (hs h) m i = mentB h m i
  mentB (hl f) (n , m) i = mentB (f n) m (i n)
  mentB (hΩ (inj₁ _ , inj₁ ()) g) m i
  mentB (hΩ (inj₁ _ , inj₂ _) g) () i
  mentB (hΩ (inj₂ c′ , κ) g) (inj₁ refl) i = proj₁ i
  mentB (hΩ (inj₂ c′ , κ) g) (inj₂ (e , m)) i = mentB (g e) m (proj₂ i e)

  -- 链在界 b 下要递归的分支 g (b ⊞ d) 不在界 b 里
  inWB-chain-out : ∀ b d (g : HB S⊥ → HB SX) → NZ d → Ment⁰ (b ⊞ d) (g (b ⊞ d)) → ¬ InWᴮ b (g (b ⊞ d))
  inWB-chain-out b d g nz m i = escape b d nz (mentB (g (b ⊞ d)) m i)
```

**读法 G: 分支处换一个更大的合法界.** 分支 $c$ 处给出合法的 $B$ 且 $b\lhd B$ (外层的种类仍在界下, 目标的路径仍可用), 分支在 $B$ 里. `mentG`: 提到的坐标与外层的界有合法的字面公共上界.

```agda
  InWᴳ : HB S⊥ → HB SX → Set
  InWᴳ b hz = ⊤
  InWᴳ b (hs h) = InWᴳ b h
  InWᴳ b (hl f) = ∀ n → InWᴳ b (f n)
  InWᴳ b (hΩ (inj₁ _ , inj₁ ()) g)
  InWᴳ b (hΩ (inj₁ _ , inj₂ _) g) = ∀ e → Σ (HB S⊥) (λ B → LgB B × (b ⊲[ tt ] B) × InWᴳ B (g e))
  InWᴳ b (hΩ (inj₂ c′ , κ) g) = (c′ ⊲[ tt ] b) × (∀ e → InWᴳ b (g e))

  mentG : ∀ {b c} h → LgB b → Ment c h → InWᴳ b h →
          Σ (HB S⊥) (λ B → LgB B × (b ⊲[ tt ] B) × (c ⊲[ tt ] B))
  mentG hz lb () i
  mentG (hs h) lb m i = mentG h lb m i
  mentG (hl f) lb (n , m) i = mentG (f n) lb m (i n)
  mentG (hΩ (inj₁ _ , inj₁ ()) g) lb m i
  mentG (hΩ (inj₁ _ , inj₂ _) g) lb (e , m) i with i e
  ... | B , lB , bB , i′ with mentG (g e) lB m i′
  ...   | B′ , lB′ , BB′ , cB′ = B′ , lB′ , ⊲ᴮ-tr bB BB′ , cB′
  mentG {b} (hΩ (inj₂ c′ , κ) g) lb (inj₁ refl) i = b , lb , hself , proj₁ i
  mentG (hΩ (inj₂ c′ , κ) g) lb (inj₂ (e , m)) i = mentG (g e) lb m (proj₂ i e)

  no-grow : ∀ (g : HB S⊥ → HB SX) → Ment (hl odᴴ) (g (hl odᴴ)) → ¬ InWᴳ (hl evᴴ) (hΩ Ω₁ g)
  no-grow g m i with i (hl odᴴ)
  ... | B , lB , eB , i′ with mentG (g (hl odᴴ)) lB m i′
  ...   | B′ , lB′ , BB′ , oB′ = no-joinᴮ {S⊥} {tt} tt (B′ , lB′ , ⊲ᴮ-tr eB BB′ , oB′)
```

**读法 C: 只对链的坐标换界, 新界就是链坐标自己.** Ω₁-结点处对一切 $d$, 分支 $g\,(b\boxplus d)$ 在界 $b\boxplus d$ 里; 新界盖住旧界是字面的 (`⊞-fst`).

```agda
  InWᶜ : HB S⊥ → HB SX → Set
  InWᶜ b hz = ⊤
  InWᶜ b (hs h) = InWᶜ b h
  InWᶜ b (hl f) = ∀ n → InWᶜ b (f n)
  InWᶜ b (hΩ (inj₁ _ , inj₁ ()) g)
  InWᶜ b (hΩ (inj₁ _ , inj₂ _) g) = ∀ d → InWᶜ (b ⊞ d) (g (b ⊞ d))
  InWᶜ b (hΩ (inj₂ c′ , κ) g) = (c′ ⊲[ tt ] b) × (∀ e → InWᶜ b (g e))

  old⊲new : ∀ b d → b ⊲[ tt ] b ⊞ d
  old⊲new b d = ⊞-fst {S⊥} {tt} b d
```

**实例: 分支提到自己坐标的结点.** `dep κ c` 是第 $c$ 个分量的种类 $\kappa\,c$ 的结点 (分支取 $0$); `D κ` 是 $\Omega_1$-结点, 分支 $c$ 处是 `dep κ c`. 读法 (判断): $\sup_c \Omega_{c+1}$ 的形状. 它满足 B 与 C, 不满足 A (任何界), 不满足 G (界 $\lim\mathrm{ev}$).

```agda
  dep : (κ : (c : HB S⊥) → K (Lv (G c))) → HB S⊥ → HB SX
  dep κ c = hΩ (inj₂ c , κ c) (λ _ → hz)

  D : (κ : (c : HB S⊥) → K (Lv (G c))) → HB SX
  D κ = hΩ Ω₁ (dep κ)

  ment-D : ∀ κ c → Ment c (dep κ c)
  ment-D κ c = inj₁ refl

  ment⁰-D : ∀ κ c → Ment⁰ c (dep κ c)
  ment⁰-D κ c = inj₁ refl

  inWA-D : ∀ κ b → ¬ InWᴬ b (D κ)
  inWA-D κ b = inWA-out b (hs b) (dep κ) (escape b (hs hz) tt) (ment-D κ (hs b))

  inWB-D : ∀ κ b → InWᴮ b (D κ)
  inWB-D κ b e p = p , (λ _ → tt)

  inWB-D-chain-out : ∀ κ b d → NZ d → ¬ InWᴮ b (dep κ (b ⊞ d))
  inWB-D-chain-out κ b d nz = inWB-chain-out b d (dep κ) nz (ment⁰-D κ (b ⊞ d))

  no-grow-D : ∀ κ → ¬ InWᴳ (hl evᴴ) (D κ)
  no-grow-D κ = no-grow (dep κ) (ment-D κ (hl odᴴ))

  inWC-D : ∀ κ b → InWᶜ b (D κ)
  inWC-D κ b d = hself , (λ _ → tt)
```

前提实例: Fab4LOm 的 $G_1\,c=c+1$ (`ls (ofC c)`) 每个分量都有新种类 `inj₂ tt`, 所以 `κ₁` 存在, 上面的定理都有实例.

```agda
G₁ : HB S⊥ → LH
G₁ c = ls (ofC c)

κ₁ : (c : HB S⊥) → K (Lv (G₁ c))
κ₁ c = inj₂ tt

module L₁ = LOm G₁

inst-A : ∀ b → ¬ L₁.InWᴬ b (L₁.D κ₁)
inst-A = L₁.inWA-D κ₁

inst-B : ∀ b → L₁.InWᴮ b (L₁.D κ₁)
inst-B = L₁.inWB-D κ₁

inst-G : ¬ L₁.InWᴳ (hl evᴴ) (L₁.D κ₁)
inst-G = L₁.no-grow-D κ₁

inst-C : ∀ b → L₁.InWᶜ b (L₁.D κ₁)
inst-C = L₁.inWC-D κ₁
```

## §3 第 1 条: 带界的节点有最大分支, 无界的没有

`bd-max`: 坐标在界 $b$ 之下 (非严格), 分支 $g$ 单调, 则一切分支在 $g\,b$ 之下; $b$ 本身是界下的坐标 (`hself`). 这就是单调性本身, 写出来只为对照. `unbd-no-max`: 无界的 `lΩ lz G₁` 的分支没有最大的 ($G_1(c+1)=G_1\,c+1$).

```agda
bd-max : ∀ (g : HB S⊥ → LH) → (∀ {a c} → a ⊲[ tt ] c → g a ⊑ᴸ g c) →
         ∀ {b c} → c ⊲[ tt ] b → (g c ⊑ᴸ g b) × (b ⊲[ tt ] b)
bd-max g mo p = mo p , hself

bd-max-inst : ∀ {b c} → c ⊲[ tt ] b → ((λ (_ : HB S⊥) → lz) c ⊑ᴸ lz) × (b ⊲[ tt ] b)
bd-max-inst = bd-max (λ _ → lz) (λ _ → ⊑self)

unbd-no-max : ∀ c₀ → ¬ (∀ c → G₁ c ⊑ᴸ G₁ c₀)
unbd-no-max c₀ h = irrᴸ (G₁ c₀) (h (hs c₀))
```

## 结论 (按档)

- **[定理]** `NZ`, `NZ-⊞`, `fst≤`, `⊞-strict`, **`escape`** (对一切 `S`); `Fab3Esc.Ψ-NZ`, `chain-NZ`, **`fab3-escape`** (对一切 `T`); `LOm.Ment`, `Ment⁰`, `InWᴬ`, `InWᴮ`, `InWᴳ`, `InWᶜ`, `mentA`, `mentB`, `mentG`, **`inWA-out`**, **`inWB-chain-out`**, **`no-grow`**, `dep`, `D`, `inWA-D`, `inWB-D`, `inWB-D-chain-out`, `no-grow-D`, **`inWC-D`** (构造); 实例 `inst-A`, `inst-B`, `inst-G`, `inst-C`; `bd-max`, `bd-max-inst`, `unbd-no-max`.
- **[判断]** `D κ` 读 $\sup_c\Omega_{c+1}$; Fab4LOm 第 1 条的 "值变了" (本篇只给有无最大分支); 第 3 条的 "扩张给不出" (本篇只给 `escape`).
