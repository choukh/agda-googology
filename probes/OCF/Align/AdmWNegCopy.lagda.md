# 可入下标比较式更新的否定 (一): 拷贝墙, 对一切种类结构

> 不含记号. 入口 [AdmWNeg](AdmWNeg.lagda.md). 配合 [Survey/StallDiagnosis.md](../../Survey/StallDiagnosis.md) §2.4, §3.3 义务 1, §5.1 第二条引理. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 入口的 `¬CmpK-Inst` 用的是接口 `AdmWIf` 固定的 `Prᴮ` (某个证据的分量里的第一位置). 这一篇把同一件事写成**不依赖 `Prᴮ` 的选法**的形式: 构造一路若改了 `Pr` (或改了 `KS` 以容纳 `SupB`, 例如去掉 `botBd`), 只要得到的种类结构 $T$ 含下面的形状, 结论照样成立.
>
> - **`copy-core`** (对一切种类结构): 合法的 $\Omega$-分支 $g$ 在同一个合法世界里, 界之下的两个坐标的像必须字面可比. 一行, 来自 `cmpK` 与单调.
> - **`CopyShape T`**: $T$ 的一个种类, 坐标是 `A`; 世界 `W₂ a₀ a₁` 里, $a_0$ 之下的坐标经第一个证据有界 (`bd₀`), $a_1$ 之下的坐标经第二个证据有界 (`bd₁`); 分量里的合法节点 `hΩ tt toH` 经 `ι` 的像在 $T$ 里合法 (`lgι`).
> - **`need-cmp`**: 任一合法的 `W₂ a₀ a₁` 里, 两个证据下的有界坐标经 `toH` 的像字面可比. 所以合法性必须约束**不同证据**下的分量.
> - **`copy-illegal`**: `W₂ X₂ X′` ($X_2=2$, $X'=\lim_n 1$, 两者在 `A` 里不可比) 不合法. **`copy→⊥`**: 若合法性逐分量 (`LocalLg`: 两个分量合法则世界合法), 就是 $ot$.
> - **前提彼此独立** (§4, 三个完整的 `KS`): `M1` 满足除 `lgι` 外的一切 ($\mathrm{Pr}=	op$); `M2` 满足除 `LocalLg` 外的一切 (合法性要求两个分量可比, 即跨证据相干; 这是相干出路的最小模型); `M3` (`S₀`) 满足除第二个证据的界外的一切.
>
> **律为什么是构造一路需要的.** (1) 两个证据的界 `bd₀`, `bd₁`: 接口的 `Bdᴮ` 定义上如此 ("有某个证据"); 更新律 `at` 读回的正是被升高的那一个分量的界. (2) `lgι`: `UniTrNeg.emb⊲` 沿 `hLim` 走进 $\Omega$-极限层时用 `ι`, `Lg-emb⊲` 要 `ι` 保合法; 比较式更新沿路径嵌入增量, 保合法律要它; 这里只用一个实例. (3) `cmpK`: `KS` 的字段, `HB T` 上的 `cmpB` 靠它. (4) `LocalLg`: 接口的 `LgWᴮ` 是逐分量的.
>
> **只否定什么.** 只否定这四组前提同时成立. **不否定**: 合法性带跨证据的相干 (`M2` 是它的模型, 入口的 `cmpKᶜ≤` 对一切 `SupB` 成立); 规范证据; 路径作种类; 更新律 (见 [AdmWNegLaws](AdmWNegLaws.lagda.md)).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AdmWNegCopy where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
```

## §1 `A` 里两个不可比的合法层, 搬成高度

`toH`: 层原样搬成任一种类结构上的高度 (没有 $\Omega$-节点). 保第一位置, 保合法.

```agda
module _ {T : KS} where
  toH : A → HB T
  toH azero = hz
  toH (asuc a) = hs (toH a)
  toH (alim f) = hl (λ n → toH (f n))

  toH-⊲ : ∀ {x y w} → x ⊲ y → toH x ⊲[ w ] toH y
  toH-⊲ C.self = hself
  toH-⊲ (C.suc p) = hsuc (toH-⊲ p)
  toH-⊲ (C.lim n p) = hlim n (toH-⊲ p)

  Lg-toH : ∀ x → Lg x → LgB (toH x)
  Lg-toH azero l = tt
  Lg-toH (asuc x) l = Lg-toH x l
  Lg-toH (alim f) (st , l) = (λ n → toH-⊲ (st n)) , (λ n → Lg-toH (f n) (l n))
```

`S₀` 里以 `toH` 为分支的 $\Omega$-节点合法: 单调就是 `toH-⊲`.

```agda
Lg-toHΩ : LgB {S₀} (hΩ tt toH)
Lg-toHΩ = (λ lw e e′ p → toH-⊲ p) , (λ c lc → Lg-toH c lc)
```

$X_2 = 2$, $X' = \lim_n 1$. 都合法. 它们的高度 $\mathrm{hs}(\mathrm{hs}\,0)$ 与 $\mathrm{hl}(\lambda\_.\,\mathrm{hs}\,0)$ 在任何种类结构的任何世界里都不互为第一位置 (只看构造子).

```agda
X₂ X′ : A
X₂ = asuc (asuc azero)
X′ = alim (λ _ → asuc azero)

lgX₂ : Lg X₂
lgX₂ = tt

lgX′ : Lg X′
lgX′ = (λ n → C.self) , (λ n → tt)

module _ {T : KS} {w : Wd T} where
  inc₁ : ¬ (_⊲[_]_ {T} (hs (hs hz)) w (hl (λ _ → hs hz)))
  inc₁ (hlim n (hsuc ()))

  inc₂ : ¬ (_⊲[_]_ {T} (hl (λ _ → hs hz)) w (hs (hs hz)))
  inc₂ (hsuc (hsuc ()))
```

## §2 一般引理: 合法分支的像在界之下可比

```agda
copy-core : (T : KS) (κ : K T) (g : E T κ → HB T) → LgB (hΩ κ g) →
  ∀ {V c₀ c₁} → LgW T V → Bd T κ c₀ V → Bd T κ c₁ V →
  (g c₁ ⊲[ V ] g c₀) ⊎ (g c₀ ⊲[ V ] g c₁)
copy-core T κ g (mo , _) lw e₀ e₁ with cmpK T e₀ e₁ lw
... | inj₁ r = inj₁ (mo lw e₁ e₀ r)
... | inj₂ r = inj₂ (mo lw e₀ e₁ r)
```


## §3 拷贝形状: 两个证据各带一个分量

`CopyShape T`: 种类结构 $T$ 里一个种类 `κ₀`, 坐标就是 `A` (`inE`, `outE`); 世界 `W₂ a₀ a₁` 里, 落在 $a_0$ 之下的坐标有界 (经第一个证据, `bd₀`), 落在 $a_1$ 之下的坐标也有界 (经第二个证据, `bd₁`); 两个分量都合法时世界合法 (`lgW₂`, 逐分量); 分支 `toH` 的 $\Omega$-节点合法 (`lgι`, 它是分量里的合法节点 `hΩ tt toH` 经 `ι` 的像).

```agda
record CopyShape (T : KS) : Set₁ where
  field
    κ₀   : K T
    inE  : A → E T κ₀
    outE : E T κ₀ → A
    oi   : ∀ x → outE (inE x) ≡ x
    W₂   : A → A → Wd T
    bd₀  : ∀ {x a₀ a₁} → x ⊲ a₀ → Bd T κ₀ (inE x) (W₂ a₀ a₁)
    bd₁  : ∀ {x a₀ a₁} → x ⊲ a₁ → Bd T κ₀ (inE x) (W₂ a₀ a₁)
    lgι  : LgB {T} (hΩ κ₀ (λ e → toH (outE e)))

LocalLg : (T : KS) → CopyShape T → Set
LocalLg T C = ∀ {a₀ a₁} → Lg a₀ → Lg a₁ → LgW T (CopyShape.W₂ C a₀ a₁)

module _ (T : KS) (C : CopyShape T) where
  open CopyShape C

  private
    tr₂ : ∀ {w x y} → toH {T} (outE (inE x)) ⊲[ w ] toH (outE (inE y)) → toH {T} x ⊲[ w ] toH y
    tr₂ {w} {x} {y} r with outE (inE x) | oi x | outE (inE y) | oi y
    ... | _ | refl | _ | refl = r
```

**`need-cmp`**: 任一合法的 `W₂ a₀ a₁` 里, 第一个证据下的坐标与第二个证据下的坐标, 经 `toH` 的像字面可比. 所以合法性必须约束**不同证据**下的分量.

```agda
  need-cmp : ∀ {a₀ a₁} → LgW T (W₂ a₀ a₁) → ∀ {x x′} → x ⊲ a₀ → x′ ⊲ a₁ →
    (toH {T} x′ ⊲[ W₂ a₀ a₁ ] toH x) ⊎ (toH {T} x ⊲[ W₂ a₀ a₁ ] toH x′)
  need-cmp lw q q′ with copy-core T κ₀ (λ e → toH (outE e)) lgι lw (bd₀ q) (bd₁ q′)
  ... | inj₁ r = inj₁ (tr₂ r)
  ... | inj₂ r = inj₂ (tr₂ r)

  copy-illegal : ¬ LgW T (W₂ X₂ X′)
  copy-illegal lw with need-cmp lw C.self C.self
  ... | inj₁ r = inc₂ {T} r
  ... | inj₂ r = inc₁ {T} r

copy→⊥ : (T : KS) (C : CopyShape T) → LocalLg T C → ⊥
copy→⊥ T C loc = copy-illegal T C (loc lgX₂ lgX′)
```

## §4 前提彼此独立: 去掉任一条都有模型

三个小种类结构, 都只有一个种类, 坐标 `A`. 它们说明 `copy→⊥` 的四组前提 (两个证据的界, `ι` 保合法, 逐分量合法, `cmpK`) 不是空真: 去掉 `lgι`, 去掉 `LocalLg`, 去掉第二个证据, 各有一个完整的 `KS` 实例.

**M1: 两个分量, 第一位置平凡.** 世界 $(a_0,a_1)$, 界 "在任一分量之下", $\mathrm{Pr}=\top$. `cmpK` 平凡; 两个证据的界与逐分量合法都成立 (`M1-shape⁻`, `M1-local`); 由 `copy→⊥`, `lgι` 必不成立 (`M1-¬lgι`).

```agda
module M1 where
  ≤₂ : A × A → A × A → Set
  ≤₂ (a₀ , a₁) (b₀ , b₁) = (a₀ ⊲ b₀) × (a₁ ⊲ b₁)

  Bd₂ : A → A × A → Set
  Bd₂ x (a₀ , a₁) = (x ⊲ a₀) ⊎ (x ⊲ a₁)

  Bd₂↑ : ∀ {x w w′} → ≤₂ w w′ → Bd₂ x w → Bd₂ x w′
  Bd₂↑ (q₀ , q₁) (inj₁ e) = inj₁ (C.⊲-tr e q₀)
  Bd₂↑ (q₀ , q₁) (inj₂ e) = inj₂ (C.⊲-tr e q₁)

  LgW₂ : A × A → Set
  LgW₂ (a₀ , a₁) = Lg a₀ × Lg a₁

  lgBd₂ : ∀ {x w} → Bd₂ x w → LgW₂ w → Lg x
  lgBd₂ (inj₁ e) (l₀ , l₁) = C.lg⊲ e l₀
  lgBd₂ (inj₂ e) (l₀ , l₁) = C.lg⊲ e l₁

  T₁ : KS
  T₁ = record
    { K = ⊤ ; E = λ _ → A ; Wd = A × A ; LgW = LgW₂ ; _≤w_ = ≤₂
    ; ≤w-rf = C.self , C.self ; ≤w-tr = λ (p₀ , p₁) (q₀ , q₁) → C.⊲-tr p₀ q₀ , C.⊲-tr p₁ q₁
    ; Bd = λ _ → Bd₂ ; Pr = λ _ _ _ _ → ⊤ ; Bd↑ = Bd₂↑ ; cmpK = λ _ _ _ → inj₁ tt
    ; LgE = λ _ → Lg ; lgBd = lgBd₂ ; bot = λ _ → azero ; botBd = λ _ w → inj₁ (C.z⊲ (proj₁ w)) }

  -- 除 lgι 外的字段
  M1-W₂ : A → A → A × A
  M1-W₂ a₀ a₁ = a₀ , a₁

  M1-local : ∀ {a₀ a₁} → Lg a₀ → Lg a₁ → LgW T₁ (M1-W₂ a₀ a₁)
  M1-local l₀ l₁ = l₀ , l₁

  M1-¬lgι : ¬ LgB {T₁} (hΩ tt (λ e → toH e))
  M1-¬lgι l = copy→⊥ T₁ (record { κ₀ = tt ; inE = λ x → x ; outE = λ x → x ; oi = λ x → refl
                                 ; W₂ = M1-W₂ ; bd₀ = inj₁ ; bd₁ = inj₂ ; lgι = l }) M1-local
```

**M2: 两个分量, 合法性要求两个分量可比 (相干).** 第一位置是 `A` 的 $\lhd$. `cmpK`: 两个界都搬到较大的分量里, 用 `cmpF`. `toH` 节点合法 (`lgι` 成立). `copy-illegal` 说 $(X_2, X')$ 不是合法世界; 这里的合法性确实排除了它 (两个分量不可比). 这是**跨证据相干**这一出路的最小模型: `need-cmp` 要的就是它.

```agda
module M2 where
  open M1 using (≤₂; Bd₂; Bd₂↑)

  Coh : A → A → Set
  Coh a₀ a₁ = (a₀ ⊲ a₁) ⊎ (a₁ ⊲ a₀)

  LgWc : A × A → Set
  LgWc (a₀ , a₁) = Lg a₀ × Lg a₁ × Coh a₀ a₁

  -- 界搬到较大的分量: 给出一个合法的公共上界
  top : ∀ {x} (w : A × A) → Bd₂ x w → LgWc w → Σ A (λ t → (x ⊲ t) × Lg t × (proj₁ w ⊲ t) × (proj₂ w ⊲ t))
  top (a₀ , a₁) (inj₁ e) (l₀ , l₁ , inj₁ q) = a₁ , C.⊲-tr e q , l₁ , q , C.self
  top (a₀ , a₁) (inj₁ e) (l₀ , l₁ , inj₂ q) = a₀ , e , l₀ , C.self , q
  top (a₀ , a₁) (inj₂ e) (l₀ , l₁ , inj₁ q) = a₁ , e , l₁ , q , C.self
  top (a₀ , a₁) (inj₂ e) (l₀ , l₁ , inj₂ q) = a₀ , C.⊲-tr e q , l₀ , C.self , q

  cmp₂ : ∀ {x x′ w} → Bd₂ x w → Bd₂ x′ w → LgWc w → (x′ ⊲ x) ⊎ (x ⊲ x′)
  cmp₂ {w = w} e e′ lw with top w e lw
  ... | t , xt , lt , q₀ , q₁ with e′
  ...   | inj₁ e₀ = C.cmpF xt (C.⊲-tr e₀ q₀) lt
  ...   | inj₂ e₁ = C.cmpF xt (C.⊲-tr e₁ q₁) lt

  lgBdc : ∀ {x w} → Bd₂ x w → LgWc w → Lg x
  lgBdc (inj₁ e) (l₀ , l₁ , _) = C.lg⊲ e l₀
  lgBdc (inj₂ e) (l₀ , l₁ , _) = C.lg⊲ e l₁

  T₂ : KS
  T₂ = record
    { K = ⊤ ; E = λ _ → A ; Wd = A × A ; LgW = LgWc ; _≤w_ = ≤₂
    ; ≤w-rf = C.self , C.self ; ≤w-tr = λ (p₀ , p₁) (q₀ , q₁) → C.⊲-tr p₀ q₀ , C.⊲-tr p₁ q₁
    ; Bd = λ _ → Bd₂ ; Pr = λ _ _ x x′ → x ⊲ x′ ; Bd↑ = Bd₂↑ ; cmpK = cmp₂
    ; LgE = λ _ → Lg ; lgBd = lgBdc ; bot = λ _ → azero ; botBd = λ _ w → inj₁ (C.z⊲ (proj₁ w)) }

  M2-shape : CopyShape T₂
  M2-shape = record { κ₀ = tt ; inE = λ x → x ; outE = λ x → x ; oi = λ x → refl
                    ; W₂ = λ a₀ a₁ → a₀ , a₁ ; bd₀ = inj₁ ; bd₁ = inj₂
                    ; lgι = (λ lw e e′ p → toH-⊲ p) , (λ c lc → Lg-toH c lc) }

  -- 相干的合法世界确实存在 (前提可满足)
  M2-legal : LgW T₂ (X₂ , X₂)
  M2-legal = tt , tt , inj₁ C.self
```

**M3: 只有一个分量.** 就是 `S₀`; `W₂ a₀ a₁ = a₀`. 除第二个证据的界 (`bd₁`) 外一切成立.

```agda
module M3 where
  M3-bd₀ : ∀ {x a₀ a₁ : A} → x ⊲ a₀ → Bd S₀ tt x a₀
  M3-bd₀ q = q

  M3-lgι : LgB {S₀} (hΩ tt (λ e → toH e))
  M3-lgι = Lg-toHΩ

  M3-local : ∀ {a₀ : A} → Lg a₀ → LgW S₀ a₀
  M3-local l = l
```
