# 可入下标比较式更新的否定 (三): 对诊断 §3.3 原文的 `supB`

> 不含记号. 入口 [AdmWNeg](AdmWNeg.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 这一篇对着诊断 §3.3 的**原文**写, 在构造一路的接口文件定稿之前起草; 与定稿接口的对照在入口里. 原文: 并 `supB` 的世界 $\Sigma\,(w:\mathrm{Wd}\,S)\,((c:E\,S\,\kappa)\to \mathrm{Bd}\,S\,\kappa\,c\,w\to\mathrm{Wd}(F\,c))$, 种类 $\Sigma_c K(F\,c)$, 界 "某个证据的分量里有界", 合法 "外层合法且每个分量合法".
>
> - **`no-botBd`**: 原文的界之下, `KS` 的字段 `botBd` ("每个种类有一个坐标在一切世界的界之下") 不可满足: 坐标 $c=1$ 在外层界 $b=0$ 之下没有证据, 种类 $(1,k)$ 在这样的世界里没有任何有界坐标. 所以原文的 `supB` **不是** `HtTowerTy.KS` 的实例; 构造一路必须改 `KS` (去掉 `botBd` 或改界). 这条是接口义务, 不是路线的否定.
> - **`AsSupB`**: 不论怎样改, 只要得到的种类结构 $T$ 含着原文的形状 (原文的世界映进 $T$ 的世界 `mkW`, 坐标 $0$ 的分量的界经每一个证据都是 $T$ 的界 `bdIn`, `ι` 的像 `hΩ (0, tt) toH` 合法 `lgι`), 并且原文意义的合法世界在 $T$ 里合法 (`LocalB`), 就推出 $\bot$ (**`supB→⊥`**), 经 [AdmWNegCopy](AdmWNegCopy.lagda.md) 的 `copy→⊥`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AdmWNegDraft where

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
open import OCF.Align.HtTowerNStage using (dWLev)
open import OCF.Align.AdmWNegCopy using (toH; X₂; X′; lgX₂; lgX′; CopyShape; LocalLg; copy→⊥)
```

## §1 原文的形状

```agda
module SupB (S : KS) (κ : K S) (F : E S κ → KS) where
  Kᵇ : Set
  Kᵇ = Σ (E S κ) (λ c → K (F c))

  Eᵇ : Kᵇ → Set
  Eᵇ k = E (F (proj₁ k)) (proj₂ k)

  Wᵇ : Set
  Wᵇ = Σ (Wd S) (λ w → (c : E S κ) → Bd S κ c w → Wd (F c))

  Bdᵇ : (k : Kᵇ) → Eᵇ k → Wᵇ → Set
  Bdᵇ (c , k) x (w , v) = Σ (Bd S κ c w) (λ p → Bd (F c) k x (v c p))

  LgWᵇ : Wᵇ → Set
  LgWᵇ (w , v) = LgW S w × (∀ c p → LgW (F c) (v c p))
```

最小实例: 外层 `step S₀`, 种类 `inj₂ tt` (坐标 `HB S₀`, 界 $c\lhd_{[a]} b$), 分量 `Lev (up c)`.

```agda
FΩ₀ : HB S₀ → KS
FΩ₀ c = Lev (up c)

open SupB (step S₀) (inj₂ tt) FΩ₀
```

## §2 `botBd` 不可满足

世界 `w0`: 外层 $(0, 0)$. 坐标 $1$ 不是 $0$ 的第一位置, 所以种类 $(1, k)$ 的界是空的.

```agda
w0 : Wᵇ
w0 = (azero , hz) , (λ c p → dWLev (up c))

not-adm : ¬ (_⊲[_]_ {S₀} (hs hz) azero hz)
not-adm ()

no-botBd : (bot : (k : Kᵇ) → Eᵇ k) → ¬ (∀ k w → Bdᵇ k (bot k) w)
no-botBd bot h with h (hs hz , inj₁ tt) w0
... | (p , _) = not-adm p
```

## §3 含着原文形状的任一种类结构

`ev₀`, `ev₁`: 坐标 $0$ 在 $b_0=\lim_n 0$ 之下的两个证据. `W₂raw a₀ a₁`: 原文的世界, 分量按证据的 ℕ-下标取 ($0$ 与 `hself` 取 $a_0$, 其余取 $a_1$); 坐标 $0$ 的分量就是 `A` 的世界.

```agda
b₀ : HB S₀
b₀ = hl (λ _ → hz)

lgb₀ : LgB b₀
lgb₀ = (λ n → hself) , (λ n → tt)

ev₀ ev₁ : hz ⊲[ azero ] b₀
ev₀ = hlim 0 hself
ev₁ = hlim 1 hself

wK : A → ∀ {S} (x : HB S) → Wd (Lev x)
wK a hz = a
wK a (hs x) = wK a x , hz
wK a (hl f) = λ n → wK a (f n)
wK a (hΩ κ g) = λ c → wK a (g c)

lgwK : ∀ {a} → Lg a → ∀ {S} (x : HB S) → LgW (Lev x) (wK a x)
lgwK l hz = l
lgwK l (hs x) = lgwK l x , tt
lgwK l (hl f) = λ n → lgwK l (f n)
lgwK l (hΩ κ g) = λ c → lgwK l (g c)

v₂ : A → A → (c : HB S₀) → c ⊲[ azero ] b₀ → Wd (Lev (up c))
v₂ a₀ a₁ c hself = wK a₀ (up c)
v₂ a₀ a₁ c (hlim zero p) = wK a₀ (up c)
v₂ a₀ a₁ c (hlim (suc n) p) = wK a₁ (up c)

W₂raw : A → A → Wᵇ
W₂raw a₀ a₁ = (azero , b₀) , v₂ a₀ a₁

W₂-local : ∀ {a₀ a₁} → Lg a₀ → Lg a₁ → LgWᵇ (W₂raw a₀ a₁)
W₂-local l₀ l₁ = (tt , lgb₀) , comp
  where
  comp : ∀ c p → LgW (Lev (up c)) (v₂ _ _ c p)
  comp c hself = lgwK l₀ (up c)
  comp c (hlim zero p) = lgwK l₀ (up c)
  comp c (hlim (suc n) p) = lgwK l₁ (up c)

-- 两个证据下的界, 原文意义 (定义)
bd₀raw : ∀ {x a₀ a₁} → x ⊲ a₀ → Bdᵇ (hz , tt) x (W₂raw a₀ a₁)
bd₀raw q = ev₀ , q

bd₁raw : ∀ {x a₀ a₁} → x ⊲ a₁ → Bdᵇ (hz , tt) x (W₂raw a₀ a₁)
bd₁raw q = ev₁ , q
```

`AsSupB T`: 种类结构 $T$ 含着原文的形状. 字段的来历:

- `kd`, `inE`, `outE`, `oi`: 种类 $(0, \mathrm{tt})$ 与它的坐标 (`A`). 原文里 $E\,(0,\mathrm{tt}) = A$ 定义相等, 取恒等.
- `mkW`: 原文的世界是 $T$ 的世界 (原文就是 $T$ 时取恒等).
- `bdIn`: 经**任一**证据 $p$ 在分量 $(0,p)$ 里有界, 就在 $T$ 里有界. 原文的 `Bdᵇ` 定义上如此; 构造一路的 `at` 律 (在 $(c_0,p_0)$ 处恰好接长, 然后读回这个界) 需要它.
- `lgι`: 分量 `S₀` 的合法节点 `hΩ tt toH` (`AdmWNegCopy.Lg-toHΩ`) 经 `ι` 的像在 $T$ 里合法. `UniTrNeg.Lg-emb⊲` 走 `hLim` 时要 `ι` 保合法; 比较式更新的保合法律要它.

```agda
record AsSupB (T : KS) : Set₁ where
  field
    kd   : K T
    inE  : A → E T kd
    outE : E T kd → A
    oi   : ∀ x → outE (inE x) ≡ x
    mkW  : Wᵇ → Wd T
    bdIn : ∀ {x} {w : Wd (step S₀)} {v} (p : hz ⊲[ proj₁ w ] proj₂ w) → x ⊲ v hz p → Bd T kd (inE x) (mkW (w , v))
    lgι  : LgB {T} (hΩ kd (λ e → toH (outE e)))
open AsSupB

LocalB : (T : KS) → AsSupB T → Set
LocalB T As = ∀ w → LgWᵇ w → LgW T (mkW As w)

asShape : ∀ {T} → AsSupB T → CopyShape T
asShape As = record
  { κ₀ = kd As ; inE = inE As ; outE = outE As ; oi = oi As
  ; W₂ = λ a₀ a₁ → mkW As (W₂raw a₀ a₁)
  ; bd₀ = λ q → bdIn As ev₀ q ; bd₁ = λ q → bdIn As ev₁ q
  ; lgι = lgι As }

supB→⊥ : (T : KS) (As : AsSupB T) → LocalB T As → ⊥
supB→⊥ T As loc = copy→⊥ T (asShape As) (λ l₀ l₁ → loc _ (W₂-local l₀ l₁))
```

**读法.** 原文的 `supB` (若能补成种类结构) 满足 `bdIn` (定义) 与 `LocalB` (原文的合法就是 `LgWᵇ`), 所以只要 `cmpK` 与 `ι` 保合法同时成立, 就是 $\bot$. 不是禁忌, 是不存在.
