# 树的语言, 否定一路 (二): 级集合定死了, 定义没有定死 — 压扁一切 Ω-极限的候选

> 不含记号. 入口 [NegTreeLang](NegTreeLang.lagda.md). 对着接口 [TreeLangIf](TreeLangIf.lagda.md) ("接口定稿 2026-11-05 20:27 (首次编译通过)", 变更记录: 无) 写, 导入它, 不另造接口; 只读导入构造一路的 [TreeLangLv](TreeLangLv.lagda.md) (20:27 之后的编译版) 以便对它的形状定理逐条检查. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> **构造一路的形状定理.** `TreeLangLv.exact→`, `exact←`: 满足 `LvCrit` 与 `LvUpper` 的候选, 每一层的**级集合**与 `Lev` 的相等; `exactL→`, `exactL←`: `LH` 上同理对 `Lv`. 本篇检查: 前提可满足吗? 结论 "唯一" 唯一的是什么?
>
> **结果.**
>
> 1. **`Fl`, `RFl` (构造), `CFl`, `UFl` (定理).** 一个与 `Lev` 种类逐个对应的候选 `Fl`: 递归形状与 `Lev` 相同 (`hz` 给一个坐标为 `A` 的种类, `hs` 加一个坐标为 `HB (Fl x)` 的新种类, 极限取并), 只是每一层的种类结构是**平的** (`flat`): 世界是 `⊤`, 界与第一位置恒真. 它满足 `LvCrit` 与 `LvUpper`, 所以由构造一路自己的定理 (`exact→`, `exact←`), 它的级集合与 `Lev` 的**相等** (`same-levels→`, `same-levels←`). 种类也逐个对应且保级 (`km`, `km-lv`, `km⁻`, `km⁻km`).
> 2. **`fl-const` (定理, 对一切层号).** `Fl c` 里**每一个合法的 Ω-结点的分支都是常函数**: 合法要求 $g\,e\lhd g\,e'$ 对一切 $e,e'$ (第一位置恒真), 两个方向都有, 而第一位置是反对称的 (`antisym`, 由高度的良基). 所以 `Fl` 的 Ω-极限在值上退化: 合法的 $\mathrm{h\Omega}\,\kappa\,g$ 只是一个分支 $g\,e$ 的一次包装.
> 3. **`contrast` (定理).** 同一层号 `hs hz`, 同一种类 (新种类, 坐标是第 0 层的值): `Lev` 里有合法的非常值分支 ($c\mapsto$ `up c`, 把 $0$ 与 $1$ 送到不同的值); `Fl` 里一切合法分支在 $0$ 与 $1$ 处取同一个值.
> 4. **`LH` 上同样 (`FlL`, `RFlL`, `CFlL`, `UFlL`, `same-levelsL→`, `same-levelsL←`, `flL-const`, `contrastL`).** `cof` 也被平的候选满足: `lΩ k g` 处的级 $k$ 种类的坐标是 `HB (FlL k)`, 与层号自己的分支域 `HB (Lv k)` 没有被判据联系起来; 层号 `ls lz` 处 `Lv` 有非常值的合法分支, `FlL` 没有.
>
> **只否定什么.** 只否定推断 "判据 (`LvCrit` + `LvUpper`, 或 `LvCritL` + `LvUpperL`) 把层的定义定死了". 构造一路的定理 `exact→`, `exactL→` 等**都对** (本篇用它们得到 `same-levels`); 它们定死的是级集合 (`LvRule` 的 `K`, `lv`, 坐标类型), 不是种类结构 (世界, 界, 第一位置, 比较). 这一点 `TreeLangLv` 文件头第 5 条已用一句话说了 ("判据也不管世界, 界, 第一位置"); 本篇把它写成定理, 并说出后果: 判据被一个**每个 Ω-极限都退化**的候选满足, 所以判据不保证层里有真的不可数分支. **不否定**: `Lev`, `Lv` 本身; 判据路线; 给判据加上界与第一位置的条件 (例如要求 `Pr` 就是坐标高度的 `⊲`) 之后的唯一性 (未写, 未否定).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegTreeLangFlat where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]; [_,_]′)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerNeg using (_≺ᴮ_; ≺s; ≺l; ≺Ω; acc≺)
open import OCF.Align.NegKindLvLev using (_⊏_; one; snoc; lvK)
open import OCF.Align.NegStratTwBlind using (_⊑_; rf⊑; sn⊑; ⊲→⊑; noLoop)
open import OCF.Align.LFReTy using (LH; lz; ls; ll; lΩ; Lv; S⊥; lvl)
open import OCF.Align.TreeLangIf
open import OCF.Align.TreeLangLv using (LevR; LevC; LevU; exact→; exact←; LvRL; LvCL; LvUL; exactL→; exactL←)
```

## §1 平的种类结构

`flat K′ E′ b`: 种类与坐标给定, 世界只有一个, 界与第一位置恒真, 合法恒真. 这是一个合法的 `KS` (一切字段都有).

```agda
flat : (K′ : Set) (E′ : K′ → Set) → (∀ κ → E′ κ) → KS
flat K′ E′ b = record
  { K = K′ ; E = E′ ; Wd = ⊤ ; LgW = λ _ → ⊤ ; _≤w_ = λ _ _ → ⊤ ; ≤w-rf = tt ; ≤w-tr = λ _ _ → tt
  ; Bd = λ _ _ _ → ⊤ ; Pr = λ _ _ _ _ → ⊤ ; Bd↑ = λ _ _ → tt ; cmpK = λ _ _ _ → inj₁ tt
  ; LgE = λ _ _ → ⊤ ; lgBd = λ _ _ → tt ; bot = b ; botBd = λ _ _ → tt }

stepF : KS → KS
stepF T = flat (K T ⊎ ⊤) [ E T , (λ _ → HB T) ]′ [ bot T , (λ _ → hz) ]

supF : (I : Set) → (I → KS) → KS
supF I F = flat (Σ I (λ i → K (F i))) (λ p → E (F (proj₁ p)) (proj₂ p)) (λ p → bot (F (proj₁ p)) (proj₂ p))
```

**反对称.** 第一位置推出结构子项的自反传递闭包 (`⊲→⊑`); 两个方向都有时相等 (否则得到一个回到自己的严格子项链, `noLoop`).

```agda
module _ {S : KS} where
  ⊑-tr : ∀ {a b c : HB S} → a ⊑ b → b ⊑ c → a ⊑ c
  ⊑-tr p rf⊑ = p
  ⊑-tr p (sn⊑ q r) = sn⊑ (⊑-tr p q) r

  ⊑-cases : ∀ {a b : HB S} → a ⊑ b → (a ≡ b) ⊎ Σ (HB S) (λ m → (a ⊑ m) × (m ≺ᴮ b))
  ⊑-cases rf⊑ = inj₁ refl
  ⊑-cases (sn⊑ r s) = inj₂ (_ , r , s)

  antisym : ∀ {a b : HB S} {w w′} → a ⊲[ w ] b → b ⊲[ w′ ] a → a ≡ b
  antisym p q with ⊑-cases (⊲→⊑ p)
  ... | inj₁ e = e
  ... | inj₂ (m , r , s) = ⊥-elim (noLoop (acc≺ m) s (⊑-tr (⊲→⊑ q) r))

-- 平的结构上合法的 Ω-结点: 分支是常函数
flat-const : ∀ {K′ E′ b} κ (g : E′ κ → HB (flat K′ E′ b)) → LgB {flat K′ E′ b} (hΩ κ g) → ∀ e e′ → g e ≡ g e′
flat-const κ g (mo , _) e e′ = antisym (mo {tt} tt tt tt tt) (mo {tt} tt tt tt tt)
```

## §2 `Fl`: 递归形状与 `Lev` 相同, 每层是平的

```agda
Fl : ∀ {S : KS} → HB S → KS
Fl hz = flat ⊤ (λ _ → A) (λ _ → azero)
Fl (hs x) = stepF (Fl x)
Fl (hl f) = supF ℕ (λ n → Fl (f n))
Fl {S} (hΩ κ g) = supF (E S κ) (λ c → Fl (g c))

lvF : ∀ {S : KS} (c : HB S) → K (Fl c) → ⊤ ⊎ HB S
lvF hz κ = inj₁ tt
lvF (hs x) (inj₁ κ) = lvF x κ
lvF (hs x) (inj₂ _) = inj₂ x
lvF (hl f) (n , κ) = lvF (f n) κ
lvF (hΩ κ g) (e , κ′) = lvF (g e) κ′

coordF : ∀ {S : KS} (c : HB S) κ → E (Fl c) κ ≡ Cdᴿ A Fl (lvF c κ)
coordF hz κ = refl
coordF (hs x) (inj₁ κ) = coordF x κ
coordF (hs x) (inj₂ _) = refl
coordF (hl f) (n , κ) = coordF (f n) κ
coordF (hΩ κ g) (e , κ′) = coordF (g e) κ′

RFl : ∀ {S : KS} → LvRule S A
RFl = record { L = Fl ; lv = lvF ; coord = coordF }
```

**判据与字面上界.**

```agda
subUpF : ∀ {S : KS} {y c : HB S} → y ≺ᴮ c → ∀ ℓ → SubLv y ℓ → SubLv c ℓ
subUpF q (inj₁ _) _ = tt
subUpF q (inj₂ z) p = snoc p q

upUpF : ∀ {S : KS} {y c : HB S} → y ≺ᴮ c → ∀ ℓ → UpLv y ℓ → UpLv c ℓ
upUpF q (inj₁ _) _ = tt
upUpF q (inj₂ z) p = sn p q

subF : ∀ {S : KS} (c : HB S) κ → SubLv c (lvF c κ)
subF hz κ = tt
subF (hs x) (inj₁ κ) = subUpF ≺s (lvF x κ) (subF x κ)
subF (hs x) (inj₂ _) = one ≺s
subF (hl f) (n , κ) = subUpF (≺l n) (lvF (f n) κ) (subF (f n) κ)
subF (hΩ κ g) (e , κ′) = subUpF (≺Ω e) (lvF (g e) κ′) (subF (g e) κ′)

inhF : ∀ {S : KS} {y c : HB S} → y ≺ᴮ c → ∀ ℓ → InLv RFl y ℓ → InLv RFl c ℓ
inhF ≺s ℓ (κ , e) = inj₁ κ , e
inhF (≺l n) ℓ (κ , e) = (n , κ) , e
inhF (≺Ω c) ℓ (κ , e) = (c , κ) , e

CFl : ∀ {S : KS} → LvCrit (RFl {S})
CFl = record { base0 = tt , refl ; feed = λ x → inj₂ tt , refl ; inherit = inhF ; sub = subF }

UFl : ∀ {S : KS} → LvUpper (RFl {S})
UFl hz κ = tt
UFl (hs x) (inj₁ κ) = upUpF ≺s (lvF x κ) (UFl x κ)
UFl (hs x) (inj₂ _) = rf
UFl (hl f) (n , κ) = upUpF (≺l n) (lvF (f n) κ) (UFl (f n) κ)
UFl (hΩ κ g) (e , κ′) = upUpF (≺Ω e) (lvF (g e) κ′) (UFl (g e) κ′)
```

**由构造一路的定理: 级集合与 `Lev` 相等.** 种类也逐个对应 (`km`, `km⁻` 互逆, 保级).

```agda
same-levels→ : ∀ {S : KS} (c : HB S) ℓ → InLv RFl c ℓ → InLv (LevR {S}) c ℓ
same-levels→ = exact→ RFl CFl UFl

same-levels← : ∀ {S : KS} (c : HB S) ℓ → InLv (LevR {S}) c ℓ → InLv RFl c ℓ
same-levels← = exact← RFl CFl UFl

km : ∀ {S : KS} (c : HB S) → K (Lev c) → K (Fl c)
km hz κ = κ
km (hs x) (inj₁ κ) = inj₁ (km x κ)
km (hs x) (inj₂ t) = inj₂ t
km (hl f) (n , κ) = n , km (f n) κ
km (hΩ κ g) (e , κ′) = e , km (g e) κ′

km⁻ : ∀ {S : KS} (c : HB S) → K (Fl c) → K (Lev c)
km⁻ hz κ = κ
km⁻ (hs x) (inj₁ κ) = inj₁ (km⁻ x κ)
km⁻ (hs x) (inj₂ t) = inj₂ t
km⁻ (hl f) (n , κ) = n , km⁻ (f n) κ
km⁻ (hΩ κ g) (e , κ′) = e , km⁻ (g e) κ′

km⁻km : ∀ {S : KS} (c : HB S) κ → km⁻ c (km c κ) ≡ κ
km⁻km hz κ = refl
km⁻km (hs x) (inj₁ κ) = cong inj₁ (km⁻km x κ)
km⁻km (hs x) (inj₂ t) = refl
km⁻km (hl f) (n , κ) = cong (n ,_) (km⁻km (f n) κ)
km⁻km (hΩ κ g) (e , κ′) = cong (e ,_) (km⁻km (g e) κ′)

kmkm⁻ : ∀ {S : KS} (c : HB S) κ → km c (km⁻ c κ) ≡ κ
kmkm⁻ hz κ = refl
kmkm⁻ (hs x) (inj₁ κ) = cong inj₁ (kmkm⁻ x κ)
kmkm⁻ (hs x) (inj₂ t) = refl
kmkm⁻ (hl f) (n , κ) = cong (n ,_) (kmkm⁻ (f n) κ)
kmkm⁻ (hΩ κ g) (e , κ′) = cong (e ,_) (kmkm⁻ (g e) κ′)

km-lv : ∀ {S : KS} (c : HB S) κ → lvF c (km c κ) ≡ lvK c κ
km-lv hz κ = refl
km-lv (hs x) (inj₁ κ) = km-lv x κ
km-lv (hs x) (inj₂ t) = refl
km-lv (hl f) (n , κ) = km-lv (f n) κ
km-lv (hΩ κ g) (e , κ′) = km-lv (g e) κ′
```

## §3 `Fl` 的 Ω-极限退化; 对照 `Lev`

`Fl c` 在每个构造子处都化成某个 `flat`, 所以 `flat-const` 对一切层号适用 (按 $c$ 的构造子分情形, 每一支同一行).

```agda
fl-const : ∀ {S : KS} (c : HB S) κ (g : E (Fl c) κ → HB (Fl c)) → LgB {Fl c} (hΩ κ g) → ∀ e e′ → g e ≡ g e′
fl-const hz κ g l = flat-const κ g l
fl-const (hs x) κ g l = flat-const κ g l
fl-const (hl f) κ g l = flat-const κ g l
fl-const (hΩ κ′ h) κ g l = flat-const κ g l
```

**对照.** 层号 `hs hz` (第 1 层), 新种类 `inj₂ tt` (坐标是第 0 层的值). `Lev (hs hz) = step S₀` 里分支 `up` 合法且把 $0$, $1$ 送到不同的值; `Fl (hs hz)` 里一切合法分支在 $0$, $1$ 处相同.

```agda
Lg-upΩ : LgB {Lev {S₀} (hs hz)} (hΩ (inj₂ tt) (λ c → up c))
Lg-upΩ = (λ lw e e′ q → up-⊲ q) , (λ c lc → Lg-up c lc)

contrast :
  Σ (HB S₀ → HB (Lev {S₀} (hs hz))) (λ g → LgB {Lev {S₀} (hs hz)} (hΩ (inj₂ tt) g) × ¬ (g hz ≡ g (hs hz))) ×
  (∀ (g : HB (Fl {S₀} hz) → HB (Fl {S₀} (hs hz))) → LgB {Fl {S₀} (hs hz)} (hΩ (inj₂ tt) g) → g hz ≡ g (hs hz))
contrast = ((λ c → up c) , Lg-upΩ , (λ ())) , (λ g l → fl-const {S₀} (hs hz) (inj₂ tt) g l hz (hs hz))
```

## §4 `LH` 上: 平的候选也满足 `cof`

```agda
FlL : LH → KS
FlL lz = flat ⊥ (λ ()) (λ ())
FlL (ls x) = stepF (FlL x)
FlL (ll f) = supF ℕ (λ n → FlL (f n))
FlL (lΩ k g) = supF (⊤ ⊎ HB (Lv k)) [ (λ _ → stepF (FlL k)) , (λ c → FlL (g c)) ]′

lvFL : ∀ x → K (FlL x) → LH
lvFL lz ()
lvFL (ls x) (inj₁ κ) = lvFL x κ
lvFL (ls x) (inj₂ _) = x
lvFL (ll f) (n , κ) = lvFL (f n) κ
lvFL (lΩ k g) (inj₁ _ , inj₁ κ) = lvFL k κ
lvFL (lΩ k g) (inj₁ _ , inj₂ _) = k
lvFL (lΩ k g) (inj₂ c , κ) = lvFL (g c) κ

coordFL : ∀ x κ → E (FlL x) κ ≡ HB (FlL (lvFL x κ))
coordFL lz ()
coordFL (ls x) (inj₁ κ) = coordFL x κ
coordFL (ls x) (inj₂ _) = refl
coordFL (ll f) (n , κ) = coordFL (f n) κ
coordFL (lΩ k g) (inj₁ _ , inj₁ κ) = coordFL k κ
coordFL (lΩ k g) (inj₁ _ , inj₂ _) = refl
coordFL (lΩ k g) (inj₂ c , κ) = coordFL (g c) κ

RFlL : LvRuleL
RFlL = record { Lᴸ = FlL ; lvᴸ = lvFL ; coordᴸ = coordFL }

inhFL : ∀ {y x} → y ≺ᴸ x → ∀ ℓ → InLvL RFlL y ℓ → InLvL RFlL x ℓ
inhFL ≺ls ℓ (κ , e) = inj₁ κ , e
inhFL (≺ll n) ℓ (κ , e) = (n , κ) , e
inhFL (≺lΩ c) ℓ (κ , e) = (inj₂ c , κ) , e
inhFL ≺lk ℓ (κ , e) = (inj₁ tt , inj₁ κ) , e

CFlL : LvCritL RFlL
CFlL = record { feedᴸ = λ x → inj₂ tt , refl ; inheritᴸ = inhFL ; cofᴸ = λ k g → (inj₁ tt , inj₂ tt) , refl }

UFlL : LvUpperL RFlL
UFlL lz ()
UFlL (ls x) (inj₁ κ) = pup (UFlL x κ) ≺ls
UFlL (ls x) (inj₂ _) = pls
UFlL (ll f) (n , κ) = pup (UFlL (f n) κ) (≺ll n)
UFlL (lΩ k g) (inj₁ _ , inj₁ κ) = pup (UFlL k κ) ≺lk
UFlL (lΩ k g) (inj₁ _ , inj₂ _) = plΩ g
UFlL (lΩ k g) (inj₂ c , κ) = pup (UFlL (g c) κ) (≺lΩ c)

same-levelsL→ : ∀ x y → InLvL RFlL x y → InLvL LvRL x y
same-levelsL→ = exactL→ RFlL CFlL UFlL

same-levelsL← : ∀ x y → InLvL LvRL x y → InLvL RFlL x y
same-levelsL← = exactL← RFlL CFlL

flL-const : ∀ x κ (g : E (FlL x) κ → HB (FlL x)) → LgB {FlL x} (hΩ κ g) → ∀ e e′ → g e ≡ g e′
flL-const lz () g l
flL-const (ls x) κ g l = flat-const κ g l
flL-const (ll f) κ g l = flat-const κ g l
flL-const (lΩ k h) κ g l = flat-const κ g l
```

**对照 (层号 `ls lz`).** `Lv (ls lz) = step S⊥`, 新种类的坐标是 `HB S⊥` (第 0 层的值); 分支 `up` 合法且非常值. `FlL (ls lz)` 里一切合法分支常值.

```agda
Lg-upΩL : LgB {Lv (ls lz)} (hΩ (inj₂ tt) (λ c → up c))
Lg-upΩL = (λ lw e e′ q → up-⊲ q) , (λ c lc → Lg-up c lc)

contrastL :
  Σ (HB S⊥ → HB (Lv (ls lz))) (λ g → LgB {Lv (ls lz)} (hΩ (inj₂ tt) g) × ¬ (g hz ≡ g (hs hz))) ×
  (∀ (g : HB (FlL lz) → HB (FlL (ls lz))) → LgB {FlL (ls lz)} (hΩ (inj₂ tt) g) → g hz ≡ g (hs hz))
contrastL = ((λ c → up c) , Lg-upΩL , (λ ())) , (λ g l → flL-const (ls lz) (inj₂ tt) g l hz (hs hz))
```

## §5 结论 (按档)

- **[构造, 定理]** `flat`, `stepF`, `supF` (合法的 `KS`); `antisym` (第一位置反对称); **`flat-const`**.
- **[定理, 前提实例]** `RFl`, **`CFl`**, **`UFl`** (平的候选满足 `LvCrit` 与 `LvUpper`); `RFlL`, **`CFlL`**, **`UFlL`** (满足 `LvCritL` 与 `LvUpperL`). 所以构造一路 `exact`, `exactL` 的前提除了 `Lev`, `Lv` 之外还有别的实例.
- **[定理, 盲]** **`same-levels→`**, **`same-levels←`**, **`same-levelsL→`**, **`same-levelsL←`** (由构造一路的定理: 级集合与 `Lev`/`Lv` 相等); `km`, `km⁻`, `km⁻km`, `kmkm⁻`, `km-lv` (种类逐个对应, 保级).
- **[定理, 差别]** **`fl-const`**, **`flL-const`** (平的候选里一切合法 Ω-结点的分支是常函数); **`contrast`**, **`contrastL`** (同一层号同一种类, `Lev`/`Lv` 有合法的非常值分支, 平的候选没有).
- **[判断]** (1) `LvCrit`/`LvCritL` 加上界确定的是 "层里有哪些级的坐标"; 要让层里真的有不可数的分支 (Ω-极限不退化), 判据还要说世界, 界与第一位置. 一条自然的补充是 "种类 $\kappa$ 的第一位置 `Pr` 就是坐标高度的 `⊲`, 界就是 `⊲` 到世界的一个分量" (`HtTowerTy.step` 的写法); 这条补充本身又读自现有形状, 写进判据前要算翻译账. (2) "唯一" 的范围: 级集合唯一是定理, 定义唯一不成立 (本篇). (3) 穷尽是判断.
