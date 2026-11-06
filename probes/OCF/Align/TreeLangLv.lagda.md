# 树的语言 (一): 由判据推出层的生成规则

> 不含记号. 入口 [TreeLang](TreeLang.lagda.md), 接口 [TreeLangIf](TreeLangIf.lagda.md) ("接口定稿 2026-11-05 20:27 (首次编译通过)", 变更记录: 无). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> **问题.** "下一个层号构造" 本身: 给层号 $c$ 的种类结构 `L c` 应当有哪些种类? 现有的 `HtTowerTy.Lev` 与 `LFReTy.Lv` 是先写出来的 (翻译账: "形状受作者对下标塔的直觉启发"). 本篇反过来: 只从判据出发, 证明满足判据的规则必须含有哪些级, 再看现有形状是不是恰好那一个.
>
> **结果 (都是定理, 除非标出).**
>
> 1. **`no-self`, `no-down` (对一切满足 `coord` 的候选).** 第 $c$ 层没有级为 $c$ 的种类; 级为 $y$ 的种类存在时, 第 $c$ 层的值不能无损地写进第 $y$ 层的值. 所以第 $x$ 层的读回最早只能在第 `hs x` 层作坐标, `feed` 取的就是最早的位置.
> 2. **`least` (形状定理, 下界).** 对一切满足 `LvCrit` 的候选 $R$, 一切层号 $c$: `Lev c` 的每个种类的级都在 $R$ 的第 $c$ 层出现. 每一行的来源: `hz` ← `base0`; `hs x` 的新种类 ← `feed`; `hs x`, `hl f`, `hΩ κ g` 的旧种类 ← `inherit`. **`Lev` 的三行 (`step`, `sup ℕ`, `sup (E S κ)`) 就是这三条判据各自逼出的最少内容.**
> 3. **`LevR`, `LevC`, `LevU` (实例).** `Lev` 本身满足 `LvCrit` 与字面上界 `LvUpper`. 所以在级集合上 **`Lev` 是满足判据的最小规则**.
> 4. **`exact→`, `exact←` (形状定理, 唯一).** 再加 `LvUpper` (级 $y$ 只在 `hs y` 是 $c$ 的子项时出现), 候选的级集合与 `Lev` 的**相等**. 判据把级集合定死了.
> 5. **剩下的自由度 (定理).** 不加 `LvUpper` 时不唯一: `R⁺` (在 ℕ-极限与 Ω-极限处给每个分支 $y$ 多一个级 $y$ 的种类) 满足 `LvCrit`, 却在 `hl (λ _ → 0)` 处有 `Lev` 没有的级 $0$ (`extra⁺`, `no-extra-Lev`), 所以不满足 `LvUpper` (`not-upper⁺`). 级集合之外, 判据不管**重数**: `Lev (hl (λ _ → 1))` 里级 $0$ 的种类有无穷多份 (`copies-Lev`); 判据也不管世界, 界, 第一位置 (`LvRule` 只看种类与坐标).
> 6. **一次封闭的层号 `LH` (§6).** 判据多一条 `cof`. `LFReTy.Lv` 满足 `LvCritL` 与 `LvUpperL` (`LvRL`, `LvCL`, `LvUL`), 是最小的 (`leastL`), 加上界后唯一 (`exactL→`, `exactL←`). 照 `Lev` 的样子写在 `LH` 上的规则 `R⁻` (`lΩ k g` 处只取分支的并, 不加 `step (Lv k)`) 不满足 `cof` (`no-cof⁻`, `no-crit⁻`). **`LFReTy` 在 `lΩ` 一行多放的分量 `step (Lv k)`, 就是 `cof` 与 `inherit` 沿 $k\prec$ `lΩ k g` 逼出的.**
>
> **只说明什么.** 判据决定的是**级集合** (哪些层的值能作坐标). 它们不决定重数, 世界, 界, 也不看值; 特别是不碰 C6 (升界) — 那是 [TreeLangRaise](TreeLangRaise.lagda.md) 的事.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLangLv where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerNeg using (_≺ᴮ_; ≺s; ≺l; ≺Ω)
open import OCF.Align.NegKindLvLev using (_⊏_; one; snoc; lvK; no-desc-at)
open import OCF.Align.LFReTy using (LH; lz; ls; ll; lΩ; Lv; S⊥; lvl; E-lvl)
open import OCF.Align.TreeLangIf
```

## §1 级不是自己; 不能向下无损地写

```agda
module _ {S : KS} {B : Set} (R : LvRule S B) where
  no-down : ∀ c κ {y} → lv R c κ ≡ inj₂ y → (d : HB (L R c) → HB (L R y)) (u : HB (L R y) → HB (L R c)) →
            ¬ (∀ x → u (d x) ≡ x)
  no-down c κ e = no-desc-at κ (trans (coord R c κ) (cong (Cdᴿ B (L R)) e))

  no-self : ∀ c κ → ¬ (lv R c κ ≡ inj₂ c)
  no-self c κ e = no-down c κ e (λ x → x) (λ x → x) (λ x → refl)

no-selfᴸ : ∀ (R : LvRuleL) x κ → ¬ (lvᴸ R x κ ≡ x)
no-selfᴸ R x κ e = no-desc-at κ (trans (coordᴸ R x κ) (cong (λ z → HB (Lᴸ R z)) e)) (λ x → x) (λ x → x) (λ x → refl)
```

## §2 下界: 满足判据的规则含 `Lev` 的一切级

```agda
module _ {S : KS} {B : Set} (R : LvRule S B) (C : LvCrit R) where
  least : ∀ c (κ : K (Lev c)) → InLv R c (lvK c κ)
  least hz κ = base0 C
  least (hs x) (inj₁ κ) = inherit C ≺s (lvK x κ) (least x κ)
  least (hs x) (inj₂ _) = feed C x
  least (hl f) (n , κ) = inherit C (≺l n) (lvK (f n) κ) (least (f n) κ)
  least (hΩ κ g) (e , κ′) = inherit C (≺Ω e) (lvK (g e) κ′) (least (g e) κ′)

  -- 子项 hs y 给出级 y
  char : ∀ {y c} → hs y ⊑ᴮ c → InLv R c (inj₂ y)
  char {y} rf = feed C y
  char (sn p q) = inherit C q _ (char p)

  -- 底在每一层
  base-all : ∀ c → InLv R c (inj₁ tt)
  base-all hz = base0 C
  base-all (hs x) = inherit C ≺s _ (base-all x)
  base-all (hl f) = inherit C (≺l 0) _ (base-all (f 0))
  base-all (hΩ κ g) = inherit C (≺Ω (bot S κ)) _ (base-all (g (bot S κ)))
```

## §3 `Lev` 满足判据

```agda
coordLev : ∀ {S : KS} (c : HB S) κ → E (Lev c) κ ≡ Cdᴿ A Lev (lvK c κ)
coordLev hz κ = refl
coordLev (hs x) (inj₁ κ) = coordLev x κ
coordLev (hs x) (inj₂ _) = refl
coordLev (hl f) (n , κ) = coordLev (f n) κ
coordLev (hΩ κ g) (e , κ′) = coordLev (g e) κ′

LevR : ∀ {S : KS} → LvRule S A
LevR = record { L = Lev ; lv = lvK ; coord = coordLev }

subUp : ∀ {S : KS} {y c : HB S} → y ≺ᴮ c → ∀ ℓ → SubLv y ℓ → SubLv c ℓ
subUp q (inj₁ _) p = tt
subUp q (inj₂ z) p = snoc p q

upUp : ∀ {S : KS} {y c : HB S} → y ≺ᴮ c → ∀ ℓ → UpLv y ℓ → UpLv c ℓ
upUp q (inj₁ _) p = tt
upUp q (inj₂ z) p = sn p q

subLev : ∀ {S : KS} (c : HB S) κ → SubLv c (lvK c κ)
subLev hz κ = tt
subLev (hs x) (inj₁ κ) = subUp ≺s (lvK x κ) (subLev x κ)
subLev (hs x) (inj₂ _) = one ≺s
subLev (hl f) (n , κ) = subUp (≺l n) (lvK (f n) κ) (subLev (f n) κ)
subLev (hΩ κ g) (e , κ′) = subUp (≺Ω e) (lvK (g e) κ′) (subLev (g e) κ′)

inhLev : ∀ {S : KS} {y c : HB S} → y ≺ᴮ c → ∀ ℓ → InLv LevR y ℓ → InLv LevR c ℓ
inhLev ≺s ℓ (κ , e) = inj₁ κ , e
inhLev (≺l n) ℓ (κ , e) = (n , κ) , e
inhLev (≺Ω c) ℓ (κ , e) = (c , κ) , e

LevC : ∀ {S : KS} → LvCrit (LevR {S})
LevC = record { base0 = tt , refl ; feed = λ x → inj₂ tt , refl ; inherit = inhLev ; sub = subLev }

LevU : ∀ {S : KS} → LvUpper (LevR {S})
LevU hz κ = tt
LevU (hs x) (inj₁ κ) = upUp ≺s (lvK x κ) (LevU x κ)
LevU (hs x) (inj₂ _) = rf
LevU (hl f) (n , κ) = upUp (≺l n) (lvK (f n) κ) (LevU (f n) κ)
LevU (hΩ κ g) (e , κ′) = upUp (≺Ω e) (lvK (g e) κ′) (LevU (g e) κ′)
```

## §4 加字面上界: 级集合与 `Lev` 相等

```agda
module _ {S : KS} {B : Set} (R : LvRule S B) (C : LvCrit R) (U : LvUpper R) where
  private
    toLev : ∀ c ℓ → UpLv c ℓ → InLv (LevR {S}) c ℓ
    toLev c (inj₁ tt) _ = base-all LevR LevC c
    toLev c (inj₂ y) p = char LevR LevC p

  exact→ : ∀ c ℓ → InLv R c ℓ → InLv (LevR {S}) c ℓ
  exact→ c ℓ (κ , e) = toLev c ℓ (subst (UpLv c) e (U c κ))

  exact← : ∀ c ℓ → InLv (LevR {S}) c ℓ → InLv R c ℓ
  exact← c ℓ (κ , e) = subst (InLv R c) e (least R C c κ)
```

## §5 自由度: 不加上界不唯一; 重数不定

`R⁺`: ℕ-极限与 Ω-极限处, 每个分支 $y$ 的规则外面再包一层 `step`, 多一个级 $y$ 的种类. 坐标仍是候选自己的低层, 判据全满足.

```agda
L⁺ : ∀ {S : KS} → HB S → KS
L⁺ hz = S₀
L⁺ (hs x) = step (L⁺ x)
L⁺ (hl f) = sup ℕ (λ n → step (L⁺ (f n)))
L⁺ {S} (hΩ κ g) = sup (E S κ) (λ e → step (L⁺ (g e)))

lv⁺ : ∀ {S : KS} (c : HB S) → K (L⁺ c) → ⊤ ⊎ HB S
lv⁺ hz _ = inj₁ tt
lv⁺ (hs x) (inj₁ κ) = lv⁺ x κ
lv⁺ (hs x) (inj₂ _) = inj₂ x
lv⁺ (hl f) (n , inj₁ κ) = lv⁺ (f n) κ
lv⁺ (hl f) (n , inj₂ _) = inj₂ (f n)
lv⁺ (hΩ κ g) (e , inj₁ κ′) = lv⁺ (g e) κ′
lv⁺ (hΩ κ g) (e , inj₂ _) = inj₂ (g e)

coord⁺ : ∀ {S : KS} (c : HB S) κ → E (L⁺ c) κ ≡ Cdᴿ A L⁺ (lv⁺ c κ)
coord⁺ hz κ = refl
coord⁺ (hs x) (inj₁ κ) = coord⁺ x κ
coord⁺ (hs x) (inj₂ _) = refl
coord⁺ (hl f) (n , inj₁ κ) = coord⁺ (f n) κ
coord⁺ (hl f) (n , inj₂ _) = refl
coord⁺ (hΩ κ g) (e , inj₁ κ′) = coord⁺ (g e) κ′
coord⁺ (hΩ κ g) (e , inj₂ _) = refl

R⁺ : ∀ {S : KS} → LvRule S A
R⁺ = record { L = L⁺ ; lv = lv⁺ ; coord = coord⁺ }

sub⁺ : ∀ {S : KS} (c : HB S) κ → SubLv c (lv⁺ c κ)
sub⁺ hz κ = tt
sub⁺ (hs x) (inj₁ κ) = subUp ≺s (lv⁺ x κ) (sub⁺ x κ)
sub⁺ (hs x) (inj₂ _) = one ≺s
sub⁺ (hl f) (n , inj₁ κ) = subUp (≺l n) (lv⁺ (f n) κ) (sub⁺ (f n) κ)
sub⁺ (hl f) (n , inj₂ _) = one (≺l n)
sub⁺ (hΩ κ g) (e , inj₁ κ′) = subUp (≺Ω e) (lv⁺ (g e) κ′) (sub⁺ (g e) κ′)
sub⁺ (hΩ κ g) (e , inj₂ _) = one (≺Ω e)

inh⁺ : ∀ {S : KS} {y c : HB S} → y ≺ᴮ c → ∀ ℓ → InLv R⁺ y ℓ → InLv R⁺ c ℓ
inh⁺ ≺s ℓ (κ , e) = inj₁ κ , e
inh⁺ (≺l n) ℓ (κ , e) = (n , inj₁ κ) , e
inh⁺ (≺Ω c) ℓ (κ , e) = (c , inj₁ κ) , e

C⁺ : ∀ {S : KS} → LvCrit (R⁺ {S})
C⁺ = record { base0 = tt , refl ; feed = λ x → inj₂ tt , refl ; inherit = inh⁺ ; sub = sub⁺ }

-- 在 hl (λ _ → 0) 处: R⁺ 有级 0, Lev 没有
z∞ : HB S₀
z∞ = hl (λ _ → hz)

extra⁺ : InLv (R⁺ {S₀}) z∞ (inj₂ hz)
extra⁺ = (0 , inj₂ tt) , refl

no-extra-Lev : ¬ InLv (LevR {S₀}) z∞ (inj₂ hz)
no-extra-Lev ((n , κ) , ())

not-upper⁺ : ¬ LvUpper (R⁺ {S₀})
not-upper⁺ U = no-extra-Lev (exact→ R⁺ C⁺ U z∞ (inj₂ hz) extra⁺)

-- 重数: Lev (hl (λ _ → 1)) 里级 0 的种类, 第 0 份与第 1 份不同
o∞ : HB S₀
o∞ = hl (λ _ → hs hz)

copies-Lev : (lvK o∞ (0 , inj₂ tt) ≡ inj₂ hz) × (lvK o∞ (1 , inj₂ tt) ≡ inj₂ hz) ×
             ¬ (_≡_ {A = K (Lev o∞)} (0 , inj₂ tt) (1 , inj₂ tt))
copies-Lev = refl , refl , (λ ())
```

## §6 一次封闭的层号 `LH`

`LFReTy.Lv` 满足 `LvCritL`; `cof` 一条由 `lΩ` 行的分量 `step (Lv k)` 的新种类给出, `inherit` 沿 $k\prec$ `lΩ k g` 由它的旧种类给出.

```agda
LvRL : LvRuleL
LvRL = record { Lᴸ = Lv ; lvᴸ = lvl ; coordᴸ = E-lvl }

inhLv : ∀ {y x} → y ≺ᴸ x → ∀ ℓ → InLvL LvRL y ℓ → InLvL LvRL x ℓ
inhLv ≺ls ℓ (κ , e) = inj₁ κ , e
inhLv (≺ll n) ℓ (κ , e) = (n , κ) , e
inhLv (≺lΩ c) ℓ (κ , e) = (inj₂ c , κ) , e
inhLv ≺lk ℓ (κ , e) = (inj₁ tt , inj₁ κ) , e

LvCL : LvCritL LvRL
LvCL = record { feedᴸ = λ x → inj₂ tt , refl ; inheritᴸ = inhLv ; cofᴸ = λ k g → (inj₁ tt , inj₂ tt) , refl }

LvUL : LvUpperL LvRL
LvUL lz ()
LvUL (ls x) (inj₁ κ) = pup (LvUL x κ) ≺ls
LvUL (ls x) (inj₂ _) = pls
LvUL (ll f) (n , κ) = pup (LvUL (f n) κ) (≺ll n)
LvUL (lΩ k g) (inj₁ _ , inj₁ κ) = pup (LvUL k κ) ≺lk
LvUL (lΩ k g) (inj₁ _ , inj₂ _) = plΩ g
LvUL (lΩ k g) (inj₂ c , κ) = pup (LvUL (g c) κ) (≺lΩ c)

module _ (R : LvRuleL) (C : LvCritL R) where
  leastL : ∀ x (κ : K (Lv x)) → InLvL R x (lvl x κ)
  leastL lz ()
  leastL (ls x) (inj₁ κ) = inheritᴸ C ≺ls _ (leastL x κ)
  leastL (ls x) (inj₂ _) = feedᴸ C x
  leastL (ll f) (n , κ) = inheritᴸ C (≺ll n) _ (leastL (f n) κ)
  leastL (lΩ k g) (inj₁ _ , inj₁ κ) = inheritᴸ C ≺lk _ (leastL k κ)
  leastL (lΩ k g) (inj₁ _ , inj₂ _) = cofᴸ C k g
  leastL (lΩ k g) (inj₂ c , κ) = inheritᴸ C (≺lΩ c) _ (leastL (g c) κ)

  charL : ∀ {y x} → Pass y x → InLvL R x y
  charL {y} pls = feedᴸ C y
  charL {y} (plΩ g) = cofᴸ C y g
  charL (pup p q) = inheritᴸ C q _ (charL p)

  exactL← : ∀ x y → InLvL LvRL x y → InLvL R x y
  exactL← x y (κ , e) = subst (InLvL R x) e (leastL x κ)

  exactL→ : LvUpperL R → ∀ x y → InLvL R x y → InLvL LvRL x y
  exactL→ U x y (κ , e) = charL′ (subst (λ z → Pass z x) e (U x κ))
    where
    charL′ : ∀ {y x} → Pass y x → InLvL LvRL x y
    charL′ {y} pls = inj₂ tt , refl
    charL′ {y} (plΩ g) = (inj₁ tt , inj₂ tt) , refl
    charL′ (pup p q) = inhLv q _ (charL′ p)
```

**照 `Lev` 的样子写在 `LH` 上: 不满足 `cof`.** `Lv⁻ (lΩ k g)` 只取分支的并 (下标仍是 `HB (Lv k)`), 不加 `step (Lv k)`.

```agda
Lv⁻ : LH → KS
Lv⁻ lz = S⊥
Lv⁻ (ls x) = step (Lv⁻ x)
Lv⁻ (ll f) = sup ℕ (λ n → Lv⁻ (f n))
Lv⁻ (lΩ k g) = sup (HB (Lv k)) (λ c → Lv⁻ (g c))

lv⁻ : ∀ x → K (Lv⁻ x) → LH
lv⁻ lz ()
lv⁻ (ls x) (inj₁ κ) = lv⁻ x κ
lv⁻ (ls x) (inj₂ _) = x
lv⁻ (ll f) (n , κ) = lv⁻ (f n) κ
lv⁻ (lΩ k g) (c , κ) = lv⁻ (g c) κ

coord⁻ : ∀ x κ → E (Lv⁻ x) κ ≡ HB (Lv⁻ (lv⁻ x κ))
coord⁻ lz ()
coord⁻ (ls x) (inj₁ κ) = coord⁻ x κ
coord⁻ (ls x) (inj₂ _) = refl
coord⁻ (ll f) (n , κ) = coord⁻ (f n) κ
coord⁻ (lΩ k g) (c , κ) = coord⁻ (g c) κ

R⁻ : LvRuleL
R⁻ = record { Lᴸ = Lv⁻ ; lvᴸ = lv⁻ ; coordᴸ = coord⁻ }

no-cof⁻ : ¬ InLvL R⁻ (lΩ lz (λ _ → lz)) lz
no-cof⁻ ((c , ()) , _)

no-crit⁻ : ¬ LvCritL R⁻
no-crit⁻ C = no-cof⁻ (cofᴸ C lz (λ _ → lz))
```

## §7 结论 (按档)

- **[定理]** `no-down`, `no-self`, `no-selfᴸ` (对一切满足 `coord` 的候选); **`least`**, `char`, `base-all` (对一切满足 `LvCrit` 的候选); `LevR`, `LevC`, `LevU` (实例); **`exact→`, `exact←`** (加 `LvUpper` 后级集合与 `Lev` 相等).
- **[定理, 自由度]** `R⁺`, `C⁺`, `extra⁺`, `no-extra-Lev`, `not-upper⁺` (不加上界不唯一); `copies-Lev` (重数不定).
- **[定理, LH]** `LvRL`, `LvCL`, `LvUL`; **`leastL`**, `charL`, **`exactL←`, `exactL→`**; `R⁻`, **`no-cof⁻`, `no-crit⁻`** (`Lev` 形状搬到 `LH` 不满足 `cof`).
- **[判断]** `LvUpper` 是 "只认字面证据" 的选择; 它挑掉的 `R⁺` 在 `hl (λ _ → 0)` 处多出的级 $0$, 读法上对应 "值为 $0$ 的层号却有第 $1$ 层的种类" — 这是值的说法, 本篇没有值的定理.
