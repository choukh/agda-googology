# `T⁺` 对输入单调, 否定一路 (一): 接口排除的两种形状确实是假的

> 不含记号. 入口 [NegTpMono](NegTpMono.lagda.md). 接口 [TpMonoIf](TpMonoIf.lagda.md) (定稿 2026-11-05 12:11) 的 "律的定义域" 一段说: (b) 量化一切世界是有意的, 走 "任意一个世界里有界的坐标" 就碰 `MonoPort9Neg.no-all` 那一类; 两个输入只在值上可比的, 不在定义域里. 那两句在接口里是判断. 本文把它们写成编译过的定理, 对任意 `F : Fn` (只要输出合法), 所以对 `T⁺` 也成立.
>
> 1. **`no-fst<W`** (无前提): "严格的字面第一位置, 但只在**某一个**合法世界里" (`FstMono<W`) 推出矛盾. 反例: 旧种类的恒等分支 $\Omega^A=\mathrm{h\Omega}\,\kappa_A\,e$ ($e$ 把 `A` 原样嵌进高度), 坐标 $a=F(\Omega^A)$ 在世界 $(a,0)$ 里有界; 由后继与 ℕ-极限两步得 $a\le F(e\,a)$, 再由律 $F(e\,a)<F(\Omega^A)=a$.
> 2. **`no-fstW`** (前提: 后继与 ℕ-极限两步严格, 即接口 `Steps` 的 `s-hs`, `s-hl`): "非严格的字面第一位置, 只在某一个合法世界里" (`FstMonoW`) 推出矛盾. 坐标取 $a=F(\Omega^A)+1$.
> 3. **新种类** (`no-fst<Wᴴ`, `no-fstWᴴ`, `no-allΩ₂`): 同一论证落在 `T-Ω₂` 的输入 $\Omega_2^H=\mathrm{h\Omega}\,\kappa_H\,\mathrm{up}$ 上, 坐标是 `H₀` 里的可数高度, 世界 $(0, e\,a)$. `no-allΩ₂`: 后继与极限两步严格时, "一切新种类分支 $\mathrm{up}\,c$ 都有 $F(\mathrm{up}\,c)\le F(\Omega_2^H)$" 是假的. 这是 `MonoPort9Neg.no-all` 在两种种类折叠上的对应.
> 4. **`no-valmono`** (前提: `Steps` 的 `s-hΩ` 一条): 对任何输入上的关系 $\preccurlyeq$, 只要它把常数 $0$ 分支的 $\Omega$-极限放在 $0$ 之下 ($\mathrm{h\Omega}\,\kappa_A\,(\lambda\_.0)\preccurlyeq 0$), "$x\preccurlyeq y\Rightarrow F\,x\le F\,y$" 就与 `s-hΩ` 矛盾. 前提的实例: 通常的值序 `_≤ᴴ_` (Ω-极限取上确界, `Ω0≤ᴴ0`). 所以按值的单调与字面的严格单调不相容: 构造一路要 `s-hΩ`, 就不能要按值的单调.
>
> **只否定什么.** 只否定 "某一个世界里的第一位置" 与 "按值" 这两种形状 (接口已排除它们). **不否定**接口的 (a) `SimInv`, (b) `FstMono`/`FstMono<` (一切世界), (c) `ShiftMono`, 也不否定 `Steps`: 那些律合起来有模型 ([NegTpMonoBlind](NegTpMonoBlind.lagda.md); 构造一路的 `TpMonoToy` 也给了一个). 第 2, 4 条的前提 (`s-hs`, `s-hl`, `s-hΩ`) 对 `T⁺` 是否成立正是构造一路要证的; 前提可满足由 `NegTpMonoBlind.rk-steps` 给出 (一个不是 `T⁺` 的 `F`). 第 1, 3 条中严格的那两条不要前提.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegTpMonoWorld where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ≤-suc; irr)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (S₁; Ht; H₀; Wd₂; LgW₂; κA; κH)
open import OCF.Align.HtTowerFClosed using (Lg-T⁺; Ω₂ᴴ; lΩ₂)
open import OCF.Align.TpMonoIf
```

## §1 把 `A` 嵌进高度; 旧种类的恒等分支

$e$ 不含 $\Omega$-极限, 所以它的位置在一切世界里都有 (`e⊲`).

```agda
eᴬ : ∀ {S} → A → HB S
eᴬ azero = hz
eᴬ (asuc a) = hs (eᴬ a)
eᴬ (alim f) = hl (λ n → eᴬ (f n))

e⊲ : ∀ {S w a b} → a C.⊲ b → eᴬ {S} a ⊲[ w ] eᴬ b
e⊲ C.self = hself
e⊲ (C.suc p) = hsuc (e⊲ p)
e⊲ (C.lim n p) = hlim n (e⊲ p)

Lg-e : ∀ {S} a → Lg a → LgB {S} (eᴬ a)
Lg-e azero l = tt
Lg-e (asuc a) l = Lg-e a l
Lg-e (alim f) (st , l) = (λ n → e⊲ (st n)) , (λ n → Lg-e (f n) (l n))

-- 旧种类上的恒等分支 (合法: 坐标单调由 e⊲ 给出)
Ωᴬ : Ht
Ωᴬ = hΩ κA eᴬ

lΩᴬ : LgB Ωᴬ
lΩᴬ = (λ lw e e′ p → e⊲ p) , (λ c lc → Lg-e c lc)

-- 新种类的坐标: H₀ 里的可数高度, 经 up 进 Ht
eH : A → Ht
eH a = up (eᴬ {S₀} a)

Lg-eH : ∀ a → Lg a → LgB (eH a)
Lg-eH a la = Lg-up (eᴬ a) (Lg-e a la)

≤suc : ∀ x → x ≤ asuc x
≤suc x = ≤-suc (≤-refl x)
```

## §2 只在一个世界里的第一位置

`FstMonoW`, `FstMono<W`: 接口 (b) 的两条, 但路径只在**一个**合法世界 $w$ 里给出 (接口要求一切世界). `StepsSL`: 接口 `Steps` 的后继与 ℕ-极限两条.

```agda
module _ (F : Fn) (LgF : ∀ h lh → Lg (F h lh)) where

  FstMonoW : Set
  FstMonoW = ∀ {w} a la b lb → LgW₂ w → a ⊲[ w ] b → F a la ≤ F b lb

  FstMono<W : Set
  FstMono<W = ∀ {w} a la b lb → LgW₂ w → a ⊲⁺[ w ] b → asuc (F a la) ≤ F b lb

  StepsSL : Set
  StepsSL = (∀ a la → asuc (F a la) ≤ F (hs a) la) ×
            (∀ (f : ℕ → Ht) (lf : LgB (hl f)) n → asuc (F (f n) (proj₂ lf n)) ≤ F (hl f) lf)

  steps→SL : Steps F → StepsSL
  steps→SL St = Steps.s-hs St , Steps.s-hl St

  w₀ : Wd₂
  w₀ = azero , hz

  lw₀ : LgW₂ w₀
  lw₀ = tt , tt

  fst<W→SL : FstMono<W → StepsSL
  fst<W→SL m = (λ a la → m {w₀} a la (hs a) la lw₀ (psuc hself)) ,
               (λ f lf n → m {w₀} (f n) (proj₂ lf n) (hl f) lf lw₀ (plim n hself))

  -- 后继与极限两步严格 ⇒ a ≤ F (e a): 输出至少是输入的可数高度本身
  id≤F : StepsSL → ∀ a (la : Lg a) → a ≤ F (eᴬ a) (Lg-e a la)
  id≤F st azero la = z≤
  id≤F st (asuc a) la = ≤-trans (s≤ (id≤F st a la)) (proj₁ st (eᴬ a) (Lg-e a la))
  id≤F st (alim f) (s , l) =
    l≤ (λ n → ≤-trans (id≤F st (f n) (l n))
                (≤-trans (≤suc (F (eᴬ (f n)) (Lg-e (f n) (l n))))
                  (proj₂ st (λ m → eᴬ (f m)) (Lg-e (alim f) (s , l)) n)))

  id≤FH : StepsSL → ∀ a (la : Lg a) → a ≤ F (eH a) (Lg-eH a la)
  id≤FH st azero la = z≤
  id≤FH st (asuc a) la = ≤-trans (s≤ (id≤FH st a la)) (proj₁ st (eH a) (Lg-eH a la))
  id≤FH st (alim f) (s , l) =
    l≤ (λ n → ≤-trans (id≤FH st (f n) (l n))
                (≤-trans (≤suc (F (eH (f n)) (Lg-eH (f n) (l n))))
                  (proj₂ st (λ m → eH (f m)) (Lg-eH (alim f) (s , l)) n)))
```

**旧种类.** 坐标 $a=F(\Omega^A)$ (严格) 或 $F(\Omega^A)+1$ (非严格), 世界 $(a,0)$, 路径 `hLim self hself`.

```agda
  no-fst<W : ¬ FstMono<W
  no-fst<W m = irr a (≤-trans (s≤ (id≤F (fst<W→SL m) a la))
                        (m {a , hz} (eᴬ a) (Lg-e a la) Ωᴬ lΩᴬ (la , tt) (pLim C.self hself)))
    where
    a = F Ωᴬ lΩᴬ
    la = LgF Ωᴬ lΩᴬ

  no-fstW : StepsSL → ¬ FstMonoW
  no-fstW st m = irr b (≤-trans (id≤F st a la)
                         (m {a , hz} (eᴬ a) (Lg-e a la) Ωᴬ lΩᴬ (la , tt) (hLim C.self hself)))
    where
    b = F Ωᴬ lΩᴬ
    a = asuc b
    la : Lg a
    la = LgF Ωᴬ lΩᴬ
```

**新种类.** $\Omega_2^H=\mathrm{h\Omega}\,\kappa_H\,\mathrm{up}$ (`T-Ω₂` 的输入). 坐标 $e\,a\in H_0$, 世界 $(0, e\,a)$: 新种类的界是世界的第二个分量, 路径 `hself`.

```agda
  no-fst<Wᴴ : ¬ FstMono<W
  no-fst<Wᴴ m = irr a (≤-trans (s≤ (id≤FH (fst<W→SL m) a la))
                         (m {azero , eᴬ a} (eH a) (Lg-eH a la) Ω₂ᴴ lΩ₂ (tt , Lg-e a la) (pLim hself hself)))
    where
    a = F Ω₂ᴴ lΩ₂
    la = LgF Ω₂ᴴ lΩ₂

  no-fstWᴴ : StepsSL → ¬ FstMonoW
  no-fstWᴴ st m = irr b (≤-trans (id≤FH st a la)
                          (m {azero , eᴬ a} (eH a) (Lg-eH a la) Ω₂ᴴ lΩ₂ (tt , Lg-e a la) (hLim hself hself)))
    where
    b = F Ω₂ᴴ lΩ₂
    a = asuc b
    la : Lg a
    la = LgF Ω₂ᴴ lΩ₂

  -- 不是一切新种类分支都在 Ω₂ᴴ 的值之下 (MonoPort9Neg.no-all 的对应)
  no-allΩ₂ : StepsSL → ¬ (∀ c (lc : LgB c) → F (up c) (Lg-up c lc) ≤ F Ω₂ᴴ lΩ₂)
  no-allΩ₂ st h = irr b (≤-trans (id≤FH st a la) (h (eᴬ a) (Lg-e a la)))
    where
    b = F Ω₂ᴴ lΩ₂
    a = asuc b
    la : Lg a
    la = LgF Ω₂ᴴ lΩ₂
```

## §3 按值的单调

`ValMono R`: 对输入上的任意关系 $R$, $R\,x\,y\Rightarrow F\,x\le F\,y$. 只要 $R$ 把常数 $0$ 分支的旧种类 $\Omega$-极限 $Z=\mathrm{h\Omega}\,\kappa_A\,(\lambda\_.0)$ 放在 $0$ 之下, 就与 `s-hΩ` ($F\,0<F\,Z$; $0$ 是 $Z$ 的最小坐标上的分支) 矛盾.

```agda
  Z : Ht
  Z = hΩ κA (λ _ → hz)

  lZ : LgB Z
  lZ = (λ lw e e′ p → hself) , (λ c lc → tt)

  ValMono : (Ht → Ht → Set) → Set
  ValMono R = ∀ a la b lb → R a b → F a la ≤ F b lb

  no-valmono : ∀ (R : Ht → Ht → Set) → R Z hz → Steps F → ¬ ValMono R
  no-valmono R z St m = irr (F hz tt) (≤-trans (Steps.s-hΩ St κA (λ _ → hz) lZ tt) (m Z lZ hz tt z))
```

**前提 `R Z hz` 的实例.** 通常的值序 (Ω-极限是分支的上确界). 在它下面 $Z$ 与 $0$ 互相 $\le$.

```agda
infix 4 _≤ᴴ_
data _≤ᴴ_ : Ht → Ht → Set where
  z≤ᴴ : ∀ {y} → hz ≤ᴴ y
  s≤ᴴ : ∀ {x y} → x ≤ᴴ y → hs x ≤ᴴ hs y
  ≤lᴴ : ∀ {x f} n → x ≤ᴴ f n → x ≤ᴴ hl f
  l≤ᴴ : ∀ {f y} → (∀ n → f n ≤ᴴ y) → hl f ≤ᴴ y
  ≤Ωᴴ : ∀ {x κ g} c → x ≤ᴴ g c → x ≤ᴴ hΩ κ g
  Ω≤ᴴ : ∀ {κ g y} → (∀ c → g c ≤ᴴ y) → hΩ κ g ≤ᴴ y

Ω0≤ᴴ0 : hΩ κA (λ _ → hz) ≤ᴴ hz
Ω0≤ᴴ0 = Ω≤ᴴ (λ _ → z≤ᴴ)

0≤ᴴΩ0 : hz ≤ᴴ hΩ κA (λ _ → hz)
0≤ᴴΩ0 = z≤ᴴ
```

## §4 对 `T⁺` 的实例

```agda
no-fst<W⁺ : ¬ FstMono<W T⁺ Lg-T⁺
no-fst<W⁺ = no-fst<W T⁺ Lg-T⁺

no-fstW⁺ : Steps T⁺ → ¬ FstMonoW T⁺ Lg-T⁺
no-fstW⁺ St = no-fstW T⁺ Lg-T⁺ (steps→SL T⁺ Lg-T⁺ St)

no-allΩ₂⁺ : Steps T⁺ → ¬ (∀ c (lc : LgB c) → T⁺ (up c) (Lg-up c lc) ≤ T⁺ Ω₂ᴴ lΩ₂)
no-allΩ₂⁺ St = no-allΩ₂ T⁺ Lg-T⁺ (steps→SL T⁺ Lg-T⁺ St)

no-valmono⁺ : Steps T⁺ → ¬ ValMono T⁺ Lg-T⁺ _≤ᴴ_
no-valmono⁺ = no-valmono T⁺ Lg-T⁺ _≤ᴴ_ Ω0≤ᴴ0
```
