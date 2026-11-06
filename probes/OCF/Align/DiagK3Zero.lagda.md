# 可数层的对角, 第三轮 (一): `towerL′` 的第 0 级, `Lev` 种类根本不进层

> 不含记号. 入口 [DiagK3](DiagK3.lagda.md). `towerL′` 的第 0 级是 `L′ 1 = step S₀ ⊕ₖ Lev (Ωtop S₀)`, 级顶 `λh 0 = ι true (Ωtop S₀)`. 这里先看清: **级顶以下的层全在 `true` 一半** (`true-below`), 所以 `Lev` 的种类在第 0 级的级顶下面**不出现在任何层里** (`noLev₀`). 于是第 0 级的折叠可以把 `false` 一半投影掉 (`pr₀`: `Lev` 种类的 $\Omega$-节点取底坐标的分支), 再交给现成的 `HtTowerFClosed.T⁺`.
>
> - **`Lg-pr₀`** (定理): 投影保合法, 对 `HB (L′ 1)` 的一切合法高度. 关键是只在 "`false` 分量取最小世界" 的世界 `embW w` 里用原高度的合法性, 那里 `Lev` 种类的坐标只有底是有界的 (`bdBot`), 所以 "取底坐标" 保第一位置 (`pr₀-mono`).
> - **`fold₀`, `Lg-fold₀`** (定理): 第 0 级上对一切合法高度的折叠, 合法由形状给出 (`T⁺` 的部分和).
> - **`pr₀-top`** (定理): `pr₀ (λh 0)` 与 `Ωtop S₀` 互模拟 (`_≈_`, 逐分支, 不用函数外延). 所以第 0 级的闭项 `t₀ = fold₀ (λh 0)` 与 `HtTowerFClosed.T-Ω₂` 是同一棵树的折叠 (两边的输入互模拟; 输出值相等是判断, 读 $\psi_0(\Omega_{\Omega_2})$, 同 `HtTowerF`).
>
> **这对 `DiagK2` 的意思 (判断).** `DiagK2` 说第一个障碍在 `L′ 1` 上; 精确地说, `L′ 1` 的函数世界在第 0 级**级顶**的折叠里用不到. `Lev` 种类第一次进层是第 1 级 (`L′ 2`), 见 [DiagK3One](DiagK3One.lagda.md) 的 `lev₁`. 投影只对级顶以下无损; 对别的合法高度, `Lev` 种类的节点被压成一个分支 (有损, 但合法).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DiagK3Zero where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym)
open import OCF.Align.CumReadCF using (A; azero; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.HtTowerNStage using (L′; two; dWLev)
open import OCF.Align.DiagKTop using (λh)
import OCF.Align.HtTowerFClosed as TC
import OCF.Free.Level as FL
open import OCF.Align.DiagKSum using (ord)
```

## §1 记号: 第 0 级的两半

```agda
S₁ : KS
S₁ = step S₀

L1 : KS
L1 = L′ 1

LevΩ : KS
LevΩ = Lev (Ωtop S₀)

ιt : HB S₁ → HB L1
ιt = ι {I = Bool} {F = two S₁ LevΩ} true
```

## §2 级顶以下全在 `true` 一半

```agda
true-below : ∀ y {x w} → x ⊲[ w ] ιt y → Σ (HB S₁) (λ y′ → x ≡ ιt y′)
true-below hz hself = hz , refl
true-below (hs y) hself = hs y , refl
true-below (hl f) hself = hl f , refl
true-below (hΩ κ g) hself = hΩ κ g , refl
true-below (hs y) (hsuc p) = true-below y p
true-below (hl f) (hlim n p) = true-below (f n) p
true-below (hΩ κ g) (hLim e p) = true-below (g _) p

side : HB L1 → Bool
side (hΩ (b , _) _) = b
side _ = true

side-ι : ∀ y → side (ιt y) ≡ true
side-ι hz = refl
side-ι (hs y) = refl
side-ι (hl f) = refl
side-ι (hΩ κ g) = refl

t≢f : true ≡ false → ⊥
t≢f ()

-- 级顶以下没有以 Lev 种类为分支的层
noLev₀ : ∀ {w κ g} → hΩ (false , κ) g ⊲[ w ] λh 0 → ⊥
noLev₀ p with true-below (Ωtop S₀) p
... | y , e = t≢f (sym (subst (λ z → side z ≡ true) (sym e) (side-ι y)))
```

## §3 最小的 `Lev` 世界: 合法, 且只有底坐标有界

```agda
lgdWLev : ∀ {S} (x : HB S) → LgW (Lev x) (dWLev x)
lgdWLev hz = tt
lgdWLev (hs x) = lgdWLev x , tt
lgdWLev (hl f) = λ n → lgdWLev (f n)
lgdWLev (hΩ κ g) = λ c → lgdWLev (g c)

bdBot : ∀ {S} (x : HB S) κ e → Bd (Lev x) κ e (dWLev x) → e ≡ bot (Lev x) κ
bdBot hz tt e C.self = refl
bdBot (hs x) (inj₁ κ) e p = bdBot x κ e p
bdBot (hs x) (inj₂ tt) e hself = refl
bdBot (hl f) (n , κ) e p = bdBot (f n) κ e p
bdBot (hΩ κ₀ g) (c , κ) e p = bdBot (g c) κ e p

embW : Wd S₁ → Wd L1
embW w true = w
embW w false = dWLev (Ωtop S₀)

lgEmb : ∀ {w} → LgW S₁ w → LgW L1 (embW w)
lgEmb lw true = lw
lgEmb lw false = lgdWLev (Ωtop S₀)
```

## §4 投影与合法

```agda
pr₀ : HB L1 → HB S₁
pr₀ hz = hz
pr₀ (hs x) = hs (pr₀ x)
pr₀ (hl f) = hl (λ n → pr₀ (f n))
pr₀ (hΩ (true , κ) g) = hΩ κ (λ c → pr₀ (g c))
pr₀ (hΩ (false , κ) g) = pr₀ (g (bot LevΩ κ))

pr₀-mono : ∀ {x y w} → x ⊲[ embW w ] y → pr₀ x ⊲[ w ] pr₀ y
pr₀-mono hself = hself
pr₀-mono (hsuc p) = hsuc (pr₀-mono p)
pr₀-mono (hlim n p) = hlim n (pr₀-mono p)
pr₀-mono (hLim {κ = true , κ} e p) = hLim e (pr₀-mono p)
pr₀-mono {x} {w = w} (hLim {κ = false , κ} {g = g} {c = c} e p) =
  subst (λ z → pr₀ x ⊲[ w ] pr₀ (g z)) (bdBot (Ωtop S₀) κ c e) (pr₀-mono p)

lgBot : ∀ κ → LgE LevΩ κ (bot LevΩ κ)
lgBot κ = lgBd LevΩ (botBd LevΩ κ (dWLev (Ωtop S₀))) (lgdWLev (Ωtop S₀))

Lg-pr₀ : ∀ x → LgB x → LgB (pr₀ x)
Lg-pr₀ hz l = tt
Lg-pr₀ (hs x) l = Lg-pr₀ x l
Lg-pr₀ (hl f) (st , l) = (λ {w} n → pr₀-mono (st {embW w} n)) , (λ n → Lg-pr₀ (f n) (l n))
Lg-pr₀ (hΩ (true , κ) g) (mo , l) =
  (λ {w} lw e e′ p → pr₀-mono (mo {embW w} (lgEmb lw) e e′ p)) , (λ c lc → Lg-pr₀ (g c) (l c lc))
Lg-pr₀ (hΩ (false , κ) g) (mo , l) = Lg-pr₀ (g (bot LevΩ κ)) (l _ (lgBot κ))
```

## §5 第 0 级的折叠与闭项

```agda
fold₀ : (Λ : HB L1) → LgB Λ → A
fold₀ Λ l = TC.T⁺ (pr₀ Λ) (Lg-pr₀ Λ l)

Lg-fold₀ : ∀ Λ (l : LgB Λ) → Lg (fold₀ Λ l)
Lg-fold₀ Λ l = TC.Lg-T⁺ (pr₀ Λ) (Lg-pr₀ Λ l)
```

**互模拟.** 逐分支的同构, 不用函数外延.

```agda
infix 4 _≈_
data _≈_ {S : KS} : HB S → HB S → Set where
  ≈z : hz ≈ hz
  ≈s : ∀ {a b} → a ≈ b → hs a ≈ hs b
  ≈l : ∀ {f g} → (∀ n → f n ≈ g n) → hl f ≈ hl g
  ≈Ω : ∀ {κ f g} → (∀ c → f c ≈ g c) → hΩ κ f ≈ hΩ κ g

pr∘ι : ∀ y → pr₀ (ιt y) ≈ y
pr∘ι hz = ≈z
pr∘ι (hs y) = ≈s (pr∘ι y)
pr∘ι (hl f) = ≈l (λ n → pr∘ι (f n))
pr∘ι (hΩ κ g) = ≈Ω (λ c → pr∘ι (g c))

pr₀-top : pr₀ (λh 0) ≈ TC.Ω₂ᴴ
pr₀-top = pr∘ι (Ωtop S₀)

lλ₀ : LgB (λh 0)
lλ₀ = Lg-ι {F = two S₁ LevΩ} true (Ωtop S₀) TC.lΩ₂

t₀ : A
t₀ = fold₀ (λh 0) lλ₀

Lg-t₀ : Lg t₀
Lg-t₀ = Lg-fold₀ (λh 0) lλ₀

fgh₀ : ℕ → ℕ
fgh₀ = FL.FGH (ord t₀)
```
