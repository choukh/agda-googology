# 高度的高度 (二): 坐标是高度时的连续分支

> 不含记号. 入口 [HtTower](HtTower.lagda.md). [HtOutRead](HtOutRead.lagda.md) 的 `Cont` 说: 坐标是 `A` 时, $\Omega$-分支在极限坐标处字面连续, 后继处步进, 就合法 (`cont→LgH`). 坐标换成高度 (`step S` 的新种类, 坐标是 `HB S`), 坐标类型多了极限构造子: `hl` 与**每个旧种类的 `hΩ κ`**. 一步定理 `cont→Lg` 对一切 `S` 成立:
>
> - `c-lim`: $g(\mathrm{hl}\,f)\equiv\mathrm{hl}(g\circ f)$;
> - **`c-Ω`**: $g(\mathrm{h\Omega}\,\kappa\,h)\equiv\mathrm{h\Omega}\,\kappa\,(g\circ h)$, 对每个旧种类 $\kappa$ (输出的种类是 `inj₁ κ`);
> - `c-suc`: $g\,x\lhd g(x+1)$, 在一切世界里;
> - 起点与后继保合法.
>
> 单调对坐标的路径归纳, 不要坐标合法, 不看世界的界. `c-Ω` 是新字段: 去掉它就有不合法的反例 ([HtTowerNeg](HtTowerNeg.lagda.md) 的 `drop-Ω`). 对坐标递归的分支 `nbᴮ` 自动连续; 嵌入 `up` 是它的特例, 所以 `Ωtop S` (新种类上的恒等分支, 读 "第 $S$ 级之上的第一个 $\Omega$") 合法 (`Lg-Ωtop`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtTowerCont where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.HtTowerTy
```

## §1 连续

```agda
module _ {S : KS} where
  record ContB (g : HB S → HB (step S)) : Set where
    constructor ctB
    field
      c-lim : ∀ f → g (hl f) ≡ hl (λ n → g (f n))
      c-Ω   : ∀ κ h → g (hΩ κ h) ≡ hΩ (inj₁ κ) (λ c → g (h c))
      c-suc : ∀ x {w} → g x ⊲[ w ] g (hs x)
      c-lgz : LgB (g hz)
      c-lgs : ∀ x → LgB (g x) → LgB (g (hs x))
  open ContB public
```

**单调.** 对路径归纳: 自身; 后继 (步进); $\mathbb N$-极限 (`c-lim`, 再进第 $n$ 项); $\Omega$-极限 (`c-Ω`, 再进同一个坐标的分支, 界的证据原样: 旧种类 $\kappa$ 在新世界里的界就是旧世界里的界).

```agda
  cont-mono : ∀ {g} → ContB g → ∀ {x y w β} → x ⊲[ w ] y → g x ⊲[ (w , β) ] g y
  cont-mono K hself = hself
  cont-mono K (hsuc p) = ⊲ᴮ-tr (cont-mono K p) (c-suc K _)
  cont-mono {g} K {x} {w = w} {β} (hlim {f = f} n p) =
    subst (λ z → g x ⊲[ (w , β) ] z) (sym (c-lim K f)) (hlim n (cont-mono K p))
  cont-mono {g} K {x} {w = w} {β} (hLim {κ = κ} {g = h} e p) =
    subst (λ z → g x ⊲[ (w , β) ] z) (sym (c-Ω K κ h)) (hLim e (cont-mono K p))

  cont-lg : ∀ {g} → ContB g → ∀ x → LgB x → LgB (g x)
  cont-lg K hz _ = c-lgz K
  cont-lg K (hs x) l = c-lgs K x (cont-lg K x l)
  cont-lg {g} K (hl f) (st , l) =
    subst LgB (sym (c-lim K f)) ((λ n → cont-mono K (st n)) , (λ n → cont-lg K (f n) (l n)))
  cont-lg {g} K (hΩ κ h) (mo , l) =
    subst LgB (sym (c-Ω K κ h)) ((λ lw e e′ p → cont-mono K (mo (proj₁ lw) e e′ p)) , (λ c lc → cont-lg K (h c) (l c lc)))
```

**一步定理.** 新种类上的分支连续就合法. 新种类的界与第一位置都是 `HB S` 的 `⊲` (`Step.Bd⁺`, `Step.Pr⁺`), 单调就是 `cont-mono`.

```agda
  cont→Lg : ∀ {g} → ContB g → LgB {step S} (hΩ (inj₂ tt) g)
  cont→Lg K = (λ lw e e′ p → cont-mono K p) , (λ c lc → cont-lg K c lc)
```

## §2 对坐标递归的分支

`nbᴮ b s`: $g(0)=b$, $g(x+1)=s\,x\,(g\,x)$, 极限 (两种) 处取同一个构造子. 与 `HtOutRead.nb` 同形, 多一种极限. 连续是定义性的.

```agda
  nbᴮ : HB (step S) → (HB S → HB (step S) → HB (step S)) → HB S → HB (step S)
  nbᴮ b s hz = b
  nbᴮ b s (hs x) = s x (nbᴮ b s x)
  nbᴮ b s (hl f) = hl (λ n → nbᴮ b s (f n))
  nbᴮ b s (hΩ κ h) = hΩ (inj₁ κ) (λ c → nbᴮ b s (h c))

  nb-contB : ∀ {b s} → LgB b → (∀ x h {w} → h ⊲[ w ] s x h) → (∀ x h → LgB h → LgB (s x h)) → ContB (nbᴮ b s)
  nb-contB {b} {s} lb fs ls = ctB (λ f → refl) (λ κ h → refl) (λ x → fs x (nbᴮ b s x)) lb (λ x → ls x (nbᴮ b s x))

  up-cont : ContB (up {S})
  up-cont = ctB (λ f → refl) (λ κ h → refl) (λ x → hsuc hself) tt (λ x l → l)

Ωtop : (S : KS) → HB (step S)
Ωtop S = hΩ (inj₂ tt) up

Lg-Ωtop : ∀ S → LgB (Ωtop S)
Lg-Ωtop S = cont→Lg up-cont
```
