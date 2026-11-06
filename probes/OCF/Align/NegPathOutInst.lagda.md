# 路径记在折叠输出上, 否定一路 (六): 对构造一路实例 `IX₁` 的检查

> 不含记号. 入口 [NegPathOut](NegPathOut.lagda.md). 只读导入构造一路的 [PathOutX1](PathOutX1.lagda.md) (实例 `IX₁`, 23:21 版: 种类证据是 "坐标在界之下" $y+1\lhd B$) 与 [PathOutFold](PathOutFold.lagda.md) (`PH`), 不改它们. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **实例的形状 (读自 `PathOutX1`).** 世界是界 $B$ ($1\lhd B$, 合法); 种类 $(\mathrm{inj}_2\,y,\kappa)$ 的证据是 $y+1\lhd B$; 进入 $(\mathrm{inj}_2\,y,\kappa)$-结点的分支世界不变; 进入 $\Omega_1$-结点的分支 $e$ (可入: $B\lhd e$, `LgB e`) 后世界换成 $e+1$. 折叠的输入谓词 `PH` 要求每个结点都有证据, 而且对 $\Omega_1$-结点的**一切**可入分支.
>
> **结果.**
>
> 1. **`ph-ment⁰` (定理).** `PH b h` 且 $h$ 提到坐标 $y$ (不经 $\Omega_1$-结点), 则 $y+1\lhd b$.
> 2. **`ph-lg-own` (定理).** $\Omega_1$-结点 $\mathrm{h\Omega}\,\Omega_1\,g$ 的分支都不含 $\Omega_1$-结点; 若它**合法** (`LgB`) 且某个可入的合法坐标 $x$ 处分支 $g\,x$ **提到 $x$ 自己**, 则它不满足 `PH B`. 证明: 可入坐标 $e=\lim(x,x,\dots)$ (合法, 字面在 $B$ 之上, $x\lhd e$); 合法性把 "提到 $x$" 带进 $g\,e$ (`ment⊲⁰`); `PH` 在那里要 $x+1\lhd e+1$, 而 $x+1\not\lhd\lim(x,x,\dots)$. 这一条靠的是**非严格的 ℕ-极限坐标** (合法性允许相邻项相等, 纲领 1 的解释): 值上 $\lim(x,x,\dots)=x$, 字面上 $x$ 不严格在它之下.
> 3. **三个实例.**
>    - **`¬PH-Dᶜ` (定理).** `NegPathOutLg.Dᶜ` (合法; 分支 $c$ 提到 $0,\dots,c$) 对任何合法界都不满足 `PH`: 2 的实例 ($x=B+1$).
>    - **`PH-D`, `¬LgB-D` (定理).** `NegPathOutWorld.D κ₁` (分支 $c$ 只是第 $c$ 个种类的结点) 对一切界满足 `PH`, 但不合法.
>    - **`Dˢ` (构造, 边界): `Lg-Dˢ`, `PH-Dˢ`.** 分支 $c$ 只提到**严格在 $c$ 之下**的坐标 ($g\,(c+1)$ 是种类 $c$ 的结点, 分支 $g\,c$): 合法, 且对一切界满足 `PH`. 所以 `PH` 与 `LgB` 可以同时成立; 被 2 排除的恰是 "分支提到自己的坐标".
> 4. **`¬LgB-topX₁` (定理).** 构造一路闭项 `TX₁` 的输入 `topX₁` ($\Omega_1$-结点, 分支 $c$ 是 $\iota_{\mathrm{inj}_2 c}\,\Omega_{c+1}$) 满足 `PH` (构造一路的 `PH-top`), 但**不合法**: 分支 $0$, $1$ 在 `Lv X₁` 的不同分量 (`NegTySupDiag.no-cross`). `LgB-TX₁` 来自 `Sh-Ψ`, 不看输入. 这是 2 的另一边 (分支提到自己坐标、满足 `PH` 的就不合法), 也是 `NegTySupC.¬LgB-topω` 在 lΩ 层号上的重演.
> 5. **`top′` (构造, 边界): `Lg-top′`, `PH-top′`.** 分支 $c$ 是 "一切 $y+1$ 字面在 $c$ 里的第 $y+1$ 层地板" 用 $\boxplus$ 接起来 (`HtTowerU.θ` 的形状). 合法且对一切界满足 `PH`. 所以构造一路可以把闭项的输入换成合法的; 读法是否不变是判断, 本篇没有值的定理.
> 6. **`tri-IX₁`, `no-world-IX₁` (定理, 正面与前提实例).** 实例的 `correct₁` (构造一路的定理) 经 `NegPathOutIf.Tri` 给出: 每次 `dec` 的种类层号与目标字面三歧. 层号 $\lim\mathrm{od}$ 的种类 `κod` 与目标 $\lim\mathrm{ev}$ 没有合法世界同时带证据 (`no-world-IX₁`, 由 `NegPathOutIf.¬tri-od-ev`).
> 7. **`LgB-TX₁c` (定理, 盲).** `shift` 换成常值的实例 `IX₁c` (`NegPathOutIf.constShiftOf`, `correct` 不变) 上同一闭项公式也有 `LgB` 证书. 证书与 `correct₁` 都不约束 `shift`.
>
> **前提实例.** 2: `Dᶜ` (`Lg-Dᶜ`, $x=B+1$). 3, 4, 5, 7: 无额外前提. 6: 任一合法世界, 例如 $B=1$ (`PathOut.lW₀`).
>
> **只否定什么.** 只否定: 输入同时合法且满足 `PH`, 对 "某个可入坐标处的分支提到这个坐标自己、分支不含 $\Omega_1$-结点" 的 $\Omega_1$-结点. **不否定**: `IX₁` 的 `correct₁`; 折叠与 `Sh` 证书; 闭项 `TX₁` 的 `LgB` 证书 (它成立; 4 只说输入不合法); `Dˢ` 一类输入 (构造); 只对 `shift` 给出的坐标 ($B\boxplus\mathrm{leg}\,c$) 要求路径的 `PH` 变体 (那时 2 的坐标 $\lim(x,x,\dots)$ 不一定出现; 未查). 本篇没有关闭任何路线.
>
> **对纲领与目标 (判断, 依据 2, 3).** 构造一路的证据方向是 "坐标在界之下", 与目标同向 (23:16 的上一版是 "在界之上", 本路对上一版的检查没有编译完成实例就改了, 不作结论). 现在的边界是字面的: 以 "提到自己坐标" 的形状写的合法输入 (`Dᶜ`, 读 $\sup_c\Omega_{c+1}$) 被 `PH` 排除, 以 "只提到更小坐标" 的形状写的 (`Dˢ`) 不被排除. 构造一路的闭项输入 `topX₁` 属于 "满足 `PH` 而不合法" 的一边 (4); 合法且满足 `PH` 的 `top′` 存在 (5). 读法: 构造一路自述 `TX₁` 读 ψ₀(Ω_{Ω_1}), 与 `TySup.TΩΩ` 相同, 未越过 (判断, 两边都没有值的定理).
>
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegPathOutInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥; Lv)
open import OCF.Align.StallDxBdec using (<l₀; lt→≢)
open import OCF.Align.PathOutIf
open import OCF.Align.PathOutX1 using (IX₁; XS₁; κΩ; LgW₁)
open import OCF.Align.PathOutFold IX₁ using (PH)
open import OCF.Align.NegPathOutWorld using (module LOm; G₁; κ₁; escape)
open import OCF.Align.NegPathOutLg using (module Spread; gᶜ; Dᶜ; Lg-Dᶜ; kc)
import OCF.Align.NegPathOutIf as NI
open import OCF.Align.PathOut using (topX₁; PH-top; TX₁; LgB-TX₁; W₀; lW₀; sh→lgB₁)
import OCF.Align.PathOutFold as PF
open import OCF.Align.TySupSum using (topΣ; Lg-topΣ)
open import OCF.Align.TySupC using (LC)
open import OCF.Align.NegTySupDiag using (no-cross)
open import OCF.Align.HtTowerNeg using (evᴴ; odᴴ)

open LOm G₁ using (Ment⁰; dep; D)
open Spread G₁ using (wB; lgwB)
```

## §1 `PH` 要提到的坐标严格在界之下

`NoΩ₁ h`: $h$ 里没有 $\Omega_1$-结点.

```agda
NoΩ₁ : HB XS₁ → Set
NoΩ₁ hz = ⊤
NoΩ₁ (hs h) = NoΩ₁ h
NoΩ₁ (hl f) = ∀ n → NoΩ₁ (f n)
NoΩ₁ (hΩ (inj₁ _ , inj₁ ()) g)
NoΩ₁ (hΩ (inj₁ _ , inj₂ _) g) = ⊥
NoΩ₁ (hΩ (inj₂ y , κ) g) = ∀ e → NoΩ₁ (g e)

ph-ment⁰ : ∀ {b y} h → PH b h → Ment⁰ y h → hs y ⊲[ tt ] b
ph-ment⁰ hz ph ()
ph-ment⁰ (hs h) ph m = ph-ment⁰ h ph m
ph-ment⁰ (hl f) ph (n , m) = ph-ment⁰ (f n) (ph n) m
ph-ment⁰ (hΩ (inj₁ _ , inj₁ ()) g) ph m
ph-ment⁰ (hΩ (inj₁ _ , inj₂ _) g) ph ()
ph-ment⁰ (hΩ (inj₂ y′ , κ) g) (yb , k) (inj₁ refl) = yb
ph-ment⁰ (hΩ (inj₂ y′ , κ) g) (yb , k) (inj₂ (e , m)) = ph-ment⁰ (g e) (k e tt) m
```

第一位置保 "提到坐标 (不经 $\Omega_1$)", 只要大的一方不含 $\Omega_1$-结点.

```agda
ment⊲⁰ : ∀ {w a b y} → a ⊲[ w ] b → NoΩ₁ b → Ment⁰ y a → Ment⁰ y b
ment⊲⁰ hself nb m = m
ment⊲⁰ (hsuc p) nb m = ment⊲⁰ p nb m
ment⊲⁰ (hlim n p) nb m = n , ment⊲⁰ p (nb n) m
ment⊲⁰ (hLim {κ = inj₁ _ , inj₁ ()} _ _) nb m
ment⊲⁰ (hLim {κ = inj₁ _ , inj₂ _} _ _) () m
ment⊲⁰ (hLim {κ = inj₂ y′ , κ} {c = e} _ p) nb m = inj₂ (e , ment⊲⁰ p (nb e) m)
```

## §2 合法, 分支提到自己的坐标, 与 `PH` 冲突

$x+1\not\lhd\lim(x,x,\dots)+1$.

```agda
cst : HB S⊥ → HB S⊥
cst x = hl (λ _ → x)

Lg-cst : ∀ {x} → LgB x → LgB (cst x)
Lg-cst lx = (λ n → hself) , (λ n → lx)

unsucE : ∀ {a b : HB S⊥} → hs a ⊲[ tt ] b → ∀ {E} → b ≡ hs E → (a ≡ E) ⊎ (hs a ⊲[ tt ] E)
unsucE hself refl = inj₁ refl
unsucE (hsuc p) refl = inj₂ p
unsucE (hlim _ _) ()
unsucE (hLim {κ = ()} _ _) _

intoL : ∀ {a b : HB S⊥} → a ⊲[ tt ] b → ∀ {f} → b ≡ hl f → (a ≡ hl f) ⊎ Σ ℕ (λ n → a ⊲[ tt ] f n)
intoL hself e = inj₁ e
intoL (hlim n q) refl = inj₂ (n , q)
intoL (hsuc _) ()
intoL (hLim {κ = ()} _ _) _

s≢l : ∀ {x : HB S⊥} {f} → ¬ (hs x ≡ hl f)
s≢l ()

no-cst : ∀ x → ¬ (hs x ⊲[ tt ] hs (cst x))
no-cst x p with unsucE p refl
... | inj₁ e = lt→≢ {S⊥} (<l₀ 0) e
... | inj₂ q with intoL q refl
...   | inj₁ e = s≢l e
...   | inj₂ (n , r) = escape x (hs hz) tt r

ph-lg-own : ∀ (g : HB S⊥ → HB XS₁) B → (∀ c → NoΩ₁ (g c)) → LgB (hΩ κΩ g) →
  ∀ x → LgB x → B ⊲[ tt ] x → Ment⁰ x (g x) → ¬ PH B (hΩ κΩ g)
ph-lg-own g B nog (mo , _) x lx Bx m (_ , k) =
  no-cst x (ph-ment⁰ (g (cst x)) (k (cst x) (hlim 0 Bx , Lg-cst lx))
    (ment⊲⁰ (mo {wB (cst x)} (lgwB (cst x) (Lg-cst lx)) (hlim 0 hself) hself (hlim 0 hself)) (nog (cst x)) m))
```

## §3 实例

`Dᶜ`: 合法, 不满足 `PH` ($x=B+1$, 分支 $g\,(B+1)$ 是种类 $B+1$ 的结点).

```agda
noΩ-gᶜ : ∀ c → NoΩ₁ (gᶜ c)
noΩ-gᶜ hz = λ _ → tt
noΩ-gᶜ (hs c) = λ _ → noΩ-gᶜ c
noΩ-gᶜ (hl f) = λ n → noΩ-gᶜ (f n)
noΩ-gᶜ (hΩ () _)

¬PH-Dᶜ : ∀ B → LgB B → ¬ PH B Dᶜ
¬PH-Dᶜ B lB = ph-lg-own gᶜ B noΩ-gᶜ Lg-Dᶜ (hs B) lB (hsuc hself) (inj₁ refl)
```

`D κ₁`: 满足 `PH` (对一切界), 不合法 (分支 $1$ 不提到坐标 $0$).

```agda
PH-D : ∀ B → PH B (D κ₁)
PH-D B = tt , (λ e a → hself , (λ _ _ → tt))

noΩ-dep : ∀ c → NoΩ₁ (dep κ₁ c)
noΩ-dep c = λ _ → tt

¬LgB-D : ¬ LgB (D κ₁)
¬LgB-D (mo , _) with ment⊲⁰ (mo {wB (hs hz)} (lgwB (hs hz) tt) (hsuc hself) hself (hsuc hself))
                           (noΩ-dep (hs hz)) (inj₁ {B = Σ _ (λ e → Ment⁰ hz hz)} refl)
... | inj₁ ()
... | inj₂ (_ , ())
```

`Dˢ`: 分支 $c+1$ 是种类 $c$ 的结点, 分支取 $g\,c$; 极限逐项. 合法, 对一切界满足 `PH`.

```agda
ks : HB S⊥ → K XS₁
ks c = kc c

gˢ : HB S⊥ → HB XS₁
gˢ hz = hz
gˢ (hs c) = hΩ (ks c) (λ _ → gˢ c)
gˢ (hl f) = hl (λ n → gˢ (f n))
gˢ (hΩ () _)

Dˢ : HB XS₁
Dˢ = hΩ κΩ gˢ

gˢ-mono : ∀ {w} {c c′ : HB S⊥} → c ⊲[ tt ] c′ → gˢ c ⊲[ w ] gˢ c′
gˢ-mono hself = hself
gˢ-mono {w} {c′ = hs c″} (hsuc p) = hLim {c = hz} (botBd XS₁ (ks c″) w) (gˢ-mono p)
gˢ-mono (hlim n p) = hlim n (gˢ-mono p)
gˢ-mono (hLim {κ = ()} _ _)

Lg-gˢ : ∀ c → LgB c → LgB (gˢ c)
Lg-gˢ hz _ = tt
Lg-gˢ (hs c) l = (λ _ _ _ _ → hself) , (λ _ _ → Lg-gˢ c l)
Lg-gˢ (hl f) (st , l) = (λ {w} n → gˢ-mono {w} (st {tt} n)) , (λ n → Lg-gˢ (f n) (l n))
Lg-gˢ (hΩ () _) _

Lg-Dˢ : LgB Dˢ
Lg-Dˢ = (λ lw e e′ p → gˢ-mono p) , (λ c lc → Lg-gˢ c lc)

ph-gˢ : ∀ c b → c ⊲[ tt ] b → PH b (gˢ c)
ph-gˢ hz b p = tt
ph-gˢ (hs c) b p = p , (λ _ _ → ph-gˢ c b (⊲ᴮ-tr (hsuc hself) p))
ph-gˢ (hl f) b p = λ n → ph-gˢ (f n) b (⊲ᴮ-tr (hlim n hself) p)
ph-gˢ (hΩ () _) b p

PH-Dˢ : ∀ B → PH B Dˢ
PH-Dˢ B = tt , (λ e a → ph-gˢ e (hs e) (hsuc hself))
```

`topX₁` (构造一路 `PathOut` 的闭项输入): 满足 `PH` (构造一路的 `PH-top`), 但**不合法**: 分支 $0$ 与分支 $1$ 在 `Lv X₁` 的不同分量里 (`NegTySupDiag.no-cross`), 而合法要分支 $0$ 是分支 $1$ 的第一位置. 闭项 `TX₁` 的证书 `LgB-TX₁` 来自 `Sh-Ψ`, 不看输入是否合法.

```agda
inj≢ : ¬ (_≡_ {A = ⊤ ⊎ HB S⊥} (inj₂ hz) (inj₂ (hs hz)))
inj≢ ()

¬LgB-topX₁ : ¬ LgB topX₁
¬LgB-topX₁ (mo , _) =
  no-cross (inj₂ hz) (inj₂ (hs hz)) (topΣ (hs hz)) (topΣ (hs (hs hz))) inj≢ tt
    (mo {wB (hs hz)} (lgwB (hs hz) tt) (hsuc hself) hself (hsuc hself))

top-summary : PH (hs hz) topX₁ × ¬ LgB topX₁ × LgB TX₁
top-summary = PH-top (hs hz) , ¬LgB-topX₁ , LgB-TX₁
```

**合法且带路径的地板 `top′` (构造, 边界).** 分支 $c$ 是 "一切 $y+1$ 字面在 $c$ 里的第 $y+1$ 层地板" 接起来: $g\,0=0$, $g\,(c+1)=g\,c\boxplus\iota_c\,\Omega_{c+1}$, $g\,(\lim f)=\lim g\circ f$ (`HtTowerU.θ` 的形状, 分支只提到严格更小的坐标). 合法 (`Lg-top′`), 对一切界满足 `PH` (`PH-top′`). 读法 (判断) 与 `topX₁` 同为 $\sup_c\Omega_{c+1}$ 一类; 本篇没有值的定理.

```agda
gt : HB S⊥ → HB XS₁
gt hz = hz
gt (hs c) = gt c ⊞ ι (inj₂ c) (topΣ (hs c))
gt (hl f) = hl (λ n → gt (f n))
gt (hΩ () _)

top′ : HB XS₁
top′ = hΩ κΩ gt

gt-mono : ∀ {w} {c c′ : HB S⊥} → c ⊲[ tt ] c′ → gt c ⊲[ w ] gt c′
gt-mono hself = hself
gt-mono {c′ = hs c″} (hsuc p) = ⊲ᴮ-tr (gt-mono p) (⊞-fst (gt c″) _)
gt-mono (hlim n p) = hlim n (gt-mono p)
gt-mono (hLim {κ = ()} _ _)

Lg-gt : ∀ c → LgB c → LgB (gt c)
Lg-gt hz _ = tt
Lg-gt (hs c) l = Lg-⊞ (gt c) _ (Lg-gt c l) (Lg-ι (inj₂ c) (topΣ (hs c)) (Lg-topΣ (hs c)))
Lg-gt (hl f) (st , l) = (λ {w} n → gt-mono {w} (st {tt} n)) , (λ n → Lg-gt (f n) (l n))
Lg-gt (hΩ () _) _

Lg-top′ : LgB top′
Lg-top′ = (λ lw e e′ p → gt-mono p) , (λ c lc → Lg-gt c lc)

PH-ιb : ∀ {b} y (h : HB (LC (hs y))) → hs y ⊲[ tt ] b → PH b (ι (inj₂ y) h)
PH-ιb y hz p = tt
PH-ιb y (hs h) p = PH-ιb y h p
PH-ιb y (hl f) p = λ n → PH-ιb y (f n) p
PH-ιb y (hΩ κ g) p = p , (λ e a → PH-ιb y (g e) p)

noΩ-ι : ∀ y (h : HB (LC (hs y))) → NoΩ₁ (ι (inj₂ y) h)
noΩ-ι y hz = tt
noΩ-ι y (hs h) = noΩ-ι y h
noΩ-ι y (hl f) = λ n → noΩ-ι y (f n)
noΩ-ι y (hΩ κ g) = λ e → noΩ-ι y (g e)

PH-⊞ : ∀ {b} a x → PH b a → NoΩ₁ x → PH b x → PH b (a ⊞ x)
PH-⊞ a hz pa nx px = pa
PH-⊞ a (hs x) pa nx px = PH-⊞ a x pa nx px
PH-⊞ a (hl f) pa nx px = λ n → PH-⊞ a (f n) pa (nx n) (px n)
PH-⊞ a (hΩ (inj₁ _ , inj₁ ()) g) pa nx px
PH-⊞ a (hΩ (inj₁ _ , inj₂ _) g) pa () px
PH-⊞ a (hΩ (inj₂ y , κ) g) pa nx (yb , k) = yb , (λ e t → PH-⊞ a (g e) pa (nx e) (k e t))

ph-gt : ∀ c b → c ⊲[ tt ] b → PH b (gt c)
ph-gt hz b p = tt
ph-gt (hs c) b p = PH-⊞ (gt c) (ι (inj₂ c) (topΣ (hs c))) (ph-gt c b (⊲ᴮ-tr (hsuc hself) p)) (noΩ-ι c (topΣ (hs c))) (PH-ιb c (topΣ (hs c)) p)
ph-gt (hl f) b p = λ n → ph-gt (f n) b (⊲ᴮ-tr (hlim n hself) p)
ph-gt (hΩ () _) b p

PH-top′ : ∀ B → PH B top′
PH-top′ B = tt , (λ e a → ph-gt e (hs e) (hsuc hself))
```

## §4 正面: 每次决定的两个下标字面三歧

```agda
open NI.Tri IX₁ using (Tri; ev-tg→tri)

tri-IX₁ : ∀ B t → LgW₁ B → t ⊲[ tt ] B → ∀ κ → PathOutIf.Ev IX₁ B κ → Tri (PathOutIf.lvX IX₁ κ) t
tri-IX₁ = ev-tg→tri

-- 前提实例: 种类 (inj₂ lim od , inj₂ tt) 的层号是 lim od; 目标 lim ev; 没有合法世界同时带两者的证据
κod : K XS₁
κod = inj₂ (hl odᴴ) , inj₂ tt

no-world-IX₁ : ∀ B → LgW₁ B → hl evᴴ ⊲[ tt ] B → ¬ PathOutIf.Ev IX₁ B κod
no-world-IX₁ = NI.Tri.no-world IX₁ (hl evᴴ) κod NI.¬tri-od-ev
```

## §5 盲: 证书不看 `shift`

`IX₁c = NegPathOutIf.constShiftOf IX₁`: `shift` 换成常值 (Ω₁ 种类的分支一律从坐标 $B\boxplus\mathrm{leg}\,0=B$ 取), `dec`, `correct` 不变. 同一闭项公式 `TX₁c` 也有 `LgB` 证书. 所以 `LgB-TX₁` 与 `correct₁` 都不说明 `shift` 保住了留下/坍缩的结点的分支; 是否保值要另外的定理 (本篇没有). `TX₁c ≢ TX₁` 本篇未证 (要展开两个链点, 判断它们不同).

```agda
IX₁c : PathOutIf
IX₁c = NI.constShiftOf IX₁

-- PH 对 IX₁c 是另一个模块实例里的递归定义, 照 PathOut.PH-ι, PH-top 重写一遍
PHc-ι : ∀ y (h : HB (LC (hs y))) → PF.PH IX₁c (hs y) (ι (inj₂ y) h)
PHc-ι y hz = tt
PHc-ι y (hs h) = PHc-ι y h
PHc-ι y (hl f) = λ n → PHc-ι y (f n)
PHc-ι y (hΩ κ g) = hself , (λ e a → PHc-ι y (g e))

PHc-top : ∀ B → PF.PH IX₁c B topX₁
PHc-top B = tt , (λ y a → PHc-ι y (topΣ (hs y)))

TX₁c : HB S⊥
TX₁c = PF.Ψ IX₁c W₀ lW₀ hz (z⊲ᴮ W₀) hz topX₁ (PHc-top W₀)

LgB-TX₁c : LgB TX₁c
LgB-TX₁c = sh→lgB₁ TX₁c (PF.Sh-Ψ IX₁c W₀ lW₀ hz (z⊲ᴮ W₀) hz topX₁ (PHc-top W₀))

shift-c : ∀ (c : HB S⊥) → PathOutIf.shift IX₁c W₀ κΩ c ≡ W₀
shift-c c = refl
```

## 结论 (按档)

- **[定理]** `NoΩ₁`, **`ph-ment⁰`**, `ment⊲⁰`, `cst`, `Lg-cst`, `unsucE`, `intoL`, `no-cst`, **`ph-lg-own`**; `noΩ-gᶜ`, **`¬PH-Dᶜ`**; **`PH-D`**, `noΩ-dep`, **`¬LgB-D`**; `gˢ`, `Dˢ`, `gˢ-mono`, `Lg-gˢ`, **`Lg-Dˢ`**, `ph-gˢ`, **`PH-Dˢ`** (构造); `inj≢`, **`¬LgB-topX₁`**, `top-summary`; `gt`, `top′`, `gt-mono`, `Lg-gt`, **`Lg-top′`**, `PH-ιb`, `noΩ-ι`, `PH-⊞`, `ph-gt`, **`PH-top′`** (构造); `tri-IX₁` (正面, 由构造一路的 `correct₁`); `κod`, **`no-world-IX₁`**; `IX₁c`, `PHc-ι`, `PHc-top`, `TX₁c`, **`LgB-TX₁c`**, `shift-c` (盲).
- **[判断]** `Dᶜ` 读 $\sup_c\Omega_{c+1}$; 文件头 "对纲领与目标" 一段; 闭项用哪一类输入, 待构造一路的闭项文件.
