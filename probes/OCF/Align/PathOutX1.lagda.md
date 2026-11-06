# 路径记在折叠输出上: 层号 $X_1$ = `lΩ lz (λ c → ls (ofC c))` 的实例

> 不含记号. 入口 [PathOut](PathOut.lagda.md), 接口 [PathOutIf](PathOutIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 层号 $X_1$ 就是 [Fab4LOm](Fab4LOm.lagda.md) 的 `X₁` (分支依赖坐标, `exact→Sep` 说裸坐标上不能精确决定). 种类结构 `XS = Lv X₁`: 一个 "$\Omega_1$ 种类" `(inj₁ tt , inj₂ tt)` (坐标是第 0 层的值), 与对每个坐标 $y$ 的 "第 $y+1$ 层的种类" `(inj₂ y , κ)` (即 `Lv (ls (ofC y))` 的种类).
>
> - **世界** 是一个第 0 层的值 $B$ (界), 合法: `LgB B` 且 $1\lhd B$.
> - **目标** $t\lhd B$; **种类** `(inj₂ y , κ)` 的证据 $y+1\lhd B$ (坐标严格在界之下); $\Omega_1$ 种类无证据. 两个证据同向 (都在 $B$ 之下), 所以界变大时证据仍成立 (判断: 本路没有用到这条单调, 只在接手清单里用).
> - **带路径的回灌**: $\Omega_1$ 种类的分支坐标 $c\mapsto B\boxplus\mathrm{leg}\,c$, `leg` 把一棵第 0 层的树改成形状合法的树 (ℕ-极限取部分和; **这是累加**, 代价见入口文末). 进入的坐标 $y$ 字面在界之上 (`⊞-fst`) 且合法 (`Lg-⊞`); 进入后世界换成 $y+1$, 于是分支里坐标为 $y$ 的种类有证据 $y+1\lhd y+1$. 指标种类的分支不换世界.
> - **决定.** 种类 `(inj₂ y , κ)`: 种类的位置 ($\lhd y+1$) 与目标都在 $B$ 之下, **公共上界是世界的界 $B$**, 用 `cmpB` 比较后交给可数层号的 `TySupC.pick`. $\Omega_1$ 种类 (层号 $0$): 位置 $1\lhd B$, 公共上界同是 $B$.
> - **正确** (`correct₁`, 定理): 由 `cmpB` 的结果逐情形.
>
> **对 Fab4LOm 的回应.** `exact→Sep` 否定的是 "对一切裸坐标 $c$ 精确决定". 本实例只对带证据 ($y+1\lhd B$) 的种类决定; 裸坐标从不进入决定: 折叠进入 $\Omega_1$ 结点的分支时坐标由折叠自己造 ($B\boxplus\mathrm{leg}\,c$), 输入高度上的证据由 `PathOutFold.PH` 带着. 留下的 $\Omega_1$ 结点在输出里对一切坐标 $c$ 有分支, 但分支取的是输入在 $B\boxplus\mathrm{leg}\,c$ 处的分支 (NegPathOut 提醒的情形).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.PathOutX1 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥; LH; lz; ls; lΩ; Lv)
open import OCF.Align.TySupIf
open import OCF.Align.TySupC
open import OCF.Align.TySupSum using (topΣ; ICdΣ)
open import OCF.Align.PathOutIf
```

## §1 层号, 种类结构, 世界

```agda
X₁ : LH
X₁ = lΩ lz (λ c → ls (ofC c))

XS₁ : KS
XS₁ = Lv X₁

-- Ω₁ 种类
κΩ : K XS₁
κΩ = inj₁ tt , inj₂ tt

one : Cd
one = hs hz

LgW₁ : Cd → Set
LgW₁ B = LgB B × (one ⊲[ tt ] B)

Ev₁ : Cd → K XS₁ → Set
Ev₁ B (inj₁ _ , inj₁ ())
Ev₁ B (inj₁ _ , inj₂ _) = ⊤
Ev₁ B (inj₂ y , κ) = hs y ⊲[ tt ] B

Adm₁ : (B : Cd) (κ : K XS₁) → E XS₁ κ → Set
Adm₁ B (inj₁ _ , inj₁ ())
Adm₁ B (inj₁ _ , inj₂ _) y = (B ⊲[ tt ] y) × LgB y
Adm₁ B (inj₂ y , κ) e = ⊤

nxt₁ : (B : Cd) (κ : K XS₁) → Ev₁ B κ → (e : E XS₁ κ) → Adm₁ B κ e → Cd
nxt₁ B (inj₁ _ , inj₁ ())
nxt₁ B (inj₁ _ , inj₂ _) _ y _ = hs y
nxt₁ B (inj₂ y , κ) _ _ _ = B

lg-nxt₁ : ∀ {B κ} (ev : Ev₁ B κ) e (a : Adm₁ B κ e) → LgW₁ B → LgW₁ (nxt₁ B κ ev e a)
lg-nxt₁ {κ = inj₁ _ , inj₁ ()}
lg-nxt₁ {κ = inj₁ _ , inj₂ _} ev y (By , ly) (lB , oB) = ly , hsuc (⊲ᴮ-tr oB By)
lg-nxt₁ {κ = inj₂ y , κ} yB e a lW = lW

tg-nxt₁ : ∀ {B κ t} (ev : Ev₁ B κ) e (a : Adm₁ B κ e) → t ⊲[ tt ] B → t ⊲[ tt ] nxt₁ B κ ev e a
tg-nxt₁ {κ = inj₁ _ , inj₁ ()}
tg-nxt₁ {κ = inj₁ _ , inj₂ _} ev y (By , ly) pt = hsuc (⊲ᴮ-tr pt By)
tg-nxt₁ {κ = inj₂ y , κ} yB e a pt = pt
```

## §2 带路径的回灌

`leg`: ℕ-极限取部分和, 其余逐构造子. 形状合法 (`Lg-leg`, 对一切输入).

```agda
Σ₀ : (ℕ → Cd) → ℕ → Cd
Σ₀ f zero = f 0
Σ₀ f (suc n) = Σ₀ f n ⊞ f (suc n)

leg : Cd → Cd
leg hz = hz
leg (hs x) = hs (leg x)
leg (hl f) = hl (Σ₀ (λ n → leg (f n)))
leg (hΩ () _)

Lg-leg : ∀ x → LgB (leg x)
Lg-Σ₀ : ∀ f n → LgB (Σ₀ (λ m → leg (f m)) n)
Lg-leg hz = tt
Lg-leg (hs x) = Lg-leg x
Lg-leg (hl f) = (λ n → ⊞-fst (Σ₀ (λ m → leg (f m)) n) (leg (f (suc n)))) , Lg-Σ₀ f
Lg-leg (hΩ () _)
Lg-Σ₀ f zero = Lg-leg (f 0)
Lg-Σ₀ f (suc n) = Lg-⊞ _ (leg (f (suc n))) (Lg-Σ₀ f n) (Lg-leg (f (suc n)))

shift₁ : (B : Cd) (κ : K XS₁) → E XS₁ κ → E XS₁ κ
shift₁ B (inj₁ _ , inj₁ ())
shift₁ B (inj₁ _ , inj₂ _) c = B ⊞ leg c
shift₁ B (inj₂ y , κ) e = e

adm-shift₁ : ∀ {B} κ e → LgW₁ B → Adm₁ B κ (shift₁ B κ e)
adm-shift₁ (inj₁ _ , inj₁ ())
adm-shift₁ {B} (inj₁ _ , inj₂ _) c (lB , oB) = ⊞-fst B (leg c) , Lg-⊞ B (leg c) lB (Lg-leg c)
adm-shift₁ (inj₂ y , κ) e lW = tt
```

## §3 决定

种类的层号: $\Omega_1$ 种类是 $0$, `(inj₂ y , κ)` 是 `lvC (hs y) κ`.

```agda
lvX₁ : K XS₁ → Cd
lvX₁ (inj₁ _ , inj₁ ())
lvX₁ (inj₁ _ , inj₂ _) = hz
lvX₁ (inj₂ y , κ) = lvC (hs y) κ

Tg₁ : Cd → Cd → Set
Tg₁ B t = t ⊲[ tt ] B

DP : (B t : Cd) (κ : K XS₁) → Ev₁ B κ → Set
DP B t κ ev = DcP LC _⊑ᶜ_ LgB XS₁ (λ i → ∀ e a → Tg₁ (nxt₁ B κ ev e a) i) t κ

unsuc : ∀ {i y : Cd} → hs i ⊲[ tt ] hs y → i ⊲[ tt ] y
unsuc hself = hself
unsuc (hsuc p) = ⊲ᴮ-tr (hsuc hself) p
```

$\Omega_1$ 种类: `cmpB` 比较位置 $1$ 与目标 $t$ (公共上界 $B+1$). $1\lhd t$: 留 (沿路径嵌进 `LC t`); $t=1$: 留 (`LC 1` 的新种类); $t=0$: 同层, 读回恒等.

```agda
pickΩ : ∀ {B t} (ev : Ev₁ B κΩ) → (t ⊲[ tt ] one) ⊎ (one ⊲[ tt ] t) → DP B t κΩ ev
pickΩ ev (inj₂ q) = keep (along q) (frA q)
pickΩ ev (inj₁ hself) = keep (inj₂ tt) (λ c → c)
pickΩ ev (inj₁ (hsuc hself)) = same (λ c → c)
```

种类 `(inj₂ y , κ)`: 种类的位置 `posC (hs y) κ` 经 $y+1\lhd B+1$ 搬到 $B+1$ 之下, 与目标 $t\lhd B+1$ 用 `cmpB` 比较 (公共上界 $B+1$, `LgB B`), 结果交给 `TySupC.pick`, 再原样搬过来; "在上" 的新目标 $i$ 由 $i+1\lhd y+1$ 得 $i\lhd y\lhd B$, 即世界 (不变) 里的目标证据.

```agda
conv : ∀ {B t y κ} → LgB B → (ev : Ev₁ B (inj₂ y , κ)) → Dc LC _⊏ᶜ_ _⊑ᶜ_ (hs y) t κ → DP B t (inj₂ y , κ) ev
conv lB yB (keep κ′ fr) = keep κ′ fr
conv lB yB (same to) = same to
conv lB yB (above i pi q to) = above i q (lgC↓ᶜ pi (lgB⊲ yB tt lB)) (λ _ _ → ⊲ᴮ-tr (hsuc hself) (⊲ᴮ-tr pi yB)) to

-- 种类的位置搬到世界的界之下
posB : ∀ {B y} κ → hs y ⊲[ tt ] B → lvC (hs y) κ ⊏ᶜ B
posB {y = y} κ yB = ⊲ᴮ-tr (posC (hs y) κ) yB

dec₁ : ∀ B t → LgW₁ B → Tg₁ B t → (κ : K XS₁) → (ev : Ev₁ B κ) → DP B t κ ev
dec₁ B t lW pt (inj₁ _ , inj₁ ())
dec₁ B t (lB , oB) pt (inj₁ _ , inj₂ _) ev = pickΩ ev (cmpB oB pt tt lB)
dec₁ B t (lB , oB) pt (inj₂ y , κ) yB =
  conv lB yB (pick (toC (hs y) κ) (posC (hs y) κ) (cmpB (posB κ yB) pt tt lB))
```

**决定正确 (定理).** 逐情形; 种类 `(inj₂ y , κ)` 的情形与 `NegTySupC.ok-pick` 同 (这里对 `conv ∘ pick` 重写一遍, 不导入否定一路). 与 `decC` 的差别只在比较用的公共上界: `decC` 用种类所在的层号, 这里用世界的界 $B+1$.

```agda
okΩ : ∀ {B t} (ev : Ev₁ B κΩ) r → OkP _⊏ᶜ_ hz (pickΩ {B} {t} ev r)
okΩ ev (inj₂ q) = q
okΩ ev (inj₁ hself) = hself
okΩ ev (inj₁ (hsuc hself)) = refl

okI : ∀ {B t y κ i} (lB : LgB B) (ev : Ev₁ B (inj₂ y , κ)) (to : HB (LC i) → E (LC (hs y)) κ)
      (pi : i ⊏ᶜ hs y) r →
      OkP _⊏ᶜ_ i (conv {B} {t} {y} {κ} lB ev (pick to pi r))
okI lB ev to pi (inj₂ q) = q
okI lB ev to pi (inj₁ hself) = hself
okI lB ev to pi (inj₁ (hsuc hself)) = refl
okI lB ev to pi (inj₁ (hsuc (hsuc q))) = refl
okI lB ev to pi (inj₁ (hsuc (hlim n q))) = refl
okI lB ev to pi (inj₁ (hsuc (hLim {κ = ()} _ _)))

correct₁ : ∀ B t (lW : LgW₁ B) (pt : Tg₁ B t) κ (ev : Ev₁ B κ) → OkP _⊏ᶜ_ (lvX₁ κ) (dec₁ B t lW pt κ ev)
correct₁ B t lW pt (inj₁ _ , inj₁ ())
correct₁ B t (lB , oB) pt (inj₁ _ , inj₂ _) ev = okΩ ev (cmpB oB pt tt lB)
correct₁ B t (lB , oB) pt (inj₂ y , κ) yB =
  okI lB yB (toC (hs y) κ) (posC (hs y) κ) (cmpB (posB κ yB) pt tt lB)
```

## §4 实例

```agda
IX₁ : PathOutIf
IX₁ = record
  { R = ICdΣ ; XS = XS₁ ; Wo = Cd ; LgWo = LgW₁ ; Tg = Tg₁ ; Ev = Ev₁ ; Adm = Adm₁
  ; nxt = nxt₁ ; lg-nxt = lg-nxt₁ ; tg-nxt = tg-nxt₁ ; shift = shift₁ ; adm-shift = adm-shift₁
  ; lvX = lvX₁ ; dec = dec₁ ; correct = correct₁ }
```
