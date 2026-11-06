# 头按自己的级读回, 否定一路 (一): 级层只有站层; 规范读法下第 $n\ge3$ 站的头没有自己的级层

> 不含记号. 入口 [NegLeanLv](NegLeanLv.lagda.md). 本篇**不依赖**构造一路的接口 `LeanLvIf` (接口定稿之前写的部分), 只导入 [LeanTBase](LeanTBase.lagda.md), [LeanTLv](LeanTLv.lagda.md), [LeanFbIf](LeanFbIf.lagda.md), [LeanFbSt](LeanFbSt.lagda.md) (都不改). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** 作者本轮选定 "LeanFb: 头按自己的级读回": 第 $n$ 站的头 `νS n` 的坐标是 `HB (Lv (st n))`; 按自己的级读回, 要一个级层 $\ell$ (接口 `LvRd` 的 `ℓ`, 对一切世界是 $\Lambda_F$ 的字面第一位置), 层 $\ell$ 的子层与 `Lv (st n)` 的种类对应. 本篇回答三件事:
>
> 1. **级层只能是哪些 (§2, 定理 `lvl-cases`, `lvrd-cases`).** 若 $\ell$ 在基世界里是 $\Lambda_F$ 的第一位置, 则 $\ell$ 是 $0$, 某个站层 $S_m=$ `up (1 ⊞ tws m)`, 或 $\Lambda_F$ 本身. 原因: 基世界里每个站的头的界是 $0$, 所以沿 $\Omega$-结点只能走坐标 $0$ 的分支, 而站层在坐标 $0$ 处的分支恰好是前一个站层 (定义相等). 所以接口 `LvRd` 的一切实例 (对 `SLs`, `ΛF`) 的级层都在这个可数的表里.
> 2. **规范读法下, 哪些头有自己的级层 (§3).** "子层与种类对应" 取与 `ofHB` 同一个配方的读法 `ofL : HB (step SLs) → LH` (站 $m$ 的头的 $\Omega$-结点读成 `lΩ (st m)`, 站里的旧种类沿 `node` 下降; 层号读成级, 种类结构是 `Lv (ofL ℓ)`). 头 $n$ 的 "自己的级层" 指 `ofL ℓ` 与 `st n` 外延相等 (`_≈_`, 对 $\Omega$-分支逐点; `≡` 蕴含 `≈`, `≡→≈`).
>    - **正面 (定理).** `own0`: `ofL 0 ≡ st 0`; `own1`: `ofL S₀ ≡ st 1`; **`own2`**: `ofL S₁ ≈ st 2`. 头 $0,1,2$ 各有自己的级层 ($0$, $S_0$, $S_1$).
>    - **否定 (定理) `no-own`.** 对一切 $n$, 一切在基世界里是 $\Lambda_F$ 第一位置的 $\ell$: `¬ (ofL ℓ ≈ st (3 + n))`. 推论 **`no-own-rd`**: 接口 `LvRd SLs ΛF Q` 的任一实例的级层, 规范读法都不是 `st (3 + n)`. 所以头 $n\ge3$ 在 $\Lambda_F$ 的级层表里**没有**规范意义下自己的级层. 证据只用到一处可判定的构造子差: `st (3+n)` 在坐标 $0$ 的分支是 `st (2+n)` (一个 `lΩ`), 而唯一首项对得上的候选 $S_1$ 在坐标 $0$ 的分支是 `ls lz`.
>    - **太大的一侧 (定理) `big-half`, `big-Λ`.** 对一切 $n$ 与一切 $m>n$: `Lv (ofL Sₘ)` 有一个种类的坐标就是 `HB (Lv (st n))` (`kAt`), 所以 `HB (Lv (ofL Sₘ))` 不是 `HB (Lv (st n))` 的收缩 (`no-retract`). 读法: 从站层 $S_m$ ($m>n$) 或 $\Lambda_F$ 的规范读回类型无损地读进头 $n$ 的坐标, 撞 Burali-Forti (`no-retract` 的形状).
> 3. **$\Omega$-头的级是否逼出有损 (§4).** `lvK-not-self` (定理, 对一切 $k$): `Lv k` 没有种类的级是 $k$ 自己 (同 `NegKindLvLev.lv-not-self`). 但对头 2 的级 `st 2 = lΩ lz g₂` (一个 $\Omega$-头的级), 过分支 $c$ 的子层的结点有一个忠实的种类可读: `succK c` (坐标 $c+1$ 处的新种类), 坐标字面就是 `HB (Lv (g₂ c))` (**`succK-co`**, `refl`). 所以 "级是 $\Omega$-头" 本身不逼出读回有损 (这里的反例是头 2); 与 `NegKindLvRdW.wr-Ω-drop` (写入有损) 不冲突, 那是写的一侧.
>
> 另: `st-not-ls2` (定理): 没有站的级是 `ls (ls lz)`; `st3-branch` (定理, `refl`): `st 3` 在坐标 $2$ 处的分支是 `lΩ (ls (ls lz)) _`. 所以一个按 `st 3` 的样子搭的层, 在那个位置上的 $\Omega$-结点不能是站的头 (`no-station-at`), 只能是站里的拷贝种类.
>
> **只否定什么.** `no-own` 只否定: 级层在 $\Lambda_F$ 的 (基世界) 第一位置里, 且 "子层与种类对应" 取规范读法 `ofL` 并要求与 `st n` 外延相等. **不否定**: 别的对应 (非规范的读法, 例如把子层的种类换成站里的拷贝种类); 改了 $\Lambda$ (例如在最高层里加上按 `tw n` 的样子搭的层); 级层依赖世界的读回 (接口 `LvRd` 的 `ℓ` 不依赖世界, 若新接口改了这一条, 本篇的 `lvrd-cases` 不适用); 头 $0,1,2$ (有正面实例). `big-half` 只否定 "从更高站层的规范读回类型到头的坐标的收缩". 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLeanLvPre where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanFbIf
open import OCF.Lean.LeanFbSt renaming (st to stL)
```

## §1 分支不能取回自己 (对 `LeanTBase` 的 `HB` 重写 `HtTowerNeg.no-retract`)

```agda
module _ {S : KS} where
  data _≺ᴮ_ : HB S → HB S → Set where
    ≺s : ∀ {x} → x ≺ᴮ hs x
    ≺l : ∀ {f} n → f n ≺ᴮ hl f
    ≺Ω : ∀ {κ g} c → g c ≺ᴮ hΩ κ g

  data Acc≺ (x : HB S) : Set where
    acc : (∀ {y} → y ≺ᴮ x → Acc≺ y) → Acc≺ x

  acc≺ : ∀ x → Acc≺ x
  acc≺ hz = acc (λ ())
  acc≺ (hs x) = acc (λ { ≺s → acc≺ x })
  acc≺ (hl f) = acc (λ { (≺l n) → acc≺ (f n) })
  acc≺ (hΩ κ g) = acc (λ { (≺Ω c) → acc≺ (g c) })

  irr≺ : ∀ {x} → Acc≺ x → ¬ (x ≺ᴮ x)
  irr≺ (acc f) p = irr≺ (f p) p

  no-self : ∀ κ (d : E S κ → HB S) c → ¬ (d c ≡ hΩ κ d)
  no-self κ d c eq = irr≺ (acc≺ (hΩ κ d)) (subst (λ z → z ≺ᴮ hΩ κ d) eq (≺Ω c))

  -- 没有种类的坐标里装着全部高度的收缩
  no-retract : ∀ κ (e : HB S → E S κ) (d : E S κ → HB S) → ¬ (∀ x → d (e x) ≡ x)
  no-retract κ e d sec = no-self κ d (e (hΩ κ d)) (sec (hΩ κ d))

subst-sr : ∀ {X Y : Set} (e : X ≡ Y) (y : Y) → subst (λ Z → Z) e (subst (λ Z → Z) (sym e) y) ≡ y
subst-sr refl y = refl

-- 坐标类型等于 X 时, HB S 不是 X 的收缩
no-desc-at : ∀ {S : KS} (κ : K S) {X : Set} → E S κ ≡ X → (d : HB S → X) (u : X → HB S) → ¬ (∀ x → u (d x) ≡ x)
no-desc-at {S} κ eq d u sec =
  no-retract κ (λ x → subst (λ Z → Z) (sym eq) (d x)) (λ e → u (subst (λ Z → Z) eq e))
    (λ x → trans (cong u (subst-sr eq (d x))) (sec x))
```

**种类的级 (`LeanTLv` 的层号上).** `lvK k κ`: 种类 $\kappa$ 的坐标是 `HB (Lv (lvK k κ))` (`coord`, 每一支 `refl`). `lvK-not-self`: 没有种类的级是 $k$ 自己.

```agda
lvK : (k : LH) → K (Lv k) → LH
lvK lz (() , _)
lvK (ls x) (inj₁ κ) = lvK x κ
lvK (ls x) (inj₂ _) = x
lvK (ll f) (n , κ) = lvK (f n) κ
lvK (lΩ k g) (inj₁ _ , inj₁ κ) = lvK k κ
lvK (lΩ k g) (inj₁ _ , inj₂ _) = k
lvK (lΩ k g) (inj₂ c , κ) = lvK (g c) κ

coord : ∀ k κ → E (Lv k) κ ≡ HB (Lv (lvK k κ))
coord lz (() , _)
coord (ls x) (inj₁ κ) = coord x κ
coord (ls x) (inj₂ _) = refl
coord (ll f) (n , κ) = coord (f n) κ
coord (lΩ k g) (inj₁ _ , inj₁ κ) = coord k κ
coord (lΩ k g) (inj₁ _ , inj₂ _) = refl
coord (lΩ k g) (inj₂ c , κ) = coord (g c) κ

lvK-not-self : ∀ k κ → ¬ (lvK k κ ≡ k)
lvK-not-self k κ eq = no-desc-at κ (trans (coord k κ) (cong (λ x → HB (Lv x)) eq)) (λ x → x) (λ x → x) (λ x → refl)
```

## §2 级层只能是 $0$, 站层, 或 $\Lambda_F$

站层 $S_m$ = `up (1 ⊞ tws m)` (= `LeanFbSt.stage-fst` 里的层). $S_{m+1}$ 的头是 `inj₁ (νS m)`, 在坐标 $0$ 处的分支**定义相等**于 $S_m$.

```agda
L₀ : KS
L₀ = step SLs

Sg : ℕ → HB L₀
Sg m = up (hs hz ⊞ tws m)

ΛF-hl : ΛF ≡ hl Sg
ΛF-hl = refl

Sg-branch0 : ∀ m → Σ (HB (Lv (stL m)) → HB L₀) (λ g → (Sg (suc m) ≡ hΩ (inj₁ (νS m)) g) × (g hz ≡ Sg m))
Sg-branch0 m = _ , refl , refl

⊲hz : ∀ {S : KS} {x : HB S} {w} → x ⊲[ w ] hz → x ≡ hz
⊲hz hself = refl

stage-down : ∀ m {x} → x ⊲[ w₀ L₀ ] Sg m → (x ≡ hz) ⊎ Σ ℕ (λ k → x ≡ Sg k)
stage-down zero hself = inj₂ (zero , refl)
stage-down zero (hsuc p) = inj₁ (⊲hz p)
stage-down (suc j) hself = inj₂ (suc j , refl)
stage-down (suc j) {x} (hLim {c = c} e p) =
  stage-down j (subst (λ c′ → x ⊲[ w₀ L₀ ] up (hs hz ⊞ (tws j ⊞ ιS j (up c′)))) (⊲hz e) p)

lvl-cases : ∀ {ℓ} → ℓ ⊲[ w₀ L₀ ] ΛF → (ℓ ≡ ΛF) ⊎ ((ℓ ≡ hz) ⊎ Σ ℕ (λ m → ℓ ≡ Sg m))
lvl-cases hself = inj₁ refl
lvl-cases (hlim n p) = inj₂ (stage-down n p)

-- 接口 LvRd 的一切实例: 级层在这个表里
lvrd-cases : ∀ {Q} (R : LvRd SLs ΛF Q) → (LvRd.ℓ R ≡ ΛF) ⊎ ((LvRd.ℓ R ≡ hz) ⊎ Σ ℕ (λ m → LvRd.ℓ R ≡ Sg m))
lvrd-cases R = lvl-cases (LvRd.ℓ⊲ R {w₀ L₀})
```

**前提实例.** 表里的每一项都对一切世界是第一位置: `z⊲ᴮ ΛF`, `LeanFbSt.stage-fst m`, `hself`. 所以 `lvl-cases` 的结论是一个刻画, 不是空的上界.

```agda
lvl-inst : ∀ m {w} → Sg m ⊲[ w ] ΛF
lvl-inst m = stage-fst m
```

## §3 规范读法 `ofL`: 子层读成级

与 `LeanTLv.ofHB` 同一个配方: 站 $m$ 的头的 $\Omega$-结点读成 `lΩ (st m)`, 站里的旧种类经 `node` 下降到它的级; 第 0 层自己的新种类 (`ΛF` 里不出现) 读成 `lz`.

```agda
ofL : HB L₀ → LH
ofL hz = lz
ofL (hs h) = ls (ofL h)
ofL (hl f) = ll (λ n → ofL (f n))
ofL (hΩ (inj₁ (m , inj₂ _)) g) = lΩ (stL m) (λ c → ofL (g c))
ofL (hΩ (inj₁ (m , inj₁ κ)) g) = node (stL m) κ (λ c → ofL (g c))
ofL (hΩ (inj₂ _) g) = lz
```

**外延相等** `_≈_`: $\mathbb N$-分支逐项, $\Omega$-分支在首项相等之后逐点 (沿首项的相等搬运坐标). `≡→≈`.

```agda
infix 4 _≈_
_≈_ : LH → LH → Set
lz ≈ lz = ⊤
ls x ≈ ls y = x ≈ y
ll f ≈ ll g = ∀ n → f n ≈ g n
lΩ k g ≈ lΩ k′ g′ = Σ (k ≡ k′) (λ e → ∀ c → g c ≈ g′ (subst (λ x → HB (Lv x)) e c))
_ ≈ _ = ⊥

≈-refl : ∀ x → x ≈ x
≈-refl lz = tt
≈-refl (ls x) = ≈-refl x
≈-refl (ll f) = λ n → ≈-refl (f n)
≈-refl (lΩ k g) = refl , (λ c → ≈-refl (g c))

≡→≈ : ∀ {x y} → x ≡ y → x ≈ y
≡→≈ {x} refl = ≈-refl x
```

**正面: 头 $0, 1, 2$ 有自己的级层.**

```agda
own0 : ofL hz ≡ stL 0
own0 = refl

own1 : ofL (Sg 0) ≡ stL 1
own1 = refl

own2-br : ∀ (c : HB S⊥) → ofL (up (hs hz ⊞ (hz ⊞ ιS 0 (up c)))) ≈ ofHB (hs hz ⊞ ι {LH} {FL} lz (up c))
own2-br hz = tt
own2-br (hs c) = own2-br c
own2-br (hl f) = λ n → own2-br (f n)
own2-br (hΩ (() , _) g)

own2 : ofL (Sg 1) ≈ stL 2
own2 = refl , own2-br
```

**`st (2+n)` 的形状.** 首项是 `lz`, 坐标 $0$ 处的分支是 `st (1+n)`.

```agda
tw-shape : ∀ m → Σ (HB (Lv lz) → HB SL) (λ h → (tw (suc (suc m)) ≡ hΩ (νL lz) h) × (h hz ≡ tw (suc m)))
tw-shape zero = _ , refl , refl
tw-shape (suc m) = (λ c → Ω̂ (proj₁ (tw-shape m) c)) , cong Ω̂ (proj₁ (proj₂ (tw-shape m))) , cong Ω̂ (proj₂ (proj₂ (tw-shape m)))

st-shape : ∀ m → Σ (HB (Lv lz) → LH) (λ h → (stL (suc (suc m)) ≡ lΩ lz h) × (h hz ≡ stL (suc m)))
st-shape m = (λ c → ofHB (proj₁ (tw-shape m) c)) , cong ofHB (proj₁ (proj₂ (tw-shape m))) , cong ofHB (proj₂ (proj₂ (tw-shape m)))
```

**观测.** `tag`: 层号的头构造子; `fstT`: `lΩ` 的首项的头; `br0`: 首项为 `lz` 的 `lΩ` 在坐标 $0$ 处的分支的头.

```agda
data Tg : Set where
  tz ts tl tΩ tn : Tg

tag : LH → Tg
tag lz = tz
tag (ls _) = ts
tag (ll _) = tl
tag (lΩ _ _) = tΩ

st-suc-nz : ∀ j → ¬ (stL (suc j) ≡ lz)
st-suc-nz zero ()
st-suc-nz (suc j) e with trans (sym (proj₁ (proj₂ (st-shape j)))) e
... | ()

st-ssc-Ω : ∀ m → tag (stL (suc (suc m))) ≡ tΩ
st-ssc-Ω m = cong tag (proj₁ (proj₂ (st-shape m)))

subst-hz : ∀ {x y : LH} (e : x ≡ y) → subst (λ z → HB (Lv z)) e hz ≡ hz
subst-hz refl = refl

≈-tag : ∀ x y → x ≈ y → tag x ≡ tag y
≈-tag lz lz p = refl
≈-tag (ls x) (ls y) p = refl
≈-tag (ll f) (ll g) p = refl
≈-tag (lΩ k g) (lΩ k′ g′) p = refl
≈-tag lz (ls _) ()
≈-tag lz (ll _) ()
≈-tag lz (lΩ _ _) ()
≈-tag (ls _) lz ()
≈-tag (ls _) (ll _) ()
≈-tag (ls _) (lΩ _ _) ()
≈-tag (ll _) lz ()
≈-tag (ll _) (ls _) ()
≈-tag (ll _) (lΩ _ _) ()
≈-tag (lΩ _ _) lz ()
≈-tag (lΩ _ _) (ls _) ()
≈-tag (lΩ _ _) (ll _) ()

-- 沿 ≡ 搬 ≈ 的右边
≈-≡ : ∀ x {y z} → x ≈ y → y ≡ z → x ≈ z
≈-≡ x p refl = p
```

**否定 `no-own`.** 对一切 $n$, 表里的一切级层, 规范读法都不外延相等于 `st (3+n)`.

```agda
H3 : ℕ → HB (Lv lz) → LH
H3 n = proj₁ (st-shape (suc n))

to-shape : ∀ n x → x ≈ stL (suc (suc (suc n))) → x ≈ lΩ lz (H3 n)
to-shape n x p = ≈-≡ x p (proj₁ (proj₂ (st-shape (suc n))))

tag-Ω : ∀ n x → x ≈ stL (suc (suc (suc n))) → tag x ≡ tΩ
tag-Ω n x p = ≈-tag x (lΩ lz (H3 n)) (to-shape n x p)

no-own-S : ∀ n m → ¬ (ofL (Sg m) ≈ stL (suc (suc (suc n))))
no-own-S n zero p with tag-Ω n (ofL (Sg zero)) p
... | ()
no-own-S n (suc zero) p with to-shape n (ofL (Sg 1)) p
... | e , q = br-bad (trans (≈-tag (ls lz) (H3 n hz) (≈-≡ (ls lz) (q hz) (cong (H3 n) (subst-hz e))))
                             (cong tag (proj₂ (proj₂ (st-shape (suc n))))))
  where
  br-bad : ¬ (ts ≡ tag (stL (suc (suc n))))
  br-bad eq with trans eq (st-ssc-Ω n)
  ... | ()
no-own-S n (suc (suc j)) p with to-shape n (ofL (Sg (suc (suc j)))) p
... | e , q = st-suc-nz j e

no-own : ∀ n {ℓ} → ℓ ⊲[ w₀ L₀ ] ΛF → ¬ (ofL ℓ ≈ stL (suc (suc (suc n))))
no-own n p with lvl-cases p
... | inj₁ refl = λ q → case-ll (tag-Ω n (ofL ΛF) q)
  where
  case-ll : ¬ (tl ≡ tΩ)
  case-ll ()
... | inj₂ (inj₁ refl) = λ q → case-z (tag-Ω n lz q)
  where
  case-z : ¬ (tz ≡ tΩ)
  case-z ()
... | inj₂ (inj₂ (m , refl)) = no-own-S n m

no-own-rd : ∀ n {Q} (R : LvRd SLs ΛF Q) → ¬ (ofL (LvRd.ℓ R) ≈ stL (suc (suc (suc n))))
no-own-rd n R = no-own n (LvRd.ℓ⊲ R {w₀ L₀})

-- ≡ 是 ≈ 的特例
no-own-≡ : ∀ n {ℓ} → ℓ ⊲[ w₀ L₀ ] ΛF → ¬ (ofL ℓ ≡ stL (suc (suc (suc n))))
no-own-≡ n p e = no-own n p (≡→≈ e)
```

**太大的一侧 `big-half`.** $S_{m}$ ($m>n$) 的规范读法里有一个种类, 坐标字面就是头 $n$ 的坐标 `HB (Lv (st n))`: 在 $S_{n+1}$ 的头 (`lΩ (st n)` 的左分量的新种类), 再沿坐标 $0$ 的分支往上.

```agda
kAt : ∀ n k → K (Lv (ofL (Sg (suc (k + n)))))
kAt n zero = inj₁ tt , inj₂ tt
kAt n (suc k) = inj₂ hz , kAt n k

kAt-co : ∀ n k → E (Lv (ofL (Sg (suc (k + n))))) (kAt n k) ≡ HB (Lv (stL n))
kAt-co n zero = refl
kAt-co n (suc k) = kAt-co n k

big-half : ∀ n k (d : HB (Lv (ofL (Sg (suc (k + n))))) → HB (Lv (stL n))) (u : HB (Lv (stL n)) → HB (Lv (ofL (Sg (suc (k + n)))))) →
  ¬ (∀ x → u (d x) ≡ x)
big-half n k = no-desc-at (kAt n k) (kAt-co n k)

big-Λ : ∀ n (d : HB (Lv (ofL ΛF)) → HB (Lv (stL n))) (u : HB (Lv (stL n)) → HB (Lv (ofL ΛF))) → ¬ (∀ x → u (d x) ≡ x)
big-Λ n = no-desc-at {Lv (ofL ΛF)} (suc n , kAt n 0) (kAt-co n 0)
```

## §4 $\Omega$-头的级: 过直接前驱的结点有忠实的种类 (头 2)

`st 2 = lΩ lz g₂`, $g_2\,c$ = `ofHB (1 ⊞ c)`. 过站层 $S_1$ 的分支 $c$ 的结点, 读回要一个坐标为 `HB (Lv (g₂ c))` 的种类: `succK c` (分支 $c+1$ 处的新种类), 坐标字面相等.

```agda
g₂ : HB S⊥ → LH
g₂ c = ofHB (hs hz ⊞ ι {LH} {FL} lz (up c))

st2-shape : stL 2 ≡ lΩ lz g₂
st2-shape = refl

succK : HB S⊥ → K (Lv (stL 2))
succK c = inj₂ (hs c) , inj₂ tt

succK-co : ∀ c → E (Lv (stL 2)) (succK c) ≡ HB (Lv (g₂ c))
succK-co c = refl

succK-lv : ∀ c → lvK (stL 2) (succK c) ≡ g₂ c
succK-lv c = refl
```

**站不够: `st 3` 的一个分支的级不是站.**

```agda
st-not-ls2 : ∀ m → ¬ (stL m ≡ ls (ls lz))
st-not-ls2 zero ()
st-not-ls2 (suc zero) ()
st-not-ls2 (suc (suc j)) e with trans (sym (proj₁ (proj₂ (st-shape j)))) e
... | ()

br0 : LH → HB S⊥ → LH
br0 (lΩ lz g) c = g c
br0 _ c = lz

st3-branch : Σ (HB (Lv (ls (ls lz))) → LH) (λ h → br0 (stL 3) (hs (hs hz)) ≡ lΩ (ls (ls lz)) h)
st3-branch = _ , refl

-- 站的头的 Ω-结点在规范读法下不是 lΩ (ls (ls lz)) _
no-station-at : ∀ m (g : HB (Lv (stL m)) → HB L₀) h → ¬ (ofL (hΩ (inj₁ (νS m)) g) ≈ lΩ (ls (ls lz)) h)
no-station-at m g h (e , _) = st-not-ls2 m e
```

## §5 结论 (按档)

- **[定理, 刻画]** **`lvl-cases`**, **`lvrd-cases`**: 在基世界里是 $\Lambda_F$ 第一位置的层只有 $0$, 站层 $S_m$, $\Lambda_F$; 接口 `LvRd SLs ΛF Q` 的一切实例的级层都在其中. 前提实例 `lvl-inst` (表里每一项对一切世界是第一位置).
- **[定理, 正面]** `own0`, `own1` (`≡`), **`own2`** (`≈`): 头 $0,1,2$ 在规范读法下各有自己的级层 ($0$, $S_0$, $S_1$).
- **[定理, 否定]** **`no-own`**, `no-own-rd`, `no-own-≡`: 对一切 $n$, 头 $3+n$ 在这张表里没有规范读法下外延相等的级层. **`big-half`**, `big-Λ`: 从 $S_{k+n+1}$ 或 $\Lambda_F$ 的规范读回类型到头 $n$ 的坐标没有收缩.
- **[定理]** `lvK-not-self` (没有种类的级是自己); `succK-co`, `succK-lv` (头 2 的 $\Omega$-头的级, 过分支 $c$ 有忠实的种类); `st-not-ls2`, `st3-branch`, `no-station-at`.
- **[判断]** (i) "子层与种类对应" 取 `ofL` 是我们的选择: 它与 `ofHB`, `KindLvRd` 的字面对应同一个配方, 头 $0,1$ 的现有读回 (`R0`, `rdX newAK`) 都符合它 (`own0`, `own1` 加 `LeanFbRd` 的级层 $0$, $1$). 构造一路若取别的对应, `no-own` 不适用. (ii) 由 `st3-branch` 与 `no-station-at`, 要让头 $3$ 有规范意义下自己的级层, 层里在对应 `ls (ls lz)` 的位置要用站里的拷贝种类作 $\Omega$-结点的头, 而 $\Lambda_F$ 里没有这样的层 (`no-own`); 这样的层能否加进 $\Lambda$ 而保持合法, 未研究.
