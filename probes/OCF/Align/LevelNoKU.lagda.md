# 唯一的定义域 $\mathbb U$, 无条件的证书

> 不含记号. 结论写在 [LevelNoK](LevelNoK.lagda.md). 块是 [LevelFixCore](LevelFixCore.lagda.md), 没有动. 下标仍然是 `el k c`, 守卫 `⊑̂` 仍然是索引数据类型, **与 [LevelFixU](LevelFixU.lagda.md) 不同的是接口不再要从 `el k c ⊑̂ el k a` 反演**: `≤̂`, `<̂` 对证据模式匹配, 两个证据的下界是同一个变量, 所以每个值只有一个父亲, 合一只解变量, 不碰回路.
>
> `Cf-toU : ∀ x → Legal x → Cfˢ (toU x)`: 无条件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LevelNoKU where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.LevelNoKLv using (Dom; module Lv)
open import OCF.Align.LevelNoKX using (XU)
open import OCF.Align.LevelFixCore
open import OCF.Align.LevelFixVal
```

## §1 $\mathbb U$

```agda
data Elt : Set where
  el : (j : LF) → Raw j → Elt

infix 4 _⊑̂_ _≤̂_ _<̂_
data _⊑̂_ : Elt → Elt → Set where
  gd : ∀ {k c η} → Gd k c η → el k c ⊑̂ el k η

-- 同一个下界之上的两个证据: 对两个证据同时模式匹配. 第二个证据的 k 由第一个解出, 这里没有 k = k.
_≤̂_ : ∀ {c a b} → c ⊑̂ a → c ⊑̂ b → Set
_≤̂_ {el k c} (gd {η = a} _) (gd {η = b} _) = Gd k a b

_<̂_ : ∀ {c a X} → c ⊑̂ a → c ⊑̂ X → Set
_<̂_ {el k c} (gd {η = a} _) (gd {η = X} _) = Dn k a X × Lgl k X

ŝ : Elt → Elt
ŝ (el j c) = el j (G.suc c)

bd̃ : ∀ {c a b X} (e₁ : c ⊑̂ a) (e₂ : c ⊑̂ b) (F : c ⊑̂ X) → e₁ <̂ F → e₂ <̂ F → (e₁ ≤̂ e₂) ⊎ (e₂ ≤̂ e₁)
bd̃ {el k c} (gd {η = a} _) (gd {η = b} _) (gd {η = X} _) (p , w) (q , _) with cmpD k X p q w
... | inj₁ s = inj₁ (s , lgl-dn k X q w)
... | inj₂ s = inj₂ (s , lgl-dn k X p w)

s̃F : ∀ {c η} → c ⊑̂ η → c ⊑̂ ŝ η
s̃F (gd (p , l)) = gd (inj₂ p , l)

self<̂ : ∀ {c η} (e : c ⊑̂ η) → e <̂ s̃F e
self<̂ (gd (p , l)) = inj₁ refl , l

𝕌 : Dom
𝕌 = record
  { D = Elt ; _⊑ᴰ_ = _⊑̂_ ; sD = ŝ
  ; _≤ᵉ_ = _≤̂_ ; _<ᵉ_ = _<̂_ ; bd = bd̃
  ; sF = s̃F ; self<ᵉ = self<̂
  }

open Lv 𝕌 using (LG; _≈_; _⊴_; WFˢ; Cfˢ; Cpᶠ; ≈→⊴; ⊴-suc-r; ⊴-lim-r; ⊴-fst; z≈; s≈; l≈; o≈; ≅ᴰ-refl; Fᵉ; fzᵉ; fkᵉ; _⊔ᵉ_; Allᵉ; Tp; tpr)
module U = Lv 𝕌
```

## §2 读来读去, 证书

`toUg`: 对证据模式匹配, 下标 `x` 是变量, 没有回路. `self-U`: 分支由结构递归给出, 没有两个证据要比, 所以不读 `irr`. `WF-U`: 上升的假设是 `e ≤̂ e′`, 三个证据的下界都是同一个变量.

```agda
toU : LF → LG
toUg : ∀ k c (g : (η : Raw k) → Gd k c η → LF) (x : Elt) → el k c ⊑̂ x → LG

toU zero = U.zero
toU (suc k) = U.suc (toU k)
toU (lim f) = U.lim (λ n → toU (f n))
toU (lc k c t g) = U.lc (el k c) (toU t) (toUg k c g)

toUg k c g (el .k η) (gd e) = toU (g η e)

fromU : LG → LF
fromU U.zero = zero
fromU (U.suc a) = suc (fromU a)
fromU (U.lim f) = lim (λ n → fromU (f n))
fromU (U.lc (el k c) t g) = lc k c (fromU t) (λ η e → fromU (g (el k η) (gd e)))

CP→Cpᶠ : ∀ {a b} → CP a b → Cpᶠ (toU a) (toU b)
CP→Cpᶠ self = U.self
CP→Cpᶠ (suc p) = U.suc (CP→Cpᶠ p)
CP→Cpᶠ (lim n p) = U.lim n (CP→Cpᶠ p)
CP→Cpᶠ (fst p) = U.fst (CP→Cpᶠ p)
```

**`cp⊴`:** 字面的第一位置推出带转移的 `⊴`, 同 [LevelFixU](LevelFixU.lagda.md).

```agda
cp⊴ : ∀ {a b} → b ≈ b → Cpᶠ a b → a ⊴ b
cp⊴ sf U.self = ≈→⊴ sf
cp⊴ (s≈ e) (U.suc p) = ⊴-suc-r (cp⊴ e p)
cp⊴ (l≈ h) (U.lim n p) = ⊴-lim-r n (cp⊴ (h n) p)
cp⊴ (o≈ d e h h⁻ hˡ hʳ) (U.fst p) = ⊴-fst (cp⊴ e p)

self-U : ∀ x → Legal x → toU x ≈ toU x
self-U zero w = z≈
self-U (suc k) w = s≈ (self-U k w)
self-U (lim f) (st , w) = l≈ (λ n → self-U (f n) (w n))
self-U (lc k c t g) (_ , _ , _ , _ , wt , wg) = o≈ (≅ᴰ-refl (el k c)) (self-U t wt) h h h h
  where
  h : ∀ (η : Elt) (e : el k c ⊑̂ η) → toUg k c g η e ≈ toUg k c g η e
  h (el .k a) (gd e) = self-U (g a e) (wg a e)

WF-U : ∀ x → Legal x → WFˢ (toU x)
WF-U zero w = tt
WF-U (suc k) w = WF-U k w
WF-U (lim f) (st , w) =
  (λ n → cp⊴ (self-U (f (suc n)) (w (suc n))) (CP→Cpᶠ (st n))) , (λ n → WF-U (f n) (w n))
WF-U (lc k c t g) (_ , tg , dir , irr , wt , wg) =
  tg′ , dir′ , WF-U t wt , wg′
  where
  tg′ : ∀ (η : Elt) (e : el k c ⊑̂ η) → toU t ⊴ toUg k c g η e
  tg′ (el .k η) (gd e) = cp⊴ (self-U (g η e) (wg η e)) (CP→Cpᶠ (tg η e))
  dir′ : ∀ (η : Elt) (e : el k c ⊑̂ η) (η′ : Elt) (e′ : el k c ⊑̂ η′) → e ≤̂ e′ → toUg k c g η e ⊴ toUg k c g η′ e′
  dir′ (el .k a) (gd e) (el .k a′) (gd e′) d = cp⊴ (self-U (g a′ e′) (wg a′ e′)) (CP→Cpᶠ (dir a e a′ e′ d))
  wg′ : ∀ (η : Elt) (e : el k c ⊑̂ η) → WFˢ (toUg k c g η e)
  wg′ (el .k η) (gd e) = WF-U (g η e) (wg η e)

Cf-toU : ∀ x → Legal x → Cfˢ (toU x)
Cf-toU x w = WF-U x w , self-U x w
```

**没有用 `irr`.** [LevelFixU](LevelFixU.lagda.md) 的 `self-U` 用 `irr` 把两个证据的分支认同; 这里 `≈` 不问两个证据, 所以 `irr` 在证书里没有被读 (`Legal` 里还有它, `Legal` 的形状不变). 同一个 $a$ 上两个证据的分支仍然相等, 只要 $a$ 是同一个 `Raw k` 的元 (`irr-U`): 这条不走 `Elt`, 所以不碰回路. 后面的证书要 "证据无关" 时用它.

```agda
irr-U : ∀ k c t g → Legal (lc k c t g) → ∀ a (e e′ : Gd k c a) → toUg k c g (el k a) (gd e) ≈ toUg k c g (el k a) (gd e′)
irr-U k c t g (_ , _ , _ , irr , _ , wg) a e e′ =
  subst (λ z → toU (g a e) ≈ toU z) (irr a e e′) (self-U (g a e) (wg a e))
```

**回路 (检查器实测, `text` 块是报错原文, 临时文件不进仓库).** 下面这个函数就是旧接口要的模式: `c ⊑̂ x`, `c ⊑̂ y`, `x <̂ X`, `y <̂ X` 四条索引关系连成一个圈, 其中 `<̂` 写成 [LevelFixU](LevelFixU.lagda.md) 那样的索引数据. 新接口把 `x`, `y`, `X` 都挂在同一个下界 `c` 上 (`bd̃`), 圈就断了.

```text
cyc : ∀ {c x y X} → c ⊑̂ x → c ⊑̂ y → x <̂ X → y <̂ X → Elt
cyc (gd _) (gd _) (lt _ _) (lt _ _) = el zero G.zero
error: [SplitError.UnificationStuck]
  el k a ≟ el k₁ η
  el k X ≟ el k₁ X₁
  Cannot eliminate reflexive equation k = k of type LF because K has been disabled.
```

## §3 求界: 字面上界之下取最大

地板的项都在同一个纤维里, 都是 `gd {η = K}`. 局部上界是分支的后继. 没有比较两个分支路径. 取最大的顺序与 [LevelFixU](LevelFixU.lagda.md) 的 `maxF` 逐字相同.

```agda
AllC : ∀ {k c₀ X} {F : el k c₀ ⊑̂ X} → Raw k → Fᵉ F → Set
AllC M fzᵉ = ⊤
AllC {k} M (fkᵉ (gd {η = K} _) _) = Cp k K M
AllC M (a ⊔ᵉ b) = AllC M a × AllC M b

record MaxR {k c₀ Y} {f : Gd k c₀ Y} (ψ : Fᵉ (gd f)) (m : Raw k) : Set where
  constructor mxr
  field
    M   : Raw k
    M<  : Dn k M Y
    m⊑  : Cp k m M
    all : AllC M ψ

allW : ∀ {k c₀ X} {F : el k c₀ ⊑̂ X} {a b} → Cp k a b → (ψ : Fᵉ F) → AllC a ψ → AllC b ψ
allW s fzᵉ _ = tt
allW {k} s (fkᵉ (gd _) _) x = Cp-tr k x s
allW s (a ⊔ᵉ b) (x , y) = allW s a x , allW s b y

maxF : ∀ {k c₀ Y} {f : Gd k c₀ Y} (ψ : Fᵉ (gd f)) → ∀ m → Dn k m Y → Lgl k Y → MaxR {f = f} ψ m
maxF {k} fzᵉ m q w = mxr m q (inj₁ refl) tt
maxF {k} {Y = Y} (fkᵉ (gd {η = a} _) (p , _)) m q w with cmpD k Y q p w
... | inj₁ c = mxr a p c (inj₁ refl)
... | inj₂ c = mxr m q (inj₁ refl) c
maxF {k} (a ⊔ᵉ b) m q w with maxF a m q w
... | mxr M₁ M₁< m₁ al₁ with maxF b M₁ M₁< w
...   | mxr M₂ M₂< m₂ al₂ = mxr M₂ M₂< (Cp-tr k m₁ m₂) (allW m₂ a al₁ , al₂)

allUp : ∀ {k c₀ X} {F : el k c₀ ⊑̂ X} {M x} (ψ : Fᵉ F) → AllC M ψ → Cp k M x → Lgl k x →
        (g : Gd k c₀ (G.suc x)) → Allᵉ (gd g) ψ
allUp fzᵉ a p l g = tt
allUp {k} (fkᵉ (gd _) _) a p l g = Cp-tr k a p , l
allUp (a ⊔ᵉ b) (x , y) p l g = allUp a x p l g , allUp b y p l g

boundU : ∀ {c X K₀} (F : c ⊑̂ X) (ψ : Fᵉ F) {e₀ : c ⊑̂ K₀} → e₀ <̂ F → Tp F ψ
boundU {el k c₀} (gd {η = Y} f) ψ {gd {η = m} e₀} (q , w) with maxF {f = f} ψ m q w
... | mxr M M< m⊑ all = tpr (el k M) gr′ (λ {η} d → ŝ η) (λ d → s̃F (gr′ d)) upEv′ (λ d → self<̂ (gr′ d))
  where
  cM : Cp k c₀ M
  cM = Cp-tr k (proj₁ e₀) m⊑
  gr′ : ∀ {η} → el k M ⊑̂ η → el k c₀ ⊑̂ η
  gr′ (gd (p , l)) = gd (Cp-tr k cM p , l)
  upEv′ : ∀ {η} (d : el k M ⊑̂ η) → Allᵉ (s̃F (gr′ d)) ψ
  upEv′ (gd (p , l)) = allUp ψ all p l _
```

## §4 实例

`ix`, `nodeC`, `nodeF` 与 [LevelFixU](LevelFixU.lagda.md) 字面相同.

```agda
natOfL : LF → ℕ
natOfL zero = 0
natOfL (suc a) = suc (natOfL a)
natOfL (lim _) = 0
natOfL (lc _ _ _ _) = 0

XF : XU
XF = record
  { 𝔻 = 𝕌
  ; bound = boundU
  ; ix = λ { (el j _) → natOfL j }
  ; nodeC = λ n → el (natF n) (cO (natF n))
  ; nodeF = λ n → toU (Ω̂ (natF n))
  ; emᵈ = λ { (el j c) → toU (up j c) }
  }
```
