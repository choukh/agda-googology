# 局部 UIP 的否定一路 (一): 局部 UIP 是函数类型的环平凡, 第一条引理本身就要环的搬运平凡

> 不含记号. 入口 [LocUipNeg](LocUipNeg.lagda.md). 对着接口 [LocUipIf](LocUipIf.lagda.md) ("接口定稿 2026-11-05 10:45", 变更记录: 无) 写, 导入它, 不另造接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延 (§4 的 `Funext` 只作前提, 条件).
>
> 构造一路 ([LocUipHed](LocUipHed.lagda.md)) 已证: 对一切合法世界的 `LocUIP` 等价于 `UIPᴸ` (合法高度上的 K), 并且它推出 `IncIrr` 与 `Lemma1`. 本篇补三件事, 都是定理:
>
> 1. **`UIPᴸ` 恰好是函数类型的环平凡** (`uipᴸ→funΩ`, `funΩ→uipᴸ`). `FunΩ`: 合法的 ℕ-极限 `hl f` 的分支函数 $f:\mathbb N\to H$ 上的环 $f\equiv f$ 都是 `refl`, 合法的 $\Omega$-极限 `hΩ tt g` 的分支 $g:A\to H$ 上的环同样. 理由: 构造子处的环由参数的环给出 (`qz`, `qs`, `ql`, `qΩ`, 对终点自由的 J), 零与后继处的环归约到更小的高度, 两种极限处的环就是函数类型的环. 构造一路的判断 "`hl f ≡ hl f` 与 `f ≡ f` 等价" 由此成为定理.
> 2. **卡住的那一步与环的搬运等价, 第一条引理本身推出环的搬运平凡** (`irr→fix`, `fix→irr`, `lemma1→fix₀`). `LoopFix`: 合法高度 $x$ 上的每个环 $\ell$ 沿族 $z\mapsto$ `HB (G₀ z)` 的搬运是恒等. `IncIrr` **当且仅当** `LoopFix`. 第一条引理 `Lemma1` (`raise₀ᴮ` 保 `Coh≡`) 夹在中间: `LoopFix → Fix⊞ → Lemma1 → LoopFix₀` (`LoopFix₀`: 环的搬运不动一切 `hz ⊞ δ`). 证明用一个合法世界: 界 $b=\Omega$-结点, 分支取常值 $x$, 界的单调数据 `mo` 在坐标 $0\lhd 1$ 处给出沿 $\ell$ 搬过的 `hself`; 坐标 $x$ 的两个证据经坐标 $0$ 与 $1$, 判定在第一个上给 `inj₁ refl`, 在第二个上给 `inj₁ ℓ` (`d₀`, `d₁`, 都是定理).
> 3. **都不可反驳** (`¬uipᴸ→¬fe`, `¬lemma1→¬fe`, `¬irr→¬fe`): 有函数外延时它们都成立, 所以在 `--without-K` 下构造 "同一界之下两个不相等的相等证明" 就是反驳函数外延.
>
> **判决 (第一条引理): 未证出, 也没有编译的否定; 不是禁忌.** 编译的部分是上面三条. 判断的部分: `FunΩ` 是外延性原理 (函数类型上相等证明的形状), `--safe --without-K` 下不加函数外延我判断证不出; 我没有反模型. 它不推出任何全知原理 (它被函数外延推出, 而函数外延与 `¬LPO` 相容), 所以**不是**壁垒定理意义上的禁忌. 第 2 条说明: 换一条充分条件 (不经 `LocUIP`) 去证 `Lemma1` 也躲不开同类的外延性内容, 因为 `Lemma1` 自己推出 `LoopFix₀`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LocUipNegLoop where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.AdmWIf
open import OCF.Align.AdmWCmp using (dec₀; dec₀-diag)
open import OCF.Align.AdmWCoh using (incD; dD; raise₀; raise₀ᴮ; UIPᴴ; wz)
open import OCF.Align.AdmWUip using (Funext; fe→uip)
open import OCF.Align.LocUipIf
open Slot
open RaiseIf
```

## §1 `UIPᴸ` 恰好是函数类型的环平凡

投影: 取后继的前驱, 取两种极限的分支函数. 不是构造子的形状给任意值 (不会用到).

```agda
pd : HB S₀ → HB S₀
pd (hs x) = x
pd x = x

unhl : HB S₀ → (ℕ → HB S₀)
unhl (hl f) = f
unhl _ = λ _ → hz

unΩ : HB S₀ → (A → HB S₀)
unΩ (hΩ _ g) = g
unΩ _ = λ _ → hz

cong-∘ : ∀ {X Y Z : Set} (g : Y → Z) (f : X → Y) {a b : X} (p : a ≡ b) → cong g (cong f p) ≡ cong (λ x → g (f x)) p
cong-∘ g f refl = refl

cong-id : ∀ {X : Set} {a b : X} (p : a ≡ b) → cong (λ x → x) p ≡ p
cong-id refl = refl
```

**构造子处的环由参数给出.** 对终点自由的 J: 族 `Q` 在终点是同一个构造子时说 "经投影再装回等于原来的路径", 否则平凡. 不用 K (起点固定, 终点是变量).

```agda
Qz : (z : HB S₀) → hz ≡ z → Set
Qz hz e = e ≡ refl
Qz _ e = ⊤

qz : ∀ z (e : hz ≡ z) → Qz z e
qz .hz refl = refl

Qs : ∀ a (z : HB S₀) → hs a ≡ z → Set
Qs a (hs z) e = cong hs (cong pd e) ≡ e
Qs a _ e = ⊤

qs : ∀ a z (e : hs a ≡ z) → Qs a z e
qs a .(hs a) refl = refl

Ql : ∀ f (z : HB S₀) → hl f ≡ z → Set
Ql f (hl g) e = cong hl (cong unhl e) ≡ e
Ql f _ e = ⊤

ql : ∀ f z (e : hl f ≡ z) → Ql f z e
ql f .(hl f) refl = refl

QΩ : ∀ g (z : HB S₀) → hΩ tt g ≡ z → Set
QΩ g (hΩ κ h) e = cong (hΩ tt) (cong unΩ e) ≡ e
QΩ g _ e = ⊤

qΩ : ∀ g z (e : hΩ tt g ≡ z) → QΩ g z e
qΩ g .(hΩ tt g) refl = refl
```

**`FunΩ`** 与等价.

```agda
FunΩ : Set
FunΩ = (∀ {f : ℕ → HB S₀} → LgB (hl f) → (λ′ : f ≡ f) → λ′ ≡ refl) ×
       (∀ {g : A → HB S₀} → LgB (hΩ tt g) → (λ′ : g ≡ g) → λ′ ≡ refl)

uipᴸ→funΩ : UIPᴸ → FunΩ
uipᴸ→funΩ u =
  (λ {f} lf (p : f ≡ f) → trans (sym (cong-id p)) (trans (sym (cong-∘ unhl hl p)) (cong (cong unhl) (u lf (cong hl p))))) ,
  (λ {g} lg (p : g ≡ g) → trans (sym (cong-id p)) (trans (sym (cong-∘ unΩ (hΩ tt) p)) (cong (cong unΩ) (u lg (cong (hΩ tt) p)))))

loopK : FunΩ → ∀ x → LgB x → (ℓ : x ≡ x) → ℓ ≡ refl
loopK F hz lx ℓ = qz hz ℓ
loopK F (hs x) lx ℓ = trans (sym (qs x (hs x) ℓ)) (cong (cong hs) (loopK F x lx (cong pd ℓ)))
loopK F (hl f) lx ℓ = trans (sym (ql f (hl f) ℓ)) (cong (cong hl) (proj₁ F lx (cong unhl ℓ)))
loopK F (hΩ κ g) lx ℓ = trans (sym (qΩ g (hΩ tt g) ℓ)) (cong (cong (hΩ tt)) (proj₂ F lx (cong unΩ ℓ)))

funΩ→uipᴸ : FunΩ → UIPᴸ
funΩ→uipᴸ F {x} lx = loopK F x lx
```

**与接口的 `LocUIP` 连起来** (构造一路 `LocUipHed` §2 的两行, 这里重写一遍以免依赖非接口文件).

```agda
uipᴸ→loc : UIPᴸ → ∀ w → LgO w → LocUIP w
uipᴸ→loc u w lo px py e refl = u (lgB⊲ px (proj₁ lo) (proj₂ lo)) e

loc→uipᴸ : (∀ w → LgO w → LocUIP w) → UIPᴸ
loc→uipᴸ u {x} lx e = u (azero , x) (tt , lx) hself hself e refl

loc⇔funΩ : ((∀ w → LgO w → LocUIP w) → FunΩ) × (FunΩ → ∀ w → LgO w → LocUIP w)
loc⇔funΩ = (λ u → uipᴸ→funΩ (loc→uipᴸ u)) , (λ F → uipᴸ→loc (funΩ→uipᴸ F))
```

例: ω 的分支 `fin` 上的环平凡, 是 `UIPᴸ` 的一个推论; 反过来它不够 (还要别的极限点), 这里只记这一个特例.

```agda
fin : ℕ → HB S₀
fin zero = hz
fin (suc n) = hs (fin n)

lg-fin : ∀ n → LgB (fin n)
lg-fin zero = tt
lg-fin (suc n) = lg-fin n

Lg-ω : LgB (hl fin)
Lg-ω = (λ n → hsuc hself) , lg-fin

uipᴸ→Ωfin : UIPᴸ → (p : fin ≡ fin) → p ≡ refl
uipᴸ→Ωfin u = proj₁ (uipᴸ→funΩ u) Lg-ω
```

## §2 卡住的那一步与环的搬运

```agda
-- 合法高度上的环沿 z ↦ HB (G₀ z) 的搬运是恒等
LoopFix : Set
LoopFix = ∀ {x : HB S₀} → LgB x → (ℓ : x ≡ x) (δ : HB (G₀ x)) → subst (λ z → HB (G₀ z)) ℓ δ ≡ δ

-- 加在任一旧界之后看
Fix⊞ : Set
Fix⊞ = ∀ {x : HB S₀} → LgB x → (ℓ : x ≡ x) (s δ : HB (G₀ x)) → s ⊞ subst (λ z → HB (G₀ z)) ℓ δ ≡ s ⊞ δ

-- 只在旧界 0 之后, 只对合法增量
LoopFix₀ : Set
LoopFix₀ = ∀ {x : HB S₀} → LgB x → (ℓ : x ≡ x) (δ : HB (G₀ x)) → LgB δ → hz ⊞ subst (λ z → HB (G₀ z)) ℓ δ ≡ hz ⊞ δ
```

**充分的一半.** `LoopFix` 给 `IncIrr`: 两个判定都说 "相等" 时, 两条相等证明 $e, e' : c_0\equiv c$ 对 $e'$ 用 J ($c$ 自由), 剩下 $e$ 是 $c_0$ 处的环; $c_0$ 合法, 因为它在合法的界之下.

```agda
fix-pair : LoopFix → ∀ {c₀ c : HB S₀} → LgB c₀ → (e e′ : c₀ ≡ c) (δ : HB (G₀ c₀)) →
           subst (λ z → HB (G₀ z)) e δ ≡ subst (λ z → HB (G₀ z)) e′ δ
fix-pair F lc₀ e refl δ = F lc₀ e δ

fix→irr : LoopFix → IncIrr
fix→irr F w lo {c₀} {c} p₀ p p′ δ = h (dD w lo p p₀) (dD w lo p′ p₀)
  where
  h : (d d′ : (c₀ ≡ c) ⊎ ¬ (c₀ ≡ c)) → incD d δ ≡ incD d′ δ
  h (inj₁ e) (inj₁ e′) = fix-pair F (lgB⊲ p₀ (proj₁ lo) (proj₂ lo)) e e′ δ
  h (inj₁ e) (inj₂ ne) = ⊥-elim (ne e)
  h (inj₂ ne) (inj₁ e) = ⊥-elim (ne e)
  h (inj₂ _) (inj₂ _) = refl

fix→fix⊞ : LoopFix → Fix⊞
fix→fix⊞ F lx ℓ s δ = cong (λ t → s ⊞ t) (F lx ℓ δ)

fix⊞-pair : Fix⊞ → ∀ {c₀ c : HB S₀} → LgB c₀ → (e e′ : c₀ ≡ c) (s : HB (G₀ c)) (δ : HB (G₀ c₀)) →
            s ⊞ subst (λ z → HB (G₀ z)) e δ ≡ s ⊞ subst (λ z → HB (G₀ z)) e′ δ
fix⊞-pair F lc₀ e refl s δ = F lc₀ e s δ

fix⊞→lemma1 : Fix⊞ → Lemma1
fix⊞→lemma1 F w lo v c₀ p₀ δ l coh c p p′ =
  trans (cong (λ t → proj₁ (v c p) , t) (h (dD w lo p p₀) (dD w lo p′ p₀)))
        (cong (λ X → proj₁ X , (proj₂ X ⊞ incD (dD w lo p′ p₀) δ)) (coh c p p′))
  where
  h : (d d′ : (c₀ ≡ c) ⊎ ¬ (c₀ ≡ c)) → proj₂ (v c p) ⊞ incD d δ ≡ proj₂ (v c p) ⊞ incD d′ δ
  h (inj₁ e) (inj₁ e′) = fix⊞-pair F (lgB⊲ p₀ (proj₁ lo) (proj₂ lo)) e e′ (proj₂ (v c p)) δ
  h (inj₁ e) (inj₂ ne) = ⊥-elim (ne e)
  h (inj₂ ne) (inj₁ e) = ⊥-elim (ne e)
  h (inj₂ _) (inj₂ _) = refl
```

**必要的一半: 一个合法世界, 判定在两个证据上给出 `refl` 与 $\ell$.** 合法高度 $x$, 环 $\ell : x\equiv x$. 界 $b = \mathrm{h\Omega}\,(\lambda\_.\,x)$; 界的合法性要单调数据 `mo`: 坐标 $c\lhd c'$ 给 $x\lhd x$ 的一条路径. 在 $0\lhd 1$ 处取 `ℓp` (沿 $\ell$ 搬过的 `hself`), 别处取 `hself`; 两者都是 $x\lhd x$ 的证明, 所以 `mo` 合法. 外层世界 $a = 1$. 坐标 $x$ 的两个证据: `p₀` 经坐标 $0$, `p₁` 经坐标 $1$. `cmpB₀ p₁ p₀` 在 $\Omega$-结点处比坐标, 得 $0\lhd 1$ (不是字面 `self`), 于是调用 `mo`, 返回 `ℓp`; `dec₀` 把它送回 `inj₁ ℓ` (`dec-sub`, 对终点自由的 J).

```agda
⊲tr-self : ∀ {S} {a b : HB S} {w} (q : a ⊲[ w ] b) → ⊲ᴮ-tr hself q ≡ q
⊲tr-self hself = refl
⊲tr-self (hsuc q) = cong hsuc (⊲tr-self q)
⊲tr-self (hlim n q) = cong (hlim n) (⊲tr-self q)
⊲tr-self (hLim e q) = cong (hLim e) (⊲tr-self q)

dec-sub : ∀ {c₀ c : HB S₀} {w : A} (e : c₀ ≡ c) → dec₀ {w = w} (inj₁ (subst (λ z → c₀ ⊲[ w ] z) e hself)) ≡ inj₁ e
dec-sub refl = refl

module Loop {x : HB S₀} (lx : LgB x) (ℓ : x ≡ x) where
  ℓp : ∀ {w : A} → x ⊲[ w ] x
  ℓp {w} = subst (λ z → x ⊲[ w ] z) ℓ hself

  g : A → HB S₀
  g _ = x

  mo : ∀ {w c c′} → Lg w → c ⊲ w → c′ ⊲ w → c ⊲ c′ → g c ⊲[ w ] g c′
  mo {c = azero} {c′ = asuc _} _ _ _ _ = ℓp
  mo {c = azero} {c′ = azero} _ _ _ _ = hself
  mo {c = azero} {c′ = alim _} _ _ _ _ = hself
  mo {c = asuc _} _ _ _ _ = hself
  mo {c = alim _} _ _ _ _ = hself

  b : HB S₀
  b = hΩ tt g

  lb : LgB b
  lb = mo , (λ c lc → lx)

  a₁ : A
  a₁ = asuc azero

  wL : Out
  wL = a₁ , b

  loL : LgO wL
  loL = tt , lb

  p₀ p₁ : AdmE wL x
  p₀ = hLim {c = azero} (C.suc C.self) hself
  p₁ = hLim {c = a₁} C.self hself

  vL : Cmp wL
  vL c p = wz (up c) , hz

  cohL : Coh≡ (wL , vL)
  cohL c p p′ = refl

  d₀ : dD wL loL p₀ p₀ ≡ inj₁ refl
  d₀ = dec₀-diag p₀ tt lb

  d₁ : dD wL loL p₁ p₀ ≡ inj₁ ℓ
  d₁ = trans (cong (λ r → dec₀ {w = a₁} (inj₁ r)) (⊲tr-self ℓp)) (dec-sub ℓ)

  -- IncIrr 在这个世界上就是 "沿 ℓ 搬运不动 δ"
  fix : IncIrr → ∀ δ → subst (λ z → HB (G₀ z)) ℓ δ ≡ δ
  fix ir δ = trans (cong (λ t → incD t δ) (sym d₁)) (trans (sym (ir wL loL p₀ p₀ p₁ δ)) (cong (λ t → incD t δ) d₀))

  -- Lemma1 在这个世界上给出 hz ⊞ 之后的同一件事
  fix₀ : Lemma1 → ∀ δ → LgB δ → hz ⊞ subst (λ z → HB (G₀ z)) ℓ δ ≡ hz ⊞ δ
  fix₀ rc δ lδ =
    trans (cong (λ t → hz ⊞ incD t δ) (sym d₁))
      (trans (cong proj₂ (sym (rc wL loL vL x p₀ δ lδ cohL x p₀ p₁)))
             (cong (λ t → hz ⊞ incD t δ) d₀))

irr→fix : IncIrr → LoopFix
irr→fix ir lx ℓ δ = Loop.fix lx ℓ ir δ

lemma1→fix₀ : Lemma1 → LoopFix₀
lemma1→fix₀ rc lx ℓ = Loop.fix₀ lx ℓ rc

-- 合起来
irr⇔fix : (IncIrr → LoopFix) × (LoopFix → IncIrr)
irr⇔fix = irr→fix , fix→irr

chain : (LoopFix → Fix⊞) × (Fix⊞ → Lemma1) × (Lemma1 → LoopFix₀)
chain = fix→fix⊞ , fix⊞→lemma1 , lemma1→fix₀

uipᴸ→fix : UIPᴸ → LoopFix
uipᴸ→fix u lx ℓ δ = cong (λ q → subst (λ z → HB (G₀ z)) q δ) (u lx ℓ)
```

**前提可满足.** `Loop` 的前提 (合法高度 $x$ 与它的一个环) 对每个合法高度都有实例: $\ell=$ `refl` (例如 $x=\omega$, `Lg-ω`); 世界 `wL` 合法 (`loL`), 相干 (`cohL`). 有非平凡环的实例要一个使 `UIPᴸ` 失败的模型, 那正是本篇判断里没有的东西; 所以 `irr→fix`, `lemma1→fix₀` 的内容是 "这些律的强度", 不是 "存在反例".

## §3 不可反驳: 有函数外延时都成立

```agda
fe→uipᴸ′ : Funext → UIPᴸ
fe→uipᴸ′ fe l e = fe→uip fe e refl

¬uipᴸ→¬fe : ¬ UIPᴸ → ¬ Funext
¬uipᴸ→¬fe n fe = n (fe→uipᴸ′ fe)

¬irr→¬fe : ¬ IncIrr → ¬ Funext
¬irr→¬fe n fe = n (fix→irr (uipᴸ→fix (fe→uipᴸ′ fe)))

¬lemma1→¬fe : ¬ Lemma1 → ¬ Funext
¬lemma1→¬fe n fe = n (fix⊞→lemma1 (fix→fix⊞ (uipᴸ→fix (fe→uipᴸ′ fe))))

¬funΩ→¬fe : ¬ FunΩ → ¬ Funext
¬funΩ→¬fe n fe = n (uipᴸ→funΩ (fe→uipᴸ′ fe))
```

## §4 结论 (按档)

- **[定理]** `uipᴸ→funΩ`, `funΩ→uipᴸ`, `loc⇔funΩ`: 对一切合法世界的局部 UIP $\iff$ 合法高度上的 K $\iff$ 合法极限点的分支函数上的环都是 `refl`.
- **[定理]** `irr→fix`, `fix→irr`: `IncIrr` $\iff$ `LoopFix`. **[定理]** `chain`: `LoopFix` $\to$ `Fix⊞` $\to$ `Lemma1` $\to$ `LoopFix₀`. 第一条引理推出合法高度上的环沿族 `HB ∘ G₀` 搬运不动 `hz ⊞ δ`.
- **[定理]** `¬uipᴸ→¬fe`, `¬irr→¬fe`, `¬lemma1→¬fe`, `¬funΩ→¬fe`: 反驳其中任何一条就是反驳函数外延. 函数外延在立方模型里成立 (标准事实, 本仓库不形式化), 所以 `--without-K` 下**造不出**同一界之下两个不相等的相等证明.
- **[判断]** `FunΩ` (从而局部 UIP, `UIPᴸ`) 在 `--safe --without-K` 无函数外延时证不出. 依据: 它说函数类型 $\mathbb N\to H$, $A\to H$ 在具体点上的环平凡, 无外延时没有构造函数之间路径的办法; 已知的证明都经函数外延 (`fe→uip`). 我没有给出使它失败的模型.
- **[判断]** `LoopFix₀` (从而 `Lemma1`) 比 `UIPᴸ` 弱多少: 未定. `HB ∘ G₀` 的搬运只经 `Lev` 的种类类型依赖高度, 我没有找到能从搬运读回环的增量 $\delta$ (形如 "截面在 $x$ 处的值" 的 $\delta$ 都被搬运固定, `apd`), 所以不能把 `lemma1→fix₀` 升成 `lemma1→uipᴸ`.
