# 共享槽, 否定一路 (一): 接口定稿之前, 槽不能是哪种类型, 不能怎样忘

> 不含记号. 入口 [NegSlot](NegSlot.lagda.md). 本篇**不依赖**构造一路的接口 `SlotIf` (接口定稿之前写的部分), 只用 [HtTowerTy](HtTowerTy.lagda.md), [HtTowerNeg](HtTowerNeg.lagda.md), [NegKindLvLev](NegKindLvLev.lagda.md) 与上一轮的接口 [RsOwnIf](RsOwnIf.lagda.md) (`RsK`, `subW`, `topSub`; 只读导入). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** 构造一路要让 "坐标是高度, 坐标类型随级变" 的种类 (`K₁` 里分量 `hs c` 的新种类 `κc c`, 坐标 `HB (Lev c)`, $c$ 取遍 `H₀`) 也能像底拷贝那样 "一起升": 世界证据带一个共享槽 (一个公共的类型 $X$) 与一族单调搬运 $\tau_c$. 本篇在接口之前回答两个问题:
>
> 1. **槽能不能是已有的坐标类型?** (§2) **`slot-wall`** (定理): 若从高度类型 `HB S` 经槽 $X$ 绕一圈回来是**膨胀的** ($x\lhd u(d\,x)$, 比 "恒等" 弱), 且 $X$ 是 `S` 的某个种类的坐标的收缩, 则矛盾. 推论 **`slot-coordK₁`**: `K₁` 的每一个种类 $\kappa_0$ (坐标 `A` 或某个 `HB (Lev y)`), 都给出一个下标 $c'$ (显式: `hz` 或 `hs y`), 使 `κc c′` 的坐标 `HB (Lev c′)` 不能经以 `E K₁ κ₀` 为收缩的槽无损 (甚至膨胀地) 来回. 所以要服务**一切** `κc c` 的精确读回, 槽必须在 `K₁` 的一切坐标类型之上 (判断: 这就是 "一个类型装下全部级", 手册 §3.1 的影子).
> 2. **一起升能不能 "忘"?** (§3, §4) **`no-forget`** (定理): 两份拷贝, 低的坐标是 `S` 的种类 $\kappa$ 的坐标, 高的坐标是 `HB S` (高的那一级里有一个种类, 坐标就是低的那份的坐标). 若 (i) 高的那份能精确置任意值 (`TopH`), (ii) 低的那份 "升到自己现在的顶" 时世界变大 (`Self≤`, 由 `RsK.rs≤` 取 $v=$ 旧顶得到), (iii) 升低的那份之后, 高的那份的界只依赖 $v$, 不依赖旧世界 (`Forgets`; 共享槽的 "一起升": 槽置成 $\sigma(v)$, 每份读 $\tau_{c}$), 则矛盾. **`no-forgetK₁`**, **`no-forget-jx`** (定理): 在 `K₁` 的任一带证据的世界 `subW K₁ P` 上, 拷贝对 (`κc c`, `κc (hs c)`) 与 (`κH f`, `κH f⁺`) 各给一条. 三个前提两两可满足 (`satTS`, `satTF`, `satSF`; `K₁` 上 `RsK` 对 (`κc hz`, `κc (hs hz)`) 的实例 `RLz`, `RHz`).
>
> 关键引理 **`no-inflate`** (§1, 定理, 对一切 `S` 与种类): 没有 `d : HB S → E S κ`, `u : E S κ → HB S` 使 $x\lhd u(d\,x)$ 对一切 $x$. 它加强 `HtTowerNeg.no-retract` (那里是 $u(d\,x)\equiv x$): 第一位置是非严格的子项关系, 取 $x=\mathrm{h\Omega}\,\kappa\,u$ 即得 $x\lhd$ 自己的一个真子项.
>
> **只否定什么.** (a) 槽是 `K₁` 的坐标类型 (或其收缩), 同时对**一切** `κc c` 的精确 (或膨胀) 读回; (b) "忘" 的一起升: 升一份时, 另一份**更高一级**的拷贝的新界只依赖 $v$, 同时高的那份能精确置值, 低的那份 `rs≤`. **不否定**: 不忘的槽 (新槽依赖旧槽, 例如 "旧槽与 $\sigma(v)$ 的某种合并"); 有损的读回 (高的那份不能精确置任意值: 只对 $\tau$ 的像精确); 只在同一级的拷贝之间共享 (`RsOwnSW` 的底拷贝, 坐标都是 `A`, 没有一份比另一份高一级; 与 `no-forget` 不冲突); 槽在一切级之上的类型 (例如 $\Sigma_c\,$`HB (Lev c)`; 本篇没有否定, 见 §5 判断).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSlotPre where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (H₀)
open import OCF.Align.HtTowerNeg using (_≺ᴮ_; ≺s; ≺l; ≺Ω; Acc≺; acc; acc≺)
open import OCF.Align.NegKindLvLev using (Cd; lvK; coord-lv)
open import OCF.Align.GenFoldIf using (K₁; TopG; top; GenK; w₀; lw₀)
open import OCF.Align.GenFoldInst using (genKc)
open import OCF.Align.NegGenFoldUpd using (jx)
open import OCF.Align.RsOwnIf using (RsK; rs; rs≤; rsLg; rs-top; subW; topSub)
```

## §1 `no-inflate`: 经一个坐标绕一圈, 不能膨胀

$\lhd$ (`_⊲[_]_`) 的每一步都走向子项或不动, 所以 $a\lhd b$ 且 $b$ 是 $a$ 的真子项 (传递闭包 `_≺⁺_`) 不可能.

```agda
module _ {S : KS} where
  infix 4 _≺⁺_
  data _≺⁺_ : HB S → HB S → Set where
    base : ∀ {x y} → x ≺ᴮ y → x ≺⁺ y
    cons : ∀ {x y z} → x ≺ᴮ y → y ≺⁺ z → x ≺⁺ z

  data Acc⁺ (x : HB S) : Set where
    acc⁺ : (∀ {y} → y ≺⁺ x → Acc⁺ y) → Acc⁺ x

  mutual
    toAcc⁺ : ∀ {x} → Acc≺ x → Acc⁺ x
    toAcc⁺ a = acc⁺ (down a)

    down : ∀ {x} → Acc≺ x → ∀ {y} → y ≺⁺ x → Acc⁺ y
    down (acc f) (base p) = toAcc⁺ (f p)
    down a (cons p q) = inv (down a q) (base p)

    inv : ∀ {x} → Acc⁺ x → ∀ {y} → y ≺⁺ x → Acc⁺ y
    inv (acc⁺ g) p = g p

  irr⁺ : ∀ {x} → Acc⁺ x → ¬ (x ≺⁺ x)
  irr⁺ (acc⁺ g) p = irr⁺ (g p) p

  no-up : ∀ {a b w} → a ⊲[ w ] b → b ≺⁺ a → ⊥
  no-up hself q = irr⁺ (toAcc⁺ (acc≺ _)) q
  no-up (hsuc p) q = no-up p (cons ≺s q)
  no-up (hlim n p) q = no-up p (cons (≺l n) q)
  no-up (hLim e p) q = no-up p (cons (≺Ω _) q)

  no-inflate-at : ∀ κ (u : E S κ → HB S) e {w} → ¬ (hΩ κ u ⊲[ w ] u e)
  no-inflate-at κ u e p = no-up p (base (≺Ω e))

  no-inflate : ∀ κ (d : HB S → E S κ) (u : E S κ → HB S) → ¬ (∀ x → Σ (Wd S) (λ w → x ⊲[ w ] u (d x)))
  no-inflate κ d u h = no-inflate-at κ u (d (hΩ κ u)) (proj₂ (h (hΩ κ u)))
```

## §2 槽不能是坐标类型的收缩

`X ◁ Y`: $X$ 是 $Y$ 的收缩 (`p ∘ s = id`). 例: $X=Y$ (`◁-rf`).

```agda
record _◁_ (X Y : Set) : Set where
  field
    s  : X → Y
    p  : Y → X
    ps : ∀ x → p (s x) ≡ x
open _◁_ public

◁-rf : ∀ {X} → X ◁ X
◁-rf = record { s = λ x → x ; p = λ x → x ; ps = λ x → refl }

◁≡ : ∀ {X Y Z : Set} → X ◁ Y → Y ≡ Z → X ◁ Z
◁≡ R refl = R

slot-wall : ∀ {S : KS} κ {X : Set} (d : HB S → X) (u : X → HB S) →
  (∀ x → Σ (Wd S) (λ w → x ⊲[ w ] u (d x))) → X ◁ E S κ → ⊥
slot-wall κ d u h R =
  no-inflate κ (λ x → s R (d x)) (λ e → u (p R e))
    (λ x → proj₁ (h x) , subst (λ y → x ⊲[ proj₁ (h x) ] u y) (sym (ps R (d x))) (proj₂ (h x)))

-- 精确的版本: τ ∘ σ = id 就是膨胀的特例
slot-wall≡ : ∀ {S : KS} κ {X : Set} (σ : HB S → X) (τ : X → HB S) → Wd S →
  (∀ x → τ (σ x) ≡ x) → X ◁ E S κ → ⊥
slot-wall≡ κ σ τ w0 e R = slot-wall κ σ τ (λ x → w0 , subst (λ y → x ⊲[ w0 ] y) (sym (e x)) hself) R
```

**`K₁` 的坐标类型.** `K₁ = Kc 1 = sup (⊤ ⊎ H₀) (FN S₀)`. 种类 `(inj₁ tt , tt)` 的坐标是 `A`; 种类 `(inj₂ c , κ)` 的坐标是 `Cd (lvK c κ)` (`coord-lv`): `A` 或 `HB (Lev y)`. `coordK₁` 对每个种类给一个下标 $c'$ 与 `Lev c′` 的一个种类, 坐标恰是 `E K₁ κ₀`: `A` 取 $c'=$ `hz` (`S₀` 的种类); `HB (Lev y)` 取 $c'=$ `hs y` (新种类).

```agda
κc : H₀ → K K₁
κc c = inj₂ (hs c) , inj₂ tt

coordK₁ : ∀ (κ₀ : K K₁) → Σ H₀ (λ c′ → Σ (K (Lev c′)) (λ κ → E (Lev c′) κ ≡ E K₁ κ₀))
coordK₁ (inj₁ tt , tt) = hz , tt , refl
coordK₁ (inj₂ c , κ) = go (lvK c κ) (coord-lv c κ)
  where
  go : ∀ ℓ → E (Lev c) κ ≡ Cd ℓ → Σ H₀ (λ c′ → Σ (K (Lev c′)) (λ κ′ → E (Lev c′) κ′ ≡ E (Lev c) κ))
  go (inj₁ tt) e = hz , tt , sym e
  go (inj₂ y) e = hs y , inj₂ tt , sym e

-- 对每个种类 κ₀: 以 E K₁ κ₀ 为收缩的槽, 有一份拷贝 κc c′ 不能经它膨胀地来回
slot-coordK₁ : ∀ (κ₀ : K K₁) {X : Set} → X ◁ E K₁ κ₀ →
  Σ H₀ (λ c′ → ∀ (d : HB (Lev c′) → X) (u : X → HB (Lev c′)) → ¬ (∀ x → Σ (Wd (Lev c′)) (λ w → x ⊲[ w ] u (d x))))
slot-coordK₁ κ₀ R with coordK₁ κ₀
... | c′ , κ , e = c′ , λ d u h → slot-wall κ d u h (◁≡ R (sym e))

-- κc c′ 的坐标就是 HB (Lev c′)
E-κc : ∀ c → E K₁ (κc c) ≡ HB (Lev c)
E-κc c = refl
```

## §3 `no-forget`: 忘的一起升

两份拷贝的操作 `Ops κ W`: 世界类型 $W$ 任意; 低的那份的界 `bL : W → E S κ`, 高的那份的界 `bH : W → HB S`; 各自的升界 `rsL`, `rsH`; 一个世界 `w₀`.

```agda
record Ops {S : KS} (κ : K S) (W : Set) : Set where
  field
    bL  : W → E S κ
    bH  : W → HB S
    rsL : W → E S κ → W
    rsH : W → HB S → W
    w₀ᵒ : W
open Ops public

module _ {S : KS} {κ : K S} {W : Set} (O : Ops κ W) where
  TopH : Set
  TopH = ∀ w x → bH O (rsH O w x) ≡ x

  Self≤ : Set
  Self≤ = ∀ w → Σ (Wd S) (λ ω → bH O w ⊲[ ω ] bH O (rsL O w (bL O w)))

  Forgets : Set
  Forgets = ∀ w w′ v → bH O (rsL O w v) ≡ bH O (rsL O w′ v)

  no-forget : TopH → Self≤ → Forgets → ⊥
  no-forget tH sf fg = no-inflate κ d u h
    where
    d : HB S → E S κ
    d x = bL O (rsH O (w₀ᵒ O) x)
    u : E S κ → HB S
    u v = bH O (rsL O (w₀ᵒ O) v)
    h : ∀ x → Σ (Wd S) (λ ω → x ⊲[ ω ] u (d x))
    h x = proj₁ q , subst₂′ (tH (w₀ᵒ O) x) (fg w₁ (w₀ᵒ O) (d x)) (proj₂ q)
      where
      w₁ = rsH O (w₀ᵒ O) x
      q = sf w₁
      subst₂′ : ∀ {a a′ b b′ ω} → a ≡ a′ → b ≡ b′ → a ⊲[ ω ] b → a′ ⊲[ ω ] b′
      subst₂′ refl refl r = r
```

**三个前提两两可满足** (在 `S = step S₀`, $\kappa=$ 新种类, 坐标 `H₀` 上; 世界 `(azero , hz)`).

```agda
private
  S₁ : KS
  S₁ = step S₀

  κn : K S₁
  κn = inj₂ tt

  ω₁ : Wd S₁
  ω₁ = azero , hz

-- TopH 与 Self≤: 两份各占一个分量, 升一份不动另一份 (不忘)
opsTS : Ops {S₁} κn (H₀ × HB S₁)
opsTS = record { bL = proj₁ ; bH = proj₂ ; rsL = λ w v → v , proj₂ w ; rsH = λ w x → proj₁ w , x ; w₀ᵒ = hz , hz }

satTS : TopH opsTS × Self≤ opsTS
satTS = (λ w x → refl) , (λ w → ω₁ , hself)

-- TopH 与 Forgets: 升低的那份时高的那份置 0
opsTF : Ops {S₁} κn (H₀ × HB S₁)
opsTF = record { bL = proj₁ ; bH = proj₂ ; rsL = λ w v → v , hz ; rsH = λ w x → proj₁ w , x ; w₀ᵒ = hz , hz }

satTF : TopH opsTF × Forgets opsTF
satTF = (λ w x → refl) , (λ w w′ v → refl)

-- Self≤ 与 Forgets: 高的那份恒为 0 (不能精确置值)
opsSF : Ops {S₁} κn H₀
opsSF = record { bL = λ w → w ; bH = λ _ → hz ; rsL = λ w v → v ; rsH = λ w x → w ; w₀ᵒ = hz }

satSF : Self≤ opsSF × Forgets opsSF
satSF = (λ w → ω₁ , hself) , (λ w w′ v → refl)
```

## §4 在 `K₁` 上: 任一带证据的世界, 任一对相邻级的拷贝

`tpK₁ = tpK (genKc 1)`: `κc c` 的顶就是分量 `hs c` 的世界的第二分量 (`refl`). 世界带任意证据 $P$ (`subW K₁ P`, 共享槽的证据是它的特例), 顶沿用 (`topSub`). `RsK` 就是 `KLv` 的三条升界律 (接口 `RsOwnIf` §1).

```agda
tpK₁ : TopG K₁
tpK₁ = GenK.tpK (genKc 1)

top-κc : ∀ c w → top tpK₁ (κc c) w ≡ proj₂ (w (inj₂ (hs c)))
top-κc c w = refl

module K1 (P : Wd K₁ → Set) where
  W : Set
  W = Σ (Wd K₁) P

  tpP : TopG (subW K₁ P)
  tpP = topSub tpK₁

  -- 低: κc c (坐标 HB (Lev c)); 高: κc (hs c) (坐标 HB (Lev (hs c)) = HB (step (Lev c)), 新种类的坐标 HB (Lev c))
  opsK : ∀ c → RsK (subW K₁ P) tpP (κc c) → RsK (subW K₁ P) tpP (κc (hs c)) → W → Ops {Lev (hs c)} (inj₂ tt) W
  opsK c RL RH w0 = record
    { bL = λ w → top tpP (κc c) w ; bH = λ w → top tpP (κc (hs c)) w
    ; rsL = rs RL ; rsH = rs RH ; w₀ᵒ = w0 }

  ForgetK : ∀ c → RsK (subW K₁ P) tpP (κc c) → Set
  ForgetK c RL = ∀ w w′ v → top tpP (κc (hs c)) (rs RL w v) ≡ top tpP (κc (hs c)) (rs RL w′ v)

  no-forgetK₁ : ∀ c (RL : RsK (subW K₁ P) tpP (κc c)) (RH : RsK (subW K₁ P) tpP (κc (hs c))) → W →
    ForgetK c RL → ⊥
  no-forgetK₁ c RL RH w0 fg =
    no-forget (opsK c RL RH w0) (λ w x → rs-top RH)
      (λ w → let q = rs≤ RL {w} {top tpP (κc c) w} hself (inj₂ (hs (hs c))) in _ , proj₂ q)
      fg
```

**只在 `κH f` 一族里 (下标都是 `jx f` 的形状).** 高的那份取 $f^+ = (n\mapsto$ `hs (jx f)`$)$: `Lev (jx f⁺)` 的第 1 个分量是 `Lev (hs (jx f)) = step (Lev (jx f))`, 它的新种类 `(1 , inj₂ tt)` 的坐标就是 `HB (Lev (jx f))` (定义相等). 所以只服务 `κH f` 一族的共享槽, 也不能忘.

```agda
  κH : (ℕ → H₀) → K K₁
  κH f = κc (jx f)

  f⁺ : (ℕ → H₀) → ℕ → H₀
  f⁺ f _ = hs (jx f)

  opsJ : ∀ f → RsK (subW K₁ P) tpP (κH f) → RsK (subW K₁ P) tpP (κH (f⁺ f)) → W →
         Ops {Lev (jx (f⁺ f))} (1 , inj₂ tt) W
  opsJ f RL RH w0 = record
    { bL = λ w → top tpP (κH f) w ; bH = λ w → top tpP (κH (f⁺ f)) w
    ; rsL = rs RL ; rsH = rs RH ; w₀ᵒ = w0 }

  no-forget-jx : ∀ f (RL : RsK (subW K₁ P) tpP (κH f)) (RH : RsK (subW K₁ P) tpP (κH (f⁺ f))) → W →
    (∀ w w′ v → top tpP (κH (f⁺ f)) (rs RL w v) ≡ top tpP (κH (f⁺ f)) (rs RL w′ v)) → ⊥
  no-forget-jx f RL RH w0 fg =
    no-forget (opsJ f RL RH w0) (λ w x → rs-top RH)
      (λ w → let q = rs≤ RL {w} {top tpP (κH f) w} hself (inj₂ (hs (jx (f⁺ f)))) in _ , proj₂ q)
      fg
```

**`RsK` 前提的实例.** 下标 `hz`, `hs hz` 不含函数, 是不是它们可以按构造子判定; 在 `K₁` 本身 ($P$ 恒真) 上, 对 `κc hz` 与 `κc (hs hz)` 各写一个点更新 (精确置自己, 别处不动), 满足 `RsK` 的三条律. 所以 `no-forgetK₁` 的 `RsK` 前提同时可满足, 缺的只是 `ForgetK` (点更新不忘: 升 `κc hz` 不动 `κc (hs hz)`).

```agda
module _ where
  private
    T⊤ : KS
    T⊤ = subW K₁ (λ _ → ⊤)

    tp⊤ : TopG T⊤
    tp⊤ = topSub tpK₁

  updZ : Wd K₁ → HB (Lev hz) → Wd K₁
  updZ w v (inj₁ tt) = w (inj₁ tt)
  updZ w v (inj₂ hz) = w (inj₂ hz)
  updZ w v (inj₂ (hs hz)) = proj₁ (w (inj₂ (hs hz))) , v
  updZ w v (inj₂ (hs (hs y))) = w (inj₂ (hs (hs y)))
  updZ w v (inj₂ (hs (hl g))) = w (inj₂ (hs (hl g)))
  updZ w v (inj₂ (hs (hΩ κ g))) = w (inj₂ (hs (hΩ κ g)))
  updZ w v (inj₂ (hl g)) = w (inj₂ (hl g))
  updZ w v (inj₂ (hΩ κ g)) = w (inj₂ (hΩ κ g))

  updZ≤ : ∀ w v → proj₂ (w (inj₂ (hs hz))) ⊲[ proj₁ (w (inj₂ (hs hz))) ] v → _≤w_ K₁ w (updZ w v)
  updZ≤ w v q (inj₁ tt) = ≤w-rf S₀
  updZ≤ w v q (inj₂ hz) = ≤w-rf S₀
  updZ≤ w v q (inj₂ (hs hz)) = ≤w-rf S₀ , q
  updZ≤ w v q (inj₂ (hs (hs y))) = ≤w-rf (Lev (hs (hs y)))
  updZ≤ w v q (inj₂ (hs (hl g))) = ≤w-rf (Lev (hs (hl g)))
  updZ≤ w v q (inj₂ (hs (hΩ κ g))) = ≤w-rf (Lev (hs (hΩ κ g)))
  updZ≤ w v q (inj₂ (hl g)) = ≤w-rf (Lev (hl g))
  updZ≤ w v q (inj₂ (hΩ κ g)) = ≤w-rf (Lev (hΩ κ g))

  updZLg : ∀ w v → LgW K₁ w → LgB v → LgW K₁ (updZ w v)
  updZLg w v lw lv (inj₁ tt) = lw (inj₁ tt)
  updZLg w v lw lv (inj₂ hz) = lw (inj₂ hz)
  updZLg w v lw lv (inj₂ (hs hz)) = proj₁ (lw (inj₂ (hs hz))) , lv
  updZLg w v lw lv (inj₂ (hs (hs y))) = lw (inj₂ (hs (hs y)))
  updZLg w v lw lv (inj₂ (hs (hl g))) = lw (inj₂ (hs (hl g)))
  updZLg w v lw lv (inj₂ (hs (hΩ κ g))) = lw (inj₂ (hs (hΩ κ g)))
  updZLg w v lw lv (inj₂ (hl g)) = lw (inj₂ (hl g))
  updZLg w v lw lv (inj₂ (hΩ κ g)) = lw (inj₂ (hΩ κ g))

  RLz : RsK T⊤ tp⊤ (κc hz)
  RLz = record
    { rs = λ w v → updZ (proj₁ w) v , tt
    ; rs≤ = λ {w} {v} q → updZ≤ (proj₁ w) v q
    ; rsLg = λ {w} {v} lw lv → updZLg (proj₁ w) v lw lv
    ; rs-top = refl }

  updO : Wd K₁ → HB (Lev (hs hz)) → Wd K₁
  updO w v (inj₁ tt) = w (inj₁ tt)
  updO w v (inj₂ hz) = w (inj₂ hz)
  updO w v (inj₂ (hs hz)) = w (inj₂ (hs hz))
  updO w v (inj₂ (hs (hs hz))) = proj₁ (w (inj₂ (hs (hs hz)))) , v
  updO w v (inj₂ (hs (hs (hs y)))) = w (inj₂ (hs (hs (hs y))))
  updO w v (inj₂ (hs (hs (hl g)))) = w (inj₂ (hs (hs (hl g))))
  updO w v (inj₂ (hs (hs (hΩ κ g)))) = w (inj₂ (hs (hs (hΩ κ g))))
  updO w v (inj₂ (hs (hl g))) = w (inj₂ (hs (hl g)))
  updO w v (inj₂ (hs (hΩ κ g))) = w (inj₂ (hs (hΩ κ g)))
  updO w v (inj₂ (hl g)) = w (inj₂ (hl g))
  updO w v (inj₂ (hΩ κ g)) = w (inj₂ (hΩ κ g))

  updO≤ : ∀ w v → proj₂ (w (inj₂ (hs (hs hz)))) ⊲[ proj₁ (w (inj₂ (hs (hs hz)))) ] v → _≤w_ K₁ w (updO w v)
  updO≤ w v q (inj₁ tt) = ≤w-rf S₀
  updO≤ w v q (inj₂ hz) = ≤w-rf S₀
  updO≤ w v q (inj₂ (hs hz)) = ≤w-rf (Lev (hs hz))
  updO≤ w v q (inj₂ (hs (hs hz))) = ≤w-rf (Lev (hs hz)) , q
  updO≤ w v q (inj₂ (hs (hs (hs y)))) = ≤w-rf (Lev (hs (hs (hs y))))
  updO≤ w v q (inj₂ (hs (hs (hl g)))) = ≤w-rf (Lev (hs (hs (hl g))))
  updO≤ w v q (inj₂ (hs (hs (hΩ κ g)))) = ≤w-rf (Lev (hs (hs (hΩ κ g))))
  updO≤ w v q (inj₂ (hs (hl g))) = ≤w-rf (Lev (hs (hl g)))
  updO≤ w v q (inj₂ (hs (hΩ κ g))) = ≤w-rf (Lev (hs (hΩ κ g)))
  updO≤ w v q (inj₂ (hl g)) = ≤w-rf (Lev (hl g))
  updO≤ w v q (inj₂ (hΩ κ g)) = ≤w-rf (Lev (hΩ κ g))

  updOLg : ∀ w v → LgW K₁ w → LgB v → LgW K₁ (updO w v)
  updOLg w v lw lv (inj₁ tt) = lw (inj₁ tt)
  updOLg w v lw lv (inj₂ hz) = lw (inj₂ hz)
  updOLg w v lw lv (inj₂ (hs hz)) = lw (inj₂ (hs hz))
  updOLg w v lw lv (inj₂ (hs (hs hz))) = proj₁ (lw (inj₂ (hs (hs hz)))) , lv
  updOLg w v lw lv (inj₂ (hs (hs (hs y)))) = lw (inj₂ (hs (hs (hs y))))
  updOLg w v lw lv (inj₂ (hs (hs (hl g)))) = lw (inj₂ (hs (hs (hl g))))
  updOLg w v lw lv (inj₂ (hs (hs (hΩ κ g)))) = lw (inj₂ (hs (hs (hΩ κ g))))
  updOLg w v lw lv (inj₂ (hs (hl g))) = lw (inj₂ (hs (hl g)))
  updOLg w v lw lv (inj₂ (hs (hΩ κ g))) = lw (inj₂ (hs (hΩ κ g)))
  updOLg w v lw lv (inj₂ (hl g)) = lw (inj₂ (hl g))
  updOLg w v lw lv (inj₂ (hΩ κ g)) = lw (inj₂ (hΩ κ g))

  RHz : RsK T⊤ tp⊤ (κc (hs hz))
  RHz = record
    { rs = λ w v → updO (proj₁ w) v , tt
    ; rs≤ = λ {w} {v} q → updO≤ (proj₁ w) v q
    ; rsLg = λ {w} {v} lw lv → updOLg (proj₁ w) v lw lv
    ; rs-top = refl }

  -- 世界前提的实例: 基世界
  w0⊤ : Σ (Wd K₁) (λ _ → ⊤)
  w0⊤ = w₀ (genKc 1) , tt

  -- 点更新不忘: 升 κc hz 后 κc (hs hz) 的界就是旧的
  RLz-keeps : ∀ w v → top tp⊤ (κc (hs hz)) (rs RLz w v) ≡ top tp⊤ (κc (hs hz)) w
  RLz-keeps w v = refl
```

## §5 结论 (按档)

- **[定理]** `no-up`, **`no-inflate-at`**, **`no-inflate`** (对一切 `S`, 一切种类; 加强 `no-retract`).
- **[定理, 否定]** **`slot-wall`**, `slot-wall≡`; **`slot-coordK₁`** (`K₁` 的每个坐标类型都挡住一份 `κc c′`, $c'$ 显式); `coordK₁`, `E-κc`, `top-κc`.
- **[定理, 否定]** **`no-forget`** (一般); **`K1.no-forgetK₁`** (相邻级 `κc c`, `κc (hs c)`), **`K1.no-forget-jx`** (`κH f`, `κH (f⁺ f)`), 对任意世界证据 $P$.
- **[定理, 前提实例]** `satTS`, `satTF`, `satSF` (三个前提两两可满足); `RLz`, `RHz` (`K₁` 上相邻两级的 `RsK` 同时成立), `w0⊤`, `RLz-keeps` (它们不忘).
- **[判断]** (1) 共享槽要对一切 `κc c` 精确读回, 槽必须装得下一切级的高度且不是任何坐标类型的收缩; 同时一起升不能忘 (升一份时, 更高一级的拷贝要记得旧界). 两条合起来, 槽的内容至少要有 "每一级各自的旧界", 这已经接近世界本身按级的分量 (我没有把 "接近" 写成定理). (2) 剩下的形状: 不忘的槽 (新槽依赖旧槽), 或有损的读回 (只对 $\tau$ 的像精确). 后者把 "坐标是高度" 的种类的回灌限制在 $\tau_c$ 的像里; 像有多大要看构造一路的 $\tau$. (3) 穷尽是判断.
