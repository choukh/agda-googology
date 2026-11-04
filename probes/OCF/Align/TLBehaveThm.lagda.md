# 对象在折叠下怎么行动 (二): 定理

> 入口 [TLBehave](TLBehave.lagda.md). **判决: HOLDS (编译过, 无条件).** 不读记号.
>
> | 定理 | 陈述 |
> | --- | --- |
> | `abs-row`, `abs-val` | 高度行折叠一次被下一个高度的第 0 行吸收, 在第一位置, 在值 ($\sqsubseteq^0$) 上 |
> | `no-abs-top` | 顶折叠一次的对象不是任何一行第 0 层的第一位置 |
> | `abs-row-strict` | 折叠确实增长, 又被吸收: $T(q,0)\prec T(q,1)\sqsubseteq^0T(q^+,0)$ |
> | `rows-not-ad` | 一切高度行, 一切层: 不 `Ad` |
> | `top-ad` | 顶的一切层 `Ad` |
> | `no-ad`, `fold-world`, `em-not-ad` | **世界内的一切对象** (高度 `ht _`, 世界合法) 不 `Ad`: 折叠到世界内目标的输出, 常数也不 |
> | `read-above` | 任何 `Cov` 的闭包节点: 第 $i$ 个输出严格低于第 $i$ 次读到的高度的秩 |
> | `read-fixed-s`, `read-fixed-l` | 高度行读到的高度不依赖世界, 也不依赖上文的值 |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLBehaveThm where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level using (_≺_; _⊑⁰_; Ordᶜ)
import OCF.Free.Level as FL
open import OCF.Align.CumReadBase using (Ord₀; next; next-⊲; cumA; _⊞_; cs)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadW using (one; Gw; g₀; pos; gnext)
open import OCF.Align.WorldTHW
open import OCF.Align.WorldTHLe
open import OCF.Align.WorldTHPsi using (NL; ns; nh; nt)
open import OCF.Align.WorldTHMain using (module M₀; ⊴₀→⊑⁰)
open import OCF.Align.WorldTHGrow using (T-strict)
open import OCF.Align.WorldTHEq
open import OCF.Align.ValueJudgeBase using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≼-suc; _≺ᵛ_; ≺ᵛ-irrefl)
open import OCF.Align.TLBehaveDef
```

## §1 高度行被吸收

```agda
abs-rowᵈ : ∀ q → Ω̇ (ht q) one ⊴ Ω̇ (ht (asuc q)) azero
abs-rowᵈ q = fc (rL {j = here} (rf (Ω≈ (ht≈ (≈ᴬ-refl q)) (≈ᴬ-refl one))))

abs-row : ∀ q → Abs₁ (ht q)
abs-row q = ht (asuc q) , abs-rowᵈ q

abs-val : ∀ q {u₀ u₁} (g : Gw u₀) (g′ : Gw u₁) (e : LB (ht q) one u₀) (e′ : LB (ht (asuc q)) azero u₁) →
          Tψ (ht q) one u₀ g e ⊑⁰ Tψ (ht (asuc q)) azero u₁ g′ e′
abs-val q {u₀} {u₁} g g′ e e′ = ⊴₀→⊑⁰ (M₀.tp₀ (abs-rowᵈ q) g₀ g₀ u₀ g (pos g) e u₁ g′ (pos g′) e′)
```

## §2 顶不被吸收

`X` 是节点, 所以它只能走 `rf`, 或者沿右边走第一位置. 一路走到 $(0,0)$ 也碰不到 `X`.

```agda
X : 𝓞 top one one
X = Ω̇ top one

noH : ∀ q b → X ⊴ Ω̇ (ht q) b → ⊥
noH q (asuc c) (rf e) with proj₁ e
... | ()
noH q (asuc c) (ni k) = invE (k C.self g₀)
  where
  invE : X ⊴ oe es (ow (pos g₀) g₀ (Ω̇ (ht q) c)) → ⊥
  invE (rf e) = noH q c (rf e)
  invE (eR (rf e)) = noH q c (rf e)
  invE (eR (rw d)) = noH q c d
noH q (alim f) (l n (rf e)) = noH q (f n) (rf e)
noH q (alim f) (l n (eR d)) = noH q (f n) d
noH azero azero (s (rf ()))
noH (asuc q) azero (fc (rf e)) = noH q one (rf e)
noH (asuc q) azero (fc (rL d)) = noH q one d
noH (alim f) azero (l n (rf e)) = noH (f n) azero (rf e)
noH (alim f) azero (l n (rL d)) = noH (f n) azero d

no-abs-top : ∀ p → X ⊴ Ω̇ p azero → ⊥
no-abs-top (ht q) d = noH q azero d
no-abs-top (tφ f) (fc (rf e)) = no-abs-top (f azero) (rf e)
no-abs-top (tφ f) (fc (rL d)) = no-abs-top (f azero) d
```

## §3 折叠确实增长, 又被吸收

```agda
abs-row-strict : ∀ {q} (nl : NL (ht q) azero) {u₀ u₁ u₂} (g₀′ : Gw u₀) (g₁ : Gw u₁) (g₂ : Gw u₂)
                 (e₀ : LB (ht q) azero u₀) (e₁ : LB (ht q) one u₁) (e₂ : LB (ht (asuc q)) azero u₂) →
                 Tψ (ht q) azero u₀ g₀′ e₀ ≺ Tψ (ht q) one u₁ g₁ e₁ × (Tψ (ht q) one u₁ g₁ e₁ ⊑⁰ Tψ (ht (asuc q)) azero u₂ g₂ e₂)
abs-row-strict {q} nl {u₀} {u₁} g₀′ g₁ g₂ e₀ e₁ e₂ = T-strict nl u₀ g₀′ e₀ u₁ g₁ e₁ , abs-val q g₁ g₂ e₁ e₂
```

## §4 秩

`rk` 把下标读成第 0 层的树, 只作陈述的刻度, 沿 `⊲` 单调. `next` 把输出接进下标, 所以秩严格盖住输出.

```agda
rk : A → Ord₀
rk azero = FL.zero
rk (asuc a) = FL.suc (rk a)
rk (alim f) = FL.lim (λ n → rk (f n))

rk-⊲ : ∀ {a b} → a ⊲ b → rk a ≼ rk b
rk-⊲ C.self = ≼-refl _
rk-⊲ (C.suc p) = ≼-suc (rk-⊲ p)
rk-⊲ (C.lim n p) = ≼l n (rk-⊲ p)

rk-⊞ʳ : ∀ a b → rk b ≼ rk (a ⊞ b)
rk-⊞ʳ a azero = z≼
rk-⊞ʳ a (asuc b) = s≼s (rk-⊞ʳ a b)
rk-⊞ʳ a (alim f) = l≼ (λ n → ≼l n (rk-⊞ʳ a (f n)))

rk-cs : ∀ g n → rk (g n) ≼ rk (cs g n)
rk-cs g zero = ≼-refl _
rk-cs g (suc n) = ≼-suc (rk-⊞ʳ (cs g n) (g (suc n)))

dom-cum : ∀ y → y ≼ rk (cumA y)
dom-cum FL.zero = z≼
dom-cum (FL.suc a) = s≼s (dom-cum a)
dom-cum (FL.lim f) = l≼ (λ n → ≼l n (≼-trans (dom-cum (f n)) (rk-cs (λ m → cumA (f m)) n)))
dom-cum (FL.limᵢ () f)
dom-cum (FL.up () x)

next-≺ : ∀ η y → y ≺ᵛ rk (next η y)
next-≺ η y = s≼s (≼-trans (dom-cum y) (rk-⊞ʳ η (cumA y)))
```

## §5 `Ad`: 高度行没有, 顶有

下标 `v₀` 是 `next one (rk q)`: 合法, 秩高于 $q$. 所以 `Cov` 在高度固定的闭包上不成立.

```agda
no-cov : ∀ q → (v₀ : A) → v₀ ⊲ q → rk q ≺ᵛ rk v₀ → ⊥
no-cov q v₀ d r = ≺ᵛ-irrefl (rk q) (≼-trans r (rk-⊲ d))

rows-not-ad : ∀ q b → Ad (Ω̇ (ht q) b) → ⊥
rows-not-ad q (asuc c) (ad-i k) with k C.self g₀
... | ad-e (ad-w d) = rows-not-ad q c d
rows-not-ad q (alim f) (ad-l n (ad-e d)) = rows-not-ad q (f n) d
rows-not-ad azero azero (ad-s ())
rows-not-ad (asuc q) azero (ad-c cov) = no-cov q v₀ (cov (next-⊲ one (rk q)) (gnext (rk q) g₀)) (next-≺ one (rk q))
  where
  v₀ = next one (rk q)
rows-not-ad (asuc q) azero (ad-x (ad-L d)) = rows-not-ad q one d
rows-not-ad (alim f) azero (ad-l n (ad-L d)) = rows-not-ad (f n) azero d

top-cov : Cov {p = top} {a = azero} {u = one} (λ {v} q g → oL (tp v) azero (z⊲ v , hbv ht v) (ow (pos g) g₀ (Ω̇ (ht v) azero)))
top-cov q g = C.self

top-ad : ∀ a → Ad (Ω̇ top a)
top-ad azero = ad-c top-cov
top-ad (asuc c) = ad-i (λ q g → ad-e (ad-w (top-ad c)))
top-ad (alim f) = ad-l 0 (ad-e (top-ad (f 0)))
```

## §5′ 世界内的一切对象都不 `Ad`

不只是行. **高度是 `ht _` 的任何对象 (世界合法)**: 折叠的输出, 加法的结果, 嵌入的常数都在内. 理由是 `hOf`: 这样的对象读到的高度都在 $q$ 之下, 与世界无关; 而世界可以取得比 $q$ 高 (`next`). 这条是对类型里的全部对象证的, 不是列举闭项.

```agda
data IsHt : Hg → Set where
  isHt : ∀ q → IsHt (ht q)

low-ht : ∀ {h p} → IsHt p → h <ᴴ p → IsHt h
low-ht (isHt _) here = isHt _
low-ht (isHt _) (st j) = low-ht (isHt _) j
low-ht (isHt _) (lh n) = isHt _
low-ht (isHt _) (ll n j) = low-ht (isHt _) j

hOf-bound : ∀ {q a v} (x : 𝓞 (ht q) a v) → hA (hOf x) ⊲ q
hOf-bound o0 = C.self
hOf-bound (os x) = C.self
hOf-bound (ol F) = C.self
hOf-bound (oi r h) = C.self
hOf-bound (od i k r h) = C.self
hOf-bound (oc x h) = C.self
hOf-bound (oe stp y) = C.self
hOf-bound (oL i k e y) = <⊲ i
hOf-bound (ow w g x) = hOf-bound x

no-ad : ∀ {p a u} → IsHt p → Gw u → {y : 𝓞 p a u} → Ad y → ⊥
no-ad (isHt q) g {y = oc x h} (ad-c cov) = no-cov q v₀ (⊲-tr (cov (next-⊲ _ (rk q)) (gnext (rk q) g)) (hOf-bound (h (next-⊲ _ (rk q)) (gnext (rk q) g)))) (next-≺ _ (rk q))
  where
  v₀ = next _ (rk q)
no-ad P g (ad-x d) = no-ad P g d
no-ad P g (ad-s d) = no-ad P g d
no-ad P g (ad-l n d) = no-ad P g d
no-ad P g (ad-i k) = no-ad P g (k C.self g)
no-ad P g (ad-d {i = i} k) = no-ad P g (k C.self g)
no-ad P g (ad-e d) = no-ad P g d
no-ad P g (ad-L {i = i} d) = no-ad (low-ht P i) g d
no-ad P g′ (ad-w {g = g} d) = no-ad P g d

-- 折叠到世界内的目标, 输出不 Ad, 不管被折叠的是什么
fold-world : ∀ {p a u} q t (x : 𝓞 p a u) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (tv : LB (ht q) t v) (av : LB p a v) → Ad (ψ (ht q) t x gu v gv uv tv av) → ⊥
fold-world q t x gu v gv uv tv av = no-ad (isHt q) gv
```

**常数也一样.** `em` 把任何第 0 层的树放进数据树, 值多大都不 `Ad`.

```agda
em-not-ad : ∀ {u} (y : Ord₀) → Gw u → Ad (em {u} y) → ⊥
em-not-ad y g = no-ad (isHt azero) g
```

## §6 读到的高度与已经产生的值

**`read-above`.** 对任何 `Cov` 的分支, 第 $i$ 个链点读到的高度的秩严格高于第 $i$ 个输出. `yss`, `ixs` 就是 `ψ₀⁰` 的 `oc` 行用的链, 对任何赋值 `val` 都成立: 这是对一切上下文的陈述.

```agda
read-above : ∀ {p a u m} {h : ∀ {v} → u ⊲ v → Gw v → 𝓞 p a v} (um : u ⊲ m) (gm : Gw m) (y₀ : Ord₀) (val : Ix m → Ord₀) →
             Cov h → ∀ i →
             yss gm y₀ val i ≺ᵛ rk (hA (hOf (h (⊲-tr um (Ix.up (ixs gm y₀ val i))) (Ix.gη (ixs gm y₀ val i)))))
read-above {m = m} {h = h} um gm y₀ val cov zero = ≼-trans (next-≺ m y₀) (rk-⊲ (cov (⊲-tr um (Ix.up (ixs gm y₀ val 0))) (Ix.gη (ixs gm y₀ val 0))))
read-above {h = h} um gm y₀ val cov (suc n) = ≼-trans (next-≺ (Ix.η (ixs gm y₀ val n)) (val (ixs gm y₀ val n))) (rk-⊲ (cov (⊲-tr um (Ix.up (ixs gm y₀ val (suc n)))) (Ix.gη (ixs gm y₀ val (suc n)))))
```

**高度行读到的高度是定值.** 后继: 分支都在 $q$. 极限: 第 $n$ 支在 $f\,n$, 与世界和上文无关.

```agda
read-fixed-s : ∀ q {v} (w : one ⊲ v) (g : Gw v) → hOf {ht (asuc q)} {azero} {v} (oL here v (C.self , tt) (ow (pos g) g₀ (Ω̇ (ht q) v))) ≡ ht q
read-fixed-s q w g = refl

read-fixed-l : ∀ f n → hOf {ht (alim f)} {azero} {one} (oL (lh n) azero (z⊲ one , tt) (Ω̇ (ht (f n)) azero)) ≡ ht (f n)
read-fixed-l f n = refl
```
