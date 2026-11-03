# 分支在 `Ordᴵ` 上的层号的数据树: 地板按高度分开 (定义)

> 底座 [UniformLvBase](UniformLvBase.lagda.md). 不含记号. 结论写在 [UniformLv](UniformLv.lagda.md). 这是第二个设计; 第一个 (一个 $\ell$ 装下全部地板, 即 [Uniform5Syn](Uniform5Syn.lagda.md) 的 `fk τ`, `ac`) 被 [UniformLvNeg](UniformLvNeg.lagda.md) 的 `noAll` 否定.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformLvTree where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level using
  (Ordᴵ; _<ᴵ_; _≅ᴵ_; _⊑ᴵ_; _≺ᴵ_; via; zero; suc; lim; <→◃; Simᴵ; <ᴵ-dec; _◃₁_; ◃₁→◃; self)
import OCF.Align.Level as Lv
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Ordˢ; intoˢ; outˢ; toZ; Ωˢ; _+ˢ_; tr⁻ˢ)
open import OCF.Align.Symbolic using (Mlev)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; fb; _⊔_; Ev; bound; Bd; Fc; evF; iF; FB; liftEv)
open import OCF.Align.UniformLvBase
```

## §1 带高度的地板

`Evt w π`: 地板 $\pi$ 在世界族 $w$ 里成立. `tk h K`: $K<w\,h$; `tb h K`: $K\le w\,h$. 高度不同的地板之间**从不比较**, 所以各有各的世界.

```agda
infixl 5 _∪_
data Fᵗ : Set where
  tz  : Fᵗ
  tk  : ℕ → Ordᴵ → Fᵗ
  tb  : ℕ → Ordᴵ → Fᵗ
  _∪_ : Fᵗ → Fᵗ → Fᵗ

Evt : Wd → Fᵗ → Set
Evt w tz        = ⊤
Evt w (tk h K)  = Simᴵ (suc K) (w h)
Evt w (tb h K)  = Simᴵ K (w h)
Evt w (a ∪ b)   = Evt w a × Evt w b

Wok : Wd → Set
Wok w = ∀ h → zero <ᴵ w h

Fl₀ : Fᵗ
Fl₀ = tz ∪ tk 0 zero

-- 按高度选: 对两个自然数结构递归, 所以 `h = h` 的情形定义地展开
upd : Wd → ℕ → Ordᴵ → Wd
upd w zero    x zero    = x
upd w zero    x (suc n) = w (suc n)
upd w (suc h) x zero    = w zero
upd w (suc h) x (suc n) = upd (λ m → w (suc m)) h x n

upd-self : ∀ w h x → upd w h x h ≡ x
upd-self w zero    x = refl
upd-self w (suc h) x = upd-self (λ m → w (suc m)) h x

sel : ℕ → ℕ → Flr → Flr
sel zero    zero    f = f
sel zero    (suc _) f = fz
sel (suc _) zero    f = fz
sel (suc h) (suc n) f = sel h n f

prj : ℕ → Fᵗ → Flr
prj h tz = fz
prj h (tk n K) = sel h n (fk K)
prj h (tb n K) = sel h n (fb K)
prj h (a ∪ b) = prj h a ⊔ prj h b

toK : ∀ w h n K → Simᴵ (suc K) (w n) → Ev (w h) (sel h n (fk K))
toK w zero    zero    K e = e
toK w zero    (suc n) K e = tt
toK w (suc h) zero    K e = tt
toK w (suc h) (suc n) K e = toK (λ m → w (suc m)) h n K e

toB : ∀ w h n K → Simᴵ K (w n) → Ev (w h) (sel h n (fb K))
toB w zero    zero    K e = e
toB w zero    (suc n) K e = tt
toB w (suc h) zero    K e = tt
toB w (suc h) (suc n) K e = toB (λ m → w (suc m)) h n K e

ofK : ∀ w x h n K → Ev x (sel h n (fk K)) → Simᴵ (suc K) (w n) → Simᴵ (suc K) (upd w h x n)
ofK w x zero    zero    K a e = a
ofK w x zero    (suc n) K a e = e
ofK w x (suc h) zero    K a e = e
ofK w x (suc h) (suc n) K a e = ofK (λ m → w (suc m)) x h n K a e

ofB : ∀ w x h n K → Ev x (sel h n (fb K)) → Simᴵ K (w n) → Simᴵ K (upd w h x n)
ofB w x zero    zero    K a e = a
ofB w x zero    (suc n) K a e = e
ofB w x (suc h) zero    K a e = e
ofB w x (suc h) (suc n) K a e = ofB (λ m → w (suc m)) x h n K a e

toPrj : ∀ {w} h (π : Fᵗ) → Evt w π → Ev (w h) (prj h π)
toPrj h tz e = tt
toPrj {w} h (tk n K) e = toK w h n K e
toPrj {w} h (tb n K) e = toB w h n K e
toPrj h (a ∪ b) e = toPrj h a (proj₁ e) , toPrj h b (proj₂ e)

ofPrj : ∀ {w x} h (π : Fᵗ) → Ev x (prj h π) → Evt w π → Evt (upd w h x) π
ofPrj h tz _ e = tt
ofPrj {w} {x} h (tk n K) a e = ofK w x h n K a e
ofPrj {w} {x} h (tb n K) a e = ofB w x h n K a e
ofPrj h (a ∪ b) x e = ofPrj h a (proj₁ x) (proj₁ e) , ofPrj h b (proj₂ x) (proj₂ e)

upd-ok : ∀ w h x → Wok w → zero <ᴵ x → Wok (upd w h x)
upd-ok w zero    x ok z zero    = z
upd-ok w zero    x ok z (suc n) = ok (suc n)
upd-ok w (suc h) x ok z zero    = ok zero
upd-ok w (suc h) x ok z (suc n) = upd-ok (λ m → w (suc m)) h x (λ m → ok (suc m)) z n
```

## §2 求值的积木

`Runᵗ π`: 给世界族与目标 $i<w\,0$, 算出 `Ordˢ i`. 第 0 层的世界就是旧的 $\ell$.

```agda
Runᵗ : Fᵗ → Set
Runᵗ π = ∀ {i w} → Wok w → Evt w π → i <ᴵ w 0 → Ordˢ i

wkᵗ : ∀ {π ρ} → (∀ {w} → Evt w ρ → Evt w π) → Runᵗ π → Runᵗ ρ
wkᵗ le R ok e p = R ok (le e) p

limᵗ : ∀ {π} → (ℕ → Runᵗ π) → Runᵗ π
limᵗ F ok e p = Ord₊ˢ.lim (λ m → F m ok e p)

sucᵗ : ∀ {π} → Runᵗ π → Runᵗ π
sucᵗ R ok e p = Ord₊ˢ.lim (iter (R ok e p +ˢ_) Ord₊ˢ.zero)

limᵢᵗ : ∀ {π j} → (∀ {w} → Evt w π → j <ᴵ w 0) → (Ordˢ j → Runᵗ π) → Runᵗ π
limᵢᵗ {j = j} ac h ok ev p with <ᴵ-dec (ac ev) p
... | injᵃ (via e r) = Ord₊ˢ.limᵢ r (λ y → h (tr⁻ˢ e (outˢ (<→◃ r) y)) ok ev p)
... | injᵇ _ = Ord₊ˢ.lim (λ m → h (iter (λ x → h x ok ev (ac ev)) (Ωˢ j) m) ok ev p)
... | injᶜ _ = Ord₊ˢ.lim (λ m → h (iter (λ x → h x ok ev (ac ev)) (Ωˢ j) m) ok ev p)

ŝᵗ : ∀ {π} (c : Ordᴵ) → Runᵗ π → ((η : Ordᴵ) → c ⊑ᴵ η → Runᵗ π) → Runᵗ π
ŝᵗ c t g ok e p = Ord₊ˢ.ŝ c (t ok e p) (λ η d → g η d ok e p)

ĉᵗ : ∀ {π} (c : Ordᴵ) → Z → ((η : Ordᴵ) → c ⊑ᴵ η → Z) → Runᵗ π → ((η : Ordᴵ) → c ⊑ᴵ η → Runᵗ π) → Runᵗ π
ĉᵗ c t₀ g o₀ o ok e p = Ord₊ˢ.ĉᴸ c t₀ g (o₀ ok e p) (λ η d → o η d ok e p)
```

**闭包: 只收高度 $h$ 的地板.** 界 $B$ 只看 `prj h π`, 新世界只改第 $h$ 层. 目标在第 0 层, 所以 $h=0$ 时目标也进界 (与 `cloA` 同形), $h\ge1$ 时目标留在原来的第 0 层世界, 界的起点取 $0$. 这是与 `cloA` 唯一的不同: **别的高度的地板既不抬高界, 也不要求与新分支有公共上界.**

```agda
cloᵗ : ∀ {π} h → Runᵗ π → ((η : Ordᴵ) → Runᵗ (π ∪ tk h η)) → Runᵗ π
cloᵗ {π} zero t g {i} {w} ok ev p =
  Ord₊ˢ.ŝ (Bd B) (t ok ev p)
    (λ η e → g η {w = W η e} (upd-ok w 0 _ ok (lim 0 (proj₂ (evF B) zero)))
                 (ofPrj 0 π (liftEv (prj 0 π) (λ q → lim 0 q) (proj₁ (evF B))) ev , (λ q → lim 1 q))
                 (lim 0 (iF B)))
  where
  B = bound (prj 0 π ⊔ fk zero) (toPrj 0 π ev , (λ { zero → ok 0 ; (suc ()) })) p
  W : ∀ η → Bd B ⊑ᴵ η → Wd
  W η e = upd w 0 (Mlev (Fc B) (suc η) (FB B e))
cloᵗ {π} (suc h) t g {i} {w} ok ev p =
  Ord₊ˢ.ŝ (Bd B) (t ok ev p)
    (λ η e → g η {w = W η e} (upd-ok w (suc h) _ ok (lim 0 (proj₂ (evF B) zero)))
                 (ofPrj (suc h) π (liftEv (prj (suc h) π) (λ q → lim 0 q) (proj₁ (evF B))) ev , tkSelf η e)
                 p)
  where
  B = bound (prj (suc h) π ⊔ fk zero) (toPrj (suc h) π ev , (λ { zero → ok (suc h) ; (suc ()) })) (ok (suc h))
  W : ∀ η → Bd B ⊑ᴵ η → Wd
  W η e = upd w (suc h) (Mlev (Fc B) (suc η) (FB B e))
  tkSelf : ∀ η e → Simᴵ (suc η) (W η e (suc h))
  tkSelf η e q = subst (λ x → _ <ᴵ x) (sym′ (upd-self w (suc h) (Mlev (Fc B) (suc η) (FB B e)))) (lim 1 q)
    where
    sym′ : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
    sym′ refl = refl
```

## §3 数据树

`oΩ r ac h`: 节点在路径 $r$ 上, 证据 `ac` 说 $r$ 的每个分支都在地板之内. `oev`: 推迟的节点, 看到世界才决定形状. `ocl h t g`: 第 $h$ 层的闭包, $h=0$ 就是 [Uniform4Two](Uniform4Two.lagda.md) 的 `oclo`.

**比较的答案从哪来: 分支带证据, 判决读证据.** 节点 $r$ 的分支 $x$ 在地板 $\pi$ 里, 目标 $q$ 的分支 $\tau$ 在地板 $\chi$ 里; 环境给同一个世界 $w$; `<-dec` 由层号的 `WF` 证书与这两份字面证据算出答案. 从不测试原始树, 也没有全局的判决函数.

```agda
module _ (L : LI) (U : ∀ {k} → k <ᴸ L → Fᵗ → Set) where
  data O₊ : Fᵗ → Set where
    o0   : ∀ {π} → O₊ π
    os   : ∀ {π} → O₊ π → O₊ π
    ol   : ∀ {π} → (ℕ → O₊ π) → O₊ π
    oi   : ∀ {π j} → (∀ {w} → Evt w π → j <ᴵ w 0) → (Ordˢ j → O₊ π) → O₊ π
    oŝ   : ∀ {π} (c₀ : Ordᴵ) → O₊ π → ((η : Ordᴵ) → c₀ ⊑ᴵ η → O₊ π) → O₊ π
    oĉ   : ∀ {π} (c₀ : Ordᴵ) → Z → ((η : Ordᴵ) → c₀ ⊑ᴵ η → Z) → O₊ π → ((η : Ordᴵ) → c₀ ⊑ᴵ η → O₊ π) → O₊ π
    ocl  : ∀ {π} (h : ℕ) → O₊ π → ((η : Ordᴵ) → O₊ (π ∪ tk h η)) → O₊ π
    owk  : ∀ {π ρ} → (∀ {w} → Evt w ρ → Evt w π) → O₊ π → O₊ ρ
    oΩ   : ∀ {π k} → (∀ {w} → Evt w π → Evt w Fl₀) → (r : k <ᴸ L) → (∀ {w} → Evt w π → Adm w r) → (∀ ξ → U r ξ → O₊ (ξ ∪ π)) → O₊ π
    oev  : ∀ {π} → (∀ {w} → Wok w → Evt w π → O₊ π) → O₊ π

O  : LI → Fᵗ → Set
Us : ∀ L {k} → k <ᴸ L → Fᵗ → Set
O L π = O₊ L (Us L) π
Us (suc a) zero      ξ = O a ξ
Us (suc b) (suc r)   ξ = Us b r ξ
Us (lim f) (lim n r) ξ = Us (f n) r ξ
Us (lcl h g) (fst r)   ξ = Us (g one) r ξ
Us (lcl h g) (bra η r) ξ = Us (g η) r ξ

outU : ∀ {L k} (r : k <ᴸ L) {ξ} → Us L r ξ → O k ξ
outU zero      x = x
outU (suc r)   x = outU r x
outU (lim n r) x = outU r x
outU (fst r)   x = outU r x
outU (bra η r) x = outU r x

intoU : ∀ {L k} (r : k <ᴸ L) {ξ} → O k ξ → Us L r ξ
intoU zero      x = x
intoU (suc r)   x = intoU r x
intoU (lim n r) x = intoU r x
intoU (fst r)   x = intoU r x
intoU (bra η r) x = intoU r x

asl : ∀ {a b d w} → Evt w (a ∪ (b ∪ d)) → Evt w ((a ∪ b) ∪ d)
asl (u , (v , t)) = (u , v) , t
asr : ∀ {a b d w} → Evt w ((a ∪ b) ∪ d) → Evt w (a ∪ (b ∪ d))
asr ((u , v) , t) = u , (v , t)
swp : ∀ {a b d w} → Evt w (b ∪ (a ∪ d)) → Evt w (a ∪ (b ∪ d))
swp (u , (v , t)) = v , (u , t)
sw₃ : ∀ {a b d w} → Evt w ((a ∪ d) ∪ b) → Evt w ((a ∪ b) ∪ d)
sw₃ ((u , v) , t) = (u , t) , v
```

## §4 加法

```agda
infixl 6 _⊕_
_⊕_ : ∀ {c φ ψ} → O c φ → O c ψ → O c (φ ∪ ψ)
W ⊕ o0       = owk proj₁ W
W ⊕ os a     = os (W ⊕ a)
W ⊕ ol F     = ol (λ n → W ⊕ F n)
W ⊕ oi ac f  = oi (λ e → ac (proj₂ e)) (λ x → W ⊕ f x)
W ⊕ oŝ c₀ t g = oŝ c₀ (W ⊕ t) (λ η e → W ⊕ g η e)
W ⊕ oĉ c₀ z zg o₀ o = oĉ c₀ z zg (W ⊕ o₀) (λ η e → W ⊕ o η e)
W ⊕ ocl h t g = ocl h (W ⊕ t) (λ η → owk asr (W ⊕ g η))
W ⊕ owk le t = owk (λ e → proj₁ e , le (proj₂ e)) (W ⊕ t)
W ⊕ oΩ fe r ac h = oΩ (λ e → fe (proj₂ e)) r (λ e → ac (proj₂ e)) (λ ξ z → owk swp (W ⊕ h ξ z))
W ⊕ oev f = oev (λ ok e → W ⊕ f ok (proj₂ e))
```

## §5 嵌入: 一步, 地板只在 `lcl` 的分支上加一项

`Dn a b`: $b$ 的一个直接下层. `dnF`: 嵌入要加的地板. 只有分支 $\eta$ 才要 $\eta<w\,h$; 第一支不要. **这一项的高度是 $h$, 里面的闭包在别的高度上就不看它.** 这就是 `noAll` 的修正.

```agda
data Dn : LI → LI → Set where
  ds : ∀ {k} → Dn k (suc k)
  dl : ∀ {f} n → Dn (f n) (lim f)
  df : ∀ {h g} → Dn (g one) (lcl h g)
  db : ∀ {h g} η → Dn (g η) (lcl h g)

dnF : ∀ {a b} → Dn a b → Fᵗ
dnF ds     = tz
dnF (dl n) = tz
dnF df     = tz
dnF (db {h} η) = tk h η

pl : ∀ {a b} → Dn a b → ∀ {k} → k <ᴸ a → k <ᴸ b
pl ds     r = suc r
pl (dl n) r = lim n r
pl df     r = fst r
pl (db η) r = bra η r

cvU : ∀ {a b} (d : Dn a b) {k} (r : k <ᴸ a) {ξ} → Us b (pl d r) ξ → Us a r ξ
cvU ds     r x = x
cvU (dl n) r x = x
cvU df     r x = x
cvU (db η) r x = x

admD : ∀ {a b} (d : Dn a b) {k} (r : k <ᴸ a) {w} → Evt w (dnF d) → Adm w r → Adm w (pl d r)
admD ds     r e a = a
admD (dl n) r e a = a
admD df     r e a = a
admD (db η) r e a = e zero , a

ι : ∀ {a b} (d : Dn a b) {π} → O a π → O b (π ∪ dnF d)
ι d o0 = o0
ι d (os a) = os (ι d a)
ι d (ol F) = ol (λ n → ι d (F n))
ι d (oi ac f) = oi (λ e → ac (proj₁ e)) (λ x → ι d (f x))
ι d (oŝ c₀ t g) = oŝ c₀ (ι d t) (λ η e → ι d (g η e))
ι d (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (ι d o₀) (λ η e → ι d (o η e))
ι d (ocl h t g) = ocl h (ι d t) (λ η → owk sw₃ (ι d (g η)))
ι d (owk le t) = owk (λ e → le (proj₁ e) , proj₂ e) (ι d t)
ι d (oΩ fe r ac h) = oΩ (λ e → fe (proj₁ e)) (pl d r) (λ e → admD d r (proj₂ e) (ac (proj₁ e))) (λ ξ z → owk asl (ι d (h ξ (cvU d r z))))
ι d (oev f) = oev (λ ok e → ι d (f ok (proj₁ e)))
```

## §6 沿 `≈` 搬运

`RestrO`: 路径搬到 `≈` 的另一边, 输入的树搬回来. 与 [Uniform4Two](Uniform4Two.lagda.md) 的 `resO` 同形, 多一项可容许性的转移.

```agda
record RestrO {k a : LI} (r : k <ᴸ a) (b : LI) : Set where
  constructor restrO
  field
    {repO} : LI
    eqO    : k ≈ repO
    ltO    : repO <ᴸ b
    trfO   : ∀ w → Adm w r → Adm w ltO
    backO  : ∀ {ξ} → O repO ξ → O k ξ
open RestrO public

trO   : ∀ {a b π} → a ≈ b → O a π → O b π
tr⁻O  : ∀ {a b π} → a ≈ b → O b π → O a π
resO  : ∀ {k a b} (r : k <ᴸ a) → a ≈ b → RestrO r b
res⁻O : ∀ {k a b} (r : k <ᴸ b) → a ≈ b → RestrO r a

trO e o0 = o0
trO e (os a) = os (trO e a)
trO e (ol F) = ol (λ n → trO e (F n))
trO e (oi ac f) = oi ac (λ x → trO e (f x))
trO e (oŝ c₀ t g) = oŝ c₀ (trO e t) (λ η d → trO e (g η d))
trO e (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (trO e o₀) (λ η d → trO e (o η d))
trO e (ocl h t g) = ocl h (trO e t) (λ η → trO e (g η))
trO e (owk le t) = owk le (trO e t)
trO e (oΩ fe q ac h) = oΩ fe (ltO (resO q e)) (λ v → trfO (resO q e) _ (ac v)) (λ ξ z → trO e (h ξ (intoU q (backO (resO q e) (outU (ltO (resO q e)) z)))))
trO e (oev f) = oev (λ ok d → trO e (f ok d))

tr⁻O e o0 = o0
tr⁻O e (os a) = os (tr⁻O e a)
tr⁻O e (ol F) = ol (λ n → tr⁻O e (F n))
tr⁻O e (oi ac f) = oi ac (λ x → tr⁻O e (f x))
tr⁻O e (oŝ c₀ t g) = oŝ c₀ (tr⁻O e t) (λ η d → tr⁻O e (g η d))
tr⁻O e (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (tr⁻O e o₀) (λ η d → tr⁻O e (o η d))
tr⁻O e (ocl h t g) = ocl h (tr⁻O e t) (λ η → tr⁻O e (g η))
tr⁻O e (owk le t) = owk le (tr⁻O e t)
tr⁻O e (oΩ fe q ac h) = oΩ fe (ltO (res⁻O q e)) (λ v → trfO (res⁻O q e) _ (ac v)) (λ ξ z → tr⁻O e (h ξ (intoU q (backO (res⁻O q e) (outU (ltO (res⁻O q e)) z)))))
tr⁻O e (oev f) = oev (λ ok d → tr⁻O e (f ok d))

resO zero      (s≈ e) = restrO e zero (λ _ _ → tt) (tr⁻O e)
resO (suc r)   (s≈ e) with resO r e
... | restrO d l t b = restrO d (suc l) t b
resO (lim n r) (l≈ h) with resO r (h n)
... | restrO d l t b = restrO d (lim n l) t b
resO (fst r)   (o≈ _ h) with resO r (h one one (Lv.≅ᴵ-refl one))
... | restrO d l t b = restrO d (fst l) t b
resO (bra η r) (o≈ x h) with resO r (h η η (Lv.≅ᴵ-refl η))
... | restrO d l t b = restrO d (bra η l) (λ w u → subst (λ y → η <ᴵ w y) x (proj₁ u) , t w (proj₂ u)) b

res⁻O zero      (s≈ e) = restrO (≈-sym e) zero (λ _ _ → tt) (trO e)
res⁻O (suc r)   (s≈ e) with res⁻O r e
... | restrO d l t b = restrO d (suc l) t b
res⁻O (lim n r) (l≈ h) with res⁻O r (h n)
... | restrO d l t b = restrO d (lim n l) t b
res⁻O (fst r)   (o≈ _ h) with res⁻O r (h one one (Lv.≅ᴵ-refl one))
... | restrO d l t b = restrO d (fst l) t b
res⁻O (bra η r) (o≈ x h) with res⁻O r (h η η (Lv.≅ᴵ-refl η))
... | restrO d l t b = restrO d (bra η l) (λ w u → subst (λ y → η <ᴵ w y) (sym′ x) (proj₁ u) , t w (proj₂ u)) b
  where
  sym′ : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
  sym′ refl = refl
```

## §7 尾巴与 $\Omega$

`tl`: 可数层的值读进树. 与 [Uniform4Two](Uniform4Two.lagda.md) 同形, 地板 `floᵗ` 在第 0 层.

```agda
floᵗ : Ordᴵ → Fᵗ
floᵗ zero      = tz
floᵗ (suc k)   = tk 0 k
floᵗ (lim f s) = tb 0 (lim f s)

cvᵗ : ∀ k {w} → Evt w (floᵗ k) → Simᴵ k (w 0)
cvᵗ zero      _ ()
cvᵗ (suc k)   e = e
cvᵗ (lim f s) e = e

toᵗ : ∀ k {w} → Simᴵ k (w 0) → Evt w (floᵗ k)
toᵗ zero      σ = tt
toᵗ (suc k)   σ = σ
toᵗ (lim f s) σ = σ

tl : ∀ {c k} (π : Fᵗ) → (∀ {w} → Evt w π → Simᴵ k (w 0)) → Ordˢ k → O c π
tl π cv Ord₊ˢ.zero = o0
tl π cv (Ord₊ˢ.suc a) = os (tl π cv a)
tl π cv (Ord₊ˢ.lim f) = ol (λ n → tl π cv (f n))
tl π cv (Ord₊ˢ.limᵢ q f) = oi (λ e → cv e q) (λ x → tl π cv (f (intoˢ (<→◃ q) x)))
tl {k = suc k′} π cv (Ord₊ˢ.up zero x) = owk (λ v → toᵗ k′ (λ q → cv v (suc q))) (tl (floᵗ k′) (cvᵗ k′) x)
tl {k = lim f s} π cv (Ord₊ˢ.up (self n) x) = owk (λ v → toᵗ (f n) (λ q → cv v (lim n q))) (tl (floᵗ (f n)) (cvᵗ (f n)) x)
tl {k = zero} π cv (Ord₊ˢ.ŝ c₀ t₀ g) = oĉ c₀ (toZ t₀) (λ η e → toZ (g η e)) (tl π cv t₀) (λ η e → tl π cv (g η e))
tl {k = suc _} π cv (Ord₊ˢ.ŝ c₀ t₀ g) = oŝ c₀ (tl π cv t₀) (λ η e → tl π cv (g η e))
tl {k = lim _ _} π cv (Ord₊ˢ.ŝ c₀ t₀ g) = oŝ c₀ (tl π cv t₀) (λ η e → tl π cv (g η e))
tl π cv (Ord₊ˢ.ĉᴸ c₀ t₀ g o₀ o) = oĉ c₀ t₀ g (tl π cv o₀) (λ η e → tl π cv (o η e))

idF : ∀ {w} → Evt w Fl₀ → Evt w Fl₀
idF e = e

pt : ∀ {π w} → Evt w π → Evt w (π ∪ tz)
pt e = e , tt

Ω̇ : ∀ L → O L Fl₀
Ω̇ zero = os o0
Ω̇ base = ocl 0 (tl Fl₀ (λ e q → proj₂ e q) (Ωˢ (suc zero))) (λ η → tl (Fl₀ ∪ tk 0 η) (λ e q → proj₂ e (suc q)) (Ωˢ η))
Ω̇ (suc k) = oΩ idF zero (λ _ → tt) (λ ξ z → owk proj₁′ (ι ds z))
  where
  proj₁′ : ∀ {ξ w} → Evt w (ξ ∪ Fl₀) → Evt w (ξ ∪ tz)
  proj₁′ e = proj₁ e , tt
Ω̇ (lim f) = ol (λ n → owk pt (ι (dl n) (Ω̇ (f n))))
Ω̇ (lcl h g) = ocl h (owk pt (ι df (Ω̇ (g one)))) (λ η → ι (db η) (Ω̇ (g η)))
```

## §8 折叠

`Cf c`: 层号的证书. 折叠对它参数化, 不存进树. 目标 $q$ 带自己的地板 $\chi$. 节点与目标的比较推迟到 `oev`, 用 `<-dec`.

```agda
Cf : LI → Set
Cf c = WF c × (c ≈ c)

repᵒ : ∀ {c π} → O c π → ℕ → O c π
repᵒ x zero          = o0
repᵒ x (suc zero)    = x
repᵒ x (suc (suc m)) = owk (λ e → e , e) (repᵒ x (suc m) ⊕ x)

chainᵒ : ∀ {k π} → (∀ {w} → Evt w π → Evt w Fl₀) → (O k π → O k π) → ℕ → O k π
chainᵒ {k} fe f zero    = owk fe (Ω̇ k)
chainᵒ fe f (suc n) = f (chainᵒ fe f n)

module Fold {c : LI} (cf : Cf c) where
  ψᵒ : ∀ {t χ} (q : t <ᴸ c) → (∀ {w} → Evt w χ → Evt w Fl₀) → (∀ {w} → Evt w χ → Adm w q) → ∀ {π} → O c π → O t (χ ∪ π)
  ψΩ : ∀ {t χ k π} (q : t <ᴸ c) (fl : ∀ {w} → Evt w χ → Evt w Fl₀) (aq : ∀ {w} → Evt w χ → Adm w q)
       (fe : ∀ {w} → Evt w π → Evt w Fl₀) (r : k <ᴸ c) (ac : ∀ {w} → Evt w π → Adm w r) (h : ∀ ξ → Us c r ξ → O c (ξ ∪ π)) →
       Tri r q → O t (χ ∪ π)
  chR : ∀ {χ k π} (fl : ∀ {w} → Evt w χ → Evt w Fl₀) (fe : ∀ {w} → Evt w π → Evt w Fl₀) (r : k <ᴸ c) (ac : ∀ {w} → Evt w π → Adm w r) (h : ∀ ξ → Us c r ξ → O c (ξ ∪ π)) → ℕ → O k (χ ∪ π)

  ψᵒ {t} q fl aq o0 = owk (λ e → fl (proj₁ e)) (Ω̇ t)
  ψᵒ q fl aq (os a) = ol (repᵒ (ψᵒ q fl aq a))
  ψᵒ q fl aq (ol F) = ol (λ n → ψᵒ q fl aq (F n))
  ψᵒ q fl aq (oi ac f) = oi (λ e → ac (proj₂ e)) (λ x → ψᵒ q fl aq (f x))
  ψᵒ q fl aq (oŝ c₀ x g) = oŝ c₀ (ψᵒ q fl aq x) (λ η e → ψᵒ q fl aq (g η e))
  ψᵒ q fl aq (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (ψᵒ q fl aq o₀) (λ η e → ψᵒ q fl aq (o η e))
  ψᵒ q fl aq (ocl h x g) = ocl h (ψᵒ q fl aq x) (λ η → owk asr (ψᵒ q fl aq (g η)))
  ψᵒ q fl aq (owk le x) = owk (λ e → proj₁ e , le (proj₂ e)) (ψᵒ q fl aq x)
  ψᵒ q fl aq (oev f) = oev (λ ok e → ψᵒ q fl aq (f ok (proj₂ e)))
  ψᵒ q fl aq (oΩ fe r ac h) =
    oev (λ {w} ok e → ψΩ q fl aq fe r ac h (<-dec (proj₁ cf) (proj₂ cf) r q w ok (ac (proj₂ e)) (aq (proj₁ e))))

  ψΩ q fl aq fe r ac h (tlt (viaᴸ d s u)) =
    oΩ (λ e → fl (proj₁ e)) s (λ {w} e → u w (ac (proj₂ e))) (λ ξ y → owk swp (ψᵒ q fl aq (h ξ (intoU r (tr⁻O d (outU s y))))))
  ψΩ {χ = χ} {π = π} q fl aq fe r ac h (tgt _) = ol (λ n → owk (λ e → proj₁ e , (e , proj₂ e)) (ψᵒ q fl aq (h (χ ∪ π) (intoU r (chR fl fe r ac h n)))))
  ψΩ {χ = χ} {π = π} q fl aq fe r ac h (teq _) = ol (λ n → owk (λ e → proj₁ e , (e , proj₂ e)) (ψᵒ q fl aq (h (χ ∪ π) (intoU r (chR fl fe r ac h n)))))

  chR {χ} {k} {π} fl fe r ac h = chainᵒ (λ e → fl (proj₁ e)) (λ z → owk (λ e → proj₂ e , (e , proj₂ e)) (ψᵒ r fe ac (h (χ ∪ π) (intoU r z))))

  ψ̄ : ∀ {π} → O c π → Runᵗ π
  ψ̄ o0 ok e {- ∅ -} p = Ωˢ _
  ψ̄ (os a) = sucᵗ (ψ̄ a)
  ψ̄ (ol F) = limᵗ (λ n → ψ̄ (F n))
  ψ̄ (oi ac f) = limᵢᵗ ac (λ x → ψ̄ (f x))
  ψ̄ (oŝ c₀ t g) = ŝᵗ c₀ (ψ̄ t) (λ η e → ψ̄ (g η e))
  ψ̄ (oĉ c₀ z zg o₀ o) = ĉᵗ c₀ z zg (ψ̄ o₀) (λ η e → ψ̄ (o η e))
  ψ̄ (ocl h t g) = cloᵗ h (ψ̄ t) (λ η → ψ̄ (g η))
  ψ̄ (owk le x) = wkᵗ le (ψ̄ x)
  ψ̄ {π} (oΩ fe r ac h) =
    limᵗ (λ n → wkᵗ (λ v → v , v)
           (ψ̄ (h π (intoU r (chainᵒ fe (λ z → owk (λ v → v , (v , v)) (ψᵒ r fe ac (h π (intoU r z)))) n)))))
  ψ̄ (oev f) ok ev p = ψ̄ (f ok ev) ok ev p

-- $\psi_0(\Omega_L)$: 任何带证书的层号
T : (L : LI) → Cf L → Runᵗ Fl₀
T L cf = Fold.ψ̄ cf (Ω̇ L)

w₀ : Wd
w₀ _ = suc zero

ok₀ : Wok w₀
ok₀ _ = zero

ev₀ : Evt w₀ Fl₀
ev₀ = tt , (λ q → q)

-- 封闭的计值
T₀ : (L : LI) → Cf L → Ordˢ zero
T₀ L cf = T L cf ok₀ ev₀ zero
```
