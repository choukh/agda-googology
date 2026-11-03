# 带守卫的层号上的树 (定义)

> 不含记号. 结论写在 [LvGuard](LvGuard.lagda.md). 与 [LvKeyTree](LvKeyTree.lagda.md) 同骨架, 四处不同:
>
> 1. **树里没有世界.** 地板 `Fl` 只记活的分支变量 (帧 `Frm`), 不记证据. 节点的路径可容许是静态的: `Adm (cov π) r`.
> 2. **折叠是立刻的.** `ψ` 带表 $E$ 与每个帧的状态 `St`, 没有 `oev`. 目标在闭包之下时闭包立刻落成字面的 `oŝ`, 输出不带这个帧. 这是 `noW` 的修法的前半. 目标在闭包之上时闭包保留, 帧搬到输出 (`ab`).
> 3. **守卫是紧的: 只看同键的帧与目标的分支.** 这只修了 `noW` 的来源之一, `tight` 没有写 (见 [LvGuard](LvGuard.lagda.md)).
> 4. **层没有高度.** 可数层与不可数层是同一种节点, 目标 0 是 `t0`. 没有 `oi`, `oc₀`, `Ordˢ`, `base`.
>
> 证据缺失的分支 (节点的帧没有证据却要比较, 或要搬到输出却没有映射) 给 `o0`. 这些分支走不走得到是证书的事, 这里没有证. 所以这是定义, 不是定理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvGuardTree where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.Level using
  (Ordᴵ; suc; _<ᴵ_; _≅ᴵ_; _⊑ᴵ_; _≺ᴵ_; via; Simᴵ; ⊑ᴵ-trans; ≅ᴵ-refl; ≅ᴵ-sym; Sim→⊑ᴵ; <ᴵ-trans)
import OCF.Align.Level as Lvl
open import OCF.Align.Prefix using (Z)
open import OCF.Align.Symbolic using (Mlev)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; fb; _⊔_; Ev; bound; Bd; Fc; evF; iF; FB; liftEv; Top; FM)
open import OCF.Align.InaccFloorBase using (≺→⊑ᴵ; ≅→⊑ᴵ)
open import OCF.Align.LvGuardBase
open Lv Dom₀
open import OCF.Align.LvGuardTab Dom₀ using (kdec; Dec′; _⊙_; adm⊙; toCp; admTo)
```

## §1 静态的可容许性

```agda
adm-wk : ∀ {π ρ a b} → Wk π ρ → (r : a < b) → Adm (cov π) r → Adm (cov ρ) r
adm-wk w zero _ = tt
adm-wk w (suc r) a = adm-wk w r a
adm-wk w (lim n r) a = adm-wk w r a
adm-wk w (fst r) a = adm-wk w r a
adm-wk w (bra η e r) ((c₁ , t₁ , g₁ , e₁ , m , k) , a) = (c₁ , t₁ , g₁ , e₁ , w m , k) , adm-wk w r a

admC-wk : ∀ {π ρ a b} → Wk π ρ → (r : Cp a b) → AdmC (cov π) r → AdmC (cov ρ) r
admC-wk w self _ = tt
admC-wk w (suc r) a = admC-wk w r a
admC-wk w (lim n r) a = admC-wk w r a
admC-wk w (fst r) a = admC-wk w r a
admC-wk w (bra η e r) ((c₁ , t₁ , g₁ , e₁ , m , k) , a) = (c₁ , t₁ , g₁ , e₁ , w m , k) , admC-wk w r a
```

## §2 第 0 层的值, 数据树

```agda
module _ (L : LG) (U : ∀ {k} → k < L → Fl → Set) where
  data O₊ : Fl → Set where
    o0  : ∀ {π} → O₊ π
    os  : ∀ {π} → O₊ π → O₊ π
    ol  : ∀ {π} → (ℕ → O₊ π) → O₊ π
    oŝ  : ∀ {π} (c₀ : Ordᴵ) → O₊ π → ((η : Ordᴵ) → c₀ ⊑ᴵ η → O₊ π) → O₊ π
    oĉ  : ∀ {π} (c₀ : Ordᴵ) → Z → ((η : Ordᴵ) → c₀ ⊑ᴵ η → Z) → O₊ π → ((η : Ordᴵ) → c₀ ⊑ᴵ η → O₊ π) → O₊ π
    owk : ∀ {π ρ} → Wk π ρ → O₊ π → O₊ ρ
    oΩ  : ∀ {π k} (r : k < L) → Adm (cov π) r → (∀ ξ → U r ξ → O₊ (ξ ∪ π)) → O₊ π
    ocl : ∀ {π c₁ t₁ g₁ c₂ t₂ g₂} (P : Cp (lc c₂ t₂ g₂) L) → (lc c₂ t₂ g₂ ≈ lc c₁ t₁ g₁ ⊎ lc c₂ t₂ g₂ ≡ lc c₁ t₁ g₁) → AdmC (cov π) P →
          O₊ π → (∀ η e → O₊ (π ∪ tk (frm c₁ t₁ g₁ η e))) → O₊ π

O  : LG → Fl → Set
Us : ∀ L {k} → k < L → Fl → Set
O L π = O₊ L (Us L) π
Us (suc a) zero        ξ = O a ξ
Us (suc b) (suc r)     ξ = Us b r ξ
Us (lim f) (lim n r)   ξ = Us (f n) r ξ
Us (lc c t g) (fst r)  ξ = Us t r ξ
Us (lc c t g) (bra η e r) ξ = Us (g η e) r ξ

outU : ∀ {L k} (r : k < L) {ξ} → Us L r ξ → O k ξ
outU zero        x = x
outU (suc r)     x = outU r x
outU (lim n r)   x = outU r x
outU (fst r)     x = outU r x
outU (bra η e r) x = outU r x

intoU : ∀ {L k} (r : k < L) {ξ} → O k ξ → Us L r ξ
intoU zero        x = x
intoU (suc r)     x = intoU r x
intoU (lim n r)   x = intoU r x
intoU (fst r)     x = intoU r x
intoU (bra η e r) x = intoU r x

-- 第 0 层: 读成 Z. 节点与闭包在第 0 层没有
rdZ : ∀ {π} → O zero π → Z
rdZ o0 = Z.zero
rdZ (os a) = Z.suc (rdZ a)
rdZ (ol F) = Z.lim (λ n → rdZ (F n))
rdZ (oŝ c₀ t g) = Z.ĉᴸ c₀ (rdZ t) (λ η e → rdZ (g η e)) (rdZ t) (λ η e → rdZ (g η e))
rdZ (oĉ c₀ z zg o₀ o) = Z.ĉᴸ c₀ z zg (rdZ o₀) (λ η e → rdZ (o η e))
rdZ (owk w x) = rdZ x
rdZ (oΩ () _ _)
rdZ (ocl () _ _ _ _)
```

## §3 加法, 嵌入, 搬运

```agda
asl : ∀ {a b d} → Wk ((a ∪ b) ∪ d) (a ∪ (b ∪ d))
asl (ml (ml m)) = ml m
asl (ml (mr m)) = mr (ml m)
asl (mr m) = mr (mr m)

asr : ∀ {a b d} → Wk (a ∪ (b ∪ d)) ((a ∪ b) ∪ d)
asr (ml m) = ml (ml m)
asr (mr (ml m)) = ml (mr m)
asr (mr (mr m)) = mr m

swp : ∀ {a b d} → Wk (b ∪ (a ∪ d)) (a ∪ (b ∪ d))
swp (ml m) = mr (ml m)
swp (mr (ml m)) = ml m
swp (mr (mr m)) = mr (mr m)

sw₃ : ∀ {a b d} → Wk ((a ∪ d) ∪ b) ((a ∪ b) ∪ d)
sw₃ (ml (ml m)) = ml (ml m)
sw₃ (ml (mr m)) = mr m
sw₃ (mr m) = ml (mr m)

infixl 6 _⊕_
_⊕_ : ∀ {k φ ψ} → O k φ → O k ψ → O k (φ ∪ ψ)
W ⊕ o0       = owk ml W
W ⊕ os a     = os (W ⊕ a)
W ⊕ ol F     = ol (λ n → W ⊕ F n)
_⊕_ {k = zero} W (oŝ c₀ t g) = oĉ c₀ (rdZ t) (λ η e → rdZ (g η e)) (W ⊕ t) (λ η e → W ⊕ g η e)
W ⊕ oŝ c₀ t g = oŝ c₀ (W ⊕ t) (λ η e → W ⊕ g η e)
W ⊕ oĉ c₀ z zg o₀ o = oĉ c₀ z zg (W ⊕ o₀) (λ η e → W ⊕ o η e)
W ⊕ owk w t = owk (λ { (ml m) → ml m ; (mr m) → mr (w m) }) (W ⊕ t)
W ⊕ oΩ r cv h = oΩ r (adm-wk mr r cv) (λ ξ z → owk swp (W ⊕ h ξ z))
W ⊕ ocl P k cv t g = ocl P k (admC-wk mr P cv) (W ⊕ t) (λ η e → owk asr (W ⊕ g η e))

data Dn : LG → LG → Set where
  ds : ∀ {k} → Dn k (suc k)
  dl : ∀ {f} n → Dn (f n) (lim f)
  df : ∀ {c t g} → Dn t (lc c t g)
  db : ∀ {c t g} η e → Dn (g η e) (lc c t g)

dnF : ∀ {a b} → Dn a b → Fl
dnF ds       = tz
dnF (dl n)   = tz
dnF df       = tz
dnF (db {c} {t} {g} η e) = tk (frm c t g η e)

pl : ∀ {a b} → Dn a b → ∀ {k} → k < a → k < b
pl ds         r = suc r
pl (dl n)     r = lim n r
pl df         r = fst r
pl (db η e)   r = bra η e r

plC : ∀ {a b} → Dn a b → ∀ {k} → Cp k a → Cp k b
plC ds         r = suc r
plC (dl n)     r = lim n r
plC df         r = fst r
plC (db η e)   r = bra η e r

cvU : ∀ {a b} (d : Dn a b) {k} (r : k < a) {ξ} → Us b (pl d r) ξ → Us a r ξ
cvU ds         r x = x
cvU (dl n)     r x = x
cvU df         r x = x
cvU (db η e)   r x = x

admD : ∀ {a b} (d : Dn a b) {π k} (r : k < a) → Adm (cov π) r → Adm (cov (π ∪ dnF d)) (pl d r)
admD ds       r a = adm-wk ml r a
admD (dl n)   r a = adm-wk ml r a
admD df       r a = adm-wk ml r a
admD (db {c} {t} {g} η e) r a = (c , t , g , e , mr hr , inj₂ refl) , adm-wk ml r a

admDC : ∀ {a b} (d : Dn a b) {π k} (r : Cp k a) → AdmC (cov π) r → AdmC (cov (π ∪ dnF d)) (plC d r)
admDC ds       r a = admC-wk ml r a
admDC (dl n)   r a = admC-wk ml r a
admDC df       r a = admC-wk ml r a
admDC (db {c} {t} {g} η e) r a = (c , t , g , e , mr hr , inj₂ refl) , admC-wk ml r a

ι : ∀ {a b} (d : Dn a b) {π} → O a π → O b (π ∪ dnF d)
ι d o0 = o0
ι d (os a) = os (ι d a)
ι d (ol F) = ol (λ n → ι d (F n))
ι {a = zero} d (oŝ c₀ t g) = oĉ c₀ (rdZ t) (λ η e → rdZ (g η e)) (ι d t) (λ η e → ι d (g η e))
ι d (oŝ c₀ t g) = oŝ c₀ (ι d t) (λ η e → ι d (g η e))
ι d (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (ι d o₀) (λ η e → ι d (o η e))
ι d (owk w t) = owk (λ { (ml m) → ml (w m) ; (mr m) → mr m }) (ι d t)
ι d (oΩ r cv h) = oΩ (pl d r) (admD d r cv) (λ ξ z → owk asl (ι d (h ξ (cvU d r z))))
ι d (ocl P k cv t g) = ocl (plC d P) k (admDC d P cv) (ι d t) (λ η e → owk sw₃ (ι d (g η e)))

record RestrO {k a : LG} (r : k < a) (b : LG) : Set where
  constructor restrO
  field
    {repO} : LG
    eqO    : k ≈ repO
    ltO    : repO < b
    trfO   : ∀ E → Adm E r → Adm E ltO
    backO  : ∀ {ξ} → O repO ξ → O k ξ
open RestrO public

lkT : ∀ {a b c} → a ≈ b → (b ≈ c ⊎ b ≡ c) → (a ≈ c ⊎ a ≡ c)
lkT e (inj₁ d) = inj₁ (≈-trans e d)
lkT e (inj₂ refl) = inj₁ e

trO   : ∀ {a b π} → a ≈ b → O a π → O b π
tr⁻O  : ∀ {a b π} → a ≈ b → O b π → O a π
resO  : ∀ {k a b} (r : k < a) → a ≈ b → RestrO r b
res⁻O : ∀ {k a b} (r : k < b) → a ≈ b → RestrO r a

trO e o0 = o0
trO e (os a) = os (trO e a)
trO e (ol F) = ol (λ n → trO e (F n))
trO e (oŝ c₀ t g) = oŝ c₀ (trO e t) (λ η d → trO e (g η d))
trO e (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (trO e o₀) (λ η d → trO e (o η d))
trO e (owk w t) = owk w (trO e t)
trO e (oΩ q ac h) = oΩ (ltO (resO q e)) (trfO (resO q e) _ ac) (λ ξ z → trO e (h ξ (intoU q (backO (resO q e) (outU (ltO (resO q e)) z)))))
trO e (ocl P k cv t g) with ≈-moveᴷ e P
... | viaᴷ d P′ u = ocl P′ (lkT (≈-sym d) k) (u _ cv) (trO e t) (λ η d′ → trO e (g η d′))

tr⁻O e o0 = o0
tr⁻O e (os a) = os (tr⁻O e a)
tr⁻O e (ol F) = ol (λ n → tr⁻O e (F n))
tr⁻O e (oŝ c₀ t g) = oŝ c₀ (tr⁻O e t) (λ η d → tr⁻O e (g η d))
tr⁻O e (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (tr⁻O e o₀) (λ η d → tr⁻O e (o η d))
tr⁻O e (owk w t) = owk w (tr⁻O e t)
tr⁻O e (oΩ q ac h) = oΩ (ltO (res⁻O q e)) (trfO (res⁻O q e) _ ac) (λ ξ z → tr⁻O e (h ξ (intoU q (backO (res⁻O q e) (outU (ltO (res⁻O q e)) z)))))
tr⁻O e (ocl P k cv t g) with ≈-moveᴷ (≈-sym e) P
... | viaᴷ d P′ u = ocl P′ (lkT (≈-sym d) k) (u _ cv) (tr⁻O e t) (λ η d′ → tr⁻O e (g η d′))

resO zero      (s≈ e) = restrO e zero (λ _ _ → tt) (tr⁻O e)
resO (suc r)   (s≈ e) with resO r e
... | restrO d l t b = restrO d (suc l) t b
resO (lim n r) (l≈ h) with resO r (h n)
... | restrO d l t b = restrO d (lim n l) t b
resO (fst r)   (o≈ d′ e h) with resO r e
... | restrO d l t b = restrO d (fst l) t b
resO (bra η e₁ r) (o≈ d′ e h) with resO r (h η e₁ η (conv d′ e₁) (≅ᴰ-refl η))
... | restrO d l t b = restrO d (bra η (conv d′ e₁) l) (λ E u → Bel-resp {E} (o≈ d′ e h) (proj₁ u) , t E (proj₂ u)) b

res⁻O zero      (s≈ e) = restrO (≈-sym e) zero (λ _ _ → tt) (trO e)
res⁻O (suc r)   (s≈ e) with res⁻O r e
... | restrO d l t b = restrO d (suc l) t b
res⁻O (lim n r) (l≈ h) with res⁻O r (h n)
... | restrO d l t b = restrO d (lim n l) t b
res⁻O (fst r)   (o≈ d′ e h) with res⁻O r e
... | restrO d l t b = restrO d (fst l) t b
res⁻O (bra η e₁ r) (o≈ d′ e h) with res⁻O r (h η (conv (≅ᴰ-sym d′) e₁) η e₁ (≅ᴰ-refl η))
... | restrO d l t b = restrO d (bra η (conv (≅ᴰ-sym d′) e₁) l) (λ E u → Bel-resp {E} (≈-sym (o≈ d′ e h)) (proj₁ u) , t E (proj₂ u)) b
```

## §4 $\Omega$

`Ω̇ k`: 没有地板, 没有下标的高度. 闭包的第一支是第一位置, 分支 $\eta$ 下面多一个帧.

```agda
Ω̇ : ∀ k → O k tz
Ω̇ zero = os o0
Ω̇ (suc k) = oΩ zero tt (λ ξ z → owk (λ { (ml m) → ml m ; (mr ()) }) (ι ds z))
Ω̇ (lim f) = ol (λ n → owk (λ { (ml ()) ; (mr ()) }) (ι (dl n) (Ω̇ (f n))))
Ω̇ (lc c t g) = ocl self (inj₂ refl) tt (owk (λ { (ml ()) ; (mr ()) }) (ι df (Ω̇ t))) (λ η e → ι (db η e) (Ω̇ (g η e)))

repᵒ : ∀ {k π} → O k π → ℕ → O k π
repᵒ x zero          = o0
repᵒ x (suc zero)    = x
repᵒ x (suc (suc m)) = owk (λ { (ml m) → m ; (mr m) → m }) (repᵒ x (suc m) ⊕ x)
```

## §5 折叠的状态

`Evd`: 帧在表里的证据, 带这个节点在 $c$ 里的一个位置 (`kdec` 要). `Ab`: 帧在输出里的映射 (闭包保留时). 一个帧可以两样都有 (上升时), 也可以都没有 (这时比较给 `cj`, 输出 `o0`).

```agda
lkC : ∀ {a b c} → (a ≈ b ⊎ a ≡ b) → (b ≈ c ⊎ b ≡ c) → (a ≈ c ⊎ a ≡ c)
lkC (inj₁ d) k = lkT d k
lkC (inj₂ refl) k = k

lk→≈ : ∀ {a b} → a ≈ a → (a ≈ b ⊎ a ≡ b) → a ≈ b
lk→≈ s (inj₁ d) = d
lk→≈ s (inj₂ refl) = s

oc≅ : ∀ {c t g c′ t′ g′} → lc c t g ≈ lc c′ t′ g′ → c ≅ᴰ c′
oc≅ (o≈ d e h) = d

selfC : ∀ {a c} → c ≈ c → Cp a c → a ≈ a
selfC e self = e
selfC (s≈ e) (suc p) = selfC e p
selfC (l≈ h) (lim n p) = selfC (h n) p
selfC (o≈ d e h) (fst p) = selfC e p
selfC (o≈ d e h) (bra η e₁ p) = selfC (h η e₁ η e₁ (≅ᴰ-refl η)) p

module Fold (c : LG) (wf : WFˢ c) (sf : c ≈ c) where
  record Evd (E : Ents) (f : Frm) : Set where
    constructor evd
    field
      {c₃} : Ordᴵ
      {t₃} : LG
      {g₃} : (η : Ordᴵ) → c₃ ⊑ᴵ η → LG
      Pf   : Cp (lc c₃ t₃ g₃) c
      adf  : AdmC (tab E) Pf
      lkf  : lc c₃ t₃ g₃ ≈ κ f
      blf  : Bel′ E (κ f) (fη f)

  record Ab (ρ : Fl) (f : Frm) : Set where
    constructor ab
    field
      {c₄} : Ordᴵ
      {t₄} : LG
      {g₄} : (η : Ordᴵ) → c₄ ⊑ᴵ η → LG
      {e₄} : c₄ ⊑ᴵ fη f
      mem₄ : Mem ρ (frm c₄ t₄ g₄ (fη f) e₄)
      lk₄  : κ f ≈ lc c₄ t₄ g₄ ⊎ κ f ≡ lc c₄ t₄ g₄

  record Fs (E : Ents) (ρ : Fl) (f : Frm) : Set where
    constructor fs
    field
      ev  : Maybe (Evd E f)
      abm : Maybe (Ab ρ f)
  open Fs public

  St : Ents → Fl → Fl → Set
  St E ρ π = ∀ {f} → Mem π f → Fs E ρ f

  mapFs : ∀ {E ρ ρ′ f} → Wk ρ ρ′ → Fs E ρ f → Fs E ρ′ f
  mapFs w (fs e nothing) = fs e nothing
  mapFs w (fs e (just (ab m k))) = fs e (just (ab (w m) k))

  stξ : ∀ {E ρ π} ξ → St E ρ π → St E (ξ ∪ ρ) (ξ ∪ π)
  stξ ξ st (ml m) = fs nothing (just (ab (ml m) (inj₂ refl)))
  stξ ξ st (mr m) = mapFs mr (st m)

  stDup : ∀ {E ρ π} → St E ρ π → St E ρ (π ∪ π)
  stDup st (ml m) = st m
  stDup st (mr m) = st m

  stSelf : ∀ {E ρ π} → St E ρ π → St E π (π ∪ π)
  stSelf st (ml m) = fs (ev (st m)) (just (ab m (inj₂ refl)))
  stSelf st (mr m) = fs (ev (st m)) (just (ab m (inj₂ refl)))
```

## §6 从帧到输出, 从帧到表

```agda
  module Vis {E : Ents} {ρ π : Fl} (st : St E ρ π) where
    toOut : ∀ {a b} (r : a < b) → Adm (cov π) r → Maybe (Adm (cov ρ) r)
    toOut zero _ = just tt
    toOut (suc r) a = toOut r a
    toOut (lim n r) a = toOut r a
    toOut (fst r) a = toOut r a
    toOut (bra η e r) ((c₁ , t₁ , g₁ , e₁ , m , k) , a) with abm (st m) | toOut r a
    ... | just (ab {c₄} {t₄} {g₄} {e₄} mem lk) | just a′ = just ((c₄ , t₄ , g₄ , e₄ , mem , lkC k lk) , a′)
    ... | _ | _ = nothing

    toOutC : ∀ {a b} (r : Cp a b) → AdmC (cov π) r → Maybe (AdmC (cov ρ) r)
    toOutC self _ = just tt
    toOutC (suc r) a = toOutC r a
    toOutC (lim n r) a = toOutC r a
    toOutC (fst r) a = toOutC r a
    toOutC (bra η e r) ((c₁ , t₁ , g₁ , e₁ , m , k) , a) with abm (st m) | toOutC r a
    ... | just (ab {c₄} {t₄} {g₄} {e₄} mem lk) | just a′ = just ((c₄ , t₄ , g₄ , e₄ , mem , lkC k lk) , a′)
    ... | _ | _ = nothing

    belOf : ∀ {y η f} → (y ≈ κ f ⊎ y ≡ κ f) → fη f ≡ η → Evd E f → Bel (tab E) y η
    belOf {f = f} (inj₁ d) refl (evd _ _ _ (ℓ , a , q)) = ℓ , at-resp {E} (≈-sym d) a , q
    belOf (inj₂ refl) refl (evd _ _ _ b) = b

    toTab : ∀ {a b} (r : a < b) → Adm (cov π) r → Maybe (Adm (tab E) r)
    toTab zero _ = just tt
    toTab (suc r) a = toTab r a
    toTab (lim n r) a = toTab r a
    toTab (fst r) a = toTab r a
    toTab (bra η e r) ((c₁ , t₁ , g₁ , e₁ , m , k) , a) with ev (st m) | toTab r a
    ... | just d | just a′ = just (belOf {f = frm c₁ t₁ g₁ η e₁} k refl d , a′)
    ... | _ | _ = nothing

    toTabC : ∀ {a b} (r : Cp a b) → AdmC (cov π) r → Maybe (AdmC (tab E) r)
    toTabC self _ = just tt
    toTabC (suc r) a = toTabC r a
    toTabC (lim n r) a = toTabC r a
    toTabC (fst r) a = toTabC r a
    toTabC (bra η e r) ((c₁ , t₁ , g₁ , e₁ , m , k) , a) with ev (st m) | toTabC r a
    ... | just d | just a′ = just (belOf {f = frm c₁ t₁ g₁ η e₁} k refl d , a′)
    ... | _ | _ = nothing
```

## §7 节点对目标

`cmpN`: 与 `kdec` 同一个骨架. 同一个节点上的两个分支才读表 (`bd`). 输出 `cb`: 节点在目标之下, 路径搬到目标里, 帧搬到输出. `cu`: 目标不在节点之上, 要上升. `cj`: 证据缺失. **`bra` 对 `bra` 且帧没有证据时给 `cj`: 这不是判定, 没有比较任何东西.**

```agda
    data CN (k t : LG) : Set where
      cb : ∀ {rp} → k ≈ rp → (s : rp < t) → Adm (cov ρ) s → CN k t
      cu : CN k t
      cj : CN k t

    shl : ∀ {k k′ t} → k ≈ k′ → CN k′ t → CN k t
    shl e (cb d s a) = cb (≈-trans e d) s a
    shl e cu = cu
    shl e cj = cj

    shr : ∀ {k t t′} → t ≈ t′ → CN k t′ → CN k t
    shr e (cb d s a) with ≈-move (≈-sym e) s
    ... | viaᴸ d′ s′ u = cb (≈-trans d d′) s′ (u (cov ρ) a)
    shr e cu = cu
    shr e cj = cj

    cmpN : ∀ {c′} → WFˢ c′ → c′ ≈ c′ → ∀ {k t} (r : k < c′) (q : t < c′) → Adm (cov π) r → Adm (tab E) q → CN k t
    cmpN w (s≈ e) zero zero _ _ = cu
    cmpN w (s≈ e) zero (suc q) _ _ = cu
    cmpN w (s≈ e) (suc r) zero cv _ with toOut r cv
    ... | just a = cb (selfAt e r) r a
    ... | nothing = cj
    cmpN w (s≈ e) (suc r) (suc q) cv aq = cmpN w e r q cv aq
    cmpN (st′ , w) (l≈ e) (lim n r) (lim m q) cv aq with <ᴺ-dec n m
    ... | injᵃ n<m with ⊴p (stepsˢ st′ n<m) r
    ...   | viaᴸ d r′ u = shl d (cmpN (w m) (e m) r′ q (u (cov π) cv) aq)
    cmpN (st′ , w) (l≈ e) (lim n r) (lim m q) cv aq | injᵇ m<n with ⊴p (stepsˢ st′ m<n) q
    ...   | viaᴸ d q′ u = shr d (cmpN (w n) (e n) r q′ cv (u (tab E) aq))
    cmpN (st′ , w) (l≈ e) (lim n r) (lim _ q) cv aq | injᶜ refl = cmpN (w n) (e n) r q cv aq
    cmpN (tg , dir , wt , wg) (o≈ d se sh) (fst r) (fst q) cv aq = cmpN wt se r q cv aq
    cmpN (tg , dir , wt , wg) (o≈ d se sh) (fst r) (bra y e q) cv (_ , aq) with ⊴p (tg y e) r
    ... | viaᴸ d′ r′ u = shl d′ (cmpN (wg y e) (sh y e y e (≅ᴰ-refl y)) r′ q (u (cov π) cv) aq)
    cmpN (tg , dir , wt , wg) (o≈ d se sh) (bra x e₁ r) (fst q) (_ , cv) aq with ⊴p (tg x e₁) q
    ... | viaᴸ d′ q′ u = shr d′ (cmpN (wg x e₁) (sh x e₁ x e₁ (≅ᴰ-refl x)) r q′ cv (u (tab E) aq))
    cmpN (tg , dir , wt , wg) (o≈ d se sh) (bra x e₁ r) (bra y e₂ q) ((c₁ , t₁ , g₁ , e₃ , m , k) , cv) ((ℓ , b₁ , ly) , aq) with ev (st m)
    ... | nothing = cj
    ... | just evi with belOf {f = frm c₁ t₁ g₁ x e₃} k refl evi
    ...   | ℓ′ , b₂ , lx with at-uq {E} (o≈ d se sh) b₂ b₁
    ...     | refl with bd lx ly
    ...       | injᵃ s with ⊴p (dir x e₁ y e₂ s) r
    ...         | viaᴸ d′ r′ u = shl d′ (cmpN (wg y e₂) (sh y e₂ y e₂ (≅ᴰ-refl y)) r′ q (u (cov π) cv) aq)
    cmpN (tg , dir , wt , wg) (o≈ d se sh) (bra x e₁ r) (bra y e₂ q) ((c₁ , t₁ , g₁ , e₃ , m , k) , cv) ((ℓ , b₁ , ly) , aq) | just evi | ℓ , b₂ , lx | refl | injᵇ s with ⊴p (dir y e₂ x e₁ s) q
    ...         | viaᴸ d′ q′ u = shr d′ (cmpN (wg x e₁) (sh x e₁ x e₁ (≅ᴰ-refl x)) r q′ cv (u (tab E) aq))
    cmpN (tg , dir , wt , wg) (o≈ d se sh) (bra x e₁ r) (bra y e₂ q) ((c₁ , t₁ , g₁ , e₃ , m , k) , cv) ((ℓ , b₁ , ly) , aq) | just evi | ℓ , b₂ , lx | refl | injᶜ k′ with ≈-move (sh x e₁ y e₂ k′) r
    ...         | viaᴸ d′ r′ u = shl d′ (cmpN (wg y e₂) (sh y e₂ y e₂ (≅ᴰ-refl y)) r′ q (u (cov π) cv) aq)
```

**闭包对目标.** `kb`: 目标在闭包之下, 所以闭包要立刻计值. `ka`: 闭包 (模 $\approx$) 在目标里, 所以保留.

```agda
    data CK (c₂ : Ordᴵ) (t₂ : LG) (g₂ : (η : Ordᴵ) → c₂ ⊑ᴵ η → LG) (t : LG) : Set where
      kb : CK c₂ t₂ g₂ t
      ka : ∀ {c′ t′ g′} (Q : Cp (lc c′ t′ g′) t) → lc c₂ t₂ g₂ ≈ lc c′ t′ g′ → AdmC (cov ρ) Q → CK c₂ t₂ g₂ t
      kj : CK c₂ t₂ g₂ t

    skl : ∀ {c₂ t₂ g₂ c₃ t₃ g₃ t} → lc c₂ t₂ g₂ ≈ lc c₃ t₃ g₃ → CK c₃ t₃ g₃ t → CK c₂ t₂ g₂ t
    skl e kb = kb
    skl e (ka Q d a) = ka Q (≈-trans e d) a
    skl e kj = kj

    skr : ∀ {c₂ t₂ g₂ t t′} → t ≈ t′ → CK c₂ t₂ g₂ t′ → CK c₂ t₂ g₂ t
    skr e kb = kb
    skr e (ka Q d a) with ≈-moveᴷ (≈-sym e) Q
    ... | viaᴷ d′ Q′ u = ka Q′ (≈-trans d d′) (u (cov ρ) a)
    skr e kj = kj

    cmpK : ∀ {c′} → WFˢ c′ → c′ ≈ c′ → ∀ {c₂ t₂ g₂ t} (P : Cp (lc c₂ t₂ g₂) c′) (q : t < c′) → AdmC (cov π) P → Adm (tab E) q → CK c₂ t₂ g₂ t
    cmpK w sf′ self q cv aq = kb
    cmpK w (s≈ e) (suc P) zero cv _ with toOutC P cv
    ... | just a = ka P (selfC e P) a
    ... | nothing = kj
    cmpK w (s≈ e) (suc P) (suc q) cv aq = cmpK w e P q cv aq
    cmpK (st′ , w) (l≈ e) (lim n P) (lim m q) cv aq with <ᴺ-dec n m
    ... | injᵃ n<m with ⊴K (stepsˢ st′ n<m) P
    ...   | viaᴷ d P′ u = skl d (cmpK (w m) (e m) P′ q (u (cov π) cv) aq)
    cmpK (st′ , w) (l≈ e) (lim n P) (lim m q) cv aq | injᵇ m<n with ⊴p (stepsˢ st′ m<n) q
    ...   | viaᴸ d q′ u = skr d (cmpK (w n) (e n) P q′ cv (u (tab E) aq))
    cmpK (st′ , w) (l≈ e) (lim n P) (lim _ q) cv aq | injᶜ refl = cmpK (w n) (e n) P q cv aq
    cmpK (tg , dir , wt , wg) (o≈ d se sh) (fst P) (fst q) cv aq = cmpK wt se P q cv aq
    cmpK (tg , dir , wt , wg) (o≈ d se sh) (fst P) (bra y e q) cv (_ , aq) with ⊴K (tg y e) P
    ... | viaᴷ d′ P′ u = skl d′ (cmpK (wg y e) (sh y e y e (≅ᴰ-refl y)) P′ q (u (cov π) cv) aq)
    cmpK (tg , dir , wt , wg) (o≈ d se sh) (bra x e₁ P) (fst q) (_ , cv) aq with ⊴p (tg x e₁) q
    ... | viaᴸ d′ q′ u = skr d′ (cmpK (wg x e₁) (sh x e₁ x e₁ (≅ᴰ-refl x)) P q′ cv (u (tab E) aq))
    cmpK (tg , dir , wt , wg) (o≈ d se sh) (bra x e₁ P) (bra y e₂ q) ((c₁ , t₁ , g₁ , e₃ , m , k) , cv) ((ℓ , b₁ , ly) , aq) with ev (st m)
    ... | nothing = kj
    ... | just evi with belOf {f = frm c₁ t₁ g₁ x e₃} k refl evi
    ...   | ℓ′ , b₂ , lx with at-uq {E} (o≈ d se sh) b₂ b₁
    ...     | refl with bd lx ly
    ...       | injᵃ s with ⊴K (dir x e₁ y e₂ s) P
    ...         | viaᴷ d′ P′ u = skl d′ (cmpK (wg y e₂) (sh y e₂ y e₂ (≅ᴰ-refl y)) P′ q (u (cov π) cv) aq)
    cmpK (tg , dir , wt , wg) (o≈ d se sh) (bra x e₁ P) (bra y e₂ q) ((c₁ , t₁ , g₁ , e₃ , m , k) , cv) ((ℓ , b₁ , ly) , aq) | just evi | ℓ , b₂ , lx | refl | injᵇ s with ⊴p (dir y e₂ x e₁ s) q
    ...         | viaᴸ d′ q′ u = skr d′ (cmpK (wg x e₁) (sh x e₁ x e₁ (≅ᴰ-refl x)) P q′ cv (u (tab E) aq))
    cmpK (tg , dir , wt , wg) (o≈ d se sh) (bra x e₁ P) (bra y e₂ q) ((c₁ , t₁ , g₁ , e₃ , m , k) , cv) ((ℓ , b₁ , ly) , aq) | just evi | ℓ , b₂ , lx | refl | injᶜ k′ with ≈-moveᴷ (sh x e₁ y e₂ k′) P
    ...         | viaᴷ d′ P′ u = skl d′ (cmpK (wg y e₂) (sh y e₂ y e₂ (≅ᴰ-refl y)) P′ q (u (cov π) cv) aq)
```

## §8 闭包的界: 只看同键的帧与目标的分支

`Sel`: 与 [LvKeyTree](LvKeyTree.lagda.md) 的 `Sel` 同形. 新东西是 `Sl`: 什么也没有挑出 (`emp`), 或者挑出了, 有字面的界, 且挑出的项都在闭包自己的下界 $c_2$ 之上 (`sel`). 所以 $c_2\sqsubseteq$ 界, 分支的守卫 `e` 给得出.

```agda
  module Sel {c₂ t₂ g₂} (P : Cp (lc c₂ t₂ g₂) c) (E : Ents) (ap : AdmC (tab E) P) where
    kself : lc c₂ t₂ g₂ ≈ lc c₂ t₂ g₂
    kself = selfC sf P

    E′ : Ordᴵ → Ents
    E′ X = E ▸ lc c₂ t₂ g₂ , X

    data Sl (φ : Flr) : Set where
      emp : (∀ ℓ → Ev ℓ φ) → Sl φ
      sel : ∀ ℓ K₀ → at E (lc c₂ t₂ g₂) ℓ → K₀ <ᴵ ℓ → Ev ℓ φ → (∀ ℓ′ → Ev ℓ′ φ → c₂ ⊑ᴵ ℓ′) → Sl φ

    record S (G : Ents → Set) : Set where
      constructor mkS
      field
        φ   : Flr
        wit : Sl φ
        lft : ∀ X → Ev X φ → G (E′ X)
    open S public

    triv : ∀ {G} → (∀ X → G (E′ X)) → S G
    triv f = mkS fz (emp (λ _ → tt)) (λ X _ → f X)

    mapS : ∀ {A B : Ents → Set} → (∀ F → A F → B F) → S A → S B
    mapS f s = mkS (φ s) (wit s) (λ X x → f _ (lft s X x))

    mg : ∀ {a b} → Sl a → Sl b → Sl (a ⊔ b)
    mg (emp f) (emp h) = emp (λ ℓ → f ℓ , h ℓ)
    mg (emp f) (sel ℓ K a q y d) = sel ℓ K a q (f ℓ , y) (λ ℓ′ x → d ℓ′ (proj₂ x))
    mg (sel ℓ K a q x d) (emp h) = sel ℓ K a q (x , h ℓ) (λ ℓ′ u → d ℓ′ (proj₁ u))
    mg (sel ℓ K a q x d) (sel ℓ′ K′ a′ q′ y d′) with at-uq {E} kself a a′
    ... | refl = sel ℓ K a q (x , y) (λ ℓ″ u → d ℓ″ (proj₁ u))

    _⋈_ : ∀ {A B : Ents → Set} → S A → S B → S (λ F → A F × B F)
    s ⋈ s′ = mkS (φ s ⊔ φ s′) (mg (wit s) (wit s′)) (λ X x → lft s X (proj₁ x) , lft s′ X (proj₂ x))

    lit : ∀ {K ℓ} → K <ᴵ ℓ → Simᴵ (suc K) ℓ
    lit q Lvl.zero = q
    lit q (Lvl.suc r) = <ᴵ-trans r q

    -- 节点 ν 与 K: 是同一个键就进界
    pick : ∀ {c₅ t₅ g₅} (Q : Cp (lc c₅ t₅ g₅) c) → AdmC (tab E) Q → ∀ K → c₅ ⊑ᴵ K → Bel′ E (lc c₅ t₅ g₅) K → S (λ F → Bel′ F (lc c₅ t₅ g₅) K)
    pick Q aq K eK (ℓ , a , q) with kdec wf sf Q P E aq ap
    ... | inj₁ e = mkS (fk K)
                       (sel ℓ K (at-resp {E} e a) q (lit q)
                            (λ ℓ′ x → ⊑ᴵ-trans (conv (oc≅ e) eK) (≺→⊑ᴵ (via (≅ᴵ-refl K) (x Lvl.zero)))))
                       (λ X x → X , inj₁ (e , refl) , x Lvl.zero)
    ... | inj₂ n = mkS fz (emp (λ _ → tt)) (λ X _ → ℓ , inj₂ (n , a) , q)

    walk : ∀ {a x} (Q : Cp a c) → AdmC (tab E) Q → (r : Cp x a) → AdmC (tab E) r → S (λ F → AdmC (tab F) r)
    walk Q aq self _ = triv (λ _ → tt)
    walk Q aq (suc r) ad = walk (Q ⊙ suc self) (adm⊙ {tab E} Q aq tt) r ad
    walk Q aq (lim n r) ad = walk (Q ⊙ lim n self) (adm⊙ {tab E} Q aq tt) r ad
    walk Q aq (fst r) ad = walk (Q ⊙ fst self) (adm⊙ {tab E} Q aq tt) r ad
    walk Q aq (bra η e r) (u , ad) =
      pick Q aq η e u ⋈ walk (Q ⊙ bra η e self) (adm⊙ {tab E} Q aq (u , tt)) r ad

    walkA : ∀ {a x} (Q : Cp a c) → AdmC (tab E) Q → (r : x < a) → Adm (tab E) r → S (λ F → Adm (tab F) r)
    walkA Q aq zero _ = triv (λ _ → tt)
    walkA Q aq (suc r) ad = walkA (Q ⊙ suc self) (adm⊙ {tab E} Q aq tt) r ad
    walkA Q aq (lim n r) ad = walkA (Q ⊙ lim n self) (adm⊙ {tab E} Q aq tt) r ad
    walkA Q aq (fst r) ad = walkA (Q ⊙ fst self) (adm⊙ {tab E} Q aq tt) r ad
    walkA Q aq (bra η e r) (u , ad) =
      pick Q aq η e u ⋈ walkA (Q ⊙ bra η e self) (adm⊙ {tab E} Q aq (u , tt)) r ad

    selSt : ∀ {ρ} π → St E ρ π → S (λ F → St F ρ π)
    selSt tz st = triv (λ X → λ ())
    selSt (tk f) st with st hr
    ... | fs nothing a = triv (λ X → λ { hr → fs nothing a })
    ... | fs (just (evd Pf adf lkf (ℓ , b , q))) a =
      mapS (λ F x → λ { hr → fs (just (evd Pf (proj₁ x) lkf (bel-to F (proj₂ x)))) a })
           (walk self tt Pf adf ⋈ pick Pf adf (fη f) (conv (≅ᴰ-sym (oc≅ lkf)) (fe f)) (ℓ , at-resp {E} (≈-sym lkf) b , q))
      where
      bel-to : ∀ F → Bel′ F (lc _ _ _) (fη f) → Bel′ F (κ f) (fη f)
      bel-to F (ℓ′ , b′ , q′) = ℓ′ , at-resp {F} lkf b′ , q′
    selSt (a ∪ b) st =
      mapS (λ F x → λ { (ml m) → proj₁ x m ; (mr m) → proj₂ x m })
           (selSt a (λ m → st (ml m)) ⋈ selSt b (λ m → st (mr m)))
```

## §9 折叠

`ψ`: 对树结构递归. 三处派发: `oΩ` 经 `cmpN` (穿透, 上升), `ocl` 经 `cmpK` (立刻计值, 保留). 目标 0 (`t0`) 没有路径: 节点总上升, 闭包总计值.

```agda
  data Tg (E : Ents) : LG → Set where
    t0 : Tg E zero
    tp : ∀ {t} (q : t < c) → Adm (tab E) q → Tg E t

  tgSel : ∀ {c₂ t₂ g₂ t} (P : Cp (lc c₂ t₂ g₂) c) (E : Ents) (ap : AdmC (tab E) P) → Tg E t → Sel.S P E ap (λ F → Tg F t)
  tgSel P E ap t0 = Sel.triv P E ap (λ _ → t0)
  tgSel P E ap (tp q aq) = Sel.mapS P E ap (λ F a → tp q a) (Sel.walkA P E ap self tt q aq)

  chainᵒ : ∀ {k π} → (O k π → O k π) → ℕ → O k π
  chainᵒ {k} f zero    = owk (λ ()) (Ω̇ k)
  chainᵒ f (suc n) = f (chainᵒ f n)

  dd : ∀ {π} → Wk (π ∪ π) π
  dd (ml m) = m
  dd (mr m) = m

  ψ : ∀ {t π ρ} (E : Ents) → Tg E t → St E ρ π → O c π → O t ρ
  evalC : ∀ {t π ρ c₁ t₁ g₁ c₂ t₂ g₂} (E : Ents) → Tg E t → St E ρ π → (P : Cp (lc c₂ t₂ g₂) c) → (lc c₂ t₂ g₂ ≈ lc c₁ t₁ g₁ ⊎ lc c₂ t₂ g₂ ≡ lc c₁ t₁ g₁) → AdmC (cov π) P →
          O c π → (∀ η e → O c (π ∪ tk (frm c₁ t₁ g₁ η e))) → O t ρ
  riseΩ : ∀ {t π ρ k} (E : Ents) → Tg E t → St E ρ π → (r : k < c) → Adm (cov π) r → (∀ ξ → Us c r ξ → O c (ξ ∪ π)) → O t ρ

  ψ {t} E T st o0 = owk (λ ()) (Ω̇ t)
  ψ E T st (os a) = ol (repᵒ (ψ E T st a))
  ψ E T st (ol F) = ol (λ n → ψ E T st (F n))
  ψ E T st (oŝ c₀ x g) = oŝ c₀ (ψ E T st x) (λ η e → ψ E T st (g η e))
  ψ E T st (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (ψ E T st o₀) (λ η e → ψ E T st (o η e))
  ψ E T st (owk w x) = ψ E T (λ m → st (w m)) x
  ψ E t0 st (oΩ r cv h) = riseΩ E t0 st r cv h
  ψ E (tp q aq) st (oΩ r cv h) with Vis.cmpN st wf sf r q cv aq
  ... | Vis.cb d s a = oΩ s a (λ ξ y → ψ E (tp q aq) (stξ ξ st) (h ξ (intoU r (tr⁻O d (outU s y)))))
  ... | Vis.cu = riseΩ E (tp q aq) st r cv h
  ... | Vis.cj = o0
  ψ E t0 st (ocl P k cv x g) = evalC E t0 st P k cv x g
  ψ {π = π} {ρ = ρ} E (tp q aq) st (ocl {c₁ = c₁} {t₁} {g₁} P k cv x g) with Vis.cmpK st wf sf P q cv aq
  ... | Vis.kb = evalC E (tp q aq) st P k cv x g
  ... | Vis.kj = o0
  ... | Vis.ka {c′} {t′} {g′} Q d a =
    ocl Q (inj₂ refl) a (ψ E (tp q aq) st x)
      (λ η e′ → ψ E (tp q aq) (st″ η e′) (g η (eg e′)))
    where
    lks₁ : lc c₁ t₁ g₁ ≈ lc c′ t′ g′
    lks₁ = ≈-trans (≈-sym (lk→≈ (selfC sf P) k)) d
    eg : ∀ {η} → c′ ⊑ᴵ η → c₁ ⊑ᴵ η
    eg e′ = conv (oc≅ (≈-sym lks₁)) e′
    st″ : ∀ η e′ → St E (ρ ∪ tk (frm c′ t′ g′ η e′)) (π ∪ tk (frm c₁ t₁ g₁ η (eg e′)))
    st″ η e′ (ml m) = mapFs ml (st m)
    st″ η e′ (mr hr) = fs nothing (just (ab {c₄ = c′} {t₄ = t′} {g₄ = g′} {e₄ = e′} (mr hr) (inj₁ lks₁)))

  riseΩ {π = π} E T st r cv h with Vis.toTab st r cv
  ... | nothing = o0
  ... | just a = ol (λ n → ψ E T (stDup st) (h π (intoU r (chainᵒ (λ z → ψ E (tp r a) (stSelf st) (h π (intoU r z))) n))))

  evalC {t} {π} {ρ} {c₁} {t₁} {g₁} {c₂} {t₂} {g₂} E T st P k cv x g with Vis.toTabC st P cv
  ... | nothing = o0
  ... | just ap = go (M.wit SS)
    where
    module M = Sel P E ap
    tgS : M.S (λ F → Tg F t)
    tgS = tgSel P E ap T
    SS : M.S (λ F → St F ρ π × (Tg F t × AdmC (tab F) P))
    SS = M._⋈_ (M.selSt π st) (M._⋈_ tgS (M.walk self tt P ap))
    lk₂ : lc c₂ t₂ g₂ ≈ lc c₁ t₁ g₁
    lk₂ = lk→≈ M.kself k
    guardC : ∀ {η} → c₂ ⊑ᴵ η → c₁ ⊑ᴵ η
    guardC d = conv (oc≅ lk₂) d
    body : ∀ η (e : c₁ ⊑ᴵ η) X → Ev X (M.φ SS) → η <ᴵ X → O t ρ
    body η e X ex q = ψ (M.E′ X) (proj₁ (proj₂ L)) stn (g η e)
      where
      L = M.lft SS X ex
      stn : St (M.E′ X) ρ (π ∪ tk (frm c₁ t₁ g₁ η e))
      stn (ml m) = proj₁ L m
      stn (mr hr) = fs (just (evd P (proj₂ (proj₂ L)) lk₂ (X , inj₁ (≈-sym lk₂ , refl) , q))) nothing
    go : M.Sl (M.φ SS) → O t ρ
    go (M.emp f) = oŝ c₂ (ψ E T st x) (λ η d → body η (guardC d) (suc η) (f (suc η)) Lvl.zero)
    go (M.sel ℓ K₀ a q y dm) = oŝ (Bd B) (ψ E T st x)
         (λ η d → body η (guardC (⊑ᴵ-trans (dm (Fc B) (evF B)) (⊑ᴵ-trans (FM B) d)))
                       (Mlev (Fc B) (suc η) (FB B d))
                       (liftEv (M.φ SS) (λ r → Lvl.lim 0 r) (evF B))
                       (Lvl.lim 1 Lvl.zero))
      where
      B : Top K₀ ℓ (M.φ SS)
      B = bound (M.φ SS) y q

-- $\psi_0(\Omega_L)$: 任何带证书的层号. 一个定义, 没有标签, 没有对阶段的归纳.
T : (L : LG) → Cfˢ L → O zero tz
T L (w , s) = Fold.ψ L w s (∅ Lvl.zero) Fold.t0 (λ ()) (Ω̇ L)

T₀ : (L : LG) → Cfˢ L → Z
T₀ L cf = rdZ (T L cf)
```
