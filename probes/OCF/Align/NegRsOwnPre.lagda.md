# 升界只剩一种? 否定一路 (一): "精确置自己, 别处只增" 在接口定稿之前

> 不含记号. 入口 [NegRsOwn](NegRsOwn.lagda.md). 本篇**不依赖**构造一路的接口 `RsOwnIf` (接口定稿之前写的部分). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延 `FE₀` 只在标 "条件" 的 `…→WLPO` 里作前提.
>
> **问题** (作者本轮原话: "挑战 '只剩一种升界'"). `NegKindLv` 的判断: 以含函数的高度为下标的并里, 升界只剩 "精确置自己的分量, 别处只增不减且按分量不同" 一种未被否定的形状. 本篇对这一形状直接写否定的尝试, 并找出否定在哪里成立, 在哪里断.
>
> **结果.**
>
> 1. **字面的形状被否定 (`ownB₁-sep`, `ownH₁-sep`, `ownBΛ⁺-sep`, `ownHΛ⁺-sep`; 定理).** 若 rs 对一切世界, 一切 $f$, 一切 $v$: (i) 把种类 $\kappa_f$ 的界**精确地**置为 $v$ (`rs-top`, 无前提), (ii) 下标不同的拷贝 $\kappa_{f'}$ 的界**无条件地**只增 (`rs-gr`, 前提只有 `¬ (jx f′ ≡ jx f)`), 那么分离子 `Sep` 成立 (`FE₀` 下 WLPO). rs 可以任意地依赖分量. 证明: 世界里每份拷贝的界都是 $1$, 把 $\kappa_f$ 置成 $0$ (**降**), 看 $\kappa_{f'}$ 的界是不是 $0$ (构造子, 可判定). 是 $0$: 下标不能不等 (不等时它 $\unrhd 1$); 不是 $0$: 下标不等 (相等时它就是 $0$). 底拷贝 (坐标 `A`) 与坐标是高度的种类 (`κH f`, 坐标 `HB (Lev (jx f))`) 都成立, 在 `K₁` 与最终层所在的 `step KΛc` 上都成立.
> 2. **断点: 别处的增长带 `KLv.rs≤` 的前提时, 上面的论证不成立 (判断, 有编译的旁证).** `KindLvIf.KLv` 的 `rs≤` 只在 "旧顶是 $v$ 的第一位置" 时要世界变大, 所以不能用 "降" 的那一步. 旁证 (定理, 条件): 给一个下标判定 `DecJ` (经典地成立, 自身推出分离子 `decJ→sep`), 就有 `K₁` 的底拷贝 `κ₁ f` 上的 `KLv` 实例 `decJ→KLv`, 它精确置自己, 别处不动. 所以 "`KLv` 形状的精确置 ⇒ ⊥" **不可证** (元层判断: 经典逻辑与 MLTT 相容); 能指望的只有 "⇒ 分离子/WLPO", 本篇**未走通**. 断在哪里写在 §4 末.
> 3. **与 `no-joinA` 的关系 (`no-ownJoin`; 定理).** "别处只增" 本身不撞 `no-joinA` (条件实例 `decJ→KLv` 合法). 撞的是 "别处还要含 $v$": 若升后某个分量 (哪怕是可判定的旧站分量 `inj₁ tt`) 必须同时 $\unrhd$ 旧界与 $v$ 且合法, 取旧界与 $v$ 为偶数列与奇数列的极限即矛盾. 这与 `RaiseC.no-bounded-raise` 同型.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegRsOwnPre where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (H₀)
open import OCF.Align.HtTowerNStage using (dWLev)
open import OCF.Align.HtTowerNeg using (evA; odA; Lg-evA; Lg-odA; no-joinA)
open import OCF.Align.RaiseCB using (dW; lg-dW)
open import OCF.Align.ColimWNeg using (WLPO; FE₀)
open import OCF.Align.LvKtIf using (KΛc; FN)
open import OCF.Align.GenFoldIf using (K₁; top)
open import OCF.Align.NegGenFoldUpd using (jx; jx-inj; Sep; WDec; wdec→sep; sep→WLPO; κ₁; fα; fω; eq→F; upd∘)
open import OCF.Align.NegKindLvRaise using (upAllR; tp₁; wA; half-top)
open import OCF.Align.NegKindLvUpd using (κH; one⊀z)
open import OCF.Align.NegNewTwrFeed using (ext₁; κΛ)
open import OCF.Align.KindLvIf using (KLv)
```

## §1 底拷贝 `κ₁ f` (坐标 `A`): 精确置自己 + 别处无条件只增 ⇒ 分离子

`κ₁ f` 是 `K₁` 的读回分量 `inj₂ (jx f)` 里第 0 个子分量的底种类; 它的顶就是 `w (inj₂ (jx f)) 0` (`NegKindLvRaise.top-κ₁`, `refl`). `rs-gr` 只对下标不同的同型拷贝 `κ₁ f′` 要求 "不降"; "一切下标不同的分量整个不降" (`OwnAll₁`) 推出它 (`all→ownB₁`), 所以定理对两者都成立.

```agda
record OwnB₁ : Set where
  field
    rs     : Wd K₁ → (ℕ → H₀) → A → Wd K₁
    rs-top : ∀ w f v → top tp₁ (κ₁ f) (rs w f v) ≡ v
    rs-gr  : ∀ w f v f′ → ¬ (jx f′ ≡ jx f) → Bd K₁ (κ₁ f′) (top tp₁ (κ₁ f′) w) (rs w f v)

record OwnAll₁ : Set where
  field
    rs     : Wd K₁ → (ℕ → H₀) → A → Wd K₁
    rs-top : ∀ w f v → top tp₁ (κ₁ f) (rs w f v) ≡ v
    rs-gr  : ∀ w f v (i : ⊤ ⊎ H₀) → ¬ (i ≡ inj₂ (jx f)) → _≤w_ (FN S₀ i) (w i) (rs w f v i)

inj₂-inj : ∀ {c c′ : H₀} → _≡_ {A = ⊤ ⊎ H₀} (inj₂ c′) (inj₂ c) → c′ ≡ c
inj₂-inj refl = refl

all→ownB₁ : OwnAll₁ → OwnB₁
all→ownB₁ P = record
  { rs = rs ; rs-top = rs-top
  ; rs-gr = λ w f v f′ ne → rs-gr w f v (inj₂ (jx f′)) (λ e → ne (inj₂-inj e)) 0 }
  where open OwnAll₁ P

one⊀0 : ¬ (asuc azero ⊲ azero)
one⊀0 ()

wdecOwn₁ : OwnB₁ → WDec
wdecOwn₁ P f f′ = go (rs (wA (asuc azero)) f azero (inj₂ (jx f′)) 0) refl
  where
  open OwnB₁ P
  W : Wd K₁
  W = rs (wA (asuc azero)) f azero
  own : jx f′ ≡ jx f → W (inj₂ (jx f′)) 0 ≡ azero
  own e = subst (λ g → W (inj₂ (jx g)) 0 ≡ azero) (sym (jx-inj e)) (rs-top (wA (asuc azero)) f azero)
  go : ∀ r → W (inj₂ (jx f′)) 0 ≡ r → ¬ (jx f′ ≡ jx f) ⊎ ¬ ¬ (jx f′ ≡ jx f)
  go azero e = inj₂ (λ ne → one⊀0 (subst (asuc azero ⊲_) e (rs-gr (wA (asuc azero)) f azero f′ ne)))
  go (asuc r) e = inj₁ (λ q → s≢z (trans (sym e) (own q)))
    where s≢z : asuc r ≡ azero → ⊥
          s≢z ()
  go (alim g) e = inj₁ (λ q → l≢z (trans (sym e) (own q)))
    where l≢z : alim g ≡ azero → ⊥
          l≢z ()

ownB₁-sep : OwnB₁ → Sep
ownB₁-sep P = wdec→sep (wdecOwn₁ P)

ownAll₁-sep : OwnAll₁ → Sep
ownAll₁-sep P = ownB₁-sep (all→ownB₁ P)

ownB₁→WLPO : FE₀ → OwnB₁ → WLPO
ownB₁→WLPO fe P = sep→WLPO fe (ownB₁-sep P)
```

**两半各自可满足.** 只要 `rs-top`: 每个读回分量的每份底拷贝都置成 $v$ (`upAllR (λ a v → v)`, 不看下标). 只要 `rs-gr`: 世界不动. **下标可判定时两半同时成立**: 旧站分量 `inj₁ tt` 的种类 (坐标 `A`) 精确置成 $v$, 一切读回分量不动 (`NegGenFoldUpd.upd∘`).

```agda
topOnly₁ : Wd K₁ → (ℕ → H₀) → A → Wd K₁
topOnly₁ w f v = upAllR (λ a v → v) w v

topOnly₁-top : ∀ w f v → top tp₁ (κ₁ f) (topOnly₁ w f v) ≡ v
topOnly₁-top w f v = half-top f w v

grOnly₁ : Wd K₁ → (ℕ → H₀) → A → Wd K₁
grOnly₁ w f v = w

grOnly₁-gr : ∀ w f v f′ → ¬ (jx f′ ≡ jx f) → Bd K₁ (κ₁ f′) (top tp₁ (κ₁ f′) w) (grOnly₁ w f v)
grOnly₁-gr w f v f′ ne = C.self

-- 可判定下标: 旧站分量精确置 v, 读回分量整个不动
own∘-top : ∀ w v → upd∘ w v (inj₁ tt) ≡ v
own∘-top w v = refl

own∘-gr : ∀ w v (c : H₀) → _≤w_ (Lev c) (w (inj₂ c)) (upd∘ w v (inj₂ c))
own∘-gr w v c = ≤w-rf (Lev c)
```

## §2 坐标是高度的种类 `κH f`: 同样

`κH f = (inj₂ (hs (jx f)) , inj₂ tt)`, 坐标 `HB (Lev (jx f))` (类型随 $f$ 变), 界是分量 `hs (jx f)` 的世界的第二分量. 世界取 "每个形如 `hs c` 的分量的新种类的界都是 $1$", 把 `κH f` 置成 $0$.

```agda
record OwnH₁ : Set where
  field
    rs     : Wd K₁ → (f : ℕ → H₀) → HB (Lev (jx f)) → Wd K₁
    rs-top : ∀ w f v → proj₂ (rs w f v (inj₂ (hs (jx f)))) ≡ v
    rs-gr  : ∀ w f v f′ → ¬ (jx f′ ≡ jx f) → Bd K₁ (κH f′) (proj₂ (w (inj₂ (hs (jx f′))))) (rs w f v)

-- 顶就是第二分量
top-κH : ∀ f w → top tp₁ (κH f) w ≡ proj₂ (w (inj₂ (hs (jx f))))
top-κH f w = refl

wH : Wd K₁
wH (inj₁ tt) = azero
wH (inj₂ hz) = azero
wH (inj₂ (hs c)) = dWLev c , hs hz
wH (inj₂ (hl g)) = dWLev (hl g)
wH (inj₂ (hΩ κ g)) = dWLev (hΩ κ g)

wdecOwnH₁ : OwnH₁ → WDec
wdecOwnH₁ P f f′ = go (proj₂ (W (inj₂ (hs (jx f′))))) refl
  where
  open OwnH₁ P
  W : Wd K₁
  W = rs wH f hz
  own : jx f′ ≡ jx f → proj₂ (W (inj₂ (hs (jx f′)))) ≡ hz
  own e = subst (λ g → proj₂ (W (inj₂ (hs (jx g)))) ≡ hz) (sym (jx-inj e)) (rs-top wH f hz)
  go : ∀ r → proj₂ (W (inj₂ (hs (jx f′)))) ≡ r → ¬ (jx f′ ≡ jx f) ⊎ ¬ ¬ (jx f′ ≡ jx f)
  go hz e = inj₂ (λ ne → one⊀z (subst (λ b → hs hz ⊲[ proj₁ (W (inj₂ (hs (jx f′)))) ] b) e (rs-gr wH f hz f′ ne)))
  go (hs r) e = inj₁ (λ q → n≢ (trans (sym e) (own q)))
    where n≢ : hs r ≡ hz → ⊥
          n≢ ()
  go (hl g) e = inj₁ (λ q → n≢ (trans (sym e) (own q)))
    where n≢ : hl g ≡ hz → ⊥
          n≢ ()
  go (hΩ κ g) e = inj₁ (λ q → n≢ (trans (sym e) (own q)))
    where n≢ : hΩ κ g ≡ hz → ⊥
          n≢ ()

ownH₁-sep : OwnH₁ → Sep
ownH₁-sep P = wdec→sep (wdecOwnH₁ P)

ownH₁→WLPO : FE₀ → OwnH₁ → WLPO
ownH₁→WLPO fe P = sep→WLPO fe (ownH₁-sep P)
```

**两半各自可满足.** 只要 `rs-top`: 每个形如 `hs c` 的分量的新种类的界都置成 "$v$ 若类型对得上" 做不到 (类型随 $c$ 变), 但 $v$ 取 `hz` 时可以: `topOnlyH₁` 把一切这样的界置成 `hz`, 它满足 `rs-top` 在 $v=\mathrm{hz}$ 处 (`topOnlyH₁-top`); 对一般的 $v$, 只要 `rs-top` 的实例是 "按分量的结构搬运 $v$", 见 `NegKindLvUpd` §5 的判断. 只要 `rs-gr`: 世界不动. 下标可判定: `NegKindLvUpd.upd-step` (`step S` 的新种类精确置 $v$, 旧种类不动).

```agda
topOnlyH₁ : Wd K₁ → Wd K₁
topOnlyH₁ w (inj₁ tt) = w (inj₁ tt)
topOnlyH₁ w (inj₂ hz) = w (inj₂ hz)
topOnlyH₁ w (inj₂ (hs c)) = proj₁ (w (inj₂ (hs c))) , hz
topOnlyH₁ w (inj₂ (hl g)) = w (inj₂ (hl g))
topOnlyH₁ w (inj₂ (hΩ κ g)) = w (inj₂ (hΩ κ g))

topOnlyH₁-top : ∀ w f → proj₂ (topOnlyH₁ w (inj₂ (hs (jx f)))) ≡ hz
topOnlyH₁-top w f = refl

grOnlyH₁-gr : ∀ w f′ → Bd K₁ (κH f′) (proj₂ (w (inj₂ (hs (jx f′))))) w
grOnlyH₁-gr w f′ = hself
```

## §3 最终层所在的 `step KΛc`

旧种类 `inj₁ (1 , κ₁ f)` 与 `inj₁ (1 , κH f)` 就是第 1 站的 `κ₁ f`, `κH f`. 证明只在世界 `(ext₁ w , hz)` 上用一次 (同 `NegNewTwrFeed.toBΛ`).

```agda
record OwnBΛ⁺ : Set where
  field
    rs     : Wd (step KΛc) → (ℕ → H₀) → A → Wd (step KΛc)
    rs-top : ∀ w f v → proj₁ (rs w f v) 1 (inj₂ (jx f)) 0 ≡ v
    rs-gr  : ∀ w f v f′ → ¬ (jx f′ ≡ jx f) →
             Bd (step KΛc) (inj₁ (κΛ f′)) (proj₁ w 1 (inj₂ (jx f′)) 0) (rs w f v)

toOwnB₁ : OwnBΛ⁺ → OwnB₁
toOwnB₁ P = record
  { rs = λ w f v → proj₁ (rs (ext₁ w , hz) f v) 1
  ; rs-top = λ w f v → rs-top (ext₁ w , hz) f v
  ; rs-gr = λ w f v f′ ne → rs-gr (ext₁ w , hz) f v f′ ne }
  where open OwnBΛ⁺ P

ownBΛ⁺-sep : OwnBΛ⁺ → Sep
ownBΛ⁺-sep P = ownB₁-sep (toOwnB₁ P)

ownBΛ⁺→WLPO : FE₀ → OwnBΛ⁺ → WLPO
ownBΛ⁺→WLPO fe P = sep→WLPO fe (ownBΛ⁺-sep P)

record OwnHΛ⁺ : Set where
  field
    rs     : Wd (step KΛc) → (f : ℕ → H₀) → HB (Lev (jx f)) → Wd (step KΛc)
    rs-top : ∀ w f v → proj₂ (proj₁ (rs w f v) 1 (inj₂ (hs (jx f)))) ≡ v
    rs-gr  : ∀ w f v f′ → ¬ (jx f′ ≡ jx f) →
             Bd (step KΛc) (inj₁ (1 , κH f′)) (proj₂ (proj₁ w 1 (inj₂ (hs (jx f′))))) (rs w f v)

toOwnH₁ : OwnHΛ⁺ → OwnH₁
toOwnH₁ P = record
  { rs = λ w f v → proj₁ (rs (ext₁ w , hz) f v) 1
  ; rs-top = λ w f v → rs-top (ext₁ w , hz) f v
  ; rs-gr = λ w f v f′ ne → rs-gr (ext₁ w , hz) f v f′ ne }
  where open OwnHΛ⁺ P

ownHΛ⁺-sep : OwnHΛ⁺ → Sep
ownHΛ⁺-sep P = ownH₁-sep (toOwnH₁ P)

ownHΛ⁺→WLPO : FE₀ → OwnHΛ⁺ → WLPO
ownHΛ⁺→WLPO fe P = sep→WLPO fe (ownHΛ⁺-sep P)
```

## §4 断点: 带 `rs≤` 前提的精确置有条件实例

`DecJ`: 对一切下标 $c$ 与 $f$, 一个布尔值说 "$c$ 是不是 `jx f`", 对 `jx f` 自己为真, 为真时确实相等. 它经典地成立 (判断), 自身推出分离子 (`decJ→sep`, 定理), 由高度上的可判定相等给出 (`decH→decJ`).

```agda
record DecJ : Set where
  field
    isJ    : H₀ → (ℕ → H₀) → Bool
    isJ-jx : ∀ f → isJ (jx f) f ≡ true
    isJ-ok : ∀ c f → isJ c f ≡ true → c ≡ jx f

isYes : ∀ {P : Set} → Dec P → Bool
isYes (yes _) = true
isYes (no _) = false

decH→decJ : (∀ (c c′ : H₀) → Dec (c ≡ c′)) → DecJ
decH→decJ deq = record
  { isJ = λ c f → isYes (deq c (jx f))
  ; isJ-jx = λ f → self-yes (deq (jx f) (jx f))
  ; isJ-ok = λ c f → yes-ok (deq c (jx f)) }
  where
  self-yes : ∀ {x : H₀} (d : Dec (x ≡ x)) → isYes d ≡ true
  self-yes (yes _) = refl
  self-yes (no ne) = ⊥-elim (ne refl)
  yes-ok : ∀ {P : Set} (d : Dec P) → isYes d ≡ true → P
  yes-ok (yes p) _ = p
  yes-ok (no _) ()

decJ→sep : DecJ → Sep
decJ→sep D α = go (isJ (jx (fα α)) fω) refl
  where
  open DecJ D
  go : ∀ b → isJ (jx (fα α)) fω ≡ b → (∀ n → α n ≡ false) ⊎ ¬ (jx (fα α) ≡ jx fω)
  go true e = inj₁ (eq→F α (isJ-ok (jx (fα α)) fω e))
  go false e = inj₂ (λ q → f≢t (trans (sym e) (trans (cong (λ c → isJ c fω) q) (isJ-jx fω))))
    where f≢t : false ≡ true → ⊥
          f≢t ()
```

给定 `DecJ`, 在 `K₁` 上写 rs: 分量 `inj₂ c` 若 `isJ c f` 为真, 把它的第 0 个子分量 (第 0 项是 `hz` 时是一份底拷贝) 置成 $v$; 否则不动. 它满足 `KLv` 的三条升界律 (`rs-top` 无前提, `rs≤` 带前提, `rsLg`), 也满足 §1 的 `rs-gr` (无条件).

```agda
module WithDecJ (D : DecJ) where
  open DecJ D

  put : (x : H₀) → Wd (Lev x) → A → Wd (Lev x)
  put hz w v = v
  put (hs x) w v = w
  put (hl g) w v = w
  put (hΩ κ g) w v = w

  setJ : (c : H₀) → Wd (Lev c) → A → Wd (Lev c)
  setJ hz w v = w
  setJ (hs x) w v = w
  setJ (hl h) w v = λ { zero → put (h zero) (w zero) v ; (suc n) → w (suc n) }
  setJ (hΩ κ g) w v = w

  pick : Bool → (c : H₀) → Wd (Lev c) → A → Wd (Lev c)
  pick true c w v = setJ c w v
  pick false c w v = w

  rsJ : Wd K₁ → (ℕ → H₀) → A → Wd K₁
  rsJ w f v (inj₁ tt) = w (inj₁ tt)
  rsJ w f v (inj₂ c) = pick (isJ c f) c (w (inj₂ c)) v

  -- 精确置自己 (无前提)
  pick-top : ∀ f (x : Wd (Lev (jx f))) v b → b ≡ true → pick b (jx f) x v 0 ≡ v
  pick-top f x v true _ = refl
  pick-top f x v false ()

  rs-topJ : ∀ w f v → top tp₁ (κ₁ f) (rsJ w f v) ≡ v
  rs-topJ w f v = pick-top f (w (inj₂ (jx f))) v (isJ (jx f) f) (isJ-jx f)

  -- 带前提的不降
  le-set : ∀ (w : Wd K₁) f v c → c ≡ jx f → w (inj₂ (jx f)) 0 ⊲ v →
           _≤w_ (Lev c) (w (inj₂ c)) (setJ c (w (inj₂ c)) v)
  le-set w f v .(jx f) refl p = λ { zero → p ; (suc n) → ≤w-rf (Lev (f n)) }

  le-pick : ∀ (w : Wd K₁) f v c b → (b ≡ true → c ≡ jx f) → w (inj₂ (jx f)) 0 ⊲ v →
            _≤w_ (Lev c) (w (inj₂ c)) (pick b c (w (inj₂ c)) v)
  le-pick w f v c true ok p = le-set w f v c (ok refl) p
  le-pick w f v c false ok p = ≤w-rf (Lev c)

  rs≤J : ∀ w f v → Pr K₁ (κ₁ f) w (top tp₁ (κ₁ f) w) v → _≤w_ K₁ w (rsJ w f v)
  rs≤J w f v p (inj₁ tt) = C.self
  rs≤J w f v p (inj₂ c) = le-pick w f v c (isJ c f) (isJ-ok c f) p

  -- 合法
  lg-put : ∀ x (w : Wd (Lev x)) v → LgW (Lev x) w → Lg v → LgW (Lev x) (put x w v)
  lg-put hz w v lw lv = lv
  lg-put (hs x) w v lw lv = lw
  lg-put (hl g) w v lw lv = lw
  lg-put (hΩ κ g) w v lw lv = lw

  lg-set : ∀ c (w : Wd (Lev c)) v → LgW (Lev c) w → Lg v → LgW (Lev c) (setJ c w v)
  lg-set hz w v lw lv = lw
  lg-set (hs x) w v lw lv = lw
  lg-set (hl h) w v lw lv = λ { zero → lg-put (h zero) (w zero) v (lw zero) lv ; (suc n) → lw (suc n) }
  lg-set (hΩ κ g) w v lw lv = lw

  lg-pick : ∀ b c (w : Wd (Lev c)) v → LgW (Lev c) w → Lg v → LgW (Lev c) (pick b c w v)
  lg-pick true c w v lw lv = lg-set c w v lw lv
  lg-pick false c w v lw lv = lw

  rsLgJ : ∀ {w} f {v} → LgW K₁ w → Lg v → LgW K₁ (rsJ w f v)
  rsLgJ f lw lv (inj₁ tt) = lw (inj₁ tt)
  rsLgJ {w} f {v} lw lv (inj₂ c) = lg-pick (isJ c f) c (w (inj₂ c)) v (lw (inj₂ c)) lv

  -- 别处无条件不降 (所以也满足 §1)
  grJ : ∀ w f v f′ → ¬ (jx f′ ≡ jx f) → Bd K₁ (κ₁ f′) (top tp₁ (κ₁ f′) w) (rsJ w f v)
  grJ w f v f′ ne = go (isJ (jx f′) f) (isJ-ok (jx f′) f)
    where
    go : ∀ b → (b ≡ true → jx f′ ≡ jx f) → w (inj₂ (jx f′)) 0 ⊲ pick b (jx f′) (w (inj₂ (jx f′))) v 0
    go true ok = ⊥-elim (ne (ok refl))
    go false ok = C.self

  ownJ : OwnB₁
  ownJ = record { rs = rsJ ; rs-top = rs-topJ ; rs-gr = grJ }

-- KLv 的实例 (读回取起点; 级层取 Λ 本身)
decJ→KLv : DecJ → ∀ f Λ → KLv K₁ tp₁ Λ (κ₁ f)
decJ→KLv D f Λ = record
  { ℓ = Λ ; ℓ⊲ = hself
  ; rd = λ lW b x → b ; rd-fst = λ lW b x → C.self ; rd-lg = λ lW b x l → l
  ; rs = λ w v → rsJ w f v
  ; rs≤ = λ {w} {v} p → rs≤J w f v p
  ; rsLg = λ lw lv → rsLgJ f lw lv
  ; rs-top = λ {w} {v} → rs-topJ w f v }
  where open WithDecJ D

decJ→ownB₁ : DecJ → OwnB₁
decJ→ownB₁ D = WithDecJ.ownJ D
```

**断在哪里 (判断).** §1 的论证用到两处: (a) 把 $\kappa_f$ 置成**低于**旧界的 $v$ (旧界 $1$, $v=0$); (b) 此时别的拷贝仍不降. `KLv.rs≤` 只在旧顶 $\lhd v$ 时要不降, 所以 (a), (b) 不能同时用. 换成满足前提的世界 (旧顶 $\lhd v$), 相等时 $\kappa_{f'}$ 的界是 $v$, 不等时它 $\unrhd$ 自己的旧界, 而相等时它的旧界就是 $\kappa_f$ 的旧界 $\lhd v$: **相等的情形是不等情形结论的特例**, 单次调用读不出差别. 要读出差别, 得有一个世界, 在 `jx f` 处 $\lhd v$ 而在 `jx f′` 处 (不等时) 与 $v$ 可判定地不同; 写这样的世界本身就要判定下标. 判断: 在连续性的模型里 (函数可读连续模), 带前提的精确置可以实现, 所以 "⇒ WLPO" 也许根本不可证; 未写成定理. 本篇对这一形状只写 "未走通".

## §5 别处还要含 $v$: 撞 `no-joinA`

若 rs (对种类 `κ₁ f`) 满足带前提的 `rs≤`, `rsLg`, 并且升后旧站分量 `inj₁ tt` (一个可判定下标的分量) 含 $v$, 则矛盾. 世界: 旧站分量是偶数列的极限, 读回分量最小 (`RaiseCB.dW`); $v$ 是奇数列的极限; $\kappa_f$ 的旧顶是 $0\lhd v$, 前提成立.

```agda
wJ : Wd K₁
wJ (inj₁ tt) = alim evA
wJ (inj₂ c) = dW c

lgwJ : LgW K₁ wJ
lgwJ (inj₁ tt) = Lg-evA
lgwJ (inj₂ c) = lg-dW c

no-ownJoin : ∀ f (rs : Wd K₁ → A → Wd K₁) →
  (∀ {w v} → Pr K₁ (κ₁ f) w (top tp₁ (κ₁ f) w) v → _≤w_ K₁ w (rs w v)) →
  (∀ {w v} → LgW K₁ w → Lg v → LgW K₁ (rs w v)) →
  (∀ w v → v ⊲ rs w v (inj₁ tt)) → ⊥
no-ownJoin f rs r≤ rLg rv =
  no-joinA (rs wJ (alim odA) (inj₁ tt) , rLg lgwJ Lg-odA (inj₁ tt) ,
            r≤ {wJ} {alim odA} (z⊲ (alim odA)) (inj₁ tt) , rv wJ (alim odA))

-- 三条两两可满足
pair≤Lg : Wd K₁ → A → Wd K₁
pair≤Lg w v = w

pair≤Lg-≤ : ∀ {w v} → _≤w_ K₁ w (pair≤Lg w v)
pair≤Lg-≤ = ≤w-rf K₁

pairLgV : Wd K₁ → A → Wd K₁
pairLgV w v (inj₁ tt) = v
pairLgV w v (inj₂ c) = w (inj₂ c)

pairLgV-lg : ∀ {w v} → LgW K₁ w → Lg v → LgW K₁ (pairLgV w v)
pairLgV-lg lw lv (inj₁ tt) = lv
pairLgV-lg lw lv (inj₂ c) = lw (inj₂ c)

pairLgV-v : ∀ w v → v ⊲ pairLgV w v (inj₁ tt)
pairLgV-v w v = C.self

pair≤V : Wd K₁ → A → Wd K₁
pair≤V w v (inj₁ tt) = alim (λ { zero → w (inj₁ tt) ; (suc _) → v })
pair≤V w v (inj₂ c) = w (inj₂ c)

pair≤V-≤ : ∀ {w v} → _≤w_ K₁ w (pair≤V w v)
pair≤V-≤ (inj₁ tt) = C.lim 0 C.self
pair≤V-≤ {w} (inj₂ c) = ≤w-rf (Lev c)

pair≤V-v : ∀ w v → v ⊲ pair≤V w v (inj₁ tt)
pair≤V-v w v = C.lim 1 C.self
```

## §6 结论 (按档)

- **[定理, 否定]** **`ownB₁-sep`**, `ownAll₁-sep` (`K₁`, 底拷贝), **`ownH₁-sep`** (`K₁`, 坐标是高度的种类), **`ownBΛ⁺-sep`**, **`ownHΛ⁺-sep`** (`step KΛc`): 精确置自己 (`rs-top`, 无前提) + 下标不同的拷贝无条件不降 (`rs-gr`) ⇒ 分离子. rs 任意依赖分量. **[条件 `FE₀`]** `ownB₁→WLPO`, `ownH₁→WLPO`, `ownBΛ⁺→WLPO`, `ownHΛ⁺→WLPO`.
- **[定理, 前提实例]** `topOnly₁-top`, `grOnly₁-gr`, `topOnlyH₁-top`, `grOnlyH₁-gr` (两半各自可满足; `topOnlyH₁` 只在 $v=\mathrm{hz}$ 处); `own∘-top`, `own∘-gr` (可判定下标上两半同时成立); `decJ→ownB₁` (给 `DecJ`, 整个前提可满足; `DecJ` 经典地成立, 判断).
- **[定理, 条件 `DecJ`]** **`decJ→KLv`**: `K₁` 的底拷贝 `κ₁ f` (下标含函数) 上有精确置自己, 别处不动的 `KLv`. **[定理]** `decJ→sep`, `decH→decJ`.
- **[定理, 否定]** **`no-ownJoin`**: 带前提不降 + 合法 + 旧站分量含 $v$ ⇒ ⊥. **[定理, 前提实例]** `pair≤Lg-≤`, `pairLgV-lg`/`pairLgV-v`, `pair≤V-≤`/`pair≤V-v` (三条两两可满足; `pair≤Lg` 是恒等, 自动合法).
- **只否定什么.** 否定: 精确置 + **无条件**不降 (对下标不同的同型拷贝) 的 rs 族 (对一切 $f$ 一致); 带前提不降 + 合法 + 一个分量含 $v$. **不否定**: `KLv` 形状 (精确置 + **带前提**的不降 + 合法) 的 rs, 不论是否依赖分量 (未走通; 条件实例 `decJ→KLv` 说 "⇒ ⊥" 不可证); 只对一个固定的 $f$ (不是一致的族) 的 rs; 可判定下标上的点更新; 有损.
- **[判断]** 对 "只剩一种" 的挑战: 原判断把 "精确置自己, 别处只增" 当作一种形状. 它其实分两种: 别处**无条件**只增 (本篇否定, 与 "留" 同型: 都是在不等的前提下要求别处的行为与自己处不同), 与别处**只在升的时候**只增 (`KLv` 的写法, 未否定也未构造). 剩下的未被否定的形状是后者.
