# 两种种类的单调 (一): 不含回灌的互模拟

> 入口 [TpPort](TpPort.lagda.md). 不含记号. **生成文件**: 由 `probes/Survey/scripts/tpport/mk_tpport.py` 从 [HtCrossVSim](HtCrossVSim.lagda.md) 逐字节可重生成 (公共变换在同目录的 `tpgen.py`). 公共变换只改: 世界的类型与序 (`A`, `_⊲_` 换成两种种类的 `Wd₂`, `_≤ʷ_`; `C.self`, `C.⊲-tr` 换成 `≤rf`, `≤tr`; `Lg` 换成 `LgW₂`), 高度的类型 (`H` 换成 `Ht`, `LgH` 换成 `LgB`, `hΩ g` 换成 `hΩ κ g`), 模块参数多一个 `oΛ` (第 1 层是实例在一切世界里的第一位置, 两种种类的折叠要它), 数据树多一个构造子 `nμ` (每个 `nκ` 的空子句后加一句), `Step` 换名 `Stp`. 证明逐句不变. `Free` 对两种种类的 Ω-极限都取 $\bot$; `Int-R` 多两个参数 `zz₁`, `zz₂` (两种种类的 `Int` 的 `NZ₁` 搬运).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`, 不改树、折叠、合法性.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TpPortSim where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; subst₂; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans)
open import OCF.Align.HtTowerTy using (HB; hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; LgB)
open import OCF.Align.HtTowerFTree renaming (_≤_ to _≤ʷ_)

```
```agda
Free : Ht → Set
Free hz = ⊤
Free (hs b) = Free b
Free (hl f) = ∀ n → Free (f n)
Free (hΩ _ g) = ⊥

free⊲ : ∀ {a b W} → a ⊲[ W ] b → Free b → Free a
free⊲ hself fb = fb
free⊲ (hsuc p) fb = free⊲ p fb
free⊲ (hlim n p) fb = free⊲ p (fb n)
free⊲ (hLim e p) ()
```
```agda
module _ {L : Ht} (Lo : ∀ {W k} → StH W k L → ∀ {u} → D k u → D k u → Set) where
  data SimD : ∀ {W} → D L W → D L W → Set where
    s0 : ∀ {W} → SimD (n0 {W = W}) n0
    s1 : ∀ {W} → SimD (n1 {W = W}) n1
    s⨾ : ∀ {W} {x x′ y y′ : D L W} → SimD x x′ → SimD y y′ → SimD (x ⨾ y) (x′ ⨾ y′)
    sl : ∀ {W} {d d′ : ℕ → D L W} → (∀ n → SimD (d n) (d′ n)) → SimD (nl d) (nl d′)
    si : ∀ {W k} {R R′ : StH W k L} {v : ∀ {W′} → W ≤ʷ W′ → LgW₂ W′ → Vs L R W′ → D L W′} {v′ : ∀ {W′} → W ≤ʷ W′ → LgW₂ W′ → Vs L R′ W′ → D L W′} →
         (∀ {W′} (p : W ≤ʷ W′) (l : LgW₂ W′) y y′ → Lo R (outS R y) (outS R′ y′) → SimD (v p l y) (v′ p l y′)) → SimD (ni R v) (ni R′ v′)
    sw : ∀ {W₀ W} {p : W₀ ≤ʷ W} {x x′ : D L W₀} → SimD x x′ → SimD (nw p x) (nw p x′)

RelA : ∀ {L} → AccY L → ∀ {W} → D L W → D L W → Set
RelA (acc g) = SimD (λ R → RelA (g R))

Rl : ∀ L {W} → D L W → D L W → Set
Rl L = RelA (accᴸ {L})

irr : ∀ {L} (a b : AccY L) {W} {x y : D L W} → RelA a x y → RelA b x y
irr (acc f) (acc g) s0 = s0
irr (acc f) (acc g) s1 = s1
irr (acc f) (acc g) (s⨾ p q) = s⨾ (irr (acc f) (acc g) p) (irr (acc f) (acc g) q)
irr (acc f) (acc g) (sl h) = sl (λ n → irr (acc f) (acc g) (h n))
irr (acc f) (acc g) (si {R = R} h) = si (λ p l y y′ r → irr (acc f) (acc g) (h p l y y′ (irr (g R) (f R) r)))
irr (acc f) (acc g) (sw p) = sw (irr (acc f) (acc g) p)

toRl : ∀ {L} (a : AccY L) {W} {x y : D L W} → RelA a x y → Rl L x y
toRl a = irr a accᴸ

ofRl : ∀ {L} (a : AccY L) {W} {x y : D L W} → Rl L x y → RelA a x y
ofRl a = irr accᴸ a
```
```agda
sym0 : ∀ (a : AccY hz) {W} {x y : D hz W} → RelA a x y → RelA a y x
sym0 (acc g) s0 = s0
sym0 (acc g) s1 = s1
sym0 (acc g) (s⨾ p q) = s⨾ (sym0 (acc g) p) (sym0 (acc g) q)
sym0 (acc g) (sl h) = sl (λ n → sym0 (acc g) (h n))
sym0 (acc g) (si {R = ()} h)
sym0 (acc g) (sw p) = sw (sym0 (acc g) p)

sum-R : ∀ (a : AccY hz) {W} {x y : D₀ W} → RelA a x y → ∀ {b b′} → b ≤ b′ → sum b x ≤ sum b′ y
pt-R  : ∀ (a : AccY hz) {W} {d d′ : ℕ → D₀ W} → (∀ n → RelA a (d n) (d′ n)) → ∀ {b b′} → b ≤ b′ → ∀ n → pt b d n ≤ pt b′ d′ n
sum-R (acc g) s0 h = h
sum-R (acc g) s1 h = s≤ h
sum-R (acc g) (s⨾ p q) h = sum-R (acc g) q (sum-R (acc g) p h)
sum-R (acc g) (sl hd) h = l≤ (λ n → ≤l n (pt-R (acc g) hd h n))
sum-R (acc g) (si {R = ()} _) h
sum-R (acc g) (sw p) h = sum-R (acc g) p h
pt-R a hd h zero = h
pt-R a hd h (suc n) = sum-R a (hd n) (pt-R a hd h n)

sum-R′ : ∀ (a : AccY hz) {W} {x y : D₀ W} → RelA a x y → ∀ {b b′} → b′ ≤ b → sum b′ y ≤ sum b x
sum-R′ a r h = sum-R a (sym0 a r) h

refl0 : ∀ (a : AccY hz) {W} (x : D hz W) → RelA a x x
refl0 (acc g) n0 = s0
refl0 (acc g) n1 = s1
refl0 (acc g) (x ⨾ y) = s⨾ (refl0 (acc g) x) (refl0 (acc g) y)
refl0 (acc g) (nl d) = sl (λ n → refl0 (acc g) (d n))
refl0 (acc g) (ni () v)
refl0 (acc g) (nκ () u)
refl0 (acc g) (nμ () u)
refl0 (acc g) (nw p x) = sw (refl0 (acc g) x)
```
```agda
outC-inC : ∀ {b W a u} (P : a ⊲[ W ] b) (x : D a u) → outC P (inC P x) ≡ x
outC-inC hself x = refl
outC-inC (hsuc P) x = outC-inC P x
outC-inC (hlim n P) x = outC-inC P x
outC-inC (hLim e P) x = outC-inC P x

outS-inS : ∀ {L W k u} (R : StH W k L) (x : D k u) → outS R (inS R x) ≡ x
outS-inS (ss P) x = outC-inC P x
outS-inS (sl n P) x = outC-inC P x
outS-inS (sL e P) x = outC-inC P x

conv : ∀ {L W k u} (a : AccY k) (R R′ : StH W k L) {x y : D k u} → Rl k x y → RelA a (outS R (inS R x)) (outS R′ (inS R′ y))
conv a R R′ {x} {y} r = subst₂ (RelA a) (sym (outS-inS R x)) (sym (outS-inS R′ y)) (ofRl a r)

-- Ω_t 与自己相关, t 不含 Ω-极限
Ωd-R : ∀ t → Free t → (a : AccY t) → ∀ {W} → RelA a (Ωd t {W}) (Ωd t {W})
Ωd-R hz ft (acc g) = s1
Ωd-R (hs b) ft (acc g) = s⨾ s1 (si (λ p l y y′ r → s1))
Ωd-R (hl f) ft (acc g) = s⨾ s1 (sl (λ n → si (λ p l y y′ r → s1)))
Ωd-R (hΩ _ h) () a

irrS : ∀ {W k} → AccY k → StH W k k → ⊥
irrS (acc g) R = irrS (g R) R
```
```agda
Pre-R : ∀ {L : Ht} {W₀ W} (q₀ : W₀ ≤ʷ W) {d₁ d₂ : ℕ → D L W₀} → (∀ n → Rl L (d₁ n) (d₂ n)) → ∀ n → Rl L (Pre q₀ d₁ n) (Pre q₀ d₂ n)
Pre-R q₀ h zero = s0
Pre-R q₀ h (suc n) = s⨾ (Pre-R q₀ h n) (sw (h n))

UR : ∀ (k ly : Ht) (W : Wd₂) → (∀ {W′} → W ≤ʷ W′ → LgW₂ W′ → D k W′ → D ly W′) → (∀ {W′} → W ≤ʷ W′ → LgW₂ W′ → D k W′ → D ly W′) → Set
UR k ly W u₁ u₂ = ∀ {W′} (p : W ≤ʷ W′) (l : LgW₂ W′) {y₁ y₂ : D k W′} → Rl k y₁ y₂ → Rl ly (u₁ p l y₁) (u₂ p l y₂)

Int-R : ∀ {ly k W₀ W} (a₁ a₂ : AccY k) {x₁ x₂ : D k W₀} → Rl k x₁ x₂ → (q₀ : W₀ ≤ʷ W) (lW : LgW₂ W) (zy₁ zy₂ : NZ ly) (zz₁ zz₂ : NZ₁ k → NZ₁ ly)
        (mk₁ mk₂ : ∀ {W₁ j} → W ≤ʷ W₁ → StH W₁ j k → StH W₁ j ly) {u₁ u₂ : ∀ {W′} → W ≤ʷ W′ → LgW₂ W′ → D k W′ → D ly W′} → UR k ly W u₁ u₂ →
        {w₁ w₂ : D k W} → Rl k w₁ w₂ → Rl ly (Int a₁ x₁ q₀ lW zy₁ zz₁ mk₁ u₁ w₁) (Int a₂ x₂ q₀ lW zy₂ zz₂ mk₂ u₂ w₂)
Int-R a₁ a₂ s0 q₀ lW zy₁ zy₂ zz₁ zz₂ mk₁ mk₂ hu hw = s0
Int-R a₁ a₂ s1 q₀ lW zy₁ zy₂ zz₁ zz₂ mk₁ mk₂ hu hw = hu ≤rf lW hw
Int-R a₁ a₂ (s⨾ hx hy) q₀ lW zy₁ zy₂ zz₁ zz₂ mk₁ mk₂ hu hw =
  s⨾ (Int-R a₁ a₂ hx q₀ lW zy₁ zy₂ zz₁ zz₂ mk₁ mk₂ hu hw) (Int-R a₁ a₂ hy q₀ lW zy₁ zy₂ zz₁ zz₂ mk₁ mk₂ hu (s⨾ hw (sw hx)))
Int-R a₁ a₂ (sl {d = d₁} {d′ = d₂} h) q₀ lW zy₁ zy₂ zz₁ zz₂ mk₁ mk₂ hu hw =
  sl (λ n → Int-R a₁ a₂ (h n) q₀ lW zy₁ zy₂ zz₁ zz₂ mk₁ mk₂ hu (s⨾ hw (Pre-R q₀ h n)))
Int-R a₁ a₂ (sw {p = p} hx) q₀ lW zy₁ zy₂ zz₁ zz₂ mk₁ mk₂ hu hw = Int-R a₁ a₂ hx (≤tr p q₀) lW zy₁ zy₂ zz₁ zz₂ mk₁ mk₂ hu hw
Int-R (acc g₁) (acc g₂) (si {R = R₁} {R′ = R₂} h) q₀ lW zy₁ zy₂ zz₁ zz₂ mk₁ mk₂ hu hw =
  si (λ p lW′ y₁ y₂ r →
    Int-R (acc g₁) (acc g₂)
      (h (≤tr q₀ p) lW′ _ _ (conv (accK R₁) R₁ R₂ (toRl (accK (mk₁ ≤rf (Kup q₀ R₁))) r)))
      ≤rf lW′ zy₁ zy₂ zz₁ zz₂ (λ p′ → mk₁ (≤tr p p′)) (λ p′ → mk₂ (≤tr p p′)) (λ p′ → hu (≤tr p p′))
      (s⨾ (sw hw) (Int-R (g₁ R₁) (g₂ R₂) (toRl (accK (mk₁ ≤rf (Kup q₀ R₁))) r) ≤rf lW′ (NZ-S R₁) (NZ-S R₂) (NZ₁-S R₁) (NZ₁-S R₂)
                     (mkOf R₁ (≤tr q₀ p)) (mkOf R₂ (≤tr q₀ p))
                     (λ p′ l′ r′ → h (≤tr (≤tr q₀ p) p′) l′ _ _ (conv (accK R₁) R₁ R₂ r′)) s0)))
```
