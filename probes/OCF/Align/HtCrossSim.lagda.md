# 跨高度 (一): 不看路径的关系

> 不含记号. 入口 [HtCross](HtCross.lagda.md). 给 [HtFeedTree](HtFeedTree.lagda.md) 的数据树一个**不看路径的关系**, 再证三件与折叠实例无关的事.
>
> - `RelA a x y` (`a : AccY L`): $x, y$ 形状相同, 但**保留节点 `ni R v`, `ni R′ v′` 的路径 $R, R'$ 可以不同** (只要求端点层 $k$ 相同); 分支在相关的参数上相关 (逻辑关系: 参数在低一层上相关). 对层的可达性递归定义, 所以低一层的关系是现成的. `Rl L = RelA accᴸ`.
> - `irr`: 关系不依赖用哪一个可达性证明.
> - `eq0`: 第 0 层的树没有节点, **在函数外延性 (`Funext`) 下相关推出相等**. 这是全篇唯一用到 `Funext` 的地方; 用它是因为世界是第 0 层输出的和 (`κc` 的 `v = sum W (z Y)`), 下游的类型依赖它, 只相关不够.
> - `Int`, `IW`, `Cut`, `Pre` (嵌入与世界上的切段) 保关系.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. `Funext` 是定理的前提, 不是公设.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtCrossSim where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; subst₂; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree

Funext : Set₁
Funext = ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g
```

## §1 关系

`Lo` 是低一层的关系 (对节点 $R$ 给出层 $k$ 上的关系). `si` 不要求两边的路径相同.

```agda
module _ {L : H} (Lo : ∀ {W k} → StH W k L → ∀ {u} → D k u → D k u → Set) where
  data SimD : ∀ {W} → D L W → D L W → Set where
    s0 : ∀ {W} → SimD (n0 {W = W}) n0
    s1 : ∀ {W} → SimD (n1 {W = W}) n1
    s⨾ : ∀ {W} {x x′ y y′ : D L W} → SimD x x′ → SimD y y′ → SimD (x ⨾ y) (x′ ⨾ y′)
    sl : ∀ {W} {d d′ : ℕ → D L W} → (∀ n → SimD (d n) (d′ n)) → SimD (nl d) (nl d′)
    si : ∀ {W k} {R R′ : StH W k L} {v : ∀ {W′} → W ⊲ W′ → Lg W′ → Vs L R W′ → D L W′} {v′ : ∀ {W′} → W ⊲ W′ → Lg W′ → Vs L R′ W′ → D L W′} →
         (∀ {W′} (p : W ⊲ W′) (l : Lg W′) y y′ → Lo R (outS R y) (outS R′ y′) → SimD (v p l y) (v′ p l y′)) → SimD (ni R v) (ni R′ v′)
    sκ : ∀ {W} {zz zz′ : NZ L} {u u′ : ∀ {c} → W ⊲ c → Lg c → D L c} →
         (∀ {c} (p : W ⊲ c) (l : Lg c) → SimD (u p l) (u′ p l)) → SimD (nκ zz u) (nκ zz′ u′)
    sw : ∀ {W₀ W} {p : W₀ ⊲ W} {x x′ : D L W₀} → SimD x x′ → SimD (nw p x) (nw p x′)

RelA : ∀ {L} → AccY L → ∀ {W} → D L W → D L W → Set
RelA (acc g) = SimD (λ R → RelA (g R))

Rl : ∀ L {W} → D L W → D L W → Set
Rl L = RelA (accᴸ {L})
```

**不依赖可达性证明.** 两个方向对两个证明交替递归.

```agda
irr : ∀ {L} (a b : AccY L) {W} {x y : D L W} → RelA a x y → RelA b x y
irr (acc f) (acc g) s0 = s0
irr (acc f) (acc g) s1 = s1
irr (acc f) (acc g) (s⨾ p q) = s⨾ (irr (acc f) (acc g) p) (irr (acc f) (acc g) q)
irr (acc f) (acc g) (sl h) = sl (λ n → irr (acc f) (acc g) (h n))
irr (acc f) (acc g) (si {R = R} h) = si (λ p l y y′ r → irr (acc f) (acc g) (h p l y y′ (irr (g R) (f R) r)))
irr (acc f) (acc g) (sκ h) = sκ (λ p l → irr (acc f) (acc g) (h p l))
irr (acc f) (acc g) (sw p) = sw (irr (acc f) (acc g) p)

toRl : ∀ {L} (a : AccY L) {W} {x y : D L W} → RelA a x y → Rl L x y
toRl a = irr a accᴸ

ofRl : ∀ {L} (a : AccY L) {W} {x y : D L W} → Rl L x y → RelA a x y
ofRl a = irr accᴸ a
```

**第 0 层: 相关推出相等** (前提 `Funext`). 第 0 层没有节点 (`StH W k hz` 空), 也没有 `nκ` (`NZ hz` 空).

```agda
eq0 : Funext → ∀ (a : AccY hz) {W} {x y : D hz W} → RelA a x y → x ≡ y
eq0 fe (acc g) s0 = refl
eq0 fe (acc g) s1 = refl
eq0 fe (acc g) (s⨾ p q) = cong₂ _⨾_ (eq0 fe (acc g) p) (eq0 fe (acc g) q)
eq0 fe (acc g) (sl h) = cong nl (fe (λ n → eq0 fe (acc g) (h n)))
eq0 fe (acc g) (si {R = ()} h)
eq0 fe (acc g) (sκ {zz = ()} h)
eq0 fe (acc g) (sw p) = cong (nw _) (eq0 fe (acc g) p)

refl0 : ∀ (a : AccY hz) {W} (x : D hz W) → RelA a x x
refl0 (acc g) n0 = s0
refl0 (acc g) n1 = s1
refl0 (acc g) (x ⨾ y) = s⨾ (refl0 (acc g) x) (refl0 (acc g) y)
refl0 (acc g) (nl d) = sl (λ n → refl0 (acc g) (d n))
refl0 (acc g) (ni () v)
refl0 (acc g) (nκ () u)
refl0 (acc g) (nw p x) = sw (refl0 (acc g) x)

≡→Rl0 : ∀ {W} {x y : D hz W} → x ≡ y → Rl hz x y
≡→Rl0 {x = x} refl = refl0 accᴸ x

drp-R : ∀ (a : AccY hz) {W W′} {x y : D hz W} → RelA a x y → Rl hz (drp {W} {W′} x) (drp {W} {W′} y)
drp-R (acc g) s0 = s0
drp-R (acc g) s1 = s1
drp-R (acc g) (s⨾ p q) = s⨾ (drp-R (acc g) p) (drp-R (acc g) q)
drp-R (acc g) (sl h) = sl (λ n → drp-R (acc g) (h n))
drp-R (acc g) (si {R = ()} h)
drp-R (acc g) (sκ {zz = ()} h)
drp-R (acc g) (sw p) = drp-R (acc g) p
```

## §2 小件

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

-- 把层 k 上的关系搬到节点 R, R′ 的分支参数上
conv : ∀ {L W k u} (a : AccY k) (R R′ : StH W k L) {x y : D k u} → Rl k x y → RelA a (outS R (inS R x)) (outS R′ (inS R′ y))
conv a R R′ {x} {y} r = subst₂ (RelA a) (sym (outS-inS R x)) (sym (outS-inS R′ y)) (ofRl a r)

-- Ω_t 与自己相关
Ωd-R : ∀ t (a : AccY t) {W} → RelA a (Ωd t {W}) (Ωd t {W})
Ωd-R hz (acc g) = s1
Ωd-R (hs b) (acc g) = s⨾ s1 (si (λ p l y y′ r → s1))
Ωd-R (hl f) (acc g) = s⨾ s1 (sl (λ n → si (λ p l y y′ r → s1)))
Ωd-R (hΩ h) (acc g) = s⨾ s1 (sκ (λ p l → si (λ p′ l′ y y′ r → s1)))

-- 层的严格第一位置是非自反的
irrS : ∀ {W k} → AccY k → StH W k k → ⊥
irrS (acc g) R = irrS (g R) R
```

## §3 嵌入与切段保关系

这几件在 `HtFeedTree` 里, 与折叠的实例无关. `mk` 两边可以不同 (只给路径).

```agda
Cut-R : ∀ {L : H} {W₀ W} {v₁ v₂ : ∀ {c} → W₀ ⊲ c → Lg c → D L c} → (∀ {c} (p : W₀ ⊲ c) (l : Lg c) → Rl L (v₁ p l) (v₂ p l)) →
        ∀ b {a} (P : a ⊲ b) (ab : W₀ ⊲ a) (lb : Lg b) (bW : b ⊲ W) → Rl L (Cut v₁ b P ab lb bW) (Cut v₂ b P ab lb bW)
Cut-R hv b C.self ab lb bW = s0
Cut-R hv (asuc c) (C.suc p) ab lb bW = s⨾ (Cut-R hv c p ab lb (⊲-tr (C.suc C.self) bW)) (sw (hv (⊲-tr ab p) lb))
Cut-R hv (alim f) (C.lim n p) ab (st , w) bW =
  s⨾ (Cut-R hv (f n) p ab (w n) (⊲-tr (C.lim n C.self) bW))
     (sl (λ m → Cut-R hv (f (suc (m + n))) (st (m + n)) (⊲-tr ab (tailP f st p m)) (w (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW)))
```

`Rl L = RelA (acc accK)` 是构造子形式, 直接展开成 `SimD`.

```agda
Pre-R : ∀ {L : H} {W₀ W} (q₀ : W₀ ⊲ W) {d₁ d₂ : ℕ → D L W₀} → (∀ n → Rl L (d₁ n) (d₂ n)) → ∀ n → Rl L (Pre q₀ d₁ n) (Pre q₀ d₂ n)
Pre-R q₀ h zero = s0
Pre-R q₀ h (suc n) = s⨾ (Pre-R q₀ h n) (sw (h n))

UR : ∀ (k ly : H) (W : A) → (∀ {W′} → W ⊲ W′ → Lg W′ → D k W′ → D ly W′) → (∀ {W′} → W ⊲ W′ → Lg W′ → D k W′ → D ly W′) → Set
UR k ly W u₁ u₂ = ∀ {W′} (p : W ⊲ W′) (l : Lg W′) {y₁ y₂ : D k W′} → Rl k y₁ y₂ → Rl ly (u₁ p l y₁) (u₂ p l y₂)

Int-R : ∀ {ly k W₀ W} (a₁ a₂ : AccY k) {x₁ x₂ : D k W₀} → Rl k x₁ x₂ → (q₀ : W₀ ⊲ W) (lW : Lg W) (zy₁ zy₂ : NZ ly)
        (mk₁ mk₂ : ∀ {W₁ j} → W ⊲ W₁ → StH W₁ j k → StH W₁ j ly) {u₁ u₂ : ∀ {W′} → W ⊲ W′ → Lg W′ → D k W′ → D ly W′} → UR k ly W u₁ u₂ →
        {w₁ w₂ : D k W} → Rl k w₁ w₂ → Rl ly (Int a₁ x₁ q₀ lW zy₁ mk₁ u₁ w₁) (Int a₂ x₂ q₀ lW zy₂ mk₂ u₂ w₂)
IW-R  : ∀ {ly k W₀ W} (a₁ a₂ : AccY k) {v₁ v₂ : ∀ {c} → W₀ ⊲ c → Lg c → D k c} → (∀ {c} (p : W₀ ⊲ c) (l : Lg c) → Rl k (v₁ p l) (v₂ p l)) →
        ∀ b {a} (P : a ⊲ b) (ap : W₀ ⊲ a) (lb : Lg b) (bW : b ⊲ W) (lW : Lg W) (zy₁ zy₂ : NZ ly)
        (mk₁ mk₂ : ∀ {W₁ j} → W ⊲ W₁ → StH W₁ j k → StH W₁ j ly) {u₁ u₂ : ∀ {W′} → W ⊲ W′ → Lg W′ → D k W′ → D ly W′} → UR k ly W u₁ u₂ →
        {w₁ w₂ : D k W} → Rl k w₁ w₂ → Rl ly (IW a₁ v₁ b P ap lb bW lW zy₁ mk₁ u₁ w₁) (IW a₂ v₂ b P ap lb bW lW zy₂ mk₂ u₂ w₂)

Int-R a₁ a₂ s0 q₀ lW zy₁ zy₂ mk₁ mk₂ hu hw = s0
Int-R a₁ a₂ s1 q₀ lW zy₁ zy₂ mk₁ mk₂ hu hw = hu C.self lW hw
Int-R a₁ a₂ (s⨾ hx hy) q₀ lW zy₁ zy₂ mk₁ mk₂ hu hw =
  s⨾ (Int-R a₁ a₂ hx q₀ lW zy₁ zy₂ mk₁ mk₂ hu hw) (Int-R a₁ a₂ hy q₀ lW zy₁ zy₂ mk₁ mk₂ hu (s⨾ hw (sw hx)))
Int-R a₁ a₂ (sl {d = d₁} {d′ = d₂} h) q₀ lW zy₁ zy₂ mk₁ mk₂ hu hw =
  sl (λ n → Int-R a₁ a₂ (h n) q₀ lW zy₁ zy₂ mk₁ mk₂ hu (s⨾ hw (Pre-R q₀ h n)))
Int-R a₁ a₂ (sw {p = p} hx) q₀ lW zy₁ zy₂ mk₁ mk₂ hu hw = Int-R a₁ a₂ hx (⊲-tr p q₀) lW zy₁ zy₂ mk₁ mk₂ hu hw
Int-R (acc g₁) (acc g₂) (si {R = R₁} {R′ = R₂} h) q₀ lW zy₁ zy₂ mk₁ mk₂ hu hw =
  si (λ p lW′ y₁ y₂ r →
    Int-R (acc g₁) (acc g₂)
      (h (⊲-tr q₀ p) lW′ _ _ (conv (accK R₁) R₁ R₂ (toRl (accK (mk₁ C.self (Kup q₀ R₁))) r)))
      C.self lW′ zy₁ zy₂ (λ p′ → mk₁ (⊲-tr p p′)) (λ p′ → mk₂ (⊲-tr p p′)) (λ p′ → hu (⊲-tr p p′))
      (s⨾ (sw hw) (Int-R (g₁ R₁) (g₂ R₂) (toRl (accK (mk₁ C.self (Kup q₀ R₁))) r) C.self lW′ (NZ-S R₁) (NZ-S R₂)
                     (mkOf R₁ (⊲-tr q₀ p)) (mkOf R₂ (⊲-tr q₀ p))
                     (λ p′ l′ r′ → h (⊲-tr (⊲-tr q₀ p) p′) l′ _ _ (conv (accK R₁) R₁ R₂ r′)) s0)))
Int-R {W = W} a₁ a₂ (sκ {zz = zz₁} {zz′ = zz₂} h) q₀ lW zy₁ zy₂ mk₁ mk₂ hu hw =
  s⨾ (IW-R a₁ a₂ h W q₀ C.self lW C.self lW zy₁ zy₂ mk₁ mk₂ hu hw)
     (sκ (λ {c} p lc →
       Int-R a₁ a₂ (h (⊲-tr q₀ p) lc) C.self lc zy₁ zy₂ (λ p′ → mk₁ (⊲-tr p p′)) (λ p′ → mk₂ (⊲-tr p p′)) (λ p′ → hu (⊲-tr p p′))
         (s⨾ (sw hw) (Cut-R h c (⊲-tr q₀ p) C.self lc C.self))))

IW-R a₁ a₂ hv b C.self ap lb bW lW zy₁ zy₂ mk₁ mk₂ hu hw = s0
IW-R a₁ a₂ hv (asuc c) (C.suc p) ap lb bW lW zy₁ zy₂ mk₁ mk₂ hu hw =
  s⨾ (IW-R a₁ a₂ hv c p ap lb (⊲-tr (C.suc C.self) bW) lW zy₁ zy₂ mk₁ mk₂ hu hw)
     (Int-R a₁ a₂ (hv (⊲-tr ap p) lb) (⊲-tr (C.suc C.self) bW) lW zy₁ zy₂ mk₁ mk₂ hu
        (s⨾ hw (Cut-R hv c p ap lb (⊲-tr (C.suc C.self) bW))))
IW-R a₁ a₂ hv (alim f) (C.lim n p) ap (st , wl) bW lW zy₁ zy₂ mk₁ mk₂ hu hw =
  s⨾ (IW-R a₁ a₂ hv (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bW) lW zy₁ zy₂ mk₁ mk₂ hu hw)
     (sl (λ m → IW-R a₁ a₂ hv (f (suc (m + n))) (st (m + n)) (⊲-tr ap (tailP f st p m)) (wl (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW) lW zy₁ zy₂ mk₁ mk₂ hu
         (s⨾ hw (Cut-R hv (f (m + n)) (tailP f st p m) ap (wl (m + n)) (⊲-tr (C.lim (m + n) C.self) bW)))))
```
