# 高度的高度 (四): 不能有的形状

> 不含记号. 入口 [HtTower](HtTower.lagda.md). 四条否定, 都是编译过的定理, 各自只否定写明的形状.
>
> 1. **`no-self`**: 对一切种类结构 `S`, 一切种类 $\kappa$, 分支 $d$ 不能在某个坐标上取回自己所在的节点 ($d\,c\equiv\mathrm{h\Omega}\,\kappa\,d$). 推论 **`no-retract`**: 没有种类的坐标里装着全部高度的收缩 ($d\circ e=\mathrm{id}$). 这是 Burali-Forti 的形状, 只用到高度的良基 (结构子项), 不用合法, 不用世界. 它杀掉 "一个高度类型, 分支取遍高度自己" 的一切编码 (不只是 Agda 的正性检查拒绝的那种直接写法): 塔的每一级都只能以**更低的级**为坐标, 塔不会在一个种类结构里封口 (`U` 里没有以 `HB U` 为坐标的种类, 即没有 "$\Lambda$ 之上的 $\Omega$").
> 2. **`drop-Ω`**: [HtTowerCont](HtTowerCont.lagda.md) 的 `ContB` 去掉 `c-Ω` (旧种类的 $\Omega$-极限处连续), 保留其余四条, 有不合法的反例. 坐标是高度时, 连续要对坐标类型的**每一种**极限.
> 3. **`no-naive-diag`**: 逐级的塔 `Ωn k` (各级独立地取 "新种类上的恒等分支") 在并 `sup ℕ` 里互相不是字面的第一位置, 所以它们的 ℕ-对角不合法 (`naive-illegal`). 只杀 "各级各自写, 再取并" 这一种写法; [HtTowerU](HtTowerU.lagda.md) 的 `θ` 把下一级接在上一级后面 (`⊞`), 对角合法.
> 4. **`no-joinᴮ`**, **`no-joinA`**: 任一种类结构的任一合法世界里, 两个合法高度 (偶数列与奇数列的 ℕ-极限) 没有合法的字面公共上界; 坐标是 `A` 时同样. 世界的每个分量 (`A` 或高度) 都没有字面的并. 这是折叠的第一个障碍的依据之一 (入口).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtTowerNeg where

open import Data.Nat using (ℕ; zero; suc; pred)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; cmpF)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (ContB; ctB)
open import OCF.Align.HtTowerU using (Sn; Ωn)
```

## §1 分支不能取回自己

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

  no-retract : ∀ κ (e : HB S → E S κ) (d : E S κ → HB S) → ¬ (∀ x → d (e x) ≡ x)
  no-retract κ e d sec = no-self κ d (e (hΩ κ d)) (sec (hΩ κ d))
```

## §2 去掉旧种类处的连续

反例 `gω` 在 `step S₀` 的新种类上: 后继与 ℕ-极限照搬, 旧种类的 $\Omega$-极限一律给 $0$. 坐标 $1\lhd y$ ($y$ 是常值 $1$ 的 $\Omega$-极限) 被送到 $1\not\lhd 0$.

```agda
gω : HB S₀ → HB (step S₀)
gω hz = hz
gω (hs x) = hs (gω x)
gω (hl f) = hl (λ n → gω (f n))
gω (hΩ κ h) = hz

yΩ : HB S₀
yΩ = hΩ tt (λ _ → hs hz)

Lg-yΩ : LgB yΩ
Lg-yΩ = (λ lw e e′ p → hself) , (λ c lc → tt)

one⊲y : hs hz ⊲[ azero ] yΩ
one⊲y = hLim {S₀} {c = azero} C.self hself

gω-not-Ω : ¬ (∀ κ h → gω (hΩ κ h) ≡ hΩ (inj₁ κ) (λ c → gω (h c)))
gω-not-Ω all with all tt (λ _ → hz)
... | ()

gω-not-Lg : ¬ LgB {step S₀} (hΩ (inj₂ tt) gω)
gω-not-Lg (mo , _) with mo {azero , yΩ} (tt , Lg-yΩ) one⊲y hself one⊲y
... | ()

drop-Ω :
  (∀ f → gω (hl f) ≡ hl (λ n → gω (f n))) × (∀ x {w} → gω x ⊲[ w ] gω (hs x)) × LgB (gω hz) ×
  (∀ x → LgB (gω x) → LgB (gω (hs x))) ×
  ¬ (∀ κ h → gω (hΩ κ h) ≡ hΩ (inj₁ κ) (λ c → gω (h c))) × ¬ LgB {step S₀} (hΩ (inj₂ tt) gω)
drop-Ω = (λ f → refl) , (λ x → hsuc hself) , tt , (λ x l → l) , gω-not-Ω , gω-not-Lg
```

## §3 逐级独立写的塔, 对角不合法

`AllK j x`: $x$ 里一切 $\Omega$-节点的种类都在第 $j$ 个分量. 第一位置保持它; 第 $j$ 个分量嵌进来的高度都满足它. `Ωn k` 嵌进来是第 $k$ 个分量, `Ωn (k+1)` 是第 $k+1$ 个, 前者不能是后者的第一位置.

```agda
FN : ℕ → KS
FN k = Sn (suc k)

ιN : ∀ k → HB (FN k) → HB (sup ℕ FN)
ιN k = ι {ℕ} {FN} k

AllK : ℕ → HB (sup ℕ FN) → Set
AllK j hz = ⊤
AllK j (hs x) = AllK j x
AllK j (hl f) = ∀ n → AllK j (f n)
AllK j (hΩ κ g) = (proj₁ κ ≡ j) × (∀ c → AllK j (g c))

allK-ι : ∀ j x → AllK j (ιN j x)
allK-ι j hz = tt
allK-ι j (hs x) = allK-ι j x
allK-ι j (hl f) = λ n → allK-ι j (f n)
allK-ι j (hΩ κ g) = refl , (λ c → allK-ι j (g c))

allK⊲ : ∀ {j a b w} → a ⊲[ w ] b → AllK j b → AllK j a
allK⊲ hself h = h
allK⊲ (hsuc p) h = allK⊲ p h
allK⊲ (hlim n p) h = allK⊲ p (h n)
allK⊲ (hLim e p) h = allK⊲ p (proj₂ h _)

k≢sk : ∀ k → ¬ (k ≡ suc k)
k≢sk zero ()
k≢sk (suc k) e = k≢sk k (cong pred e)

no-naive-diag : ∀ {w} k → ¬ (ιN k (Ωn k) ⊲[ w ] ιN (suc k) (Ωn (suc k)))
no-naive-diag k p = k≢sk k (proj₁ (allK⊲ p (allK-ι (suc k) (Ωn (suc k)))))

-- 一个世界: 每一级取最小的分量
dW : ∀ k → Wd (Sn k)
dW zero = azero
dW (suc k) = dW k , hz

naive-illegal : ¬ LgB (hl (λ k → ιN k (Ωn k)))
naive-illegal (st , _) = no-naive-diag 0 (st {λ k → dW (suc k)} 0)
```

## §4 没有字面的并

偶数列与奇数列. 两条引理各对第一位置的证明归纳, 用等式携带下标 (下标里有函数, 不能直接合一).

```agda
module _ {S : KS} where
  evᴴ odᴴ : ℕ → HB S
  evᴴ zero = hz
  evᴴ (suc n) = hs (hs (evᴴ n))
  odᴴ zero = hs hz
  odᴴ (suc n) = hs (hs (odᴴ n))

  Lg-num : ∀ (f : ℕ → HB S) → (∀ n → LgB (f n)) → (∀ {w} n → f n ⊲[ w ] f (suc n)) → LgB (hl f)
  Lg-num f l st = st , l

  lg-ev : ∀ n → LgB (evᴴ n)
  lg-ev zero = tt
  lg-ev (suc n) = lg-ev n

  lg-od : ∀ n → LgB (odᴴ n)
  lg-od zero = tt
  lg-od (suc n) = lg-od n

  Lg-ev : LgB (hl evᴴ)
  Lg-ev = Lg-num evᴴ lg-ev (λ n → hsuc (hsuc hself))

  Lg-od : LgB (hl odᴴ)
  Lg-od = Lg-num odᴴ lg-od (λ n → hsuc (hsuc hself))

  NatH : HB S → Set
  NatH hz = ⊤
  NatH (hs x) = NatH x
  NatH (hl _) = ⊥
  NatH (hΩ _ _) = ⊥

  nat-ev : ∀ n → NatH (evᴴ n)
  nat-ev zero = tt
  nat-ev (suc n) = nat-ev n

  nat-od : ∀ n → NatH (odᴴ n)
  nat-od zero = tt
  nat-od (suc n) = nat-od n

  no-lim⊲nat : ∀ {g w x} → hl g ⊲[ w ] x → NatH x → ⊥
  no-lim⊲nat hself ()
  no-lim⊲nat (hsuc p) n = no-lim⊲nat p n
  no-lim⊲nat (hlim m p) ()
  no-lim⊲nat (hLim e p) ()

  hd : HB S → HB S
  hd (hl f) = f 0
  hd x = x

  at : HB S → ℕ → HB S
  at (hl f) n = f n
  at x n = x

  s≢z : ¬ (hs {S} hz ≡ hz)
  s≢z ()

  no-into : ∀ {w a b} (u v : ℕ → HB S) → (∀ n → NatH (v n)) → ¬ (u 0 ≡ v 0) →
            a ⊲[ w ] b → b ≡ hl v → a ≡ hl u → ⊥
  no-into u v nv d hself eb ea = d (cong hd (trans (sym ea) eb))
  no-into u v nv d (hsuc p) () ea
  no-into {w} {a} u v nv d (hlim {f = f} n p) eb ea =
    no-lim⊲nat (subst (λ z → z ⊲[ w ] v n) ea (subst (λ z → a ⊲[ w ] z) (cong (λ h → at h n) eb) p)) (nv n)
  no-into u v nv d (hLim e p) () ea

  no-joinᴮ : ∀ {w} → LgW S w → ¬ Σ (HB S) (λ b → LgB b × (hl evᴴ ⊲[ w ] b) × (hl odᴴ ⊲[ w ] b))
  no-joinᴮ lw (b , lb , p , q) with cmpB p q lw lb
  ... | inj₁ od⊲ev = no-into odᴴ evᴴ nat-ev s≢z od⊲ev refl refl
  ... | inj₂ ev⊲od = no-into evᴴ odᴴ nat-od (λ e → s≢z (sym e)) ev⊲od refl refl
```

坐标是 `A` 时同样 (`A` 是 `S₀` 的坐标, 也是一切世界的第一个分量).

```agda
evA odA : ℕ → A
evA zero = azero
evA (suc n) = asuc (asuc (evA n))
odA zero = asuc azero
odA (suc n) = asuc (asuc (odA n))

Lg-evA : Lg (alim evA)
Lg-evA = (λ n → C.suc (C.suc C.self)) , lg
  where
  lg : ∀ n → Lg (evA n)
  lg zero = tt
  lg (suc n) = lg n

Lg-odA : Lg (alim odA)
Lg-odA = (λ n → C.suc (C.suc C.self)) , lg
  where
  lg : ∀ n → Lg (odA n)
  lg zero = tt
  lg (suc n) = lg n

NatA : A → Set
NatA azero = ⊤
NatA (asuc x) = NatA x
NatA (alim _) = ⊥

natA-ev : ∀ n → NatA (evA n)
natA-ev zero = tt
natA-ev (suc n) = natA-ev n

natA-od : ∀ n → NatA (odA n)
natA-od zero = tt
natA-od (suc n) = natA-od n

no-limA : ∀ {g x} → alim g ⊲ x → NatA x → ⊥
no-limA C.self ()
no-limA (C.suc p) n = no-limA p n
no-limA (C.lim m p) ()

hdA : A → A
hdA (alim f) = f 0
hdA x = x

atA : A → ℕ → A
atA (alim f) n = f n
atA x n = x

no-intoA : ∀ {a b} (u v : ℕ → A) → (∀ n → NatA (v n)) → ¬ (u 0 ≡ v 0) → a ⊲ b → b ≡ alim v → a ≡ alim u → ⊥
no-intoA u v nv d C.self eb ea = d (cong hdA (trans (sym ea) eb))
no-intoA u v nv d (C.suc p) () ea
no-intoA {a} u v nv d (C.lim {f = f} n p) eb ea =
  no-limA (subst (λ z → z ⊲ v n) ea (subst (λ z → a ⊲ z) (cong (λ h → atA h n) eb) p)) (nv n)

sA≢z : ¬ (asuc azero ≡ azero)
sA≢z ()

no-joinA : ¬ Σ A (λ c → Lg c × (alim evA ⊲ c) × (alim odA ⊲ c))
no-joinA (c , lc , p , q) with cmpF p q lc
... | inj₁ od⊲ev = no-intoA odA evA natA-ev sA≢z od⊲ev refl refl
... | inj₂ ev⊲od = no-intoA evA odA natA-od (λ e → sA≢z (sym e)) ev⊲od refl refl
```
