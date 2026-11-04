# 累加的毛刺: 哪些是写法带的, 哪些是定义逼的

> 不含记号. 账的数字在验收文件 [CumUpAcceptLedger](CumUpAcceptLedger.lagda.md).
>
> 上一轮的 `next η y = η ⊞ asuc ⌈y⌉` 和 `cs g (n+1) = cs g n ⊞ asuc (g (n+1))` 带三种东西:
>
> | 毛刺 | 判定 | 依据 |
> |---|---|---|
> | `next` 与 `cs` 里的 `asuc` (每步多 $+1$) | **写法带的** | 下面的 `Tᵇ` 去掉了, `HS-Tᵇ` 照样成立 |
> | 极限的第 $n$ 项是前 $n$ 项之和 (`cs`, `cB`) | **在 "下标不带证据" 的前提下未见替代** | `no-rd`: 对 `HS` 树, 逐点读出不一定字面合法 (这否定 "逐点读对一切 `HS` 树合法", 不否定 "对折叠的输出合法"); `dec⊲→LPO`: "判定字面步进, 只在缺失处补偿" 要 LPO |
> | 链上的 `η ⊞` | **未定** | `no-cum-⊲` 说累加不保第一位置, 是抽象的例子, 不是链上的点. 没有定理说链上不能去掉 `η ⊞`, 只是未走通 |
>
> 不带毛刺的另一边是 `toLevel`: 下标是输出的逐点读出 (`NoCumsum`), 代价是**定义依赖证书**: 层号 `lim` 的步进来自 `Uniform`, 而 $\psi$ 的派发读这个步进 (`NoCumsum` 的 `γ-indep` 说值不依赖, 字面树依赖). 这本账写在 [CumUp](CumUp.lagda.md).
>
> 全文 `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumUpClean where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
import OCF.Free.Level as FL
open FL using (HS; hz; hs; hl; _⊑⁰_; _≺_; ≺s; ≺l; FGH)
open import OCF.Barrier using (LPO)
open import OCF.Align.CumReadBase using (Ord₀; _⊞_; ⊞-fst; Lg-⊞; natO; ω₁)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲; O; Vs; Vc; o0; os; ol; oi; oe; Strict; ss; sl; Tg; rkT; keep; rise; inS; ≪S; ≪⊲; chainᵒ; Ω̇; tgS; lgS)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadCFThm using (Y; HS-Y; Y-mono)
open import OCF.Align.CumReadTop using (one)
```

## §1 去掉写法带的 $+1$

`cB` 是不加 1 的累加, `nextB` 是不加 1 的链. 第一位置与合法性照旧来自 `⊞-fst`, `Lg-⊞`: 证明里从来没用过那个 `asuc`.

```agda
cB : (ℕ → A) → ℕ → A
cB g zero = g 0
cB g (suc n) = cB g n ⊞ g (suc n)

cB-step : ∀ g n → cB g n ⊲ cB g (suc n)
cB-step g n = ⊞-fst (cB g n) (g (suc n))

Lg-cB : ∀ g → (∀ n → Lg (g n)) → ∀ n → Lg (cB g n)
Lg-cB g w zero = w 0
Lg-cB g w (suc n) = Lg-⊞ (cB g n) (g (suc n)) (Lg-cB g w n) (w (suc n))

cumB : Ord₀ → A
cumB FL.zero = azero
cumB (FL.suc a) = asuc (cumB a)
cumB (FL.lim f) = alim (cB (λ n → cumB (f n)))
cumB (FL.limᵢ () f)
cumB (FL.up () x)

Lg-cumB : ∀ y → Lg (cumB y)
Lg-cumB FL.zero = tt
Lg-cumB (FL.suc a) = Lg-cumB a
Lg-cumB (FL.lim f) = cB-step (λ n → cumB (f n)) , Lg-cB (λ n → cumB (f n)) (λ n → Lg-cumB (f n))
Lg-cumB (FL.limᵢ () f)
Lg-cumB (FL.up () x)

nextB : A → Ord₀ → A
nextB η y = η ⊞ cumB y

record IxB : Set where
  constructor ixB
  field
    η  : A
    lg : Lg η
    up : one ⊲ η
open IxB

stepB : IxB → Ord₀ → IxB
stepB (ixB η w u) y = ixB (nextB η y) (Lg-⊞ η (cumB y) w (Lg-cumB y)) (⊲-tr u (⊞-fst η (cumB y)))

valB : IxB → Ord₀
valB (ixB η w u) = Y η w

chainB : ℕ → IxB
chainB zero = stepB (ixB one tt C.self) (Y one tt)
chainB (suc n) = stepB (chainB n) (valB (chainB n))

ysB : ℕ → Ord₀
ysB zero = Y one tt
ysB (suc n) = valB (chainB n)

Tᵇ : Ord₀
Tᵇ = FL.lim ysB

HS-Tᵇ : HS Tᵇ
HS-Tᵇ = hl hy st
  where
  hy : ∀ n → HS (ysB n)
  hy zero = HS-Y one tt
  hy (suc n) = HS-Y (η (chainB n)) (lg (chainB n))
  st : ∀ n → ysB n ⊑⁰ ysB (suc n)
  st zero = Y-mono tt (lg (chainB 0)) (up (chainB 0))
  st (suc n) = Y-mono (lg (chainB n)) (lg (chainB (suc n))) (⊞-fst (η (chainB n)) (cumB (ysB (suc n))))
```

## §2 逐点读出

逐点读出 `rd` 不累加. 下面的 `x₀` 是 `HS` 树, 相邻两项值相等 ($\omega$ 的两个表示), 但读出来字面不合法. **这条定理否定的是 "`rd` 对一切 `HS` 树字面合法", 不是 "对折叠的输出字面合法".** 后者只是没有走通: 折叠输出的相邻项差的是逐点相等的函数, 既证不出 $\equiv$ (要函数外延), 也否定不了.

```agda
rd : Ord₀ → A
rd FL.zero = azero
rd (FL.suc a) = asuc (rd a)
rd (FL.lim f) = alim (λ n → rd (f n))
rd (FL.limᵢ () f)
rd (FL.up () x)

fω : ℕ → Ord₀
fω zero = ω₁
fω (suc _) = FL.lim (λ n → natO (suc n))

x₀ : Ord₀
x₀ = FL.lim fω

hnat : ∀ n → HS (natO n)
hnat zero = hz
hnat (suc n) = hs (hnat n)

natst : ∀ n → natO n ⊑⁰ natO (suc n)
natst n h = ≺s h

HS-x₀ : HS x₀
HS-x₀ = hl hy st
  where
  hy : ∀ n → HS (fω n)
  hy zero = hl hnat natst
  hy (suc _) = hl (λ n → hnat (suc n)) (λ n → natst (suc n))
  st : ∀ n → fω n ⊑⁰ fω (suc n)
  st zero (≺l n h) = ≺l n (≺s h)
  st (suc m) h = h

na : ℕ → A
na n = rd (natO n)

nlim : ∀ {a c} n → a ⊲ c → c ≡ na n → a ≡ alim na → ⊥
nlim zero C.self refl ()
nlim (suc n) C.self refl ()
nlim zero (C.suc P) () e
nlim zero (C.lim k P) () e
nlim (suc n) (C.suc P) refl e = nlim n P refl e
nlim (suc n) (C.lim k P) () e

hd : A → A
hd (alim f) = f 0
hd _ = azero

at : ℕ → A → A
at k (alim f) = f k
at k _ = azero

ne : asuc azero ≡ azero → ⊥
ne ()

aux-rd : ∀ {a c} → a ⊲ c → c ≡ alim (λ n → na (suc n)) → a ≡ alim na → ⊥
aux-rd C.self e e′ = ne (cong hd (trans (sym e) e′))
aux-rd (C.suc P) () e′
aux-rd (C.lim k P) e e′ = nlim (suc k) P (cong (at k) e) e′

no-rd : Lg (rd x₀) → ⊥
no-rd (st , _) = aux-rd (st 0) refl refl
```

## §3 只在缺失处补偿

"判定相邻两项的字面第一位置, 缺了才累加" 要判定 $\triangleleft$, 那就是 LPO. **这条否定的是 "用判定 $\triangleleft$ 做补偿" 这一条, 不否定不判定的补偿 (比如带证据).**

```agda
bit : Bool → A
bit true = one
bit false = azero

no-one : one ⊲ azero → ⊥
no-one ()

dec⊲→LPO : (∀ a b → Dec (a ⊲ b)) → LPO
dec⊲→LPO d α with d one (alim (λ n → bit (α n)))
... | yes (C.lim n p) = inj₁ (n , aux (α n) p)
  where
  aux : ∀ b → one ⊲ bit b → b ≡ true
  aux true _ = refl
  aux false q = ⊥-elim (no-one q)
... | no q = inj₂ (λ k → aux′ k (α k) refl)
  where
  aux′ : ∀ k b → α k ≡ b → α k ≡ false
  aux′ k false e = e
  aux′ k true e = ⊥-elim (q (C.lim k (subst′ e)))
    where
    subst′ : α k ≡ true → one ⊲ bit (α k)
    subst′ e′ rewrite e′ = C.self
```

## §4 更小的放大: 影子下标

`os` 产生的极限 $y\cdot n$ 相邻项字面就有第一位置, 不必累加. 但输出的树已经忘了哪个极限来自 `os`, 读出时分不清. 所以**在折叠时并行算下标** (`ψA`): `os` 处写 `repA` (不累加), 其余极限累加 (`cB`). 合法性 `LgA` 对项递归, 不用任何关于输出的定理. 其余极限的相邻项只有模 $\approx$ 的第一位置, 所以仍要累加.

这只减小放大, 不去掉它. `Tˢ` 的序数值这里**未证**.

```agda
repA : A → ℕ → A
repA y zero = azero
repA y (suc zero) = y
repA y (suc (suc m)) = repA y (suc m) ⊞ y

repA-step : ∀ y n → repA y n ⊲ repA y (suc n)
repA-step y zero = z⊲ y
repA-step y (suc m) = ⊞-fst (repA y (suc m)) y

Lg-repA : ∀ y → Lg y → ∀ n → Lg (repA y n)
Lg-repA y w zero = tt
Lg-repA y w (suc zero) = w
Lg-repA y w (suc (suc m)) = Lg-⊞ (repA y (suc m)) y (Lg-repA y w (suc m)) w

ψA  : ∀ {L} → Tg azero L → Lg L → O L → A
ψAS : ∀ {L a} (R : Strict a L) → Tg azero a → Lg a → Vs L R → A
ψAC : ∀ {b a} (P : a ⊲ b) → Tg azero a → Lg a → Vc b P → A

ψA T w o0 = one
ψA T w (os a) = alim (repA (ψA T w a))
ψA T w (ol F) = alim (cB (λ n → ψA T w (F n)))
ψA T w (oi {k} r h) with rkT r T w
... | keep ()
... | rise _ = alim (cB (λ n → ψA T w (h (inS (≪S r) (chainᵒ (λ z → C.ψ k (inj₁ (≪⊲ r)) w (h (inS (≪S r) z))) n)))))
ψA T w (oe R x) = ψAS R (tgS R T w) (lgS R w) x

ψAS (ss P) T w x = ψAC P T w x
ψAS (sl n P) T w x = ψAC P T w x

ψAC C.self T w x = ψA T w x
ψAC (C.suc P) T w x = ψAC P T w x
ψAC (C.lim n P) T w x = ψAC P T w x

LgA  : ∀ {L} (T : Tg azero L) (w : Lg L) (x : O L) → Lg (ψA T w x)
LgAS : ∀ {L a} (R : Strict a L) (T : Tg azero a) (w : Lg a) (x : Vs L R) → Lg (ψAS R T w x)
LgAC : ∀ {b a} (P : a ⊲ b) (T : Tg azero a) (w : Lg a) (x : Vc b P) → Lg (ψAC P T w x)

LgA T w o0 = tt
LgA T w (os a) = repA-step _ , Lg-repA _ (LgA T w a)
LgA T w (ol F) = cB-step _ , Lg-cB _ (λ n → LgA T w (F n))
LgA T w (oi r h) with rkT r T w
... | keep ()
... | rise _ = cB-step _ , Lg-cB _ (λ n → LgA T w (h _))
LgA T w (oe R x) = LgAS R (tgS R T w) (lgS R w) x

LgAS (ss P) T w x = LgAC P T w x
LgAS (sl n P) T w x = LgAC P T w x

LgAC C.self T w x = LgA T w x
LgAC (C.suc P) T w x = LgAC P T w x
LgAC (C.lim n P) T w x = LgAC P T w x

sh : ∀ η → Lg η → A
sh η w = ψA (inj₁ (z⊲ η)) w (Ω̇ η)

record IxS : Set where
  constructor ixS
  field
    ηs  : A
    lgs : Lg ηs
    ups : one ⊲ ηs
open IxS

stepS : IxS → IxS
stepS (ixS η w u) = ixS (η ⊞ sh η w) (Lg-⊞ η (sh η w) w (LgA _ w _)) (⊲-tr u (⊞-fst η (sh η w)))

chainS : ℕ → IxS
chainS zero = stepS (ixS one tt C.self)
chainS (suc n) = stepS (chainS n)

ysS : ℕ → Ord₀
ysS zero = Y one tt
ysS (suc n) = Y (ηs (chainS n)) (lgs (chainS n))

Tˢ : Ord₀
Tˢ = FL.lim ysS

HS-Tˢ : HS Tˢ
HS-Tˢ = hl hy st
  where
  hy : ∀ n → HS (ysS n)
  hy zero = HS-Y one tt
  hy (suc n) = HS-Y (ηs (chainS n)) (lgs (chainS n))
  st : ∀ n → ysS n ⊑⁰ ysS (suc n)
  st zero = Y-mono tt (lgs (chainS 0)) (ups (chainS 0))
  st (suc n) = Y-mono (lgs (chainS n)) (lgs (chainS (suc n))) (⊞-fst (ηs (chainS n)) (sh (ηs (chainS n)) (lgs (chainS n))))
```
