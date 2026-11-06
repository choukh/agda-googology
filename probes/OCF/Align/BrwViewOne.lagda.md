# 布劳威尔树的 View (五): 第 1 层的差树, 条件于世界稳定

> 不含记号. 入口 [BrwView](BrwView.lagda.md). 第 1 层的差树 `D one W` ([SumOneTree](SumOneTree.lagda.md)), 值 `toB l` ([LayerTrOne](LayerTrOne.lagda.md)), 目标 `B₁ W`, 值前序 `LayerTrBase._≼_`. 下标是带合法性的世界. $\Omega$-极限两种: `ki` (按坐标, 译 `bi`), `kκ` (按世界, 译 `bκ`); 两种的坐标都是合法的第 0 层布劳威尔树 (坐标 $y$, 或层 $c$).
>
> **View 直接建在差树上, 不经 `toB` 再读回** (`LayerTrNeg.no-round` 说那样不保值). 同第 0 层, `vw l x hx vx q y`: 已走过前缀 $x$, 再走 $y$, 对 $y$ 分情况; `n0`, `n1`, `⨾`, `nl`, `nw` 与第 0 层逐字同形. 新的是:
>
> - **`ni` 段** (`ki` 种 $\Omega$-极限): 坐标 $(W',p,l',y)$ 上的分支是 $x$ 抬到 $W'$ 再接上**沿 `dif y` 的部分积分** `J` (差树版的 `LayerTrOne.I`). 值一致要两件:
>   1. `JI`: 部分积分的差树的值就是 `I` 积出的值 (无条件).
>   2. `lift`: 前缀抬到更大的世界, 值不变: $S_p(0,x)\approx x$. **这一条不是无条件的**: 差树的抬升 `nw` 在 `S` 里会在大世界里**重新求值** (`ni` 的分支只取更大世界上的), 布劳威尔树的抬升 `bw` 是透明的. 两者之差就是 "对世界单调".
> - **`nκ` 段**: 模块参数 `κseg`, 类型见 §5. [BrwViewKappa](BrwViewKappa.lagda.md) 在同一条件下给出它.
>
> **条件** `HW` (世界稳定, 遗传): 每个 `ni`, `nκ` 节点满足 `WSq` (在更大世界里求值, 值不变, 底可以换成值相等的), 并且分支都 `HW`. 由此对一切 `HW` 树 `WSq` 成立 (`hw→ws`), 所以 `lift` 成立. `HW` 是 View 的合法性谓词 (`Lgl`), 部分都 `HW`. **前提可满足**: $\Omega_1$ 的差树 `Ωx` 满足 `HW` (`HW-Ωx`, §6).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwViewOne where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ss; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; Pre; sum; pt; Ωd)
open import OCF.Align.BrwMidZero using (dif; sum₀; round₁)
open import OCF.Align.LayerTrBase
open import OCF.Align.LayerTrOne using (one; S; Sp; I; Ip; toB; S-fst; ok-yes)
open import OCF.Align.LayerTrRound using (S-cong; ⊲-idˡ; ≈-refl; ≈-sym; bi-≈)
open import OCF.Align.BrwViewDef using (Sig; View; vz; vs; vl; vΩ; BrwView)
```

## §1 签名

```agda
data K1 : Set where
  ki kκ : K1

Ix₁ : Set
Ix₁ = Σ A Lg

Cd₁ : ∀ {i : Ix₁} → K1 → Set
Cd₁ {W , _} ki = Σ A (λ W′ → (W ⊲ W′) × Σ (Lg W′) (λ _ → Σ A Lg))
Cd₁ {W , _} kκ = Σ A (λ c → (W ⊲ c) × Lg c)

tg₁ : ∀ {i : Ix₁} {k : K1} → Cd₁ {i} k → Ix₁
tg₁ {W , l} {k = ki} (W′ , p , l′ , _) = W′ , l′
tg₁ {W , l} {k = kκ} (c , p , lc) = c , lc

bΩ₁ : ∀ {i : Ix₁} (k : K1) → ((c : Cd₁ {i} k) → B₁ (proj₁ (tg₁ c))) → B₁ (proj₁ i)
bΩ₁ {W , l} ki g = bi (λ {W′} p l′ y ly → g (W′ , p , l′ , y , ly))
bΩ₁ {W , l} kκ g = bκ (λ {c} p lc → g (c , p , lc))

Sig₁ : Sig
Sig₁ = record
  { Ix = Ix₁ ; B = λ i → B₁ (proj₁ i) ; _≼_ = λ a b → a ≼ b ; Stp = λ a b → a ⊲⟨ yes ⟩ b
  ; Kd = λ _ → K1 ; Cd = λ {i} k → Cd₁ {i} k ; LgC = λ _ → ⊤ ; tg = λ {i} {k} c → tg₁ {i} {k} c
  ; bz = λ {i} → bz {proj₁ i} ; bs = λ {i} → bs {proj₁ i} ; bl = λ {i} → bl {proj₁ i} ; bΩ = λ {i} → bΩ₁ {i} }

X₁ : Ix₁ → Set
X₁ (W , _) = D one W

val₁ : ∀ {i} → X₁ i → B₁ (proj₁ i)
val₁ {W , l} x = toB l x
```

## §2 小件: 路径, 极限的同余

```agda
⊲-assoc : ∀ {a b c d} (r : a ⊲ b) (q : b ⊲ c) (p : c ⊲ d) → ⊲-tr (⊲-tr r q) p ≡ ⊲-tr r (⊲-tr q p)
⊲-assoc r q C.self = refl
⊲-assoc r q (C.suc p) = cong C.suc (⊲-assoc r q p)
⊲-assoc r q (C.lim n p) = cong (C.lim n) (⊲-assoc r q p)

bl-≈ : ∀ {W W′} {f : ℕ → B₁ W} {g : ℕ → B₁ W′} → (∀ n → f n ≈ g n) → bl f ≈ bl g
bl-≈ h = l≼ (λ n → ≼l n (proj₁ (h n))) , l≼ (λ n → ≼l n (proj₂ (h n)))

bw-≈ : ∀ {W₀ W} (p : W₀ ⊲ W) (a : B₁ W₀) → bw p a ≈ a
bw-≈ p a = w≼ (≼-refl a) , ≼w (≼-refl a)

≡→≈ : ∀ {W} {a b : B₁ W} → a ≡ b → a ≈ b
≡→≈ {a = a} refl = ≈-refl a
```

## §3 世界稳定

`WSq y`: $y$ 在世界 $W$ (沿 $q$) 与更大的世界 $W'$ (沿 $q\cdot p$) 里求值, 底值相等则结果值相等.

```agda
WSq : ∀ {W₀} → D one W₀ → Set
WSq {W₀} y = ∀ {W W′} (q : W₀ ⊲ W) (p : W ⊲ W′) (l : Lg W) (l′ : Lg W′) {b : B₁ W} {b′ : B₁ W′} →
             b ≈ b′ → S q l b y ≈ S (⊲-tr q p) l′ b′ y

HW : ∀ {W} → D one W → Set
HW n0 = ⊤
HW n1 = ⊤
HW (x ⨾ y) = HW x × HW y
HW (nl d) = ∀ n → HW (d n)
HW (ni (ss C.self) u) = (∀ {W′} p l w → HW (u {W′} p l w)) × WSq (ni (ss C.self) u)
HW (nκ zz u) = (∀ {c} p l → HW (u {c} p l)) × WSq (nκ zz u)
HW (nw p x) = HW x

hw→ws  : ∀ {W₀} (y : D one W₀) → HW y → WSq y
hw→wsp : ∀ {W₀ W W′} (d : ℕ → D one W₀) → (∀ n → HW (d n)) → (q : W₀ ⊲ W) (p : W ⊲ W′) (l : Lg W) (l′ : Lg W′)
         {b : B₁ W} {b′ : B₁ W′} → b ≈ b′ → ∀ n → Sp q l b d n ≈ Sp (⊲-tr q p) l′ b′ d n
hw→ws n0 h q p l l′ e = e
hw→ws n1 h q p l l′ e = s≼s (proj₁ e) , s≼s (proj₂ e)
hw→ws (x ⨾ y) (hx , hy) q p l l′ e = hw→ws y hy q p l l′ (hw→ws x hx q p l l′ e)
hw→ws (nl d) h q p l l′ e = bl-≈ (hw→wsp d h q p l l′ e)
hw→ws (ni (ss C.self) u) h = proj₂ h
hw→ws (nκ zz u) h = proj₂ h
hw→ws (nw r y) h q p l l′ {b} {b′} e =
  subst (λ t → S (⊲-tr r q) l b y ≈ S t l′ b′ y) (⊲-assoc r q p) (hw→ws y h (⊲-tr r q) p l l′ e)
hw→wsp d h q p l l′ e zero = e
hw→wsp d h q p l l′ e (suc n) = hw→ws (d n) (h n) q p l l′ (hw→wsp d h q p l l′ e n)

-- 前缀抬升: 差树的 nw 与布劳威尔树的 bw 值相同
lift : ∀ {W W′} (l : Lg W) (l′ : Lg W′) (p : W ⊲ W′) (x : D one W) → HW x → S p l′ bz x ≈ bw p (toB l x)
lift l l′ p x h =
  ≈-trans (≈-sym (subst (λ t → S C.self l bz x ≈ S t l′ bz x) (⊲-idˡ p) (hw→ws x h C.self p l l′ (z≼ , z≼))))
          (≈-sym (bw-≈ p (toB l x)))
```

## §4 部分积分的差树

`J e z q w`: 沿第 0 层坐标树 $z$ 的每个位置放 $e(w)$, 坐标记法同 `I`. `JI`: 它的值就是 `I` 积出的值.

```agda
J : ∀ {W₀ W} → (D azero W → D one W) → D azero W₀ → W₀ ⊲ W → D azero W → D one W
J e n0 q w = n0
J e n1 q w = e w
J e (x ⨾ y) q w = J e x q w ⨾ J e y q (w ⨾ nw q x)
J e (nl d) q w = nl (λ n → J e (d n) q (w ⨾ Pre q d n))
J e (ni () u) q w
J e (nκ () u) q w
J e (nw p x) q w = J e x (⊲-tr p q) w

module _ {W : A} (l : Lg W) (e : D azero W → D one W) where
  JI  : ∀ {W₀} (z : D azero W₀) (q : W₀ ⊲ W) (w : D azero W) {c c′ : B₁ W} → c ≈ c′ →
        S C.self l c (J e z q w) ≈ I (λ w′ b → S C.self l b (e w′)) z q w c′
  JIp : ∀ {W₀} (d : ℕ → D azero W₀) (q : W₀ ⊲ W) (w : D azero W) {c c′ : B₁ W} → c ≈ c′ →
        ∀ n → Sp C.self l c (λ n → J e (d n) q (w ⨾ Pre q d n)) n ≈ Ip (λ w′ b → S C.self l b (e w′)) d q w c′ n
  JI n0 q w h = h
  JI n1 q w h = S-cong C.self l (e w) h
  JI (x ⨾ y) q w h = JI y q (w ⨾ nw q x) (JI x q w h)
  JI (nl d) q w h = bl-≈ (JIp d q w h)
  JI (ni () u) q w h
  JI (nκ () u) q w h
  JI (nw p x) q w h = JI x (⊲-tr p q) w h
  JIp d q w h zero = h
  JIp d q w h (suc n) = JI (d n) q (w ⨾ Pre q d n) (JIp d q w h n)

HW-J : ∀ {W₀ W} (e : D azero W → D one W) → (∀ w → HW (e w)) → (z : D azero W₀) (q : W₀ ⊲ W) (w : D azero W) → HW (J e z q w)
HW-J e h n0 q w = tt
HW-J e h n1 q w = h w
HW-J e h (x ⨾ y) q w = HW-J e h x q w , HW-J e h y q (w ⨾ nw q x)
HW-J e h (nl d) q w = λ n → HW-J e h (d n) q (w ⨾ Pre q d n)
HW-J e h (ni () u) q w
HW-J e h (nκ () u) q w
HW-J e h (nw p x) q w = HW-J e h x (⊲-tr p q) w

-- 部分和的树
ps : ∀ {W₀} → (ℕ → D one W₀) → ℕ → D one W₀
ps d zero = n0
ps d (suc n) = ps d n ⨾ d n

HW-ps : ∀ {W₀} (d : ℕ → D one W₀) → (∀ n → HW (d n)) → ∀ n → HW (ps d n)
HW-ps d h zero = tt
HW-ps d h (suc n) = HW-ps d h n , h n

ps-Sp : ∀ {W₀ W} (q : W₀ ⊲ W) (l : Lg W) (b : B₁ W) (d : ℕ → D one W₀) n → S q l b (ps d n) ≡ Sp q l b d n
ps-Sp q l b d zero = refl
ps-Sp q l b d (suc n) = cong (λ t → S q l t (d n)) (ps-Sp q l b d n)
```

## §5 View, `nκ` 段作参数

`V₁ i v`: 值为 $v$ 的对象的读法. `κseg`: 前缀 $x$ 之后接一个 `nκ` 节点 (沿 $q$ 抬升), 给出它的读法. **这是 `nκ` 段的确切类型.**

```agda
Lgl₁ : ∀ {i} → X₁ i → Set
Lgl₁ {W , _} x = HW x

V₁ : (i : Ix₁) → B₁ (proj₁ i) → Set
V₁ = View Sig₁ X₁ val₁ Lgl₁

KSeg : Set
KSeg = ∀ {W₀ W} (l : Lg W) (x : D one W) → HW x → (q : W₀ ⊲ W) (zz : ⊤) (u : ∀ {c} → W₀ ⊲ c → Lg c → D one c) →
       HW (nκ zz u) → V₁ (W , l) (S q l (toB l x) (nκ zz u))

module WithKappa (κseg : KSeg) where
  vw : ∀ {W₀ W} (l : Lg W) (x : D one W) → HW x → V₁ (W , l) (toB l x) →
       (q : W₀ ⊲ W) (y : D one W₀) → HW y → V₁ (W , l) (S q l (toB l x) y)
  vw l x hx vx q n0 hy = vx
  vw l x hx vx q n1 hy = vs x hx (≈-refl _)
  vw l x hx vx q (y₁ ⨾ y₂) (h₁ , h₂) = vw l (x ⨾ nw q y₁) (hx , h₁) (vw l x hx vx q y₁ h₁) q y₂ h₂
  vw l x hx vx q (nl d) hy =
    vl (λ n → x ⨾ nw q (ps d n)) (λ n → hx , HW-ps d hy n)
       (λ n → S-fst yes q l (S q l (toB l x) (ps d n)) (d n) (ok-yes (d n)))
       (bl-≈ (λ n → ≡→≈ (sym (ps-Sp q l (toB l x) d n))))
  vw l x hx vx q (nw r y) hy = vw l x hx vx (⊲-tr r q) y hy
  vw {W₀} {W} l x hx vx q (ni (ss C.self) u) (hu , _) =
    vΩ ki g (λ c _ → hg c)
       (bi-≈ (λ {W′} p l′ y ly → ≈-sym (JI l′ (λ w → u (⊲-tr q p) l′ w) (dif {W′} y (z⊲ y) ly) C.self n0 (lift l l′ p x hx))))
    where
    g : (c : Cd₁ {W , l} ki) → X₁ (tg₁ {W , l} {ki} c)
    g (W′ , p , l′ , y , ly) = nw p x ⨾ J (λ w → u (⊲-tr q p) l′ w) (dif {W′} y (z⊲ y) ly) C.self n0
    hg : ∀ c → Lgl₁ {tg₁ {W , l} {ki} c} (g c)
    hg (W′ , p , l′ , y , ly) = hx , HW-J _ (λ w → hu (⊲-tr q p) l′ w) (dif {W′} y (z⊲ y) ly) C.self n0
  vw l x hx vx q (nκ zz u) hy = κseg l x hx q zz u hy

  view₁ : BrwView Sig₁ X₁ val₁ Lgl₁
  view₁ = record { view = λ { {W , l} x hx → vw l n0 tt (vz (z≼ , z≼)) C.self x hx } }
```

## §6 前提可满足: $\Omega_1$

`Ωx` $=1+\sum_z1$. 它唯一的节点的分支不读世界也不读坐标, 所以在大世界里求值不变: 一边的每一支在另一边取同一个坐标、世界取 $W'$ (或 $p\cdot p'$). 比值用 `plus` ($b+a$, $a$ 是第 0 层的值).

```agda
plus : ∀ {W} → B₁ W → A → B₁ W
plus c azero = c
plus c (asuc a) = bs (plus c a)
plus c (alim f) = bl (λ n → plus c (f n))

≼-suc : ∀ {W W′} {a : B₁ W} {b : B₁ W′} → a ≼ b → a ≼ bs b
≼-suc z≼ = z≼
≼-suc (s≼s p) = s≼s (≼-suc p)
≼-suc (≼l {f = f} n p) = ≼-trans (≼-suc p) (s≼s (≼l n (≼-refl (f n))))
≼-suc (l≼ p) = l≼ (λ n → ≼-suc (p n))
≼-suc (≼i {f = f} r l y ly p) = ≼-trans (≼-suc p) (s≼s (≼i r l y ly (≼-refl (f r l y ly))))
≼-suc (i≼ p) = i≼ (λ r l y ly → ≼-suc (p r l y ly))
≼-suc (≼κ {g = g} r l p) = ≼-trans (≼-suc p) (s≼s (≼κ r l (≼-refl (g r l))))
≼-suc (κ≼ p) = κ≼ (λ r l → ≼-suc (p r l))
≼-suc (≼w {b = b} p) = ≼-trans (≼-suc p) (s≼s (≼w (≼-refl b)))
≼-suc (w≼ p) = w≼ (≼-suc p)

plus-≥ : ∀ {W} (c : B₁ W) a → c ≼ plus c a
plus-≥ c azero = ≼-refl c
plus-≥ c (asuc a) = ≼-suc (plus-≥ c a)
plus-≥ c (alim f) = ≼l 0 (plus-≥ c (f 0))

plus-mono : ∀ {W W′} {a a′} → a ≤ a′ → {c : B₁ W} {c′ : B₁ W′} → c ≼ c′ → plus c a ≼ plus c′ a′
plus-mono {a′ = a′} z≤ {c′ = c′} e = ≼-trans e (plus-≥ c′ a′)
plus-mono (s≤ p) e = s≼s (plus-mono p e)
plus-mono (≤l n p) e = ≼l n (plus-mono p e)
plus-mono (l≤ p) e = l≼ (λ n → plus-mono (p n) e)

module _ {W : A} where
  Ib  : ∀ {W₀} (z : D azero W₀) (q : W₀ ⊲ W) (w : D azero W) (c : B₁ W) a {c₀ : B₁ W} → c₀ ≈ plus c a →
        I (λ _ b → bs b) z q w c₀ ≈ plus c (sum a z)
  Ibp : ∀ {W₀} (d : ℕ → D azero W₀) (q : W₀ ⊲ W) (w : D azero W) (c : B₁ W) a {c₀ : B₁ W} → c₀ ≈ plus c a →
        ∀ n → Ip (λ _ b → bs b) d q w c₀ n ≈ plus c (pt a d n)
  Ib n0 q w c a h = h
  Ib n1 q w c a h = s≼s (proj₁ h) , s≼s (proj₂ h)
  Ib (x ⨾ y) q w c a h = Ib y q (w ⨾ nw q x) c (sum a x) (Ib x q w c a h)
  Ib (nl d) q w c a h = bl-≈ (Ibp d q w c a h)
  Ib (ni () u) q w c a h
  Ib (nκ () u) q w c a h
  Ib (nw p x) q w c a h = Ib x (⊲-tr p q) w c a h
  Ibp d q w c a h zero = h
  Ibp d q w c a h (suc n) = Ib (d n) q (w ⨾ Pre q d n) c (pt a d n) (Ibp d q w c a h n)

-- 坐标 y 上一支的值: 底加上 y
br : ∀ {W} (c : B₁ W) y (ly : Lg y) → I (λ _ b → bs b) (dif {W} y (z⊲ y) ly) C.self n0 c ≈ plus c (sum azero (dif {W} y (z⊲ y) ly))
br c y ly = Ib (dif y (z⊲ y) ly) C.self n0 c azero (≈-refl c)

rd : ∀ {V V′} y (ly : Lg y) → sum azero (dif {V} y (z⊲ y) ly) ≤ sum azero (dif {V′} y (z⊲ y) ly)
rd {V} {V′} y ly = ≤-trans (proj₁ (sum₀ (dif {V} y (z⊲ y) ly))) (≤-trans (proj₁ (round₁ {V} y ly))
                    (≤-trans (proj₂ (round₁ {V′} y ly)) (proj₂ (sum₀ (dif {V′} y (z⊲ y) ly)))))

br≼ : ∀ {V V′} {c : B₁ V} {c′ : B₁ V′} → c ≼ c′ → ∀ y ly →
      I (λ _ b → bs b) (dif {V} y (z⊲ y) ly) C.self n0 c ≼ I (λ _ b → bs b) (dif {V′} y (z⊲ y) ly) C.self n0 c′
br≼ {c = c} {c′} e y ly = ≼-trans (proj₁ (br c y ly)) (≼-trans (plus-mono (rd y ly) e) (proj₂ (br c′ y ly)))

uΩ : ∀ {W′} → azero ⊲ W′ → Lg W′ → D azero W′ → D one W′
uΩ _ _ _ = n1

WSq-Ω : WSq {azero} (ni (ss C.self) uΩ)
WSq-Ω q p l l′ e =
  i≼ (λ p″ l″ y ly → ≼i C.self l′ y ly (br≼ (w≼ (≼w (proj₁ e))) y ly)) ,
  i≼ (λ p‴ l‴ y ly → ≼i (⊲-tr p p‴) l‴ y ly (br≼ (w≼ (≼w (proj₂ e))) y ly))

Ωx : D one azero
Ωx = Ωd one C.self tt

HW-Ωx : HW Ωx
HW-Ωx = tt , (tt , ((λ p l w → tt) , WSq-Ω))
```
