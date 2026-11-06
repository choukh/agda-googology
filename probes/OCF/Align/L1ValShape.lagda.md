# 第 1 层差树的值语义 (二): 布劳威尔读法丢掉的坐标

> 不含记号. 入口 [L1Val](L1Val.lagda.md). **编译过的否定.** 两棵第 1 层差树 $x_b$, $x_0$ (都只有一个 `ni`), 它们的布劳威尔读法 `toB` **逐分支字面一致** (`Bis`: 同构造子, 同路径, 分支逐个 `Bis`), 而折叠 ($\psi_0(\Omega_{\Omega+1})$ 用的那一个, 动作 `Step`, 目标第 0 层) 在 $x_b$ 上输出 $\ge1$, 在 $x_0$ 上输出 $0$.
>
> **原因.** `toB` 只在坐标 `I` 走 `dif y` 时经过的位置调用分支 (形如 `w ⨾ nw _ x`, 其中 `w` 是 `n0` 或 `_ ⨾ Pre _ _ _`); 折叠在链上走第 0 层的树时, 调用分支的位置是 `Run` 的前缀 (形如 `(w ⨾ nw _ x) ⨾ nw _ y`, 左结合). 两种位置的形状不同, 值相同. 分支 $u_b$ 只在 `(n0 ⨾ nw _ n0) ⨾ nw _ n0` 这一种形状上给 `n1`, `toB` 从来走不到它 (`Bis-I`, 对一切 `dif` 的形状 `DF` 与一切起点形状 `PS`), 折叠在第一个链点上就走到它.
>
> **否定的是什么.** 不止 "折叠对 `toB` 的值单调" (`¬toB-mono`): 任何一个包含 `Bis` 的关系 (例如逐分支比较布劳威尔树的关系) 都不能让折叠单调 (`¬Bis-mono`). 所以第 1 层的值语义不能经由 `toB` 读: 它要看得见差树坐标. 反例的分支不满足 `Mono` (`ub-not-mono`), 所以这条与 "限制到分支对坐标值单调的树" 不矛盾; 那条路由 [L1ValSup](L1ValSup.lagda.md) 处理.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.L1ValShape where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ss; z⊲; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; Pre; sum)
import OCF.Align.SumOneClosed as F
open import OCF.Align.BrwMidZero using (dif)
open import OCF.Align.LayerTrBase
open import OCF.Align.LayerTrOne using (one; S; I; Ip; toB)
open import OCF.Align.L1ValBase
```

## §1 读坐标形状的分支

```agda
isN0 : ∀ {W} → D azero W → Bool
isN0 n0 = true
isN0 _ = false

nwN0 : ∀ {W} → D azero W → Bool
nwN0 (nw p x) = isN0 x
nwN0 _ = false

badL : ∀ {W} → D azero W → Bool
badL (a ⨾ b) = isN0 a ∧ nwN0 b
badL _ = false

-- (n0 ⨾ nw _ n0) ⨾ nw _ n0
bad : ∀ {W} → D azero W → Bool
bad (a ⨾ b) = badL a ∧ nwN0 b
bad _ = false

pk : ∀ {W} → Bool → D one W
pk true = n1
pk false = n0

ub : ∀ {W′} → one ⊲ W′ → Lg W′ → D azero W′ → D one W′
ub p l w = pk (bad w)

xb x0 : D one one
xb = ni (ss C.self) ub
x0 = ni (ss C.self) (λ _ _ _ → n0)
```

## §2 `toB` 走不到坏形状

`DF`: `dif` 的像的形状 (左结合, 右边只有 `n1` 或 `nl`). `PS`: `I` 往下传的起点的形状 (`n0`, 或右边不是 `nw`).

```agda
data DF {W} : D azero W → Set where
  f0 : DF n0
  f1 : ∀ {x} → DF x → DF (x ⨾ n1)
  fl : ∀ {x d} → DF x → (∀ m → DF (d m)) → DF (x ⨾ nl d)

dif-DF : ∀ {W} b {a} (p : a ⊲ b) (w : Lg b) → DF (dif {W} b p w)
dif-DF b C.self w = f0
dif-DF (asuc c) (C.suc p) w = f1 (dif-DF c p w)
dif-DF (alim f) (C.lim n p) (st , w) = fl (dif-DF (f n) p (w n)) (λ m → dif-DF (f (suc (m Data.Nat.+ n))) (st (m Data.Nat.+ n)) (w (suc (m Data.Nat.+ n))))

NN : ∀ {W} → D azero W → Set
NN (nw p x) = ⊥
NN _ = ⊤

PS : ∀ {W} → D azero W → Set
PS n0 = ⊤
PS (a ⨾ b) = NN b
PS _ = ⊥

pre-NN : ∀ {W₀ W} (q : W₀ ⊲ W) (d : ℕ → D azero W₀) n → NN (Pre q d n)
pre-NN q d zero = tt
pre-NN q d (suc n) = tt

∧f : ∀ b → (b ∧ false) ≡ false
∧f true = refl
∧f false = refl

bad-ps : ∀ {W₀ W} (w : D azero W) (q : W₀ ⊲ W) (x : D azero W₀) → PS w → bad (w ⨾ nw q x) ≡ false
bad-ps n0 q x ps = refl
bad-ps (a ⨾ n0) q x ps rewrite ∧f (isN0 a) = refl
bad-ps (a ⨾ n1) q x ps rewrite ∧f (isN0 a) = refl
bad-ps (a ⨾ (b ⨾ c)) q x ps rewrite ∧f (isN0 a) = refl
bad-ps (a ⨾ nl d) q x ps rewrite ∧f (isN0 a) = refl
bad-ps (a ⨾ ni () u) q x ps
bad-ps (a ⨾ nκ () u) q x ps
bad-ps (a ⨾ nw p y) q x ()
bad-ps n1 q x ()
bad-ps (nl d) q x ()
bad-ps (nw p y) q x ()
bad-ps (ni () u) q x ps
bad-ps (nκ () u) q x ps
```

**逐分支字面一致.** `Bis`: 两棵布劳威尔树同构造子, 抬升路径相同, 分支逐个 `Bis`. 它推出 $\approx$ (`Bis→≼`). 不用函数外延.

```agda
data Bis : ∀ {W} → B₁ W → B₁ W → Set where
  Bz : ∀ {W} → Bis {W} bz bz
  Bs : ∀ {W} {a b : B₁ W} → Bis a b → Bis (bs a) (bs b)
  Bl : ∀ {W} {f g : ℕ → B₁ W} → (∀ n → Bis (f n) (g n)) → Bis (bl f) (bl g)
  Bi : ∀ {W} {f g : ∀ {W′} → W ⊲ W′ → Lg W′ → (y : A) → Lg y → B₁ W′} →
       (∀ {W′} p l y ly → Bis (f {W′} p l y ly) (g p l y ly)) → Bis (bi f) (bi g)
  Bκ : ∀ {W} {f g : ∀ {c} → W ⊲ c → Lg c → B₁ c} → (∀ {c} p l → Bis (f {c} p l) (g p l)) → Bis (bκ f) (bκ g)
  Bw : ∀ {W₀ W} {p : W₀ ⊲ W} {a b : B₁ W₀} → Bis a b → Bis (bw p a) (bw p b)

Bis→≼ : ∀ {W} {a b : B₁ W} → Bis a b → a ≼ b
Bis→≼ Bz = z≼
Bis→≼ (Bs h) = s≼s (Bis→≼ h)
Bis→≼ (Bl h) = l≼ (λ n → ≼l n (Bis→≼ (h n)))
Bis→≼ (Bi h) = i≼ (λ p l y ly → ≼i p l y ly (Bis→≼ (h p l y ly)))
Bis→≼ (Bκ h) = κ≼ (λ p l → ≼κ p l (Bis→≼ (h p l)))
Bis→≼ (Bw h) = w≼ (≼w (Bis→≼ h))

Bis-sym : ∀ {W} {a b : B₁ W} → Bis a b → Bis b a
Bis-sym Bz = Bz
Bis-sym (Bs h) = Bs (Bis-sym h)
Bis-sym (Bl h) = Bl (λ n → Bis-sym (h n))
Bis-sym (Bi h) = Bi (λ p l y ly → Bis-sym (h p l y ly))
Bis-sym (Bκ h) = Bκ (λ p l → Bis-sym (h p l))
Bis-sym (Bw h) = Bw (Bis-sym h)

Bis-I  : ∀ {W₀ W} (e e′ : D azero W → B₁ W → B₁ W) → (∀ w {b b′} → bad w ≡ false → Bis b b′ → Bis (e w b) (e′ w b′)) →
         (z : D azero W₀) → DF z → (q : W₀ ⊲ W) → ∀ w → PS w → ∀ {b b′} → Bis b b′ → Bis (I e z q w b) (I e′ z q w b′)
Bis-Ip : ∀ {W₀ W} (e e′ : D azero W → B₁ W → B₁ W) → (∀ w {b b′} → bad w ≡ false → Bis b b′ → Bis (e w b) (e′ w b′)) →
         (d : ℕ → D azero W₀) → (∀ m → DF (d m)) → (q : W₀ ⊲ W) → ∀ w → ∀ {b b′} → Bis b b′ → ∀ n → Bis (Ip e d q w b n) (Ip e′ d q w b′ n)
Bis-I e e′ he n0 f0 q w ps h = h
Bis-I e e′ he (x ⨾ n1) (f1 dx) q w ps h = he (w ⨾ nw q x) (bad-ps w q x ps) (Bis-I e e′ he x dx q w ps h)
Bis-I e e′ he (x ⨾ nl d) (fl dx dd) q w ps h = Bl (Bis-Ip e e′ he d dd q (w ⨾ nw q x) (Bis-I e e′ he x dx q w ps h))
Bis-Ip e e′ he d dd q w h zero = h
Bis-Ip e e′ he d dd q w h (suc n) = Bis-I e e′ he (d n) (dd n) q (w ⨾ Pre q d n) (pre-NN q d n) (Bis-Ip e e′ he d dd q w h n)

he : ∀ {W′} (l′ : Lg W′) (w : D azero W′) {b b′ : B₁ W′} → bad w ≡ false → Bis b b′ → Bis (S C.self l′ b (pk (bad w))) (S C.self l′ b′ n0)
he l′ w eq h rewrite eq = h

toB-Bis : Bis (toB tt xb) (toB tt x0)
toB-Bis = Bi (λ p l′ y ly →
  Bis-I _ _ (λ w eq h → he l′ w eq h) (dif y (z⊲ y) ly) (dif-DF y (z⊲ y) ly) C.self n0 tt (Bw Bz))

toB-≈ : toB tt xb ≈ toB tt x0
toB-≈ = Bis→≼ toB-Bis , Bis→≼ (Bis-sym toB-Bis)
```

## §3 折叠走得到坏形状

第一个链点是起点状态的差 `n0 ⨾ (n0 ⨾ n1)`. 折叠走它, 在 `n1` 处的前缀正是 `(n0 ⨾ nw _ n0) ⨾ nw _ n0`, 那里 $u_b$ 给 `n1`, 动作 `Step` 给出 $\ge1$ (`has1`, 由检查器归约). $x_0$ 的分支总是 `n0`, 动作的每一步都是零 (`RunZA`).

```agda
big : has1 (out xb) ≡ true
big = refl

small : Z (out x0)
small n = RunZA (F.accCn azero) _ C.self tt _ _ (λ p l w Y τ lt → tt) _ _ (inj₁ (z⊲ one)) tt
```

## §4 否定

```agda
fold-sep : ¬ (val xb ≤ val x0)
fold-sep = sep (out xb) (out x0) big small

¬Bis-mono : ¬ (∀ (x x′ : D one one) → Bis (toB tt x) (toB tt x′) → val x ≤ val x′)
¬Bis-mono H = fold-sep (H xb x0 toB-Bis)

¬toB-mono : ¬ (∀ (x x′ : D one one) → toB tt x ≼ toB tt x′ → val x ≤ val x′)
¬toB-mono H = fold-sep (H xb x0 (proj₁ toB-≈))

-- 反例的分支不对坐标值单调: 坏形状的值是 0, 那里给 1, 坐标 n0 那里给 0
ub-not-mono : ¬ Mono ub
ub-not-mono H = no-suc {b = bz {one}} tt (H C.self tt ((n0 ⨾ nw C.self n0) ⨾ nw C.self n0) n0 z≤)
```
