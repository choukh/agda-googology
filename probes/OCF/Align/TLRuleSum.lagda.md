# 折叠是和的作用 (一): 定义

> 不含记号. 入口 [TLRule](TLRule.lagda.md). **这里的合法性证明只有 §2 讲和的那十几行, 无前提, 不提折叠:** 树的 $\omega$-极限节点不是序列的上确界, 而是**差的和** `nl d` ($\sum_n d_n$), 所以相邻部分和字面地一个是另一个的第一位置, 不用证. 加法是构造子 `_⨾_`, 不是函数. 折叠 `Run` 不返回一棵树, 返回**差**: 输入多走一段, 输出多长一段.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLRuleSum where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Strict; ss; sl; Lg; ⊲-tr; lg⊲; z⊲; ≪∘; ≪S; ≪⊲; S→⊲; Rk; keep; rise; cmpN)
import OCF.Align.CumReadCF as C
import OCF.Free.Level as FL
```

## §1 树

`n0`: 空和. `n1`: 一. `x ⨾ y`: 先 $x$ 后 $y$. `nl d`: $\sum_{n<\omega}d_n$. `ni r u`: $\sum_{w}u(w)$, $w$ 过低层 $k$ 的元素; 这一段的第一个位置接在 $\Omega_k$ 上, $w$ 是从 $\Omega_k$ 算起的坐标 (见 §4).

```agda
module _ (L : A) (V : ∀ {a} → Strict a L → Set) where
  infixl 6 _⨾_
  data D₊ : Set where
    n0  : D₊
    n1  : D₊
    _⨾_ : D₊ → D₊ → D₊
    nl  : (ℕ → D₊) → D₊
    ni  : ∀ {k} (r : k ≪ L) → (V (≪S r) → D₊) → D₊

D  : A → Set
Ws : ∀ L {a} → Strict a L → Set
Wc : ∀ b {a} → a ⊲ b → Set
D L = D₊ L (Ws L)
Ws (asuc b) (ss P) = Wc b P
Ws (alim f) (sl n P) = Wc (f n) P
Wc a C.self = D a
Wc (asuc b) (C.suc P) = Wc b P
Wc (alim f) (C.lim n P) = Wc (f n) P

outC : ∀ {b a} (P : a ⊲ b) → Wc b P → D a
outC C.self x = x
outC (C.suc P) x = outC P x
outC (C.lim n P) x = outC P x

inC : ∀ {b a} (P : a ⊲ b) → D a → Wc b P
inC C.self x = x
inC (C.suc P) x = inC P x
inC (C.lim n P) x = inC P x

outS : ∀ {b a} (R : Strict a b) → Ws b R → D a
outS (ss P) x = outC P x
outS (sl n P) x = outC P x

inS : ∀ {b a} (R : Strict a b) → D a → Ws b R
inS (ss P) x = inC P x
inS (sl n P) x = inC P x

out-inC : ∀ {b a} (P : a ⊲ b) (x : D a) → outC P (inC P x) ≡ x
out-inC C.self x = refl
out-inC (C.suc P) x = out-inC P x
out-inC (C.lim n P) x = out-inC P x

out-inS : ∀ {b a} (R : Strict a b) (x : D a) → outS R (inS R x) ≡ x
out-inS (ss P) x = out-inC P x
out-inS (sl n P) x = out-inC P x
```

## §2 第 0 层的树给层: 没有证据

`sum b x`: 从 $b$ 接着走 $x$. **相邻部分和字面是第一位置 (`sum-fst`), 所以结果总是 `Lg` (`Lg-sum`), 对一切 $x$, 无前提.** 这就是回灌. 没有 `HS`, 没有 `toLevel`, 没有累加: `sum` 给的层就是这棵树的值.

```agda
-- 第 n 个部分和; 第 0 个是 b 自己
pt  : A → (ℕ → D azero) → ℕ → A
sum : A → D azero → A

pt b d zero = b
pt b d (suc n) = sum (pt b d n) (d n)

sum b n0 = b
sum b n1 = asuc b
sum b (x ⨾ y) = sum (sum b x) y
sum b (nl d) = alim (pt b d)
sum b (ni () u)

sum-fst : ∀ b x → b ⊲ sum b x
pt-fst  : ∀ b d n → b ⊲ pt b d n
sum-fst b n0 = C.self
sum-fst b n1 = C.suc C.self
sum-fst b (x ⨾ y) = ⊲-tr (sum-fst b x) (sum-fst (sum b x) y)
sum-fst b (nl d) = C.lim 0 C.self
sum-fst b (ni () u)
pt-fst b d zero = C.self
pt-fst b d (suc n) = ⊲-tr (pt-fst b d n) (sum-fst (pt b d n) (d n))

Lg-sum : ∀ b x → Lg b → Lg (sum b x)
Lg-pt  : ∀ b d n → Lg b → Lg (pt b d n)
Lg-sum b n0 w = w
Lg-sum b n1 w = w
Lg-sum b (x ⨾ y) w = Lg-sum (sum b x) y (Lg-sum b x w)
Lg-sum b (nl d) w = (λ n → sum-fst (pt b d n) (d n)) , (λ n → Lg-pt b d n w)
Lg-sum b (ni () u) w
Lg-pt b d zero w = w
Lg-pt b d (suc n) w = Lg-sum (pt b d n) (d n) (Lg-pt b d n w)
```

## §3 $\Omega$ 也是和

$\Omega_b-\Omega_a$ 沿 $a\sqsubseteq b$ 的第一位置写成和. 后继: $\Omega_{c+1}-\Omega_c=\sum_{w:c}1$. 极限: 逐段. 所以 $\Omega_a$ 是 $1$ 接上 $0$ 到 $a$ 的差 (`Ωd`).

```agda
Dif : ∀ b {a L} → a ⊲ b → b ⊲ L → Lg b → D L
Dif b C.self q w = n0
Dif (asuc c) (C.suc p) q w = Dif c p (⊲-tr (C.suc C.self) q) w ⨾ ni (≪∘ C.zero q) (λ _ → n1)
Dif (alim f) (C.lim n p) q (st , w) =
  Dif (f n) p (⊲-tr (C.lim n C.self) q) (w n) ⨾ nl (λ m → Dif (f (suc (m + n))) (st (m + n)) (⊲-tr (C.lim (suc (m + n)) C.self) q) (w (suc (m + n))))

Ωd : ∀ a {L} → a ⊲ L → Lg a → D L
Ωd a q w = n1 ⨾ Dif a (z⊲ a) q w
```

## §4 折叠

$W$: 世界, 字面合法的上界. `St`: 状态, 对每个低于 $W$ 的目标 $t$, 记 $\psi_t(X)-\Omega_t$, $X$ 是已经走过的输入. `Run A w δ Y`: 已走到坐标 $w$, 再走 $\delta$, 每一个位置上做一次 `A`, 返回状态的差.

`S`: 一步, 模块参数. **折叠里只有这一件是选择.** 其余都是和的结构.

```agda
data AccL (k : A) : Set where
  acc : (∀ {j} → j ≪ k → AccL j) → AccL k

acc≪ : ∀ k {j} → j ≪ k → AccL j
acc≪ (asuc a) C.zero = acc (acc≪ a)
acc≪ (asuc a) (C.suc r) = acc≪ a r
acc≪ (alim f) (C.lim n r) = acc≪ (f n) r

accL : ∀ k → AccL k
accL k = acc (acc≪ k)

≪≪ : ∀ {j k L} → j ≪ k → k ≪ L → j ≪ L
≪≪ r s = ≪∘ r (≪⊲ s)

-- ∫ u: 走过 δ, 每个位置上放 u (w). 没有目标, 所以没有比较.
Int : ∀ {j k} → AccL j → j ≪ k → (D j → D k) → D j → D j → D k
Ipt : ∀ {j k} → AccL j → j ≪ k → (D j → D k) → D j → (ℕ → D j) → ℕ → D j

Ipt ac r u w d zero = w
Ipt ac r u w d (suc n) = Ipt ac r u w d n ⨾ d n

Int ac r u w n0 = n0
Int ac r u w n1 = u w
Int ac r u w (x ⨾ y) = Int ac r u w x ⨾ Int ac r u (w ⨾ x) y
Int ac r u w (nl d) = nl (λ n → Int ac r u (Ipt ac r u w d n) (d n))
Int (acc f) r u w (ni r′ v) =
  ni (≪≪ r′ r) (λ y → let z = outS (≪S (≪≪ r′ r)) y in
    Int (acc f) r u (w ⨾ Int (f r′) r′ (λ z′ → v (inS (≪S r′) z′)) n0 z) (v (inS (≪S r′) z)))

module Fold (W : A) (lW : Lg W) (S : ∀ {t} → D t → D t) where

  St : Set
  St = ∀ {t} → t ⊲ W → D t

  infixl 6 _⊕_
  _⊕_ : St → St → St
  (Y ⊕ Δ) τ = Y τ ⨾ Δ τ

  -- 一格: ψ_t(X+1) - ψ_t(X)
  Step : St → St
  Step Y {t} τ = S (Ωd t C.self (lg⊲ τ lW) ⨾ Y τ)

  Run   : ∀ {k} → AccL k → k ⊲ W → (D k → St → St) → D k → D k → St → St
  RunNi : ∀ {j k} → AccL k → AccL j → k ⊲ W → (D k → St → St) → D k → (r : j ≪ k) → (Ws k (≪S r) → D k) → St → St
  RunK  : ∀ {j k t} → AccL k → AccL j → k ⊲ W → (D k → St → St) → D k → (r : j ≪ k) → (Ws k (≪S r) → D k) → St → t ⊲ W → Rk j t → D t
  Rpt   : ∀ {k} → AccL k → k ⊲ W → (D k → St → St) → D k → (ℕ → D k) → St → ℕ → D k × St
  Chn   : ∀ {j} → AccL j → j ⊲ W → (D j → St → St) → St → ℕ → D j × (D j × St)
  Ai    : ∀ {j k} → AccL k → (r : j ≪ k) → k ⊲ W → AccL j → (D k → St → St) → D k → (Ws k (≪S r) → D k) → D j → St → St

  -- 走到 d 的第 n 项之前
  Rpt ac kp A w d Y zero = w , Y
  Rpt ac kp A w d Y (suc n) =
    (proj₁ (Rpt ac kp A w d Y n) ⨾ d n) ,
    (proj₂ (Rpt ac kp A w d Y n) ⊕ Run ac kp A (proj₁ (Rpt ac kp A w d Y n)) (d n) (proj₂ (Rpt ac kp A w d Y n)))

  -- u 这一段的每个坐标 z 上走 u z
  Ai ac r kp ac′ A w u z Y′ = Run ac kp A (w ⨾ Int ac′ r (λ z′ → u (inS (≪S r) z′)) n0 z) (u (inS (≪S r) z)) Y′

  -- 链: 坐标 w_n, 下一段 δ_n, 状态 Y_n. δ₀ 是状态在 j 的差, 不需要另给起点.
  Chn ac ρ A Y zero = n0 , (Y ρ , Y)
  Chn ac ρ A Y (suc n) =
    (proj₁ (Chn ac ρ A Y n) ⨾ proj₁ (proj₂ (Chn ac ρ A Y n))) ,
    (Run ac ρ A (proj₁ (Chn ac ρ A Y n)) (proj₁ (proj₂ (Chn ac ρ A Y n))) (proj₂ (proj₂ (Chn ac ρ A Y n))) ρ ,
     (proj₂ (proj₂ (Chn ac ρ A Y n)) ⊕ Run ac ρ A (proj₁ (Chn ac ρ A Y n)) (proj₁ (proj₂ (Chn ac ρ A Y n))) (proj₂ (proj₂ (Chn ac ρ A Y n)))))

  Run ac kp A w n0 Y τ = n0
  Run ac kp A w n1 Y τ = A w Y τ
  Run ac kp A w (x ⨾ y) Y τ =
    Run ac kp A w x Y τ ⨾ Run ac kp A (w ⨾ x) y (Y ⊕ Run ac kp A w x Y) τ
  Run ac kp A w (nl d) Y τ =
    nl (λ n → Run ac kp A (proj₁ (Rpt ac kp A w d Y n)) (d n) (proj₂ (Rpt ac kp A w d Y n)) τ)
  Run (acc f) kp A w (ni r u) Y τ = RunNi (acc f) (f r) kp A w r u Y τ

  RunNi ac ac′ kp A w r u Y {t} τ = RunK ac ac′ kp A w r u Y τ (cmpN (≪∘ r kp) τ lW)

  RunK ac ac′ kp A w r u Y τ (keep s) = ni s (λ y →
       Run ac kp A (w ⨾ Int ac′ r (λ z′ → u (inS (≪S r) z′)) n0 (outS (≪S s) y)) (u (inS (≪S r) (outS (≪S s) y)))
         (Y ⊕ Run ac′ (⊲-tr (≪⊲ r) kp) (Ai ac r kp ac′ A w u) n0 (outS (≪S s) y) Y) τ)
  RunK ac ac′ kp A w r u Y τ (rise _) = nl (λ n →
       Run ac′ (⊲-tr (≪⊲ r) kp) (Ai ac r kp ac′ A w u)
         (proj₁ (Chn ac′ (⊲-tr (≪⊲ r) kp) (Ai ac r kp ac′ A w u) Y n))
         (proj₁ (proj₂ (Chn ac′ (⊲-tr (≪⊲ r) kp) (Ai ac r kp ac′ A w u) Y n)))
         (proj₂ (proj₂ (Chn ac′ (⊲-tr (≪⊲ r) kp) (Ai ac r kp ac′ A w u) Y n))) τ)

  -- 顶层: 每一格做一次 Step
  Act : ∀ {k} → k ⊲ W → D k → St → St
  Act {k} kp x = Run (accL k) kp (λ _ Y → Step Y) n0 x
```

## §5 闭项

`Ψd y w`: $\psi_0(\Omega_y)-1$. 世界就是 $y$. `cell`: 回灌. 层的合法性只有 `Lg-sum`, 没有别的证明.

```agda
module Gen (S : ∀ {t} → D t → D t) where
  Ψd : ∀ y → Lg y → D azero
  Ψd y w = Act {y} C.self (Ωd y C.self w) (λ _ → n0) (z⊲ y)
    where open Fold y w S

  Ψ : ∀ y → Lg y → A
  Ψ y w = sum azero (n1 ⨾ Ψd y w)

  Lg-Ψ : ∀ y w → Lg (Ψ y w)
  Lg-Ψ y w = Lg-sum azero (n1 ⨾ Ψd y w) tt

  cell : ℕ → Σ A Lg
  cell zero = asuc azero , tt
  cell (suc n) = Ψ (proj₁ (cell n)) (proj₂ (cell n)) , Lg-Ψ (proj₁ (cell n)) (proj₂ (cell n))

  ys : ℕ → A
  ys n = proj₁ (cell (suc n))

  Top : A
  Top = alim ys

-- ψ(a+1) = ψ(a)·ω: 差是 ψ(a) 的 ω 个
ω⋅ : ∀ {t} → D t → D t
ω⋅ c = nl (λ _ → c)

open Gen ω⋅ public
```

## §6 到第 0 层的树

```agda
ord : A → FL.Ordᶜ FL.zero
ord azero = FL.zero
ord (asuc a) = FL.suc (ord a)
ord (alim f) = FL.lim (λ n → ord (f n))

FGH′ : A → ℕ → ℕ
FGH′ a = FL.FGH (ord a)

fgh : ℕ → ℕ
fgh = FGH′ Top
```
