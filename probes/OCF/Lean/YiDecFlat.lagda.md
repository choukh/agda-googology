# V107 的实验 (二): 诊断：上界 (结构上的, 不是值的)

> 诊断：上界. 不进成品. 判决: 编译定理, 无前提, 对一切下标层号 k, 一切输入树, 一切底. 朝孩子层目标 (`inb c′ w`) 的折叠, 输出里的结点只有两种来源: 起点 β 自带的, 与输入的主侧槽位保留下来的 (`thin`); 自身行 (上折) 从孩子树搬来的结点一律成为 ℕ 极限 (`up-flat`).
> 在 `tw 1` 上: 孩子的底在层号 j 的分量, 除 `Ωt j` 自带的结点外, 只有以第 0 层的树为分支的结点 (`base-thin`, `base-thin₂`). 对照: 记号的 ψ_j(·) 的余尾可以是任何 Ω_i, i ≤ j (`YiT2Frame.note-cof` 是一例).
> 不给出什么: 没有值的上界, 没有 `¬ (Rt h₊ ≼ …)`; "这两行使 `T⁺` 低于记号" 仍是判断. 下界见 [YiDecLow](YiDecLow.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDecFlat where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath hiding (eq; lt; gt; here)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSTw1 using (h₁)
open import OCF.Lean.YiT2Frame using (ε¹; ρ¹; IsLim; two)
```

## 结点的槽位谓词

`Nd Q t`: 树 t 在本层的每个结点, 槽位都满足 Q. 嵌入的孩子树不看 (它在更低的层). 加法, `next`, 部分和的极限, 第 0 层的嵌入都保持它.

```agda
data Nd {S : Sg} (Q : P S → Set) : T S → Set where
  dz : Nd Q zero
  ds : ∀ {x} → Nd Q x → Nd Q (suc x)
  dl : ∀ {f a} → ((n : ℕ) → Nd Q (f n)) → Nd Q (lim f a)
  dΩ : ∀ {p g} → Q p → ((z : B S p) → Nd Q (g z)) → Nd Q (Ω p g)
  du : ∀ {x c y e} → Nd Q x → Nd Q (up x c y e)

module _ {S : Sg} {Q : P S → Set} where
  Nd-+ : {a b : T S} → Nd Q a → Nd Q b → Nd Q (a + b)
  Nd-+ pa dz       = pa
  Nd-+ pa (ds h)   = ds (Nd-+ pa h)
  Nd-+ pa (dl h)   = dl (λ n → Nd-+ pa (h n))
  Nd-+ pa (dΩ q h) = dΩ q (λ z → Nd-+ pa (h z))
  Nd-+ pa (du h)   = du (Nd-+ pa h)

  Nd-iter : {b : T S} → Nd Q b → (n : ℕ) → Nd Q (iter (b +_) b n)
  Nd-iter pb zero    = pb
  Nd-iter pb (suc n) = Nd-+ pb (Nd-iter pb n)

  Nd-next : {b : T S} {e : Lt S zero b} → Nd Q b → Nd Q (next b e)
  Nd-next pb = dl (Nd-iter pb)

  Nd-cum : {F : ℕ → T S} → ((n : ℕ) → Nd Q (F n)) → (n : ℕ) → Nd Q (cum F n)
  Nd-cum h zero    = h zero
  Nd-cum h (suc n) = Nd-+ (Nd-cum h n) (h (suc n))

  Nd-limc : {F : ℕ → T S} {e : (n : ℕ) → Lt S zero (F n)} → ((n : ℕ) → Nd Q (F n)) → Nd Q (limc F e)
  Nd-limc h = dl (Nd-cum h)

Nd-ι : (j : LF) {Q : Pos j → Set} (x : Tr zero) → Nd Q (ι j x)
Nd-ι j zero          = dz
Nd-ι j (suc x)       = ds (Nd-ι j x)
Nd-ι j (lim f a)     = dl (λ n → Nd-ι j (f n))
Nd-ι j (Ω () _)
Nd-ι j (up _ () _ _)
```

## 保留判定只交出同层号的槽位

`kp` 保留时交给 K 的槽位 q, 层号与原槽位 p 相同. 证明与 `YiLegFold.kp-ind` 同构, 不变量换成 `at`.

```agda
psh-at : ∀ {k a} (v : k ≤ a) (t : Pos⁼ k) → at⁼ a (psh v t) ≡ at⁼ k t
psh-at self      t = refl
psh-at (ins v)   t = psh-at v t
psh-at (inl n v) t = psh-at v t
psh-at (inlu vs) t = psh-at (vs zero) t
psh-at (ink v)   t = psh-at v t
psh-at (inb c v) t = psh-at v t
psh-at (inu vs)  t = psh-at (vs zero) t

mutual
  kp-at : (ℓ : LF) (ε : Ev ℓ) (ρ : Rt ℓ) (p : Pos ℓ) {j : LF} (v : j ≤ ℓ) {X : Set} (Q : X → Set)
    {K : (q : Pos j) → (Br j q → Br ℓ p) → X} {d : X}
    → ((q : Pos j) (cv : Br j q → Br ℓ p) → at j q ≡ at ℓ p → Q (K q cv)) → Q d
    → Q (kp ℓ ε ρ p v K d)
  kp-at ℓ        ε ρ p       self      Q hk hd = hk p (λ z → z) refl
  kp-at (suc a)  ε ρ p       (ins v)   Q hk hd = kp⁼-at a ε ρ p v Q hk hd
  kp-at (lim g)  ε (ρc , R) (m , p) (inl n v) Q hk hd with way g R m n
  ... | fwd r = kp⁼-at (g n) (ε n) (ρc n) (psh r p) v Q
      (λ q cv e → hk q (λ z → pshBr r p (cv z)) (trans e (psh-at r p))) hd
  ... | bwd r = kp⁼-at (g m) (ε m) (ρc m) p (v ∙ r) Q hk hd
  kp-at (lim g)  ε (ρc , R) (m , p) (inlu vs) Q hk hd = kp⁼-at (g m) (ε m) (ρc m) p (vs m) Q hk hd
  kp-at (Ωₗ k h) (ek , e) (ρk , ρc) (inj₁ t)       (ink v)    Q hk hd = kp⁼-at k ek ρk t v Q hk hd
  kp-at (Ωₗ k h) (ek , e) (ρk , ρc) (inj₁ t)       (inb c v)  Q hk hd =
    kp⁼-at (h c) (proj₂ (e c)) (ρc c) (psh (proj₁ (e c)) t) v Q
      (λ q cv eq → hk q (λ z → pshBr (proj₁ (e c)) t (cv z)) (trans eq (psh-at (proj₁ (e c)) t))) hd
  kp-at (Ωₗ k h) (ek , e) (ρk , ρc) (inj₁ t)       (inu vs)   Q hk hd =
    kp⁼-at (h zero) (proj₂ (e zero)) (ρc zero) (psh (proj₁ (e zero)) t) (vs zero) Q
      (λ q cv eq → hk q (λ z → pshBr (proj₁ (e zero)) t (cv z)) (trans eq (psh-at (proj₁ (e zero)) t))) hd
  kp-at (Ωₗ k h) (ek , e) (ρk , ρc) (inj₂ (c , t)) (ink v)    Q hk hd =
    kp⁼-at (h c) (proj₂ (e c)) (ρc c) t (v ∙ proj₁ (e c)) Q hk hd
  kp-at (Ωₗ k h) (ek , e) (ρk , ρc) (inj₂ (c , t)) (inu vs)   Q hk hd =
    kp⁼-at (h c) (proj₂ (e c)) (ρc c) t (vs c) Q hk hd
  kp-at (Ωₗ k h) (ek , e) (ρk , ρc) (inj₂ (c , t)) (inb c′ v) Q hk hd = hd

  kp⁼-at : (a : LF) (ε : Ev a) (ρ : Rt a) (p : Pos⁼ a) {j : LF} (v : j ≤ a) {X : Set} (Q : X → Set)
    {K : (q : Pos j) → (Br j q → Br⁼ a p) → X} {d : X}
    → ((q : Pos j) (cv : Br j q → Br⁼ a p) → at j q ≡ at⁼ a p → Q (K q cv)) → Q d
    → Q (kp⁼ a ε ρ p v K d)
  kp⁼-at a ε ρ (inj₁ _) v Q hk hd = hd
  kp⁼-at a ε ρ (inj₂ p) v Q hk hd = kp-at a ε ρ p v Q hk hd
```

## 朝孩子层目标的折叠: 输出的结点来自 β 或输入的主侧槽位

对输入树归纳. 四行: 主侧槽位的结点按 `kp` 保留 (槽位层号是 k 一侧的, `kp-at`) 或成为部分和的极限; 孩子一侧槽位的结点一律成为部分和的极限 (摊平式); 嵌入一行是回退, 加上的是第 0 层的树的嵌入, 没有结点.

```agda
module Thin (k : LF) (h : Tr k → LF) (ek : Ev k) (e : (c : Tr k) → (k ≤ h c) × Ev (h c))
  (ρk : Rt k) (ρc : (c : Tr k) → Rt (h c)) (B : Base (Ωₗ k h))
  (j : LF) (c′ : Tr k) (w : j ≤ h c′)
  (Q : Pos j → Set) (mq : (q : Pos j) (t : Pos⁼ k) → at j q ≡ at⁼ k t → Q q)
  (β : Tr j) (nβ : j ⊢ zero ◃ β) (pβ : Nd Q β) where

  F : Tr (Ωₗ k h) → Tr j
  F = ψs (Ωₗ k h) (ek , e) (ρk , ρc) B j (inb c′ w) β nβ

  stp : (p : Pos (Ωₗ k h)) (g : Br (Ωₗ k h) p → Tr (Ωₗ k h)) → ℕ → Br (Ωₗ k h) p
  stp p g = iter (λ z → fromBr (Ωₗ k h) p (ψs (Ωₗ k h) (ek , e) (ρk , ρc) B (at (Ωₗ k h) p) (posW (Ωₗ k h) p)
    (bs B (at (Ωₗ k h) p) (posW (Ωₗ k h) p)) (ns B (at (Ωₗ k h) p) (posW (Ωₗ k h) p)) (g z))) (br0 (Ωₗ k h) p)

  thin′ : (x : Tr (Ωₗ k h)) → Nd Q (F x)
  thin′ zero      = pβ
  thin′ (suc x)   = Nd-next (thin′ x)
  thin′ (lim f a) = dl (λ n → thin′ (f n))
  thin′ (Ω (inj₁ t) g) =
    kp⁼-at (h c′) (proj₂ (e c′)) (ρc c′) (psh (proj₁ (e c′)) t) w (Nd Q)
      (λ q cv eq → dΩ (mq q t (trans eq (psh-at (proj₁ (e c′)) t)))
                      (λ z → thin′ (g (pshBr (proj₁ (e c′)) t (cv z)))))
      (dl (Nd-cum {F = λ n → F (g (stp (inj₁ t) g n))} (λ n → thin′ (g (stp (inj₁ t) g n)))))
  thin′ (Ω (inj₂ (c , t)) g) =
    dl (Nd-cum {F = λ n → F (g (stp (inj₂ (c , t)) g n))} (λ n → thin′ (g (stp (inj₂ (c , t)) g n))))
  thin′ (up x c y e₀) = Nd-+ (thin′ x) (Nd-ι j _)

thin : (k : LF) (h : Tr k → LF) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h))
  (j : LF) (c′ : Tr k) (w : j ≤ h c′)
  (Q : Pos j → Set) → ((q : Pos j) (t : Pos⁼ k) → at j q ≡ at⁼ k t → Q q)
  → (β : Tr j) (nβ : j ⊢ zero ◃ β) → Nd Q β
  → (x : Tr (Ωₗ k h)) → Nd Q (ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x)
thin k h ε ρ B j c′ w Q mq β nβ pβ =
  Thin.thin′ k h (proj₁ ε) (proj₂ ε) (proj₁ ρ) (proj₂ ρ) B j c′ w Q mq β nβ pβ
```

## 自身行搬来的结点一律成为 ℕ 极限

上折把孩子树的结点搬到孩子一侧的槽位 (`mvC`); 这种槽位朝任何孩子层目标都不保留 (`slot-lim`). 所以对一切孩子层号, 一切孩子树里的结点 `Ω p g`, 一切底: 上折的像再朝孩子层目标折叠, 是 ℕ 极限 (`up-flat`). `YiT2Frame.flat-lim` 是 `tw 1` 上的一例.

```agda
mvC : (k : LF) (h : Tr k → LF) {j′ : LF} (d : Dn (Ωₗ k h) j′) (c : Ch j′) (p : Pos (chL j′ c))
  → Σ (Tr k) λ c₀ → Σ (Pos⁼ (h c₀)) λ t → mv (down d c) p ≡ inj₂ (c₀ , t)
mvC k h stop              c p = c , inj₂ p , refl
mvC k h (down d c₁)      c p = mvC k h d c₁ (chP _ c p)

slot-lim : (k : LF) (h : Tr k → LF) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h))
  (j : LF) (c′ : Tr k) (w : j ≤ h c′) (β : Tr j) (nβ : j ⊢ zero ◃ β)
  (q : Pos (Ωₗ k h)) → (Σ (Tr k) λ c₀ → Σ (Pos⁼ (h c₀)) λ t → q ≡ inj₂ (c₀ , t))
  → (g : Br (Ωₗ k h) q → Tr (Ωₗ k h))
  → IsLim (ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ (Ω q g))
slot-lim k h ε ρ B j c′ w β nβ .(inj₂ (c₀ , t)) (c₀ , t , refl) g = tt

up-flat : (k : LF) (h : Tr k → LF) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h))
  (j : LF) (c′ : Tr k) (w : j ≤ h c′) (β : Tr j) (nβ : j ⊢ zero ◃ β)
  {j′ : LF} (d : Dn (Ωₗ k h) j′) (c : Ch j′) (b : Tr (Ωₗ k h)) (nb : Ωₗ k h ⊢ zero ◃ b)
  (p : Pos (chL j′ c)) (g : Br (chL j′ c) p → Tr (chL j′ c))
  → IsLim (ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ (Up (chL j′ c) (down d c) b nb (Ω p g)))
up-flat k h ε ρ B j c′ w β nβ {j′} d c b nb p g =
  slot-lim k h ε ρ B j c′ w β nβ (mv (down d c) p) (mvC k h d c p)
    (λ z → Up (chL j′ c) (down d c) b nb (g (mvBr (down d c) p z)))
```

## `tw 1` 上的实例

主侧只有一个槽位, 层号是第 0 层. 所以孩子的底在层号 j 的分量 (对一切输入 x, 一切分支 c): 结点或者是 `Ωt j` 自带的 (Q 里由 `pΩ` 给出), 或者以第 0 层的树为分支.

```agda
at⁼0 : (t : Pos⁼ zero) → at⁼ zero t ≡ zero
at⁼0 (inj₁ _) = refl
at⁼0 (inj₂ ())

base-thin : (j : LF) (Q : Pos j → Set) → ((q : Pos j) → at j q ≡ zero → Q q) → Nd Q (Ωt j)
  → (x : Tr (tw 1)) (c : Tr zero) (w : j ≤ h₁ c)
  → Nd Q (bs (dW zero h₁ ε¹ ρ¹ (B₀ (tw 1)) c x) j w)
base-thin j Q mq pΩ x c w =
  thin zero h₁ ε¹ ρ¹ (B₀ (tw 1)) j c w Q (λ q t eq → mq q (trans eq (at⁼0 t))) (Ωt j) (Ωt-nz j) pΩ x
```

层号 2 (分支 `two`): `Ωt 2` 自带的结点在顶槽位 `inj₁ tt`, 分支是第 1 层的树 (余尾 Ω₂). 对一切 x, 底在层号 2 的分量里, 别的结点都以第 0 层的树为分支. 特别地, x 里以第 1 层的树为分支的结点 (自身行从孩子树搬来的) 不留在输出里.

```agda
Q₂ : Pos (suc (suc zero)) → Set
Q₂ q = (at (suc (suc zero)) q ≡ zero) ⊎ (q ≡ inj₁ tt)

base-thin₂ : (x : Tr (tw 1))
  → Nd Q₂ (bs (dW zero h₁ ε¹ ρ¹ (B₀ (tw 1)) two x) (suc (suc zero)) self)
base-thin₂ x = base-thin (suc (suc zero)) Q₂ (λ q eq → inj₁ eq) (dΩ (inj₂ refl) (λ z → du dz)) x two self
```
