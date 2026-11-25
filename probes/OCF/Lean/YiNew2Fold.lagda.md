# YiNew2 相对折叠: 相对于底层 a, 朝 a 之上的一切有限层同时折叠

判决 (编译定理): 相对折叠 `Φ a m` 把 `a ⊕ m` 层的树折到各 `a ⊕ fin j` 层; 嵌入一致是 `refl` (`rup-Om`), 对第一位置序单调 (`rmono`), 不降底 (`rinfl`), 非零 (`rnz`).
做了什么: 第一轮的折叠是 a 取零层的情形; 字面证书是层号的字面分解 `a ⊕ m`, 分支类型字面为 `a ⊕ fin k` 的码带底对角化, a 自己的码一律保留.
不否定什么: 分支类型为 `a ⊕ m′` 而 m′ 非有限的码仍只有局部一步折叠 (`locR`), 跨 ℕ 极限或 Ω 结点后退成按自然数取值; 输出树的合法性没有证.
入口: 验收在 `OCF.Lean.YiNew2Key`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNew2Fold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Lean.YiNewBlock
open import OCF.Lean.YiNewFold
  using (_+_; S; iter; module Ord; module O; Le; D; Fin?; yes; no; fin?; Cmp; eq; ne; cmp; one)
```

## 相对目标与底

目标是 `a ⊕ fin j`: 对 a 之上的一切层 m 与一切孩子一致给出, 只由自然数 j 标记.
`hoist` 把 a 层的树逐层嵌进 `a ⊕ fin j`.

```agda
G : Lv → ℕ → Set
G a j = T (a ⊕ fin j)

RBase : Lv → Set
RBase a = (j : ℕ) → G a j

hoist : (a : Lv) (j : ℕ) → T a → G a j
hoist a zero    t = t
hoist a (suc j) t = up zr tt (hoist a j t)

scB : (ℓ : Lv) (u : U ℓ) → Br ℓ u → Br ℓ u
scB (su ℓ)   (inj₁ _) x = sc x
scB (su ℓ)   (inj₂ u) x = scB ℓ u x
scB (li f)   (n , u)  x = scB (f n) u x
scB (Om a f) (c , u)  x = scB (f c) u x
```

## 码的相对分类

对 m 递归, 只看码自己在 m 里的字面路径, 不比较孩子:

- `lowR`: 码来自 a 自己 (m 走到零), 在每个目标层里都有, 一律保留;
- `absR k`: 分支类型字面是 `a ⊕ fin k`, 带底对角化或保留;
- `locR`: 其余, 只有局部迭代.

```agda
data RC (a m : Lv) (u : U (a ⊕ m)) : Set where
  lowR : (u₀ : U a) (to : Br a u₀ → Br (a ⊕ m) u) → to (z0 a u₀) ≡ z0 (a ⊕ m) u → RC a m u
  absR : (k : ℕ) (to : G a k → Br (a ⊕ m) u) → to zr ≡ z0 (a ⊕ m) u → RC a m u
  locR : ((Br (a ⊕ m) u → T (a ⊕ m)) → Br (a ⊕ m) u → Br (a ⊕ m) u) → RC a m u

rcls : (a m : Lv) (u : U (a ⊕ m)) → RC a m u
rcls a ze u = lowR u (λ x → x) refl
rcls a (su m) (inj₁ _) with fin? m
... | yes k = absR k (λ x → x) refl
... | no    = locR (λ g ζ → D (a ⊕ m) (g ζ) one)
rcls a (su m) (inj₂ u) with rcls a m u
... | lowR u₀ to e = lowR u₀ to e
... | absR k to e  = absR k to e
... | locR s       = locR (λ g → s (λ z → D (a ⊕ m) (g z) one))
rcls a (li f) (n , u) with rcls a (f n) u
... | lowR u₀ to e = lowR u₀ to e
... | absR k to e  = absR k to e
... | locR _       = locR (λ g ζ → scB (a ⊕ f n) u ζ)
rcls a (Om b f) (c , u) with rcls a (f c) u
... | lowR u₀ to e = lowR u₀ to e
... | absR k to e  = absR k to e
... | locR _       = locR (λ g ζ → scB (a ⊕ f c) u ζ)
```

目标层里的槽位: a 自己的码总有 (`lowslot`); `a ⊕ fin k` 的顶码当 k < j 时有 (`rslot`, 自然数比较).

```agda
LowSlot : (a : Lv) (j : ℕ) (u₀ : U a) → Set
LowSlot a j u₀ = Σ (U (a ⊕ fin j)) (λ v → Σ (Br (a ⊕ fin j) v → Br a u₀)
                   (λ bk → bk (z0 (a ⊕ fin j) v) ≡ z0 a u₀))

lowslot : (a : Lv) (j : ℕ) (u₀ : U a) → LowSlot a j u₀
lowslot a zero    u₀ = u₀ , (λ x → x) , refl
lowslot a (suc j) u₀ with lowslot a j u₀
... | v , bk , e = inj₂ v , bk , e

RSlot : Lv → ℕ → ℕ → Set
RSlot a k j = Σ (U (a ⊕ fin j)) (λ v → Σ (Br (a ⊕ fin j) v → G a k)
                (λ bk → bk (z0 (a ⊕ fin j) v) ≡ zr))

rslot : (a : Lv) (k j : ℕ) → Maybe (RSlot a k j)
rslot a k zero = nothing
rslot a k (suc j) with cmp k j
... | eq = just (inj₁ tt , (λ x → x) , refl)
... | ne with rslot a k j
...   | just (v , bk , e) = just (inj₂ v , bk , e)
...   | nothing           = nothing
```

## 相对折叠

`Φ a m y B j`: 左边的项朝各 `a ⊕ fin j` 层的折叠是 B 时, 接上 `a ⊕ m` 层的 y, 朝 `a ⊕ fin j` 折叠.
m 走到零时 y 是 a 层自己的树: 它的嵌入段不再往里折, 逐层嵌进目标后加在右边.

```agda
RLimC : ∀ {a m u} → RC a m u → (Br (a ⊕ m) u → T (a ⊕ m)) → (Br (a ⊕ m) u → RBase a) → RBase a
RLimC {a} (lowR u₀ to _) g r j =
  Lm (proj₁ (lowslot a j u₀)) (λ z′ → r (to (proj₁ (proj₂ (lowslot a j u₀)) z′)) j)
RLimC {a} (absR k to _) g r j with rslot a k j
... | just (v , bk , _) = Lm v (λ z′ → r (to (bk z′)) j)
... | nothing           = lm (λ n → r (to (iter (λ ζ → r (to ζ) k) zr n)) j)
RLimC {a} {m} {u} (locR s) g r j = lm (λ n → r (iter (s g) (z0 (a ⊕ m) u) n) j)

Φ  : (a m : Lv) → T (a ⊕ m) → RBase a → RBase a
ΦE : (a m : Lv) (e : E (a ⊕ m)) → Em (a ⊕ m) e → RBase a → RBase a
Φ a m zr         B = B
Φ a m (sc y)     B = λ j → S (Φ a m y B j)
Φ a m (lm g)     B = λ j → lm (λ n → Φ a m (g n) B j)
Φ a m (Lm u g)   B = RLimC (rcls a m u) g (λ z → Φ a m (g z) B)
Φ a m (up x e y) B = ΦE a m e y (Φ a m x B)
ΦE a ze       e y B = λ j → B j + hoist a j (up zr e y)
ΦE a (su m)   _ y B = Φ a m y B
ΦE a (li f)   n y B = Φ a (f n) y B
ΦE a (Om b f) c y B = Φ a (f c) y B
```

嵌入一致: 定义等式. 孩子 c 只来自 `up` 自己.

```agda
rup-Om : ∀ a b f x c y B → Φ a (Om b f) (up x c y) B ≡ Φ a (f c) y (Φ a (Om b f) x B)
rup-Om a b f x c y B = refl

rup-li : ∀ a f x n y B → Φ a (li f) (up x n y) B ≡ Φ a (f n) y (Φ a (li f) x B)
rup-li a f x n y B = refl

rup-su : ∀ a m x y B → Φ a (su m) (up x tt y) B ≡ Φ a m y (Φ a (su m) x B)
rup-su a m x y B = refl
```

## 不降底与单调

```agda
module _ {a : Lv} {j : ℕ} where
  open O (a ⊕ fin j)

  RLimC-infl : ∀ {m u} (c : RC a m u) g r {b} → b ≤ r (z0 (a ⊕ m) u) j → b ≤ RLimC c g r j
  RLimC-infl (lowR u₀ to e) g r {b} p =
    ≤L (subst (λ w → b ≤ r w j) (sym (trans (cong to (proj₂ (proj₂ (lowslot a j u₀)))) e)) p)
  RLimC-infl (absR k to e) g r {b} p with rslot a k j
  ... | just (v , bk , e′) = ≤L (subst (λ w → b ≤ r w j) (sym (trans (cong to e′) e)) p)
  ... | nothing            = ≤l (subst (λ w → b ≤ r w j) (sym e) p)
  RLimC-infl (locR s) g r p = ≤l p

  RLimC-mono : ∀ {m u} (c : RC a m u) g g′ r r′
             → r (z0 (a ⊕ m) u) j ≤ r′ (z0 (a ⊕ m) u) j → RLimC c g r j ≤ RLimC c g′ r′ j
  RLimC-mono (lowR u₀ to e) g g′ r r′ p =
    L≤L (subst (λ w → r w j ≤ r′ w j) (sym (trans (cong to (proj₂ (proj₂ (lowslot a j u₀)))) e)) p)
  RLimC-mono (absR k to e) g g′ r r′ p with rslot a k j
  ... | just (v , bk , e′) = L≤L (subst (λ w → r w j ≤ r′ w j) (sym (trans (cong to e′) e)) p)
  ... | nothing            = l≤l (subst (λ w → r w j ≤ r′ w j) (sym e) p)
  RLimC-mono (locR s) g g′ r r′ p = l≤l p

rinfl  : ∀ a m y B j {b} → Le (a ⊕ fin j) b (B j) → Le (a ⊕ fin j) b (Φ a m y B j)
rinflE : ∀ a m e y B j {b} → Le (a ⊕ fin j) b (B j) → Le (a ⊕ fin j) b (ΦE a m e y B j)
rinfl a m zr         B j p = p
rinfl a m (sc y)     B j p = O.≤S (a ⊕ fin j) (rinfl a m y B j p)
rinfl a m (lm g)     B j p = Ord.≤l (rinfl a m (g 0) B j p)
rinfl a m (Lm u g)   B j p =
  RLimC-infl (rcls a m u) g (λ z → Φ a m (g z) B) (rinfl a m (g (z0 (a ⊕ m) u)) B j p)
rinfl a m (up x e y) B j p = rinflE a m e y (Φ a m x B) j (rinfl a m x B j p)
rinflE a ze       e y B j p = O.≤+ (a ⊕ fin j) (hoist a j (up zr e y)) p
rinflE a (su m)   _ y B j p = rinfl a m y B j p
rinflE a (li f)   n y B j p = rinfl a (f n) y B j p
rinflE a (Om b f) c y B j p = rinfl a (f c) y B j p

_≤ᴿ[_]_ : ∀ {a} → RBase a → (a′ : Lv) → RBase a → Set
_≤ᴿ[_]_ {a} B _ B′ = ∀ j → Le (a ⊕ fin j) (B j) (B′ j)

rmono  : ∀ a m {x y} → Le (a ⊕ m) x y → ∀ {B B′} → B ≤ᴿ[ a ] B′ → Φ a m x B ≤ᴿ[ a ] Φ a m y B′
rmonoE : ∀ a m e y {B B′} → B ≤ᴿ[ a ] B′ → ΦE a m e y B ≤ᴿ[ a ] ΦE a m e y B′
rmono a m (Ord.z≤ {a = t}) {B′ = B′} q j = rinfl a m t B′ j (q j)
rmono a m (Ord.s≤s p) q j = O.S-mono (a ⊕ fin j) (rmono a m p q j)
rmono a m (Ord.≤s p)  q j = O.≤S (a ⊕ fin j) (rmono a m p q j)
rmono a m (Ord.≤l p)  q j = Ord.≤l (rmono a m p q j)
rmono a m (Ord.l≤l p) q j = Ord.l≤l (rmono a m p q j)
rmono a m (Ord.≤L {u = u} {g = g} p) {B′ = B′} q j =
  RLimC-infl (rcls a m u) g (λ z → Φ a m (g z) B′) (rmono a m p q j)
rmono a m (Ord.L≤L {u = u} {f = f} {g = g} p) {B = B} {B′ = B′} q j =
  RLimC-mono (rcls a m u) f g (λ z → Φ a m (f z) B) (λ z → Φ a m (g z) B′) (rmono a m p q j)
rmono a m (Ord.≤u {x = x} {e = e} {y = y} p) {B′ = B′} q j =
  rinflE a m e y (Φ a m x B′) j (rmono a m p q j)
rmono a m (Ord.u≤u {e = e} {y = y} p) q j = rmonoE a m e y (rmono a m p q) j
rmonoE a ze       e y q j =
  O.+mono (a ⊕ fin j) (q j) (O.≤-refl (a ⊕ fin j) (hoist a j (up zr e y)))
rmonoE a (su m)   _ y q = rmono a m (O.≤-refl (a ⊕ m) y) q
rmonoE a (li f)   n y q = rmono a (f n) (O.≤-refl (a ⊕ f n) y) q
rmonoE a (Om b f) c y q = rmono a (f c) (O.≤-refl (a ⊕ f c) y) q
```

## 起始的底与非零

```agda
R° : (a : Lv) → RBase a
R° a zero    = one
R° a (suc j) = Lm (inj₁ tt) (λ ζ → up one tt ζ)

R°-nz : ∀ a j → Le (a ⊕ fin j) one (R° a j)
R°-nz a zero    = Ord.s≤s Ord.z≤
R°-nz a (suc j) = Ord.≤L (Ord.≤u (Ord.s≤s Ord.z≤))

rnz : ∀ a m y j → Le (a ⊕ fin j) one (Φ a m y (R° a) j)
rnz a m y j = rinfl a m y (R° a) j (R°-nz a j)
```
