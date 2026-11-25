# 空白页候选 B 的折叠: 字面比较位置, 孩子里的目标经 `ex` 结点相对给出

> 折叠 (不读记号). `ψc ℓ T bot w`: 把 "底 + w" 折到目标 T, 底在 w 走到零时由 `bot` 按当时的目标折出; 走进 `ex x a y` 时底变成 "折 x 到孩子 a 里的目标", 所以孩子层里的对角链每一步都带着左边的 x. 目标 `Tg ℓ A`: ℓ 的位置 (`pos`), 孩子 a 里的目标 (`inch`), 同一基底上别的孩子里的层 (`side`), 高于 ℓ 全部位置的层 (`abv`, 带字面嵌入), 或比不出 (`unk`). 合法性由类型保证.
> 不比较两个孩子: 两个孩子位置之间一律 `other`; 孩子里的目标搬进任一个孩子 (含它自己) 一律给 `side` (只认基底); 不看孩子树是否相等; ℕ 极限层只比较自然数下标. 闭项 `ψΛ` (读作 ψ₀(Λ)) 与 `tB′` (读作 ψ₀(Ω_Ω+Ω₂)), 读法是判断.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBPFold where

open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiBPBlock
```

## 同一层里位置的字面比较

`Cmp A T`: 目标层 A 里有位置 q*, 分支类型换算到 T (`below`, 换算都是恒等); 或比不出 (`other`).

```agda
data Cmp (A : Lv) (T : Set) : Set where
  below : (q* : Pos A) → (TrAt A q* → T) → Cmp A T
  other : Cmp A T

mutual
  cmp⁺ : ∀ μ (b b′ : Pos⁺ μ) → Cmp (at⁺ μ b) (TrAt⁺ μ b′)
  cmp⁺ μ (inj₁ _) (inj₁ _)  = other
  cmp⁺ μ (inj₁ _) (inj₂ q)  = below q (λ x → x)
  cmp⁺ μ (inj₂ p) (inj₁ _)  = other
  cmp⁺ μ (inj₂ p) (inj₂ q)  = cmp μ p q

  cmp : ∀ ℓ (p q : Pos ℓ) → Cmp (at ℓ p) (TrAt ℓ q)
  cmp z () q
  cmp (μ ⊞ c) (inj₁ b) (inj₁ b′)     = cmp⁺ μ b b′
  cmp (μ ⊞ c) (inj₁ b) (inj₂ _)      = other
  cmp (μ ⊞ c) (inj₂ ip) (inj₁ b′)    = below (inj₁ b′) (λ x → x)
  cmp (μ ⊞ c) (inj₂ ip) (inj₂ ip′)   = cmpI μ c ip ip′
  cmp (l f) (n , b) (m , b′)         = cmpN f n m b b′ (n ≟ m)
  cmp (Ωₗ μ) (inj₁ b) (inj₁ b′)      = cmp⁺ μ b b′
  cmp (Ωₗ μ) (inj₁ b) (inj₂ _)       = other
  cmp (Ωₗ μ) (inj₂ (c , inj₁ _)) (inj₁ b′)  = below (inj₁ b′) (λ x → x)
  cmp (Ωₗ μ) (inj₂ (c , inj₂ _)) (inj₁ b′)  = below (inj₁ b′) (λ x → x)
  cmp (Ωₗ μ) (inj₂ _) (inj₂ _)       = other

  cmpN : ∀ (f : ℕ → Lv) n m (b : Pos⁺ (f n)) (b′ : Pos⁺ (f m)) → Dec (n ≡ m) →
         Cmp (at⁺ (f n) b) (TrAt⁺ (f m) b′)
  cmpN f n .n b b′ (yes refl) = cmp⁺ (f n) b b′
  cmpN f n m  b b′ (no _)     = other

  cmpI : ∀ μ c (ip ip′ : IPos μ c) → Cmp (μ ⊞ sub μ c ip) (TrI μ c ip′)
  cmpI μ (suc c) (inj₁ _) (inj₁ _)     = other
  cmpI μ (suc c) (inj₁ _) (inj₂ ip′)   = below (inj₂ ip′) (λ x → x)
  cmpI μ (suc c) (inj₂ _) (inj₁ _)     = other
  cmpI μ (suc c) (inj₂ ip) (inj₂ ip′)  = cmpI μ c ip ip′
  cmpI μ (lim f) (n , x) (m , y)       = cmpIL μ f n m x y (n ≟ m)
  cmpI μ (Ω q f) _ _                   = other
  cmpI μ (ex x a y) ip ip′             = cmpI μ x ip ip′

  cmpIL : ∀ μ (f : ℕ → Tr μ) n m (x : ⊤ ⊎ IPos μ (f n)) (y : ⊤ ⊎ IPos μ (f m)) → Dec (n ≡ m) →
          Cmp (μ ⊞ sub μ (lim f) (n , x)) (TrI μ (lim f) (m , y))
  cmpIL μ f n .n (inj₁ _) (inj₁ _)    (yes refl) = other
  cmpIL μ f n .n (inj₁ _) (inj₂ ip′)  (yes refl) = below (inj₂ ip′) (λ x → x)
  cmpIL μ f n .n (inj₂ _) (inj₁ _)    (yes refl) = other
  cmpIL μ f n .n (inj₂ ip) (inj₂ ip′) (yes refl) = cmpI μ (f n) ip ip′
  cmpIL μ f n m x y (no _) = other
```

## 目标

`Tg ℓ A`: 从层 ℓ 看, 目标层是 A. `inch a T`: 目标在孩子 a 里, 由孩子自己的坐标给出; 这是 `ex` 结点留下的字面证据.

```agda
record Emb (L A : Lv) : Set where
  constructor emb
  field
    ι : Pos L → Pos A
    κ : ∀ r → TrAt A (ι r) → TrAt L r
open Emb

_∘ᴱ_ : ∀ {L M A} → Emb M A → Emb L M → Emb L A
F ∘ᴱ E = emb (λ r → ι F (ι E r)) (λ r x → κ E r (κ F (ι E r) x))

e⊞ : ∀ μ c → Emb μ (μ ⊞ c)
e⊞ μ c = emb (λ r → inj₁ (inj₂ r)) (λ r x → x)

eB : ∀ μ → Emb μ (Ωₗ μ)
eB μ = emb (λ r → inj₁ (inj₂ r)) (λ r x → x)

eN : ∀ (f : ℕ → Lv) n → Emb (f n) (l f)
eN f n = emb (λ r → n , inj₂ r) (λ r x → x)

eC : ∀ μ s → Emb (μ ⊞ s) (Ωₗ μ)
eC μ s = emb h k
  where
  h : Pos (μ ⊞ s) → Pos (Ωₗ μ)
  h (inj₁ b)  = inj₁ b
  h (inj₂ ip) = inj₂ (s , inj₂ ip)
  k : ∀ r → TrAt (Ωₗ μ) (h r) → TrAt (μ ⊞ s) r
  k (inj₁ b)  x = x
  k (inj₂ ip) x = x

ιI : ∀ μ c ia → IPos μ (subC μ c ia) → IPos μ c
ιI μ (suc c) ia ip               = inj₂ (ιI μ c ia ip)
ιI μ (lim f) (n , ia) ip         = n , inj₂ (ιI μ (f n) ia ip)
ιI μ (Ω q f) (e , inj₁ _) ip     = e , inj₂ ip
ιI μ (Ω q f) (e , inj₂ ia) ip    = e , inj₂ (ιI μ (f e) ia ip)
ιI μ (ex x a y) ia ip            = ιI μ x ia ip

κI : ∀ μ c ia ip → TrI μ c (ιI μ c ia ip) → TrI μ (subC μ c ia) ip
κI μ (suc c) ia ip x             = κI μ c ia ip x
κI μ (lim f) (n , ia) ip x       = κI μ (f n) ia ip x
κI μ (Ω q f) (e , inj₁ _) ip x   = x
κI μ (Ω q f) (e , inj₂ ia) ip x  = κI μ (f e) ia ip x
κI μ (ex y a w) ia ip x          = κI μ y ia ip x

eI : ∀ μ c ia → Emb (μ ⊞ subC μ c ia) (μ ⊞ c)
eI μ c ia = emb h k
  where
  h : Pos (μ ⊞ subC μ c ia) → Pos (μ ⊞ c)
  h (inj₁ b)  = inj₁ b
  h (inj₂ ip) = inj₂ (ιI μ c ia ip)
  k : ∀ r → TrAt (μ ⊞ c) (h r) → TrAt (μ ⊞ subC μ c ia) r
  k (inj₁ b)  x = x
  k (inj₂ ip) x = κI μ c ia ip x

chE : ∀ ℓ (a : Ch ℓ) → Emb (chAt ℓ a) ℓ
chE z ()
chE (μ ⊞ c) (inj₁ a)            = e⊞ μ c ∘ᴱ chE μ a
chE (μ ⊞ c) (inj₂ ia)           = eI μ c ia
chE (l f) (n , a)               = eN f n ∘ᴱ chE (f n) a
chE (Ωₗ μ) (inj₁ a)             = eB μ ∘ᴱ chE μ a
chE (Ωₗ μ) (inj₂ (c , inj₁ _))  = eC μ c
chE (Ωₗ μ) (inj₂ (c , inj₂ ia)) = eC μ (subC μ c ia)
```

`ι`, `κ`: 一层的位置字面地嵌进另一层, 分支类型的换算是恒等; `chE ℓ a`: 孩子 a 的位置嵌进 ℓ (孩子内部的位置是 ℓ 的展平位置).

```agda
data IsSide : Lv → Lv → Set where
  sd : ∀ {μ c s} → IsSide (μ ⊞ c) (μ ⊞ s)

data Tg : Lv → Lv → Set where
  pos  : ∀ {ℓ} (p : Pos ℓ) → Tg ℓ (at ℓ p)
  inch : ∀ {ℓ A} (a : Ch ℓ) → Tg (chAt ℓ a) A → Tg ℓ A
  side : ∀ {ℓ A} → IsSide ℓ A → Tg ℓ A
  abv  : ∀ {ℓ A} → Emb ℓ A → Tg ℓ A
  unk  : ∀ {ℓ A} → Tg ℓ A
```

`abv E`: 目标层 A 高于 ℓ 的全部位置, 并由 E 字面地给出 ℓ 的位置在 A 里的位置.

`side`: 目标是同一个基底 μ 之上的另一层 μ ⊞ s (来自别的孩子里的目标); 只知道它高于基底, 所以基底部分的位置字面地在它之下, 增量部分比不出.

`cmpT`: 分支位置 r 对目标. 目标在孩子 a 里时, r 字面地在 a 的基底之下才搬进孩子的坐标再比, 否则 `other`.

```agda
mapCmp : ∀ {A T T′} → (T → T′) → Cmp A T → Cmp A T′
mapCmp g (below q* cv) = below q* (λ e → g (cv e))
mapCmp g other         = other

mutual
  cmpT : ∀ ℓ {A} → Tg ℓ A → (r : Pos ℓ) → Cmp A (TrAt ℓ r)
  cmpT ℓ (pos p)    r = cmp ℓ p r
  cmpT ℓ (inch a T) r = cmpIn ℓ a T r
  cmpT .(_ ⊞ _) (side sd) (inj₁ b) = below (inj₁ b) (λ x → x)
  cmpT .(_ ⊞ _) (side sd) (inj₂ _) = other
  cmpT ℓ (abv E)    r = below (ι E r) (κ E r)
  cmpT ℓ unk        r = other

  cmpIn : ∀ ℓ (a : Ch ℓ) {A} → Tg (chAt ℓ a) A → (r : Pos ℓ) → Cmp A (TrAt ℓ r)
  cmpIn z () T r
  cmpIn (μ ⊞ c) (inj₁ a) T (inj₁ (inj₂ q)) = cmpIn μ a T q
  cmpIn (μ ⊞ c) (inj₁ a) T _               = other
  cmpIn (μ ⊞ c) (inj₂ ia) T (inj₁ b)       = cmpT (μ ⊞ subC μ c ia) T (inj₁ b)
  cmpIn (μ ⊞ c) (inj₂ ia) T (inj₂ _)       = other
  cmpIn (l f) (n , a) T (m , b)            = cmpInN f n m a T b (n ≟ m)
  cmpIn (Ωₗ μ) (inj₁ a) T (inj₁ (inj₂ q))  = cmpIn μ a T q
  cmpIn (Ωₗ μ) (inj₁ a) T _                = other
  cmpIn (Ωₗ μ) (inj₂ (c , inj₁ _)) T (inj₁ b)  = cmpT (μ ⊞ c) T (inj₁ b)
  cmpIn (Ωₗ μ) (inj₂ (c , inj₂ ia)) T (inj₁ b) = cmpT (μ ⊞ subC μ c ia) T (inj₁ b)
  cmpIn (Ωₗ μ) (inj₂ _) T (inj₂ _)         = other

  cmpInN : ∀ (f : ℕ → Lv) n m (a : Ch (f n)) {A} → Tg (chAt (f n) a) A → (b : Pos⁺ (f m)) →
           Dec (n ≡ m) → Cmp A (TrAt⁺ (f m) b)
  cmpInN f n .n a T (inj₂ q) (yes refl) = cmpIn (f n) a T q
  cmpInN f n m a T b _ = other
```

`enter`: 走进 `ex x a y` 时把目标搬进孩子 a 的坐标. 目标位置字面地在 a 的基底之下: 搬成孩子的位置; 字面地在 a 所属 Ω 结点之上或就是它: `abv` (孩子的位置经 `chE` 嵌进目标层); 目标在某个孩子里 (`inch`): 不比较两个孩子, 给 `side` 或 `unk`.

```agda
mutual
  enter : ∀ ℓ (a : Ch ℓ) {A} → Tg ℓ A → Tg (chAt ℓ a) A
  enter ℓ a (pos p)    = enterP ℓ a p
  enter (Ωₗ μ) (inj₂ (c′ , inj₁ _)) (inch (inj₂ (c , inj₁ _)) (pos (inj₂ _)))   = side sd
  enter (Ωₗ μ) (inj₂ (c′ , inj₁ _)) (inch (inj₂ (c , inj₂ _)) (pos (inj₂ _)))   = side sd
  enter (Ωₗ μ) (inj₂ (c′ , inj₂ _)) (inch (inj₂ (c , inj₁ _)) (pos (inj₂ _)))   = side sd
  enter (Ωₗ μ) (inj₂ (c′ , inj₂ _)) (inch (inj₂ (c , inj₂ _)) (pos (inj₂ _)))   = side sd
  enter ℓ a (inch _ _) = unk
  enter ℓ a (side _)   = unk
  enter ℓ a (abv E)    = abv (E ∘ᴱ chE ℓ a)
  enter ℓ a unk        = unk

  enterP : ∀ ℓ (a : Ch ℓ) (p : Pos ℓ) → Tg (chAt ℓ a) (at ℓ p)
  enterP z () p
  enterP (μ ⊞ c) (inj₁ a) (inj₁ (inj₂ q))  = enterP μ a q
  enterP (μ ⊞ c) (inj₁ a) (inj₁ (inj₁ _))  = abv (chE μ a)
  enterP (μ ⊞ c) (inj₁ a) (inj₂ ip)        = abv (e⊞ μ (sub μ c ip) ∘ᴱ chE μ a)
  enterP (μ ⊞ c) (inj₂ ia) (inj₁ b)        = pos (inj₁ b)
  enterP (μ ⊞ c) (inj₂ ia) (inj₂ _)        = unk
  enterP (l f) (n , a) (m , b)             = enterN f n m a b (n ≟ m)
  enterP (Ωₗ μ) (inj₁ a) (inj₁ (inj₂ q))   = enterP μ a q
  enterP (Ωₗ μ) (inj₁ a) (inj₁ (inj₁ _))   = abv (chE μ a)
  enterP (Ωₗ μ) (inj₁ a) (inj₂ (c , inj₁ _))  = abv (e⊞ μ c ∘ᴱ chE μ a)
  enterP (Ωₗ μ) (inj₁ a) (inj₂ (c , inj₂ ip)) = abv (e⊞ μ (sub μ c ip) ∘ᴱ chE μ a)
  enterP (Ωₗ μ) (inj₂ (c , inj₁ _)) (inj₁ b)  = pos (inj₁ b)
  enterP (Ωₗ μ) (inj₂ (c , inj₂ ia)) (inj₁ b) = pos (inj₁ b)
  enterP (Ωₗ μ) (inj₂ _) (inj₂ _)          = unk

  enterN : ∀ (f : ℕ → Lv) n m (a : Ch (f n)) (b : Pos⁺ (f m)) → Dec (n ≡ m) →
           Tg (chAt (f n) a) (at⁺ (f m) b)
  enterN f n .n a (inj₂ q) (yes refl) = enterP (f n) a q
  enterN f n .n a (inj₁ _) (yes refl) = abv (chE (f n) a)
  enterN f n m a b (no _) = unk
```

`up ℓ a T`: 孩子 a 里的目标退回 ℓ 的坐标. 目标位置在孩子的基底部分时它就是 ℓ 的位置 (字面地), 否则记作 `inch a`. 只看目标位置的构造子, 不比较孩子.

```agda
liftB : ∀ {μ A} → Tg μ A → Tg (Ωₗ μ) A
liftB (pos q)    = pos (inj₁ (inj₂ q))
liftB (inch a T) = inch (inj₁ a) T
liftB _          = unk

lift⊞ : ∀ {μ c A} → Tg μ A → Tg (μ ⊞ c) A
lift⊞ (pos q)    = pos (inj₁ (inj₂ q))
lift⊞ (inch a T) = inch (inj₁ a) T
lift⊞ _          = unk

liftN : ∀ {f : ℕ → Lv} {n A} → Tg (f n) A → Tg (l f) A
liftN {n = n} (pos q)    = pos (n , inj₂ q)
liftN {n = n} (inch a T) = inch (n , a) T
liftN _                  = unk

upP : ∀ ℓ (a : Ch ℓ) (p : Pos (chAt ℓ a)) → Tg ℓ (at (chAt ℓ a) p)
upP z () p
upP (μ ⊞ c) (inj₁ a) p                    = lift⊞ (upP μ a p)
upP (μ ⊞ c) (inj₂ ia) (inj₁ b)            = pos (inj₁ b)
upP (μ ⊞ c) (inj₂ ia) (inj₂ ip)           = inch (inj₂ ia) (pos (inj₂ ip))
upP (l f) (n , a) p                       = liftN (upP (f n) a p)
upP (Ωₗ μ) (inj₁ a) p                     = liftB (upP μ a p)
upP (Ωₗ μ) (inj₂ (c , inj₁ _)) (inj₁ b)   = pos (inj₁ b)
upP (Ωₗ μ) (inj₂ (c , inj₁ t)) (inj₂ ip)  = inch (inj₂ (c , inj₁ t)) (pos (inj₂ ip))
upP (Ωₗ μ) (inj₂ (c , inj₂ ia)) (inj₁ b)  = pos (inj₁ b)
upP (Ωₗ μ) (inj₂ (c , inj₂ ia)) (inj₂ ip) = inch (inj₂ (c , inj₂ ia)) (pos (inj₂ ip))

up : ∀ ℓ (a : Ch ℓ) {A} → Tg (chAt ℓ a) A → Tg ℓ A
up ℓ a (pos p) = upP ℓ a p
up ℓ a T       = inch a T
```

## 折叠

零: 底按当时的目标折出; 后继: ψ(a)·ω; ℕ 极限逐项; Ω 极限: `cmpT` 给 `below` 时保留为目标层的 Ω 极限, 否则沿分支位置 r 对角化, 链从 0 起, 第 n+1 项把 "底 + g (第 n 项)" 整个折到 r. 走进 `ex v a u`: 目标经 `enter` 搬进孩子 a, 底换成 "把 v 折到孩子 a 里的目标" (`up ℓ a`), 再折 u. `ψx` 只沿地址展开孩子层的树类型, 不改值.

```agda
itc : ∀ {X : Set} → (X → X) → X → ℕ → X
itc g x zero    = x
itc g x (suc n) = g (itc g x n)

ψΩ : ∀ {A : Lv} {T : Set} → Cmp A T → (T → Tr A) → (T → T) → T → Tr A
ψΩ (below q* cv) F G t₀ = Ω q* (λ e → F (cv e))
ψΩ other         F G t₀ = lim (λ n → F (itc G t₀ n))

Bot : Lv → Set
Bot ℓ = ∀ {B} → Tg ℓ B → Tr B

mutual
  ψc : ∀ ℓ {A} → Tg ℓ A → Bot ℓ → Tr ℓ → Tr A
  ψc ℓ T bot zero       = bot T
  ψc ℓ T bot (suc v)    = lim (λ n → itc (λ y → y + ψc ℓ T bot v) (ψc ℓ T bot v) n)
  ψc ℓ T bot (lim g)    = lim (λ n → ψc ℓ T bot (g n))
  ψc ℓ T bot (Ω r g)    = ψΩ (cmpT ℓ T r) (λ e → ψc ℓ T bot (g e))
                             (λ e → into ℓ r (ψc ℓ (pos r) bot (g e))) (into ℓ r zero)
  ψc ℓ T bot (ex v a u) = ψx ℓ a (enter ℓ a T) (λ T″ → ψc ℓ (up ℓ a T″) bot v) u

  ψx : ∀ ℓ (a : Ch ℓ) {A} → Tg (chAt ℓ a) A → Bot (chAt ℓ a) → TrCh ℓ a → Tr A
  ψx z ()
  ψx (μ ⊞ c) (inj₁ a)              T bot y = ψx μ a T bot y
  ψx (μ ⊞ c) (inj₂ ia)             T bot y = ψxI μ c ia T bot y
  ψx (l f) (n , a)                 T bot y = ψx (f n) a T bot y
  ψx (Ωₗ μ) (inj₁ a)               T bot y = ψx μ a T bot y
  ψx (Ωₗ μ) (inj₂ (c , inj₁ _))    T bot y = ψc (μ ⊞ c) T bot y
  ψx (Ωₗ μ) (inj₂ (c , inj₂ ia))   T bot y = ψxI μ c ia T bot y

  ψxI : ∀ μ c (ia : ChI μ c) {A} → Tg (μ ⊞ subC μ c ia) A → Bot (μ ⊞ subC μ c ia) → TrChI μ c ia → Tr A
  ψxI μ (suc c) ia              T bot y = ψxI μ c ia T bot y
  ψxI μ (lim f) (n , ia)        T bot y = ψxI μ (f n) ia T bot y
  ψxI μ (Ω q f) (e , inj₁ _)    T bot y = ψc (μ ⊞ f e) T bot y
  ψxI μ (Ω q f) (e , inj₂ ia)   T bot y = ψxI μ (f e) ia T bot y
  ψxI μ (ex x a′ w) ia          T bot y = ψxI μ x ia T bot y

ψ : ∀ ℓ {A} → Tg ℓ A → Tr ℓ → Tr A
ψ ℓ T w = ψc ℓ T (λ {B} _ → top B) w
```

## 闭项

Λ 的第 0 个位置是层 z. `ψΛ` 读作 ψ₀(Λ). 判据的最小见证: 左边是塔第 1 项那一层的 Ω 树 `ΩΩ` (读作 Ω_Ω), 经 `ex` 接上孩子层 z ⊞ 1 (读作层 2) 的 Ω 树 `Ω₂` (读作 Ω₂).

```agda
ψΛ : Tr z
ψΛ = ψ Λ (pos (0 , inj₁ tt)) (top Λ)

ΩΩ : Tr (Ωₗ z)
ΩΩ = top (Ωₗ z)

Ω₂ : Tr (z ⊞ suc zero)
Ω₂ = topP z (suc zero)

argB : Tr (Ωₗ z)
argB = ex ΩΩ (inj₂ (suc zero , inj₁ tt)) Ω₂

tB′ : Tr z
tB′ = ψ (Ωₗ z) (pos (inj₁ (inj₁ tt))) argB
```
