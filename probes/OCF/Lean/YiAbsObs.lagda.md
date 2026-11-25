# 抽象理论 (一): 观察原则与 "行" 的充要条件

> 判决: 编译定理, 无前提, 不导入仓库模块. 折叠是全函数, 输出的头部可判定; 一条律若使头部观察与命题 P 等价, 就判定 P (`obs→dec`, `obs→wdec`, 逆向 `dec→obs`, `wdec→obs`).
> 两种 P: (E) 孩子下标的字面相等: 指定孩子的交接加可观察的回退, 当且仅当探针处弱判等 (`sep→wdec`, `wdec→sep`); 有自反的同支证据函数就能写出这一行 (`rowE-same`, `rowE-off`), 经证据函数派发则判等 (`viaE→dec`). (S) 层号上的存在命题: "能保留处都保留" 判定它 (`full→dec`, `sig→lpo`).
> 不否定什么: 对一切孩子一致给出的目标不需要比较 (`rowU`); ⊤ 与 ℕ 上有证据函数 (`Eq⊤`, `Eqℕ`). 框架在 `YiAbsFrame`, 实填在 `YiAbsInst`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAbsObs where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
```

## 1 观察原则

```agda
Dec′ WDec : Set → Set
Dec′ A = A ⊎ (A → ⊥)
WDec A = (A → ⊥) ⊎ ((A → ⊥) → ⊥)

t≢f : true ≡ false → ⊥
t≢f ()

obs→dec : {P : Set} (b : Bool) → (P → b ≡ true) → (b ≡ true → P) → Dec′ P
obs→dec true  c s = inj₁ (s refl)
obs→dec false c s = inj₂ (λ p → t≢f (sym (c p)))

obs→wdec : {P : Set} (b : Bool) → (P → b ≡ true) → ((P → ⊥) → b ≡ false) → WDec P
obs→wdec true  c o = inj₂ (λ np → t≢f (o np))
obs→wdec false c o = inj₁ (λ p → t≢f (sym (c p)))

dec→obs : {P : Set} → Dec′ P → Σ Bool λ b → (P → b ≡ true) × (b ≡ true → P)
dec→obs (inj₁ p)  = true , (λ _ → refl) , (λ _ → p)
dec→obs (inj₂ np) = false , (λ p → ⊥-elim (np p)) , (λ ())

wdec→obs : {P : Set} → WDec P → Σ Bool λ b → (P → b ≡ true) × ((P → ⊥) → b ≡ false)
wdec→obs (inj₁ np)  = false , (λ p → ⊥-elim (np p)) , (λ _ → refl)
wdec→obs (inj₂ nnp) = true , (λ _ → refl) , (λ np → ⊥-elim (nnp np))
```

## 2 (E) 字面相等: 分离与弱判等互推

`Sep c₀`: 一个布尔观察在 c₀ 为真, 在字面不等于 c₀ 处为假.

```agda
record Sep {C : Set} (c₀ : C) : Set where
  field
    f   : C → Bool
    on  : f c₀ ≡ true
    off : ∀ c′ → (c₀ ≡ c′ → ⊥) → f c′ ≡ false

sep→wdec : ∀ {C} {c₀ : C} → Sep c₀ → ∀ c′ → WDec (c₀ ≡ c′)
sep→wdec S c′ = obs→wdec (f c′) (λ e → subst (λ c → f c ≡ true) e on) (off c′)
  where open Sep S

wdec→sep : ∀ {C} {c₀ : C} → (∀ c′ → WDec (c₀ ≡ c′)) → Sep c₀
wdec→sep {c₀ = c₀} W = record
  { f   = λ c′ → proj₁ (wdec→obs (W c′))
  ; on  = proj₁ (proj₂ (wdec→obs (W c₀))) refl
  ; off = λ c′ → proj₂ (proj₂ (wdec→obs (W c′))) }
```

同支证据是下标上的函数时, 对角上给出证据就判等 (`YiCtxNeg.diag1→dec` 的陈述, 去掉块).

```agda
IsJust : ∀ {A : Set} → Maybe A → Set
IsJust (just _) = ⊤
IsJust nothing  = ⊥

diag→dec : ∀ {C : Set} {c₀ : C} (E : ∀ c′ → Maybe (c₀ ≡ c′)) → IsJust (E c₀) → ∀ c′ → Dec′ (c₀ ≡ c′)
diag→dec {c₀ = c₀} E j c′ = go (E c′) refl
  where
  back : ∀ {y} → c₀ ≡ y → E y ≡ nothing → ⊥
  back refl h = subst IsJust h j
  go : (u : Maybe (c₀ ≡ c′)) → E c′ ≡ u → Dec′ (c₀ ≡ c′)
  go (just e) h = inj₁ e
  go nothing  h = inj₂ (λ e → back e h)

dec→diag : ∀ {C : Set} {c₀ : C} → (∀ c′ → Dec′ (c₀ ≡ c′)) → Σ (∀ c′ → Maybe (c₀ ≡ c′)) λ E → IsJust (E c₀)
dec→diag {c₀ = c₀} D = E , ok (D c₀) refl
  where
  m : ∀ {c′} → Dec′ (c₀ ≡ c′) → Maybe (c₀ ≡ c′)
  m (inj₁ e) = just e
  m (inj₂ _) = nothing
  E : ∀ c′ → Maybe (c₀ ≡ c′)
  E c′ = m (D c′)
  ok : (d : Dec′ (c₀ ≡ c₀)) → D c₀ ≡ d → IsJust (E c₀)
  ok (inj₁ e)  q = subst (λ d → IsJust (m d)) (sym q) tt
  ok (inj₂ ne) q = ⊥-elim (ne refl)
```

## 3 一行的抽象: 目标在孩子 c′, 嵌入在孩子 c

`H c` 是落在孩子 c 里的目标 (路径), `Y c` 是孩子层的树, `X` 是输出. `k` 交给孩子, `fb` 回退.

```agda
record Row : Set₁ where
  field
    C  : Set
    H  : C → Set
    Y  : C → Set
    X  : Set
    hd : X → Bool
    k  : (c : C) → H c → Y c → X
    fb : (c′ : C) → H c′ → (c : C) → Y c → X

module RowLaws (R : Row) where
  open Row R

  Disp : Set
  Disp = (c′ : C) → H c′ → (c : C) → Y c → X

  Same Off : Disp → Set
  Same r = ∀ c w y → r c w c y ≡ k c w y
  Off  r = ∀ c′ w c y → (c ≡ c′ → ⊥) → r c′ w c y ≡ fb c′ w c y
```

探针: 一个孩子 c₀, 对每个孩子各一条目标路径, c₀ 层的一棵树; 交给孩子时头部为真, 回退时头部为假.

```agda
  record Probe : Set where
    field
      c₀     : C
      w      : ∀ c′ → H c′
      y      : Y c₀
      k-on   : hd (k c₀ (w c₀) y) ≡ true
      fb-off : ∀ c′ → hd (fb c′ (w c′) c₀ y) ≡ false

  row→sep : (r : Disp) → Same r → Off r → (P : Probe) → Sep (Probe.c₀ P)
  row→sep r S O P = record
    { f   = λ c′ → hd (r c′ (w c′) c₀ y)
    ; on  = trans (cong hd (S c₀ (w c₀) y)) k-on
    ; off = λ c′ ne → trans (cong hd (O c′ (w c′) c₀ y ne)) (fb-off c′) }
    where open Probe P

  row→wdec : (r : Disp) → Same r → Off r → (P : Probe) → ∀ c′ → WDec (Probe.c₀ P ≡ c′)
  row→wdec r S O P = sep→wdec (row→sep r S O P)
```

充分的一侧: 有自反的同支证据函数, 这一行就写得出, 两条律都成立.

```agda
  hand : ∀ {c c′} → c ≡ c′ → H c′ → H c
  hand refl w = w

  record Eq : Set where
    field
      E      : (c c′ : C) → Maybe (c ≡ c′)
      E-refl : ∀ c → E c c ≡ just refl

  rowE : Eq → Disp
  rowE Q c′ w c y = maybe′ (λ e → k c (hand e w) y) (fb c′ w c y) (Eq.E Q c c′)

  rowE-same : (Q : Eq) → Same (rowE Q)
  rowE-same Q c w y = cong (maybe′ (λ e → k c (hand e w) y) (fb c w c y)) (Eq.E-refl Q c)

  rowE-off : (Q : Eq) → Off (rowE Q)
  rowE-off Q c′ w c y ne = go (Eq.E Q c c′)
    where
    go : (m : Maybe (c ≡ c′)) → maybe′ (λ e → k c (hand e w) y) (fb c′ w c y) m ≡ fb c′ w c y
    go (just e) = ⊥-elim (ne e)
    go nothing  = refl

  eq→dec : Eq → ∀ c c′ → Dec′ (c ≡ c′)
  eq→dec Q c = diag→dec (Eq.E Q c) (subst IsJust (sym (Eq.E-refl Q c)) tt)
```

经证据函数派发的一行 (`ViaE`), 对角上交给孩子, 就在探针处判等.

```agda
  ViaE : Disp → Set
  ViaE r = Σ ((c c′ : C) → Maybe (c ≡ c′)) λ E →
    ∀ c′ w c y → r c′ w c y ≡ maybe′ (λ e → k c (hand e w) y) (fb c′ w c y) (E c c′)

  viaE→dec : (r : Disp) → Same r → ViaE r → (P : Probe) → ∀ c′ → Dec′ (Probe.c₀ P ≡ c′)
  viaE→dec r S (E , V) P = diag→dec (E c₀) (go (E c₀ c₀) refl)
    where
    open Probe P
    go : (m : Maybe (c₀ ≡ c₀)) → E c₀ c₀ ≡ m → IsJust (E c₀ c₀)
    go (just e) q = subst IsJust (sym q) tt
    go nothing  q = ⊥-elim (t≢f (trans (sym k-on) (trans (cong hd (trans (sym (S c₀ (w c₀) y))
      (trans (V c₀ (w c₀) c₀ y) (cong (maybe′ (λ e → k c₀ (hand e (w c₀)) y) (fb c₀ (w c₀) c₀ y)) q))))
      (fb-off c₀))))
```

一致的目标: 对每个孩子各给一条路径, 嵌入在哪个孩子就用哪一条. 不比较孩子.

```agda
  rowU : ((c : C) → H c) → (c : C) → Y c → X
  rowU ws c y = k c (ws c) y
```

⊤ 与 ℕ 上的证据函数 (后继层号与 ℕ 极限层号的孩子下标).

```agda
Eq⊤ : (H Y : ⊤ → Set) (X : Set) (hd : X → Bool) (k : ∀ c → H c → Y c → X) (fb : ∀ c′ → H c′ → ∀ c → Y c → X)
  → RowLaws.Eq (record { C = ⊤ ; H = H ; Y = Y ; X = X ; hd = hd ; k = k ; fb = fb })
Eq⊤ H Y X hd k fb = record { E = λ _ _ → just refl ; E-refl = λ _ → refl }

eqN : (m n : ℕ) → Maybe (m ≡ n)
eqN zero    zero    = just refl
eqN zero    (suc n) = nothing
eqN (suc m) zero    = nothing
eqN (suc m) (suc n) = sc (eqN m n)
  where
  sc : Maybe (m ≡ n) → Maybe (suc m ≡ suc n)
  sc (just refl) = just refl
  sc nothing     = nothing

eqN-refl : ∀ n → eqN n n ≡ just refl
eqN-refl zero    = refl
eqN-refl (suc n) rewrite eqN-refl n = refl

Eqℕ : (H Y : ℕ → Set) (X : Set) (hd : X → Bool) (k : ∀ c → H c → Y c → X) (fb : ∀ c′ → H c′ → ∀ c → Y c → X)
  → RowLaws.Eq (record { C = ℕ ; H = H ; Y = Y ; X = X ; hd = hd ; k = k ; fb = fb })
Eqℕ H Y X hd k fb = record { E = eqN ; E-refl = eqN-refl }
```

## 4 全知原理与康托探针

```agda
Found AllF : (ℕ → Bool) → Set
Found α = Σ ℕ λ n → α n ≡ true
AllF α = ∀ n → α n ≡ false

LPO WLPO : Set
LPO  = (α : ℕ → Bool) → Found α ⊎ (Found α → ⊥)
WLPO = (α : ℕ → Bool) → AllF α ⊎ (AllF α → ⊥)

stab : ∀ α → ((AllF α → ⊥) → ⊥) → AllF α
stab α nn n = go (α n) refl
  where
  go : (b : Bool) → α n ≡ b → α n ≡ false
  go true  q = ⊥-elim (nn (λ af → t≢f (trans (sym q) (af n))))
  go false q = q

lpo→wlpo : LPO → WLPO
lpo→wlpo lpo α with lpo α
... | inj₁ (n , e) = inj₂ (λ af → t≢f (trans (sym e) (af n)))
... | inj₂ nf      = inj₁ (λ n → go n (α n) refl)
  where
  go : ∀ n (b : Bool) → α n ≡ b → α n ≡ false
  go n true  q = ⊥-elim (nf (n , q))
  go n false q = q
```

康托探针: 下标类型里一族 `cα α`, 与 c₀ 字面相等就推出 α 处处为假. 反方向 (`back`) 在含函数的树上要函数外延.

```agda
record Cantor {C : Set} (c₀ : C) : Set where
  field
    cα      : (ℕ → Bool) → C
    eq→allF : ∀ α → c₀ ≡ cα α → AllF α

sep→wdecα : ∀ {C} {c₀ : C} → Sep c₀ → (K : Cantor c₀) → ∀ α → AllF α ⊎ (c₀ ≡ Cantor.cα K α → ⊥)
sep→wdecα S K α with sep→wdec S (Cantor.cα K α)
... | inj₁ ne  = inj₂ ne
... | inj₂ nne = inj₁ (stab α (λ naf → nne (λ e → naf (Cantor.eq→allF K α e))))

sep→wlpo : ∀ {C} {c₀ : C} → Sep c₀ → (K : Cantor c₀) → (∀ α → AllF α → c₀ ≡ Cantor.cα K α) → WLPO
sep→wlpo S K back α with sep→wdecα S K α
... | inj₁ af = inj₁ af
... | inj₂ ne = inj₂ (λ af → ne (back α af))
```

## 5 (S) 存在命题: "能保留处都保留"

目标的槽位 `Q`, 槽位的层号 `lv`, 源结点槽位的层号 `m`, 输出 o 的根槽位 `root o`. `Full`: 目标里有层号 m 的槽位, 输出就以这样一个槽位为根.
`tst` 是层号上认出 m 的布尔测试. 结论: 判定任何夹在 "测试认出的根" 与 "有同层号槽位" 之间的命题 P.

```agda
module Slot {Q M X : Set} (lv : Q → M) (m : M) (root : X → Maybe Q) where

  Has : Set
  Has = Σ Q λ q → lv q ≡ m

  Full : X → Set
  Full o = Has → Σ Q λ q → (root o ≡ just q) × (lv q ≡ m)

  full→dec : {P : Set} (tst : M → Bool) → tst m ≡ true → (o : X) → Full o
    → (P → Has) → (∀ q → tst (lv q) ≡ true → P) → Dec′ P
  full→dec {P} tst tm o F ph hp = obs→dec (ob (root o)) cpl (snd (root o))
    where
    ob : Maybe Q → Bool
    ob (just q) = tst (lv q)
    ob nothing  = false
    cpl : P → ob (root o) ≡ true
    cpl p with F (ph p)
    ... | q , e , l = trans (cong ob e) (trans (cong tst l) tm)
    snd : (r : Maybe Q) → ob r ≡ true → P
    snd (just q) e = hp q e
    snd nothing  ()

sig→lpo : (o : (ℕ → Bool) → Bool) → (∀ α → Found α → o α ≡ true) → (∀ α → o α ≡ true → Found α) → LPO
sig→lpo o c s α = obs→dec (o α) (c α) (s α)
```
