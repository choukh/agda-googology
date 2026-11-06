# NegRaise (二): 下界可判定相等时 $R$ 可以构造; 对 $\omega$ 判定相等是 WLPO

> 不含记号. 入口 [NegRaise](NegRaise.lagda.md). 导入接口 [RaiseIf](RaiseIf.lagda.md), 不改它. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示; 函数外延 `FEA` (只对 $\mathbb N\to$ `A`) 只在条件定理 `deqω→WLPO` 里作前提, 标 "条件".
>
> 否定一路要划边界, 先看哪里**能**构造. 本篇的定理:
>
> 1. **`deq→at` (构造, 无条件).** 固定合法的 $a$. 若 "一棵树是否等于 $a$" 可判定 (`DecAt a`), 则对这个 $a$ 有升界算子 `RaiseAt a` (对一切合法 $v$ 的 `R-lo`, `R-hi`, `R-lg`). 构造: 对 $v$ 的一切有限路径做对角搜索 (第 $n$ 步查深度与下标都不超过 $n$ 的路径, 看那里的子树是否等于 $a$); $R_a\,v = \lim_n m_n$, 搜到之前 $m_n=a$, 搜到之后 $m_n=v$. 常值段 $a,a,\dots$ 合法, 搜到时有字面证据 $a\lhd v$, 所以跳到 $v$ 合法. 不判定 $a\lhd v$, 只**半判定**它.
> 2. **`raiseFin` (构造).** 有限数 $a=$ `nat k` 的相等可判定 (`nat-deq`), 所以对有限数的 $a$ 有 `RaiseAt`.
> 3. **`deq→raise` (条件: `A` 上的相等可判定).** 若对一切 $a$ 都可判定相等, 就有完整的 `RaiseA`. 这比构造一路的 `dec→Raise` (前提: 子项关系可判定, 推出 LPO) 要的少: 只要判定相等.
> 4. **`deqω-sep` (定理), `deqω→WLPO` (条件 `FEA`).** 对 $\omega=$ `alim nat` 判定 "合法的树是否等于 $\omega$" 推出分离子, 有外延时推出 WLPO. 所以第 1 条的构造到 $\omega$ 就停: 下界是 ℕ-极限时, "等于 $a$" 是 $\Pi$ 型, 搜索不终止.
>
> 5. **`wlpo→deq`, `wlpo→raise` (条件: `FEA` 与 WLPO).** 反方向: WLPO 加外延推出 `A` 上处处可判定相等, 从而推出 `RaiseA`. 合起来 (条件 `FEA`): `DecLgAt ω` ⇔ WLPO ⇔ 处处可判定相等, 都推出 `RaiseA`. 所以 `RaiseA` 的经典实例只要 WLPO 这一档 (加外延), 不要 LPO (构造一路 `dec→Raise` 的前提是 LPO 档). 否定一路能指望的最强结论是 `RaiseA → WLPO` 一类, 不是 `RaiseA → LPO` (判断, 见 §5 读法).
>
> **只说什么.** 第 4 条否定的是 "用判定相等来构造 $R$" 这一种做法 (在 $a=\omega$ 处), **不**否定 `RaiseAt ω` 或 `RaiseA` 本身; 那两个我既没有构造出来也没有否定 (未走通, 见入口).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegRaiseFin where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.ColimWNeg using (WLPO)
open import OCF.Align.RaiseIf using (RaiseA)
```

## §0 布尔小工具

```agda
∨-l : ∀ {b c} → b ≡ true → b ∨ c ≡ true
∨-l refl = refl

∨-r : ∀ b {c} → c ≡ true → b ∨ c ≡ true
∨-r false e = e
∨-r true e = refl

∨-e : ∀ b {c} → b ∨ c ≡ true → (b ≡ true) ⊎ (c ≡ true)
∨-e true _ = inj₁ refl
∨-e false e = inj₂ e

any : ℕ → (ℕ → Bool) → Bool
any zero g = g zero
any (suc n) g = any n g ∨ g (suc n)

any-e : ∀ n g → any n g ≡ true → Σ ℕ (λ i → g i ≡ true)
any-e zero g e = zero , e
any-e (suc n) g e with ∨-e (any n g) e
... | inj₁ e′ = any-e n g e′
... | inj₂ e′ = suc n , e′

any-last : ∀ i g → g i ≡ true → any i g ≡ true
any-last zero g e = e
any-last (suc i) g e = ∨-r (any i g) e

any-i : ∀ k i g → g i ≡ true → any (k + i) g ≡ true
any-i zero i g e = any-last i g e
any-i (suc k) i g e = ∨-l (any-i k i g e)
```

## §1 只对一个 $a$ 的升界算子

```agda
record RaiseAt (a : A) : Set where
  field
    Rₐ    : A → A
    Rₐ-lo : ∀ {v} → Lg v → a ⊲ Rₐ v
    Rₐ-hi : ∀ {v} → Lg v → a ⊲ v → v ⊲ Rₐ v
    Rₐ-lg : ∀ {v} → Lg v → Lg (Rₐ v)
open RaiseAt public

raise→at : RaiseA → ∀ {a} → Lg a → RaiseAt a
raise→at ρ la = record
  { Rₐ = RaiseA.R ρ _
  ; Rₐ-lo = λ lv → RaiseA.R-lo ρ la lv
  ; Rₐ-hi = λ lv p → RaiseA.R-hi ρ la lv p
  ; Rₐ-lg = λ lv → RaiseA.R-lg ρ la lv }

DecAt : A → Set
DecAt a = ∀ t → Dec (t ≡ a)
```

## §2 对角搜索

`F n t`: 在 $t$ 里查深度与下标都不超过 $n$ 的路径. 对 $n$ 单调是写进定义的 (`F (suc n) t = F n t ∨ …`).

```agda
module Search (a : A) (deq : DecAt a) where
  eqb : A → Bool
  eqb t with deq t
  ... | yes _ = true
  ... | no _ = false

  eqb-sound : ∀ t → eqb t ≡ true → t ≡ a
  eqb-sound t e with deq t
  ... | yes p = p
  eqb-sound t () | no _

  eqb-refl : eqb a ≡ true
  eqb-refl with deq a
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p refl)

  F : ℕ → A → Bool
  D : ℕ → A → Bool
  F zero t = eqb t
  F (suc n) t = F n t ∨ D n t
  D n azero = false
  D n (asuc b) = F n b
  D n (alim f) = any n (λ i → F n (f i))

  F-sound : ∀ n t → F n t ≡ true → a ⊲ t
  D-sound : ∀ n t → D n t ≡ true → a ⊲ t
  F-sound zero t e = subst (a ⊲_) (sym (eqb-sound t e)) C.self
  F-sound (suc n) t e with ∨-e (F n t) e
  ... | inj₁ e′ = F-sound n t e′
  ... | inj₂ e′ = D-sound n t e′
  D-sound n azero ()
  D-sound n (asuc b) e = C.suc (F-sound n b e)
  D-sound n (alim f) e with any-e n (λ i → F n (f i)) e
  ... | i , e′ = C.lim i (F-sound n (f i) e′)

  F-mono : ∀ k n t → F n t ≡ true → F (k + n) t ≡ true
  F-mono zero n t e = e
  F-mono (suc k) n t e = ∨-l (F-mono k n t e)

  F-comp : ∀ {t} → a ⊲ t → Σ ℕ (λ n → F n t ≡ true)
  F-comp C.self = zero , eqb-refl
  F-comp (C.suc {b = b} p) with F-comp p
  ... | n , e = suc n , ∨-r (F n (asuc b)) e
  F-comp (C.lim {f = f} i p) with F-comp p
  ... | n , e = suc (n + i) , ∨-r (F (n + i) (alim f)) (any-i n i (λ j → F (n + i) (f j)) e′)
    where
    e′ : F (n + i) (f i) ≡ true
    e′ = subst (λ m → F m (f i) ≡ true) (+-comm i n) (F-mono i n (f i) e)
```

**升界.** $m_n$ = 搜到之前 $a$, 搜到之后 $v$.

```agda
  module _ (v : A) where
    sel : Bool → A
    sel true = v
    sel false = a

    m : ℕ → A
    m n = sel (F n v)

  step-sel : ∀ v b b′ → (b ≡ true → b′ ≡ true) → (b′ ≡ true → a ⊲ v) → sel v b ⊲ sel v b′
  step-sel v false false _ _ = C.self
  step-sel v false true _ h = h refl
  step-sel v true true _ _ = C.self
  step-sel v true false h _ with h refl
  ... | ()

  lg-sel : ∀ {v} → Lg a → Lg v → ∀ b → Lg (sel v b)
  lg-sel la lv true = lv
  lg-sel la lv false = la

  lo-sel : ∀ v b → (b ≡ true → a ⊲ v) → a ⊲ sel v b
  lo-sel v true h = h refl
  lo-sel v false _ = C.self

  Rs : A → A
  Rs v = alim (m v)

  Rs-lg : Lg a → ∀ {v} → Lg v → Lg (Rs v)
  Rs-lg la {v} lv =
    (λ n → step-sel v (F n v) (F (suc n) v) ∨-l (F-sound (suc n) v)) , (λ n → lg-sel la lv (F n v))

  Rs-lo : ∀ v → a ⊲ Rs v
  Rs-lo v = C.lim 0 (lo-sel v (F 0 v) (F-sound 0 v))

  Rs-hi : ∀ {v} → a ⊲ v → v ⊲ Rs v
  Rs-hi {v} p with F-comp p
  ... | n , e = C.lim n (subst (λ b → v ⊲ sel v b) (sym e) C.self)

deq→at : ∀ {a} → Lg a → DecAt a → RaiseAt a
deq→at {a} la deq = record
  { Rₐ = Rs ; Rₐ-lo = λ {v} _ → Rs-lo v ; Rₐ-hi = λ _ p → Rs-hi p ; Rₐ-lg = Rs-lg la }
  where open Search a deq

-- A 上的相等处处可判定时, 有完整的 RaiseA (条件)
deq→raise : (∀ a → DecAt a) → RaiseA
deq→raise deq = record
  { R = λ a → Search.Rs a (deq a)
  ; R-lo = λ {a} {v} _ _ → Search.Rs-lo a (deq a) v
  ; R-hi = λ {a} _ _ p → Search.Rs-hi a (deq a) p
  ; R-lg = λ {a} la lv → Search.Rs-lg a (deq a) la lv }
```

## §3 有限数的 $a$

```agda
nat : ℕ → A
nat zero = azero
nat (suc k) = asuc (nat k)

lg-nat : ∀ k → Lg (nat k)
lg-nat zero = tt
lg-nat (suc k) = lg-nat k

unsuc : A → A
unsuc (asuc x) = x
unsuc x = x

nat-deq : ∀ k → DecAt (nat k)
nat-deq zero azero = yes refl
nat-deq zero (asuc t) = no (λ ())
nat-deq zero (alim f) = no (λ ())
nat-deq (suc k) azero = no (λ ())
nat-deq (suc k) (alim f) = no (λ ())
nat-deq (suc k) (asuc t) with nat-deq k t
... | yes e = yes (cong asuc e)
... | no ne = no (λ e → ne (cong unsuc e))

raiseFin : ∀ k → RaiseAt (nat k)
raiseFin k = deq→at (lg-nat k) (nat-deq k)
```

**一个具体的检查 (定理, `refl`/小证明).** $a=1$, $v=\omega$: $R_1\,\omega$ 的第 $0$ 项还是 $1$ ($\omega$ 的根不是 $1$), 第 $2$ 项已经是 $\omega$ (查到深度 $1$, 下标 $1$ 的路径 `lim 1 self`).

```agda
ω : A
ω = alim nat

ex-m0 : Search.m (nat 1) (nat-deq 1) ω 0 ≡ nat 1
ex-m0 = refl

ex-m2 : Search.m (nat 1) (nat-deq 1) ω 2 ≡ ω
ex-m2 = refl
```

## §4 对 $\omega$ 判定相等是 WLPO

`tω α`: 第 $n$ 项在 $\alpha$ 的前 $n+1$ 位里见过 `true` 之前是 $n$, 之后是 $n+1$. 合法. 它等于 $\omega$ 推出 $\alpha$ 恒假 (无条件); $\alpha$ 恒假推出它等于 $\omega$ 要外延.

```agda
seen : (ℕ → Bool) → ℕ → Bool
seen α zero = α zero
seen α (suc n) = seen α n ∨ α (suc n)

seen-mono : ∀ α n → seen α n ≡ true → seen α (suc n) ≡ true
seen-mono α n = ∨-l

seen-intro : ∀ α n → α n ≡ true → seen α n ≡ true
seen-intro α zero e = e
seen-intro α (suc n) e = ∨-r (seen α n) e

seen-false : ∀ α → (∀ n → α n ≡ false) → ∀ n → seen α n ≡ false
seen-false α h zero = h zero
seen-false α h (suc n) rewrite seen-false α h n = h (suc n)

selN : Bool → ℕ → A
selN true n = nat (suc n)
selN false n = nat n

tω : (ℕ → Bool) → A
tω α = alim (λ n → selN (seen α n) n)

stepN : ∀ n b b′ → (b ≡ true → b′ ≡ true) → selN b n ⊲ selN b′ (suc n)
stepN n false false _ = C.suc C.self
stepN n false true _ = C.suc (C.suc C.self)
stepN n true true _ = C.suc C.self
stepN n true false h with h refl
... | ()

lgN : ∀ b n → Lg (selN b n)
lgN true n = lg-nat (suc n)
lgN false n = lg-nat n

Lg-tω : ∀ α → Lg (tω α)
Lg-tω α = (λ n → stepN n (seen α n) (seen α (suc n)) (seen-mono α n)) , (λ n → lgN (seen α n) n)

nat-sn : ∀ n → ¬ (nat (suc n) ≡ nat n)
nat-sn zero ()
nat-sn (suc n) e = nat-sn n (cong unsuc e)

atA : ℕ → A → A
atA n (alim g) = g n
atA n x = x

sel-true : ∀ b n → b ≡ true → ¬ (selN b n ≡ nat n)
sel-true true n refl e = nat-sn n e

eq→F : ∀ α → tω α ≡ ω → ∀ n → α n ≡ false
eq→F α e n with α n in eqn
... | false = refl
... | true = ⊥-elim (sel-true (seen α n) n (seen-intro α n eqn) (cong (atA n) e))

FEA : Set
FEA = ∀ (f g : ℕ → A) → (∀ n → f n ≡ g n) → f ≡ g

F→eq : FEA → ∀ α → (∀ n → α n ≡ false) → tω α ≡ ω
F→eq fe α h = cong alim (fe _ _ (λ n → cong (λ b → selN b n) (seen-false α h n)))

DecLgAt : A → Set
DecLgAt a = ∀ t → Lg t → Dec (t ≡ a)

Sepω : Set
Sepω = ∀ (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ ¬ (tω α ≡ ω)

deqω-sep : DecLgAt ω → Sepω
deqω-sep d α with d (tω α) (Lg-tω α)
... | yes e = inj₁ (eq→F α e)
... | no ne = inj₂ ne

deqω→WLPO : FEA → DecLgAt ω → WLPO
deqω→WLPO fe d α with deqω-sep d α
... | inj₁ h = inj₁ h
... | inj₂ ne = inj₂ (λ h → ne (F→eq fe α h))

-- DecAt 比 DecLgAt 强
decAt→lg : ∀ {a} → DecAt a → DecLgAt a
decAt→lg d t _ = d t
```

## §5 反方向: WLPO 加外延给出处处可判定相等, 从而给出 `RaiseA`

对 $a$ 结构递归判定 $t\equiv a$: 头不同则否; 后继处递归; ℕ-极限处逐项递归得到一列可判定命题, 用 WLPO 判定 "逐项都相等", 再用外延把逐项相等合成相等. 所以 (条件 `FEA`) WLPO 推出 `A` 上处处可判定相等, 再由 `deq→raise` 推出 `RaiseA`.

```agda
nb : ∀ {P : Set} → Dec P → Bool
nb (yes _) = false
nb (no _) = true

nb-f : ∀ {P : Set} (d : Dec P) → nb d ≡ false → P
nb-f (yes p) _ = p
nb-f (no _) ()

nb-p : ∀ {P : Set} (d : Dec P) → P → nb d ≡ false
nb-p (yes _) _ = refl
nb-p (no ¬p) p = ⊥-elim (¬p p)

unlim : A → ℕ → A
unlim (alim f) = f
unlim x = λ _ → x

wlpo→deq : FEA → WLPO → ∀ a → DecAt a
wlpo→deq fe W azero azero = yes refl
wlpo→deq fe W azero (asuc t) = no (λ ())
wlpo→deq fe W azero (alim g) = no (λ ())
wlpo→deq fe W (asuc a) azero = no (λ ())
wlpo→deq fe W (asuc a) (alim g) = no (λ ())
wlpo→deq fe W (asuc a) (asuc t) with wlpo→deq fe W a t
... | yes e = yes (cong asuc e)
... | no ne = no (λ e → ne (cong unsuc e))
wlpo→deq fe W (alim f) azero = no (λ ())
wlpo→deq fe W (alim f) (asuc t) = no (λ ())
wlpo→deq fe W (alim f) (alim g) with W (λ n → nb (wlpo→deq fe W (f n) (g n)))
... | inj₁ h = yes (cong alim (fe g f (λ n → nb-f (wlpo→deq fe W (f n) (g n)) (h n))))
... | inj₂ nh = no (λ e → nh (λ n → nb-p (wlpo→deq fe W (f n) (g n)) (cong (λ x → unlim x n) e)))

wlpo→raise : FEA → WLPO → RaiseA
wlpo→raise fe W = deq→raise (wlpo→deq fe W)

-- 与 §4 合起来 (条件 FEA): 对 ω 判定相等 ⇒ WLPO ⇒ 处处判定相等
deqω→deq : FEA → DecLgAt ω → ∀ a → DecAt a
deqω→deq fe d = wlpo→deq fe (deqω→WLPO fe d)
```

**读法.** 在 `FEA` 下: `DecLgAt ω` ⇔ WLPO ⇔ "`A` 上处处可判定相等", 三者都推出 `RaiseA`. 所以若能证 `RaiseA → P` (P 是某个非构造原则), 则 `FEA → WLPO → P`; 特别地, 证 `RaiseA → LPO` 就要证 `FEA → WLPO → LPO` (判断: 不可能, WLPO 严格弱于 LPO 在有外延的模型里也成立; 元层, 未编译). 否定一路的目标最多是 WLPO 这一档.

## §6 前提实例

- `wlpo→deq`, `wlpo→raise` 的前提 `FEA`, WLPO: 经典地成立, Agda 里证不出也否证不了 (判断), 两者相容 (经典模型).
- `deq→at` 的前提 `DecAt a`: 对有限数成立 (`nat-deq`, 构造). `deq→raise` 的前提 "处处可判定相等" 与 `deqω→WLPO` 的前提 `DecLgAt ω`, `FEA`: 在 Agda 里都证不出也否证不了 (判断: 经典地成立, 所以相容; 计算地不成立). `deqω-sep` 的结论 `Sepω` 经典地成立 (判断).
- `Lg-tω`: 每个 $\alpha$ 的 `tω α` 合法 (定理), 所以 `DecLgAt ω` 确实被用在合法的树上.

## §7 结论 (按档)

- **[定理, 构造]** `deq→at`, `raiseFin`, `Search.F-sound`, `F-comp`, `Rs-lo`, `Rs-hi`, `Rs-lg`; `ex-m0`, `ex-m2` (`refl`).
- **[定理, 条件: `A` 上处处可判定相等]** `deq→raise`.
- **[定理]** `deqω-sep`, `eq→F`, `Lg-tω`. **[定理, 条件 `FEA`]** `deqω→WLPO`, `F→eq`, `deqω→deq`. **[定理, 条件 `FEA` 与 WLPO]** `wlpo→deq`, `wlpo→raise`.
- **[判断]** 构造 $R$ 的难处在于下界是 ℕ-极限时 "等于 $a$" 不可半判定. 有限的下界可以; `deq→raise` 说明处处可判定相等就够, 不必判定子项关系. 我没有得到 `RaiseA → WLPO` 一类的定理, 也没有构造 `RaiseAt ω`.
