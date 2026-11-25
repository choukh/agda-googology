# φ 的配对否定: 分支侧 "同一分支就交给孩子" 要判定分支下标的相等

> 验收文件 (否定). 判决: 编译定理. 接口实例加上 `J2-Ωb` (目标在分支 c、嵌入也在分支 c 时交给孩子层) 与 `Ωb-off` (分支不同时照 `phi` 回退), 就对塔第 3 项的一个合法下标 c₀ 与一切 c′ 弱判定 c₀ ≡ c′ (`wdec`: ¬ 或 ¬¬), 从而对一切 α: α 处处为假, 或 c₀ 与 cα α 字面不等 (`wdecα`); 加函数外延作前提得 WLPO (`wlpo`, 条件定理).
> 若分支侧的派发经一个由两下标算出的同支证据 E (`ViaE`), 结论是字面相等可判定 (`viaE→dec`, 与 `R13Diag.diag→dec` 同). 探针 c₀, cα α, 嵌入的树都合法, 结点都在顶槽位 (`YiPhiNegDom` 核对), 在规范域内.
> 不否定什么: 只加 `J2-Ωb` 不加回退律时本篇不推出判定 (`J2-Ωb` 的式子由常值折叠满足, `j2b-const`, 它不是接口实例); 不否定接口 (`phi` 满足 `Ωb-off`, `ViaE`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPhiNegB where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (_+_; ι; Ωt)
open import OCF.Lean.YiFreshLegal using (_⊢_◃_; ◃s; ◃w; ◃u; ◃t; Leg)
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiPhiIface using (Iface)
open import OCF.Lean.YiPhiLegal using (LegB₀)
open import OCF.Lean.YiPhiCheck using (phi)
```

## 两条律

`J2-Ωb`: 目标路径 `inb c w` 与嵌入 `up x c y` 在同一个分支变量 c 上. `Ωb-off`: 分支不同时, 照 `phi` 的回退.

```agda
J2-Ωb : Iface → Set
J2-Ωb I = let open Iface I in
  (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (c : Tr k) (w : j ≤ h c) (β : Tr j)
  (x : Tr (Ωₗ k h)) (y : Tr (h c))
  → ψs (Ωₗ k h) ε B j (inb c w) β (up x c y)
  ≡ ψs (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) j w (ψs (Ωₗ k h) ε B j (inb c w) β x) y

Ωb-off : Iface → Set
Ωb-off I = let open Iface I in
  (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (c c′ : Tr k) (w : j ≤ h c′) (β : Tr j)
  (x : Tr (Ωₗ k h)) (y : Tr (h c)) → (c ≡ c′ → ⊥)
  → ψs (Ωₗ k h) ε B j (inb c′ w) β (up x c y)
  ≡ ψs (Ωₗ k h) ε B j (inb c′ w) β x + ι j (ψ⊥ (h c) (proj₂ (proj₂ ε c)) (B₀ (h c)) y)

off-phi : Ωb-off phi
off-phi k h ε B j c c′ w β x y ne = refl
```

## 探针 (塔第 3 项, 目标 tw 1 在分支 c′ 里)

c₀ 的第 m 项是 2m 个后继, cα α 在 α m 为真处多一个后继; 嵌入的树在 c₀ 的第 0 项 (层号 tw 2) 里, 是 tw 2 的第 0 个孩子里的一个顶槽位结点.

```agda
sucs : ∀ {ℓ} → ℕ → Tr ℓ
sucs zero    = zero
sucs (suc m) = suc (sucs m)

double : ℕ → ℕ
double zero    = zero
double (suc m) = suc (suc (double m))

ev : ℕ → Tr (tw 2)
ev m = sucs (double m)

bump : ∀ {ℓ} → Bool → Tr ℓ → Tr ℓ
bump true  t = suc t
bump false t = t

c₀ : Tr (tw 2)
c₀ = lim ev

cα : (ℕ → Bool) → Tr (tw 2)
cα α = lim (λ m → bump (α m) (ev m))

top₁ : Pos (tw 1)
top₁ = inj₁ (inj₁ tt)

h₃ : Tr (tw 2) → L
h₃ c = tw 2 ⊕ ↑ (tw 2) c

wc : (c : Tr (tw 2)) → tw 1 ≤ h₃ c
wc c = ink self ∙ lift (tw 2) (↑ (tw 2) c)

y₁ : Tr (tw 2)
y₁ = up zero zero (Ω top₁ (λ _ → zero))

y₀ : Tr (h₃ c₀)
y₀ = up zero zero y₁

legy₀ : Leg (h₃ c₀) y₀
legy₀ = tt , (tt , (λ _ _ → tt) , ◃w) , ◃u ◃w

isΩb : ∀ {P B C D} → T P B C D → Bool
isΩb (Ω _ _) = true
isΩb _       = false

t≢f : true ≡ false → ⊥
t≢f ()
```

## 两侧的头部

对角上: `J2-Ωb`, 接口的 `J2-limu` 与 `kstep` 连起来, 输出是结点. 分支不同: 回退的右加数是 `ι` 作用在非零的第 0 层树上 (`pres⊥`), 头部是后继或极限.

```agda
no-◃zero : ∀ {ℓ} {x : Tr ℓ} → ℓ ⊢ x ◃ zero → ⊥
no-◃zero (◃t d e) = no-◃zero e

plus-ι : ∀ {j} (a : Tr j) (t : Tr zero) → zero ⊢ zero ◃ t → isΩb (a + ι j t) ≡ false
plus-ι a zero    nz = ⊥-elim (no-◃zero nz)
plus-ι a (suc t) nz = refl
plus-ι a (lim f) nz = refl

module Probe (I : Iface) where
  open Iface I

  O : Tr (tw 2) → Tr (tw 1)
  O c′ = ψs (tw 3) (Ev-tw 3) (B₀ _) (tw 1) (inb c′ (wc c′)) (Ωt (tw 1)) (up zero c₀ y₀)

  fb : Tr (tw 1)
  fb = ψs (tw 3) (Ev-tw 3) (B₀ _) (tw 1) (inb c₀ (wc c₀)) (Ωt (tw 1)) zero
     + ι (tw 1) (ψ⊥ (h₃ c₀) (proj₂ (proj₂ (Ev-tw 3) c₀)) (B₀ (h₃ c₀)) y₀)

  diag : J2-Ωb I → isΩb (O c₀) ≡ true
  diag J = cong isΩb (trans (J (tw 2) h₃ (Ev-tw 3) (B₀ _) (tw 1) c₀ (wc c₀) (Ωt (tw 1)) zero y₀)
                     (trans (J2-limu (λ m → h₃ (ev m)) (proj₂ (proj₂ (Ev-tw 3) c₀)) _ (tw 1)
                                     (λ m → wc (ev m)) _ zero zero y₁)
                            (kstep 1 _ _ zero top₁ (λ _ → zero))))

  nz : zero ⊢ zero ◃ ψ⊥ (h₃ c₀) (proj₂ (proj₂ (Ev-tw 3) c₀)) (B₀ (h₃ c₀)) y₀
  nz = proj₂ (pres⊥ (h₃ c₀) (proj₂ (proj₂ (Ev-tw 3) c₀)) (B₀ _) (LegB₀ _) y₀ legy₀)

  off : Ωb-off I → (c′ : Tr (tw 2)) → (c₀ ≡ c′ → ⊥) → isΩb (O c′) ≡ false
  off F c′ ne = trans (cong isΩb (F (tw 2) h₃ (Ev-tw 3) (B₀ _) (tw 1) c₀ c′ (wc c′) (Ωt (tw 1)) zero y₀ ne))
                      (plus-ι _ _ nz)
```

## 弱判定

```agda
WDec : Set → Set
WDec A = (A → ⊥) ⊎ ((A → ⊥) → ⊥)

wdecᵂ : (I : Iface) → J2-Ωb I
  → ((c′ : Tr (tw 2)) → (c₀ ≡ c′ → ⊥) → isΩb (Probe.O I c′) ≡ false) → (c′ : Tr (tw 2)) → WDec (c₀ ≡ c′)
wdecᵂ I J off′ c′ = go (isΩb (O c′)) refl
  where
  open Probe I
  go : (b : Bool) → isΩb (O c′) ≡ b → WDec (c₀ ≡ c′)
  go true  e = inj₂ (λ ne → t≢f (trans (sym e) (off′ c′ ne)))
  go false e = inj₁ (λ eq → t≢f (trans (sym (diag J)) (subst (λ c → isΩb (O c) ≡ false) (sym eq) e)))

wdec : (I : Iface) → J2-Ωb I → Ωb-off I → (c′ : Tr (tw 2)) → WDec (c₀ ≡ c′)
wdec I J F = wdecᵂ I J (Probe.off I F)
```

c₀ ≡ cα α 推出 α 处处为假 (逐项比较后继个数). 反方向要函数外延.

```agda
pd : ∀ {ℓ} → Tr ℓ → Tr ℓ
pd (suc t) = t
pd t       = t

no-suc : ∀ {ℓ} (m : ℕ) → sucs {ℓ} m ≡ suc (sucs m) → ⊥
no-suc zero    ()
no-suc (suc m) e = no-suc m (cong pd e)

comp : Tr (tw 2) → ℕ → Tr (tw 2)
comp (lim f) = f
comp _       = λ _ → zero

eq→allF : ∀ α → c₀ ≡ cα α → ∀ n → α n ≡ false
eq→allF α e n = go (α n) (cong (λ t → comp t n) e)
  where
  go : (b : Bool) → ev n ≡ bump b (ev n) → b ≡ false
  go true  e′ = ⊥-elim (no-suc (double n) e′)
  go false e′ = refl

stab : ∀ α → ((c₀ ≡ cα α → ⊥) → ⊥) → ∀ n → α n ≡ false
stab α nne n = go (α n) refl
  where
  go : (b : Bool) → α n ≡ b → α n ≡ false
  go true  q = ⊥-elim (nne (λ e → t≢f (trans (sym q) (eq→allF α e n))))
  go false q = q

wdecα : (I : Iface) → J2-Ωb I → Ωb-off I → ∀ α → (∀ n → α n ≡ false) ⊎ (c₀ ≡ cα α → ⊥)
wdecα I J F α with wdec I J F (cα α)
... | inj₁ ne  = inj₂ ne
... | inj₂ nne = inj₁ (stab α nne)
```

条件定理: 加函数外延, 得 WLPO.

```agda
Funext : Set₁
Funext = {A : Set} {B : A → Set} {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g

WLPO : Set
WLPO = (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ ((∀ n → α n ≡ false) → ⊥)

allF→eq : Funext → ∀ α → (∀ n → α n ≡ false) → c₀ ≡ cα α
allF→eq fe α af = cong lim (fe λ n → cong (λ b → bump b (ev n)) (sym (af n)))

wlpo : Funext → (I : Iface) → J2-Ωb I → Ωb-off I → WLPO
wlpo fe I J F α with wdecα I J F α
... | inj₁ af = inj₁ af
... | inj₂ ne = inj₂ (λ af → ne (allF→eq fe α af))
```

## 经同支证据派发: 字面相等可判定

`ViaE`: 分支侧那一行由同支证据 `E k c c′` 决定, 有证据就沿 `hand` 搬路径交给孩子, 否则回退. `phi` 是 E 恒为 `nothing` 的情形.

```agda
hand : ∀ {k} {h : Tr k → L} {j} {c c′ : Tr k} → c ≡ c′ → j ≤ h c′ → j ≤ h c
hand refl w = w

IsJust : ∀ {A : Set} → Maybe A → Set
IsJust (just _) = ⊤
IsJust nothing  = ⊥

ViaE : Iface → Set
ViaE I = let open Iface I in
  Σ ((k : L) → (c c′ : Tr k) → Maybe (c ≡ c′)) λ E →
  (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (c c′ : Tr k) (w : j ≤ h c′) (β : Tr j)
  (x : Tr (Ωₗ k h)) (y : Tr (h c))
  → ψs (Ωₗ k h) ε B j (inb c′ w) β (up x c y)
  ≡ maybe′ (λ e → ψs (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) j (hand e w) (ψs (Ωₗ k h) ε B j (inb c′ w) β x) y)
           (ψs (Ωₗ k h) ε B j (inb c′ w) β x + ι j (ψ⊥ (h c) (proj₂ (proj₂ ε c)) (B₀ (h c)) y))
           (E k c c′)

viaE-phi : ViaE phi
viaE-phi = (λ _ _ _ → nothing) , λ k h ε B j c c′ w β x y → refl

Dec′ : Set → Set
Dec′ A = A ⊎ (A → ⊥)

diag→dec : ∀ {k} (E : (c c′ : Tr k) → Maybe (c ≡ c′)) (a : Tr k) → IsJust (E a a) → ∀ c′ → Dec′ (a ≡ c′)
diag→dec E a j c′ = go (E a c′) refl
  where
  back : ∀ {y} → a ≡ y → E a y ≡ nothing → ⊥
  back refl h = subst IsJust h j
  go : (u : Maybe (a ≡ c′)) → E a c′ ≡ u → Dec′ (a ≡ c′)
  go (just e) h = inj₁ e
  go nothing  h = inj₂ (λ e → back e h)

viaE→dec : (I : Iface) → J2-Ωb I → ViaE I → (c′ : Tr (tw 2)) → Dec′ (c₀ ≡ c′)
viaE→dec I J (E , V) = diag→dec (E (tw 2)) c₀ (go (E (tw 2) c₀ c₀) refl)
  where
  open Probe I
  open Iface I using (ψs; dW)
  ch : c₀ ≡ c₀ → Tr (tw 1)
  ch e = ψs (h₃ c₀) (proj₂ (proj₂ (Ev-tw 3) c₀)) (dW (tw 2) h₃ (Ev-tw 3) (B₀ _) c₀ zero) (tw 1) (hand {h = h₃} e (wc c₀))
            (ψs (tw 3) (Ev-tw 3) (B₀ _) (tw 1) (inb c₀ (wc c₀)) (Ωt (tw 1)) zero) y₀
  go : (m : Maybe (c₀ ≡ c₀)) → E (tw 2) c₀ c₀ ≡ m → IsJust (E (tw 2) c₀ c₀)
  go (just e) q = subst IsJust (sym q) tt
  go nothing  q = ⊥-elim (t≢f (trans (sym (diag J))
    (trans (cong isΩb (trans (V (tw 2) h₃ (Ev-tw 3) (B₀ _) (tw 1) c₀ c₀ (wc c₀) (Ωt (tw 1)) zero y₀)
                             (cong (maybe′ ch fb) q)))
           (plus-ι _ _ nz))))
```

## 前提的实例

`J2-Ωb` 的式子本身可以满足: 常值折叠 (输出恒为偏移 β) 满足它, 但不满足 `Ωb-off`. 它不是接口实例 (不严格单调).

```agda
J2-Ωbᶠ : (ψs : (ℓ : L) → Ev ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr j → Tr ℓ → Tr j)
  → (dW : (k : L) (h : Tr k → L) → Ev (Ωₗ k h) → Base (Ωₗ k h) → (c : Tr k) → Tr (Ωₗ k h) → Base (h c)) → Set
J2-Ωbᶠ ψs dW =
  (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (c : Tr k) (w : j ≤ h c) (β : Tr j)
  (x : Tr (Ωₗ k h)) (y : Tr (h c))
  → ψs (Ωₗ k h) ε B j (inb c w) β (up x c y)
  ≡ ψs (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) j w (ψs (Ωₗ k h) ε B j (inb c w) β x) y

j2b-const : J2-Ωbᶠ (λ ℓ ε B j w β x → β) (λ k h ε B c x → B₀ (h c))
j2b-const k h ε B j c w β x y = refl
```
