# 上折的配对否定: 摊平后的同支保留要判定同支

> 验收文件 (否定). 判决: 编译定理. 加强 `FlatKeep` (摊平进 Ωₗ 层分支 c 的结点, 以同支目标 `inb c w` 折叠时, 以孩子层保留判定给出的槽位为根) 连同 `FlatOff` (分支不同时不以任何槽位为根, `upI` 满足) 对塔第 3 项的合法下标 c₀ 与一切 c′ 弱判定 c₀ ≡ c′ (`flat→wdec`), 加函数外延得 WLPO (`flat→wlpo`, 条件定理); 经同支证据 E 派发则字面相等可判定 (`flatE→dec`). `upI` 不满足加强 (`up-not-flatKeep`, 即 omD 写成定理).
> 规范域: 探针结点是 `upI` 的自身行对 `YiTopDom.Top` 内合法输入 `up zero c₀ y₀` (偏移合法非零) 的输出 (`probe-self`, `probe-in`); 结点本身不在 `Top` (`probe-notTop`). 所用的域是 "Top 内合法输入的自身行像". `upI` 自己的链步里就有这一情形 (`chain-flat` 对 `chain-emb`, 有限测试).
> 不否定什么: 不否定接口 (`upI` 满足 `FlatOff` 与 `FlatE`). 只有加强而无 `FlatOff` 时本篇不推出判定 (探针上的保留由常值函数满足, `keep-const`; 它不满足 `FlatOff`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUpNegFlat where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (Ωt)
open import OCF.Lean.YiFreshLegal using (_⊢_◃_; ◃u; ◃w; ◃t; Leg; LN; Ωt-leg; Ωt-nz)
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiPhiFold using (kp⁼)
open import OCF.Lean.YiPhiNegK using (Kept)
open import OCF.Lean.YiPhiNegB
  using (sucs; double; ev; bump; c₀; cα; h₃; wc; top₁; y₀; legy₀; isΩb; t≢f; WDec; stab; Funext; WLPO; allF→eq;
         hand; IsJust; Dec′; diag→dec)
open import OCF.Lean.YiPhiNegDom using (b-c₀-leg; b-cα-leg)
open import OCF.Lean.YiTopDom using (Top)
open import OCF.Lean.YiUpBlock using (Upc)
open import OCF.Lean.YiUpIface using (Iface)
import OCF.Lean.YiUpFold as F
open import OCF.Lean.YiUpCheck using (upI)
```

## 加强与回退

`root⁼`: 孩子层的保留判定 (`kp⁼`, 折叠里原样使用的那个) 交出的槽位, 不保留时 `nothing`. 律对裸函数陈述, 以便给非实例的见证.

```agda
ψT : Set
ψT = (ℓ : L) → Ev ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr j → Tr ℓ → Tr j

root⁼ : (a : L) → Ev a → Pos⁼ a → {j : L} → j ≤ a → Maybe (Pos j)
root⁼ a ε t w = kp⁼ a ε t w (λ q _ → just q) nothing

FlatKeepᶠ : ψT → Set
FlatKeepᶠ ψs = (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (c : Tr k) (w : j ≤ h c)
  (β : Tr j) (b : Tr (Ωₗ k h)) (p : Pos (h c)) (G : Br (h c) p → Tr (h c)) (q : Pos j)
  → root⁼ (h c) (proj₂ (proj₂ ε c)) (inj₂ p) w ≡ just q
  → Kept q (ψs (Ωₗ k h) ε B j (inb c w) β (Upc (Ωₗ k h) c b (Ω p G)))

FlatOffᶠ : ψT → Set
FlatOffᶠ ψs = (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (c c′ : Tr k) (w : j ≤ h c′)
  (β : Tr j) (b : Tr (Ωₗ k h)) (p : Pos (h c)) (G : Br (h c) p → Tr (h c)) → (c ≡ c′ → ⊥)
  → (q : Pos j) → Kept q (ψs (Ωₗ k h) ε B j (inb c′ w) β (Upc (Ωₗ k h) c b (Ω p G))) → ⊥

FlatEᶠ : ψT → Set
FlatEᶠ ψs = Σ ((k : L) (c c′ : Tr k) → Maybe (c ≡ c′)) λ E →
  (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (c c′ : Tr k) (w : j ≤ h c′)
  (β : Tr j) (b : Tr (Ωₗ k h)) (p : Pos (h c)) (G : Br (h c) p → Tr (h c)) → E k c c′ ≡ nothing
  → (q : Pos j) → Kept q (ψs (Ωₗ k h) ε B j (inb c′ w) β (Upc (Ωₗ k h) c b (Ω p G))) → ⊥

FlatKeep FlatOff FlatE : Iface → Set
FlatKeep I = FlatKeepᶠ (Iface.ψs I)
FlatOff  I = FlatOffᶠ (Iface.ψs I)
FlatE    I = FlatEᶠ (Iface.ψs I)
```

## `upI`: 摊平进分支的结点在分支侧目标下从不保留

对一切 c, c′ (不要求不等): 保留判定在 `inj₂ (c , …)` 对 `inb c′ …` 一行走默认.

```agda
up-never : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (c c′ : Tr k) (w : j ≤ h c′)
  (β : Tr j) (b : Tr (Ωₗ k h)) (p : Pos (h c)) (G : Br (h c) p → Tr (h c)) (q : Pos j)
  → Kept q (F.ψs (Ωₗ k h) ε B j (inb c′ w) β (Upc (Ωₗ k h) c b (Ω p G))) → ⊥
up-never k h ε B j c c′ w β b p G q (G′ , ())

off-up : FlatOff upI
off-up k h ε B j c c′ w β b p G ne = up-never k h ε B j c c′ w β b p G

flatE-up : FlatE upI
flatE-up = (λ _ _ _ → nothing) , λ k h ε B j c c′ w β b p G e → up-never k h ε B j c c′ w β b p G
```

## 探针

c₀, `h₃`, `wc`, `y₀` 取自 `YiPhiNegB`. `p₀` 是 `y₀` 里那个结点 (tw 1 的顶槽位) 在孩子层 h₃ c₀ 里的槽位; `node β` 是它摊平进 tw 3 后的样子.

```agda
p₀ : Pos (h₃ c₀)
p₀ = zero , inj₂ (inj₂ (zero , inj₂ top₁))

node : Tr (tw 3) → Tr (tw 3)
node b = Upc (tw 3) c₀ b (Ω p₀ (λ _ → zero))

O : Iface → Tr (tw 3) → Tr (tw 2) → Tr (tw 1)
O I b c′ = Iface.ψs I (tw 3) (Ev-tw 3) (B₀ (tw 3)) (tw 1) (inb c′ (wc c′)) (Ωt (tw 1)) (node b)

root-p₀ : root⁼ (h₃ c₀) (proj₂ (proj₂ (Ev-tw 3) c₀)) (inj₂ p₀) (wc c₀) ≡ just top₁
root-p₀ = refl
```

omC 与 omD 的定理形式: 孩子层里以 `wc c₀` 折叠, 结点以 `top₁` 为根保留; 摊平后以 `inb c₀ (wc c₀)` 折叠, 不以任何槽位为根. 两者对一切底与偏移.

```agda
child-keeps : (B : Base (h₃ c₀)) (β : Tr (tw 1)) (G : Br (h₃ c₀) p₀ → Tr (h₃ c₀))
  → Kept top₁ (F.ψs (h₃ c₀) (proj₂ (proj₂ (Ev-tw 3) c₀)) B (tw 1) (wc c₀) β (Ω p₀ G))
child-keeps B β G = _ , refl

flat-folds : (B : Base (tw 3)) (β : Tr (tw 1)) (b : Tr (tw 3)) (q : Pos (tw 1))
  → Kept q (F.ψs (tw 3) (Ev-tw 3) B (tw 1) (inb c₀ (wc c₀)) β (node b)) → ⊥
flat-folds B β b q = up-never (tw 2) h₃ (Ev-tw 3) B (tw 1) c₀ c₀ (wc c₀) β b p₀ (λ _ → zero) q
```

## 探针在哪个域

输入 `up zero c₀ y₀` 在 `Top` 内且合法, 偏移 `Ωt (tw 3)` 合法非零; `upI` 的自身行把它变成 `node β`, 后者离开 `Top`. 下标 c₀, cα α 合法 (`YiPhiNegDom`) 且在 `Top` 内.

```agda
probe-self : (B : Base (tw 3)) (β : Tr (tw 3))
  → F.ψs (tw 3) (Ev-tw 3) B (tw 3) self β (up zero c₀ y₀) ≡ node β
probe-self B β = refl

probe-in : Top (tw 3) (up zero c₀ y₀) × Leg (tw 3) (up zero c₀ y₀) × LN (tw 3) (Ωt (tw 3))
probe-in = (tt , tt , tt , tt , λ _ _ → tt) , (tt , legy₀ , ◃u (◃u ◃w)) , (Ωt-leg (tw 3) , Ωt-nz (tw 3))

probe-notTop : (β : Tr (tw 3)) → Top (tw 3) (node β) → ⊥
probe-notTop β (() , _)

top-sucs : ∀ {ℓ} (m : ℕ) → Top ℓ (sucs m)
top-sucs zero    = tt
top-sucs (suc m) = top-sucs m

c₀-in : Top (tw 2) c₀ × Leg (tw 2) c₀
c₀-in = (λ n → top-sucs (double n)) , b-c₀-leg

top-bump : ∀ {ℓ} (v : Bool) (t : Tr ℓ) → Top ℓ t → Top ℓ (bump v t)
top-bump true  t h = h
top-bump false t h = h

cα-in : ∀ α → Top (tw 2) (cα α) × Leg (tw 2) (cα α)
cα-in α = (λ n → top-bump (α n) (ev n) (top-sucs (double n))) , b-cα-leg α
```

## 规范计算里的出现 (有限测试, 单个样本, 对一切底与偏移)

`upI` 自身的链步里就有 omD 的情形. 层号 tw 1, 孩子 c₂ = 2 (孩子层是 2), 输入 `up zero c₂ yS` 在 `Top` 内且合法. 自身行把 yS 的两个结点摊平到 `s₁` (层号 1) 与 `s₂` (层号 0); 外结点的链步以 `posW (tw 1) s₁ = inb c₂ (ins self)` 折分支, 内结点走默认 (`chain-flat`). 摊平前, 孩子层里同一链步保留内结点 (`chain-emb`).

```agda
two : L
two = suc (suc zero)

c₂ : Tr zero
c₂ = suc (suc zero)

yS : Tr two
yS = Ω (inj₁ tt) (λ z → up zero tt (Ω (inj₁ tt) (λ _ → zero)))

yS-in : Top (tw 1) (up zero c₂ yS) × Leg (tw 1) (up zero c₂ yS)
yS-in = (tt , tt , λ z _ → tt , tt , λ _ _ → tt) , (tt , (λ z _ → tt , (λ _ _ → tt) , ◃w) , ◃t (◃u ◃w) ◃w)

s₁ s₂ : Pos (tw 1)
s₁ = inj₂ (c₂ , inj₂ (inj₁ tt))
s₂ = inj₂ (c₂ , inj₂ (inj₂ (inj₁ tt)))

chain-self : (B : Base (tw 1)) (β : Tr (tw 1))
  → F.ψs (tw 1) (Ev-tw 1) B (tw 1) self β (up zero c₂ yS) ≡ Ω s₁ (λ _ → Ω s₂ (λ _ → β))
chain-self B β = refl

chain-path : posW (tw 1) s₁ ≡ inb c₂ (ins self)
chain-path = refl

chain-flat : (B : Base (tw 1)) (β : Tr (tw 1)) (β′ : Tr (at (tw 1) s₁))
  → isΩb (F.ψs (tw 1) (Ev-tw 1) B (at (tw 1) s₁) (posW (tw 1) s₁) β′ (Ω s₂ (λ _ → β))) ≡ false
chain-flat B β β′ = refl

chain-emb : (B : Base two) (β′ : Tr (at two (inj₁ tt)))
  → isΩb (F.ψs two tt B (at two (inj₁ tt)) (posW two (inj₁ tt)) β′ (up zero tt (Ω (inj₁ tt) (λ _ → zero)))) ≡ true
chain-emb B β′ = refl
```

## 两侧的头部

```agda
kept-isΩ : ∀ {j} {q : Pos j} (o : Tr j) → Kept q o → isΩb o ≡ true
kept-isΩ o (G′ , e) = cong isΩb e

none-isΩ : ∀ {j} (o : Tr j) → ((q : Pos j) → Kept q o → ⊥) → isΩb o ≡ false
none-isΩ zero       f = refl
none-isΩ (suc o)    f = refl
none-isΩ (lim g)    f = refl
none-isΩ (Ω q G)    f = ⊥-elim (f q (G , refl))
none-isΩ (up x c y) f = refl

keep₀ : (I : Iface) → FlatKeep I → (b : Tr (tw 3)) → Kept top₁ (O I b c₀)
keep₀ I K b = K (tw 2) h₃ (Ev-tw 3) (B₀ (tw 3)) (tw 1) c₀ (wc c₀) (Ωt (tw 1)) b p₀ (λ _ → zero) top₁ root-p₀

off₀ : (I : Iface) → FlatOff I → (b : Tr (tw 3)) (c′ : Tr (tw 2)) → (c₀ ≡ c′ → ⊥) → isΩb (O I b c′) ≡ false
off₀ I F b c′ ne = none-isΩ _ (F (tw 2) h₃ (Ev-tw 3) (B₀ (tw 3)) (tw 1) c₀ c′ (wc c′) (Ωt (tw 1)) b p₀ (λ _ → zero) ne)
```

## 弱判定

`wdecᴾ` 只用探针上的两件事 (在 c₀ 处是结点, 在其余处不是), 不用接口.

```agda
wdecᴾ : (O′ : Tr (tw 2) → Tr (tw 1)) → isΩb (O′ c₀) ≡ true
  → ((c′ : Tr (tw 2)) → (c₀ ≡ c′ → ⊥) → isΩb (O′ c′) ≡ false) → (c′ : Tr (tw 2)) → WDec (c₀ ≡ c′)
wdecᴾ O′ d off c′ = go (isΩb (O′ c′)) refl
  where
  go : (v : Bool) → isΩb (O′ c′) ≡ v → WDec (c₀ ≡ c′)
  go true  e = inj₂ (λ ne → t≢f (trans (sym e) (off c′ ne)))
  go false e = inj₁ (λ eq → t≢f (trans (sym d) (subst (λ c → isΩb (O′ c) ≡ false) (sym eq) e)))

flat→wdec : (I : Iface) → FlatKeep I → FlatOff I → (c′ : Tr (tw 2)) → WDec (c₀ ≡ c′)
flat→wdec I K F = wdecᴾ (O I (Ωt (tw 3))) (kept-isΩ _ (keep₀ I K (Ωt (tw 3)))) (off₀ I F (Ωt (tw 3)))

flat→wdecα : (I : Iface) → FlatKeep I → FlatOff I → ∀ α → (∀ n → α n ≡ false) ⊎ (c₀ ≡ cα α → ⊥)
flat→wdecα I K F α with flat→wdec I K F (cα α)
... | inj₁ ne  = inj₂ ne
... | inj₂ nne = inj₁ (stab α nne)

flat→wlpo : Funext → (I : Iface) → FlatKeep I → FlatOff I → WLPO
flat→wlpo fe I K F α with flat→wdecα I K F α
... | inj₁ af = inj₁ af
... | inj₂ ne = inj₂ (λ af → ne (allF→eq fe α af))
```

经同支证据派发: c₀ 处必须给出证据, 于是字面相等可判定.

```agda
flatE→dec : (I : Iface) → FlatKeep I → FlatE I → (c′ : Tr (tw 2)) → Dec′ (c₀ ≡ c′)
flatE→dec I K (E , V) = diag→dec (E (tw 2)) c₀ (go (E (tw 2) c₀ c₀) refl)
  where
  go : (m : Maybe (c₀ ≡ c₀)) → E (tw 2) c₀ c₀ ≡ m → IsJust (E (tw 2) c₀ c₀)
  go (just e) r = subst IsJust (sym r) tt
  go nothing  r = ⊥-elim (V (tw 2) h₃ (Ev-tw 3) (B₀ (tw 3)) (tw 1) c₀ c₀ (wc c₀) (Ωt (tw 1)) (Ωt (tw 3)) p₀
                             (λ _ → zero) r top₁ (keep₀ I K (Ωt (tw 3))))
```

## omD 写成定理

```agda
up-not-flatKeep : FlatKeep upI → ⊥
up-not-flatKeep K = flat-folds (B₀ (tw 3)) (Ωt (tw 1)) (Ωt (tw 3)) top₁ (keep₀ upI K (Ωt (tw 3)))
```

## 前提的实例

`FlatOff`, `FlatE`: `upI` (上文). 探针上的保留单独可满足: 常值函数 (输出恒为偏移) 在探针上以 `top₁` 为根, 但它不满足 `FlatOff`.

```agda
ψc : ψT
ψc ℓ ε B j w β x = β

keep-const : Kept top₁ (ψc (tw 3) (Ev-tw 3) (B₀ (tw 3)) (tw 1) (inb c₀ (wc c₀)) (Ωt (tw 1)) (node (Ωt (tw 3))))
keep-const = _ , refl

const-not-off : FlatOffᶠ ψc → ⊥
const-not-off F = F (tw 2) h₃ (Ev-tw 3) (B₀ (tw 3)) (tw 1) c₀ zero (wc zero) (Ωt (tw 1)) (Ωt (tw 3)) p₀ (λ _ → zero)
                    (λ ()) top₁ (_ , refl)
```

`FlatKeep` 与 `FlatOff` 合起来, 在给定同支判定 E (对角上是 `just refl`) 时由裸函数 `ψsᴱ` 满足 (条件实例; 它不是接口实例). 构造地给不出 E, 这正是上面的定理所说.

```agda
mk : ∀ {j} → Tr j → Maybe (Pos j) → Tr j
mk β (just q) = Ω q (λ _ → β)
mk β nothing  = suc β

selᴱ : ∀ {k} (h : Tr k → L) (c c′ : Tr k) {j : L} → Ev (h c) → Pos (h c) → j ≤ h c′ → Tr j → Maybe (c ≡ c′) → Tr j
selᴱ h c c′ ε p w β (just e) = mk β (root⁼ (h c) ε (inj₂ p) (hand {h = h} e w))
selᴱ h c c′ ε p w β nothing  = suc β

ψsᴱ : ((k : L) (c c′ : Tr k) → Maybe (c ≡ c′)) → ψT
ψsᴱ E (Ωₗ k h) ε B j (inb c′ w) β (Ω (inj₂ (c , inj₂ p)) G) = selᴱ h c c′ (proj₂ (proj₂ ε c)) p w β (E k c c′)
ψsᴱ E ℓ ε B j w β x = suc β

keepᴱ : (E : (k : L) (c c′ : Tr k) → Maybe (c ≡ c′)) → ((k : L) (c : Tr k) → E k c c ≡ just refl)
  → FlatKeepᶠ (ψsᴱ E)
keepᴱ E Er k h ε B j c w β b p G q r =
  subst (λ m → Kept q (selᴱ h c c (proj₂ (proj₂ ε c)) p w β m)) (sym (Er k c))
        (subst (λ m → Kept q (mk β m)) (sym r) (_ , refl))

selOff : ∀ {k} (h : Tr k → L) (c c′ : Tr k) {j : L} (ε : Ev (h c)) (p : Pos (h c)) (w : j ≤ h c′) (β : Tr j)
  (m : Maybe (c ≡ c′)) → ((e : c ≡ c′) → m ≡ just e → ⊥) → (q : Pos j) → Kept q (selᴱ h c c′ ε p w β m) → ⊥
selOff h c c′ ε p w β (just e) f q _        = f e refl
selOff h c c′ ε p w β nothing  f q (G′ , ())

offᴱ : (E : (k : L) (c c′ : Tr k) → Maybe (c ≡ c′)) → FlatOffᶠ (ψsᴱ E)
offᴱ E k h ε B j c c′ w β b p G ne =
  selOff h c c′ (proj₂ (proj₂ ε c)) p w β (E k c c′) (λ e _ → ne e)

flatEᴱ : (E : (k : L) (c c′ : Tr k) → Maybe (c ≡ c′)) → FlatEᶠ (ψsᴱ E)
flatEᴱ E = E , λ k h ε B j c c′ w β b p G r →
  selOff h c c′ (proj₂ (proj₂ ε c)) p w β (E k c c′) (λ e r′ → no (trans (sym r) r′))
  where
  no : ∀ {A : Set} {a : A} → nothing ≡ just a → ⊥
  no ()
```
