# 非数字目标孩子上, 三种写法的那一格

> 判决: 编译定理, 形状档 (`refl` 或对变量的归纳), 不读记号. `Ωt (tw 1)` 朝 `h₁ d` (经孩子 d) 折: 顶结点在四个折叠里都保留 (`top₁`, `top₂`, `top₂ᴬ`, `top₃`); 分支 c 处现行行退到第 0 层 (`w1`), 上折回退进 `ψˡ` (`w2`; K = `kp` 时材料里任何深度的槽位都走链, `w2-never`), 换基换成 `h₁ d ⊕ ↑c` 的 Ω 树, 保留判定在其中目标层副本的槽位上保留 (`w3`, `keep-lift`). 三种写法的行都不看 c 是否字面延伸 d.
> 字面延伸 `Ext d c` 是第一位置序 d ◃ c, 给出 `h₁ d ≤ h₁ c` (`ext-path`); d = ω 时 c = ωᵉ 两个方向都没有字面路径 (`no-ωᵉ`). 来源: `ext-path` 即 `YiPTAll.Rg`; `NoΩ`, `noΩ-↑` 照抄 `YiTLReduce` (其导入闭包含记号).
> 不否定什么: 没有值的定理. 真实链点 `chain 1` 上的同一张表在 [YiRKChain](YiRKChain.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRKCell where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; kp; kp⁼; node⁺)
open import OCF.Lean.YiTBRow using (h₁; nat) renaming (ψ to ψ₁)
open import OCF.Lean.YiMTTab using (rbᶻ; ψ₀ᶻ)
open import OCF.Lean.YiVALeaf using (NZ; nzs; nzl; fall)
open import OCF.Lean.YiTBTab using (ωᶜ; ωᵉ)
open import OCF.Lean.YiTBObs using (no-ωᵉ≤ω; no-ω≤ωᵉ)
open import OCF.Lean.YiDXFold using (KeepFn; kpᴬ; module Fold)
open import OCF.Lean.YiBSBase using (Schema; schema; seen; rb-tw)
import OCF.Lean.YiBSFold as BS
```

## 字面延伸与目标孩子 ω

```agda
Ext : Tr zero → Tr zero → Set
Ext d c = zero ⊢ d ◃ c

ext-nz : ∀ {d c} → Ext d c → NZ c
ext-nz ◃s           = nzs _
ext-nz (◃l n)       = nzl _ _
ext-nz (◃w {p = ()})
ext-nz (◃u x () y e)
ext-nz (◃c x () r)
ext-nz (◃t _ e)     = ext-nz e

ext-path : ∀ {d c} → Ext d c → h₁ d ≤ h₁ c
ext-path p = wk (⊕⊑ zero (◃→⊑ zero p))

ωω : Tr zero
ωω = ωᶜ + ωᶜ

nzω : NZ ωᶜ
nzω = nzl _ _

e-s : Ext ωᶜ (suc ωᶜ)
e-s = ◃s

e-ω : Ext ωᶜ ωω
e-ω = ◃l 0

no-ωᵉ : (h₁ ωᵉ ≤ h₁ ωᶜ) ⊎ (h₁ ωᶜ ≤ h₁ ωᵉ) → ⊥
no-ωᵉ (inj₁ p) = no-ωᵉ≤ω p
no-ωᵉ (inj₂ p) = no-ω≤ωᵉ p
```

## 输出形状的谓词

`IsL`: 顶是 ℕ 极限 (走链的结点). `IsΩ q`: 顶是槽位 q 上的 Ω 结点 (保留). `Ωfree`: 没有 Ω 与嵌入; 回退尾项 `ι j t` 都是这样.

```agda
data IsL {j : L} : Tr j → Set where
  isL : ∀ f a → IsL (lim f a)

data IsΩ {j : L} : Pos j → Tr j → Set where
  isΩ : ∀ p g → IsΩ p (Ω p g)

Kept : ∀ {j} → Tr j → Set
Kept {j} t = Σ (Pos j) λ q → IsΩ q t

Ωfree : ∀ {j} → Tr j → Set
Ωfree zero         = ⊤
Ωfree (suc x)      = Ωfree x
Ωfree (lim f a)    = (n : ℕ) → Ωfree (f n)
Ωfree (Ω p g)      = ⊥
Ωfree (up x c y e) = ⊥

ι-free : ∀ j (t : Tr zero) → Ωfree (ι j t)
ι-free j zero      = tt
ι-free j (suc t)   = ι-free j t
ι-free j (lim f a) = λ n → ι-free j (f n)

⊞-form : ∀ {j} (b : Tr⁺ j) (t : Tr⁺ zero) → proj₁ (b ⊞ t) ≡ proj₁ b + ι j (proj₁ t)
⊞-form b t = refl
```

## 顶结点: 四个折叠都保留

下标槽位沿 `kh d = lift zero (↑ zero d)` 推进 `h₁ d` 的第一孩子方向; d = ω 时落在 `q₀`. 所以分支对一切 c 都被问到.

```agda
q₀ : Pos (h₁ ωᶜ)
q₀ = inj₂ (0 , inj₁ tt)

top-ω : (B : Base (tw 1)) (β : Tr⁺ (h₁ ωᶜ))
  → IsΩ q₀ (proj₁ (ψ₁ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) B (h₁ ωᶜ) (inc ωᶜ self) β (proj₁ (Ωt (tw 1)))))
top-ω B β = isΩ _ _

top₁ : ∀ {d} → NZ d → (B : Base (tw 1)) (β : Tr⁺ (h₁ d))
  → Kept (proj₁ (ψ₁ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) B (h₁ d) (inc d self) β (proj₁ (Ωt (tw 1)))))
top₁ (nzs _)   B β = _ , isΩ _ _
top₁ (nzl _ _) B β = _ , isΩ _ _

top₂ : ∀ {d} → NZ d → (B : Base (tw 1)) (β : Tr⁺ (h₁ d))
  → Kept (proj₁ (Fold.ψ kp true (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) B (h₁ d) (inc d self) β (proj₁ (Ωt (tw 1)))))
top₂ (nzs _)   B β = _ , isΩ _ _
top₂ (nzl _ _) B β = _ , isΩ _ _

top₂ᴬ : ∀ {d} → NZ d → (B : Base (tw 1)) (β : Tr⁺ (h₁ d))
  → Kept (proj₁ (Fold.ψ kpᴬ true (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) B (h₁ d) (inc d self) β (proj₁ (Ωt (tw 1)))))
top₂ᴬ (nzs _)   B β = _ , isΩ _ _
top₂ᴬ (nzl _ _) B β = _ , isΩ _ _

top₃ : ∀ {d} → NZ d → (B : Base (tw 1)) (β : Tr⁺ (h₁ d))
  → Kept (proj₁ (BS.ψ (tw 1) (Ok-tw 1) (rb-tw 1) B (h₁ d) (inc d self) β (proj₁ (Ωt (tw 1)))))
top₃ (nzs _)   B β = _ , isΩ _ _
top₃ (nzl _ _) B β = _ , isΩ _ _
```

## 分支 c 处的一格

`Cell₁`: 现行行 (`YiTBRow.ψ` 配 `rbᶻ`). `Cell₂ K`: 上折回退 (`YiDXFold.Fold K true`). `Cell₃`: 换基 (`YiBSFold`, 证据 `rb-tw 1`, 地板是第 0 层); `Cell₃′` 是同步对象给的路径 (经孩子 d+1). `S₁` 逐字是 `rb-tw 1` 的第一分量.

```agda
S₁ : Schema zero h₁
S₁ = schema zero (↑ zero) tt self (OkO↑ zero zero tt self) (λ c → refl)

module _ (d c : Tr zero) where
  Cell₁ : Set
  Cell₁ = (o : Ok (tw 1)) (B : Base (tw 1)) (β : Tr⁺ (h₁ d)) (x : Tr (tw 1)) (y : Tr (h₁ c)) (e : h₁ c ⊢ zero ◃ y)
    → ψ₁ (tw 1) o (rbᶻ (tw 1)) B (h₁ d) (inc d self) β (up x c y e)
    ≡ ψ₁ (tw 1) o (rbᶻ (tw 1)) B (h₁ d) (inc d self) β x ⊞ ψ₀ᶻ (h₁ c) (proj₂ o c) y

  Cell₂ : KeepFn → Set
  Cell₂ K = (o : Ok (tw 1)) (B : Base (tw 1)) (β : Tr⁺ (h₁ d)) (x : Tr (tw 1)) (y : Tr (h₁ c)) (e : h₁ c ⊢ zero ◃ y)
    → Fold.ψ K true (tw 1) o (rbᶻ (tw 1)) B (h₁ d) (inc d self) β (up x c y e)
    ≡ Fold.ψˡ K true (tw 1) o (λ i u → Fold.ψ K true (tw 1) o (rbᶻ (tw 1)) B i u (B i u) x) (h₁ d) (inc d self)
        (Fold.ψ K true (tw 1) o (rbᶻ (tw 1)) B (h₁ d) (inc d self) β x) (h₁ c) (down stop c) y

  Cell₃ : Set
  Cell₃ = (o : Ok (tw 1)) (B : Base (tw 1)) (β : Tr⁺ (h₁ d)) (x : Tr (tw 1)) (y : Tr (h₁ c)) (e : h₁ c ⊢ zero ◃ y)
    → BS.ψ (tw 1) o (rb-tw 1) B (h₁ d) (inc d self) β (up x c y e)
    ≡ seen S₁ (h₁ d) (proj₂ o d) (lift zero (↑ zero d)) (BS.ψ (tw 1) o (rb-tw 1) B (h₁ d) (inc d self) β x) c
      ⊞ BS.ψ (h₁ c) (proj₂ o c) (proj₂ (rb-tw 1) c) (B₀ (h₁ c)) zero (z≤ (h₁ c)) (Ωt zero) y

  Cell₃′ : Set
  Cell₃′ = (o : Ok (tw 1)) (B : Base (tw 1)) (β : Tr⁺ (h₁ d)) (x : Tr (tw 1)) (y : Tr (h₁ c)) (e : h₁ c ⊢ zero ◃ y)
    → BS.ψ (tw 1) o (rb-tw 1) B (h₁ d) (inc (suc d) (inc tt self)) β (up x c y e)
    ≡ seen S₁ (h₁ d) (proj₂ (proj₂ o (suc d)) tt) (lift zero (↑ zero d))
        (BS.ψ (tw 1) o (rb-tw 1) B (h₁ d) (inc (suc d) (inc tt self)) β x) c
      ⊞ BS.ψ (h₁ c) (proj₂ o c) (proj₂ (rb-tw 1) c) (B₀ (h₁ c)) zero (z≤ (h₁ c)) (Ωt zero) y

w1 : ∀ {d c} → NZ d → NZ c → Cell₁ d c
w1 zd zc o B β x y e = fall zc zd o B _ self β x y e

w2 : ∀ (K : KeepFn) {d c} → NZ d → NZ c → Cell₂ d c K
w2 K (nzs _)   (nzs _)   o B β x y e = refl
w2 K (nzs _)   (nzl _ _) o B β x y e = refl
w2 K (nzl _ _) (nzs _)   o B β x y e = refl
w2 K (nzl _ _) (nzl _ _) o B β x y e = refl

w3 : ∀ {d} → NZ d → ∀ c → Cell₃ d c
w3 (nzs _)   c o B β x y e = refl
w3 (nzl _ _) c o B β x y e = refl

w3′ : ∀ {d} → NZ d → ∀ c → Cell₃′ d c
w3′ (nzs _)   c o B β x y e = refl
w3′ (nzl _ _) c o B β x y e = refl
```

d = ω, 两个字面延伸的孩子 (ω+1, ω+ω) 与两个不延伸的孩子 (1, ωᵉ).

```agda
t1-s : Cell₁ ωᶜ (suc ωᶜ)
t1-s = w1 nzω (ext-nz e-s)
t1-ω : Cell₁ ωᶜ ωω
t1-ω = w1 nzω (ext-nz e-ω)
t1-1 : Cell₁ ωᶜ (nat 1)
t1-1 = w1 nzω (nzs _)
t1-e : Cell₁ ωᶜ ωᵉ
t1-e = w1 nzω (nzl _ _)

t2-s : ∀ K → Cell₂ ωᶜ (suc ωᶜ) K
t2-s K = w2 K nzω (ext-nz e-s)
t2-ω : ∀ K → Cell₂ ωᶜ ωω K
t2-ω K = w2 K nzω (ext-nz e-ω)
t2-1 : ∀ K → Cell₂ ωᶜ (nat 1) K
t2-1 K = w2 K nzω (nzs _)
t2-e : ∀ K → Cell₂ ωᶜ ωᵉ K
t2-e K = w2 K nzω (nzl _ _)

t3-s : Cell₃ ωᶜ (suc ωᶜ)
t3-s = w3 nzω (suc ωᶜ)
t3-ω : Cell₃ ωᶜ ωω
t3-ω = w3 nzω ωω
t3-1 : Cell₃ ωᶜ (nat 1)
t3-1 = w3 nzω (nat 1)
t3-e : Cell₃ ωᶜ ωᵉ
t3-e = w3 nzω ωᵉ
```

## 槽位: 上折回退

`ψˡ` 的结点问 `K (tw 1) o (mv d p) (inc c′ v)`; d 从 `down stop c` 起只往下接, 所以 `mv d p` 总在孩子里 (`mv-child`), `kp` 在 "Ω 形状、槽位在孩子里、路径经 `inc`" 一行一律不保留 (`w2-never`, 同 `YiRQDom.drop`). `kpᴬ` 只在槽位层号字面是第 0 层时保留 (`w2A-floor`); p¹ 的层号是 `h₁ 1`, p⁼ 的层号就是目标.

```agda
IsNothing : {A : Set} → Maybe A → Set
IsNothing (just _) = ⊥
IsNothing nothing  = ⊤

IsChild : (a : L) → Pos a → Set
IsChild (nd s h) (inj₁ _) = ⊥
IsChild (nd s h) (inj₂ _) = ⊤

mv-child : ∀ {ℓ a} (d : Dn ℓ a) (p : Pos a) → IsChild a p → IsChild ℓ (mv d p)
mv-child stop       p ch = ch
mv-child (down d c) p ch = mv-child d (inj₂ (c , inj₂ p)) tt

drop-child : ∀ (o : Ok (tw 1)) (p : Pos (tw 1)) → IsChild (tw 1) p → ∀ c′ {j} (v : j ≤ h₁ c′)
  → IsNothing (kp (tw 1) o p (inc c′ v))
drop-child o (inj₂ t) ch c′ v = tt

w2-never : ∀ (o : Ok (tw 1)) {s h} (d : Dn (tw 1) (nd s h)) (c : Ch s) (p : Pos (h c)) c′ {j} (v : j ≤ h₁ c′)
  → IsNothing (kp (tw 1) o (mv (down d c) p) (inc c′ v))
w2-never o d c p c′ v = drop-child o (mv (down d c) p) (mv-child d (inj₂ (c , inj₂ p)) tt) c′ v

w2-drop : ∀ (o : Ok (tw 1)) (X : Base (tw 1)) j c′ (v : j ≤ h₁ c′) (β : Tr⁺ j) c (p : Pos (h₁ c)) g
  → IsL (proj₁ (Fold.ψˡ kp true (tw 1) o X j (inc c′ v) β (h₁ c) (down stop c) (Ω p g)))
w2-drop o X j c′ v β c p g = isL _ _

p⁰ p¹ p⁼ : Pos (h₁ (suc ωᶜ))
p⁰ = inj₂ (tt , inj₂ (inj₂ (0 , inj₁ tt)))
p¹ = inj₂ (tt , inj₂ (inj₂ (1 , inj₁ tt)))
p⁼ = inj₂ (tt , inj₁ tt)

w2A-floor : ∀ (o : Ok (tw 1)) (X : Base (tw 1)) c′ (v : h₁ ωᶜ ≤ h₁ c′) (β : Tr⁺ (h₁ ωᶜ)) g
  → IsΩ q₀ (proj₁ (Fold.ψˡ kpᴬ true (tw 1) o X (h₁ ωᶜ) (inc c′ v) β (h₁ (suc ωᶜ)) (down stop (suc ωᶜ)) (Ω p⁰ g)))
w2A-floor o X c′ v β g = isΩ _ _

w2A-one : ∀ (o : Ok (tw 1)) (X : Base (tw 1)) c′ (v : h₁ ωᶜ ≤ h₁ c′) (β : Tr⁺ (h₁ ωᶜ)) g
  → IsL (proj₁ (Fold.ψˡ kpᴬ true (tw 1) o X (h₁ ωᶜ) (inc c′ v) β (h₁ (suc ωᶜ)) (down stop (suc ωᶜ)) (Ω p¹ g)))
w2A-one o X c′ v β g = isL _ _

w2A-same : ∀ (o : Ok (tw 1)) (X : Base (tw 1)) c′ (v : h₁ ωᶜ ≤ h₁ c′) (β : Tr⁺ (h₁ ωᶜ)) g
  → IsL (proj₁ (Fold.ψˡ kpᴬ true (tw 1) o X (h₁ ωᶜ) (inc c′ v) β (h₁ (suc ωᶜ)) (down stop (suc ωᶜ)) (Ω p⁼ g)))
w2A-same o X c′ v β g = isL _ _
```

## 槽位: 换基

换基树在 `j ⊕ b` 层上沿 `lift j b` 折. 目标层的槽位 q 沿第一孩子推进 `j ⊕ b` 后, 在原槽位 q 上保留 (`keep-lift`, 对一切 j, b, q 与证据). `h₁ d ⊕ ↑c` 里没有 Ω 形状的层号 (`noΩ-reb`), 所以换基树的折叠碰不到 Ω 形状的回退行与 `kp` 的走链行. 后继孩子处换基树的顶结点走链, 槽位层号是 `j ⊕ ↑ d`, 不低于目标 (`seen-s`).

```agda
KeptAt : ∀ {j X x₀} → Pos j → Keep j X x₀ → Set
KeptAt q (just (q′ , _)) = q′ ≡ q
KeptAt q nothing         = ⊥

keep-lift : (j b : L) (o : Ok (j ⊕ b)) (q : Pos j) → KeptAt q (kp⁼ (j ⊕ b) o (psh (lift j b) (inj₂ q)) (lift j b))
keep-lift j zero          o q = refl
keep-lift j (nd sS h)     o q = keep-lift j (h tt) (proj₂ o tt) q
keep-lift j (nd sL h)     o q = keep-lift j (h zero) (proj₂ o zero) q
keep-lift j (nd (sΩ k) h) o q = keep-lift j (h zero) (proj₂ o zero) q

q₁ : Pos (h₁ ωᶜ)
q₁ = inj₂ (1 , inj₁ tt)

keep-ω : ∀ c (o : Ok (h₁ ωᶜ ⊕ ↑ zero c))
  → KeptAt q₁ (kp⁼ (h₁ ωᶜ ⊕ ↑ zero c) o (psh (lift (h₁ ωᶜ) (↑ zero c)) (inj₂ q₁)) (lift (h₁ ωᶜ) (↑ zero c)))
keep-ω c o = keep-lift (h₁ ωᶜ) (↑ zero c) o q₁

seen-s : ∀ d j (oj : Ok j) (u : zero ≤ j) (β : Tr⁺ j) → IsL (proj₁ (seen S₁ j oj u β (suc d)))
seen-s d j oj u β = isL _ _

NoΩ : L → Set
NoΩ zero          = ⊤
NoΩ (nd sS h)     = NoΩ (h tt)
NoΩ (nd sL h)     = (n : ℕ) → NoΩ (h n)
NoΩ (nd (sΩ _) _) = ⊥

noΩ-↑ : (c : Tr zero) → NoΩ (↑ zero c)
noΩ-↑ zero      = tt
noΩ-↑ (suc c)   = noΩ-↑ c
noΩ-↑ (lim f a) = λ n → noΩ-↑ (f n)

noΩ-⊕ : (a b : L) → NoΩ a → NoΩ b → NoΩ (a ⊕ b)
noΩ-⊕ a zero          na nb = na
noΩ-⊕ a (nd sS h)     na nb = noΩ-⊕ a (h tt) na nb
noΩ-⊕ a (nd sL h)     na nb = λ n → noΩ-⊕ a (h n) na (nb n)
noΩ-⊕ a (nd (sΩ _) _) na ()

noΩ-reb : (d c : Tr zero) → NoΩ (h₁ d ⊕ ↑ zero c)
noΩ-reb d c = noΩ-⊕ (h₁ d) (↑ zero c) (noΩ-⊕ zero (↑ zero d) tt (noΩ-↑ d)) (noΩ-↑ c)
```
