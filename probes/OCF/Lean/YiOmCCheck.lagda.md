# 留在孩子里, 底依赖左边: 检查

> 验收文件 (测试). 编译定理: 接口 `YiOmCIface.Iface` 由 `YiOmCFold`, `YiOmCLegal` 实填 (`omI`, 对一切带证据的层号); `kall` 成立; Ω 结点层号的自身行是加法 (`self-add`); x = 0 时孩子的底就是底 B 的分量 (`kid-zero`).
> 有限测试 (`refl`, `tt`): 同支结点留在孩子里且在孩子层的链步下保留 (`P-kept`, `omD`, `deep`); 塔第 2 项链第一步上 (C′) 的孩子的底化成常量 `Ωt (h c)` (`step1`), 第 0 支与常量底 (C) 逐字相同 (`br0-same`), 第 1 支同形 (`br1-C′`, `br1-C`; 两个折叠是不同的函数, `refl` 不比较); x 非零时两者不同 (`differ-C′`, `differ-C`); 层号 tw 1 + 1 的 Ω 树的链 (`form-suc`) 上, 自身折叠 F 对右加 β₁ 在 (C′) 是右加 (`F-add`), 在 (A) 是上折 (`F-up`).
> 不陈述值 (值在 `YiOmCVal`). 不否定任何路线. 入口: `YiOmCFold`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOmCCheck where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (_+_; iter; next; cum; Ωt; ι; eqℕ-refl)
open import OCF.Lean.YiFreshLegal using (_⊢_◃_; Leg; LN)
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiPhiNegK using (InB; prE; brE; lemB; evc; Kept; kept-self)
open import OCF.Lean.YiUpBlock using (Dn; stop; down; Up; Upc)
import OCF.Lean.YiOmCIface as OI
import OCF.Lean.YiUpFold as A
import OCF.Lean.YiOmCConst as C
open import OCF.Lean.YiOmCFold
open import OCF.Lean.YiOmCLegal
```

## 接口实填

```agda
J2-lim : (g : ℕ → L) (ε : Ev (lim g)) (B : Base (lim g)) (n : ℕ) (j : L) (w : j ≤ g n) (β : Tr j)
  (x : Tr (lim g)) (y : Tr (g n))
  → ψs (lim g) ε B j (inl n w) β (up x n y)
  ≡ ψs (g n) (ε n) (dL g ε B n x) j w (ψs (lim g) ε B j (inl n w) β x) y
J2-lim g ε B n j w β x y rewrite eqℕ-refl n = refl

child-kept : (a b : L) (ea : Ev a) (eb : EvO a b) (B : Base (a ⊕ b)) (β : Tr a)
  {t : Pos (a ⊕ b)} (G : Br (a ⊕ b) t → Tr (a ⊕ b)) (i : InB a b t) (p : Pos a) → prE i eb ≡ inj₂ p
  → Kept p (ψs (a ⊕ b) (Ev⊕ a b ea eb) B a (self ∙ lift a b) β (Ω t G))
child-kept a b ea eb B β G i p e =
  subst (Kept p)
    (sym (lemB a b ea i eb self (λ q cv → Ω q (λ z → ψs (a ⊕ b) (Ev⊕ a b ea eb) B a (self ∙ lift a b) β (G (cv z)))) _))
    (kept-self a ea (prE i eb) p e (λ q cv z → ψs (a ⊕ b) (Ev⊕ a b ea eb) B a (self ∙ lift a b) β (G (brE i eb (cv z)))) _)

omI : OI.Iface
omI = record
  { ψ⊥ = ψ⊥
  ; ψs = ψs
  ; U  = Up′
  ; J2-suc  = λ a ε B j w β x y → refl
  ; J2-lim  = J2-lim
  ; J2-limu = λ g ε B j ws β x n y → refl
  ; J2-Ωk   = λ k h ε B j w β x c y → refl
  ; J2-Ωu   = λ k h ε B j ws β x c y → refl
  ; J2⊥-suc = λ a ε B x y → refl
  ; J2⊥-lim = λ g ε B x n y → refl
  ; J2⊥-Ω   = λ k h ε B x c y → refl
  ; mono⊥ = mono⊥
  ; monos = monos
  ; pres⊥ = pres⊥
  ; press = press
  ; tw-leg = twᶜ-leg
  ; EBO-leg = EBOᶜ-leg
  ; kstep = λ n B β x p g → refl
  ; self-suc = λ a ε B β x y → refl
  ; self-lim = λ g ε B β x n y → refl
  ; self-Ω = λ k h ε B β x c y → refl
  ; U-Ω = λ k h ε d b y c y′ → refl
  ; kall = λ n B β x c G i p e → child-kept (tw n) (↑ (tw n) c) (Ev-tw n) (evc n c) _ _ G i p e
  }
```

单调的前提在规范闭项上的实例: 塔各项与 Λ 的规范底, 以及链里出现的孩子的底.

```agda
nz-tw : (n : ℕ) → NZB (tw n) (B₀ (tw n))
nz-tw n = nzB₀ (tw n)

nz-Λ : NZB Λ (B₀ Λ)
nz-Λ = nzB₀ Λ

nz-child : (n : ℕ) (c : Tr (tw n)) (x : Tr (tw (suc n)))
  → NZB (tw n ⊕ ↑ (tw n) c) (dW (tw n) (λ c → tw n ⊕ ↑ (tw n) c) (Ev-tw (suc n)) (B₀ (tw (suc n))) c x)
nz-child n c x = nzW (tw n) (λ c → tw n ⊕ ↑ (tw n) c) (Ev-tw (suc n)) (B₀ (tw (suc n))) (nzB₀ (tw (suc n))) c x
```

## 自身行的两条读法 (编译定理)

Ω 结点层号上, 自身行的输出是 x 的折叠右加一棵嵌入的孩子树: 左边与孩子部分只是相加.
x = 0 时孩子的底记录与当前目标的底都直接取自 B.

```agda
self-add : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (B : Base (Ωₗ k h)) (β x : Tr (Ωₗ k h)) (c : Tr k) (y : Tr (h c))
  → ψs (Ωₗ k h) ε B (Ωₗ k h) self β (up x c y)
  ≡ ψs (Ωₗ k h) ε B (Ωₗ k h) self β x + up zero c (kid k h ε B c x y)
self-add k h ε B β x c y = refl

kid-zero : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (B : Base (Ωₗ k h)) (c : Tr k) (y : Tr (h c))
  → kid k h ε B c zero y
  ≡ ψs (h c) (proj₂ (proj₂ ε c)) (base (b⊥ B) (λ j w → bs B j (inb c w))) (h c) self (bs B (h c) (inb c self)) y
kid-zero k h ε B c y = refl
```

## 同支保留 (有限测试)

配置取自 `YiUpNegFlat` 的 omD: 孩子层 two 里的结点 P (槽位在 one) 套着结点 nodeC (槽位在第 0 层).

```agda
IsΩ : ∀ {P B C D} → T P B C D → Set
IsΩ (Ω _ _) = ⊤
IsΩ _       = ⊥

one two : L
one = suc zero
two = suc one

c₂ : Tr zero
c₂ = suc (suc zero)

ε₁ : Ev (tw 1)
ε₁ = Ev-tw 1

h₁ : Tr zero → L
h₁ c = zero ⊕ ↑ zero c

nodeC : (Tr zero → Tr two) → Tr two
nodeC G = Ω (inj₂ (inj₁ tt)) G

P : (Tr one → Tr zero → Tr two) → Tr two
P G = Ω (inj₁ tt) (λ z → nodeC (G z))

P-kept : (B : Base (tw 1)) (β x : Tr (tw 1)) (G : Tr one → Tr zero → Tr two) →
  ψs (tw 1) ε₁ B (tw 1) self β (up x c₂ (P G))
  ≡ up (ψs (tw 1) ε₁ B (tw 1) self β x) c₂
       (Ω (inj₁ tt) (λ z → Ω (inj₂ (inj₁ tt)) (λ z′ → kid zero h₁ ε₁ B c₂ x (G z z′))))
P-kept B β x G = refl

P-down : (B : Base (tw 1)) (β x : Tr (tw 1)) (G : Tr one → Tr zero → Tr two) →
  ψ⊥ (tw 1) ε₁ B (ψs (tw 1) ε₁ B (tw 1) self β (up x c₂ (P G)))
  ≡ ψ⊥ two tt (dW zero h₁ ε₁ B c₂ (ψs (tw 1) ε₁ B (tw 1) self β x)) (kid zero h₁ ε₁ B c₂ x (P G))
P-down B β x G = refl

omD : (B : Base (tw 1)) (x : Tr (tw 1)) (B′ : Base two) (β′ : Tr one) (G : Tr zero → Tr two) →
  IsΩ (ψs two tt B′ one (ins self) β′ (kid zero h₁ ε₁ B c₂ x (nodeC G)))
omD B x B′ β′ G = tt

deep : (B : Base (suc (tw 1))) (β X : Tr (suc (tw 1))) (x : Tr (tw 1)) (G : Tr one → Tr zero → Tr two) →
  ψs (suc (tw 1)) ε₁ B (suc (tw 1)) self β (up X tt (up x c₂ (P G)))
  ≡ up (Up′ (tw 1) ε₁ (down stop tt) (ψs (suc (tw 1)) ε₁ B (suc (tw 1)) self β X) x) tt
       (up zero c₂ (kid zero h₁ ε₁ (B₀ (tw 1)) c₂ x (P G)))
deep B β X x G = refl
```

没有改的一行: 在 tw 1 层直接以分支侧目标折嵌入分支, 仍回退 (与 `YiUpFold` 同一行).

```agda
fallback : (B : Base (tw 1)) (β : Tr one) (X : Tr (tw 1)) (G : Tr zero → Tr two) →
  ψs (tw 1) ε₁ B one (inb c₂ (ins self)) β (up X c₂ (nodeC G))
  ≡ ψs (tw 1) ε₁ B one (inb c₂ (ins self)) β X + ι one (ψ⊥ two tt (B₀ two) (nodeC G))
fallback B β X G = refl
```

## 塔第 2 项链第一步 (有限测试)

目标 tw 1, 路径 `ink self`. 三个折叠在同一输入上: (A) `YiUpFold`, (C) `YiOmCConst`, (C′) 本线.

```agda
ε₂ : Ev (tw 2)
ε₂ = Ev-tw 2

β₁ : Tr (tw 1)
β₁ = Ωt (tw 1)

stepA stepC stepC′ : Tr (tw 1) → Tr (tw 1)
stepA  c = A.ψs (tw 2) ε₂ (B₀ (tw 2)) (tw 1) (ink self) β₁ (up zero c (Ωt (tw 1 ⊕ ↑ (tw 1) c)))
stepC  c = C.ψs (tw 2) ε₂ (B₀ (tw 2)) (tw 1) (ink self) β₁ (up zero c (Ωt (tw 1 ⊕ ↑ (tw 1) c)))
stepC′ c = ψs   (tw 2) ε₂ (B₀ (tw 2)) (tw 1) (ink self) β₁ (up zero c (Ωt (tw 1 ⊕ ↑ (tw 1) c)))
```

(C′) 的第一步: 结点保留, 第 c 支是 β₁ 右加孩子 c 里的一棵树; 孩子的底化成常量 `Ωt (h₁ c)`, 底记录化成 `B₀`.
也就是 (C) 的公式, 只是折叠换成 (C′) 自己: 这一步上 x = 0, 底是规范底, 依赖 x 的底没有带进新的东西.

```agda
step1 : stepC′ zero
  ≡ Ω (inj₁ (inj₁ tt)) (λ c → up β₁ c
      (ψs (h₁ c) (proj₂ (proj₂ ε₁ c)) (B₀ (h₁ c)) (h₁ c) self (Ωt (h₁ c)) (Ωt (h₁ c))))
step1 = refl

step1-C : stepC zero ≡ Ω (inj₁ (inj₁ tt)) (λ c → up β₁ c (C.selfC (h₁ c) (proj₂ (proj₂ ε₁ c)) (Ωt (h₁ c))))
step1-C = refl

step1-A : stepA zero ≡ Ω (inj₁ (inj₁ tt)) (λ c → Up (h₁ c) (down stop c) β₁ (Ωt (h₁ c)))
step1-A = refl
```

第 0 支: (C′) 与 (C) 逐字相同, (A) 是 `next β₁`. 第 1 支 (孩子层 one): (C′) 与 (C) 的结点留在孩子里, 形状相同; (A) 的结点进了 tw 1 的槽位.

```agda
br : Tr (tw 1) → Tr zero → Tr (tw 1)
br (Ω (inj₁ (inj₁ tt)) g) c = g c
br _ _ = zero

br0-C′ : br (stepC′ zero) zero ≡ up β₁ zero (next (suc zero))
br0-C′ = refl

br0-same : br (stepC′ zero) zero ≡ br (stepC zero) zero
br0-same = refl

br0-A : br (stepA zero) zero ≡ next β₁
br0-A = refl

br1-A : IsΩ (br (stepA zero) (suc zero))
br1-A = tt

br1-C′ : br (stepC′ zero) (suc zero)
  ≡ up β₁ (suc zero) (Ω (inj₁ tt) (λ c → next (Up′ zero tt (down stop tt) (Ωt one) c)))
br1-C′ = refl

br1-C : br (stepC zero) (suc zero)
  ≡ up β₁ (suc zero) (Ω (inj₁ tt) (λ c → next (C.Up′ zero tt (down stop tt) (Ωt one) c)))
br1-C = refl
```

x 非零时 (C′) 与 (C) 不同: 孩子的底是 x 折进孩子层的值.

```agda
differ-C′ : (β : Tr (tw 1)) →
  ψs (tw 1) ε₁ (B₀ (tw 1)) (tw 1) self β (up (suc zero) zero (suc zero))
  ≡ up (next β) zero (next (next (suc zero)))
differ-C′ β = refl

differ-C : (β : Tr (tw 1)) →
  C.ψs (tw 1) ε₁ (B₀ (tw 1)) (tw 1) self β (up (suc zero) zero (suc zero))
  ≡ up (next β) zero (next (suc zero))
differ-C β = refl
```

## 层号 tw 1 + 1 的链: 自身折叠对右加 β₁ (编译定理, `refl`)

层号 `suc (tw 1)` 的 Ω 树折到第 0 层, 链点是 `z (k+1) = next (F (z k))`, F 是 tw 1 层折到自身 (`form-suc`; 与 `YiUpVal.At.form` 同形, 两个折叠同一式).
`x + β₁` 是顶槽位的结点, 第 c 支是 `up x c (Ωt (h₁ c))`. (C′): F 的输出是 `F x` 右加一棵同形的树, 各孩子的内容仍在孩子层里 (`F-add`).
(A): 第 c 支是孩子的 Ω 树上折进 tw 1, 底是 `F x` (`F-up`).

```agda
module Suc (B₂ : Base (suc (tw 1))) where
  Bᵃ : Base (tw 1)
  Bᵃ = dS (tw 1) ε₁ B₂ zero

  βt : Tr (tw 1)
  βt = bs B₂ (tw 1) (ins self)

  F : Tr (tw 1) → Tr (tw 1)
  F t = ψs (tw 1) ε₁ Bᵃ (tw 1) self βt t

  z : ℕ → Tr (tw 1)
  z = iter (λ c → next (F c)) zero

  form-suc : ψ⊥ (suc (tw 1)) ε₁ B₂ (Ωt (suc (tw 1))) ≡ lim (cum (λ k → next (ψ⊥ (tw 1) ε₁ Bᵃ (z k))))
  form-suc = refl

  F-add : (x : Tr (tw 1)) →
    F (x + β₁) ≡ F x + Ω (inj₁ (inj₁ tt)) (λ c → up zero c (kid zero h₁ ε₁ Bᵃ c x (Ωt (h₁ c))))
  F-add x = refl

  F-next : (x : Tr (tw 1)) → F (next x) ≡ lim (λ n → F (iter (x +_) x n))
  F-next x = refl

module SucA (B₂ : Base (suc (tw 1))) where
  Bᵃ : Base (tw 1)
  Bᵃ = base (A.ψ⊥ (suc (tw 1)) ε₁ B₂ zero) (λ j w → A.ψs (suc (tw 1)) ε₁ B₂ j (ins w) (bs B₂ j (ins w)) zero)

  βt : Tr (tw 1)
  βt = bs B₂ (tw 1) (ins self)

  F : Tr (tw 1) → Tr (tw 1)
  F t = A.ψs (tw 1) ε₁ Bᵃ (tw 1) self βt t

  z : ℕ → Tr (tw 1)
  z = iter (λ c → next (F c)) zero

  form-suc : A.ψ⊥ (suc (tw 1)) ε₁ B₂ (Ωt (suc (tw 1))) ≡ lim (cum (λ k → next (A.ψ⊥ (tw 1) ε₁ Bᵃ (z k))))
  form-suc = refl

  F-up : (x : Tr (tw 1)) →
    F (x + β₁) ≡ Ω (inj₁ (inj₁ tt)) (λ c → Up (h₁ c) (down stop c) (F x) (Ωt (h₁ c)))
  F-up x = refl
```
