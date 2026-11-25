# 折叠带证据 (F1 原型): 律, 决定性测试, 暴露的两个问题

> 验收文件. 编译定理: J2 各律带证据后仍是 `refl` (`J2⊥-Ω` 等), 孩子层的路线取自下标的证据; 塔各项与 Λ 的闭项带证据且非零; 保留行的分支取 `E₀` (`keep-self`); 折叠的输出随下标的合法性证明而变 (`dep`); 保留行要的 "分支处处合法" 对塔第 1 项的 Ω 树为假 (`no-keep`).
> 有限测试: ω+1 那一层孩子的底, 路线由折叠从下标的证据取时是结点 (`bω-fl`), 取平凡证据时是极限 (`bω-0`); 真链第 1 步的值带相邻序, 第 2 步的值不带 (`ch1-route`, `ch2-route`); 与 `YiLimFold` 的回归 2 条.
> 不否定什么. `dep` 的两个证明都是合法性的证明, 它说的是 "单调性不能对两边各自独立的证据陈述", 不是路线走不通.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFLCheck where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (_+_; iter; next; cum; Ωt; ι)
open import OCF.Lean.YiFreshLegal using (_⊢_◃_; ◃s; ◃l; ◃t; Ωt-nz)
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiUpBlock
open import OCF.Lean.YiLimBlock
import OCF.Lean.YiLimFold as LF
open import OCF.Lean.YiLimLegal using (◃→⊑)
open import OCF.Lean.YiLimCheck using
  (ω₀; gω; εω; preω; one; two; Fo; cut₀; cut₁; gL; εL; rL; ρL; pA; pB; x₀₁; nodeL; badf; bad)
open import OCF.Lean.YiFLBlock
open import OCF.Lean.YiFLLegal
open import OCF.Lean.YiFLFold

isLim isΩ : ∀ {P B C D} → T P B C D → Set
isLim (lim _) = ⊤
isLim _       = ⊥
isΩ (Ω _ _) = ⊤
isΩ _       = ⊥

isJ isN : {A : Set} → Maybe A → Set
isJ (just _) = ⊤
isJ nothing  = ⊥
isN (just _) = ⊥
isN nothing  = ⊤
```

## J2 各律 (带证据)

孩子的底连同它的证据. 律的右边: 孩子层的折叠, 路线是 `proj₂ ρ c ec`, 其中 ec 是 `up x c y` 的证据里下标 c 的那一份.

```agda
dS : (a : L) (ε : Ev (suc a)) (ρ : Rt′ (suc a)) → Bs (suc a) → (x : Tr (suc a)) → E (suc a) x → Bs a
dS a ε ρ B x ex =
  base (ψ⊥ (suc a) ε ρ B x ex) (λ j w → ψs (suc a) ε ρ B j (ins w) (bs⁺ B j (ins w)) x ex)
  , pres⊥ (suc a) ε ρ B x ex , λ j w → press (suc a) ε ρ B j (ins w) (bs⁺ B j (ins w)) x ex

dL : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt′ (lim g)) → Bs (lim g) → (n : ℕ) (x : Tr (lim g)) → E (lim g) x → Bs (g n)
dL g ε ρ B n x ex =
  base (ψ⊥ (lim g) ε ρ B x ex) (λ j w → ψs (lim g) ε ρ B j (inl n w) (bs⁺ B j (inl n w)) x ex)
  , pres⊥ (lim g) ε ρ B x ex , λ j w → press (lim g) ε ρ B j (inl n w) (bs⁺ B j (inl n w)) x ex

dW : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt′ (Ωₗ k h)) → Bs (Ωₗ k h) → (c : Tr k)
  (x : Tr (Ωₗ k h)) → E (Ωₗ k h) x → Bs (h c)
dW k h ε ρ B c x ex =
  base (ψ⊥ (Ωₗ k h) ε ρ B x ex) (λ j w → ψs (Ωₗ k h) ε ρ B j (inb c w) (bs⁺ B j (inb c w)) x ex)
  , pres⊥ (Ωₗ k h) ε ρ B x ex , λ j w → press (Ωₗ k h) ε ρ B j (inb c w) (bs⁺ B j (inb c w)) x ex

J2⊥-Ω : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt′ (Ωₗ k h)) (B : Bs (Ωₗ k h))
  (x : Tr (Ωₗ k h)) (c : Tr k) (y : Tr (h c)) (ex : E (Ωₗ k h) x) (ec : E k c) (ey : E (h c) y)
  → ψ⊥ (Ωₗ k h) ε ρ B (up x c y) (ex , ec , ey)
  ≡ ψ⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c ec) (dW k h ε ρ B c x ex) y ey
J2⊥-Ω k h ε ρ B x c y ex ec ey = refl

J2-Ωk : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt′ (Ωₗ k h)) (B : Bs (Ωₗ k h)) (j : L) (w : j ≤ k)
  (β : T⁺ j) (x : Tr (Ωₗ k h)) (c : Tr k) (y : Tr (h c)) (ex : E (Ωₗ k h) x) (ec : E k c) (ey : E (h c) y)
  → ψs (Ωₗ k h) ε ρ B j (ink w) β (up x c y) (ex , ec , ey)
  ≡ ψs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c ec) (dW k h ε ρ B c x ex) j (w ∙ proj₁ (proj₂ ε c))
      (ψs (Ωₗ k h) ε ρ B j (ink w) β x ex , press (Ωₗ k h) ε ρ B j (ink w) β x ex) y ey
J2-Ωk k h ε ρ B j w β x c y ex ec ey = refl

J2-Ωu : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt′ (Ωₗ k h)) (B : Bs (Ωₗ k h)) (j : L)
  (ws : (c : Tr k) → j ≤ h c)
  (β : T⁺ j) (x : Tr (Ωₗ k h)) (c : Tr k) (y : Tr (h c)) (ex : E (Ωₗ k h) x) (ec : E k c) (ey : E (h c) y)
  → ψs (Ωₗ k h) ε ρ B j (inu ws) β (up x c y) (ex , ec , ey)
  ≡ ψs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c ec) (dW k h ε ρ B c x ex) j (ws c)
      (ψs (Ωₗ k h) ε ρ B j (inu ws) β x ex , press (Ωₗ k h) ε ρ B j (inu ws) β x ex) y ey
J2-Ωu k h ε ρ B j ws β x c y ex ec ey = refl

J2-suc : (a : L) (ε : Ev (suc a)) (ρ : Rt′ (suc a)) (B : Bs (suc a)) (j : L) (w : j ≤ a)
  (β : T⁺ j) (x : Tr (suc a)) (y : Tr a) (ex : E (suc a) x) (ey : E a y)
  → ψs (suc a) ε ρ B j (ins w) β (up x tt y) (ex , tt , ey)
  ≡ ψs a ε ρ (dS a ε ρ B x ex) j w
      (ψs (suc a) ε ρ B j (ins w) β x ex , press (suc a) ε ρ B j (ins w) β x ex) y ey
J2-suc a ε ρ B j w β x y ex ey = refl

J2-lim : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt′ (lim g)) (B : Bs (lim g)) (n : ℕ) (j : L) (w : j ≤ g n)
  (β : T⁺ j) (x : Tr (lim g)) (y : Tr (g n)) (ex : E (lim g) x) (ey : E (g n) y)
  → ψs (lim g) ε ρ B j (inl n w) β (up x n y) (ex , tt , ey)
  ≡ ψs (g n) (ε n) (proj₁ ρ n) (dL g ε ρ B n x ex) j w
      (ψs (lim g) ε ρ B j (inl n w) β x ex , press (lim g) ε ρ B j (inl n w) β x ex) y ey
J2-lim g ε ρ B n j w β x y ex ey rewrite way-refl g (proj₂ ρ) n = refl

J2-limu : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt′ (lim g)) (B : Bs (lim g)) (j : L) (ws : (n : ℕ) → j ≤ g n)
  (β : T⁺ j) (x : Tr (lim g)) (n : ℕ) (y : Tr (g n)) (ex : E (lim g) x) (ey : E (g n) y)
  → ψs (lim g) ε ρ B j (inlu ws) β (up x n y) (ex , tt , ey)
  ≡ ψs (g n) (ε n) (proj₁ ρ n) (dL g ε ρ B n x ex) j (ws n)
      (ψs (lim g) ε ρ B j (inlu ws) β x ex , press (lim g) ε ρ B j (inlu ws) β x ex) y ey
J2-limu g ε ρ B j ws β x n y ex ey = refl

self-up : (ℓ : L) (ε : Ev ℓ) (ρ : Rt′ ℓ) (B : Bs ℓ) (β : T⁺ ℓ) (x : Tr ℓ) (c : Ch ℓ) (y : ChT ℓ c)
  (e : E ℓ (up x c y))
  → ψs ℓ ε ρ B ℓ self β (up x c y) e ≡ Upc ℓ c (ψs ℓ ε ρ B ℓ self β x (proj₁ e)) y
self-up ℓ ε ρ B β x c y e = refl
```

保留行: 目标是本层时结点保留, 分支 z 是裸的, 分支的值用平凡证据 `EBr₀` 取出来折叠.

```agda
keep-self : (ℓ : L) (ε : Ev ℓ) (ρ : Rt′ ℓ) (B : Bs ℓ) (β : T⁺ ℓ) (p : Pos ℓ) (g : Br ℓ p → Tr ℓ)
  (e : E ℓ (Ω p g))
  → ψs ℓ ε ρ B ℓ self β (Ω p g) e
  ≡ Ω p (λ z → ψs ℓ ε ρ B ℓ self β (g z) (proj₂ e z (EBr₀ ℓ p z)))
keep-self ℓ ε ρ B β p g e = refl
```

## 闭项 (带证据且非零)

```agda
twᶜ : ℕ → Tr zero
twᶜ n = ψ₀ (tw n) (Ev-tw n) (Rt′-tw n) (Ωt (tw n)) (Ωt-E (tw n))

twᶜ-EN : (n : ℕ) → EN zero (twᶜ n)
twᶜ-EN n = pres⊥ (tw n) (Ev-tw n) (Rt′-tw n) (B₀⁺ (tw n)) (Ωt (tw n)) (Ωt-E (tw n))

EBOᶜ : Tr zero
EBOᶜ = ψ₀ Λ Ev-Λ Rt′-Λ (Ωt Λ) (Ωt-E Λ)

EBOᶜ-EN : EN zero EBOᶜ
EBOᶜ-EN = pres⊥ Λ Ev-Λ Rt′-Λ (B₀⁺ Λ) (Ωt Λ) (Ωt-E Λ)
```

## 决定性测试: ω+1 那一层

下标 c = ω+1 (`suc ω₀`) 的证据来自它的合法性 (`le₀`). 塔第 1 项对这个下标给的孩子层路线带相邻路径 (`fl-adj`); 对照 `YiLimCheck.tw1-none-all` (旧路线对一切 ℕ 极限给 `nothing`).
孩子的底 (前缀里孩子 1 的 Ω 树对 "孩子 2 里的第 1 层" 的折叠) 这时是结点; 下标取平凡证据时是极限.

```agda
ω₀-leg′ : Leg′ zero ω₀
ω₀-leg′ = hf , λ n → ◃s
  where
  hf : (n : ℕ) → Leg′ zero (iter suc zero n)
  hf zero    = tt
  hf (suc n) = hf n

eω : E zero (suc ω₀)
eω = le₀ (suc ω₀) ω₀-leg′

ρω-fl ρω-0 : Rt′ (lim gω)
ρω-fl = proj₂ (Rt′-tw 1) (suc ω₀) eω
ρω-0  = proj₂ (Rt′-tw 1) (suc ω₀) (E₀ zero (suc ω₀))

fl-adj : proj₂ ρω-fl ≡ just (λ n → ins self)
fl-adj = refl

fl-0 : proj₂ ρω-0 ≡ nothing
fl-0 = refl

βone : T⁺ one
βone = Ωt one , Ωt-E one , Ωt-nz one

bω-fl : isΩ (ψs (lim gω) εω ρω-fl (B₀⁺ (lim gω)) one (inl 2 (ins self)) βone preω (E₀ (lim gω) preω))
bω-fl = tt

bω-0 : isLim (ψs (lim gω) εω ρω-0 (B₀⁺ (lim gω)) one (inl 2 (ins self)) βone preω (E₀ (lim gω) preω))
bω-0 = tt
```

从塔第 1 项出发: 嵌入 `up x (suc ω₀) y` 的折叠交给孩子层, 用的路线就是 `ρω-fl` (`J2⊥-Ω` 的实例).

```agda
tw1-ω+1 : (B : Bs (tw 1)) (x : Tr (tw 1)) (y : Tr (suc (lim gω))) (ex : E (tw 1) x) (ey : E (suc (lim gω)) y)
  → ψ⊥ (tw 1) (Ev-tw 1) (Rt′-tw 1) B (up x (suc ω₀) y) (ex , eω , ey)
  ≡ ψ⊥ (suc (lim gω)) εω ρω-fl (dW zero (λ c → zero ⊕ ↑ zero c) (Ev-tw 1) (Rt′-tw 1) B (suc ω₀) x ex) y ey
tw1-ω+1 B x y ex ey = refl
```

## 真链上的两步

塔第 1 项的 Ω 树 `Ω _ (λ c → up zero c (Ωt (h c)))` 折到第 0 层时的链步, 分支连同证据一起走.
第 1 步的值是 `next` 出来的极限, 带相邻序, 它作下标时孩子层有路径. 第 2 步的值是对孩子层的 Ω 树 (ℕ 极限) 逐项折叠出来的极限, 不带相邻序, 它作下标时孩子层没有路径.

```agda
h₁ : Tr zero → L
h₁ c = zero ⊕ ↑ zero c

st : Σ (Tr zero) (E zero) → Σ (Tr zero) (E zero)
st z =
  ψs (tw 1) (Ev-tw 1) (Rt′-tw 1) (B₀⁺ (tw 1)) zero (ink self) (bs⁺ (B₀⁺ (tw 1)) zero (ink self))
    (up zero (proj₁ z) (Ωt (h₁ (proj₁ z)))) (tt , proj₂ z , Ωt-E (h₁ (proj₁ z)))
  , proj₁ (press (tw 1) (Ev-tw 1) (Rt′-tw 1) (B₀⁺ (tw 1)) zero (ink self) (bs⁺ (B₀⁺ (tw 1)) zero (ink self))
    (up zero (proj₁ z) (Ωt (h₁ (proj₁ z)))) (tt , proj₂ z , Ωt-E (h₁ (proj₁ z))))

z₁ z₂ : Σ (Tr zero) (E zero)
z₁ = st (zero , tt)
z₂ = st z₁

ch1-lim : isLim (proj₁ z₁)
ch1-lim = tt

ch1-route : isJ (proj₂ (proj₂ (Rt′-tw 1) (proj₁ z₁) (proj₂ z₁)))
ch1-route = tt

ch2-lim : isLim (proj₁ z₂)
ch2-lim = tt

ch2-route : isN (proj₂ (proj₂ (Rt′-tw 1) (proj₁ z₂) (proj₂ z₂)))
ch2-route = tt
```

## 暴露的问题 (一): 折叠的输出随合法性证明而变

下标 c = lim (1, ω, ω+1, …) 合法, 相邻的第一步 1 ◃ ω 有两个推导: 经 ω 的第 1 项, 或先到 2 再经 ω 的第 2 项. 两个合法性证明给出两条不同的相邻路径.
孩子 0 里的结点对 "孩子 1 整层" 的折叠: 槽位沿这条路径搬进孩子 1, 落在不同的编号上, 输出是两棵不同的树.
所以 "x ◃ y 蕴含折叠值 ◃" 不能对两边各自任取的证据陈述 (`x ◃ suc x` 的两边就是同一棵树的两份证据); 要陈述单调, 先要有证据之间的相干关系.

```agda
fd : ℕ → Tr zero
fd zero          = suc zero
fd (suc zero)    = ω₀
fd (suc (suc n)) = suc (fd (suc n))

hfd : (n : ℕ) → Leg′ zero (fd n)
hfd zero          = tt
hfd (suc zero)    = ω₀-leg′
hfd (suc (suc n)) = hfd (suc n)

a₁ a₂ : (n : ℕ) → zero ⊢ fd n ◃ fd (suc n)
a₁ zero    = ◃l 1
a₁ (suc n) = ◃s
a₂ zero    = ◃t ◃s (◃l 2)
a₂ (suc n) = ◃s

cd : Tr zero
cd = lim fd

l₁ l₂ : Leg′ zero cd
l₁ = hfd , a₁
l₂ = hfd , a₂

gd : ℕ → L
gd n = zero ⊕ ↑ zero (fd n)

εd : Ev (lim gd)
εd = proj₂ (proj₂ (Ev-tw 1) cd)

ρd : Leg′ zero cd → Rt′ (lim gd)
ρd l = proj₂ (Rt′-tw 1) cd (le₀ cd l)

Nd : Tr (lim gd)
Nd = Ω (0 , inj₁ tt) (λ _ → zero)

outd : Leg′ zero cd → Tr (lim gω)
outd l = ψs (lim gd) εd (ρd l) (B₀⁺ (lim gd)) (lim gω) (inl 1 self)
           (Ωt (lim gω) , Ωt-E (lim gω) , Ωt-nz (lim gω)) Nd (tt , λ z ez → tt)

slotN : Tr (lim gω) → Maybe ℕ
slotN (Ω (m , _) _) = just m
slotN _             = nothing

dep₁ : slotN (outd l₁) ≡ just 1
dep₁ = refl

dep₂ : slotN (outd l₂) ≡ just 2
dep₂ = refl

1≢2 : just 1 ≡ just 2 → ⊥
1≢2 ()

dep : outd l₁ ≡ outd l₂ → ⊥
dep q = 1≢2 (trans (sym dep₁) (trans (cong slotN q) dep₂))
```

## 暴露的问题 (二): 保留行的分支没有合法性可用

保留行的输出 `Ω q (λ z → …)` 对裸的分支 z 全定义. 若折叠的参数是 `Leg′`, 这一行要对一切 z 给出分支的值的合法性; 对塔第 1 项的 Ω 树这是假的 (分支的值把 z 作下标嵌入, 而 z 可以不合法).
所以折叠带的只能是可选的证据, 保留行里取 `E₀` (`keep-self`): 以保留结点的分支为下标的孩子层仍没有路径.

```agda
¬s⊑z : ∀ {a} → suc a ⊑ zero → ⊥
¬s⊑z ()

no-keep : ((z : Tr zero) → Leg′ (tw 1) (up zero z (Ωt (h₁ z)))) → ⊥
no-keep H = ¬s⊑z (◃→⊑ (proj₂ (proj₁ (proj₂ (H bad))) zero))

keep-none : (f : ℕ → Tr zero) → proj₂ (EBr₀ (tw 1) (inj₁ (inj₁ tt)) (lim f)) ≡ nothing
keep-none f = refl
```

## 回归: 证据平凡时与 `YiLimFold` 相同 (有限测试)

层号 `lim gL` 带相邻路径, 证据取 `E₀`; 比深度 4 的截断 (两个折叠是不同的互递归定义).

```agda
rc′ : (n : ℕ) → Rt′ (gL n)
rc′ zero    = tt
rc′ (suc n) = rc′ n

ρL′ : Rt′ (lim gL)
ρL′ = rc′ , just rL

reg-up : cut₁ 4 (ψs (lim gL) εL ρL′ (B₀⁺ _) one pB βone x₀₁ (E₀ _ x₀₁))
       ≡ cut₁ 4 (LF.ψs (lim gL) εL ρL (B₀ _) one pB (Ωt one) x₀₁)
reg-up = refl

reg-node : cut₁ 4 (ψs (lim gL) εL ρL′ (B₀⁺ _) one pB βone (nodeL (λ c → up zero 0 (Ωt one))) (E₀ _ _))
         ≡ cut₁ 4 (LF.ψs (lim gL) εL ρL (B₀ _) one pB (Ωt one) (nodeL (λ c → up zero 0 (Ωt one))))
reg-node = refl
```
