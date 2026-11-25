# 甲脚手架审查：标准形封闭的定义域与零起步链

这是交接 S1 的配对审查，读记号，不进成品。结论限于码层：
“输入码为标准形”不足以直接再包一层 ψ；但零起步与记号链的起点不同，
本身也不构成失败。这里不声称实际 T甲 已被否定。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaAuditClosure where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (proj₁)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; sym; trans)
open import OCF.Align.EboLeanDef
  using (T; ψ; Ωt; Ωs; sucT; pred; cof; c1; cΩ;
         _<ᵀ_; []<; fsT; fsT0; γT)
open import OCF.Align.EboLeanBase
  using (NF; n[]; nf-ψ; nf-Ω; nf-hd; nfp-g;
         InG; gp; gtl; gh; gw; gc; <→lt; noG-le)
open import OCF.Align.EboLean3Base using (nf-suc)
open import OCF.Align.EboLeanView using (ωr; γ-eq; VΩ; vΩ)
open import OCF.Align.EboLeanClosure using (tow)
open import OCF.Align.JiaBase using (Below; below)
```

## 直接再包 ψ 的限定反例

`a` 是 ψ₀(Ω)。零与 `a` 都有标准形证据；它们也都严格小于 Ω，
所以缺失的不是公共码上界。ψ₀(`a`) 的标准形却会要求 Ω < `a`。
这只否定 `NF i → NF b → NF (ψ i b)`，不否定带生成域或规范化的接口。

```agda
one omega a : T
one = Ωt []
omega = Ωs []
a = ψ [] omega ∷ []

G-one : ∀ {z} → InG [] z one → z ≡ []
G-one (gp (gh _)) = refl
G-one (gp (gw _ ()))
G-one (gp (gc _ ()))
G-one (gtl ())

G-omega : ∀ {z} → InG [] z omega → z ≡ []
G-omega (gp (gh _)) = refl
G-omega (gp (gw _ i)) = G-one i
G-omega (gp (gc _ ()))
G-omega (gtl ())

normal-a : NF a
normal-a = nf-ψ n[] (nf-Ω (nf-Ω n[]))
  (λ i → subst (_<ᵀ omega) (sym (G-omega i)) []<)

zero-below-omega : Below [] omega
zero-below-omega = below n[] []<

a-below-omega : Below a omega
a-below-omega = below normal-a (OCF.Align.EboLeanDef.hd<
  (OCF.Align.EboLeanDef.lv< []<))

omega-not-below-a : omega <ᵀ a → ⊥
omega-not-below-a p with <→lt p
... | ()

no-direct-repeat : NF (ψ [] a ∷ []) → ⊥
no-direct-repeat n = omega-not-below-a
  (nfp-g (nf-hd n) (gp (gh (inj₂ refl))))
```

## 零起步链与现成 γT 的接线

`fromZero` 只把 γT 的初项换成零，递推式不变。若原分支在零处给零，
那么删掉 `fromZero` 的初项后，逐项就是原 γT。这是对所有码与层号的
归纳定理，不是有限展开测试。前提有实例：正规 Ω 的分支是恒等。

```agda
fromZero : T → T → ℕ → T
fromZero B ν zero = []
fromZero B ν (suc n) = ψ ν (fsT B (fromZero B ν n)) ∷ []

shift : ∀ B ν → fsT B [] ≡ [] →
  ∀ n → fromZero B ν (suc n) ≡ γT B ν n
shift B ν e zero = cong (λ x → ψ ν x ∷ []) e
shift B ν e (suc n) =
  cong (λ x → ψ ν (fsT B x) ∷ []) (shift B ν e n)

regular-zero : fsT omega [] ≡ []
regular-zero = refl

regular-shift : ∀ n → fromZero omega [] (suc n) ≡ γT omega [] n
regular-shift = shift omega [] regular-zero

-- 在最小正规 Ω 实例上，现成 tow 确实填得上；不能以起点差异判失败。
regular-normal : ∀ n → NF (fromZero omega [] n)
regular-normal zero = n[]
regular-normal (suc n) = subst NF (sym (regular-shift n))
  (subst NF (sym (γ-eq (ωr refl) n))
    (proj₁ (tow normal-a (ωr refl) (inj₂ refl) n)))
```

现成 `cl-fsn-NF` 要求标准形父码及其 ω-共尾证据；`tow` 更要求
`NF (ψ A B ∷ [])`，其中已有 `GB A B B`。共享 `JiaBase.Tree` 只约束
Ω 结点的层号为标准形，不包含树本身的输出码或这条 `GB`。
因此仍须先给生成域的码树对应，再证明它随折叠与回灌生成。
本篇没有给出实际链点封闭失败，也没有达到 S1 的早期停点。

## 任意正规 Ω 层的零起步链都接得上码侧封闭

下面把最小实例推广到任意标准形层号。后继码新引入的 `G` 元素
除了原码已有的元素，只可能是零。因而父码 ψν(Ω_{ν+1}) 的标准形
不需要按层新增前提；ν 的标准形即可构造它。

```agda
G-suc-split : ∀ u ν {z} → InG u z (sucT ν) → InG u z ν ⊎ z ≡ []
G-suc-split u [] (gp (gh _)) = inj₂ refl
G-suc-split u [] (gp (gw _ ()))
G-suc-split u [] (gp (gc _ ()))
G-suc-split u [] (gtl ())
G-suc-split u (x ∷ xs) (gp p) = inj₁ (gp p)
G-suc-split u (x ∷ xs) (gtl p) with G-suc-split u xs p
... | inj₁ q = inj₁ (gtl q)
... | inj₂ e = inj₂ e

cof-suc : ∀ ν → cof (sucT ν) ≡ c1
cof-suc [] = refl
cof-suc (x ∷ []) = refl
cof-suc (x ∷ y ∷ ys) = cof-suc (y ∷ ys)

pred-suc : ∀ ν → pred (sucT ν) ≡ ν
pred-suc [] = refl
pred-suc (x ∷ []) = refl
pred-suc (x ∷ y ∷ ys) = cong (x ∷_) (pred-suc (y ∷ ys))

cof-regular : ∀ ν → cof (Ωs ν) ≡ cΩ ν
cof-regular [] = refl
cof-regular ν@(x ∷ xs) = trans
  (cong (OCF.Align.EboLeanDef.cofψ0 (sucT ν)) (cof-suc ν))
  (cong cΩ (pred-suc ν))

regular-view : ∀ ν → VΩ (Ωs ν) ν
regular-view ν = vΩ (Ωs ν) (cof-regular ν)

fs-regular : ∀ ν η → fsT (Ωs ν) η ≡ η
fs-regular [] η = refl
fs-regular ν@(x ∷ xs) η =
  cong (λ c → fsT0 (sucT ν) c η) (cof-suc ν)

parent-normal : ∀ {ν} → NF ν → NF (ψ ν (Ωs ν) ∷ [])
parent-normal {ν} nν = nf-ψ nν (nf-Ω (nf-suc nν)) guard
  where
  guard : ∀ {z} → InG ν z (Ωs ν) → z <ᵀ Ωs ν
  guard (gp (gh _)) = []<
  guard (gp (gw _ p)) with G-suc-split ν ν p
  ... | inj₁ q = ⊥-elim (noG-le nν (inj₂ refl) q)
  ... | inj₂ refl = []<
  guard (gp (gc _ ()))
  guard (gtl ())

all-regular-shift : ∀ ν n → fromZero (Ωs ν) ν (suc n) ≡ γT (Ωs ν) ν n
all-regular-shift ν = shift (Ωs ν) ν (fs-regular ν [])

all-regular-normal : ∀ {ν} → NF ν → ∀ n → NF (fromZero (Ωs ν) ν n)
all-regular-normal nν zero = n[]
all-regular-normal {ν} nν (suc n) = subst NF
  (sym (all-regular-shift ν n))
  (subst NF (sym (γ-eq (regular-view ν) n))
    (proj₁ (tow (parent-normal nν) (regular-view ν) (inj₂ refl) n)))
```

这仍是码层的封闭，不是新树的码树对应。首次 Ω 塔的奇异结点 Ω_Ω
会把分支坐标送进 Ω，零坐标的像为 Ω₀=1，所以它不满足上面的
`fsT B [] ≡ []` 前提。这不是路线否定；它精确标出必须描述
“低层分支坐标与输出码对应”的第一个塔结点。

```agda
singular : T
singular = Ωt omega

singular-zero : fsT singular [] ≡ one
singular-zero = refl

singular-not-zero : fsT singular [] ≡ [] → ⊥
singular-not-zero ()
```
