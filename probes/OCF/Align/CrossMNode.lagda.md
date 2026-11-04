# 跨段 (三): 绑定高度的节点

> 入口 [CrossM](CrossM.lagda.md). **判决: HOLDS (编译过, 无条件), 但节点在折叠之后的 `Z` 层, 不在数据树 `Q` 里, 见文末.**
>
> **节点.** `Node` 的分支 `br : Code → Z` 对 **一切码** 给出, 带上它的证书, 和一条跨段的单调性 `↑br`: $M$ 与 $M$ `ᶜ+ cs N` 上的两个分支可比. 折叠 `ν` 走一条链: $C_0=M_0$, $C_{n+1}=C_n$ `ᶜ+ cs` $\lceil$ 第 $n$ 个分支的值 $\rceil$. 这是回灌 (折叠的输出作下一个高度), 也是对角 ℕ-极限.
>
> **公共上界.** 比较的两个分支 $C_n$, $C_{n+1}$ 都落在 $C_{n+1}$ 这个字面的码里. 没有跨 $M$ 的全局比较: 只比较链上相邻两项, 公共上界由链自己写出. 所以 `no-tri-code`, `no-all-Ord`, `barrier` 的前提都不被要求 (下标类型没有变, `Code` 没有全局三歧, 也不需要).
>
> **闭包定理.** `Gν 𝒩 M₀ : Goodᴺ (νZ 𝒩 M₀)`: 对任何 `Node`, 任何起点, 一步给出; 不分 $M$, 不分阶段. 塔的实例 `𝒯` 在 [CrossMInst](CrossMInst.lagda.md): 分支是 `Tᵒ M 0`, 单调性由 `step≺` 给出.
>
> **为什么是累加链, 不是 $\lceil\cdot\rceil$ 本身.** `gc` (`ĉᴸ` 的证书) 的链点只记得上一个 $\eta$, 分支只能是 $\eta$ 的函数. 那样 $C_{n+1}=\lceil y_n\rceil$, 与 $C_n$ 没有字面的初始段关系, 单调性要跨段的值比较. `≼` 不能代替: `≼↛⊑` 说 Brouwer 序不推出 `Goodᴺ` 要的结构序 $\sqsubseteq^0$. 这条只否定那个证明办法, 不否定 `gc` 路线本身.
>
> **定点 (定理, `Fix`).** 第 $n$ 个分支的层号 $\preceq\lVert C_{n+1}\rVert$ (`feed-up`), $\lVert C_n\rVert\preceq$ 第 $n$ 个分支的层号 (`feed-dn`), 所以输出的层号与高度互相共尾 (`cof-out`, `cof-ht`): 输出就是 "高度 $\mapsto$ 第 0 行的值" 沿这条链的闭包点. 对任何带 `val≼` 的节点; 塔的 `val≼` 是 [CrossMInst](CrossMInst.lagda.md) 的 `val≼T`.
>
> **闭项.** `T⊤`, `fgh⊤`, 无参数, 见 [CrossMClosed](CrossMClosed.lagda.md).
>
> **节点不在 `Q` 里.** `Q` 的折叠 `Ψ` 没有经过 `ν`; 只有第 0 行的计值之后才有这个节点. 所以 $\psi_0(\Omega_{\psi_1(\Omega)+1})$ 这种要把 $\Omega_{\psi_1(\Omega)}$ 当作被折叠对象的树, 这里没有. 见 [CrossM](CrossM.lagda.md) 的第一个障碍.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CrossMNode where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import OCF.Free.Level hiding (up)
open import OCF.Free.Prefix using (Z)
open import OCF.Free.Force using (Goodᴺ; gl; forceᴺ; forceᴺ-HS)
open import OCF.Free.Class using (lvG)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode
open import OCF.Align.LadderOrdStr using (≺→s≼; ≺→≼; plus-mono; Sb-mono)
```

## §1 结构序

```agda
≺-trans : ∀ {ℓ₁ ℓ₂ ℓ₃} {c : Ordᶜ ℓ₁} {a : Ordᶜ ℓ₂} {b : Ordᶜ ℓ₃} → c ≺ a → a ≺ b → c ≺ b
≺-trans h (≺z e) = ≺s (≺-respʳ h e)
≺-trans h (≺s r) = ≺s (≺-trans h r)
≺-trans h (≺l n r) = ≺l n (≺-trans h r)
≺-trans h (≺i x ex r) = ≺i x ex (≺-trans h r)
≺-trans h (≺u r) = ≺u (≺-trans h r)

≺→⊑ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≺ b → a ⊑ b
≺→⊑ r h = ≺-trans h r
```

## §2 节点与它的折叠

```agda
record Node : Set where
  constructor node
  field
    br  : Code → Z
    Gbr : ∀ M → Goodᴺ (br M)
    ↑br : ∀ M N → forceᴺ _ (Gbr M) ⊑⁰ forceᴺ _ (Gbr (M ᶜ+ cs N))
open Node public

-- 分支的值和它的层号
yv : (𝒩 : Node) → Code → Ordᶜ zero
yv 𝒩 M = forceᴺ _ (Gbr 𝒩 M)

ly : (𝒩 : Node) → Code → Ordᴵ
ly 𝒩 M = lvG (Gbr 𝒩 M)

-- 累加链: 下一个高度把上一个输出接在上面
C : (𝒩 : Node) → Code → ℕ → Code
C 𝒩 M₀ zero = M₀
C 𝒩 M₀ (suc n) = C 𝒩 M₀ n ᶜ+ cs ⌈ ly 𝒩 (C 𝒩 M₀ n) ⌉

νZ : Node → Code → Z
νZ 𝒩 M₀ = Z.lim (λ n → br 𝒩 (C 𝒩 M₀ n))

-- 闭包定理: 对任何节点, 任何起点
Gν : (𝒩 : Node) (M₀ : Code) → Goodᴺ (νZ 𝒩 M₀)
Gν 𝒩 M₀ = gl (λ n → Gbr 𝒩 (C 𝒩 M₀ n)) (λ n → ↑br 𝒩 (C 𝒩 M₀ n) _)

νT : Node → Code → Ordᶜ zero
νT 𝒩 M₀ = forceᴺ _ (Gν 𝒩 M₀)

νHS : (𝒩 : Node) (M₀ : Code) → HS (νT 𝒩 M₀)
νHS 𝒩 M₀ = forceᴺ-HS _ (Gν 𝒩 M₀)

νlv : Node → Code → Ordᴵ
νlv 𝒩 M₀ = lvG (Gν 𝒩 M₀)
```

## §4 严格增长的函数支配秩

位置的秩就是字面路径. 对码归纳, 不按阶段.

```agda
Inc : ∀ {c} → (Pos c → Ordᴵ) → Set
Inc {c} f = ∀ p q → p <ᴾ q → f p ≺ᴵ f q

rk≼ : ∀ c b (f : Pos (cs c) → Ordᴵ) → Inc f → (∀ x → b ≼ f x) → ∀ p → rkP b p ≼ f p
rkB : ∀ g b (f : Pos (cs (cl g)) → Ordᴵ) → Inc f → (∀ x → b ≼ f x) → ∀ j x → Sb b g j ≼ f (low (blk j x))
rk≼ cz b f inc h end = h end
rk≼ cz b f inc h (low ())
rk≼ (cs c) b f inc h end =
  ≼-trans (s≼ (rk≼ c b (λ x → f (low x)) (λ p q r → inc (low p) (low q) r) (λ x → h (low x)) end)) (≺→s≼ (inc (low end) end tt))
rk≼ (cs c) b f inc h (low p) = rk≼ c b (λ x → f (low x)) (λ p′ q r → inc (low p′) (low q) r) (λ x → h (low x)) p
rk≼ (cl g) b f inc h end = l≼ (λ j → ≼-trans (rkB g b f inc h j end) (≺→≼ (inc (low (blk j end)) end tt)))
rk≼ (cl g) b f inc h (low (blk j p)) =
  rk≼ (g j) (Sb b g j) (λ x → f (low (blk j x))) (λ p′ q r → inc (low (blk j p′)) (low (blk j q)) (ltB-same g j r)) (rkB g b f inc h j) p
rkB g b f inc h zero x = h _
rkB g b f inc h (suc j) x =
  ≼-trans (s≼ (rk≼ (g j) (Sb b g j) (λ y → f (low (blk j y))) (λ p′ q r → inc (low (blk j p′)) (low (blk j q)) (ltB-same g j r)) (rkB g b f inc h j) end))
          (≺→s≼ (inc (low (blk j end)) (low (blk (suc j) x)) (ltB-next g j end x)))

```

## §5 累加的值

`plus` 对 `ᶜ+` 的结合律, 只要 `≼` 一个方向.

```agda
gOf : Code → ℕ → Code
gOf (cl h) = h
gOf _      = λ _ → cz

Sb-g′ : ∀ B b (g g′ : ℕ → Code) → plus B (g 0) ≼ plus b (g′ 0) → (∀ i → g′ (suc i) ≡ g (suc i)) → ∀ j → Sb B g (suc j) ≼ Sb b g′ (suc j)
Sb-g′ B b g g′ e0 es zero = s≼ e0
Sb-g′ B b g g′ e0 es (suc j) = s≼ (subst (λ w → plus (Sb B g (suc j)) (g (suc j)) ≼ plus (Sb b g′ (suc j)) w) (sym (es j)) (plus-mono (g (suc j)) (Sb-g′ B b g g′ e0 es j)))

plus-ᶜ+ : ∀ b c d → plus (plus b c) d ≼ plus b (c ᶜ+ d)
plus-ᶜ+ b c cz = ≼-refl _
plus-ᶜ+ b c (cs d) = s≼ (plus-ᶜ+ b c d)
plus-ᶜ+ b c (cl g) = l≼ go
  where
  go : ∀ j → Sb (plus b c) g j ≼ plus b (c ᶜ+ cl g)
  go zero = l≼ʳ 1 (s≼ʳ (≼-trans (≼-plus (plus b c) (g 0)) (plus-ᶜ+ b c (g 0))))
  go (suc j) = l≼ʳ (suc j) (Sb-g′ (plus b c) b g (gOf (c ᶜ+ cl g)) (plus-ᶜ+ b c (g 0)) (λ i → refl) j)

-- 上移后的高度不低于接上去的段
val-next : ∀ M η → η ≼ val (M ᶜ+ cs ⌈ η ⌉)
val-next M η = s≼ʳ (≼-trans (dom η (val M)) (plus-ᶜ+ zero M ⌈ η ⌉))
```

## §6 定点

对任何节点, 只要第 0 行的值不低于高度的值.

```agda
module Fix (b : Code → Z) (G : ∀ M → Goodᴺ (b M)) (u≺ : ∀ M N → forceᴺ _ (G M) ≺ forceᴺ _ (G (M ᶜ+ cs N))) (val≼ : ∀ M → val M ≼ lvG (G M)) (M₀ : Code) where
  𝒩 : Node
  𝒩 = node b G (λ M N → ≺→⊑ (u≺ M N))

  Cₜ : ℕ → Code
  Cₜ = C 𝒩 M₀

  -- 输出的层号不超过下一个高度
  feed-up : ∀ n → ly 𝒩 (Cₜ n) ≼ val (Cₜ (suc n))
  feed-up n = val-next (Cₜ n) (ly 𝒩 (Cₜ n))

  -- 高度不超过输出的层号
  feed-dn : ∀ n → val (Cₜ n) ≼ ly 𝒩 (Cₜ n)
  feed-dn n = val≼ (Cₜ n)

  -- 节点的层号是上面的极限
  lv-is : ∀ n → ly 𝒩 (Cₜ n) ≼ νlv 𝒩 M₀
  lv-is n = l≼ʳ n (≼-refl _)

  -- 输出与高度互相共尾
  cof-out : ∀ n → val (Cₜ n) ≼ νlv 𝒩 M₀
  cof-out n = ≼-trans (feed-dn n) (lv-is n)

  -- 分支严格增长 (不空)
  y≺ : ∀ n → yv 𝒩 (Cₜ n) ≺ yv 𝒩 (Cₜ (suc n))
  y≺ n = u≺ (Cₜ n) _

  -- 节点层号之下的东西都低于某个高度
  cof-ht : ∀ {x} → x ≺ᴵ νlv 𝒩 M₀ → Σ ℕ λ n → x ≼ val (Cₜ (suc n))
  cof-ht (via e (lim n q)) = n , ≼-trans (≺→≼ (via e q)) (feed-up n)
```

## §7 `≼` 不推出 $\sqsubseteq^0$

这是累加链的理由, 不是路线的否定. 两个 $\omega$ 字面不同, Brouwer 序下 $\omega+1\preceq\omega'+1$; 结构序要 $\omega\cong\omega'$, 而 $\omega$, $\omega'$ 不互模拟.

```agda
nat⁰ : ℕ → Ordᶜ zero
nat⁰ zero = zero
nat⁰ (suc n) = suc (nat⁰ n)

ω⁰ ω′⁰ : Ordᶜ zero
ω⁰ = lim nat⁰
ω′⁰ = lim (λ n → nat⁰ (suc n))

not≅ : ω⁰ ≅ ω′⁰ → ⊥
not≅ (l≅ h) with h 0
... | ()

no-suc : suc ω⁰ ⊑⁰ suc ω′⁰ → ⊥
no-suc k with k (≺z (l≅ (λ n → ≅-refl⁰ (nat⁰ n))))
... | ≺z e = not≅ e
... | ≺s (≺l n r) = lim-nat n r
  where
  lim-nat : ∀ n → ω⁰ ≺ nat⁰ (suc n) → ⊥
  lim-nat zero (≺z ())
  lim-nat zero (≺s ())
  lim-nat (suc n) (≺z ())
  lim-nat (suc n) (≺s r′) = lim-nat n r′

nat-HS : ∀ n → HS (nat⁰ n)
nat-HS zero = hz
nat-HS (suc n) = hs (nat-HS n)

nat-st : ∀ n → nat⁰ n ⊑⁰ nat⁰ (suc n)
nat-st n h = ≺s h

ω-HS : HS ω⁰
ω-HS = hl nat-HS nat-st

ω′-HS : HS ω′⁰
ω′-HS = hl (λ n → nat-HS (suc n)) (λ n → nat-st (suc n))

nat-≼ : ∀ n (h h′ : HS (nat⁰ n)) → toLevel (nat⁰ n) h ≼ toLevel (nat⁰ n) h′
nat-≼ zero h h′ = z≼
nat-≼ (suc n) h h′ = s≼ (nat-≼ n (hs⁻ h) (hs⁻ h′))

ω≼ω′ : toLevel ω⁰ ω-HS ≼ toLevel ω′⁰ ω′-HS
ω≼ω′ = l≼ (λ n → l≼ʳ n (s≼ʳ (nat-≼ n _ _)))

-- 层号在 Brouwer 序下 ≼, 结构序却是假的
≼↛⊑ : Σ (Ordᶜ zero) λ a → Σ (Ordᶜ zero) λ b → Σ (HS a) λ ha → Σ (HS b) λ hb → (toLevel a ha ≼ toLevel b hb) × (a ⊑⁰ b → ⊥)
≼↛⊑ = suc ω⁰ , suc ω′⁰ , hs ω-HS , hs ω′-HS , s≼ ω≼ω′ , no-suc
```
