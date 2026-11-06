# ValX (一): $\Omega_1$ 层上的值关系 (同种类比较), 累加引理

> 不含记号. 入口 [ValX](ValX.lagda.md), 接口 [ValXIf](ValXIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP. 只导入 stdlib, `OCF.Lean.CRw*`, `OCF.Lean.ValCRel`, `OCF.Lean.ValCBase` (只用, 不改).
>
> **对象.** $\Omega_1$ 层的高度 `HB XS`. `XS` 的种类是 $(c,\kappa)$, $\kappa$ 是第 $c+1$ 层的种类; 它的层是 `lvX (c , κ) = lvK (hs c) κ`, 坐标是那一层的高度 (经 `toX` 搬成坐标). 坐标上的关系与值合法取 ValC 的 `LeAt`, `MoAt` (可数层号).
>
> **与 ValC 的差: `Ω≤Ω` 要求同一个分量、同一层** (ValC 只要求同层). 理由由树逼出: 同在第 0 层的 $\Omega_1$ 本身 (`(hz , inj₂ tt)`, 进入时移动世界并回灌) 与别的分量里的拷贝 (不动世界) 被跨底折叠以不同方式处理; 否定一路 `NegValXSelf.self≰copy` (实例 `I₁`; 否定一路报告已编译, 本路未复核) 给出 "本身 ≤ 拷贝" 的反例. 同一分量 $c$ 里的种类策略相同 (分量 $0$ 只有 $\Omega_1$ 本身; 别的分量都不动世界). 同分量同层的不同种类要能比较: 分支 $d\mapsto\iota_c(\mathrm{up}\,d)$ 把第 $c$ 层的值关系 (ValC 的, 按层比较) 搬到 $\Omega_1$ 层 ([ValXP1](ValXP1.lagda.md) `ιX-mono`).
>
> (修订记录: 本篇首次编译时 `Ω≤Ω` 要求同一种类; 为证 `gt C` 值合法改成同分量同层, 依赖本篇的文件随之重编.)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwIf
module OCF.Lean.ValXRel (I : CRwIf) where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (<⇒<′; n<1+n)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwFold I
open import OCF.Lean.ValCRel I
```

## §1 种类的层与坐标

```agda
HX : Set
HX = HB XS

lvX : K XS → Cd
lvX (c , κ) = lvK (hs c) κ

toX : ∀ κ → H (lvX κ) → E XS κ
toX (c , κ) = toK (hs c) κ
```

## §2 关系与值合法

```agda
infix 4 _≤X_
data _≤X_ : HX → HX → Set where
  z≤  : ∀ {b} → hz ≤X b
  s≤s : ∀ {a b} → a ≤X b → hs a ≤X hs b
  ≤s  : ∀ {a b} → a ≤X b → a ≤X hs b
  l≤l : ∀ {f g} (σ : ℕ → ℕ) → Inc σ → (∀ n → f n ≤X g (σ n)) → hl f ≤X hl g
  ≤l  : ∀ {a g} n → a ≤X g n → a ≤X hl g
  ≤Ω  : ∀ {a κ g} c → LeAt (lvX κ) c (top b⊥ (lvX κ)) → MoAt (lvX κ) c → a ≤X g (toX κ c) → a ≤X hΩ κ g
  Ω≤Ω : ∀ {c κ κ′ g g′} (e : lvK (hs c) κ ≡ lvK (hs c) κ′) →
        (∀ d → MoAt (lvK (hs c) κ) d → g (toK (hs c) κ d) ≤X g′ (toK (hs c) κ′ (subst H e d))) →
        hΩ (c , κ) g ≤X hΩ (c , κ′) g′

MoX : HX → Set
MoX hz = ⊤
MoX (hs h) = MoX h
MoX (hl f) = ∀ n → MoX (f n)
MoX (hΩ κ g) =
  (∀ c c′ → MoAt (lvX κ) c → MoAt (lvX κ) c′ → LeAt (lvX κ) c c′ → g (toX κ c) ≤X g (toX κ c′)) ×
  (∀ c → MoAt (lvX κ) c → MoX (g (toX κ c)))

idInc : Inc (λ n → n)
idInc n = n<1+n n

≤X-refl : ∀ a → a ≤X a
≤X-refl hz = z≤
≤X-refl (hs a) = s≤s (≤X-refl a)
≤X-refl (hl f) = l≤l (λ n → n) idInc (λ n → ≤X-refl (f n))
≤X-refl (hΩ (c , κ) g) = Ω≤Ω refl (λ d _ → ≤X-refl (g (toK (hs c) κ d)))

≤X-trans : ∀ {a b c} → a ≤X b → b ≤X c → a ≤X c
≤X-trans z≤ q = z≤
≤X-trans p (≤s q) = ≤s (≤X-trans p q)
≤X-trans p (≤l n q) = ≤l n (≤X-trans p q)
≤X-trans p (≤Ω c e m q) = ≤Ω c e m (≤X-trans p q)
≤X-trans (s≤s p) (s≤s q) = s≤s (≤X-trans p q)
≤X-trans (≤s p) (s≤s q) = ≤s (≤X-trans p q)
≤X-trans (l≤l σ i h) (l≤l τ j h′) = l≤l (λ n → τ (σ n)) (L.inc∘ hz i j) (λ n → ≤X-trans (h n) (h′ (σ n)))
≤X-trans (≤l n p) (l≤l τ j h′) = ≤l (τ n) (≤X-trans p (h′ n))
≤X-trans (≤Ω c bd m p) (Ω≤Ω e′ h′) =
  ≤Ω (subst H e′ c) (subst (λ z → LeAt _ (subst H e′ c) z) (top-tr e′) (LeAt-tr e′ c _ bd)) (MoAt-tr e′ c m)
     (≤X-trans p (h′ c m))
≤X-trans {hΩ (c , κ) g} {_} {hΩ (_ , κ″) g″} (Ω≤Ω e h) (Ω≤Ω e′ h′) =
  Ω≤Ω (trans e e′) (λ d m → subst (λ z → g (toK (hs c) κ d) ≤X g″ (toK (hs c) κ″ z)) (ss e e′ d)
    (≤X-trans (h d m) (h′ (subst H e d) (MoAt-tr e d m))))
  where
  ss : ∀ {i j k} (e : i ≡ j) (e′ : j ≡ k) (c : H i) → subst H e′ (subst H e c) ≡ subst H (trans e e′) c
  ss refl refl c = refl
```

## §3 加法与累加

```agda
≤X⊞ : ∀ a b → a ≤X a ⊞ b
≤X⊞ a hz = ≤X-refl a
≤X⊞ a (hs b) = ≤s (≤X⊞ a b)
≤X⊞ a (hl f) = ≤l 0 (≤X⊞ a (f 0))
≤X⊞ a (hΩ κ g) = ≤Ω hz Rel.z≤ tt (≤X⊞ a (g (toX κ hz)))

≤X⊞ˡ : ∀ a x → x ≤X a ⊞ x
≤X⊞ˡ a hz = z≤
≤X⊞ˡ a (hs x) = s≤s (≤X⊞ˡ a x)
≤X⊞ˡ a (hl f) = l≤l (λ n → n) idInc (λ n → ≤X⊞ˡ a (f n))
≤X⊞ˡ a (hΩ (c , κ) g) = Ω≤Ω refl (λ d _ → ≤X⊞ˡ a (g (toK (hs c) κ d)))

⊞X-monoˡ : ∀ {a a′} x → a ≤X a′ → a ⊞ x ≤X a′ ⊞ x
⊞X-monoˡ hz p = p
⊞X-monoˡ (hs x) p = s≤s (⊞X-monoˡ x p)
⊞X-monoˡ (hl f) p = l≤l (λ n → n) idInc (λ n → ⊞X-monoˡ (f n) p)
⊞X-monoˡ (hΩ (c , κ) g) p = Ω≤Ω refl (λ d _ → ⊞X-monoˡ (g (toK (hs c) κ d)) p)

⊞X-monoʳ : ∀ a {x y} → x ≤X y → a ⊞ x ≤X a ⊞ y
⊞X-monoʳ a (z≤ {b = y}) = ≤X⊞ a y
⊞X-monoʳ a (s≤s p) = s≤s (⊞X-monoʳ a p)
⊞X-monoʳ a (≤s p) = ≤s (⊞X-monoʳ a p)
⊞X-monoʳ a (l≤l σ i h) = l≤l σ i (λ n → ⊞X-monoʳ a (h n))
⊞X-monoʳ a (≤l n p) = ≤l n (⊞X-monoʳ a p)
⊞X-monoʳ a (≤Ω c e m p) = ≤Ω c e m (⊞X-monoʳ a p)
⊞X-monoʳ a (Ω≤Ω e h) = Ω≤Ω e (λ d md → ⊞X-monoʳ a (h d md))

⊞X-mono : ∀ {a a′ x y} → a ≤X a′ → x ≤X y → a ⊞ x ≤X a′ ⊞ y
⊞X-mono {x = x} p q = ≤X-trans (⊞X-monoˡ x p) (⊞X-monoʳ _ q)

MoX-⊞ : ∀ a b → MoX a → MoX b → MoX (a ⊞ b)
MoX-⊞ a hz ma mb = ma
MoX-⊞ a (hs b) ma mb = MoX-⊞ a b ma mb
MoX-⊞ a (hl f) ma mb = λ n → MoX-⊞ a (f n) ma (mb n)
MoX-⊞ a (hΩ κ g) ma (mo , mh) =
  (λ c c′ mc mc′ p → ⊞X-monoʳ a (mo c c′ mc mc′ p)) , (λ c mc → MoX-⊞ a (g (toX κ c)) ma (mh c mc))

mulX-mono : ∀ {a a′} → a ≤X a′ → ∀ n → mul a n ≤X mul a′ n
mulX-mono p zero = p
mulX-mono p (suc n) = ⊞X-mono (mulX-mono p n) p

MoX-mul : ∀ a → MoX a → ∀ n → MoX (mul a n)
MoX-mul a m zero = m
MoX-mul a m (suc n) = MoX-⊞ (mul a n) a (MoX-mul a m n) m

MoX-Σ : ∀ F → (∀ n → MoX (F n)) → ∀ n → MoX (Σ⁺ F n)
MoX-Σ F m zero = m 0
MoX-Σ F m (suc n) = MoX-⊞ _ _ (MoX-Σ F m n) (m (suc n))

ΣX-ge : ∀ F n → F n ≤X Σ⁺ F n
ΣX-ge F zero = ≤X-refl _
ΣX-ge F (suc n) = ≤X⊞ˡ (Σ⁺ F n) (F (suc n))

ΣX-idx : ∀ F {i j} → i ≤′ j → Σ⁺ F i ≤X Σ⁺ F j
ΣX-idx F ≤′-refl = ≤X-refl _
ΣX-idx F (≤′-step p) = ≤X-trans (ΣX-idx F p) (≤X⊞ _ _)

private
  lw : ∀ {i j} → suc i ≤′ j → i ≤′ j
  lw ≤′-refl = ≤′-step ≤′-refl
  lw (≤′-step p) = ≤′-step (lw p)

  skip : ∀ F {i j} → suc i ≤′ j → Σ⁺ F i ⊞ F j ≤X Σ⁺ F j
  skip F ≤′-refl = ≤X-refl _
  skip F (≤′-step p) = ⊞X-monoˡ _ (ΣX-idx F (lw p))

ΣX-sub : ∀ F G σ → Inc σ → (∀ n → F n ≤X G (σ n)) → ∀ n → Σ⁺ F n ≤X Σ⁺ G (σ n)
ΣX-sub F G σ i h zero = ≤X-trans (h 0) (ΣX-ge G (σ 0))
ΣX-sub F G σ i h (suc n) = ≤X-trans (⊞X-mono (ΣX-sub F G σ i h n) (h (suc n))) (skip G (<⇒<′ (i n)))
```

## §4 回灌与世界的值律 (实例的性质, 不是接口的律)

跨底折叠进入 $\Omega_1$ 种类的分支时, 坐标先回灌 (`sh₀ B c`), 世界换成 `nxt₀`. 跨底单调要它们对值关系单调, 且回灌不降坐标. 这是实例 (`I₁`: $B\boxplus\mathrm{leg}\,c$, $e+1$) 的性质, 在 [ValXTm](ValXTm.lagda.md) 对 `I₁` 证出; 这里只写成记录, 作 [ValXMono](ValXMono.lagda.md) 的模块参数.

```agda
record ShLaw : Set where
  field
    shM : ∀ {B B′ c c′} → LeAt hz B B′ → LeAt hz c c′ → LeAt hz (CRwIf.sh₀ I B c) (CRwIf.sh₀ I B′ c′)
    shI : ∀ {B} c → LeAt hz c (CRwIf.sh₀ I B c)
    nxM : ∀ {B B′ e e′} (a : CRwIf.Adm₀ I B e) (a′ : CRwIf.Adm₀ I B′ e′) → LeAt hz e e′ →
          LeAt hz (CRwIf.nxt₀ I B e a) (CRwIf.nxt₀ I B′ e′ a′)

⊲→≤ : ∀ {a b : Cd} → a ⊲ b → LeAt hz a b
⊲→≤ {a} hself = L.≤-refl hz a
⊲→≤ (hsuc q) = Rel.≤s (⊲→≤ q)
⊲→≤ (hlim n q) = Rel.≤l n (⊲→≤ q)
⊲→≤ (hLim {κ = ()} _ _)
```

## 结论 (按档)

- **[定理]** 关系 `_≤X_` (同分量同层的 `Ω≤Ω`), 值合法 `MoX`; `≤X-refl`, `≤X-trans`; 加法 `≤X⊞`, `≤X⊞ˡ`, `⊞X-monoˡ`, `⊞X-monoʳ`, `⊞X-mono`, `MoX-⊞`; 累加 `mulX-mono`, `MoX-mul`, `MoX-Σ`, `ΣX-ge`, `ΣX-idx`, `ΣX-sub`; 记录 `ShLaw` (回灌与世界的值律, 作参数), `⊲→≤`.
