# 键在闭包上做了什么: 不同节点不进界, 同节点进界

> 不含记号. 结论写在 [LvKey](LvKey.lagda.md). 全部是对 [LvKeyTree](LvKeyTree.lagda.md) 的编译过的陈述, 其中 $K$ 是变量.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvKeyClo where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Level using (Ordᴵ; _<ᴵ_; natᴵ; zero; suc; lim; Simᴵ; _⊑ᴵ_; ⊑ᴵ-trans)
open import OCF.Align.Prefix using (Ord₊ˢ; Ordˢ; toZ)
open import OCF.Align.NotFree using (Goodᴺ)
open import OCF.Align.UniformLvNeg using (lvG; clo⊑)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; _⊔_; Ev; Bd; bound)
open import OCF.Align.LvKeyNeg using (Inᵏ; ink′; inl′; inr′; Bd-in)
open import OCF.Align.LvKeyBase
open import OCF.Align.LvKeyTree renaming (T to Tv)
```

## §1 $\psi_1(1)+\Omega$: 外层的地板不进内层闭包的界

旧树里这一处标签相撞 ([LvKeyNeg](LvKeyNeg.lagda.md)). 这里外层键是 `self`, 内层键是 `fst (suc (lim 2 self))`; `kdec` 在 `self` 对 `fst` 处直接由 `irr` 回答, 不用任何比较. 挑出的地板是**与 $K$ 无关的同一个项** (`free`, `refl`, $K$ 是变量).

```agda
c₁ : LI
c₁ = times Ω·ω

cf₁ : Cf c₁
cf₁ = Mono.WF-times Ω·ω selfΩ·ω WFΩ·ω , ≈times selfΩ·ω

module A = Over c₁

Pin : Cp (Ω· 2) c₁
Pin = fst (suc (lim 2 Cp.self))

π₁ : Ordᴵ → A.Fᵗ
π₁ K = (A.tz A.∪ A.tk Cp.self K) A.∪ (A.Fl₀ A.∪ A.tz)

w₁ : Ordᴵ → Wd
w₁ K = wd (suc zero) (∅ (suc K))

ok₁ : ∀ K → zero <ᴵ K → Wok (w₁ K)
ok₁ K q = zero , suc q

ev₁ : ∀ K → A.Evt (w₁ K) (π₁ K)
ev₁ K = (tt , (tt , suc K , refl , (λ q → q))) , ((tt , (λ q → q)) , tt)

φ₁ : ∀ K → zero <ᴵ K → Flr
φ₁ K q = A.Sel.φ (A.Sel.selF (proj₁ cf₁) (proj₂ cf₁) Pin (w₁ K) (ok₁ K q) tt (π₁ K) (ev₁ K))

free : ∀ K K′ (q : zero <ᴵ K) (q′ : zero <ᴵ K′) → φ₁ K q ≡ φ₁ K′ q′
free K K′ q q′ = refl
```

## §2 同一个节点: 地板进界

键相同 (`self` 对 `self`). 这一条**不是修好的, 是设计如此**: 比较这个节点上的分支要公共上界. 它就是 [LvCert](LvCert.lagda.md) 的 `noCert₂` 读的那一步, 见 [LvKey](LvKey.lagda.md) 的第一个障碍.

```agda
Psame : Cp c₁ c₁
Psame = Cp.self

φ₂ : ∀ K → zero <ᴵ K → Flr
φ₂ K q = A.Sel.φ (A.Sel.selF (proj₁ cf₁) (proj₂ cf₁) Psame (w₁ K) (ok₁ K q) tt (π₁ K) (ev₁ K))

same-in : ∀ K (q : zero <ᴵ K) → Inᵏ K (φ₂ K q)
same-in K q = inl′ (inr′ (inr′ ink′))
```

## §3 有限测试: `kdec` 跨分支

`P₃`, `P₅`: 分支 3 与 5 下面的同一个内层 $\Omega\cdot2$. 回答 "相同", 比较读的是 `<ᴵ-dec`. `P₃′`: 分支 3 下的 $\Omega\cdot3$. 回答 "不同". 这是测试, 不是定理.

```agda
isYes : ∀ {A : Set} → A ⊎ (A → ⊥) → Bool
isYes (inj₁ _) = true
isYes (inj₂ _) = false

E₇ : Ents
E₇ = ∅ (natᴵ 7)

okE₇ : OkE E₇
okE₇ = suc (suc (suc (suc (suc (suc zero)))))

P₃ P₅ : Cp (Ω· 2) c₁
P₃ = bra (natᴵ 3) (suc (suc (suc (lim 2 Cp.self))))
P₅ = bra (natᴵ 5) (suc (suc (suc (suc (suc (lim 2 Cp.self))))))

P₃′ : Cp (Ω· 3) c₁
P₃′ = bra (natᴵ 3) (suc (suc (suc (lim 3 Cp.self))))

a₃ : AdmC E₇ P₃
a₃ = (natᴵ 7 , refl , suc (suc (suc zero))) , tt

a₅ : AdmC E₇ P₅
a₅ = (natᴵ 7 , refl , suc zero) , tt

a₃′ : AdmC E₇ P₃′
a₃′ = (natᴵ 7 , refl , suc (suc (suc zero))) , tt

t-same : isYes (kdec (proj₁ cf₁) (proj₂ cf₁) P₃ P₅ E₇ okE₇ a₃ a₅) ≡ true
t-same = refl

t-diff : isYes (kdec (proj₁ cf₁) (proj₂ cf₁) P₃ P₃′ E₇ okE₇ a₃ a₃′) ≡ false
t-diff = refl

t-outer : isYes (kdec (proj₁ cf₁) (proj₂ cf₁) Cp.self P₃ E₇ okE₇ tt a₃) ≡ false
t-outer = refl
```

## §4 `noW` 的形状在这棵树上: 同键的地板进界, 换键逃不掉

[LvCertWorld](LvCertWorld.lagda.md) 的 `Core.noSame` 的键版, **对任何位置, 任何世界**. `pick-in`: 地板项的键 $\approx\kappa$ 时, `pick` 不可能答 "不同" (答了就与证据矛盾), 所以 `fk K` 必在 `φ` 里. `sel-in`: 这对任何形状的地板成立. `noSameᵏ`: 所以闭包的 `Goodᴺ` 推出第 0 点的层号 $\succ K$. 而 $W=\dot\Omega_D$ 的闭包与 `ι (db τ P₂)` 的项键都是字面的 `P₂` ($W$ 的闭包在 `Ω̇ᵖ D P₂`, 项由 `Ω̇ᵖ` 里同一个 `P` 给出): `same-P₂`.

```agda
module KS (c : LI) (wf : WF c) (sf : c ≈ c) where
  open Over c

  data InFl {g} (Q : Cp (lcl g) c) (K : Ordᴵ) : Fᵗ → Set where
    here : InFl Q K (tk Q K)
    inˡ  : ∀ {a b} → InFl Q K a → InFl Q K (a ∪ b)
    inʳ  : ∀ {a b} → InFl Q K b → InFl Q K (a ∪ b)

  module _ {κ} (P : Cp (lcl κ) c) (w : Wd) (ok : Wok w) (ap : AdmC (Ε w) P) where
    open Sel wf sf P w ok ap

    pick-in : ∀ {g} (Q : Cp (lcl g) c) (aq : AdmC (Ε w) Q) K b → lcl g ≈ lcl κ → Inᵏ K (S.φ (pick Q aq K b))
    pick-in Q aq K (ℓ , a , s) e with kdec wf sf Q P (Ε w) (proj₂ ok) aq ap
    ... | inj₁ _ = ink′
    ... | inj₂ n = ⊥-elim (n e)

    sel-in : ∀ {g} {Q : Cp (lcl g) c} {K π} → lcl g ≈ lcl κ → InFl Q K π → (ev : Evt w π) → Inᵏ K (S.φ (selF π ev))
    sel-in e here (ad , b) = inr′ (pick-in _ ad _ b e)
    sel-in e (inˡ k) (x , y) = inl′ (sel-in e k x)
    sel-in e (inʳ k) (x , y) = inr′ (sel-in e k y)

  noSameᵏ : ∀ {π g κ} {Q : Cp (lcl g) c} {K} (P : Cp (lcl κ) c) (pa : ∀ {w} → Evt w π → AdmC (Ε w) P) (t : Runᵗ π) (h : (η : Ordᴵ) → Runᵗ (π ∪ tk P η)) →
            lcl g ≈ lcl κ → InFl Q K π → ∀ {w} (ok : Wok w) (ev : Evt w π) (p : zero <ᴵ ℓ₀ w) →
            Goodᴺ (toZ (cloK wf sf P pa t h ok ev p)) → Σ (Goodᴺ (toZ (t ok ev p))) λ G₀ → suc K ⊑ᴵ lvG G₀
  noSameᵏ {π} {κ = κ} P pa t h e k {w} ok ev p G with clo⊑ G
  ... | G₀ , d = G₀ , ⊑ᴵ-trans (Bd-in (Sel.S.φ (Sel.selF wf sf P w ok (pa ev) π ev) ⊔ fk zero) _ _ (inl′ (sel-in P w ok (pa ev) e k ev))) d
```

**`same-P₂`.** $\Omega\cdot2+1$ 上的两个键是同一个位置, 不是 "模 ≈ 相同" 那种需要比较的情形. 所以 `noW` 的第 3 步在这棵树上逐字成立. 还差的是第 4 步 (第 0 点与 $\tau$ 无关, 层号 $\sqsubseteq\tau$): 它用 [LvCertRel](LvCertRel.lagda.md) 的跨层互模拟, 那是对旧树写的, **没有移植**. 所以 "这棵树也没有 `Goodᴺ`" 在这里是判断, 第 3 步是定理.

```agda
same-P₂ : ∀ {τ} → _≡_ {A = Over.Fᵗ (suc (Ω· 2))} (Over.dnF (suc (Ω· 2)) (Over.db τ (suc Cp.self))) (Over.tk (suc Cp.self) τ)
same-P₂ = refl
```
