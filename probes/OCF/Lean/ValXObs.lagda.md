# ValX (二): 卡点 — $\Omega_1$ 层的地板的分支对坐标不值单调

> 不含记号. 入口 [ValX](ValX.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP. 对一切 `I : CRwIf`.
>
> **问题.** 跨底折叠在 $\Omega_1$ 结点处取回灌链: 第 $n$ 点的分支取在坐标 $B\boxplus\mathrm{leg}(\text{链的前一点})$ 处. 比较两个输入的折叠时, 两边链的前一点只按值相关, 所以要右边 $\Omega_1$ 结点的分支对坐标**值单调** (`MoX` 的第一个分量). 地板 `topL` 的分支是 `gt`: `gt C` 是 $\sum_{c+1\lhd C}\Omega_{c+1}$, 它的种类在第 $c$ 个分量里, **分量由坐标 $C$ 的结构决定**. 两个值相关但结构不同的坐标给出不同分量的种类.
>
> **定理 `floor-block`.** 对 $\Omega_1$ 层上**一切**满足 "层反射" (`LvRefl`: 左边是第 $k$ 层种类的 $\Omega$-结点时, 右边含一个第 $k$ 层种类的结点) 的关系 $R$: 坐标 $1+\omega$ (以 $n$ 为基本列) 与 $1+\omega'$ (以 $n+1$ 为基本列) 在第 0 层的值关系下 $\le$ (`le₁₂`), 但 `¬ R (gt (1+ω)) (gt (1+ω′))`. 本路的关系 `_≤X_` (同分量同层) 与 ValC 式的按层比较都层反射 (`refl≤X`).
>
> **推论 `¬MoX-topL`.** 地板 `topL` 不是 `MoX`. 所以按 ValC 式的值合法, 接口 `ValX` 的锚 `MoX-topL` 不能满足: 本路的关系不给 `ValX` 的实例 (`noValX` 的读法见入口). 要满足它, $\Omega$-结点必须能跨层比较 (第 $c$ 层的高度搬到值不小的第 $c'$ 层: 层号的值搬运), 那是层号单调的问题 (ValC 接手清单第 4 条) 的跨结构版本. 判断: 这是跨底值定理的真正卡点.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwIf
module OCF.Lean.ValXObs (I : CRwIf) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwFold I
open import OCF.Lean.ValCRel I
open import OCF.Lean.ValXRel I
```

## §1 层反射

```agda
data HasL (k : Cd) : HX → Set where
  here : ∀ {κ g} → lvX κ ≡ k → HasL k (hΩ κ g)
  ins  : ∀ {h} → HasL k h → HasL k (hs h)
  inl  : ∀ {f} n → HasL k (f n) → HasL k (hl f)
  inΩ  : ∀ {κ g} e → HasL k (g e) → HasL k (hΩ κ g)

LvRefl : (HX → HX → Set) → Set
LvRefl R = ∀ {κ g y} → R (hΩ κ g) y → HasL (lvX κ) y

refl≤X : LvRefl _≤X_
refl≤X (≤s p) = ins (refl≤X p)
refl≤X (≤l n p) = inl n (refl≤X p)
refl≤X (≤Ω {κ = κ′} c _ _ p) = inΩ (toX κ′ c) (refl≤X p)
refl≤X (Ω≤Ω e h) = here (sym e)
```

## §2 分量的不变量

`Inv W y`: $y$ 里每个结点的种类 $(c,\kappa)$ 满足 $c+1\lhd W$ (对一切坐标处的分支). 于是它含的每个种类的层 $k$ 满足 $k+1\lhd W$.

```agda
Inv : Cd → HX → Set
Inv W hz = ⊤
Inv W (hs h) = Inv W h
Inv W (hl f) = ∀ n → Inv W (f n)
Inv W (hΩ (c , κ) g) = (hs c ⊲ W) × (∀ e → Inv W (g e))

has-inv : ∀ {k W y} → HasL k y → Inv W y → hs k ⊲ W
has-inv {W = W} (here {κ = (c , κ)} e) (q , _) = subst (λ z → hs z ⊲ W) e (⊲ᴮ-tr (pK (hs c) κ) q)
has-inv (ins h) v = has-inv h v
has-inv (inl n h) v = has-inv h (v n)
has-inv {y = hΩ (c , κ) g} (inΩ e h) (_ , v) = has-inv h (v e)

Inv-⊞ : ∀ {W} a b → Inv W a → Inv W b → Inv W (a ⊞ b)
Inv-⊞ a hz va vb = va
Inv-⊞ a (hs b) va vb = Inv-⊞ a b va vb
Inv-⊞ a (hl f) va vb = λ n → Inv-⊞ a (f n) va (vb n)
Inv-⊞ a (hΩ (c , κ) g) va (q , vb) = q , λ e → Inv-⊞ a (g e) va (vb e)

Inv-ι : ∀ {W} c → hs c ⊲ W → ∀ x → Inv W (ι {Cd} {λ c → Tw S⊥ (hs c)} c x)
Inv-ι c q hz = tt
Inv-ι c q (hs x) = Inv-ι c q x
Inv-ι c q (hl f) = λ n → Inv-ι c q (f n)
Inv-ι c q (hΩ κ g) = q , λ e → Inv-ι c q (g e)

Inv-gt : ∀ {W} y → y ⊲ W → Inv W (gt y)
Inv-gt hz q = tt
Inv-gt (hs c) q = Inv-⊞ (gt c) _ (Inv-gt c (⊲ᴮ-tr (hsuc hself) q)) (Inv-ι c q (topT S⊥ hz (hs c)))
Inv-gt (hl f) q = λ n → Inv-gt (f n) (⊲ᴮ-tr (hlim n hself) q)
Inv-gt (hΩ () _) q
```

## §3 两个坐标

$\omega_1=\lim(0,1,2,\dots)$, $\omega_2=\lim(1,2,3,\dots)$; $1+\omega_1\le1+\omega_2$ (第 0 层的值关系, 子列取恒等), 但 $1+\omega_1\not\lhd1+\omega_2$.

```agda
nat : ℕ → Cd
nat zero = hz
nat (suc n) = hs (nat n)

ω₁ ω₂ : Cd
ω₁ = hl nat
ω₂ = hl (λ n → nat (suc n))

le₁₂ : LeAt hz (hs ω₁) (hs ω₂)
le₁₂ = Rel.s≤s (Rel.l≤l (λ n → n) idInc (λ n → Rel.≤s (L.≤-refl hz (nat n))))

moAll : ∀ c → MoAt hz c
moAll hz = tt
moAll (hs c) = moAll c
moAll (hl f) = λ n → moAll (f n)
moAll (hΩ () _)

private
  NoLim : Cd → Set
  NoLim hz = ⊤
  NoLim (hs x) = NoLim x
  NoLim (hl _) = ⊥
  NoLim (hΩ () _)

  nl-nat : ∀ n → NoLim (nat n)
  nl-nat zero = tt
  nl-nat (suc n) = nl-nat n

  nl⊲ : ∀ {a b} → a ⊲ b → NoLim b → NoLim a
  nl⊲ hself v = v
  nl⊲ (hsuc q) v = nl⊲ q v
  nl⊲ (hlim n q) ()
  nl⊲ (hLim {κ = ()} _ _) v

  isZ isS isL : Cd → Set
  isZ hz = ⊤
  isZ _ = ⊥
  isS (hs _) = ⊤
  isS _ = ⊥
  isL (hl _) = ⊤
  isL _ = ⊥

  hd0 pd : Cd → Cd
  hd0 (hs (hl f)) = f 0
  hd0 _ = hz
  pd (hs x) = x
  pd y = y

  at : ℕ → Cd → Cd
  at n (hl f) = f n
  at n _ = hz

  bad2 : ∀ {a b} → a ⊲ b → a ≡ hs ω₁ → b ≡ ω₂ → ⊥
  bad2 hself e e′ = subst isL (sym (trans (sym e) e′)) tt
  bad2 (hsuc q) e e′ = subst isS e′ tt
  bad2 (hlim n q) e e′ = subst NoLim e (nl⊲ q (subst NoLim (sym (cong (at n) e′)) (nl-nat (suc n))))
  bad2 (hLim {κ = ()} _ _) e e′

  bad1 : ∀ {a b} → a ⊲ b → a ≡ hs ω₁ → b ≡ hs ω₂ → ⊥
  bad1 hself e e′ = subst isZ (cong hd0 (trans (sym e) e′)) tt
  bad1 (hsuc q) e e′ = bad2 q e (cong pd e′)
  bad1 (hlim n q) e e′ = subst isL e′ tt
  bad1 (hLim {κ = ()} _ _) e e′

not⊲ : ¬ (hs ω₁ ⊲ hs ω₂)
not⊲ q = bad1 q refl refl
```

## §4 地板的分支

`gt (1+ω₁)` 的根是第 $\omega_1$ 层的种类 $(\omega_1, \Omega_{\omega_1+1})$; `gt (1+ω₂)` 的一切种类的层 $k$ 满足 $k+1\lhd 1+\omega_2$.

```agda
floor-block : ∀ (R : HX → HX → Set) → LvRefl R → ¬ R (gt (hs ω₁)) (gt (hs ω₂))
floor-block R rf r = not⊲ (has-inv (rf r) (Inv-gt (hs ω₂) hself))

¬gt-mono : ¬ (gt (hs ω₁) ≤X gt (hs ω₂))
¬gt-mono = floor-block _≤X_ refl≤X

¬MoX-topL : ¬ MoX topL
¬MoX-topL (mo , _) = ¬gt-mono (mo (hs ω₁) (hs ω₂) (moAll (hs ω₁)) (moAll (hs ω₂)) le₁₂)
```

## 结论 (按档)

- **[定理, 对一切 `I`]** `floor-block`: 一切层反射的关系都不让地板的分支 `gt` 在 $1+\omega_1\le1+\omega_2$ 处单调; `refl≤X` (本路的关系层反射); `¬gt-mono`, **`¬MoX-topL`**; 辅助 `has-inv`, `Inv-gt`, `le₁₂`, `not⊲`.
- **[判断]** 卡点是 "层号的值搬运": 坐标值相关而结构不同时, 分支里的 $\Omega_{c+1}$ 落在不同分量, 只能跨层比较.
