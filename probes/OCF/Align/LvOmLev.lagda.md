# Ω-极限坐标上的读回包 (一): 带外层世界的层结构 `Lv a c`, 读回层 `Ly c`, 公共上界之下的可入判定

> 不含记号. 入口 [LvOm](LvOm.lagda.md). 主审派的提前探路, 与 `LvRd` 并行; 只读导入 [LvRdEmb](LvRdEmb.lagda.md) 的嵌入 `Emb`. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP.
>
> **问题.** `LvRd` 的读回包只在坐标 $c=n,\omega,\omega+1$ 上 (层是后继或 ℕ-极限). 层号由回灌给出之后 (`LvRdWk.lvShapeδ`), 坐标 $c$ 是一般的 `HB S₀` 高度, 可含 $\Omega$-结点 $\mathrm{h\Omega}\,g$ (分支以 `A` 为坐标). `HtTowerTy.Lev` 在那里取对**一切** `A` 的并 `sup A (Lev ∘ g)`; 照 `trKg` 把它的种类翻译回树, 要一条对一切世界成立的层证据, `NegLvRdLay.no-unifΩ` 说没有.
>
> **本篇的写法 (R1 读世界).** 层结构带一个外层 `A`-世界 $a$ (就是码 `Code a b` 的那个 $a$): $\Omega$-结点的种类只取**在 $a$ 里可入**的分支, 种类自带证据 $x\lhd a$.
>
> - `Lv a c`: `hz` ↦ `S₀`; `hs c` ↦ `step (Lv a c)`; `hl f` ↦ `sup ℕ (n ↦ step (Lv a (f n)))`; `hΩ g` ↦ `sup (Σ x. x ⊲ a) ((x,e) ↦ step (Lv a (g x)))`. 极限处每一支取后继 (`step`), 于是 "过第 $n$ 支本层的结点" 总有种类 (第 $n$ 支的新种类), 不必在支之间找下一个后继.
> - `Ly c`: 读回层, `hz` ↦ $1$, 其余逐结构 (`hΩ g` ↦ `hΩ κA (Ly ∘ g)`); 就是 $1\boxplus c$ 逐构造子展开.
> - `eA c`, `eM c`: 闭包 `nκ`, `nμ` 的种类嵌进 `Lv a c` (取第 0 支; $0\lhd a$ 恒成立, `z⊲`).
> - **公共上界之下的可入判定** `dec⊲`: $x\lhd L$, $a\lhd L$, $L$ 合法 ⇒ `Dec (x ⊲ a)`. 用 `cmpF` 与 `A` 上严格子项的良基. 对照 `NegLvRdLay.decAcc-sep`: 裸元素上判定 "在 $\omega$ 之下" 推出分离子; 差别只在前提里有没有公共上界 $L$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvOmLev where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲; cmpF)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (H₀; Ht; κA; NZ₁)
open import OCF.Align.LvRdEmb using (Emb; idE; inj₁E; ιE; compE)
```

## §1 `A` 上的严格子项与良基

```agda
infix 4 _<A_
data _<A_ : A → A → Set where
  <s₀ : ∀ {b} → b <A asuc b
  <s  : ∀ {x b} → x <A b → x <A asuc b
  <l₀ : ∀ {f} n → f n <A alim f
  <l  : ∀ {x f} n → x <A f n → x <A alim f

data AccA (x : A) : Set where
  acc : (∀ {y} → y <A x → AccA y) → AccA x

downA : ∀ {x y} → AccA x → y <A x → AccA y
downA (acc r) p = r p

wfA : ∀ x → AccA x
wfA azero = acc (λ ())
wfA (asuc x) = acc (λ { <s₀ → wfA x ; (<s p) → downA (wfA x) p })
wfA (alim f) = acc (λ { (<l₀ n) → wfA (f n) ; (<l n p) → downA (wfA (f n)) p })

irrA : ∀ {x} → AccA x → ¬ (x <A x)
irrA (acc r) p = irrA (r p) p

<A-tr : ∀ {x y z} → x <A y → y <A z → x <A z
<A-tr p <s₀ = <s p
<A-tr p (<s q) = <s (<A-tr p q)
<A-tr p (<l₀ n) = <l n p
<A-tr p (<l n q) = <l n (<A-tr p q)

toLtA : ∀ {x y} → x ⊲ y → (x ≡ y) ⊎ (x <A y)
toLtA C.self = inj₁ refl
toLtA (C.suc p) with toLtA p
... | inj₁ refl = inj₂ <s₀
... | inj₂ q = inj₂ (<s q)
toLtA (C.lim n p) with toLtA p
... | inj₁ refl = inj₂ (<l₀ n)
... | inj₂ q = inj₂ (<l n q)

-- 严格在下, 就不在上
<¬⊲ : ∀ {x y} → y <A x → ¬ (x ⊲ y)
<¬⊲ s r with toLtA r
... | inj₁ refl = irrA (wfA _) s
... | inj₂ s′ = irrA (wfA _) (<A-tr s′ s)
```

## §2 公共上界之下的可入判定

```agda
dec-lt : ∀ {x a} → a ⊲ x → (a ≡ x) ⊎ (a <A x) → Dec (x ⊲ a)
dec-lt q (inj₁ refl) = yes C.self
dec-lt q (inj₂ s) = no (<¬⊲ s)

dec-of : ∀ {x a} → (a ⊲ x) ⊎ (x ⊲ a) → Dec (x ⊲ a)
dec-of (inj₂ q) = yes q
dec-of (inj₁ q) = dec-lt q (toLtA q)

dec⊲ : ∀ {x a L} → x ⊲ L → a ⊲ L → Lg L → Dec (x ⊲ a)
dec⊲ e i l = dec-of (cmpF e i l)

-- 外层世界 0: 可入就是等于 0 (不需要上界)
adm₀ : ∀ {x} → x ⊲ azero → x ≡ azero
adm₀ C.self = refl
```

## §3 读回层

```agda
Ly : H₀ → Ht
Ly hz = hs hz
Ly (hs c) = hs (Ly c)
Ly (hl f) = hl (λ n → Ly (f n))
Ly (hΩ κ g) = hΩ κA (λ x → Ly (g x))
```

## §4 带外层世界的层结构

```agda
module LvM (a : A) where
  Lv : H₀ → KS
  Lv hz = S₀
  Lv (hs c) = step (Lv c)
  Lv (hl f) = sup ℕ (λ n → step (Lv (f n)))
  Lv (hΩ κ g) = sup (Σ A (λ x → x ⊲ a)) (λ p → step (Lv (g (proj₁ p))))

  -- 第 0 支总可入
  o⋆ : Σ A (λ x → x ⊲ a)
  o⋆ = azero , z⊲ a

  eA : ∀ c → Emb S₀ (Lv c)
  eA hz = idE S₀
  eA (hs c) = compE (eA c) (inj₁E (Lv c))
  eA (hl f) = compE (compE (eA (f 0)) (inj₁E (Lv (f 0)))) (ιE {F = λ n → step (Lv (f n))} 0)
  eA (hΩ κ g) = compE (compE (eA (g azero)) (inj₁E (Lv (g azero)))) (ιE {F = λ p → step (Lv (g (proj₁ p)))} o⋆)

  eS : ∀ c → Emb (step S₀) (step (Lv c))
  eS hz = idE (step S₀)
  eS (hs c) = compE (eS c) (inj₁E (step (Lv c)))
  eS (hl f) = compE (compE (eS (f 0)) (ιE {F = λ n → step (Lv (f n))} 0)) (inj₁E (Lv (hl f)))
  eS (hΩ κ g) = compE (compE (eS (g azero)) (ιE {F = λ p → step (Lv (g (proj₁ p)))} o⋆)) (inj₁E (Lv (hΩ κ g)))

  -- 第 1 层 (Ly hz) 没有 nμ, 其余层的 nμ 读成第一个新种类
  eM : ∀ c → NZ₁ (Ly c) → Emb (step S₀) (Lv c)
  eM hz ()
  eM (hs c) _ = eS c
  eM (hl f) _ = compE (eS (f 0)) (ιE {F = λ n → step (Lv (f n))} 0)
  eM (hΩ κ g) _ = compE (eS (g azero)) (ιE {F = λ p → step (Lv (g (proj₁ p)))} o⋆)
```

## §5 沿外层路径的嵌入 (W1 的部分和外层界上的单调)

外层界沿 `A`-世界 $a$ 里的路径 $p : c \lhd_{[a]} c'$ 长高时 (W1: $B_{s+1}=B_s\boxplus\sigma_s$, `⊞-fst`), 层结构沿 $p$ 嵌入. 走进 $\Omega$-结点 (`hLim e p`) 时, 路径自带的证据 $e : x\lhd a$ **就是** `Lv a` 的种类下标的证据: 不判定, 不搬运.

```agda
  embP : ∀ {c c′ : H₀} → c ⊲[ a ] c′ → Emb (Lv c) (Lv c′)
  embP {c} hself = idE (Lv c)
  embP (hsuc {b = d} p) = compE (embP p) (inj₁E (Lv d))
  embP (hlim {f = f} n p) = compE (compE (embP p) (inj₁E (Lv (f n)))) (ιE {F = λ n → step (Lv (f n))} n)
  embP (hLim {g = g} {c = x} e p) =
    compE (compE (embP p) (inj₁E (Lv (g x)))) (ιE {F = λ q → step (Lv (g (proj₁ q)))} (x , e))
```
