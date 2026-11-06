# RaiseC (一): `A` 上的升界算子, 哪些形状不行

> 不含记号. 入口 [RaiseC](RaiseC.lagda.md). 对着接口 [RaiseIf](RaiseIf.lagda.md) ("接口定稿 2026-11-05 (主审写, 首次编译通过后定稿)") 写, 导入它, 不改它.
>
> **一个基本事实.** `A` 的 `⊲` 就是自反的子项关系 (构造子 `self`, `suc`, `lim` 恰好走进前驱与每一个分支). 所以 $v\lhd R\,a\,v$ 说的是: $v$ 字面地是 $R\,a\,v$ 的一棵子树. 合法的树的一切子树两两可比 (`cmpF`).
>
> 本篇的定理 (全部编译过):
>
> 1. **`R-in→cmp`, `R-cmp→in`**: 对任一 `RaiseA` 与合法的 $a, v$: $v\lhd R\,a\,v$ 当且仅当 $a, v$ 可比. 所以 $R$ 必须**恰好在可比时**把 $v$ 放进输出; 对 `no-joinA` 的那一对 (`alim evA`, `alim odA`), $R$ 的输出一定**不含** $v$ (**`R-out-evod`**). 这就是 $R$ 不撞 `no-joinA` 的原因, 也是代价.
> 2. **`no-always`**: 任何 $R$ 若满足 `R-lo`, `R-lg`, 又对一切合法 $a, v$ 有 $v\lhd R\,a\,v$ ("总把 $v$ 放进去"), 就撞 `no-joinA`. 推论: "以 $v$ 为底" 的一族 $R\,a\,v = v\oplus F\,a\,v$ 都违反 `R-lo` (**`no-on-v`**).
> 3. **`no-on-a`**: "以 $a$ 为底" 的一族 $R\,a\,v = a\oplus F\,a\,v$ 都违反 `R-hi` (实例 $a=1$, $v=\omega$).
> 4. **`no-only-a`, `no-only-v`**: 只看 $a$ 的 $R$ 违反 `R-hi`, 只看 $v$ 的 $R$ 违反 `R-lo` (都撞 `no-joinA`).
> 5. **`fst-fails`, `snd-fails`**: 接口文件头说的 $R\,a\,v=a$ 与 $R\,a\,v=v$ 的反例, 写成定理.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RaiseCBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲; cmpF; Strict; ss; sl; S→⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadBase using (_⊞_; ⊞-fst; Lg-⊞)
open import OCF.Align.HtTowerNeg using (evA; odA; Lg-evA; Lg-odA; no-joinA)
open import OCF.Align.RaiseIf using (RaiseA; R; R-lo; R-hi; R-lg)
```

## §1 子项的反对称

`Strict a b`: $a$ 是 $b$ 的真子项. 它不自反 (`irrS`, 对树结构递归), 所以 `⊲` 反对称 (`⊲-antisym`). 后面 (`RaiseCBd`) 用它说有界的升界算子的值与证据无关.

```agda
S⊲ : ∀ {a b c} → Strict a b → b ⊲ c → Strict a c
S⊲ r C.self = r
S⊲ r (C.suc q) = ss (⊲-tr (S→⊲ r) q)
S⊲ r (C.lim n q) = sl n (⊲-tr (S→⊲ r) q)

irrS : ∀ a → ¬ Strict a a
irrS (asuc b) (ss P) = irrS b (S⊲ (ss C.self) P)
irrS (alim f) (sl n P) = irrS (f n) (S⊲ (sl n C.self) P)

⊲-split : ∀ {a b} → a ⊲ b → (a ≡ b) ⊎ Strict a b
⊲-split C.self = inj₁ refl
⊲-split (C.suc p) = inj₂ (ss p)
⊲-split (C.lim n p) = inj₂ (sl n p)

⊲-antisym : ∀ {a b} → a ⊲ b → b ⊲ a → a ≡ b
⊲-antisym {a} p q with ⊲-split p
... | inj₁ e = e
... | inj₂ r = ⊥-elim (irrS a (S⊲ r q))
```

## §2 $v\lhd R\,a\,v$ 当且仅当可比

```agda
module _ (ρ : RaiseA) where
  R-in→cmp : ∀ {a v} → Lg a → Lg v → v ⊲ R ρ a v → (v ⊲ a) ⊎ (a ⊲ v)
  R-in→cmp la lv p = cmpF (R-lo ρ la lv) p (R-lg ρ la lv)

  R-cmp→in : ∀ {a v} → Lg a → Lg v → (v ⊲ a) ⊎ (a ⊲ v) → v ⊲ R ρ a v
  R-cmp→in la lv (inj₁ va) = ⊲-tr va (R-lo ρ la lv)
  R-cmp→in la lv (inj₂ av) = R-hi ρ la lv av

  R-out-evod : ¬ (alim odA ⊲ R ρ (alim evA) (alim odA))
  R-out-evod p = no-joinA (R ρ (alim evA) (alim odA) , R-lg ρ Lg-evA Lg-odA , R-lo ρ Lg-evA Lg-odA , p)
```

## §3 总把 $v$ 放进去: 撞 `no-joinA`

```agda
Lo Hi Gd Al : (A → A → A) → Set
Lo F = ∀ {a v} → Lg a → Lg v → a ⊲ F a v
Hi F = ∀ {a v} → Lg a → Lg v → a ⊲ v → v ⊲ F a v
Gd F = ∀ {a v} → Lg a → Lg v → Lg (F a v)
Al F = ∀ {a v} → Lg a → Lg v → v ⊲ F a v

no-always : ∀ F → Lo F → Gd F → ¬ Al F
no-always F lo gd al = no-joinA (F (alim evA) (alim odA) , gd Lg-evA Lg-odA , lo Lg-evA Lg-odA , al Lg-evA Lg-odA)

-- 以 v 为底: R a v = v ⊞ G a v, 且合法 ⇒ 违反 R-lo
no-on-v : ∀ (G : A → A → A) → (∀ {a v} → Lg a → Lg v → Lg (G a v)) → ¬ Lo (λ a v → v ⊞ G a v)
no-on-v G lg lo = no-always (λ a v → v ⊞ G a v) lo (λ {a} {v} la lv → Lg-⊞ v (G a v) lv (lg la lv)) (λ {a} {v} _ _ → ⊞-fst v (G a v))

-- 只看 v: R a v = H v ⇒ 违反 R-lo (取 v = 0)
no-only-v : ∀ (H : A → A) → Gd (λ a v → H v) → ¬ Lo (λ a v → H v)
no-only-v H gd lo = no-joinA (H azero , gd {azero} {azero} tt tt , lo Lg-evA tt , lo Lg-odA tt)

-- 只看 a: R a v = G a ⇒ 违反 R-hi (取 a = 0, 0 是一切树的子项)
no-only-a : ∀ (G : A → A) → Gd (λ a v → G a) → ¬ Hi (λ a v → G a)
no-only-a G gd hi =
  no-joinA (G azero , gd {azero} {azero} tt tt , hi tt Lg-evA (z⊲ (alim evA)) , hi tt Lg-odA (z⊲ (alim odA)))
```

## §4 以 $a$ 为底: 违反 `R-hi`

$1\oplus y$ 的一切子树都不是 "第 0 项为 $0$ 的极限" (`GoodT`), 而 $\omega=\lim(0,1,2,\dots)$ 是. 所以 $\omega\not\lhd 1\oplus y$, 而 $1\lhd\omega$.

```agda
natA : ℕ → A
natA zero = azero
natA (suc n) = asuc (natA n)

ωA : A
ωA = alim natA

Lg-ωA : Lg ωA
Lg-ωA = (λ n → C.suc C.self) , lg
  where
  lg : ∀ n → Lg (natA n)
  lg zero = tt
  lg (suc n) = lg n

oneA : A
oneA = asuc azero

one⊲ω : oneA ⊲ ωA
one⊲ω = C.lim 1 C.self

IsZ : A → Set
IsZ azero = ⊤
IsZ (asuc _) = ⊥
IsZ (alim _) = ⊥

Bad : A → Set
Bad (alim f) = IsZ (f 0)
Bad _ = ⊥

GoodT : A → Set
GoodT azero = ⊤
GoodT (asuc a) = GoodT a
GoodT (alim f) = ¬ IsZ (f 0) × (∀ n → GoodT (f n))

good-self : ∀ c → GoodT c → ¬ Bad c
good-self azero g ()
good-self (asuc c) g ()
good-self (alim f) g b = proj₁ g b

good⊲ : ∀ {x c} → x ⊲ c → GoodT c → ¬ Bad x
good⊲ {c = c} C.self g = good-self c g
good⊲ (C.suc p) g = good⊲ p g
good⊲ (C.lim n p) g = good⊲ p (proj₂ g n)

nz-one⊞ : ∀ y → ¬ IsZ (oneA ⊞ y)
nz-one⊞ azero ()
nz-one⊞ (asuc y) ()
nz-one⊞ (alim f) ()

good-one⊞ : ∀ y → GoodT (oneA ⊞ y)
good-one⊞ azero = tt
good-one⊞ (asuc y) = good-one⊞ y
good-one⊞ (alim f) = nz-one⊞ (f 0) , (λ n → good-one⊞ (f n))

ω∉one⊞ : ∀ y → ¬ (ωA ⊲ oneA ⊞ y)
ω∉one⊞ y p = good⊲ p (good-one⊞ y) tt

-- 以 a 为底: R a v = a ⊞ G a v ⇒ 违反 R-hi (a = 1, v = ω)
no-on-a : ∀ (G : A → A → A) → ¬ Hi (λ a v → a ⊞ G a v)
no-on-a G hi = ω∉one⊞ (G oneA ωA) (hi tt Lg-ωA one⊲ω)
```

## §5 接口文件头的两个平凡候选

```agda
fst-fails : ¬ Hi (λ a v → a)
fst-fails hi with hi {azero} {oneA} tt tt (C.suc C.self)
... | ()

snd-fails : ¬ Lo (λ a v → v)
snd-fails lo with lo {oneA} {azero} tt tt
... | ()

-- 两者各自满足的那两条
fst-lo : Lo (λ a v → a)
fst-lo _ _ = C.self

snd-hi : Hi (λ a v → v)
snd-hi _ _ _ = C.self
```

`a ⊞ v` 满足 `R-lo` 与 `R-lg` (`⊞-fst`, `Lg-⊞`), 违反 `R-hi` (`no-on-a` 取 `G a v = v`); `v ⊞ a` 满足 `R-hi` 与 `R-lg`, 违反 `R-lo` (`no-on-v` 取 `G a v = a`):

```agda
add-lo : Lo (λ a v → a ⊞ v)
add-lo {a} {v} _ _ = ⊞-fst a v

add-hi-fails : ¬ Hi (λ a v → a ⊞ v)
add-hi-fails = no-on-a (λ a v → v)

swap-hi : Hi (λ a v → v ⊞ a)
swap-hi {a} {v} _ _ _ = ⊞-fst v a

swap-lo-fails : ¬ Lo (λ a v → v ⊞ a)
swap-lo-fails = no-on-v (λ a v → a) (λ la lv → la)
```
