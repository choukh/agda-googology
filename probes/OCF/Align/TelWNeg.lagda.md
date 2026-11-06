# 望远镜世界 (三): 推入的位置由路径自选, 升高一个位置就失去可比

> 不含记号. 入口 [TelW](TelW.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> [TelWOm](TelWOm.lagda.md) 说固定望远镜装不下 $x\mapsto\Omega_x$, 分支体必须推入新位置. 推入的位置要一个界. 折叠的历史里, 同一层号会被推入不止一次 (同一个分支被走两次, 或两个分支读回同一层号), 于是**一个种类的出现可以落在同层的几个位置上**. 若由路径自选 (`AdmF`: 落在任一同层位置之下即可), `cmpB` 在 Ω-节点处要的 "同一界之下可比" 就变成 "这些位置的界的并之下可比". 本篇在 `TelWTy.ST` 本身上 (望远镜 `lz ∷ lz ∷ []`, 两个同层位置, 坐标是第 0 层的值 `HB S⊥`) 证明:
>
> - `cmpF-Γ₀`: 世界 $[1,\ \omega']$ ($\omega'=\lim_n (n+2)$) 合法, 自选的并之下可比 (前提可满足).
> - **`raise→¬cmp`**: 把位置 0 的界升成 $1\boxplus\omega$ (`TelWTy.rais`, 定义地只改这一位置) 之后不再可比: $1\boxplus\omega$ 与 $\omega'$ 互不为第一位置. 一般形 `sel→¬cmp`: 任何满足 `at`/`off` 的选择性升高都如此.
> - **`exists→¬cmp`**: 新位置的界若由路径存在地选取 (世界里没有它的条目), 一开始就不可比.
> - `occ-find→dec`: 若改为按出现查位置 (出现由分支坐标确定), 就是 `ClosedReview1.find→dec` 在坐标类型上的实例: 坐标相等可判定.
>
> **范围.** 否定的是 "同层位置由路径自选 + 回灌升高一个位置" 与 "新位置的界存在地选取" 这两个接口; 不否定 D1 本身. 第三种出路 "每个出现恰好一个位置" 要么按出现或按层号查 (`occ-find→dec`, `find→dec`), 要么把世界做成分支坐标上的积 (那就是 `DiagKLev.upd→wdec` 的 $I$ = 坐标); 这三种是否穷尽是**判断**.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TelWNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (LH; lz; Lv; FL; S⊥)
open import OCF.Align.TelWTy
import OCF.Align.ClosedReview1 as CR
```

## §1 第 0 层的几个值

`HB S⊥` 是第 0 层的值 (只有 $0$, 后继, ℕ-极限). 世界是 `⊤`.

```agda
V₀ : Set
V₀ = HB S⊥

nat : ℕ → V₀
nat zero = hz
nat (suc n) = hs (nat n)

one ω ω′ : V₀
one = hs hz
ω = hl nat
ω′ = hl (λ n → nat (suc (suc n)))

Lg-nat : ∀ n → LgB (nat n)
Lg-nat zero = tt
Lg-nat (suc n) = Lg-nat n

Lg-ω : LgB ω
Lg-ω = (λ n → hsuc hself) , Lg-nat

Lg-ω′ : LgB ω′
Lg-ω′ = (λ n → hsuc hself) , (λ n → Lg-nat (suc (suc n)))

-- 1 ⊞ ω, 写成单态的名字, 免得 with 抽象里推不出种类结构
oneω : V₀
oneω = _⊞_ {S⊥} one ω

one⊲ω′ : one ⊲[ tt ] ω′
one⊲ω′ = hlim 0 (hsuc hself)
```

**两个互不为第一位置的极限.** $1\boxplus\omega=\lim_n(1\boxplus n)$ 与 $\omega'=\lim_n(n+2)$ 的第 0 项不同 ($1$ 对 $2$), 且极限不是有限值的第一位置. 不用函数外延: 只用 "`hl f ≡ hl g` 推出 `f 0 ≡ g 0`".

```agda
IsFin : V₀ → Set
IsFin hz = ⊤
IsFin (hs a) = IsFin a
IsFin (hl f) = ⊥
IsFin (hΩ () g)

fin⊲ : ∀ {a b : V₀} → IsFin b → a ⊲[ tt ] b → IsFin a
fin⊲ fb hself = fb
fin⊲ fb (hsuc p) = fin⊲ fb p
fin⊲ () (hlim n p)
fin⊲ {b = hΩ () g} fb (hLim e p)

fin-nat : ∀ n → IsFin (nat n)
fin-nat zero = tt
fin-nat (suc n) = fin-nat n

fin-1n : ∀ n → IsFin (_⊞_ {S⊥} one (nat n))
fin-1n zero = tt
fin-1n (suc n) = fin-1n n

⊲-hl : ∀ {a : V₀} {f : ℕ → V₀} → a ⊲[ tt ] hl f → (a ≡ hl f) ⊎ Σ ℕ (λ n → a ⊲[ tt ] f n)
⊲-hl hself = inj₁ refl
⊲-hl (hlim n p) = inj₂ (n , p)

private
  hd0 : V₀ → V₀
  hd0 (hl f) = f 0
  hd0 x = x

  pd : V₀ → V₀
  pd (hs x) = x
  pd x = x

  isZ : V₀ → Set
  isZ hz = ⊤
  isZ _ = ⊥

  1≢2 : ¬ (one ≡ nat 2)
  1≢2 e = subst isZ (cong pd e) tt

1ω⋪ω′ : ¬ (oneω ⊲[ tt ] ω′)
1ω⋪ω′ p = go (⊲-hl p)
  where
  go : (oneω ≡ ω′) ⊎ Σ ℕ (λ n → oneω ⊲[ tt ] nat (suc (suc n))) → ⊥
  go (inj₁ e) = 1≢2 (cong hd0 e)
  go (inj₂ (n , q)) = fin⊲ {b = nat (suc (suc n))} (fin-nat (suc (suc n))) q

ω′⋪1ω : ¬ (ω′ ⊲[ tt ] oneω)
ω′⋪1ω p = go (⊲-hl p)
  where
  go : (ω′ ≡ oneω) ⊎ Σ ℕ (λ n → ω′ ⊲[ tt ] _⊞_ {S⊥} one (nat n)) → ⊥
  go (inj₁ e) = 1≢2 (sym (cong hd0 e))
  go (inj₂ (n , q)) = fin⊲ {b = _⊞_ {S⊥} one (nat n)} (fin-1n n) q

-- 两者不可比
incmp : ¬ ((ω′ ⊲[ tt ] oneω) ⊎ (oneω ⊲[ tt ] ω′))
incmp = [ ω′⋪1ω , 1ω⋪ω′ ]′
```

## §2 两个同层位置, 路径自选

望远镜 `L2 = lz ∷ lz ∷ []`: 两个位置, 层号都是 $0$, 种类 `νT z`, `νT (s z)` 的坐标都是 `V₀`. `AdmF Γ c`: $c$ 落在任一位置的界之下.

```agda
L2 : List LH
L2 = lz ∷ lz ∷ []

AdmF : Tel L2 → V₀ → Set
AdmF Γ c = Bd (ST L2) (νT z) c Γ ⊎ Bd (ST L2) (νT (s z)) c Γ

CmpF : Tel L2 → Set
CmpF Γ = ∀ {c c′} → AdmF Γ c → AdmF Γ c′ → (c′ ⊲[ tt ] c) ⊎ (c ⊲[ tt ] c′)

Γ₀ : Tel L2
Γ₀ = (tt , one) ∷ (tt , ω′) ∷ []

Lg-Γ₀ : LgT Γ₀
Lg-Γ₀ = (tt , tt) , (tt , Lg-ω′) , tt

-- 前提可满足: 两个界在同一条链上, 自选的并之下可比
cmpF-Γ₀ : CmpF Γ₀
cmpF-Γ₀ e e′ = cmpB {S⊥} (to e) (to e′) tt Lg-ω′
  where
  to : ∀ {c} → AdmF Γ₀ c → c ⊲[ tt ] ω′
  to (inj₁ p) = ⊲ᴮ-tr p one⊲ω′
  to (inj₂ p) = p
```

**升高位置 0.** `rais z ω Γ₀` 定义地是 $[1\boxplus\omega,\ \omega']$; 合法 (`Lg-rais`), 比原世界大 (`rais-≤`), 但自选的并之下有一对不可比的坐标.

```agda
Γ₁ : Tel L2
Γ₁ = rais z ω Γ₀

Lg-Γ₁ : LgT Γ₁
Lg-Γ₁ = Lg-rais z ω Γ₀ Lg-Γ₀ Lg-ω

Γ₀≤Γ₁ : Γ₀ ≤T Γ₁
Γ₀≤Γ₁ = rais-≤ z ω Γ₀

¬cmpF-Γ₁ : ¬ CmpF Γ₁
¬cmpF-Γ₁ cf = incmp (cf {oneω} {ω′} (inj₁ hself) (inj₂ hself))

raise→¬cmp : ¬ (∀ (Γ : Tel L2) → LgT Γ → CmpF Γ → ∀ δ → LgB δ → CmpF (rais z δ Γ))
raise→¬cmp h = ¬cmpF-Γ₁ (h Γ₀ Lg-Γ₀ cmpF-Γ₀ ω Lg-ω)
```

**一般形.** 不用 `rais` 的具体写法: 任何世界操作, 只要在位置 0 处是 $1\boxplus\omega$ (`at`), 位置 1 不动 (`off`), 都破坏可比. 这是 "回灌恰好升高携带的那个位置" 的一切实现.

```agda
sel→¬cmp : (Γ : Tel L2) → bnd Γ z ≡ (tt , oneω) → bnd Γ (s z) ≡ (tt , ω′) → ¬ CmpF Γ
sel→¬cmp Γ e0 e1 cf = incmp (cf {oneω} {ω′} (inj₁ (subst (λ w → oneω ⊲[ proj₁ w ] proj₂ w) (sym e0) hself))
                                            (inj₂ (subst (λ w → ω′ ⊲[ proj₁ w ] proj₂ w) (sym e1) hself)))
```

## §3 新位置的界由路径存在地选取

若推入的位置在世界里没有条目, 由路径自己挑一个合法的界, 同一个出现的两条路径就可以挑两个不在一条链上的界.

```agda
AdmE : V₀ → Set
AdmE c = Σ (Wd (FL lz)) (λ β → LgW (FL lz) β × Bd (FL lz) (inj₂ tt) c β)

exists→¬cmp : ¬ (∀ {c c′} → AdmE c → AdmE c′ → (c′ ⊲[ tt ] c) ⊎ (c ⊲[ tt ] c′))
exists→¬cmp h = incmp (h {oneω} {ω′} ((tt , oneω) , (tt , Lg-⊞ one ω tt Lg-ω) , hself) ((tt , ω′) , (tt , Lg-ω′) , hself))
```

## §4 按出现查位置

出现 (分支体里的一个推入) 由它上方的分支坐标确定. 若世界把出现映到位置并按出现查, 那就是 `ClosedReview1.Tele` 以坐标为 `L` 的 `Find`, 推出坐标相等可判定. 实例取第 0 层的值; 更高层的坐标同理 (`Tele` 对一切 `L`).

```agda
module Occ = CR.Tele V₀ (λ _ → ⊤) (λ _ _ → ⊤) (λ _ → ⊤) (λ _ _ _ → inj₁ tt)

occ-find→dec : Occ.Find → ∀ (c c′ : V₀) → (c ≡ c′) ⊎ ¬ (c ≡ c′)
occ-find→dec = Occ.find→dec
```
