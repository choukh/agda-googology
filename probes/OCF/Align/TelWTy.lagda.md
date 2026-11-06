# 望远镜世界 (一): 种类是位置, 层号在类型里

> 不含记号. 入口 [TelW](TelW.lagda.md). 设计 D1 ([Survey/ClosedTermReview.md](../../Survey/ClosedTermReview.md) §2) 的第一步: 把 [HtTowerTy](HtTowerTy.lagda.md) 的种类结构 `KS` 实例化成**望远镜**.
>
> - 层号表 `lvs : List LH` (层号取 [LFReTy](LFReTy.lagda.md) 的一次封闭块) 放在类型里; 世界 `Tel lvs` 每个位置一个条目, 条目是 `FL ℓ = step (Lv ℓ)` 的世界, 即 "第 ℓ 层的值的世界, 加 Ω_{ℓ+1} 坐标的界".
> - 种类 `Σ (Pos lvs) (K ∘ FL ∘ lv)`: 位置加该层里的种类. 坐标、界、第一位置都是该位置那一层的 (`ST`).
> - 比较 `cmpT` 就是 `cmpB {ST lvs}`, **对一切 `lvs` 一条**, 不新写.
> - 恰好改一个位置 (`upd`, `at`, `off`, 取自 [ClosedReview1](ClosedReview1.lagda.md)) 是定义; 升高一个位置的界 `rais` 使世界变大 (`rais-≤`), 保合法 (`Lg-rais`), 不判定任何层号.
> - 推入新层 `push`, 旧高度弱化 `wkH`: 保第一位置 (`wk-⊲`), 保合法 (`Lg-wk`); 旧界原样 (定义相等).
>
> 与 `sup` 的区别只在世界: `sup (Pos lvs) (FL ∘ lv)` 的世界是 `Pos lvs` 上的函数, 这里是同形的有限列表, 改一个位置不必判定 (位置相等本来也可判定, `decPos`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TelWTy where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (LH; Lv; FL)
import OCF.Align.ClosedReview1 as CR
```

## §1 望远镜

`ClosedReview1.Tele` 的结构部分 (`Tel`, `Pos`, `lv`, `bnd`, `upd`, `at`, `off`, `decPos`, `push`, `wk`) 不用它的 `⊲` 与 `cmp`; 这里取平凡的那两个参数, 只借结构. 条目类型是 `Wd (FL ℓ)`.

```agda
module TT = CR.Tele LH (λ ℓ → Wd (FL ℓ)) (λ _ _ → ⊤) (λ _ → ⊤) (λ _ _ _ → inj₁ tt)
open TT public using (Tel; []; _∷_; Pos; z; s; lv; bnd; upd; at; off; decPos; push; wk; bnd-wk)

LgT : ∀ {lvs} → Tel lvs → Set
LgT [] = ⊤
LgT (_∷_ {ℓ} b Γ) = LgW (FL ℓ) b × LgT Γ

lg-at : ∀ {lvs} {Γ : Tel lvs} → LgT Γ → ∀ p → LgW (FL (lv p)) (bnd Γ p)
lg-at {Γ = b ∷ Γ} (lb , lΓ) z = lb
lg-at {Γ = b ∷ Γ} (lb , lΓ) (s p) = lg-at lΓ p

infix 4 _≤T_
_≤T_ : ∀ {lvs} → Tel lvs → Tel lvs → Set
[] ≤T [] = ⊤
(_∷_ {ℓ} b Γ) ≤T (b′ ∷ Γ′) = _≤w_ (FL ℓ) b b′ × Γ ≤T Γ′

≤T-rf : ∀ {lvs} {Γ : Tel lvs} → Γ ≤T Γ
≤T-rf {Γ = []} = tt
≤T-rf {Γ = _∷_ {ℓ} b Γ} = ≤w-rf (FL ℓ) , ≤T-rf

≤T-tr : ∀ {lvs} {Γ Δ Θ : Tel lvs} → Γ ≤T Δ → Δ ≤T Θ → Γ ≤T Θ
≤T-tr {Γ = []} {Δ = []} {Θ = []} _ _ = tt
≤T-tr {Γ = _∷_ {ℓ} _ _} {Δ = _ ∷ _} {Θ = _ ∷ _} (p , P) (q , Q) = ≤w-tr (FL ℓ) p q , ≤T-tr P Q

≤-at : ∀ {lvs} {Γ Γ′ : Tel lvs} → Γ ≤T Γ′ → ∀ p → _≤w_ (FL (lv p)) (bnd Γ p) (bnd Γ′ p)
≤-at {Γ = _ ∷ _} {Γ′ = _ ∷ _} (q , Q) z = q
≤-at {Γ = _ ∷ _} {Γ′ = _ ∷ _} (q , Q) (s p) = ≤-at Q p
```

## §2 种类结构 `ST lvs`

每个字段都是 "取位置 $p$ 的条目, 交给 `FL (lv p)` 的同名字段". 与 `sup` 的字段逐个同形.

```agda
module STd (lvs : List LH) where
  Kᵀ : Set
  Kᵀ = Σ (Pos lvs) (λ p → K (FL (lv p)))

  Eᵀ : Kᵀ → Set
  Eᵀ (p , κ) = E (FL (lv p)) κ

  Bdᵀ : (κ : Kᵀ) → Eᵀ κ → Tel lvs → Set
  Bdᵀ (p , κ) c Γ = Bd (FL (lv p)) κ c (bnd Γ p)

  Prᵀ : (κ : Kᵀ) → Tel lvs → Eᵀ κ → Eᵀ κ → Set
  Prᵀ (p , κ) Γ c c′ = Pr (FL (lv p)) κ (bnd Γ p) c c′

  Bd↑ᵀ : ∀ {κ c Γ Γ′} → Γ ≤T Γ′ → Bdᵀ κ c Γ → Bdᵀ κ c Γ′
  Bd↑ᵀ {p , κ} q e = Bd↑ (FL (lv p)) (≤-at q p) e

  cmpKᵀ : ∀ {κ c c′ Γ} → Bdᵀ κ c Γ → Bdᵀ κ c′ Γ → LgT Γ → Prᵀ κ Γ c′ c ⊎ Prᵀ κ Γ c c′
  cmpKᵀ {p , κ} e e′ lΓ = cmpK (FL (lv p)) e e′ (lg-at lΓ p)

  LgEᵀ : (κ : Kᵀ) → Eᵀ κ → Set
  LgEᵀ (p , κ) = LgE (FL (lv p)) κ

  lgBdᵀ : ∀ {κ c Γ} → Bdᵀ κ c Γ → LgT Γ → LgEᵀ κ c
  lgBdᵀ {p , κ} e lΓ = lgBd (FL (lv p)) e (lg-at lΓ p)

  botᵀ : (κ : Kᵀ) → Eᵀ κ
  botᵀ (p , κ) = bot (FL (lv p)) κ

  botBdᵀ : ∀ κ Γ → Bdᵀ κ (botᵀ κ) Γ
  botBdᵀ (p , κ) Γ = botBd (FL (lv p)) κ (bnd Γ p)

ST : List LH → KS
ST lvs = record
  { K = Kᵀ ; E = Eᵀ ; Wd = Tel lvs ; LgW = LgT ; _≤w_ = _≤T_ ; ≤w-rf = ≤T-rf ; ≤w-tr = ≤T-tr
  ; Bd = Bdᵀ ; Pr = Prᵀ ; Bd↑ = λ {κ} → Bd↑ᵀ {κ} ; cmpK = λ {κ} → cmpKᵀ {κ}
  ; LgE = LgEᵀ ; lgBd = λ {κ} → lgBdᵀ {κ} ; bot = botᵀ ; botBd = botBdᵀ }
  where open STd lvs

HT : List LH → Set
HT lvs = HB (ST lvs)

-- 第 p 个位置的新种类, 即 Ω_{lv p + 1}
νT : ∀ {lvs} → Pos lvs → K (ST lvs)
νT p = p , inj₂ tt
```

**比较: 一条, 对一切望远镜.** 同一个世界之下的两个第一位置可比. 它在 Ω-节点处调用的是位置 $p$ 那一层的 `cmpK`, 也就是 `cmpB {Lv (lv p)}` 或更低层的; 从头到尾没有比较两个层号.

```agda
cmpT : ∀ {lvs} {a b L : HT lvs} {Γ : Tel lvs} → a ⊲[ Γ ] L → b ⊲[ Γ ] L → LgT Γ → LgB L → (b ⊲[ Γ ] a) ⊎ (a ⊲[ Γ ] b)
cmpT {lvs} = cmpB {ST lvs}
```

## §3 升高一个位置的界

条目 `(w , b)`: $w$ 是第 ℓ 层的值的世界, $b$ 是 Ω_{ℓ+1} 坐标的界. 回灌把 $b$ 换成 $b\boxplus\delta$, 内层世界 $w$ 不动. 只改位置 $p$, 其余位置定义地不动 (`off`).

```agda
raiseE : ∀ {ℓ} → Wd (FL ℓ) → HB (Lv ℓ) → Wd (FL ℓ)
raiseE (w , b) δ = w , (b ⊞ δ)

rais : ∀ {lvs} (p : Pos lvs) → HB (Lv (lv p)) → Tel lvs → Tel lvs
rais p δ Γ = upd p (raiseE (bnd Γ p) δ) Γ

rais-at : ∀ {lvs} (p : Pos lvs) δ (Γ : Tel lvs) → bnd (rais p δ Γ) p ≡ raiseE (bnd Γ p) δ
rais-at p δ Γ = at p (raiseE (bnd Γ p) δ) Γ

rais-≤ : ∀ {lvs} (p : Pos lvs) δ (Γ : Tel lvs) → Γ ≤T rais p δ Γ
rais-≤ {ℓ ∷ _} z δ (b ∷ Γ) = (≤w-rf (Lv ℓ) , ⊞-fst (proj₂ b) δ) , ≤T-rf
rais-≤ {ℓ ∷ _} (s p) δ (b ∷ Γ) = ≤w-rf (FL ℓ) , rais-≤ p δ Γ

Lg-rais : ∀ {lvs} (p : Pos lvs) δ (Γ : Tel lvs) → LgT Γ → LgB δ → LgT (rais p δ Γ)
Lg-rais z δ (b ∷ Γ) ((lw , lb) , lΓ) lδ = (lw , Lg-⊞ (proj₂ b) δ lb lδ) , lΓ
Lg-rais (s p) δ (b ∷ Γ) (lb , lΓ) lδ = lb , Lg-rais p δ Γ lΓ lδ
```

## §4 推入新层, 弱化

`wkH`: 旧高度的每个种类 $(p,\kappa)$ 改成 $(\mathtt s\,p,\kappa)$. 坐标类型字面不变 (`lv (s p)` 归约到 `lv p`), 旧界字面不变 (`bnd-wk`), 所以第一位置与合法原样搬过去.

```agda
module _ {ℓ : LH} {lvs : List LH} where
  wkH : HT lvs → HT (ℓ ∷ lvs)
  wkH hz = hz
  wkH (hs a) = hs (wkH a)
  wkH (hl f) = hl (λ n → wkH (f n))
  wkH (hΩ (p , κ) g) = hΩ (s p , κ) (λ c → wkH (g c))

  wk-⊲ : ∀ {a b : HT lvs} {Γ : Tel lvs} {β : Wd (FL ℓ)} → a ⊲[ Γ ] b → wkH a ⊲[ β ∷ Γ ] wkH b
  wk-⊲ hself = hself
  wk-⊲ (hsuc p) = hsuc (wk-⊲ p)
  wk-⊲ (hlim n p) = hlim n (wk-⊲ p)
  wk-⊲ (hLim e p) = hLim e (wk-⊲ p)

  private
    mo-wk : ∀ {p : Pos lvs} {κ} {g : E (FL (lv p)) κ → HT lvs} →
      (∀ {Γ c c′} → LgT Γ → Bd (ST lvs) (p , κ) c Γ → Bd (ST lvs) (p , κ) c′ Γ → Pr (ST lvs) (p , κ) Γ c c′ → g c ⊲[ Γ ] g c′) →
      ∀ {Δ : Tel (ℓ ∷ lvs)} {c c′} → LgT Δ → Bd (ST (ℓ ∷ lvs)) (s p , κ) c Δ → Bd (ST (ℓ ∷ lvs)) (s p , κ) c′ Δ →
      Pr (ST (ℓ ∷ lvs)) (s p , κ) Δ c c′ → wkH (g c) ⊲[ Δ ] wkH (g c′)
    mo-wk mo {β ∷ Γ} (lβ , lΓ) e e′ q = wk-⊲ (mo lΓ e e′ q)

  Lg-wk : ∀ (a : HT lvs) → LgB a → LgB (wkH a)
  Lg-wk hz l = tt
  Lg-wk (hs a) l = Lg-wk a l
  Lg-wk (hl f) (st , l) = (λ {Δ} n → wk-st Δ n) , (λ n → Lg-wk (f n) (l n))
    where
    wk-st : ∀ (Δ : Tel (ℓ ∷ lvs)) n → wkH (f n) ⊲[ Δ ] wkH (f (suc n))
    wk-st (β ∷ Γ) n = wk-⊲ (st n)
  Lg-wk (hΩ (p , κ) g) (mo , l) = mo-wk {p} {κ} {g} mo , (λ c lc → Lg-wk (g c) (l c lc))
```

推入不改旧界: 弱化过的位置在新世界里的界就是旧界, 定义相等.

```agda
push-old : ∀ {ℓ lvs} (β : Wd (FL ℓ)) (Γ : Tel lvs) (p : Pos lvs) → bnd (push β Γ) (wk p) ≡ bnd Γ p
push-old β Γ p = refl

Lg-push : ∀ {ℓ lvs} {β : Wd (FL ℓ)} {Γ : Tel lvs} → LgW (FL ℓ) β → LgT Γ → LgT (push β Γ)
Lg-push lβ lΓ = lβ , lΓ
```
