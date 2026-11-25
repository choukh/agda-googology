# 项模型: 记号项在树的代数里求值

> 判决: 验收侧定义, 条件 (排中律作模块参数), 读记号, 不进成品. 定义写得出: `⟦ t ⟧` 对项结构递归, 给出层号, 证据与树; ψ_u(b) 是 ψ♯ 朝 `⟦ u ⟧` 读成的层号折 `⟦ b ⟧`, 和是经典取大后经 `τ` 搬进公共层号再做树加法.
> 编译定理: 后继与项模型交换 (`⟦sucT⟧`), 标准形的和 `∔` 与后继交换 (`∔-sucT`). 没有值定理, 不否定什么.
> 命名关系与 B 的各行在 `YiNMName`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNMTerm where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRVLevel
open import OCF.Lean.YiNMSharp
import OCF.Align.EboLeanDef as E
```

## 标准形的和

`a ∔ b`: 从 a 的头起逐项与 b 的首项比较, 第一个严格小于 b 首项的主项起全部丢掉 (a 降序时就是序数和的标准形).

```agda
dr : E.Cmp → E.PT → E.T → E.T → E.T
dr E.lt x r b = b
dr E.eq x r b = x ∷ r
dr E.gt x r b = x ∷ r

infixl 6 _∔_
_∔_ : E.T → E.T → E.T
[]       ∔ b        = b
(x ∷ xs) ∔ []       = x ∷ xs
(x ∷ xs) ∔ (y ∷ ys) = dr (E.cmpᴾ x y) x (xs ∔ (y ∷ ys)) (y ∷ ys)

∔-[] : ∀ K → K ∔ [] ≡ K
∔-[] []       = refl
∔-[] (x ∷ xs) = refl

dr-𝟏 : ∀ x r → dr (E.cmpᴾ x E.𝟏) x r (E.𝟏 ∷ []) ≡ x ∷ r
dr-𝟏 (E.ψ [] [])            r = refl
dr-𝟏 (E.ψ [] (_ ∷ _))       r = refl
dr-𝟏 (E.ψ (_ ∷ _) a)        r = refl

dr-suc : ∀ m x r b → dr m x (E.sucT r) (E.sucT b) ≡ E.sucT (dr m x r b)
dr-suc E.lt x r b = refl
dr-suc E.eq x r b = refl
dr-suc E.gt x r b = refl

∔-sucT : ∀ K c → K ∔ E.sucT c ≡ E.sucT (K ∔ c)
∔-sucT []       c        = refl
∔-sucT (x ∷ xs) []       = trans (dr-𝟏 x (xs ∔ (E.𝟏 ∷ []))) (cong (x ∷_) (trans (∔-sucT xs []) (cong E.sucT (∔-[] xs))))
∔-sucT (x ∷ xs) (y ∷ ys) =
  trans (cong (λ r → dr (E.cmpᴾ x y) x r (E.sucT (y ∷ ys))) (∔-sucT xs (y ∷ ys)))
        (dr-suc (E.cmpᴾ x y) x (xs ∔ (y ∷ ys)) (y ∷ ys))
```

## 项模型

`M`: 一棵树连同它所在的层号与证据. `sv` 是树的严格值 (读回), `rd` 是把树读成层号 (块自己的读法 `k ⊕ ↑ k x`, 带证据 `rdOk`). `comb` 是和: 两个层号经典取大, 值低的一侧经 `τ` 搬过去, 再做树加法.

```agda
record M : Set where
  constructor mk
  field
    lv : L
    ok : Ok lv
    tr : Tr lv
open M public

sv : M → L
sv m = ↑ (lv m) (tr m)

rd : M → L
rd m = lv m ⊕ sv m

rdOk : (m : M) → Ok (rd m)
rdOk m = Ok⊕ (lv m) (sv m) (ok m) (OkO↑ (lv m) (lv m) (ok m) self (tr m))

sucM : M → M
sucM m = mk (lv m) (ok m) (suc (tr m))

module Term (lem : LEM) where
  open Sharp lem

  comb′ : (m₁ m₂ : M) → (lv m₂ ≼ᴸ lv m₁) ⊎ (lv m₁ ≺ᴸ lv m₂) → M
  comb′ m₁ m₂ (inj₁ le) =
    mk (lv m₁) (ok m₁) (tr m₁ + τ (lv m₂) (lv m₁) (ok m₂) (ok m₁) (wfL (lv m₂)) le (tr m₂))
  comb′ m₁ m₂ (inj₂ lt) =
    mk (lv m₂) (ok m₂) (τ (lv m₁) (lv m₂) (ok m₁) (ok m₂) (wfL (lv m₁)) (≺→≼ (lv m₂) lt) (tr m₁) + tr m₂)

  comb : M → M → M
  comb m₁ m₂ = comb′ m₁ m₂ (Dk (lv m₂) (lv m₁))

  mutual
    ⟦_⟧ : E.T → M
    ⟦ [] ⟧     = mk zero tt zero
    ⟦ x ∷ xs ⟧ = comb ⟦ x ⟧ᴾ ⟦ xs ⟧

    ⟦_⟧ᴾ : E.PT → M
    ⟦ E.ψ u a ⟧ᴾ = mk (rd ⟦ u ⟧) (rdOk ⟦ u ⟧)
      (proj₁ (ψ♯ (lv ⟦ a ⟧) (ok ⟦ a ⟧) B♯ (rd ⟦ u ⟧) (rdOk ⟦ u ⟧) (Ωt (rd ⟦ u ⟧)) (tr ⟦ a ⟧)))

  lev : E.T → L
  lev t = rd ⟦ t ⟧

  levOk : (t : E.T) → Ok (lev t)
  levOk t = rdOk ⟦ t ⟧
```

## 后继与项模型交换

`τ` 与树加法都逐字穿过 `suc`, 所以 `⟦ c + 1 ⟧` 就是 `⟦ c ⟧` 的后继, 层号不变. 1 的模型是第 0 层的 `suc zero`.

```agda
  ⟦𝟏⟧ : ⟦ E.𝟏 ∷ [] ⟧ ≡ mk zero tt (suc zero)
  ⟦𝟏⟧ = refl

  comb′-suc : ∀ m₁ m₂ d → comb′ m₁ (sucM m₂) d ≡ sucM (comb′ m₁ m₂ d)
  comb′-suc m₁ m₂ (inj₁ le) = refl
  comb′-suc m₁ m₂ (inj₂ lt) = refl

  ⟦sucT⟧ : ∀ c → ⟦ E.sucT c ⟧ ≡ sucM ⟦ c ⟧
  ⟦sucT⟧ []       = refl
  ⟦sucT⟧ (x ∷ xs) = trans (cong (comb ⟦ x ⟧ᴾ) (⟦sucT⟧ xs)) (comb′-suc ⟦ x ⟧ᴾ ⟦ xs ⟧ (Dk (lv ⟦ xs ⟧) (lv ⟦ x ⟧ᴾ)))
```
