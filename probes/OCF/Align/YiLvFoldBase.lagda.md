# YiLvFold 底座二：派发的数据、保留结点、定义域与一般层的加法链

**档位：定义与编译定理，没有折叠。** `Way m k` 是一个结点 (层号 `k`) 在目标层 `m` 上的派发结果：保留时带槽位 `s` 与
`lev m s ≡ k`。`nodeAt` 按槽位造保留结点，不搬运下界与分支域。定义域 `Dom = OnlyP × Legal × Seedᶠ`。
`Chain` 是 `YiIrrFbBase.Chain₁` 把层号换成参数。入口 [YiLvFold](YiLvFold.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLvFoldBase where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (cO)
open import OCF.Align.YiIrrIf using (CP; Legal; iterate)
open import OCF.Align.YiIrrFoldSeed using (Seedᶠ)
open import OCF.Align.YiIrrFbRaw using (Cp-tr)
open import OCF.Align.YiIrrFbIf using (Pt; pt; at)
open import OCF.Align.YiLvIf using (Plain; OnlyP; lev)
open import OCF.Align.YiLvFoldAdd
```

## 1 派发的数据与保留结点

保留行要把层号 `k` 的结点放进 `Raw m` 的槽位 `s`。匹配 `lev m s ≡ k` 为 `refl` 之后，下界在 `Raw (lev m s)` 里；
`nodeAt` 对 `(m , s)` 递归走到 `suc k′` 的 `inj₁`，那里 `Low` 就是 `Raw k′`，所以不需要沿 `Low-lev` 搬运。

```agda
data Way (m k : LF) : Set where
  keep : (s : Pre m) → lev m s ≡ k → Way m k
  fold : Way m k

nodeAt : ∀ m (s : Pre m) (A : Alg m) (c : Raw (lev m s)) → Alg.T A →
  ((η : Raw (lev m s)) → .(Gd (lev m s) c η) → Alg.T A) → Alg.T A
nodeAt (suc k) (inj₁ _) A c t g = Alg.nT A (inj₁ tt) c t g
nodeAt (suc k) (inj₂ r) A c t g = nodeAt k r (shS A) c t g
nodeAt (lim f) (n , r) A c t g = nodeAt (f n) r (shL A n) c t g
nodeAt (lc k c₀ w₀ b₀ t₀ g₀) s A c t g = Alg.sT A t

node-dn : ∀ m s (A : Alg m) c t g {a} →
  Alg.Cpᵀ A a t → Alg.Dnᵀ A a (nodeAt m s A c t g)
node-dn (suc k) (inj₁ _) A c t g p = Alg.dnN A (inj₁ tt) c t g p
node-dn (suc k) (inj₂ r) A c t g p = node-dn k r (shS A) c t g p
node-dn (lim f) (n , r) A c t g p = node-dn (f n) r (shL A n) c t g p
node-dn (lc k c₀ w₀ b₀ t₀ g₀) s A c t g p = Alg.dnS A p

node-lgl : ∀ m s (A : Alg m) c t g →
  (∀ η (e : Gd (lev m s) c η) → Alg.Cpᵀ A t (g η e)) →
  (∀ η (e : Gd (lev m s) c η) η′ (e′ : Gd (lev m s) c η′) →
    Gd (lev m s) η η′ → Alg.Cpᵀ A (g η e) (g η′ e′)) →
  Alg.Lgᵀ A t → (∀ η (e : Gd (lev m s) c η) → Alg.Lgᵀ A (g η e)) →
  Alg.Lgᵀ A (nodeAt m s A c t g)
node-lgl (suc k) (inj₁ _) A c t g tg dir lt lg =
  Alg.lgN A (inj₁ tt) c t g tg dir lt lg
node-lgl (suc k) (inj₂ r) A c t g tg dir lt lg =
  node-lgl k r (shS A) c t g tg dir lt lg
node-lgl (lim f) (n , r) A c t g tg dir lt lg =
  node-lgl (f n) r (shL A n) c t g tg dir lt lg
node-lgl (lc k c₀ w₀ b₀ t₀ g₀) s A c t g tg dir lt lg = Alg.lgS A lt

node-ns : ∀ m s (A : Alg m) c t g →
  Lgl (lev m s) c → Nested (lev m s) c →
  Alg.Nsᵀ A t → (∀ η (e : Gd (lev m s) c η) → Alg.Nsᵀ A (g η e)) →
  Alg.Nsᵀ A (nodeAt m s A c t g)
node-ns (suc k) (inj₁ _) A c t g l nl nt ng =
  Alg.nsN A (inj₁ tt) c t g l nl nt ng
node-ns (suc k) (inj₂ r) A c t g l nl nt ng =
  node-ns k r (shS A) c t g l nl nt ng
node-ns (lim f) (n , r) A c t g l nl nt ng =
  node-ns (f n) r (shL A n) c t g l nl nt ng
node-ns (lc k c₀ w₀ b₀ t₀ g₀) s A c t g l nl nt ng = Alg.nsS A nt

node-ps : ∀ m s (A : Alg m) c t g → Alg.Psᵀ A (nodeAt m s A c t g)
node-ps (suc k) (inj₁ _) A c t g = Alg.psN A (inj₁ tt) c t g
node-ps (suc k) (inj₂ r) A c t g = node-ps k r (shS A) c t g
node-ps (lim f) (n , r) A c t g = node-ps (f n) r (shL A n) c t g
node-ps (lc k c₀ w₀ b₀ t₀ g₀) s A c t g = Alg.psS A

cO-pos : ∀ m → Pos m (cO m)
cO-pos zero = tt
cO-pos (suc k) = tt
cO-pos (lim f) = tt
cO-pos (lc k c w b t g) = tt
```

## 2 定义域

片段是 `YiLvIf.OnlyP` (Ω 结点的层号是 `Plain` 的)；证书的第三项是对层号、第一支、分支都遗传的 `Seedᶠ`。
它含全塔的 `tw 3` (`YiLvIf.tw3-onlyP`, `Legal-tw`, `seed-tw`)。

```agda
Dom : LF → Set
Dom x = OnlyP x × Legal x × Seedᶠ x

dom-at : ∀ f → Dom (lim f) → ∀ n → Dom (f n)
dom-at f (o , (st , l) , s) n = o n , l n , s n

dom-step : ∀ f → Dom (lim f) → ∀ n → CP (f n) (f (suc n))
dom-step f (o , (st , l) , s) = st

module Node (k : LF) (c : Raw k) .(w : Lgl k c) .(b : Nested k c) (t : LF)
  (g : (η : Raw k) → .(Gd k c η) → LF) where

  plain : Dom (lc k c w b t g) → Plain k
  plain ((pk , ot , og) , l , s) = pk

  first : Dom (lc k c w b t g) → Dom t
  first ((pk , ot , og) , (lk , tg , dir , irr , lt , lg) , (sk , s , st , sg)) =
    ot , lt , st

  branch : Dom (lc k c w b t g) → ∀ η (e : Gd k c η) → Dom (g η e)
  branch ((pk , ot , og) , (lk , tg , dir , irr , lt , lg) , (sk , s , st , sg)) η e =
    og η e , lg η e , sg η e

  low : Dom (lc k c w b t g) → Lgl k c × Nested k c
  low (o , l , (sk , s , st , sg)) = s

  seed : Dom (lc k c w b t g) → Gd k c c
  seed d = inj₁ refl , low d

  to-branch : Dom (lc k c w b t g) → ∀ η (e : Gd k c η) → CP t (g η e)
  to-branch (o , (lk , tg , dir , irr , lt , lg) , s) = tg

  directed : Dom (lc k c w b t g) →
    ∀ η (e : Gd k c η) η′ (e′ : Gd k c η′) → Gd k η η′ → CP (g η e) (g η′ e′)
  directed (o , (lk , tg , dir , irr , lt , lg) , s) = dir
```

## 3 层 `k` 里的加法链

链点的守卫无关；`pl`, `lawful`, `nested` 只进下一点的守卫，是无关的模块参数。`obs` 的目标层 `m` 任意。

```agda
startᴸ : ∀ k (c : Raw k) → .(Lgl k c) → .(Nested k c) → Pt k c
startᴸ k c w b = pt c (inj₁ refl , w , b)

module Chain (k : LF) .(pl : Plain k) (c : Raw k)
  (body : (η : Raw k) → .(Gd k c η) → Raw k)
  .(lawful : ∀ η (e : Gd k c η) → Lgl k (body η e))
  .(nested : ∀ η (e : Gd k c η) → Nested k (body η e))
  (positive : ∀ η .(e : Gd k c η) → Pos k (body η e)) where

  step : Pt k c → Raw k
  step (pt η e) = body η e

  next : Pt k c → Pt k c
  next (pt η e) = pt (plus k η (body η e))
    (Cp-tr k (proj₁ e) (inj₂ (grow k (rawAlg k) η (body η e) (positive η e))) ,
     add-lgl k pl (rawAlg k) η (body η e) (proj₁ (proj₂ e)) (lawful η e) ,
     add-ns k (rawAlg k) η (body η e) (proj₂ (proj₂ e)) (nested η e))

  grows : ∀ p → Dn k (at p) (at (next p))
  grows (pt η e) = grow k (rawAlg k) η (body η e) (positive η e)

  see : ∀ m (obs : (η : Raw k) → .(Gd k c η) → Raw m) → Pt k c → Raw m
  see m obs (pt η e) = obs η e

  collapse : ∀ m (obs : (η : Raw k) → .(Gd k c η) → Raw m) → Pt k c → Raw m
  collapse m obs p = G.lim (λ n → see m obs (iterate next p n))

module ChainLegal (k : LF) (pl : Plain k) (c : Raw k)
  (body : (η : Raw k) → .(Gd k c η) → Raw k)
  (lawful : ∀ η (e : Gd k c η) → Lgl k (body η e))
  (nested : ∀ η (e : Gd k c η) → Nested k (body η e))
  (positive : ∀ η .(e : Gd k c η) → Pos k (body η e))
  (p₀ : Pt k c) (e₀ : Gd k c (at p₀)) where

  open Chain k pl c body lawful nested positive

  points : ℕ → Pt k c
  points = iterate next p₀

  guards : ∀ n → Gd k c (at (points n))
  guards zero = e₀
  guards (suc n) =
    Cp-tr k (proj₁ (guards n)) (inj₂ (grows (points n))) ,
    add-lgl k pl (rawAlg k) (at (points n)) (step (points n))
      (proj₁ (proj₂ (guards n))) (lawful (at (points n)) (guards n)) ,
    add-ns k (rawAlg k) (at (points n)) (step (points n))
      (proj₂ (proj₂ (guards n))) (nested (at (points n)) (guards n))

  module _ (m : LF) (obs : (η : Raw k) → .(Gd k c η) → Raw m) where

    collapse-legal :
      (∀ η (e : Gd k c η) → Lgl m (obs η e)) →
      (∀ η (e : Gd k c η) η′ (e′ : Gd k c η′) → Gd k η η′ →
        Cp m (obs η e) (obs η′ e′)) →
      Lgl m (collapse m obs p₀)
    collapse-legal obs-lawful obs-monotone =
      (λ n → obs-monotone (at (points n)) (guards n)
        (at (points (suc n))) (guards (suc n))
        (inj₂ (grows (points n)) , proj₂ (guards (suc n)))) ,
      (λ n → obs-lawful (at (points n)) (guards n))

    collapse-nested : (∀ η (e : Gd k c η) → Nested m (obs η e)) →
      Nested m (collapse m obs p₀)
    collapse-nested h n = h (at (points n)) (guards n)
```
