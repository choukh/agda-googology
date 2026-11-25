# YiLvNeg 第 2 项：证书无关的一般目标层折叠与保留律

**判决：编译定理。** 折叠的证书无关、定义域对一切带守卫的分支遗传并含 `tw 3`、保留结点交出槽位 (`KeepRows`)，
则 `IrrSearch` (`keep→irr-search`)。探针坐标在 `tw 3` 的分支域里 (守卫无关地成立)，是不是链点没有判定；读作 "对一切带守卫的分支遗传" 这个定义域太宽，不读作数学障碍。
不否定：证书相关的折叠；定义域只沿链点遗传的折叠。`KeepRows` 在排中律的一个实例下有模型 (`oracle-model`)。另两条：层号合法性作数据放进证书时，遗传要经相关的守卫 (`lv-irr→irr-search`)；
派发只读裸层号而又在 `tw 3` 的带相关守卫的分支域上正确，则 LPO (`bare-way→lpo`)。接口 [YiLvIf](YiLvIf.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLvNegKeep where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim; ⊥-elim-irr)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
open import OCF.Align.YiLvIf
open import OCF.Align.YiIrrNegWide
  using (Found; IrrSearch; seen; seen-hit; seen-found; flag; dense; dense-legal;
         always; always-found)
open import OCF.Align.YiIrrNegLegal using (Legal-tw)
open import OCF.Align.YiIrrFoldBase using (add-legal)
open import OCF.Align.YiLvNegCompare
  using (At; pre-flag; branch₃; coordᴺ; levelᴺ; found→lgl; PosIrr; pos-irr→compare-irr)
```

## 1 最小记录

`Dom m x` 是把 `x` 折到目标层 `m` 的证书，`ψ` 只无关地用它。遗传只写目标层 0 的三条，形状取自已有接口：
`dom-branch` 是 `FoldRows.dom-branch`；`dom-step`、`dom-out` 是 `FbRows` 里链点处的 `step₁`、`out₁`，
层号从字面的 1 换成 "0 在 `k` 的某个位置上" 的相关证据。`keep` 的前提也是相关的槽位，所以这是最弱的写法：
前提越强，律越容易满足。

```agda
record KeepRows : Set₁ where
  field
    Dom : (m x : LF) → Set
    ψ : (m x : LF) → .(Dom m x) → Raw m
    dom-tw3 : Dom zero (tw 3)
    dom-branch : ∀ c (w : Lgl zero c) (b : Nested zero c) t
      (g : (η : R) → .(Gd zero c η) → LF) →
      Dom zero (lc zero c w b t g) → ∀ η (e : Gd zero c η) → Dom zero (g η e)
    dom-step : ∀ k c (w : Lgl k c) (b : Nested k c) t
      (g : (η : Raw k) → .(Gd k c η) → LF) →
      Dom zero (lc k c w b t g) → (s : Pre k) → lev k s ≡ zero →
      ∀ η (e : Gd k c η) → Dom k (g η e)
    dom-out : ∀ k c (w : Lgl k c) (b : Nested k c) t
      (g : (η : Raw k) → .(Gd k c η) → LF) →
      Dom zero (lc k c w b t g) → (s : Pre k) → lev k s ≡ zero →
      ∀ η (e : Gd k c η) → Dom zero (g η e)
    keep : ∀ m k c (w : Lgl k c) (b : Nested k c) t
      (g : (η : Raw k) → .(Gd k c η) → LF)
      (d : Dom m (lc k c w b t g)) (s : Pre m) → lev m s ≡ k →
      Kept m k (ψ m (lc k c w b t g) d)
```

各前提在规范实例上可满足 (第一次回灌里已经出现的情形)：`dom-branch` 取 `tw 3` 的起点 `η = 1`；
`dom-step`、`dom-out` 取层号 1 的结点，槽位 `inj₁ tt`；`keep` 取目标层 1、结点 `tw 2`。

```agda
start-guard₃ : Gd zero raw1 raw1
start-guard₃ = inj₁ refl , tt , tt

slot₁ : At (suc zero) zero
slot₁ = inj₁ tt , refl
```

## 2 探针

`a` 是第 0 层的值。根上的坐标 `η₁ = suc (lim (1, suc a, suc a, …))`，层号 `K₁ = lim (1, suc (read0 a), …)`。
`K₁` 的结点下取一支 `η′`：槽位 `(1, 根)` (层号 `read0 a`) 的结点，它的各支是槽位 `(0, 根)` (层号 0) 的结点 `X`。
读回后，层号 `read0 a` 的结点的分支是字面的层号 0 的结点 `Y`。折 `η′` 的读回到目标层 0 时，链在 `Raw (read0 a)` 里，
推进要把 `Y` 折到目标层 `read0 a`；`Y` 的层号 0 在 `read0 a` 之下当且仅当 `1 ⊲ a`。

```agda
colᴷ : R → ℕ → R
colᴷ a zero = one
colᴷ a (suc n) = G.suc a

innerᴷ : R → R
innerᴷ a = G.lim (colᴷ a)

innerᴷ-lgl : ∀ a → Lgl zero a → Cp zero one a → Lgl zero (innerᴷ a)
innerᴷ-lgl a la p = step , lawful
  where
  step : ∀ n → Cp zero (colᴷ a n) (colᴷ a (suc n))
  step zero = inj₂ p
  step (suc n) = inj₁ refl
  lawful : ∀ n → Lgl zero (colᴷ a n)
  lawful zero = tt
  lawful (suc n) = la

rootᴷ : R → R
rootᴷ a = G.suc (innerᴷ a)

rootᴷ-guard : ∀ a → Lgl zero a → Cp zero one a → Gd zero raw1 (rootᴷ a)
rootᴷ-guard a la p =
  inj₂ (inj₂ (zero , inj₁ refl)) , innerᴷ-lgl a la p , raw0-Nested (rootᴷ a)

K₁ : R → LF
K₁ a = read0 (innerᴷ a)

X : ∀ a → Raw (K₁ a)
X a = G.lc (0 , inj₁ tt) G.zero G.top (λ _ _ → G.top)

X-lgl : ∀ a → Lgl (K₁ a) (X a)
X-lgl a = (λ _ _ → inj₁ refl) , (λ _ _ _ _ _ → inj₁ refl) , (λ _ _ _ → refl) ,
  tt , (λ _ _ → tt)

X-nested : ∀ a → Nested (K₁ a) (X a)
X-nested a = tt , tt , tt , (λ _ _ → tt)

η′ : ∀ a → Raw (K₁ a)
η′ a = G.lc (1 , inj₁ tt) G.zero (X a) (λ _ _ → X a)

η′-guard : ∀ a → Gd (K₁ a) G.top (η′ a)
η′-guard a =
  inj₂ (inj₂ (inj₁ refl)) ,
  ((λ _ _ → inj₁ refl) , (λ _ _ _ _ _ → inj₁ refl) , (λ _ _ _ → refl) ,
    X-lgl a , (λ _ _ → X-lgl a)) ,
  (tt , tt , X-nested a , (λ _ _ → X-nested a))

Y : R → LF
Y a = lc zero G.zero tt tt (upT (K₁ a)) (λ _ _ → upT (K₁ a))

-- 读回: η′ 是层号 read0 a 的结点, 第一支与各支都是 Y.
η′-read : ∀ a → up (K₁ a) (η′ a) (proj₂ (proj₂ (η′-guard a))) ≡
  lc (read0 a) G.zero tt tt (Y a) (λ _ _ → Y a)
η′-read a = refl

below-one : ∀ a → Cp zero one a → At (read0 a) zero
below-one a p = shift (read0-cp a p) (inj₁ tt)
```

证书链：四步都只用记录里的遗传字段。`la`、`p` 在这里是相关参数；下面只在无关位置调用。

```agda
module Probe (F : KeepRows) where
  open KeepRows F

  d₁ : ∀ a → Lgl zero a → Cp zero one a → Dom zero (Ω̂ (read0 (rootᴷ a)))
  d₁ a la p = dom-branch raw1 tt tt (tw 2) branch₃ dom-tw3 (rootᴷ a) (rootᴷ-guard a la p)

  d₂ : ∀ a → Lgl zero a → Cp zero one a →
    Dom zero (lc (read0 a) G.zero tt tt (Y a) (λ _ _ → Y a))
  d₂ a la p = dom-out (K₁ a) G.top tt tt (upT (K₁ a))
    (λ η e → up (K₁ a) η (proj₂ (proj₂ e))) (d₁ a la p)
    (0 , inj₁ tt) refl (η′ a) (η′-guard a)

  d₃ : ∀ a → Lgl zero a → Cp zero one a → Dom (read0 a) (Y a)
  d₃ a la p = dom-step (read0 a) G.zero tt tt (Y a) (λ _ _ → Y a) (d₂ a la p)
    (proj₁ (below-one a p)) (proj₂ (below-one a p)) G.zero (inj₁ refl , tt , tt)

  probe : ∀ a → .(Lgl zero a) → .(Cp zero one a) → Raw (read0 a)
  probe a la p = ψ (read0 a) (Y a) (d₃ a la p)

  probe-kept : ∀ a (la : Lgl zero a) (p : Cp zero one a) →
    Kept (read0 a) zero (probe a la p)
  probe-kept a la p = keep (read0 a) zero G.zero tt tt (upT (K₁ a)) (λ _ _ → upT (K₁ a))
    (d₃ a la p) (proj₁ (below-one a p)) (proj₂ (below-one a p))
```

## 3 取出槽位

输出是相关的数据，它是不是保留结点可以看出来；不是的情形只需要无关的 ⊥。槽位上的层号是不是零可判定。

```agda
IsNode : ∀ {m} → Raw m → Set
IsNode (G.lc r c t g) = ⊤
IsNode _ = ⊥

kept-node : ∀ m k (y : Raw m) → Kept m k y → IsNode y
kept-node m k y (r , e , c , t , g , refl) = tt

slot-or : ∀ {m} → Pre m → Raw m → Pre m
slot-or d (G.lc r c t g) = r
slot-or d _ = d

kept-at : ∀ m k r c t g → Kept m k (G.lc r c t g) → lev m r ≡ k
kept-at m k r c t g (r′ , e , c′ , t′ , g′ , eq) =
  subst (λ z → lev m z ≡ k) (sym (cong (slot-or r) eq)) e

is-zero : (x : LF) → .(x ≡ zero) → x ≡ zero
is-zero zero e = refl
is-zero (suc x) e = ⊥-elim-irr (no e)
  where no : suc x ≡ zero → ⊥
        no ()
is-zero (lim f) e = ⊥-elim-irr (no e)
  where no : lim f ≡ zero → ⊥
        no ()
is-zero (lc k c w b t g) e = ⊥-elim-irr (no e)
  where no : lc k c w b t g ≡ zero → ⊥
        no ()

locate : ∀ m (y : Raw m) → .(Kept m zero y) → At m zero
locate m (G.lc r c t g) kp = r , is-zero (lev m r) (kept-at m zero r c t g kp)
locate m G.zero kp = ⊥-elim-irr (kept-node m zero G.zero kp)
locate m (G.suc y) kp = ⊥-elim-irr (kept-node m zero (G.suc y) kp)
locate m (G.lim f) kp = ⊥-elim-irr (kept-node m zero (G.lim f) kp)
locate m (G.em i T) kp = ⊥-elim-irr (kept-node m zero (G.em i T) kp)
locate m G.top kp = ⊥-elim-irr (kept-node m zero G.top kp)

-- 第 0 层的值 a 只无关地知道 1 ⊲ a, 交出 read0 a 里层号为零的位置.
keep→locate : KeepRows → ∀ (a : R) → .(Lgl zero a) → .(Cp zero one a) → At (read0 a) zero
keep→locate F a la p = locate (read0 a) (probe a la p) (probe-kept a la p)
  where open Probe F

found→below : ∀ α → Found α → Cp zero one (dense α)
found→below α (n , q) = inj₂ (n , subst (λ z → Cp zero one (flag z))
  (sym (seen-hit α n q)) (inj₁ refl))

keep→irr-search : KeepRows → IrrSearch
keep→irr-search F α s
  with keep→locate F (dense α) (dense-legal α) (found→below α s)
... | (m , r) , e = seen-found α m (pre-flag (seen α m) _ r)
```

## 4 探针在片段里

三棵探针树都是 `tw 3` 的分支的分支，`OnlyP` 只要无关的守卫；给了相关的 `la`、`p`，根上的那一支也合法。
`α = always` 时 `la`、`p` 有闭证明，证书链的每个前提都有闭实例。

```agda
probe-onlyP₁ : ∀ a .(la : Lgl zero a) .(p : Cp zero one a) → OnlyP (Ω̂ (read0 (rootᴷ a)))
probe-onlyP₁ a la p = proj₂ (proj₂ tw3-onlyP) (rootᴷ a) (rootᴷ-guard a la p)

probe-onlyP₂ : ∀ a .(la : Lgl zero a) .(p : Cp zero one a) →
  OnlyP (lc (read0 a) G.zero tt tt (Y a) (λ _ _ → Y a))
probe-onlyP₂ a la p = proj₂ (proj₂ (probe-onlyP₁ a la p)) (η′ a) (η′-guard a)

probe-onlyP₃ : ∀ a .(la : Lgl zero a) .(p : Cp zero one a) → OnlyP (Y a)
probe-onlyP₃ a la p = proj₁ (proj₂ (probe-onlyP₂ a la p))

probe-legal₁ : ∀ a → Lgl zero a → Cp zero one a → Legal (Ω̂ (read0 (rootᴷ a)))
probe-legal₁ a la p =
  proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (Legal-tw 3))))) (rootᴷ a) (rootᴷ-guard a la p)

closed-root-guard : Gd zero raw1 (rootᴷ (dense always))
closed-root-guard =
  rootᴷ-guard (dense always) (dense-legal always) (found→below always always-found)
```

## 5 记录不可反驳

给一个判定 "`k` 是不是 `m` 的某个位置上的层号" 的神谕 (排中律的实例)，`KeepRows` 有模型：定义域取全部，保留结点的槽位由神谕给。
所以 `KeepRows → ⊥` 不可证；上面的定理把它的构造内容定在 `IrrSearch` 以上。

```agda
Locate : Set
Locate = ∀ m k → At m k ⊎ (At m k → ⊥)

low-zero : ∀ m r → Low m r
low-zero (suc k) (inj₁ _) = G.zero
low-zero (suc k) (inj₂ r) = low-zero k r
low-zero (lim f) (n , r) = low-zero (f n) r
low-zero (lc k c w b t g) (inj₁ (inj₁ _)) = G.zero
low-zero (lc k c w b t g) (inj₁ (inj₂ r)) = low-zero k r
low-zero (lc k c w b t g) (inj₂ (inj₁ r)) = low-zero t r
low-zero (lc k c w b t g) (inj₂ (inj₂ (η , e , r))) = low-zero (g η e) r

place : ∀ m k → At m k ⊎ (At m k → ⊥) → Raw m
place m k (inj₁ (r , e)) = G.lc r (low-zero m r) G.zero (λ _ _ → G.zero)
place m k (inj₂ no) = G.zero

place-kept : ∀ m k (o : At m k ⊎ (At m k → ⊥)) → At m k → Kept m k (place m k o)
place-kept m k (inj₁ (r , e)) a = r , e , low-zero m r , G.zero , (λ _ _ → G.zero) , refl
place-kept m k (inj₂ no) a = ⊥-elim (no a)

oracle-fold : Locate → (m x : LF) → Raw m
oracle-fold orc m (lc k c w b t g) = place m k (orc m k)
oracle-fold orc m zero = G.zero
oracle-fold orc m (suc x) = G.zero
oracle-fold orc m (lim f) = G.zero

oracle-model : Locate → KeepRows
oracle-model orc = record
  { Dom = λ m x → ⊤
  ; ψ = λ m x d → oracle-fold orc m x
  ; dom-tw3 = tt
  ; dom-branch = λ c w b t g d η e → tt
  ; dom-step = λ k c w b t g d s e η e′ → tt
  ; dom-out = λ k c w b t g d s e η e′ → tt
  ; keep = λ m k c w b t g d s e → place-kept m k (orc m k) (s , e)
  }
```

同一个神谕也给出 [YiLvNegCompare](YiLvNegCompare.lagda.md) 的 `PosIrr` 与 `CompareIrr`，所以那里的前提同样不可反驳。

```agda
locate→pos-irr : Locate → PosIrr
locate→pos-irr orc i j pi pj L a with orc i j
... | inj₁ a′ = a′
... | inj₂ no = ⊥-elim-irr (no a)

locate→compare-irr : Locate → CompareIrr
locate→compare-irr orc = pos-irr→compare-irr (locate→pos-irr orc)
```

## 6 层号的合法性作数据放进证书：遗传必须经相关的守卫

`LvIrr x`：`x` 的每个 Ω 结点的层号有相关的 `Legal`，对分支遗传时守卫无关 (像 `OnlyP` 那样)。
`tw 3` 上有这样的证书就有 `IrrSearch`：坐标 `suc (coordᴺ α)` 的那一支是层号 `levelᴺ α` 的结点。
守卫相关的同形谓词是 `Legal` 的一部分，`tw 3` 满足 (`YiIrrNegLegal.Legal-tw`)。

```agda
LvIrr : LF → Set
LvIrr zero = ⊤
LvIrr (suc x) = LvIrr x
LvIrr (lim f) = ∀ n → LvIrr (f n)
LvIrr (lc k c w b t g) = Legal k × (∀ η .(e : Gd k c η) → LvIrr (g η e))

level-legal→found : ∀ α → Legal (levelᴺ α) → Found α
level-legal→found α (st , lg) with st zero
... | suc (lim m p) = seen-found α m (hit (seen α m) _ p)
  where
  hit : ∀ x .(nb : Nested zero (flag x)) → CP (suc zero) (up zero (flag x) nb) → x ≡ true
  hit true nb p = refl
  hit false nb ()

lv-irr→irr-search : LvIrr (tw 3) → IrrSearch
lv-irr→irr-search (L₀ , branches) α s =
  level-legal→found α (proj₁ (branches (G.suc (coordᴺ α))
    (inj₂ (inj₂ (zero , inj₁ refl)) , found→lgl α s , raw0-Nested (G.suc (coordᴺ α)))))
```

## 7 派发只读裸层号：正确的保留判定给出 LPO

`way m k` 只看两个层号，交出槽位 (保留) 或不交 (折叠)。律只要求一个方向：`k` 在 `m` 的某个位置上时必须保留；
定义域只取 `tw 3` 的带**相关**守卫的坐标的读回里各位置上的层号。坐标 `suc (1 + dense α)` 对一切 `α` 都有闭形式的守卫，
它根上的层号 `read0 (1 + dense α)` 里有层号 1 的位置当且仅当 `α` 有见证。所以这样的 `way` 判定 `Found α`。
这一条的对象在带相关证据的读回域内；它否定的只是 "派发不读位置、不读证书而又处处正确"，不否定读公共上界里的位置与合法性的派发 (`YiLvIf.compare`)。
在排中律的实例 `Locate` 下前提可满足 (取 `way = orc`)。

```agda
LPO : Set
LPO = ∀ (α : ℕ → Bool) → Found α ⊎ (Found α → ⊥)

BareWay : Set
BareWay = ∀ (m k : LF) → At m k ⊎ ⊤

IsKeep : ∀ {m k} → At m k ⊎ ⊤ → Set
IsKeep (inj₁ a) = ⊤
IsKeep (inj₂ tt) = ⊥

Correct : BareWay → Set
Correct way = ∀ (η : R) (e : Gd zero raw1 η) (q : Pre (read0 η)) k →
  At (lev (read0 η) q) k → IsKeep (way (lev (read0 η) q) k)

plus-one : ∀ y → Cp zero one (one +ʳ y)
plus-one G.zero = inj₁ refl
plus-one (G.suc y) = inj₂ (plus-one y)
plus-one (G.lim f) = inj₂ (zero , plus-one (f zero))
plus-one (G.lc () c t g)
plus-one (G.em () a)
plus-one G.top = inj₂ (inj₁ refl)

coordᴸ : (ℕ → Bool) → R
coordᴸ α = G.suc (one +ʳ dense α)

coordᴸ-guard : ∀ α → Gd zero raw1 (coordᴸ α)
coordᴸ-guard α =
  inj₂ (plus-one (dense α)) ,
  add-legal one (dense α) tt (dense-legal α) ,
  raw0-Nested (coordᴸ α)

levelᴸ : (ℕ → Bool) → LF
levelᴸ α = read0 (one +ʳ dense α)

levelᴸ-at : ∀ α → lev (read0 (coordᴸ α)) (inj₁ tt) ≡ levelᴸ α
levelᴸ-at α = refl

flag-one : ∀ x .(nb : Nested zero (one +ʳ flag x)) (r : Pre (up zero (one +ʳ flag x) nb)) →
  lev (up zero (one +ʳ flag x) nb) r ≡ suc zero → x ≡ true
flag-one true nb r e = refl
flag-one false nb (inj₁ _) ()
flag-one false nb (inj₂ ()) e

one-flag : ∀ x → x ≡ true → .(nb : Nested zero (one +ʳ flag x)) →
  At (up zero (one +ʳ flag x) nb) (suc zero)
one-flag .true refl nb = inj₁ tt , refl

found→one : ∀ α → Found α → At (levelᴸ α) (suc zero)
found→one α (n , p) =
  (n , proj₁ (one-flag (seen α n) (seen-hit α n p) _)) ,
  proj₂ (one-flag (seen α n) (seen-hit α n p) _)

bare-way→lpo : (way : BareWay) → Correct way → LPO
bare-way→lpo way ok α
  with way (levelᴸ α) (suc zero) | ok (coordᴸ α) (coordᴸ-guard α) (inj₁ tt) (suc zero)
... | inj₁ ((n , r) , e) | c = inj₁ (seen-found α n (flag-one (seen α n) _ r e))
... | inj₂ tt | c = inj₂ (λ s → c (found→one α s))

oracle-way : Locate → Σ BareWay Correct
oracle-way orc = way , ok
  where
  pick : ∀ {m k} → At m k ⊎ (At m k → ⊥) → At m k ⊎ ⊤
  pick (inj₁ a) = inj₁ a
  pick (inj₂ no) = inj₂ tt
  pick-keep : ∀ {m k} (o : At m k ⊎ (At m k → ⊥)) → At m k → IsKeep (pick o)
  pick-keep (inj₁ a) _ = tt
  pick-keep (inj₂ no) a = no a
  way : BareWay
  way m k = pick (orc m k)
  ok : Correct way
  ok η e q k a = pick-keep (orc (lev (read0 η) q) k) a
```
