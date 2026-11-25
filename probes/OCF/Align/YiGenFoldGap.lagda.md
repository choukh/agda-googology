# YiGenFold：归一链 `pointsᴺ` 上的闭项与约化

**判决 (编译定理、条件定理、闭实例)：归一链的目标层 0 闭项 `Tᴾ` 写得出、合法，没有前提；派发 "不多保留" 处处成立，"完全" 只证到结点在主干上、或目标与结点都在有限坐标的支上的对，其余的对上一律折叠 (§4；同一支里的对上这不完全，§6)。
把其余的对上的判定作为前提 `AskDec` 给出，就得到派发全都完全的闭项 `Tᴺ` (`Canon`)；链与自目标的折叠都不改。第 1 个链点问到这样的一对 (`asked₁`)：
在它上面 "在位置上" 等价于两个逐点相等的函数字面相等 (`at→fe`, `fe→at`, `fe-pointwise`)，`Tᴾ` 的折叠在它上面完全当且仅当这个相等不成立 (`complete-there→`, `complete-there←`)。**
`AskDec` 推出判定这个函数外延的实例 (`askdec→fe`)，这一对上接口的 `Honest` 推出它的弱判定 (`weak-fe`)；两个结论都不是矛盾。`AskDec` 没有被反驳 (`locate→askdec`)，是否推出 LPO 没有判定。
实例的坐标在根的分支函数的定义域里，不是根上的链走到的可数个坐标之一。都用了替代行，不写读法。有限坐标的链见 [YiGenFoldFin](YiGenFoldFin.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiGenFoldGap where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw1; raw0-Nested)
open import OCF.Align.YiIrrIf using (R; one; _+ʳ_; read0)
open import OCF.Align.YiLvIf using (lev; Kept)
open import OCF.Align.YiLvFoldBase using (Way; keep; fold)
open import OCF.Align.YiLvFoldFin using (IsKeep)
open import OCF.Align.YiLvNegCompare using (At)
open import OCF.Align.YiLvNegCum using (psum)
open import OCF.Align.YiLvNegKeep using (Locate)
open import OCF.Align.YiRawIf using (IsLim; tri→way; tri-complete)
open import OCF.Align.YiRawFoldTw3 using (T₃ᵐ)
open import OCF.Align.YiRawNegOmega using (K₂ω; root₂; first₂; br; compare-zero; flip; read-shape)
open import OCF.Align.YiOmFoldBase
open import OCF.Align.YiOmFoldNorm
open import OCF.Align.YiOmFoldChain
open import OCF.Align.YiGenIf using (OwnFold; Honest)
open import OCF.Align.YiGenFold
open import OCF.Align.YiGenFoldDom using (module Dm)
import OCF.Align.YiGenFoldFin as Fin
```

## 1 归一链点里没有嵌入的孩子

`N.D`：坐标谓词取恒真，只剩 "没有嵌入的孩子"。归一链对它封闭。`F.D` 是有限坐标的定义域；第 1 个归一链点不在其中 (§7)。

```agda
module N = Dm (λ (_ : R) → ⊤)
module F = Dm LimFree

GκD : ∀ η → N.D (Gκ η)
GκD G.zero = N.t₀D
GκD (G.suc a) = N.plusD (Gκ a) (KT a) (GκD a) (N.KT-D a tt)
GκD (G.lim f) = λ n → GκD (f n)
GκD G.top = N.t₀D

Φˢ⁺-D : ∀ ξ → N.D ξ → N.D (Φˢ⁺ ξ)
Φˢ⁺-D G.zero d = tt
Φˢ⁺-D (G.suc a) d = N.copiesD (Φˢ⁺ a) (Φˢ⁺-D a d)
Φˢ⁺-D (G.lim f) d = λ n → Φˢ⁺-D (f n) (d n)
Φˢ⁺-D (G.lc (inj₁ (inj₁ _)) c t g) (dt , dg) = Φˢ⁺-D t dt , (λ η e → Φˢ⁺-D (g η e) (dg η e))
Φˢ⁺-D (G.lc (inj₂ (inj₁ (inj₁ _))) c t g) (dt , dg) =
  Φˢ⁺-D t dt , (λ η e → Φˢ⁺-D (g η e) (dg η e))
Φˢ⁺-D (G.lc (inj₂ (inj₂ (η , e , r))) c t g) (h , dt , dg) =
  h , Φˢ⁺-D t dt , (λ ζ e′ → Φˢ⁺-D (g ζ e′) (dg ζ e′))
Φˢ⁺-D G.top d = N.t₀D , (λ η e → GκD η)

noem : ∀ n → N.D (pointsᴺ n)
noem zero = tt
noem (suc n) = N.plusD (pointsᴺ n) (Φˢ⁺ (pointsᴺ n)) (noem n) (Φˢ⁺-D (pointsᴺ n) (noem n))

ask-noem : ∀ {τ₀ ξ₀ τ ξ} → Ask τ₀ ξ₀ τ ξ → N.D ξ₀ → N.D ξ
ask-noem here d = d
ask-noem (pred a) d = ask-noem a d
ask-noem (term a n) d = ask-noem a d n
ask-noem (first {p = p} {c} {t} {g} a) d = N.D-first p c t g (ask-noem a d)
ask-noem (obs {p = p} {c} {t} {g} a ζ e) d = N.D-branch p c t g (ask-noem a d) ζ e
ask-noem (drive {p = p} {c} {t} {g} a ζ e) d = N.D-branch p c t g (ask-noem a d) ζ e
```

## 2 派发全都完全所缺的陈述

`AskN τ ξ`：某个归一链点折到第 0 层时调用到 "把 `ξ` 折到 `τ`"。`AskDec`：目标在第 `η` 支的位置 `r`，被折的树的根在第 `η′` 支的位置 `r′`，
这一对被调用到 (无关的证据) 时，交出 "结点层在目标层的位置上" 的判定，肯定时带槽位。目标或结点在主干上的对不需要它 (`compare-zero`)。

```agda
AskN : Tg → RΩ → Set
AskN τ ξ = Σ ℕ λ n → Ask base (pointsᴺ n) τ ξ

AskDec : Set
AskDec = ∀ η (e : Gd zero raw1 η) (r : Pre (read0 η))
  η′ (e′ : Gd zero raw1 η′) (r′ : Pre (read0 η′)) (c : Low (read0 η′) r′) (t : RΩ)
  (g : (ζ : Low (read0 η′) r′) → .(GdL (read0 η′) r′ c ζ) → RΩ) →
  .(AskN (at η e r) (G.lc (br η′ e′ r′) c t g)) →
  At (lev (read0 η) r) (lev (read0 η′) r′) ⊎ (At (lev (read0 η) r) (lev (read0 η′) r′) → ⊥)

dec→way : ∀ {i j} → At i j ⊎ (At i j → ⊥) → Way i j
dec→way (inj₁ (s , q)) = keep s q
dec→way (inj₂ no) = fold

dec-complete : ∀ {i j} (x : At i j ⊎ (At i j → ⊥)) → At i j → IsKeep (dec→way x)
dec-complete (inj₁ (s , q)) a = tt
dec-complete (inj₂ no) a = ⊥-elim (no a)

-- 前提可满足: 判定 "在位置上" 的神谕给出它.
locate→askdec : Locate → AskDec
locate→askdec orc η e r η′ e′ r′ c t g a = orc (lev (read0 η) r) (lev (read0 η′) r′)
```

## 3 条件定理：给了 `AskDec`，归一链的闭项与派发的完全性

定义域取调用闭包本身 (连同 "没有嵌入的孩子")，折叠只无关地带着它；派发在分支对分支时读 `AskDec`。其余与 [YiGenFold](YiGenFold.lagda.md) 相同，链与自目标的折叠不改。
`top` 在分支目标下取 `rowᶠ` (替代行)，自目标的折叠里 `top` 的行是归一行 (替代行)，所以即使在前提下也不写读法。

```agda
module Canon (dec : AskDec) where

  Domᴺ : Tg → RΩ → Set
  Domᴺ τ ξ = AskN τ ξ × N.D ξ

  wayᴺ : ∀ τ p c t g → .(Domᴺ τ (G.lc p c t g)) → Way (tl τ) (lev K₂ω p)
  wayᴺ base p c t g d = fold
  wayᴺ (at η e r) (inj₁ (inj₁ _)) c t g d = tri→way (flip (compare-zero η e r))
  wayᴺ (at η e r) (inj₂ (inj₁ (inj₁ _))) c t g d = tri→way (flip (compare-zero η e r))
  wayᴺ (at η e r) (inj₂ (inj₂ (η′ , e′ , r′))) c t g d =
    dec→way (dec η e r η′ e′ r′ c t g (proj₁ d))

  canon : Disp
  canon = record
    { Dom = Domᴺ
    ; d-pred = λ d → (proj₁ (proj₁ d) , pred (proj₂ (proj₁ d))) , proj₂ d
    ; d-term = λ d m → (proj₁ (proj₁ d) , term (proj₂ (proj₁ d)) m) , proj₂ d m
    ; d-first = λ p c t g d →
        (proj₁ (proj₁ d) , first (proj₂ (proj₁ d))) , N.D-first p c t g (proj₂ d)
    ; d-obs = λ p c t g d ζ e →
        (proj₁ (proj₁ d) , obs (proj₂ (proj₁ d)) ζ e) , N.D-branch p c t g (proj₂ d) ζ e
    ; d-drive = λ p c t g d ζ e →
        (proj₁ (proj₁ d) , drive (proj₂ (proj₁ d)) ζ e) , N.D-branch p c t g (proj₂ d) ζ e
    ; d-em = λ i a d → proj₂ d
    ; way = wayᴺ
    ; topᴮ = Fin.topS
    ; topᴮ-legal = Fin.topS-legal
    ; topᴮ-nested = Fin.topS-nested
    ; topᴮ-pos = Fin.topS-pos }

  open Fold canon public

  wayᴺ-complete : ∀ τ p c t g (d : Domᴺ τ (G.lc p c t g)) →
    At (tl τ) (lev K₂ω p) → IsKeep (wayᴺ τ p c t g d)
  wayᴺ-complete base p c t g d (() , q)
  wayᴺ-complete (at η e r) (inj₁ (inj₁ _)) c t g d a =
    tri-complete (flip (compare-zero η e r)) a
  wayᴺ-complete (at η e r) (inj₂ (inj₁ (inj₁ _))) c t g d a =
    tri-complete (flip (compare-zero η e r)) a
  wayᴺ-complete (at η e r) (inj₂ (inj₂ (η′ , e′ , r′))) c t g d a =
    dec-complete (dec η e r η′ e′ r′ c t g (proj₁ d)) a

  domᴺ : ∀ n → Domᴺ base (pointsᴺ n)
  domᴺ n = (n , here) , noem n

  obsᴺ : ℕ → R
  obsᴺ n = Ψᶠ base (pointsᴺ n) (domᴺ n) (pointsᴺ-legal n) (pointsᴺ-nested n)

  Tᴺ : R
  Tᴺ = G.lim obsᴺ

  Tᴺ-legal : Lgl zero Tᴺ
  Tᴺ-legal =
    (λ n → Ψᶠ-cp base (pointsᴺ (suc n)) (domᴺ n) (domᴺ (suc n))
      (pointsᴺ-legal n) (pointsᴺ-nested n) (pointsᴺ-legal (suc n)) (pointsᴺ-nested (suc n))
      (plus-weak (pointsᴺ n) (Φˢ⁺ (pointsᴺ n)))) ,
    (λ n → Ψᶠ-legal base (pointsᴺ n) (domᴺ n) (pointsᴺ-legal n) (pointsᴺ-nested n))

  Tᴺ-term₀ : obsᴺ 0 ≡ T₃ᵐ
  Tᴺ-term₀ = refl

  -- 调用闭包里每个结点上, 接口的两条都成立.
  honestᴺ : ∀ n {τ p c t g} (a : Ask base (pointsᴺ n) τ (G.lc p c t g))
    (l : Lgl K₂ω (G.lc p c t g)) (nb : Nested K₂ω (G.lc p c t g)) →
    Honest (posT τ)
      (ownAt τ (G.lc p c t g) ((n , a) , ask-noem a (noem n)) l nb) (G.lc p c t g)
  honestᴺ n {τ} {p} {c} {t} {g} a l nb =
    honest-if τ p c t g ((n , a) , ask-noem a (noem n)) l nb
      (wayᴺ-complete τ p c t g ((n , a) , ask-noem a (noem n)))
```

## 4 无前提：归一链的闭项，派发只在有限坐标的对上完全

派发取 [YiGenFoldFin](YiGenFoldFin.lagda.md) 的那一个 (两支的坐标都不含极限时取 `compare-link`，否则折叠)，定义域只要 "没有嵌入的孩子"。
闭项 `Tᴾ` 合法，没有前提；"不多保留" 处处成立；"派发完全" 在结点位于主干、或目标与结点都在有限坐标的支上时成立。其余的对上派发一律取折叠：§5 的一对上这是否完全等价于一个函数相等不成立，§6 的一对 (同一支) 上它不完全。

```agda
partial : Disp
partial = record
  { Dom = λ τ ξ → N.D ξ
  ; d-pred = λ d → d
  ; d-term = λ d n → d n
  ; d-first = N.D-first
  ; d-obs = N.D-branch
  ; d-drive = N.D-branch
  ; d-em = λ i a d → d
  ; way = λ τ p c t g d → Fin.wayS τ p
  ; topᴮ = Fin.topS
  ; topᴮ-legal = Fin.topS-legal
  ; topᴮ-nested = Fin.topS-nested
  ; topᴮ-pos = Fin.topS-pos }

module P = Fold partial

Tᴾ : R
Tᴾ = G.lim (λ n → P.Ψᶠ base (pointsᴺ n) (noem n) (pointsᴺ-legal n) (pointsᴺ-nested n))

Tᴾ-legal : Lgl zero Tᴾ
Tᴾ-legal =
  (λ n → P.Ψᶠ-cp base (pointsᴺ (suc n)) (noem n) (noem (suc n))
    (pointsᴺ-legal n) (pointsᴺ-nested n) (pointsᴺ-legal (suc n)) (pointsᴺ-nested (suc n))
    (plus-weak (pointsᴺ n) (Φˢ⁺ (pointsᴺ n)))) ,
  (λ n → P.Ψᶠ-legal base (pointsᴺ n) (noem n) (pointsᴺ-legal n) (pointsᴺ-nested n))

soundᴾ : ∀ τ p c t g (d : N.D (G.lc p c t g))
  (l : Lgl K₂ω (G.lc p c t g)) (nb : Nested K₂ω (G.lc p c t g)) →
  (At (tl τ) (lev K₂ω p) → ⊥) → IsLim (P.Ψᶠ τ (G.lc p c t g) d l nb)
soundᴾ = P.sound

keptᴾ-trunk : ∀ τ p c t g (d : N.D (G.lc p c t g))
  (l : Lgl K₂ω (G.lc p c t g)) (nb : Nested K₂ω (G.lc p c t g)) → Fin.TrunkP p →
  At (tl τ) (lev K₂ω p) → Kept (tl τ) (lev K₂ω p) (P.Ψᶠ τ (G.lc p c t g) d l nb)
keptᴾ-trunk τ p c t g d l nb tp a = P.kept τ p c t g d l nb (Fin.wayS-trunk τ p tp a)

keptᴾ-fin : ∀ τ p c t g (d : N.D (G.lc p c t g))
  (l : Lgl K₂ω (G.lc p c t g)) (nb : Nested K₂ω (G.lc p c t g)) → Fin.FinT τ → F.GoodP p →
  At (tl τ) (lev K₂ω p) → Kept (tl τ) (lev K₂ω p) (P.Ψᶠ τ (G.lc p c t g) d l nb)
keptᴾ-fin τ p c t g d l nb ft gp a = P.kept τ p c t g d l nb (Fin.wayS-complete τ ft p gp a)
```

## 5 第 1 个链点问到的一对

`wᴾ = lim (1, 1, …)`，`wᴸ = lim (0, wᴾ+1, wᴾ+1, …)`，都合法；`suc wᴸ` 是根上分支函数定义域里的带守卫坐标。
`Gκ (suc wᴸ) = Gκ wᴸ + KT wᴸ`：结点 `KT wᴸ` 在坐标 `suc (nrm wᴸ)` 那一支的根上，它的每一支以 `Gκ wᴸ` 为前缀，其中第 1 项含 `KT wᴾ`。
路径：根的第 `suc wᴸ` 支；那个结点的起点分支 (目标换成它自己那一层)；沿极限的第 0 项与第一支走到零叶上的前缀；前缀的第 1 项。

```agda
wᴾ : R
wᴾ = G.lim (λ _ → one)

fᴸ : ℕ → R
fᴸ zero = G.zero
fᴸ (suc n) = G.suc wᴾ

wᴸ : R
wᴸ = G.lim fᴸ

lwᴾ : Lgl zero wᴾ
lwᴾ = (λ _ → inj₁ refl) , (λ _ → tt)

fᴸ-step : ∀ n → Cp zero (fᴸ n) (fᴸ (suc n))
fᴸ-step zero = inj₂ (inj₂ (zero , inj₂ (inj₁ refl)))
fᴸ-step (suc n) = inj₁ refl

fᴸ-lgl : ∀ n → Lgl zero (fᴸ n)
fᴸ-lgl zero = tt
fᴸ-lgl (suc n) = lwᴾ

lwᴸ : Lgl zero wᴸ
lwᴸ = fᴸ-step , fᴸ-lgl

eᴸ : Gd zero raw1 (G.suc wᴸ)
eᴸ = inj₂ (inj₂ (1 , inj₂ (inj₂ (zero , inj₁ refl)))) , lwᴸ , raw0-Nested (G.suc wᴸ)

τᴸ : Tg
τᴸ = at (G.suc (nrm wᴸ)) (γ wᴸ) (inj₁ tt)

ξᴾ : RΩ
ξᴾ = plusΩ G.top (Gκ (G.suc wᴾ))

here¹ : Ask base (pointsᴺ 1) base (pointsᴺ 1)
here¹ = here

asked₁ : Ask base (pointsᴺ 1) τᴸ ξᴾ
asked₁ =
  let a₁ = obs here¹ (G.suc wᴸ) eᴸ
      a₂ = drive a₁ G.top (inj₁ refl , tt , tt)
      a₃ = term a₂ 0
      a₄ = term a₃ 0
      a₅ = first a₄
      a₆ = first a₅
      a₇ = pred a₆
  in term a₇ 1
```

两个层号。目标层 `tl τᴸ = read0 (nrm wᴸ)` 是极限，第 `m` 项是 `read0 (psum gᴸ m)`；结点层 `Xᴾ = read0 (nrm wᴾ)` 也是极限。
目标层的位置上，层号是极限的只有每一项里的一个：`lim (λ i → read0 (psum gᴸ m +ʳ cᴾ i))`。`m = 0` 时前面的和是零，这个层号与 `Xᴾ` 逐点相等；`m ≥ 1` 时在第 0 点就不同。

```agda
cᴾ : ℕ → R
cᴾ = psum (λ _ → one)

gᴸ : ℕ → R
gᴸ m = nrm (fᴸ m)

Xᴾ : LF
Xᴾ = lim (λ i → read0 (cᴾ i))

node-level : lev K₂ω (br (G.suc (nrm wᴾ)) (γ wᴾ) (inj₁ tt)) ≡ Xᴾ
node-level = refl

target-level : tl τᴸ ≡ lim (λ m → read0 (psum gᴸ m))
target-level = refl

FE : Set
FE = _≡_ {A = ℕ → LF} (λ i → read0 (G.zero +ʳ cᴾ i)) (λ i → read0 (cᴾ i))

fe-pointwise : ∀ i → read0 (G.zero +ʳ cᴾ i) ≡ read0 (cᴾ i)
fe-pointwise zero = refl
fe-pointwise (suc i) = cong (λ (z : LF) → suc (suc z)) (fe-pointwise i)

unlim : LF → ℕ → LF
unlim (lim h) = h
unlim zero = λ _ → zero
unlim (suc x) = λ _ → zero
unlim (lc k c w b t g) = λ _ → zero

two≢one : ∀ {x : LF} → _≡_ {A = LF} (suc (suc x)) (suc zero) → ⊥
two≢one ()

no-lim : ∀ P i (h : ℕ → LF) → read0 (P +ʳ cᴾ i) ≡ lim h → ⊥
no-lim P zero h ()
no-lim P (suc i) h ()

outer : ∀ m (s : Pre (read0 (psum gᴸ m))) → lev (read0 (psum gᴸ m)) s ≡ Xᴾ → FE
inner : ∀ m i (s : Pre (read0 (psum gᴸ m +ʳ cᴾ i))) →
  lev (read0 (psum gᴸ m +ʳ cᴾ i)) s ≡ Xᴾ → FE

outer zero () eq
outer (suc m) (inj₁ _) ()
outer (suc zero) (inj₂ (inj₁ _)) eq = cong unlim eq
outer (suc (suc m)) (inj₂ (inj₁ _)) eq = ⊥-elim (two≢one (cong (λ z → unlim z 0) eq))
outer (suc m) (inj₂ (inj₂ (i , s))) eq = inner m i s eq

inner zero zero (inj₁ _) ()
inner (suc m) zero (inj₁ _) ()
inner zero zero (inj₂ s) eq = outer zero s eq
inner (suc m) zero (inj₂ s) eq = outer (suc m) s eq
inner m (suc i) (inj₁ _) ()
inner m (suc i) (inj₂ (inj₁ _)) eq = ⊥-elim (no-lim (psum gᴸ m) i _ eq)
inner m (suc i) (inj₂ (inj₂ s)) eq = inner m i s eq

at→fe : At (tl τᴸ) Xᴾ → FE
at→fe ((m , s) , eq) = outer m s eq

fe→at : FE → At (tl τᴸ) Xᴾ
fe→at fe = (1 , inj₂ (inj₁ tt)) , cong lim fe
```

`FE` 的两边逐点相等 (`fe-pointwise`)，所以它是函数外延的一个实例：有函数外延时这一对 "在位置上"，诚实的派发是保留；没有时 `FE` 与它的否定都不是本仓库里的定理 (判断)。

```agda
lᴾ : Lgl K₂ω ξᴾ
lᴾ = plus-lgl G.top (Gκ (G.suc wᴾ)) tt (Gκ-legal (G.suc wᴾ) lwᴾ)

nᴾ : Nested K₂ω ξᴾ
nᴾ = plus-ns G.top (Gκ (G.suc wᴾ)) tt (Gκ-nested (G.suc wᴾ))

shape→fe : (At (tl τᴸ) Xᴾ → ⊥) ⊎ ((At (tl τᴸ) Xᴾ → ⊥) → ⊥) → (FE → ⊥) ⊎ ((FE → ⊥) → ⊥)
shape→fe (inj₁ no) = inj₁ (λ fe → no (fe→at fe))
shape→fe (inj₂ nn) = inj₂ (λ nfe → nn (λ a → nfe (at→fe a)))

-- 这一对上接口的 Honest (任何 OwnFold) 推出 FE 的弱判定.
weak-fe : (F : OwnFold (posT τᴸ)) → Honest (posT τᴸ) F ξᴾ → (FE → ⊥) ⊎ ((FE → ⊥) → ⊥)
weak-fe F H = shape→fe (read-shape (F ξᴾ lᴾ nᴾ) (proj₁ (H lᴾ nᴾ)) (proj₂ (H lᴾ nᴾ)))

decided : At (tl τᴸ) Xᴾ ⊎ (At (tl τᴸ) Xᴾ → ⊥) → FE ⊎ (FE → ⊥)
decided (inj₁ a) = inj₁ (at→fe a)
decided (inj₂ no) = inj₂ (λ fe → no (fe→at fe))

-- 缺的陈述在这一对上的内容.
askdec→fe : AskDec → FE ⊎ (FE → ⊥)
askdec→fe dec = decided
  (dec (G.suc (nrm wᴸ)) (γ wᴸ) (inj₁ tt) (G.suc (nrm wᴾ)) (γ wᴾ) (inj₁ tt) _ _ _ (1 , asked₁))
```

§4 的无前提折叠在这一对上取折叠 (两个坐标都含极限)。所以它在这一对上完全，当且仅当 `FE` 不成立。

```agda
dᴾ : N.D ξᴾ
dᴾ = ask-noem asked₁ (noem 1)

folds-there : IsLim (P.Ψᶠ τᴸ ξᴾ dᴾ lᴾ nᴾ)
folds-there = tt

complete-there→ : (At (tl τᴸ) Xᴾ → Kept (tl τᴸ) Xᴾ (P.Ψᶠ τᴸ ξᴾ dᴾ lᴾ nᴾ)) → FE → ⊥
complete-there→ cm fe = lim≢kept (P.Ψᶠ τᴸ ξᴾ dᴾ lᴾ nᴾ) folds-there (cm (fe→at fe))
  where
  lim≢kept : ∀ {m k} (y : Raw m) → IsLim y → Kept m k y → ⊥
  lim≢kept (G.lim f) h (r , q , c , t , g , ())

complete-there← : (FE → ⊥) → At (tl τᴸ) Xᴾ → Kept (tl τᴸ) Xᴾ (P.Ψᶠ τᴸ ξᴾ dᴾ lᴾ nᴾ)
complete-there← nfe a = ⊥-elim (nfe (at→fe a))
```

## 6 同一支里的一对：无前提的派发在那里不完全

目标在坐标 `suc (nrm wᴾ)` 那一支的根上，结点在同一支里层号 0 的位置上 (`keepAll` 搬进来的)。结点层在目标层的位置上 (`same-at`)，这一对被问到 (`askedˢ`)，
而 §4 的派发从树里读不出两个位置在同一支 (坐标含极限，不可判定)，取了折叠 (`same-folds`)。`AskDec` 把这一种对也算在前提里。

```agda
eᴾ : Gd zero raw1 (G.suc wᴾ)
eᴾ = inj₂ (inj₂ (zero , inj₁ refl)) , lwᴾ , raw0-Nested (G.suc wᴾ)

τᴾ : Tg
τᴾ = at (G.suc (nrm wᴾ)) (γ wᴾ) (inj₁ tt)

ζˢ : Raw Xᴾ
ζˢ = G.lc (0 , inj₁ tt) G.zero G.top (λ _ _ → G.top)

eˢ : Gd Xᴾ G.top ζˢ
eˢ = inj₂ (inj₁ refl) ,
  ((λ η e → inj₁ refl) , (λ η e η′ e′ q → inj₁ refl) , (λ η e e′ → refl) , tt , (λ η e → tt)) ,
  (tt , tt , tt , (λ η e → tt))

ξˢ : RΩ
ξˢ = plusΩ G.top (plusΩ (Gκ wᴾ)
  (keepAll Xᴾ (nS (νᴮ (G.suc (nrm wᴾ)) (γ wᴾ))) ζˢ))

askedˢ : Ask base (pointsᴺ 1) τᴾ ξˢ
askedˢ = drive (obs here¹ (G.suc wᴾ) eᴾ) ζˢ eˢ

same-at : At (tl τᴾ) (lev K₂ω (br (G.suc (nrm wᴾ)) (γ wᴾ) (inj₂ (0 , inj₁ tt))))
same-at = (0 , inj₁ tt) , refl

same-folds : ∀ (d : N.D ξˢ) (l : Lgl K₂ω ξˢ) (nb : Nested K₂ω ξˢ) →
  IsLim (P.Ψᶠ τᴾ ξˢ d l nb)
same-folds d l nb = tt
```

## 7 归一链不在有限坐标的定义域里

第 1 个归一链点的第 `suc wᴸ` 支的头在坐标 `suc (nrm wᴸ)` 那一支上，这个坐标含极限。所以 [YiGenFoldFin](YiGenFoldFin.lagda.md) 的无前提结果不覆盖归一链。

```agda
point₁ᴺ-out : F.D (pointsᴺ 1) → ⊥
point₁ᴺ-out d = proj₁ (proj₂ d (G.suc wᴸ) eᴸ)
```

## 范围与归类

`AskDec` 与上一轮的 `YiOmNegBranch.TopBranch` 不是同一个陈述。`TopBranch` 说的是 `top` 的各支在一切目标下的像与保留律，推出 LPO，机制是判定一个固定的有限层号是否出现在另一支的极限层号的位置上；
`AskDec` 说的是已经放在归一坐标的槽位上的结点对，本篇从它得到的是一个函数外延实例的判定，机制是两个极限层号字面相等。两者之间的蕴涵没有证；两者都由 `Locate` 给出。
归一把 `TopBranch` 的探针 (`coordᴸ α`) 换成部分和，那里有限层号总在位置上，所以那条机制不照搬到 `AskDec` 上 (判断，没有编译)。
实例不否定任何路线：`weak-fe` 与 `askdec→fe` 的结论都不是矛盾；它说的是这一对上诚实的派发等价于定下一个函数外延实例的真假。量化域是调用闭包；根上的链实际走到的可数个坐标上是否出现同类的对，没有判定。
§6 的那一种 (同一支) 不是这类障碍：位置在同一支这件事在生成 `KT` 时是已知的，只是搬进槽位以后树里读不出；把折叠写在生成数据上能否补上它，没有做。
