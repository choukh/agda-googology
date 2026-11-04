# 折叠: 由 [LevelFixTree](LevelFixTree.lagda.md) 用脚本改写

> 不含记号. 结论写在 [LevelNoK](LevelNoK.lagda.md). 折叠的算法不变: 同样的 `O`, `ψ`, `Ω̇`, `ι`, `kdec`, `cmpN`, `cmpK`, `keepP`. 改动只在证据的形状:
>
> 1. 表与地板的项是纤维里的证据 ([LevelNoKLv](LevelNoKLv.lagda.md) 的 `Up`, `Bel′`, `Flr`, `Ev`), 两个分支的比较走 `cmpBr`.
> 2. `CovB`, `Ab`: 帧的证据是路径证据的像 (带方程 `e₁ ≡ lkG k e`). 这个方程只在树里搬运, 从不被模式匹配到名字上.
> 3. 求界走 `Tp`: `gr` 给守卫, `upF` 给新的上界. `sD`, `sF`, `self<ᵉ` 给空表时的上界.
>
> 证据缺失的分支给 `o0`, 同 [GuardTightTree](GuardTightTree.lagda.md). 这是定义, 不是定理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LevelNoKX using (XU)

module OCF.Align.LevelNoKTree (X : XU) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.LevelNoKLv
open XU X
open Lv 𝔻
open import OCF.Align.LevelNoKTab 𝔻 using (kdec; Dec′; _⊙_; adm⊙; toCp; admTo; Strict; st-suc; st-lim; st-fst; st-bra; stCp; st⊙)
open import OCF.Align.LevelNoKBase X

leq : ℕ → ℕ → Bool
leq zero    _       = true
leq (suc _) zero    = false
leq (suc a) (suc b) = leq a b
```

## §1 静态的可容许性

```agda
adm-wk : ∀ {π ρ a b} → Wk π ρ → (r : a < b) → Adm (cov π) r → Adm (cov ρ) r
adm-wk w zero _ = tt
adm-wk w (suc r) a = adm-wk w r a
adm-wk w (lim n r) a = adm-wk w r a
adm-wk w (fst r) a = adm-wk w r a
adm-wk w (bra η e r) ((c₁ , t₁ , g₁ , e₁ , m , k) , a) = (c₁ , t₁ , g₁ , e₁ , w m , k) , adm-wk w r a
```

## §2 第 0 层的值, 数据树

`V R ξ`: 严格位置 $R$ 处的层 $k$ 的值. `Vs`, `Vc` 对位置递归, 所以到底总是 `O k ξ`.

```agda
module _ (L : LG) (U : ∀ {k} → k < L → Fl → Set) (V : ∀ {k} → Strict k L → Fl → Set) where
  data O₊ : Fl → Set where
    o0  : ∀ {π} → O₊ π
    os  : ∀ {π} → O₊ π → O₊ π
    ol  : ∀ {π} → (ℕ → O₊ π) → O₊ π
    oŝ  : ∀ {π} (c₀ : D) → O₊ π → ((η : D) → c₀ ⊑ᴰ η → O₊ π) → O₊ π
    oĉ  : ∀ {π} (c₀ : D) → LG → ((η : D) → c₀ ⊑ᴰ η → LG) → O₊ π → ((η : D) → c₀ ⊑ᴰ η → O₊ π) → O₊ π
    owk : ∀ {π ρ} → Wk π ρ → O₊ π → O₊ ρ
    ocv : ∀ {π ρ} → Cov π ρ → O₊ π → O₊ ρ
    omk : ∀ {π ξ k} (R : Strict k L) → Wk ξ π → AdmC (cov π) (stCp R) → V R ξ → O₊ π → O₊ π
    oΩ  : ∀ {π k} (r : k < L) → Adm (cov π) r → (∀ ξ → U r ξ → O₊ (ξ ∪ π)) → O₊ π
    ocl : ∀ {π c₁ t₁ g₁ c₂ t₂ g₂} (P : Cp (lc c₂ t₂ g₂) L) → Lk (lc c₂ t₂ g₂) (lc c₁ t₁ g₁) → AdmC (cov π) P →
          O₊ π → (∀ η e → O₊ (π ∪ tk (frm c₁ t₁ g₁ η e))) → O₊ π

O  : LG → Fl → Set
Us : ∀ L {k} → k < L → Fl → Set
Vs : ∀ L {k} → Strict k L → Fl → Set
Vc : ∀ L {k} → Cp k L → Fl → Set
O L π = O₊ L (Us L) (Vs L) π
Us (suc a) zero        ξ = O a ξ
Us (suc b) (suc r)     ξ = Us b r ξ
Us (lim f) (lim n r)   ξ = Us (f n) r ξ
Us (lc c t g) (fst r)  ξ = Us t r ξ
Us (lc c t g) (bra η e r) ξ = Us (g η e) r ξ
Vs (suc b) (st-suc P) ξ = Vc b P ξ
Vs (lim f) (st-lim n P) ξ = Vc (f n) P ξ
Vs (lc c t g) (st-fst P) ξ = Vc t P ξ
Vs (lc c t g) (st-bra η e P) ξ = Vc (g η e) P ξ
Vc a self ξ = O a ξ
Vc (suc b) (suc P) ξ = Vc b P ξ
Vc (lim f) (lim n P) ξ = Vc (f n) P ξ
Vc (lc c t g) (fst P) ξ = Vc t P ξ
Vc (lc c t g) (bra η e P) ξ = Vc (g η e) P ξ

outU : ∀ {L k} (r : k < L) {ξ} → Us L r ξ → O k ξ
outU zero        x = x
outU (suc r)     x = outU r x
outU (lim n r)   x = outU r x
outU (fst r)     x = outU r x
outU (bra η e r) x = outU r x

intoU : ∀ {L k} (r : k < L) {ξ} → O k ξ → Us L r ξ
intoU zero        x = x
intoU (suc r)     x = intoU r x
intoU (lim n r)   x = intoU r x
intoU (fst r)     x = intoU r x
intoU (bra η e r) x = intoU r x

outC : ∀ {L k} (P : Cp k L) {ξ} → Vc L P ξ → O k ξ
outC self        x = x
outC (suc P)     x = outC P x
outC (lim n P)   x = outC P x
outC (fst P)     x = outC P x
outC (bra η e P) x = outC P x

intoC : ∀ {L k} (P : Cp k L) {ξ} → O k ξ → Vc L P ξ
intoC self        x = x
intoC (suc P)     x = intoC P x
intoC (lim n P)   x = intoC P x
intoC (fst P)     x = intoC P x
intoC (bra η e P) x = intoC P x

outV : ∀ {L k} (R : Strict k L) {ξ} → Vs L R ξ → O k ξ
outV (st-suc P)     x = outC P x
outV (st-lim n P)   x = outC P x
outV (st-fst P)     x = outC P x
outV (st-bra η e P) x = outC P x

intoV : ∀ {L k} (R : Strict k L) {ξ} → O k ξ → Vs L R ξ
intoV (st-suc P)     x = intoC P x
intoV (st-lim n P)   x = intoC P x
intoV (st-fst P)     x = intoC P x
intoV (st-bra η e P) x = intoC P x

-- 自然数层
natL : ℕ → LG
natL zero = zero
natL (suc n) = suc (natL n)

natV : LG → Maybe ℕ
natV zero = just 0
natV (suc a) with natV a
... | just n = just (suc n)
... | nothing = nothing
natV (lim _) = nothing
natV (lc _ _ _) = nothing

natOf : LG → ℕ
natOf zero = 0
natOf (suc a) = suc (natOf a)
natOf (lim _) = 0
natOf (lc _ _ _) = 0

gapL : LG → D → Bool
gapL k c with natV k
... | just n = leq n (ix c)
... | nothing = false

-- 层号嵌进任何一层的树: 闭包写成带守卫的闭包
emO : ∀ {k} → LG → O k tz
emO zero = o0
emO (suc a) = os (emO a)
emO (lim f) = ol (λ n → emO (f n))
emO (lc c t g) = oŝ c (emO t) (λ η e → emO (g η e))

-- 读回, 对一切层. 第 j 层的节点 Ω_{j+1} 读成闭包, 下界 nodeC j, 第一支在 nodeF j.
-- 高于塔的 j 的 nodeC 是哑值; j 不是自然数的节点只在读高层的树时出现, 这里不读.
rb : ∀ {k π} → O k π → LG
rb o0 = zero
rb (os a) = suc (rb a)
rb (ol F) = lim (λ n → rb (F n))
rb (oŝ c t g) = lc c (rb t) (λ η e → rb (g η e))
rb (oĉ c z zg o₀ o) = lc c (rb o₀) (λ η e → rb (o η e))
rb (owk w x) = rb x
rb (ocv w x) = rb x
rb (omk R lk ad z x) = rb x
rb (oΩ {k = j} r cv h) =
  lc (nodeC (natOf j)) (rb (h tz (intoU r (emO (nodeF (natOf j))))))
     (λ η e → rb (h tz (intoU r (emO (emᵈ η)))))
rb (ocl {c₁ = c₁} P k cv t g) = lc c₁ (rb t) (λ η e → rb (g η e))

-- 闭包: 链语义的层上带链
ŝ? : ∀ {k π} → Bool → (c₀ : D) → LG → ((η : D) → c₀ ⊑ᴰ η → LG) → O k π → ((η : D) → c₀ ⊑ᴰ η → O k π) → O k π
ŝ? true  c₀ z zg o₀ o = oĉ c₀ z zg o₀ o
ŝ? false c₀ z zg o₀ o = oŝ c₀ o₀ o
```

## §3 加法, 嵌入, 搬运

```agda
asl : ∀ {a b d} → Wk ((a ∪ b) ∪ d) (a ∪ (b ∪ d))
asl (ml (ml m)) = ml m
asl (ml (mr m)) = mr (ml m)
asl (mr m) = mr (mr m)

asr : ∀ {a b d} → Wk (a ∪ (b ∪ d)) ((a ∪ b) ∪ d)
asr (ml m) = ml (ml m)
asr (mr (ml m)) = ml (mr m)
asr (mr (mr m)) = mr m

swp : ∀ {a b d} → Wk (b ∪ (a ∪ d)) (a ∪ (b ∪ d))
swp (ml m) = mr (ml m)
swp (mr (ml m)) = ml m
swp (mr (mr m)) = mr (mr m)

sw₃ : ∀ {a b d} → Wk ((a ∪ d) ∪ b) ((a ∪ b) ∪ d)
sw₃ (ml (ml m)) = ml (ml m)
sw₃ (ml (mr m)) = mr m
sw₃ (mr m) = ml (mr m)

infixl 6 _⊕_
_⊕_ : ∀ {k φ ψ} → O k φ → O k ψ → O k (φ ∪ ψ)
W ⊕ o0       = owk ml W
W ⊕ os a     = os (W ⊕ a)
W ⊕ ol F     = ol (λ n → W ⊕ F n)
_⊕_ {k = k} W (oŝ c₀ t g) = ŝ? (gapL k c₀) c₀ (rb t) (λ η e → rb (g η e)) (W ⊕ t) (λ η e → W ⊕ g η e)
W ⊕ oĉ c₀ z zg o₀ o = oĉ c₀ z zg (W ⊕ o₀) (λ η e → W ⊕ o η e)
W ⊕ owk w t = owk (λ { (ml m) → ml m ; (mr m) → mr (w m) }) (W ⊕ t)
W ⊕ ocv w t = ocv (λ { (ml m) → cov-exact ml m ; (mr m) → cvR (w m) }) (W ⊕ t)
  where
  cvR : ∀ {φ′ ρ c t g η} {e : c ⊑ᴰ η} → Dm ρ c t g e → Dm (φ′ ∪ ρ) c t g e
  cvR (f , m , k , l) = f , mr m , k , l
W ⊕ omk R lk ad z x = W ⊕ x
W ⊕ oΩ r cv h = oΩ r (adm-wk mr r cv) (λ ξ z → owk swp (W ⊕ h ξ z))
W ⊕ ocl P k cv t g = ocl P k (admC-wk mr P cv) (W ⊕ t) (λ η e → owk asr (W ⊕ g η e))
```

**搬运.** 对 `≈`, 与 [LvGuardTree](LvGuardTree.lagda.md) 同形, 加两行. `ocv` 逐点. `omk`: $R$ 沿 `≈` 搬运, $z$ 也一起搬运: `trV` 对 $R$ 与 `≈` 同时结构递归, 到底调用 `trO` 的 `≈` 是结构子项.

```agda
record RestrO {k a : LG} (r : k < a) (b : LG) : Set where
  constructor restrO
  field
    {repO} : LG
    eqO    : k ≈ repO
    ltO    : repO < b
    trfO   : ∀ E → Adm E r → Adm E ltO
    backO  : ∀ {ξ} → O repO ξ → O k ξ
open RestrO public

record RestrV {k a b : LG} (R : Strict k a) (ξ : Fl) (z : Vs a R ξ) : Set where
  constructor restrV
  field
    {repW} : LG
    posW   : Strict repW b
    trfW   : ∀ E → AdmC E (stCp R) → AdmC E (stCp posW)
    valW   : Vs b posW ξ
open RestrV public

record RestrC {k a b : LG} (P : Cp k a) (ξ : Fl) (z : Vc a P ξ) : Set where
  constructor restrC
  field
    {repC} : LG
    posC   : Cp repC b
    trfC   : ∀ E → AdmC E P → AdmC E posC
    valC   : Vc b posC ξ
open RestrC public

trO   : ∀ {a b π} → a ≈ b → O a π → O b π
tr⁻O  : ∀ {a b π} → a ≈ b → O b π → O a π
resO  : ∀ {k a b} (r : k < a) → a ≈ b → RestrO r b
res⁻O : ∀ {k a b} (r : k < b) → a ≈ b → RestrO r a
trC   : ∀ {k a b ξ} (P : Cp k a) (e : a ≈ b) (z : Vc a P ξ) → RestrC {b = b} P ξ z
tr⁻C  : ∀ {k a b ξ} (P : Cp k b) (e : a ≈ b) (z : Vc b P ξ) → RestrC {b = a} P ξ z
trV   : ∀ {k a b ξ} (R : Strict k a) (e : a ≈ b) (z : Vs a R ξ) → RestrV {b = b} R ξ z
tr⁻V  : ∀ {k a b ξ} (R : Strict k b) (e : a ≈ b) (z : Vs b R ξ) → RestrV {b = a} R ξ z

trO e o0 = o0
trO e (os a) = os (trO e a)
trO e (ol F) = ol (λ n → trO e (F n))
trO e (oŝ c₀ t g) = oŝ c₀ (trO e t) (λ η d → trO e (g η d))
trO e (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (trO e o₀) (λ η d → trO e (o η d))
trO e (owk w t) = owk w (trO e t)
trO e (ocv w t) = ocv w (trO e t)
trO e (omk R lk ad z x) with trV R e z
... | restrV R′ u z′ = omk R′ lk (u _ ad) z′ (trO e x)
trO e (oΩ q ac h) = oΩ (ltO (resO q e)) (trfO (resO q e) _ ac) (λ ξ z → trO e (h ξ (intoU q (backO (resO q e) (outU (ltO (resO q e)) z)))))
trO e (ocl P k cv t g) with ≈-moveᴷ e P
... | viaᴷ d P′ u = ocl P′ (lkT (≈-sym d) k) (u _ cv) (trO e t) (λ η d′ → trO e (g η d′))

tr⁻O e o0 = o0
tr⁻O e (os a) = os (tr⁻O e a)
tr⁻O e (ol F) = ol (λ n → tr⁻O e (F n))
tr⁻O e (oŝ c₀ t g) = oŝ c₀ (tr⁻O e t) (λ η d → tr⁻O e (g η d))
tr⁻O e (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (tr⁻O e o₀) (λ η d → tr⁻O e (o η d))
tr⁻O e (owk w t) = owk w (tr⁻O e t)
tr⁻O e (ocv w t) = ocv w (tr⁻O e t)
tr⁻O e (omk R lk ad z x) with tr⁻V R e z
... | restrV R′ u z′ = omk R′ lk (u _ ad) z′ (tr⁻O e x)
tr⁻O e (oΩ q ac h) = oΩ (ltO (res⁻O q e)) (trfO (res⁻O q e) _ ac) (λ ξ z → tr⁻O e (h ξ (intoU q (backO (res⁻O q e) (outU (ltO (res⁻O q e)) z)))))
tr⁻O e (ocl P k cv t g) with ≈-moveᴷ (≈-sym e) P
... | viaᴷ d P′ u = ocl P′ (lkT (≈-sym d) k) (u _ cv) (tr⁻O e t) (λ η d′ → tr⁻O e (g η d′))

resO zero      (s≈ e) = restrO e zero (λ _ _ → tt) (tr⁻O e)
resO (suc r)   (s≈ e) with resO r e
... | restrO d l t b = restrO d (suc l) t b
resO (lim n r) (l≈ h) with resO r (h n)
... | restrO d l t b = restrO d (lim n l) t b
resO (fst r)   (o≈ d′ e h h⁻ hˡ hʳ) with resO r e
... | restrO d l t b = restrO d (fst l) t b
resO (bra η e₁ r) (o≈ d′ e h h⁻ hˡ hʳ) with resO r (h η e₁)
... | restrO d l t b = restrO d (bra η (conv d′ e₁) l) (λ E u → Bel-resp {E} (o≈ d′ e h h⁻ hˡ hʳ) (proj₁ u) , t E (proj₂ u)) b

res⁻O zero      (s≈ e) = restrO (≈-sym e) zero (λ _ _ → tt) (trO e)
res⁻O (suc r)   (s≈ e) with res⁻O r e
... | restrO d l t b = restrO d (suc l) t b
res⁻O (lim n r) (l≈ h) with res⁻O r (h n)
... | restrO d l t b = restrO d (lim n l) t b
res⁻O (fst r)   (o≈ d′ e h h⁻ hˡ hʳ) with res⁻O r e
... | restrO d l t b = restrO d (fst l) t b
res⁻O (bra η e₁ r) (o≈ d′ e h h⁻ hˡ hʳ) with res⁻O r (h⁻ η e₁)
... | restrO d l t b = restrO d (bra η (conv (≅ᴰ-sym d′) e₁) l) (λ E u → Bel-resp {E} (≈-sym (o≈ d′ e h h⁻ hˡ hʳ)) (proj₁ u) , t E (proj₂ u)) b

trC self e z = restrC self (λ _ _ → tt) (trO e z)
trC (suc P) (s≈ e) z with trC P e z
... | restrC Q u z′ = restrC (suc Q) u z′
trC (lim n P) (l≈ h) z with trC P (h n) z
... | restrC Q u z′ = restrC (lim n Q) u z′
trC (fst P) (o≈ d e h h⁻ hˡ hʳ) z with trC P e z
... | restrC Q u z′ = restrC (fst Q) u z′
trC (bra η e₁ P) (o≈ d e h h⁻ hˡ hʳ) z with trC P (h η e₁) z
... | restrC Q u z′ = restrC (bra η (conv d e₁) Q) (λ E x → Bel-resp {E} (o≈ d e h h⁻ hˡ hʳ) (proj₁ x) , u E (proj₂ x)) z′

tr⁻C self e z = restrC self (λ _ _ → tt) (tr⁻O e z)
tr⁻C (suc P) (s≈ e) z with tr⁻C P e z
... | restrC Q u z′ = restrC (suc Q) u z′
tr⁻C (lim n P) (l≈ h) z with tr⁻C P (h n) z
... | restrC Q u z′ = restrC (lim n Q) u z′
tr⁻C (fst P) (o≈ d e h h⁻ hˡ hʳ) z with tr⁻C P e z
... | restrC Q u z′ = restrC (fst Q) u z′
tr⁻C (bra η e₁ P) (o≈ d e h h⁻ hˡ hʳ) z with tr⁻C P (h⁻ η e₁) z
... | restrC Q u z′ = restrC (bra η (conv (≅ᴰ-sym d) e₁) Q) (λ E x → Bel-resp {E} (≈-sym (o≈ d e h h⁻ hˡ hʳ)) (proj₁ x) , u E (proj₂ x)) z′

trV (st-suc P) (s≈ e) z with trC P e z
... | restrC Q u z′ = restrV (st-suc Q) u z′
trV (st-lim n P) (l≈ h) z with trC P (h n) z
... | restrC Q u z′ = restrV (st-lim n Q) u z′
trV (st-fst P) (o≈ d e h h⁻ hˡ hʳ) z with trC P e z
... | restrC Q u z′ = restrV (st-fst Q) u z′
trV (st-bra η e₁ P) (o≈ d e h h⁻ hˡ hʳ) z with trC P (h η e₁) z
... | restrC Q u z′ = restrV (st-bra η (conv d e₁) Q) (λ E x → Bel-resp {E} (o≈ d e h h⁻ hˡ hʳ) (proj₁ x) , u E (proj₂ x)) z′

tr⁻V (st-suc P) (s≈ e) z with tr⁻C P e z
... | restrC Q u z′ = restrV (st-suc Q) u z′
tr⁻V (st-lim n P) (l≈ h) z with tr⁻C P (h n) z
... | restrC Q u z′ = restrV (st-lim n Q) u z′
tr⁻V (st-fst P) (o≈ d e h h⁻ hˡ hʳ) z with tr⁻C P e z
... | restrC Q u z′ = restrV (st-fst Q) u z′
tr⁻V (st-bra η e₁ P) (o≈ d e h h⁻ hˡ hʳ) z with tr⁻C P (h⁻ η e₁) z
... | restrC Q u z′ = restrV (st-bra η (conv (≅ᴰ-sym d) e₁) Q) (λ E x → Bel-resp {E} (≈-sym (o≈ d e h h⁻ hˡ hʳ)) (proj₁ x) , u E (proj₂ x)) z′

trL : ∀ {a b π} → Lk a b → O a π → O b π
trL (inj₁ e) x = trO e x
trL (inj₂ refl) x = x

trL⁻ : ∀ {a b π} → Lk a b → O b π → O a π
trL⁻ (inj₁ e) x = tr⁻O e x
trL⁻ (inj₂ refl) x = x
```

**嵌入.** `ι a P d`: 层 $a$ 的值, 经 $a$ 与 $a'$ 的等价, 放到 $L$ 里的位置 $a'$. 它对 $a$ 与值字典序递归: 读到 `omk` 时 $a$ 严格下降 (`ιV`, `ιC` 对位置递归), 其余情形 $a$ 不变, 值是结构子项. **`omk` 这一行就是修正:** 位置规范化, $z$ 直接嵌到规范的位置, 地板变成规范位置的帧, 用 `ocv` 盖住.

```agda
infixr 8 _◁_
_◁_ : ∀ {k a b} → Cp a b → k < a → k < b
self      ◁ r = r
suc P     ◁ r = suc (P ◁ r)
lim n P   ◁ r = lim n (P ◁ r)
fst P     ◁ r = fst (P ◁ r)
bra η e P ◁ r = bra η e (P ◁ r)

adm◁ : ∀ {E k a b} (P : Cp a b) {r : k < a} → AdmC E P → Adm E r → Adm E (P ◁ r)
adm◁ self        _ y = y
adm◁ (suc P)     x y = adm◁ P x y
adm◁ (lim n P)   x y = adm◁ P x y
adm◁ (fst P)     x y = adm◁ P x y
adm◁ (bra η e P) (u , x) y = u , adm◁ P x y

cvP : ∀ {k a b} (P : Cp a b) (r : k < a) {ξ} → Us b (P ◁ r) ξ → Us a r ξ
cvP self        r x = x
cvP (suc P)     r x = cvP P r x
cvP (lim n P)   r x = cvP P r x
cvP (fst P)     r x = cvP P r x
cvP (bra η e P) r x = cvP P r x

record RL {k a : LG} (r : k < a) (b : LG) : Set where
  constructor rl
  field
    {repL} : LG
    eqL    : Lk k repL
    ltL    : repL < b
    trfL   : ∀ E → Adm E r → Adm E ltL
    backL  : ∀ {ξ} → O repL ξ → O k ξ
open RL public

resL : ∀ {k a b} (r : k < a) → Lk a b → RL r b
resL r (inj₁ e) with resO r e
... | restrO d l t b = rl (inj₁ d) l t b
resL r (inj₂ refl) = rl (inj₂ refl) r (λ _ a → a) (λ x → x)

mvL : ∀ {k a a′} (R : Strict k a) → Lk a a′ → MvS {k} {a} {a′} R
mvL R (inj₁ e) = mvS R e
mvL R (inj₂ refl) = mvs (inj₂ refl) R (λ _ u → u)

module Emb (L : LG) (tc : Tc L) where
  ι  : ∀ a {a′ π} (P : Cp a′ L) → Lk a a′ → O a π → O L (π ∪ pF P)
  ιC : ∀ a {k ξ a′} (Q : Cp k a) (P : Cp a′ L) → Lk k a′ → Vc a Q ξ → O L (ξ ∪ pF P)
  ιV : ∀ a {k ξ a′} (R : Strict k a) (P : Cp a′ L) → Lk k a′ → Vs a R ξ → O L (ξ ∪ pF P)

  ιC a self P d z = ι a P d z
  ιC (suc b) (suc Q) P d z = ιC b Q P d z
  ιC (lim f) (lim n Q) P d z = ιC (f n) Q P d z
  ιC (lc c t g) (fst Q) P d z = ιC t Q P d z
  ιC (lc c t g) (bra η e Q) P d z = ιC (g η e) Q P d z

  ιV (suc b) (st-suc Q) P d z = ιC b Q P d z
  ιV (lim f) (st-lim n Q) P d z = ιC (f n) Q P d z
  ιV (lc c t g) (st-fst Q) P d z = ιC t Q P d z
  ιV (lc c t g) (st-bra η e Q) P d z = ιC (g η e) Q P d z

  ι a P d o0 = o0
  ι a P d (os x) = os (ι a P d x)
  ι a P d (ol F) = ol (λ n → ι a P d (F n))
  ι a P d (oŝ c₀ t g) = ŝ? (gapL a c₀) c₀ (rb t) (λ η e → rb (g η e)) (ι a P d t) (λ η e → ι a P d (g η e))
  ι a P d (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (ι a P d o₀) (λ η e → ι a P d (o η e))
  ι a P d (owk w t) = owk (λ { (ml m) → ml (w m) ; (mr m) → mr m }) (ι a P d t)
  ι a P d (ocv w t) = ocv (λ { (ml m) → lcv (w m) ; (mr m) → cov-exact mr m }) (ι a P d t)
    where
    lcv : ∀ {ρ σ c t g η} {e : c ⊑ᴰ η} → Dm ρ c t g e → Dm (ρ ∪ σ) c t g e
    lcv (f , m , k , l) = f , ml m , k , l
  ι a {π = π} P d (omk {ξ = ξ} R lk ad z x) with mvL R d
  ... | mvs e R′ u with nfS L tc (st⊙ P R′)
  ...   | nfs e₂ pos t r =
    ocv cv (omk pos ml (admC-wk mr (stCp pos) (admP (stCp pos))) (intoV pos (trL (lkC e e₂) (outV R z))) (ιV a R (stCp pos) (lkC e e₂) z))
    where
    ad₂ : AdmC (cov (π ∪ pF P)) (stCp (st⊙ P R′))
    ad₂ = stCp-adm P R′ (admC-wk mr P (admP P)) (admC-wk ml (stCp R′) (u (cov π) ad))
    cv : Cov (ξ ∪ pF (stCp pos)) (π ∪ pF P)
    cv (ml m) = cov-exact ml (lk m)
    cv (mr m) = covOf (stCp pos) (r _ ad₂) m
  ι a P d (oΩ r cv h) with resL r d
  ... | rl _ s u b = oΩ (P ◁ s) (adm◁ {cov _} P (admC-wk mr P (admP P)) (adm-wk ml s (u _ cv)))
                     (λ ξ y → owk asl (ι a P d (h ξ (intoU r (b (outU s (cvP P s y)))))))
  ι a P (inj₁ e) (ocl Q k cv t g) with ≈-moveᴷ e Q
  ... | viaᴷ d′ Q′ u = ocl (P ⊙ Q′) (lkT (≈-sym d′) k) (adm⊙ {cov _} P (admC-wk mr P (admP P)) (admC-wk ml Q′ (u _ cv)))
                           (ι a P (inj₁ e) t) (λ η e′ → owk sw₃ (ι a P (inj₁ e) (g η e′)))
  ι a P (inj₂ refl) (ocl Q k cv t g) =
    ocl (P ⊙ Q) k (adm⊙ {cov _} P (admC-wk mr P (admP P)) (admC-wk ml Q cv))
        (ι a P (inj₂ refl) t) (λ η e′ → owk sw₃ (ι a P (inj₂ refl) (g η e′)))
```

## §4 $\dot\Omega$

`Ω̇ k`: 没有地板, 没有高度. 后继的节点与极限的项带记号. 闭包的分支 $\eta$ 下面多一个帧, 第一支与分支都经 `ι`, 读到记号就收紧.

```agda
Ω̇ : ∀ k → Tc k → O k tz
Ω̇ zero tc = os o0
Ω̇ (suc k) tc = oΩ zero tt (λ ξ z → omk (st-suc self) ml tt z (Emb.ι (suc k) tc k (suc self) (inj₂ refl) z))
Ω̇ (lim f) tc = ol (λ n → owk (λ { (ml ()) ; (mr ()) })
                              (omk (st-lim n self) ml tt (Ω̇ (f n) (tc n)) (Emb.ι (lim f) tc (f n) (lim n self) (inj₂ refl) (Ω̇ (f n) (tc n)))))
Ω̇ (lc c t g) tc = ocl self (inj₂ refl) tt
  (owk (λ { (ml ()) ; (mr ()) }) (Emb.ι (lc c t g) tc t (fst self) (inj₂ refl) (Ω̇ t (proj₁ (proj₂ tc)))))
  (λ η e → owk (λ { (ml ()) ; (mr (ml m)) → mr m ; (mr (mr ())) })
               (Emb.ι (lc c t g) tc (g η e) (bra η e self) (inj₂ refl) (Ω̇ (g η e) (proj₂ (proj₂ tc) η e))))

repᵒ : ∀ {k π} → O k π → ℕ → O k π
repᵒ x zero    = o0
repᵒ x (suc m) = owk (λ { (ml m) → m ; (mr m) → m }) (x ⊕ repᵒ x m)
```

## §5 折叠的状态

`Evd`: 帧在表里的证据, 带这个节点在 $c$ 里的一个位置 (`kdec` 要). `Ab`: 帧在输出里的映射 (闭包保留时). 一个帧可以两样都有 (上升时), 也可以都没有 (这时比较给 `cj`, 输出 `o0`).

```agda
selfC : ∀ {a c} → c ≈ c → Cp a c → a ≈ a
selfC e self = e
selfC (s≈ e) (suc p) = selfC e p
selfC (l≈ h) (lim n p) = selfC (h n) p
selfC (o≈ d e h h⁻ hˡ hʳ) (fst p) = selfC e p
selfC (o≈ d e h h⁻ hˡ hʳ) (bra η e₁ p) = selfC (hˡ η e₁) p

-- 节点的层 k 对自然数目标 n: 结构递归, 不走路径, 不读证据
sucP : ∀ n {rp} → rp < natL n → suc rp < suc (natL n)
sucP (suc n) zero = zero
sucP (suc n) (suc s) = suc (sucP n s)

zero<nat : ∀ n → zero < natL (suc n)
zero<nat zero = zero
zero<nat (suc n) = suc (zero<nat n)

data NC (k : LG) (n : ℕ) : Set where
  nb : ∀ {rp} → k ≈ rp → (s : rp < natL n) → NC k n
  na : NC k n

natCmp : ∀ k n → NC k n
natCmp zero zero = na
natCmp zero (suc n) = nb z≈ (zero<nat n)
natCmp (suc a) zero = na
natCmp (suc a) (suc n) with natCmp a n
... | nb d s = nb (s≈ d) (sucP n s)
... | na = na
natCmp (lim f) n = na
natCmp (lc c t g) n = na

admN : ∀ {E n rp} (s : rp < natL n) → Adm E s
admN {n = suc n} zero = tt
admN {n = suc n} (suc s) = admN s

mkOut : ∀ {t ρ} → Maybe ℕ → (c₀ : D) → (ℕ → LG) → (ℕ → (η : D) → c₀ ⊑ᴰ η → LG) → O t ρ → ((η : D) → c₀ ⊑ᴰ η → O t ρ) → O t ρ
mkOut nothing  c₀ r rg o₀ o = oŝ c₀ o₀ o
mkOut (just m) c₀ r rg o₀ o = oĉ c₀ (r m) (rg m) o₀ o

module Fold (c : LG) (wf : WFˢ c) (sf : c ≈ c) (tc : Tc c) where
  record Evd (E : Ents) (f : Frm) : Set where
    constructor evd
    field
      {c₃} : D
      {t₃} : LG
      {g₃} : (η : D) → c₃ ⊑ᴰ η → LG
      Pf   : Cp (lc c₃ t₃ g₃) c
      adf  : AdmC (tab E) Pf
      lkf  : lc c₃ t₃ g₃ ≈ κ f
      blf  : Bel′ E (fc f) (ft f) (fg f) (fe f)

  record Ab (ρ : Fl) (f : Frm) : Set where
    constructor ab
    field
      {c₄} : D
      {t₄} : LG
      {g₄} : (η : D) → c₄ ⊑ᴰ η → LG
      {e₄} : c₄ ⊑ᴰ fη f
      mem₄ : Mem ρ (frm c₄ t₄ g₄ (fη f) e₄)
      lk₄  : Lk (κ f) (lc c₄ t₄ g₄)
      eq₄  : e₄ ≡ lkG lk₄ (fe f)

  record Fs (E : Ents) (ρ : Fl) (f : Frm) : Set where
    constructor fs
    field
      ev  : Maybe (Evd E f)
      abm : Maybe (Ab ρ f)
  open Fs public

  St : Ents → Fl → Fl → Set
  St E ρ π = ∀ {f} → Mem π f → Fs E ρ f

  mapFs : ∀ {E ρ ρ′ f} → Wk ρ ρ′ → Fs E ρ f → Fs E ρ′ f
  mapFs w (fs e nothing) = fs e nothing
  mapFs w (fs e (just (ab m k q))) = fs e (just (ab (w m) k q))

  stξ : ∀ {E ρ π} ξ → St E ρ π → St E (ξ ∪ ρ) (ξ ∪ π)
  stξ ξ st (ml m) = fs nothing (just (ab (ml m) (inj₂ refl) refl))
  stξ ξ st (mr m) = mapFs mr (st m)

  stDup : ∀ {E ρ π} → St E ρ π → St E ρ (π ∪ π)
  stDup st (ml m) = st m
  stDup st (mr m) = st m

  stSelf : ∀ {E ρ π} → St E ρ π → St E π (π ∪ π)
  stSelf st (ml m) = fs (ev (st m)) (just (ab m (inj₂ refl) refl))
  stSelf st (mr m) = fs (ev (st m)) (just (ab m (inj₂ refl) refl))
```

## §6 从帧到输出, 从帧到表

```agda
  module Vis {E : Ents} {ρ π : Fl} (st : St E ρ π) where
    toOut : ∀ {a b} (r : a < b) → Adm (cov π) r → Maybe (Adm (cov ρ) r)
    toOut zero _ = just tt
    toOut (suc r) a = toOut r a
    toOut (lim n r) a = toOut r a
    toOut (fst r) a = toOut r a
    toOut (bra η e r) ((c₁ , t₁ , g₁ , e₁ , m , k , eq) , a) with abm (st m) | toOut r a
    ... | just (ab {c₄} {t₄} {g₄} {e₄} mem lk q) | just a′ = just ((c₄ , t₄ , g₄ , e₄ , mem , lkC k lk , trans q (trans (cong (lkG lk) eq) (lkG-∘ k lk e))) , a′)
    ... | _ | _ = nothing

    toOutC : ∀ {a b} (r : Cp a b) → AdmC (cov π) r → Maybe (AdmC (cov ρ) r)
    toOutC self _ = just tt
    toOutC (suc r) a = toOutC r a
    toOutC (lim n r) a = toOutC r a
    toOutC (fst r) a = toOutC r a
    toOutC (bra η e r) ((c₁ , t₁ , g₁ , e₁ , m , k , eq) , a) with abm (st m) | toOutC r a
    ... | just (ab {c₄} {t₄} {g₄} {e₄} mem lk q) | just a′ = just ((c₄ , t₄ , g₄ , e₄ , mem , lkC k lk , trans q (trans (cong (lkG lk) eq) (lkG-∘ k lk e))) , a′)
    ... | _ | _ = nothing

    belOf : ∀ {c t g c₁ t₁ g₁ η} {e : c ⊑ᴰ η} {e₁ : c₁ ⊑ᴰ η} (k : Lk (lc c t g) (lc c₁ t₁ g₁)) → e₁ ≡ lkG k e → Evd E (frm c₁ t₁ g₁ η e₁) → Bel (tab E) c t g e
    belOf {e = e} (inj₁ d) refl (evd _ _ _ (u , a , o , q)) =
      u , at-resp {E} (≈-sym d) a , ≈-trans d o , subst (λ z → z <ᵉ uF u) (sym (oc-tr d o e)) q
    belOf (inj₂ refl) refl (evd _ _ _ b) = b

    toTab : ∀ {a b} (r : a < b) → Adm (cov π) r → Maybe (Adm (tab E) r)
    toTab zero _ = just tt
    toTab (suc r) a = toTab r a
    toTab (lim n r) a = toTab r a
    toTab (fst r) a = toTab r a
    toTab (bra η e r) ((c₁ , t₁ , g₁ , e₁ , m , k , eq) , a) with ev (st m) | toTab r a
    ... | just d | just a′ = just (belOf k eq d , a′)
    ... | _ | _ = nothing

    toTabC : ∀ {a b} (r : Cp a b) → AdmC (cov π) r → Maybe (AdmC (tab E) r)
    toTabC self _ = just tt
    toTabC (suc r) a = toTabC r a
    toTabC (lim n r) a = toTabC r a
    toTabC (fst r) a = toTabC r a
    toTabC (bra η e r) ((c₁ , t₁ , g₁ , e₁ , m , k , eq) , a) with ev (st m) | toTabC r a
    ... | just d | just a′ = just (belOf k eq d , a′)
    ... | _ | _ = nothing
```

## §7 节点对目标

`cmpN`: 与 `kdec` 同一个骨架. 同一个节点上的两个分支才读表 (`bd`). 输出 `cb`: 节点在目标之下, 路径搬到目标里, 帧搬到输出. `cu`: 目标不在节点之上, 要上升. `cj`: 证据缺失. **`bra` 对 `bra` 且帧没有证据时给 `cj`: 这不是判定, 没有比较任何东西.**

```agda
    data CN (k t : LG) : Set where
      cb : ∀ {rp} → k ≈ rp → (s : rp < t) → Adm (cov ρ) s → CN k t
      cu : (t ≈ k ⊎ Below t k) → CN k t
      cj : CN k t

    shl : ∀ {k k′ t} → k ≈ k′ → CN k′ t → CN k t
    shl e (cb d s a) = cb (≈-trans e d) s a
    shl e (cu (inj₁ d)) = cu (inj₁ (≈-trans d (≈-sym e)))
    shl e (cu (inj₂ (pre d s))) with ≈-move (≈-sym e) s
    ... | viaᴸ d′ s′ _ = cu (inj₂ (pre (≈-trans d d′) s′))
    shl e cj = cj

    shr : ∀ {k t t′} → t ≈ t′ → CN k t′ → CN k t
    shr e (cb d s a) with ≈-move (≈-sym e) s
    ... | viaᴸ d′ s′ u = cb (≈-trans d d′) s′ (u (cov ρ) a)
    shr e (cu (inj₁ d)) = cu (inj₁ (≈-trans e d))
    shr e (cu (inj₂ (pre d s))) = cu (inj₂ (pre (≈-trans e d) s))
    shr e cj = cj

    cmpN : ∀ {c′} → WFˢ c′ → c′ ≈ c′ → ∀ {k t} (r : k < c′) (q : t < c′) → Adm (cov π) r → Adm (tab E) q → CN k t
    cmpN w (s≈ e) zero zero _ _ = cu (inj₁ e)
    cmpN w (s≈ e) zero (suc q) _ _ = cu (inj₂ (pre (selfAt e q) q))
    cmpN w (s≈ e) (suc r) zero cv _ with toOut r cv
    ... | just a = cb (selfAt e r) r a
    ... | nothing = cj
    cmpN w (s≈ e) (suc r) (suc q) cv aq = cmpN w e r q cv aq
    cmpN (st′ , w) (l≈ e) (lim n r) (lim m q) cv aq with <ᴺ-dec n m
    ... | injᵃ n<m with ⊴p (stepsˢ st′ n<m) r
    ...   | viaᴸ d r′ u = shl d (cmpN (w m) (e m) r′ q (u (cov π) cv) aq)
    cmpN (st′ , w) (l≈ e) (lim n r) (lim m q) cv aq | injᵇ m<n with ⊴p (stepsˢ st′ m<n) q
    ...   | viaᴸ d q′ u = shr d (cmpN (w n) (e n) r q′ cv (u (tab E) aq))
    cmpN (st′ , w) (l≈ e) (lim n r) (lim _ q) cv aq | injᶜ refl = cmpN (w n) (e n) r q cv aq
    cmpN (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (fst r) (fst q) cv aq = cmpN wt se r q cv aq
    cmpN (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (fst r) (bra y e q) cv (_ , aq) with ⊴p (tg y e) r
    ... | viaᴸ d′ r′ u = shl d′ (cmpN (wg y e) (shˡ y e) r′ q (u (cov π) cv) aq)
    cmpN (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (bra x e₁ r) (fst q) (_ , cv) aq with ⊴p (tg x e₁) q
    ... | viaᴸ d′ q′ u = shr d′ (cmpN (wg x e₁) (shˡ x e₁) r q′ cv (u (tab E) aq))
    cmpN (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (bra x e₁ r) (bra y e₂ q) ((c₁ , t₁ , g₁ , e₃ , m , k , eq) , cv) ((ℓ , b₁ , o₂ , ly) , aq) with ev (st m)
    ... | nothing = cj
    ... | just evi with belOf k eq evi
    ...   | ℓ′ , b₂ , o₁ , lx with at-uq {E} (o≈ d se sh sh⁻ shˡ shʳ) b₂ b₁
    ...     | refl with cmpBr {u = ℓ} dir o₁ o₂ e₁ e₂ lx ly
    ...       | inj₁ s with ⊴p s r
    ...         | viaᴸ d′ r′ u = shl d′ (cmpN (wg y e₂) (shˡ y e₂) r′ q (u (cov π) cv) aq)
    cmpN (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (bra x e₁ r) (bra y e₂ q) ((c₁ , t₁ , g₁ , e₃ , m , k , eq) , cv) ((ℓ , b₁ , o₂ , ly) , aq) | just evi | ℓ , b₂ , o₁ , lx | refl | inj₂ s with ⊴p s q
    ...         | viaᴸ d′ q′ u = shr d′ (cmpN (wg x e₁) (shˡ x e₁) r q′ cv (u (tab E) aq))
```

**闭包对目标.** `kb`: 目标在闭包之下, 所以闭包要立刻计值. `ka`: 闭包 (模 $\approx$) 在目标里, 所以保留.

```agda
    data CK (c₂ : D) (t₂ : LG) (g₂ : (η : D) → c₂ ⊑ᴰ η → LG) (t : LG) : Set where
      kb : CK c₂ t₂ g₂ t
      ka : ∀ {c′ t′ g′} (Q : Cp (lc c′ t′ g′) t) → lc c₂ t₂ g₂ ≈ lc c′ t′ g′ → AdmC (cov ρ) Q → CK c₂ t₂ g₂ t
      kj : CK c₂ t₂ g₂ t

    skl : ∀ {c₂ t₂ g₂ c₃ t₃ g₃ t} → lc c₂ t₂ g₂ ≈ lc c₃ t₃ g₃ → CK c₃ t₃ g₃ t → CK c₂ t₂ g₂ t
    skl e kb = kb
    skl e (ka Q d a) = ka Q (≈-trans e d) a
    skl e kj = kj

    skr : ∀ {c₂ t₂ g₂ t t′} → t ≈ t′ → CK c₂ t₂ g₂ t′ → CK c₂ t₂ g₂ t
    skr e kb = kb
    skr e (ka Q d a) with ≈-moveᴷ (≈-sym e) Q
    ... | viaᴷ d′ Q′ u = ka Q′ (≈-trans d d′) (u (cov ρ) a)
    skr e kj = kj

    cmpK : ∀ {c′} → WFˢ c′ → c′ ≈ c′ → ∀ {c₂ t₂ g₂ t} (P : Cp (lc c₂ t₂ g₂) c′) (q : t < c′) → AdmC (cov π) P → Adm (tab E) q → CK c₂ t₂ g₂ t
    cmpK w sf′ self q cv aq = kb
    cmpK w (s≈ e) (suc P) zero cv _ with toOutC P cv
    ... | just a = ka P (selfC e P) a
    ... | nothing = kj
    cmpK w (s≈ e) (suc P) (suc q) cv aq = cmpK w e P q cv aq
    cmpK (st′ , w) (l≈ e) (lim n P) (lim m q) cv aq with <ᴺ-dec n m
    ... | injᵃ n<m with ⊴K (stepsˢ st′ n<m) P
    ...   | viaᴷ d P′ u = skl d (cmpK (w m) (e m) P′ q (u (cov π) cv) aq)
    cmpK (st′ , w) (l≈ e) (lim n P) (lim m q) cv aq | injᵇ m<n with ⊴p (stepsˢ st′ m<n) q
    ...   | viaᴸ d q′ u = skr d (cmpK (w n) (e n) P q′ cv (u (tab E) aq))
    cmpK (st′ , w) (l≈ e) (lim n P) (lim _ q) cv aq | injᶜ refl = cmpK (w n) (e n) P q cv aq
    cmpK (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (fst P) (fst q) cv aq = cmpK wt se P q cv aq
    cmpK (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (fst P) (bra y e q) cv (_ , aq) with ⊴K (tg y e) P
    ... | viaᴷ d′ P′ u = skl d′ (cmpK (wg y e) (shˡ y e) P′ q (u (cov π) cv) aq)
    cmpK (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (bra x e₁ P) (fst q) (_ , cv) aq with ⊴p (tg x e₁) q
    ... | viaᴸ d′ q′ u = skr d′ (cmpK (wg x e₁) (shˡ x e₁) P q′ cv (u (tab E) aq))
    cmpK (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (bra x e₁ P) (bra y e₂ q) ((c₁ , t₁ , g₁ , e₃ , m , k , eq) , cv) ((ℓ , b₁ , o₂ , ly) , aq) with ev (st m)
    ... | nothing = kj
    ... | just evi with belOf k eq evi
    ...   | ℓ′ , b₂ , o₁ , lx with at-uq {E} (o≈ d se sh sh⁻ shˡ shʳ) b₂ b₁
    ...     | refl with cmpBr {u = ℓ} dir o₁ o₂ e₁ e₂ lx ly
    ...       | inj₁ s with ⊴K s P
    ...         | viaᴷ d′ P′ u = skl d′ (cmpK (wg y e₂) (shˡ y e₂) P′ q (u (cov π) cv) aq)
    cmpK (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (bra x e₁ P) (bra y e₂ q) ((c₁ , t₁ , g₁ , e₃ , m , k , eq) , cv) ((ℓ , b₁ , o₂ , ly) , aq) | just evi | ℓ , b₂ , o₁ , lx | refl | inj₂ s with ⊴p s q
    ...         | viaᴸ d′ q′ u = skr d′ (cmpK (wg x e₁) (shˡ x e₁) P q′ cv (u (tab E) aq))
```

## §8 闭包的界: 只看同键的帧与目标的分支

`Sel`: 与 [LvKeyTree](LvKeyTree.lagda.md) 的 `Sel` 同形. `Sl`: 什么也没有挑出 (`emp`), 或者挑出了 (`sel`): 表项 $u$, 节点到 $u$ 的 `≈`, 表项纤维里的一个证据. 地板 `φ` 的项是帧, 所以 `lft` 由 `Ev` 直接读出 `Bel′` 要的东西, 不要比较两个证据.

```agda
  module Sel {c₂ t₂ g₂} (P : Cp (lc c₂ t₂ g₂) c) (E : Ents) (ap : AdmC (tab E) P) where
    kself : lc c₂ t₂ g₂ ≈ lc c₂ t₂ g₂
    kself = selfC sf P

    w₂ : (X : D) → c₂ ⊑ᴰ X → Up
    w₂ X F = mkU c₂ t₂ g₂ X F

    E′ : (X : D) → c₂ ⊑ᴰ X → Ents
    E′ X F = E ▸ w₂ X F

    data Sl (φ : Flr) : Set where
      emp : (∀ w → Ev w φ) → Sl φ
      sel : ∀ u → at E (lc c₂ t₂ g₂) u → lc c₂ t₂ g₂ ≈ key u → ∀ {K₀} (e₀ : uc u ⊑ᴰ K₀) → e₀ <ᵉ uF u → Ev u φ → Sl φ

    record S (G : Ents → Set) : Set where
      constructor mkS
      field
        φ   : Flr
        wit : Sl φ
        lft : ∀ X F → Ev (w₂ X F) φ → G (E′ X F)
    open S public

    triv : ∀ {G} → (∀ X F → G (E′ X F)) → S G
    triv f = mkS fz (emp (λ _ → tt)) (λ X F _ → f X F)

    mapS : ∀ {A B : Ents → Set} → (∀ F → A F → B F) → S A → S B
    mapS f s = mkS (φ s) (wit s) (λ X F x → f _ (lft s X F x))

    mg : ∀ {a b} → Sl a → Sl b → Sl (a ⊔ b)
    mg (emp f) (emp h) = emp (λ w → f w , h w)
    mg (emp f) (sel u a o e q y) = sel u a o e q (f u , y)
    mg (sel u a o e q x) (emp h) = sel u a o e q (x , h u)
    mg (sel u a o e q x) (sel u′ a′ o′ e′ q′ y) with at-uq {E} kself a a′
    ... | refl = sel u a o e q (x , y)

    _⋈_ : ∀ {A B : Ents → Set} → S A → S B → S (λ F → A F × B F)
    s ⋈ s′ = mkS (φ s ⊔ φ s′) (mg (wit s) (wit s′)) (λ X F x → lft s X F (proj₁ x) , lft s′ X F (proj₂ x))

    -- 节点 ν 与 K: 是同一个键就进界. 地板的项是帧本身.
    pick : ∀ {c₅ t₅ g₅} (Q : Cp (lc c₅ t₅ g₅) c) → AdmC (tab E) Q → ∀ K (eK : c₅ ⊑ᴰ K) → Bel′ E c₅ t₅ g₅ eK → S (λ F → Bel′ F c₅ t₅ g₅ eK)
    pick {c₅} {t₅} {g₅} Q aq K eK (u , a , o , q) with kdec wf sf Q P E aq ap
    ... | inj₁ e = mkS (fk (frm c₅ t₅ g₅ K eK))
                       (sel u (at-resp {E} e a) (≈-trans (≈-sym e) o) (conv (oc≅ o) eK) q (o , q))
                       (λ Y F x → w₂ Y F , inj₁ (e , refl) , proj₁ x , proj₂ x)
    ... | inj₂ n = mkS fz (emp (λ _ → tt)) (λ Y F _ → u , inj₂ (n , a) , o , q)

    walk : ∀ {a x} (Q : Cp a c) → AdmC (tab E) Q → (r : Cp x a) → AdmC (tab E) r → S (λ F → AdmC (tab F) r)
    walk Q aq self _ = triv (λ _ _ → tt)
    walk Q aq (suc r) ad = walk (Q ⊙ suc self) (adm⊙ {tab E} Q aq tt) r ad
    walk Q aq (lim n r) ad = walk (Q ⊙ lim n self) (adm⊙ {tab E} Q aq tt) r ad
    walk Q aq (fst r) ad = walk (Q ⊙ fst self) (adm⊙ {tab E} Q aq tt) r ad
    walk Q aq (bra η e r) (u , ad) =
      pick Q aq η e u ⋈ walk (Q ⊙ bra η e self) (adm⊙ {tab E} Q aq (u , tt)) r ad

    walkA : ∀ {a x} (Q : Cp a c) → AdmC (tab E) Q → (r : x < a) → Adm (tab E) r → S (λ F → Adm (tab F) r)
    walkA Q aq zero _ = triv (λ _ _ → tt)
    walkA Q aq (suc r) ad = walkA (Q ⊙ suc self) (adm⊙ {tab E} Q aq tt) r ad
    walkA Q aq (lim n r) ad = walkA (Q ⊙ lim n self) (adm⊙ {tab E} Q aq tt) r ad
    walkA Q aq (fst r) ad = walkA (Q ⊙ fst self) (adm⊙ {tab E} Q aq tt) r ad
    walkA Q aq (bra η e r) (u , ad) =
      pick Q aq η e u ⋈ walkA (Q ⊙ bra η e self) (adm⊙ {tab E} Q aq (u , tt)) r ad

    selSt : ∀ {ρ} π → St E ρ π → S (λ F → St F ρ π)
    selSt tz st = triv (λ X F → λ ())
    selSt (tk f) st with st hr
    ... | fs nothing a = triv (λ X F → λ { hr → fs nothing a })
    ... | fs (just (evd Pf adf lkf (u , b , o , q))) a =
      mapS (λ F x → λ { hr → fs (just (evd Pf (proj₁ x) lkf (bel-to F (proj₂ x)))) a })
           (walk self tt Pf adf ⋈ pick Pf adf (fη f) eK (u , at-resp {E} (≈-sym lkf) b , ≈-trans lkf o , q′))
      where
      eK = conv⁻ (oc≅ lkf) (fe f)
      q′ : conv (oc≅ (≈-trans lkf o)) eK <ᵉ uF u
      q′ = subst (λ z → z <ᵉ uF u) (sym (trans (oc-tr lkf o eK) (cong (conv (oc≅ o)) (sec (oc≅ lkf) (fe f))))) q
      bel-to : ∀ F → Bel′ F _ _ _ eK → Bel′ F (fc f) (ft f) (fg f) (fe f)
      bel-to F x = subst (λ z → Bel′ F (fc f) (ft f) (fg f) z) (sec (oc≅ lkf) (fe f)) (Bel-resp {tab F} lkf x)
    selSt (a ∪ b) st =
      mapS (λ F x → λ { (ml m) → proj₁ x m ; (mr m) → proj₂ x m })
           (selSt a (λ m → st (ml m)) ⋈ selSt b (λ m → st (mr m)))
```

## §5′ 地板下降时的状态

`lowerSt`: 外层状态在 $\pi$ 上, `Cov π′ π` 说 $\pi'$ 的帧被 $\pi$ 支配. 表里的证据随分支值下降 (字面子项, 所以 $a<\ell$ 还是字面的). 输出里的帧也下降: 输出的地板是算出来的 ($\sigma$), 不是 $\rho$ 本身, 所以闭包只看到紧的帧.

```agda
  sbL : ∀ {x u v} → Lk u v → x ≈ v → x ≈ u
  sbL (inj₁ d′) d = ≈-trans d (≈-sym d′)
  sbL (inj₂ refl) d = d

  atL : ∀ {E u v ℓ} → Lk u v → at E v ℓ → at E u ℓ
  atL {E} (inj₁ d′) b = at-resp {E} (≈-sym d′) b
  atL (inj₂ refl) b = b

  fsLow : ∀ {E ρ f f′} (lk : Lk (κ f) (κ f′)) → lkG lk (fe f) ⊲ fe f′ → Fs E ρ f′ → Σ Fl λ σ → Fs E σ f × Cov σ ρ
  fsLow {E} {ρ} {f} {f′} lk lt (fs e a) = go₂ a
    where
    me : Maybe (Evd E f′) → Maybe (Evd E f)
    me nothing = nothing
    me (just (evd Pf adf lkf (u , b , o , q))) =
      just (evd Pf adf (sbL lk lkf)
        (u , atL {E} lk b , lkO lk o ,
         subst (λ z → z <ᵉ uF u) (sym (lkO-conv lk o (fe f)))
           (⊲-conv (oc≅ o) (lkG lk (fe f)) (fe f′) lt (uF u) q)))
    go₂ : Maybe (Ab ρ f′) → Σ Fl λ σ → Fs E σ f × Cov σ ρ
    go₂ nothing = tz , fs (me e) nothing , (λ ())
    go₂ (just (ab {c₄} {t₄} {g₄} {e₄} mem lk₄ eq₄)) =
      tk (frm c₄ t₄ g₄ (fη f) (lkG (lkC lk lk₄) (fe f))) ,
      fs (me e) (just (ab {c₄ = c₄} {t₄ = t₄} {g₄ = g₄} {e₄ = lkG (lkC lk lk₄) (fe f)} hr (lkC lk lk₄) refl)) ,
      (λ { hr → frm c₄ t₄ g₄ (fη f′) e₄ , mem , inj₂ refl ,
          subst (λ z → lkG (lkC lk lk₄) (fe f) ⊲ z) (sym eq₄)
            (subst (λ z → z ⊲ lkG lk₄ (fe f′)) (lkG-∘ lk lk₄ (fe f))
              (⊲-lk lk₄ (lkG lk (fe f)) (fe f′) lt)) })

  lowerSt : ∀ {E ρ π} (π′ : Fl) → Cov π′ π → St E ρ π → Σ Fl λ σ → St E σ π′ × Cov σ ρ
  lowerSt tz w st = tz , (λ ()) , (λ ())
  lowerSt (tk f) w st with w hr
  ... | f′ , m , lk , lt with fsLow lk lt (st m)
  ...   | σ , F , c = σ , (λ { hr → F }) , c
  lowerSt (a ∪ b) w st with lowerSt a (λ m → w (ml m)) st | lowerSt b (λ m → w (mr m)) st
  ... | σa , sa , ca | σb , sb , cb =
    σa ∪ σb , (λ { (ml m) → mapFs ml (sa m) ; (mr m) → mapFs mr (sb m) }) , (λ { (ml m) → ca m ; (mr m) → cb m })
```

## §5″ 链的地板: 只留层里有位置的帧

节点 $k$ 的链在 `O k` 里. 外层的帧 $f$ 进链, 只在 $f$ 的闭包在 $k$ 里有位置时才有意义: 否则 $k$ 里的节点与闭包都用不到它, 但它会经 `⊕` 的左边读进右边闭包的界. [ScafLadderQ](ScafLadderQ.lagda.md) 由类型做这件事: 高度 $n$ 的节点的输入只带 $<n$ 的高度 (`lo n ζ`). **这里没有高度: `keepP` 用表里的证据比较闭包的位置与节点的路径**, 与 `cmpK` 同一个骨架. 这是 "位置作键" 取代高度的地方. 没有证据的帧 (活的分支变量, 闭包保留在输出里) 总留下: 它的闭包在目标里, 目标不高于节点.

```agda
  keepP : ∀ {E c′} → WFˢ c′ → c′ ≈ c′ → ∀ {c₂ t₂ g₂ t} (P : Cp (lc c₂ t₂ g₂) c′) (q : t < c′) → AdmC (tab E) P → Adm (tab E) q → Bool
  keepP w sf′ self q cv aq = false
  keepP w (s≈ e) (suc P) zero cv _ = true
  keepP w (s≈ e) (suc P) (suc q) cv aq = keepP w e P q cv aq
  keepP {E = E} (st′ , w) (l≈ e) (lim n P) (lim m q) cv aq with <ᴺ-dec n m
  ... | injᵃ n<m with ⊴K (stepsˢ st′ n<m) P
  ...   | viaᴷ d P′ u = keepP (w m) (e m) P′ q (u (tab E) cv) aq
  keepP {E = E} (st′ , w) (l≈ e) (lim n P) (lim m q) cv aq | injᵇ m<n with ⊴p (stepsˢ st′ m<n) q
  ...   | viaᴸ d q′ u = keepP (w n) (e n) P q′ cv (u (tab E) aq)
  keepP (st′ , w) (l≈ e) (lim n P) (lim _ q) cv aq | injᶜ refl = keepP (w n) (e n) P q cv aq
  keepP (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (fst P) (fst q) cv aq = keepP wt se P q cv aq
  keepP {E = E} (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (fst P) (bra y e q) cv (_ , aq) with ⊴K (tg y e) P
  ... | viaᴷ d′ P′ u = keepP (wg y e) (shˡ y e) P′ q (u (tab E) cv) aq
  keepP {E = E} (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (bra x e₁ P) (fst q) (_ , cv) aq with ⊴p (tg x e₁) q
  ... | viaᴸ d′ q′ u = keepP (wg x e₁) (shˡ x e₁) P q′ cv (u (tab E) aq)
  keepP {E = E} (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (bra x e₁ P) (bra y e₂ q) ((ℓ′ , b₂ , o₁ , lx) , cv) ((ℓ , b₁ , o₂ , ly) , aq) with at-uq {E} (o≈ d se sh sh⁻ shˡ shʳ) b₂ b₁
  ... | refl with cmpBr {u = ℓ} dir o₁ o₂ e₁ e₂ lx ly
  ...   | inj₁ s with ⊴K s P
  ...     | viaᴷ d′ P′ u = keepP (wg y e₂) (shˡ y e₂) P′ q (u (tab E) cv) aq
  keepP {E = E} (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (bra x e₁ P) (bra y e₂ q) ((ℓ′ , b₂ , o₁ , lx) , cv) ((ℓ , b₁ , o₂ , ly) , aq) | refl | inj₂ s with ⊴p s q
  ...     | viaᴸ d′ q′ u = keepP (wg x e₁) (shˡ x e₁) P q′ cv (u (tab E) aq)

  record Tr {E : Ents} {ρ : Fl} (π : Fl) (st : St E ρ π) : Set where
    constructor mkTr
    field
      ξᵗ   : Fl
      wkᵗ  : Wk ξᵗ π
      bkᵗ  : ∀ {f} → Mem π f → Maybe (Mem ξᵗ f)
  open Tr public

  keepF : ∀ {E ρ f k} (s : Fs E ρ f) {r : k < c} → Adm (tab E) r → Bool
  keepF (fs nothing a) ar = true
  keepF (fs (just (evd Pf adf _ _)) a) {r} ar = keepP wf sf Pf r adf ar

  trim : ∀ {E ρ k} (π : Fl) (st : St E ρ π) {r : k < c} → Adm (tab E) r → Tr π st
  trim tz st ar = mkTr tz (λ ()) (λ ())
  trim (tk f) st {r} ar with keepF (st hr) {r} ar
  ... | true = mkTr (tk f) (λ m → m) just
  ... | false = mkTr tz (λ ()) (λ _ → nothing)
  trim (a ∪ b) st {r} ar with trim a (λ m → st (ml m)) {r} ar | trim b (λ m → st (mr m)) {r} ar
  ... | mkTr ξa wa ba | mkTr ξb wb bb =
    mkTr (ξa ∪ ξb) (λ { (ml m) → ml (wa m) ; (mr m) → mr (wb m) })
         (λ { (ml m) → mapM ml (ba m) ; (mr m) → mapM mr (bb m) })
    where
    mapM : ∀ {A B : Set} → (A → B) → Maybe A → Maybe B
    mapM g nothing = nothing
    mapM g (just x) = just (g x)

  stBody : ∀ {E ρ π} (ξ : Fl) → Wk ξ π → St E ρ π → St E ρ (ξ ∪ π)
  stBody ξ w st (ml m) = st (w m)
  stBody ξ w st (mr m) = st m

  stChain : ∀ {E ρ π} (ξ : Fl) → (∀ {f} → Mem π f → Maybe (Mem ξ f)) → Wk ξ π → St E ρ π → St E ξ (ξ ∪ π)
  stChain ξ bk w st (ml m) = fs (ev (st (w m))) (just (ab m (inj₂ refl) refl))
  stChain ξ bk w st {f} (mr m) with bk m
  ... | just m′ = fs (ev (st m)) (just (ab m′ (inj₂ refl) refl))
  ... | nothing = fs (ev (st m)) nothing
```

## §9 折叠

`ψ`: 对树结构递归. 与 [LvGuardTree](LvGuardTree.lagda.md) 的差别: `ocv` 一行 (状态下降, 输出的地板下降), `omk` 一行 (读 $x$, 不读 $z$, 与 `ψᵠ` 同), `riseΩ` 的目标规范化 (`nfT`). `Ω̇` 带 `Tc`. 目标 0 (`t0`) 没有路径.

```agda
  data Tg (E : Ents) : LG → Set where
    tn : ∀ n → Tg E (natL n)
    tp : ∀ {t} (q : t < c) → Adm (tab E) q → Tg E t

  tcT : ∀ {E t} → Tg E t → Tc t
  tcT (tn n) = Tc-id (natL n)
  tcT (tp q _) = Tc-at q tc

  gapT : ∀ {E t} → Tg E t → D → Maybe ℕ
  gapT (tn n) c′ with leq (suc n) (ix c′)
  ... | true = just (ix c′)
  ... | false = nothing
  gapT (tp q a) c′ = nothing

  tgSel : ∀ {c₂ t₂ g₂ t} (P : Cp (lc c₂ t₂ g₂) c) (E : Ents) (ap : AdmC (tab E) P) → Tg E t → Sel.S P E ap (λ F → Tg F t)
  tgSel P E ap (tn n) = Sel.triv P E ap (λ _ _ → tn n)
  tgSel P E ap (tp q aq) = Sel.mapS P E ap (λ F a → tp q a) (Sel.walkA P E ap self tt q aq)

  chainᵒ : ∀ {k π} → Tc k → (O k π → O k π) → ℕ → O k π
  chainᵒ {k} tk′ f zero    = owk (λ ()) (Ω̇ k tk′)
  chainᵒ tk′ f (suc n) = f (chainᵒ tk′ f n)

  dd : ∀ {π} → Wk (π ∪ π) π
  dd (ml m) = m
  dd (mr m) = m

  SSc : ∀ {t π ρ c₂ t₂ g₂} (E : Ents) → Tg E t → St E ρ π → (P : Cp (lc c₂ t₂ g₂) c) (ap : AdmC (tab E) P) →
        Sel.S P E ap (λ F → St F ρ π × (Tg F t × AdmC (tab F) P))
  SSc {π = π} E T st P ap = Sel._⋈_ P E ap (Sel.selSt P E ap π st) (Sel._⋈_ P E ap (tgSel P E ap T) (Sel.walk P E ap self tt P ap))

  ψ : ∀ {t π ρ} (E : Ents) → Tg E t → St E ρ π → O c π → O t ρ
  evalC : ∀ {t π ρ c₁ t₁ g₁ c₂ t₂ g₂} (E : Ents) → Tg E t → St E ρ π → (P : Cp (lc c₂ t₂ g₂) c) → Lk (lc c₂ t₂ g₂) (lc c₁ t₁ g₁) → AdmC (cov π) P →
          O c π → (∀ η e → O c (π ∪ tk (frm c₁ t₁ g₁ η e))) → O t ρ
  goC : ∀ {t π ρ c₁ t₁ g₁ c₂ t₂ g₂} (E : Ents) → Tg E t → St E ρ π → (P : Cp (lc c₂ t₂ g₂) c) → Lk (lc c₂ t₂ g₂) (lc c₁ t₁ g₁) → (ap : AdmC (tab E) P) →
        O c π → (∀ η e → O c (π ∪ tk (frm c₁ t₁ g₁ η e))) → (SS : Sel.S P E ap (λ F → St F ρ π × (Tg F t × AdmC (tab F) P))) → Sel.Sl P E ap (Sel.φ SS) → O t ρ
  riseΩ : ∀ {t π ρ k} (E : Ents) → Tg E t → St E ρ π → (r : k < c) → Adm (cov π) r → (∀ ξ → Us c r ξ → O c (ξ ∪ π)) → O t ρ

  ψ {t} E T st o0 = owk (λ ()) (Ω̇ t (tcT T))
  ψ E T st (os a) = ol (repᵒ (ψ E T st a))
  ψ E T st (ol F) = ol (λ n → ψ E T st (F n))
  ψ E T st (oŝ c₀ x g) = oŝ c₀ (ψ E T st x) (λ η e → ψ E T st (g η e))
  ψ E T st (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (ψ E T st o₀) (λ η e → ψ E T st (o η e))
  ψ E T st (owk w x) = ψ E T (λ m → st (w m)) x
  ψ E T st (ocv {π = π′} w x) with lowerSt π′ w st
  ... | σ , st′ , cv₁ = ocv cv₁ (ψ E T st′ x)
  ψ E T st (omk R lk ad z x) = ψ E T st x
  ψ E (tn n) st (oΩ {k = k} r cv h) with natCmp k n
  ... | nb d s = oΩ s (admN s) (λ ξ y → ψ E (tn n) (stξ ξ st) (h ξ (intoU r (tr⁻O d (outU s y)))))
  ... | na = riseΩ E (tn n) st r cv h
  ψ E (tp q aq) st (oΩ r cv h) with Vis.cmpN st wf sf r q cv aq
  ... | Vis.cb d s a = oΩ s a (λ ξ y → ψ E (tp q aq) (stξ ξ st) (h ξ (intoU r (tr⁻O d (outU s y)))))
  ... | Vis.cu _ = riseΩ E (tp q aq) st r cv h
  ... | Vis.cj = o0
  ψ E (tn n) st (ocl P k cv x g) = evalC E (tn n) st P k cv x g
  ψ {π = π} {ρ = ρ} E (tp q aq) st (ocl {c₁ = c₁} {t₁} {g₁} P k cv x g) with Vis.cmpK st wf sf P q cv aq
  ... | Vis.kb = evalC E (tp q aq) st P k cv x g
  ... | Vis.kj = o0
  ... | Vis.ka {c′} {t′} {g′} Q d a =
    ocl Q (inj₂ refl) a (ψ E (tp q aq) st x)
      (λ η e′ → ψ E (tp q aq) (st″ η e′) (g η (eg e′)))
    where
    lks₁ : lc c₁ t₁ g₁ ≈ lc c′ t′ g′
    lks₁ = ≈-trans (≈-sym (lk→≈ (selfC sf P) k)) d
    eg : ∀ {η} → c′ ⊑ᴰ η → c₁ ⊑ᴰ η
    eg e′ = conv (oc≅ (≈-sym lks₁)) e′
    st″ : ∀ η e′ → St E (ρ ∪ tk (frm c′ t′ g′ η e′)) (π ∪ tk (frm c₁ t₁ g₁ η (eg e′)))
    st″ η e′ (ml m) = mapFs ml (st m)
    st″ η e′ (mr hr) = fs nothing (just (ab {c₄ = c′} {t₄ = t′} {g₄ = g′} {e₄ = e′} (mr hr) (inj₁ lks₁) (sym (oc-sym-sec lks₁ e′))))

  riseΩ {π = π} E T st r cv h with Vis.toTab st r cv
  ... | nothing = o0
  ... | just a with nfT c tc r | trim π st {r} a
  ...   | nft d r′ tb | mkTr ξ w bk = ol (λ n → ψ E T (stBody ξ w st) (h ξ (intoU r (chainᵒ (Tc-at r tc) (λ z → trL⁻ d (ψ E (tp r′ (tb E a)) (stChain ξ bk w st) (h ξ (intoU r z)))) n))))

  evalC E T st P k cv x g with Vis.toTabC st P cv
  ... | nothing = o0
  ... | just ap = goC E T st P k ap x g (SSc E T st P ap) (Sel.wit (SSc E T st P ap))

  goC {t} {π} {ρ} {c₁} {t₁} {g₁} {c₂} {t₂} {g₂} E T st P k ap x g SS w = go w
    where
    module M = Sel P E ap
    lk₂ : lc c₂ t₂ g₂ ≈ lc c₁ t₁ g₁
    lk₂ = lk→≈ M.kself k
    guardC : ∀ {η} → c₂ ⊑ᴰ η → c₁ ⊑ᴰ η
    guardC d = conv (oc≅ lk₂) d
    bodyG : ∀ {t′} η (d : c₂ ⊑ᴰ η) Y (F : c₂ ⊑ᴰ Y) → Ev (M.w₂ Y F) (M.φ SS) → d <ᵉ F → Tg (M.E′ Y F) t′ → O t′ ρ
    bodyG η d Y F ex q T′ = ψ (M.E′ Y F) T′ stn (g η (guardC d))
      where
      L = M.lft SS Y F ex
      stn : St (M.E′ Y F) ρ (π ∪ tk (frm c₁ t₁ g₁ η (guardC d)))
      stn (ml m) = proj₁ L m
      stn (mr hr) = fs (just (evd P (proj₂ (proj₂ L)) lk₂ (M.w₂ Y F , inj₁ (≈-sym lk₂ , refl) , ≈-sym lk₂ , subst (λ z → z <ᵉ F) (sym (oc-sym-ret lk₂ d)) q))) nothing
    body : ∀ η (d : c₂ ⊑ᴰ η) Y (F : c₂ ⊑ᴰ Y) → Ev (M.w₂ Y F) (M.φ SS) → d <ᵉ F → O t ρ
    body η d Y F ex q = bodyG η d Y F ex q (proj₁ (proj₂ (M.lft SS Y F ex)))
    go : M.Sl (M.φ SS) → O t ρ
    go (M.emp f) = mkOut (gapT T c₂) c₂
         (λ m → rb (ψ E (tn m) st x))
         (λ m η d → rb (bodyG η d (sD η) (sF d) (f _) (self<ᵉ d) (tn m)))
         (ψ E T st x)
         (λ η d → body η d (sD η) (sF d) (f _) (self<ᵉ d))
    go (M.sel u a o₃ e₀ q₀ y) = mkOut (gapT T (Bd B)) (Bd B)
         (λ m → rb (ψ E (tn m) st x))
         (λ m η d → rb (bodyG η (dG d) (upX B d) (FG d) (exG d) (qG d) (tn m)))
         (ψ E T st x)
         (λ η d → body η (dG d) (upX B d) (FG d) (exG d) (qG d))
      where
      B : Tp (uF u) (toFᵉ (M.φ SS) y)
      B = bound (uF u) (toFᵉ (M.φ SS) y) {e₀ = e₀} q₀
      dG : ∀ {η} → Bd B ⊑ᴰ η → c₂ ⊑ᴰ η
      dG d = conv⁻ (oc≅ o₃) (gr B d)
      FG : ∀ {η} (d : Bd B ⊑ᴰ η) → c₂ ⊑ᴰ upX B d
      FG d = conv⁻ (oc≅ o₃) (upF B d)
      exG : ∀ {η} (d : Bd B ⊑ᴰ η) → Ev (M.w₂ (upX B d) (FG d)) (M.φ SS)
      exG d = evBack o₃ (upF B d) (M.φ SS) y (upEv B d)
      qG : ∀ {η} (d : Bd B ⊑ᴰ η) → dG d <ᵉ FG d
      qG d = <-conv⁻ (oc≅ o₃) _ _ (up< B d)

-- ψ_n(Ω_L): 任何带证书的层号, 任何自然数目标. 一个定义, 没有标签, 没有对阶段或 n 的归纳.
Tn : (L : LG) → Cfˢ L → Tc L → (n : ℕ) → O (natL n) tz
Tn L (w , s) tc n = Fold.ψ L w s tc ∅ (Fold.tn n) (λ ()) (Ω̇ L tc)

T⁰ : ℕ → Set
T⁰ n = O (natL n) tz
```
