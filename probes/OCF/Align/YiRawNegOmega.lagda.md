# YiRawNeg 第 4 项：公共上界含 Ω 结点时，哪些位置对可以比较

**判决：编译定理 (否定三条，正面一条)。没有折叠，没有值。** 公共上界取 `tw 2` (不是 `Plain` 的)：`Compare` 的同形命题不可满足 (`no-compare-tw2`，两支上的层号在位置关系下不可比)；
把三路放宽成 "判定结点层是否在目标层的位置上" 推出 LPO (`dec-at→lpo`)；`RawFold` 的保留律与折叠律原样搬到 `tw 2` 推出 WLPO (`keep-fold→wlpo`)。
正面：两个位置在主干上，或所在两支的坐标有字面的第一位置路径 (含同一支) 时，三路成立 (`compare-link`)。
不否定第 3 步 (`tw 3` 的各支只用 `Plain` 的公共上界 `read0 η`)；否定的是把律的定义域取成 `tw 2` 的一切位置对。接口 [YiRawIf](YiRawIf.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRawNegOmega where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
open import OCF.Align.YiLvIf
open import OCF.Align.YiIrrNegWide using (Found; seen; seen-found)
open import OCF.Align.YiLvNegCompare using (At)
open import OCF.Align.YiLvNegCert using (ω′)
open import OCF.Align.YiLvNegCanon using (ccompare)
open import OCF.Align.YiLvNegKeep
  using (LPO; Locate; coordᴸ; coordᴸ-guard; levelᴸ; flag-one; found→one; below-one; low-zero)
open import OCF.Align.YiRawIf
```

## 1 `tw 2` 的位置

主干上有两个位置 (结点自己的层号，第一支 `suc zero` 的根)，层号都是 0。其余位置在某一支里：坐标 `η`，相关的守卫 `e`，`read0 η` 里的位置 `r`。

```agda
K₂ω : LF
K₂ω = tw 2

root₂ first₂ : Pre K₂ω
root₂ = inj₁ (inj₁ tt)
first₂ = inj₂ (inj₁ (inj₁ tt))

br : (η : R) (e : Gd zero raw1 η) → Pre (read0 η) → Pre K₂ω
br η e r = inj₂ (inj₂ (η , e , r))

br-level : ∀ η e r → lev K₂ω (br η e r) ≡ lev (read0 η) r
br-level η e r = refl
```

## 2 同形的 `Compare` 不可满足

第 `suc ω′` 支的根，层号是 `lim (λ _ → suc zero)`；第 3 支里层号为 `suc zero` 的位置。两个守卫都是闭的相关证明。
这两个层号之间三路的三个构造子都没有居留：前者的位置上只有层号 0，后者的位置上也只有层号 0，两者不相等。

```agda
η₁ η₂ : R
η₁ = G.suc ω′
η₂ = G.suc (G.suc one)

e₁ : Gd zero raw1 η₁
e₁ = inj₂ (inj₂ (zero , inj₁ refl)) , ((λ _ → inj₁ refl) , (λ _ → tt)) , raw0-Nested η₁

e₂ : Gd zero raw1 η₂
e₂ = inj₂ (inj₂ (inj₁ refl)) , tt , raw0-Nested η₂

q₁ q₂ : Pre K₂ω
q₁ = br η₁ e₁ (inj₁ tt)
q₂ = br η₂ e₂ (inj₂ (inj₁ tt))

q₁-level : lev K₂ω q₁ ≡ lim (λ _ → suc zero)
q₁-level = refl

q₂-level : lev K₂ω q₂ ≡ suc zero
q₂-level = refl

no-tri : Tri (lim (λ _ → suc zero)) (suc zero) → ⊥
no-tri (below (n , inj₁ _) ())
no-tri (below (n , inj₂ ()) e)
no-tri (above (inj₁ _) ())
no-tri (above (inj₂ ()) e)
no-tri (same ())

no-compare-tw2 : (Legal K₂ω → (q q′ : Pre K₂ω) → Tri (lev K₂ω q) (lev K₂ω q′)) → ⊥
no-compare-tw2 cmp = no-tri (cmp Ω₁-legal q₁ q₂)
```

## 3 放宽成判定，仍推出 LPO

派发真正要的是判定 "结点层在目标层的某个位置上"。目标取第 `coordᴸ α` 支的根 (守卫对一切 `α` 有闭形式，取自
[YiLvNegKeep](YiLvNegKeep.lagda.md))，结点层取 `q₂` 的 `suc zero`：这个判定等于判定 `α` 有没有真值。

```agda
qα : (ℕ → Bool) → Pre K₂ω
qα α = br (coordᴸ α) (coordᴸ-guard α) (inj₁ tt)

qα-level : ∀ α → lev K₂ω (qα α) ≡ levelᴸ α
qα-level α = refl

at→found : ∀ α → At (levelᴸ α) (suc zero) → Found α
at→found α ((n , r) , e) = seen-found α n (flag-one (seen α n) _ r e)

DecAt₂ : Set
DecAt₂ = (q r : Pre K₂ω) →
  At (lev K₂ω q) (lev K₂ω r) ⊎ (At (lev K₂ω q) (lev K₂ω r) → ⊥)

dec-at→lpo : DecAt₂ → LPO
dec-at→lpo dec α with dec (qα α) q₂
... | inj₁ a = inj₁ (at→found α a)
... | inj₂ no = inj₂ (λ s → no (found→one α s))
```

## 4 保留律与折叠律原样搬到 `tw 2`

`KeepFold₂` 是 `RawFold` 的两条携带强度的律，公共上界固定为 `tw 2`，去掉 `Plain`。输出是结点还是极限可以由构造子读出，
所以两条律合起来判定 "不在位置上" 与它的否定。探针树是位置 `q₂` 上的一个结点，下界与各支都取零；它合法并带嵌套证据。

```agda
record KeepFold₂ : Set where
  field
    Φ : (τ : Tgt K₂ω) (ξ : Raw K₂ω) → .(Lgl K₂ω ξ) → .(Nested K₂ω ξ) → Raw (tlev K₂ω τ)
    keep-law : ∀ τ r c t g
      (l : Lgl K₂ω (G.lc r c t g)) (nb : Nested K₂ω (G.lc r c t g)) →
      At (tlev K₂ω τ) (lev K₂ω r) →
      Kept (tlev K₂ω τ) (lev K₂ω r) (Φ τ (G.lc r c t g) l nb)
    fold-law : ∀ τ r c t g
      (l : Lgl K₂ω (G.lc r c t g)) (nb : Nested K₂ω (G.lc r c t g)) →
      (At (tlev K₂ω τ) (lev K₂ω r) → ⊥) →
      IsLim (Φ τ (G.lc r c t g) l nb)

WLPO : Set
WLPO = ∀ (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ ((∀ n → α n ≡ false) → ⊥)

ξ₂ : Raw K₂ω
ξ₂ = G.lc q₂ G.zero G.zero (λ _ _ → G.zero)

ξ₂-lgl : Lgl K₂ω ξ₂
ξ₂-lgl = (λ η e → inj₁ refl) , (λ η e η′ e′ d → inj₁ refl) , (λ η e e′ → refl) , tt , (λ η e → tt)

ξ₂-nested : Nested K₂ω ξ₂
ξ₂-nested = tt , tt , tt , (λ η e → tt)

read-shape : ∀ {m k} {A : Set} (y : Raw m) → (A → Kept m k y) → ((A → ⊥) → IsLim y) →
  (A → ⊥) ⊎ ((A → ⊥) → ⊥)
read-shape (G.lc r c t g) kl fl = inj₂ fl
read-shape G.zero kl fl = inj₁ (λ a → no (kl a))
  where no : Kept _ _ G.zero → ⊥
        no (r , e , c , t , g , ())
read-shape (G.suc y) kl fl = inj₁ (λ a → no (kl a))
  where no : Kept _ _ (G.suc y) → ⊥
        no (r , e , c , t , g , ())
read-shape (G.lim f) kl fl = inj₁ (λ a → no (kl a))
  where no : Kept _ _ (G.lim f) → ⊥
        no (r , e , c , t , g , ())
read-shape (G.em i T) kl fl = inj₁ (λ a → no (kl a))
  where no : Kept _ _ (G.em i T) → ⊥
        no (r , e , c , t , g , ())
read-shape G.top kl fl = inj₁ (λ a → no (kl a))
  where no : Kept _ _ G.top → ⊥
        no (r , e , c , t , g , ())

not-true : ∀ b → (b ≡ true → ⊥) → b ≡ false
not-true false no = refl
not-true true no = ⊥-elim (no refl)

true≢false : true ≡ false → ⊥
true≢false ()

keep-fold→wlpo : KeepFold₂ → WLPO
keep-fold→wlpo F α
  with read-shape (Φ (at (qα α)) ξ₂ ξ₂-lgl ξ₂-nested)
         (keep-law (at (qα α)) q₂ G.zero G.zero (λ _ _ → G.zero) ξ₂-lgl ξ₂-nested)
         (fold-law (at (qα α)) q₂ G.zero G.zero (λ _ _ → G.zero) ξ₂-lgl ξ₂-nested)
  where open KeepFold₂ F
... | inj₁ no = inj₁ (λ n → not-true (α n) (λ p → no (found→one α (n , p))))
... | inj₂ nn = inj₂ (λ h → nn (λ a → true≢false
    (trans (sym (proj₂ (at→found α a))) (h (proj₁ (at→found α a))))))
```

前提的可满足性：有判定 `At` 的神谕 (排中律的实例，`YiLvNegKeep.Locate`) 时 `DecAt₂` 与 `KeepFold₂` 都有模型。所以 §3、§4 说的是 "这样的律拿不到数据"，不是矛盾。

```agda
placeᵒ : ∀ m k → At m k ⊎ (At m k → ⊥) → Raw m
placeᵒ m k (inj₁ (r , e)) = G.lc r (low-zero m r) G.zero (λ _ _ → G.zero)
placeᵒ m k (inj₂ no) = G.lim (λ _ → G.zero)

placeᵒ-kept : ∀ m k (o : At m k ⊎ (At m k → ⊥)) → At m k → Kept m k (placeᵒ m k o)
placeᵒ-kept m k (inj₁ (r , e)) a = r , e , low-zero m r , G.zero , (λ _ _ → G.zero) , refl
placeᵒ-kept m k (inj₂ no) a = ⊥-elim (no a)

placeᵒ-lim : ∀ m k (o : At m k ⊎ (At m k → ⊥)) → (At m k → ⊥) → IsLim (placeᵒ m k o)
placeᵒ-lim m k (inj₁ a) no = ⊥-elim (no a)
placeᵒ-lim m k (inj₂ _) no = tt

foldᵒ : Locate → (τ : Tgt K₂ω) → Raw K₂ω → Raw (tlev K₂ω τ)
foldᵒ orc τ (G.lc r c t g) = placeᵒ (tlev K₂ω τ) (lev K₂ω r) (orc (tlev K₂ω τ) (lev K₂ω r))
foldᵒ orc τ G.zero = G.zero
foldᵒ orc τ (G.suc ξ) = G.zero
foldᵒ orc τ (G.lim f) = G.zero
foldᵒ orc τ (G.em i T) = G.zero
foldᵒ orc τ G.top = G.zero

locate→dec-at : Locate → DecAt₂
locate→dec-at orc q r = orc (lev K₂ω q) (lev K₂ω r)

oracle-model₂ : Locate → KeepFold₂
oracle-model₂ orc = record
  { Φ = λ τ ξ l nb → foldᵒ orc τ ξ
  ; keep-law = λ τ r c t g l nb a →
      placeᵒ-kept (tlev K₂ω τ) (lev K₂ω r) (orc (tlev K₂ω τ) (lev K₂ω r)) a
  ; fold-law = λ τ r c t g l nb no →
      placeᵒ-lim (tlev K₂ω τ) (lev K₂ω r) (orc (tlev K₂ω τ) (lev K₂ω r)) no
  }
```

## 5 正面：有路径相连的位置对

`Link q q′`：两个位置里有一个在主干上，或两支的坐标一个是另一个的字面第一位置 (同一支是它的特例)。
这时把位置沿 `read0-cp` 搬进同一个 `Plain` 的层号 `read0 η′`，用那里的规范比较。主干上的层号 0 用守卫里 `1 ⊲ η` 的路径在支里找到。

```agda
flip : ∀ {i j} → Tri i j → Tri j i
flip (below s e) = above s e
flip (above s e) = below s e
flip (same e) = same (sym e)

compare-up : ∀ η η′ (e : Gd zero raw1 η) (e′ : Gd zero raw1 η′) r r′ → Cp zero η η′ →
  Tri (lev K₂ω (br η e r)) (lev K₂ω (br η′ e′ r′))
compare-up η η′ e e′ r r′ d =
  subst (λ z → Tri z (lev (read0 η′) r′)) (proj₂ (shift (read0-cp η′ d) r))
    (ccompare (read0 η′) (up0-plain η′ (raw0-Nested η′)) (read0-legal η′ (proj₁ (proj₂ e′)))
      (proj₁ (shift (read0-cp η′ d) r)) r′)

compare-zero : ∀ η (e : Gd zero raw1 η) r → Tri zero (lev K₂ω (br η e r))
compare-zero η e r =
  subst (λ z → Tri z (lev (read0 η) r)) (proj₂ (below-one η (proj₁ e)))
    (ccompare (read0 η) (up0-plain η (raw0-Nested η)) (read0-legal η (proj₁ (proj₂ e)))
      (proj₁ (below-one η (proj₁ e))) r)

Link : Pre K₂ω → Pre K₂ω → Set
Link (inj₂ (inj₂ (η , e , r))) (inj₂ (inj₂ (η′ , e′ , r′))) = Cp zero η η′ ⊎ Cp zero η′ η
Link _ _ = ⊤

compare-link : ∀ q q′ → Link q q′ → Tri (lev K₂ω q) (lev K₂ω q′)
compare-link (inj₁ (inj₁ _)) (inj₁ (inj₁ _)) l = same refl
compare-link (inj₁ (inj₁ _)) (inj₂ (inj₁ (inj₁ _))) l = same refl
compare-link (inj₁ (inj₁ _)) (inj₂ (inj₂ (η , e , r))) l = compare-zero η e r
compare-link (inj₂ (inj₁ (inj₁ _))) (inj₁ (inj₁ _)) l = same refl
compare-link (inj₂ (inj₁ (inj₁ _))) (inj₂ (inj₁ (inj₁ _))) l = same refl
compare-link (inj₂ (inj₁ (inj₁ _))) (inj₂ (inj₂ (η , e , r))) l = compare-zero η e r
compare-link (inj₂ (inj₂ (η , e , r))) (inj₁ (inj₁ _)) l = flip (compare-zero η e r)
compare-link (inj₂ (inj₂ (η , e , r))) (inj₂ (inj₁ (inj₁ _))) l = flip (compare-zero η e r)
compare-link (inj₂ (inj₂ (η , e , r))) (inj₂ (inj₂ (η′ , e′ , r′))) (inj₁ d) =
  compare-up η η′ e e′ r r′ d
compare-link (inj₂ (inj₂ (η , e , r))) (inj₂ (inj₂ (η′ , e′ , r′))) (inj₂ d) =
  flip (compare-up η′ η e′ e r′ r d)
compare-link (inj₁ (inj₂ ())) q′ l
compare-link (inj₂ (inj₁ (inj₂ ()))) q′ l
compare-link (inj₁ (inj₁ _)) (inj₁ (inj₂ ())) l
compare-link (inj₁ (inj₁ _)) (inj₂ (inj₁ (inj₂ ()))) l
compare-link (inj₂ (inj₁ (inj₁ _))) (inj₁ (inj₂ ())) l
compare-link (inj₂ (inj₁ (inj₁ _))) (inj₂ (inj₁ (inj₂ ()))) l
compare-link (inj₂ (inj₂ (η , e , r))) (inj₁ (inj₂ ())) l
compare-link (inj₂ (inj₂ (η , e , r))) (inj₂ (inj₁ (inj₂ ()))) l

-- 同一支: 两份守卫可以不同.
compare-same-branch : ∀ η (e e′ : Gd zero raw1 η) r r′ →
  Tri (lev K₂ω (br η e r)) (lev K₂ω (br η e′ r′))
compare-same-branch η e e′ r r′ = compare-link (br η e r) (br η e′ r′) (inj₁ (inj₁ refl))

-- §2 的反例对没有路径相连.
unlinked : Link q₁ q₂ → ⊥
unlinked l = no-tri (compare-link q₁ q₂ l)
```

范围与归类。§2 的机制与旧块上的 `InaccTree.noBT` 相同 (两支上的层号在位置关系下不可比)，这里是在当前的块与 `Tri` 上重证；陈述里没有折叠，没有值，
失败的是 `Tri` 的三个构造子都无居留。它不是 `Barrier.barrier` 的实例：那里的前提 (精确初始段，Ω-共尾元) 这里没有检查。
§3、§4 的机制是 [YiLvNegKeep](YiLvNegKeep.lagda.md) 的 `bare-way→lpo`：判定一个固定层号是否出现在另一支的极限层号的位置上。
§4 的探针树合法并带嵌套证据，位置的守卫是闭的相关证明；它是不是第 4 步的规范构造折叠时走到的 (目标，结点) 对，没有判定。
第 3 步不受影响：`tw 3` 的根只调用各支 `read0 η` 上的折叠 ([YiRawNegChain](YiRawNegChain.lagda.md) 的 `Bridge`)，那里公共上界是 `Plain` 的。
