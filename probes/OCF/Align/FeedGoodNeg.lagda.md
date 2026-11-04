# `GoodFeed` 按现在的形状是假的; 跨界的 $\trianglelefteq$ 只能走第一支 (判决: HOLDS, 对文件里写明的陈述)

> 不含记号. 结论写在 [FeedGood](FeedGood.lagda.md). 全部编译过, 无模块参数.
>
> - `no-≈₁`: **`Lv₅ ≈ feedL u₀` 是假的.** 目标 1 穿过分支 2, `feedL u₀` 的界是 2, `Lv₅` 的界是 1. 正确的陈述是 `feed≈` ([FeedGoodFirst](FeedGoodFirst.lagda.md)).
> - `no-cfF`, `no-GoodFeed`: **`GoodFeed` 不可满足.** 字段 `cfF` 对一切 `GL`, 而 `GL` 的 `tcG : Tc lvl` 可以读分支的证明 $e$. 取闭包 `V` (分支恒为 $\Omega_1+1$), 在 $\omega$ 上按 $e$ 给两个读法: `lim 1` 用紧的, 其余用恒等的. 输出里同一个分支 $\omega$ 的两份树, 沿同一条路径界分别是 2 与 3, 所以输出连 `≈` 自反都没有. **这只杀 "对一切 `GL`" (带任意的 `Tc`), 不杀链本身.** 修法: `cfF` 只沿链 (`FeedChain`), 或者 `Tc` 不读 $e$.
> - `⊴-cross`: **第二个否定, 这才是实质.** 若表 $E$ 不给闭包 $R$ 的任何分支证据 (例如 $R$ 的界太高), 则任何 $L\trianglelefteq R$ 把 $L$ 的分支里的 $k$ 只能搬到 $R$ 的第一支. `cross₃`: 实例. 与验收 `c-sib-id`, `c-sib-ti` 合起来说明恒等读法下 `cfF` 大概不成立 (**判断**, 差一步: 没有证 $k$ 不在第一支之下).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FeedGoodNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import OCF.Align.GuardTightCum using (Ordᴵ; natᴵ; ωᴵ; zero; suc; lim; _⊑ᴵ_; _≅ᴵ_; _<ᴵ_; z≅; s≅; l≅; s⊑; z⊑; ≅ᴵ-refl; ⊑ᴵ-trans)
open import OCF.Align.GuardTightLv
open Lv Dom₀
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTree
open import OCF.Align.GuardTightUp hiding (e₃)
open import OCF.Align.GuardTightRd using (module RdIter)
import OCF.Align.GuardTightUni as Uni
private module U = Uni Dom₀
open U using (Lv₅)
```

## §1 `Lv₅` 不是 `feedL u₀`

```agda
no-≈₁ : Lv₅ ≈ feedL u₀ → ⊥
no-≈₁ (o≈ (s≅ ()) _ _)
```

## §2 沿路径看界

`bdOf p x`: 沿路径 $p$ 走到底, 读界. 对 $\approx$ 不变 (`bdOf-≈`). 所以路径上算出不同的数, 就证伪 $\approx$, 不必比较两棵大树.

```agda
toN : Ordᴵ → ℕ
toN zero = 0
toN (suc a) = suc (toN a)
toN (lim f s) = toN (f 1)

toN-≅ : ∀ {a b} → a ≅ᴵ b → toN a ≡ toN b
toN-≅ z≅ = refl
toN-≅ (s≅ e) = cong suc (toN-≅ e)
toN-≅ {lim f s} {lim g t} (l≅ h) = toN-≅ {f 1} {g 1} (h 1)

data Stp : Set where
  L : ℕ → Stp
  F₀ : Stp
  B₃ : Stp

e₂₃ : suc (suc zero) ⊑ᴵ natᴵ 3
e₂₃ = s⊑ (s≅ z≅) (suc zero)

bc : (c : Ordᴵ) → ((η : Ordᴵ) → c ⊑ᴵ η → LG) → (LG → ℕ) → ℕ
bc (suc (suc zero)) g k = k (g (natᴵ 3) e₂₃)
bc zero g k = 0
bc (suc zero) g k = 0
bc (suc (suc (suc c))) g k = 0
bc (suc (suc (lim f s))) g k = 0
bc (suc (lim f s)) g k = 0
bc (lim f s) g k = 0

bdOf : List Stp → LG → ℕ
bdOf [] (lc c t g) = toN c
bdOf [] zero = 0
bdOf [] (suc x) = 0
bdOf [] (lim f) = 0
bdOf (L n ∷ p) (lim f) = bdOf p (f n)
bdOf (L n ∷ p) zero = 0
bdOf (L n ∷ p) (suc x) = 0
bdOf (L n ∷ p) (lc c t g) = 0
bdOf (F₀ ∷ p) (lc c t g) = bdOf p t
bdOf (F₀ ∷ p) zero = 0
bdOf (F₀ ∷ p) (suc x) = 0
bdOf (F₀ ∷ p) (lim f) = 0
bdOf (B₃ ∷ p) (lc c t g) = bc c g (bdOf p)
bdOf (B₃ ∷ p) zero = 0
bdOf (B₃ ∷ p) (suc x) = 0
bdOf (B₃ ∷ p) (lim f) = 0

bdOf-≈ : ∀ p {x y} → x ≈ y → bdOf p x ≡ bdOf p y
bdOf-≈ [] z≈ = refl
bdOf-≈ [] (s≈ e) = refl
bdOf-≈ [] (l≈ h) = refl
bdOf-≈ [] (o≈ d e h) = toN-≅ d
bdOf-≈ (L n ∷ p) z≈ = refl
bdOf-≈ (L n ∷ p) (s≈ e) = refl
bdOf-≈ (L n ∷ p) (l≈ h) = bdOf-≈ p (h n)
bdOf-≈ (L n ∷ p) (o≈ d e h) = refl
bdOf-≈ (F₀ ∷ p) z≈ = refl
bdOf-≈ (F₀ ∷ p) (s≈ e) = refl
bdOf-≈ (F₀ ∷ p) (l≈ h) = refl
bdOf-≈ (F₀ ∷ p) (o≈ d e h) = bdOf-≈ p e
bdOf-≈ (B₃ ∷ p) z≈ = refl
bdOf-≈ (B₃ ∷ p) (s≈ e) = refl
bdOf-≈ (B₃ ∷ p) (l≈ h) = refl
bdOf-≈ (B₃ ∷ p) (o≈ (s≅ (s≅ z≅)) e h) = bdOf-≈ p (h (natᴵ 3) e₂₃ (natᴵ 3) e₂₃ (≅ᴵ-refl (natᴵ 3)))
bdOf-≈ (B₃ ∷ p) (o≈ z≅ e h) = refl
bdOf-≈ (B₃ ∷ p) (o≈ (s≅ z≅) e h) = refl
bdOf-≈ (B₃ ∷ p) (o≈ (s≅ (s≅ (s≅ _))) e h) = refl
bdOf-≈ (B₃ ∷ p) (o≈ (s≅ (s≅ (l≅ _))) e h) = refl
bdOf-≈ (B₃ ∷ p) (o≈ (s≅ (l≅ _)) e h) = refl
bdOf-≈ (B₃ ∷ p) (o≈ (l≅ _) e h) = refl
```

## §3 反例

`V`: 界 1, 第一支与全部分支都是 $X=\Omega_1+1$. 好层号 (`wV`, `sV`). 读法 `tcSel` 读分支的证明. 目标 1 走第一支, 表是 `∅ 2`.

```agda
X : LG
X = suc xΩ

sX : X ≈ X
sX = s≈ (proj₂ cfΩ)

V : LG
V = lc (suc zero) X (λ _ _ → X)

wV : WFˢ V
wV = (λ η e → ≈→⊴ sX) , (λ η e η′ e′ d → ≈→⊴ sX) , proj₁ cfΩ , (λ η e → proj₁ cfΩ)

sV : V ≈ V
sV = o≈ (s≅ z≅) sX (λ η e η′ e′ k → sX)

tcSel : (η : Ordᴵ) → suc zero ⊑ᴵ η → Tc X
tcSel (lim f s) (s⊑ _ (lim (suc zero) _)) = RdIter.Tc-c
tcSel _ _ = Tc-id X

tcV : Tc V
tcV = rdId , Tc-id X , tcSel

two : Ordᴵ
two = natᴵ 2

qV : suc zero < V
qV = fst (suc (bra two (s⊑ z≅ (suc zero)) zero))

aV : Adm (tab (∅ two)) qV
aV = (two , refl , zero) , tt

uV : GL
uV = gl V (wV , sV) tcV (∅ two) qV aV

e₅ e₆ : suc zero ⊑ᴵ ωᴵ
e₅ = s⊑ z≅ (lim 1 zero)
e₆ = s⊑ z≅ (lim 2 (suc zero))

Bdy : (e : suc zero ⊑ᴵ ωᴵ) → LG → LG
Bdy e (lc (suc zero) t g) = g ωᴵ e
Bdy e zero = zero
Bdy e (suc x) = zero
Bdy e (lim f) = zero
Bdy e (lc zero t g) = zero
Bdy e (lc (suc (suc c)) t g) = zero
Bdy e (lc (suc (lim f s)) t g) = zero
Bdy e (lc (lim f s) t g) = zero

Bdy-≈ : ∀ e e′ {x y} → x ≈ y → Bdy e x ≈ Bdy e′ y
Bdy-≈ e e′ z≈ = z≈
Bdy-≈ e e′ (s≈ _) = z≈
Bdy-≈ e e′ (l≈ _) = z≈
Bdy-≈ e e′ (o≈ (s≅ z≅) _ h) = h ωᴵ e ωᴵ e′ (≅ᴵ-refl ωᴵ)
Bdy-≈ e e′ (o≈ z≅ _ _) = z≈
Bdy-≈ e e′ (o≈ (s≅ (s≅ _)) _ _) = z≈
Bdy-≈ e e′ (o≈ (s≅ (l≅ _)) _ _) = z≈
Bdy-≈ e e′ (o≈ (l≅ _) _ _) = z≈

ptX : List Stp
ptX = L 1 ∷ B₃ ∷ L 0 ∷ L 1 ∷ F₀ ∷ L 1 ∷ []

valA : bdOf ptX (Bdy e₅ (feedL uV)) ≡ 2
valA = refl

valB : bdOf ptX (Bdy e₆ (feedL uV)) ≡ 3
valB = refl

ne : 2 ≡ 3 → ⊥
ne ()

no-cfF : (∀ u → Cfˢ (feedL u)) → ⊥
no-cfF cf = ne (trans (sym valA) (trans (bdOf-≈ ptX {Bdy e₅ (feedL uV)} {Bdy e₆ (feedL uV)} (Bdy-≈ e₅ e₆ {feedL uV} {feedL uV} (proj₂ (cf uV)))) valB))

no-GoodFeed : GoodFeed → ⊥
no-GoodFeed G = no-cfF (GoodFeed.cfF G)
```

## §4 跨界的搬运只能走第一支

`⊴-cross`: 闭包 $R$ 的分支都没有 $E$ 的证据, 则 $L\trianglelefteq R$ 把 $L$ 的分支里的 $k$ 送进 $R$ 的第一支. 这就是界为什么必须紧: 两份同形的闭包只要界不同就不是同一个键, 而 `⊴` 的转移对**一切**表成立.

```agda
⊴-cross : ∀ {c t g c′ t′ g′ η e k} (r : k < g η e) (E : Ents) →
          Adm (tab E) (bra {c = c} {t = t} {g = g} η e r) →
          (∀ η′ → c′ ⊑ᴵ η′ → Bel (tab E) (lc c′ t′ g′) η′ → ⊥) →
          lc c t g ⊴ lc c′ t′ g′ → Below k t′
⊴-cross {η = η} {e = e} r E a no x with ⊴p x (bra η e r)
... | viaᴸ d (fst s) tf = pre d s
... | viaᴸ d (bra η′ e′ s) tf = ⊥-elim (no η′ e′ (proj₁ (tf (tab E) a)))

no32 : natᴵ 3 ⊑ᴵ natᴵ 2 → ⊥
no32 (s⊑ (s≅ (s≅ z≅)) (suc (suc ())))

no-bel₃ : ∀ {y η′} → natᴵ 3 ⊑ᴵ η′ → Bel (tab (∅ two)) y η′ → ⊥
no-bel₃ {η′ = η′} e (ℓ , refl , q) = no32 (⊑ᴵ-trans e (pr⊑ η′ q))

cross₃ : ∀ {c t g t′ g′ η e k} (r : k < g η e) → Adm (tab (∅ two)) (bra {c = c} {t = t} {g = g} η e r) →
         lc c t g ⊴ lc (natᴵ 3) t′ g′ → Below k t′
cross₃ r a x = ⊴-cross r (∅ two) a (λ η′ e′ b → no-bel₃ e′ b) x
```
