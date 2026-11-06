# 嵌套 `nκ` (六): 可靠性只剩一格

> 不含记号. 入口 [KNest2](KNest2.lagda.md). [KNestSound](KNestSound.lagda.md) 的关系, `κ` 规则多一条前提: 两边树世界可比 (`V ≤ V′ ⊎ V′ ≤ V`). 一格之内要按起点的大小选对齐方式, 而 $A$ 上的序不可判定, 所以这一条要由推导携带.
>
> **定理.**
>
> - `snd² : CellStep → …`: 关系对一切深度可靠, 唯一的参数是 [KNest2Glue](KNest2Glue.lagda.md) 的**一格**比较 `CellStep`. 证明是 `KNestSound.sndᴬ` 的同一个结构归纳, `κ²` 那一格交给 `kstep cs`.
> - `nest-diag²`, `nest-rel²`: 嵌套族 $\mathrm{nest}_k$ 对一切 $k$ 都在关系里, 无条件. 层 $c\le c'$ 的一对分支给出 `inj₁`.
> - `nest-mono²`: 是条件定理, 参数是 `CellStep`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KNest2Sound where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; nκ; nw; pt; sum-fst)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KValTree using (Bk; lo; _⊑[_]_)
open import OCF.Align.KValSem using (ac₁; κ₀)
open import OCF.Align.KValSound using (W; lW; ll; act; hx; Rn; cx; snd-lo)
open import OCF.Align.KNestInv using (cLᴵ; cRᴵ; vleᴵ)
open import OCF.Align.KNestAdm using (Adm)
open import OCF.Align.KNestSound using (Cxᴬ; ci; OutLeᴬ; nextᴬ; nest; adm-self)
open import OCF.Align.KNest2Glue using (CellStep; KStep²; kstep)
```

## §1 关系

```agda
infix 4 _⊑²⟨_,_⟩_
data _⊑²⟨_,_⟩_ : ∀ {V V′} → D one V → A → A → D one V′ → Set where
  n0² : ∀ {α α′ V V′} {x : D one V′} → n0 {W = V} ⊑²⟨ α , α′ ⟩ x
  n1² : ∀ {α α′ V V′} → n1 {W = V} ⊑²⟨ α , α′ ⟩ n1 {W = V′}
  ⨾²  : ∀ {α α′ V V′} {x y : D one V} {x′ y′ : D one V′} → x ⊑²⟨ α , α′ ⟩ x′ → y ⊑²⟨ α , α′ ⟩ y′ → (x ⨾ y) ⊑²⟨ α , α′ ⟩ (x′ ⨾ y′)
  nl²  : ∀ {α α′ V V′} {d : ℕ → D one V} {d′ : ℕ → D one V′} → (∀ n → d n ⊑²⟨ α , α′ ⟩ d′ n) → nl d ⊑²⟨ α , α′ ⟩ nl d′
  nwˡ² : ∀ {α α′ V₀ V V′} {p : V₀ ⊲ V} {x : D one V₀} {x′ : D one V′} → x ⊑²⟨ α , α′ ⟩ x′ → nw p x ⊑²⟨ α , α′ ⟩ x′
  nwʳ² : ∀ {α α′ V₀ V V′} {p : V₀ ⊲ V′} {x : D one V} {x′ : D one V₀} → x ⊑²⟨ α , α′ ⟩ x′ → x ⊑²⟨ α , α′ ⟩ nw p x′
  lo²  : ∀ {α α′ V V′} {x : D one V} {x′ : D one V′} → x ⊑[ lo ] x′ → x ⊑²⟨ α , α′ ⟩ x′
  κ²   : ∀ {α α′ V V′ zz zz′} {u : Bk V} {u′ : Bk V′} → Adm V V′ α α′ → (V ≤ V′ ⊎ V′ ≤ V) →
         (∀ {c c′} (p : V ⊲ c) (p′ : V ⊲ c′) (l : Lg c) (l′ : Lg c′) → c ≤ c′ → u p l ⊑²⟨ c , c′ ⟩ u p′ l′) →
         (∀ {c c′} (p : V′ ⊲ c) (p′ : V′ ⊲ c′) (l : Lg c) (l′ : Lg c′) → c ≤ c′ → u′ p l ⊑²⟨ c , c′ ⟩ u′ p′ l′) →
         (∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (l : Lg c) (l′ : Lg c′) → c ≤ c′ → u p l ⊑²⟨ c , c′ ⟩ u′ p′ l′) →
         nκ zz u ⊑²⟨ α , α′ ⟩ nκ zz′ u′
```

## §2 可靠性: 只剩 `CellStep`

```agda
snd² : CellStep → ∀ {α α′ V V′} {x : D one V} {x′ : D one V′} → x ⊑²⟨ α , α′ ⟩ x′ → OutLeᴬ α α′ x x′
snd² cs n0² s s′ o q q′ w w′ Y Y′ k c c′ cb = ≤-trans cb (⊲→≤ (sum-fst c′ _))
snd² cs n1² s s′ o q q′ w w′ Y Y′ k c c′ cb =
  hx o C.self C.self (lW s) (lW s′) w w′ Y Y′ _ _ (cLᴵ (ci k)) (cRᴵ (ci k)) (vleᴵ (ci k)) c c′ cb
snd² cs (⨾² hx′ hy) s s′ o q q′ w w′ Y Y′ k c c′ cb =
  snd² cs hy s s′ o q q′ _ _ _ _ (nextᴬ o Hx k) _ _ (Hx c c′ cb)
  where Hx = snd² cs hx′ s s′ o q q′ w w′ Y Y′ k
snd² cs (nl² {d = d} {d′} h) s s′ o q q′ w w′ Y Y′ k c c′ cb = l≤ (λ n → ≤l n (proj₁ (go n)))
  where
  P = λ n → F.Rpt ac₁ d q (lW s) (ll s) (act s) w Y n
  P′ = λ n → F.Rpt ac₁ d′ q′ (lW s′) (ll s′) (act s′) w′ Y′ n
  go : ∀ n → (pt c (λ m → F.yc (Rn s (d m) q (proj₁ (P m)) (proj₂ (P m))) (inj₁ (κ₀ (ll s))) tt) n ≤
              pt c′ (λ m → F.yc (Rn s′ (d′ m) q′ (proj₁ (P′ m)) (proj₂ (P′ m))) (inj₁ (κ₀ (ll s′))) tt) n) ×
             Cxᴬ _ _ s s′ (proj₂ (P n)) (proj₂ (P′ n))
  go zero = cb , k
  go (suc n) = let (gb , gk) = go n
                   H = snd² cs (h n) s s′ o q q′ _ _ _ _ gk
               in H _ _ gb , nextᴬ o H gk
snd² cs (nwˡ² {p = p} h) s s′ o q q′ = snd² cs h s s′ o (⊲-tr p q) q′
snd² cs (nwʳ² {p = p} h) s s′ o q q′ = snd² cs h s s′ o q (⊲-tr p q′)
snd² cs (lo² h) s s′ o q q′ w w′ Y Y′ k =
  snd-lo h s s′ o q q′ w w′ Y Y′ (cx (cLᴵ (ci k)) (cRᴵ (ci k)) (vleᴵ (ci k)) tt)
snd² cs (κ² a md mu mu′ cr) =
  kstep cs a md (λ p p′ l l′ le → snd² cs (mu p p′ l l′ le)) (λ p p′ l l′ le → snd² cs (mu′ p p′ l l′ le))
                (λ p p′ l l′ le → snd² cs (cr p p′ l l′ le))
```

## §3 覆盖

```agda
nest-diag² : ∀ k {c c′} → c ≤ c′ → nest k {c} ⊑²⟨ c , c′ ⟩ nest k {c′}
nest-diag² zero le = n1²
nest-diag² (suc k) le =
  κ² (adm-self _ _) (inj₁ le) (λ _ _ _ _ h → nest-diag² k h) (λ _ _ _ _ h → nest-diag² k h) (λ _ _ _ _ h → nest-diag² k h)

nest-rel² : ∀ k {V V′ α α′} → Adm V V′ α α′ → (V ≤ V′ ⊎ V′ ≤ V) → nest k {V} ⊑²⟨ α , α′ ⟩ nest k {V′}
nest-rel² zero a md = n1²
nest-rel² (suc k) a md = κ² a md (λ _ _ _ _ h → nest-diag² k h) (λ _ _ _ _ h → nest-diag² k h) (λ _ _ _ _ h → nest-diag² k h)

nest-mono² : CellStep → ∀ k {V V′ α α′} → Adm V V′ α α′ → (V ≤ V′ ⊎ V′ ≤ V) → OutLeᴬ α α′ (nest k {V}) (nest k {V′})
nest-mono² cs k a md = snd² cs (nest-rel² k a md)
```
