# 验收一侧: 第 0 层出口的记号引理 (见证项的标准形封闭, 一步折叠的那一类)

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提. `exitᴰ`: `M̃ 0 s x` 且 s 与见证项是标准形, 见证项可数, 则 s 的参照值不高于 x 的值 (`lower⁰` 接 `YiCFMono.mono≤ⁿ`).
> 记号引理 (路 a): 规范前缀 `Pre t₀ n` (t₀ 是标准形, `GB [] t₀ t₀`, t₀ 的末项不低于 Ω_n) 之下, ψ₀(t₀ + Ω_m) (m ≤ n) 是可数标准形 (`nf-low`); 一般形式 `nf-app`.
> 不给出什么: 两步折叠产出的见证项 ψ₀(ψ₁(Ω₃)) 不是标准形 (`¬nf₂`), 这一类不在引理之内; `YiAbsGIface.Laws.Base` 记录在 `M̃` 上没有填.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDCExit where

open import Data.Nat using (ℕ; zero; suc) renaming (_≤_ to _≤ⁿ_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import OCF.Lean.YiLegBlock using (Tr; zero)
import OCF.Align.EboLeanDef as E
open E using (T; PT; ψ; natT; HC; _<ᵀ_; []<; hd<; tl<; lv<; ar<)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; _≤ᴾ_; <-≤; ≤ᴾ-trans; InG; gp; gtl; gh; gw; gc; GB; HdLe;
  NF; n[]; n∷; nψ; nf-ψ; nf-Ω; Ctbl; c[]; c∷)
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Align.StandardOmega using (Flat; f[]; f∷)
open import OCF.Align.Value using (_≼_; ≼-trans)
open import OCF.Lean.YiMEBase using (read; Rt; lower⁰)
open import OCF.Lean.YiCFMono using (mono≤ⁿ)
open import OCF.Lean.YiNFOCase using (z<; flatG)
open import OCF.Lean.YiANEnd using (natB; flatN)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ)
open import OCF.Lean.YiDCRel using (M̃; nat≤)
```

## 出口

见证项 t 上用 `lower⁰`, s ≤ᵀ t 上用标准形的项序推出值序. s 的推导 h 任取.

```agda
exitᴰ : ∀ {s x} (m : M̃ 0 s x) → NF s → NF (proj₁ m) → Ctbl (proj₁ m) → (h : HC s) → Rt h ≼ read x
exitᴰ (t , le , m) ns nt ct h = ≼-trans (mono≤ⁿ ns nt ct h (hc nt ct) le) (lower⁰ m (hc nt ct))
```

## 和的标准形

`Join s a`: s 的末项不低于 a 的首项 (s 或 a 为空时无条件). `gb-++`: 前缀自身的 `GB` 加上 a 相对整个和的 `GB`.

```agda
Join : T → T → Set
Join []           a = ⊤
Join (x ∷ [])     a = HdLe x a
Join (x ∷ y ∷ ys) a = Join (y ∷ ys) a

nf-++ : ∀ {s a} → NF s → NF a → Join s a → NF (s ++ a)
nf-++ n[]                      na j = na
nf-++ (n∷ {xs = []}     p h n) na j = n∷ p j na
nf-++ (n∷ {xs = y ∷ ys} p h n) na j = n∷ p h (nf-++ n na j)

++-≤ : ∀ s a → s ≤ᵀ s ++ a
++-≤ []      []      = inj₂ refl
++-≤ []      (_ ∷ _) = inj₁ []<
++-≤ (x ∷ s) a with ++-≤ s a
... | inj₁ p = inj₁ (tl< p)
... | inj₂ e = inj₂ (cong (x ∷_) e)

G-++⁻ : ∀ {u z} p q → InG u z (p ++ q) → InG u z p ⊎ InG u z q
G-++⁻ []      q h       = inj₂ h
G-++⁻ (x ∷ p) q (gp h)  = inj₁ (gp h)
G-++⁻ (x ∷ p) q (gtl h) with G-++⁻ p q h
... | inj₁ i = inj₁ (gtl i)
... | inj₂ i = inj₂ i

gb-++ : ∀ {u} s a → GB u s s → GB u a (s ++ a) → GB u (s ++ a) (s ++ a)
gb-++ s a gs ga i with G-++⁻ s a i
... | inj₁ i′ = <-≤ (gs i′) (++-≤ s a)
... | inj₂ i′ = ga i′

nf-app : ∀ {u} s a → NF u → NF s → GB u s s → NF a → Join s a → GB u a (s ++ a) → NF (ψ u (s ++ a) ∷ [])
nf-app s a nu ns gs na j ga = nf-ψ nu (nf-++ ns na j) (gb-++ s a gs ga)
```

## 规范前缀与 Ω_m

Ω_m 的 `InG` 元素只有 0 (`flatG`), 所以它相对任何非空的和满足 `GB`.

```agda
nfΩ : ∀ m → NF (Ωᴺ m)
nfΩ m = nf-Ω (natB m)

ne++ : ∀ s {y : PT} {ys} → [] <ᵀ s ++ y ∷ ys
ne++ []      = []<
ne++ (_ ∷ _) = []<

gbΩ : ∀ {u} s m → GB u (Ωᴺ m) (s ++ Ωᴺ m)
gbΩ s m i with flatG (f∷ (flatN m) f[]) i
... | refl = ne++ s

Ωᴾ≤ : ∀ {m n} → m ≤ⁿ n → ψ (natT m) [] ≤ᴾ ψ (natT n) []
Ωᴾ≤ l with nat≤ l
... | inj₁ p = inj₁ (lv< p)
... | inj₂ e = inj₂ (cong (λ u → ψ u []) e)

join↓ : ∀ s {x x′ : PT} → x′ ≤ᴾ x → Join s (x ∷ []) → Join s (x′ ∷ [])
join↓ []           l j = tt
join↓ (y ∷ [])     l j = ≤ᴾ-trans l j
join↓ (y ∷ z ∷ zs) l j = join↓ (z ∷ zs) l j

record Pre (t₀ : T) (n : ℕ) : Set where
  constructor mkPre
  field
    nf₀ : NF t₀
    gb₀ : GB [] t₀ t₀
    jn  : Join t₀ (Ωᴺ n)
open Pre public

nf-low : ∀ {t₀ n m} → Pre t₀ n → m ≤ⁿ n → NF (ψᴺ 0 (t₀ ++ Ωᴺ m))
nf-low {t₀} {n} {m} P l = nf-app t₀ (Ωᴺ m) n[] (nf₀ P) (gb₀ P) (nfΩ m) (join↓ t₀ (Ωᴾ≤ l) (jn P)) (gbΩ t₀ m)

ct-low : ∀ a → Ctbl (ψᴺ 0 a)
ct-low a = c∷ c[]
```

前提可满足: 空前缀; 前缀 Ω_k, k 不低于 n.

```agda
pre[] : ∀ n → Pre [] n
pre[] n = mkPre n[] (λ ()) tt

preΩ : ∀ {n k} → n ≤ⁿ k → Pre (Ωᴺ k) n
preΩ {n} {k} l = mkPre (nfΩ k) (λ i → z< (flatG (f∷ (flatN k) f[]) i)) (Ωᴾ≤ l)
```

## 引理的边界

第 3 层的 Ω 树先折到第 1 层再折到第 0 层, `LowKeep` 给出的见证项是 ψ₀(ψ₁(Ω₃)) (关系成立见 [YiDCCheck](YiDCCheck.lagda.md) 的 `wit₂`). 它不是标准形: Ω₃ 是它的 `InG` 元素, 而 Ω₃ 不低于 ψ₁(Ω₃).

```agda
¬Ω₃< : Ωᴺ 3 <ᵀ ψᴺ 1 (Ωᴺ 3) → ⊥
¬Ω₃< (hd< (lv< (hd< (lv< ()))))
¬Ω₃< (hd< (lv< (hd< (ar< ()))))
¬Ω₃< (hd< (lv< (tl< ())))

¬nf₂ : NF (ψᴺ 0 (ψᴺ 1 (Ωᴺ 3))) → ⊥
¬nf₂ (n∷ (nψ _ _ g) _ _) = ¬Ω₃< (g (gp (gh (inj₁ []<))))
```
