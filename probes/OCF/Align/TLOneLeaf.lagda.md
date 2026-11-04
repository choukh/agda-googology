# `tH` 实验 (四): 同一组折叠规则, 换叶子

> 入口 [TLOne](TLOne.lagda.md). **判决: HOLDS (只有定义, 编译过, 无条件; 没有证书).** [CrossMTop](CrossMTop.lagda.md) 的 `ψᵀ`, `ΨT`, `ψ̄ᵀ` 里, 第 0 层的 $\dot\Omega$ 只出现在两处: 叶子 `ψᵀ q t0` 和链的起点 `chainT`. 这里把它抽成参数 `Lf`, 别的逐字相同 (机械改写, 脚本没有进仓库; 改写只是把 `Ω̇ᵀ M zero` 换成 `Lf M`, 并给名字加上标). 所以 **$\alpha\ge1$ 的基本列不是为 `tH` 写的, `tH` 只是 `Lf` 的一个取值.** 四个取值:
>
> | 叶子 | 定义 | 有没有绑定 |
> | --- | --- | --- |
> | `L-orig` | `tH 𝟏ᵀ stepT`, 就是 `CrossMTop` | 有 |
> | `L-self` | `tH (本世界第 0 行) stepT`: 第 0 支不抄 `𝟏`, 用闭包链自己的起点 | 有 |
> | `L-row` | 本世界第 0 行, 不绑定 | 无 |
> | `L-cst x` | 常数 $x$ 的树 (`x = lv⊤` 就是 "把 `T⊤` 当被折叠的对象") | 无 |
>
> 这些都不读记号. `L-self` 的动机见 [TLOne](TLOne.lagda.md) 的翻译账: `𝟏ᵀ` 是 `rowL` 第 0 项的翻版, 而那一项在账上是读自记号的.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLOneLeaf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; trans)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level hiding (up)
open import OCF.Free.Prefix using (Z; Ord₊ˢ; Ordˢ; intoˢ; toZ; Ωˢ)
open import OCF.Free.Floor using
  (Flr; fz; fk; fb; _⊔_; Ev; Run; wk; limA; limᵢA; ŝA; ĉA; cloA; flo; cvFlo; toFlo; ∅ᴿ; sucRun; bound; Bd; Fc; FB; evF; iF; liftEv; Top)
open import OCF.Free.Tree using (Fl; asl; asr; swp; dupr2; <◃)
open import OCF.Align.LadderOrdBase
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode using (_ᶜ+_; ⌈_⌉)
open import OCF.Align.CrossMUp
import OCF.Align.CrossMLift as L
open import OCF.Align.CrossMTop
open import OCF.Align.CrossMClosed using (lv⊤)
```

## §1 对叶子参数化的折叠

```agda
module Leaf (Lf : ∀ M → QT zero M Fl (κ′ Fl)) where
  Ω̇ᴸ : ∀ M α → QT α M Fl (κ′ Fl)
  Ω̇ᴸ M zero = Lf M
  Ω̇ᴸ M (suc α) = tΩ (λ e → e) zero (λ e ξ ζ z → twk proj₁ (λ i y → proj₁ y) (tk zero z (ιT zero z)))
  Ω̇ᴸ M (lim f s) = tl (λ n → tk (self n) (Ω̇ᴸ M (f n)) (ιT (self n) (Ω̇ᴸ M (f n))))

  chainᴸ : ∀ {M k φ χ} → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → Sub∞ {M} χ (κ′ Fl) → (QT k M φ χ → QT k M φ χ) → ℕ → QT k M φ χ
  chainᴸ {M} {k} fe fc f zero    = twk fe fc (Ω̇ᴸ M k)
  chainᴸ fe fc f (suc n) = f (chainᴸ fe fc f n)

  ψᴸ : ∀ {M α t} → t <ᴵ α → ∀ {φ χ} → QT α M φ χ → QT t M (Fl ⊔ φ) (𝕎.Z* χ)
  ψᴸ {M} {t = t} q t0 = twk proj₁ fcT (Ω̇ᴸ M t)
  ψᴸ q (ts a) = tl (repT (ψᴸ q a))
  ψᴸ q (tl F) = tl (λ n → ψᴸ q (F n))
  ψᴸ q (ti ac f) = ti (λ e → ac (proj₂ e)) (λ x → ψᴸ q (f x))
  ψᴸ q (tŝ c₀ t g) = tŝ c₀ (ψᴸ q t) (λ η e → ψᴸ q (g η e))
  ψᴸ q (tĉ c₀ z zg o₀ o) = tĉ c₀ z zg (ψᴸ q o₀) (λ η e → ψᴸ q (o η e))
  ψᴸ q (tclo t g) = twk asl (λ i e → e) (tclo (twk asr (λ i e → e) (ψᴸ q t)) (λ η → twk asr (λ i e → e) (ψᴸ q (g η))))
  ψᴸ q {χ = χ} (tcl n ψ s t g) =
    tcl n (Fl ⊔ ψ) (λ e → (proj₁ e , proj₁ (s (proj₂ e))) , proj₂ (s (proj₂ e))) (ψᴸ q t) (λ η → twk (λ e → e) (𝕎.as-upd {_} {κ′ Fl} {χ} n η) (ψᴸ q (g η)))
  ψᴸ q (twk le lc x) = twk (λ e → proj₁ e , le (proj₂ e)) (λ i e → proj₁ e , lc i (proj₂ e)) (ψᴸ q x)
  ψᴸ q (tΩ↓ n fe ac h) = tΩ↓ n proj₁ (λ e → ac (proj₂ e)) (λ ξ ζ z → twk swp (λ i → swp) (ψᴸ q (h ξ ζ z)))
  ψᴸ q {χ = χ} (tH t g) = tH (ψᴸ q t) (λ e → twk (λ y → y) (Ext.cE-Z e χ) (ψᴸ q (g e)))
  ψᴸ q (tk r z x) = ψᴸ q x
  ψᴸ q {φ} {χ} (tΩ fe r h) with <ᴵ-dec r q
  ... | injᵃ (via d s) = tΩ proj₁ s (λ e ξ ζ y → twk swp (λ i w → let c = Ext.cE-Z e χ i (proj₂ w) in proj₁ c , (proj₁ w , proj₂ c)) (ψᴸ q (h e ξ ζ (intoT (<→◃ r) (tr⁻T d (outT (<→◃ s) y))))))
  ... | injᵇ _ = tl (λ n → twk dupr2 (cvT χ) (ψᴸ q (h ⊂r (Fl ⊔ φ) (𝕎.Z* χ) (intoT (<→◃ r) (chainᴸ proj₁ fcT (λ z → twk dupr2 (cvT χ) (ψᴸ r (h ⊂r (Fl ⊔ φ) (𝕎.Z* χ) (intoT (<→◃ r) z)))) n)))))
  ... | injᶜ _ = tl (λ n → twk dupr2 (cvT χ) (ψᴸ q (h ⊂r (Fl ⊔ φ) (𝕎.Z* χ) (intoT (<→◃ r) (chainᴸ proj₁ fcT (λ z → twk dupr2 (cvT χ) (ψᴸ r (h ⊂r (Fl ⊔ φ) (𝕎.Z* χ) (intoT (<→◃ r) z)))) n)))))
  Ψᴸ : ∀ {M α φ χ t w} (H : Hᴹ M) → 𝕎.Ok w → EhT H w χ → t <ᴵ w H → QT α M φ χ → Qᴹ M H t (Fl ⊔ φ) (𝕎.Z* χ)
  Ψᴸ {t = t} H ok e p t0 = 𝕎.qwk proj₁ 𝕎.fc* (𝕎.Ω̇ H t)
  Ψᴸ H ok e p (ts a) = 𝕎.ql (𝕎.repᵠ (Ψᴸ H ok e p a))
  Ψᴸ H ok e p (tl F) = 𝕎.ql (λ n → Ψᴸ H ok e p (F n))
  Ψᴸ H ok e p (ti ac f) = 𝕎.qi (λ u → ac (proj₂ u)) (λ x → Ψᴸ H ok e p (f x))
  Ψᴸ H ok e p (tŝ c₀ x g) = 𝕎.qŝ c₀ (Ψᴸ H ok e p x) (λ η d → Ψᴸ H ok e p (g η d))
  Ψᴸ H ok e p (tĉ c₀ z zg o₀ o) = 𝕎.qĉ c₀ z zg (Ψᴸ H ok e p o₀) (λ η d → Ψᴸ H ok e p (o η d))
  Ψᴸ H ok e p (tclo x g) = 𝕎.qwk asl 𝕎.sub-id (𝕎.qclo (𝕎.qwk asr 𝕎.sub-id (Ψᴸ H ok e p x)) (λ η → 𝕎.qwk asr 𝕎.sub-id (Ψᴸ H ok e p (g η))))
  Ψᴸ H ok e p (twk le le′ x) = 𝕎.qwk (λ u → proj₁ u , le (proj₂ u)) (λ i r u → proj₁ u , le′ i (proj₂ u)) (Ψᴸ H ok (λ i h → le′ i (e i h)) p x)
  Ψᴸ H ok e p (tk r z x) = Ψᴸ H ok e p x
  Ψᴸ {M} {t = t} H ok e p (tH x g) =
    𝕎.qŝ zero (Ψᴸ H ok e p x) (λ η d →
      let e₁ = ⊂+ M ⌈ η ⌉
      in 𝕎.qwk (λ u → u) (Raise.back e₁ _) (L.↓ᴾ e₁ H t (Ψᴸ (up e₁ H) (Raise.ok′ e₁ ok) (Raise.rise e₁ e) (Raise.rise< e₁ p) (g e₁))))
  Ψᴸ {M} {χ = χ} {w = w} H ok e p (tcl n ψ s x g) with <ᴾ-tri n H
  ... | tlt l =
    𝕎.qcl l (Fl ⊔ ψ) (λ u → (proj₁ u , proj₁ (s (proj₂ u))) , proj₂ (s (proj₂ u))) (Ψᴸ H ok e p x)
        (λ η → 𝕎.qwk (λ u → u) (𝕎.⇑ (𝕎.as-upd {_} {𝕎.κ Fl} {χ} n η))
           (Ψᴸ H ok (λ i h → subst (Ev _) (sym (𝕎.upd-gt χ _ (𝕎.Hi-gt l h))) (e i h)) p (g η)))
  ... | teq refl =
    𝕎.qŝ (Bd B) (Ψᴸ H ok e p x)
       (λ η d → 𝕎.qwk (λ u → u) (λ i r u → proj₁ u , subst (Ev _) (sym (𝕎.upd-lt χ _ r)) (proj₂ u))
                (Ψᴸ H (𝕎.upd-ok n w ok (tt , λ q′ → lim 0 (proj₂ (evF B) q′)))
                 (λ i h → 𝕎.upd-ev n i w χ (𝕎.evη {M} ψ B η d) (e i h))
                 (subst (t′ <ᴵ_) (sym (𝕎.upd-self w n _)) (lim 0 (iF B))) (g η)))
    where
    B = bound (ψ ⊔ fk zero) (s (e n (inj₁ refl))) p
    t′ = _
  ... | tgt l =
    𝕎.qŝ (Bd B) (Ψᴸ H ok e p x)
       (λ η d → 𝕎.qwk (λ u → u) (λ i r u → proj₁ u , subst (Ev _) (sym (𝕎.upd-lt χ _ (<ᴾ-trans i H n r l))) (proj₂ u))
                (Ψᴸ H (𝕎.upd-ok n w ok (tt , λ q′ → lim 0 (proj₂ (evF B) q′)))
                 (λ i h → 𝕎.upd-ev n i w χ (𝕎.evη {M} ψ B η d) (e i h))
                 (subst (t′ <ᴵ_) (sym (𝕎.upd-lt w _ l)) p) (g η)))
    where
    B = bound (ψ ⊔ fk zero) (s (e n (inj₂ l))) (𝕎.zr ok n)
    t′ = _
  Ψᴸ {φ = φ} {χ = χ} H ok e p (tΩ↓ {k = k} n fe ac h) with <ᴾ-tri n H
  ... | tlt l = 𝕎.qΩ↓ l proj₁ (λ u → ac (proj₂ u)) (λ ξ ζ z → 𝕎.qwk swp (λ i r → swp) (Ψᴸ H ok (e-loᵀ ζ (inj₂ l) e) p (h ξ ζ (𝕎.outV l z))))
  ... | teq refl with <ᴵ-dec (ac (e n (inj₁ refl))) p
  ...   | injᵃ (via d s) = 𝕎.qΩ proj₁ s (λ ξ ζ y → 𝕎.qwk swp (λ i r → swp) (Ψᴸ H ok (e-loᵀ ζ (inj₁ refl) e) p (h ξ ζ (𝕎.tr⁻Q d (𝕎.outU (<→◃ s) y)))))
  ...   | injᵇ _ = 𝕎.ql (λ i → 𝕎.qwk dupr2 (𝕎.⇑ (𝕎.cv* H)) (Ψᴸ H ok (e⁺ᵀ H ok e) p (h (Fl ⊔ φ) (𝕎.Z* χ) (𝕎.chainᵠ proj₁ 𝕎.fc* (λ z → 𝕎.qwk dupr2 (𝕎.⇑ (𝕎.cv* n)) (Ψᴸ n ok (e⁺ᵀ n ok e) (ac (e n (inj₁ refl))) (h (Fl ⊔ φ) (𝕎.Z* χ) z))) i))))
  ...   | injᶜ _ = 𝕎.ql (λ i → 𝕎.qwk dupr2 (𝕎.⇑ (𝕎.cv* H)) (Ψᴸ H ok (e⁺ᵀ H ok e) p (h (Fl ⊔ φ) (𝕎.Z* χ) (𝕎.chainᵠ proj₁ 𝕎.fc* (λ z → 𝕎.qwk dupr2 (𝕎.⇑ (𝕎.cv* n)) (Ψᴸ n ok (e⁺ᵀ n ok e) (ac (e n (inj₁ refl))) (h (Fl ⊔ φ) (𝕎.Z* χ) z))) i))))
  Ψᴸ {φ = φ} {χ = χ} H ok e p (tΩ↓ {k = k} n fe ac h) | tgt l =
    𝕎.ql (λ i → 𝕎.qwk dupr2 (𝕎.⇑ (𝕎.cv* n)) (Ψᴸ H ok (e⁺ᵀ n ok e) p (h (Fl ⊔ φ) (𝕎.Z* χ) (𝕎.chainᵠ proj₁ 𝕎.fc* (λ z → 𝕎.qwk dupr2 (𝕎.⇑ (𝕎.cv* n)) (Ψᴸ n ok (e⁺ᵀ n ok (e↑ᵀ l e)) (ac (e↑ᵀ l e n (inj₁ refl))) (h (Fl ⊔ φ) (𝕎.Z* χ) z))) i))))
  Ψᴸ {φ = φ} {χ = χ} H ok e p (tΩ fe r h) =
    𝕎.ql (λ i → 𝕎.qwk dupr2 (𝕎.⇑ (cvT χ)) (Ψᴸ H ok (eZᵀ ok e) p (h ⊂r (Fl ⊔ φ) (𝕎.Z* χ) (intoT (<→◃ r) (chainᴸ proj₁ fcT (λ z → twk dupr2 (cvT χ) (ψᴸ r (h ⊂r (Fl ⊔ φ) (𝕎.Z* χ) (intoT (<→◃ r) z)))) i)))))
  ψ̄ᴸ : ∀ {M α φ χ w} → 𝕎.Ok w → EA w χ → QT α M φ χ → Run φ
  ψ̄ᴸ ok e t0 = wk 0 (λ _ → tt) ∅ᴿ
  ψ̄ᴸ ok e (ts a) = sucRun (ψ̄ᴸ ok e a)
  ψ̄ᴸ ok e (tl F) = limA 0 (λ n → ψ̄ᴸ ok e (F n))
  ψ̄ᴸ ok e (ti ac f) = limᵢA 0 ac (λ x → ψ̄ᴸ ok e (f x))
  ψ̄ᴸ ok e (tŝ c₀ t g) = ŝA 0 c₀ (ψ̄ᴸ ok e t) (λ η d → ψ̄ᴸ ok e (g η d))
  ψ̄ᴸ ok e (tĉ c₀ t₀ zg o₀ o) = ĉA 0 c₀ t₀ zg (ψ̄ᴸ ok e o₀) (λ η d → ψ̄ᴸ ok e (o η d))
  ψ̄ᴸ ok e (tclo t g) = cloA 0 (ψ̄ᴸ ok e t) (λ η → ψ̄ᴸ ok e (g η))
  ψ̄ᴸ {M} {χ = χ} {w = w} ok e (tcl n ψ s t g) =
    ŝA 0 (Bd B) (ψ̄ᴸ ok e t)
       (λ η d → ψ̄ᴸ (𝕎.upd-ok n w ok (tt , λ q′ → lim 0 (proj₂ (evF B) q′))) (λ i → 𝕎.upd-ev n i w χ (𝕎.evη {M} ψ B η d) (e i)) (g η))
    where B = bound (ψ ⊔ fk zero) (s (e n)) (𝕎.zr ok n)
  ψ̄ᴸ ok e (twk le le′ x) = wk 0 le (ψ̄ᴸ ok (λ i → le′ i (e i)) x)
  ψ̄ᴸ ok e (tk r z x) = ψ̄ᴸ ok e x
  ψ̄ᴸ {M} ok e (tH x g) = ŝA 0 zero (ψ̄ᴸ ok e x) (λ η d → ψ̄ᴸ (Raise.ok′ (⊂+ M ⌈ η ⌉) ok) (Raise.riseA (⊂+ M ⌈ η ⌉) e) (g (⊂+ M ⌈ η ⌉)))
  ψ̄ᴸ {φ = φ} {χ = χ} ok e (tΩ↓ {k = k} n fe ac h) =
    limA 0 (λ i → wk 0 (λ v → v , v) (ψ̄ᴸ ok (λ j → 𝕎.Ev-lo {_} {𝕎.Z* χ} n j (ok j , e j) , e j) (h φ (𝕎.Z* χ) (𝕎.chainᵠ fe 𝕎.fc* (λ z → 𝕎.qwk (λ v → fe v , (v , v)) (𝕎.⇑ (𝕎.cv* n)) (Ψᴸ n ok (e⁺ᵀ n ok (λ j′ _ → e j′)) (ac (e n)) (h φ (𝕎.Z* χ) z))) i))))
  ψ̄ᴸ {φ = φ} {χ = χ} ok e (tΩ fe r h) =
    limA 0 (λ i → wk 0 (λ v → v , v) (ψ̄ᴸ ok (λ j → (ok j , e j) , cE-r χ j (e j)) (h ⊂r φ (𝕎.Z* χ) (intoT (<→◃ r) (chainᴸ fe fcT (λ z → twk (λ v → fe v , (v , v)) (cvT χ) (ψᴸ r (h ⊂r φ (𝕎.Z* χ) (intoT (<→◃ r) z)))) i)))))

  Tᴸ : Code → Ordᴵ → Run Fl
  Tᴸ M α = ψ̄ᴸ 𝕎.ok₀ (λ i → 𝕎.ok₀ i) (Ω̇ᴸ M α)
```

## §2 四片叶子

```agda
L-orig : ∀ M → QT zero M Fl (κ′ Fl)
L-orig M = tH 𝟏ᵀ stepT

row : ∀ M → QT zero M Fl (κ′ Fl)
row M = twk (λ y → y) (𝕎.κ-cap {M} end (λ _ → tt)) (ι↓T {n = end} (𝕎.Ω̇ {M} end zero))

L-self : ∀ M → QT zero M Fl (κ′ Fl)
L-self M = tH (row M) stepT

L-row : ∀ M → QT zero M Fl (κ′ Fl)
L-row = row

cst : ∀ {M} → Ordᴵ → QT zero M Fl (κ′ Fl)
cst zero = twk (λ _ → tt) (λ i _ → tt) (t0 {φ = fz} {χ = κ′ fz})
cst (suc a) = ts (cst a)
cst (lim f s) = tl (λ n → cst (f n))

L-cst : Ordᴵ → ∀ M → QT zero M Fl (κ′ Fl)
L-cst x M = cst x

module Lo = Leaf L-orig
module Ls = Leaf L-self
module Lr = Leaf L-row
module Lc = Leaf (L-cst lv⊤)
```

## §3 折叠的输出可以落回世界, 叶子不行

`ΨT` 的 `tH` 行: 把绑定折叠到世界 $M$ 的高度 `H`, 输出是世界 $M$ 里的项 (`Y`, 经 `↓ᴾ`, 没有新构造子). 所以 "$\Omega_u$ 被折叠之后" 在世界里写得出. 写不出的是 $\Omega_u$ 本身: 它的分支的高度比世界里任何高度都高, 见 [TLOne](TLOne.lagda.md) 的报错.

```agda
Y : ∀ M (H : Hᴹ M) → Qᴹ M H zero (Fl ⊔ Fl) (𝕎.Z* (κ′ Fl))
Y M H = ΨT H 𝕎.ok₀ (λ i _ → 𝕎.ok₀ i) zero (tH 𝟏ᵀ stepT)
```
