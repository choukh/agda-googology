# 事件世界上的真折叠 (五): 不被压回 $\Omega_2$

> 不含记号. 入口 [EvFold](EvFold.lagda.md). 对照 `TdPlusVal.pr-top` (每一级的级顶投影后与 `Ω₂ᴴ` 互模拟) 与 `UipFbTop.pr₂-top` (投影折叠 `fold₂ = T⁺ ∘ pr₂` 把第二级级顶压回 `Ω₂ᴴ`). 这里的折叠**没有投影**: 它直接以 `Ht = HB T` 为层. 本篇的定理:
>
> 1. **输入不是两种种类的层** (`¬two-kind`): 闭项的层 `top₃ Ω₃ᴱ` 的最外是 κ₁ 的 $\Omega$-结点 (`Λ₃-top`, `refl`), 坐标类型是 `HB S₁` (`E-κ₁`, `refl`); 它与两种种类的层经 `nbᴱ` 的任何像都不互模拟. (两种种类的层就是 `HtTowerF` 的层 `HB S₁`; `nbᴱ` 把它的 `σA`, `σH` 送到 `κa`, κ₀.)
> 2. **折叠把 κ₁ 的结点当作 κ₁ 的闭包处理** (`Ωd-top`): $\Omega_\Lambda$ 的数据树是 `n1 ⨾ nε κ₁ …`; 折叠这一项就是 `RunE … κ₁ …`, 状态是 $Y\oplus\mathrm{Stp}\,Y$ (`run-top`, `refl`).
> 3. **κ₁ 的第一次回灌带新结点** (`first-new`, `cell₀-new`, 对一切世界, 一切状态, 一切闭包): 闭包的第 0 格加的事件, 增量 $\delta_0$ 是第 2 层累积的读回; 它含 `σH` 结点 (坐标是 $H_0$ 的 $\Omega$-分支, `HasH`), 所以与任何 $H_0$ 高度的嵌入 `up h` 都不互模拟. 格的世界里 κ₁ 的界字面地是旧界 ⊞ $\delta_0$ (`AdmEvBase.new-gen₀`), 也含 `σH` 结点, 也不是任何 `up h` (`bd₁-new`), 并且严格高于旧界 (`bd₁-strict`, 严格增长档).
> 4. **`top-bd` 的同形物不成立** (`¬top-bd-ε`): `TdPlusVal.top-bd` 说一致世界里级顶种类有界的坐标都是 $H_0$ 的嵌入. 这里: 第 0 格的世界里, κ₁ 有一个有界的坐标 (界本身) 不与任何 `up h` 互模拟.
>
> **只说什么.** 这些是形状定理: 第 1 条说输入的类型与 `HtTowerF` 的层不同, 第 2 条说这个结点进了 κ₁ 的闭包, 第 3, 4 条说 κ₁ 的界在折叠里真的长出了不在 $H_0$ 嵌入里的高度. **不是值定理**: 不说 `T-Ω₃` 的值高于 `Tᵁ`, `Tdg₂`, `Tᴰ₊` 或 `HtTowerFClosed.T-Ω₂²` (没有跨折叠的比较).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EvFoldNew where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.CumReadCF using (A; azero; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.StallDxBdec using (_<ᴮ_)
open import OCF.Align.DiagK3Zero using (_≈_; ≈z; ≈s; ≈l; ≈Ω)
open import OCF.Align.AdmEvFeed using (⊞-strict)
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead using (rd₂; rd₂-fst; σA; σH; RB; evRB)
open import OCF.Align.EvFoldClosed
```

## §1 输入

```agda
E-κ₁ : E T (inj₂ κ₁) ≡ H₁
E-κ₁ = refl

Λ₃ : Ht
Λ₃ = top₃ Ω₃ᴱ

Λ₃-top : Λ₃ ≡ hΩ (inj₂ κ₁) (λ x → three ⊞ nbᴱ hz (λ _ h → hs h) x)
Λ₃-top = refl

-- 两种种类的层 (HB S₁) 经 nbᴱ 的像
embF : H₁ → Ht
embF = nbᴱ hz (λ _ h → hs h)

¬two-kind : ∀ x → ¬ (Λ₃ ≈ embF x)
¬two-kind hz ()
¬two-kind (hs x) ()
¬two-kind (hl f) ()
¬two-kind (hΩ (inj₁ tt) h) ()
¬two-kind (hΩ (inj₂ tt) h) ()
```

## §2 折叠进了 κ₁ 的闭包

```agda
Ωd-top : ∀ {W} → Σ (ZE κ₁ Λ₃) (λ zz → Σ (∀ {W′} → W ≤ W′ → LgWε W′ → D Λ₃ W′) (λ u → Ωd Λ₃ {W} ≡ n1 ⨾ nε κ₁ zz u))
Ωd-top = _ , _ , refl
```

## §3 κ₁ 的第一次回灌带新结点

`HasH x`: 高度 $x$ (`HB S₁`) 里有 `σH` 结点. 第一位置的上方保持它; `up` 的像没有它; 互模拟保持它.

```agda
HasH : H₁ → Set
HasH hz = ⊥
HasH (hs x) = HasH x
HasH (hl f) = Σ ℕ (λ n → HasH (f n))
HasH (hΩ (inj₁ tt) g) = Σ A (λ c → HasH (g c))
HasH (hΩ (inj₂ tt) g) = ⊤

has⊲ : ∀ {x y : H₁} {w} → x ⊲[ w ] y → HasH x → HasH y
has⊲ hself h = h
has⊲ (hsuc p) h = has⊲ p h
has⊲ (hlim n p) h = n , has⊲ p h
has⊲ (hLim {κ = inj₁ tt} {c = c} e p) h = c , has⊲ p h
has⊲ (hLim {κ = inj₂ tt} e p) h = tt

has-⊞ : ∀ (a δ : H₁) → HasH δ → HasH (a ⊞ δ)
has-⊞ a (hs δ) h = has-⊞ a δ h
has-⊞ a (hl f) (n , h) = n , has-⊞ a (f n) h
has-⊞ a (hΩ (inj₁ tt) g) (c , h) = c , has-⊞ a (g c) h
has-⊞ a (hΩ (inj₂ tt) g) h = tt

up-noH : ∀ (h : H₀) → ¬ HasH (up h)
up-noH (hs h) e = up-noH h e
up-noH (hl f) (n , e) = up-noH (f n) e
up-noH (hΩ tt g) (c , e) = up-noH (g c) e

≈-has : ∀ {x y : H₁} → x ≈ y → HasH x → HasH y
≈-has (≈s e) h = ≈-has e h
≈-has (≈l e) (n , h) = n , ≈-has (e n) h
≈-has (≈Ω {κ = inj₁ tt} e) (c , h) = c , ≈-has (e c) h
≈-has (≈Ω {κ = inj₂ tt} e) h = tt

has→¬up : ∀ {x : H₁} → HasH x → ∀ h → ¬ (x ≈ up h)
has→¬up hx h e = up-noH h (≈-has e hx)
```

```agda
module Top (Λ : Ht) (lΛ : LgB Λ) (o₁ : ∀ {w} → hs hz ⊲[ w ] Λ) (o₂ : ∀ {w} → hs (hs hz) ⊲[ w ] Λ) where
  open At Λ lΛ o₁ o₂

  run-top : ∀ {ly W₀ W} (ac : AccY ly) zz (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgWε W) (ll : LW ly W) (w : D ly W) (Y : St W) →
            Run ac (n1 ⨾ nε κ₁ zz u) q₀ lW ll Act w Y ≡
            Stp Y ⨾ᴰ RunE ac κ₁ u q₀ lW ll Act (w ⨾ nw q₀ n1) (Y ⊕⟨ lW ⟩ Stp Y)
  run-top ac zz u q₀ lW ll w Y = refl
```

**第 0 格的增量.** 状态是 $Y'\oplus\mathrm{Stp}\,Y''$ 时 (`run-top` 给的就是这一形), 第 2 层累积的末段是 $\omega$ 个 $\Omega_2$ 的数据树 (`n1 ⨾ ni (ss hself) …`, 过第 1 层的节点); `rd₂` 把那个节点读成 `σH` 结点.

```agda
  first-new : ∀ {W} (lW : LgWε W) (Y′ Y″ : St W) → HasH (proj₁ (RB κ₁ lW (z₂ (Y′ ⊕⟨ lW ⟩ Stp Y″))))
  first-new lW Y′ Y″ = 1 , has⊲ (rd₂-fst lW _ (yc (d Y″) (τ₂ lW)) {azero , hz}) tt

  module Cell {ly W₀ W} (ac : AccY ly) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgWε W) (ll : LW ly W) (w : D ly W) (Y : St W) where
    Y₁ : St W
    Y₁ = Y ⊕⟨ lW ⟩ Stp Y

    c₀ : Clε W W₀ ly
    c₀ = κcε ac κ₁ u q₀ lW ll Act (w ⨾ nw q₀ n1) Y₁ zero

    δ₀ : H₁
    δ₀ = proj₁ (RB κ₁ lW (zRL κ₁ Y₁))

    -- 第 0 格的世界: 当前世界前面加 κ₁ 的事件, 增量 δ₀
    cell₀-ev : hc c₀ ≡ evRB κ₁ lW (zRL κ₁ Y₁) ∷ proj₂ W
    cell₀-ev = refl

    cell₀-new : HasH δ₀
    cell₀-new = first-new lW Y Y

    δ₀-¬up : ∀ h → ¬ (δ₀ ≈ up h)
    δ₀-¬up = has→¬up cell₀-new

    -- κ₁ 在第 0 格世界里的界
    β₁ : H₁
    β₁ = rp (hc c₀) (hs hz) hself

    β₁≡ : β₁ ≡ rp (proj₂ W) (hs hz) hself ⊞ δ₀
    β₁≡ = EK.new-gen₀ (hs hz) hself δ₀ (proj₂ (RB κ₁ lW (zRL κ₁ Y₁))) (proj₂ W)

    bd₁-new : HasH β₁
    bd₁-new = subst HasH (sym β₁≡) (has-⊞ (rp (proj₂ W) (hs hz) hself) δ₀ cell₀-new)

    bd₁-¬up : ∀ h → ¬ (β₁ ≈ up h)
    bd₁-¬up = has→¬up bd₁-new

    bd₁-strict : rp (proj₂ W) (hs hz) hself <ᴮ β₁
    bd₁-strict = subst (λ t → rp (proj₂ W) (hs hz) hself <ᴮ t) (sym β₁≡) (⊞-strict (rp (proj₂ W) (hs hz) hself) δ₀ tt (azero , hz))

    -- κ₁ 有界的坐标不都是 H₀ 的嵌入
    ¬top-bd-ε : ¬ (∀ x → Bd evK κ₁ x (hc c₀) → Σ H₀ (λ h → x ≈ up h))
    ¬top-bd-ε f with f β₁ hself
    ... | h , e = bd₁-¬up h e
```
