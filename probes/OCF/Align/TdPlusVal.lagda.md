# `Tᴰ₊` 的值 (一): 下界与每一级的输入

> 不含记号. 入口 [TdPlus](TdPlus.lagda.md). 两组结论.
>
> - **值的下界 (定理, `TLRuleSpec._≤_`).** `Tᴰ₊` 的第 $k$ 项 $t_k$ 在值上 $\le$ `Tᴰ₊` (`t≤T`); `Tᴰ₊` **严格高于** `DiagK3Zero.t₀` (`t₀<T`: $t_0+1\le$ `Tᴰ₊`), 也严格高于每个部分和 (`pre<T`). 档: 字面前缀式的严格增长 (手册 §3.3 的最低一档): 它只说部分和每一步加了至少 $1$, 不说大小.
> - **每一级的输入 (定理, 互模拟 `_≈_`).** 第 $k$ 级折叠的输入 `prL (k+1) (λh k)` 与 `Ω₂ᴴ = Ωtop S₀` (`HtTowerFClosed.T-Ω₂` 的输入) **互模拟, 对一切 $k$** (`pr-top`). 所以 $t_{k+1}=$ `T⁺ (prL (k+2) (λh (k+1)))` (`t-suc`, `refl`) 与 `T-Ω₂ = T⁺ Ω₂ᴴ` 是互模拟输入上的同一个折叠; $t_0$ 也是 (`DiagK3Zero.pr₀-top`). 证明经三条一般的引理: 投影穿过 `up` (`pr-up`) 与 `ι` (`pr-ι`) 不变 (互模拟), 投影把第二数类的嵌入还原成 `up` (`pr-emb`).
>
> **这对读法的意思 (判断).** 级顶 `λh k` 的 $\Omega$-分支的坐标是 `HB (L′ k)`; 一致世界里有界的只有 `embK k` 的像 (`TdPlusUni.embI`), 那个分支在 `embK k h` 处又只是 $h$ 本身. 所以按 `growL′` (统一 $H_0$ 增量) 回灌, 每一级的级顶在投影后都退成 $\Omega_2$. 若互模拟输入上 `T⁺` 的值相等 (判断, 没有定理; 同 `DiagK3Zero` 对 `t₀` 的判断), 则每个 $t_k$ 读 $\psi_0(\Omega_{\Omega_2})$, `Tᴰ₊ = Dg t` 读 $\psi_0(\Omega_{\Omega_2})\cdot\omega$ (部分和, `DiagKSum` 的毛刺一侧: 上确界 $\psi_0(\Omega_{\Omega_2})$ 不严格高于每一项, `Dg≈sup` 的前提不成立). 这低于 $\psi_0(\Omega_{\Omega_2+1})$ (`T-Ω₂+1` 的读法), 远低于 $\psi_0\Lambda$.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TdPlusVal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc)
open import OCF.Align.TLRuleSpec using (_≤_; ≤-trans; ⊲→≤; one)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.HtTowerNStage using (L′; two)
open import OCF.Align.HtTowerFTree using (S₁; H₀; κA; κH; sum-fst)
open import OCF.Align.HtTowerFClosed using (T⁺; Ω₂ᴴ)
open import OCF.Align.DiagKSum using (pre; Dg; x≤pre; pre≤Dg; pre-<)
open import OCF.Align.DiagKTop using (λh; Lg-λh; towerL′; module Top)
open import OCF.Align.DiagK3Zero using (t₀; _≈_; ≈z; ≈s; ≈l; ≈Ω)
import OCF.Align.DiagK3One as D3
open import OCF.Align.TdPlusUni
open import OCF.Align.TdPlusFold using (prL; Lg-prL; fold₊; Tᴰ₊)
```

## §1 `Tᴰ₊` 的各项

```agda
t₊ : ℕ → A
t₊ = Top.t towerL′ (D3.mkFd fold₊)

Tᴰ₊≡ : Tᴰ₊ ≡ Dg t₊
Tᴰ₊≡ = refl

t-zero : t₊ 0 ≡ t₀
t-zero = refl

t-suc : ∀ k → t₊ (suc k) ≡ T⁺ (prL (suc (suc k)) (λh (suc k))) (Lg-prL (suc (suc k)) (λh (suc k)) (Lg-λh (suc k)))
t-suc k = refl
```

## §2 值的下界

`T⁺ h` 的第 0 层树以 $1$ 开头 (`ΨΩ = n1 ⨾ …`), 所以 $1\le$ `T⁺ h`.

```agda
one≤T⁺ : ∀ h (lh : LgB h) → one ≤ T⁺ h lh
one≤T⁺ h lh = ⊲→≤ (sum-fst (asuc azero) _)

t≤T : ∀ k → t₊ k ≤ Tᴰ₊
t≤T k = ≤-trans (x≤pre t₊ k) (pre≤Dg t₊ k)

pre<T : ∀ k → asuc (pre t₊ k) ≤ Tᴰ₊
pre<T k = ≤-trans (pre-< t₊ k (one≤T⁺ (prL (suc (suc k)) (λh (suc k))) (Lg-prL (suc (suc k)) (λh (suc k)) (Lg-λh (suc k))))) (pre≤Dg t₊ (suc k))

t₀<T : asuc t₀ ≤ Tᴰ₊
t₀<T = pre<T 0
```

## §3 互模拟的引理

```agda
≈-refl : ∀ {S} (x : HB S) → x ≈ x
≈-refl hz = ≈z
≈-refl (hs x) = ≈s (≈-refl x)
≈-refl (hl f) = ≈l (λ n → ≈-refl (f n))
≈-refl (hΩ κ g) = ≈Ω (λ c → ≈-refl (g c))

≈-trans : ∀ {S} {x y z : HB S} → x ≈ y → y ≈ z → x ≈ z
≈-trans ≈z ≈z = ≈z
≈-trans (≈s p) (≈s q) = ≈s (≈-trans p q)
≈-trans (≈l p) (≈l q) = ≈l (λ n → ≈-trans (p n) (q n))
≈-trans (≈Ω p) (≈Ω q) = ≈Ω (λ c → ≈-trans (p c) (q c))
```

## §4 投影穿过 `up` 与 `ι`

```agda
module _ {S : KS} (U : Uni S) where
  private
    module P = Pr U
    module P⁺ = Pr (uStep U)

  prK-up : ∀ {κ} (cl : Cls S (uW U) κ) {G G′ : E S κ → HB S₁} → (∀ c → G c ≈ G′ c) →
           P⁺.prK (inj₁ κ) (liftStep U cl) G ≈ P.prK κ cl G′
  prK-up (cA e _ _ _ _) h = ≈Ω (λ c → h (e c))
  prK-up (cH e _ _ _ _) h = ≈Ω (λ c → h (e c))

  pr-up : ∀ t → P⁺.pr (up t) ≈ P.pr t
  pr-up hz = ≈z
  pr-up (hs t) = ≈s (pr-up t)
  pr-up (hl f) = ≈l (λ n → pr-up (f n))
  pr-up (hΩ κ g) = prK-up (cls U κ) (λ c → pr-up (g c))

module _ {I : Set} {F : I → KS} (i₀ : I) (U : (i : I) → Uni (F i)) where
  private
    module Pˢ = Pr (uSup i₀ U)

  prK-ι : ∀ {i κ} (cl : Cls (F i) (uW (U i)) κ) {G G′ : E (F i) κ → HB S₁} → (∀ c → G c ≈ G′ c) →
          Pˢ.prK (i , κ) (liftSup i₀ U cl) G ≈ Pr.prK (U i) κ cl G′
  prK-ι (cA e _ _ _ _) h = ≈Ω (λ c → h (e c))
  prK-ι (cH e _ _ _ _) h = ≈Ω (λ c → h (e c))

  pr-ι : ∀ i t → Pˢ.pr (ι {F = F} i t) ≈ Pr.pr (U i) t
  pr-ι i hz = ≈z
  pr-ι i (hs t) = ≈s (pr-ι i t)
  pr-ι i (hl f) = ≈l (λ n → pr-ι i (f n))
  pr-ι i (hΩ κ g) = prK-ι (cls (U i) κ) (λ c → pr-ι i (g c))
```

## §5 投影把嵌入还原成 `up`, 级顶退成 $\Omega_2$

```agda
pr₀-up : ∀ h → Pr.pr uS₀ h ≈ up {S₀} h
pr₀-up hz = ≈z
pr₀-up (hs h) = ≈s (pr₀-up h)
pr₀-up (hl f) = ≈l (λ n → pr₀-up (f n))
pr₀-up (hΩ tt g) = ≈Ω (λ c → pr₀-up (g c))

FL : ℕ → Bool → KS
FL k = two (step (L′ k)) (Lev (Ωtop (L′ k)))

UL : ∀ k (b : Bool) → Uni (FL k b)
UL k = uTwo (uStep (uL k)) (uLev (Ωtop (L′ k)))

pr-emb : ∀ k h → Pr.pr (uL k) (emb (uL k) h) ≈ up {S₀} h
pr-emb zero h = pr₀-up h
pr-emb (suc k) h =
  ≈-trans (pr-ι true (UL k) true (up (emb (uL k) h)))
    (≈-trans (pr-up (uL k) (emb (uL k) h)) (pr-emb k h))

pr-top : ∀ k → prL (suc k) (λh k) ≈ Ω₂ᴴ
pr-top k = ≈Ω (λ h →
  ≈-trans (pr-ι true (UL k) true (up (emb (uL k) h)))
    (≈-trans (pr-up (uL k) (emb (uL k) h)) (pr-emb k h)))

-- 第 k+1 项的输入
in-suc : ∀ k → prL (suc (suc k)) (λh (suc k)) ≈ Ω₂ᴴ
in-suc k = pr-top (suc k)
```

**级顶的坐标.** 一致世界里, 级顶 `λh k` 那个种类 (`L′ (k+1)` 的 `(true , inj₂ tt)`, 坐标 `HB (L′ k)`) 有界的坐标都是第二数类的嵌入 `emb (uL k) h` (就是 `embK k h`), 原像在世界的高度界之下. 这是 `DiagK3One.noNew-emb` 在一切级上的对应: 只增长的世界给不出新种类的坐标.

```agda
top-bd : ∀ k {x a β} → Bd (L′ (suc k)) (true , inj₂ tt) x (uW (uL (suc k)) a β) →
         Σ H₀ (λ h → (x ≡ emb (uL k) h) × (h ⊲[ a ] β))
top-bd k p = embI (uL k) p
```
