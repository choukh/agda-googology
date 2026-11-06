# `T⁺` 对输入单调 (四): 闭项之间的值定理表

> 不含记号. 接口 [TpMonoIf](TpMonoIf.lagda.md). 两部分:
>
> 1. **输入之间的字面关系 (定理, 无前提).** 第一批闭项都是 `T⁺` 在某个输入上的值. 这里列出输入之间已有的字面证据: 一切世界的 (严格) 第一位置, 互模拟, 左加平移, 以及两条 `refl` (`Tlv 0` 就是 `T-Ω₂`; `idx (Ω₃+1)` 就是 `idx Ω₃` 的后继).
> 2. **值定理表 (条件定理, 前提是 `Laws⁺`, 即 `T⁺` 满足接口的四条律).** 每条都只用到输入之间的字面证据加一条律. 前提 `Laws⁺` 没有对 `T⁺` 的实例 (第一个障碍见入口 [TpMono](TpMono.lagda.md)); 律的形状可满足由 [TpMonoToy](TpMonoToy.lagda.md) 给出.
>
> 本文的值定理都是值的定理 (`TLRuleSpec._≤_`), 不是对参照树的序数值验收.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TpMonoTab where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.TLRuleSpec using (s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊞-mono) renaming (_≤_ to _≤ᴬ_)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop)
open import OCF.Align.HtTowerFTree using (S₁; Ht; Wd₂)
open import OCF.Align.HtTowerFClosed using (T⁺; Ω₂ᴴ; lΩ₂; mul; Lg-mul; Ω₂ω; Lg-Ω₂ω; T-Ω₂; T-Ω₂+1; T-Ω₂·2; T-Ω₂ω)
open import OCF.Align.DiagK3Zero using (≈z; ≈s; ≈l; ≈Ω; t₀; pr₀; Lg-pr₀; pr₀-top; lλ₀)
open import OCF.Align.DiagKTop using (λh; Lg-λh)
open import OCF.Align.DiagKSum using (pre; Dg)
open import OCF.Align.TdPlusFold using (prL; Lg-prL; Tᴰ₊)
open import OCF.Align.TdPlusVal using (t₊; in-suc; ≈-refl; ≈-trans)
open import OCF.Align.FamFoldAll using (H; lgH; Tlv; cum; lcum; Λ∞; lΛ∞; T∞)
open import OCF.Align.FamFoldOne using (idx; Lg-idx; cells; cells-st; Ω₃; Tᵀ; Tᵀ+1)
open import OCF.Align.HtTowerNFb using (Λs₂; Λω₂; lΛω₂; fb₂-fst; fb₂-st; T-fb₂; T-fb₂ω)
open import OCF.Align.UipFbClosed using (module C₁; module Cω; Tᵁ; inω≈)
open import OCF.Align.TpMonoIf
```

## §1 关系的小件

```agda
⁺→⊲ : ∀ {a b} {w : Wd₂} → a ⊲⁺[ w ] b → a ⊲[ w ] b
⁺→⊲ (psuc p) = hsuc p
⁺→⊲ (plim n p) = hlim n p
⁺→⊲ (pLim e p) = hLim e p

-- 后继是第一位置 ⇒ 严格第一位置
hs→⁺ : ∀ {a b} {w : Wd₂} → hs a ⊲[ w ] b → a ⊲⁺[ w ] b
hs→⁺ hself = psuc hself
hs→⁺ (hsuc p) = psuc (⁺→⊲ (hs→⁺ p))
hs→⁺ (hlim n p) = plim n (⁺→⊲ (hs→⁺ p))
hs→⁺ (hLim e p) = pLim e (⁺→⊲ (hs→⁺ p))

-- 左加非零的高度: 严格第一位置 (一切世界)
⊞-hs⁺ : ∀ a b → a ⊏ a ⊞ hs b
⊞-hs⁺ a b = psuc (⊞-fst a b)

⊞-hl⁺ : ∀ a f → a ⊏ a ⊞ hl f
⊞-hl⁺ a f = plim 0 (⊞-fst a (f 0))

⊞-hΩ⁺ : ∀ a κ g → a ⊏ a ⊞ hΩ κ g
⊞-hΩ⁺ a κ g {w} = pLim (botBd S₁ κ w) (⊞-fst a (g (bot S₁ κ)))

≈-sym : ∀ {S} {x y : HB S} → x ≈ y → y ≈ x
≈-sym ≈z = ≈z
≈-sym (≈s p) = ≈s (≈-sym p)
≈-sym (≈l p) = ≈l (λ n → ≈-sym (p n))
≈-sym (≈Ω p) = ≈Ω (λ c → ≈-sym (p c))

-- 0 ⊞ x 与 x 互模拟
hz⊞≈ : ∀ {S} (x : HB S) → hz ⊞ x ≈ x
hz⊞≈ hz = ≈z
hz⊞≈ (hs x) = ≈s (hz⊞≈ x)
hz⊞≈ (hl f) = ≈l (λ n → hz⊞≈ (f n))
hz⊞≈ (hΩ κ g) = ≈Ω (λ c → hz⊞≈ (g c))

-- 部分和的对角对逐项 ≤ 单调
preM : ∀ {x y : ℕ → A} → (∀ k → x k ≤ᴬ y k) → ∀ k → pre x k ≤ᴬ pre y k
preM h zero = h zero
preM h (suc k) = ⊞-mono (preM h k) (h (suc k))

DgM : ∀ {x y : ℕ → A} → (∀ k → x k ≤ᴬ y k) → Dg x ≤ᴬ Dg y
DgM h = l≤ (λ k → ≤l k (preM h k))
```

## §2 输入之间的字面关系 (定理, 无前提)

```agda
-- refl: 第 0 级的级顶就是 Ω₂
Tlv0≡ : Tlv 0 ≡ T-Ω₂
Tlv0≡ = refl

-- refl: 一级折叠把后继折成后继
idx-hs : idx (hs Ω₃) ≡ hs (idx Ω₃)
idx-hs = refl

-- Ω₂ 一族
Ω₂⊏+1 : Ω₂ᴴ ⊏ hs Ω₂ᴴ
Ω₂⊏+1 = psuc hself

mul1≈ : mul 1 ≈ Ω₂ᴴ
mul1≈ = hz⊞≈ Ω₂ᴴ

mul1⊏2 : mul 1 ⊏ mul 2
mul1⊏2 = ⊞-hΩ⁺ (mul 1) (inj₂ tt) up

mul⊏ω : ∀ n → mul n ⊏ Ω₂ω
mul⊏ω n = plim n hself

-- 一切级: 累加的第 k 段是对角的严格第一位置; 第 k+1 级的级顶左加到累加上
cum⊏∞ : ∀ k → cum k ⊏ Λ∞
cum⊏∞ k = plim k hself

cum⊑ : ∀ k → cum k ⊑ cum (suc k)
cum⊑ k = ⊞-fst (cum k) (H (suc k))

-- 回灌族 Λs₂
fb₂⊏ : ∀ n → proj₁ (Λs₂ n) ⊏ proj₁ (Λs₂ (suc n))
fb₂⊏ n = hs→⁺ (fb₂-fst (Λs₂ n))

fb₂⊏ω : ∀ n → proj₁ (Λs₂ n) ⊏ Λω₂
fb₂⊏ω n = plim n hself

-- 一级折叠的级顶: 格是它的严格第一位置; 级顶是 Ω₃+1 的输入的严格第一位置
cells⊏ : ∀ n → cells n ⊏ idx Ω₃
cells⊏ n = plim n hself

idx⊏+1 : idx Ω₃ ⊏ idx (hs Ω₃)
idx⊏+1 = psuc hself

-- UIP 链: 槽是极限的严格第一位置
x⊏ : ∀ n → C₁.x n ⊏ C₁.Λᶜ
x⊏ n = plim n hself
```

## §3 值定理表 (条件定理: 前提 `Laws⁺`)

```agda
module Tab (Lw : Laws⁺) where
  open Laws Lw

  -- Ω₂ 一族
  Ω₂<Ω₂+1 : asuc T-Ω₂ ≤ᴬ T-Ω₂+1
  Ω₂<Ω₂+1 = fst< Ω₂ᴴ lΩ₂ (hs Ω₂ᴴ) lΩ₂ Ω₂⊏+1

  Ω₂<Ω₂·2 : asuc T-Ω₂ ≤ᴬ T-Ω₂·2
  Ω₂<Ω₂·2 = ≤-trans (s≤ (sim Ω₂ᴴ lΩ₂ (mul 1) (Lg-mul 1) (≈-sym mul1≈))) (fst< (mul 1) (Lg-mul 1) (mul 2) (Lg-mul 2) mul1⊏2)

  mul<ω : ∀ n → asuc (T⁺ (mul n) (Lg-mul n)) ≤ᴬ T-Ω₂ω
  mul<ω n = fst< (mul n) (Lg-mul n) Ω₂ω Lg-Ω₂ω (mul⊏ω n)

  Ω₂·2<Ω₂ω : asuc T-Ω₂·2 ≤ᴬ T-Ω₂ω
  Ω₂·2<Ω₂ω = mul<ω 2

  -- 一切级: 每级的闭项严格低于对角
  cum<∞ : ∀ k → asuc (T⁺ (cum k) (lcum k)) ≤ᴬ T∞
  cum<∞ k = fst< (cum k) (lcum k) Λ∞ lΛ∞ (cum⊏∞ k)

  lv≤cum : ∀ n → Tlv n ≤ᴬ T⁺ (cum n) (lcum n)
  lv≤cum zero = ≤-refl (Tlv 0)
  lv≤cum (suc n) = shift (cum n) (lcum n) (H (suc n)) (lgH (suc n))

  lv<∞ : ∀ n → asuc (Tlv n) ≤ᴬ T∞
  lv<∞ n = ≤-trans (s≤ (lv≤cum n)) (cum<∞ n)

  Ω₂<∞ : asuc T-Ω₂ ≤ᴬ T∞
  Ω₂<∞ = lv<∞ 0

  -- 回灌族
  fb₂< : ∀ n → asuc (T-fb₂ n) ≤ᴬ T-fb₂ (suc n)
  fb₂< n = fst< (proj₁ (Λs₂ n)) (proj₂ (Λs₂ n)) (proj₁ (Λs₂ (suc n))) (proj₂ (Λs₂ (suc n))) (fb₂⊏ n)

  fb₂<ω : ∀ n → asuc (T-fb₂ n) ≤ᴬ T-fb₂ω
  fb₂<ω n = fst< (proj₁ (Λs₂ n)) (proj₂ (Λs₂ n)) Λω₂ lΛω₂ (fb₂⊏ω n)

  -- 一级折叠的级顶
  cells<Tᵀ : ∀ n → asuc (T⁺ (cells n) (proj₂ (Lg-idx Ω₃) n)) ≤ᴬ Tᵀ
  cells<Tᵀ n = fst< (cells n) (proj₂ (Lg-idx Ω₃) n) (idx Ω₃) (Lg-idx Ω₃) (cells⊏ n)

  cells≤ : ∀ n → T⁺ (cells n) (proj₂ (Lg-idx Ω₃) n) ≤ᴬ T⁺ (cells (suc n)) (proj₂ (Lg-idx Ω₃) (suc n))
  cells≤ n = fst (cells n) (proj₂ (Lg-idx Ω₃) n) (cells (suc n)) (proj₂ (Lg-idx Ω₃) (suc n)) (cells-st n)

  Tᵀ<Tᵀ+1 : asuc Tᵀ ≤ᴬ Tᵀ+1
  Tᵀ<Tᵀ+1 = fst< (idx Ω₃) (Lg-idx Ω₃) (idx (hs Ω₃)) (Lg-idx (hs Ω₃)) idx⊏+1

  -- UIP 链
  x<Tᵁ : ∀ n → asuc (T⁺ (C₁.x n) (C₁.lx n)) ≤ᴬ Tᵁ
  x<Tᵁ n = fst< (C₁.x n) (C₁.lx n) C₁.Λᶜ C₁.lΛᶜ (x⊏ n)

  -- 外层世界 (0,ω) 上的同一条链: 与 Tᵁ 同值
  Tᵁω≤ : T⁺ Cω.Λᶜ Cω.lΛᶜ ≤ᴬ Tᵁ
  Tᵁω≤ = sim Cω.Λᶜ Cω.lΛᶜ C₁.Λᶜ C₁.lΛᶜ inω≈

  Tᵁ≤ω : Tᵁ ≤ᴬ T⁺ Cω.Λᶜ Cω.lΛᶜ
  Tᵁ≤ω = sim C₁.Λᶜ C₁.lΛᶜ Cω.Λᶜ Cω.lΛᶜ (≈-sym inω≈)

  -- Tᴰ₊: 每一项与 T-Ω₂ 同值, 整体与 Dg (常数 T-Ω₂) 同值
  t≤Ω₂ : ∀ k → t₊ k ≤ᴬ T-Ω₂
  t≤Ω₂ zero = sim (pr₀ (λh 0)) (Lg-pr₀ (λh 0) lλ₀) Ω₂ᴴ lΩ₂ pr₀-top
  t≤Ω₂ (suc k) = sim (prL (suc (suc k)) (λh (suc k))) (Lg-prL (suc (suc k)) (λh (suc k)) (Lg-λh (suc k))) Ω₂ᴴ lΩ₂ (in-suc k)

  Ω₂≤t : ∀ k → T-Ω₂ ≤ᴬ t₊ k
  Ω₂≤t zero = sim Ω₂ᴴ lΩ₂ (pr₀ (λh 0)) (Lg-pr₀ (λh 0) lλ₀) (≈-sym pr₀-top)
  Ω₂≤t (suc k) = sim Ω₂ᴴ lΩ₂ (prL (suc (suc k)) (λh (suc k))) (Lg-prL (suc (suc k)) (λh (suc k)) (Lg-λh (suc k))) (≈-sym (in-suc k))

  Tᴰ₊≤ : Tᴰ₊ ≤ᴬ Dg (λ _ → T-Ω₂)
  Tᴰ₊≤ = DgM t≤Ω₂

  ≤Tᴰ₊ : Dg (λ _ → T-Ω₂) ≤ᴬ Tᴰ₊
  ≤Tᴰ₊ = DgM Ω₂≤t
```
