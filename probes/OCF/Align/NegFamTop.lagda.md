# 族增量世界上的真折叠, 否定一路 (三): 级顶的压回只由采样映射决定

> 不含记号. 入口 [NegFam](NegFam.lagda.md). 对着接口 [FamFoldIf](FamFoldIf.lagda.md) ("接口定稿 2026-11-05 11:20 (编译通过)", 变更记录: 无) §4 的 `Input₁`, `NotPressed` 写. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> `TdPlusVal.pr-top`, `UipFbTop.pr₂-top` 的压回来自投影 `pr₂`: 新种类 (坐标 `HB S₁`) 的 $\Omega$-节点只在 $H_0$ 的嵌入 `up h` 处取分支. 本篇把这件事一般化: 称输入 `inp : Input₁` 是 **以 $e$ 采样的局部输入** (`Local inp e`), 若它在旧种类上与 `up` 互逆 (`l-up`), 并把新种类的节点 $\mathrm{h\Omega}\,\kappa_2\,g$ 送到 $\mathrm{h\Omega}\,\kappa_H\,(h\mapsto \mathrm{inp}(g(e\,h)))$ (`l-new`), 其中 $e : H_0\to$ `HB S₁` 是采样映射.
>
> **定理.**
>
> 1. **`local-top`**: 局部输入把级顶 `Ωtop S₁` 送到与 $\mathrm{h\Omega}\,\kappa_H\,e$ 互模拟的高度. 所以级顶的输入**就是采样映射本身**.
> 2. **`pressed⇔`**: 级顶被压回 (`inp (Ωtop S₁) ≈ Ω₂ᴴ`) 当且仅当 $e$ 逐点与 `up` 互模拟. **`never-up`**: 局部输入的级顶从不与 $H_0$ 嵌入互模拟. 合起来 **`notPressed⇔`**: `NotPressed inp` 当且仅当 $\neg\forall h.\ e\,h\approx \mathrm{up}\,h$.
> 3. 实例: `pr₂` 是以 `up` 采样的局部输入 (`local-pr₂`), 所以被压回 (`pressed-pr₂`, 重得 `pr₂-top`). 以 $e_+(h) = \Omega_2^H\boxplus \mathrm{up}\,h$ 采样的局部输入 `prE e₊` **不被压回** (`notPressed-e₊`, 定理).
>
> **这说明什么.** 接口的 `NotPressed` 只是关于输入函数在一个点上的形状; 它**不含合法性**. 第 3 条说它可以被一个只改采样映射的投影满足, 而这个投影是否保合法 (在两种种类折叠的一致世界里, 新种类有界的坐标都是 $H_0$ 的嵌入, `TdPlusVal.top-bd`/`TdPlusUni.up-inv`; $e_+$ 的值不在这个像里) 本篇没有证, 也没有否 (判断: 多半不保, 因为 `Lg-pr₂` 的证明正是靠 $e=$ `up` 才把世界搬过去). 所以 **`NotPressed` 不足以当作 "不被压回" 的验收**: 要连同 `Lg (T⁺ (inp Λ) _)` 一类的合法性一起要求, 并对 $e$ 的像在一致世界里有界给出理由. 本篇不否定任何构造; 只否定 "局部输入以 `up` 采样而不被压回" (`pressed⇔` 的一个方向).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegFamTop where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.HtTowerFTree using (S₁; H₀; Ht; κA; κH)
open import OCF.Align.HtTowerFClosed using (Ω₂ᴴ)
open import OCF.Align.DiagK3Zero using (_≈_; ≈z; ≈s; ≈l; ≈Ω)
open import OCF.Align.TdPlusVal using (≈-trans; ≈-refl)
open import OCF.Align.UipFbTop using (pr₂; pr₂-up)
open import OCF.Align.FamFoldIf using (S₂; κ₂; Input₁; NotPressed; Sk; Down; DownStep; TowerDown)
```

## §1 局部输入

```agda
record Local (inp : Input₁) (e : H₀ → Ht) : Set where
  field
    l-up  : ∀ (y : Ht) → inp (up y) ≈ y
    l-new : ∀ (g : Ht → HB S₂) → inp (hΩ κ₂ g) ≡ hΩ κH (λ h → inp (g (e h)))
open Local public

≈-sym : ∀ {S} {x y : HB S} → x ≈ y → y ≈ x
≈-sym ≈z = ≈z
≈-sym (≈s p) = ≈s (≈-sym p)
≈-sym (≈l p) = ≈l (λ n → ≈-sym (p n))
≈-sym (≈Ω p) = ≈Ω (λ c → ≈-sym (p c))

local-top : ∀ {inp e} → Local inp e → inp (Ωtop S₁) ≈ hΩ κH e
local-top {inp} {e} L =
  subst (λ t → t ≈ hΩ κH e) (sym (l-new L up)) (≈Ω (λ h → l-up L (e h)))
```

## §2 压回当且仅当采样映射是 `up`

```agda
invΩ : ∀ {f g : H₀ → Ht} → _≈_ {S₁} (hΩ κH f) (hΩ κH g) → ∀ h → f h ≈ g h
invΩ (≈Ω p) = p

pressed⇔ : ∀ {inp e} → Local inp e →
  ((inp (Ωtop S₁) ≈ Ω₂ᴴ) → ∀ h → e h ≈ up h) × ((∀ h → e h ≈ up h) → inp (Ωtop S₁) ≈ Ω₂ᴴ)
pressed⇔ L =
  (λ q → invΩ (≈-trans (≈-sym (local-top L)) q)) ,
  (λ q → ≈-trans (local-top L) (≈Ω q))

never-up′ : ∀ (e : H₀ → Ht) (h : H₀) → ¬ (hΩ κH e ≈ up h)
never-up′ e hz ()
never-up′ e (hs h) ()
never-up′ e (hl f) ()
never-up′ e (hΩ κ g) ()

never-up : ∀ {inp e} → Local inp e → ∀ h → ¬ (inp (Ωtop S₁) ≈ up h)
never-up {e = e} L h q = never-up′ e h (≈-trans (≈-sym (local-top L)) q)

notPressed⇔ : ∀ {inp e} → Local inp e →
  (NotPressed inp → ¬ (∀ h → e h ≈ up h)) × (¬ (∀ h → e h ≈ up h) → NotPressed inp)
notPressed⇔ L =
  (λ np q → proj₁ np (proj₂ (pressed⇔ L) q)) ,
  (λ nq → (λ q → nq (proj₁ (pressed⇔ L) q)) , never-up L)
```

## §3 实例

**`pr₂` 以 `up` 采样**, 所以被压回.

```agda
local-pr₂ : Local pr₂ up
local-pr₂ = record { l-up = pr₂-up ; l-new = λ g → refl }

pressed-pr₂ : pr₂ (Ωtop S₁) ≈ Ω₂ᴴ
pressed-pr₂ = proj₂ (pressed⇔ local-pr₂) (λ h → ≈-refl (up h))
```

**一般的采样投影 `prE e`**; 以 $e_+ (h) = \Omega_2^H \boxplus \mathrm{up}\,h$ 采样的不被压回.

```agda
module _ (e : H₀ → Ht) where
  prE : HB S₂ → Ht
  prE hz = hz
  prE (hs x) = hs (prE x)
  prE (hl f) = hl (λ n → prE (f n))
  prE (hΩ (inj₁ κ) g) = hΩ κ (λ c → prE (g c))
  prE (hΩ (inj₂ tt) g) = hΩ κH (λ h → prE (g (e h)))

  prE-up : ∀ (y : Ht) → prE (up y) ≈ y
  prE-up hz = ≈z
  prE-up (hs y) = ≈s (prE-up y)
  prE-up (hl f) = ≈l (λ n → prE-up (f n))
  prE-up (hΩ κ g) = ≈Ω (λ c → prE-up (g c))

  local-prE : Local prE e
  local-prE = record { l-up = prE-up ; l-new = λ g → refl }

e₊ : H₀ → Ht
e₊ h = Ω₂ᴴ ⊞ up h

e₊-not-up : ¬ (∀ h → e₊ h ≈ up h)
e₊-not-up q with q hz
... | ()

notPressed-e₊ : NotPressed (prE e₊)
notPressed-e₊ = proj₂ (notPressed⇔ (local-prE e₊)) e₊-not-up
```

## §4 接口 §5 的类型不带内容

`Down S` 只要求下降的值合法, 常值 $0$ 就满足; 所以 `DownStep`, `TowerDown` 平凡地有实例. 要它们说明 "一切级" 的折叠, 还要加律 (例如在嵌入 `up` 上互逆, 或单调), 接口目前没有.

```agda
downZ : ∀ S → Down S
downZ S = record { down = λ _ → hz ; lg-down = λ _ → tt }

downStep-triv : DownStep
downStep-triv k _ = downZ (Sk (suc (suc k)))

towerDown-triv : TowerDown
towerDown-triv k = downZ (Sk (suc k))
```

## §5 结论 (按档)

- **[定理]** `local-top`, **`pressed⇔`**, `never-up`, **`notPressed⇔`**: 局部输入的级顶就是采样映射; 压回当且仅当采样映射逐点是 `up`.
- **[定理]** `local-pr₂`, `pressed-pr₂`: `pr₂` 的压回 (`pr₂-top`) 是 `pressed⇔` 的特例.
- **[定理]** `local-prE`, `e₊-not-up`, **`notPressed-e₊`**: 接口的 `NotPressed` 可以由只换采样映射的投影满足.
- **[定理]** `downZ`, `downStep-triv`, `towerDown-triv`: 接口 §5 的 `Down`, `DownStep`, `TowerDown` 由常值 $0$ 平凡满足.
- **[判断]** `prE e₊` 多半不保合法 (两种种类折叠的一致世界里新种类有界的坐标只有 `up` 的像); 未证, 未否. 所以 `NotPressed` 要连同合法性一起作验收.
