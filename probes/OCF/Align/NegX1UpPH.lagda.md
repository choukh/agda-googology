# X₁ 上叠层, 否定一路 (五): `PH` 对世界单调, 对 ⊞ 与链封闭; 第 0 世界的根部只容层号 1 的种类

> 不含记号. 入口 [NegX1Up](NegX1Up.lagda.md). 对 PathOut 的实例 `IX₁` 与它的 `PH` (只读导入 [PathOutX1](PathOutX1.lagda.md), [PathOutFold](PathOutFold.lagda.md)) 写; 不依赖叠层的接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** 叠层的上层折叠若以 $X_1$ 为目标, 它的输出 (一棵 `HB XS₁`) 要带路径 (`PH W₀`) 才能交给 `Ψ` (PathOut 接手清单第 1 条 (b)). 上层折叠用 $\boxplus$, `mul`, `chain`, `Σ⁺` 搭输出. 本篇问: 这些运算保 `PH` 吗? `PH W₀` 对输出的根部有什么限制?
>
> **结果.**
>
> 1. **`PH-mono` (定理).** $B\lhd B'$ 则 `PH B h → PH B′ h`. (PathOutX1 文首的判断, 这里是定理.)
> 2. **`PH-⊞` (定理).** `PH B a → PH B x → PH B (a ⊞ x)`, 对一切 $x$ (`NegPathOutInst.PH-⊞` 要 $x$ 不含 $\Omega_1$-结点; 有了 1 这个前提可以去掉: 进入 $x$ 的 $\Omega_1$-分支 $e$ 时 $a$ 要在世界 $e+1$ 里带路径, 由 $B\lhd e$ 与 1).
> 3. **`PH-mul`, `PH-Σ⁺`, `PH-chain` (定理).** 由 2. `chain` 要起点与每一步保 `PH`.
> 4. **`ph-root` (定理, 边界).** `PH W₀` (界 $1$) 下, 根部 (不在 $\Omega_1$-结点之内) 的种类 `(inj₂ y , κ)` 只能有 $y=0$. 所以上层折叠交给 `Ψ W₀` 的树, 根部只能有第 1 层的种类, 其余的种类都要在某个 $\Omega_1$-结点之内. 前提实例: `PathOut.topL` 的根是 $\Omega_1$-结点 (`PH-topL`); 反例 `bad₂` (根部是第 2 层的种类) 不满足 `PH W₀` (`¬PH-bad₂`), 但对界 $3$ 满足 (`PH-bad₂-3`).
>
> **只否定什么.** 4 只否定 "任意的 `HB XS₁` 都能在界 $1$ 的世界里交给 `Ψ`". **不否定**: 换更大的初始世界 (1 说路径对世界单调; 但 `Ψ` 的初始世界与目标的证据 `Tg` 一起选, 这里未讨论); 上层折叠的输出带路径 (2, 3 是构造; 全部的证明要构造一路的折叠). 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegX1UpPH where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥)
open import OCF.Align.TySupC using (Cd; LC)
open import OCF.Align.PathOutX1 using (IX₁; XS₁; κΩ)
open import OCF.Align.PathOutFold IX₁ using (PH)
open import OCF.Align.PathOut using (W₀; topL; PH-topL)
import OCF.Align.TySupFold as TF
open import OCF.Align.TySupSum using (ICdΣ)
open TF ICdΣ using (mul; chain; Σ⁺)
```

## §1 单调

```agda
PH-mono : ∀ {B B′} h → B ⊲[ tt ] B′ → PH B h → PH B′ h
PH-mono hz q ph = tt
PH-mono (hs h) q ph = PH-mono h q ph
PH-mono (hl f) q ph = λ n → PH-mono (f n) q (ph n)
PH-mono (hΩ (inj₁ _ , inj₁ ()) g) q ph
PH-mono (hΩ (inj₁ _ , inj₂ _) g) q (ev , k) = tt , (λ e a → k e (⊲ᴮ-tr q (proj₁ a) , proj₂ a))
PH-mono (hΩ (inj₂ y , κ) g) q (yb , k) = ⊲ᴮ-tr yb q , (λ e a → PH-mono (g e) q (k e a))
```

## §2 ⊞, `mul`, `Σ⁺`, `chain`

```agda
PH-⊞ : ∀ {B} a x → PH B a → PH B x → PH B (a ⊞ x)
PH-⊞ a hz pa px = pa
PH-⊞ a (hs x) pa px = PH-⊞ a x pa px
PH-⊞ a (hl f) pa px = λ n → PH-⊞ a (f n) pa (px n)
PH-⊞ a (hΩ (inj₁ _ , inj₁ ()) g) pa px
PH-⊞ a (hΩ (inj₁ _ , inj₂ _) g) pa (ev , k) =
  tt , (λ e a′ → PH-⊞ a (g e) (PH-mono a (⊲ᴮ-tr (proj₁ a′) (hsuc hself)) pa) (k e a′))
PH-⊞ a (hΩ (inj₂ y , κ) g) pa (yb , k) = yb , (λ e a′ → PH-⊞ a (g e) pa (k e a′))

PH-mul : ∀ {B} x → PH B x → ∀ n → PH B (mul x n)
PH-mul x px zero = px
PH-mul x px (suc n) = PH-⊞ (mul x n) x (PH-mul x px n) px

PH-Σ⁺ : ∀ {B} f → (∀ n → PH B (f n)) → ∀ n → PH B (Σ⁺ f n)
PH-Σ⁺ f pf zero = pf 0
PH-Σ⁺ f pf (suc n) = PH-⊞ _ (f (suc n)) (PH-Σ⁺ f pf n) (pf (suc n))

PH-chain : ∀ {B} b k → PH B b → (∀ c → PH B c → PH B (k c)) → ∀ n → PH B (chain b k n)
PH-chain b k pb pk zero = pk b pb
PH-chain b k pb pk (suc n) =
  PH-⊞ _ _ (PH-chain b k pb pk n) (pk _ (PH-⊞ b _ pb (PH-chain b k pb pk n)))
```

## §3 第 0 世界的根部

```agda
ph-root : ∀ y κ g → PH W₀ (hΩ (inj₂ y , κ) g) → y ≡ hz
ph-root y κ g (hself , _) = refl
ph-root y κ g (hsuc () , _)

-- 反例: 根部是第 2 层的种类 (y = 1)
bad₂ : HB XS₁
bad₂ = hΩ (inj₂ (hs hz) , inj₂ tt) (λ _ → hz)

¬PH-bad₂ : ¬ PH W₀ bad₂
¬PH-bad₂ ph with ph-root (hs hz) (inj₂ tt) (λ _ → hz) ph
... | ()

PH-bad₂-3 : PH (hs (hs (hs hz))) bad₂
PH-bad₂-3 = hsuc hself , (λ _ _ → tt)

-- 前提实例: topL 的根是 Ω₁-结点
topL-root : PH W₀ topL
topL-root = PH-topL W₀
```

## 结论 (按档)

- **[定理]** **`PH-mono`**, **`PH-⊞`**, `PH-mul`, `PH-Σ⁺`, **`PH-chain`**; **`ph-root`**, `bad₂`, **`¬PH-bad₂`**, `PH-bad₂-3`, `topL-root`.
- **[判断]** 上层折叠的输出能否满足 `PH W₀`, 取决于它的根部形状 (4) 与链的起点 (`NegX1UpFlat`); 要构造一路的折叠.
