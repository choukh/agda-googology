# X₁ 上叠层, 否定一路 (四): `correct` 不管读回 (PathOut 接口上)

> 不含记号. 入口 [NegX1Up](NegX1Up.lagda.md). 对 [PathOutIf](PathOutIf.lagda.md) (只读导入) 写; 回应 [PathOut](PathOut.lagda.md) 接手清单第 4 条 ("`correct` 的盲区: `same` 的 `to` 可以是常值而 `correct` 仍成立; 可请否定一路对它写盲定理"). 叠层的接口若沿用 `OkP` 形状的 `correct`, 本篇的构造逐字适用 (接口定稿后在实例检查里写). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **结果.**
>
> 1. **`constPay`, `ok-constPay` (定理, 对一切决定).** 把决定的读回 (`keep` 的 `fr`, `same` 与 `above` 的 `to`) 一律换成常值 `bot`, 标签与层号不变; `OkP` 只看标签与层号, 所以仍成立.
> 2. **`constPayOf` (构造, 盲; 对一切实例).** 实例的 `dec` 换成 `constPay ∘ dec`, `correct` 由 1 得到, 其余字段不动, 仍是实例. 推论: 接口的 `correct` 不约束 "留下的结点的分支取输入的哪个分支", 也不约束 "同层的链把什么喂给分支".
> 3. **`IX₁k`, `TXLk`, `LgB-TXLk` (定理, 盲).** 在 PathOut 的实例 `IX₁` 上做 2, 同一闭项公式 (输入合法的地板 `topL`) 也有 `LgB` 证书. 根结点的决定是 `same` 加常值读回 (`dec-root-k`, refl): 同层的链 `chain hz k` 的每一步都在同一坐标 `shift W₀ κΩ hz` 处取分支.
>
> **前提实例.** 1, 2: 任一实例, 例如 `IX₁`. 3: 无额外前提.
>
> **只否定什么.** 只否定 "`correct` 加 `Sh`/`LgB` 证书保证读回取对了分支". **不否定**: `IX₁` 的 `correct₁` 与它的读回 (构造一路的定义, 读回是恒等); 增补一条关于读回的律 (例如 "`same` 的 `to` 是恒等搬运", 或 "`to` 单调且共尾"; 判断: 这是值不变所需). `TXLk ≢ TXL` 本篇未证 (要展开两个 $\Psi$, 判断它们不同). 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegX1UpPay where

open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥)
open import OCF.Align.TySupC using (LC)
open import OCF.Align.TySupSum using (topΣ)
open import OCF.Align.PathOutIf
open import OCF.Align.PathOutX1 using (IX₁; XS₁; κΩ)
open import OCF.Align.PathOut using (W₀; lW₀; topL; gt; TXL; sh→lgB₁)
import OCF.Align.PathOutFold as PF
```

## §1 常值读回

```agda
constPay : ∀ {C L _⊑_ LgC XS Tn t κ} → DcP {C} L _⊑_ LgC XS Tn t κ → DcP L _⊑_ LgC XS Tn t κ
constPay {XS = XS} {κ = κ} (keep κ′ fr) = keep κ′ (λ _ → bot XS κ)
constPay {XS = XS} {κ = κ} (same to) = same (λ _ → bot XS κ)
constPay {XS = XS} {κ = κ} (above i q li ti to) = above i q li ti (λ _ → bot XS κ)

ok-constPay : ∀ {C L _⊑_ LgC XS Tn t κ} (_⊏_ : C → C → Set) j (d : DcP {C} L _⊑_ LgC XS Tn t κ) →
  OkP _⊏_ j d → OkP _⊏_ j (constPay d)
ok-constPay _⊏_ j (keep _ _) o = o
ok-constPay _⊏_ j (same _) o = o
ok-constPay _⊏_ j (above _ _ _ _ _) o = o

constPayOf : PathOutIf → PathOutIf
constPayOf P = record
  { R = R ; XS = XS ; Wo = Wo ; LgWo = LgWo ; Tg = Tg ; Ev = Ev ; Adm = Adm ; nxt = nxt
  ; lg-nxt = lg-nxt ; tg-nxt = tg-nxt ; shift = shift ; adm-shift = adm-shift ; lvX = lvX
  ; dec = λ W t lW pt κ ev → constPay (dec W t lW pt κ ev)
  ; correct = λ W t lW pt κ ev → ok-constPay _ (lvX κ) (dec W t lW pt κ ev) (correct W t lW pt κ ev) }
  where open PathOutIf P
```

## §2 在 `IX₁` 上

`PH` 是另一个模块实例里的递归定义 (证据, 可入, 新世界都不变), 照 `PathOut.PH-gt`, `PH-topL` 重写一遍.

```agda
IX₁k : PathOutIf
IX₁k = constPayOf IX₁

open PF IX₁k using () renaming (PH to PHk; Ψ to Ψk; Sh-Ψ to Sh-Ψk)

PHk-⊞ι : ∀ {W} a c (h : HB (LC (hs c))) → PHk W a → hs c ⊲[ tt ] W → PHk W (a ⊞ ι (inj₂ c) h)
PHk-⊞ι a c hz pa q = pa
PHk-⊞ι a c (hs h) pa q = PHk-⊞ι a c h pa q
PHk-⊞ι a c (hl f) pa q = λ n → PHk-⊞ι a c (f n) pa q
PHk-⊞ι a c (hΩ κ g) pa q = q , (λ e _ → PHk-⊞ι a c (g e) pa q)

PHk-gt : ∀ y W → y ⊲[ tt ] W → PHk W (gt y)
PHk-gt hz W q = tt
PHk-gt (hs c) W q = PHk-⊞ι (gt c) c (topΣ (hs c)) (PHk-gt c W (⊲ᴮ-tr (hsuc hself) q)) q
PHk-gt (hl f) W q = λ n → PHk-gt (f n) W (⊲ᴮ-tr (hlim n hself) q)
PHk-gt (hΩ () _) W q

PHk-topL : ∀ B → PHk B topL
PHk-topL B = tt , (λ y a → PHk-gt y (hs y) (hsuc hself))

TXLk : HB S⊥
TXLk = Ψk W₀ lW₀ hz (z⊲ᴮ W₀) hz topL (PHk-topL W₀)

LgB-TXLk : LgB TXLk
LgB-TXLk = sh→lgB₁ TXLk (Sh-Ψk W₀ lW₀ hz (z⊲ᴮ W₀) hz topL (PHk-topL W₀))
```

**同层的链喂常值.** 根结点 ($\Omega_1$ 种类, 目标 $0$) 在 `IX₁k` 里的决定是 `same` 加常值读回 (refl); 所以 `PathOutFold.Ψ` 的同层子句里, 链的每一步都在同一坐标 `shift W₀ κΩ hz` 处取分支 (由 `Ψ` 的定义).

```agda
dec-root-k : PathOutIf.dec IX₁k W₀ hz lW₀ (z⊲ᴮ W₀) κΩ tt ≡ same (λ _ → hz)
dec-root-k = refl
```

## 结论 (按档)

- **[定理]** `constPay`, **`ok-constPay`**; `PHk-⊞ι`, `PHk-gt`, `PHk-topL`, `TXLk`, **`LgB-TXLk`**, **`dec-root-k`**.
- **[构造, 盲]** **`constPayOf`** (对一切实例), `IX₁k`.
- **[判断]** 建议增补关于读回的律; `TXLk ≢ TXL`.
