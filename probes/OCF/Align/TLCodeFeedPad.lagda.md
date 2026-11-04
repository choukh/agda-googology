# 严格列 (九): 有累加的 `Out`, 复现 `T⊤`

> 入口 [TLCode](TLCode.lagda.md). **判决: HOLDS (编译过, 无条件), 但这是探路, 累加都在 `padO` 里.** `padO`: $\mathrm{out}(c)$ 取 `lv₀ ⌈ ly c ⌉`, 就是 [CrossMNode](CrossMNode.lagda.md) 的 `⌈_⌉` 换成带证书的写法. 这个文件的导入闭包含 `Code`, `⌈_⌉`.
>
> - `T⊤ᵖ`, `fgh⊤ᵖ`: 证据的链上的闭项.
> - `same-T⊤ : T⊤ᵖ ≅ T⊤`, `same-fgh`: 与已有的 `T⊤` 计值 $\cong$, FGH 逐点相等.
> - `pad~`: 新链与旧链每一项逐块同形. 这说明 `C` 的 `ᶜ+` 就是 $\oplus$ (`⊕~`), 真正的累加只有 `⌈_⌉`.
>
> 所以 `T⊤` 是 [TLCodeFeed](TLCodeFeed.lagda.md) 的一个实例, 去累加只剩下一个问题: 换掉 `padO`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLCodeFeedPad where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level hiding (up; sim; out; acc)
open import OCF.Free.Prefix using (Z; toZ)
open import OCF.Free.Force using (Goodᴺ; forceᴺ; forceᴺ-HS)
open import OCF.Free.Class using (lvG)
open import OCF.Align.TLCodeShape using (Sh; sz; ss; sl; end)
open import OCF.Align.TLCodeLit
open import OCF.Align.TLCodeLe
open import OCF.Align.TLCodeArith using (_⊕_; L⊕; ⊕-path)
open import OCF.Align.TLCodeCert using (Gᴸ; Tᴸ; ev₀; val≼ᴸ)
import OCF.Align.LadderOrdPos as B
open import OCF.Align.TLCodeBridge
open import OCF.Align.TLCodeAccept using (lv₀; Lv; lv-shape; lv-exact; old→new; Lω~)
open import OCF.Align.TLCodeFeed
open import OCF.Align.TLCodeArith using (Lω)
open import OCF.Align.LadderOrdPos using (Code; cz; cs; cl)
open import OCF.Align.LadderOrdCode using (⌈_⌉; dom₀; _ᶜ+_; ωᶜ)
open import OCF.Align.LadderOrdCert using (Gᵖ; Tᵖ)
open import OCF.Align.CrossMNode using (Node; node; νT; Gbr) renaming (C to Cᴼ)
open import OCF.Align.CrossMInst using (𝒯)
open import OCF.Align.CrossMClosed using () renaming (T⊤ to T⊤ᴼ)
```

## §1 $\oplus$ 与 `ᶜ+`

```agda
above⊕ : ∀ {a x t} (ha : Lit a) (ht : Lit t) (q : x <ᴵ t) {c} → above ht q ~ c → above (L⊕ ha ht) (⊕-path a q) ~ c
above⊕ ha (ls ht) zero ~z = ~z
above⊕ ha (ls ht) (suc q) (~s r) = ~s (above⊕ ha ht q r)
above⊕ ha (ll hf hr) (lim j q) (~l R) = ~l (λ { zero → above⊕ ha (hf j) q (R 0) ; (suc i) → above⊕ ha (hf (suc i + j)) (hr (i + j)) (R (suc i)) })

⊕~ : ∀ {a b A B} (ha : Lit a) (hb : Lit b) → shape ha ~ A → shape hb ~ B → shape (L⊕ ha hb) ~ A ᶜ+ B
⊕~ ha lz ra ~z = ra
⊕~ ha (ls hb) ra (~s rb) = ~s (⊕~ ha hb ra rb)
⊕~ ha (ll hf hr) ra (~l R) = ~l (λ { zero → ⊕~ ha (hf 0) ra (R 0) ; (suc i) → above⊕ ha (hf (suc i + 0)) (hr (i + 0)) (R (suc i)) })

~≈ : ∀ {s a b} → a ≅ᴵ b → s ~ ⌈ a ⌉ → s ~ ⌈ b ⌉
~≈ z≅ r = r
~≈ (s≅ e) (~s r) = ~s (~≈ e r)
~≈ (l≅ h) (~l R) = ~l (λ i → ~≈ (h i) (R i))
```

## §2 有累加的 `Out`, 与 `T⊤` 同值

对节点和证书都抽象着证, 检查器不展开闭包定理.

```agda
pad≼ : ∀ η → η ≼ lv₀ ⌈ η ⌉
pad≼ η = ≼-trans (old→new (dom₀ η)) (proj₂ (lv-exact ⌈ η ⌉))

M₀ : LC
M₀ = lc _ Lω

module Gen (br : LC → Z) (G : ∀ c → Goodᴺ (br c)) (u≺ : ∀ c d → forceᴺ _ (G c) ≺ forceᴺ _ (G (c ⊞ d))) (val≼ : ∀ c → ⟦ c ⟧ ≼ lvG (G c))
           (𝒩 : Node) (H : ∀ c M → shape (cert c) ~ M → forceᴺ _ (G c) ≅ forceᴺ _ (Gbr 𝒩 M)) where
  open Chain br G u≺ val≼

  padO : Out
  padO = mkOut (λ c → lc (lv₀ ⌈ ly c ⌉) (Lv ⌈ ly c ⌉)) (λ c → pad≼ (ly c))

  Cn : ℕ → LC
  Cn = C padO M₀

  CO : ℕ → Code
  CO = Cᴼ 𝒩 ωᶜ

  pad~ : ∀ n → shape (cert (Cn n)) ~ CO n
  pad~ zero = Lω~
  pad~ (suc n) = ⊕~ (cert (Cn n)) (ls (Lv ⌈ ly (Cn n) ⌉)) (pad~ n)
    (~s (~≈ (toLevel-≅ (forceᴺ-HS _ (G (Cn n))) (forceᴺ-HS _ (Gbr 𝒩 (CO n))) (H (Cn n) (CO n) (pad~ n))) (lv-shape ⌈ ly (Cn n) ⌉)))

  same : T⊤ padO M₀ ≅ νT 𝒩 ωᶜ
  same = l≅ (λ n → H (Cn n) (CO n) (pad~ n))

Hᵀ : ∀ c M → shape (cert c) ~ M → forceᴺ _ (Gᴸ (cert c) end zero) ≅ forceᴺ _ (Gᵖ M B.end zero)
Hᵀ c M r = Br.val≅ (cert c) r end zero

module GI = Gen (λ c → toZ (Tᴸ (cert c) end zero ev₀ zero)) (λ c → Gᴸ (cert c) end zero) up≺ᶜ (λ c → val≼ᴸ (cert c)) 𝒯 Hᵀ

padO : 𝕋ʷ.Out
padO = GI.padO

T⊤ᵖ : Ordᶜ zero
T⊤ᵖ = 𝕋ʷ.T⊤ padO M₀

fgh⊤ᵖ : ℕ → ℕ
fgh⊤ᵖ = FGH T⊤ᵖ

same-T⊤ : T⊤ᵖ ≅ T⊤ᴼ
same-T⊤ = GI.same

same-fgh : ∀ n → fgh⊤ᵖ n ≡ FGH T⊤ᴼ n
same-fgh = FGH-≅ same-T⊤
```
