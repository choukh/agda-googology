# 守卫的核心: 一步的定理

> 不含记号. 这几条都是对结构参数的一步定理, **不看折叠的规则**:
>
> - `≪→Fp`: $c\ll v$ 且 $v\approx\mathrm{rd}\,y$, 则 $c$ 在 $y$ 的第一位置. 这是 "链点是读出" 的全部用处.
> - `Bach`: 闭包的链上 $c\ll v_j$, 项 $t$ 在第一位置上压过第一支, 也压过低于 $c$ 的链点上的分支, 则 $c$ 在 $t$ 的计值里. 只用到 `tie`, 链点的第一位置 `lk`, 有界比较 `cmpN`.
> - `Vis-lift`: 目标 $k$ 的折叠的输出压过 $\Omega_k$ (`Ωfst`). 上下文对压过 $\Omega_k$ 的输入诚实, 就对 `ψ 0 k` 的任何输出诚实.
> - `mono₂`: 判断的论证用的上下文 $\psi_{0,0}\circ\psi_{1,0}$ 保第一位置 (`ψL′`).
>
> **这不是 `Hn` 在 Ω+1 的证明.** 缺的是把它们传过任意嵌套的上下文 (`os`, `add`, 输入). 见 [NoCumHn](NoCumHn.lagda.md).
>
> 全文 `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoCumHnCore where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; ⊲-tr; keep; rise; cmpN)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit
open import OCF.Align.NoCumW
open import OCF.Align.NoCumLe
open import OCF.Align.NoCumMain
open import OCF.Align.NoCumForce
```

## §1 `Bach`

```agda
≪→Fp : ∀ {c v} {y : Ord₀} → c ≪ v → v ≈ᴬ rd y → Fp c y
≪→Fp {y = FL.zero} C.zero ()
≪→Fp {y = FL.suc y} C.zero (s≈ e) = fs (fq e)
≪→Fp {y = FL.lim f} C.zero ()
≪→Fp {y = FL.limᵢ () f} C.zero e
≪→Fp {y = FL.up () x} C.zero e
≪→Fp {y = FL.zero} (C.suc r) ()
≪→Fp {y = FL.suc y} (C.suc r) (s≈ e) = fs (≪→Fp r e)
≪→Fp {y = FL.lim f} (C.suc r) ()
≪→Fp {y = FL.limᵢ () f} (C.suc r) e
≪→Fp {y = FL.up () x} (C.suc r) e
≪→Fp {y = FL.zero} (C.lim n r) ()
≪→Fp {y = FL.suc y} (C.lim n r) ()
≪→Fp {y = FL.lim f} (C.lim n r) (l≈ h) = fl n (≪→Fp r (h n))
≪→Fp {y = FL.limᵢ () f} (C.lim n r) e
≪→Fp {y = FL.up () x} (C.lim n r) e

module Chain {u} {x : 𝓡 u} {h : ∀ {v} → u ⊲ v → Gw v → 𝓡 v} (G₀ : G x)
  (vs : ℕ → A) (gv : ∀ n → Gw (vs n)) (up : ∀ n → u ⊲ vs n) (Gh : ∀ n → G (h (up n) (gv n)))
  (t₀ : vs 0 ≈ᴬ rd (force G₀)) (tS : ∀ n → vs (suc n) ≈ᴬ rd (force (Gh n)))
  (lk : ∀ n → vs n ⊲ vs (suc n)) where

  Bach : ∀ {w} {t : 𝓡 w} (d : G t) {c} → x ⊴ t → (∀ n → vs n ⊲ c → h (up n) (gv n) ⊴ t) → ∀ j → c ≪ vs j → Fp c (force d)
  Bach d fx fh zero r = Fp-mono (≪→Fp r t₀) (fo⊴ fx G₀ d)
  Bach d fx fh (suc i) r with cmpN r (lk i) (lgw (gv (suc i)))
  ... | keep s₁ = Bach d fx fh i s₁
  ... | rise q = Fp-mono (≪→Fp r (tS i)) (fo⊴ (fh i q) (Gh i) d)
```

## §2 下界在折叠下

```agda
Vis-lift : ∀ {p a u₀ k m} (gm : Gw m) (D : 𝓞 zero k m → 𝓡 m) →
           (∀ z → Ω̇at zero k gm ⊴ z → (d : G (D z)) → Fp k (force d)) →
           ∀ (w : 𝓞 p a u₀) (gu : Gw u₀) (um : u₀ ⊲ m) (tm : k ⊲ m) (am : a ⊲ m) (d : G (D (ψ zero k w gu m gm um tm am))) → Fp k (force d)
Vis-lift {k = k} gm D H w gu um tm am d = H _ (Ωfst zero k w gu _ gm um tm am) d

mono₂ : ∀ {b b′ w w′ m m′} {y : 𝓞 zero b w} {y′ : 𝓞 zero b′ w′} → y ⊴ y′ → (gw₁ : Gw w) (gw₂ : Gw w′) (gm : Gw m) (gm′ : Gw m′)
        (um : w ⊲ m) (am : b ⊲ m) (um′ : w′ ⊲ m′) (am′ : b′ ⊲ m′) (z₁ : azero ⊲ m) (z₂ : azero ⊲ m′) →
        ψ zero azero (ψ 1 azero y gw₁ m gm um z₁ am) gm m gm C.self z₁ z₁ ⊴ ψ zero azero (ψ 1 azero y′ gw₂ m′ gm′ um′ z₂ am′) gm′ m′ gm′ C.self z₂ z₂
mono₂ d gw₁ gw₂ gm gm′ um am um′ am′ z₁ z₂ =
  ψL′ zero azero (ψL′ 1 azero d gw₁ gw₂ _ gm um z₁ am _ gm′ um′ z₂ am′) gm gm′ _ gm C.self z₁ z₁ _ gm′ C.self z₂ z₂
```
