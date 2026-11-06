# 最高层含与站层号同形的层, 否定一路 (六): 头 3 的读回产出 `kTop3`

> 不含记号. 入口 [NegLamIso](NegLamIso.lagda.md). 只读导入构造一路的 [LamIsoTm](LamIsoTm.lagda.md), [LamIsoL](LamIsoL.lagda.md) (不改) 与否定一路旧文件 [NegLeanLvEmb](NegLeanLvEmb.lagda.md) 的 `kTop3`. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** 构造一路的头 $n$ 的读回 `Rown n` 沿 `L n` 与 `st n` 的忠实同形读进 `Lv (st n)` (嵌入 `idE`). 旧的主候选 `TVs` 的头 3 读不出 `kTop3` (`Lv (st 3)` 里坐标为 `HB (Lv (st 2))` 的种类; `NegLeanLvS.no-top3-RLs`). 本篇查新实例.
>
> **结果 (定理).**
>
> 1. **`rd-top3`** (`refl`, 对一切世界与界的证据): 过 `L 3` 的顶结点第 $1$ 支、内层结点第 $1$ 支、再减一 (那里是 `L 2`) 的结点, 经 `Rown 3` 读成 `kTop3` 的 $\Omega$-结点. 前提实例: 合法世界 `Wi` (`lWi`), 界的证据 `hself`; **`top3-has`**: `HasK kTop3` 成立. 所以头 3 的读回确实产出自己的级的高层种类, 对照 `no-top3-RLs`.
> 2. **`rd-br0`** (`refl`, 对构造一路 23:2x 版): 过 `L 3` 的顶结点第 $0$ 支**本身** (也是 `L 2`) 的结点也读成 `kTop3` 的 $\Omega$-结点 (`br0-has`). 历史: 23:0x 版里这里有损 (本篇当时的 `rd-br0-lossy`, `refl`, 编译过); 依 **`succ3`** (`Lv (ls (st 2))` 嵌进 `Lv (st 3)`, 新种类就是 `kTop3`, `succ3-k`) 的提示, 构造一路加了后继种类 `succE` (一切 $n$).
>
> **只否定什么.** 不否定; 都是正面的形状定理. 只对 $n=3$; 一般的 $n$ 未查 (构造一路另有 `LamIsoVal.rdΩd4`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLamIsoRd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanTTree
open import OCF.Lean.LeanFbIf
open import OCF.Lean.LeanFbSt using (SLs) renaming (st to stL)
open import OCF.Lean.LamIsoL using (L)
open import OCF.Lean.LamIsoTm using (Rown)
open import OCF.Lean.NegLeanLvEmb using (kTop3)
open import OCF.Lean.LeanLvIf using (HasK; here)
open import OCF.Lean.NegLamIsoPre using (g₃)
open Tree SLs

κ₁ κ₂ : K L₀
κ₁ = inj₁ (3 , inj₁ (inj₁ tt , inj₂ tt))
κ₂ = inj₁ (3 , inj₁ (inj₂ (hs hz) , (inj₁ tt , inj₂ tt)))

rd-top3 : ∀ {W} (lW : LgW L₀ W) (bd₁ : Bd L₀ κ₁ (hs hz) W) (bd₂ : Bd L₀ κ₂ (hs hz) W)
  (u : ∀ {W′} → W ≤ W′ → LgW L₀ W′ → D (L 2) W′ → D (L 3) W′) →
  Σ (_ → HB (Lv (stL 3))) (λ g → LvRd.δ (Rown 3) lW (ni (sL {c = hs hz} bd₁ (hLim {c = hs hz} bd₂ (hsuc hself))) u) ≡ hΩ kTop3 g)
rd-top3 lW bd₁ bd₂ u = _ , refl
```

**前提实例: 一个合法世界.** 第 3 站里, 左分量的界升到 $1$, 分量 `inj₂ 1` 的左分量的界升到 $1$, 其余取基世界.

```agda
h₁ : HB (Lv (ls lz)) → LH
h₁ c = ofHB (Ω̂ (hs hz) ⊞ ι {LH} {FL} (ls lz) (up c))

W31 : Wd (Lv (g₃ (hs hz)))
W31 (inj₁ tt) = w₀ (Lv (ls lz)) , hs hz
W31 (inj₂ c) = w₀ (Lv (h₁ c))

lW31 : LgW (Lv (g₃ (hs hz))) W31
lW31 (inj₁ tt) = lw₀ (Lv (ls lz)) , tt
lW31 (inj₂ c) = lw₀ (Lv (h₁ c))

W3 : Wd (Lv (stL 3))
W3 (inj₁ tt) = w₀ S⊥ , hs hz
W3 (inj₂ hz) = w₀ (Lv (g₃ hz))
W3 (inj₂ (hs hz)) = W31
W3 (inj₂ (hs (hs c))) = w₀ (Lv (g₃ (hs (hs c))))
W3 (inj₂ (hs (hl f))) = w₀ (Lv (g₃ (hs (hl f))))
W3 (inj₂ (hs (hΩ (() , _) g)))
W3 (inj₂ (hl f)) = w₀ (Lv (g₃ (hl f)))
W3 (inj₂ (hΩ (() , _) g))

lW3 : LgW (Lv (stL 3)) W3
lW3 (inj₁ tt) = (λ ()) , tt
lW3 (inj₂ hz) = lw₀ (Lv (g₃ hz))
lW3 (inj₂ (hs hz)) = lW31
lW3 (inj₂ (hs (hs c))) = lw₀ (Lv (g₃ (hs (hs c))))
lW3 (inj₂ (hs (hl f))) = lw₀ (Lv (g₃ (hs (hl f))))
lW3 (inj₂ (hs (hΩ (() , _) g)))
lW3 (inj₂ (hl f)) = lw₀ (Lv (g₃ (hl f)))
lW3 (inj₂ (hΩ (() , _) g))

open import OCF.Lean.LeanFbSt using (FS)

WS : Wd SLs
WS (suc (suc (suc zero))) = W3 , hz
WS zero = w₀ (FS 0)
WS (suc zero) = w₀ (FS 1)
WS (suc (suc zero)) = w₀ (FS 2)
WS (suc (suc (suc (suc m)))) = w₀ (FS (suc (suc (suc (suc m)))))

lWS : LgW SLs WS
lWS (suc (suc (suc zero))) = lW3 , tt
lWS zero = lw₀ (FS 0)
lWS (suc zero) = lw₀ (FS 1)
lWS (suc (suc zero)) = lw₀ (FS 2)
lWS (suc (suc (suc (suc m)))) = lw₀ (FS (suc (suc (suc (suc m)))))

Wi : Wd L₀
Wi = WS , hz

lWi : LgW L₀ Wi
lWi = lWS , tt

xi : D (L 3) Wi
xi = ni (sL {c = hs hz} hself (hLim {c = hs hz} hself (hsuc hself))) (λ _ _ _ → n0)

top3-has : HasK kTop3 (LvRd.δ (Rown 3) lWi xi)
top3-has with rd-top3 lWi hself hself (λ _ _ _ → n0)
... | g , e = subst (HasK kTop3) (sym e) here
```

**同一个子层, 另一条路径 (构造一路 23:2x 版).** 过 `L 3` 的顶结点第 $0$ 支**本身** (那一支就是 `L 2`) 的结点. 22:0x–23:0x 版里 `prtL 3` 的顶结点不带后继种类, 这样的结点有损 (本篇早先的 `rd-br0-lossy`, 那一版编译过). 构造一路按 `succ3` 的提示在一切 $n$ 加了后继种类 (`succE`), 现在它也读成 `kTop3` 的 $\Omega$-结点 (**`rd-br0`**, `refl`). `succ3` 留作对照: `Lv (ls (st 2))` 嵌进 `Lv (st 3)`, 新种类就是 `kTop3`.

```agda
open import OCF.Lean.LeanLvIf using (Emb; j)
open import OCF.Lean.LeanLvEmb using (supE; _∘E_)

rd-br0 : ∀ {W} (lW : LgW L₀ W) (bd : Bd L₀ κ₁ hz W)
  (u : ∀ {W′} → W ≤ W′ → LgW L₀ W′ → D (L 2) W′ → D (L 3) W′) →
  Σ (_ → HB (Lv (stL 3))) (λ g → LvRd.δ (Rown 3) lW (ni (sL {c = hz} bd hself) u) ≡ hΩ kTop3 g)
rd-br0 lW bd u = _ , refl

succ3 : Emb (Lv (ls (stL 2))) (Lv (stL 3))
succ3 = supE {⊤ ⊎ HB S⊥} {λ i → _} (inj₂ (hs hz)) ∘E supE {⊤ ⊎ HB (Lv (ls lz))} {λ i → _} (inj₂ (hs hz))

succ3-k : j succ3 (inj₂ tt) ≡ kTop3
succ3-k = refl

-- 前提实例: 底坐标总在界内
br0-has : HasK kTop3 (LvRd.δ (Rown 3) lWi (ni (sL {c = hz} (botBd L₀ κ₁ Wi) hself) (λ _ _ _ → n1)))
br0-has with rd-br0 lWi (botBd L₀ κ₁ Wi) (λ _ _ _ → n1)
... | g , e = subst (HasK kTop3) (sym e) here
```
