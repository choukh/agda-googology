# LamIso (二): 各站的同形层 `L n`, 新最高层 $\Lambda'$

> 不含记号. 入口 [LamIso](LamIso.lagda.md), 接口 [LamIsoIf](LamIsoIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> **层 `L n`** (对 $n$ 递归, 对一切 $n$):
>
> - `L 0 = 0`, `L 1 = 1`.
> - `L (2+n)`: 顶结点的种类是**第 $2+n$ 站自己**的种类 `(inj₁ tt , inj₂ tt)` (`Lv (st (2+n))` 的左分量 `step S⊥` 的新种类, 坐标 `HB S⊥`); 第 $c$ 支是 [LamIsoPsi](LamIsoPsi.lagda.md) 的 $\Psi_n$, 前缀是 `L (1+n)`, 提供者是第 $2+n$ 站的分量 `inj₂ (c+1)` (`Sr n`). 于是 `L (2+n)` 的一切 $\Omega$-结点的种类都是第 $2+n$ 站自己的种类, 外加前缀 `L (1+n)` 里的 (逐项继承).
>
> **为什么合法.** 顶结点: 界内 $c\lhd c'$ 给出 $\Psi_n(c)\lhd\Psi_n(c')$ (`Ψ-mono`, `HB S⊥` 上的路径不看世界). 第 $0$ 支以 `L (1+n)` 为前缀 (`Ψ-fst`), 所以 `L (1+n) ⊲ L (2+n)` 对一切世界 (`L-st`, 走底坐标), $\Lambda_L = \sup_n$ `L n` 合法.
>
> **新最高层** $\Lambda' = \Lambda_L\boxplus\Lambda_F$. `L n` 是 $\Lambda'$ 的字面第一位置 (对一切世界); 原 `ΛF` 接在后面, 站的头 `νS m` 的 $\Omega$-结点仍出现在 $\Lambda'$ 里 (判断: 不接 `ΛF` 时, 第 $m\ge1$ 站的头不出现在最高层里, 头的回灌不触发).
>
> **与 `st n` 忠实同形** (`prtL`): 经 `tw-eq` (`tw (2+n)` 的第 $c$ 支是 $\hat\Omega^n(1\boxplus c)$, 对 $n$ 归纳, 每步 `cong Ω̂`) 与 `Prt-Ψ`. 一切顶结点的第 $c$ 支带后继种类 (第 $c+1$ 支里的 `succE`; 头 2 时同 `LeanLvTmS.σ₂⁺`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LamIsoL where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanFbSt using (FS; SLs; ΛF; lΛF) renaming (st to stL)
open import OCF.Lean.LeanLvIf using (Emb; j; cv; π; lgπ; bd→; pr→)
open import OCF.Lean.LeanLvEmb using (stepE; supE; _∘E_; botE)
open import OCF.Lean.LamIsoIf using (Prt; pz; ps; pl; pΩ; LamIso)
open import OCF.Lean.LamIsoPsi SLs
```

## §1 站自己的种类, `tw` 的形状

```agda
Est : ∀ m → Emb (Lv (stL m)) X
Est m = stepE ∘E supE {ℕ} {FS} m ∘E stepE

tw-eq : ∀ n → tw (suc (suc n)) ≡ hΩ (νL lz) (λ c → it n (hs hz ⊞ ι lz (up c)))
tw-eq zero = refl
tw-eq (suc n) = cong Ω̂ (tw-eq n)

tw1 : ∀ n → tw (suc n) ≡ it n (hs hz)
tw1 zero = refl
tw1 (suc n) = cong Ω̂ (tw1 n)

g₀ : ℕ → HB S⊥ → LH
g₀ n c = ofHB (it n (hs hz ⊞ ι lz (up c)))

Gt : ∀ n → Emb (Lv (lΩ lz (g₀ n))) X
Gt n = subst (λ H → Emb (Lv (ofHB H)) X) (tw-eq n) (Est (suc (suc n)))

Et : ∀ n → Emb (FL lz) X
Et n = Gt n ∘E lft lz (g₀ n)

Sr : ∀ n → Src n (hs hz) lz
Sr n c = Gt n ∘E rgt lz (g₀ n) (hs c)
```

## §2 层与合法

```agda
L : ℕ → HB X
L zero = hz
L (suc zero) = hs hz
L (suc (suc n)) = hΩ (j (Et n) (inj₂ tt)) (λ c → Ψ n (L (suc n)) (Sr n) botE (cv (Et n) {inj₂ tt} c))

Lg-L : ∀ n → LgB (L n)
Lg-L zero = tt
Lg-L (suc zero) = tt
Lg-L (suc (suc n)) =
  (λ lw e e′ p → Ψ-mono n (L (suc n)) (Sr n) botE (⊲ᴮ↑ (λ ()) (pr→ (Et n) p))) ,
  (λ {w} {c} lw e → Lg-Ψ n (L (suc n)) (Sr n) botE (Lg-L (suc n)) (cv (Et n) c)
     (lgB⊲ (bd→ (Et n) e) (proj₁ (lgπ (Et n) lw)) (proj₂ (lgπ (Et n) lw))))

L-st : ∀ n {w} → L n ⊲[ w ] L (suc n)
L-st zero = hsuc hself
L-st (suc n) {w} = hLim (botBd X (j (Et n) (inj₂ tt)) w) (Ψ-fst n (L (suc n)) (Sr n) botE _)

ΛL : HB X
ΛL = hl L

Lg-ΛL : LgB ΛL
Lg-ΛL = (λ n → L-st n) , Lg-L

Λ′ : HB X
Λ′ = ΛL ⊞ ΛF

lΛ′ : LgB Λ′
lΛ′ = Lg-⊞ ΛL ΛF Lg-ΛL lΛF

L⊲ : ∀ n {w} → L n ⊲[ w ] Λ′
L⊲ n = ⊲ᴮ-tr (hlim n hself) (⊞-fst ΛL ΛF)

one′ : ∀ {w} → hs hz ⊲[ w ] Λ′
one′ = L⊲ 1
```

## §3 忠实同形, 接口实例

```agda
skL : ∀ n (c : E (FL lz) (inj₂ tt)) → Emb (Lv (ls (g₀ n c))) (Lv (lΩ lz (g₀ n))) ⊎ ⊤
skL n c = inj₁ (rgt lz (g₀ n) (hs c) ∘E succE n (hs hz ⊞ ι lz (up c)))

prtL : ∀ n → Prt SLs (L n) (stL n)
prtL zero = pz
prtL (suc zero) = ps pz
prtL (suc (suc n)) =
  subst (λ H → P⟨ L (suc (suc n)) ⟩ H) (sym (tw-eq n))
    (pΩ (Et n) (λ c → Prt-Ψ n (L (suc n)) (Sr n) botE (cv (Et n) c) (subst (λ H → P⟨ L (suc n) ⟩ H) (tw1 n) (prtL (suc n))))
       (λ c → skL n (cv (Et n) c)))

lamIso : LamIso Λ′
lamIso = record { lΛ = lΛ′ ; L = L ; L⊲ = L⊲ ; prt = prtL }
```
