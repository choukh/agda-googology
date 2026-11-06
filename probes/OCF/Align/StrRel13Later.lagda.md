# 结构关系, 第十三轮 (五): 左留右升的两个输出, 以后再折叠时值上就错 (否定)

> 不读记号. 入口 [StrRel13](StrRel13.lagda.md). [StrRel13Kr](StrRel13Kr.lagda.md) 说: 在空状态 `Y₀` 下, 跨坐标层的节点对 (`xL` 坐标层 $0$, `xR` 坐标层 $1$) 在第 $1$ 层目标上的两个输出是 "节点" 对 "极限" (`OutL₁`, `OutR₁`), 结构关系里没有这样的规则. 本文回答下一个问题: **给结论层加一条 "节点 ≤ 极限" 的读法行不行?** 不行, 至少在 `R∀c` 的语义下不行: 把这两个输出当作第 $1$ 层的树, 在同一实例、同一世界里, 以**折叠真正产生的状态** $Y_1 = Y_0\oplus\mathrm{Step}\,Y_0$ 再折叠一次, 第 $0$ 层的读数左边非零 (`lowLater`), 右边为零 (`upLater`), 所以值上左边严格大 (`¬laterV`). 推论 `¬semLater`: `SemW (hs hz) tt tt OutL₁ OutR₁` 不成立 ($Y_1$ 与自己按 `R∀c` 相关, `hY₁`).
>
> 原因: 右边在产生输出时就上升, 链从**当时**的状态 (空) 读坐标层 $1$, 得到全 `n0`; 左边留成节点, 等**以后**的状态 ($Y_1$, 第 $0$ 层读数非零) 来折叠. 两个状态都是折叠实际经过的 (起始状态与第一个 `n1` 之后的状态). 所以 "一边升一边留" 的比较依赖 "升的那一边当时的状态" 与 "留的那一边以后的状态" 之间的关系, 不是关系族加一条规则能解决的.
>
> **范围.** 否定的是: 任何把 `OutL₁` 放在 `OutR₁` 之下、并且对以后的折叠 (相关的状态, 同一动作与上下文) 给出第 $0$ 层值 $\le$ 的读法. 不否定带状态不变量的语义, 例如要求 "产生输出时的状态在第 $k'$ 层的读数非空" (这里的反例用的是空状态 `Y₀`, 而 `Y₀` 是闭项的起始状态, 所以这种不变量对闭项的第一步不成立; 闭项的节点只在第一个 `n1` 之后出现, 那时状态已非空, 判断).
>
> 有限的判定: `nzb` 在闭项上计算 "非零", `nzb-ok` 把它变成 `NZ₀` 的证明 (定理, 对一切 $x$).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel13Later where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false; _∨_; T)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; l≤; ≤-refl; ≤-trans; irr)
open import OCF.Align.HtFeedTree using (H; hz; hs; hself; hsuc; D; D₀; n0; n1; _⨾_; nl; ni; nκ; nw; AccY; accL; sum)
open import OCF.Align.HtFeedGrow using (NZ₀; nz1; nzL; nzR; nzl; nzw; nz≤)
open import OCF.Align.StrRel12Rel using (Rel; n0ᴸ; n1ᴸ; ⨾ᴸ; nlᴸ; vsum)
open import OCF.Align.StrRel13Val using (Λ₂; module P; module S; module E₂; cp00; pt≤; xz)
open import OCF.Align.StrRel13Kr using (OutL₁; OutR₁)
```

## 1 判定非零

```agda
nzb : ∀ {W} → D₀ W → Bool
nzb n0 = false
nzb n1 = true
nzb (x ⨾ y) = nzb x ∨ nzb y
nzb (nl d) = nzb (d 0)
nzb (ni () u)
nzb (nκ () u)
nzb (nw p x) = nzb x

∨-sp : ∀ a b → T (a ∨ b) → T a ⊎ T b
∨-sp true b h = inj₁ tt
∨-sp false b h = inj₂ h

nzb-ok : ∀ {W} (x : D₀ W) → T (nzb x) → NZ₀ x
nzb-ok n0 ()
nzb-ok n1 h = nz1
nzb-ok (x ⨾ y) h with ∨-sp (nzb x) (nzb y) h
... | inj₁ a = nzL (nzb-ok x a)
... | inj₂ b = nzR (nzb-ok y b)
nzb-ok (nl d) h = nzl (nzb-ok (d 0) h)
nzb-ok (ni () u) h
nzb-ok (nκ () u) h
nzb-ok (nw p x) h = nzw (nzb-ok x h)
```

## 2 以后的折叠

```agda
ll₁ : P.LW (hs hz) azero
ll₁ = hsuc hself

Y₁ : P.St azero
Y₁ = P._⊕⟨_⟩_ P.Y₀ tt (P.Step P.Y₀)

LaterL LaterR : D₀ azero
LaterL = P.yc (P.Run (accL (hs hz)) OutL₁ C.self tt ll₁ P.Act n0 Y₁) (P.τ₀ tt)
LaterR = P.yc (P.Run (accL (hs hz)) OutR₁ C.self tt ll₁ P.Act n0 Y₁) (P.τ₀ tt)

lowLater : asuc azero ≤ sum azero LaterL
lowLater = nz≤ azero (nzb-ok LaterL tt)

-- 极限的每一项都是 n0 时, 折叠的读数不加东西
nlz : ∀ {ly W₀ W} (ac : AccY ly) (F : ℕ → D ly W₀) → (∀ n → F n ≡ n0) → (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : P.LW ly W) (A₀ : P.Ig ly W)
      (w : D ly W) (Y : P.St W) → ∀ b → sum b (P.yc (P.Run ac (nl F) q₀ lW ll A₀ w Y) (P.τ₀ lW)) ≤ b
nlz ac F e q₀ lW ll A₀ w Y b =
  l≤ (pt≤ b _ (λ n → cong (λ x → P.yc (P.Run ac x q₀ lW ll A₀ (proj₁ (P.Rpt ac F q₀ lW ll A₀ w Y n)) (proj₂ (P.Rpt ac F q₀ lW ll A₀ w Y n))) (P.τ₀ lW)) (e n)))

-- 链的每一段的读数 (任意目标) 都是 n0
stz : ∀ {k W t m} (ac : AccY k) (hk : P.LW k W) (lW : Lg W) (A² : P.Ig k W) (Y : P.St W) →
      P.yc (P.d Y) (P.tg C.self hk lW) ≡ n0 → (T : P.Tg W t m) → ∀ n →
      P.yc (P.Run ac (proj₁ (proj₂ (P.Chn ac hk lW A² Y n))) C.self lW hk A² (proj₁ (P.Chn ac hk lW A² Y n)) (proj₂ (proj₂ (P.Chn ac hk lW A² Y n)))) T ≡ n0
stz ac hk lW A² Y e T n =
  cong (λ x → P.yc (P.Run ac x C.self lW hk A² (proj₁ (P.Chn ac hk lW A² Y n)) (proj₂ (proj₂ (P.Chn ac hk lW A² Y n)))) T) (xz ac hk lW A² Y e n)

upLater : sum azero LaterR ≤ azero
upLater = nlz _ _ (stz _ _ tt _ P.Y₀ refl _) C.self tt ll₁ P.Act n0 Y₁ azero
```

## 3 否定

```agda
¬laterV : ¬ (sum azero LaterL ≤ sum azero LaterR)
¬laterV h = irr azero (≤-trans lowLater (≤-trans h upLater))

hY₁ : S.R∀c tt tt Y₁ Y₁
hY₁ = (λ {t} T T′ tc → ⨾ᴸ n0ᴸ (nlᴸ (λ _ → ⨾ᴸ (E₂.ΩR t (E₂.noΩ⊲ (P.tm T) tt)) n0ᴸ))) , ⨾ᴸ n0ᴸ (nlᴸ (λ _ → ⨾ᴸ n1ᴸ n0ᴸ))

¬semLater : ¬ S.SemW (hs hz) tt tt OutL₁ OutR₁
¬semLater s = ¬laterV (vsum (s tt tt (accL (hs hz)) (accL (hs hz)) ll₁ ll₁ C.self C.self cp00 P.Act P.Act (E₂.haAct tt (hs hz))
                               n0 n0 n0ᴸ Y₁ Y₁ hY₁ (P.τ₀ tt) (P.τ₀ tt) cp00) (≤-refl azero))
```
