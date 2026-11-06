# 结构关系, 第十四轮 (四): 带不变量的两世界语义, 八条规则 `semJ`

> 不读记号. 入口 [StrRel14](StrRel14.lagda.md). 接手清单第 1 项 (StrRel13 §3): 把 `MonoPort7` 的单世界不变量与 `StrRel12` 的两世界语义合起来, 重证 `StrRel12.sem` 的八条规则带不变量.
>
> 1. **(定理) `Sem.semJ`: 对任意不变量记录 `I : Inv` (`StrRel14If`), 对一切层 $L$, `Rel L x x′` 蕴含 `SemJ L x x′`.** 一个证明对一切 $\Lambda$ (含 $\Omega$-极限的实例) 与一切层; 证明逐句是 `StrRel12.sem` (由脚本从 `StrRel12Sem`/`Ni`/`Kp` 生成 `StrRel14SemJ`/`NiJ`/`KpJ`), 状态前提只经记录的三条律 (`toR`, `cvJ`, `⊕J`) 使用. 这说明 `StrRel12` 的证明里状态只经这三条律进入 (编译证据: 生成的文件逐字照抄后编译通过).
> 2. **两个不变量.** `I₀`: `J = R∀c` (`semJ I₀` 就是 `StrRel12` 的设定). `I₁`: `J = R∀c` 加上两边状态都 "非空" (`NE`: 每个目标 $T$ (层 $t$) 上的读数在左脊上含一段 $\omega\cdot(\Omega_t⨾y)$, 即 `Step` 留下的字面形状). `NE` 经 `⊕` (右边加东西, 左脊不变) 与 `cv` (读数是同一个函数在抬升后的目标上的值) 封闭 (`ne⊕`, `necv`); `Kp`/`Kb`/`BNi`/`Chn`/`κc` 的状态都由这两种变化组成, 所以 `semJ I₁` 在它们处不另需前提 (这一句是判断, 依据是 `semJ` 的证明只用记录的律).
> 3. **(定理) `ne-pos`**: `NE` 的状态在第 $0$ 层目标上的读数的和严格大于底 ($\beta<\Sigma_\beta$). 这正是 `StrRel13Later.¬laterV` 的反例状态 (空状态 `Y₀`) 不满足的那一条 (`¬NEY₀`).
> 4. **前提可满足 (`inst₁`).** 对一切不含 $\Omega$-极限的 $\Lambda$, 状态 $Y_1=Y_0\oplus\mathrm{Step}\,Y_0$ (闭项在第一个 `n1` 之后的状态) 满足 `I₁` (`hY₁`); 外层动作 `Act` 的 `HAWJ` 由 `StrRel12.haAct` 削弱得到 (`haw→J`); 于是 `semJ I₁` 对 $\Omega_\Lambda$ 在这一状态上给出 `OAc`.
>
> **范围 (判断).** `semJ` 的关系仍是 `StrRel12Rel.Rel` (同层节点), 所以本文不解决跨坐标层; 它给出的是下一步 (异质关系 `RelX` 的语义) 要用的带不变量的框架, 以及 "状态只经三条律进入" 这一结构事实. `I₁` 的 `NE` 对应 StrRel13 接手清单的 (b) (对 "当时" 的状态成立, 不能是空状态); (a) (跨目标层的支配) 没有放进 `I₁`, 见入口 §3.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
module OCF.Align.StrRel14J (Λ : H) (lΛ : LgH Λ) where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; Lg; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; ≤-refl; ≤-trans; ⊲→≤; irr)
open import OCF.Align.HtFeedTree using (hz; hself; D; D₀; n0; n1; _⨾_; nl; Ωd; AccY; acc; accL; accᴸ; sum; pt; sum-fst)
open import OCF.Align.HtFeedClosed using (module At; one)
open import OCF.Align.StrRel12Al using (CP)
open import OCF.Align.StrRel12Rel using (Rel; n0ᴸ; n1ᴸ; ⨾ᴸ; nlᴸ; prᴸ; nwAᴸ; niᴸ; κᴸ)
open import OCF.Align.StrRel12Sem Λ lΛ using (OAc; R∀c; cvRc; advRc; HAW)
open import OCF.Align.StrRel12 Λ lΛ using (NoΩ; noΩ⊲; ΩR; haAct; cpOne)
open import OCF.Align.StrRel14If Λ lΛ using (Inv; module WithInv)

module P = At Λ lΛ
open P using (Tg; tm; St; Df; yc; d; cv; _⊕⟨_⟩_; Act; Y₀; Step; Run; Ig; τ₀)
```

## 1 八条规则, 对一切不变量

```agda
module Sem (I : Inv) where
  open WithInv I public
  open Inv I using (J; toR)
  open import OCF.Align.StrRel14SemJ Λ lΛ I using (sem-n0; sem-n1; sem-⨾; sem-nl; sem-nw; sem-pr)
  open import OCF.Align.StrRel14NiJ Λ lΛ I using (module NiS)
  open import OCF.Align.StrRel14KpJ Λ lΛ I using (module KpS)

  semJ : ∀ L → AccY L → ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {x′ : D L V′} → Rel L lV lV′ x x′ → SemJ L lV lV′ x x′
  semJ L ac n0ᴸ = sem-n0 L
  semJ L ac n1ᴸ = sem-n1 L
  semJ L ac (⨾ᴸ hx hy) = sem-⨾ L hx (semJ L ac hx) (semJ L ac hy)
  semJ L ac (nlᴸ hd) = sem-nl L hd (λ n → semJ L ac (hd n))
  semJ L ac (prᴸ hx) = sem-pr L (semJ L ac hx)
  semJ L ac (nwAᴸ hp hx) = sem-nw L hp (semJ L ac hx)
  semJ L (acc g) (niᴸ {r = r} {r′ = r′} h) =
    NiS.sem-ni r r′ h (λ p p′ lc lc′ cp y y′ b → semJ L (acc g) (h p p′ lc lc′ cp y y′ b)) (λ hk → semJ _ (g r) hk)
  semJ L ac (κᴸ h) = KpS.sem-κ h (λ p p′ lc lc′ cp → semJ L ac (h p p′ lc lc′ cp))

  semJ∀ : ∀ L {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {x′ : D L V′} → Rel L lV lV′ x x′ → SemJ L lV lV′ x x′
  semJ∀ L = semJ L (accL L)

  -- 动作前提: 对一切 R∀c 状态成立的, 对 J 状态也成立
  haw→J : ∀ L {W W′} {lW : Lg W} {lW′ : Lg W′} {A₀ : Ig L W} {A₀′ : Ig L W′} → HAW L lW lW′ A₀ A₀′ → HAWJ L lW lW′ A₀ A₀′
  haw→J L ha p p′ l l′ cp w w′ hw Y Y′ hY = ha p p′ l l′ cp w w′ hw Y Y′ (toR hY)
```

## 2 不变量 `I₀`: 就是 `R∀c`

```agda
I₀ : Inv
I₀ = record { J = R∀c ; toR = λ h → h ; cvJ = cvRc ; ⊕J = advRc }
```

## 3 不变量 `I₁`: 加上 "非空"

`Lf s x`: $s$ 在 $x$ 的左脊上 (向左走, 或跳过左边的 `n0`). `NE Y`: 每个目标上的读数在左脊上含 $\omega\cdot(\Omega_t⨾y)$.

```agda
data Lf {t : H} {m : A} (s : D t m) : D t m → Set where
  here : Lf s s
  left : ∀ {x y} → Lf s x → Lf s (x ⨾ y)
  rgt0 : ∀ {y} → Lf s y → Lf s (n0 ⨾ y)

NE : ∀ {W} → St W → Set
NE {W} Y = ∀ {t m} (T : Tg W t m) → Σ (D t m) (λ y → Lf (nl (λ _ → Ωd t ⨾ y)) (yc (d Y) T))

ne⊕ : ∀ {W} {lW : Lg W} (Y : St W) (Δ : Df W) → NE Y → NE (Y ⊕⟨ lW ⟩ Δ)
ne⊕ Y Δ h T = proj₁ (h T) , left (proj₂ (h T))

necv : ∀ {W W′} (q : W C.⊲ W′) (Y : St W) → NE Y → NE (cv q Y)
necv q Y h T = h (P.tg↑ q T)

J₁ : ∀ {W W′} → Lg W → Lg W′ → St W → St W′ → Set
J₁ lW lW′ Y Y′ = R∀c lW lW′ Y Y′ × (NE Y × NE Y′)

I₁ : Inv
I₁ = record
  { J = J₁
  ; toR = proj₁
  ; cvJ = λ ap Y Y′ h → cvRc ap Y Y′ (proj₁ h) , (necv _ Y (proj₁ (proj₂ h)) , necv _ Y′ (proj₂ (proj₂ h)))
  ; ⊕J = λ {_} {_} {lW} {lW′} tp Y Y′ Δ Δ′ h O → advRc tp Y Y′ Δ Δ′ (proj₁ h) O , (ne⊕ {lW = lW} Y Δ (proj₁ (proj₂ h)) , ne⊕ {lW = lW′} Y′ Δ′ (proj₂ (proj₂ h)))
  }
```

## 4 "非空" 在第 0 层给出严格的下界

```agda
lf≤ : ∀ {W} {s x : D₀ W} → Lf s x → ∀ β → sum β s ≤ sum β x
lf≤ here β = ≤-refl _
lf≤ {x = x ⨾ y} (left h) β = ≤-trans (lf≤ h β) (⊲→≤ (sum-fst (sum β x) y))
lf≤ (rgt0 h) β = lf≤ h β

ne-pos : ∀ {W} (lW : Lg W) (Y : St W) → NE Y → ∀ β → asuc β ≤ sum β (yc (d Y) (τ₀ lW))
ne-pos lW Y h β = ≤-trans (≤l 1 (⊲→≤ (sum-fst (asuc β) (proj₁ (h (τ₀ lW)))))) (lf≤ (proj₂ (h (τ₀ lW))) β)

-- 空状态不满足 NE (StrRel13Later 的反例状态被排除)
¬NEY₀ : ∀ {W} (lW : Lg W) → ¬ NE (Y₀ {W})
¬NEY₀ lW h = irr azero (ne-pos lW Y₀ h azero)
```

## 5 前提可满足: 不含 $\Omega$-极限的 $\Lambda$, 状态 $Y_1$

```agda
Y₁ : St one
Y₁ = Y₀ ⊕⟨ tt ⟩ Step Y₀

hY₁ : NoΩ Λ → J₁ tt tt Y₁ Y₁
hY₁ o = ((λ {t} T T′ tc → ⨾ᴸ n0ᴸ (nlᴸ (λ _ → ⨾ᴸ (ΩR t (noΩ⊲ (tm T) o)) n0ᴸ))) , ⨾ᴸ n0ᴸ (nlᴸ (λ _ → ⨾ᴸ n1ᴸ n0ᴸ))) ,
        ((λ T → n0 , rgt0 here) , (λ T → n0 , rgt0 here))

module S₁ = Sem I₁

inst₁ : NoΩ Λ → OAc tt tt (Run accᴸ (Ωd Λ {azero}) (z⊲ one) tt hself Act n0 Y₁) (Run accᴸ (Ωd Λ {azero}) (z⊲ one) tt hself Act n0 Y₁)
inst₁ o = S₁.semJ∀ Λ (ΩR Λ o) tt tt accᴸ accᴸ hself hself (z⊲ one) (z⊲ one) cpOne Act Act (S₁.haw→J Λ (haAct o Λ)) n0 n0 n0ᴸ Y₁ Y₁ (hY₁ o)
```
