# 结构关系, 第十四轮的否定 (二): 不变量经 `⊕J` 封闭时, 含 "右边高坐标层读数为零" 的状态对就推出反例

> 不读记号. 入口 [StrRel14Neg](StrRel14Neg.lagda.md). 对着 [StrRel14If](StrRel14If.lagda.md) 的 `Inv` (§2, 定稿 10:18) 与 `NodeObl⁼` (§6, 10:40 增补) 写.
>
> [StrRel14NegNode](StrRel14NegNode.lagda.md) 否定的是以 `R∀X` 为状态前提的 `NodeSound`. 自然的修法是把状态前提换成接口 §2 的不变量 `J`. 本文问: **哪些 `J` 也不行?** `Inv` 的律 `⊕J` 对**任意**按 `OAc` 相关的一对输出 $\Delta,\Delta'$ 封闭 (不只折叠产生的输出). 取 $\Delta=\Delta'=\Delta_v$ (`d Yv`: 第 $0$ 层目标上读 `n1`, 别的层读 `n0`; 它与自己 `OAc` 相关, `ovv`), 从任何 `J` 相关的 $(Y,Y')$ 出发, $(Y\oplus\Delta_v,\ Y'\oplus\Delta_v)$ 仍 `J` 相关.
>
> **定理 `inv-kill`** (实例 $\Lambda_2=2$, 节点对 `xL` (坐标层 $0$) 与 `xR` (坐标层 $1$), 运行世界 $0$, 路径 `self`, 动作 `Act`, 上下文 `n0`): 对任意 `I : Inv`, 任意 `J tt tt Y Y′`, 若 $Y'$ 在坐标层 $1$ 上的读数是 "零树" (`Zt`: 只由 `n0`, `⨾`, `nl`, `nw` 组成), 则 $(Y^+,Y'^+)=(Y\oplus\Delta_v,\ Y'\oplus\Delta_v)$ 满足 `J`, 而第 $0$ 层目标上左边的读数和严格大于右边:
>
> - 左边 (`lowAny`): 链从 $Y^+$ 在第 $0$ 层的读数 $a⨾\mathrm{n1}$ 起 ($a$ 任意), 第一段里那个 `n1` 经动作 `Act` 输出 $\omega\cdot(\mathrm{n1}⨾\ldots)$, 非零. 对一切 $Y$ 成立.
> - 右边 (`upZ`): 链从 $Y'^+$ 在第 $1$ 层的读数 (零树 `⨾ n0`) 起, 零树的折叠在一切目标上还是零树 (`runZ`), 所以每一段都是零树, 和不超过底.
>
> **`inv-obl`** 把同一件事写成接口的类型: 在这对 `J` 相关的状态上, §6 的升升义务 `OblRR⁼` 不成立 (第 $0$ 层目标上两边的 `rkT` 都是 `rise`, 等式是 `refl`). 推论 **`inv-kill₀`**: 若 `J tt tt Y₀ Y₀` (空状态, 闭项的起始状态), 同样的反例. **`I₀`-实例**: `J = R∀c` 的不变量 (`StrRel14J` 的 `I₀`) 含 $(Y_0,Y_0)$, 所以带它的任何跨坐标层节点规则在第 $0$ 层值上不可靠 (`kill-R∀c`).
>
> **构造一路为什么需要这条律.** `⊕J` 是接口 `Inv` 的字段; 构造一路的 `StrRel14J.semJ` 只经 `toR`, `cvJ`, `⊕J` 用状态 (该文件头的判断). 跨坐标层节点规则若以 `J` 为状态前提, 它在一切 `J` 相关的状态上都要成立, 包括 `⊕J` 造出来的这些.
>
> **前提可满足.** `J tt tt Y₀ Y₀` 对 `J = R∀c` 成立 (`r∀c₀`); 零树前提对 $Y_0$ 成立 (`refl` 化简后是 `n0`). 节点对的分支前提同 `StrRel14NegNode` (`n1ˣ`).
>
> **只否定什么.** 只否定: 以满足 "含某个右边坐标层 $1$ 读数为零树的状态对" 的 `J` 为状态前提、第 $0$ 层结论蕴含值 $\le$ 的跨坐标层节点规则 (对 `xL`, `xR` 这一对). 这里没有写出 "`J` 版的 `NodeSound`" 这个类型 (接口里没有), 定理直接说那一对读数的值. **不否定**: 要求每个状态对在高坐标层上的读数都非零的不变量 (例如 `StrRel14J` 的 `I₁`, 它的 `NE` 要求一切目标上的读数在左脊上含 $\omega\cdot(\Omega_t⨾y)$, 所以不含零树读数; 判断: 本文的办法对 `I₁` 不起作用, 因为右边的链此时从含 $\Omega_1$ 的读数起, 它的节点上升时也读到左边加进来的东西). 不否定同层的 `semJ`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel14NegInv where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; l≤; ≤-refl; ≤-trans; irr)
open import OCF.Align.HtFeedTree using (H; hz; hs; hself; hsuc; D; D₀; n0; n1; _⨾_; nl; nw; AccY; accL; sum; pt)
open import OCF.Align.HtFeedGrow using (NZ₀; nz1; nzL; nzR; nzl; nz≤)
open import OCF.Align.StrRel12Rel using (n0ᴸ)
import OCF.Align.StrRel12Sem as Sm
import OCF.Align.StrRel14If as If
open import OCF.Align.StrRel13Val using (Λ₂; r₀; r₁; xL; xR; Yv; cp00; rr)
open import OCF.Align.StrRel14NegNode using (module G)
open import Relation.Binary.PropositionalEquality using (refl)

open If Λ₂ tt
module S = Sm Λ₂ tt
open P using (Tg; tg; St; Df; yc; d; Run; Chn; τ₀; Act; Y₀; _⊕⟨_⟩_)
```

## 1 零树: 折叠后还是零树, 和不超过底

```agda
data Zt {L : H} : ∀ {W} → D L W → Set where
  z0 : ∀ {W} → Zt (n0 {W = W})
  z⨾ : ∀ {W} {x y : D L W} → Zt x → Zt y → Zt (x ⨾ y)
  zl : ∀ {W} {e : ℕ → D L W} → (∀ n → Zt (e n)) → Zt (nl e)
  zw : ∀ {W₀ W} {p : W₀ ⊲ W} {x : D L W₀} → Zt x → Zt (nw p x)

runZ : ∀ {ly W₀ W} (ac : AccY ly) {x : D ly W₀} → Zt x → ∀ (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : P.LW ly W) (A₀ : P.Ig ly W) (w : D ly W) (Y : St W) {t m} (T : Tg W t m) →
       Zt (yc (Run ac x q₀ lW ll A₀ w Y) T)
runZ ac z0 q₀ lW ll A₀ w Y T = z0
runZ ac {x ⨾ y} (z⨾ hx hy) q₀ lW ll A₀ w Y T =
  z⨾ (runZ ac hx q₀ lW ll A₀ w Y T) (runZ ac hy q₀ lW ll A₀ (w ⨾ nw q₀ x) (Y ⊕⟨ lW ⟩ Run ac x q₀ lW ll A₀ w Y) T)
runZ ac (zl hd) q₀ lW ll A₀ w Y T = zl (λ n → runZ ac (hd n) q₀ lW ll A₀ _ _ T)
runZ ac (zw {p = p} hx) q₀ lW ll A₀ w Y T = runZ ac hx (⊲-tr p q₀) lW ll A₀ w Y T

chZ : ∀ {k W} (ac : AccY k) (hk : P.LW k W) (lW : Lg W) (A² : P.Ig k W) (Y : St W) → Zt (yc (d Y) (tg C.self hk lW)) →
      ∀ n → Zt (proj₁ (proj₂ (Chn ac hk lW A² Y n)))
chZ ac hk lW A² Y h zero = h
chZ ac hk lW A² Y h (suc n) = runZ ac (chZ ac hk lW A² Y h n) C.self lW hk A² _ _ (tg C.self hk lW)

sumZ : ∀ {W} b {x : D₀ W} → Zt x → sum b x ≤ b
sumZ b z0 = ≤-refl b
sumZ b {x ⨾ y} (z⨾ hx hy) = ≤-trans (sumZ (sum b x) hy) (sumZ b hx)
sumZ b {nl e} (zl hd) = l≤ go
  where
  go : ∀ n → pt b e n ≤ b
  go zero = ≤-refl b
  go (suc n) = ≤-trans (sumZ (pt b e n) (hd n)) (go n)
sumZ b (zw {x = x} hx) = sumZ b {x} hx
```

## 2 两次运行, 一个附加的输出

```agda
OL OR : St azero → D₀ azero
OL Y = yc (Run (accL Λ₂) xL C.self tt hself Act n0 Y) (τ₀ tt)
OR Y = yc (Run (accL Λ₂) xR C.self tt hself Act n0 Y) (τ₀ tt)

Δv : Df azero
Δv = d Yv

ovv : S.OAc tt tt Δv Δv
ovv {t} T T′ tc = rr t

-- 左: 对一切 Y, 加上 Δv 之后第 0 层读数非零
lowAny : ∀ Y → asuc azero ≤ sum azero (OL (Y ⊕⟨ tt ⟩ Δv))
lowAny Y = nz≤ azero {OL (Y ⊕⟨ tt ⟩ Δv)} (nzl (nzR (nzl (nzL nz1))))

-- 右: 坐标层 1 上读数是零树时, 加上 Δv 之后读数的和不超过底
upZ : ∀ Y′ → Zt (yc (d Y′) (tg C.self (hsuc hself) tt)) → sum azero (OR (Y′ ⊕⟨ tt ⟩ Δv)) ≤ azero
upZ Y′ h = sumZ azero {OR (Y′ ⊕⟨ tt ⟩ Δv)} (zl (λ n → runZ (accL (hs hz)) (chZ _ _ tt _ (Y′ ⊕⟨ tt ⟩ Δv) (z⨾ h z0) n) C.self tt _ _ _ _ (τ₀ tt)))
```

## 3 定理

```agda
inv-kill : (I : Inv) → ∀ (Y Y′ : St azero) → Inv.J I tt tt Y Y′ → Zt (yc (d Y′) (tg C.self (hsuc hself) tt)) →
           Inv.J I tt tt (Y ⊕⟨ tt ⟩ Δv) (Y′ ⊕⟨ tt ⟩ Δv) × ¬ (sum azero (OL (Y ⊕⟨ tt ⟩ Δv)) ≤ sum azero (OR (Y′ ⊕⟨ tt ⟩ Δv)))
inv-kill I Y Y′ j h = Inv.⊕J I cp00 Y Y′ Δv Δv j ovv , λ le → irr azero (≤-trans (lowAny Y) (≤-trans le (upZ Y′ h)))

inv-kill₀ : (I : Inv) → Inv.J I tt tt Y₀ Y₀ →
            Inv.J I tt tt (Y₀ ⊕⟨ tt ⟩ Δv) (Y₀ ⊕⟨ tt ⟩ Δv) × ¬ (sum azero (OL (Y₀ ⊕⟨ tt ⟩ Δv)) ≤ sum azero (OR (Y₀ ⊕⟨ tt ⟩ Δv)))
inv-kill₀ I j = inv-kill I Y₀ Y₀ j z0

-- 前提可满足: J = R∀c 是一个不变量, 含 (Y₀, Y₀)
I∀ : Inv
I∀ = record { J = S.R∀c ; toR = λ h → h ; cvJ = S.cvRc ; ⊕J = S.advRc }

r∀c₀ : S.R∀c {W = azero} {W′ = azero} tt tt Y₀ Y₀
r∀c₀ = (λ T T′ tc → n0ᴸ) , n0ᴸ

kill-R∀c : S.R∀c {W = azero} {W′ = azero} tt tt (Y₀ ⊕⟨ tt ⟩ Δv) (Y₀ ⊕⟨ tt ⟩ Δv) × ¬ (sum azero (OL (Y₀ ⊕⟨ tt ⟩ Δv)) ≤ sum azero (OR (Y₀ ⊕⟨ tt ⟩ Δv)))
kill-R∀c = inv-kill₀ I∀ r∀c₀

-- 用接口 §6 的类型说: 在 ⊕J 造出的 J 相关状态上, 升升义务 OblRR⁼ 不成立
module O⁼ (Y Y′ : St azero) = NodeObl⁼ {lV = tt} {lV′ = tt} r₀ r₁ (λ _ _ _ → n1) (λ _ _ _ → n1) tt tt
  (accL Λ₂) (accL hz) (accL Λ₂) (accL (hs hz)) C.self C.self hself hself Act Act n0 n0 Y Y′

inv-obl : (I : Inv) → ∀ (Y Y′ : St azero) → Inv.J I tt tt Y Y′ → Zt (yc (d Y′) (tg C.self (hsuc hself) tt)) →
          Inv.J I tt tt (Y ⊕⟨ tt ⟩ Δv) (Y′ ⊕⟨ tt ⟩ Δv) × ¬ O⁼.OblRR⁼ (Y ⊕⟨ tt ⟩ Δv) (Y′ ⊕⟨ tt ⟩ Δv)
inv-obl I Y Y′ j h = proj₁ (inv-kill I Y Y′ j h) ,
  λ ob → proj₂ (inv-kill I Y Y′ j h) (G.vsumX Λ₂ tt (ob (τ₀ tt) (τ₀ tt) cp00 refl refl) (≤-refl _))
```
