# 结构关系, 第十九轮 (四): 值: kZ 形的时间条件在 `cv` 之后仍成立, 且足以给出 `rkAt` 那一对在 $(\tau_0,\tau_0)$ 上的值

> 不读记号. 入口 [StrRel19](StrRel19.lagda.md). 设定同 `StrRel17Time`: $\Lambda_2=2$, 节点 `xL` (层 $2$, 坐标层 $0$, 分支 `n1`), 动作 `Act`, 上下文 `n0`, 产生状态 $Y$ 任意; 再折叠左边以 $Y_2$, 右边以 $Y_2'$, 都用 `Act`, `n0`, 读第 $0$ 层目标.
>
> 1. **(定理) `valZ`: 时间条件取 kZ 形 (`DomZ⁰`: 差分量 $Y\le Y_2'$, 累计 $z_Y\le Y_2'$ 在 $\tau_0$ 上的读数) 就够.** `J²⁺ Y₂ Y₂′` 且 `DomZ⁰ Y Y₂′` ⇒ 两次再折叠的输出 `RelX⁺ hz hz` 相关; `valZV`: 第 $0$ 层的和 $\le$. 证明同 `StrRel17Time.valT` 的四步, 只换掉状态前提里累计的那一项: 右边内部节点处的状态 $S_0\oplus\mathrm{Step}\,S_0$ 的累计以 $\omega\cdot(1⨾\text{读数}(S_0))$ 结尾, 而 $S_0$ 的读数以 $Y_2'$ 的读数为左前缀, 所以 $z_Y$ 落在它的一个分量之下 (`in⁺`).
> 2. **(定理) 前提实例, 在 `cv` 之后: `domZC`, `¬domLC`, `exCv`.** $Y_B=Y_1\oplus\mathrm{Step}\,Y_1$, $Y_C=$ `cv self` $Y_B$ (累计被清成 `n0`, 差分量不变). `DomZ⁰ Y_B Y_C` 成立 (`domZC`), 而 `StrRel17If.DomL` 的形状 `J²⁺ Y_B Y_C` 不成立 (`¬domLC`: 累计 $z_{Y_B}$ 不低于 `n0`). `exCv`: 以 $Y_B$ 产生, 两边以 $Y_C$ 再折叠, 第 $0$ 层的和左 $\le$ 右.
>
> 这里用旧关系 `RelX⁺` 写 (`DomZ⁰`), 因为 `StrRel17Time` 的工具 (`Z00.rr00`, `semX00⁺`) 是旧关系的; 第 $0$ 层上两个关系相同 (`StrRel19Up.emb00`, `back00`), 高层上新关系多出 `up`, 所以接口的 `DomZ` 不能直接换成 `DomZ⁰` (判断).
>
> **范围.** 一个具体的节点 (`xL` 对自己), 有限的 $\Lambda_2$, 一个目标对 $(\tau_0,\tau_0)$; 不是 `RkSoundZ`. 关于闭项 ($T_\Omega<T_{\Omega+1}$ 或界) 的值: 没有.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel19Val where

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (azero; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; ≤-refl)
open import OCF.Align.HtFeedTree using (hz; D₀; n0; _⨾_; sum)
open import OCF.Align.StrRel12Al using (ap-self)
open import OCF.Align.StrRel13Val using (Λ₂)
open import OCF.Align.StrRel14J Λ₂ tt using (NE; ne⊕; necv)
open import OCF.Align.StrRel16If Λ₂ tt using (RelX⁺; OA²⁺; J²⁺; pr⁺; in⁺; here; inL; inR; inE; module P)
open import OCF.Align.StrRel16Sem Λ₂ tt using (lp→rel⁺; lawcv⁺)
open import OCF.Align.StrRel16Lem using (module V0)
open import OCF.Align.StrRel17Time using (module Core; YB; hYB)

open V0 Λ₂ tt using (vsum⁺)
open P using (τ₀; St; d; z; yc; cv; _⊕⟨_⟩_; Step)
```

## 1 kZ 形的时间条件 (旧关系)

```agda
DomZ⁰ : St azero → St azero → Set
DomZ⁰ Y Y′ = (OA²⁺ tt tt (d Y) (d Y′) × RelX⁺ hz hz tt tt (z Y) (yc (d Y′) (τ₀ tt))) × (NE Y × NE Y′)

valZ : ∀ (Y Y₂ Y₂′ : St azero) (hY₂ : J²⁺ tt tt Y₂ Y₂′) → DomZ⁰ Y Y₂′ →
       RelX⁺ hz hz tt tt (Core.Re.LaterLY Y Y₂ Y₂′ hY₂) (Core.Re.LaterRY Y Y₂ Y₂′ hY₂)
valZ Y Y₂ Y₂′ hY₂ ((o , zr) , (ne , ne′)) = R.valC hS
  where
  module R = Core.Re Y Y₂ Y₂′ hY₂
  hS : J²⁺ tt tt Y (R.S₀ ⊕⟨ tt ⟩ Step R.S₀)
  hS = ((λ T T′ tx → pr⁺ (lp→rel⁺ (o T T′ tx) (proj₁ R.laterS₀ T′))) ,
        in⁺ (lp→rel⁺ zr (proj₁ R.laterS₀ (τ₀ tt))) (inR (inE 0 (inR here)))) ,
       (ne , ne⊕ {lW = tt} R.S₀ (Step R.S₀) R.neS₀)

valZV : ∀ (Y Y₂ Y₂′ : St azero) (hY₂ : J²⁺ tt tt Y₂ Y₂′) → DomZ⁰ Y Y₂′ →
        sum azero (Core.Re.LaterLY Y Y₂ Y₂′ hY₂) ≤ sum azero (Core.Re.LaterRY Y Y₂ Y₂′ hY₂)
valZV Y Y₂ Y₂′ hY₂ dom = vsum⁺ (valZ Y Y₂ Y₂′ hY₂ dom) (≤-refl azero)
```

## 2 `cv` 之后: kZ 成立, `DomL` 不成立

```agda
YC : St azero
YC = cv C.self YB

hYC : J²⁺ tt tt YC YC
hYC = lawcv⁺ (ap-self tt tt) YB YB hYB

domZC : DomZ⁰ YB YC
domZC = (proj₁ (proj₁ hYB) , proj₂ (proj₁ hYB)) , (proj₁ (proj₂ hYB) , necv C.self YB (proj₂ (proj₂ hYB)))

-- 累计: 非零的树不低于 n0
¬le0 : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {a b : D₀ V} → ¬ RelX⁺ hz hz lV lV′ (a ⨾ b) (n0 {W = V′})
¬le0 (in⁺ h here) = ¬le0 h

¬domLC : ¬ J²⁺ tt tt YB YC
¬domLC ((_ , rz) , _) = ¬le0 rz

exCv : sum azero (Core.Re.LaterLY YB YC YC hYC) ≤ sum azero (Core.Re.LaterRY YB YC YC hYC)
exCv = valZV YB YC YC hYC domZC
```
