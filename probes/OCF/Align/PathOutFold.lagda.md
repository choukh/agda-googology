# 路径记在折叠输出上: 折叠与形状给出的合法

> 不含记号. 入口 [PathOut](PathOut.lagda.md), 接口 [PathOutIf](PathOutIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 对任一满足接口的 `P` 一条定义. 输入是 **带路径的高度**: 高度 $h$ 加上 `PH W h` (每个 $\Omega$-结点的种类带相对世界 $W$ 的证据 `Ev`, 每个可入的分支在新世界 `nxt` 里递归地带路径). `Ψ W lW t pt b h ph`: 把 `XS` 的高度折到目标层 $t$ (`pt : Tg W t`), 当前界 $b$. 与 [TySupFold](TySupFold.lagda.md) 的 `Φ` 逐子句对应, 只差两处:
>
> - 决定用 `dec W t lW pt κ ev`: 目标与种类的证据相对同一世界.
> - 进入分支时坐标先 `shift` (接在界后面), 世界换成 `nxt`, 目标的证据由 `tg-nxt` 搬过去, 分支的路径由 `PH` 给出. 这是 "回灌不再是恒等".
>
> "在上" 之后从第 $i$ 层折到 $t$ 用可数层号的 `TySupFold.Φ` (实例 `R`), 不在这里递归.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.PathOutIf
module OCF.Align.PathOutFold (P : PathOutIf) where

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_)
open import OCF.Align.HtTowerTy using (KS; K; E; HB; hz; hs; hl; hΩ)
open import OCF.Align.TySupIf using (module TySupIf)
import OCF.Align.TySupFold as F
open PathOutIf P
open TySupIf R hiding (dec)
open F R using (mul; chain; Σ⁺; Sh; Sh-mulL; Sh-chain; Sh-Σ; Sh-Φ) renaming (Φ to Φc)
```

## §1 带路径的高度

```agda
PH : Wo → HB XS → Set
PH W hz = ⊤
PH W (hs h) = PH W h
PH W (hl f) = ∀ n → PH W (f n)
PH W (hΩ κ g) = Σ (Ev W κ) (λ ev → ∀ e (a : Adm W κ e) → PH (nxt W κ ev e a) (g e))
```

## §2 折叠

```agda
caseP : ∀ {t κ Tn} {B : Set} → DcP L _⊑_ LgC XS Tn t κ →
        ((κ′ : K (L t)) → (E (L t) κ′ → E XS κ) → B) →
        ((HB (L t) → E XS κ) → B) →
        ((i : C) → t ⊑ i → LgC i → Tn i → (HB (L i) → E XS κ) → B) → B
caseP (keep κ′ fr) k s ab = k κ′ fr
caseP (same to) k s ab = s to
caseP (above i q li ti to) k s ab = ab i q li ti to

Ψ : ∀ W → LgWo W → ∀ t → Tg W t → HB (L t) → (h : HB XS) → PH W h → HB (L t)
Ψ W lW t pt b hz ph = hs hz
Ψ W lW t pt b (hs h) ph = hl (mul (Ψ W lW t pt b h ph))
Ψ W lW t pt b (hl f) ph = hl (Σ⁺ (λ n → Ψ W lW t pt b (f n) (ph n)))
Ψ W lW t pt b (hΩ κ g) (ev , ph) = caseP (dec W t lW pt κ ev)
  (λ κ′ fr → hΩ κ′ (λ c →
     Ψ (nxt W κ ev (shift W κ (fr c)) (adm-shift κ (fr c) lW))
       (lg-nxt ev (shift W κ (fr c)) (adm-shift κ (fr c) lW) lW)
       t (tg-nxt ev (shift W κ (fr c)) (adm-shift κ (fr c) lW) pt) b
       (g (shift W κ (fr c))) (ph (shift W κ (fr c)) (adm-shift κ (fr c) lW))))
  (λ to → hl (chain b (λ b′ →
     Ψ (nxt W κ ev (shift W κ (to b′)) (adm-shift κ (to b′) lW))
       (lg-nxt ev (shift W κ (to b′)) (adm-shift κ (to b′) lW) lW)
       t (tg-nxt ev (shift W κ (to b′)) (adm-shift κ (to b′) lW) pt) b′
       (g (shift W κ (to b′))) (ph (shift W κ (to b′)) (adm-shift κ (to b′) lW)))))
  (λ i q li ti to → Φc i (wf i) li t q b (hl (chain (top i) (λ b′ →
     Ψ (nxt W κ ev (shift W κ (to b′)) (adm-shift κ (to b′) lW))
       (lg-nxt ev (shift W κ (to b′)) (adm-shift κ (to b′) lW) lW)
       i (ti (shift W κ (to b′)) (adm-shift κ (to b′) lW)) b′
       (g (shift W κ (to b′))) (ph (shift W κ (to b′)) (adm-shift κ (to b′) lW))))))
```

## §3 形状给出的合法

`Sh` 是 `TySupFold.Sh` (ℕ-极限相邻项在一切世界里是第一位置, 遗传; $\Omega$-结点只要分支遗传). 证明的递归与 `Ψ` 相同; "在上" 处直接用 `TySupFold.Sh-Φ`.

```agda
Sh-caseP : ∀ {t κ Tn} {S : KS} (d : DcP L _⊑_ LgC XS Tn t κ) {k s ab} →
           (∀ κ′ fr → Sh {S} (k κ′ fr)) → (∀ to → Sh {S} (s to)) → (∀ i q li ti to → Sh {S} (ab i q li ti to)) →
           Sh (caseP d k s ab)
Sh-caseP (keep κ′ fr) sk ss sa = sk κ′ fr
Sh-caseP (same to) sk ss sa = ss to
Sh-caseP (above i q li ti to) sk ss sa = sa i q li ti to

Sh-Ψ : ∀ W lW t pt b h ph → Sh (Ψ W lW t pt b h ph)
Sh-Ψ W lW t pt b hz ph = tt
Sh-Ψ W lW t pt b (hs h) ph = Sh-mulL _ (Sh-Ψ W lW t pt b h ph)
Sh-Ψ W lW t pt b (hl f) ph = Sh-Σ _ (λ n → Sh-Ψ W lW t pt b (f n) (ph n))
Sh-Ψ W lW t pt b (hΩ κ g) (ev , ph) = Sh-caseP (dec W t lW pt κ ev)
  (λ κ′ fr c →
     Sh-Ψ (nxt W κ ev (shift W κ (fr c)) (adm-shift κ (fr c) lW))
       (lg-nxt ev (shift W κ (fr c)) (adm-shift κ (fr c) lW) lW)
       t (tg-nxt ev (shift W κ (fr c)) (adm-shift κ (fr c) lW) pt) b
       (g (shift W κ (fr c))) (ph (shift W κ (fr c)) (adm-shift κ (fr c) lW)))
  (λ to → Sh-chain b _ (λ b′ →
     Sh-Ψ (nxt W κ ev (shift W κ (to b′)) (adm-shift κ (to b′) lW))
       (lg-nxt ev (shift W κ (to b′)) (adm-shift κ (to b′) lW) lW)
       t (tg-nxt ev (shift W κ (to b′)) (adm-shift κ (to b′) lW) pt) b′
       (g (shift W κ (to b′))) (ph (shift W κ (to b′)) (adm-shift κ (to b′) lW))))
  (λ i q li ti to → Sh-Φ i (wf i) li t q b _)
```
