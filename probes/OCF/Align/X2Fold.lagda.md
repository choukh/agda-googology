# $X_2$: 带底的 `lΩ` 层号的折叠

> 不含记号. 入口 [X2](X2.lagda.md), 接口 [X2If](X2If.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 对任一满足接口的 `V` 一条定义.
>
> - **换层** `cv W h cb`: 高度逐构造子换到第 $X_1\oplus\mathrm{lvW}\,W$ 层, 种类用 `cvK`, 分支坐标用 `cvE` 读回; `CB W h` 说每个种类可换 (遗传, 一切坐标).
> - **带路径的高度** `PH₂ W h`: 低种类照 `PathOutFold.PH` (底种类 $\kappa_0$ 的证据, 可入的分支在 `nxt` 世界里递归); 高种类 (第 $X_1\oplus i$ 层) 的分支对一切坐标可换 (`CB`), 且对 "在 $W$ 里带路径的第 $X_1\oplus i$ 层的值 $b'$", 第 $b'$ 个分支换过去后在 $W$ 里带路径 (`PHU`).
> - **带底的可数折叠** `ΦB`: 第 $X_1\oplus i$ 层的带路径的值, 经 `ΦX` 折到第 $X_1$ 层 (路径由 `PH-ΦX`), 再经 `Ψ` 折到 $X_1$ 之下的目标 $t$. 叠层之间 ($X_1\oplus m\to X_1\oplus i$) 就是 `ΦU`.
> - **折叠** `Ψ₂ W lW t pt b h ph`: 与 `PathOutFold.Ψ` 逐子句对应. 结点按 `cls` 分: 低种类照 `Ψ` (分支取在 `to` 之后); 高种类一律在上: 链从 `topU i` 起, 第 $b'$ 项是 `ΦU` 把换过去的第 $b'$ 个分支从第 $X_1\oplus\mathrm{lvW}\,W$ 层折到第 $X_1\oplus i$ 层, 链的路径由 `PH-chain`, `PH-ΦU` 给出, 整个交给 `ΦB`. 高种类处不对 `Ψ₂` 递归.
> - **形状给出的合法** `Sh-Ψ₂`: 输出由形状合法, 对一切输入.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.X2If
module OCF.Align.X2Fold (V : X2If) where

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; _×_)
open import OCF.Align.HtTowerTy using (KS; K; E; HB; hz; hs; hl; hΩ; LgB)
open import OCF.Align.TySupIf using (module TySupIf)
open import OCF.Align.TySupC using (Cd; _⊏ᶜ_; _⊑ᶜ_; wfC; ⊏→⊑ᶜ; lgC↓ᶜ)
open import OCF.Align.TySupSum using (ICdΣ)
open import OCF.Align.PathOutIf using (module PathOutIf; DcP)
open import OCF.Align.X1UpIf
import OCF.Align.TySupFold as F
import OCF.Align.PathOutFold as PF
import OCF.Align.X1UpFold as UF
open X2If V
open X1UpIf U using (P)
open PathOutIf P
open TySupIf R hiding (dec)
open F R using (mul; chain; Σ⁺; Sh; Sh-mulL; Sh-chain; Sh-Σ; Sh-Φ) renaming (Φ to Φc)
open F ICdΣ using () renaming (chain to chainU)
open PF P using (Ψ; Sh-Ψ; caseP; Sh-caseP)
open UF U using (LS; topU; ΦU; ΦX; PSL; PHU; PH-ΦU; PH-ΦX; PH-chain; PH-topU)
```

## §1 换层

```agda
CB : Wo → HB XS₂ → Set
CB W hz = ⊤
CB W (hs h) = CB W h
CB W (hl f) = ∀ n → CB W (f n)
CB W (hΩ κ g) = CvK W κ × (∀ e → CB W (g e))

cv : ∀ W h → CB W h → HB (LS (lvW W))
cv W hz cb = hz
cv W (hs h) cb = hs (cv W h cb)
cv W (hl f) cb = hl (λ n → cv W (f n) (cb n))
cv W (hΩ κ g) (k , cb) = hΩ (cvK W κ k) (λ e → cv W (g (cvE W κ k e)) (cb (cvE W κ k e)))
```

## §2 带路径的高度

```agda
Br : ∀ W κ → (E XS₂ κ → HB XS₂) → (Wo → E XS₂ κ → Set) → ClX U XS₂ lvW W κ → Set
Br W κ g Rc (lo κ₀ ev₀ to) = ∀ e₀ (a : Adm W κ₀ e₀) → Rc (nxt W κ₀ ev₀ e₀ a) (to e₀)
Br W κ g Rc (up i q to) =
  Σ (∀ b′ → CB W (g (to b′))) (λ cp → ∀ b′ → PHU i W b′ → PHU (lvW W) W (cv W (g (to b′)) (cp b′)))

PH₂ : Wo → HB XS₂ → Set
PH₂ W hz = ⊤
PH₂ W (hs h) = PH₂ W h
PH₂ W (hl f) = ∀ n → PH₂ W (f n)
PH₂ W (hΩ κ g) = Σ (Ev₂ W κ) (λ ev → Br W κ g (λ W′ e → PH₂ W′ (g e)) (cls W κ ev))
```

## §3 带底的可数折叠

```agda
ΦB : ∀ W → LgWo W → ∀ t → Tg W t → HB (L t) → ∀ i → LgB i → (v : HB (LS i)) → PHU i W v → HB (L t)
ΦB W lW t pt b i li v pv = Ψ W lW t pt b (ΦX i li v) (PH-ΦX i li v W pv)
```

高种类的链 (第 $X_1\oplus i$ 层) 与它的路径.

```agda
chU : ∀ W → LgWo W → ∀ {κ} (g : E XS₂ κ → HB XS₂) i → i ⊏ᶜ lvW W → (to : HB (LS i) → E XS₂ κ) →
      (∀ b′ → CB W (g (to b′))) → HB (LS i)
chU W lW g i q to cp =
  hl (chainU (topU i) (λ b′ → ΦU (lvW W) (wfC (lvW W)) (lgW lW) i (⊏→⊑ᶜ q) b′ (cv W (g (to b′)) (cp b′))))

PH-chU : ∀ W lW {κ} (g : E XS₂ κ → HB XS₂) i q to cp →
         (∀ b′ → PHU i W b′ → PHU (lvW W) W (cv W (g (to b′)) (cp b′))) → PHU i W (chU W lW g i q to cp)
PH-chU W lW g i q to cp pk =
  PH-chain (PSL i) (topU i) _ (PH-topU i W) (λ b′ pb′ →
    PH-ΦU (lvW W) (wfC (lvW W)) (lgW lW) i (⊏→⊑ᶜ q) b′ (cv W (g (to b′)) (cp b′)) W pb′ (pk b′ pb′))
```

## §4 折叠

```agda
caseX : ∀ {W κ} {g : E XS₂ κ → HB XS₂} {Rc : Wo → E XS₂ κ → Set} {B : Set}
        (c : ClX U XS₂ lvW W κ) → Br W κ g Rc c →
        ((κ₀ : K XS) (ev₀ : Ev W κ₀) (to : E XS κ₀ → E XS₂ κ) →
           (∀ e₀ (a : Adm W κ₀ e₀) → Rc (nxt W κ₀ ev₀ e₀ a) (to e₀)) → B) →
        ((i : Cd) (q : i ⊏ᶜ lvW W) (to : HB (LS i) → E XS₂ κ) (cp : ∀ b′ → CB W (g (to b′))) →
           (∀ b′ → PHU i W b′ → PHU (lvW W) W (cv W (g (to b′)) (cp b′))) → B) → B
caseX (lo κ₀ ev₀ to) p kl ku = kl κ₀ ev₀ to p
caseX (up i q to) (cp , pk) kl ku = ku i q to cp pk

Ψ₂ : ∀ W → LgWo W → ∀ t → Tg W t → HB (L t) → (h : HB XS₂) → PH₂ W h → HB (L t)
Ψ₂ W lW t pt b hz ph = hs hz
Ψ₂ W lW t pt b (hs h) ph = hl (mul (Ψ₂ W lW t pt b h ph))
Ψ₂ W lW t pt b (hl f) ph = hl (Σ⁺ (λ n → Ψ₂ W lW t pt b (f n) (ph n)))
Ψ₂ W lW t pt b (hΩ κ g) (ev , ph) = caseX {g = g} (cls W κ ev) ph
  (λ κ₀ ev₀ to ph′ → caseP (dec W t lW pt κ₀ ev₀)
    (λ κ′ fr → hΩ κ′ (λ c →
       Ψ₂ (nxt W κ₀ ev₀ (shift W κ₀ (fr c)) (adm-shift κ₀ (fr c) lW))
         (lg-nxt ev₀ (shift W κ₀ (fr c)) (adm-shift κ₀ (fr c) lW) lW)
         t (tg-nxt ev₀ (shift W κ₀ (fr c)) (adm-shift κ₀ (fr c) lW) pt) b
         (g (to (shift W κ₀ (fr c)))) (ph′ (shift W κ₀ (fr c)) (adm-shift κ₀ (fr c) lW))))
    (λ to′ → hl (chain b (λ b′ →
       Ψ₂ (nxt W κ₀ ev₀ (shift W κ₀ (to′ b′)) (adm-shift κ₀ (to′ b′) lW))
         (lg-nxt ev₀ (shift W κ₀ (to′ b′)) (adm-shift κ₀ (to′ b′) lW) lW)
         t (tg-nxt ev₀ (shift W κ₀ (to′ b′)) (adm-shift κ₀ (to′ b′) lW) pt) b′
         (g (to (shift W κ₀ (to′ b′)))) (ph′ (shift W κ₀ (to′ b′)) (adm-shift κ₀ (to′ b′) lW)))))
    (λ i q li ti to′ → Φc i (wf i) li t q b (hl (chain (top i) (λ b′ →
       Ψ₂ (nxt W κ₀ ev₀ (shift W κ₀ (to′ b′)) (adm-shift κ₀ (to′ b′) lW))
         (lg-nxt ev₀ (shift W κ₀ (to′ b′)) (adm-shift κ₀ (to′ b′) lW) lW)
         i (ti (shift W κ₀ (to′ b′)) (adm-shift κ₀ (to′ b′) lW)) b′
         (g (to (shift W κ₀ (to′ b′)))) (ph′ (shift W κ₀ (to′ b′)) (adm-shift κ₀ (to′ b′) lW)))))))
  (λ i q to cp pk → ΦB W lW t pt b i (lgC↓ᶜ q (lgW lW)) (chU W lW g i q to cp) (PH-chU W lW g i q to cp pk))
```

## §5 形状给出的合法

**定理 (一步, 对一切 `V`, 一切输入).** 递归与 `Ψ₂` 相同; 低种类的 "在上" 用 `TySupFold.Sh-Φ`, 高种类用 `PathOutFold.Sh-Ψ`.

```agda
Sh-caseX : ∀ {W κ} {g : E XS₂ κ → HB XS₂} {Rc : Wo → E XS₂ κ → Set} {S : KS}
           (c : ClX U XS₂ lvW W κ) (p : Br W κ g Rc c) {kl ku} →
           (∀ κ₀ ev₀ to p′ → Sh {S} (kl κ₀ ev₀ to p′)) → (∀ i q to cp pk → Sh {S} (ku i q to cp pk)) →
           Sh (caseX {g = g} c p kl ku)
Sh-caseX (lo κ₀ ev₀ to) p sl su = sl κ₀ ev₀ to p
Sh-caseX (up i q to) (cp , pk) sl su = su i q to cp pk

Sh-Ψ₂ : ∀ W lW t pt b h ph → Sh (Ψ₂ W lW t pt b h ph)
Sh-Ψ₂ W lW t pt b hz ph = tt
Sh-Ψ₂ W lW t pt b (hs h) ph = Sh-mulL _ (Sh-Ψ₂ W lW t pt b h ph)
Sh-Ψ₂ W lW t pt b (hl f) ph = Sh-Σ _ (λ n → Sh-Ψ₂ W lW t pt b (f n) (ph n))
Sh-Ψ₂ W lW t pt b (hΩ κ g) (ev , ph) = Sh-caseX {g = g} (cls W κ ev) ph
  (λ κ₀ ev₀ to ph′ → Sh-caseP (dec W t lW pt κ₀ ev₀)
    (λ κ′ fr c →
       Sh-Ψ₂ (nxt W κ₀ ev₀ (shift W κ₀ (fr c)) (adm-shift κ₀ (fr c) lW))
         (lg-nxt ev₀ (shift W κ₀ (fr c)) (adm-shift κ₀ (fr c) lW) lW)
         t (tg-nxt ev₀ (shift W κ₀ (fr c)) (adm-shift κ₀ (fr c) lW) pt) b
         (g (to (shift W κ₀ (fr c)))) (ph′ (shift W κ₀ (fr c)) (adm-shift κ₀ (fr c) lW)))
    (λ to′ → Sh-chain b _ (λ b′ →
       Sh-Ψ₂ (nxt W κ₀ ev₀ (shift W κ₀ (to′ b′)) (adm-shift κ₀ (to′ b′) lW))
         (lg-nxt ev₀ (shift W κ₀ (to′ b′)) (adm-shift κ₀ (to′ b′) lW) lW)
         t (tg-nxt ev₀ (shift W κ₀ (to′ b′)) (adm-shift κ₀ (to′ b′) lW) pt) b′
         (g (to (shift W κ₀ (to′ b′)))) (ph′ (shift W κ₀ (to′ b′)) (adm-shift κ₀ (to′ b′) lW))))
    (λ i q li ti to′ → Sh-Φ i (wf i) li t q b _))
  (λ i q to cp pk → Sh-Ψ W lW t pt b (ΦX i (lgC↓ᶜ q (lgW lW)) (chU W lW g i q to cp))
     (PH-ΦX i (lgC↓ᶜ q (lgW lW)) (chU W lW g i q to cp) W (PH-chU W lW g i q to cp pk)))
```
