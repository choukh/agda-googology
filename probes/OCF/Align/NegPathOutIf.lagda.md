# 路径记在折叠输出上, 否定一路 (四): 接口的盲区与边界

> 不含记号. 入口 [NegPathOut](NegPathOut.lagda.md). 对着接口 [PathOutIf](PathOutIf.lagda.md) ("接口定稿 2026-11-05 (首次编译通过)") 写, 导入它, 不另造接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **结果.**
>
> 1. **`ok→tri`, `ev-tg→tri` (定理, 对一切实例).** 接口的 `correct` 加上 `dec` 的前提 (合法世界 $W$, `Tg W t`, `Ev W κ`) 推出种类的层号 `lvX κ` 与目标 $t$ 在 `R` 的层号里字面三歧 (`Tri`: 严格在下, 相等, 或目标在它之下). 所以 `Tg`/`Ev` 是一张 "公共上界证书": **`no-world`**: 字面不三歧的一对 $(t,\kappa)$, 没有任何合法世界同时带 `Tg W t` 与 `Ev W κ`.
> 2. **`¬tri-od-ev` (定理, 前提实例).** 在 `TySupC.ICd` 的可数层号上, $\lim\mathrm{od}$ 与 $\lim\mathrm{ev}$ 字面不三歧 (双向都不是第一位置, 不相等). 所以 `no-world` 的前提可满足: 任一以 `ICd` 为 `R` 的实例里, 层号为 $\lim\mathrm{od}$ 的种类与目标 $\lim\mathrm{ev}$ 不能同时有证据 (对具体实例在 NegPathOutInst 里写). 这是 [NegPathOutCmp](NegPathOutCmp.lagda.md) `no-exact-lim` 在接口上的样子.
> 3. **`constShiftOf` (构造, 盲; 对一切实例).** 把 `shift` 换成常值 ($e\mapsto$ `shift W κ (bot XS κ)`), 其余字段不动, 仍是实例. 接口不要求 `shift` 保住分支的共尾 (留下的结点经 `shift` 进入分支时, 可能只剩一个分支); 建议增补 "坐标在 `shift` 之下且 `shift` 单调" 一类的律 (判断: 这是值不变所需).
> 4. **`voidIf` (构造, 盲).** 证据 `Ev` 恒空的实例: `dec`, `correct`, `nxt` 都空真. 接口不要求任何种类带证据, 所以 `correct` 可以从不被用到. 是否 "lΩ 层号真的被折到" 要对实例查 (覆盖: 折叠访问的每个种类要么带 `Ev`, 要么另有去处).
>
> **前提实例.** 1: 任一实例的任一合法世界 (实例里给). 2: `ICd` (构造一路 TySup 的可数层号实例), $\lim\mathrm{od}$, $\lim\mathrm{ev}$ 都合法. 3: 任一实例. 4: 无前提.
>
> **只否定什么.** 只否定: (a) 字面不三歧的一对 (目标, 种类) 在同一合法世界里同时带证据; (b) "接口保证 `shift` 保值" 与 "接口保证 `dec` 被用到". **不否定**: 接口本身; 任何实例的 `correct` (那是构造一路的定理); 增补律. 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegPathOutIf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥; Lv)
open import OCF.Align.TySupIf using (TySupIf; module TySupIf)
open import OCF.Align.TySupC using (ICd; Cd)
open import OCF.Align.HtTowerNeg using (evᴴ; odᴴ; NatH; nat-ev; nat-od; no-lim⊲nat; no-into)
open import OCF.Align.Fab4LOm using (X₁)
open import OCF.Align.PathOutIf
```

## §1 正确的决定给出字面三歧; 不三歧处没有世界

```agda
module Tri (P : PathOutIf) where
  open PathOutIf P
  open TySupIf R using (C; L; _⊑_; _⊏_; LgC)

  Tri : C → C → Set
  Tri j t = (j ⊏ t) ⊎ (j ≡ t) ⊎ (t ⊑ j)

  ok→tri : ∀ {Tn t κ} (d : DcP L _⊑_ LgC XS Tn t κ) → OkP _⊏_ (lvX κ) d → Tri (lvX κ) t
  ok→tri (keep _ _) o = inj₁ o
  ok→tri (same _) o = inj₂ (inj₁ o)
  ok→tri {t = t} (above i q _ _ _) o = inj₂ (inj₂ (subst (λ z → t ⊑ z) o q))

  ev-tg→tri : ∀ W t → LgWo W → Tg W t → ∀ κ → Ev W κ → Tri (lvX κ) t
  ev-tg→tri W t lW pt κ ev = ok→tri (dec W t lW pt κ ev) (correct W t lW pt κ ev)

  no-world : ∀ t κ → ¬ Tri (lvX κ) t → ∀ W → LgWo W → Tg W t → ¬ Ev W κ
  no-world t κ nt W lW pt ev = nt (ev-tg→tri W t lW pt κ ev)
```

## §2 前提实例: `ICd` 上 $\lim\mathrm{od}$ 与 $\lim\mathrm{ev}$ 不三歧

`ICd` 的 `_⊏_` 是 `hs i ⊲[ tt ] X`, `_⊑_` 是 `⊲[ tt ]`.

```agda
intoH : ∀ {a b : HB S⊥} → a ⊲[ tt ] b → ∀ {f} → b ≡ hl f → (a ≡ hl f) ⊎ Σ ℕ (λ n → a ⊲[ tt ] f n)
intoH hself e = inj₁ e
intoH (hlim n q) refl = inj₂ (n , q)
intoH (hsuc _) ()
intoH (hLim {κ = ()} _ _) _

s≢z : ¬ (hs {S⊥} hz ≡ hz)
s≢z ()

l≢s : ∀ {f : ℕ → HB S⊥} {x} → ¬ (hs x ≡ hl f)
l≢s ()

hd : HB S⊥ → HB S⊥
hd (hl f) = f 0
hd x = x

ICdTri : Cd → Cd → Set
ICdTri j t = (TySupIf._⊏_ ICd j t) ⊎ (j ≡ t) ⊎ (TySupIf._⊑_ ICd t j)

¬tri-od-ev : ¬ ICdTri (hl odᴴ) (hl evᴴ)
¬tri-od-ev (inj₁ p) with intoH p refl
... | inj₁ e = l≢s e
... | inj₂ (n , q) = no-lim⊲nat (⊲ᴮ-tr (hsuc hself) q) (nat-ev n)
¬tri-od-ev (inj₂ (inj₁ e)) = s≢z (cong hd e)
¬tri-od-ev (inj₂ (inj₂ p)) = no-into evᴴ odᴴ nat-od (λ e → s≢z (sym e)) p refl refl

```

对一个以 `ICd` 为 `R` 的具体实例, `no-world` 加 `¬tri-od-ev` 就给出: 层号 (`lvX κ`) 为 $\lim\mathrm{od}$ 的种类与目标 $\lim\mathrm{ev}$ 不能在同一合法世界里同时带证据. 构造一路的实例出来后在 [NegPathOutInst](NegPathOutInst.lagda.md) 里具体写.

## §3 盲: 常值的 `shift`

```agda
constShiftOf : PathOutIf → PathOutIf
constShiftOf P = record
  { R = R ; XS = XS ; Wo = Wo ; LgWo = LgWo ; Tg = Tg ; Ev = Ev ; Adm = Adm ; nxt = nxt
  ; lg-nxt = lg-nxt ; tg-nxt = tg-nxt
  ; shift = λ W κ e → shift W κ (bot XS κ)
  ; adm-shift = λ κ e lW → adm-shift κ (bot XS κ) lW
  ; lvX = lvX ; dec = dec ; correct = correct }
  where open PathOutIf P

-- 常值 shift 不依赖坐标: 对一切 e, e′ 两个 shift 字面相同
constShift-const : ∀ P W κ e e′ → PathOutIf.shift (constShiftOf P) W κ e ≡ PathOutIf.shift (constShiftOf P) W κ e′
constShift-const P W κ e e′ = refl
```

## §4 盲: 证据恒空的实例

`R = ICd`, `XS = Lv X₁` (Fab4LOm 的 $X_1$), `Ev` 恒空. `dec`, `correct`, `nxt` 都对空的证据定义.

```agda
module Void where
  open TySupIf ICd using (C; L; _⊑_; _⊏_; LgC)

  XSv : KS
  XSv = Lv X₁

  Evv : ⊤ → K XSv → Set
  Evv _ _ = ⊥

  decv : ∀ (W : ⊤) t → ⊤ → ⊤ → (κ : K XSv) → (ev : Evv W κ) →
         DcP L _⊑_ LgC XSv (λ i → ∀ (e : E XSv κ) (a : ⊤) → ⊤) t κ
  decv W t lW pt κ ()

  correctv : ∀ (W : ⊤) t (lW : ⊤) (pt : ⊤) κ (ev : Evv W κ) → OkP _⊏_ hz (decv W t lW pt κ ev)
  correctv W t lW pt κ ()

voidIf : PathOutIf
voidIf = record
  { R = ICd ; XS = XSv ; Wo = ⊤ ; LgWo = λ _ → ⊤ ; Tg = λ _ _ → ⊤ ; Ev = Evv
  ; Adm = λ _ _ _ → ⊤ ; nxt = λ _ _ _ _ _ → tt ; lg-nxt = λ _ _ _ _ → tt ; tg-nxt = λ _ _ _ _ → tt
  ; shift = λ _ _ e → e ; adm-shift = λ _ _ _ → tt
  ; lvX = λ _ → hz ; dec = decv ; correct = correctv }
  where open Void

void-noEv : ∀ W κ → ¬ PathOutIf.Ev voidIf W κ
void-noEv W κ ()
```

## 结论 (按档)

- **[定理]** `Tri.Tri`, **`Tri.ok→tri`**, **`Tri.ev-tg→tri`**, **`Tri.no-world`** (对一切实例); `intoH`, **`¬tri-od-ev`** (`ICd` 上的前提实例); **`constShiftOf`**, `constShift-const` (盲); **`voidIf`**, `void-noEv` (盲).
- **[判断]** 建议增补的律: `shift` 保共尾 (坐标在 `shift` 之下, 单调); 覆盖 (折叠访问的每个种类带 `Ev` 或另有去处). 是否必需, 看实例.
