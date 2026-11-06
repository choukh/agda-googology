# X₂ 与往 `tw n`, 否定一路 (五): 对构造一路实例 `I₂` 与闭项 `TX2` 的检查

> 不含记号. 入口 [NegX2](NegX2.lagda.md). 只读导入构造一路的 [X2If](X2If.lagda.md), [X2Fold](X2Fold.lagda.md), [X2Inst](X2Inst.lagda.md), 不改它们. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **检查四件事: $X_2$ 的种类是否真被折到; 决定是否正确; 证书是否标准 `LgB`; 读法是否高于 `TU2`.**
>
> 1. **分类正确 (`cls-ok`, 定理, 对一切世界与种类).** 给 `XS₂` 的种类按结构读出读回层 `lv₂` ($X_2$ 的 $\Omega_1$ 种类是 `lz`; 分支 $c$ 的种类按 `LS (hs c)` 的递归: 底种类是 $X_1$ 里的层, 第 $j$ 个叠层新种类是 $X_1\oplus j$). 实例的 `cls₂`: 低种类 $\kappa_0$ 的读回层就是 $\kappa_0$ 在 $X_1$ 里的读回层, 高种类 $i$ 的读回层就是 $X_1\oplus i$. 推论 **`up-not-below`**: 高种类的读回层不在任何可数目标之下 (`NegX1UpCmp.U-not-cnt`), 所以 "高种类一律在上" 对 `Ψ₂` 的一切目标正确; 低种类的决定是 PathOut 的 `dec₁`, 正确是构造一路旧的定理 `correct₁`. 接口没有这条律 (`NegX2If.allLoOf`), 实例满足它.
> 2. **种类真被折到 (`TX2-root`, `up-step`, 定理, refl).** `TX2` 的根是 $X_2$ 的 $\Omega_1$ 结点 (低种类, 视作底的 $\Omega_1$), 对目标 $0$ 是同层: `TX2` 字面是链 `hl (chain hz k)`, 第 $b'$ 项把分支 `gt₂ (1 ⊞ leg b′)` 交给 `Ψ₂` (世界换成 $2\boxplus\mathrm{leg}\,b'$ 的后继). 分支里叠层新种类的结点 (第 $X_1\oplus c$ 层) 由 `ΦB` 折下 (`up-step`, 对一切 $c$).
> 3. **证书.** `LgB-TX2` 是标准 `LgB` (`HtTowerTy.LgB`, 第 0 层), 由 `Sh-Ψ₂` 与 `PathOut.sh→lgB₁`; 输入 `topL₂` 合法 (`Lg-topL₂`). **盲 (`LgB-TX2c`, 定理).** 实例换成 `NegX2If.constOf I₂` (读入一律常值) 后, 同一闭项公式也有 `LgB` 证书, 路径对一切世界平凡 (`PHc-top`). 证书不约束读入.
> 4. **`Ψ₂` 不单调** (`NegX2Mono.Ψ₂-not-mono`) 在 `I₂` 上的实例: **`Ψ₂-not-mono-I₂`**.
> 5. **边界.**
>    - **`no-PH₂-high` (定理).** 合法的输入 `ι (inj₂ 1) (topU 2)` (第 $X_1\oplus2$ 层的地板放进分支 $1$, `Lg-high`) 在初始世界 $1$ 里不带路径 ($1\sqsubset 1$ 不成立). `Ψ₂` 的定义域只含 "叠层下标在世界之下" 的树; 闭项从 $\Omega_1$ 根进入, 不受影响.
>    - **`¬CB-⊞`, `no-up-after` (定理).** 一棵不可换层的树 $a$ 接在任一高种类结点前面 ($a\boxplus\Omega_{X_1\oplus c+1}$ 形), 结果不带路径. 推论 **`no-up-after-floor`**: $X_2$ 的地板之后接任一叠层结点 (`topL₂ ⊞ hΩ (inj₂ c , inj₂ tt) g`, 对一切 $c, g$, 一切世界) 不带路径. 构造一路的 `no-ΩΩ` 是它的一个特例的形状.
>    - **`κΩ₂-not-cv` (定理).** 对任一界 $B$, $X_2$ 地板的分支 `gt₂ c` 不能对一切 $c$ 都换到第 $X_1\oplus B$ 层 (取 $c=B+1$, 分支的根是第 $X_1\oplus B$ 层的新种类, 要 $B+1\lhd B$). 所以实例里 `CvK₂ (κΩ₂) = ⊥` 不只是选择: 只要换层的目标是固定的叠层 `LS B`, 带地板式分支的 $X_2$-$\Omega_1$ 结点就换不过去 (同 `NegX2Lv.no-fixed-m`).
>
> **前提实例.** 1: 无前提. 3: `constOf I₂` 是实例 (构造). 5: `Lg-high` (合法); `¬CB-topL₂` (地板不可换, 对一切世界).
>
> **只否定什么.** 4 只否定 `Ψ₂` 保第一位置. 5 只否定: 叠层下标超过世界的输入、高种类分支里含 $X_2$-$\Omega_1$ 结点的输入落在 `Ψ₂` 的定义域里; 用固定叠层 `LS B` 换 $X_2$-$\Omega_1$ 结点. **不否定**: `Ψ₂`, `Sh-Ψ₂`, `PH₂-top`, `TX2` 与 `LgB-TX2`; 用别的换法 (例如按世界逐分支升 $B$) 处理 $X_2$-$\Omega_1$ 结点. 本篇没有关闭任何路线.
>
> **读法 (判断, 没有值的定理).** `TX2` 的外层是同层链 $b_{n+1}=b_n\boxplus\Psi_2(\mathrm{gt}_2(1\boxplus\mathrm{leg}\,b_n'))$ (2, 字面), 每项把前面的输出当叠层高度, 第 $c$ 项在 $X_1\oplus c$ 处由 `ΦB` 折下, 与 `X1Up.TU` 同一机制 (只多了前缀 `gt₂ c`, 是更低叠层地板的和). 这与 `X1Up.TU2` 的对角 $y_{n+1}=y_n\boxplus TU(y_n+1)$ 是同一个不动点迭代, 读 ψ₀(Ω_{Ω·2}). 所以 **判断: `TX2` 的读法与 `TU2` 相同, 不更高**; 正如 PathOut 的 `TXL` 与 TySup 的 `TΩΩ` 读法相同 (都是 ψ₀(Ω_Ω)). 新的是同一序数由 `lΩ` 层号 $X_2$ 的地板经一次折叠得到. 越过 ψ₀(Ω_{Ω·2}) 要在 $X_2$ 上再叠层 ($X_2\oplus m$), 那时上层折叠到 $X_2$ 的输出会把 $X_2$ 的地板接在叠层结点前面, 由 5 (`no-up-after-floor`, `κΩ₂-not-cv`) 它们不在 `Ψ₂` 的定义域里 (判断: 上层折叠尚未写出, 这一步只依据输出的形状).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegX2Inst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥; LH; lz; lvl)
open import OCF.Align.TySupC using (Cd; _⊏ᶜ_; ofC)
open import OCF.Align.TySupSum using (ICdΣ)
import OCF.Align.TySupFold as TF
open import OCF.Align.Fab4LOm using (_⊑ᴸ_; irr)
open import OCF.Align.NegPathOutCmp using (ofC-mono)
open import OCF.Align.PathOutX1 using (X₁; XS₁; κΩ)
open import OCF.Align.PathOut using (W₀; lW₀; sh→lgB₁)
open import OCF.Align.NegX1UpEmb using () renaming (ofU to ofUᴱ)
open import OCF.Align.NegX1UpCmp using (U-not-cnt)
open import OCF.Align.X1Up using (IU)
import OCF.Align.X1UpFold as UF
open UF IU using (LS; topU; ClD; bas; nw; clD; ClP; clP; cS; cL; Lg-topU)
open import OCF.Align.X2If renaming (up to upK)
import OCF.Align.X2Fold as XF
open import OCF.Align.X2Inst using (I₂; XS₂; G₂; κΩ₂; Ev₂; cls₂; clsC; idW; CvK₂; gt₂; topL₂; Lg-topL₂; TX2; LgB-TX2)
open import OCF.Align.NegX2If using (constOf)
open import OCF.Align.NegX2Mono using (module NotMono₂)
open XF I₂ using (CB; PH₂; Ψ₂; Sh-Ψ₂; ΦB; chU; PH-chU)
open import OCF.Align.TySupC using (lgC↓ᶜ)
```

## §1 分类正确

```agda
lvS : ∀ m → K (LS m) → LH
lvS hz κ = lvl X₁ κ
lvS (hs x) (inj₁ κ) = lvS x κ
lvS (hs x) (inj₂ _) = ofUᴱ x
lvS (hl f) (n , κ) = lvS (f n) κ
lvS (hΩ () _) _

lv₂ : K XS₂ → LH
lv₂ (inj₁ _ , inj₁ ())
lv₂ (inj₁ _ , inj₂ _) = lz
lv₂ (inj₂ c , κ) = lvS (hs c) κ

OkD : ∀ m κ → ClD m κ → Set
OkD m κ (bas κ₀ _) = lvS m κ ≡ lvl X₁ κ₀
OkD m κ (nw j _ _) = lvS m κ ≡ ofUᴱ j

okS : ∀ {x κ} (d : ClD x κ) → OkD x κ d → OkD (hs x) (inj₁ κ) (cS d)
okS (bas κ₀ to) e = e
okS (nw j p to) e = e

okL : ∀ {f} n {κ} (d : ClD (f n) κ) → OkD (f n) κ d → OkD (hl f) (n , κ) (cL n d)
okL n (bas κ₀ to) e = e
okL n (nw j p to) e = e

okD : ∀ m κ → OkD m κ (clD m κ)
okD hz κ = refl
okD (hs x) (inj₁ κ) = okS (clD x κ) (okD x κ)
okD (hs x) (inj₂ _) = refl
okD (hl f) (n , κ) = okL n (clD (f n) κ) (okD (f n) κ)
okD (hΩ () _) _

OkX : ∀ {W} κ → ClX IU XS₂ idW W κ → Set
OkX κ (lo κ₀ _ _) = lv₂ κ ≡ lvl X₁ κ₀
OkX κ (upK i _ _) = lv₂ κ ≡ ofUᴱ i

okC : ∀ {B} c κ′ (q : c ⊏ᶜ B) (d : ClD c κ′) (p : ClP c κ′ d) ev →
      OkD c κ′ d → OkX (inj₂ c , inj₁ κ′) (clsC c κ′ q d p ev)
okC c κ′ q (bas κ₀ to) p ev e = e
okC c κ′ q (nw i pi to) p ev e = e

cls-ok : ∀ B κ ev → OkX κ (cls₂ B κ ev)
cls-ok B (inj₁ _ , inj₁ ()) _
cls-ok B (inj₁ _ , inj₂ _) _ = refl
cls-ok B (inj₂ c , inj₂ _) _ = refl
cls-ok B (inj₂ c , inj₁ κ′) (q , ev) = okC c κ′ q (clD c κ′) (clP c κ′) ev (okD c κ′)

-- 高种类的读回层不在任何可数目标之下: "一律在上" 正确
UpBelow : ∀ {W} κ → ClX IU XS₂ idW W κ → Set
UpBelow κ (lo _ _ _) = ⊤
UpBelow κ (upK i _ _) = ∀ t → ¬ (lv₂ κ ⊑ᴸ ofC t)

upB : ∀ {W} κ (c : ClX IU XS₂ idW W κ) → OkX κ c → UpBelow κ c
upB κ (lo _ _ _) e = tt
upB κ (upK i _ _) e t p = U-not-cnt i t (subst (λ z → z ⊑ᴸ ofC t) e p)

up-not-below : ∀ B κ ev → UpBelow κ (cls₂ B κ ev)
up-not-below B κ ev = upB κ (cls₂ B κ ev) (cls-ok B κ ev)
```

## §2 种类真被折到 (refl)

```agda
open TF ICdΣ using (chain)

-- TX2 的根是同层: 字面是链, 第 b′ 项把分支 gt₂ (W₀ ⊞ leg b′) 交给 Ψ₂
TX2-root : Σ (HB S⊥ → HB S⊥) (λ k → TX2 ≡ hl (chain hz k))
TX2-root = _ , refl

-- 分支里的叠层新种类结点: 由 ΦB 折下 (对一切 c, 世界, 目标)
up-step : ∀ W lW t pt b c (g : HB (LS c) → HB XS₂) ph →
  Ψ₂ W lW t pt b (hΩ (inj₂ c , inj₂ tt) g) ph ≡
  ΦB W lW t pt b c (lgC↓ᶜ (proj₁ (proj₁ ph)) (proj₁ lW))
     (chU W lW {κ = inj₂ c , inj₂ tt} g c (proj₁ (proj₁ ph)) (λ v → v) (proj₁ (proj₂ ph)))
     (PH-chU W lW {κ = inj₂ c , inj₂ tt} g c (proj₁ (proj₁ ph)) (λ v → v) (proj₁ (proj₂ ph)) (proj₂ (proj₂ ph)))
up-step W lW t pt b c g ph = refl
```

## §3 证书的盲: 读入常值的实例

```agda
I₂c : X2If
I₂c = constOf I₂

open XF I₂c using () renaming (PH₂ to PH₂c; Ψ₂ to Ψ₂c; Sh-Ψ₂ to Sh-Ψ₂c)

PHc-top : ∀ W → PH₂c W topL₂
PHc-top W = tt , λ y a → tt

TX2c : HB S⊥
TX2c = Ψ₂c W₀ lW₀ hz (z⊲ᴮ W₀) hz topL₂ (PHc-top W₀)

LgB-TX2c : LgB TX2c
LgB-TX2c = sh→lgB₁ TX2c (Sh-Ψ₂c W₀ lW₀ hz (z⊲ᴮ W₀) hz topL₂ (PHc-top W₀))
```

## §4 `Ψ₂` 不单调: 实例

```agda
open NotMono₂ I₂ using () renaming (Ψ₂-not-mono to Ψ₂-not-mono-I₂) public
```

## §5 边界

```agda
one two : Cd
one = hs hz
two = hs one

high : HB XS₂
high = ι (inj₂ one) (topU two)

Lg-high : LgB high
Lg-high = Lg-ι (inj₂ one) (topU two) (Lg-topU two)

no-sB : ∀ (B : Cd) → ¬ (hs B ⊲[ tt ] B)
no-sB B p = irr (ofC B) (ofC-mono p)

no-PH₂-high : ¬ PH₂ W₀ high
no-PH₂-high ((q , _) , _) = no-sB one q
```

不可换层的树接在高种类结点前面: 不带路径.

```agda
¬CB-⊞ : ∀ {B} a h → ¬ CB B a → ¬ CB B (a ⊞ h)
¬CB-⊞ a hz na c = na c
¬CB-⊞ a (hs h) na c = ¬CB-⊞ a h na c
¬CB-⊞ a (hl f) na c = ¬CB-⊞ a (f 0) na (c 0)
¬CB-⊞ a (hΩ κ g) na (k , c) = ¬CB-⊞ a (g (bot XS₂ κ)) na (c (bot XS₂ κ))

¬CB-topL₂ : ∀ {B} → ¬ CB B topL₂
¬CB-topL₂ (() , _)

no-up-after : ∀ W a c (g : HB (LS c) → HB XS₂) → ¬ CB W a → ¬ PH₂ W (a ⊞ hΩ (inj₂ c , inj₂ tt) g)
no-up-after W a c g na (_ , cp , _) = ¬CB-⊞ a (g hz) na (cp hz)

no-up-after-floor : ∀ W c (g : HB (LS c) → HB XS₂) → ¬ PH₂ W (topL₂ ⊞ hΩ (inj₂ c , inj₂ tt) g)
no-up-after-floor W c g = no-up-after W topL₂ c g ¬CB-topL₂
```

$X_2$ 地板的分支不能都换到一个固定的叠层.

```agda
κΩ₂-not-cv : ∀ B → ¬ (∀ c → CB B (gt₂ c))
κΩ₂-not-cv B all = no-sB B (proj₁ (all (hs B)))
```

## 结论 (按档)

- **[定理]** `lvS`, `lv₂`, `OkD`, `okS`, `okL`, `okD`, `OkX`, `okC`, **`cls-ok`**, `UpBelow`, `upB`, **`up-not-below`**; **`TX2-root`**, **`up-step`** (refl); `I₂c`, `PHc-top`, `TX2c`, **`LgB-TX2c`** (盲); **`Ψ₂-not-mono-I₂`**; `high`, `Lg-high`, `no-sB`, **`no-PH₂-high`**, **`¬CB-⊞`**, `¬CB-topL₂`, **`no-up-after`**, **`no-up-after-floor`**, **`κΩ₂-not-cv`**.
- **[判断]** 读法: `TX2` 与 `TU2` 同读 ψ₀(Ω_{Ω·2}), 不更高; $X_2\oplus m$ 的上层输出不在 `Ψ₂` 的定义域里 (依据输出形状, 上层折叠未写).
