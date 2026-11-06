# X₁ 上叠层, 否定一路 (八): 对构造一路实例 `IU` 与折叠 `ΦU` 的检查

> 不含记号. 入口 [NegX1Up](NegX1Up.lagda.md). 只读导入构造一路的 [X1UpFold](X1UpFold.lagda.md) (折叠 `ΦU`, `ΦX`, 地板 `topU`) 与 [X1Up](X1Up.lagda.md) (实例 `IU`, 闭项 `TU`), 不改它们. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **检查四件事: $X_1$ 的种类是否真被留下; 决定是否正确; 中间层与输入是否 `LgB`; 读法是否真的越过 ψ₀(Ω_Ω).**
>
> 1. **`root-Ω₁` (定理, 闭项上的字面事实).** `TU1` 的中间值 `ΦX 1 (topU 1)` (第 $X_1$ 层) 的第 0 个链点, 根是 $X_1$ 的 $\Omega_1$-结点. 所以 $X_1$ 的种类在上层折叠的输出里被**留下**, 中间值不是可数层号上的树. `keep-base` (定理, 对一切 $m$, 目标, 底种类): 底种类一律 "留", 种类经 `emb`, 读回经 `frE`.
> 2. **决定.** 构造一路的 `okU` 是正面定理. 盲 (**`OkU-bas-blind`**, 定理): `OkU` 对底种类的 "留" 是 $\top$, 不提层号; 层号上的精确性由 [NegX1UpCmp](NegX1UpCmp.lagda.md) `exact-keep-base` 在 `ofU` 的写法上给出 (`LS` 与 `ofU` 的种类结构在具体层号上字面相同, `LS≡LU-2`, 测试; 对变量 $m$ 未证).
> 3. **合法性.**
>    - 输入: `Lg-topU` (构造一路的定理), 合法.
>    - **`ΦU-not-mono` (定理, 对一切 `U`, 一切 $m$, 目标, 界).** $1\lhd\lim(0,1,1,\dots)$, 但 $\Phi_U\,1\not\lhd\Phi_U\,\lim(0,1,1,\dots)$. 同 `NegTySupMono.Φ-not-mono` (直接用它的 `MS.notLim`).
>    - **`kept-not-LgB-U` (定理, 实例 `IU`).** 合法的输入 `hΩ (inj₁ κΩ) lift` (第 $X_1\oplus1$ 层, 底种类 $\Omega_1$ 的结点, 分支是坐标自己; `Lg-inΩ`) 折到 $X_1$ 层: 留下 $\Omega_1$ 结点, 输出**不满足 `LgB`**. 中间层的输出只有 `PH` (与 `Sh`), 不是树自己的合法.
> 4. **地板的盲区落到折叠上 (`flat-U1`, 定理).** 在 `NegX1UpIf.hzTopOf IU` (地板换成 $0$, 仍是实例) 上, 同一公式 `ΦX 1 (topU 1)` 不含 $\Omega$-结点; 再交给 `Ψ` 时不经 `dec` (`NegX1UpFlat.Ψ-noΩ`). 构造一路的实例用 `topL`, 不落在这里 (1); 落不落取决于接口没有约束的字段.
> 5. **读法 (判断).** `ΦX 1 (topU 1)` 是从 `topL` 起步的同层链 $b_{n+1}=b_n\boxplus\Phi_U(\mathrm{up}(\mathrm{topL}\boxplus b_n))$, $\Phi_U\circ\mathrm{up}$ 留下一切底种类 (1), 读 $\varepsilon_{\Omega_{\Omega_1}+1}$ 一类的第 $X_1$ 层值; 再经 `Ψ` 读 ψ₀(Ω_{Ω_1+1}). 所以按读法越过了 ψ₀(Ω_{Ω_1}) (= PathOut 与 TySup 的读法), 不是可数层号的重写 (1 是这一点的字面依据: 中间值里有 $\Omega_1$-结点). 这一条是读法, 没有值的定理; 定理档只到 1, 3, 4.
>
> **前提实例.** 3: 输入 `inΩ` 合法 (`Lg-inΩ`), 世界 `wB c′` 合法 (`lgwB`, `Lg-hI`). 4: `hzTopOf IU` 是实例 (构造).
>
> **只否定什么.** 只否定: (a) 上层折叠保字面第一位置 (3); (b) 上层折叠的中间输出满足 `LgB` (3, 在一个合法输入上; 闭项 `TU1` 的中间值里是否出现同样的不单调, 本篇未证, 判断: 出现); (c) `OkU` 对底种类说了层号 (2); (d) 接口保证同层链不塌 (4). **不否定**: `PH-ΦU`, `PH-ΦX` (构造一路的定理), 闭项 `TU m`, `TU2` 的 `LgB` 证书, `okU`; 读法. 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegX1UpInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥)
open import OCF.Align.TySupIf using (AccR; acc; Dc; keep; same; above)
open import OCF.Align.TySupC using (Cd; _⊑ᶜ_; _⊏ᶜ_; wfC)
open import OCF.Align.TySupSum using (ICdΣ)
open import OCF.Align.PathOutX1 using (XS₁; κΩ)
open import OCF.Align.PathOut using (topL; gt)
open import OCF.Align.X1UpIf
import OCF.Align.X1UpFold as UF
open import OCF.Align.X1Up using (IU; OkU)
open import OCF.Align.NegTySupMono using (module MS; module NotMono)
open import OCF.Align.NegPathOutLg using (module Spread)
open import OCF.Align.NegPathOutWorld using (G₁)
open import OCF.Align.NegX1UpFlat using (NoΩ; noΩ-up; module FoldΦ)
open import OCF.Align.NegX1UpIf using (hzTopOf)
open import OCF.Align.NegX1UpEmb using (LU)
open Spread G₁ using (wB; lgwB)
```

## §1 $X_1$ 的种类被留下

```agda
open UF IU using (LS; topU; ΦU; ΦX; decU; clD; emb; frE; ClD; bas; nw)

IsΩ₁ : HB XS₁ → Set
IsΩ₁ (hΩ (inj₁ _ , inj₂ _) _) = ⊤
IsΩ₁ _ = ⊥

at : ∀ {S : KS} → HB S → ℕ → HB S
at (hl f) n = f n
at x n = x

root-Ω₁ : IsΩ₁ (at (ΦX (hs hz) tt (topU (hs hz))) 0)
root-Ω₁ = tt

keep-base : ∀ m t pt lm κ κ₀ (to : E XS₁ κ₀ → E (LS m) κ) →
  decU m t pt lm κ (bas κ₀ to) ≡ keep (emb t κ₀) (λ c → to (frE t κ₀ c))
keep-base m t pt lm κ κ₀ to = refl
```

## §2 决定: `OkU` 对底种类不说层号

```agda
OkU-bas-blind : ∀ {m t κ} κ₀ (to : E XS₁ κ₀ → E (LS m) κ) (κ′ : K (LS t)) fr →
  OkU {m} {t} (bas κ₀ to) (keep κ′ fr) ≡ ⊤
OkU-bas-blind κ₀ to κ′ fr = refl

-- 测试: 具体层号上, LS 与 ofU 的种类结构字面相同
LS≡LU-2 : LS (hs (hs hz)) ≡ LU (hs (hs hz))
LS≡LU-2 = refl
```

## §3 合法性: 上层折叠不单调, 留下的结点不合法

```agda
module NotMonoU (U : X1UpIf) where
  module V = UF U

  ΦU-not-mono : ∀ m (a : AccR _⊏ᶜ_ m) lm t pt b {w : Wd (V.LS t)} →
    ¬ (V.ΦU m a lm t pt b (hs hz) ⊲[ w ] V.ΦU m a lm t pt b (NotMono.hI ICdΣ))
  ΦU-not-mono m (acc rs) lm t pt b p =
    MS.notLim ICdΣ {V.LS t} (λ n → V.ΦU m (acc rs) lm t pt b (NotMono.fI ICdΣ n)) refl (λ _ → refl) p
```

合法输入: 第 $X_1\oplus1$ 层, 底种类 $\Omega_1$ (`inj₁ κΩ`) 的结点, 分支在坐标 $c$ 处是 $c$ 自己 (`lift`).

```agda
lift : ∀ {S : KS} → HB S⊥ → HB S
lift hz = hz
lift (hs c) = hs (lift c)
lift (hl f) = hl (λ n → lift (f n))
lift (hΩ () _)

lift-⊲ : ∀ {S : KS} {w : Wd S} {c c′ : HB S⊥} → c ⊲[ tt ] c′ → lift {S} c ⊲[ w ] lift {S} c′
lift-⊲ hself = hself
lift-⊲ {S} {w} (hsuc p) = hsuc (lift-⊲ {S} {w} p)
lift-⊲ {S} {w} (hlim n p) = hlim n (lift-⊲ {S} {w} p)
lift-⊲ (hLim {κ = ()} _ _)

Lg-lift : ∀ {S : KS} c → LgB c → LgB {S} (lift c)
Lg-lift hz _ = tt
Lg-lift {S} (hs c) l = Lg-lift {S} c l
Lg-lift {S} (hl f) (st , l) = (λ {w} n → lift-⊲ {S} {w} (st n)) , (λ n → Lg-lift {S} (f n) (l n))
Lg-lift (hΩ () _) _

inΩ : HB (LS (hs hz))
inΩ = hΩ (inj₁ κΩ) lift

Lg-inΩ : LgB inΩ
Lg-inΩ = (λ {w} lw e e′ p → lift-⊲ {LS (hs hz)} {w} p) , (λ c lc → Lg-lift {LS (hs hz)} c lc)

outΩ : HB XS₁
outΩ = ΦX (hs hz) tt inΩ

-- 输出就是留下的 Ω₁ 结点, 分支是 ΦU 作用在 lift c 上
out-shape : outΩ ≡ hΩ κΩ (λ c → ΦU (hs hz) (wfC (hs hz)) tt hz (z⊲ᴮ (hs hz)) topL (lift c))
out-shape = refl

kept-not-LgB-U : ¬ LgB outΩ
kept-not-LgB-U (mo , _) =
  MS.notLim ICdΣ {XS₁} (λ n → ΦU (hs hz) (wfC (hs hz)) tt hz (z⊲ᴮ (hs hz)) topL (lift (NotMono.fI ICdΣ n)))
    refl (λ _ → refl)
    (mo {wB c′} (lgwB c′ (NotMono.Lg-hI ICdΣ)) (hlim 1 hself) hself (hlim 1 hself))
  where
  c′ : HB S⊥
  c′ = NotMono.hI ICdΣ
```

## §4 地板换成 $0$: 同一公式不含结点

```agda
module Flat0 where
  I0 : X1UpIf
  I0 = hzTopOf IU
  open UF I0 using () renaming (ΦU to ΦU0; ΦX to ΦX0; topU to topU0)
  open FoldΦ ICdΣ using (nmul; nchain; nΣ)

  ΦU0-noΩ : ∀ m a lm t pt b h → NoΩ h → NoΩ (ΦU0 m a lm t pt b h)
  ΦU0-noΩ m (acc rs) lm t pt b hz nh = tt
  ΦU0-noΩ m (acc rs) lm t pt b (hs h) nh = nmul _ (ΦU0-noΩ m (acc rs) lm t pt b h nh)
  ΦU0-noΩ m (acc rs) lm t pt b (hl f) nh = nΣ _ (λ n → ΦU0-noΩ m (acc rs) lm t pt b (f n) (nh n))
  ΦU0-noΩ m (acc rs) lm t pt b (hΩ κ g) ()

  flat-U1 : NoΩ (ΦX0 (hs hz) tt (topU0 (hs hz)))
  flat-U1 = λ n → nchain hz _ tt
    (λ c nc → ΦU0-noΩ (hs hz) (wfC (hs hz)) tt hz (z⊲ᴮ (hs hz)) c (up c) (noΩ-up c nc)) n
```

## 结论 (按档)

- **[定理]** `IsΩ₁`, **`root-Ω₁`**, **`keep-base`**; **`OkU-bas-blind`**; **`NotMonoU.ΦU-not-mono`** (对一切 `U`); `lift`, `lift-⊲`, `Lg-lift`, `inΩ`, **`Lg-inΩ`**, `out-shape`, **`kept-not-LgB-U`**; `Flat0.ΦU0-noΩ`, **`Flat0.flat-U1`**.
- **[测试]** `LS≡LU-2` (具体层号).
- **[判断]** 读法 ψ₀(Ω_{Ω_1+1}) (`TU1`) 与 ψ₀(Ω_{Ω_1·2}) (`TU2`); 闭项 `TU1` 的中间值里也有不合法的留下结点 (未证).
