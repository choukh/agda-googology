# 级回灌参数 `Fb`, 否定一路 (一): 接口定稿之前 — 盲, 执行条件, 跨级族, 点世界

> 不含记号. 入口 [NegLeanFb](NegLeanFb.lagda.md). 本篇**不依赖**构造一路的接口 `LeanFbIf` (接口定稿之前写的部分), 只读导入 [LeanTBase](LeanTBase.lagda.md), [LeanTLv](LeanTLv.lagda.md), [LeanTTree](LeanTTree.lagda.md), [LeanTFold](LeanTFold.lagda.md) 与 [LeanT](LeanT.lagda.md) 的 `Λ′`. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延 `FEℕL`, `FEΩL` 只在标 "条件" 的定理里作前提.
>
> **问题.** [LeanT](LeanT.lagda.md) §3 说 `TΛ′` 不执行任何回灌 (`old-target` 是定理, "不执行" 是判断). 构造一路要在同一个折叠上给级回灌参数 `fb : K T → Fb ⊎ ⊤` 的非平凡实例. 本篇回答三个不依赖接口的问题:
>
> 1. **`Fb` 记录本身逼不逼回灌读数据、升世界?** (§1) 不逼. **`stayFb`** (对一切 $T,\Lambda$) 不升世界, 折叠里每一格的世界都等于当前世界 (**`stay-wA`**, 定理); **`relevelFb`** 把任一 `Fb` 改成级层 $0$, 升界不看数据, 折叠里每一格的世界与合法证据都与分支, 累计数据, 状态无关 (**`relevel-u`**, 定理). 所以 "`fb κ = inj₁ F`" 只说那一行被选中, 不说回灌读了什么或升了什么.
> 2. **回灌那一行什么时候被执行?** (§2) **`exec-old`** (定理, 对一切折叠参数): 在第 $0$ 层目标上折叠一个头为旧种类 $\kappa$ 的层的 $\Omega_L$, 输出字面地含 `RKa ac (fb κ) …`; 头不是旧种类时不经过这一行 (按定义). **`hd-target`** (定理): 若 $\Lambda$ 的一切 $\Omega$-结点的种类都满足 $P$, 则一切目标层 ($t\lhd\Lambda$) 的头种类满足 $P$. 两者合起来: 回灌行在某个旧种类 $\kappa$ 上执行, **必须** $\kappa$ 是 $\Lambda$ 里某个第一位置的头 (这一步的 "必须" 还要一条对折叠数据的不变式, 没写, 记为判断); 反过来, $\kappa$ 是某个目标层的头时, 那一层的 $\Omega_L$ 在第 $0$ 层目标上执行它 (`exec-old`); 那一层的 $\Omega_L$ 是否真被折叠到, 是对整个折叠的判断.
> 3. **`Λ′` 里有没有跨级族?** (§3) 有. **`cross-tg`** (定理): 对每个合法的 $c$ : `HB S⊥`, 层 $\Lambda'$ 在基世界之上的一个合法世界 `(wAt c , hz)` 里有目标层, 头种类是旧种类 `inj₁ (νL (kc c))`, 其中 `kc c = ofHB (1 ⊞ ι lz (up c))`. 这些层号两两不同 (`dep-kc`: 有限 $c$ 处 `dep` 是 $c+1$), 坐标类型 `HB (Lv (kc c))` 随 $c$ 变; 除 $c=0$ (`kc 0` 是第 1 站的层号, `kc0-station`) 外都**不是站的层号** (`kc-suc-not-station`, `kc-hl-not-station`). $c=\mathrm{hl}\,f$ 处层号是 `ll (kc ∘ f)` (`kc-hl`, 含函数).
> 4. **对跨级族的成员能不能精确回灌?** (§4) **`wdec1`** (定理): 只要**一个**世界 $W$ 把 `νL s` 的界升到 $1$ 以上, 而一切别的 `νL k` 在 $W$ 里的界之下的坐标在基世界里也在界之下, 就对一切 $k$ 弱判定 $k\equiv s$. 推论 **`cross-sep`** (定理): 对族里任一含函数的成员 $s=$ `kc (hl f)`, 这样的世界推出分离子 `SepLl`; **`stage-sep`** (定理): 对第 $n+2$ 站的层号同样 (分离子 `SepLΩ`). 有外延时推出 WLPO (**条件** `FEℕL`, `FEΩL`: `cross-WLPO`, `stage-WLPO`). 一个 `Fb` 在**基世界**上的一次升界 `nx F lw₀ x` 就是这样一个世界, 所以对这些种类 "升自己, 别处不动" 的回灌推出分离子 (`fb-cross-sep`).
> 5. **前提可满足, 两半各自可满足** (§5): 只升 (`wAll`, 一切 `νL k` 的界都是 $1$), 只留 (`wb`); 在可按构造子判定的层号 `ls lz` 上两半同时成立 (`wLs`). 不读层的非有损回灌是构造: **`allFb`** 让一切种类都有回灌 (没有有损种类), 但它把每一层的界加上**同一个**可数值 (**`all-raise`**, `refl`), 一次调用就升了一切层 (**`all-moves`**).
>
> **只否定什么.** (i) 推断 "`fb κ = inj₁ F`, 所以回灌读了数据或升了界" (§1); (ii) 在 `SL` 的世界上存在一个世界, 只升跨级族里一个含函数的成员 (或第 $n+2$ 站) 而不升别的任何层 (§4, 分离子; 加外延是 WLPO). **不否定**: 一起升 (`allFb`, `wAll`); 只留 (`wb`); 在可判定层号上的点更新 (`wLs`); 带证据的世界类型 (本篇的世界是 `Wd SL` 本身; 若构造一路换了世界类型, 只要基世界在里面, 同一论证照用, 但要对新类型重写, 未写); 有损的回灌; 不精确的回灌 (升自己也动别处, 但不是全升). "总有有损种类" **不是**定理: `allFb` 说一切种类都可以非有损; 定理说的是: 对跨级族的含函数成员, 非有损的回灌不能是 "只升自己". 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLeanFbPre where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanTTree
import OCF.Lean.LeanTFold as FoldM
open import OCF.Lean.LeanT using (Λ′)
```

## §1 `Fb` 的盲区

**不升** (`stayFb`): 级层 $0$, 起点空, 升界返回当前世界. **改级** (`relevelFb F`): 级层 $0$, 升界取 `F` 在空数据上的升界, 不看级层数据.

```agda
module Blind (T : KS) (Λ : HB (step T)) where
  open Tree T
  open FoldTy T Λ

  stayFb : Fb
  stayFb = record
    { ℓ = hz ; ℓ⊲ = z⊲ᴮ Λ ; d₀ = λ _ _ → n0
    ; nx = λ {W} _ _ → proj₁ W ; nx≤ = λ _ _ → ≤w-rf T ; nxLg = λ lW _ → proj₁ lW }

  relevelFb : Fb → Fb
  relevelFb F = record
    { ℓ = hz ; ℓ⊲ = z⊲ᴮ Λ ; d₀ = λ _ _ → n0
    ; nx = λ lW _ → nx F lW n0 ; nx≤ = λ lW _ → nx≤ F lW n0 ; nxLg = λ lW _ → nxLg F lW n0 }

  relevel-ℓ : ∀ F → ℓ (relevelFb F) ≡ hz
  relevel-ℓ F = refl

  relevel-blind : ∀ F {W} (lW : LgW L₀ W) (x y : D hz W) → nx (relevelFb F) lW x ≡ nx (relevelFb F) lW y
  relevel-blind F lW x y = refl
```

**在折叠里.** 对任一折叠参数打开 [LeanTFold](LeanTFold.lagda.md). `stay-wA`: 用 `stayFb` 时级回灌的每一格的世界都是当前世界. `relevel-u`: 用 `relevelFb F` 时每一格的 (世界, 合法证据) 与分支 `u`, 动作 `A₀`, 累计数据 `w`, 状态 `Y` 都无关.

```agda
module BlindRun (T : KS) (bk : Tree.BotK T) (Λ : HB (step T)) (lΛ : LgB Λ)
  (one⊲ : ∀ {w} → hs hz ⊲[ w ] Λ) (fb : K T → FoldTy.Fb T Λ ⊎ ⊤) where
  open Tree T
  open FoldTy T Λ
  open Blind T Λ
  open FoldM T bk Λ lΛ one⊲ fb

  stay-wA : ∀ {ly W₀ W} (ac : AccY ly) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W) (lL : LW ly W)
            (A₀ : Ig ly W) (w : D ly W) (Y : St W) n → wA (κcF ac stayFb u q₀ lW lL A₀ w Y n) ≡ proj₁ W
  stay-wA ac u q₀ lW lL A₀ w Y zero = refl
  stay-wA ac u q₀ lW lL A₀ w Y (suc n) = stay-wA ac u q₀ lW lL A₀ w Y n

  wl : ∀ {W ly} → ClA W ly → Σ (Wd T) (LgW T)
  wl c = wA c , lwA c

  relevel-u : ∀ (F : Fb) {ly W₀ W} (ac : AccY ly) (u u′ : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W) (lL : LW ly W)
              (A₀ A₀′ : Ig ly W) (w w′ : D ly W) (Y Y′ : St W) n →
              wl (κcF ac (relevelFb F) u q₀ lW lL A₀ w Y n) ≡ wl (κcF ac (relevelFb F) u′ q₀ lW lL A₀′ w′ Y′ n)
  relevel-u F ac u u′ q₀ lW lL A₀ A₀′ w w′ Y Y′ zero = refl
  relevel-u F {W = W} ac u u′ q₀ lW lL A₀ A₀′ w w′ Y Y′ (suc n) =
    cong (λ p → nx F {proj₁ p , proj₂ W} (proj₂ p , proj₂ lW) n0 , nxLg F {proj₁ p , proj₂ W} (proj₂ p , proj₂ lW) n0)
      (relevel-u F ac u u′ q₀ lW lL A₀ A₀′ w w′ Y Y′ n)
```

## §2 回灌那一行什么时候被执行

**`exec-old`.** 折叠一个头为旧种类 `inj₁ κ` 的层 $L$ 的 $\Omega_L$ (`n1 ⨾ nc (inj₁ κ) …`), 在第 $0$ 层目标上的输出是 "动作的输出 ⨾ `RKa ac (fb κ) …`". 这一行按 `fb κ` 分: `inj₁ F` 是级回灌 (`κcF`), `inj₂ tt` 是有损. (新种类在第 $0, 1$ 层目标上的回灌 `κc₁` 同理, 由 `Ωd (hΩ (inj₂ tt) g)` 生出.)

```agda
  exec-old : ∀ (κ : K T) (g : E T κ → HB L₀) {W₀ W} (ac : AccY (hΩ (inj₁ κ) g)) (q₀ : W₀ ≤ W) (lW : LgW L₀ W)
             (lL : LW (hΩ (inj₁ κ) g) W) (A₀ : Ig (hΩ (inj₁ κ) g) W) (w : D (hΩ (inj₁ κ) g) W) (Y : St W) →
             yc (Run ac (Ωd (hΩ (inj₁ κ) g) {W₀}) q₀ lW lL A₀ w Y) (τ₀ lW)
               ≡ yc (A₀ ≤rf lW w Y) (τ₀ lW) ⨾ RKa ac (fb κ) _ q₀ lW lL A₀ (w ⨾ nw q₀ n1) (Y ⊕⟨ lW ⟩ A₀ ≤rf lW w Y) (τ₀ lW)
  exec-old κ g ac q₀ lW lL A₀ w Y = refl
```

**`hd-target`.** `AllK P L`: $L$ 的一切 $\Omega$-结点 (沿一切坐标) 的种类满足 $P$. 它沿第一位置向下封闭, 所以一切目标层的头种类满足 $P$. 取 $P\,\kappa$ = "`fb` 在 $\kappa$ 上有损" 就是: $\Lambda$ 里不出现的旧种类, 不是任何目标层的头.

```agda
module _ {S : KS} (P : K S → Set) where
  AllK : HB S → Set
  AllK hz = ⊤
  AllK (hs h) = AllK h
  AllK (hl f) = ∀ n → AllK (f n)
  AllK (hΩ κ g) = P κ × (∀ c → AllK (g c))

  allK-⊲ : ∀ {k L w} → k ⊲[ w ] L → AllK L → AllK k
  allK-⊲ hself a = a
  allK-⊲ (hsuc p) a = allK-⊲ p a
  allK-⊲ (hlim n p) a = allK-⊲ p (a n)
  allK-⊲ (hLim e p) a = allK-⊲ p (proj₂ a _)

  hd-target : ∀ {L w κ g} → AllK L → hΩ κ g ⊲[ w ] L → P κ
  hd-target a p = proj₁ (allK-⊲ p a)
```

## §3 `Λ′` 里的跨级族

`kc c = ofHB (1 ⊞ ι lz (up c))`. 世界 `wAt c`: 第 `lz` 层的新界是 $c+1$, 别处是基世界. 路径: $\Lambda$ 的第 3 项 `tw 3` 的头是 `νL lz`, 在坐标 $c+1$ 处的分支是 $\hat\Omega(1\boxplus\iota(c)+1)$, 头是 `νL (kc c)`.

```agda
wb : Wd SL
wb = w₀ SL

wAt : HB S⊥ → Wd SL
wAt c lz = w₀ S⊥ , hs c
wAt c (ls x) = wb (ls x)
wAt c (ll f) = wb (ll f)
wAt c (lΩ k g) = wb (lΩ k g)

lwAt : ∀ c → LgB c → LgW SL (wAt c)
lwAt c l lz = lw₀ S⊥ , l
lwAt c l (ls x) = lw₀ SL (ls x)
lwAt c l (ll f) = lw₀ SL (ll f)
lwAt c l (lΩ k g) = lw₀ SL (lΩ k g)

wb≤wAt : ∀ c → _≤w_ SL wb (wAt c)
wb≤wAt c lz = ≤w-rf S⊥ , z⊲ᴮ (hs c)
wb≤wAt c (ls x) = ≤w-rf (FL (ls x))
wb≤wAt c (ll f) = ≤w-rf (FL (ll f))
wb≤wAt c (lΩ k g) = ≤w-rf (FL (lΩ k g))

kc : HB S⊥ → LH
kc c = ofHB (hs hz ⊞ ι lz (up c))

cross-occ : ∀ c → Σ (HB (Lv (kc c)) → HB SL) (λ g → hΩ (νL (kc c)) g ⊲[ wAt c ] Λ)
cross-occ c = _ , hlim 3 (hLim {κ = νL lz} {c = hs c} hself hself)

cross-occ′ : ∀ c → Σ (HB (Lv (kc c)) → HB (step SL)) (λ g → hΩ (inj₁ (νL (kc c))) g ⊲[ (wAt c , hz) ] Λ′)
cross-occ′ c = _ , ⊞-⊲ (hs hz) (up-⊲ (proj₂ (cross-occ c)))
```

**是闭项的折叠的目标.** 从基世界 `w₀ (step SL)` 出发, `(wAt c , hz)` 更大且合法, 层在 $\Lambda'$ 之下: 一个 `Tg` (折叠的目标记录).

```agda
module _ where
  open FoldTy SL Λ′

  cross-tg : ∀ c → LgB c → Σ (HB (Lv (kc c)) → HB (step SL)) (λ g → Tg (w₀ (step SL)) (hΩ (inj₁ (νL (kc c))) g) (wAt c , hz))
  cross-tg c l = proj₁ (cross-occ′ c) , tg (wb≤wAt c , hself) (proj₂ (cross-occ′ c)) (lwAt c l , tt)
```

**层号两两不同, 不是站.** `dep`: 前面 `ls` 的个数.

```agda
dep : LH → ℕ
dep (ls y) = suc (dep y)
dep _ = zero

num : ∀ {S : KS} → ℕ → HB S
num zero = hz
num (suc n) = hs (num n)

lsN : ℕ → LH
lsN zero = lz
lsN (suc n) = ls (lsN n)

kc-num : ∀ n → kc (num n) ≡ lsN (suc n)
kc-num zero = refl
kc-num (suc n) = cong ls (kc-num n)

dep-lsN : ∀ n → dep (lsN n) ≡ n
dep-lsN zero = refl
dep-lsN (suc n) = cong suc (dep-lsN n)

dep-kc : ∀ n → dep (kc (num n)) ≡ suc n
dep-kc n = trans (cong dep (kc-num n)) (dep-lsN (suc n))

kc-distinct : ∀ m n → kc (num m) ≡ kc (num n) → m ≡ n
kc-distinct m n e = cong pred (trans (sym (dep-kc m)) (trans (cong dep e) (dep-kc n)))
  where pred : ℕ → ℕ
        pred zero = zero
        pred (suc k) = k

kc-hl : ∀ f → kc (hl f) ≡ ll (λ n → kc (f n))
kc-hl f = refl
```

**站的层号** (同 `NegSLFbSep.stage-lΩ`, 在 `OCF.Lean` 的类型上重写): 第 $n+2$ 站是 `lΩ lz g`.

```agda
tw-hΩ : ∀ n → Σ (HB S⊥ → HB SL) (λ g → tw (suc (suc n)) ≡ hΩ (νL lz) g)
tw-hΩ zero = _ , refl
tw-hΩ (suc n) = _ , cong Ω̂ (proj₂ (tw-hΩ n))

stage-lΩ : ∀ n → Σ (HB S⊥ → LH) (λ g → ofHB (tw (suc (suc n))) ≡ lΩ lz g)
stage-lΩ n = (λ c → ofHB (proj₁ (tw-hΩ n) c)) , cong ofHB (proj₂ (tw-hΩ n))

kc0-station : kc hz ≡ ofHB (tw 1)
kc0-station = refl

dep-station : ∀ m → (dep (ofHB (tw m)) ≡ 0) ⊎ (dep (ofHB (tw m)) ≡ 1)
dep-station zero = inj₁ refl
dep-station (suc zero) = inj₂ refl
dep-station (suc (suc m)) = inj₁ (cong dep (proj₂ (stage-lΩ m)))

kc-suc-not-station : ∀ n m → ¬ (kc (num (suc n)) ≡ ofHB (tw m))
kc-suc-not-station n m e with dep-station m
... | inj₁ d = s≢0 (trans (sym (dep-kc (suc n))) (trans (cong dep e) d))
  where s≢0 : ∀ {k} → ¬ (suc k ≡ 0)
        s≢0 ()
... | inj₂ d = ss≢1 (trans (sym (dep-kc (suc n))) (trans (cong dep e) d))
  where ss≢1 : ∀ {k} → ¬ (suc (suc k) ≡ 1)
        ss≢1 ()

kc-hl-not-station : ∀ f m → ¬ (kc (hl f) ≡ ofHB (tw m))
kc-hl-not-station f zero ()
kc-hl-not-station f (suc zero) ()
kc-hl-not-station f (suc (suc m)) e = ll≢lΩ (trans e (proj₂ (stage-lΩ m)))
  where ll≢lΩ : ∀ {h k g} → ¬ (ll h ≡ lΩ k g)
        ll≢lΩ ()
```

## §4 只升一层的世界 ⇒ 弱判定 ⇒ 分离子

`Raise s W`: `νL s` 在 $W$ 里的界 $\ge 1$. `Keep s W`: 对一切裸下标 $k\ne s$, `νL k` 在 $W$ 的界之下的坐标, 在基世界 (界 $0$) 的界之下.

```agda
Raise : LH → Wd SL → Set
Raise s W = Bd SL (νL s) (hs hz) W

Keep : LH → Wd SL → Set
Keep s W = ∀ k → ¬ (k ≡ s) → ∀ {c} → Bd SL (νL k) c W → Bd SL (νL k) c wb

one⊀z : ∀ {S : KS} {w} → ¬ (hs {S} hz ⊲[ w ] hz)
one⊀z ()

notz : ∀ {S : KS} {w} {x : HB S} → ¬ (x ≡ hz) → ¬ (x ⊲[ w ] hz)
notz ne hself = ne refl

wdec1 : ∀ s W → Raise s W → Keep s W → ∀ k → ¬ (k ≡ s) ⊎ ¬ ¬ (k ≡ s)
wdec1 s W r kp k = go (proj₂ (W k)) refl
  where
  go : ∀ v → proj₂ (W k) ≡ v → ¬ (k ≡ s) ⊎ ¬ ¬ (k ≡ s)
  go hz eq = inj₁ (λ e → one⊀z (subst (λ b → hs hz ⊲[ proj₁ (W k) ] b) eq (subst (λ x → Raise x W) (sym e) r)))
  go (hs v) eq = inj₂ (λ ne → notz (λ ()) (kp k ne (subst (λ b → hs v ⊲[ proj₁ (W k) ] b) (sym eq) hself)))
  go (hl f) eq = inj₂ (λ ne → notz (λ ()) (kp k ne (subst (λ b → hl f ⊲[ proj₁ (W k) ] b) (sym eq) hself)))
  go (hΩ κ f) eq = inj₂ (λ ne → notz (λ ()) (kp k ne (subst (λ b → hΩ κ f ⊲[ proj₁ (W k) ] b) (sym eq) hself)))
```

**补丁.** `ll h` 旁边: 在第 $n$ 项, $\alpha\,n$ 为真时换成 `ls (h n)`. `lΩ k g` 旁边: 在坐标 `num n` 处同理 (同 `NegSLFbSep`). 从补丁等于原层号读出 $\alpha$ 全假不用外延 (`dep` 在第 $n$ 项比较); 反方向要外延.

```agda
sel : Bool → LH → LH
sel true y = ls y
sel false y = y

suc≢ : ∀ n → ¬ (suc n ≡ n)
suc≢ zero ()
suc≢ (suc n) e = suc≢ n (cong pr e)
  where pr : ℕ → ℕ
        pr zero = zero
        pr (suc m) = m

sel-dep : ∀ b y → dep (sel b y) ≡ dep y → b ≡ false
sel-dep true y e = ⊥-elim (suc≢ (dep y) e)
sel-dep false y e = refl

t≢f : ¬ (true ≡ false)
t≢f ()

WLPO : Set
WLPO = ∀ (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ ¬ (∀ n → α n ≡ false)

-- ll 旁边
hα : (ℕ → LH) → (ℕ → Bool) → ℕ → LH
hα h α n = sel (α n) (h n)

SepLl : (ℕ → LH) → Set
SepLl h = ∀ (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ ¬ (ll (hα h α) ≡ ll h)

depAtL : LH → ℕ → ℕ
depAtL (ll h) n = dep (h n)
depAtL _ n = zero

eq→Fl : ∀ h α → ll (hα h α) ≡ ll h → ∀ n → α n ≡ false
eq→Fl h α e n = sel-dep (α n) (h n) (cong (λ x → depAtL x n) e)

wdec→sepLl : ∀ h → (∀ k → ¬ (k ≡ ll h) ⊎ ¬ ¬ (k ≡ ll h)) → SepLl h
wdec→sepLl h D α with D (ll (hα h α))
... | inj₁ ne = inj₂ ne
... | inj₂ nn = inj₁ nnF
  where
  nnF : ∀ n → α n ≡ false
  nnF n with α n in eq
  ... | false = refl
  ... | true = ⊥-elim (nn (λ e → t≢f (trans (sym eq) (eq→Fl h α e n))))

FEℕL : Set
FEℕL = ∀ (h h′ : ℕ → LH) → (∀ n → h n ≡ h′ n) → h ≡ h′

sepLl→WLPO : FEℕL → ∀ h → SepLl h → WLPO
sepLl→WLPO fe h S α with S α
... | inj₁ x = inj₁ x
... | inj₂ ne = inj₂ (λ hf → ne (cong ll (fe (hα h α) h (λ n → cong (λ b → sel b (h n)) (hf n)))))

-- lΩ 旁边
nat : ∀ {S : KS} → HB S → ℕ
nat (hs c) = suc (nat c)
nat _ = zero

nat-num : ∀ {S : KS} n → nat {S} (num {S} n) ≡ n
nat-num zero = refl
nat-num (suc n) = cong suc (nat-num n)

gα : ∀ {k : LH} → (HB (Lv k) → LH) → (ℕ → Bool) → HB (Lv k) → LH
gα g α c = sel (α (nat c)) (g c)

SepLΩ : (k : LH) → (HB (Lv k) → LH) → Set
SepLΩ k g = ∀ (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ ¬ (lΩ k (gα {k} g α) ≡ lΩ k g)

depAtΩ : LH → ℕ → ℕ
depAtΩ (lΩ k h) n = dep (h (num n))
depAtΩ _ n = zero

eq→FΩ : ∀ k g α → lΩ k (gα {k} g α) ≡ lΩ k g → ∀ n → α n ≡ false
eq→FΩ k g α e n =
  sel-dep (α n) (g (num n))
    (subst (λ m → dep (sel (α m) (g (num n))) ≡ dep (g (num n))) (nat-num {Lv k} n) (cong (λ x → depAtΩ x n) e))

wdec→sepLΩ : ∀ k g → (∀ k′ → ¬ (k′ ≡ lΩ k g) ⊎ ¬ ¬ (k′ ≡ lΩ k g)) → SepLΩ k g
wdec→sepLΩ k g D α with D (lΩ k (gα {k} g α))
... | inj₁ ne = inj₂ ne
... | inj₂ nn = inj₁ nnF
  where
  nnF : ∀ n → α n ≡ false
  nnF n with α n in eq
  ... | false = refl
  ... | true = ⊥-elim (nn (λ e → t≢f (trans (sym eq) (eq→FΩ k g α e n))))

FEΩL : Set
FEΩL = ∀ (k : LH) (g g′ : HB (Lv k) → LH) → (∀ c → g c ≡ g′ c) → g ≡ g′

sepLΩ→WLPO : FEΩL → ∀ k g → SepLΩ k g → WLPO
sepLΩ→WLPO fe k g S α with S α
... | inj₁ x = inj₁ x
... | inj₂ ne = inj₂ (λ hf → ne (cong (lΩ k) (fe k (gα {k} g α) g (λ c → cong (λ b → sel b (g c)) (hf (nat c))))))
```

**推论.** 跨级族的含函数成员 (`kc (hl f) = ll (kc ∘ f)`) 与第 $n+2$ 站的层号上, 只升这一层的世界推出分离子.

```agda
cross-sep : ∀ f W → Raise (kc (hl f)) W → Keep (kc (hl f)) W → SepLl (λ n → kc (f n))
cross-sep f W r kp = wdec→sepLl (λ n → kc (f n)) (wdec1 (kc (hl f)) W r kp)

cross-WLPO : FEℕL → ∀ f W → Raise (kc (hl f)) W → Keep (kc (hl f)) W → WLPO
cross-WLPO fe f W r kp = sepLl→WLPO fe (λ n → kc (f n)) (cross-sep f W r kp)

stage-sep : ∀ n W → Raise (ofHB (tw (suc (suc n)))) W → Keep (ofHB (tw (suc (suc n)))) W →
            SepLΩ lz (proj₁ (stage-lΩ n))
stage-sep n W r kp =
  wdec→sepLΩ lz (proj₁ (stage-lΩ n))
    (wdec1 (lΩ lz (proj₁ (stage-lΩ n))) W
      (subst (λ s → Raise s W) (proj₂ (stage-lΩ n)) r)
      (subst (λ s → Keep s W) (proj₂ (stage-lΩ n)) kp))

stage-WLPO : FEΩL → ∀ n W → Raise (ofHB (tw (suc (suc n)))) W → Keep (ofHB (tw (suc (suc n)))) W → WLPO
stage-WLPO fe n W r kp = sepLΩ→WLPO fe lz (proj₁ (stage-lΩ n)) (stage-sep n W r kp)
```

**`Fb` 版.** `SL` 上任一 `Fb` 在基世界上的一次升界 `nx F lw₀ x` 是一个世界; 它若只升 `νL (kc (hl f))`, 就是分离子.

```agda
module _ (Λ : HB (step SL)) where
  open Tree SL
  open FoldTy SL Λ

  fb-cross-sep : ∀ (F : Fb) f (x : D (ℓ F) (w₀ L₀)) →
                 Raise (kc (hl f)) (nx F (lw₀ L₀) x) → Keep (kc (hl f)) (nx F (lw₀ L₀) x) → SepLl (λ n → kc (f n))
  fb-cross-sep F f x = cross-sep f (nx F (lw₀ L₀) x)
```

## §5 前提可满足; 一起升的非有损回灌

**两半各自可满足.** 只升: `wAll` (一切 `νL k` 的界是 $1$). 只留: `wb`. 在 `ls lz` (`kc 0`, 第 1 站) 上两半同时成立: `wLs`, 按构造子匹配.

```agda
wAll : Wd SL
wAll k = w₀ (Lv k) , hs hz

raise-all : ∀ s → Raise s wAll
raise-all s = hself

keep-wb : ∀ s → Keep s wb
keep-wb s k ne b = b

wLs : Wd SL
wLs lz = wb lz
wLs (ls lz) = w₀ (Lv (ls lz)) , hs hz
wLs (ls (ls x)) = wb (ls (ls x))
wLs (ls (ll f)) = wb (ls (ll f))
wLs (ls (lΩ k g)) = wb (ls (lΩ k g))
wLs (ll f) = wb (ll f)
wLs (lΩ k g) = wb (lΩ k g)

raise-Ls : Raise (ls lz) wLs
raise-Ls = hself

keep-Ls : Keep (ls lz) wLs
keep-Ls lz ne b = b
keep-Ls (ls lz) ne b = ⊥-elim (ne refl)
keep-Ls (ls (ls x)) ne b = b
keep-Ls (ls (ll f)) ne b = b
keep-Ls (ls (lΩ k g)) ne b = b
keep-Ls (ll f) ne b = b
keep-Ls (lΩ k g) ne b = b
```

**一起升, 没有有损种类.** `emb`: `HB S⊥` 嵌入任一 `HB S`. `allFb`: 级层 $0$, 起点是第 $0$ 层的输出, 升界把**每一层**的界加上同一个可数值 `emb (sum hz x)`. `fbAll` 对一切种类给 `inj₁ allFb`: 没有有损种类. `all-raise`: 每一层加的是同一个值 (`refl`), 不读层自己的数据; `all-moves`: 从基世界一次调用就把一切 `νL k` 升到 $1$.

```agda
emb : ∀ {S : KS} → HB S⊥ → HB S
emb hz = hz
emb (hs c) = hs (emb c)
emb (hl f) = hl (λ n → emb (f n))
emb (hΩ (() , _) g)

emb-⊲ : ∀ {S : KS} {v w} {a b : HB S⊥} → a ⊲[ v ] b → emb {S} a ⊲[ w ] emb b
emb-⊲ hself = hself
emb-⊲ (hsuc p) = hsuc (emb-⊲ p)
emb-⊲ (hlim n p) = hlim n (emb-⊲ p)
emb-⊲ (hLim {κ = () , _} e p)

Lg-emb : ∀ {S : KS} (a : HB S⊥) → LgB a → LgB (emb {S} a)
Lg-emb hz l = tt
Lg-emb (hs a) l = Lg-emb a l
Lg-emb (hl f) (st , l) = (λ n → emb-⊲ (st {w₀ S⊥} n)) , (λ n → Lg-emb (f n) (l n))
Lg-emb (hΩ (() , _) g) l

module AllFb (Λ : HB (step SL)) where
  open Tree SL
  open FoldTy SL Λ

  rsAll : Wd SL → HB S⊥ → Wd SL
  rsAll w v k = proj₁ (w k) , proj₂ (w k) ⊞ emb v

  allFb : Fb
  allFb = record
    { ℓ = hz ; ℓ⊲ = z⊲ᴮ Λ ; d₀ = λ lW Y → z Y
    ; nx = λ {W} lW x → rsAll (proj₁ W) (sum hz x)
    ; nx≤ = λ {W} lW x k → ≤w-rf (Lv k) , ⊞-fst (proj₂ (proj₁ W k)) (emb (sum hz x))
    ; nxLg = λ {W} lW x k → proj₁ (proj₁ lW k) ,
               Lg-⊞ (proj₂ (proj₁ W k)) (emb (sum hz x)) (proj₂ (proj₁ lW k)) (Lg-emb (sum hz x) (Lg-sum hz x tt)) }

  fbAll : K SL → Fb ⊎ ⊤
  fbAll _ = inj₁ allFb

  all-raise : ∀ {W} (lW : LgW L₀ W) x k → proj₂ (nx allFb lW x k) ≡ proj₂ (proj₁ W k) ⊞ emb (sum hz x)
  all-raise lW x k = refl

  all-moves : ∀ k → Raise k (nx allFb (lw₀ L₀) n1)
  all-moves k = hself
```

## §6 结论 (按档)

- **[定理, 盲]** `stayFb`, **`stay-wA`** (不升的 `Fb`: 级回灌每一格的世界 ≡ 当前世界); `relevelFb`, `relevel-ℓ`, `relevel-blind`, **`relevel-u`** (任一 `Fb` 改成级层 $0$ 且升界不看数据, 折叠里每一格的 (世界, 合法) 与分支, 动作, 累计, 状态无关). 都对一切 $T,\Lambda$, 一切 `bk`, `fb`.
- **[定理, 执行条件]** **`exec-old`** (`refl`; 第 $0$ 层目标上折叠头为旧种类 $\kappa$ 的 $\Omega_L$, 字面地经过 `RKa ac (fb κ)`); `AllK`, `allK-⊲`, **`hd-target`**.
- **[判断]** "回灌行在 $\kappa$ 上执行 ⇒ $\kappa$ 是 $\Lambda$ 某个第一位置的头": 需要一条对折叠数据的不变式 (闭包结点的种类都来自某个目标层的头, 经 `Ωd`, `RKk`, `Int` 只复制种类), 没写. 与 [LeanT](LeanT.lagda.md) §3 的判断同档.
- **[定理, 跨级族]** **`cross-occ`**, **`cross-occ′`**, **`cross-tg`** (对每个合法 $c$, `inj₁ (νL (kc c))` 是 $\Lambda'$ 的目标层的头, 世界从基世界升上来且合法); `kc-num`, **`dep-kc`**, **`kc-distinct`** (有限 $c$ 处两两不同), `kc-hl` (`refl`, 含函数); `tw-hΩ`, `stage-lΩ`, `kc0-station`, `dep-station`, **`kc-suc-not-station`**, **`kc-hl-not-station`** (除 $c=0$ 外不是站).
- **[定理, 否定]** **`wdec1`** (一个只升 `νL s` 的世界 ⇒ 对一切 $k$ 弱判定 $k\equiv s$; 对一切 $s$), `wdec→sepLl`, `wdec→sepLΩ`, `eq→Fl`, `eq→FΩ`, **`cross-sep`**, **`stage-sep`**, **`fb-cross-sep`**. **[条件 `FEℕL` / `FEΩL`]** `sepLl→WLPO`, `sepLΩ→WLPO`, `cross-WLPO`, `stage-WLPO`.
- **[定理, 前提实例]** `raise-all` (只升可满足), `keep-wb` (只留可满足), `raise-Ls`, `keep-Ls` (在 `ls lz` = `kc 0` 上两半同时成立); `cross-tg` 的前提 `LgB c` 对一切有限 $c$ 与 `hl` 合法的 $c$ 成立 (例如 $c=$ `hz`, `tt`). `allFb`, `fbAll` (没有有损种类的 `fb`, 构造), `all-raise`, **`all-moves`** (它一次升一切层: 不满足 `Keep`).
- **[判断]** `SepLl`, `SepLΩ` 经典地成立; `FEℕL`, `FEΩL` 在 Agda 里证不出也否证不了 (与 `NegSLFbSep.FEΩ` 同档). 世界换成带证据的子类型时, 只要基世界在里面, `wdec1` 的论证照用 (它只用一个世界 $W$ 与基世界), 未对具体的新类型重写.
