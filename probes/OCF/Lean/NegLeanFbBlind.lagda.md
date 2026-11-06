# 级回灌参数 `Fb`, 否定一路 (三): 接口 `LeanFbIf` 的盲区与边界

> 不含记号. 入口 [NegLeanFb](NegLeanFb.lagda.md). 对着接口 [LeanFbIf](LeanFbIf.lagda.md) ("接口定稿 2026-11-05 21:23 (首次编译通过)"; 变更记录: 22:00 只改文字, 依本篇 `rdConst` 更正 `δ-n1` 的说明) 写, 导入它, 不另造接口. 另导入 [NegLeanFbPre](NegLeanFbPre.lagda.md) 的 `wdec1` 一族. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **结果.**
>
> 1. **盲 (§1, §2).**
>    - **`rdConst`** (定理, 对一切 $T,\Lambda,Q$): 读回取常数 $1$, 级层 $0$ 的 `LvRd`. `δ-n1` 被 `refl` 满足. 所以接口定稿时文件头的 "δ-n1 (δ n1 ≡ hs hz, 排除不看数据)" 不成立 (构造一路已在 22:00 的变更记录里更正文字): **`δ-n1` 不排除不看数据的读回** (`rdConst-blind`). 级层也不受约束 (`ℓ = 0`).
>    - **`upCopies`** (定理, 对一切 $S$, 一切下标集 $J$): `step S` 的新种类自己构成一个 `Up`, 成员族是常值 (`copies-same`: 一切成员是同一个种类). 所以 "`Up` 的成员族" 可以退化成一个种类的多个下标; 成员是不是不同的种类, 不同的拷贝, 是实例的事.
>    - **`feedStep`**, **`planStep`** (定理): `step S` 的新种类有一个 `Feed` (`upCopies ⊤` 加 `rdConst`); 旧种类有损. 接口的 `Plan` 由此可满足, 回灌不看数据.
>    - **`const-u`** (定理, 在折叠里): 按本篇的读法 `feedFb` (升界 = `rz (δ x) w`) 把 `rdConst` 的 `Feed` 接进 [LeanTFold](LeanTFold.lagda.md), 级回灌每一格的 (世界, 合法) 都与分支, 动作, 累计数据, 状态无关. (`feedFb` 是本篇的转换, 构造一路自己的转换若 `nx` 也是 `rz (δ x) w`, 结论相同, 判断.)
> 2. **同一个 `Up` 的成员分不开 (§3).** **`same-stays`**, **`same-iter`** (定理, 对一切 `Up`): 两个成员在某个世界里读出的顶相同, 则经这个 `Up` 的任意多次升界后仍相同. 构造计划里 "级 0 的头与一切级 0 拷贝一个 `Up`" 在基世界里读数都是 $0$ 时 (前提, 待对实例查), 只经这个 `Up` 升界的世界里这些成员的读数**恒相等**: 这个 `Up` 不区分成员. (别的回灌可能另外动它们; 接口没有关于非成员的律, 所以这里只说经同一个 `Up`.)
> 3. **边界 (§4).**
>    - **`no-up-co`** (定理, 否定; 对一切 $T, S'$): 若 `Up T (step S′)` 有一个成员, 它的 `co` 经 `up` 进来 (`co j e ≡ up (f e)`, 例如把低一级的拷贝经自然嵌入读进高一级), 只要有一个世界, 就矛盾. 原因: `rz-top` 要对**一切**增量 $\delta$ 成立, 取 $\delta$ 为 `step S′` 新种类的 $\Omega$-结点, 左边的头永远是旧种类. **`no-ι-co`** (定理, 否定): `Q = sup I F` 时, 成员经 `ι i` 进来, 而另有 $i'\ne i$ 的种类, 同样矛盾. 所以**一个 `Up` 不能跨级**: 成员的读数必须能产出 `HB Q` 里一切头种类.
>    - **`upPt-sep`**, **`upPt-sepLΩ`** (定理, 否定): 在 `SL` 上, 给 `Up` 的单成员实例 (成员 `νL s`, 读数恒等) 加上接口没有的 "留别份" 律 (`keepP`), 在 $s=$ `ll h` 或 `lΩ k g` 处推出分离子 (`SepLl`, `SepLΩ`; 加外延是 WLPO, 见 [NegLeanFbPre](NegLeanFbPre.lagda.md)). 接口不带这条律是必要的. 前提实例: 可判定层号 `lz` 上带留别份的单成员 `Up` 是构造 (`upPtLz`).
>
> **只否定什么.** (i) 推断 "有 `LvRd`/`Feed`/`Plan` 的实例, 所以回灌读了数据, 或读在自己的级上" (§1); (ii) 推断 "同一个 `Up` 的不同成员被分别回灌" (§3, 只对经同一个 `Up` 的升界); (iii) 跨级的 `Up` (成员经 `up` 或 `ι` 嵌入公共类型) (§4); (iv) 给单成员 `Up` 在含函数的层号上加 "留别份". **不否定**: 接口的任何记录 (都有实例); 构造一路的计划 (同级拷贝一个 `Up`, 站以 $\mathbb N$ 为下标); 不带留别份律的单成员 `Up` 在含函数层号上是否存在 (本篇既没构造也没否定, 判断: 要把 `HB (Lv s)` 的增量放进下标为 `s` 的分量, 而不判定别的下标是否等于 `s`, 我们没找到写法). 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLeanFbBlind where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanTTree
import OCF.Lean.LeanTFold as FoldM
open import OCF.Lean.LeanFbIf
open import OCF.Lean.NegLeanFbPre using (wb; Raise; Keep; wdec1; SepLl; SepLΩ; wdec→sepLl; wdec→sepLΩ)
```

## §1 读回: 常数 $1$

```agda
module _ (T : KS) (Λ : HB (step T)) (Q : KS) where
  open Tree T

  rdConst : LvRd T Λ Q
  rdConst = record { ℓ = hz ; ℓ⊲ = z⊲ᴮ Λ ; δ = λ _ _ → hs hz ; δLg = λ _ _ → tt ; δ-n1 = λ _ → refl }

  rdConst-blind : ∀ {W} (lW : LgW L₀ W) (x y : D hz W) → LvRd.δ rdConst lW x ≡ LvRd.δ rdConst lW y
  rdConst-blind lW x y = refl

  rdConst-ℓ : LvRd.ℓ rdConst ≡ hz
  rdConst-ℓ = refl
```

## §2 一起升: 退化的成员族; `Feed`, `Plan` 的平凡实例

`step S` 的新种类: 坐标 `HB S`, 顶是世界的第二分量. `rz δ (w , b) = (w , b ⊞ δ)`.

```agda
module _ (S : KS) where
  upCopies : (J′ : Set) → Up (step S) S
  upCopies J′ = record
    { J = J′ ; κJ = λ _ → inj₂ tt ; co = λ _ e → e
    ; rz = λ δ w → proj₁ w , proj₂ w ⊞ δ
    ; rz≤ = λ δ w → ≤w-rf S , ⊞-fst (proj₂ w) δ
    ; rzLg = λ {δ} {w} lδ lw → proj₁ lw , Lg-⊞ (proj₂ w) δ (proj₂ lw) lδ
    ; rz-top = λ j δ w → refl }

  copies-same : ∀ (J′ : Set) (j j′ : J′) → κJ (upCopies J′) j ≡ κJ (upCopies J′) j′
  copies-same J′ j j′ = refl

  upStep : Up (step S) S
  upStep = upCopies ⊤

  feedStep : (Λ : HB (step (step S))) → Feed (step S) Λ (inj₂ tt)
  feedStep Λ = record { Q = S ; R = rdConst (step S) Λ S ; U = upStep ; mem = tt , refl }

  planStep : (Λ : HB (step (step S))) → Plan (step S) Λ
  planStep Λ (inj₂ tt) = inj₁ (feedStep Λ)
  planStep Λ (inj₁ κ) = inj₂ tt
```

**接进折叠 (本篇的读法).** `feedFb`: 级层与读回取 `LvRd`, 起点取状态在级层上的数据, 升界 `rz (δ x) w`. 用 `rdConst` 时每一格的 (世界, 合法) 与分支, 动作, 累计, 状态无关.

```agda
module ToFb (T : KS) (Λ : HB (step T)) where
  open Tree T
  open FoldTy T Λ

  feedFb : ∀ {κ} → Feed T Λ κ → Fb
  feedFb F = record
    { ℓ = LvRd.ℓ (R F) ; ℓ⊲ = LvRd.ℓ⊲ (R F) ; d₀ = λ lW Y → yc (d Y) (tg ≤rf (LvRd.ℓ⊲ (R F)) lW)
    ; nx = λ {W} lW x → rz (U F) (LvRd.δ (R F) lW x) (proj₁ W)
    ; nx≤ = λ {W} lW x → rz≤ (U F) (LvRd.δ (R F) lW x) (proj₁ W)
    ; nxLg = λ lW x → rzLg (U F) (LvRd.δLg (R F) lW x) (proj₁ lW) }

  planFb : Plan T Λ → K T → Fb ⊎ ⊤
  planFb P κ = [ (λ F → inj₁ (feedFb F)) , (λ _ → inj₂ tt) ]′ (P κ)

  constFeed : ∀ {Q′ κ} (U′ : Up T Q′) (j : J U′) → κJ U′ j ≡ κ → Feed T Λ κ
  constFeed {Q′} U′ j e = record { Q = Q′ ; R = rdConst T Λ Q′ ; U = U′ ; mem = j , e }

module ConstRun (T : KS) (bk : Tree.BotK T) (Λ : HB (step T)) (lΛ : LgB Λ)
  (one⊲ : ∀ {w} → hs hz ⊲[ w ] Λ) (fb : K T → FoldTy.Fb T Λ ⊎ ⊤) where
  open Tree T
  open FoldTy T Λ
  open ToFb T Λ
  open FoldM T bk Λ lΛ one⊲ fb

  wl : ∀ {W ly} → ClA W ly → Σ (Wd T) (LgW T)
  wl c = wA c , lwA c

  const-u : ∀ {Q′ κ} (U′ : Up T Q′) (j : J U′) (e : κJ U′ j ≡ κ) {ly W₀ W} (ac : AccY ly) (u u′ : Bu ly W₀) (q₀ : W₀ ≤ W)
            (lW : LgW L₀ W) (lL : LW ly W) (A₀ A₀′ : Ig ly W) (w w′ : D ly W) (Y Y′ : St W) n →
            wl (κcF ac (feedFb (constFeed U′ j e)) u q₀ lW lL A₀ w Y n) ≡ wl (κcF ac (feedFb (constFeed U′ j e)) u′ q₀ lW lL A₀′ w′ Y′ n)
  const-u U′ j e ac u u′ q₀ lW lL A₀ A₀′ w w′ Y Y′ zero = refl
  const-u U′ j e ac u u′ q₀ lW lL A₀ A₀′ w w′ Y Y′ (suc n) =
    cong (λ p → rz U′ (hs hz) (proj₁ p) , rzLg U′ {hs hz} tt (proj₂ p)) (const-u U′ j e ac u u′ q₀ lW lL A₀ A₀′ w w′ Y Y′ n)
```

## §3 同一个 `Up` 的成员: 读数相同则一直相同

```agda
module _ {T Q : KS} (U : Up T Q) where
  rd : J U → Wd T → HB Q
  rd j w = co U j (top T (κJ U j) w)

  same-stays : ∀ j j′ δ w → rd j w ≡ rd j′ w → rd j (rz U δ w) ≡ rd j′ (rz U δ w)
  same-stays j j′ δ w e = trans (rz-top U j δ w) (trans (cong (λ a → a ⊞ δ) e) (sym (rz-top U j′ δ w)))

  rzN : (ℕ → HB Q) → ℕ → Wd T → Wd T
  rzN ds zero w = w
  rzN ds (suc n) w = rz U (ds n) (rzN ds n w)

  same-iter : ∀ j j′ ds w → rd j w ≡ rd j′ w → ∀ n → rd j (rzN ds n w) ≡ rd j′ (rzN ds n w)
  same-iter j j′ ds w e zero = e
  same-iter j j′ ds w e (suc n) = same-stays j j′ (ds n) (rzN ds n w) (same-iter j j′ ds w e n)
```

**前提实例.** `upCopies` 的任两个成员在任一世界里读数相同 (同一个种类): `same-copies`.

```agda
same-copies : ∀ (S : KS) (J′ : Set) j j′ w → rd (upCopies S J′) j w ≡ rd (upCopies S J′) j′ w
same-copies S J′ j j′ w = refl
```

## §4 边界

**`no-up-co`.** `newHd`: 头是新种类的 $\Omega$-结点. `up` 的像没有这种头; $a\boxplus\delta$ 在 $\delta$ 有这种头时也有.

```agda
newHd : ∀ {S : KS} → HB (step S) → Bool
newHd (hΩ (inj₂ _) _) = true
newHd _ = false

newHd-up : ∀ {S : KS} (x : HB S) → newHd (up x) ≡ false
newHd-up hz = refl
newHd-up (hs x) = refl
newHd-up (hl f) = refl
newHd-up (hΩ κ g) = refl

f≢t : ¬ (false ≡ true)
f≢t ()

no-up-co : ∀ {T S′ : KS} (U : Up T (step S′)) (j : J U) (f : E T (κJ U j) → HB S′) →
           (∀ e → co U j e ≡ up (f e)) → Wd T → ⊥
no-up-co {T} {S′} U j f hco w = f≢t (trans (sym (newHd-up (f (top T (κJ U j) (rz U δ₁ w)))))
                                  (cong newHd (trans (sym (hco _)) (rz-top U j δ₁ w))))
  where
  δ₁ : HB (step S′)
  δ₁ = hΩ (inj₂ tt) (λ _ → hz)
```

**`no-ι-co`.** `Q = sup I F`; `hdI`: 头的 $\Omega$-结点的下标.

```agda
module _ {I : Set} {F : I → KS} where
  hdI : HB (sup I F) → Maybe I
  hdI (hΩ κ _) = just (proj₁ κ)
  hdI _ = nothing

  hdI-ι : ∀ i (x : HB (F i)) → (hdI (ι i x) ≡ nothing) ⊎ (hdI (ι i x) ≡ just i)
  hdI-ι i hz = inj₁ refl
  hdI-ι i (hs x) = inj₁ refl
  hdI-ι i (hl f) = inj₁ refl
  hdI-ι i (hΩ κ g) = inj₂ refl

  just≢nothing : ∀ {i : I} → ¬ (just i ≡ nothing)
  just≢nothing ()

  just-inj : ∀ {i i′ : I} → just i ≡ just i′ → i ≡ i′
  just-inj refl = refl

  no-ι-co : ∀ {T : KS} (U : Up T (sup I F)) (j : J U) (i : I) (f : E T (κJ U j) → HB (F i)) →
            (∀ e → co U j e ≡ ι i (f e)) → (i′ : I) → ¬ (i′ ≡ i) → K (F i′) → Wd T → ⊥
  no-ι-co {T} U j i f hco i′ ne κ′ w = go (hdI-ι i (f t₁))
    where
    δ₁ : HB (sup I F)
    δ₁ = hΩ (i′ , κ′) (λ _ → hz)
    t₁ : E T (κJ U j)
    t₁ = top T (κJ U j) (rz U δ₁ w)
    eq : hdI (ι i (f t₁)) ≡ just i′
    eq = cong hdI (trans (sym (hco _)) (rz-top U j δ₁ w))
    go : (hdI (ι i (f t₁)) ≡ nothing) ⊎ (hdI (ι i (f t₁)) ≡ just i) → ⊥
    go (inj₁ h) = just≢nothing (trans (sym eq) h)
    go (inj₂ h) = ne (just-inj (trans (sym eq) h))
```

**`upPt-sep`.** 单成员 `Up` (成员 `νL s`, 读数恒等) 加留别份律 `keepP`.

```agda
record UpPt (s : LH) : Set where
  field
    rzP     : HB (Lv s) → Wd SL → Wd SL
    rzP≤    : ∀ δ w → _≤w_ SL w (rzP δ w)
    rzPLg   : ∀ {δ w} → LgB δ → LgW SL w → LgW SL (rzP δ w)
    rzP-top : ∀ δ w → proj₂ (rzP δ w s) ≡ proj₂ (w s) ⊞ δ
    keepP   : ∀ δ w k → ¬ (k ≡ s) → ∀ {c} → Bd SL (νL k) c (rzP δ w) → Bd SL (νL k) c w
open UpPt public

toUp : ∀ {s} → UpPt s → Up SL (Lv s)
toUp {s} P = record
  { J = ⊤ ; κJ = λ _ → νL s ; co = λ _ e → e ; rz = rzP P ; rz≤ = rzP≤ P ; rzLg = rzPLg P ; rz-top = λ _ → rzP-top P }

upPt-wdec : ∀ s → UpPt s → ∀ k → ¬ (k ≡ s) ⊎ ¬ ¬ (k ≡ s)
upPt-wdec s P = wdec1 s (rzP P (hs hz) wb) r (keepP P (hs hz) wb)
  where
  r : Raise s (rzP P (hs hz) wb)
  r = subst (λ b → hs hz ⊲[ proj₁ (rzP P (hs hz) wb s) ] b) (sym (rzP-top P (hs hz) wb)) hself

upPt-sep : ∀ h → UpPt (ll h) → SepLl h
upPt-sep h P = wdec→sepLl h (upPt-wdec (ll h) P)

upPt-sepLΩ : ∀ k g → UpPt (lΩ k g) → SepLΩ k g
upPt-sepLΩ k g P = wdec→sepLΩ k g (upPt-wdec (lΩ k g) P)
```

**前提实例: 可判定层号 `lz` 上带留别份的单成员 `Up`.**

```agda
rzLz : HB (Lv lz) → Wd SL → Wd SL
rzLz δ w lz = proj₁ (w lz) , proj₂ (w lz) ⊞ δ
rzLz δ w (ls x) = w (ls x)
rzLz δ w (ll f) = w (ll f)
rzLz δ w (lΩ k g) = w (lΩ k g)

upPtLz : UpPt lz
upPtLz = record { rzP = rzLz ; rzP≤ = le ; rzPLg = lg ; rzP-top = λ δ w → refl ; keepP = kp }
  where
  le : ∀ δ w → _≤w_ SL w (rzLz δ w)
  le δ w lz = ≤w-rf S⊥ , ⊞-fst (proj₂ (w lz)) δ
  le δ w (ls x) = ≤w-rf (FL (ls x))
  le δ w (ll f) = ≤w-rf (FL (ll f))
  le δ w (lΩ k g) = ≤w-rf (FL (lΩ k g))
  lg : ∀ {δ w} → LgB δ → LgW SL w → LgW SL (rzLz δ w)
  lg {δ} {w} lδ lw lz = proj₁ (lw lz) , Lg-⊞ (proj₂ (w lz)) δ (proj₂ (lw lz)) lδ
  lg lδ lw (ls x) = lw (ls x)
  lg lδ lw (ll f) = lw (ll f)
  lg lδ lw (lΩ k g) = lw (lΩ k g)
  kp : ∀ δ w k → ¬ (k ≡ lz) → ∀ {c} → Bd SL (νL k) c (rzLz δ w) → Bd SL (νL k) c w
  kp δ w lz ne b = ⊥-elim (ne refl)
  kp δ w (ls x) ne b = b
  kp δ w (ll f) ne b = b
  kp δ w (lΩ k g) ne b = b
```

## §5 结论 (按档)

- **[定理, 盲]** **`rdConst`**, **`rdConst-blind`**, `rdConst-ℓ` (`δ-n1` 不排除不看数据的读回; 级层不受约束; 对一切 $T,\Lambda,Q$). **`upCopies`**, **`copies-same`** (成员族可退化成一个种类), `upStep`, `feedStep`, **`planStep`** (接口的 `Plan` 有不看数据的实例). `feedFb`, `planFb`, `constFeed` (本篇的转换); **`const-u`** (常数读回接进折叠: 级回灌每一格的世界与分支, 动作, 累计, 状态无关).
- **[定理, 成员分不开]** **`same-stays`**, **`same-iter`** (对一切 `Up`); 前提实例 `same-copies`.
- **[定理, 否定]** **`no-up-co`** (成员经 `up` 读进 `step S′`: 有一个世界就矛盾), **`no-ι-co`** (成员经 `ι i` 读进 `sup I F`, 另有 $i'\ne i$ 的种类: 矛盾); **`upPt-wdec`**, **`upPt-sep`**, **`upPt-sepLΩ`** (单成员 `Up` 加留别份, 在 `ll`/`lΩ` 层号上推出分离子). 前提实例: `upPtLz` (可判定层号上 `UpPt` 是构造); `no-up-co` 与 `no-ι-co` 的各前提单独可满足 (`Up` 有实例 `upCopies`; 任一函数可以写成 `up ∘ f` 的形状只要它的值在 `up` 的像里; 有世界: `w₀ T`), 合起来不可满足正是定理.
- **[判断]** `feedFb` 与构造一路的转换是否相同, 待对实例查 (见 [NegLeanFbInst](NegLeanFbInst.lagda.md), 若已写). 不带留别份律的单成员 `Up` 在含函数层号上是否存在, 没构造也没否定.
