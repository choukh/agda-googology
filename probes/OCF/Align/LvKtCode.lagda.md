# 层号换类型 (码): 对一般种类结构的路径码

> 不含记号. 入口 [LvKt](LvKt.lagda.md), 接口 [LvKtIf](LvKtIf.lagda.md). 作者此前选定的方向原话: "A3: 读回包 + 第 ω+1 级折叠"; 本路 (前缀 `LvKt`) 是 [LvTop](LvTop.lagda.md) 接手清单第 1 条 "层号换类型" 的构造一路. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> [LvFbCode](LvFbCode.lagda.md) 的码只对 `HB S₀` 写: 外层世界是 `A`, 进 $\Omega$-分支时坐标用 `A` 的码 `RA`. 这里推广到一般种类结构 `S`:
>
> - **一个通用的原始码** `RC`: 停 (`rH`), 进后继 (`rP`), 进第 $n$ 支 (`rL n`), 进 $\Omega$-分支 (`rΩ re r`, `re` 是坐标的码). 不带索引, 对一切种类结构共用, 相等可判定 (`≟RC`). `A` 的码与高度的码都是它 (`A` 没有 $\Omega$-分支, `rΩ` 在那里不合法).
> - **种类结构的码** `CdK S` (记录): 坐标的码在世界 $a$ 里合法 (`vE`, 命题), 目标坐标 (`tE`), 目标在 $a$ 的界之下 (`pE`), 外加一个基世界 `w0` (合法). 种类 $\kappa$ 不进码: 码走到 `hΩ κ g` 时 $\kappa$ 由树给出.
> - **高度的码** `Codes.vB a b r` (码 $r$ 在世界 $a$、界 $b$ 之下合法), `tB` (目标), `pB` (目标是 $b$ 在 $a$ 里的第一位置), `vB-prop`, 码 `Code a b = Σ RC (vB a b)`, **`code-≟`** (同一界之下的两个码相等可判定). 对一切 `S` 与一切 `CdK S` 一条定义.
> - **实例**: `cdS₀` (坐标 `A`), `cdStep` (新种类的坐标是旧高度, 它的码就是旧高度的码: `Codes.vB`), `cdSup` (逐分量), **`cdLev x`** (对高度 $x$ 结构递归, 与 `Lev` 同形, 不要 `S` 的码). 所以 `Lev` 给出的一切种类结构都有码.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvKtCode where

open import Data.Nat using (ℕ; zero; suc)
import Data.Nat as N
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
```

## §1 通用的原始码

```agda
data RC : Set where
  rH : RC
  rP : RC → RC
  rL : ℕ → RC → RC
  rΩ : RC → RC → RC

tlC : RC → RC
tlC rH = rH
tlC (rP r) = r
tlC (rL n r) = r
tlC (rΩ re r) = r

hdΩ : RC → RC
hdΩ (rΩ re r) = re
hdΩ r = r

≟RC : (r s : RC) → Dec (r ≡ s)
≟RC rH rH = yes refl
≟RC rH (rP s) = no (λ ())
≟RC rH (rL m s) = no (λ ())
≟RC rH (rΩ se s) = no (λ ())
≟RC (rP r) rH = no (λ ())
≟RC (rP r) (rP s) with ≟RC r s
... | yes refl = yes refl
... | no ne = no (λ e → ne (cong tlC e))
≟RC (rP r) (rL m s) = no (λ ())
≟RC (rP r) (rΩ se s) = no (λ ())
≟RC (rL n r) rH = no (λ ())
≟RC (rL n r) (rP s) = no (λ ())
≟RC (rL n r) (rL m s) with n N.≟ m | ≟RC r s
... | yes refl | yes refl = yes refl
... | no ne | _ = no (λ { refl → ne refl })
... | yes refl | no ne = no (λ e → ne (cong tlC e))
≟RC (rL n r) (rΩ se s) = no (λ ())
≟RC (rΩ re r) rH = no (λ ())
≟RC (rΩ re r) (rP s) = no (λ ())
≟RC (rΩ re r) (rL m s) = no (λ ())
≟RC (rΩ re r) (rΩ se s) with ≟RC re se | ≟RC r s
... | yes refl | yes refl = yes refl
... | no ne | _ = no (λ e → ne (cong hdΩ e))
... | yes refl | no ne = no (λ e → ne (cong tlC e))
```

## §2 种类结构的码

```agda
record CdK (S : KS) : Set₁ where
  field
    vE      : (κ : K S) → Wd S → RC → Set
    vE-prop : ∀ κ a r (x y : vE κ a r) → x ≡ y
    tE      : (κ : K S) (a : Wd S) (r : RC) → vE κ a r → E S κ
    pE      : ∀ κ a r (v : vE κ a r) → Bd S κ (tE κ a r v) a
    w0      : Wd S
    lw0     : LgW S w0
open CdK public
```

## §3 高度的码 (对一切 `S` 与它的坐标码)

```agda
module Codes {S : KS} (ck : CdK S) where
  vB  : Wd S → HB S → RC → Set
  vBP : Wd S → HB S → RC → Set
  vBL : Wd S → HB S → ℕ → RC → Set
  vBΩ : Wd S → HB S → RC → RC → Set
  vB a b rH = ⊤
  vB a b (rP r) = vBP a b r
  vB a b (rL n r) = vBL a b n r
  vB a b (rΩ re r) = vBΩ a b re r
  vBP a (hs b) r = vB a b r
  vBP a hz r = ⊥
  vBP a (hl f) r = ⊥
  vBP a (hΩ κ g) r = ⊥
  vBL a (hl f) n r = vB a (f n) r
  vBL a hz n r = ⊥
  vBL a (hs b) n r = ⊥
  vBL a (hΩ κ g) n r = ⊥
  vBΩ a (hΩ κ g) re r = Σ (vE ck κ a re) (λ v → vB a (g (tE ck κ a re v)) r)
  vBΩ a hz re r = ⊥
  vBΩ a (hs b) re r = ⊥
  vBΩ a (hl f) re r = ⊥

  tB  : (a : Wd S) (b : HB S) (r : RC) → vB a b r → HB S
  tBP : (a : Wd S) (b : HB S) (r : RC) → vBP a b r → HB S
  tBL : (a : Wd S) (b : HB S) (n : ℕ) (r : RC) → vBL a b n r → HB S
  tBΩ : (a : Wd S) (b : HB S) (re r : RC) → vBΩ a b re r → HB S
  tB a b rH _ = b
  tB a b (rP r) v = tBP a b r v
  tB a b (rL n r) v = tBL a b n r v
  tB a b (rΩ re r) v = tBΩ a b re r v
  tBP a (hs b) r v = tB a b r v
  tBL a (hl f) n r v = tB a (f n) r v
  tBΩ a (hΩ κ g) re r (ve , v) = tB a (g (tE ck κ a re ve)) r v

  pB  : (a : Wd S) (b : HB S) (r : RC) (v : vB a b r) → tB a b r v ⊲[ a ] b
  pBP : (a : Wd S) (b : HB S) (r : RC) (v : vBP a b r) → tBP a b r v ⊲[ a ] b
  pBL : (a : Wd S) (b : HB S) (n : ℕ) (r : RC) (v : vBL a b n r) → tBL a b n r v ⊲[ a ] b
  pBΩ : (a : Wd S) (b : HB S) (re r : RC) (v : vBΩ a b re r) → tBΩ a b re r v ⊲[ a ] b
  pB a b rH _ = hself
  pB a b (rP r) v = pBP a b r v
  pB a b (rL n r) v = pBL a b n r v
  pB a b (rΩ re r) v = pBΩ a b re r v
  pBP a (hs b) r v = hsuc (pB a b r v)
  pBL a (hl f) n r v = hlim n (pB a (f n) r v)
  pBΩ a (hΩ κ g) re r (ve , v) = hLim (pE ck κ a re ve) (pB a (g (tE ck κ a re ve)) r v)

  vB-prop  : ∀ a b r (x y : vB a b r) → x ≡ y
  vBP-prop : ∀ a b r (x y : vBP a b r) → x ≡ y
  vBL-prop : ∀ a b n r (x y : vBL a b n r) → x ≡ y
  vBΩ-prop : ∀ a b re r (x y : vBΩ a b re r) → x ≡ y
  vB-prop a b rH x y = refl
  vB-prop a b (rP r) x y = vBP-prop a b r x y
  vB-prop a b (rL n r) x y = vBL-prop a b n r x y
  vB-prop a b (rΩ re r) x y = vBΩ-prop a b re r x y
  vBP-prop a (hs b) r x y = vB-prop a b r x y
  vBL-prop a (hl f) n r x y = vB-prop a (f n) r x y
  vBΩ-prop a (hΩ κ g) re r (ve , v) (ve′ , v′) with vE-prop ck κ a re ve ve′
  ... | refl = cong (ve ,_) (vB-prop a (g (tE ck κ a re ve)) r v v′)

  -- 世界 a, 界 b 之下的码
  Code : Wd S → HB S → Set
  Code a b = Σ RC (vB a b)

  tgt : ∀ {a b} → Code a b → HB S
  tgt {a} {b} k = tB a b (proj₁ k) (proj₂ k)

  pth : ∀ {a b} (k : Code a b) → tgt k ⊲[ a ] b
  pth {a} {b} k = pB a b (proj₁ k) (proj₂ k)

  -- 同一 (世界, 界) 之下的两个码: 相等可判定
  code-≟ : ∀ {a b} (k k′ : Code a b) → Dec (k ≡ k′)
  code-≟ {a} {b} (r , v) (s , u) with ≟RC r s
  ... | yes refl = yes (cong (r ,_) (vB-prop a b r v u))
  ... | no ne = no (λ e → ne (cong proj₁ e))

  -- 顶码: 停在界上, 目标就是界 (定义地)
  top : ∀ {a} b → Code a b
  top b = rH , tt

  top-tgt : ∀ {a} b → tgt {a} (top b) ≡ b
  top-tgt b = refl
```

## §4 实例

**底 `S₀`**: 坐标 `A` 的码就是 `RC` 里不含 `rΩ` 的那部分.

```agda
vA  : A → RC → Set
vAP : A → RC → Set
vAL : A → ℕ → RC → Set
vA a rH = ⊤
vA a (rP r) = vAP a r
vA a (rL n r) = vAL a n r
vA a (rΩ re r) = ⊥
vAP (asuc a) r = vA a r
vAP azero r = ⊥
vAP (alim f) r = ⊥
vAL (alim f) n r = vA (f n) r
vAL azero n r = ⊥
vAL (asuc a) n r = ⊥

tA  : (a : A) (r : RC) → vA a r → A
tAP : (a : A) (r : RC) → vAP a r → A
tAL : (a : A) (n : ℕ) (r : RC) → vAL a n r → A
tA a rH _ = a
tA a (rP r) v = tAP a r v
tA a (rL n r) v = tAL a n r v
tAP (asuc a) r v = tA a r v
tAL (alim f) n r v = tA (f n) r v

pA  : (a : A) (r : RC) (v : vA a r) → tA a r v ⊲ a
pAP : (a : A) (r : RC) (v : vAP a r) → tAP a r v ⊲ a
pAL : (a : A) (n : ℕ) (r : RC) (v : vAL a n r) → tAL a n r v ⊲ a
pA a rH _ = C.self
pA a (rP r) v = pAP a r v
pA a (rL n r) v = pAL a n r v
pAP (asuc a) r v = C.suc (pA a r v)
pAL (alim f) n r v = C.lim n (pA (f n) r v)

vA-prop  : ∀ a r (x y : vA a r) → x ≡ y
vAP-prop : ∀ a r (x y : vAP a r) → x ≡ y
vAL-prop : ∀ a n r (x y : vAL a n r) → x ≡ y
vA-prop a rH x y = refl
vA-prop a (rP r) x y = vAP-prop a r x y
vA-prop a (rL n r) x y = vAL-prop a n r x y
vAP-prop (asuc a) r x y = vA-prop a r x y
vAL-prop (alim f) n r x y = vA-prop (f n) r x y

cdS₀ : CdK S₀
cdS₀ = record
  { vE = λ _ a r → vA a r ; vE-prop = λ _ a r → vA-prop a r
  ; tE = λ _ a r v → tA a r v ; pE = λ _ a r v → pA a r v
  ; w0 = azero ; lw0 = tt }
```

**一步 `step S`**: 旧种类的坐标码照旧; 新种类的坐标是 `HB S` 的高度, 坐标码就是 `S` 上的高度码, 世界 $(w, b)$ 的界 $b$ 是它的界.

```agda
module _ {S : KS} (ck : CdK S) where
  private module CS = Codes ck

  vE⁺ : (κ : K (step S)) → Wd (step S) → RC → Set
  vE⁺ (inj₁ κ) w r = vE ck κ (proj₁ w) r
  vE⁺ (inj₂ _) w r = CS.vB (proj₁ w) (proj₂ w) r

  vE⁺-prop : ∀ κ a r (x y : vE⁺ κ a r) → x ≡ y
  vE⁺-prop (inj₁ κ) w r = vE-prop ck κ (proj₁ w) r
  vE⁺-prop (inj₂ _) w r = CS.vB-prop (proj₁ w) (proj₂ w) r

  tE⁺ : (κ : K (step S)) (a : Wd (step S)) (r : RC) → vE⁺ κ a r → E (step S) κ
  tE⁺ (inj₁ κ) w r v = tE ck κ (proj₁ w) r v
  tE⁺ (inj₂ _) w r v = CS.tB (proj₁ w) (proj₂ w) r v

  pE⁺ : ∀ κ a r (v : vE⁺ κ a r) → Bd (step S) κ (tE⁺ κ a r v) a
  pE⁺ (inj₁ κ) w r v = pE ck κ (proj₁ w) r v
  pE⁺ (inj₂ _) w r v = CS.pB (proj₁ w) (proj₂ w) r v

  cdStep : CdK (step S)
  cdStep = record
    { vE = vE⁺ ; vE-prop = vE⁺-prop ; tE = tE⁺ ; pE = pE⁺
    ; w0 = w0 ck , hz ; lw0 = lw0 ck , tt }
```

**并 `sup I F`**: 种类 $(i,\kappa)$ 的坐标码看世界的第 $i$ 个分量.

```agda
cdSup : (I : Set) (F : I → KS) → ((i : I) → CdK (F i)) → CdK (sup I F)
cdSup I F cks = record
  { vE = λ κ w r → vE (cks (proj₁ κ)) (proj₂ κ) (w (proj₁ κ)) r
  ; vE-prop = λ κ w r → vE-prop (cks (proj₁ κ)) (proj₂ κ) (w (proj₁ κ)) r
  ; tE = λ κ w r v → tE (cks (proj₁ κ)) (proj₂ κ) (w (proj₁ κ)) r v
  ; pE = λ κ w r v → pE (cks (proj₁ κ)) (proj₂ κ) (w (proj₁ κ)) r v
  ; w0 = λ i → w0 (cks i)
  ; lw0 = λ i → lw0 (cks i) }
```

**以高度为下标 `Lev x`**: 对 $x$ 结构递归, 与 `Lev` 同形. 不需要 `S` 的码.

```agda
cdLev : ∀ {S} (x : HB S) → CdK (Lev x)
cdLev hz = cdS₀
cdLev (hs x) = cdStep (cdLev x)
cdLev (hl f) = cdSup ℕ (λ n → Lev (f n)) (λ n → cdLev (f n))
cdLev {S} (hΩ κ g) = cdSup (E S κ) (λ c → Lev (g c)) (λ c → cdLev (g c))
```

## §5 结论 (按档)

- **[定义]** `RC`, `CdK`, `Codes.vB`/`tB`/`pB`, `Codes.Code`, `cdS₀`, `cdStep`, `cdSup`, **`cdLev`**.
- **[定理]** `≟RC`; `Codes.vB-prop`; **`Codes.code-≟`** (对一切 `S` 与 `CdK S`: 同一世界与界之下的两个码相等可判定); `Codes.pB` (码的目标是界的第一位置).
- 与 `LvFbCode` 的关系: `LvFbCode.RB`/`RA` 是两个类型, 这里合成一个 `RC`; 在 `S₀` 上 `vB` 与 `LvFbCode.vB` 同形 (逐构造子). 没有写两者之间的映射 (不需要).
