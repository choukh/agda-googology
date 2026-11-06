# C 线重写成一个折叠, 否定一路 (二): 路径与世界统一到一切层号的代价

> 不含记号. 入口 [NegCRw](NegCRw.lagda.md). 本篇**不依赖**构造一路 CRw 的接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** C 线里路径与世界只在 `lΩ` 层号上出现: TySup (可数层号) 没有世界, 决定用层号自己作公共上界; PathOut ($X_1$) 的世界是一个第 0 层的界 $B$, 世界的序是 $B\lhd B'$ (世界 `tt` 里的第一位置); X1Up 在 $X_1$ 上叠可数层时, 新种类的可入是 Kripke 式 (`X1UpFold.StepPS`). 一个对层号 `LH` 递归的折叠要在一切层号上用同一份定义. 本篇问: 统一之后, 可数层上的路径是什么; `lΩ k g` 在 $k$ 更高时世界还能不能是 "一个界加一个与世界无关的序".
>
> **结果.**
>
> 1. **`allEv→PH`, `allEv-step`, `allEv-sup` (定理, 对一切世界类型与序).** 若一个带路径结构的每个种类在每个世界里都有证据, 则每棵树在每个世界里都带路径; X1Up 的一步搭法 `psStep` 与并 `psSup` 保持这一条. 推论 **`ph-free-cnt`** (对一切 `U : X1UpIf`): 用 X1Up 的同一份搭法从底 `S⊥` 起搭出可数层号的结构 (`PSC x`, 种类结构字面是 `TySupC.LC x`), **一切树在一切世界里都带路径**. 所以统一后的路径在可数层号上不约束任何东西 (盲区), 它的代价只是要带着世界与路径证明走.
> 2. **`base-not-free` (定理, 实例 `IU`).** 对照: 在 $X_1$ 的底上, 路径不平凡: 坐标为 $1$ 的第 2 层种类的结点在界 $1$ 里不带路径 (用 `X1Up.no21`). 所以 "可数层不要路径, `lΩ` 层要" 在统一的定义里体现为: 路径约束只来自 `lΩ` 层号的种类的证据, 一步搭法与并只传递, 不新增.
> 3. **`wfree` (定理, 对一切种类结构).** 不含 $\Omega$-结点的树之间的第一位置与世界无关. 第 0 层的值 (`HB S⊥`) 都不含结点, 所以 PathOut 的世界 (第 0 层的界, 序 $B\lhd_{\mathrm{tt}}B'$) 的序与世界无关 (`wfree-S⊥`).
> 4. **`wdep₁` (定理).** 第 1 层的值 (`HB (step S⊥)`) 之间的第一位置依赖世界: $1\lhd\Omega_1$ 在世界 $(\mathrm{tt},1)$ 里成立, 在 $(\mathrm{tt},0)$ 里不成立. 所以对 `lΩ k g` 且 $k$ 至少是第 1 层时, 若世界的界取第 $k$ 层的值, 界之间的序要再带一个第 $k$ 层的世界: 世界是一座塔, 不是 PathOut 那样的 "一个界加一个与世界无关的序".
>
> **前提实例.** 1: 底 `S⊥` 的结构没有种类, `allEv` 空真地成立 (`allEv-⊥`); `U` 取 `X1Up.IU`. 2: 世界 $1$ 合法 (`LgW₁`: $1\lhd1$, `LgB 1`). 4: 两个世界都合法 (`lgw₁`, `lgw₀`).
>
> **只否定什么.** 4 只否定 "第 $k\geq1$ 层的值之间的第一位置与世界无关", 即 PathOut 的世界写法不能逐字推到 `lΩ (ls lz) g` 一类层号; 不否定带世界塔的写法, 也不否定别的世界设计. 1 不否定任何东西, 是盲区: 统一的路径在可数层号上无内容; 不说统一不可做. 本篇没有关闭任何路线.
>
> **对纲领与目标.** 纲领 3 (壁垒): 4 是 "比较要带字面公共上界" 在世界一侧的形状: 第 $k$ 层的界之间的比较本身要第 $k$ 层的世界. 目标 "让树自足": 1 说统一后路径的约束全部来自 `lΩ` 层号的种类证据; 一个对 `LH` 递归的折叠若在可数层号上也带路径, 那部分是形式上的统一, 不是新的判据.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegCRwWorld where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥)
open import OCF.Align.TySupC using (Cd; LC)
open import OCF.Align.X1UpIf using (X1UpIf; module X1UpIf; PS; module PS; PHg)
import OCF.Align.X1UpFold as UF
```

## §1 证据处处有, 路径就处处有

```agda
module _ {Wo : Set} {_≼_ : Wo → Wo → Set} {T : KS} (Q : PS _≼_ T) where
  open PS Q
  AllEv : Set
  AllEv = ∀ W κ → Ev W κ

  allEv→PH : AllEv → ∀ W h → PHg Q W h
  allEv→PH ae W hz = tt
  allEv→PH ae W (hs h) = allEv→PH ae W h
  allEv→PH ae W (hl f) = λ n → allEv→PH ae W (f n)
  allEv→PH ae W (hΩ κ g) = ae W κ , λ e a → allEv→PH ae (nxt W κ (ae W κ) e a) (g e)
```

X1Up 的一步与并保持 `AllEv` (对一切 `U`): 一步的新种类证据是 `⊤`, 旧种类沿用; 并逐分量.

```agda
module Uni (U : X1UpIf) where
  open X1UpIf U using (_≼_)
  open import OCF.Align.PathOutIf using (module PathOutIf)
  open PathOutIf (X1UpIf.P U) using (Wo)
  open UF U using (psStep; psSup)

  allEv-step : ∀ {T} (Q : PS _≼_ T) → AllEv Q → AllEv (psStep Q)
  allEv-step Q ae W (inj₁ κ) = ae W κ
  allEv-step Q ae W (inj₂ _) = tt

  allEv-sup : ∀ {I : Set} {G : I → KS} (Q : (i : I) → PS _≼_ (G i)) → (∀ i → AllEv (Q i)) → AllEv (psSup {I} {G} Q)
  allEv-sup Q ae W (i , κ) = ae i W κ
```

底 `S⊥`: 没有种类. `PSC x`: 用 `psStep`, `psSup` 从底搭出可数层号 $x$ 的结构; 种类结构字面就是 `TySupC.LC x`.

```agda
  module B⊥ where
    Ev⊥ : Wo → K S⊥ → Set
    Ev⊥ W ()
    Adm⊥ : (W : Wo) (κ : K S⊥) → E S⊥ κ → Set
    Adm⊥ W ()
    nxt⊥ : (W : Wo) (κ : K S⊥) → Ev⊥ W κ → (e : E S⊥ κ) → Adm⊥ W κ e → Wo
    nxt⊥ W ()
    ev↑⊥ : ∀ {W W′} → W ≼ W′ → ∀ {κ} → Ev⊥ W κ → Ev⊥ W′ κ
    ev↑⊥ q {()}
    adm↓⊥ : ∀ {W W′} (q : W ≼ W′) {κ} (ev : Ev⊥ W κ) {e} (a′ : Adm⊥ W′ κ e) →
            Σ (Adm⊥ W κ e) (λ a → nxt⊥ W κ ev e a ≼ nxt⊥ W′ κ (ev↑⊥ q {κ} ev) e a′)
    adm↓⊥ q {()}
    ≼nx⊥ : ∀ {W κ} (ev : Ev⊥ W κ) e (a : Adm⊥ W κ e) → W ≼ nxt⊥ W κ ev e a
    ≼nx⊥ {κ = ()}

  PS⊥ : PS _≼_ S⊥
  PS⊥ = record { Ev = Ev⊥ ; Adm = Adm⊥ ; nxt = nxt⊥ ; ev↑ = ev↑⊥ ; adm↓ = adm↓⊥ ; ≼nx = ≼nx⊥ }
    where open B⊥

  allEv-⊥ : AllEv PS⊥
  allEv-⊥ W ()

  PSC : (x : Cd) → PS _≼_ (LC x)
  PSC hz = PS⊥
  PSC (hs x) = psStep (PSC x)
  PSC (hl f) = psSup {ℕ} {λ n → LC (f n)} (λ n → PSC (f n))
  PSC (hΩ () _)

  allEv-C : ∀ x → AllEv (PSC x)
  allEv-C hz = allEv-⊥
  allEv-C (hs x) = allEv-step (PSC x) (allEv-C x)
  allEv-C (hl f) = allEv-sup {ℕ} {λ n → LC (f n)} (λ n → PSC (f n)) (λ n → allEv-C (f n))
  allEv-C (hΩ () _)

  -- 统一的路径在可数层号上处处成立 (盲区)
  ph-free-cnt : ∀ x W (h : HB (LC x)) → PHg (PSC x) W h
  ph-free-cnt x = allEv→PH (PSC x) (allEv-C x)
```

## §2 对照: $X_1$ 的底上路径不平凡

`X1Up.cy`: 坐标为 $1$ 的第 2 层种类的结点. 它的证据要 $2\lhd B$; 在界 $1$ 里没有.

```agda
open import OCF.Align.X1Up using (IU; cy; no21)
open UF IU using (base)

base-not-free : ¬ (∀ W h → PHg base W h)
base-not-free f = no21 (proj₁ (f (hs hz) cy))
```

## §3 世界的序: 第 0 层与世界无关, 第 1 层依赖世界

```agda
module _ {S : KS} where
  NoΩ : HB S → Set
  NoΩ hz = ⊤
  NoΩ (hs h) = NoΩ h
  NoΩ (hl f) = ∀ n → NoΩ (f n)
  NoΩ (hΩ _ _) = ⊥

  wfree : ∀ {a b w w′} → NoΩ b → a ⊲[ w ] b → a ⊲[ w′ ] b
  wfree nb hself = hself
  wfree nb (hsuc p) = hsuc (wfree nb p)
  wfree nb (hlim n p) = hlim n (wfree (nb n) p)
  wfree () (hLim e p)

noΩ-S⊥ : (h : HB S⊥) → NoΩ h
noΩ-S⊥ hz = tt
noΩ-S⊥ (hs h) = noΩ-S⊥ h
noΩ-S⊥ (hl f) = λ n → noΩ-S⊥ (f n)
noΩ-S⊥ (hΩ () _)

wfree-S⊥ : ∀ {a b : HB S⊥} {w w′} → a ⊲[ w ] b → a ⊲[ w′ ] b
wfree-S⊥ {b = b} = wfree (noΩ-S⊥ b)
```

第 1 层: `Ω₁ = hΩ (inj₂ tt) up`, 世界是 $(\mathrm{tt}, B)$, 新种类的坐标要 $c\lhd B$.

```agda
S₁ : KS
S₁ = step S⊥

Ω₁ : HB S₁
Ω₁ = hΩ (inj₂ tt) up

w₁ w₀ : Wd S₁
w₁ = tt , hs hz
w₀ = tt , hz

lgw₁ : LgW S₁ w₁
lgw₁ = tt , tt

lgw₀ : LgW S₁ w₀
lgw₀ = tt , tt

at-z : ∀ {c : HB S⊥} → c ⊲[ tt ] hz → c ≡ hz
at-z hself = refl

in-w₁ : hs hz ⊲[ w₁ ] Ω₁
in-w₁ = hLim {c = hs hz} hself hself

not-w₀ : ¬ (hs hz ⊲[ w₀ ] Ω₁)
not-w₀ p = go p refl
  where
  hs⋪hz : ∀ {x : HB S₁} → ¬ (hs x ⊲[ w₀ ] hz)
  hs⋪hz ()
  go : ∀ {b} → hs hz ⊲[ w₀ ] b → b ≡ Ω₁ → ⊥
  go hself ()
  go (hsuc p) ()
  go (hlim n p) ()
  go (hLim {c = c} e p) refl = hs⋪hz (subst (λ z → hs hz ⊲[ w₀ ] up z) (at-z e) p)

wdep₁ : Σ (HB S₁) (λ a → Σ (HB S₁) (λ b → Σ (Wd S₁) (λ w → Σ (Wd S₁) (λ w′ →
          LgW S₁ w × LgW S₁ w′ × (a ⊲[ w ] b) × ¬ (a ⊲[ w′ ] b)))))
wdep₁ = hs hz , Ω₁ , w₁ , w₀ , lgw₁ , lgw₀ , in-w₁ , not-w₀
```

## 结论 (按档)

- **[定理]** `allEv→PH` (对一切带路径结构); `Uni.allEv-step`, `Uni.allEv-sup`, `Uni.allEv-⊥`, `Uni.allEv-C`, **`Uni.ph-free-cnt`** (对一切 `U`); **`base-not-free`** (`IU`); **`wfree`** (对一切种类结构), `wfree-S⊥`; `in-w₁`, `not-w₀`, **`wdep₁`**.
- **[判断]** 一个对 `LH` 递归的折叠在 `lΩ k g` ($k\geq1$) 上要的世界是 "第 $k$ 层的界加第 $k$ 层的世界" 的塔: 由 4 推测, 未写出这样的世界, 也未否定别的设计.
