# X₁ 上叠层, 否定一路 (一): 底种类的嵌入, 搬运, 拷贝

> 不含记号. 入口 [NegX1Up](NegX1Up.lagda.md). 本篇**不依赖**构造一路的接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** [PathOut](PathOut.lagda.md) 接手清单第 1 条的卡点 (判断, 未编译): 在 $X_1$ 上叠可数层号 $x$ 得到层号 `ofU x` ($X_1\oplus x$), 留下的底种类 ($X_1$ 的种类) 在目标层里的种类 `embB t κ₀` 与输入里的种类经不同的递归到达同一个 `Ev₁`, "证据要沿嵌入搬运, 对变量层号不是 refl". 本篇把这句话拆开, 能写成定理的写成定理.
>
> **结果.**
>
> 1. **`cls`, `embB` (定义).** 叠层 `ofU x` 的每个种类分成 "底种类 $\kappa$" (`inj₁ κ`) 或 "第 $z$ 个新种类" (`inj₂ z`, 层号 `ofU z`). `embB x κ` 是底种类 $\kappa$ 在 `ofU x` 里的一个代表 (ℕ-极限处取第 0 分量).
> 2. **`cls-emb`, `E-base`, `lvl-base`, `ev-emb` (定理, 对一切 $x$).** 命题等式都成立, 由对 $x$ 的归纳; 在每个具体的 $x$ 上是 `refl` (`ev-emb-2`, 测试). "对变量层号不是 refl" 是关于 Agda 定义等同的元层事实, **不能**写成对象层的定理; 对象层能写的是: 命题等式成立, 搬运在具体层号上计算到恒等.
> 3. **`outB`, `inB`, `out-in`, `in-out` (构造).** 不经 `subst`: 搬运函数按 $x$ 递归定义, 每个子句是恒等; 往返是恒等 (对一切 $x$, 由归纳). 证据 `EvU` 按同样的递归定义 (`EvU`), 与 "经分类读出的证据" (`EvC`) 互推 (`evU→C`, `evC→U`). 所以卡点是**要把这些搬运穿进折叠的工程量**, 不是障碍. 本篇不对行数作估计.
> 4. **`copies-ll`, `emb-not-unique` (定理).** 在偏移为 ℕ-极限的叠层 `ofU (hl f)` 里, 每个底种类有可数多个不同的代表 (第 $n$ 分量), 分类相同. 所以 "底种类" 只能由分类 `cls` 读出, 不能由 `embB` 的逆读出: 上层折叠留下底种类时, 读回要对每个代表写 (经 `outB`), 不能只对 `embB` 的像写.
>
> **前提实例.** 2, 3: 无前提 (对一切 $x$, $\kappa$). 4: 任一 $f$ 与任一底种类, 例如 $\Omega_1$ 种类 `κΩ`.
>
> **只否定什么.** 4 只否定 "`ofU x` 的底种类与 $X_1$ 的种类一一对应 (经 `embB`)". **不否定**: 上层折叠留下底种类 (3 给出所需的搬运); PathOut 的卡点判断里 "要搬运" 这一半 (成立, 由 2); 被本篇推翻的只是 "这是卡点" 的读法 (判断档的推翻: 3 是构造, 是否够用要看构造一路的折叠). 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegX1UpEmb where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥; LH; lz; ls; ll; lΩ; Lv; lvl)
open import OCF.Align.TySupC using (Cd; ofC)
open import OCF.Align.PathOutX1 using (X₁; XS₁; κΩ; Ev₁)
```

## §1 叠层与种类的分类

```agda
ofU : Cd → LH
ofU hz = X₁
ofU (hs x) = ls (ofU x)
ofU (hl f) = ll (λ n → ofU (f n))
ofU (hΩ () _)

LU : Cd → KS
LU x = Lv (ofU x)

-- 底种类 (inj₁) 或第 z 个新种类 (inj₂ z, 层号 ofU z)
cls : ∀ x → K (LU x) → K XS₁ ⊎ Cd
cls hz κ = inj₁ κ
cls (hs x) (inj₁ κ) = cls x κ
cls (hs x) (inj₂ _) = inj₂ x
cls (hl f) (n , κ) = cls (f n) κ
cls (hΩ () _) _

embB : ∀ x → K XS₁ → K (LU x)
embB hz κ = κ
embB (hs x) κ = inj₁ (embB x κ)
embB (hl f) κ = 0 , embB (f 0) κ
embB (hΩ () _) _
```

## §2 命题等式 (对一切 $x$)

```agda
cls-emb : ∀ x κ → cls x (embB x κ) ≡ inj₁ κ
cls-emb hz κ = refl
cls-emb (hs x) κ = cls-emb x κ
cls-emb (hl f) κ = cls-emb (f 0) κ
cls-emb (hΩ () _) _

E-base : ∀ x κ′ {κ} → cls x κ′ ≡ inj₁ κ → E (LU x) κ′ ≡ E XS₁ κ
E-base hz κ′ refl = refl
E-base (hs x) (inj₁ κ′) p = E-base x κ′ p
E-base (hs x) (inj₂ _) ()
E-base (hl f) (n , κ′) p = E-base (f n) κ′ p
E-base (hΩ () _) _

lvl-base : ∀ x κ′ {κ} → cls x κ′ ≡ inj₁ κ → lvl (ofU x) κ′ ≡ lvl X₁ κ
lvl-base hz κ′ refl = refl
lvl-base (hs x) (inj₁ κ′) p = lvl-base x κ′ p
lvl-base (hs x) (inj₂ _) ()
lvl-base (hl f) (n , κ′) p = lvl-base (f n) κ′ p
lvl-base (hΩ () _) _

lvl-new : ∀ x κ′ {z} → cls x κ′ ≡ inj₂ z → lvl (ofU x) κ′ ≡ ofU z
lvl-new hz κ′ ()
lvl-new (hs x) (inj₁ κ′) p = lvl-new x κ′ p
lvl-new (hs x) (inj₂ _) refl = refl
lvl-new (hl f) (n , κ′) p = lvl-new (f n) κ′ p
lvl-new (hΩ () _) _

E-new : ∀ x κ′ {z} → cls x κ′ ≡ inj₂ z → E (LU x) κ′ ≡ HB (LU z)
E-new hz κ′ ()
E-new (hs x) (inj₁ κ′) p = E-new x κ′ p
E-new (hs x) (inj₂ _) refl = refl
E-new (hl f) (n , κ′) p = E-new (f n) κ′ p
E-new (hΩ () _) _

lvl-emb : ∀ x κ → lvl (ofU x) (embB x κ) ≡ lvl X₁ κ
lvl-emb x κ = lvl-base x (embB x κ) (cls-emb x κ)
```

经分类读出的证据: 底种类用 PathOut 的 `Ev₁`, 新种类不要证据.

```agda
EvC : ∀ x → Cd → K (LU x) → Set
EvC x B κ′ = [ Ev₁ B , (λ _ → ⊤) ]′ (cls x κ′)

ev-emb : ∀ x B κ → EvC x B (embB x κ) ≡ Ev₁ B κ
ev-emb x B κ = cong [ Ev₁ B , (λ _ → ⊤) ]′ (cls-emb x κ)
```

**测试 (具体层号上是 refl).** $x=2$: 等式本身就是 `refl`.

```agda
two : Cd
two = hs (hs hz)

ev-emb-2 : ∀ B κ → ev-emb two B κ ≡ refl
ev-emb-2 B κ = refl

lvl-emb-2 : ∀ κ → lvl-emb two κ ≡ refl
lvl-emb-2 κ = refl
```

## §3 不经 `subst` 的搬运 (构造)

```agda
outB : ∀ x κ′ {κ} → cls x κ′ ≡ inj₁ κ → E (LU x) κ′ → E XS₁ κ
outB hz κ′ refl e = e
outB (hs x) (inj₁ κ′) p e = outB x κ′ p e
outB (hs x) (inj₂ _) () e
outB (hl f) (n , κ′) p e = outB (f n) κ′ p e
outB (hΩ () _) _

inB : ∀ x κ′ {κ} → cls x κ′ ≡ inj₁ κ → E XS₁ κ → E (LU x) κ′
inB hz κ′ refl e = e
inB (hs x) (inj₁ κ′) p e = inB x κ′ p e
inB (hs x) (inj₂ _) () e
inB (hl f) (n , κ′) p e = inB (f n) κ′ p e
inB (hΩ () _) _

out-in : ∀ x κ′ {κ} (p : cls x κ′ ≡ inj₁ κ) e → outB x κ′ p (inB x κ′ p e) ≡ e
out-in hz κ′ refl e = refl
out-in (hs x) (inj₁ κ′) p e = out-in x κ′ p e
out-in (hs x) (inj₂ _) () e
out-in (hl f) (n , κ′) p e = out-in (f n) κ′ p e
out-in (hΩ () _) _

in-out : ∀ x κ′ {κ} (p : cls x κ′ ≡ inj₁ κ) e → inB x κ′ p (outB x κ′ p e) ≡ e
in-out hz κ′ refl e = refl
in-out (hs x) (inj₁ κ′) p e = in-out x κ′ p e
in-out (hs x) (inj₂ _) () e
in-out (hl f) (n , κ′) p e = in-out (f n) κ′ p e
in-out (hΩ () _) _
```

留下的底种类: 输入在 `ofU x` 的种类 $\kappa'$, 目标在 `ofU y` 的代表 `embB y κ`, 读回是两次搬运的复合.

```agda
moveB : ∀ x y κ′ {κ} → cls x κ′ ≡ inj₁ κ → E (LU y) (embB y κ) → E (LU x) κ′
moveB x y κ′ p e = inB x κ′ p (outB y _ (cls-emb y _) e)
```

证据按同样的递归定义 (`EvU`), 与 `EvC` 互推; 在 `embB` 上的版本由此得到.

```agda
EvU : ∀ x → Cd → K (LU x) → Set
EvU hz B κ = Ev₁ B κ
EvU (hs x) B (inj₁ κ) = EvU x B κ
EvU (hs x) B (inj₂ _) = ⊤
EvU (hl f) B (n , κ) = EvU (f n) B κ
EvU (hΩ () _) B _

evU→C : ∀ x B κ′ → EvU x B κ′ → EvC x B κ′
evU→C hz B κ ev = ev
evU→C (hs x) B (inj₁ κ) ev = evU→C x B κ ev
evU→C (hs x) B (inj₂ _) ev = tt
evU→C (hl f) B (n , κ) ev = evU→C (f n) B κ ev
evU→C (hΩ () _) B _

evC→U : ∀ x B κ′ → EvC x B κ′ → EvU x B κ′
evC→U hz B κ ev = ev
evC→U (hs x) B (inj₁ κ) ev = evC→U x B κ ev
evC→U (hs x) B (inj₂ _) ev = tt
evC→U (hl f) B (n , κ) ev = evC→U (f n) B κ ev
evC→U (hΩ () _) B _

evMove : ∀ x y B κ′ {κ} → cls x κ′ ≡ inj₁ κ → EvU x B κ′ → EvU y B (embB y κ)
evMove x y B κ′ {κ} p ev =
  evC→U y B (embB y κ) (subst (λ z → [ Ev₁ B , (λ _ → ⊤) ]′ z) (trans p (sym (cls-emb y κ))) (evU→C x B κ′ ev))
```

## §4 拷贝: ℕ-极限偏移里, 底种类有可数多个代表

```agda
0≢1 : ¬ (0 ≡ 1)
0≢1 ()

copies-ll : ∀ (f : ℕ → Cd) κ →
  (cls (hl f) (0 , embB (f 0) κ) ≡ cls (hl f) (1 , embB (f 1) κ)) ×
  ¬ (_≡_ {A = K (LU (hl f))} (0 , embB (f 0) κ) (1 , embB (f 1) κ))
copies-ll f κ = trans (cls-emb (f 0) κ) (sym (cls-emb (f 1) κ)) , (λ e → 0≢1 (cong proj₁ e))

emb-not-unique : ∀ (f : ℕ → Cd) κ → ¬ (∀ κ′ → cls (hl f) κ′ ≡ inj₁ κ → κ′ ≡ embB (hl f) κ)
emb-not-unique f κ h = 0≢1 (cong proj₁ (sym (h (1 , embB (f 1) κ) (cls-emb (f 1) κ))))

-- 前提实例: 偏移 ω, Ω₁ 种类
natc : ℕ → Cd
natc zero = hz
natc (suc n) = hs (natc n)

ωo : Cd
ωo = hl natc

copies-ω : ¬ (∀ κ′ → cls ωo κ′ ≡ inj₁ κΩ → κ′ ≡ embB ωo κΩ)
copies-ω = emb-not-unique natc κΩ
```

## 结论 (按档)

- **[定理]** `cls-emb`, `E-base`, `lvl-base`, `lvl-new`, `E-new`, `lvl-emb`, `ev-emb` (对一切 $x$); `out-in`, `in-out`, `evU→C`, `evC→U`, `evMove`; **`copies-ll`**, **`emb-not-unique`**, `copies-ω`.
- **[构造]** `ofU`, `cls`, `embB`, `EvC`, `EvU`, **`outB`**, **`inB`**, `moveB`.
- **[测试]** `ev-emb-2`, `lvl-emb-2` (具体层号 $x=2$ 上是 refl).
- **[判断]** "对变量层号不是 refl" 是元层事实, 不写成对象层定理; "卡点只是工程量" 依据 3, 要构造一路的折叠来确认.
