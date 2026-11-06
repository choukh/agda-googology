# ValC (一): 可数层号上的值关系 (按层比较种类, 没有无限制的 "极限在左边")

> 不含记号. 入口 [ValC](ValC.lagda.md), 接口 [ValCIf](ValCIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP. 只导入 stdlib 与 `OCF.Lean.CRw*` (不改它们).
>
> **从 Fab5 搬过来, 改了两处.** 参考 [Fab5ValRel](../Align/Fab5ValRel.lagda.md) (只作参考, 重写在 `CRwBase` 的高度上). 对象是 CRw 的可数层号 $t$ 上的塔 `Tw S⊥ t` (第 $t$ 层).
>
> 1. **ℕ-极限在左边只能对子列.** Fab5 的 `l≤` ($\forall n.\,f_n\le b\Rightarrow\lim f\le b$) 换成 `l≤l σ`: $\lim f\le\lim g$, 当 $\sigma$ 严格增且 $f_n\le g_{\sigma n}$. 理由是 CRw 的折叠在 ℕ-极限处取部分和: $\lim(0,0,\dots)$ 与 $0$ 值相同, 折出来却是 $\omega$ 与 $1$ (否定一路 `NegValCInst.acc-not-mono≤`, 与本路读码一致). 部分和只对 "严格增的子列" 单调, 所以关系只留这一种极限在左边. 这仍是值关系的可靠子关系 (第 0 层推出标准前序, 入口 `sound₀`).
> 2. **$\Omega$-结点按种类的层比较.** Fab5 的 `Ω≤Ω` 要求两边是同一个种类. CRw 的塔里, 同一层 $k$ 的 $\Omega_{k+1}$ 有许多种类 (经 ℕ-极限的不同分量到达, `along q` 的路径不同), 坐标类型都是第 $k$ 层的高度. 折叠留下的种类由 `cmpB` 的路径决定, 两种折法 (直接 / 经中间层) 的路径可能不同, 所以 `Ω≤Ω` 只要求两种类的层相等 (`lvK`), 坐标经 `subst` 搬运.
>
> 世界去掉: 坐标的值界取规范的地板 `top b⊥ k`. 分层仍是 Fab5 的做法: 第 $t$ 层的关系由一个记录 `Low t` (每个种类的坐标上的值关系与值合法) 参数化, `lowT` 对 $t$ 结构递归给出; 跨种类的搬运由 "每个种类的坐标关系就是它那一层的关系" (`lmo→` 等, 对 $t$ 归纳) 加上对层号的 J 给出.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwIf
module OCF.Lean.ValCRel (I : CRwIf) where

open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (n<1+n; <-trans)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwFold I
```

## §1 种类的层, 坐标, 路径

```agda
T : Cd → KS
T t = Tw S⊥ t

H : Cd → Set
H t = HB (T t)

lvK : ∀ t → K (T t) → Cd
lvK hz ()
lvK (hs x) (inj₁ κ) = lvK x κ
lvK (hs x) (inj₂ _) = x
lvK (hl f) (n , κ) = lvK (f n) κ
lvK (hΩ () _) _

toK : ∀ t κ → H (lvK t κ) → E (T t) κ
toK hz ()
toK (hs x) (inj₁ κ) c = toK x κ c
toK (hs x) (inj₂ _) c = c
toK (hl f) (n , κ) c = toK (f n) κ c
toK (hΩ () _) _

pK : ∀ t κ → hs (lvK t κ) ⊲ t
pK hz ()
pK (hs x) (inj₁ κ) = hsuc (pK x κ)
pK (hs x) (inj₂ _) = hself
pK (hl f) (n , κ) = hlim n (pK (f n) κ)
pK (hΩ () _) _

clEq : ∀ t κ → cl t κ ≡ nw (lvK t κ) (pK t κ) (toK t κ)
clEq hz ()
clEq (hs x) (inj₁ κ) = cong cS (clEq x κ)
clEq (hs x) (inj₂ _) = refl
clEq (hl f) (n , κ) = cong (cL n) (clEq (f n) κ)
clEq (hΩ () _) _

lvA : ∀ {i t} (q : hs i ⊲ t) → lvK t (along q) ≡ i
lvA hself = refl
lvA (hsuc q) = lvA q
lvA (hlim n q) = lvA q
lvA (hLim {κ = ()} _ _)

frto : ∀ {i t} (q : hs i ⊲ t) c → frA q (toK t (along q) c) ≡ subst H (lvA q) c
frto hself c = refl
frto (hsuc q) c = frto q c
frto (hlim n q) c = frto q c
frto (hLim {κ = ()} _ _) _
```

## §2 没有真回路

$x\lhd a$ 且 $a$ 真包含于 $x$ (`Pp a x`) 不可能. 推论: $k+1\not\lhd k$, $k$ 到自身没有经后继或 ℕ-极限的路径. 折叠的决定 (留 / 同层 / 在上) 因此只依赖种类的层与目标, 不依赖路径 (§5 之后用).

```agda
data Pp (a : Cd) : Cd → Set where
  pps : ∀ {y} → a ⊲ y → Pp a (hs y)
  ppl : ∀ {f} n → a ⊲ f n → Pp a (hl f)

nl : ∀ (a : Cd) {x} → x ⊲ a → Pp a x → ⊥
nl hz hself ()
nl (hs b) hself (pps u) = nl b u (pps hself)
nl (hs b) (hsuc p) (pps u) = nl b p (pps (⊲ᴮ-tr (hsuc hself) u))
nl (hs b) (hsuc p) (ppl n u) = nl b p (ppl n (⊲ᴮ-tr (hsuc hself) u))
nl (hl f) hself (ppl n u) = nl (f n) u (ppl n hself)
nl (hl f) (hlim n p) (pps u) = nl (f n) p (pps (⊲ᴮ-tr (hlim n hself) u))
nl (hl f) (hlim n p) (ppl m u) = nl (f n) p (ppl m (⊲ᴮ-tr (hlim n hself) u))
nl (hΩ () _) _ _

nos : ∀ {k} → hs k ⊲ k → ⊥
nos {k} p = nl k p (pps hself)

nos′ : ∀ {k t} → hs k ⊲ t → t ⊲ k → ⊥
nos′ p q = nos (⊲ᴮ-tr p q)
```

## §3 坐标关系的记录, 关系, `Mo`

```agda
record Low (t : Cd) : Set₁ where
  field
    LMo  : ∀ κ → H (lvK t κ) → Set
    LLe  : ∀ κ → H (lvK t κ) → H (lvK t κ) → Set
    LMo-z : ∀ κ → LMo κ hz
    LLe-z : ∀ κ d → LLe κ hz d
open Low public

Inc : (ℕ → ℕ) → Set
Inc σ = ∀ n → σ n < σ (suc n)

module Rel (t : Cd) (lw : Low t) where
  infix 4 _≤_
  data _≤_ : H t → H t → Set where
    z≤  : ∀ {b} → hz ≤ b
    s≤s : ∀ {a b} → a ≤ b → hs a ≤ hs b
    ≤s  : ∀ {a b} → a ≤ b → a ≤ hs b
    l≤l : ∀ {f g} (σ : ℕ → ℕ) → Inc σ → (∀ n → f n ≤ g (σ n)) → hl f ≤ hl g
    ≤l  : ∀ {a g} n → a ≤ g n → a ≤ hl g
    ≤Ω  : ∀ {a κ g} c → LLe lw κ c (top b⊥ (lvK t κ)) → LMo lw κ c → a ≤ g (toK t κ c) → a ≤ hΩ κ g
    Ω≤Ω : ∀ {κ κ′ g g′} (e : lvK t κ ≡ lvK t κ′) →
          (∀ c → LMo lw κ c → g (toK t κ c) ≤ g′ (toK t κ′ (subst H e c))) → hΩ κ g ≤ hΩ κ′ g′

  Mo : H t → Set
  Mo hz = ⊤
  Mo (hs h) = Mo h
  Mo (hl f) = ∀ n → Mo (f n)
  Mo (hΩ κ g) =
    (∀ c c′ → LMo lw κ c → LMo lw κ c′ → LLe lw κ c c′ → g (toK t κ c) ≤ g (toK t κ c′)) ×
    (∀ c → LMo lw κ c → Mo (g (toK t κ c)))

  idInc : Inc (λ n → n)
  idInc n = n<1+n n

  ≤-refl : ∀ a → a ≤ a
  ≤-refl hz = z≤
  ≤-refl (hs a) = s≤s (≤-refl a)
  ≤-refl (hl f) = l≤l (λ n → n) idInc (λ n → ≤-refl (f n))
  ≤-refl (hΩ κ g) = Ω≤Ω refl (λ c _ → ≤-refl (g (toK t κ c)))
```

**加法** (不用传递): $a\le a\boxplus b$, $x\le a\boxplus x$, 两边单调, 保 `Mo`.

```agda
  ≤⊞ : ∀ a b → a ≤ a ⊞ b
  ≤⊞ a hz = ≤-refl a
  ≤⊞ a (hs b) = ≤s (≤⊞ a b)
  ≤⊞ a (hl f) = ≤l 0 (≤⊞ a (f 0))
  ≤⊞ a (hΩ κ g) = ≤Ω hz (LLe-z lw κ _) (LMo-z lw κ) (≤⊞ a (g (toK t κ hz)))

  ≤⊞ˡ : ∀ a x → x ≤ a ⊞ x
  ≤⊞ˡ a hz = z≤
  ≤⊞ˡ a (hs x) = s≤s (≤⊞ˡ a x)
  ≤⊞ˡ a (hl f) = l≤l (λ n → n) idInc (λ n → ≤⊞ˡ a (f n))
  ≤⊞ˡ a (hΩ κ g) = Ω≤Ω refl (λ c _ → ≤⊞ˡ a (g (toK t κ c)))

  ⊞-monoˡ : ∀ {a a′} x → a ≤ a′ → a ⊞ x ≤ a′ ⊞ x
  ⊞-monoˡ hz p = p
  ⊞-monoˡ (hs x) p = s≤s (⊞-monoˡ x p)
  ⊞-monoˡ (hl f) p = l≤l (λ n → n) idInc (λ n → ⊞-monoˡ (f n) p)
  ⊞-monoˡ (hΩ κ g) p = Ω≤Ω refl (λ c _ → ⊞-monoˡ (g (toK t κ c)) p)

  ⊞-monoʳ : ∀ a {x y} → x ≤ y → a ⊞ x ≤ a ⊞ y
  ⊞-monoʳ a (z≤ {b = y}) = ≤⊞ a y
  ⊞-monoʳ a (s≤s p) = s≤s (⊞-monoʳ a p)
  ⊞-monoʳ a (≤s p) = ≤s (⊞-monoʳ a p)
  ⊞-monoʳ a (l≤l σ i h) = l≤l σ i (λ n → ⊞-monoʳ a (h n))
  ⊞-monoʳ a (≤l n p) = ≤l n (⊞-monoʳ a p)
  ⊞-monoʳ a (≤Ω c e m p) = ≤Ω c e m (⊞-monoʳ a p)
  ⊞-monoʳ a (Ω≤Ω e h) = Ω≤Ω e (λ c mc → ⊞-monoʳ a (h c mc))

  Mo-⊞ : ∀ a b → Mo a → Mo b → Mo (a ⊞ b)
  Mo-⊞ a hz ma mb = ma
  Mo-⊞ a (hs b) ma mb = Mo-⊞ a b ma mb
  Mo-⊞ a (hl f) ma mb = λ n → Mo-⊞ a (f n) ma (mb n)
  Mo-⊞ a (hΩ κ g) ma (mo , mh) =
    (λ c c′ mc mc′ p → ⊞-monoʳ a (mo c c′ mc mc′ p)) , (λ c mc → Mo-⊞ a (g (toK t κ c)) ma (mh c mc))
```

**传递** 要坐标的值合法与值界能沿层号相等搬运 (模块参数; 对 `lowT` 在 §4 给出).

```agda
  module Tr (trMo : ∀ {κ κ′} (e : lvK t κ ≡ lvK t κ′) c → LMo lw κ c → LMo lw κ′ (subst H e c))
            (trBd : ∀ {κ κ′} (e : lvK t κ ≡ lvK t κ′) c →
                    LLe lw κ c (top b⊥ (lvK t κ)) → LLe lw κ′ (subst H e c) (top b⊥ (lvK t κ′))) where

    ss : ∀ {i j k} (e : i ≡ j) (e′ : j ≡ k) (c : H i) → subst H e′ (subst H e c) ≡ subst H (trans e e′) c
    ss refl refl c = refl

    inc∘ : ∀ {σ τ} → Inc σ → Inc τ → Inc (λ n → τ (σ n))
    inc∘ {σ} {τ} i j n = incM (i n)
      where
      incM : ∀ {a b} → a < b → τ a < τ b
      incM {a} {suc b} (Data.Nat.s≤s p) with Data.Nat.Properties.m≤n⇒m<n∨m≡n p
      ... | inj₁ a<b = <-trans (incM a<b) (j b)
      ... | inj₂ refl = j a

    ≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
    ≤-trans z≤ q = z≤
    ≤-trans p (≤s q) = ≤s (≤-trans p q)
    ≤-trans p (≤l n q) = ≤l n (≤-trans p q)
    ≤-trans p (≤Ω c e m q) = ≤Ω c e m (≤-trans p q)
    ≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)
    ≤-trans (≤s p) (s≤s q) = ≤s (≤-trans p q)
    ≤-trans (l≤l σ i h) (l≤l τ j h′) = l≤l (λ n → τ (σ n)) (inc∘ i j) (λ n → ≤-trans (h n) (h′ (σ n)))
    ≤-trans (≤l n p) (l≤l τ j h′) = ≤l (τ n) (≤-trans p (h′ n))
    ≤-trans (≤Ω c e m p) (Ω≤Ω e′ h′) = ≤Ω (subst H e′ c) (trBd e′ c e) (trMo e′ c m) (≤-trans p (h′ c m))
    ≤-trans {hΩ κ g} {hΩ κ′ g′} {hΩ κ″ g″} (Ω≤Ω e h) (Ω≤Ω e′ h′) =
      Ω≤Ω (trans e e′) (λ c m → subst (λ z → g (toK t κ c) ≤ g″ (toK t κ″ z)) (ss e e′ c)
        (≤-trans (h c m) (h′ (subst H e c) (trMo e c m))))

    ⊞-mono : ∀ {a a′ x y} → a ≤ a′ → x ≤ y → a ⊞ x ≤ a′ ⊞ y
    ⊞-mono {x = x} p q = ≤-trans (⊞-monoˡ x p) (⊞-monoʳ _ q)
```

## §4 各层的坐标关系, 与搬运

```agda
lowT : ∀ t → Low t
lowT hz = record { LMo = λ () ; LLe = λ () ; LMo-z = λ () ; LLe-z = λ () }
lowT (hs x) = record { LMo = M ; LLe = L ; LMo-z = Mz ; LLe-z = Lz }
  where
  M : ∀ κ → H (lvK (hs x) κ) → Set
  M (inj₁ κ) = LMo (lowT x) κ
  M (inj₂ _) = Rel.Mo x (lowT x)
  L : ∀ κ → H (lvK (hs x) κ) → H (lvK (hs x) κ) → Set
  L (inj₁ κ) = LLe (lowT x) κ
  L (inj₂ _) = Rel._≤_ x (lowT x)
  Mz : ∀ κ → M κ hz
  Mz (inj₁ κ) = LMo-z (lowT x) κ
  Mz (inj₂ _) = tt
  Lz : ∀ κ d → L κ hz d
  Lz (inj₁ κ) = LLe-z (lowT x) κ
  Lz (inj₂ _) d = Rel.z≤
lowT (hl f) = record { LMo = λ κ → LMo (lowT (f (proj₁ κ))) (proj₂ κ) ; LLe = λ κ → LLe (lowT (f (proj₁ κ))) (proj₂ κ)
                     ; LMo-z = λ κ → LMo-z (lowT (f (proj₁ κ))) (proj₂ κ) ; LLe-z = λ κ → LLe-z (lowT (f (proj₁ κ))) (proj₂ κ) }
lowT (hΩ () _)

-- 第 t 层的关系与值合法
LeAt : ∀ t → H t → H t → Set
LeAt t = Rel._≤_ t (lowT t)

MoAt : ∀ t → H t → Set
MoAt t = Rel.Mo t (lowT t)

-- 每个种类的坐标关系就是它那一层的关系 (两个方向)
lmo→ : ∀ t κ c → LMo (lowT t) κ c → MoAt (lvK t κ) c
lmo→ hz ()
lmo→ (hs x) (inj₁ κ) c m = lmo→ x κ c m
lmo→ (hs x) (inj₂ _) c m = m
lmo→ (hl f) (n , κ) c m = lmo→ (f n) κ c m
lmo→ (hΩ () _) _

→lmo : ∀ t κ c → MoAt (lvK t κ) c → LMo (lowT t) κ c
→lmo hz ()
→lmo (hs x) (inj₁ κ) c m = →lmo x κ c m
→lmo (hs x) (inj₂ _) c m = m
→lmo (hl f) (n , κ) c m = →lmo (f n) κ c m
→lmo (hΩ () _) _

lle→ : ∀ t κ c d → LLe (lowT t) κ c d → LeAt (lvK t κ) c d
lle→ hz ()
lle→ (hs x) (inj₁ κ) c d p = lle→ x κ c d p
lle→ (hs x) (inj₂ _) c d p = p
lle→ (hl f) (n , κ) c d p = lle→ (f n) κ c d p
lle→ (hΩ () _) _

→lle : ∀ t κ c d → LeAt (lvK t κ) c d → LLe (lowT t) κ c d
→lle hz ()
→lle (hs x) (inj₁ κ) c d p = →lle x κ c d p
→lle (hs x) (inj₂ _) c d p = p
→lle (hl f) (n , κ) c d p = →lle (f n) κ c d p
→lle (hΩ () _) _

-- 沿层号相等搬运 (J)
MoAt-tr : ∀ {j j′} (e : j ≡ j′) c → MoAt j c → MoAt j′ (subst H e c)
MoAt-tr refl c m = m

LeAt-tr : ∀ {j j′} (e : j ≡ j′) c d → LeAt j c d → LeAt j′ (subst H e c) (subst H e d)
LeAt-tr refl c d p = p

top-tr : ∀ {j j′} (e : j ≡ j′) → subst H e (top b⊥ j) ≡ top b⊥ j′
top-tr refl = refl

trMoT : ∀ t {κ κ′} (e : lvK t κ ≡ lvK t κ′) c → LMo (lowT t) κ c → LMo (lowT t) κ′ (subst H e c)
trMoT t {κ} {κ′} e c m = →lmo t κ′ _ (MoAt-tr e c (lmo→ t κ c m))

trBdT : ∀ t {κ κ′} (e : lvK t κ ≡ lvK t κ′) c →
        LLe (lowT t) κ c (top b⊥ (lvK t κ)) → LLe (lowT t) κ′ (subst H e c) (top b⊥ (lvK t κ′))
trBdT t {κ} {κ′} e c p =
  →lle t κ′ _ _ (subst (λ z → LeAt (lvK t κ′) (subst H e c) z) (top-tr e)
    (LeAt-tr e c _ (lle→ t κ c _ p)))

module L (t : Cd) where
  open Rel t (lowT t) public
  open Tr (trMoT t) (trBdT t) public
```

## 结论 (按档)

- **[定理]** `lvK`, `toK`, `pK`, `clEq` (种类的分类就是 (层, 路径, 坐标)), `lvA`, `frto`; `nl`, `nos`, `nos′` (没有真回路); `Rel._≤_`, `Rel.Mo`, `≤-refl`, `≤⊞`, `≤⊞ˡ`, `⊞-monoˡ`, `⊞-monoʳ`, `Mo-⊞`; `lowT`, `LeAt`, `MoAt`, 搬运 `lmo→`, `→lmo`, `lle→`, `→lle`, `MoAt-tr`, `LeAt-tr`, `top-tr`; 对一切层 `L.≤-trans`, `L.⊞-mono`.
