# 最高层含与站层号同形的层, 否定一路 (二): 累加的最高层与前缀

> 不含记号. 入口 [NegLamIso](NegLamIso.lagda.md). 本篇**不依赖**接口 `LamIsoIf`. 导入 [LeanTBase](LeanTBase.lagda.md), [LeanTLv](LeanTLv.lagda.md), [LeanFbSt](LeanFbSt.lagda.md), [NegLeanLvPre](NegLeanLvPre.lagda.md) 的规范读法 `ofL`, `_≈_`, 与 [NegLamIsoPre](NegLamIsoPre.lagda.md) 的 `HasP` (都不改). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** `LeanLv` 接手清单第 1 条的候选: $\Lambda'=\mathrm{hl}\,P$, $P_{n+1}=P_n\boxplus(L_{n+1}\boxplus S_{n+1})$ (累加, 相邻项第一位置由 `⊞-fst` 给出), 级层取 $P_{n-1}\boxplus L_n$ ("`Sim` 要加一个前缀读成 `lz` 的构造子"). 本篇问: 这样的最高层里, 对一切世界是第一位置的层长什么样, 规范读法下能不能是 `st n`.
>
> 1. **第一位置的刻画 (§1, 定理 `⊞-inv`, `acc-cases`, `top-cases`).** $x\lhd a\boxplus b$ 当且仅当形状上 $x\lhd a$ 或 $x=a\boxplus b'$ 且 $b'\lhd b$. 所以累加的 $\mathrm{hl}\,P$ 的第一位置是: 它自己; $P_0$ 的第一位置; 或 $P_j\boxplus b'$, $b'\lhd Y_j$. **前缀是字面的**: 第 $j$ 块里的层一律带着整个 $P_j$.
> 2. **前缀的规范读法 (§2, 定理 `prefix-reads`).** 若 $b$ 不含 `L₀` 自己的新种类, `ofL (a ⊞ b) ≈ st n` 推出 `ofL a ≈ st j` 对某个 $j$ (`st n` 沿底坐标下降只经过站层号, `desc-st`). **`head-not-st`**: 外层是第 $m+1$ 站的头的层 (规范读法 `lΩ (st (m+1)) _`) 不与任何 `st j` 外延相等.
> 3. **对候选 (§3, 定理 `cand-no-own`).** $Y_j = Z_j\boxplus S_j$ (任意 $Z$, $P_0$; $Y$ 不含新种类) 时, 对 $j\ge2$, 一切 $P_{j+1}\boxplus b'$ ($b'\lhd Y_{j+1}$) 的规范读法都不是任何 `st n`. 合起来 (**`cand-own-early`**): 这样的 $\Lambda'$ 里, 规范读法为某个 `st n` 且对一切世界是第一位置的层, 只能在 $P_0$ 里或在前三块 ($P_0\boxplus b'$, $P_1\boxplus b'$, $P_2\boxplus b'$) 里. 候选里第 $n\ge3$ 块新加的 $L_n$ 带前缀之后不能当规范意义下自己的级层.
>
> **只否定什么.** 只否定: 累加式 $P_{n+1}=P_n\boxplus Y_n$ 且 $Y_n$ 外层是站层 $S_n$ ($n\ge2$) 时, 第 $3$ 块及以后带前缀的层在**规范读法 `ofL` 的外延相等**下是 `st n`. **不否定**: 接口另定的读法 (例如 "前缀读成 `lz`" 的同形, 那是另一个判据, 它与规范读法不同这件事本身由本篇给出); 不累加的 $\Lambda'$ (例如同形层在对角上逐项继承, 对照 `NegLamIsoPre.ΛC`); 同形层都放在前几块里的设计. 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLamIsoAcc where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanFbSt renaming (st to stL)
open import OCF.Lean.NegLeanLvPre using (ofL; _≈_; ≈-≡; subst-hz; st-shape; st-suc-nz; Sg)
open import OCF.Lean.NegLamIsoPre using (HasP; here; inS; inL; inΩ; has⊲; L₀)
```

## §1 $\boxplus$ 的第一位置; 累加的最高层

```agda
module _ {S : KS} where
  ⊞-inv : ∀ {w x} a b → x ⊲[ w ] a ⊞ b → (x ⊲[ w ] a) ⊎ Σ (HB S) (λ b′ → (x ≡ a ⊞ b′) × (b′ ⊲[ w ] b))
  ⊞-inv a hz p = inj₁ p
  ⊞-inv a (hs b) hself = inj₂ (hs b , refl , hself)
  ⊞-inv a (hs b) (hsuc p) with ⊞-inv a b p
  ... | inj₁ q = inj₁ q
  ... | inj₂ (b′ , e , q) = inj₂ (b′ , e , hsuc q)
  ⊞-inv a (hl f) hself = inj₂ (hl f , refl , hself)
  ⊞-inv a (hl f) (hlim n p) with ⊞-inv a (f n) p
  ... | inj₁ q = inj₁ q
  ... | inj₂ (b′ , e , q) = inj₂ (b′ , e , hlim n q)
  ⊞-inv a (hΩ κ g) hself = inj₂ (hΩ κ g , refl , hself)
  ⊞-inv a (hΩ κ g) (hLim e p) with ⊞-inv a (g _) p
  ... | inj₁ q = inj₁ q
  ... | inj₂ (b′ , eq , q) = inj₂ (b′ , eq , hLim e q)

  module Acc (P₀ : HB S) (Y : ℕ → HB S) where
    P : ℕ → HB S
    P zero = P₀
    P (suc n) = P n ⊞ Y n

    P-st : ∀ {w} n → P n ⊲[ w ] P (suc n)
    P-st n = ⊞-fst (P n) (Y n)

    Blk : Wd S → HB S → Set
    Blk w x = Σ ℕ (λ j → Σ (HB S) (λ b′ → (x ≡ P j ⊞ b′) × (b′ ⊲[ w ] Y j)))

    acc-cases : ∀ {w x} k → x ⊲[ w ] P k → (x ⊲[ w ] P₀) ⊎ Blk w x
    acc-cases zero p = inj₁ p
    acc-cases (suc k) p with ⊞-inv (P k) (Y k) p
    ... | inj₁ q = acc-cases k q
    ... | inj₂ (b′ , e , q) = inj₂ (k , b′ , e , q)

    top-cases : ∀ {w x} → x ⊲[ w ] hl P → (x ≡ hl P) ⊎ ((x ⊲[ w ] P₀) ⊎ Blk w x)
    top-cases hself = inj₁ refl
    top-cases (hlim n p) = inj₂ (acc-cases n p)
```

## §2 前缀的规范读法

`New`: `L₀` 自己的新种类 (`ofL` 把它读成 `lz`, $\Lambda_F$ 与候选里都不出现). `Desc y y′`: 沿底坐标 ($\mathbb N$-极限取第 0 项, $\Omega$-极限取坐标 $0$) 从 $y$ 下降到 $y'$.

```agda
New : K L₀ → Set
New (inj₁ _) = ⊥
New (inj₂ _) = ⊤

data Desc : LH → LH → Set where
  dz : ∀ {y} → Desc y y
  ds : ∀ {y y′} → Desc y y′ → Desc (ls y) y′
  dl : ∀ {g y′} → Desc (g 0) y′ → Desc (ll g) y′
  dΩ : ∀ {k g y′} → Desc (g hz) y′ → Desc (lΩ k g) y′

Desc-tr : ∀ {x y z} → Desc x y → Desc y z → Desc x z
Desc-tr dz q = q
Desc-tr (ds p) q = ds (Desc-tr p q)
Desc-tr (dl p) q = dl (Desc-tr p q)
Desc-tr (dΩ p) q = dΩ (Desc-tr p q)
```

**`node` 的一步下降.**

```agda
lΩ-step : ∀ k (h : HB (Lv k) → LH) y → lΩ k h ≈ y → Σ LH (λ y₁ → Desc y y₁ × (h hz ≈ y₁))
lΩ-step k h (lΩ k′ g′) (e , q) = g′ hz , dΩ dz , ≈-≡ (h hz) (q hz) (cong g′ (subst-hz e))
lΩ-step k h lz ()
lΩ-step k h (ls _) ()
lΩ-step k h (ll _) ()

nodeD : ∀ k κ (h : E (Lv k) κ → LH) y → node k κ h ≈ y → Σ LH (λ y₁ → Desc y y₁ × (h (bot (Lv k) κ) ≈ y₁))
nodeD lz (() , _) h y p
nodeD (ls x) (inj₁ κ) h y p = nodeD x κ h y p
nodeD (ls x) (inj₂ _) h y p = lΩ-step x h y p
nodeD (ll f) (n , κ) h y p = nodeD (f n) κ h y p
nodeD (lΩ k g) (inj₁ _ , inj₁ κ) h y p = nodeD k κ h y p
nodeD (lΩ k g) (inj₁ _ , inj₂ _) h y p = lΩ-step k h y p
nodeD (lΩ k g) (inj₂ c , κ) h y p = nodeD (g c) κ h y p
```

**定理 `prefix-reads`.** $b$ 不含新种类时, `ofL (a ⊞ b) ≈ y` 推出 `ofL a` 与 $y$ 沿底坐标的某个下降外延相等.

```agda
prefix-desc : ∀ a b y → ¬ HasP New b → ofL (a ⊞ b) ≈ y → Σ LH (λ y′ → Desc y y′ × (ofL a ≈ y′))
prefix-desc a hz y nn p = y , dz , p
prefix-desc a (hs b) (ls y) nn p with prefix-desc a b y (λ h → nn (inS h)) p
... | y′ , d , q = y′ , ds d , q
prefix-desc a (hs b) lz nn ()
prefix-desc a (hs b) (ll _) nn ()
prefix-desc a (hs b) (lΩ _ _) nn ()
prefix-desc a (hl f) (ll g) nn p with prefix-desc a (f 0) (g 0) (λ h → nn (inL 0 h)) (p 0)
... | y′ , d , q = y′ , dl d , q
prefix-desc a (hl f) lz nn ()
prefix-desc a (hl f) (ls _) nn ()
prefix-desc a (hl f) (lΩ _ _) nn ()
prefix-desc a (hΩ (inj₂ _) g) y nn p with nn (here tt)
... | ()
prefix-desc a (hΩ (inj₁ (m , inj₂ _)) g) y nn p with lΩ-step (stL m) (λ c → ofL (a ⊞ g c)) y p
... | y₁ , d₁ , q with prefix-desc a (g hz) y₁ (λ h → nn (inΩ hz h)) q
... | y′ , d₂ , r = y′ , Desc-tr d₁ d₂ , r
prefix-desc a (hΩ (inj₁ (m , inj₁ κ)) g) y nn p with nodeD (stL m) κ (λ c → ofL (a ⊞ g c)) y p
... | y₁ , d₁ , q with prefix-desc a (g (bot (Lv (stL m)) κ)) y₁ (λ h → nn (inΩ _ h)) q
... | y′ , d₂ , r = y′ , Desc-tr d₁ d₂ , r
```

**`st n` 沿底坐标只下降到站层号.**

```agda
desc-st₁ : ∀ {y′} → Desc (stL 1) y′ → Σ ℕ (λ j → y′ ≡ stL j)
desc-st₁ dz = 1 , refl
desc-st₁ (ds dz) = 0 , refl

H : ℕ → HB (Lv lz) → LH
H m = proj₁ (st-shape m)

-- st (2+m) ≡ lΩ lz (H m), H m hz ≡ st (1+m)
desc-st′ : ∀ m {y′} → Desc (lΩ lz (H m)) y′ → Σ ℕ (λ j → y′ ≡ stL j)
desc-st′ m dz = suc (suc m) , sym (proj₁ (proj₂ (st-shape m)))
desc-st′ zero {y′} (dΩ d′) = desc-st₁ (subst (λ z → Desc z y′) (proj₂ (proj₂ (st-shape zero))) d′)
desc-st′ (suc m) {y′} (dΩ d′) =
  desc-st′ m (subst (λ z → Desc z y′) (trans (proj₂ (proj₂ (st-shape (suc m)))) (proj₁ (proj₂ (st-shape m)))) d′)

desc-st : ∀ n {y′} → Desc (stL n) y′ → Σ ℕ (λ j → y′ ≡ stL j)
desc-st zero dz = zero , refl
desc-st (suc zero) d = desc-st₁ d
desc-st (suc (suc m)) {y′} d = desc-st′ m (subst (λ z → Desc z y′) (proj₁ (proj₂ (st-shape m))) d)

prefix-reads : ∀ a b n → ¬ HasP New b → ofL (a ⊞ b) ≈ stL n → Σ ℕ (λ j → ofL a ≈ stL j)
prefix-reads a b n nn p with prefix-desc a b (stL n) nn p
... | y′ , d , q with desc-st n d
... | j , e = j , ≈-≡ (ofL a) q e
```

**定理 `head-not-st`.** 外层是第 $m+1$ 站的头的结点, 规范读法与任何 `st j` 都不外延相等.

```agda
head-not-st : ∀ m (g : HB (Lv (stL (suc m))) → HB L₀) j → ¬ (ofL (hΩ (inj₁ (νS (suc m))) g) ≈ stL j)
head-not-st m g zero ()
head-not-st m g (suc zero) ()
head-not-st m g (suc (suc i)) p with ≈-≡ _ p (proj₁ (proj₂ (st-shape i)))
... | e , _ = st-suc-nz m e
```

## §3 对候选

候选: $Y_j = Z_j\boxplus S_j$ (`Sg j` = `up (1 ⊞ tws j)`), $P_0$, $Z$ 任意. 当 $j\ge2$, $Y_j$ 的外层是第 $j-1$ 站的头, 所以 $P_{j+1}$ 的外层也是.

```agda
module Cand (P₀ : HB L₀) (Z : ℕ → HB L₀) where
  Y : ℕ → HB L₀
  Y j = Z j ⊞ Sg j

  open Acc P₀ Y public

  P-head : ∀ i → Σ (HB (Lv (stL (suc i))) → HB L₀) (λ g → P (suc (suc (suc i))) ≡ hΩ (inj₁ (νS (suc i))) g)
  P-head i = _ , refl

  P-not-st : ∀ i j → ¬ (ofL (P (suc (suc (suc i)))) ≈ stL j)
  P-not-st i j p with P-head i
  ... | g , e = head-not-st i g j (≈-≡ _ (subst (λ t → ofL t ≈ stL j) e p) refl)

  -- 第 3 块及以后: 带前缀的层不是任何 st n
  cand-no-own : ∀ i b′ n → ¬ HasP New b′ → ¬ (ofL (P (suc (suc (suc i))) ⊞ b′) ≈ stL n)
  cand-no-own i b′ n nn p with prefix-reads (P (suc (suc (suc i)))) b′ n nn p
  ... | j , q = P-not-st i j q
```

**合起来.** $Y$ 不含新种类时, 规范读法为 `st n` 且是第一位置的层, 要么在 $P_0$ 里, 要么在前三块里.

```agda
  Early : Wd L₀ → HB L₀ → Set
  Early w x = (x ⊲[ w ] P₀) ⊎ Σ ℕ (λ j → Σ (HB L₀) (λ b′ → (x ≡ P j ⊞ b′) × (b′ ⊲[ w ] Y j) × ¬ (Σ ℕ (λ i → j ≡ suc (suc (suc i))))))

  ll-not-st : ∀ (f : ℕ → LH) j → ¬ (ll f ≈ stL j)
  ll-not-st f zero ()
  ll-not-st f (suc zero) ()
  ll-not-st f (suc (suc i)) p with ≈-≡ _ p (proj₁ (proj₂ (st-shape i)))
  ... | ()

  cand-own-early : ∀ {w x} n → (∀ j → ¬ HasP New (Y j)) → x ⊲[ w ] hl P → ofL x ≈ stL n → Early w x
  cand-own-early n nnY p q with top-cases p
  ... | inj₁ refl = ⊥-elim′ (ll-not-st _ n q)
    where
    ⊥-elim′ : ∀ {A : Set} → ⊥ → A
    ⊥-elim′ ()
  ... | inj₂ (inj₁ r) = inj₁ r
  ... | inj₂ (inj₂ (j , b′ , e , r)) = inj₂ (j , b′ , e , r , late)
    where
    late : ¬ Σ ℕ (λ i → j ≡ suc (suc (suc i)))
    late (i , refl) = cand-no-own i b′ n (λ h → nnY _ (has⊲ New h r)) (subst (λ t → ofL t ≈ stL n) e q)
```

**前提实例.** $P_0=0$, $Z_j=0$: $Y_j=S_j$ 不含新种类 (`Y0-nn`, 它是 `up` 的像); $\mathrm{hl}\,P$ 合法的相邻项第一位置 `P-st`; `cand-no-own` 的层 $P_3\boxplus 0 = P_3$ 对一切世界是第一位置 (`P3-fst`).

```agda
up-nn : ∀ (a : HB SLs) → ¬ HasP New (up a)
up-nn hz ()
up-nn (hs a) (inS h) = up-nn a h
up-nn (hl f) (inL n h) = up-nn (f n) h
up-nn (hΩ κ g) (inΩ c h) = up-nn (g c) h

nn-⊞ : ∀ (a b : HB L₀) → ¬ HasP New a → ¬ HasP New b → ¬ HasP New (a ⊞ b)
nn-⊞ a hz na nb h = na h
nn-⊞ a (hs b) na nb (inS h) = nn-⊞ a b na (λ h′ → nb (inS h′)) h
nn-⊞ a (hl f) na nb (inL n h) = nn-⊞ a (f n) na (λ h′ → nb (inL n h′)) h
nn-⊞ a (hΩ κ g) na nb (here p) = nb (here p)
nn-⊞ a (hΩ κ g) na nb (inΩ c h) = nn-⊞ a (g c) na (λ h′ → nb (inΩ c h′)) h

module Inst where
  open Cand hz (λ _ → hz)

  Y0-nn : ∀ j → ¬ HasP New (Y j)
  Y0-nn j = nn-⊞ hz (Sg j) (λ ()) (up-nn _)

  P3-fst : ∀ {w} → P 3 ⊲[ w ] hl P
  P3-fst = hlim 3 hself

  P3-not-own : ∀ n → ¬ (ofL (P 3) ≈ stL n)
  P3-not-own n = cand-no-own 0 hz n (λ ())
```

## §4 结论 (按档)

- **[定理, 一般]** **`⊞-inv`**, `acc-cases`, **`top-cases`**: 累加的 $\mathrm{hl}\,P$ 的第一位置 (任一世界) 是它自己, $P_0$ 的第一位置, 或 $P_j\boxplus b'$ ($b'\lhd Y_j$).
- **[定理, 读法]** **`prefix-reads`** (`prefix-desc`, `desc-st`, `nodeD`): 不含新种类的 $b$ 上, `ofL (a ⊞ b) ≈ st n` 推出 `ofL a ≈ st j`. **`head-not-st`**: 外层是第 $m+1$ 站的头的层不读成任何 `st j`.
- **[定理, 对候选]** **`cand-no-own`**, **`cand-own-early`**: 接手清单的累加候选 ($Y_j=Z_j\boxplus S_j$) 里, 规范读法为某个 `st n` 的第一位置层只在 $P_0$ 或前三块. 前提实例 `Inst` (`Y0-nn`, `P3-fst`, `P3-not-own`).
- **[判断]** (i) 候选要 "前缀读成 `lz`" 的同形, 这是比规范读法宽的判据; 宽在哪里由 `prefix-reads` 给出: 前缀必须被读掉, 而前缀里有站 $j-1$ 的头 (`head-not-st`), 它们的数据在按级读回时去哪里, 接口要说明. (ii) 不累加的设计 (同形层在对角上逐项继承) 不受本篇约束.
