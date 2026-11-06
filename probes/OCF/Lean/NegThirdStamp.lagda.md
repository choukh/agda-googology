# 第三种组织, 否定一路 (三): 坐标带证据 (戳) 与合法性

> 不含记号. 入口 [NegThird](NegThird.lagda.md). 只导入 [CRwBase](CRwBase.lagda.md), [NegThirdPre](NegThirdPre.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** 构造一路判断: 戳方案 (新种类的坐标 $=$ (值 $c$, 证据), 证据含世界 $V$ 与路径) 断在合法性: 分支读证据时 `LgB` 的单调不成立. 这里写成定理, 并看序怎样改.
>
> 1. **`antisym`** (对一切 `S`, 一切世界): 第一位置反对称.
> 2. **(A) 序只看值.** `SE.stepE`: 对任一证据族 `Ev` (有 `ev₀`) 是种类结构, `cmpK` 由 `cmpB`. **`SE.branch-indep`**: 合法的结点, 同一个值在界之下时, 分支不读证据 ($g(c,a)\equiv g(c,a')$). **`SE₀.reads-illegal`**: 证据是戳 $V$, 分支读 $V$ 的结点不合法.
> 3. **(B) 序也读证据 (积序).** **`SEp.no-cmp-product`**: 值与戳反向的两个坐标积序下不可比, 所以 `cmpK` 不成立, 不是 `KS`.
> 4. **(C) 字典序.** **`SEp.lex-needs`**: 值严格变大时分支对任意两份证据都上升; 只读戳的分支违反它.
>
> **前提实例.** 2: `SE₀` (世界 $(\mathrm{tt},0)$ 合法, $0\lhd0$, 两份证据 $0$, $1$). 3: `bdp` ($a_0,a_1$ 的分量都在 $2$ 之下). 4: `a₀`, `a₁`.
>
> **只否定什么.** 2 只否定: 序只看值的 `stepE` 上读证据的合法结点. 3 只否定积序满足 `cmpK`. 4 只否定字典序下只读戳的分支. **不否定**: 分支读证据但跨戳单调 (例如 $g$ 对值与戳的某个合成单调); 改 `KS` 的 `cmpK` 字段; 用形状证书 (`Sh`) 而不用 `LgB` 走中间层, 只在闭项读 `LgB`; 把回灌改成不要合法高度的做法. 所以戳方案 **未走通**, 不是已否定: 这三条只说它不能同时要 "序不读证据", "分支读证据", "`LgB`".

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegThirdStamp where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.NegThirdPre using (num)
```

## §1 第一位置反对称

```agda
module _ {S : KS} where
  data Sub : HB S → HB S → Set where
    sS : ∀ {a b} → a ≡ b → Sub a (hs b)
    sL : ∀ {a f} n → a ≡ f n → Sub a (hl f)
    sΩ : ∀ {a κ g} c → a ≡ g c → Sub a (hΩ κ g)
    sT : ∀ {a b c} → Sub a b → Sub b c → Sub a c

  data AccS (x : HB S) : Set where
    acc : (∀ {y} → Sub y x → AccS y) → AccS x

  acc-sub : ∀ {x y} → AccS x → Sub y x → AccS y
  acc-sub (acc f) p = f p

  accS : ∀ x → AccS x
  accS hz = acc λ { (sT p q) → go q p }
    where go : ∀ {y b} → Sub b (hz {S}) → Sub y b → AccS y
          go (sT r s) p = go s (sT p r)
  accS (hs x) = acc (go x (accS x))
    where
    go : ∀ x → AccS x → ∀ {y} → Sub y (hs x) → AccS y
    go x a (sS refl) = a
    go x a (sT p q) = acc-sub (go x a q) p
  accS (hl f) = acc (go f (λ n → accS (f n)))
    where
    go : ∀ f → (∀ n → AccS (f n)) → ∀ {y} → Sub y (hl f) → AccS y
    go f a (sL n refl) = a n
    go f a (sT p q) = acc-sub (go f a q) p
  accS (hΩ κ g) = acc (go κ g (λ c → accS (g c)))
    where
    go : ∀ κ g → (∀ c → AccS (g c)) → ∀ {y} → Sub y (hΩ κ g) → AccS y
    go κ g a (sΩ c refl) = a c
    go κ g a (sT p q) = acc-sub (go κ g a q) p

  irr : ∀ {x} → AccS x → ¬ Sub x x
  irr (acc f) p = irr (f p) p

  ⊲→ : ∀ {a b w} → a ⊲[ w ] b → (a ≡ b) ⊎ Sub a b
  ⊲→ hself = inj₁ refl
  ⊲→ (hsuc p) with ⊲→ p
  ... | inj₁ e = inj₂ (sS e)
  ... | inj₂ s = inj₂ (sT s (sS refl))
  ⊲→ (hlim n p) with ⊲→ p
  ... | inj₁ e = inj₂ (sL n e)
  ... | inj₂ s = inj₂ (sT s (sL n refl))
  ⊲→ (hLim {c = c} b p) with ⊲→ p
  ... | inj₁ e = inj₂ (sΩ c e)
  ... | inj₂ s = inj₂ (sT s (sΩ c refl))

  antisym : ∀ {a b w} → a ⊲[ w ] b → b ⊲[ w ] a → a ≡ b
  antisym {a} p q with ⊲→ p | ⊲→ q
  ... | inj₁ e | _ = e
  ... | inj₂ _ | inj₁ e = sym e
  ... | inj₂ s | inj₂ s′ = ⊥-elim (irr (accS a) (sT s s′))
```

## §2 种类结构: 坐标 = 值 + 证据, 序只看值

`Ev c`: 坐标 $c$ 的证据 (戳方案里是 (世界 $V$, 路径)). 新种类的坐标 $\Sigma\,c.\,\mathrm{Ev}\,c$; 界与第一位置只看 $c$. 这是一个种类结构 (`stepE`): `cmpK` 由 `cmpB`.

```agda
module SE (T : KS) (Ev : HB T → Set) (ev₀ : Ev hz) where
  open Step T using (W⁺; _≤⁺_)

  E⁺ : K T ⊎ ⊤ → Set
  E⁺ (inj₁ κ) = E T κ
  E⁺ (inj₂ _) = Σ (HB T) Ev

  Bd⁺ : (κ : K T ⊎ ⊤) → E⁺ κ → W⁺ → Set
  Bd⁺ (inj₁ κ) c w = Bd T κ c (proj₁ w)
  Bd⁺ (inj₂ _) a w = proj₁ a ⊲[ proj₁ w ] proj₂ w

  Pr⁺ : (κ : K T ⊎ ⊤) → W⁺ → E⁺ κ → E⁺ κ → Set
  Pr⁺ (inj₁ κ) w = Pr T κ (proj₁ w)
  Pr⁺ (inj₂ _) w a a′ = proj₁ a ⊲[ proj₁ w ] proj₁ a′

  stepE : KS
  stepE = record
    { K = K T ⊎ ⊤ ; E = E⁺ ; Wd = W⁺ ; LgW = λ w → LgW T (proj₁ w) × LgB (proj₂ w) ; _≤w_ = _≤⁺_
    ; ≤w-tr = λ { (p , b) (q , c) → ≤w-tr T p q , ⊲ᴮ-tr (⊲ᴮ↑ q b) c }
    ; Bd = Bd⁺ ; Pr = Pr⁺
    ; Bd↑ = λ { {inj₁ κ} (q , _) e → Bd↑ T q e ; {inj₂ _} (q , b) e → ⊲ᴮ-tr (⊲ᴮ↑ q e) b }
    ; cmpK = λ { {inj₁ κ} e e′ (lw , lb) → cmpK T e e′ lw ; {inj₂ _} e e′ (lw , lb) → cmpB e e′ lw lb }
    ; bot = λ { (inj₁ κ) → bot T κ ; (inj₂ _) → hz , ev₀ }
    ; botBd = λ { (inj₁ κ) w → botBd T κ (proj₁ w) ; (inj₂ _) w → z⊲ᴮ (proj₂ w) } }
```

**(A) 序只看值: 合法的分支不读证据.** 同一个值 $c$ 的两份证据在界之下时, 互为第一位置 (`hself`), 单调给两个方向, 反对称给相等.

```agda
  κN : K stepE
  κN = inj₂ tt


  branch-indep : ∀ (g : E stepE κN → HB stepE) → LgB {stepE} (hΩ κN g) →
    ∀ {w} → LgW stepE w → ∀ c (a a′ : Ev c) → c ⊲[ proj₁ w ] proj₂ w → g (c , a) ≡ g (c , a′)
  branch-indep g (mo , _) lw c a a′ b = antisym (mo lw b b hself) (mo lw b b hself)
```

**实例.** $T=$ `S⊥`, 证据是一棵可数树 (戳世界 $V$); 分支读 $V$: $g(c, V)=$ `up` 的 $V$ 的像 (任何分开两个戳的读法). 不合法. 合法世界 $(\mathrm{tt}, 1)$ 取在 $0$ 的值上.

```agda
module SE₀ where
  open SE S⊥ (λ _ → Cd) hz

  lf : Cd → HB stepE
  lf hz = hz
  lf (hs c) = hs (lf c)
  lf (hl f) = hl (λ n → lf (f n))
  lf (hΩ () _)

  gV : E stepE κN → HB stepE
  gV (c , V) = lf V

  reads-illegal : ¬ LgB {stepE} (hΩ κN gV)
  reads-illegal l = no (branch-indep gV l {w = tt , hz} (tt , tt) hz hz (hs hz) hself)
    where no : ¬ (hz {stepE} ≡ hs hz)
          no ()
```

**(B) 序也读证据 (积序): `cmpK` 不成立.** 两个坐标 $(c_0, V_1)$, $(c_1, V_0)$, $c_0\lhd c_1$ 而戳反向, 都在同一个合法界之下, 积序下不可比. 

```agda
module SEp where
  -- 积序
  PrP : Cd × Cd → Cd × Cd → Set
  PrP a a′ = (proj₁ a ⊲ proj₁ a′) × (proj₂ a ⊲ proj₂ a′)

  no21 : ¬ (num {S⊥} 2 ⊲ num 1)
  no21 (hsuc ())

  a₀ a₁ : Cd × Cd
  a₀ = num 1 , num 2
  a₁ = num 2 , num 1

  bdp : (num {S⊥} 1 ⊲ num 2) × (num {S⊥} 2 ⊲ num 2)
  bdp = hsuc hself , hself

  no-cmp-product : ¬ (PrP a₁ a₀ ⊎ PrP a₀ a₁)
  no-cmp-product (inj₁ (p , _)) = no21 p
  no-cmp-product (inj₂ (_ , q)) = no21 q
```

**(C) 戳反方向时单调的代价.** 字典序 (值的第一位置严格时不看戳) 能比较, 这时单调要求: 值严格变大时, 分支对**任意两份**证据都上升. 所以读戳的分支在严格的一对上也要跨戳单调: 戳大的小值要不高于戳小的大值. 实例: $g(c,V)=V$ 的读法违反它 ($c=1$ 戳 $2$, $c'=2$ 戳 $1$).

```agda
  gR : Cd × Cd → Cd
  gR a = proj₂ a

  lex-needs : ¬ (∀ a a′ → (proj₁ a ⊲ proj₁ a′) → gR a ⊲ gR a′)
  lex-needs all = no21 (all a₀ a₁ (hsuc hself))
```

## 结论 (按档)

- **[定理]** `antisym`, `⊲→`, `accS`; `SE.stepE`.
- **[定理, 否定]** **`SE.branch-indep`**, **`SE₀.reads-illegal`**, **`SEp.no-cmp-product`**, **`SEp.lex-needs`**.
- **[判断]** 戳方案的其余变体没有测.
