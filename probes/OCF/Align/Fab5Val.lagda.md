# 带类型折叠的值: 对世界与输入联合单调, 塔逐站严格增长 (C 线第一批值定理)

> 不含记号. Fable 5.1, 2026-11-06 (第五轮自选: 摆脱侧). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP. 不改任何已有文件. 只导入 [Fab3Typed](Fab3Typed.lagda.md) (塔与折叠), [Fab5ValRel](Fab5ValRel.lagda.md) (值关系), [HtTowerTy](HtTowerTy.lagda.md), [LFReTy](LFReTy.lagda.md) (`S⊥`), [TLRuleSpec](TLRuleSpec.lagda.md) (第 0 层的标准前序, 只作对照), [CumReadCF](CumReadCF.lagda.md) (`A`).
>
> **我选的这一步, 为什么.** 作者的担心是: 候选树的前 3 层逼近标杆, 再写闭项意义不大, 除非大幅压缩, 或找出树的语言和来自树自身的后路指引. 本轮同时在跑的两路 (`CRw*` 压缩成一个对层号递归的折叠; `X2*` 往 Λ 爬) 覆盖了压缩与攀爬. 我判断还空着、而且最能回答 "闭项写出来有没有意义" 的一侧是**值**: B 线与 C 线合起来没有一条 "回灌提高值" 的定理, 主审把障碍归到 "折叠对层单调" 一条, 而 C 线的折叠是一条定义, 正是在它上面最容易把 "单调" 写成定理. 已有的否定 `NegTySupMono.Φ-not-mono` 说的是**字面第一位置** `⊲` 不被累加的折叠保持; 但 `⊲` 是前缀关系, 不是值关系: "第 $n$ 站的树低于第 $n+1$ 站的树" 在 `⊲` 下根本不成立 (两棵树不互为前缀), 所以值的一侧卡住, 一半原因是用错了关系. 本篇换成值关系 (`Fab5ValRel`, 第 0 层上就是 `TLRuleSpec._≤_`), 对 Fab3Typed 的带类型折叠 `Ψ` 证:
>
> 1. **`Ψ-mono≤` (定理, 对一切种类结构 `T` 与 `CR T`).** 折叠对**世界与输入联合**单调: 输入 $x\le y$, 世界的界 $b\le b'$, 则 $\Psi_{(w,b)}\,x\le\Psi_{(w,b')}\,y$. 前提只有值合法 `Mo` (两个界与两个输入), **不要 `LgB`**, 不要世界合法, 不读字面第一位置. 与 Fab3Typed 的 `Ψ-mono` (`⊲`, 单一世界, 要 `Lg*`) 对照: 这里世界可以不同, 这正是链的相邻点所在的世界.
> 2. **`Mo-Ψ` (定理).** 折叠保值合法: 右输入 `Mo` 且界 `Mo`, 输出 `Mo`. 与 1 互递归 (链点的值合法用 2, 留下的旧种类分支的单调用 1).
> 3. **`infl` (定理).** 嵌入再折回不降值: $x\le\Psi_W(\mathrm{up}\,x)$. 这是 "回灌不降值" 的一步形式.
> 4. **`grow` (定理, 无条件, 对一切 $n$).** 塔逐站严格增长: $\mathrm{T}\Omega_n+1\le\mathrm{T}\Omega_{n+1}$ (第 0 层, 读法 ψ₀(Ω_n) < ψ₀(Ω_{n+1}), 读法是判断); `grow-ω`: 每站低于 ℕ-和 `TΩω`. 经 `≤→≤ᴬ` 落到 `TLRuleSpec._≤_` (`growᴬ`), 即此前值验收用的第 0 层前序.
> 5. **`lgB-not-mo` (否定定理).** 字面合法 (`LgB`) 推不出值合法 (`Mo`): 第 1 层一个 `LgB` 的 $\Omega_1$-结点, 分支把 $\lim(0,1,2,\dots)$ 送到 $\omega$, 把 $\lim(1,2,3,\dots)$ 送到 $\omega+1$. 所以值的定理需要 `Mo` 这条**树侧自己的**合法性判据, 它不是 `LgB` 的推论; 塔的地板 `Ω n` 满足它 (`Mo-Ω`), 折叠保它 (`Mo-Ψ`).
>
> **对纲领与目标.** 纲领 1: 关系 `≤` 就是 "x 的值与对应构造子作用在各部分的值" 的比较, 对一切 `HB S` 一条定义. 纲领 2, 4: 无公理, 不读记号. 目标 "树侧的合法性标准": `Mo` 是第一条**为值而设**的合法性 (`LgB` 为比较而设), 由 `lgB-not-mo` 划出它不是 `LgB` 的推论, 由 `Mo-Ψ` 说明折叠保它. 目标 "闭包定理与阶段无关": `Ψ-mono≤`, `Mo-Ψ`, `infl` 都对一切 `T` 一步, 不按站.
>
> **边界, 如实.** (1) 只对 Fab3Typed 的后继层折叠 (不累加). sup 层的 `TySupFold.Φ` 累加且 "在上" 走两段折叠, 要先证两种折法在 `≤` 下可比 (路线引理); 本篇没有做, 接手清单第 1 条. (2) `grow` 只说明 "不塌缩" (严格增长), 不是 "回灌提高值" 的定量下界; 但它是 C 线第一条值定理, 并且证明的中间结论 `Ω n ≤ chain 0`、`hs (chain 0) ≤ chain 1` 是 "链每一步都把前一步的输出接上去" 的值形式. (3) `≤` 没有 "$\Omega$-极限在左边" 的规则, 坐标限于值合法: 它是值关系的可靠子关系, 不是全部 (判断); 第 0 层上它推出标准前序 (`≤→≤ᴬ`, 定理; 反向是判断, 未写).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Fab5Val where

open import Data.Nat using (ℕ; zero; suc) renaming (_≤_ to _≤ℕ_; z≤n to z≤ℕ; s≤s to s≤sℕ)
open import Data.Nat.Properties using (1+n≰n; m≤n⇒m≤1+n)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
import OCF.Align.TLRuleSpec as TL
open import OCF.Align.Fab3Typed using (module Fold; T; Ω; W; fold; TΩ; Σ⊥; TΩω)
open import OCF.Align.Fab5ValRel
```

## §1 底与塔上的坐标关系

```agda
module CR⊥ where
  ≤ᴱ⊥ : ∀ {κ : K S⊥} → E S⊥ κ → ⊤ → E S⊥ κ → Set
  ≤ᴱ⊥ {()}
  Moᴱ⊥ : ∀ {κ : K S⊥} → ⊤ → E S⊥ κ → Set
  Moᴱ⊥ {()}
  Bdᵛ⊥ : ∀ {κ : K S⊥} → E S⊥ κ → ⊤ → Set
  Bdᵛ⊥ {()}
  bot⊥ : ∀ (κ : K S⊥) w → Moᴱ⊥ {κ} w (bot S⊥ κ)
  bot⊥ ()
  bbot⊥ : ∀ (κ : K S⊥) w → Bdᵛ⊥ {κ} (bot S⊥ κ) w
  bbot⊥ ()

cr⊥ : CR S⊥
cr⊥ = record { _≤ᴱ[_]_ = ≤ᴱ⊥ ; Moᴱ = Moᴱ⊥ ; Bdᵛ = Bdᵛ⊥ ; moᴱ-bot = bot⊥ ; botBdᵛ = bbot⊥ }
  where open CR⊥

crT : ∀ n → CR (T n)
crT zero = cr⊥
crT (suc n) = cr⁺ (crT n)
```

## §2 折叠对世界与输入联合单调, 保值合法

对一切 `T` 与 `CR T`. 记号: `V` 是 `T` 上的关系, `V⁺` 是 `step T` 上的. 陈述里三个界: 输入关系所在世界的界 $b_V$, 左右折叠世界的界 $b\le b'$, 前提 $b_V\le b$: 于是 "$a\le g\,c$, $c$ 在 $b_V$ 之下" 能经 $c\le b_V\le b'$ 与 `Mo` 搬到链的第 0 点 $g\,b'$ 上. 四个 `Mo` 前提 (两个界, 两个输入) 都在链的比较里用到: 逐支假设只在值合法的坐标上成立, 而链的坐标 $b\boxplus d_k$ 要由 `Mo-⊞` 与 `Mo-Ψ` 证明值合法.

```agda
module FoldVal (T : KS) (cr : CR T) where
  open Fold T
  private
    module V = Rel cr
    module V⁺ = Rel (cr⁺ cr)
  open V using (z≤; s≤s; ≤s; l≤; ≤l; ≤Ω; Ω≤Ω)

  one≤Ψ : ∀ {w b} x → hs hz V.≤[ w ] Ψ (w , b) x
  one≤Ψ hz = s≤s z≤
  one≤Ψ (hs x) = ≤l 0 (one≤Ψ x)
  one≤Ψ (hl f) = ≤l 0 (one≤Ψ (f 0))
  one≤Ψ {w} (hΩ (inj₁ κ) g) = ≤Ω (botBdᵛ cr κ w) (moᴱ-bot cr κ w) (one≤Ψ (g (bot T κ)))
  one≤Ψ {w} {b} (hΩ (inj₂ _) g) = ≤l 0 (one≤Ψ (g b))

  mul-mono : ∀ {w a a′} → a V.≤[ w ] a′ → ∀ n → mul a n V.≤[ w ] mul a′ n
  mul-mono p zero = p
  mul-mono p (suc n) = V.⊞-mono (mul-mono p n) p

  Mo-mul : ∀ {w} a → V.Mo w a → ∀ n → V.Mo w (mul a n)
  Mo-mul a m zero = m
  Mo-mul a m (suc n) = V.Mo-⊞ (mul a n) a (Mo-mul a m n) m
```

**主定理.** 对右输入 $y$ 的结构归纳 (左输入 $x$ 在 `l≤` 处变小而 $y$ 不变, 字典序); 推导只用来分情形. 新种类的结点 (`Ω≤Ω` 情形) 比较两条链: 第 $k$ 点互相 `≤`, 由 $k$ 归纳, 用 $g'$ 在值合法坐标上的单调 (`Mo` 的第一分量) 把 $g\,(b\boxplus d_k)\le g'\,(b\boxplus d_k)\le g'\,(b'\boxplus e_k)$ 接起来; 链点的值合法由 `Mo-Ψ` 给出.

```agda
  Ψ-mono≤ : ∀ {w bV b b′} → bV V.≤[ w ] b → b V.≤[ w ] b′ → V.Mo w b → V.Mo w b′ →
            ∀ {x} y → V⁺.Mo (w , bV) x → V⁺.Mo (w , bV) y → x V⁺.≤[ (w , bV) ] y →
            Ψ (w , b) x V.≤[ w ] Ψ (w , b′) y
  Mo-Ψ : ∀ {w bV b} → bV V.≤[ w ] b → V.Mo w b → ∀ x → V⁺.Mo (w , bV) x → V.Mo w (Ψ (w , b) x)

  Ψ-mono≤ vb bb mb mb′ y mx my V⁺.z≤ = one≤Ψ y
  Ψ-mono≤ vb bb mb mb′ (hs y) mx my (V⁺.s≤s p) =
    l≤ (λ n → ≤l n (mul-mono (Ψ-mono≤ vb bb mb mb′ y mx my p) n))
  Ψ-mono≤ vb bb mb mb′ (hs y) mx my (V⁺.≤s p) = ≤l 0 (Ψ-mono≤ vb bb mb mb′ y mx my p)
  Ψ-mono≤ vb bb mb mb′ y mx my (V⁺.l≤ h) = l≤ (λ n → Ψ-mono≤ vb bb mb mb′ y (mx n) my (h n))
  Ψ-mono≤ vb bb mb mb′ (hl f) mx my (V⁺.≤l n p) = ≤l n (Ψ-mono≤ vb bb mb mb′ (f n) mx (my n) p)
  Ψ-mono≤ vb bb mb mb′ (hΩ (inj₁ κ) g) mx (mo , mh) (V⁺.≤Ω e m p) =
    ≤Ω e m (Ψ-mono≤ vb bb mb mb′ (g _) mx (mh _ m) p)
  Ψ-mono≤ {w} {bV} {b} {b′} vb bb mb mb′ (hΩ (inj₂ _) g) mx (mo , mh) (V⁺.≤Ω {c = c} e m p) =
    ≤l 0 (Ψ-mono≤ vb bb mb mb′ (g b′) mx (mh b′ mb′)
           (V⁺.≤-trans p (mo c b′ m mb′ (V.≤-trans e (V.≤-trans vb bb)))))
  Ψ-mono≤ vb bb mb mb′ (hΩ (inj₁ κ) g′) (moˡ , mhˡ) (mo , mh) (V⁺.Ω≤Ω H) =
    Ω≤Ω (λ c mc → Ψ-mono≤ vb bb mb mb′ (g′ c) (mhˡ c mc) (mh c mc) (H c mc))
  Ψ-mono≤ {w} {bV} {b} {b′} vb bb mb mb′ (hΩ (inj₂ _) g′) (moˡ , mhˡ) (mo , mh) (V⁺.Ω≤Ω {g = g} H) =
    l≤ (λ k → ≤l k (ch k))
    where
    kL kR : Wd (step T) → HB T → HB T
    kL W′ c = Ψ W′ (g c)
    kR W′ c = Ψ W′ (g′ c)
    chMˡ : ∀ k → V.Mo w (chain w b kL k)
    chM : ∀ k → V.Mo w (chain w b′ kR k)
    ch : ∀ k → chain w b kL k V.≤[ w ] chain w b′ kR k
    chMˡ zero = Mo-Ψ vb mb (g b) (mhˡ b mb)
    chMˡ (suc k) = V.Mo-⊞ _ _ (chMˡ k)
      (Mo-Ψ (V.≤-trans vb (V.≤⊞ b _)) (V.Mo-⊞ b _ mb (chMˡ k)) (g _) (mhˡ _ (V.Mo-⊞ b _ mb (chMˡ k))))
    chM zero = Mo-Ψ (V.≤-trans vb bb) mb′ (g′ b′) (mh b′ mb′)
    chM (suc k) = V.Mo-⊞ _ _ (chM k)
      (Mo-Ψ (V.≤-trans (V.≤-trans vb bb) (V.≤⊞ b′ _)) (V.Mo-⊞ b′ _ mb′ (chM k)) (g′ _) (mh _ (V.Mo-⊞ b′ _ mb′ (chM k))))
    ch zero = Ψ-mono≤ vb bb mb mb′ (g′ b′) (mhˡ b mb) (mh b′ mb′)
      (V⁺.≤-trans (H b mb) (mo b b′ mb mb′ bb))
    ch (suc k) = V.⊞-mono (ch k)
      (Ψ-mono≤ (V.≤-trans vb (V.≤⊞ b _)) (V.⊞-mono bb (ch k))
         (V.Mo-⊞ b _ mb (chMˡ k)) (V.Mo-⊞ b′ _ mb′ (chM k))
         (g′ _) (mhˡ _ (V.Mo-⊞ b _ mb (chMˡ k))) (mh _ (V.Mo-⊞ b′ _ mb′ (chM k)))
         (V⁺.≤-trans (H _ (V.Mo-⊞ b _ mb (chMˡ k)))
            (mo _ _ (V.Mo-⊞ b _ mb (chMˡ k)) (V.Mo-⊞ b′ _ mb′ (chM k)) (V.⊞-mono bb (ch k)))))

  Mo-Ψ vb mb hz mx = tt
  Mo-Ψ vb mb (hs x) mx = Mo-mul _ (Mo-Ψ vb mb x mx)
  Mo-Ψ vb mb (hl f) mx = λ n → Mo-Ψ vb mb (f n) (mx n)
  Mo-Ψ vb mb (hΩ (inj₁ κ) g) (mo , mh) =
    (λ c c′ mc mc′ p → Ψ-mono≤ vb (V.≤-refl _) mb mb (g c′) (mh c mc) (mh c′ mc′) (mo c c′ mc mc′ p)) ,
    (λ c mc → Mo-Ψ vb mb (g c) (mh c mc))
  Mo-Ψ {w} {bV} {b} vb mb (hΩ (inj₂ _) g) (mo , mh) = chM
    where
    k : Wd (step T) → HB T → HB T
    k W′ c = Ψ W′ (g c)
    chM : ∀ n → V.Mo w (chain w b k n)
    chM zero = Mo-Ψ vb mb (g b) (mh b mb)
    chM (suc n) = V.Mo-⊞ _ _ (chM n)
      (Mo-Ψ (V.≤-trans vb (V.≤⊞ b _)) (V.Mo-⊞ b _ mb (chM n)) (g _) (mh _ (V.Mo-⊞ b _ mb (chM n))))
```

**嵌入再折回不降值.** `up x` 只有旧种类, 折叠全部保留; $0\mapsto1$, 后继 $\mapsto\cdot\omega$, 都不降.

```agda
  infl : ∀ {w β} x → x V.≤[ w ] Ψ (w , β) (up x)
  infl hz = z≤
  infl {w} {β} (hs x) = ≤l 1 (V.≤-trans (s≤s (infl x)) (V.⊞-monoʳ (Ψ (w , β) (up x)) (one≤Ψ (up x))))
  infl (hl f) = l≤ (λ n → ≤l n (infl (f n)))
  infl (hΩ κ g) = Ω≤Ω (λ c _ → infl (g c))
```

## §3 塔: 地板值合法, 折到底单调, 逐站严格增长

```agda
module _ where
  private
    module R n = Rel (crT n)

  LE : ∀ n → HB (T n) → HB (T n) → Set
  LE n x y = Rel._≤[_]_ (crT n) x (W n) y

  Mo-Ω : ∀ n → R.Mo n (W n) (Ω n)
  Mo-Ω zero = tt
  Mo-Ω (suc n) = (λ c c′ mc mc′ p → up-mono≤ (crT n) p) , (λ c mc → Mo-up (crT n) c mc)

  fold-mono : ∀ n {x y} → R.Mo n (W n) x → R.Mo n (W n) y → LE n x y → LE 0 (fold n x) (fold n y)
  fold-mono zero mx my p = p
  fold-mono (suc n) {x} {y} mx my p =
    fold-mono n (FoldVal.Mo-Ψ (T n) (crT n) (R.≤-refl n _) (Mo-Ω n) x mx)
      (FoldVal.Mo-Ψ (T n) (crT n) (R.≤-refl n _) (Mo-Ω n) y my)
      (FoldVal.Ψ-mono≤ (T n) (crT n) (R.≤-refl n _) (R.≤-refl n _) (Mo-Ω n) (Mo-Ω n) y mx my p)

  fold-suc : ∀ n x → R.Mo n (W n) x → LE 0 (hs (fold n x)) (fold n (hs x))
  fold-suc zero x mx = R.≤-refl 0 _
  fold-suc (suc n) x mx =
    R.≤-trans 0 (fold-suc n (Ψ x) mΨ)
      (fold-mono n mΨ (FoldVal.Mo-mul (T n) (crT n) (Ψ x) mΨ)
        (R.≤l 1 (R.≤-trans n (R.s≤s (R.≤-refl n _)) (R.⊞-monoʳ n (Ψ x) (FoldVal.one≤Ψ (T n) (crT n) x)))))
    where
    Ψ = Fold.Ψ (T n) (W (suc n))
    mΨ = FoldVal.Mo-Ψ (T n) (crT n) (R.≤-refl n _) (Mo-Ω n) x mx
```

**逐站严格增长.** $n=0$: $\mathrm{T}\Omega_0=0$, $1\le\mathrm{T}\Omega_1$ 由 `one≤Ψ`. $n+1$: 第 $n+2$ 层的顶坍缩成链, 链的第 0 点是 $\Omega_{n+1}$-结点 (分支 $c\mapsto\Psi(\mathrm{up}(\mathrm{up}\,c))$, 由 `infl` 逐支不低于 `up c`), 所以 $\Omega_{n+1}\le d_0$; 第 1 点 $d_1=d_0\boxplus\Psi(\cdots)\ge d_0+1$. 于是 $\Omega_{n+1}+1\le\lim d$, 再用 `fold-suc` 与 `fold-mono` 折到底.

```agda
  grow : ∀ n → LE 0 (hs (TΩ n)) (TΩ (suc n))
  grow zero = FoldVal.one≤Ψ S⊥ cr⊥ (Ω 1)
  grow (suc n) =
    R.≤-trans 0 (fold-suc (suc n) (Ω (suc n)) (Mo-Ω (suc n)))
      (fold-mono (suc n) (Mo-Ω (suc n)) my₁ step₁)
    where
    n′ = suc n
    Ψ₂ = Fold.Ψ (T n′) (W (suc n′))
    -- 第 n+2 层的顶折到第 n+1 层: 链
    y₁ : HB (T n′)
    y₁ = Ψ₂ (Ω (suc n′))
    my₁ : R.Mo n′ (W n′) y₁
    my₁ = FoldVal.Mo-Ψ (T n′) (crT n′) (R.≤-refl n′ _) (Mo-Ω n′) (Ω (suc n′)) (Mo-Ω (suc n′))
    d₀ : HB (T n′)
    d₀ = Ψ₂ (up (Ω n′))
    Ω≤d₀ : LE n′ (Ω n′) d₀
    Ω≤d₀ = R.Ω≤Ω (λ c _ → FoldVal.infl (T n′) (crT n′) (up c))
    step₁ : LE n′ (hs (Ω n′)) y₁
    step₁ = R.≤l 1 (R.≤-trans n′ (R.s≤s Ω≤d₀)
              (R.⊞-monoʳ n′ d₀ (FoldVal.one≤Ψ (T n′) (crT n′) (up (Ω n′ ⊞ d₀)))))

  grow-ω : ∀ n → LE 0 (TΩ n) TΩω
  grow-ω n = R.≤l n (le n)
    where
    le : ∀ n → LE 0 (TΩ n) (Σ⊥ TΩ n)
    le zero = R.≤-refl 0 _
    le (suc n) = R.≤⊞ˡ 0 _ (TΩ (suc n))
```

## §4 第 0 层: 与标准前序相同

```agda
toA : HB S⊥ → A
toA hz = azero
toA (hs h) = asuc (toA h)
toA (hl f) = alim (λ n → toA (f n))
toA (hΩ () _)

private
  module R₀ = Rel cr⊥

≤→≤ᴬ : ∀ {a b} → a R₀.≤[ tt ] b → toA a TL.≤ toA b
≤→≤ᴬ R₀.z≤ = TL.z≤
≤→≤ᴬ (R₀.s≤s p) = TL.s≤ (≤→≤ᴬ p)
≤→≤ᴬ (R₀.≤s p) = TL.≤-suc (≤→≤ᴬ p)
≤→≤ᴬ (R₀.l≤ h) = TL.l≤ (λ n → ≤→≤ᴬ (h n))
≤→≤ᴬ (R₀.≤l n p) = TL.≤l n (≤→≤ᴬ p)
≤→≤ᴬ (R₀.≤Ω {κ = ()} _ _ _)
≤→≤ᴬ (R₀.Ω≤Ω {κ = ()} _)

growᴬ : ∀ n → asuc (toA (TΩ n)) TL.≤ toA (TΩ (suc n))
growᴬ n = ≤→≤ᴬ (grow n)
```

## §5 否定: 字面合法推不出值合法

第 1 层 (`T 1 = step S⊥`) 的 $\Omega_1$-结点 `N`, 分支 $c\mapsto\mathrm{up}\,(g\,c)$, 其中 $g$ 在 ℕ-极限处把第 0 项接在后面: $g(\lim f)=\lim(g\circ f)\boxplus f_0$. $g$ 保字面第一位置 (`g-⊲`), 保 `LgB` (`Lg-g`), 所以 `N` 满足 `LgB`. 但 $g(\lim(0,1,2,\dots))=\omega$, $g(\lim(1,2,3,\dots))=\omega+1$, 而 $\lim(1,2,3,\dots)\le\lim(0,1,2,\dots)$: 分支不保 `≤`, `N` 不满足 `Mo`.

```agda
module Neg where
  g : HB S⊥ → HB S⊥
  g hz = hz
  g (hs x) = hs (g x)
  g (hl f) = hl (λ n → g (f n)) ⊞ f 0
  g (hΩ () _)

  g-⊲ : ∀ {w a b} → a ⊲[ w ] b → g a ⊲[ w ] g b
  g-⊲ hself = hself
  g-⊲ (hsuc p) = hsuc (g-⊲ p)
  g-⊲ (hlim {f = f} n p) = ⊲ᴮ-tr (hlim n (g-⊲ p)) (⊞-fst (hl (λ m → g (f m))) (f 0))
  g-⊲ (hLim {κ = ()} _ _)

  Lg-g : ∀ c → LgB c → LgB (g c)
  Lg-g hz l = tt
  Lg-g (hs c) l = Lg-g c l
  Lg-g (hl f) (st , l) = Lg-⊞ (hl (λ n → g (f n))) (f 0) ((λ n → g-⊲ (st n)) , (λ n → Lg-g (f n) (l n))) (l 0)
  Lg-g (hΩ () _) l

  N : HB (T 1)
  N = hΩ (inj₂ tt) (λ c → up (g c))

  LgB-N : LgB N
  LgB-N = (λ lw e e′ p → up-⊲ (g-⊲ p)) , (λ c lc → Lg-up (g c) (Lg-g c lc))
```

值的一侧: 第 0 层的树都值合法 (没有结点); $\lim(1,2,\dots)\le\lim(0,1,\dots)$; 而 $\omega+1\not\le\omega$ (对任一只含 $0$, 后继的 `nat`: `hs (hl F) ≤ nat n` 不可能, 当 $F_m=\mathrm{nat}(m+1)$).

```agda
  private
    module R₁ = Rel (crT 1)

  Mo⊥ : ∀ c → R₀.Mo tt c
  Mo⊥ hz = tt
  Mo⊥ (hs c) = Mo⊥ c
  Mo⊥ (hl f) = λ n → Mo⊥ (f n)
  Mo⊥ (hΩ () _)

  nat : ℕ → HB S⊥
  nat zero = hz
  nat (suc n) = hs (nat n)

  nat₁ : ℕ → HB (T 1)
  nat₁ zero = hz
  nat₁ (suc n) = hs (nat₁ n)

  g-nat : ∀ n → g (nat n) ≡ nat n
  g-nat zero = refl
  g-nat (suc n) = cong hs (g-nat n)

  up-nat : ∀ n → up (nat n) ≡ nat₁ n
  up-nat zero = refl
  up-nat (suc n) = cong hs (up-nat n)

  ω̂ ω̂′ : HB S⊥
  ω̂ = hl nat
  ω̂′ = hl (λ n → nat (suc n))

  ω̂′≤ω̂ : ω̂′ R₀.≤[ tt ] ω̂
  ω̂′≤ω̂ = R₀.l≤ (λ n → R₀.≤l (suc n) (R₀.≤-refl _))

  nat≤ : ∀ {w a b} → nat₁ a R₁.≤[ w ] nat₁ b → a ≤ℕ b
  nat≤ {a = zero} p = z≤ℕ
  nat≤ {a = suc a} {suc b} (R₁.s≤s p) = s≤sℕ (nat≤ p)
  nat≤ {a = suc a} {suc b} (R₁.≤s p) = m≤n⇒m≤1+n (nat≤ p)

  ¬hlF≤nat : ∀ {w} (F : ℕ → HB (T 1)) → (∀ m → F m ≡ nat₁ (suc m)) → ∀ n → ¬ (hl F R₁.≤[ w ] nat₁ n)
  ¬hlF≤nat F eF zero (R₁.l≤ h) = 1+n≰n (nat≤ (subst (λ z → z R₁.≤[ _ ] nat₁ 0) (eF 0) (h 0)))
  ¬hlF≤nat F eF (suc n) (R₁.l≤ h) =
    1+n≰n (nat≤ (subst (λ z → z R₁.≤[ _ ] nat₁ (suc n)) (eF (suc n)) (h (suc n))))
  ¬hlF≤nat F eF (suc n) (R₁.≤s p) = ¬hlF≤nat F eF n p

  ¬hsF≤nat : ∀ {w} (F : ℕ → HB (T 1)) → (∀ m → F m ≡ nat₁ (suc m)) → ∀ n → ¬ (hs (hl F) R₁.≤[ w ] nat₁ n)
  ¬hsF≤nat F eF zero ()
  ¬hsF≤nat F eF (suc n) (R₁.s≤s q) = ¬hlF≤nat F eF n q
  ¬hsF≤nat F eF (suc n) (R₁.≤s p) = ¬hsF≤nat F eF n p

  -- 分支在 ω̂′ 与 ω̂ 处的值: up (g ω̂′) = hs (hl F), up (g ω̂) = hl G, 字面
  F G : ℕ → HB (T 1)
  F m = up (g (nat (suc m)))
  G n = up (g (nat n))

  eF : ∀ m → F m ≡ nat₁ (suc m)
  eF m = cong hs (subst (λ z → up z ≡ nat₁ m) (sym′ (g-nat m)) (up-nat m))
    where
    sym′ : ∀ {x y : HB S⊥} → x ≡ y → y ≡ x
    sym′ refl = refl

  eG : ∀ n → G n ≡ nat₁ n
  eG n = subst (λ z → up z ≡ nat₁ n) (sym′ (g-nat n)) (up-nat n)
    where
    sym′ : ∀ {x y : HB S⊥} → x ≡ y → y ≡ x
    sym′ refl = refl

  ¬branch : ¬ (up (g ω̂′) R₁.≤[ (tt , hz) ] up (g ω̂))
  ¬branch (R₁.≤l n p) = ¬hsF≤nat F eF n (subst (λ z → hs (hl F) R₁.≤[ (tt , hz) ] z) (eG n) p)

  ¬Mo-N : ¬ R₁.Mo (W 1) N
  ¬Mo-N (mo , _) = ¬branch (mo ω̂′ ω̂ (Mo⊥ ω̂′) (Mo⊥ ω̂) ω̂′≤ω̂)

lgB-not-mo : Σ (HB (T 1)) (λ N → LgB N × ¬ Rel.Mo (crT 1) (W 1) N)
lgB-not-mo = Neg.N , Neg.LgB-N , Neg.¬Mo-N
```

## 结论 (按档)

- **[定理]** `cr⊥`, `crT`; `FoldVal.one≤Ψ`, `FoldVal.Ψ-mono≤` (折叠对世界与输入联合单调, 前提只有值合法), `FoldVal.Mo-Ψ` (折叠保值合法), `FoldVal.infl` (嵌入再折回不降值), 都对一切 `T`, `CR T`; 塔: `Mo-Ω`, `fold-mono`, `fold-suc`, **`grow`** (逐站严格增长, 无条件), `grow-ω`; 第 0 层 `≤→≤ᴬ`, `growᴬ`; 否定 **`lgB-not-mo`**.
- **[判断]** 读法 (`TΩ n` 读 ψ₀(Ω_n)) 沿用 Fab3Typed; `≤` 是值关系的可靠子关系 (没有 "Ω-极限在左边"); sup 层 (`TySupFold.Φ`, 累加) 上同样的定理要先有两种折法的路线引理, 未做.
