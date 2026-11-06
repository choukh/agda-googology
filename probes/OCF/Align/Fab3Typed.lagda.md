# 带类型的一层折叠: 回灌是恒等, 单调与合法是一步定理

> 不含记号. Fable 5.1, 2026-11-05 (第三轮自选: 压缩与自足). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提. 闭项, 证书, FGH 无模块参数. 不改任何已有文件. 只导入 [HtTowerTy](HtTowerTy.lagda.md), [LFReTy](LFReTy.lagda.md) (只用 `S⊥`) 与 `OCF.Free.Level` (只用 `FGH`).
>
> **这一篇做什么.** 作者的担心: 候选树的前 3 层已接近标杆, 不大幅压缩或找出树自己的语言, 闭项写出来意义不大. 本篇问一个具体的问题: **折叠的输出为什么不是下一层的高度本身?** 主线的一般折叠 ([GenFoldRun](GenFoldRun.lagda.md)) 把输出放进无类型的数据树 `D`, 再经读回 `rd₁` 读成坐标; 数据树、状态、目标、读回加起来约 500 行, 而且读回只产生底种类的结点 (`NewTwrObs.onlyA-rd₁`), 这是 C6 的根. 本篇把一层的折叠写成**带类型的** `Ψ : Wd (step T) → HB (step T) → HB T`, 对一切种类结构 `T` 一条定义 (§2, 7 行加一个链): 新种类的 $\Omega$-结点坍缩成回灌链的 ℕ-极限, 链的起点是世界里这个种类的界, 下一点是 "界 $\boxplus$ 到此为止的输出"; 旧种类的结点原样保留, 分支递归. 因为输出的类型就是新种类的坐标类型 `HB T`, **回灌不需要读回: 链点就是输出** (`feed-id`, `refl`). 链的起点是下一层的顶 $\Omega_n$, 所以回灌进坐标的值字面含低层种类的 $\Omega$-结点 (`feed-Ω`, `refl`), 与 `onlyA-rd₁` 相反.
>
> **定理 (一步, 对一切 `T`).** `Ψ-mono`: 在合法世界里保第一位置 ($a \lhd b \Rightarrow \Psi a \lhd \Psi b$); `Ψ-lg`: 保合法. 两条都对 `T` 一般, 不按层, 不按站, 没有逐站的闭包定理. 这正是目标里 "闭包定理与阶段无关" 的形状. 用它们沿后继层的塔 `T n = stepⁿ S⊥` 折到底 (§3), 得到每个 $n$ 的无条件闭项 `TΩ n` (读法 ψ₀(Ω_n), 判断) 与一个 ℕ-和 `TΩω` (读法 ψ₀(Ω_ω), 判断), 带证书与 FGH. 行数见文末: 前 3 层 (定义 + 折叠 + 证书) 的定义级切片约 300 行, 其中本文件约 150 行, 其余是 `HtTowerTy` 的类型与 `⊞`/`up` (口径同 `FabLFReGen` 的 1042, 见 `Survey/scripts/fab3/`).
>
> **代价, 如实.** (1) **合法性换了量词.** `HtTowerTy.LgB` 要求 ℕ-极限在**一切**世界里步进, 而 $\Omega$-分支只在合法坐标上合法; 带类型的折叠在不合法的世界里无法把合法性沿 `⊲` 传下去 (`lgB⊲` 要 `LgW`), 所以 `Ψ-mono` 用 `LgB` 陈述时证不出 (这是本篇的判断, "未走通", 不是否定). 本篇用 `Lg*`: 与 `LgB` 逐构造子相同, 只把 ℕ-极限的步进改成 "在一切**合法**世界里" (§1), 世界合法按 `Lg*` 自己算 (`LS`, 3 个字段, `step*` 一次给出; `step` 的字段 `LgE⁺`, `LgW⁺` 写死了 `LgB`, 用不上). 两者的关系, 如实: 一般的 `T` 上 `Lg*` 与 `LgB` **不可互推** (判断): ℕ-极限处 `Lg*` 弱, $\Omega$-结点处 `Lg*` 要求单调的世界类更大 (`Lg*`-合法的界比 `LgB`-合法的多). 形状给出的单调 (`up-⊲`, `⊞-⊲`) 对一切世界成立, 所以本篇的输入高度两者都满足 (`LgB-Ω`); 比较 `cmpB` 只在合法世界里用步进 (它带 `LgW`), 不受影响. 到底层 `S⊥` 时世界只有一个, `Lg*` 就是 `LgB` (`lgB⊥`), 所以闭项的证书是标准的 `LgB`. (2) **只到后继层.** `Ψ` 对一切 `T` 一条定义, 包括 `sup`; 但从 `sup ℕ T` 的高度 (种类带层号 $(n,\kappa)$) 折到底要按目标层决定 "留" 还是 "坍缩", 下标是 ℕ 时可判定 (同 `Fab2SLs` 的站号), 下标是高度时就是 `rkT`/`cmpB` 要带的公共上界. 本篇没有写 `sup` 层的折叠; 这是接手清单第 1 条. (3) 读法是判断, 没有 `ord` 定理. (4) $\psi(a+1)=\psi(a)\cdot\omega$ 与 $\psi(0)=1$ 是约定 (同 `TLRuleSum`).
>
> **对纲领与目标.** 纲领 1: 闭项是 `HB S⊥` (就是 `A` 的形状) 的元素, FGH 在树上算; 塔的每层是布劳威尔树 `HB (T n)`. 纲领 2: 无公理, 检查器接受, 链是 ℕ 上的普通递归. 纲领 3: 折叠里没有比较, 没有判等; 世界的界只被读出与 $\boxplus$. 纲领 4: 不读记号. 目标: 折叠的定义与两条定理都对一切 `T` 一步写出, 没有看记号; 它们说的是折叠**自己的**性质 (保第一位置, 保合法), 不是对照记号的验收. "回灌是恒等" 是树侧对 C6 的一句话: **当输出的类型就是坐标的类型时, 按级回灌不需要任何升界算子.** 这一句在后继层是定理 (`feed-id`); 在 `sup` 层要先解决 "留还是坍缩", 那里才是 C6 真正的位置 (判断).
>
> **翻译账.** 没有新结点, 没有新接口字段来自记号. `Lg*` 的形状来自树侧的要求 (`Ψ-mono` 的归纳只在合法世界里能传合法). 摆脱侧: 去掉数据树 `D`, 状态 `St`/`Df`/`Ig`/`Tg`, 读回 `rd₁`, 下降, 塔的拷贝与嵌入. 攀爬侧: 强度低于 `TΛ` 等候选 (后者的树形到 Λ, 读法同样是判断).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Fab3Typed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥)
import OCF.Free.Level as FLv
```

## §1 合法性: ℕ-极限只在合法世界里步进

`LS S`: 种类结构 `S` 上的合法性结构, 三个字段: 世界合法 `LgW*`, 坐标合法 `LgE*`, 界之下的坐标合法 `lgBd*`. `Lg*`: 与 `HtTowerTy.LgB` 逐构造子相同, 只有 `hl` 一行多一个 `LgW* w →`. `lg*⊲`, `Lg*-⊞`, `Lg*-up` 与 `lgB⊲`, `Lg-⊞`, `Lg-up` 逐行相同.

```agda
record LS (S : KS) : Set₁ where
  field
    LgW*  : Wd S → Set
    LgE*  : (κ : K S) → E S κ → Set
    lgBd* : ∀ {κ c w} → Bd S κ c w → LgW* w → LgE* κ c
open LS public

module _ {S : KS} (ℓ : LS S) where
  Lg* : HB S → Set
  Lg* hz = ⊤
  Lg* (hs h) = Lg* h
  Lg* (hl f) = (∀ {w} → LgW* ℓ w → ∀ n → f n ⊲[ w ] f (suc n)) × (∀ n → Lg* (f n))
  Lg* (hΩ κ g) =
    (∀ {w c c′} → LgW* ℓ w → Bd S κ c w → Bd S κ c′ w → Pr S κ w c c′ → g c ⊲[ w ] g c′) ×
    (∀ c → LgE* ℓ κ c → Lg* (g c))

  lg*⊲ : ∀ {a b w} → a ⊲[ w ] b → LgW* ℓ w → Lg* b → Lg* a
  lg*⊲ hself lw l = l
  lg*⊲ (hsuc p) lw l = lg*⊲ p lw l
  lg*⊲ (hlim n p) lw l = lg*⊲ p lw (proj₂ l n)
  lg*⊲ (hLim e p) lw l = lg*⊲ p lw (proj₂ l _ (lgBd* ℓ e lw))

  Lg*-⊞ : ∀ a b → Lg* a → Lg* b → Lg* (a ⊞ b)
  Lg*-⊞ a hz la lb = la
  Lg*-⊞ a (hs b) la lb = Lg*-⊞ a b la lb
  Lg*-⊞ a (hl f) la (st , l) = (λ lw n → ⊞-⊲ a (st lw n)) , (λ n → Lg*-⊞ a (f n) la (l n))
  Lg*-⊞ a (hΩ κ g) la (mo , l) = (λ lw e e′ p → ⊞-⊲ a (mo lw e e′ p)) , (λ c lc → Lg*-⊞ a (g c) la (l c lc))
```

底 `S⊥` 没有种类, 世界只有 `tt`. `step*`: 新种类的坐标合法是 `Lg*`, 新世界合法是旧世界合法加界合法, 与 `HtTowerTy.Step` 的 `LgE⁺`, `LgW⁺`, `lgBd⁺` 同形.

```agda
ls⊥ : LS S⊥
ls⊥ = record { LgW* = λ _ → ⊤ ; LgE* = LgE⊥ ; lgBd* = λ {κ} {c} {w} → lgBd⊥ {κ} {c} {w} }
  where
  LgE⊥ : (κ : K S⊥) → E S⊥ κ → Set
  LgE⊥ ()
  lgBd⊥ : ∀ {κ c w} → Bd S⊥ κ c w → ⊤ → LgE⊥ κ c
  lgBd⊥ {()}

module Step* {T : KS} (ℓ : LS T) where
  LgW⁺* : Wd (step T) → Set
  LgW⁺* w = LgW* ℓ (proj₁ w) × Lg* ℓ (proj₂ w)

  LgE⁺* : (κ : K (step T)) → E (step T) κ → Set
  LgE⁺* (inj₁ κ) = LgE* ℓ κ
  LgE⁺* (inj₂ _) = Lg* ℓ

  lgBd⁺* : ∀ {κ c w} → Bd (step T) κ c w → LgW⁺* w → LgE⁺* κ c
  lgBd⁺* {inj₁ κ} e (lw , lb) = lgBd* ℓ e lw
  lgBd⁺* {inj₂ _} e (lw , lb) = lg*⊲ ℓ e lw lb

step* : ∀ {T} → LS T → LS (step T)
step* ℓ = record { LgW* = LgW⁺* ; LgE* = LgE⁺* ; lgBd* = λ {κ} {c} {w} → lgBd⁺* {κ} {c} {w} }
  where open Step* ℓ

module _ {T : KS} (ℓ : LS T) where
  Lg*-up : ∀ a → Lg* ℓ a → Lg* (step* ℓ) (up a)
  Lg*-up hz l = tt
  Lg*-up (hs a) l = Lg*-up a l
  Lg*-up (hl f) (st , l) = (λ lw n → up-⊲ (st (proj₁ lw) n)) , (λ n → Lg*-up (f n) (l n))
  Lg*-up (hΩ κ g) (mo , l) = (λ lw e e′ p → up-⊲ (mo (proj₁ lw) e e′ p)) , (λ c lc → Lg*-up (g c) (l c lc))
```

## §2 一层的折叠, 对一切种类结构

`Ψ W h`: 把 `step T` 的高度 $h$ 在世界 $W=(w,b)$ 里折成 `T` 的高度. $0\mapsto1$, 后继 $\mapsto\cdot\omega$ (`mul`), ℕ-极限逐项, 旧种类的结点保留, 新种类的结点坍缩成链 `chain` 的 ℕ-极限: 链点 $d_0=\Psi_{(w,b)}(g\,b)$, $d_{n+1}=d_n\boxplus\Psi_{(w,\,b\boxplus d_n)}(g\,(b\boxplus d_n))$. 链用延续 $k$ 写 (`k W′ c = Ψ W′ (g c)`), 所以 `Ψ` 的递归在检查器眼里是结构的 (`g c` 是 `hΩ κ g` 的子项), 不要停机指示.

```agda
module Fold (T : KS) where
  L : KS
  L = step T

  mul : HB T → ℕ → HB T
  mul x zero = x
  mul x (suc n) = mul x n ⊞ x

  chain : (w : Wd T) (b : HB T) → (Wd L → HB T → HB T) → ℕ → HB T
  chain w b k zero = k (w , b) b
  chain w b k (suc n) = chain w b k n ⊞ k (w , b ⊞ chain w b k n) (b ⊞ chain w b k n)

  Ψ : Wd L → HB L → HB T
  Ψ W hz = hs hz
  Ψ W (hs h) = hl (mul (Ψ W h))
  Ψ W (hl f) = hl (λ n → Ψ W (f n))
  Ψ W (hΩ (inj₁ κ) g) = hΩ κ (λ c → Ψ W (g c))
  Ψ W (hΩ (inj₂ _) g) = hl (chain (proj₁ W) (proj₂ W) (λ W′ c → Ψ W′ (g c)))
```

**回灌是恒等 (定理, `refl`).** 链的第 0 点就是在当前世界里对界 $b$ 的分支折出的输出, 不经任何读回; 第 $n+1$ 点把输出接在界后面作下一个坐标, 坐标类型与输出类型字面相同.

```agda
  feed-id : ∀ w b k → chain w b k zero ≡ k (w , b) b
  feed-id w b k = refl

  feed-suc : ∀ w b k n → chain w b k (suc n) ≡ chain w b k n ⊞ k (w , b ⊞ chain w b k n) (b ⊞ chain w b k n)
  feed-suc w b k n = refl
```

**单调与合法: 一步定理.** `Ψ-mono`: 在合法世界 $(v,b)$ 里 $a\lhd b'$ 推出 $\Psi\,a\lhd\Psi\,b'$ (世界 $v$). 对 $b'$ 结构归纳; 新种类的 $\Omega$-结点处用输入的单调 (`mo`) 把坐标 $c\lhd b$ 搬到 $g\,c\lhd g\,b$, 再用链的第 0 点. `Ψ-lg`: 保 `Lg*`; 链的每一点合法由 `Lg*-⊞` 与 `Ψ-lg` 自己给出 (ℕ 上归纳).

```agda
  module Thm (ℓ : LS T) where
    ℓ⁺ : LS L
    ℓ⁺ = step* ℓ

    mul-fst : ∀ {w} x n → mul x n ⊲[ w ] mul x (suc n)
    mul-fst x n = ⊞-fst (mul x n) x

    Lg*-mul : ∀ x → Lg* ℓ x → ∀ n → Lg* ℓ (mul x n)
    Lg*-mul x l zero = l
    Lg*-mul x l (suc n) = Lg*-⊞ ℓ (mul x n) x (Lg*-mul x l n) l

    Ψ-mono : ∀ {W v a b} → LgW* ℓ v → Lg* ℓ (proj₂ W) → Lg* ℓ⁺ b →
             a ⊲[ (v , proj₂ W) ] b → Ψ W a ⊲[ v ] Ψ W b
    Ψ-mono lv lb l hself = hself
    Ψ-mono lv lb l (hsuc p) = ⊲ᴮ-tr (Ψ-mono lv lb l p) (hlim 0 hself)
    Ψ-mono lv lb (st , l) (hlim n p) = hlim n (Ψ-mono lv lb (l n) p)
    Ψ-mono lv lb (mo , l) (hLim {κ = inj₁ κ} e p) = hLim e (Ψ-mono lv lb (l _ (lgBd* ℓ e lv)) p)
    Ψ-mono {W} lv lb (mo , l) (hLim {κ = inj₂ _} {c = c} e p) =
      ⊲ᴮ-tr (Ψ-mono lv lb (l c (lg*⊲ ℓ e lv lb)) p)
        (⊲ᴮ-tr (Ψ-mono lv lb (l (proj₂ W) lb) (mo (lv , lb) e hself e)) (hlim 0 hself))

    Ψ-lg : ∀ {W} → LgW* ℓ⁺ W → ∀ b → Lg* ℓ⁺ b → Lg* ℓ (Ψ W b)
    Ψ-lg lW hz l = tt
    Ψ-lg {W} lW (hs b) l = (λ lw n → mul-fst (Ψ W b) n) , Lg*-mul (Ψ W b) (Ψ-lg lW b l)
    Ψ-lg {W} lW (hl f) (st , l) =
      (λ lv n → Ψ-mono {W} lv (proj₂ lW) (l (suc n)) (st (lv , proj₂ lW) n)) , (λ n → Ψ-lg lW (f n) (l n))
    Ψ-lg {W} lW (hΩ (inj₁ κ) g) (mo , l) =
      (λ lw e e′ p → Ψ-mono {W} lw (proj₂ lW) (l _ (lgBd* ℓ e′ lw)) (mo (lw , proj₂ lW) e e′ p)) ,
      (λ c lc → Ψ-lg lW (g c) (l c lc))
    Ψ-lg {W} lW (hΩ (inj₂ _) g) (mo , l) = (λ lw n → ⊞-fst _ _) , lch
      where
      k : Wd L → HB T → HB T
      k W′ c = Ψ W′ (g c)
      lch : ∀ n → Lg* ℓ (chain (proj₁ W) (proj₂ W) k n)
      lch zero = Ψ-lg lW (g (proj₂ W)) (l _ (proj₂ lW))
      lch (suc n) =
        Lg*-⊞ ℓ _ _ (lch n)
          (Ψ-lg (proj₁ lW , Lg*-⊞ ℓ _ _ (proj₂ lW) (lch n)) (g _) (l _ (Lg*-⊞ ℓ _ _ (proj₂ lW) (lch n))))
```

## §3 后继层的塔, 闭项, 证书, FGH

`T n = stepⁿ S⊥`, 第 $n$ 层的顶 `Ω n` ($n\ge1$ 时是新种类的结点 $\sup_c c$, 即 $\Omega_n$), 基世界 `W n` 把第 $n$ 层新种类的界取作 `Ω (n-1)`: 这就是 $\psi_n(0)=\Omega_n$ 那一层地板, 它不在折叠里, 在世界里. 折到底 `fold n` 是 `Ψ` 的 $n$ 次复合, 证书是 `Ψ-lg` 的 $n$ 次复合.

```agda
T : ℕ → KS
T zero = S⊥
T (suc n) = step (T n)

ℓT : ∀ n → LS (T n)
ℓT zero = ls⊥
ℓT (suc n) = step* (ℓT n)

Ω : ∀ n → HB (T n)
Ω zero = hz
Ω (suc n) = hΩ (inj₂ tt) up

Lg*-Ω : ∀ n → Lg* (ℓT n) (Ω n)
Lg*-Ω zero = tt
Lg*-Ω (suc n) = (λ lw e e′ p → up-⊲ p) , (λ c lc → Lg*-up (ℓT n) c lc)

-- 输入高度也满足 HtTowerTy 的标准合法 LgB (单调由形状给出, 对一切世界)
LgB-Ω : ∀ n → LgB (Ω n)
LgB-Ω zero = tt
LgB-Ω (suc n) = (λ lw e e′ p → up-⊲ p) , (λ c lc → Lg-up c lc)

W : ∀ n → Wd (T n)
W zero = tt
W (suc n) = W n , Ω n

lW : ∀ n → LgW* (ℓT n) (W n)
lW zero = tt
lW (suc n) = lW n , Lg*-Ω n

fold : ∀ n → HB (T n) → HB S⊥
fold zero h = h
fold (suc n) h = fold n (Fold.Ψ (T n) (W (suc n)) h)

Lg*-fold : ∀ n h → Lg* (ℓT n) h → Lg* ls⊥ (fold n h)
Lg*-fold zero h l = l
Lg*-fold (suc n) h l = Lg*-fold n _ (Fold.Thm.Ψ-lg (T n) (ℓT n) (lW (suc n)) h l)
```

**回灌带 $\Omega$-结点 (定理, `refl`).** 第 2 层的顶 `Ω 2` 坍缩时链的第 0 点是 `Ψ (W 2) (up (Ω 1))`, 字面是一个 $\Omega_1$-结点 (旧种类保留); 对照 `NewTwrObs.onlyA-rd₁`: 数据树的读回只产生底种类的结点.

```agda
feed-Ω : Fold.chain (T 1) (W 1) (Ω 1) (λ W′ c → Fold.Ψ (T 1) W′ (up c)) zero
       ≡ hΩ (inj₂ tt) (λ c → Fold.Ψ (T 1) (W 2) (up (up c)))
feed-Ω = refl
```

**闭项.** `TΩ n` 是第 $n$ 层的顶折到底 (读法 ψ₀(Ω_n), 判断); `TΩω` 是它们的 ℕ-和 (读法 ψ₀(Ω_ω), 判断; 和的部分和字面是第一位置, 所以合法由形状给出, 不要跨层的单调). 底层 `S⊥` 的 `Lg*` 就是 `LgB` (`lgB⊥`), 树读成 `Ordᶜ zero` 取 FGH.

```agda
TΩ : ℕ → HB S⊥
TΩ n = fold n (Ω n)

Lg-TΩ : ∀ n → Lg* ls⊥ (TΩ n)
Lg-TΩ n = Lg*-fold n (Ω n) (Lg*-Ω n)

Σ⊥ : (ℕ → HB S⊥) → ℕ → HB S⊥
Σ⊥ f zero = f 0
Σ⊥ f (suc n) = Σ⊥ f n ⊞ f (suc n)

Lg-Σ⊥ : ∀ f → (∀ n → Lg* ls⊥ (f n)) → ∀ n → Lg* ls⊥ (Σ⊥ f n)
Lg-Σ⊥ f l zero = l 0
Lg-Σ⊥ f l (suc n) = Lg*-⊞ ls⊥ (Σ⊥ f n) (f (suc n)) (Lg-Σ⊥ f l n) (l (suc n))

TΩω : HB S⊥
TΩω = hl (Σ⊥ TΩ)

Lg-TΩω : Lg* ls⊥ TΩω
Lg-TΩω = (λ _ n → ⊞-fst (Σ⊥ TΩ n) (TΩ (suc n))) , Lg-Σ⊥ TΩ Lg-TΩ

lgB⊥ : ∀ h → Lg* ls⊥ h → LgB h
lgB⊥ hz l = tt
lgB⊥ (hs h) l = lgB⊥ h l
lgB⊥ (hl f) (st , l) = (λ {w} n → st {w} tt n) , (λ n → lgB⊥ (f n) (l n))
lgB⊥ (hΩ () _) l

LgB-TΩ : ∀ n → LgB (TΩ n)
LgB-TΩ n = lgB⊥ (TΩ n) (Lg-TΩ n)

LgB-TΩω : LgB TΩω
LgB-TΩω = lgB⊥ TΩω Lg-TΩω

ord⊥ : HB S⊥ → FLv.Ordᶜ FLv.zero
ord⊥ hz = FLv.zero
ord⊥ (hs h) = FLv.suc (ord⊥ h)
ord⊥ (hl f) = FLv.lim (λ n → ord⊥ (f n))
ord⊥ (hΩ () _)

fghΩ : ℕ → ℕ → ℕ
fghΩ n = FLv.FGH (ord⊥ (TΩ n))

fghΩω : ℕ → ℕ
fghΩω = FLv.FGH (ord⊥ TΩω)
```

## §4 测试: 前几个链点 (有限样本, 不是证明)

第 1 层的顶 $\Omega_1$ 折到第 0 层: 链从界 $0$ 起, $d_0=\Psi(\mathrm{up}\,0)=1$, $d_1=1\boxplus\Psi(\mathrm{up}\,1)=1\boxplus\omega$. 字面相等, `refl`.

```agda
private
  k₁ : Wd (T 1) → HB S⊥ → HB S⊥
  k₁ W′ c = Fold.Ψ S⊥ W′ (up c)

  d₀ : Fold.chain S⊥ tt hz k₁ 0 ≡ hs hz
  d₀ = refl

  d₁ : Fold.chain S⊥ tt hz k₁ 1 ≡ hs hz ⊞ hl (Fold.mul S⊥ (hs hz))
  d₁ = refl
```

## 结论 (按档)

- **[定理]** `Lg*`, `LS`, `ls⊥`, `step*`, `lg*⊲`, `Lg*-⊞`, `Lg*-up`; 折叠 `Fold.Ψ` (对一切 `T`), `feed-id`, `feed-suc`; 一步定理 `Fold.Thm.Ψ-mono`, `Fold.Thm.Ψ-lg` (对一切 `T` 与 `LS T`); 塔 `T`, `Ω`, `W`, `fold`, `Lg*-fold`; `feed-Ω`; 闭项 `TΩ n`, `TΩω`, 证书 `Lg-TΩ`, `Lg-TΩω`, `LgB-TΩ`, `LgB-TΩω`, FGH `fghΩ`, `fghΩω`.
- **[测试]** `d₀`, `d₁`.
- **[判断]** 读法 ψ₀(Ω_n), ψ₀(Ω_ω); "用 `LgB` 陈述 `Ψ-mono` 证不出" 是未走通, 不是否定; `sup` 层的折叠要 "留还是坍缩" 的决定, 下标是 ℕ 时可判定, 是高度时要公共上界.
