# 链从 0 起 (三): "有界" 与 "等于" 带着同样的新节点信息

> 不含记号. 入口 [ChainZ](ChainZ.lagda.md). 审查 (`Survey/ClosedTermReview.md`) 的 D2 说: 链从底起 ($x_0=\mathrm{bot}$, $x_{n+1}=x_n\boxplus\mathrm{rd}(\Delta_n)$), 世界只要 "让 $x_{n+1}$ 有界", 不要求 "分量恰好是旧界 ⊞ 读回", 所以只增长的世界 (`DiagK3Grow.growL′`) 够用, 命题 W′ 的 "忠实相等" 弱化成 "有界". 这一篇把这句话里的两步各写成一条编译过的定理, 两条都是否定方向:
>
> 1. **`dich` (对一切 `S`).** 在 `step S` 的新种类上, 只要新世界比某个旧世界大且合法, 新世界里有界的格就与旧界**字面可比**: 要么在旧界之下, 要么字面含旧界. 所以 "不读界" 的格若要爬过旧界, 就字面地含旧界; 与旧界字面不可比的格**没有世界** (`no-world`, 前提可满足: `ω`, `ω′` 合法, 世界合法). 旧世界可以是节点自己的世界 $W_0$ (分支只在 $W_0$ 之上有定义), 所以这不只是 "当前世界" 的问题.
> 2. **`no-chain` (第 1 级, `κ₂`).** 由 `dW 1` 经任意多次 `growL′` (任意 `A` 增量 $f$, 任意 $H_0$ 增量 $h$) 得到的世界里, `κ₂` 的界没有新种类的 $\Omega$-节点 (`reach-noNew`); 有界就是字面第一位置, 第一位置继承 "无新节点" (`noNew⊲`); 所以**含新种类节点的格 $y\boxplus\delta$ ($\delta$ 含新节点) 在这些世界里从不有界** (`no-chain`), 对一切 $y$. 前提可满足: `Ωtop S₀` 合法且含新节点, `dW 1` 合法, `growL′` 保合法.
>
> 合起来: "有界" ($\lhd$) 与 "等于" 对新种类节点携带同样的信息 (子项继承 `NoNew`), 所以 W′ 从 "忠实相等" 弱化成 "有界" 不改变能到达的坐标类; 只增长的世界在 `κ₂` 处的损失与 `DiagK3One.noNew-emb` 是同一个, D2 没有绕开它. 范围: 只杀 "世界由 `growL′` 从 `dW 1` 生成" 这一族 (D2 的原文); 不杀以 `HB S₁` 为增量的一致搬运 (那是 `DiagK4` 的 $\mathrm{tr}$, 有 `¬Lg-Tr₀`, `Lg-const`, 一般情形开放), 不杀 D1.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ChainZNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop)
open import OCF.Align.HtTowerNStage using (L′; dW)
open import OCF.Align.DiagK3Grow using (growL′; lg-growL′)
open import OCF.Align.DiagK3One using (NoNew; up-noNew; ⊞-noNew; κ₂; lgdW)
```

## §1 有界的格与旧界字面可比

`step S` 的世界是 $(w,b)$; 新种类的界是 $b$, 有界是 $x\lhd_{[w]} b$. 新世界 $(w',b')$ 比 $(w,b)$ 大, 就有 $b\lhd_{[w']}b'$; 合法给出 $b'$ 合法; `cmpB` 让 $b'$ 的两个第一位置可比. 这一行就是证明.

```agda
module _ {S : KS} where
  dich : ∀ {w b w′ b′ x} → _≤w_ (step S) (w , b) (w′ , b′) → LgW (step S) (w′ , b′) →
         Bd (step S) (inj₂ tt) x (w′ , b′) → (x ⊲[ w′ ] b) ⊎ (b ⊲[ w′ ] x)
  dich (q , bb′) (lw′ , lb′) e = cmpB bb′ e lw′ lb′
```

**例子: 与旧界字面不可比的格没有世界.** $\omega=\mathrm{hl}\,\mathrm{fin}$, $\omega'=\mathrm{hl}\,(\mathrm{fin}\circ\mathrm{suc})$, 都合法, 值相同, 字面互不为第一位置. 不可比用一个可算的观察量: $\omega$ 的第一位置要么是它自己 (头一项是 $0$), 要么没有极限节点.

```agda
fin : ℕ → HB S₀
fin zero = hz
fin (suc n) = hs (fin n)

ω ω′ : HB S₀
ω = hl fin
ω′ = hl (λ n → fin (suc n))

lfin : ∀ n → LgB (fin n)
lfin zero = tt
lfin (suc n) = lfin n

lω : LgB ω
lω = (λ n → hsuc hself) , lfin

lω′ : LgB ω′
lω′ = (λ n → hsuc hself) , (λ n → lfin (suc n))

NoL : HB S₀ → Set
NoL hz = ⊤
NoL (hs a) = NoL a
NoL (hl f) = ⊥
NoL (hΩ κ g) = ⊥

hd0 : HB S₀ → HB S₀
hd0 (hl f) = f 0
hd0 _ = hz

IsL : HB S₀ → Set
IsL (hl f) = ⊤
IsL _ = ⊥

noL⊲ : ∀ {a b w} → a ⊲[ w ] b → NoL b → NoL a
noL⊲ hself n = n
noL⊲ (hsuc p) n = noL⊲ p n

noLfin : ∀ n → NoL (fin n)
noLfin zero = tt
noLfin (suc n) = noLfin n

pos : ∀ {f a w} → a ⊲[ w ] hl f → (∀ n → NoL (f n)) → (hd0 a ≡ f 0 × IsL a) ⊎ NoL a
pos hself nf = inj₁ (refl , tt)
pos (hlim n p) nf = inj₂ (noL⊲ p (nf n))

ω′⋬ω : ∀ {w} → ¬ (ω′ ⊲[ w ] ω)
ω′⋬ω p with pos p noLfin
... | inj₁ (() , _)
... | inj₂ ()

ω⋬ω′ : ∀ {w} → ¬ (ω ⊲[ w ] ω′)
ω⋬ω′ p with pos p (λ n → noLfin (suc n))
... | inj₁ (() , _)
... | inj₂ ()
```

`S₁ = step S₀` (`HtTowerF` 的层的种类结构). 世界 $(0,\omega)$ 合法; 比它大的合法世界里, `κH` 处 $\omega'$ 不有界.

```agda
no-world : ∀ {w′ b′} → _≤w_ (step S₀) (azero , ω) (w′ , b′) → LgW (step S₀) (w′ , b′) →
           ¬ Bd (step S₀) (inj₂ tt) ω′ (w′ , b′)
no-world q l e with dich q l e
... | inj₁ p = ω′⋬ω p
... | inj₂ p = ω⋬ω′ p

-- 前提可满足: 世界合法, 格合法; 正对照: 字面含旧界的格 ω ⊞ 1 在升高的世界里有界
lW₀ : LgW (step S₀) (azero , ω)
lW₀ = tt , lω

pos-ctl : Σ (Wd (step S₀)) (λ W′ → _≤w_ (step S₀) (azero , ω) W′ × LgW (step S₀) W′ × Bd (step S₀) (inj₂ tt) (ω ⊞ hs hz) W′)
pos-ctl = (azero , ω ⊞ hs hz) , (C.self , ⊞-fst ω (hs hz)) , (tt , Lg-⊞ ω (hs hz) lω tt) , hself
```

## §2 第 1 级: 只增长的世界里, `κ₂` 处含新节点的格从不有界

`κ₂` 是 `L′ 1` 里坐标为 `HB S₁` 的 `Lev` 新种类 (`DiagK3One`). 它的界是世界在 `false` 一侧、坐标 `hs (hs hz)` 处的第二分量.

```agda
bnd₂ : Wd (L′ 1) → HB (step S₀)
bnd₂ w = proj₂ (w false (hs (hs hz)))

bd₂ : ∀ {x w} → Bd (L′ 1) κ₂ x w → x ⊲[ proj₁ (w false (hs (hs hz))) ] bnd₂ w
bd₂ e = e

-- 第一位置继承 "无新节点"
noNew⊲ : ∀ {S} {a b : HB (step S)} {w} → a ⊲[ w ] b → NoNew b → NoNew a
noNew⊲ hself n = n
noNew⊲ (hsuc p) n = noNew⊲ p n
noNew⊲ (hlim k p) n = noNew⊲ p (n k)
noNew⊲ (hLim {κ = inj₁ κ} e p) n = noNew⊲ p (n _)
noNew⊲ (hLim {κ = inj₂ tt} e p) ()

-- 右边含新节点, 和就含新节点
noNew-⊞r : ∀ {S} (y δ : HB (step S)) → NoNew (y ⊞ δ) → NoNew δ
noNew-⊞r y hz n = tt
noNew-⊞r y (hs δ) n = noNew-⊞r y δ n
noNew-⊞r y (hl f) n = λ k → noNew-⊞r y (f k) (n k)
noNew-⊞r y (hΩ (inj₁ κ) g) n = λ c → noNew-⊞r y (g c) (n c)
noNew-⊞r y (hΩ (inj₂ tt) g) ()
```

**由 `dW 1` 经 `growL′` 生成的世界.** 每一步可以换 $f$ 与 $h$ (D2 的世界操作就是这一步).

```agda
data Reach : Wd (L′ 1) → Set where
  r0 : Reach (dW 1)
  rg : ∀ {w} (f : A → A) (ffst : ∀ a → a ⊲ f a) (flg : ∀ a → Lg a → Lg (f a)) (h : HB S₀) (lh : LgB h) →
       Reach w → Reach (growL′ f ffst flg h lh 1 w)

reach-noNew : ∀ {w} → Reach w → NoNew (bnd₂ w)
reach-noNew r0 = tt
reach-noNew (rg f ffst flg h lh r) = ⊞-noNew _ (up h) (reach-noNew r) (up-noNew h)

reach-lg : ∀ {w} → Reach w → LgW (L′ 1) w
reach-lg r0 = lgdW 1
reach-lg (rg f ffst flg h lh r) = lg-growL′ f ffst flg h lh 1 _ (reach-lg r)

no-cell : ∀ {w x} → Reach w → Bd (L′ 1) κ₂ x w → NoNew x
no-cell {w} r e = noNew⊲ (bd₂ {w = w} e) (reach-noNew r)

-- D2 的格 y ⊞ δ: δ 含新节点就从不有界, 对一切 y
no-chain : ∀ {w} y δ → Reach w → ¬ NoNew δ → ¬ Bd (L′ 1) κ₂ (y ⊞ δ) w
no-chain y δ r nn e = nn (noNew-⊞r y δ (no-cell r e))
```

**前提可满足.** `κ₂` 的坐标类型里, 第一个新种类的 $\Omega$ (`Ωtop S₀`) 合法且含新节点; 可达世界合法.

```agda
new-Ω : ¬ NoNew (Ωtop S₀)
new-Ω ()

sat : Reach (dW 1) × LgW (L′ 1) (dW 1) × LgB (Ωtop S₀) × ¬ NoNew (Ωtop S₀)
sat = r0 , lgdW 1 , Lg-Ωtop S₀ , new-Ω

-- 推论: 第 n 格 y ⊞ Ωtop S₀ 在一切可达世界里都不有界
no-Ω-cell : ∀ {w} y → Reach w → ¬ Bd (L′ 1) κ₂ (y ⊞ Ωtop S₀) w
no-Ω-cell y r = no-chain y (Ωtop S₀) r new-Ω
```

**正对照 (`κ₂` 处).** 无新节点的格是有界的: 增长一步后, 界本身 ($\mathrm{hz}\boxplus\mathrm{up}\,h$) 就是可达世界里有界的格. 所以 `no-chain` 杀的恰好是新节点, 不是一切格.

```agda
pos-κ₂ : ∀ (h : HB S₀) (lh : LgB h) →
  let w = growL′ (λ a → a) (λ a → C.self) (λ a l → l) h lh 1 (dW 1) in
  Reach w × Bd (L′ 1) κ₂ (hz ⊞ up h) w
pos-κ₂ h lh = rg (λ a → a) (λ a → C.self) (λ a l → l) h lh r0 , hself
```

**提升到 `L′ 2`.** `κ₂` 进第 1 级的层是经链分量 (`DiagK3One.head₂`: 种类 `(true , inj₁ κ₂)`); 那里的界就是 `L′ 1` 世界的 `κ₂` 界, `growL′ 2` 在链分量上就是 `growL′ 1`. 两条都是 `refl`, 所以 §2 原样适用于第 1 级的层.

```agda
lift₂ : ∀ {c w} → Bd (L′ 2) (true , inj₁ κ₂) c w ≡ Bd (L′ 1) κ₂ c (proj₁ (w true))
lift₂ = refl

grow₂ : ∀ f ffst flg h lh (w : Wd (L′ 2)) → proj₁ (growL′ f ffst flg h lh 2 w true) ≡ growL′ f ffst flg h lh 1 (proj₁ (w true))
grow₂ f ffst flg h lh w = refl
```
