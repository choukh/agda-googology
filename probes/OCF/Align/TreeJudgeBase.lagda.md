# 树侧判据 (定义与定理): 头律, 幽灵地板, 界不进值

> 不含记号. 结论写在 [TreeJudge](TreeJudge.lagda.md). 只导入 `OCF.Free.Level`, `OCF.Free.Prefix`, `OCF.Free.Force` 与 stdlib.
>
> 这里的对象都是第 0 层的只读树 `Z`: 后继, $\omega$-极限, 闭包 `ĉᴸ c t₀ g o₀ o`. 闭包的读法: 链点 $y_0=t_0$, $y_{k+1}=g(\mathrm{lv}\,y_k)$; 输出 $o_0, o(\mathrm{lv}\,y_0), o(\mathrm{lv}\,y_1),\dots$. `c` 是界 (分支 $\eta$ 要 $c\sqsubseteq\eta$), `t₀` 是头.
>
> - §1 `Sub`, `FP`: 子树与第一路径.
> - §2 `head-law`: `Goodᴺ` 推出 $c\sqsubseteq\mathrm{lv}(t_0)$. 这是 `gc-t` ([LvCertNeg](LvCertNeg.lagda.md)) 搬到无记号的 `Z` 上.
> - §3 `ghost`: **幽灵地板定理.** 闭包 $X$ 的每个分支 $\tau$ 的第一路径上都有闭包 $C_\tau$, 界 $\ge\tau+1$, 头落在 $X$ 自己的头的第一路径上. 则 $X$ 没有 `Goodᴺ`. 对一切 $X$, 不看定义.
> - §4 `force-≃`, `rebound`: **界不进值.** 两棵树只差界, 都 `Goodᴺ`, 则值 $\cong$.
> - §5 `HF`: **同头同界.** 判据的主条. `hf-indep`: 它不是 `Goodᴺ` 的推论, 也不是值的性质 (编译过的反例).
> - §6 `Reg⁰`: 纯树上的 Bachmann 性质, 只看 $\omega$-极限 ([InaccModulusBase](InaccModulusBase.lagda.md) 的 `Reg` 搬到 `Tr`).
> - §7 `Climb`, `Vis`: 折叠的行写成关系. **这两条是折叠方程本身, 不是新判据.**

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeJudgeBase where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; m≤n⇒m≤1+n; <-irrefl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; ĉᴸ; _≅ᶻ_; zᶻ; sᶻ; lᶻ; ĉᶻ)
open import OCF.Free.Force using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅; outsᴺ; outsᴺ-≅; ys-≅)
```

## §1 子树与第一路径

`Sub y x`: $y$ 是 $x$ 沿后继, 极限项, 第一支, 任一分支走到的子树. `FP y x`: 只走后继, 极限项, 第一支, 不走分支. `FP` 的好处是 `Goodᴺ` 沿它下降不要知道链 (`fp-good`).

```agda
data Sub (y : Z) : Z → Set where
  here : Sub y y
  ↓s   : ∀ {x} → Sub y x → Sub y (Z.suc x)
  ↓l   : ∀ {f} n → Sub y (f n) → Sub y (Z.lim f)
  ↓f   : ∀ {c t g o₀ o} → Sub y o₀ → Sub y (ĉᴸ c t g o₀ o)
  ↓b   : ∀ {c t g o₀ o} η e → Sub y (o η e) → Sub y (ĉᴸ c t g o₀ o)

data FP (y : Z) : Z → Set where
  here : FP y y
  ↓s   : ∀ {x} → FP y x → FP y (Z.suc x)
  ↓l   : ∀ {f} n → FP y (f n) → FP y (Z.lim f)
  ↓f   : ∀ {c t g o₀ o} → FP y o₀ → FP y (ĉᴸ c t g o₀ o)

FP→Sub : ∀ {y x} → FP y x → Sub y x
FP→Sub here = here
FP→Sub (↓s p) = ↓s (FP→Sub p)
FP→Sub (↓l n p) = ↓l n (FP→Sub p)
FP→Sub (↓f p) = ↓f (FP→Sub p)

⊑-suc⁰ : ∀ {x y : Ordᶜ zero} → x ⊑⁰ y → x ⊑⁰ suc y
⊑-suc⁰ p h = ≺s (p h)

fp-good : ∀ {y x} → FP y x → (G : Goodᴺ x) → Σ (Goodᴺ y) λ H → forceᴺ y H ⊑⁰ forceᴺ x G
fp-good here G = G , (λ h → h)
fp-good (↓s p) (gs G) with fp-good p G
... | H , le = H , ⊑-suc⁰ le
fp-good (↓l n p) (gl G st) with fp-good p (G n)
... | H , le = H , ⊑-lim n le
fp-good (↓f p) (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) with fp-good p Go₀
... | H , le = H , ⊑-lim 0 le
```

## §2 头律

`lv G`: 证书读出的层号. **`head-law`: 界不高于头的层号.** 这是 `Goodᴺ` 的一部分: 第 0 个链点要过守卫. 它只提树.

```agda
lv : ∀ {x : Z} → Goodᴺ x → Ordᴵ
lv {x} G = toLevel (forceᴺ x G) (forceᴺ-HS x G)

lv-≅ : ∀ {x y} → x ≅ᶻ y → (G : Goodᴺ x) (G′ : Goodᴺ y) → lv G ≅ᴵ lv G′
lv-≅ d G G′ = toLevel-≅ (forceᴺ-HS _ G) (forceᴺ-HS _ G′) (forceᴺ-≅ d G G′)

≅ᴵ→⊑ : ∀ {a b} → a ≅ᴵ b → a ⊑ᴵ b
≅ᴵ→⊑ z≅     = z⊑
≅ᴵ→⊑ (s≅ e) = s⊑ e zero
≅ᴵ→⊑ (l≅ h) = l⊑ (λ n → ⊑ᴵ-trans (≅ᴵ→⊑ (h n)) (Sim→⊑ᴵ (λ q → lim n q)))

head-law : ∀ {c t₀ o₀} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z} (G : Goodᴺ (ĉᴸ c t₀ g o₀ o)) →
           Σ (Goodᴺ t₀) λ G₀ → c ⊑ᴵ lv G₀
head-law (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) =
  G₀ , ⊑ᴵ-trans (dy 0) (≅ᴵ→⊑ (toLevel-≅ (hy 0) (forceᴺ-HS _ G₀) (≅-sym l₀)))
```

## §3 幽灵地板定理

**`Ghost X`**: 闭包 $X$ 的每个分支 $\tau$ 的第一路径上有闭包 $C_\tau$, 界至少 $\tau+1$, 它的头 $\cong$ $X$ 的头的第一路径上的一个点. 这时 $C_\tau$ 的界读到了 $\tau$, 头却不读: 地板是 "幽灵".

**`ghost`: `Ghost X` 推出 $X$ 没有 `Goodᴺ`.** 令 $\tau=\mathrm{lv}(t_0)$, 第 0 个分支. $C_\tau$ 的头律给 $\tau+1\sqsubseteq\mathrm{lv}(\text{头})$, 而头在 $t_0$ 的第一路径上, 所以 $\mathrm{lv}(\text{头})\sqsubseteq\tau$. 这个定理是 [LvCertNeg](LvCertNeg.lagda.md) 的 `noW` 的抽象: 那里是对一棵树走出来的, 这里对一切 `Z`.

**这给了 `Tc` 的 "最小" 一个树侧的理由:** 不紧的读法把穿过的分支值 $\tau$ 读进界, 头不读, 于是 `Ghost`, 于是没有证书. 理由不要看目标.

```agda
record Ghost₁ (t₀ : Z) (τ : Ordᴵ) (X : Z) : Set where
  constructor ghost₁
  field
    {c′ t′ p′} : _
    {g′ o′}    : (η : Ordᴵ) → c′ ⊑ᴵ η → Z
    fpC        : FP (ĉᴸ c′ t′ g′ p′ o′) X
    bdC        : suc τ ⊑ᴵ c′
    {y}        : Z
    fpY        : FP y t₀
    hdC        : t′ ≅ᶻ y

Ghost : ∀ {c} (t₀ : Z) (o : (η : Ordᴵ) → c ⊑ᴵ η → Z) → Set
Ghost {c} t₀ o = ∀ τ (e : c ⊑ᴵ τ) → Ghost₁ t₀ τ (o τ e)

suc⊑self : ∀ {τ} → suc τ ⊑ᴵ τ → ⊥
suc⊑self (s⊑ e q) = ≺ᴵ-irrefl (via e q)

ghost : ∀ {c t₀ o₀} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z} → Ghost t₀ o → Goodᴺ (ĉᴸ c t₀ g o₀ o) → ⊥
ghost {t₀ = t₀} {o = o} gh (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = suc⊑self bad
  where
  τ : Ordᴵ
  τ = toLevel (ys 0) (hy 0)
  W = gh τ (dy 0)
  C = fp-good (Ghost₁.fpC W) (Go 0)
  H = head-law (proj₁ C)
  Y = fp-good (Ghost₁.fpY W) G₀
  lvH⊑τ : lv (proj₁ H) ⊑ᴵ τ
  lvH⊑τ = ⊑ᴵ-trans (≅ᴵ→⊑ (lv-≅ (Ghost₁.hdC W) (proj₁ H) (proj₁ Y)))
            (toLevel-⊑ (forceᴺ-HS _ (proj₁ Y)) (hy 0) (⊑-trans (proj₂ Y) (≅→⊑ l₀)))
  bad : suc τ ⊑ᴵ τ
  bad = ⊑ᴵ-trans (Ghost₁.bdC W) (⊑ᴵ-trans (proj₂ H) lvH⊑τ)
```

## §4 界不进值

`_≃ᶻ_` 是 `_≅ᶻ_` 去掉 `c ≅ᴵ c′`: 头, 链, 输出逐点 (在两边守卫都过的 $\eta$ 上) 相关, 界随便. **`force-≃`: 只差界的两棵树, 都有证书, 值 $\cong$.** 证明与 `forceᴺ-≅` 同形: 证书只在链点上取分支, 链点都过了两边的守卫.

**所以界不是序数内容.** 它只决定合法性: 窗口是 "分支上证据齐全" 与 `head-law` 之间. 紧不紧本身不改值; 不紧的害处是窗口变空 (`ghost`). 这也说明 `agree` 看到的 "这里 2, 塔 1" 单独不是值的错误.

```agda
infix 4 _≃ᶻ_
data _≃ᶻ_ : Z → Z → Set where
  z≃ : Z.zero ≃ᶻ Z.zero
  s≃ : ∀ {x y} → x ≃ᶻ y → Z.suc x ≃ᶻ Z.suc y
  l≃ : ∀ {f g : ℕ → Z} → (∀ n → f n ≃ᶻ g n) → Z.lim f ≃ᶻ Z.lim g
  c≃ : ∀ {c c′ t₀ t₀′ o₀ o₀′} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z} {g′ o′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Z} →
       t₀ ≃ᶻ t₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≃ᶻ g′ η′ e′) →
       o₀ ≃ᶻ o₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → o η e ≃ᶻ o′ η′ e′) →
       ĉᴸ c t₀ g o₀ o ≃ᶻ ĉᴸ c′ t₀′ g′ o₀′ o′

≅ᶻ→≃ᶻ : ∀ {x y} → x ≅ᶻ y → x ≃ᶻ y
≅ᶻ→≃ᶻ zᶻ = z≃
≅ᶻ→≃ᶻ (sᶻ d) = s≃ (≅ᶻ→≃ᶻ d)
≅ᶻ→≃ᶻ (lᶻ h) = l≃ (λ n → ≅ᶻ→≃ᶻ (h n))
≅ᶻ→≃ᶻ (ĉᶻ ec dt dg dp dO) =
  c≃ (≅ᶻ→≃ᶻ dt) (λ η e η′ e′ d → ≅ᶻ→≃ᶻ (dg η e η′ e′ d)) (≅ᶻ→≃ᶻ dp) (λ η e η′ e′ d → ≅ᶻ→≃ᶻ (dO η e η′ e′ d))

force-≃ : ∀ {x y} → x ≃ᶻ y → (G : Goodᴺ x) (G′ : Goodᴺ y) → forceᴺ x G ≅ forceᴺ y G′
force-≃ z≃ gz gz = z≅
force-≃ (s≃ d) (gs G) (gs G′) = s≅ (force-≃ d G G′)
force-≃ (l≃ h) (gl G _) (gl G′ _) = l≅ (λ n → force-≃ (h n) (G n) (G′ n))
force-≃ (c≃ dt dg dp dO) (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) (gc ys′ hy′ dy′ G₀′ l₀′ Gg′ lE′ Go₀′ Go′ mo₀′ mo′) =
  l≅ (outsᴺ-≅ (force-≃ dp Go₀ Go₀′)
              (λ k → force-≃ (dO _ _ _ _ (toLevel-≅ (hy k) (hy′ k) (eY k))) (Go k) (Go′ k)))
  where
  eY : ∀ m → ys m ≅ ys′ m
  eY = ys-≅ (≅-trans (≅-sym l₀) (≅-trans (force-≃ dt G₀ G₀′) l₀′))
            (λ m e → ≅-trans (≅-sym (lE m))
                     (≅-trans (force-≃ (dg _ _ _ _ (toLevel-≅ (hy m) (hy′ m) e)) (Gg m) (Gg′ m)) (lE′ m)))

-- 同一族数据, 两个界
rebound : ∀ {c c′ t₀ o₀} {g o : ∀ η → c ⊑ᴵ η → Z} {g′ o′ : ∀ η → c′ ⊑ᴵ η → Z} →
          t₀ ≃ᶻ t₀ → o₀ ≃ᶻ o₀ →
          (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≃ᶻ g′ η′ e′) → (∀ η e η′ e′ → η ≅ᴵ η′ → o η e ≃ᶻ o′ η′ e′) →
          (G : Goodᴺ (ĉᴸ c t₀ g o₀ o)) (G′ : Goodᴺ (ĉᴸ c′ t₀ g′ o₀ o′)) →
          forceᴺ _ G ≅ forceᴺ _ G′
rebound dt dp dg dO G G′ = force-≃ (c≃ dt dg dp dO) G G′
```

## §5 同头同界 `HF`

**`HF T`: 树 $T$ 里任意两个闭包, 头相同 ($\cong$), 界就相同.** 一个闭包的身份由它的头决定, 界是头的函数. 这是 `tail-free` 的不带形状的版本: 那里说 "$a+\eta$ 的闭包的界不看穿过的 $\tau$", 这里不提 $a+\eta$.

**它只提树: 没有记号, 没有目标, 没有层号的形状.** 它不可判定 (量词过全部分支, $\cong$ 是互模拟). 用法是有限测试: [TreeJudgeObs](TreeJudgeObs.lagda.md) 取样走树, 用深度受限的指纹代替 $\cong$. 指纹相同不是定理, 所以测试给出的 "违反" 也只是测试.

```agda
HF : Z → Set
HF T = ∀ {c t₀ o₀ c′ t₀′ o₀′} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z} {g′ o′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Z} →
       Sub (ĉᴸ c t₀ g o₀ o) T → Sub (ĉᴸ c′ t₀′ g′ o₀′ o′) T → t₀ ≅ᶻ t₀′ → c ≅ᴵ c′
```

**`hf-indep`: `HF` 不是 `Goodᴺ` 的推论.** 反例: 同一个头 $2$, 界 $1$ 与 $2$, 分支全是 $0$. 两个闭包都有证书, 值都是 $\omega$ 个 $0$ 的极限. 所以 `HF` 不是合法性, 也不是值的性质 (`force-≃`). **它是判据的增量:** 把 `Good` 之外的一条设计约束写出来. 有没有根据, 只能看它拒绝和接受了什么.

```agda
private
  one two : Ordᴵ
  one = suc zero
  two = suc one

  hd : Z
  hd = Z.suc (Z.suc Z.zero)

  c1 c2 : Z
  c1 = ĉᴸ one hd (λ _ _ → hd) Z.zero (λ _ _ → Z.zero)
  c2 = ĉᴸ two hd (λ _ _ → hd) Z.zero (λ _ _ → Z.zero)

  Y2 : Ordᶜ zero
  Y2 = suc (suc zero)

  hY : HS Y2
  hY = hs (hs hz)

  lvY : toLevel Y2 hY ≡ two
  lvY = refl

  one⊑ : one ⊑ᴵ toLevel Y2 hY
  one⊑ = s⊑ z≅ (suc zero)

  two⊑ : two ⊑ᴵ toLevel Y2 hY
  two⊑ = s⊑ (s≅ z≅) zero

  gHd : Goodᴺ hd
  gHd = gs (gs gz)

  ⊑z : ∀ {ℓ₁ ℓ₂} {b : Ordᶜ ℓ₂} → zero {ℓ₁} ⊑ b
  ⊑z ()

  G1 : Goodᴺ c1
  G1 = gc (λ _ → Y2) (λ _ → hY) (λ _ → one⊑) gHd (s≅ (s≅ z≅)) (λ _ → gHd) (λ _ → s≅ (s≅ z≅)) gz (λ _ → gz) ⊑z (λ _ → ⊑z)

  G2 : Goodᴺ c2
  G2 = gc (λ _ → Y2) (λ _ → hY) (λ _ → two⊑) gHd (s≅ (s≅ z≅)) (λ _ → gHd) (λ _ → s≅ (s≅ z≅)) gz (λ _ → gz) ⊑z (λ _ → ⊑z)

  X : Z
  X = Z.lim (λ { zero → c1 ; (suc _) → c2 })

  force-c1-⊑ : ∀ {H : Goodᴺ c1} {H′ : Goodᴺ c2} → forceᴺ c1 H ⊑⁰ forceᴺ c2 H′
  force-c1-⊑ {H} {H′} = ≅→⊑ (force-≃ (c≃ (s≃ (s≃ z≃)) (λ _ _ _ _ _ → s≃ (s≃ z≃)) z≃ (λ _ _ _ _ _ → z≃)) H H′)

  force-c2-⊑ : ∀ {H H′ : Goodᴺ c2} → forceᴺ c2 H ⊑⁰ forceᴺ c2 H′
  force-c2-⊑ {H} {H′} = ≅→⊑ (force-≃ (c≃ (s≃ (s≃ z≃)) (λ _ _ _ _ _ → s≃ (s≃ z≃)) z≃ (λ _ _ _ _ _ → z≃)) H H′)

  GX : Goodᴺ X
  GX = gl (λ { zero → G1 ; (suc _) → G2 }) (λ { zero → force-c1-⊑ ; (suc _) → force-c2-⊑ })

  hdSelf : hd ≅ᶻ hd
  hdSelf = sᶻ (sᶻ zᶻ)

  ¬1≅2 : one ≅ᴵ two → ⊥
  ¬1≅2 (s≅ ())

  ¬HFX : HF X → ⊥
  ¬HFX h = ¬1≅2 (h (↓l 0 here) (↓l 1 here) hdSelf)

hf-indep : Σ Z λ X → Goodᴺ X × (HF X → ⊥)
hf-indep = X , GX , ¬HFX
```

## §6 纯树的 Bachmann 性质

`Tr`: 只有后继与 $\omega$-极限的树. 可数树一律读到这里. `W⁰ y x`: $y$ 在 $x$ 的 1-走步上, 严格. `Reg⁰`: 每个极限节点上 $h\,n$ 在 $h(n+1)$ 的 1-走步上. **这是 `Reg` ([InaccModulusBase](InaccModulusBase.lagda.md)) 的同形版本.** 它是纯树的性质, 不看输入.

`lim-const`: 常值的极限不规整. [VerdictSpecReject](VerdictSpecReject.lagda.md) 的 `PW` 把链丢掉, 输出正是常值的极限, 所以 `Reg⁰` 一条就拒绝它.

```agda
data Tr : Set where
  t0 : Tr
  ts : Tr → Tr
  tl : (ℕ → Tr) → Tr

wk⁰ : Tr → ℕ
wk⁰ t0     = 0
wk⁰ (ts a) = suc (wk⁰ a)
wk⁰ (tl f) = suc (wk⁰ (f 1))

data W⁰ (y : Tr) : Tr → Set where
  w0  : W⁰ y (ts y)
  ws  : ∀ {a} → W⁰ y a → W⁰ y (ts a)
  wl0 : ∀ {f} → f 1 ≡ y → W⁰ y (tl f)
  wl  : ∀ {f} → W⁰ y (f 1) → W⁰ y (tl f)

Reg⁰ : Tr → Set
Reg⁰ t0     = ⊤
Reg⁰ (ts a) = Reg⁰ a
Reg⁰ (tl h) = (∀ n → W⁰ (h n) (h (suc n))) × (∀ n → Reg⁰ (h n))

wk-< : ∀ {y x} → W⁰ y x → wk⁰ y < wk⁰ x
wk-< w0         = ≤-refl
wk-< (ws w)     = m≤n⇒m≤1+n (wk-< w)
wk-< (wl0 refl) = ≤-refl
wk-< (wl w)     = m≤n⇒m≤1+n (wk-< w)

no-self : ∀ {x} → W⁰ x x → ⊥
no-self w = <-irrefl refl (wk-< w)

lim-const : ∀ {x} → Reg⁰ (tl (λ _ → x)) → ⊥
lim-const r = no-self (proj₁ r 0)
```

## §7 折叠的行写成关系 (不是新判据)

这一节写的是**折叠方程本身**, 只是写成关系, 对一个抽象的节点. 它管 `Sub` 和界管不到的两种错: 看得见的节点被压成 $\omega$-极限, 与链不爬升. 同一个 `Climb`, `Vis` 可以实例化到 `Lv`, `Ordᶜ`, `O` 上. **这不是从树逼出来的:** 方程的来源是折叠的定义, 与 [VerdictSpec](VerdictSpec.lagda.md) 说的 "规格是折叠方程加判决正确" 一样.

`Climb Ψ Op s T`: 目标输出 $T\,n=\Psi(y_n)$, 链从 $s$ 出发, $y_{n+1}$ 不低于 $\mathrm{Op}(y_n)$. $\Psi$ 是节点上的目标折叠, $\mathrm{Op}$ 是节点上的链算子 ($\psi_r\circ h$). 只要求不低于, 所以 $T$ 的链不必是字面的 `iter`. `Vis`: 节点在目标里有字面路径时, 判决必须穿透.

```agda
module Rows {D K : Set} (_≈_ : D → D → Set) (_≤ₖ_ : K → K → Set) where
  record Climb (Ψ : K → D) (Op : K → K) (s : K) (T : ℕ → D) : Set where
    constructor climb
    field
      y    : ℕ → K
      y0   : s ≤ₖ y 0
      eqT  : ∀ n → T n ≈ Ψ (y n)
      step : ∀ n → Op (y n) ≤ₖ y (suc n)

data Vd : Set where
  vp vr : Vd

-- `Lit`: 节点的层在目标层里有字面路径. `vd`: 判决的种类
Vis : {L : Set} → (L → L → Set) → (L → L → Vd) → L → L → Set
Vis Lit vd j i = Lit j i → vd j i ≡ vp
```
