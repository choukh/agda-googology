# 族增量世界上的真折叠, 否定一路 (一): "读回对坐标一致" 这条律

> 不含记号. 入口 [NegFam](NegFam.lagda.md). 对着接口 [FamFoldIf](FamFoldIf.lagda.md) ("接口定稿 2026-11-05 11:20 (编译通过)", 变更记录: 无) 写, 导入它, 不另造接口; 本篇另加的定义 (`Isolated`, `SlotFam`, `PresFam`) 都只由接口与 `HtTowerTy`, `AdmWIf`, `LocUipIf` 的名字组成. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延; `FE₀` (`ColimWNeg` 的 $\mathbb N\to H_0$ 外延) 只作前提, 用到它的结论标 "条件".
>
> 接口 §2 的两条: `SecAt c₀ δ` (读回值 $\delta$ 是某个族 `F : Inc` 在 $c_0$ 的值), `Uniform O c₀ rd` (读回由输出对一切坐标给出族, 在 $c_0$ 处是 `rd`). `Feed₁` 的字段 `famO : Uniform Out₂ c₁ rdO` 用的是 $c_1=1$.
>
> **判决 (本篇).**
>
> 1. **在一级 ($c_0=1$) 这条律不是障碍 (定理).** 有限坐标是**孤立点** (`isolated-fin`: 对一切裸坐标 $c$, `fin n ≡ c` 可判定, 只按构造子匹配, 不用证据), 孤立点上局部 Hedberg 成立 (`Iso.isoK`: 环都是 `refl`), 所以一切读回都延成族 (`iso→uniform`). 推论 **`famO-free : ∀ rd → Uniform O c₁ rd`**: `Feed₁` 的 `famO` 对任意读回 `rdO` 都写得出. 要对不可入坐标给的值, 由 "是不是 $1$" 的结构判定给出, 不触任何壁垒.
> 2. **对一切级 (含 $\omega$ 这样的极限坐标), 这条律至少与 LocUip 的第一条引理一样强 (定理).** `uniform⇔sec`: 对一切 `O`, `rd` 的 `Uniform O c₀ rd` 当且仅当一切 $\delta$ 都 `SecAt c₀ δ`. `sec→fix`: `SecAt c₀ δ` 推出 $c_0$ 处一切环沿 `HB ∘ G₀` 搬运不动 $\delta$. 合起来 `uniformAll→fix`, `→irr`, `→lemma1`: 对一切合法坐标的 `Uniform` 推出 `LocUipNegLoop.LoopFix`, 从而 `IncIrr` 与 `Lemma1`. 所以把增量写成族**没有消掉**外延性内容, 只是把它从更新 (`raise₀ᴮ`) 挪到了读回 (`famO`). 便宜的办法 (孤立) 在 $\omega$ 处是禁忌: **`iso-ω→WLPO`** (条件 `FE₀`): $\omega$ 孤立推出 WLPO; 无条件的部分是分离子 `iso-ω-sep`.
> 3. **"读界" 的读回若对一切级一致, 撞 `raiseA-sep` 的影子 (定理).** 回灌形状 `RunM` 的第一格读世界的界 (槽). 若对一切级一条折叠的读回要成为族, 并且读的是各级的槽, 就要求**槽本身延成坐标族** (`SlotFam`; "旧界接增量" 形式由 `cell→slot` 归约到它). **`slotFam-sep`**: 对**任一**满足 `atF`, `belowF` 的族更新 `R : RaiseF` (接口原样的记录, `raiseFᴮ`, `raiseF⁺`, `raiseFᵒ` 都是), 若在外层世界族 $w_\alpha = (0, y_\alpha+2)$ 上一次更新 (从全 0 世界, 在 $c_0 = y_\alpha$) 之后的槽都延成族, 则对每个 $\alpha$: $y_\alpha\not\equiv\omega$ 或 $\alpha$ 恒假. **`slotFam→WLPO`** (条件 `FE₀`). 推论 **`pres-sep`, `pres→WLPO`**: 保持 "槽是族" 这个不变量的族更新 (`PresFam R`) 推出同样的分离. 单个增量的 `RaiseB` 同样 (`slotFamB-sep`). 机制与 `ColimWNeg.raiseA-sep` 相同: 族在裸坐标 $\omega$ 处的值, 要在 $\omega\equiv c_0$ 时随 $c_0$ 升高 (`atF`, 沿相等搬), 在 $\omega$ 可入且严格在 $c_0$ 之下时不动 (`belowF`); $\omega$ 是否可入取决于 $\alpha$.
>
> **只否定什么.** 第 3 条只否定: 对外层世界族 $w_\alpha$ 一致地, 族更新后 (或保族的更新下) 槽延成坐标族; 它**不**否定接口的 `Feed₁` (那里 `famO` 读的是**输出** `o`, 不是各级的槽, 且只在 $c_1$; 第 1 条说它在 $c_1$ 是定理), 不否定单个世界上槽延成族 (`fam₁`: 有限外界上族更新之后的槽是族, 实例), 不否定相干世界上经典地延成族 (判断). 第 2 条不是否定: `Uniform` 在函数外延下是否成立未证 (判断: 要一个沿结构的坐标翻译, 对角上恒等要分支函数的外延); 它只说一切级的 `famO` 不比 `IncIrr` 便宜.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegFamSec where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Binary.PropositionalEquality.Properties using (trans-symˡ)
open import OCF.Align.CumReadCF using (A; azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.StallDxBdec using (_<ᴮ_; toLt)
open import OCF.Align.AdmWIf
open import OCF.Align.AdmWCoh using (wz; fin)
open import OCF.Align.ColimWIf using (ω₀)
open import OCF.Align.ColimWNeg using (WLPO; FE₀; t≢f; isz; yα; Lg-yα; hit⊲; ne₁; yα≡)
open import OCF.Align.LocUipIf
open import OCF.Align.LocUipFam using (raiseFᴮ)
open import OCF.Align.LocUipNegLoop using (LoopFix; fix→irr; fix→fix⊞; fix⊞→lemma1)
open import OCF.Align.LocUipNegSec using (sec-subst)
open import OCF.Align.FamFoldIf using (SecAt; Uniform; c₁)
open Slot
open RaiseIf
```

## §1 孤立点与局部 Hedberg; 一级的 `famO` 写得出

`Isolated x`: 与 $x$ 的相等对一切**裸**坐标可判定. 有限坐标是孤立的 (只按构造子匹配). 孤立点上环都是 `refl` (Hedberg 的局部版: 收缩函数取判定给的证明, 对 $e$ 归纳, 终点自由), 于是沿判定搬运给出族, 在 $x$ 处恰好是原值.

```agda
Isolated : HB S₀ → Set
Isolated x = ∀ c → (x ≡ c) ⊎ ¬ (x ≡ c)

isolated-fin : ∀ n → Isolated (fin n)
isolated-fin zero hz = inj₁ refl
isolated-fin zero (hs _) = inj₂ (λ ())
isolated-fin zero (hl _) = inj₂ (λ ())
isolated-fin zero (hΩ _ _) = inj₂ (λ ())
isolated-fin (suc n) hz = inj₂ (λ ())
isolated-fin (suc n) (hs c) with isolated-fin n c
... | inj₁ e = inj₁ (cong hs e)
... | inj₂ ne = inj₂ (λ { refl → ne refl })
isolated-fin (suc n) (hl _) = inj₂ (λ ())
isolated-fin (suc n) (hΩ _ _) = inj₂ (λ ())

module Iso {x : HB S₀} (d : Isolated x) where
  col : ∀ {c} → (x ≡ c) ⊎ ¬ (x ≡ c) → x ≡ c → x ≡ c
  col (inj₁ e′) _ = e′
  col (inj₂ ne) e = ⊥-elim (ne e)

  col-const : ∀ {c} (r : (x ≡ c) ⊎ ¬ (x ≡ c)) (e e′ : x ≡ c) → col r e ≡ col r e′
  col-const (inj₁ _) _ _ = refl
  col-const (inj₂ ne) e _ = ⊥-elim (ne e)

  f : ∀ {c} → x ≡ c → x ≡ c
  f {c} = col (d c)

  hed : ∀ {c} (e : x ≡ c) → e ≡ trans (sym (f refl)) (f e)
  hed refl = sym (trans-symˡ (f refl))

  isoK : (e : x ≡ x) → e ≡ refl
  isoK e = trans (hed e) (trans (cong (trans (sym (f refl))) (col-const (d x) e refl)) (sym (hed refl)))

  pick : ∀ {c} → (x ≡ c) ⊎ ¬ (x ≡ c) → HB (G₀ x) → HB (G₀ c)
  pick (inj₁ e) δ = subst (λ z → HB (G₀ z)) e δ
  pick (inj₂ _) δ = hz

  pick-at : ∀ (r : (x ≡ x) ⊎ ¬ (x ≡ x)) δ → pick r δ ≡ δ
  pick-at (inj₁ e) δ = cong (λ q → subst (λ z → HB (G₀ z)) q δ) (isoK e)
  pick-at (inj₂ ne) δ = ⊥-elim (ne refl)

  sec : ∀ δ → SecAt x δ
  sec δ = (λ c → pick (d c) δ) , pick-at (d x) δ

iso→sec : ∀ {x} → Isolated x → ∀ δ → SecAt x δ
iso→sec d = Iso.sec d

iso→uniform : ∀ {x} → Isolated x → ∀ (O : Set) (rd : O → HB (G₀ x)) → Uniform O x rd
iso→uniform d O rd = (λ o → proj₁ (Iso.sec d (rd o))) , (λ o → proj₂ (Iso.sec d (rd o)))

-- Feed₁ 的 famO: 对任意读回都写得出
famO-free : ∀ (O : Set) (rd : O → HB (G₀ c₁)) → Uniform O c₁ rd
famO-free = iso→uniform (isolated-fin 1)
```

## §2 一切级: `Uniform` 与 `SecAt` 等价, 推出环的搬运平凡

```agda
uniform→sec : ∀ {c₀} → (∀ (O : Set) (rd : O → HB (G₀ c₀)) → Uniform O c₀ rd) → ∀ δ → SecAt c₀ δ
uniform→sec {c₀} U δ = proj₁ (U (HB (G₀ c₀)) (λ o → o)) δ , proj₂ (U (HB (G₀ c₀)) (λ o → o)) δ

sec→uniform : ∀ {c₀} → (∀ δ → SecAt c₀ δ) → ∀ (O : Set) (rd : O → HB (G₀ c₀)) → Uniform O c₀ rd
sec→uniform s O rd = (λ o → proj₁ (s (rd o))) , (λ o → proj₂ (s (rd o)))

uniform⇔sec : ∀ {c₀} → ((∀ (O : Set) (rd : O → HB (G₀ c₀)) → Uniform O c₀ rd) → ∀ δ → SecAt c₀ δ) ×
                        ((∀ δ → SecAt c₀ δ) → ∀ (O : Set) (rd : O → HB (G₀ c₀)) → Uniform O c₀ rd)
uniform⇔sec = uniform→sec , sec→uniform

sec→fix : ∀ {x} δ → SecAt x δ → (ℓ : x ≡ x) → subst (λ z → HB (G₀ z)) ℓ δ ≡ δ
sec→fix δ (F , e) ℓ = trans (cong (subst (λ z → HB (G₀ z)) ℓ) (sym e)) (trans (sec-subst F ℓ) e)

-- 对一切合法坐标 (一切级) 的读回对坐标一致
UniformAll : Set₁
UniformAll = ∀ {c₀ : HB S₀} → LgB c₀ → ∀ (O : Set) (rd : O → HB (G₀ c₀)) → Uniform O c₀ rd

uniformAll→fix : UniformAll → LoopFix
uniformAll→fix U lx ℓ δ = sec→fix δ (uniform→sec (U lx) δ) ℓ

uniformAll→irr : UniformAll → IncIrr
uniformAll→irr U = fix→irr (uniformAll→fix U)

uniformAll→lemma1 : UniformAll → Lemma1
uniformAll→lemma1 U = fix⊞→lemma1 (fix→fix⊞ (uniformAll→fix U))
```

**便宜的办法在 $\omega$ 处是禁忌.** $\omega$ 孤立就要判定 $y_\alpha\equiv\omega$.

```agda
iso-ω-sep : Isolated ω₀ → ∀ α → ¬ (yα α ≡ ω₀) ⊎ (∀ n → α n ≡ false)
iso-ω-sep d α with d (yα α)
... | inj₂ ne = inj₁ (λ e → ne (sym e))
... | inj₁ e = inj₂ (λ n → h n (α n) refl)
  where
  h : ∀ n b → α n ≡ b → α n ≡ false
  h n false q = q
  h n true q = ⊥-elim (ne₁ α n q (cong up (sym e)))

sep→WLPO : FE₀ → (∀ α → ¬ (yα α ≡ ω₀) ⊎ (∀ n → α n ≡ false)) → WLPO
sep→WLPO fe s α with s α
... | inj₁ ne = inj₂ (λ h → ne (yα≡ fe α h))
... | inj₂ h = inj₁ h

iso-ω→WLPO : FE₀ → Isolated ω₀ → WLPO
iso-ω→WLPO fe d = sep→WLPO fe (iso-ω-sep d)
```

## §3 读界的读回对一切级一致: 槽要延成族, 撞分离

`SlotFam W`: 世界 $W$ 的槽 (对一切可入的 $(c,p)$) 是某个族 $\Phi$ 的值. 对一切级一条折叠, 若读回是族且读的是各级的槽 (`RunM` 第一格 $x_0 = \mathrm{rd}(\text{界}, z_1)$ 的形状), 就要这个.

```agda
SlotFam : Wᴮ → Set
SlotFam W = Σ Inc (λ Φ → ∀ c (p : AdmE (proj₁ W) c) → proj₂ (proj₂ W c p) ≡ Φ c)
```

**"旧界接增量" 归约到槽.** 若对某个族 $d$, 一切可入坐标上的 "槽 $\boxplus\,d\,c$" 是族 $F$ 的值, 则槽也是族 (右减 `⊟` 是 `⊞` 的左逆, 对 $d$ 归纳, 不用外延).

```agda
infixl 6 _⊟_
_⊟_ : ∀ {S} → HB S → HB S → HB S
x ⊟ hz = x
hs x ⊟ hs d = x ⊟ d
hl F ⊟ hl f = F 0 ⊟ f 0
_⊟_ {S} (hΩ κ G) (hΩ κ′ g) = G (bot S κ) ⊟ g (bot S κ′)
x ⊟ hs d = x
x ⊟ hl f = x
x ⊟ hΩ κ g = x

⊞⊟ : ∀ {S} (a d : HB S) → (a ⊞ d) ⊟ d ≡ a
⊞⊟ a hz = refl
⊞⊟ a (hs d) = ⊞⊟ a d
⊞⊟ a (hl f) = ⊞⊟ a (f 0)
⊞⊟ {S} a (hΩ κ g) = ⊞⊟ a (g (bot S κ))

cell→slot : ∀ W (d : Inc) → Σ Inc (λ F → ∀ c (p : AdmE (proj₁ W) c) → proj₂ (proj₂ W c p) ⊞ d c ≡ F c) → SlotFam W
cell→slot W d (F , e) =
  (λ c → F c ⊟ d c) , (λ c p → trans (sym (⊞⊟ (proj₂ (proj₂ W c p)) (d c))) (cong (λ t → t ⊟ d c) (e c p)))
```

**外层世界族.** $w_\alpha = (0, y_\alpha+2)$; $c_0 = y_\alpha$ 对一切 $\alpha$ 可入; $\omega$ 在 $\alpha$ 某处为真时可入, 且严格在 $y_\alpha$ 之下 (结构子项). 全 0 的分量 `v₀`.

```agda
bα : (ℕ → Bool) → HB S₀
bα α = hs (hs (yα α))

wα : (ℕ → Bool) → Out
wα α = azero , bα α

loα : ∀ α → LgO (wα α)
loα α = tt , Lg-yα α

p₀α : ∀ α → AdmE (wα α) (yα α)
p₀α α = hsuc (hsuc hself)

ptα : ∀ α k → α k ≡ true → AdmE (wα α) ω₀
ptα α k e = hsuc (hsuc (⊲ᴮ-tr (hsuc hself) (hit⊲ α k e)))

ltα : ∀ α k → α k ≡ true → ω₀ <ᴮ yα α
ltα α k e with toLt (⊲ᴮ-tr (hsuc hself) (hit⊲ α k e))
... | inj₁ eq = ⊥-elim (ne₁ α k e (cong up (sym eq)))
... | inj₂ lt = lt

v₀ : ∀ w → Cmp w
v₀ w c p = wz (up c) , hz

δ₁ : Inc
δ₁ c = hs hz
```

**抽象的分离.** 只用三件事: $c_0$ 处的槽非零, 可入且严格在下的 $\omega$ 处的槽为零, 槽延成族. 族在 $\omega$ 处的值为零 ⇒ $y_\alpha\not\equiv\omega$ (相等时沿相等搬, 值非零); 非零 ⇒ $\alpha$ 处处为假 (某处为真时 $\omega$ 可入, 族的值等于槽, 为零).

```agda
module Sep (V : ∀ α → Cmp (wα α))
           (atZ : ∀ α → isz (proj₂ (V α (yα α) (p₀α α))) ≡ false)
           (blZ : ∀ α k (e : α k ≡ true) → isz (proj₂ (V α ω₀ (ptα α k e))) ≡ true)
           (Fm : ∀ α → SlotFam (wα α , V α)) where
  Φ : (ℕ → Bool) → Inc
  Φ α = proj₁ (Fm α)

  look : ∀ α (b : Bool) → isz (Φ α ω₀) ≡ b → ¬ (yα α ≡ ω₀) ⊎ (∀ n → α n ≡ false)
  look α true e = inj₁ (λ eq → t≢f (trans (sym e)
    (trans (cong (λ z → isz (Φ α z)) (sym eq)) (trans (cong isz (sym (proj₂ (Fm α) (yα α) (p₀α α)))) (atZ α)))))
  look α false e = inj₂ (λ n → h n (α n) refl)
    where
    h : ∀ n b → α n ≡ b → α n ≡ false
    h n false q = q
    h n true q = ⊥-elim (t≢f (trans (sym (trans (cong isz (sym (proj₂ (Fm α) ω₀ (ptα α n q)))) (blZ α n q))) e))

  sep : ∀ α → ¬ (yα α ≡ ω₀) ⊎ (∀ n → α n ≡ false)
  sep α = look α (isz (Φ α ω₀)) refl
```

**对任一族更新 (接口的 `RaiseF`).**

```agda
VF : RaiseF → ∀ α → Cmp (wα α)
VF R α = raiseF R (wα α) (loα α) (v₀ (wα α)) (yα α) (p₀α α) δ₁

slotFam-sep : ∀ (R : RaiseF) → (∀ α → SlotFam (wα α , VF R α)) → ∀ α → ¬ (yα α ≡ ω₀) ⊎ (∀ n → α n ≡ false)
slotFam-sep R Fm = Sep.sep (VF R)
  (λ α → cong (λ X → isz (proj₂ X)) (atF R (wα α) (loα α) (v₀ (wα α)) (yα α) (p₀α α) δ₁))
  (λ α k e → cong (λ X → isz (proj₂ X)) (belowF R (wα α) (loα α) (v₀ (wα α)) (yα α) (p₀α α) δ₁ ω₀ (ptα α k e) (ltα α k e)))
  Fm

slotFam→WLPO : FE₀ → ∀ (R : RaiseF) → (∀ α → SlotFam (wα α , VF R α)) → WLPO
slotFam→WLPO fe R Fm = sep→WLPO fe (slotFam-sep R Fm)

-- 单个增量的更新同样
VB : RaiseB → ∀ α → Cmp (wα α)
VB R α = raiseB R (wα α) (loα α) (v₀ (wα α)) (yα α) (p₀α α) (hs hz)

slotFamB-sep : ∀ (R : RaiseB) → (∀ α → SlotFam (wα α , VB R α)) → ∀ α → ¬ (yα α ≡ ω₀) ⊎ (∀ n → α n ≡ false)
slotFamB-sep R Fm = Sep.sep (VB R)
  (λ α → cong (λ X → isz (proj₂ X)) (at R (wα α) (loα α) (v₀ (wα α)) (yα α) (p₀α α) (hs hz)))
  (λ α k e → cong (λ X → isz (proj₂ X)) (below R (wα α) (loα α) (v₀ (wα α)) (yα α) (p₀α α) (hs hz) ω₀ (ptα α k e) (ltα α k e)))
  Fm
```

**"槽是族" 作不变量.** 全 0 世界的槽是族; 保持它的族更新推出同样的分离.

```agda
slotFam₀ : ∀ w → SlotFam (w , v₀ w)
slotFam₀ w = (λ c → hz) , (λ c p → refl)

PresFam : RaiseF → Set
PresFam R = ∀ w lo v c₀ p₀ (δ : Inc) → LgB (δ c₀) → SlotFam (w , v) → SlotFam (w , raiseF R w lo v c₀ p₀ δ)

pres-sep : ∀ R → PresFam R → ∀ α → ¬ (yα α ≡ ω₀) ⊎ (∀ n → α n ≡ false)
pres-sep R P = slotFam-sep R (λ α → P (wα α) (loα α) (v₀ (wα α)) (yα α) (p₀α α) δ₁ tt (slotFam₀ (wα α)))

pres→WLPO : FE₀ → ∀ R → PresFam R → WLPO
pres→WLPO fe R P = sep→WLPO fe (pres-sep R P)
```

**前提实例.** 有限外界 $(0, 1)$ 上, 族更新 `raiseFᴮ` 在 $c_0=1$ 之后的槽是族 (对证据分情形, 判定在闭项上算出). 所以 `SlotFam` 不是空的; 被否定的是对外层世界族一致地成立.

```agda
w₁ : Out
w₁ = azero , hs hz

lo₁ : LgO w₁
lo₁ = tt , tt

V₁ : Cmp w₁
V₁ = raiseF raiseFᴮ w₁ lo₁ (v₀ w₁) (hs hz) hself δ₁

Φ₁ : Inc
Φ₁ (hs hz) = hs hz
Φ₁ _ = hz

fam₁ : SlotFam (w₁ , V₁)
fam₁ = Φ₁ , h
  where
  h : ∀ c (p : AdmE w₁ c) → proj₂ (V₁ c p) ≡ Φ₁ c
  h .(hs hz) hself = refl
  h .hz (hsuc hself) = refl
```

## §4 结论 (按档)

- **[定理]** `isolated-fin`, `Iso.isoK`, `iso→sec`, `iso→uniform`, **`famO-free`**: 孤立点上读回都延成族; 一级 ($c_1$) 的 `famO` 对任意 `rdO` 写得出.
- **[定理]** `uniform⇔sec`, `sec→fix`, **`uniformAll→fix`**, `uniformAll→irr`, `uniformAll→lemma1`: 一切级的 `Uniform` ⇒ `LoopFix` ⇒ `IncIrr`, `Lemma1`.
- **[定理]** `iso-ω-sep`; **[定理, 条件 FE₀]** `iso-ω→WLPO`.
- **[定理]** `cell→slot`, `Sep.sep`, **`slotFam-sep`** (对一切 `RaiseF`), `slotFamB-sep` (对一切 `RaiseB`), `pres-sep`; **[定理, 条件 FE₀]** `slotFam→WLPO`, `pres→WLPO`.
- **[定理]** `slotFam₀`, `fam₁`: 前提实例.
- **[判断]** `Uniform` 在 $\omega$ 处 (不加孤立) 由函数外延推出: 未证. 依据: 沿结构的坐标翻译在对角上只逐点恒等.
- **[判断]** 相干世界上槽经典地延成族 (经典地可入性可判定, 相干给出与证据无关的值), 所以 `slotFam-sep` 的前提族经典地可满足, 与 `ColimWNeg.raiseA-sep` 同档.
