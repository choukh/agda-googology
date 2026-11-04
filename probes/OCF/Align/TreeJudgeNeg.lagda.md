# 树侧判据: 拒绝的定理 (旧树)

> **检验旧树的文件, 导入不干净的模块:** `OCF.Align.InaccStrikeAccept`, `InaccTreeAccept` 读记号的项 (只用它们算出来的层号), `OCFSpecNeg`, `VerdictSpecReject`, `LvCertNeg` 经旧文件的导入链碰到记号. **判据的定义不在这里**, 在 [TreeJudgeBase](TreeJudgeBase.lagda.md). 结论写在 [TreeJudge](TreeJudge.lagda.md).
>
> 这里全部是**编译过的定理**, 无条件 (`Wrong` 的模块参数 `S` 是任意判决).
>
> | 树 | 定理 | 用的条款 |
> |---|---|---|
> | `UniformLvTree` 的 `T₀` | `reject-uniformLv` | `Goodᴺ` (即 `noCert₂`) |
> | `PW` (`wrong-fold`) | `reject-wrong-fold` | `Reg⁰` |
> | $\psi^0(\Omega+\omega)$ 当 $\psi_0(\Omega+\Omega)$ (`static-rejected`) | `reject-static` | `Climb` |
> | `ver` | `reject-ver` | `Vis` |
>
> §5 `hf-blind`: `HF` 单独拒绝不了这些树的后三棵: 没有闭包的树都过 `HF`. 这是判据的边界. §6 `toy-ghost`, `toy-fine`: `ghost` 不是空的.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeJudgeNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)

open import OCF.Align.TreeJudgeBase using (Tr; t0; ts; tl; Reg⁰; lim-const; module Rows; Vd; vp; vr; Vis)
```

## §1 `UniformLvTree`: 没有证书

`reject-uniformLv` 就是 `noCert₂`. 这一条的判官是 `Goodᴺ`, 不是新东西. 它的 `Goodᴺ` 是 `OCF.Align.NotFree` 那一份, 与 `OCF.Free.Force` 逐字相同 (`OCF.Free.Force` 由它切出). `ghost` ([TreeJudgeBase](TreeJudgeBase.lagda.md)) 是 `noW` 的抽象, 没有重新证这棵树满足 `Ghost`.

```agda
import OCF.Align.LvCertNeg as LN
import OCF.Align.UniformLvTree as UT
open import OCF.Align.Prefix as AP using (toZ)
open import OCF.Align.NotFree using () renaming (Goodᴺ to Goodᴺᴬ)

reject-uniformLv : ∀ cf → Goodᴺᴬ (toZ (UT.T₀ LN.c₀ cf)) → ⊥
reject-uniformLv = LN.noCert₂
```

## §2 `wrong-fold`: 常值的极限

`PW` 把链丢掉, 第 0 层的输出是常值的极限 ($\psi_0(\Omega_2)$ 上第一步就是). `Reg⁰` 一条拒绝, 对任意判决 `S`, 不看目标. 对照: 正确的 `PF` 的树不是常值的 (`pf-not-const`, 第 1 个分支与第 0 个分支的头不同, 所以这一条没有把它也拒绝掉; 规整性的取样在 [TreeJudgeCheck](TreeJudgeCheck.lagda.md)).

```agda
open import OCF.Align.InaccTreeBase as IB using (Lv; Ordᴸ; Tree)
open import OCF.Align.InaccFloorTree using (Sib; natL; module PF)
open import OCF.Align.VerdictSpecReject using (module PW)

rdT : Ordᴸ IB.zero → Tr
rdT Tree.zero = t0
rdT (Tree.suc x) = ts (rdT x)
rdT (Tree.lim f) = tl (λ n → rdT (f n))

data HdT : Set where
  hz hs hl : HdT

stripT : Tr → Tr
stripT (ts x) = stripT x
stripT x = x

kidT : ℕ → Tr → Tr
kidT n x with stripT x
... | tl f = f n
... | y = y

hdT : Tr → HdT
hdT t0 = hz
hdT (ts _) = hs
hdT (tl _) = hl

module Wrong (S : Sib) where
  module W = PW S
  module F = PF S

  reject-wrong-fold : Reg⁰ (rdT (W.Tʷ (natL 2))) → ⊥
  reject-wrong-fold = lim-const

  -- 对照: 正确的折叠与它不同 (路径同 `path₂`, 头不同)
  pf-not-const : rdT (F.T (natL 2)) ≡ rdT (W.Tʷ (natL 2)) → ⊥
  pf-not-const e with cong (λ x → hdT (kidT 0 (kidT 0 (kidT 1 x)))) e
  ... | ()
```

## §3 静态替身: 链不爬升

`T-static` $=\psi^0(\Omega+\omega)$, 当作 $\psi_0(\Omega+\Omega)$. 它的第 $n$ 项是 $\psi^0(\Omega+n)$. `reject-static`: **不存在任何链 $y$**, 使 $T\,n\equiv\psi^0(\Omega+y_n)$ 且 $y_{n+1}\sqsupseteq\psi_0(\Omega+y_n)$. 证明: $n=1$ 的方程逼出 $y_1\equiv1$ (`P-inj`, 只比极限的第 0, 1 项); 而 $\psi_0(\Omega+y_0)$ 严格大于 $1$ (`one≺Q`). 不用 `IsPsi`, 不用 `Acc`.

`real-climb`: 真实的 `ψ⁰ (Ω₁ + Ω₁)` 过 `Climb`, 链就是折叠的链. 这是定义展开, 不算证据; 它只说明条款不是空的.

```agda
open import OCF.Align.Level using (Ordᶜ; _⊑_; _≺_; ψ⁰; ψ; add; Ω; _+_; ≺z; ≺s; ≺l; s≅; z≅; natᶜ)
import OCF.Align.Level as L
open import OCF.Align.OCFSpecAnchor using (Ω₁; Ω+)
open import OCF.Align.OCFSpecRule using (𝟏)
open import OCF.Align.OCFSpecNeg using (T-static; ΩΩ)

P Q : Ordᶜ L.zero → Ordᶜ L.zero
P y = ψ⁰ (Ω+ y)
Q y = ψ L.zero (λ r → r) (Ω+ y)

Tₛ : ℕ → Ordᶜ L.zero
Tₛ n = P (natᶜ n)

static-is-lim : T-static ≡ L.lim Tₛ
static-is-lim = refl

pick : ℕ → Ordᶜ L.zero → Ordᶜ L.zero
pick n (L.lim f) = f n
pick n x = L.zero

P-inj : ∀ y → P y ≡ P 𝟏 → y ≡ 𝟏
P-inj L.zero e with cong (pick 0) e
... | ()
P-inj (L.suc b) e = cong L.suc (lem b (cong (pick 1) e))
  where
  lem : ∀ b → P b ≡ P L.zero → b ≡ L.zero
  lem L.zero _ = refl
  lem (L.suc c) e with cong (pick 0) e
  ... | ()
  lem (L.lim h) e = ⊥-elim (lem₂ (h 0) (cong (pick 0) e))
    where
    w : Ordᶜ L.zero
    w = ψ⁰ (𝟏 {L.zero})
    notSuc : ∀ c → P c ≡ L.suc L.zero → ⊥
    notSuc L.zero ()
    notSuc (L.suc c) ()
    notSuc (L.lim h) ()
    notZero : ∀ c → P c ≡ L.zero → ⊥
    notZero L.zero ()
    notZero (L.suc c) ()
    notZero (L.lim h) ()
    lem₂ : ∀ c → P c ≡ w → ⊥
    lem₂ L.zero e with cong (pick 0) e
    ... | ()
    lem₂ (L.suc c) e = notSuc c (cong (pick 1) e)
    lem₂ (L.lim h′) e = notZero (h′ 0) (cong (pick 0) e)
P-inj (L.lim h) e = ⊥-elim (notZero (h 0) (cong (pick 0) e))
  where
  notZero : ∀ c → P c ≡ L.zero → ⊥
  notZero L.zero ()
  notZero (L.suc c) ()
  notZero (L.lim h) ()

one≺Q : ∀ x → 𝟏 {L.zero} ≺ Q x
one≺Q L.zero = ≺l 0 (≺l 2 (≺z (s≅ z≅)))
one≺Q (L.suc b) = ≺l 1 (one≺Q b)
one≺Q (L.lim h) = ≺l 0 (one≺Q (h 0))

¬1≺1 : 𝟏 {L.zero} ≺ 𝟏 {L.zero} → ⊥
¬1≺1 (≺z ())
¬1≺1 (≺s ())

open Rows {Ordᶜ L.zero} {Ordᶜ L.zero} _≡_ _⊑_ using (Climb; climb)

reject-static : ∀ s → Climb P Q s Tₛ → ⊥
reject-static s (climb y y0 eqT step) = ¬1≺1 (subst (λ u → 𝟏 {L.zero} ≺ u) (P-inj (y 1) (sym (eqT 1))) (step 0 (one≺Q (y 0))))

-- 真实的折叠: 链就是定义里的链
Rreal : ℕ → Ordᶜ L.zero
Rreal = pick′
  where
  pick′ : ℕ → Ordᶜ L.zero
  pick′ n = pick n (ψ⁰ ΩΩ)

real-climb : Climb P Q (Ω L.zero) Rreal
real-climb = climb (iter Q (Ω L.zero)) (λ h → h) (λ n → refl) (λ n h → h)
```

## §4 `ver`: 看得见的节点被压平

$\Omega_1$ 的层号在 $\Omega_2$ 的层号里有字面路径 (`lit`: 分支 $x=\Omega_1+1$, 第 0 步). `ver` 对这一对答 `rise` (`ver-rise-Ω`). `reject-ver`: `Vis` 不成立. **这是这一对的定理; 判决对一切层号满足 `Vis` 是做不到的 (`no-uniform`), 所以判据只对折叠真问到的对子说话.** 对照: `D★` 在同一对上穿透, 这是有限测试.

```agda
open import OCF.Align.InaccTreeBase using (ver; Verdict; pen; rise; Oracle; Pre; at; toLv)
open import OCF.Align.InaccModulusBase using (Nd)
open import OCF.Align.InaccTreeAccept using (L)
open import OCF.Align.InaccStrikeAccept using (Ωn)
open import OCF.Align.InaccStrikeOracle using (D★)

kind : Oracle → Lv → Lv → Vd
kind D j i with D j i
... | pen _ _ = vp
... | rise = vr

-- 这两个层号直接写出, 不读记号; `L₁-is`, `L₂-is` 说它们就是 `ver` 在 $\Omega_1,\Omega_2$ 上算出的 (`refl`)
L₁ L₂ : Lv
L₁ = IB.limᴼ IB.zero toLv
L₂ = IB.limᴼ (IB.suc IB.zero) toLv

L₁-is : L ver (Ωn 1) ≡ L₁
L₁-is = refl

L₂-is : L ver (Ωn 2) ≡ L₂
L₂-is = refl

lit : Nd L₁ L₂
lit = inj₂ (Tree.suc (IB.Ω (IB.suc IB.zero)) , inj₁ tt) , refl

reject-ver : Vis Nd (kind ver) L₁ L₂ → ⊥
reject-ver h with h lit
... | ()

-- 有限测试: 正确的判决在它自己的层号上穿透
d★-pen : kind D★ (L D★ (Ωn 1)) (L D★ (Ωn 2)) ≡ vp
d★-pen = refl
```

## §5 `HF` 的边界

**`hf-blind`: 没有闭包的树都过 `HF`.** `ver`, `PW`, 静态替身的树都没有闭包, 所以 `HF` 对它们是空的. **同头同界只管界, 不管值.** 值这一半要 `Climb`, `Vis`, 而那是折叠方程.

```agda
open import OCF.Align.TreeJudgeBase using (HF; Sub; here; ↓s; ↓l; ↓f; ↓b)
open import OCF.Free.Prefix using (Z; ĉᴸ)

emb : Tr → Z
emb t0 = Z.zero
emb (ts x) = Z.suc (emb x)
emb (tl f) = Z.lim (λ n → emb (f n))

noClo : ∀ {c t₀ g o₀ o} (t : Tr) → Sub (ĉᴸ c t₀ g o₀ o) (emb t) → ⊥
noClo t0 ()
noClo (ts x) (↓s p) = noClo x p
noClo (tl f) (↓l n p) = noClo (f n) p

hf-blind : ∀ t → HF (emb t)
hf-blind t p q _ = ⊥-elim (noClo t p)
```

## §6 `ghost` 不是空的: 最小的一对

`toy-ghost`: 外层闭包的分支 $\tau$ 里, 内层闭包的头与外层的头相同, 界是 $\tau+1$. `Ghost` 成立, 所以没有证书. `toy-fine`: 同样的树, 内层的界换成常数 1, 有证书. **两棵树只差内层的界.** 这是 `noW` 的全部内容, 去掉了折叠. 它也说明 `force-≃` 与 `ghost` 不矛盾: `force-≃` 要两边都有证书.

```agda
module Toy where
  open import OCF.Free.Level as FL using (Ordᴵ; _⊑ᴵ_; toLevel; HS; hz; hs; ⊑ᴵ-refl; s⊑; z≅; s≅; zero; suc)
  import OCF.Free.Level as FL′
  open import OCF.Free.Prefix using (_≅ᶻ_; zᶻ; sᶻ)
  open import OCF.Free.Force using (Goodᴺ; gs; gz; gc)
  open import OCF.Align.TreeJudgeBase using (Ghost; ghost; ghost₁; FP) renaming (here to hereᶠ)

  one : Ordᴵ
  one = suc zero

  hd : Z
  hd = Z.suc (Z.suc Z.zero)

  in-g : (τ : Ordᴵ) → Z
  in-g τ = ĉᴸ (suc τ) hd (λ _ _ → hd) Z.zero (λ _ _ → Z.zero)

  X-g : Z
  X-g = ĉᴸ one hd (λ _ _ → hd) Z.zero (λ τ _ → in-g τ)

  toy-ghost : Goodᴺ X-g → ⊥
  toy-ghost = ghost {t₀ = hd} {g = λ _ _ → hd} (λ τ e → ghost₁ {c′ = suc τ} {t′ = hd} {p′ = Z.zero} {g′ = λ _ _ → hd} {o′ = λ _ _ → Z.zero} hereᶠ ⊑ᴵ-refl {y = hd} hereᶠ (sᶻ (sᶻ zᶻ)))

  in-f : Z
  in-f = ĉᴸ one hd (λ _ _ → hd) Z.zero (λ _ _ → Z.zero)

  X-f : Z
  X-f = ĉᴸ one hd (λ _ _ → hd) Z.zero (λ _ _ → in-f)

  Y2 : FL′.Ordᶜ zero
  Y2 = FL′.suc (FL′.suc FL′.zero)

  hY : HS Y2
  hY = hs (hs hz)

  one⊑ : one ⊑ᴵ toLevel Y2 hY
  one⊑ = s⊑ z≅ (FL′.suc FL′.zero)

  gHd : Goodᴺ hd
  gHd = gs (gs gz)

  e2 : FL′._≅_ Y2 Y2
  e2 = FL′.s≅ (FL′.s≅ FL′.z≅)

  ⊑z : ∀ {b : FL′.Ordᶜ zero} → FL′._⊑⁰_ FL′.zero b
  ⊑z ()

  G-in : Goodᴺ in-f
  G-in = gc (λ _ → Y2) (λ _ → hY) (λ _ → one⊑) gHd e2 (λ _ → gHd) (λ _ → e2) gz (λ _ → gz) ⊑z (λ _ → ⊑z)

  toy-fine : Goodᴺ X-f
  toy-fine = gc (λ _ → Y2) (λ _ → hY) (λ _ → one⊑) gHd e2 (λ _ → gHd) (λ _ → e2) gz (λ _ → G-in) ⊑z (λ _ h → h)
```
