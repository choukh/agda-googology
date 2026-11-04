# 严格列 (十): 否定与第一个障碍

> 入口 [TLCode](TLCode.lagda.md). **判决: 下面每条都只否定写明的陈述, 都不否定 "输出带证书" 这条路线.**
>
> | 定理 | 陈述 | 只否定什么 | 前提可满足吗 |
> | --- | --- | --- | --- |
> | `exact→LPO` | 每个 `Ordᴵ` 都有 `Lit` 的码, 值互相 `≼`, 则 LPO | **统一地**把任意 `Ordᴵ` 变成带证书的精确码 (`viewE→LPO` 在这条路线上的形状) | `exact-Lit`: 带证书的 $t$ 自己满足; `Str→Lit-val`: 带证书 `Str` 的也满足 |
> | `binder→LPO` | `ŝ` 的绑定 (`c = zero`) 的每一支都有精确的带证书的高度, 则 LPO | 数据树 `tH` 不改绑定类型, 只把 `⌈η⌉` 换成精确码 | 同上, 带证书的 $\eta$ 上满足 |
> | `no-Lit-deg` | $\alpha_0=\lim(0,0,\dots)$ 没有 `Lit` | 退化的极限进 `HL`. 这是证书的作用 | 不适用 |
> | `no-Good→Str` | 不是每个 `Goodᴺ` 的层号都 `Str` | 只由 `Goodᴺ` 读出严格性: `gl` 的步进只有 `⊑⁰` | 不适用 |
> | `no-Str-out` | 对一切 `HtB`, 一切 $m$: 退化的 $\alpha_0=\lim(0,0,\dots)$ 那一行的层号不 `Str` | "对一切 $\alpha$, 输出都严格". 不说 $\alpha$ 严格时 | 这一行本身是合法的树, 有 `Goodᴺ` |
> | `ofStr` | 若每个输出的层号 `Str`, 则有 `Out` (精确) | 这是条件定理, 不是否定 | 前提未证 |
>
> **回答: `viewE→LPO` 挡不挡回灌?** 它挡统一的转换 (`exact→LPO`), 不挡这条路线. 回灌只对折叠的输出取码, 输出不是任意的 `Ordᴵ`, 而 `T⊤` 的链只用 $\alpha=0$. 所以要的是一条关于输出的定理 (`LitOut` 或 `StrOut`), 不是一个转换函数. 这条定理现在没有: `Goodᴺ` 不够 (`no-Good→Str`), 要跟踪输入的严格性 (`no-Str-out`). 未走通, 不是否定.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLCodeNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Free.Level hiding (up; sim; out) renaming (z≅ to z≅ᴵ)
open import Data.Bool using (Bool; true; false)
open import OCF.Free.Prefix using (Z; toZ)
open import OCF.Free.Eq using (_≅ᶻ_; ≅ᶻ-sym; toZ-≅)
open import OCF.Free.Force using (Goodᴺ; gz; gl; forceᴺ; forceᴺ-≅; forceᴺ-HS)
open import OCF.Free.Floor using (Ev)
open import OCF.Free.Class using (lvG)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdBase using (HtB)
open import OCF.Align.LadderOrdNeg using (LPO; 𝕋; any; any-true; true-any; b2o)
open import OCF.Align.LadderOrdStr using (Str; code; sl)
open import OCF.Align.TLCodeLit
open import OCF.Align.TLCodeLe
open import OCF.Align.TLCodeAccept using (lv₀; Lv; Str→Lit; Str→Lit-val)
open import OCF.Align.TLCodeCert using (ev₀)
open import OCF.Align.TLCodeFeed using (LC; lc; ⟦_⟧; cert; module 𝕋ʷ)
import OCF.Align.LadderOrdTree
import OCF.Align.LadderOrdRel
import OCF.Align.LadderOrdMain
```

## §1 统一的转换推出 LPO

```agda
Exact : Ordᴵ → Set
Exact η = Σ Ordᴵ λ η′ → Lit η′ × Eqv η′ η

s≼0 : ∀ {a} → suc a ≼ zero → ⊥
s≼0 ()

ex : ∀ (h : ℕ → Bool) {a} → suc a ≼ 𝕋 h → Σ ℕ λ j → h j ≡ true
ex h (l≼ʳ n y) with any h n in e
... | true = any-true h n e
... | false = ⊥-elim (s≼0 y)

fls : ∀ (h : ℕ → Bool) → 𝕋 h ≼ zero → ∀ n → h n ≡ false
fls h (l≼ k) n with h n in e
... | false = refl
... | true = ⊥-elim (s≼0 (subst (λ x → b2o x ≼ zero) (true-any h n e) (k n)))

exact→LPO : (∀ η → Exact η) → LPO
exact→LPO x h with x (𝕋 h)
... | _ , lz , (_ , k) = inj₂ (fls h k)
... | _ , ls _ , (u , _) = inj₁ (ex h u)
... | _ , ll hf hr , (u , _) = inj₁ (ex h (≼-trans (l≼ʳ 1 (<→s≼ (hr 0))) u))

-- 前提在带证书的 Ordᴵ 上成立
exact-Lit : ∀ {t} → Lit t → Exact t
exact-Lit {t} h = t , h , (≼-refl t , ≼-refl t)

exact-Str : ∀ {η} → Str η → Exact η
exact-Str h = _ , Str→Lit h , Str→Lit-val h
```

`ŝ` 的绑定 (数据树 `tH` 经 `ψ̄ᵀ` 落成的就是这个, [CrossMTop](CrossMTop.lagda.md): `ŝA 0 zero _ (λ η d → …)`) 要对**任意**的 $\eta$ 给一支. 那里的世界如果要精确且带证书, 就是下面的前提. 这一条否定的是 "`ŝ` 的绑定不变, 分支的高度换成精确的带证书的码". 不否定改绑定的类型 (绑定带证书的码, 要动 `Ordˢ`, `Z`, `Goodᴺ`).

```agda
binder→LPO : ((η : Ordᴵ) → zero ⊑ᴵ η → Exact η) → LPO
binder→LPO w = exact→LPO (λ η → w η z⊑)
```

## §2 `Goodᴺ` 不给严格性

```agda
no-Good→Str : (∀ {x} (G : Goodᴺ x) → Str (lvG G)) → ⊥
no-Good→Str k with k (gl {f = λ _ → Z.zero} (λ _ → gz) (λ _ q → q))
... | sl hf hr = ≺ᴵ-irrefl (hr 0)
```

## §3 输入不严格, 输出就不严格

这一行是合法的树. 两项的树互相模拟, 所以证书 `sl` 的步进给出 $\prec$ 自反.

```agda
lim-tie : ∀ (f : ℕ → Z) (G : Goodᴺ (Z.lim f)) → f 0 ≅ᶻ f 1 → Str (lvG G) → ⊥
lim-tie f (gl G st) e (sl hf hr) =
  ≺ᴵ-irrefl (≺ᴵ-respʳ (hr 0) (toLevel-≅ (forceᴺ-HS _ (G 1)) (forceᴺ-HS _ (G 0)) (forceᴺ-≅ (≅ᶻ-sym e) (G 1) (G 0))))

α₀ : Ordᴵ
α₀ = lim (λ _ → zero) (λ _ → z⊑)

-- 证书确实挡住退化的极限: 这个结构只接受带证书的码
no-Lit-deg : Lit α₀ → ⊥
no-Lit-deg (ll hf hr) with hr 0
... | ()

module Out0 (𝕊 : HtB) (m : HtB.Ht 𝕊) where
  open OCF.Align.LadderOrdTree 𝕊
  open OCF.Align.LadderOrdRel 𝕊
  open OCF.Align.LadderOrdMain 𝕊 using (GᴺTᵠ)

  Fe : ℕ → Q m α₀ Fl (κ Fl)
  Fe n = omk (self n) (FΩ m (ΩI m) zero) (ι (self n) (FΩ m (ΩI m) zero))

  R01 : Rq m α₀ α₀ (Fe 0) (Fe 1)
  R01 = rob {r = self 0} {r′ = self 1} z≅ᴵ (RΩ̇ m z≅ᴵ) (R-ι (self 0) (self 1) (RΩ̇ m z≅ᴵ))

  e01 : toZ (ψ̄ᵠ ok₀ (λ i h r → ok₀ i) (Fe 0) ev₀ zero) ≅ᶻ toZ (ψ̄ᵠ ok₀ (λ i h r → ok₀ i) (Fe 1) ev₀ zero)
  e01 = toZ-≅ (R→≈ᵠ R01 ok₀ (λ i h r → ok₀ i) ok₀ (λ i h r → ok₀ i) ev₀ zero ev₀ zero z≅ᴵ)

  no-Str-out : Str (lvG (GᴺTᵠ m α₀ ev₀ zero)) → ⊥
  no-Str-out = lim-tie _ (GᴺTᵠ m α₀ ev₀ zero) e01
```

## §4 条件定理: 输出 `Str` 就够了

```agda
StrOut : Set
StrOut = ∀ c → Str (𝕋ʷ.ly c)

ofStr : StrOut → 𝕋ʷ.Out
ofStr x = 𝕋ʷ.mkOut (λ c → lc _ (Str→Lit (x c))) (λ c → proj₂ (Str→Lit-val (x c)))
```
