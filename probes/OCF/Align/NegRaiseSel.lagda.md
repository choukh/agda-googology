# NegRaise (三): 选择子形状推出 LPO; 高度版 `RaiseB S` 的边界 (对一切 `S`)

> 不含记号. 入口 [NegRaise](NegRaise.lagda.md). 导入接口 [RaiseIf](RaiseIf.lagda.md), 不改它. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 1. **`sel1→LPO` (定理).** 若 `RaiseA` 在 $a=1$ 处是**选择子** (对一切合法 $v$, 可判定地 $R\,1\,v\equiv 1$ 或 $R\,1\,v\equiv v$), 则 LPO. 族: $v_\alpha=\lim_n b_n$, $b_n=1$ 若 $\alpha$ 的前 $n+1$ 位见过 `true`, 否则 $0$; 合法. $R\equiv v$ 时 `R-lo` 给 $1\lhd v_\alpha$, 读出 `true` 的位置; $R\equiv 1$ 时 `R-hi` 说 $\alpha$ 某处为真就有 $v_\alpha\lhd 1$, 不可能, 所以 $\alpha$ 恒假. 推论 `sel→LPO` (处处是选择子).
>    对照: [NegRaiseFin](NegRaiseFin.lagda.md) 的 `raiseFin 1` 在 $a=1$ 处是构造, 它的输出是 $\lim(1,\dots,1,v,v,\dots)$, 不是 $1$ 也不是 $v$. 所以 "$R$ 的值是 $a$ 或 $v$" 这一条是多出来的要求, 不是 `RaiseA` 逼出的. 构造一路的 `RaiseCBd.Rᵇ` 在带公共上界时是选择子 (`Rᵇ-cases`); 本条说这个形状不能推广到不带上界的定义域.
> 2. **`selᴮ1→LPO` (定理, 对一切 `S` 与一个合法世界).** 高度版同样.
> 3. **`no-alwaysᴮ`, `no-mono0ᴮ` (定理, 对一切 `S` 与一个合法世界).** `RaiseB S` 加 "$v\lhd_w R\,a\,v$ 无条件" 或 "$R\,0\,v\lhd_w R\,a\,v$" 矛盾 (撞 `no-joinᴮ`).
> 4. **`inflateᴮ`, `head-sucᴮ` (盲).** 高度版的律同样对输出向上封闭.
>
> 前提 "有一个合法世界" 的实例: `S₀` 的世界 $0$ (`lw-S₀`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegRaiseSel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Barrier using (LPO)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerNeg using (evᴴ; odᴴ; Lg-ev; Lg-od; no-joinᴮ)
open import OCF.Align.RaiseIf using (RaiseA; R; R-lo; R-hi; R-lg; RaiseB; Rᴮ; Rᴮ-lo; Rᴮ-hi; Rᴮ-lg)
open import OCF.Align.NegRaiseFin using (seen; seen-mono; seen-intro; ∨-e)
```

## §0 `seen` 读出位置

```agda
seen-sound : ∀ α n → seen α n ≡ true → Σ ℕ (λ k → α k ≡ true)
seen-sound α zero e = zero , e
seen-sound α (suc n) e with ∨-e (seen α n) e
... | inj₁ e′ = seen-sound α n e′
... | inj₂ e′ = suc n , e′
```

## §1 `A` 上: 选择子推出 LPO

```agda
one : A
one = asuc azero

bitA : Bool → A
bitA true = one
bitA false = azero

vA : (ℕ → Bool) → A
vA α = alim (λ n → bitA (seen α n))

stepA : ∀ b b′ → (b ≡ true → b′ ≡ true) → bitA b ⊲ bitA b′
stepA false false _ = C.self
stepA false true _ = C.suc C.self
stepA true true _ = C.self
stepA true false h with h refl
... | ()

lgA : ∀ b → Lg (bitA b)
lgA true = tt
lgA false = tt

Lg-vA : ∀ α → Lg (vA α)
Lg-vA α = (λ n → stepA (seen α n) (seen α (suc n)) (seen-mono α n)) , (λ n → lgA (seen α n))

bit-true : ∀ b → one ⊲ bitA b → b ≡ true
bit-true true _ = refl
bit-true false ()

decodeA : ∀ α → one ⊲ vA α → Σ ℕ (λ k → α k ≡ true)
decodeA α (C.lim n p) = seen-sound α n (bit-true (seen α n) p)

encA : ∀ α k → α k ≡ true → one ⊲ vA α
encA α k e = C.lim k (subst (λ b → one ⊲ bitA b) (sym (seen-intro α k e)) C.self)

no-lim1 : ∀ {f} → ¬ (alim f ⊲ one)
no-lim1 (C.suc ())

Sel1 : RaiseA → Set
Sel1 ρ = ∀ {v} → Lg v → (R ρ one v ≡ one) ⊎ (R ρ one v ≡ v)

sel1→LPO : ∀ ρ → Sel1 ρ → LPO
sel1→LPO ρ s α with s (Lg-vA α)
... | inj₂ e = inj₁ (decodeA α (subst (one ⊲_) e (R-lo ρ tt (Lg-vA α))))
... | inj₁ e = inj₂ allF
  where
  allF : ∀ k → α k ≡ false
  allF k with α k in eqk
  ... | false = refl
  ... | true = ⊥-elim (no-lim1 (subst (vA α ⊲_) e (R-hi ρ tt (Lg-vA α) (encA α k eqk))))

Sel : RaiseA → Set
Sel ρ = ∀ {a v} → Lg a → Lg v → (R ρ a v ≡ a) ⊎ (R ρ a v ≡ v)

sel→LPO : ∀ ρ → Sel ρ → LPO
sel→LPO ρ s = sel1→LPO ρ (λ lv → s tt lv)
```

## §2 高度上: 选择子推出 LPO (对一切 `S`)

```agda
module OnS (S : KS) (w₀ : Wd S) (lw₀ : LgW S w₀) where
  oneᴮ : HB S
  oneᴮ = hs hz

  bitH : Bool → HB S
  bitH true = oneᴮ
  bitH false = hz

  vB : (ℕ → Bool) → HB S
  vB α = hl (λ n → bitH (seen α n))

  stepH : ∀ {w} b b′ → (b ≡ true → b′ ≡ true) → bitH b ⊲[ w ] bitH b′
  stepH false false _ = hself
  stepH false true _ = hsuc hself
  stepH true true _ = hself
  stepH true false h with h refl
  ... | ()

  lgH : ∀ b → LgB (bitH b)
  lgH true = tt
  lgH false = tt

  Lg-vB : ∀ α → LgB (vB α)
  Lg-vB α = (λ n → stepH (seen α n) (seen α (suc n)) (seen-mono α n)) , (λ n → lgH (seen α n))

  bit-trueᴮ : ∀ {w} b → oneᴮ ⊲[ w ] bitH b → b ≡ true
  bit-trueᴮ true _ = refl
  bit-trueᴮ false ()

  decodeB : ∀ {w} α → oneᴮ ⊲[ w ] vB α → Σ ℕ (λ k → α k ≡ true)
  decodeB α (hlim n p) = seen-sound α n (bit-trueᴮ (seen α n) p)

  encB : ∀ {w} α k → α k ≡ true → oneᴮ ⊲[ w ] vB α
  encB {w} α k e = hlim k (subst (λ b → oneᴮ ⊲[ w ] bitH b) (sym (seen-intro α k e)) hself)

  no-lim1ᴮ : ∀ {w f} → ¬ (hl f ⊲[ w ] oneᴮ)
  no-lim1ᴮ (hsuc ())

  Selᴮ1 : RaiseB S → Set
  Selᴮ1 ρ = ∀ {v} → LgB v → (Rᴮ ρ oneᴮ v ≡ oneᴮ) ⊎ (Rᴮ ρ oneᴮ v ≡ v)

  selᴮ1→LPO : ∀ ρ → Selᴮ1 ρ → LPO
  selᴮ1→LPO ρ s α with s (Lg-vB α)
  ... | inj₂ e = inj₁ (decodeB α (subst (oneᴮ ⊲[ w₀ ]_) e (Rᴮ-lo ρ lw₀ tt (Lg-vB α))))
  ... | inj₁ e = inj₂ allF
    where
    allF : ∀ k → α k ≡ false
    allF k with α k in eqk
    ... | false = refl
    ... | true = ⊥-elim (no-lim1ᴮ (subst (vB α ⊲[ w₀ ]_) e (Rᴮ-hi ρ lw₀ tt (Lg-vB α) (encB α k eqk))))
```

## §3 高度上的边界 (对一切 `S`)

```agda
  EVᴮ ODᴮ : HB S
  EVᴮ = hl evᴴ
  ODᴮ = hl odᴴ

  bothᴮ : ∀ {L} → LgB L → EVᴮ ⊲[ w₀ ] L → ODᴮ ⊲[ w₀ ] L → ⊥
  bothᴮ {L} l p q = no-joinᴮ lw₀ (L , l , p , q)

  Alwaysᴮ : RaiseB S → Set
  Alwaysᴮ ρ = ∀ {a v w} → LgW S w → LgB a → LgB v → v ⊲[ w ] Rᴮ ρ a v

  no-alwaysᴮ : ∀ ρ → ¬ Alwaysᴮ ρ
  no-alwaysᴮ ρ al = bothᴮ (Rᴮ-lg ρ Lg-ev Lg-od) (Rᴮ-lo ρ lw₀ Lg-ev Lg-od) (al lw₀ Lg-ev Lg-od)

  Mono0ᴮ : RaiseB S → Set
  Mono0ᴮ ρ = ∀ {a v w} → LgW S w → LgB a → LgB v → Rᴮ ρ hz v ⊲[ w ] Rᴮ ρ a v

  no-mono0ᴮ : ∀ ρ → ¬ Mono0ᴮ ρ
  no-mono0ᴮ ρ m = bothᴮ (Rᴮ-lg ρ Lg-ev Lg-od) (Rᴮ-lo ρ lw₀ Lg-ev Lg-od)
    (⊲ᴮ-tr (Rᴮ-hi ρ lw₀ tt Lg-od (z⊲ᴮ ODᴮ)) (m lw₀ Lg-ev Lg-od))
```

## §4 盲: 高度版对输出向上封闭

```agda
module _ {S : KS} where
  inflateᴮ : RaiseB S → (F : HB S → HB S) → (∀ {w} x → x ⊲[ w ] F x) → (∀ {x} → LgB x → LgB (F x)) → RaiseB S
  inflateᴮ ρ F up lg = record
    { Rᴮ = λ a v → F (Rᴮ ρ a v)
    ; Rᴮ-lo = λ lw la lv → ⊲ᴮ-tr (Rᴮ-lo ρ lw la lv) (up _)
    ; Rᴮ-hi = λ lw la lv p → ⊲ᴮ-tr (Rᴮ-hi ρ lw la lv p) (up _)
    ; Rᴮ-lg = λ la lv → lg (Rᴮ-lg ρ la lv) }

  head-sucᴮ : RaiseB S → Σ (RaiseB S) (λ ρ′ → ∀ a v → Σ (HB S) (λ y → Rᴮ ρ′ a v ≡ hs y))
  head-sucᴮ ρ = inflateᴮ ρ hs (λ x → hsuc hself) (λ l → l) , λ a v → Rᴮ ρ a v , refl
```

## §5 前提实例

```agda
-- S₀ 有合法世界 0
lw-S₀ : LgW S₀ azero
lw-S₀ = tt

-- 选择子与三条律中的两条可同时满足: R a v = a (R-lo, R-lg), R a v = v (R-hi, R-lg)
fst-sel1 : ∀ {v} → (one ≡ one) ⊎ (one ≡ v)
fst-sel1 = inj₁ refl

snd-sel1 : ∀ {v} → (v ≡ one) ⊎ (v ≡ v)
snd-sel1 = inj₂ refl

-- Lg-vA: 族里每一棵都合法 (上面已证); 例: α 恒假时 1 不是 v 的第一位置
none : ∀ α → (∀ n → seen α n ≡ false) → ¬ (one ⊲ vA α)
none α h (C.lim n p) = f≢t (h n) (bit-true (seen α n) p)
  where
  f≢t : ∀ {b} → b ≡ false → b ≡ true → ⊥
  f≢t refl ()
```

## §6 结论 (按档)

- **[定理]** `sel1→LPO`, `sel→LPO` (`A`); `OnS.selᴮ1→LPO` (一切 `S`, 一个合法世界): 选择子形状推出 LPO.
- **[定理]** `OnS.no-alwaysᴮ`, `OnS.no-mono0ᴮ`: 高度版的两条边界 (`A` 版的同名定理在 [NegRaiseBnd](NegRaiseBnd.lagda.md), 构造一路也有 `RaiseCBase.no-always`).
- **[定理, 盲]** `inflateᴮ`, `head-sucᴮ`.
- **[定理, 前提实例]** `lw-S₀`, `fst-sel1`, `snd-sel1`, `Lg-vA`, `OnS.Lg-vB`, `none`.
- **[判断]** 选择子形状经典地可满足 (构造一路 `dec→Raise` 的实例就是选择子), 所以这条只说 "选择子要 LPO", 不说 `RaiseA` 要 LPO; [NegRaiseFin](NegRaiseFin.lagda.md) 的 `raiseFin 1` 在 $a=1$ 处不是选择子而是构造.
