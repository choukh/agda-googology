# 燃料搜索派发在 ℕ 极限层号的源位置上仍折叠: `T⁺ʷ` 问到的结点链的第一步

非验收文件. 编译定理与有限测试 (`refl`), 无前提. 对一切派发目标, 源位置的层号字面是 ℕ 极限时 `dl` 折叠 (`dl-lim`). `YiLamVLost` 那个结点 (坐标 `ξa = 1 + (Tw 2 + 1)` 换成新折叠的 `Tw 2`) 在 `gK ξa` 的第 1 个分量里 (`gKc-1`), 它的链从 `top` 起, 第一步折叠 `bN top`;
`bN top` 里有位置 `pN` 上的结点 (`occP`), `pN` 的层号是 ℕ 极限 (`limP`), 目标层 `LN` 有这个层号的槽位 (`couldP`), 派发折叠 (`lostP`), 所以这个结点上的派发不完全 (`not-full`). 值的问法在 [YiDlVLost](YiDlVLost.lagda.md). 不陈述丢掉多少值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDlLost where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (lev; Way; keep; fold; Ext; R; ⌜_⌝; chain; ΨN)
open import OCF.Lean.YiLamFold using (Kfk; nrmk; nrmk-lgl; Lw; Lw-tw; lgl→Lw; w0; fin; finOf)
open import OCF.Lean.YiLamNFuel using (pol)
open import OCF.Lean.YiUniIf using (At; Full)
open import OCF.Lean.YiDlFold
open import OCF.Lean.YiDlInst using (V2; ξa; rN)
```

## 1 ℕ 极限层号的源位置一律折叠

```agda
LimL : LF → Set
LimL L = Σ (ℕ → LF) λ f → L ≡ lim f

dl-lim : ∀ k K r → LimL (lev K r) → dl k K r ≡ fold
dl-lim zero K r _ = refl
dl-lim (suc k) K r (f , e) = subst (λ L → pol (λ n → n) (suc k) L ≡ fold) (sym e) refl
dl-lim (lim h) K r (f , e) = subst (λ L → pol (λ n → n) (lim h) L ≡ fold) (sym e) refl
dl-lim (lc k g) K r (f , e) = subst (λ L → pol (λ n → n) (lc k g) L ≡ fold) (sym e) refl
```

## 2 结点出现

`Occ p ξ`: `ξ` 沿 `suc`, `lim` 的分量与结点的分支走到位置 `p` 上的结点. 左加 (`plus m x`) 保持右加数里的出现.

```agda
data Occ {M : LF} (p : Pre M) : Raw M → Set where
  here : ∀ {g} → Occ p (G.lc p g)
  inS  : ∀ {a} → Occ p a → Occ p (G.suc a)
  inL  : ∀ {f} n → Occ p (f n) → Occ p (G.lim f)
  inC  : ∀ {r g} η → Occ p (g η) → Occ p (G.lc r g)

Occ-plus : ∀ {M} {p : Pre M} x {b} → Occ p b → Occ p (plus M x b)
Occ-plus x here = here
Occ-plus x (inS o) = inS (Occ-plus x o)
Occ-plus x (inL n o) = inL n (Occ-plus x o)
Occ-plus x (inC η o) = inC η (Occ-plus x o)
```

## 3 那个结点与它的链的第一步

```agda
Vw : (η : R) → Lgl zero η → Lw ⌜ η ⌝
Vw η l = lgl→Lw zero tt w0 η l

Tt : R → Raw (tw 2)
Tt η = Ψ (tw 2) (Vw (nrmk zero η) (nrmk-lgl zero η)) (λ r → keep (nrmk zero η , nrmk-lgl zero η , r) refl) G.top

gK : R → Raw (tw 2)
gK ξ = plus (tw 2) G.top (Kfk zero Tt ξ)

a : R
a = plus zero G.top (Tw 2)

LN : LF
LN = lev (tw 2) rN

gN : Raw LN → Raw (tw 2)
gN η = Ψ (tw 2) (Vw (nrmk zero a) (nrmk-lgl zero ξa)) (λ r → keep (nrmk zero ξa , nrmk-lgl zero ξa , inj₂ r) refl) η

Tt-node : Tt ξa ≡ G.lc rN gN
Tt-node = refl

gKc : ℕ → Raw (tw 2)
gKc n = plus (tw 2) G.top (acc (λ _ z → plus (tw 2) z (Tt ξa)) (Kfk zero Tt a) n)

gK-form : gK ξa ≡ G.lim gKc
gK-form = refl

bN : Raw LN → Raw (tw 2)
bN η = plus (tw 2) G.top (plus (tw 2) (Kfk zero Tt a) (gN η))

gKc-1 : gKc 1 ≡ G.lc rN bN
gKc-1 = refl

-- 外部派发折叠时, 这个结点的值是链的极限; 链在 LN 层, 从 top 起, 每步折叠 bN 到 LN.
Gk : Raw LN → Raw LN
Gk η = Ψ LN V2 (cmpw V2 rN) (bN η)

node-fold : Ψ zero V2 (λ _ → fold) (G.lc rN bN) ≡ G.lim (λ n → Ψ zero V2 (λ _ → fold) (bN (chain LN Gk n)))
node-fold = refl
```

## 4 第一步里的 ℕ 极限层号位置

位置 `s` 由有限的字面搜索找出 (`LN` 的分量 0, 1, 0, 0, 0, 再进 `suc` 一层取结点层号).

```agda
s : Pre LN
s = 0 , 1 , 0 , 0 , 0 , inj₂ (inj₁ tt)

pN : Pre (tw 2)
pN = nrmk zero ξa , nrmk-lgl zero ξa , inj₂ s

occN : Occ pN (gN G.top)
occN = inL 0 (inL 1 (Occ-plus _ (inL 0 (inL 0 (inL 0 (inC G.top here))))))

occP : Occ pN (bN G.top)
occP = Occ-plus G.top (Occ-plus (Kfk zero Tt a) occN)

limP : LimL (lev (tw 2) pN)
limP = _ , refl

couldP : At LN (lev (tw 2) pN)
couldP = s , refl

lostP : cmpw V2 rN pN ≡ fold
lostP = refl

lostP′ : cmpw V2 rN pN ≡ fold
lostP′ = dl-lim LN (tw 2) pN limP

not-full : Full LN (tw 2) (cmpw V2 rN) → ⊥
not-full full = full pN couldP
```

`pN` 的层号是分量字面有限的 ℕ 极限 (有限测试: 分量 0, 1, 2, 5 是 `fin 2`, `fin 5`, `fin 9`, `fin 27`); 判断: 它是 ω 那一层, `pN` 上的结点是 Ω_{ω+1} 型的, 目标层 `LN` 是 `⌜nrmk (1 + Tw 2)⌝`.

```agda
comp : LF → ℕ → LF
comp (lim f) n = f n
comp _ n = zero

LP-0 : comp (lev (tw 2) pN) 0 ≡ fin 2
LP-0 = refl

LP-1 : comp (lev (tw 2) pN) 1 ≡ fin 5
LP-1 = refl

LP-2 : comp (lev (tw 2) pN) 2 ≡ fin 9
LP-2 = refl

LP-5 : finOf (comp (lev (tw 2) pN) 5) ≡ just (27 , refl)
LP-5 = refl
```
