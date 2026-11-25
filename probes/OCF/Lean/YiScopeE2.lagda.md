# 实验 E2: `T⁺ʷ` 链第一步里 ℕ 极限层号的结点在作用域块上保留

验收文件 (对照 [YiDlLost](YiDlLost.lagda.md), 不导入旧块). 判决: 有限测试 (`refl` 与构造出的出现证据), 无前提. 结果: **保留**.
`T⁺ʷ` 的链的第 1 点 `γ₁` 在分支 `ξ = suc (1 + Tw 2)` 的第 1 个分量里有孩子 `ξ` 根上的结点 (`nodeN`, 对应 `gKc-1` 的 `lc rN bN`); 它折到零层时的链在 `LN` 层, 链步 `Gk` 把分支折到 `LN` (`node-fold`).
第一步的源 `bN (top LN)` 在作用域 `ξ, tt, sP` 上有结点 (`occP`), 它的下标层是 ℕ 极限 (`limP`); 输出 `Gk (top LN)` 在 `LN` 的作用域 `sP` 上有结点 (`keptP`), 分支是源分支的 `In` (`kept-branch`).
不陈述值; 新块的 `Tw 2` 与旧块的不是同一棵树, 这里对照的是同一构造下的对应物.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiScopeE2 where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiScopeCore
open import OCF.Lean.YiScopeFold
```

## 1 结点的出现

`At q t s h`: 作用域 `q` 的树 `t` 沿 `suc`, `lim` 的分量, 结点的分支与 `into` 走到作用域 `s` 上分支为 `h` 的结点. 不经过 `up`.

```agda
data At {X K} : (q : Path K) → Tr X K q → (s : Path K) → (Dom K s → Tr X K s) → Set where
  here : ∀ {q r h} → At q (G.nd r h) q h
  inS  : ∀ {q a s h} → At q a s h → At q (G.suc a) s h
  inL  : ∀ {q f s h} n → At q (f n) s h → At q (G.lim f) s h
  inC  : ∀ {q r b s h} η → At q (b η) s h → At q (G.nd r b) s h
  inI  : ∀ {q c t s h} → At (sub K q c) t s h → At q (G.into c t) s h

Node : ∀ {X K} (q : Path K) → Tr X K q → Path K → Set
Node {X} {K} q t s = Σ (Dom K s → Tr X K s) (At q t s)
```

## 2 链与那个结点

```agda
K2 K⁺ : Level
K2 = tw 2
K⁺ = sucᴸ K2

hK : Raw K2 → Raw K⁺
hK η = plus G.zero (G.into tt (un one (λ _ → K2) tt ⊥-elim root η))

stp : Raw K2 → Raw K2
stp γ = F ⊥-elim K⁺ K2 kp (top K2 G.zero) (hK γ)

T⁺ʷ-form : T⁺ʷ ≡ G.lim (λ n → F ⊥-elim K⁺ zero col (top zero G.zero) (hK (chain K2 stp n)))
T⁺ʷ-form = refl

γ₁ : Raw K2
γ₁ = chain K2 stp 1

a′ ξ : Raw zero
a′ = plus (G.suc G.zero) (Tw 2)
ξ = G.suc a′

LN : Level
LN = rb zero root a′

nodeN : Node root γ₁ (down ξ root)
nodeN = _ , inC ξ (inL 1 (inI here))

bN : Raw LN → Tr ⊥ K2 (down ξ root)
bN = proj₁ nodeN

Gk : Raw LN → Raw LN
Gk δ = F (λ v → v) (sucᴸ LN) LN kp (top LN G.zero) (dn ⊥-elim K2 (down ξ root) (bN δ))

node-fold : ∀ b → F ⊥-elim K2 zero col b (G.into ξ (G.nd tt bN)) ≡
  G.lim (λ n → F (λ v → v) (sucᴸ LN) zero col b (dn ⊥-elim K2 (down ξ root) (bN (chain LN Gk n))))
node-fold b = refl
```

## 3 第一步: 源里的结点, 它的下标层, 输出里的结点

```agda
sP : Path LN
sP = down 0 (down 1 (down 0 (down 1 (down 0 root))))

occP : Node (down ξ root) (bN (top LN G.zero)) (down ξ (down tt sP))
occP = _ , inI (inL 0 (inI (inL 1 (inI (inL 0 (inI (inL 1 (inI (inL 0 (inI here))))))))))

at : ∀ K → Path K → Level
at K root = K
at zero (inj₂ ())
at (sup S g) (down c p) = at (g c) p

SucLim : Level → Set
SucLim (sup one g) with g tt
... | sup nat _ = ⊤
... | _ = ⊥
SucLim _ = ⊥

limP : SucLim (at LN sP)
limP = tt

keptP : Node root (Gk (top LN G.zero)) sP
keptP = _ , inL 0 (inI (inL 1 (inI (inL 0 (inI (inL 1 (inI (inL 0 (inI here)))))))))

kept-branch : proj₁ keptP ≡
  (λ η → In (λ v → v) (sucᴸ LN) (down tt sP) (top LN G.zero) (dn ⊥-elim K2 (down ξ (down tt sP)) (proj₁ occP η)))
kept-branch = refl
```
