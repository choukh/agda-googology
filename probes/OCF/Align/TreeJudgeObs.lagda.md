# 树侧判据 (有限测试的工具): 观察树, 指纹, 同头同界的取样

> 不含记号. 结论写在 [TreeJudge](TreeJudge.lagda.md). **本文件的东西都是有限测试的工具, 不是定理.** `HF` ([TreeJudgeBase](TreeJudgeBase.lagda.md)) 量词过全部分支, $\cong$ 是互模拟. 这里取样: 极限走前 $w$ 项; 闭包走第一支与分支 $\eta=c+k$, $k<w$; $\cong$ 换成深度受限的指纹.
>
> `Obs` 是各个 `Z` 副本的公共载体: 仓库里 `Z` 有好几份 (`OCF.Free.Prefix`, `OCF.Align.Prefix`, `ScafLadderZPrefix`), 它们不互通. 每一份写一个几行的 `rd` 就能比.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.TreeJudgeObs where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; reverse; length)
open import Data.Maybe using (Maybe; just; nothing)
```

## §1 观察树

`oc b h o₀ o`: 闭包, 界读成自然数 $b$ (`toN`), 头 $h$, 第一支 $o_0$, 分支 $o\,k=o(c+k)$. 界读不成自然数时 (`toN (lim f)` 取 $f\,1$) 这是取样: 只说到这个读法.

```agda
data Obs : Set where
  o0 : Obs
  os : Obs → Obs
  ol : (ℕ → Obs) → Obs
  oc : ℕ → Obs → Obs → (ℕ → Obs) → Obs

_==_ : ℕ → ℕ → Bool
zero == zero = true
suc a == suc b = a == b
_ == _ = false

eqL : List ℕ → List ℕ → Bool
eqL [] [] = true
eqL (a ∷ x) (b ∷ y) = (a == b) ∧ eqL x y
eqL _ _ = false
```

## §2 指纹

`fp d w x`: 深度 $d$, 宽度 $w$ 的串行化, 看界. `fpn`: 不看界, 闭包读成第一支. **指纹相同不说明 $\cong$:** 深度 6 上 `t3` 出现过假警报, 深度 9 就没有了.

```agda
fp : ℕ → ℕ → Obs → List ℕ
fpL : ℕ → ℕ → ℕ → (ℕ → Obs) → List ℕ
fp zero w x = 9 ∷ []
fp (suc d) w o0 = 0 ∷ []
fp (suc d) w (os x) = 1 ∷ fp d w x
fp (suc d) w (ol f) = 2 ∷ fpL w d w f
fp (suc d) w (oc b h o₀ o) = 3 ∷ b ∷ (fp d w o₀ ++ fpL w d w o)
fpL zero d w f = []
fpL (suc n) d w f = fpL n d w f ++ fp d w (f n)

fpn : ℕ → ℕ → Obs → List ℕ
fpnL : ℕ → ℕ → ℕ → (ℕ → Obs) → List ℕ
fpn zero w x = 9 ∷ []
fpn (suc d) w o0 = 0 ∷ []
fpn (suc d) w (os x) = 1 ∷ fpn d w x
fpn (suc d) w (ol f) = 2 ∷ fpnL w d w f
fpn (suc d) w (oc b h o₀ o) = 3 ∷ fpn d w o₀
fpnL zero d w f = []
fpnL (suc n) d w f = fpnL n d w f ++ fpn d w (f n)
```

## §3 同头同界的取样

`coll d fd w`: 走树 (深度 $d$, 宽度 $w$), 收集每个闭包的路径, 界, 头的指纹 (深度 `fd`). 路径的编码: 极限项 $n$ 就是 $n$; 第一支是 500; 分支 $k$ 是 $100+k$. `hfv`: 找一对同指纹不同界. `run d fd w x` 是 **`HF` 的有限测试**: `nothing` 只说这个取样里没有; `just` 说这个取样里有一对, 头的指纹相同.

```agda
record Nd : Set where
  constructor nd
  field
    path : List ℕ
    bd   : ℕ
    hd   : List ℕ
open Nd public

coll : ℕ → ℕ → ℕ → List ℕ → Obs → List Nd
collL : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → ℕ → (ℕ → Obs) → List Nd
coll zero fd w p x = []
coll (suc d) fd w p o0 = []
coll (suc d) fd w p (os x) = coll d fd w p x
coll (suc d) fd w p (ol f) = collL w 0 d fd w p 0 f
coll (suc d) fd w p (oc b h o₀ o) =
  nd (reverse p) b (fp fd w h) ∷ (coll d fd w (500 ∷ p) o₀ ++ collL w 0 d fd w p 1 o)
collL zero s d fd w p t f = []
collL (suc n) s d fd w p t f = coll d fd w ((t * 100 + s) ∷ p) (f s) ++ collL n (suc s) d fd w p t f

data Vio : Set where
  vio : List ℕ → ℕ → List ℕ → ℕ → Vio

chk1 : Nd → List Nd → Maybe Vio
chk1 a [] = nothing
chk1 a (b ∷ r) with eqL (hd a) (hd b) ∧ (if bd a == bd b then false else true)
... | true = just (vio (path a) (bd a) (path b) (bd b))
... | false = chk1 a r

hfv : List Nd → Maybe Vio
hfv [] = nothing
hfv (a ∷ r) with chk1 a r
... | just v = just v
... | nothing = hfv r

run : ℕ → ℕ → ℕ → Obs → Maybe Vio
run d fd w x = hfv (coll d fd w [] x)

-- 取样里有多少个闭包: 测试的分母
nclo : ℕ → ℕ → Obs → ℕ
nclo d w x = length (coll d 0 w [] x)

-- 沿路径走, 取子树. 步: `lim n` 走极限项; `fst` 走第一支; `br k` 走分支 $c+k$; 后继自动剥掉
data St : Set where
  lm : ℕ → St
  fs : St
  br : ℕ → St

go : List St → Obs → Maybe Obs
go [] x = just x
go (s ∷ p) o0 = nothing
go p (os x) = go p x
go (lm n ∷ p) (ol f) = go p (f n)
go (fs ∷ p) (oc b h o₀ o) = go p o₀
go (br k ∷ p) (oc b h o₀ o) = go p (o k)
go (_ ∷ p) _ = nothing

-- 节点的形状
data Sh : Set where
  sh0 shs shl : Sh
  shc : ℕ → Sh
  shN : Sh

shape : Maybe Obs → Sh
shape nothing = shN
shape (just o0) = sh0
shape (just (os _)) = shs
shape (just (ol _)) = shl
shape (just (oc b _ _ _)) = shc b

-- 头
hdOf : Maybe Obs → Maybe Obs
hdOf (just (oc b h _ _)) = just h
hdOf _ = nothing

fpM : ℕ → ℕ → Maybe Obs → List ℕ
fpM d w nothing = 7 ∷ []
fpM d w (just x) = fp d w x

sameM : ℕ → ℕ → Maybe Obs → Maybe Obs → Bool
sameM d w x y = eqL (fpM d w x) (fpM d w y)
```

## §4 Bachmann 性质的取样

`reg d fu fd w x`: 走树, 在每个 $\omega$-极限节点上看 $h\,n$ 是否在 $h(n+1)$ 的 1-走步上, 走步预算 `fu`, 相等用不看界的指纹 `fpn`. **走步进了闭包就算超预算:** 闭包的真实第 1 项是 $o(\mathrm{lv}\,t_0)$, 这里算不出来. `bad p n`: 走步走到 $0$ 也没碰到 (在指纹意义下), 这是对 `Reg⁰` 的取样反例. `okv a b`: 命中 $a$ 次, 超预算 $b$ 次.

```agda
data Rg : Set where
  hit miss over : Rg

data Stp : Set where
  stop : Stp
  more : Obs → Stp
  blk  : Stp

step : Obs → Stp
step o0 = stop
step (os x) = more x
step (ol f) = more (f 1)
step (oc b h o₀ o) = blk

onW : ℕ → ℕ → ℕ → List ℕ → Obs → Rg
onW zero fd w fy x = over
onW (suc n) fd w fy x with step x
... | stop = miss
... | blk = over
... | more x′ with eqL fy (fpn fd w x′)
...   | true = hit
...   | false = onW n fd w fy x′

data V : Set where
  bad : List ℕ → ℕ → V
  okv : ℕ → ℕ → V

merge : V → V → V
merge (bad p n) _ = bad p n
merge _ (bad p n) = bad p n
merge (okv a b) (okv c d) = okv (a + c) (b + d)

reg : ℕ → ℕ → ℕ → ℕ → List ℕ → Obs → V
regL : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → (ℕ → Obs) → V
regk : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → (ℕ → Obs) → V
reg zero fu fd w p x = okv 0 0
reg (suc d) fu fd w p o0 = okv 0 0
reg (suc d) fu fd w p (os x) = reg d fu fd w p x
reg (suc d) fu fd w p (ol f) = regL w d fu fd w p f
reg (suc d) fu fd w p (oc b h o₀ o) = merge (reg d fu fd w (500 ∷ p) o₀) (regk w d fu fd w p o)
regk zero d fu fd w p o = okv 0 0
regk (suc n) d fu fd w p o = merge (reg d fu fd w ((100 + n) ∷ p) (o n)) (regk n d fu fd w p o)
regL zero d fu fd w p f = okv 0 0
regL (suc n) d fu fd w p f with onW fu fd w (fpn fd w (f n)) (f (suc n))
... | hit  = merge (reg d fu fd w (n ∷ p) (f n)) (merge (okv 1 0) (regL n d fu fd w p f))
... | over = merge (reg d fu fd w (n ∷ p) (f n)) (merge (okv 0 1) (regL n d fu fd w p f))
... | miss = bad (reverse p) n
```
