# MLM 的规则系统，作为数据

[RESEARCH.md](../RESEARCH.md) §122。这是核心目标第一段「形式化类型宇宙」的落实：把 Setzer 的 MLM（mahlo.pdf **Definition 4.1、4.3**，印刷页 8–11，读图转写）写成 Agda 数据——签名、b-对象语法、判断、规则模式。**不是**在 Agda 里实现一个 Mahlo 宇宙（那在 `--safe` 下做不到，见 §122.2），而是把**被分析的对象理论**忠实地摆在提取器面前。

提取器 [`Extract`](Extract.lagda.md) 只对这里的数据做句法分析。凡它读出的参数，都能回溯到本文件的某条规则。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Mahlo.Object.Rules where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Product.Base using (_×_; _,_)
open import Data.String.Base using (String)
```

## 1. 签名（Definition 4.1(a)）

原文按四组给出：项构造子、U-宇宙项构造子、V-宇宙项构造子、Mahlo 项构造子；另有类型构造子。ℕ 索引的族（\(l_k\)、\(\mathrm N_k\)、\(\widehat{\mathrm N}_k\)、\(\mathrm C_n\)）保留索引。

```agda
data Sym : Set where
  -- 项构造子（元数见 arity）
  c0 : Sym ; cl : ℕ → ℕ → Sym            -- 0；l_k（l<k）
  cS ci cj cp0 cp1 cr cLam : Sym         -- S i j p₀ p₁ r λ
  cE cp csup cR cAp cJ : Sym             -- E p sup R Ap J
  cD cP : Sym ; cC : ℕ → Sym             -- D P C_n
  -- U-宇宙项构造子
  uN : Sym ; uNk : ℕ → Sym ; u+ uΠ uΣ uW uI : Sym
  -- V-宇宙项构造子
  vN : Sym ; vNk : ℕ → Sym ; v+ vΠ vΣ vW vI : Sym
  -- Mahlo 项构造子
  mU mS mRes0 mRes1 : Sym
  -- 类型构造子
  tNk : ℕ → Sym ; tN t+ tΠ tΣ tW tI tV tT tU : Sym

arity : Sym → ℕ
arity c0 = 0 ; arity (cl _ _) = 0
arity cS = 1 ; arity ci = 1 ; arity cj = 1 ; arity cp0 = 1 ; arity cp1 = 1
arity cr = 1 ; arity cLam = 1
arity cE = 2 ; arity cp = 2 ; arity csup = 2 ; arity cR = 2 ; arity cAp = 2 ; arity cJ = 2
arity cD = 3 ; arity cP = 3 ; arity (cC n) = suc n
arity uN = 2 ; arity (uNk _) = 2 ; arity u+ = 4 ; arity uΠ = 4 ; arity uΣ = 4 ; arity uW = 4 ; arity uI = 5
arity vN = 0 ; arity (vNk _) = 0 ; arity v+ = 2 ; arity vΠ = 2 ; arity vΣ = 2 ; arity vW = 2 ; arity vI = 3
arity mU = 2 ; arity mS = 3 ; arity mRes0 = 4 ; arity mRes1 = 5
arity (tNk _) = 0 ; arity tN = 0 ; arity t+ = 2 ; arity tΠ = 2 ; arity tΣ = 2
arity tW = 2 ; arity tI = 3 ; arity tV = 0 ; arity tT = 1 ; arity tU = 2

```

`Definition 4.6(b)` 的对应 \(\gamma_v\)：基类型构造子 ↔ 宇宙代码构造子。提取器用它判断「新宇宙对基构造子是否封闭」。

```agda
record Sig : Set where
  constructor mkSig
  field
    tyCons : List Sym          -- 类型构造子
    tmCons : List Sym          -- 项构造子（含三组宇宙构造子）
    -- γ：基类型构造子 ↦ (U-代码构造子 , V-代码构造子)，Def 4.6(b)(e)
    γ      : List (Sym × Sym × Sym)

mlmSig : Sig
mlmSig = mkSig
  (tNk 0 ∷ tNk 1 ∷ tNk 2 ∷ tN ∷ t+ ∷ tΠ ∷ tΣ ∷ tW ∷ tI ∷ tV ∷ tT ∷ tU ∷ [])
  (c0 ∷ cl 0 1 ∷ cS ∷ ci ∷ cj ∷ cp0 ∷ cp1 ∷ cr ∷ cLam ∷ cE ∷ cp ∷ csup ∷ cR ∷ cAp ∷ cJ
   ∷ cD ∷ cP ∷ cC 2
   ∷ uN ∷ uNk 0 ∷ u+ ∷ uΠ ∷ uΣ ∷ uW ∷ uI
   ∷ vN ∷ vNk 0 ∷ v+ ∷ vΠ ∷ vΣ ∷ vW ∷ vI
   ∷ mU ∷ mS ∷ mRes0 ∷ mRes1 ∷ [])
  ((tN , uN , vN) ∷ (tNk 0 , uNk 0 , vNk 0) ∷ (t+ , u+ , v+) ∷ (tΠ , uΠ , vΠ)
   ∷ (tΣ , uΣ , vΣ) ∷ (tW , uW , vW) ∷ (tI , uI , vI) ∷ [])
```

（ℕ 索引族只列有限个代表；`arity` 对全族有定义。）

## 2. b-对象（Definition 4.1(b)）与规则模式里的元变量

原文：b-对象是变量、\((x_1,\dots,x_n)b\)、\(C(b_1,\dots,b_n)\)。规则是**模式**（\(r,s,t,f,g\) 等在规则里是 m-项占位符），故再加元变量：`meta m args` 是元变量作用于实参（原文写 \(f(x,y)\)，即代换），`mvar m` 是未作用的 b-对象本身（原文写 \(\widehat{\mathrm U}_{f,g}\) 里的 \(f\)）。

```agda
Var  = ℕ
Meta = ℕ

data B : Set where
  var  : Var → B
  abs  : List Var → B → B          -- (x₁,…,xₙ)b
  con  : Sym → List B → B          -- C(b₁,…,bₙ)
  meta : Meta → List B → B         -- f(x,y)：元变量作用于实参
  mvar : Meta → B                  -- f 本身（作为 b-对象参数）
```

判断（Definition 4.1(g)）：`context`、\(A=B\)、\(s=t:A\)。原文把 \(A\ \mathrm{type}\) 与 \(s:A\) 当作 \(A=A\)、\(s=s:A\) 的缩写（页 10 第一条修改）。

```agda
data Judg : Set where
  ctx  : Judg
  tyEq : B → B → Judg              -- A = B
  tmEq : B → B → B → Judg          -- s = t : A

Ctx = List (Var × B)

record Hyp : Set where             -- 前提：Γ ⇒ θ
  constructor _⇒_
  field hctx : Ctx ; hj : Judg
infix 4 _⇒_

record Rule : Set where
  constructor rule
  field
    name  : String
    prem  : List Hyp
    concl : Judg

tyOf : B → B → Judg                -- s : A  ≡  s = s : A
tyOf s A = tmEq s s A

isTy : B → Judg                    -- A type ≡ A = A
isTy A = tyEq A A
```

记法助手。对象变量 `x y z` 与元变量 `f g f' g' r r' s s' t t' A A' Bm Bm'`（`Bm` 是动机） 编号如下。

```agda
x y z w : Var
x = 0 ; y = 1 ; z = 2 ; w = 9

f g f' g' r r' s s' t t' A A' Bm Bm' : Meta
f = 0 ; g = 1 ; f' = 2 ; g' = 3 ; r = 4 ; r' = 5 ; s = 6 ; s' = 7 ; t = 8 ; t' = 9
A = 10 ; A' = 11 ; Bm = 12 ; Bm' = 13

V : B
V = con tV []

T : B → B
T a = con tT (a ∷ [])

-- 非依赖箭头 A → B := Π w : A . B（w 不出现）
_⇒ᵗ_ : B → B → B
a ⇒ᵗ b = con tΠ (a ∷ abs (w ∷ []) b ∷ [])
infixr 6 _⇒ᵗ_

m₀ : Meta → B                      -- 0 元元变量 = 一个 m-项
m₀ m = meta m []

-- U_{f,g}、s_{f,g}(r)、Res0_{f,g}(r,s)、Res1_{f,g}(r,s,t)
U : Meta → Meta → B
U a b = con tU (mvar a ∷ mvar b ∷ [])

sfg : Meta → Meta → B → B
sfg a b e = con mS (mvar a ∷ mvar b ∷ e ∷ [])

lam : Var → B → B
lam v b = con cLam (abs (v ∷ []) b ∷ [])
```

## 3. Mahlo 宇宙的规则（Definition 4.3，页 10–11，逐条）

`Ass_I` 与 `Ass_=`（页 11）：

```agda
-- x : V, y : (T(x) → V) ⇒ f(x,y) = f'(x,y) : V
-- x : V, y : (T(x) → V), z : T(f(x,y)) ⇒ g(x,y,z) = g'(x,y,z) : V
Γf Γg : Ctx
Γf = (x , V) ∷ (y , T (var x) ⇒ᵗ V) ∷ []
Γg = Γf ++ ((z , T (meta f (var x ∷ var y ∷ []))) ∷ [])

fxy gxyz : Meta → B
fxy m  = meta m (var x ∷ var y ∷ [])
gxyz m = meta m (var x ∷ var y ∷ var z ∷ [])

AssI Ass= : List Hyp
AssI = (Γf ⇒ tmEq (fxy f) (fxy f') V) ∷ (Γg ⇒ tmEq (gxyz g) (gxyz g') V) ∷ []
Ass= = (Γf ⇒ tyOf (fxy f) V)         ∷ (Γg ⇒ tyOf (gxyz g) V)          ∷ []
```

V 的类型引入与引入规则（页 10）。「Similarly for N̂, Σ̂, Ŵ, +̂, Î」按 Π̂ 的样式展开。

```agda
Vcode : Sym → List B → B
Vcode c as = con c as

vIntro : Sym → Sym → List Rule       -- 二元带族的代码：Π̂_V、Σ̂_V、Ŵ_V
vIntro ĉ tc =
    rule "ĉ_V,I"
      ((([] ⇒ tmEq (m₀ r) (m₀ r') V)) ∷
       ((((x , T (m₀ r)) ∷ []) ⇒ tmEq (meta s (var x ∷ [])) (meta s' (var x ∷ [])) V)) ∷ [])
      (tmEq (Vcode ĉ (m₀ r ∷ mvar s ∷ [])) (Vcode ĉ (m₀ r' ∷ mvar s' ∷ [])) V)
  ∷ rule "ĉ_V,="
      ((([] ⇒ tyOf (m₀ r) V)) ∷
       ((((x , T (m₀ r)) ∷ []) ⇒ tyOf (meta s (var x ∷ [])) V)) ∷ [])
      (tyEq (T (Vcode ĉ (m₀ r ∷ mvar s ∷ [])))
            (con tc (T (m₀ r) ∷ abs (x ∷ []) (T (meta s (var x ∷ []))) ∷ [])))
  ∷ []

mahloV : List Rule
mahloV =
    rule "V_I" [] (tyEq V V)
  ∷ rule "T_I" (([] ⇒ tmEq (m₀ r) (m₀ r') V) ∷ []) (tyEq (T (m₀ r)) (T (m₀ r')))
  ∷ rule "N̂_k,V,I" [] (tmEq (con (vNk 0) []) (con (vNk 0) []) V)
  ∷ rule "N̂_k,V,=" [] (tyEq (T (con (vNk 0) [])) (con (tNk 0) []))
  ∷ rule "N̂_V,I"   [] (tmEq (con vN []) (con vN []) V)
  ∷ rule "N̂_V,="   [] (tyEq (T (con vN [])) (con tN []))
  ∷ vIntro vΠ tΠ ++ vIntro vΣ tΣ ++ vIntro vW tW
  ++ rule "+̂_V,I" (([] ⇒ tmEq (m₀ r) (m₀ r') V) ∷ ([] ⇒ tmEq (m₀ s) (m₀ s') V) ∷ [])
       (tmEq (con v+ (m₀ r ∷ m₀ s ∷ [])) (con v+ (m₀ r' ∷ m₀ s' ∷ [])) V)
  ∷ rule "+̂_V,=" (([] ⇒ tyOf (m₀ r) V) ∷ ([] ⇒ tyOf (m₀ s) V) ∷ [])
       (tyEq (T (con v+ (m₀ r ∷ m₀ s ∷ []))) (con t+ (T (m₀ r) ∷ T (m₀ s) ∷ [])))
  ∷ rule "Î_V,I" (([] ⇒ tmEq (m₀ r) (m₀ r') V) ∷ ([] ⇒ tmEq (m₀ s) (m₀ s') (T (m₀ r)))
                  ∷ ([] ⇒ tmEq (m₀ t) (m₀ t') (T (m₀ r))) ∷ [])
       (tmEq (con vI (m₀ r ∷ m₀ s ∷ m₀ t ∷ [])) (con vI (m₀ r' ∷ m₀ s' ∷ m₀ t' ∷ [])) V)
  ∷ rule "Î_V,=" (([] ⇒ tyOf (m₀ r) V) ∷ ([] ⇒ tyOf (m₀ s) (T (m₀ r))) ∷ ([] ⇒ tyOf (m₀ t) (T (m₀ r))) ∷ [])
       (tyEq (T (con vI (m₀ r ∷ m₀ s ∷ m₀ t ∷ []))) (con tI (T (m₀ r) ∷ m₀ s ∷ m₀ t ∷ [])))
  ∷ []
```

Mahlo 子宇宙：\(\widehat{\mathrm U}\)、\(\mathrm U\)、\(\mathrm s\)、\(\mathrm{Res}0\)、\(\mathrm{Res}1\)（页 10–11）。

```agda
Ûfg : Meta → Meta → B
Ûfg a b = con mU (mvar a ∷ mvar b ∷ [])

sx : Meta → B                         -- s(x)
sx m = meta m (var x ∷ [])

-- Res0_{f,g}(r,s)、Res1_{f,g}(r,s,t)
Res0 : Meta → Meta → B → B → B
Res0 a b e h = con mRes0 (mvar a ∷ mvar b ∷ e ∷ h ∷ [])
Res1 : Meta → Meta → B → B → B → B
Res1 a b e h k = con mRes1 (mvar a ∷ mvar b ∷ e ∷ h ∷ k ∷ [])

mahloU : List Rule
mahloU =
    rule "Û_I" AssI (tmEq (Ûfg f g) (Ûfg f' g') V)
  ∷ rule "Û_=" Ass= (tyEq (T (Ûfg f g)) (U f g))
  ∷ rule "U_T" AssI (tyEq (U f g) (U f' g'))
  ∷ rule "s_I" (AssI ++ (([] ⇒ tmEq (m₀ r) (m₀ r') (U f g)) ∷ []))
       (tmEq (sfg f g (m₀ r)) (sfg f' g' (m₀ r')) V)
  ∷ rule "Res0_I"
       ((([] ⇒ tmEq (m₀ r) (m₀ r') (U f g)))
        ∷ ((((x , T (sfg f g (m₀ r))) ∷ []) ⇒ tmEq (sx s) (sx s') (U f g)))
        ∷ AssI)
       (tmEq (Res0 f g (m₀ r) (mvar s)) (Res0 f' g' (m₀ r') (mvar s')) (U f g))
  ∷ rule "Res0_="
       ((([] ⇒ tyOf (m₀ r) (U f g)))
        ∷ ((((x , T (sfg f g (m₀ r))) ∷ []) ⇒ tyOf (sx s) (U f g)))
        ∷ Ass=)
       (tmEq (sfg f g (Res0 f g (m₀ r) (mvar s)))
             (meta f (sfg f g (m₀ r) ∷ lam x (sfg f g (sx s)) ∷ []))
             V)
  ∷ rule "Res1_I"
       ((([] ⇒ tmEq (m₀ r) (m₀ r') (U f g)))
        ∷ ((((x , T (sfg f g (m₀ r))) ∷ []) ⇒ tmEq (sx s) (sx s') (U f g)))
        ∷ (([] ⇒ tmEq (m₀ t) (m₀ t') (T (sfg f g (Res0 f g (m₀ r) (mvar s))))))
        ∷ AssI)
       (tmEq (Res1 f g (m₀ r) (mvar s) (m₀ t)) (Res1 f' g' (m₀ r') (mvar s') (m₀ t')) (U f g))
  ∷ rule "Res1_="
       ((([] ⇒ tyOf (m₀ r) (U f g)))
        ∷ ((((x , T (sfg f g (m₀ r))) ∷ []) ⇒ tyOf (sx s) (U f g)))
        ∷ (([] ⇒ tyOf (m₀ t) (T (sfg f g (Res0 f g (m₀ r) (mvar s))))))
        ∷ Ass=)
       (tmEq (sfg f g (Res1 f g (m₀ r) (mvar s) (m₀ t)))
             (meta g (sfg f g (m₀ r) ∷ lam x (sfg f g (sx s)) ∷ m₀ t ∷ []))
             V)
  ∷ []
```

U_{f,g} 对基构造子的引入规则（页 11：\(\widehat{\mathrm N}_{k,\vec f}\)、\(\widehat\Pi_{\vec f}\)，「Similarly for N̂, Σ̂, Ŵ, +̂, Î」）。

```agda
Ucode : Sym → List B → B                -- Ĉ_{f,g}(…)
Ucode c as = con c (mvar f ∷ mvar g ∷ as)

uIntro : Sym → Sym → List Rule         -- Π̂_f、Σ̂_f、Ŵ_f
uIntro ĉ v̂ =
    rule "ĉ_f,I"
      ((([] ⇒ tmEq (m₀ r) (m₀ r') (U f g)))
       ∷ ((((x , T (sfg f g (m₀ r))) ∷ []) ⇒ tmEq (sx s) (sx s') (U f g)))
       ∷ AssI)
      (tmEq (Ucode ĉ (m₀ r ∷ mvar s ∷ [])) (con ĉ (mvar f' ∷ mvar g' ∷ m₀ r' ∷ mvar s' ∷ [])) (U f g))
  ∷ rule "ĉ_f,="
      ((([] ⇒ tyOf (m₀ r) (U f g)))
       ∷ ((((x , T (sfg f g (m₀ r))) ∷ []) ⇒ tyOf (sx s) (U f g)))
       ∷ Ass=)
      (tmEq (sfg f g (Ucode ĉ (m₀ r ∷ mvar s ∷ [])))
            (con v̂ (sfg f g (m₀ r) ∷ abs (x ∷ []) (sfg f g (sx s)) ∷ []))
            V)
  ∷ []

mahloUintro : List Rule
mahloUintro =
    rule "N̂_k,f,I" AssI (tmEq (Ucode (uNk 0) []) (con (uNk 0) (mvar f' ∷ mvar g' ∷ [])) (U f g))
  ∷ rule "N̂_k,f,=" Ass= (tmEq (sfg f g (Ucode (uNk 0) [])) (con (vNk 0) []) V)
  ∷ rule "N̂_f,I"   AssI (tmEq (Ucode uN []) (con uN (mvar f' ∷ mvar g' ∷ [])) (U f g))
  ∷ rule "N̂_f,="   Ass= (tmEq (sfg f g (Ucode uN [])) (con vN []) V)
  ∷ uIntro uΠ vΠ ++ uIntro uΣ vΣ ++ uIntro uW vW
  ++ rule "+̂_f,I" ((([] ⇒ tmEq (m₀ r) (m₀ r') (U f g))) ∷ (([] ⇒ tmEq (m₀ s) (m₀ s') (U f g))) ∷ AssI)
       (tmEq (Ucode u+ (m₀ r ∷ m₀ s ∷ [])) (con u+ (mvar f' ∷ mvar g' ∷ m₀ r' ∷ m₀ s' ∷ [])) (U f g))
  ∷ rule "+̂_f,=" ((([] ⇒ tyOf (m₀ r) (U f g))) ∷ (([] ⇒ tyOf (m₀ s) (U f g))) ∷ Ass=)
       (tmEq (sfg f g (Ucode u+ (m₀ r ∷ m₀ s ∷ []))) (con v+ (sfg f g (m₀ r) ∷ sfg f g (m₀ s) ∷ [])) V)
  ∷ rule "Î_f,I" ((([] ⇒ tmEq (m₀ r) (m₀ r') (U f g)))
                  ∷ (([] ⇒ tmEq (m₀ s) (m₀ s') (T (sfg f g (m₀ r)))))
                  ∷ (([] ⇒ tmEq (m₀ t) (m₀ t') (T (sfg f g (m₀ r))))) ∷ AssI)
       (tmEq (Ucode uI (m₀ r ∷ m₀ s ∷ m₀ t ∷ []))
             (con uI (mvar f' ∷ mvar g' ∷ m₀ r' ∷ m₀ s' ∷ m₀ t' ∷ [])) (U f g))
  ∷ rule "Î_f,=" ((([] ⇒ tyOf (m₀ r) (U f g)))
                  ∷ (([] ⇒ tyOf (m₀ s) (T (sfg f g (m₀ r)))))
                  ∷ (([] ⇒ tyOf (m₀ t) (T (sfg f g (m₀ r))))) ∷ Ass=)
       (tmEq (sfg f g (Ucode uI (m₀ r ∷ m₀ s ∷ m₀ t ∷ [])))
             (con vI (sfg f g (m₀ r) ∷ m₀ s ∷ m₀ t ∷ [])) V)
  ∷ []
```

## 4. 基段规则（Definition 4.3 转引 [Se93] 的 ML_J，等式版）

原文说基段规则「in the same way as ML_J in [Se93]」并只展示 Π 的三条（页 10）。[Se93] 本项目未取得；这里按标准 Martin-Löf 规则的等式版写出形成、引入、**消去**、计算。对提取器而言基段规则的作用只有两点：每个基类型构造子**有**消去规则（其主前提是该类型），以及 \(\mathrm W\) 的形成规则对 \(A\) 是模式（故 \(\mathrm W(\mathrm V,\mathrm T)\) 合法）。基段消去子的**精确形状**（`R(r,(x,y,z)s)` 等）本项目未逐条核对 [Se93]，[SOURCES.md](../SOURCES.md) 已注明。

消去规则的标志：结论的**类型是一个动机元变量** \(B(r)\)（对主前提项 \(r\) 的依赖类型），而不是某个固定的类型构造子。这一形状是提取器识别「消去」的句法判据。

```agda
motive : B → B                         -- B(r)
motive e = meta Bm (e ∷ [])

-- 三条通用形状：形成（模式在 A、B 上）、消去（动机）
formation : String → Sym → Rule       -- A = A', x:A ⇒ B(x) = B'(x)  ⊢  C(A,B) = C(A',B')
formation nm c = rule nm
  ((([] ⇒ tyEq (m₀ A) (m₀ A')))
   ∷ ((((x , m₀ A) ∷ []) ⇒ tyEq (meta Bm (var x ∷ [])) (meta Bm' (var x ∷ [])))) ∷ [])
  (tyEq (con c (m₀ A ∷ abs (x ∷ []) (meta Bm (var x ∷ [])) ∷ []))
        (con c (m₀ A' ∷ abs (x ∷ []) (meta Bm' (var x ∷ [])) ∷ [])))

elim : String → Sym → Sym → Rule       -- 主前提 r : C(…)，结论 e(r) : B(r)
elim nm c e = rule nm
  ((([] ⇒ tyOf (m₀ r) (con c [])))
   ∷ ((((x , con c []) ∷ []) ⇒ isTy (motive (var x)))) ∷ [])
  (tyOf (con e (m₀ r ∷ mvar s ∷ [])) (motive (m₀ r)))

baseRules : List Rule
baseRules =
    rule "N_T" [] (tyEq (con tN []) (con tN []))
  ∷ rule "N_I0" [] (tyOf (con c0 []) (con tN []))
  ∷ rule "N_IS" (([] ⇒ tmEq (m₀ r) (m₀ r') (con tN [])) ∷ [])
      (tmEq (con cS (m₀ r ∷ [])) (con cS (m₀ r' ∷ [])) (con tN []))
  ∷ elim "N_E" tN cR
  ∷ rule "N_k,T" [] (tyEq (con (tNk 0) []) (con (tNk 0) []))
  ∷ elim "N_k,E" (tNk 0) (cC 0)
  ∷ formation "Π_T" tΠ
  ∷ rule "Π_I" (((((x , m₀ A) ∷ []) ⇒ tmEq (meta t (var x ∷ [])) (meta t' (var x ∷ [])) (meta Bm (var x ∷ [])))) ∷ [])
      (tmEq (lam x (meta t (var x ∷ []))) (lam x (meta t' (var x ∷ [])))
            (con tΠ (m₀ A ∷ abs (x ∷ []) (meta Bm (var x ∷ [])) ∷ [])))
  ∷ rule "Π_E" (((((x , m₀ A) ∷ []) ⇒ isTy (meta Bm (var x ∷ []))))
                ∷ (([] ⇒ tmEq (m₀ s) (m₀ s') (con tΠ (m₀ A ∷ abs (x ∷ []) (meta Bm (var x ∷ [])) ∷ []))))
                ∷ (([] ⇒ tmEq (m₀ r) (m₀ r') (m₀ A))) ∷ [])
      (tmEq (con cAp (m₀ s ∷ m₀ r ∷ [])) (con cAp (m₀ s' ∷ m₀ r' ∷ [])) (meta Bm (m₀ r ∷ [])))
  ∷ rule "Π_=" (((((x , m₀ A) ∷ []) ⇒ tyOf (meta t (var x ∷ [])) (meta Bm (var x ∷ []))))
                ∷ (([] ⇒ tyOf (m₀ r) (m₀ A))) ∷ [])
      (tmEq (con cAp (lam x (meta t (var x ∷ [])) ∷ m₀ r ∷ [])) (meta t (m₀ r ∷ [])) (meta Bm (m₀ r ∷ [])))
  ∷ formation "Σ_T" tΣ ∷ elim "Σ_E" tΣ cp0
  ∷ formation "W_T" tW ∷ elim "W_E" tW cP
  ∷ rule "+_T" (([] ⇒ tyEq (m₀ A) (m₀ A')) ∷ ([] ⇒ tyEq (m₀ Bm) (m₀ Bm')) ∷ [])
      (tyEq (con t+ (m₀ A ∷ m₀ Bm ∷ [])) (con t+ (m₀ A' ∷ m₀ Bm' ∷ [])))
  ∷ elim "+_E" t+ cD
  ∷ rule "I_T" (([] ⇒ tyEq (m₀ A) (m₀ A')) ∷ ([] ⇒ tmEq (m₀ r) (m₀ r') (m₀ A)) ∷ ([] ⇒ tmEq (m₀ s) (m₀ s') (m₀ A)) ∷ [])
      (tyEq (con tI (m₀ A ∷ m₀ r ∷ m₀ s ∷ [])) (con tI (m₀ A' ∷ m₀ r' ∷ m₀ s' ∷ [])))
  ∷ elim "I_E" tI cJ
  ∷ []
```

## 5. MLM

```agda
record RuleTable : Set where
  constructor mkRT
  field
    sig   : Sig
    rules : List Rule

mlm : RuleTable
mlm = mkRT mlmSig (baseRules ++ mahloV ++ mahloU ++ mahloUintro)
```

## 6. 这份数据忠实到什么程度

**逐字**：Definition 4.1(a) 的签名与元数；4.1(b) 的 b-对象三种形状；4.1(g) 的三种判断与「type／:」作缩写的约定；4.3 页 10–11 的全部 Mahlo 规则（V_I、T_I、V 的七组引入规则、Û_I、Û_=、U_T、s_I、Res0_I/=、Res1_I/=、U 的七组引入规则）。「Similarly for …」按原文给出的 Π̂ 样式展开。

**未逐字**：基段规则（原文转引 [Se93]，未取得）；`elim` 只保留「主前提类型 + 动机结论」的形状。ℕ 索引族只列代表。

**没有的东西**：代换的定义（4.1(b) 说「in the usual way」）、α-等价、上下文合法性判断的推导规则。它们是 E-2（绑定／代换／计算相容）的内容，不是本文件的目标；这里只把规则**摆出来**。

**关键事实，现在从数据上可读**：`mahloV ++ mahloU ++ mahloUintro` 里没有一条规则的结论类型是动机元变量——**V 与 U_{f,g} 没有消去规则**。这不再是「由签名穷举可见」的间接推断（§97.1），是规则表的直接性质，[`Extract`](Extract.lagda.md) 用一个句法函数读它。
