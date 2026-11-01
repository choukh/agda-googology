# 提取器：对规则表做句法分析

[RESEARCH.md](../RESEARCH.md) §122。输入是 [`Rules`](Rules.lagda.md) 里的规则表，输出是配方要的参数。**每个参数都由一个句法函数从规则表算出**，不再有人手填的字段。前任的 `ExtSpec` 里 `quantified`／`rank`／`targetBaseClosed`／`hasElim` 是四个由人赋值的字段——那是把答案写进输入，本文件用四个函数取代它们。

作用域审计：import 里没有 `ExtOT`／`ExtOrd`，没有任何序数记号。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Mahlo.Object.Extract where

open import Mahlo.Object.Rules

open import Data.Nat.Base using (ℕ; zero; suc; _⊔_; _≡ᵇ_)
open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_; map; filter; foldr)
open import Data.Bool.ListAction using (any; all)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Empty using (⊥)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)
open import Relation.Unary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym)
```

## 1. 符号相等

```agda
tag : Sym → ℕ
tag c0 = 0 ; tag (cl _ _) = 1 ; tag cS = 2 ; tag ci = 3 ; tag cj = 4 ; tag cp0 = 5 ; tag cp1 = 6
tag cr = 7 ; tag cLam = 8 ; tag cE = 9 ; tag cp = 10 ; tag csup = 11 ; tag cR = 12 ; tag cAp = 13
tag cJ = 14 ; tag cD = 15 ; tag cP = 16 ; tag (cC _) = 17
tag uN = 20 ; tag (uNk _) = 21 ; tag u+ = 22 ; tag uΠ = 23 ; tag uΣ = 24 ; tag uW = 25 ; tag uI = 26
tag vN = 30 ; tag (vNk _) = 31 ; tag v+ = 32 ; tag vΠ = 33 ; tag vΣ = 34 ; tag vW = 35 ; tag vI = 36
tag mU = 40 ; tag mS = 41 ; tag mRes0 = 42 ; tag mRes1 = 43
tag (tNk _) = 50 ; tag tN = 51 ; tag t+ = 52 ; tag tΠ = 53 ; tag tΣ = 54 ; tag tW = 55
tag tI = 56 ; tag tV = 57 ; tag tT = 58 ; tag tU = 59

idx : Sym → ℕ × ℕ
idx (cl l k) = l , k ; idx (cC n) = n , 0 ; idx (uNk k) = k , 0
idx (vNk k) = k , 0 ; idx (tNk k) = k , 0 ; idx _ = 0 , 0

symEq : Sym → Sym → Bool
symEq a b = (tag a ≡ᵇ tag b) ∧ (proj₁ (idx a) ≡ᵇ proj₁ (idx b)) ∧ (proj₂ (idx a) ≡ᵇ proj₂ (idx b))

elemSym : Sym → List Sym → Bool
elemSym c = any (symEq c)
```

## 2. 句法测度

`mentions c b`：b-对象里出现符号 `c`。`small A`：类型表达式里不出现宇宙类型构造子 `V`、`U`——即「解码出来的小类型」（`T(·)`、`N`、`N_k`、`I` 等）。

```agda
mutual
  mentions : Sym → B → Bool
  mentions c (var _)      = false
  mentions c (abs _ b)    = mentions c b
  mentions c (con d as)   = symEq c d ∨ mentionsL c as
  mentions c (meta _ as)  = mentionsL c as
  mentions c (mvar _)     = false

  mentionsL : Sym → List B → Bool
  mentionsL c []       = false
  mentionsL c (b ∷ bs) = mentions c b ∨ mentionsL c bs

small : B → Bool
small A = not (mentions tV A ∨ mentions tU A)
```

**类型的阶**（§122.3）。`Π A B` 在 `A` 小时不抬阶（那是一个族，是数据）；`A` 提到宇宙时抬一阶（那是对宇宙元素或族的函数，是算子）。

```agda
ordTy : B → ℕ
ordTy (con tΠ (A ∷ abs _ Bd ∷ [])) = if small A then ordTy Bd else suc (ordTy A) ⊔ ordTy Bd
ordTy (con tΣ (A ∷ abs _ Bd ∷ [])) = ordTy A ⊔ ordTy Bd
ordTy _                            = 0

ctxOrd : Ctx → ℕ                      -- 上下文各类型的阶的最大值
ctxOrd = foldr (λ p m → ordTy (proj₂ p) ⊔ m) 0

ctxSmall : Ctx → Bool                 -- 上下文里的类型全都小
ctxSmall = all (λ p → small (proj₂ p))
```

## 3. 从规则表读出的四样东西

### 3.1 消去规则

一条规则是类型构造子 `c` 的**消去规则**，当它有一个类型为 `c(…)` 的前提（主前提，出现在判断里或上下文里），且**结论的类型是一个动机元变量** `B(r)`。结论落在固定的类型构造子上的规则（`: V`、`: U_{f,g}`、`T(…) = …`）都不是消去。

```agda
isMotive : B → Bool
isMotive (meta _ _) = true
isMotive _          = false

hypHasType : Sym → Hyp → Bool
hypHasType c (Γ ⇒ tmEq _ _ (con d _)) = symEq c d ∨ any (λ p → headIs c (proj₂ p)) Γ
  where headIs : Sym → B → Bool
        headIs c (con d _) = symEq c d
        headIs _ _         = false
hypHasType c (Γ ⇒ _) = any (λ p → headIs c (proj₂ p)) Γ
  where headIs : Sym → B → Bool
        headIs c (con d _) = symEq c d
        headIs _ _         = false

conclType : Rule → Maybe B
conclType (rule _ _ (tmEq _ _ A)) = just A
conclType _                       = nothing

elimFor : Sym → Rule → Bool
elimFor c ru with conclType ru
... | just A  = isMotive A ∧ any (hypHasType c) (Rule.prem ru)
... | nothing = false

hasElim : Sym → RuleTable → Bool
hasElim c rt = any (elimFor c) (RuleTable.rules rt)
```

### 3.2 算子闭包规则、顶宇宙、算子的阶

**顶宇宙**：不带参数的宇宙类型 `con tyc []`（`V` 是，`U_{f,g}` 不是）。**算子元变量**：结论左边的代码构造子的某个 b-对象参数 `mvar m`，其前提上下文**提到宇宙**（不全小）。`Π̂_V(r,s)` 里的 `s` 上下文是 `x : T(r)`——小，是族，不算；`Û_{f,g}` 里的 `f` 上下文是 `x : V, y : T(x) → V`——提到 `V`，是算子。

```agda
-- 元变量 m 在前提里的上下文（找 tmEq (meta m …) 那条）
metaCtx : Meta → List Hyp → Maybe Ctx
metaCtx m [] = nothing
metaCtx m ((Γ ⇒ tmEq (meta m' _) _ _) ∷ hs) = if m ≡ᵇ m' then just Γ else metaCtx m hs
metaCtx m (_ ∷ hs) = metaCtx m hs

mvars : List B → List Meta
mvars []            = []
mvars (mvar m ∷ bs) = m ∷ mvars bs
mvars (_ ∷ bs)      = mvars bs

-- 规则里的算子元变量及其阶：1 + 上下文的阶
opMetas : Rule → List (Meta × ℕ)
opMetas ru with Rule.concl ru
... | tmEq (con _ as) _ (con _ []) = go (mvars as)
  where
    go : List Meta → List (Meta × ℕ)
    go [] = []
    go (m ∷ ms) with metaCtx m (Rule.prem ru)
    ... | just Γ  = if ctxSmall Γ then go ms else (m , suc (ctxOrd Γ)) ∷ go ms
    ... | nothing = go ms
... | _ = []

-- 顶宇宙的算子闭包规则：结论 C(…, f, …) : 𝒱，𝒱 无参数，且有算子元变量
isClosureRule : Rule → Bool
isClosureRule ru with opMetas ru
... | [] = false
... | _  = true

closureRules : RuleTable → List Rule
closureRules rt = filter′ isClosureRule (RuleTable.rules rt)
  where
    filter′ : (Rule → Bool) → List Rule → List Rule
    filter′ p []       = []
    filter′ p (u ∷ us) = if p u then u ∷ filter′ p us else filter′ p us

quantified : RuleTable → Bool
quantified rt with closureRules rt
... | [] = false
... | _  = true

maxOrd : List (Meta × ℕ) → ℕ
maxOrd = foldr (λ p m → proj₂ p ⊔ m) 0

rank : RuleTable → ℕ                  -- 算子的最高阶
rank rt = foldr (λ ru m → maxOrd (opMetas ru) ⊔ m) 0 (closureRules rt)

-- 顶宇宙：闭包规则结论的类型构造子
topUniv : RuleTable → Maybe Sym
topUniv rt with closureRules rt
... | rule _ _ (tmEq _ _ (con tyc [])) ∷ _ = just tyc
... | _ = nothing

-- 闭包规则引入的代码构造子（Û）
closureCode : RuleTable → Maybe Sym
closureCode rt with closureRules rt
... | rule _ _ (tmEq (con c _) _ _) ∷ _ = just c
... | _ = nothing
```

### 3.3 闭点是否须基闭

由解码规则 `T(Û_{f,g}) = U_{f,g}` 找出闭包代码的**目标宇宙**（`tU`），再按签名的 γ 表逐个基类型构造子查：目标宇宙有没有对应代码构造子的引入规则（`Π̂_f(r,s) : U_{f,g}` 等）。

```agda
decodesTo : Sym → Rule → Maybe Sym     -- T(c(…)) = d(…)  ↦  d
decodesTo c (rule _ _ (tyEq (con tT (con c' _ ∷ [])) (con d _))) = if symEq c c' then just d else nothing
decodesTo _ _ = nothing

firstJust : List (Maybe Sym) → Maybe Sym
firstJust []             = nothing
firstJust (just d ∷ _)   = just d
firstJust (nothing ∷ xs) = firstJust xs

targetUniv : RuleTable → Maybe Sym
targetUniv rt with closureCode rt
... | just c  = firstJust (map (decodesTo c) (RuleTable.rules rt))
... | nothing = nothing

introInto : Sym → Sym → Rule → Bool   -- 结论  c(…) = … : tyc(…)
introInto tyc c (rule _ _ (tmEq (con c' _) _ (con d _))) = symEq c c' ∧ symEq tyc d
introInto _ _ _ = false

targetBaseClosed : RuleTable → Bool
targetBaseClosed rt with targetUniv rt
... | nothing  = false
... | just tyc = all (λ γ₃ → any (introInto tyc (proj₁ (proj₂ γ₃))) (RuleTable.rules rt))
                     (Sig.γ (RuleTable.sig rt))
```

### 3.4 `W`，以及它的形成规则对 `A` 是模式

```agda
hasW : RuleTable → Bool
hasW rt = elemSym tW (Sig.tyCons (RuleTable.sig rt))

wSchematic : RuleTable → Bool         -- 存在  W(A,…) = …  的形成规则，A 是元变量
wSchematic rt = any isWform (RuleTable.rules rt)
  where
    isWform : Rule → Bool
    isWform (rule _ _ (tyEq (con tW (meta _ _ ∷ _)) _)) = true
    isWform _ = false
```

## 4. 参数

```agda
data ReflLevel : Set where
  noRefl : ReflLevel
  piK    : ℕ → ReflLevel

data Degree : Set where
  naDeg : Degree
  deg   : ℕ → Degree
  unbdd : Degree

data IndForm : Set where
  schema full : IndForm

record Params : Set where
  constructor mkParams
  field
    reflLv   : ReflLevel
    mahloDeg : Degree
    indForm  : IndForm
    ΩUnbdd   : Bool

topHasElim : RuleTable → Bool
topHasElim rt with topUniv rt
... | just tyc = hasElim tyc rt
... | nothing  = false

spec : RuleTable → Params
spec rt = mkParams lv dg ind Ω
  where
    q  = quantified rt
    e  = topHasElim rt
    lv = if q then piK (suc (rank rt)) else noRefl
    dg = if not q then naDeg
         else if e then unbdd
         else if targetBaseClosed rt then deg 2 else deg 1
    ind = if e then full else schema
    Ω  = hasW rt ∧ wSchematic rt
```

三条依据：算子的阶 `r` ⟹ `Π_{r+1}` 反射（§112.2：一阶算子的闭包是 `∀(f,g) ∃κ Δ₀`，Π₂；Arai 的 `RM_k`／`Π_k` 对应逐阶上推）；闭点基闭且不能内部迭代 ⟹ `RM₂(RM₂)`，度 2（§115.2）；顶宇宙无消去子 ⟹ 模式形式（§111.4）。

## 5. MLM 的参数——由规则表算出

```agda
_ : spec mlm ≡ mkParams (piK 2) (deg 2) schema true
_ = refl
```

四个中间量各自可查：

```agda
_ : quantified mlm ≡ true
_ = refl

_ : rank mlm ≡ 1
_ = refl

_ : topUniv mlm ≡ just tV
_ = refl

_ : targetUniv mlm ≡ just tU
_ = refl

_ : targetBaseClosed mlm ≡ true
_ = refl

-- V 与 U 没有消去规则；N、Π、W 有
_ : hasElim tV mlm ≡ false
_ = refl
_ : hasElim tU mlm ≡ false
_ = refl
_ : hasElim tN mlm ≡ true
_ = refl
_ : hasElim tΠ mlm ≡ true
_ = refl
_ : hasElim tW mlm ≡ true
_ = refl
```

## 6. 扰动：改的是规则

```agda
ruleMentions : Sym → Rule → Bool
ruleMentions c (rule _ ps cc) = any hypM ps ∨ judgM cc
  where
    judgM : Judg → Bool
    judgM ctx = false
    judgM (tyEq a b) = mentions c a ∨ mentions c b
    judgM (tmEq a b d) = mentions c a ∨ mentions c b ∨ mentions c d
    hypM : Hyp → Bool
    hypM (Γ ⇒ j) = any (λ p → mentions c (proj₂ p)) Γ ∨ judgM j

-- 只删规则：去掉所有提到符号 c 的规则，签名不动（理论仍「有」这个构造子，只是少了规则）
dropRules : Sym → RuleTable → RuleTable
dropRules c (mkRT sg rs) = mkRT sg (keep rs)
  where
    keep : List Rule → List Rule
    keep []       = []
    keep (u ∷ us) = if ruleMentions c u then keep us else u ∷ keep us

-- 删符号：从签名（含 γ 表）和规则表里一起删掉 c
dropSym : Sym → RuleTable → RuleTable
dropSym c rt with dropRules c rt
... | mkRT (mkSig tys tms γ) rs = mkRT (mkSig (filterOut tys) (filterOut tms) (filterγ γ)) rs
  where
    filterOut : List Sym → List Sym
    filterOut []       = []
    filterOut (d ∷ ds) = if symEq c d then filterOut ds else d ∷ filterOut ds
    filterγ : List (Sym × Sym × Sym) → List (Sym × Sym × Sym)
    filterγ [] = []
    filterγ ((a , b , d) ∷ gs) =
      if symEq c a ∨ symEq c b ∨ symEq c d then filterγ gs else (a , b , d) ∷ filterγ gs

addRule : Rule → RuleTable → RuleTable
addRule u (mkRT sg rs) = mkRT sg (u ∷ rs)
```

**(a) 给 V 加一条消去规则**（假想的 `V_E`：主前提 `r : V`，结论落在动机上）。这正是 Dybjer–Setzer Appendix B 说会导致不一致的那种规则。

```agda
mlm+elim : RuleTable
mlm+elim = addRule (elim "V_E" tV cR) mlm

_ : spec mlm+elim ≡ mkParams (piK 2) unbdd full true
_ = refl
```

**(b) 从签名和规则表里删掉 `W`**（`W_T`、`W_E`、`Ŵ_V`、`Ŵ_f` 全部随之消失）。

```agda
mlm−W : RuleTable
mlm−W = dropSym uW (dropSym vW (dropSym tW mlm))

_ : spec mlm−W ≡ mkParams (piK 2) (deg 2) schema false
_ = refl
```

**(c) 删掉子宇宙对 Π 的引入规则**（只删规则，Π 仍是理论的基构造子）——`U_{f,g}` 不再对全部基构造子封闭。

```agda
mlm−Ucl : RuleTable
mlm−Ucl = dropRules uΠ mlm

_ : targetBaseClosed mlm−Ucl ≡ false
_ = refl

_ : spec mlm−Ucl ≡ mkParams (piK 2) (deg 1) schema true
_ = refl
```

**(d) 算子固定**：把 `Û_{f,g}` 换成一个不带 b-对象参数的常量代码 `Û`（对一个内建算子封闭的超宇宙）。

```agda
superRules : List Rule
superRules =
    rule "Û_I" [] (tmEq (con mU []) (con mU []) V)
  ∷ rule "Û_=" [] (tyEq (T (con mU [])) (con tU []))
  ∷ []

superU : RuleTable
superU = mkRT mlmSig (baseRules ++ mahloV ++ superRules)

_ : spec superU ≡ mkParams noRefl naDeg schema true
_ = refl
```

**(e) 算子升一阶**：给 `f` 的前提上下文加一个**算子类型**的变量 `o : (x:V)(y:T(x)→V) → V`——Takahashi 式的高阶闭包。

```agda
opTy : B                                 -- (x : V)(y : T(x) → V) → V
opTy = con tΠ (V ∷ abs (x ∷ []) (con tΠ ((T (var x) ⇒ᵗ V) ∷ abs (y ∷ []) V ∷ [])) ∷ [])

Γf₂ : Ctx
Γf₂ = (x , V) ∷ (y , T (var x) ⇒ᵗ V) ∷ (z , opTy) ∷ []

AssI₂ : List Hyp
AssI₂ = (Γf₂ ⇒ tmEq (meta f (var x ∷ var y ∷ var z ∷ [])) (meta f' (var x ∷ var y ∷ var z ∷ [])) V)
      ∷ (Γg ⇒ tmEq (gxyz g) (gxyz g') V) ∷ []

mlm↑ : RuleTable
mlm↑ = addRule (rule "Û_I↑" AssI₂ (tmEq (Ûfg f g) (Ûfg f' g') V)) (dropSym mU mlm)

_ : rank mlm↑ ≡ 2
_ = refl

_ : ReflLevel.piK 3 ≡ Params.reflLv (spec (addRule (rule "Û_=" Ass= (tyEq (T (Ûfg f g)) (U f g))) mlm↑))
_ = refl
```

（(e) 里 `dropSym mU` 连同 `Û_=`、`s`、`Res` 一起删掉了，故补回一条解码规则只为读 `reflLv`。）

## 7. 每个参数分量都真依赖规则

```agda
lvDiff : ¬ (noRefl ≡ piK 2)
lvDiff ()
sensitive-op : spec mlm ≢ spec superU
sensitive-op eq = lvDiff (cong Params.reflLv (sym eq))

degDiff : ¬ (deg 2 ≡ deg 1)
degDiff ()
sensitive-cl : spec mlm ≢ spec mlm−Ucl
sensitive-cl eq = degDiff (cong Params.mahloDeg eq)

indDiff : ¬ (schema ≡ full)
indDiff ()
sensitive-elim : spec mlm ≢ spec mlm+elim
sensitive-elim eq = indDiff (cong Params.indForm eq)

boolDiff : ¬ (true ≡ false)
boolDiff ()
sensitive-W : spec mlm ≢ spec mlm−W
sensitive-W eq = boolDiff (cong Params.ΩUnbdd eq)
```

## 8. 这检验了什么

**E-1**：`spec : RuleTable → Params`，输入是 [`Rules`](Rules.lagda.md) 里逐条转写的规则。四个中间量（`quantified`、`rank`、`targetBaseClosed`、`topHasElim`）各由一个句法函数算出，§5 逐个 `refl`。

**E-3**：五条扰动改的是**规则**——加一条消去规则、删一个类型构造子及其全部规则、删一组引入规则、把算子改成常量、给算子升一阶——输出按 §111／§112／§115.2 的预测变，四个分量各被至少一处扰动改变（§7）。作用域内没有序数记号。

**没检验的**：三条读出规则（阶 ⟹ 反射层级、基闭 ⟹ 度 2、无消去 ⟹ 模式）本身是否正确——那是 C1；E-2（绑定／代换／计算相容）不在本文件。`hasElim` 用「结论落在动机元变量上」识别消去，这是对 Martin-Löf 消去规则形状的句法刻画，基段规则按此形状录入（[`Rules`](Rules.lagda.md) §4 已注明 [Se93] 未取得）。
